local urlparse = require("socket.url")
local http = require("socket.http")
local https = require("ssl.https")
local cjson = require("cjson")
local utf8 = require("utf8")
local html_entities = require("htmlEntities")
local base64 = require("base64")
local basexx = require("basexx")
local iconv = require("iconv")
local openssl_digest = require("openssl.digest")
local uuid = require("uuid")

math.randomseed(os.time())
uuid.set_rng(uuid.rng.math_random())

local item_dir = os.getenv("item_dir")
local warc_file_base = os.getenv("warc_file_base")
local concurrency = tonumber(os.getenv("concurrency"))

local item_type = nil
local item_name = nil
local item_value = nil
local item_user = nil

local url_count = 0
local tries = 0
local downloaded = {}
local seen_200 = {}
local addedtolist = {}
local abortgrab = false
local killgrab = false
local logged_response = false

local discovered_outlinks = {}
local discovered_items = {}
local discovered_binaries = {}
local discovered_updateids = {}
local discovered_classifications = {}
local discovered_periodic = {}
local bad_items = {}
local ids = {}

local b32digests = cjson.decode(os.getenv("b32digests"))
local uuid_searches = cjson.decode(os.getenv("uuid_searches"))

local retry_url = false
local is_initial_url = true

abort_item = function(item)
  abortgrab = true
  --killgrab = true
  if not item then
    item = item_name
  end
  if not bad_items[item] then
    io.stdout:write("Aborting item " .. item .. ".\n")
    io.stdout:flush()
    bad_items[item] = true
  end
end

kill_grab = function(item)
  io.stdout:write("Aborting crawling.\n")
  killgrab = true
end

read_file = function(file)
  if file then
    local f = assert(io.open(file))
    local data = f:read("*all")
    f:close()
    return data
  else
    return ""
  end
end

processed = function(url)
  if downloaded[url] or addedtolist[url] then
    return true
  end
  return false
end

discover_item = function(target, item)
  if not target[item] then
--print("discovered", item)
    target[item] = true
    return true
  end
  return false
end

find_item = function(url)
  if ids[url] then
    return nil
  end
  local value, revision = string.match(url, "^https?://www%.catalog%.update%.microsoft%.com/ScopedViewRedirect%.aspx%?updateid=([0-9a-f%-]+)&revisionnumber=([0-9]+)$")
  if value then
    return {
      ["value"]=value,
      ["type"]="id",
      ["revision"]=revision
    }
  end
  local type_ = nil
  for pattern, name in pairs({
    ["^https?://www%.catalog%.update%.microsoft%.com/ScopedViewInline%.aspx%?updateid=([0-9a-f%-]+)$"]="id",
    ["^https?://www%.catalog%.update%.microsoft%.com/ScopedViewRedirect%.aspx%?updateid=([0-9a-f%-]+)$"]="id",
    ["^https?://catalog%.s%.download%.windowsupdate%.com/(.+)$"]="bin",
    ["^(https?://download%.microsoft%.com/.+)$"]="binurl",
    ["^(https?://catalog%.sf%.dl%.delivery%.mp%.microsoft%.com/.+)$"]="binurl",
    ["^https?://www%.microsoft%.com/[0-9a-z%-]+/download/details%.aspx%?id=([0-9]+)$"]="dlc",
    ["^https?://www%.catalog%.update%.microsoft%.com/Search%.aspx%?q=([^&]+)$"]="search"
  }) do
    value = string.match(url, pattern)
    type_ = name
    if value then
      break
    end
  end
  if value and type_ then
    return {
      ["value"]=value,
      ["type"]=type_
    }
  end
end

is_binary_item = function(type_)
  return type_ == "bin" or type_ == "binurl"
end

finish_item = function()
  if item_type == "id" then
    if abortgrab then
      return true
    end
    for digest in pairs(context["encrypted"]) do
      if not context["decryption"][digest] then
        error("Did not finish the decryption check.")
      end
    end
    if context["metadata_seen"]
      and not context["revision_item"]
      and context["revision_checks"] ~= math.max(3, math.floor(tonumber(context["revision"]) / 100) + 1) then
      error("Did not finish the revision check.")
    end
    if not context["download_found"]
      and not context["metadata_seen"]
      and not context["driver_set_seen"] then
      error("Did not finish the catalog or metadata check.")
    end
    return true
  elseif item_type == "dlc" then
    if not abortgrab and not context["download_found"] then
      error("Did not find a DLC download.")
    end
    return true
  elseif not is_binary_item(item_type) then
    return true
  end
  local count = 0
  for _, matches in pairs(context["matches"]) do
    if matches == false then
      error("Incorrect matching SHA1 found.")
    elseif matches == true then
      count = count + 1
    end
  end
  if count < 1 then
    error("Incorrect number of matching URLs found.")
  end
  return true
end

set_item = function(url)
  found = find_item(url)
  if found then
    local newcontext = {
      ["decryption"]={},
      ["encrypted"]={},
      ["matches"]={},
      ["retried"]={},
      ["revision_checks"]=0,
      ["todo_binaries"]={}
    }
    new_item_type = found["type"]
    new_item_value = found["value"]
    if new_item_type == "bin" then
      local temp = string.match(new_item_value, "^[cd]/(.*)$")
      if temp then
        new_item_value = temp
      end
    elseif new_item_type == "search" then
      newcontext["search_escaped"] = new_item_value
      new_item_value = string.gsub(new_item_value, "%+", " ")
      new_item_value = urlparse.unescape(new_item_value)
      newcontext["search"] = new_item_value
      local search_term, star_term = string.match(new_item_value, "^(.-) *([0-9a-f]*)%*$")
      newcontext["search_term"] = search_term
      newcontext["star_term"] = star_term
      if star_term then
        star_term_check = uuid_searches[new_item_value]
        if not star_term_check then
          error("Expected a UUID search query.")
        elseif star_term_check ~= star_term then
          error("Inconsistent star terms found.")
        end
        new_item_type = "uuid-search"
        new_item_value = star_term .. ":" .. search_term
      end
    end
    if found["revision"] then
      newcontext["revision_item"] = true
      newcontext["revision"] = found["revision"]
      discover_item(discovered_updateids, "id:" .. new_item_value)
    end
    local extra = ""
    if is_binary_item(new_item_type) then
      local b32digest = b32digests[new_item_value]
      extra = b32digest .. ":"
    end
    new_item_name = new_item_type .. ":" .. extra .. new_item_value
    if newcontext["revision_item"] then
      new_item_name = new_item_name .. ":" .. newcontext["revision"]
    end
    if new_item_name ~= item_name then
      finish_item()
      ids = {}
      context = newcontext
      item_value = new_item_value
      item_type = new_item_type
      ids[string.lower(item_value)] = true
      if context["search"] then
        ids[string.lower(context["search"])] = true
        ids[string.lower(context["search_escaped"])] = true
      end
      abortgrab = false
      tries = 0
      retry_url = false
      is_initial_url = true
      item_name = new_item_name
      print("Archiving item " .. item_name)
    end
  end
end

allowed = function(url, parenturl)
  local noscheme = string.match(url, "^https?://(.*)$")

  if ids[url]
    or (noscheme and ids[string.lower(noscheme)]) then
    return true
  end

  if ids[string.match(url, "^https?://[^/]+/(.*)$")]
    or ids[string.match(url, "^https?://[^/]+/[^/]+/(.*)$")]
    or (
      item_type == "id"
      and (
        string.match(url, "/DownloadDialog%.aspx")
        or string.match(url, "^https://sws%.update%.microsoft%.com/[^/]+/[^/]+%.asmx$")
        or string.match(url, "^https://sws%.update%.microsoft%.com/[^/]+/[^/]+%.asmx%?op=[0-9a-zA-Z]+[&]?.*$")
        or string.match(url, "^https://www%.microsoft%.com/en%-us/wdsi/definitions/antimalware%-definition%-release%-notes%?requestVersion=[0-9]+%.[0-9]+%.[0-9]+%.[0-9]+$")
      )
    )
    or (
      item_type == "dlc"
      and string.match(url, "^https?://www%.microsoft%.com/[0-9a-z%-]+/download/details%.aspx%?id=" .. item_value .. "$")
    ) then
    return true
  end

  if item_type == "dlc"
    and string.match(url, "^https?://download%.microsoft%.com/.+$") then
    discover_item(discovered_binaries, "binurl::" .. percent_encode_url(string.gsub(url, "^http://", "https://")))
    return false
  end

  if not string.match(url, "^https?://[^/]*update%.microsoft%.com/")
    and not string.match(url, "^https?://[^/]*download%.windowsupdate%.com/") then
    discover_item(discovered_outlinks, string.match(percent_encode_url(url), "^([^%s]+)"))
    return false
  end

  for _, pattern in pairs({
    "([0-9a-fA-F%-]+)",
    "([^%?=&;]+)"
  }) do
    for s in string.gmatch(url, pattern) do
      if ids[string.lower(s)] then
        return true
      end
    end
  end

  return false
end

wget.callbacks.download_child_p = function(urlpos, parent, depth, start_url_parsed, iri, verdict, reason)
  local url = urlpos["url"]["url"]
  local html = urlpos["link_expect_html"]

  --[[if allowed(url, parent["url"])
    and not processed(url)
    and string.match(url, "^https://")
    and not addedtolist[url] then
    addedtolist[url] = true
    return true
  end]]

  return false
end

decode_codepoint = function(newurl)
  newurl = string.gsub(
    newurl, "\\[uU]([0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F])",
    function (s)
      return utf8.char(tonumber(s, 16))
    end
  )
  return newurl
end

percent_encode_url = function(newurl)
  result = string.gsub(
    newurl, "(.)",
    function (s)
      local b = string.byte(s)
      if b <= 32 or b > 126 then
        return string.format("%%%02X", b)
      end
      return s
    end
  )
  return result
end

wget.callbacks.get_urls = function(file, url, is_css, iri)
  local urls = {}
  local html = nil
  local json = nil

  local post_data = nil
  local soap_action = nil
  local software_distribution = "http://www.microsoft.com/SoftwareDistribution"
  local server_sync_url = "https://sws.update.microsoft.com/ServerSyncWebService/ServerSyncWebService.asmx"
  local protocol_version = "1.21"

  downloaded[url] = true

  if abortgrab then
    return {}
  end

  local function fix_case(newurl)
    if not newurl then
      newurl = ""
    end
    if not string.match(newurl, "^https?://[^/]") then
      return newurl
    end
    if string.match(newurl, "^https?://[^/]+$") then
      newurl = newurl .. "/"
    end
    local a, b = string.match(newurl, "^(https?://[^/]+/)(.*)$")
    return string.lower(a) .. b
  end

  local function check(newurl)
    if not string.match(newurl, "^https?://") then
      return nil
    end
    if not newurl then
      newurl = ""
    end
    newurl = decode_codepoint(newurl)
    newurl = fix_case(newurl)
    local origurl = url
    if string.len(url) == 0
      or string.len(newurl) == 0 then
      return nil
    end
    local url = string.match(newurl, "^([^#]+)")
    local url_ = string.match(url, "^(.-)[%.\\]*$")
    while string.find(url_, "&amp;") do
      url_ = string.gsub(url_, "&amp;", "&")
    end
    local request_id = url_ .. (post_data or "")
    if not processed(request_id)
      and allowed(url_, origurl) then
      local headers = {}
      if string.match(url_, "/DownloadDialog%.aspx") then
        if not post_data then
          return nil
        end
        headers["Content-Type"] = "application/x-www-form-urlencoded"
        table.insert(urls, {
          url=url_,
          headers=headers,
          body_data=post_data,
          method="POST"
        })
      elseif soap_action then
        headers["Content-Type"] = "text/xml; charset=utf-8"
        headers["SOAPAction"] = "\"" .. soap_action .. "\""
        table.insert(urls, {
          url=url_,
          headers=headers,
          body_data=post_data,
          method="POST"
        })
      elseif post_data then
        error("Did not expect post data.")
      else
        table.insert(urls, {
          url=url_,
          headers=headers
        })
      end
      addedtolist[request_id] = true
      addedtolist[url] = true
    end
  end

  local function checknewurl(newurl)
    if not newurl then
      newurl = ""
    end
    newurl = decode_codepoint(newurl)
    if string.match(newurl, "['\"><]") then
      return nil
    end
    if string.match(newurl, "^https?:////") then
      check(string.gsub(newurl, ":////", "://"))
    elseif string.match(newurl, "^https?://") then
      check(newurl)
    elseif string.match(newurl, "^https?:\\/\\?/") then
      check(string.gsub(newurl, "\\", ""))
    elseif string.match(newurl, "^\\/\\/") then
      checknewurl(string.gsub(newurl, "\\", ""))
    elseif string.match(newurl, "^//") then
      check(urlparse.absolute(url, newurl))
    elseif string.match(newurl, "^\\/") then
      checknewurl(string.gsub(newurl, "\\", ""))
    elseif string.match(newurl, "^/") then
      check(urlparse.absolute(url, newurl))
    elseif string.match(newurl, "^%.%./") then
      if string.match(url, "^https?://[^/]+/[^/]+/") then
        check(urlparse.absolute(url, newurl))
      else
        checknewurl(string.match(newurl, "^%.%.(/.+)$"))
      end
    elseif string.match(newurl, "^%./") then
      check(urlparse.absolute(url, newurl))
    end
  end

  local function checknewshorturl(newurl)
    if not newurl then
      newurl = ""
    end
    newurl = decode_codepoint(newurl)
    if string.match(newurl, "^%?") then
      check(urlparse.absolute(url, newurl))
    elseif not (
      string.match(newurl, "^https?:\\?/\\?//?/?")
      or string.match(newurl, "^[/\\]")
      or string.match(newurl, "^%./")
      or string.match(newurl, "^[jJ]ava[sS]cript:")
      or string.match(newurl, "^[mM]ail[tT]o:")
      or string.match(newurl, "^vine:")
      or string.match(newurl, "^android%-app:")
      or string.match(newurl, "^ios%-app:")
      or string.match(newurl, "^data:")
      or string.match(newurl, "^irc:")
      or string.match(newurl, "^%${")
    ) then
      check(urlparse.absolute(url, newurl))
    end
  end

  local function set_new_params(newurl, data)
    for param, value in pairs(data) do
      if value == nil then
        value = ""
      elseif type(value) == "string" then
        value = "=" .. value
      end
      if string.match(newurl, "[%?&]" .. param .. "[=&]") then
        newurl = string.gsub(newurl, "([%?&]" .. param .. ")=?[^%?&;]*", "%1" .. value)
      else
        if string.match(newurl, "%?") then
          newurl = newurl .. "&"
        else
          newurl = newurl .. "?"
        end
        newurl = newurl .. param .. value
      end
    end
    return newurl
  end

  local function increment_param(newurl, param, default, step)
    local value = string.match(newurl, "[%?&]" .. param .. "=([0-9]+)")
    if value then
      value = tonumber(value)
      value = value + step
      return set_new_params(newurl, {[param]=tostring(value)})
    else
      if default ~= nil then
        default = tostring(default)
      end
      return set_new_params(newurl, {[param]=default})
    end
  end

  local function get_count(data)
    local count = 0
    for _ in pairs(data) do
      count = count + 1
    end
    return count
  end

  local function check_soap(newurl, action, data, params, params_only)
    soap_action = action
    post_data = "<?xml version=\"1.0\" encoding=\"utf-8\"?>"
      .. "<soap:Envelope xmlns:soap=\"http://schemas.xmlsoap.org/soap/envelope/\">"
        .. "<soap:Body>" .. data .. "</soap:Body>"
      .. "</soap:Envelope>"
    local query_url = newurl .. "?op=" .. string.match(action, "([^/]+)$")
    if not params_only then
      check(newurl)
      if not params then
        check(query_url)
      end
    end
    if type(params) == "string" then
      params = {params}
    end
    if params then
      for _, value in ipairs(params) do
        check(query_url .. "&" .. value)
      end
    end
    post_data = nil
    soap_action = nil
  end

  local function update_identity(revision)
    return "<UpdateIdentity>"
        .. "<UpdateID>" .. item_value .. "</UpdateID>"
        .. "<RevisionNumber>" .. revision .. "</RevisionNumber>"
      .. "</UpdateIdentity>"
  end

  local function discover_binary(digest, newurl)
    if item_type == "id"
      and context["encrypted"]
      and context["encrypted"][digest]
      and not context["decryption"][digest] then
      context["todo_binaries"][digest .. ":" .. newurl] = {digest, newurl}
      return
    end
    local b32digest = ""
    if digest then
      b32digest = basexx.to_base32(base64.decode(digest))
    end
    newurl = string.gsub(newurl, "^(https?://)www%.", "%1")
    local domain, path = string.match(newurl, "^https?://([^/]+)/(.+)$")
    if domain == "catalog.sf.dl.delivery.mp.microsoft.com"
      or domain == "download.microsoft.com" then
      discover_item(discovered_binaries, "binurl:" .. b32digest .. ":" .. percent_encode_url(string.gsub(newurl, "^http://", "https://")))
    elseif domain == "catalog.s.download.windowsupdate.com"
      or domain == "download.windowsupdate.com"
      or domain == "b1.download.windowsupdate.com"
      or domain == "au.download.windowsupdate.com"
      or domain == "au.b1.download.windowsupdate.com" then
      path = string.match(path, "^[cd]/(.+)$") or path
      discover_item(discovered_binaries, "bin:" .. b32digest .. ":" .. path)
    else
      error("Found unexpected address " .. domain .. ".")
    end
    context["download_found"] = true
  end

  if item_type == "bin" then
    for _, domain in pairs({
      "https://catalog.s.download.windowsupdate.com/",
      "http://download.windowsupdate.com/",
      "http://b1.download.windowsupdate.com/",
      "http://au.download.windowsupdate.com/",
      "http://au.b1.download.windowsupdate.com/"
    }) do
      for _, path in pairs({"", "c/", "d/"}) do
        check(domain .. path .. item_value)
      end
    end
  end

  if allowed(url)
    and (
      status_code < 300
      or (
        status_code == 500
        and string.match(url, "[%?&]revisionstart=[0-9]+&revisionend=[0-9]+")
      )
    )
    and not is_binary_item(item_type) then
    html = read_file(file)
    if string.match(url, "^https://www%.microsoft%.com/en%-us/wdsi/definitions/antimalware%-definition%-release%-notes%?requestVersion=") then
      local requested = string.match(url, "requestVersion=([0-9]+%.[0-9]+%.[0-9]+%.[0-9]+)$")
      local returned = string.match(html, "<snap id=\"titleVersion\">([0-9]+%.[0-9]+%.[0-9]+%.[0-9]+)</snap>")
      if returned ~= requested then
        error("Response has wrong version " .. tostring(returned) .. " for " .. requested .. ".")
      end
      return urls
    end
    if string.match(url, "/ScopedViewRedirect%.aspx%?updateid=") then
      check_soap(
        server_sync_url,
        software_distribution .. "/GetAuthConfig",
        "<GetAuthConfig xmlns=\"" .. software_distribution .. "\" />"
      )
    end
    if string.match(url, "/ScopedViewInline%.aspx%?updateid=") then
      post_data = "updateIDs=%5B%7B%22size%22%3A0%2C%22languages%22%3A%22%22%2C%22uidInfo%22%3A%22" .. item_value .. "%22%2C%22updateID%22%3A%22" .. item_value .. "%22%7D%5D"
        .. "&updateIDsBlockedForImport="
        .. "&wsusApiPresent="
        .. "&contentImport="
        .. "&sku="
        .. "&serverName="
        .. "&ssl="
        .. "&portNumber="
        .. "&version="
      for _, params in pairs({
        "",
        "?updateid=" .. item_value,
        "?scopedview=true",
        "?updateid=" .. item_value .. "&scopedview=true"
      }) do
        check("https://www.catalog.update.microsoft.com/DownloadDialog.aspx" .. params)
      end
      post_data = nil
      for _, endpoint in pairs({
        "ViewBasket.aspx?updateids=",
        "ScopedView.aspx?updateid=",
        "ScopedViewBasic.aspx?updateid=",
        "ScopedViewGeneric.aspx?updateid="
      }) do
        check("https://www.catalog.update.microsoft.com/" .. endpoint .. item_value)
      end
    end
    if string.match(url, "/DownloadDialog%.aspx") then
      for download_information in string.gmatch(html, "downloadInformation%[([0-9]+)%]%s*=") do
        if download_information ~= "0" then
          error("Unexpected downloadInformation ID " .. download_information .. ".")
        end
        local base_s = "downloadInformation%[" .. download_information .. "%]%.files%["
        local max_num = -1
        local count = 0
        local files = {}
        for files_id in string.gmatch(html, base_s .. "([0-9]+)%]%s*=") do
          local num = tonumber(files_id)
          if num > max_num then
            max_num = num
          end
          local file_data = {}
          for k, v in string.gmatch(html, base_s .. files_id .. "%]%.([0-9a-zA-Z]+)%s*=%s*(.-);\r?\n") do
            local temp = string.match(v, "^'(.*)'$")
            if temp then
              v = temp
            end
            file_data[k] = v
          end
          files[files_id] = file_data
          count = count + 1
        end
        if max_num + 1 ~= count then
          error("Got incorrect file count.")
        end
        for _, file_data in pairs(files) do
          discover_binary(file_data["digest"], file_data["url"])
        end
      end
    end
    if string.match(url, "^https://sws%.update%.microsoft%.com/") then
      local revision_start, revision_end = string.match(url, "[%?&]revisionstart=([0-9]+)&revisionend=([0-9]+)")
      if revision_start then
        revision_start = tonumber(revision_start)
        revision_end = tonumber(revision_end)
        local revisions = {}
        local expected = revision_end - revision_start + 1
        local requested = expected
        local returned = expected
        local removed = 0
        for revision = revision_start, revision_end do
          revisions[revision] = true
        end
        if status_code == 500 then
          local message = html_entities.decode(string.match(html, "<Message>(.-)</Message>"))
          local missing = nil
          requested, returned, removed, missing = string.match(
            message,
            "Requested ([0-9]+) returned ([0-9]+) %(test content removed: ([0-9]+)%)%. Missing Revisions: (.+)"
          )
          requested = tonumber(requested)
          returned = tonumber(returned)
          removed = tonumber(removed)
          for updateid, revision in string.gmatch(missing, "([0-9a-fA-F%-]+)%.([0-9]+)") do
            if string.lower(updateid) == item_value then
              revisions[tonumber(revision)] = false
            end
          end
        end
        local count = 0
        for revision = revision_start, revision_end do
          if revisions[revision] then
            count = count + 1
          end
        end
        if requested ~= expected
          or returned ~= count
          or removed ~= 0 then
          error("Incorrect revision check response.")
        end
        for revision = revision_start, revision_end do
          if revisions[revision] then
            discover_item(discovered_updateids, "id:" .. item_value .. ":" .. revision)
          end
        end
        context["revision_checks"] = context["revision_checks"] + 1
        return urls
      elseif string.match(url, "[%?&]op=") then
        return urls
      end
      html = string.gsub(
        html,
        "<[0-9a-zA-Z_%-]*:?XmlUpdateBlobCompressed>(.-)</[0-9a-zA-Z_%-]*:?XmlUpdateBlobCompressed>",
        function(compressed)
          local filename = item_dir .. "/" .. warc_file_base .. "_metadata.cab"
          local file = assert(io.open(filename, "wb"))
          file:write(base64.decode(compressed))
          file:close()
          local process = assert(io.popen("cabextract -q -p " .. filename))
          local metadata = process:read("*all")
          local success = process:close()
          os.remove(filename)
          if not success or string.len(metadata) == 0 then
            error("Could not decompress XmlUpdateBlob.")
          end
          if string.byte(metadata, 2) == 0 and string.byte(metadata, 4) == 0 then
            metadata = assert(iconv.new("UTF-8", "UTF-16LE"):iconv(metadata))
          end
          for _, escape in ipairs({
            {"&", "&amp;"},
            {"<", "&lt;"},
            {">", "&gt;"}
          }) do
            metadata = string.gsub(metadata, escape[1], escape[2])
          end
          return "<XmlUpdateBlob>" .. metadata .. "</XmlUpdateBlob>"
        end
      )
      if string.match(html, "<GetAuthConfigResponse") then
        local dss_auth = software_distribution .. "/Server/DssAuthWebService"
        check_soap(
          "https://sws.update.microsoft.com/DssAuthWebService/DssAuthWebService.asmx",
          dss_auth .. "/GetAuthorizationCookie",
          "<GetAuthorizationCookie xmlns=\"" .. dss_auth .. "\">"
            .. "<accountName>wsus.contoso.com</accountName>"
            .. "<accountGuid>" .. uuid() .. "</accountGuid>"
          .. "</GetAuthorizationCookie>"
        )
      elseif string.match(html, "<GetAuthorizationCookieResponse") then
        local plugin_id = html_entities.decode(string.match(html, "<PlugInId>(.-)</PlugInId>"))
        local cookie_data = html_entities.decode(string.match(html, "<CookieData>(.-)</CookieData>"))
        check_soap(
          server_sync_url,
          software_distribution .. "/GetCookie",
          "<GetCookie xmlns=\"" .. software_distribution .. "\">"
            .. "<authCookies>"
              .. "<AuthorizationCookie>"
                .. "<PlugInId>" .. plugin_id .. "</PlugInId>"
                .. "<CookieData>" .. cookie_data .. "</CookieData>"
              .. "</AuthorizationCookie>"
            .. "</authCookies>"
            .. "<protocolVersion>" .. protocol_version .. "</protocolVersion>"
          .. "</GetCookie>"
        )
      elseif string.match(html, "<GetCookieResponse") then
        local expiration = html_entities.decode(string.match(html, "<Expiration>(.-)</Expiration>"))
        local encrypted_data = html_entities.decode(string.match(html, "<EncryptedData>(.-)</EncryptedData>"))
        context["wsus_cookie"] = "<cookie>"
            .. "<Expiration>" .. expiration .. "</Expiration>"
            .. "<EncryptedData>" .. encrypted_data .. "</EncryptedData>"
          .. "</cookie>"
        check_soap(
          server_sync_url,
          software_distribution .. "/GetConfigData",
          "<GetConfigData xmlns=\"" .. software_distribution .. "\">"
            .. context["wsus_cookie"]
          .. "</GetConfigData>"
        )
      elseif string.match(html, "<GetConfigDataResponse") then
        if string.match(html, "<ProtocolVersion>(.-)</ProtocolVersion>") ~= protocol_version then
          error("Found higher protocol version.")
        end
        check_soap(
          server_sync_url,
          software_distribution .. "/GetRelatedRevisionsForUpdates",
          "<GetRelatedRevisionsForUpdates xmlns=\"" .. software_distribution .. "\">"
            .. context["wsus_cookie"]
            .. "<updateIDs>"
              .. "<guid>" .. item_value .. "</guid>"
            .. "</updateIDs>"
          .. "</GetRelatedRevisionsForUpdates>",
          "updateid=" .. item_value
        )
      elseif string.match(html, "<GetRelatedRevisionsForUpdatesResponse") then
        for updateid, revision in string.gmatch(
          html,
          "<UpdateIdentity>%s*"
            .. "<UpdateID>([0-9a-fA-F%-]+)</UpdateID>%s*"
            .. "<RevisionNumber>([0-9]+)</RevisionNumber>%s*"
          .. "</UpdateIdentity>"
        ) do
          updateid = string.lower(updateid)
          if updateid == item_value then
            if not context["revision_item"] then
              context["revision"] = revision
              discover_item(discovered_updateids, "id:" .. updateid .. ":" .. revision)
            end
          elseif string.match(updateid, "^[0-9a-f%-]+$") then
            discover_item(discovered_updateids, "id:" .. updateid)
            discover_item(discovered_updateids, "id:" .. updateid .. ":" .. revision)
          end
        end
        if context["revision"] then
          check_soap(
            server_sync_url,
            software_distribution .. "/GetUpdateData",
            "<GetUpdateData xmlns=\"" .. software_distribution .. "\">"
              .. context["wsus_cookie"]
              .. "<updateIds>" .. update_identity(context["revision"]) .. "</updateIds>"
            .. "</GetUpdateData>",
            {
              "updateid=" .. item_value .. "&revisionnumber=" .. context["revision"],
              "updateid=" .. item_value
            }
          )
        else
          check_soap(
            server_sync_url,
            software_distribution .. "/GetDriverSetData",
            "<GetDriverSetData xmlns=\"" .. software_distribution .. "\">"
              .. context["wsus_cookie"]
              .. "<driverSets>"
                .. "<guid>" .. item_value .. "</guid>"
              .. "</driverSets>"
            .. "</GetDriverSetData>",
            "driversetid=" .. item_value
          )
        end
      elseif string.match(html, "<GetDriverSetDataResponse") then
        for data in string.gmatch(html, "<ServerSyncDriverSetData>(.-)</ServerSyncDriverSetData>") do
          local driver_set_id = string.lower(html_entities.decode(string.match(data, "<DriverSetId>(.-)</DriverSetId>")))
          if driver_set_id ~= item_value then
            error("Found unexpected driver set.")
          end
          context["driver_set_seen"] = true
          local driver_set = html_entities.decode(string.match(data, "<DriverSetXml>(.-)</DriverSetXml>"))
          for _, pattern in ipairs({
            "UpdateID%s*=%s*\"([0-9a-fA-F%-]+)\"",
            "<UpdateID>%s*([0-9a-fA-F%-]+)%s*</UpdateID>"
          }) do
            for updateid in string.gmatch(driver_set, pattern) do
              discover_item(discovered_updateids, "id:" .. string.lower(updateid))
            end
          end
        end
        if not context["driver_set_seen"] and not context["download_found"] then
          abort_item()
        end
      elseif string.match(html, "<GetUpdateDataResponse") then
        local is_product = false
        local metadata_has_files = false
        local secured = false
        for data in string.gmatch(html, "<ServerSyncUpdateData>(.-)</ServerSyncUpdateData>") do
          local updateid, revision = string.match(
            data,
            "<Id>%s*"
              .. "<UpdateID>([0-9a-fA-F%-]+)</UpdateID>%s*"
              .. "<RevisionNumber>([0-9]+)</RevisionNumber>%s*"
            .. "</Id>"
          )
          if updateid then
            updateid = string.lower(updateid)
          end
          if updateid == item_value
            and revision == context["revision"] then
            context["metadata_seen"] = true
            metadata_has_files = string.match(data, "<FileDigestList>") ~= nil
            local decoded = html_entities.decode(data)
            local bundle = string.gsub(
              updateid,
              "^([0-9]+%-[0-9]+)%-[0-9]+%-00[36][24]%-([0-9]+)[0-9][0-9]$",
              "%1-0001-0000-%200"
            )
            if bundle ~= updateid then
              discover_item(discovered_updateids, "id:" .. bundle)
              discover_item(discovered_updateids, "id:" .. bundle .. ":" .. revision)
            end
            local definition_version = string.match(decoded, "Microsoft Endpoint Protection %- KB2461484.-([0-9]+%.[0-9]+%.[0-9]+%.[0-9]+)")
            if definition_version then
              check("https://www.microsoft.com/en-us/wdsi/definitions/antimalware-definition-release-notes?requestVersion=" .. definition_version)
            end
            if string.match(decoded, "UpdateType%s*=%s*\"Category\"") then
              local category_type = string.match(decoded, "CategoryType%s*=%s*\"([a-zA-Z]+)\"")
              if category_type == "Product" then
                is_product = true
              end
              if category_type == "Product"
                or category_type == "ProductFamily"
                or category_type == "UpdateClassification"
                or category_type == "Company" then
                discover_item(discovered_periodic, "id:" .. updateid)
              end
              if category_type == "UpdateClassification" then
                discover_item(discovered_classifications, "id:" .. updateid)
              end
            end
            secured = string.match(decoded, "SecuredFragment%s*=%s*\"FileDecryption\"") ~= nil
              or string.match(decoded, "<[0-9a-zA-Z_%-]*:?SecuredFragment>%s*FileDecryption%s*</[0-9a-zA-Z_%-]*:?SecuredFragment>") ~= nil
            for attributes in string.gmatch(decoded, "<[0-9a-zA-Z_%-]*:?File%s+([^>]+)>") do
              if string.match(attributes, "IsEncrypted%s*=%s*\"true\"") then
                local digest = string.match(attributes, "Digest%s*=%s*\"([^\"]+)\"")
                if not digest then
                  error("Did not find digest for encrypted file.")
                end
                context["encrypted"][digest] = true
              end
            end
            for related in string.gmatch(decoded, "UpdateID%s*=%s*\"([0-9a-fA-F%-]+)\"") do
              related = string.lower(related)
              if related ~= item_value then
                discover_item(discovered_updateids, "id:" .. related)
              end
            end
          elseif updateid then
            discover_item(discovered_updateids, "id:" .. updateid)
            discover_item(discovered_updateids, "id:" .. updateid .. ":" .. revision)
          end
        end
        if not context["metadata_seen"] then
          error("Did not find expected metadata.")
        end
        if secured and get_count(context["encrypted"]) == 0 then
          error("Did not find encrypted files.")
        end
        local metadata_url_found = false
        for data in string.gmatch(html, "<ServerSyncUrlData>(.-)</ServerSyncUrlData>") do
          local newurl = string.match(data, "<MUUrl>(.-)</MUUrl>")
          if newurl then
            local digest = html_entities.decode(string.match(data, "<FileDigest>(.-)</FileDigest>"))
            metadata_url_found = true
            discover_binary(digest, html_entities.decode(newurl))
          end
        end
        if metadata_has_files and not metadata_url_found then
          error("Did not find a metadata file download.")
        end
        if not context["revision_item"] then
          local revision = tonumber(context["revision"])
          for revision_start = 0, math.max(200, math.floor(revision / 100) * 100), 100 do
            local revision_end = revision_start + 99
            if revision_start == 0 then
              revision_start = 1
            end
            local update_ids = ""
            for value = revision_start, revision_end do
              update_ids = update_ids .. update_identity(value)
            end
            check_soap(
              server_sync_url,
              software_distribution .. "/GetUpdateData",
              "<GetUpdateData xmlns=\"" .. software_distribution .. "\">"
                .. context["wsus_cookie"]
                .. "<updateIds>" .. update_ids .. "</updateIds>"
              .. "</GetUpdateData>",
              "updateid=" .. item_value .. "&revisionstart=" .. revision_start .. "&revisionend=" .. revision_end,
              true
            )
          end
        end
        if get_count(context["encrypted"]) > 0 then
          check_soap(
            server_sync_url,
            software_distribution .. "/GetUpdateDecryptionData",
            "<GetUpdateDecryptionData xmlns=\"" .. software_distribution .. "\">"
              .. context["wsus_cookie"]
              .. "<updateIds>" .. update_identity(context["revision"]) .. "</updateIds>"
            .. "</GetUpdateDecryptionData>",
            {
              "updateid=" .. item_value .. "&revisionnumber=" .. context["revision"],
              "updateid=" .. item_value
            }
          )
        end
        if is_product then
          local classifications = ""
          for _, classification in ipairs({
            "0fa1201d-4330-4fa8-8ae9-b877473b6441", -- Security Updates
            "28bc880e-0592-4cbf-8f95-c79b17911d5f", -- Update Rollups
            "3689bdc8-b205-4af4-8d4a-a63924c5e9d5", -- Upgrades
            "68c5b0a3-d1a6-4553-ae49-01d3a7827828", -- Service Packs
            "b4832bd8-e735-4761-8daf-37f882276dab", -- Tools
            "b54e7d24-7add-428f-8b75-90a396fa584f", -- Feature Packs
            "cd5ffd1e-e932-4e3a-bf74-18bf0b1bbd83", -- Updates
            "e0789628-ce08-4437-be74-2495b842f43b", -- Definition Updates
            "e6cf1350-c01b-414d-a61f-263d14d133b4", -- Critical Updates
            "ebfc1fc5-71a4-4f7b-9aca-3b9a503104a0", -- Drivers
            "5c9376ab-8ce6-464a-b136-22113dd69801", -- Applications (old)
            "434de588-ed14-48f5-8eed-a15e09a991f6", -- Connectors (old)
            "e140075d-8433-45c3-ad87-e72345b36078", -- Developer Kits (old)
            "9511d615-35b2-47bb-927f-f73d8e9260bb" -- Guidance (old)
          }) do
            classifications = classifications
              .. "<IdAndDelta>"
                .. "<Id>" .. classification .. "</Id>"
                .. "<Delta>false</Delta>"
              .. "</IdAndDelta>"
          end
          check_soap(
            server_sync_url,
            software_distribution .. "/GetRevisionIdList",
            "<GetRevisionIdList xmlns=\"" .. software_distribution .. "\">"
              .. context["wsus_cookie"]
              .. "<filter>"
                .. "<GetConfig>false</GetConfig>"
                .. "<Get63LanguageOnly>false</Get63LanguageOnly>"
                .. "<Categories>"
                  .. "<IdAndDelta>"
                    .. "<Id>" .. item_value .. "</Id>"
                    .. "<Delta>false</Delta>"
                  .. "</IdAndDelta>"
                .. "</Categories>"
                .. "<Classifications>" .. classifications .. "</Classifications>"
              .. "</filter>"
            .. "</GetRevisionIdList>",
            "categoryid=" .. item_value
          )
        end
        local inline_url = "https://www.catalog.update.microsoft.com/ScopedViewInline.aspx?updateid=" .. item_value
        ids[inline_url] = true
        check(inline_url)
      elseif string.match(html, "<GetRevisionIdListResponse") then
        for updateid, revision in string.gmatch(
          html,
          "<UpdateIdentity>%s*"
            .. "<UpdateID>([0-9a-fA-F%-]+)</UpdateID>%s*"
            .. "<RevisionNumber>([0-9]+)</RevisionNumber>%s*"
          .. "</UpdateIdentity>"
        ) do
          updateid = string.lower(updateid)
          discover_item(discovered_updateids, "id:" .. updateid)
          discover_item(discovered_updateids, "id:" .. updateid .. ":" .. revision)
        end
      elseif string.match(html, "<GetUpdateDecryptionDataResponse") then
        local updateid, revision = string.match(
          html,
          "<UpdateId>%s*"
            .. "<UpdateID>([0-9a-fA-F%-]+)</UpdateID>%s*"
            .. "<RevisionNumber>([0-9]+)</RevisionNumber>%s*"
          .. "</UpdateId>"
        )
        if not updateid
          or string.lower(updateid) ~= item_value
          or revision ~= context["revision"] then
          error("Did not find expected decryption data.")
        end
        for data in string.gmatch(html, "<ServerSyncFileDecryption>(.-)</ServerSyncFileDecryption>") do
          local key = string.match(data, "<DecryptionKey>(.-)</DecryptionKey>")
          if key then
            if string.len(key) % 4 ~= 0
              or not string.match(key, "^[0-9a-zA-Z+/]+=?=?$") then
              error("Found invalid decryption key.")
            end
            local digest = html_entities.decode(string.match(data, "<FileDigest>(.-)</FileDigest>"))
            context["decryption"][digest] = true
          end
        end
        local missing = false
        for digest in pairs(context["encrypted"]) do
          if not context["decryption"][digest] then
            error("Did not find all decryption keys.")
          end
        end
        for _, binary in pairs(context["todo_binaries"]) do
          discover_binary(binary[1], binary[2])
        end
        context["todo_binaries"] = {}
      else
        error("Unexpected response.")
      end
      return urls
    end
    if item_type == "id" then
      for updateid in string.gmatch(html, "ScopedView[a-zA-Z]*%.aspx%?updateid=([0-9a-fA-F%-]+)") do
        updateid = string.lower(updateid)
        if updateid ~= item_value then
          discover_item(discovered_updateids, "id:" .. updateid)
        end
      end
    end
    if string.match(url, "^https?://www%.microsoft%.com/[0-9a-z%-]+/download/details%.aspx%?id=") then
      json = string.match(html, "window%.__DLCDetails__=(.-)</script>")
      if not json then
        error("Did not find DLC details.")
      end
      local details = cjson.decode(json)["dlcDetailsView"]
      if details["detailsId"] ~= item_value then
        error("Found incorrect DLC ID.")
      end
      local found = false
      for _, file_data in pairs(details["downloadFile"]) do
        discover_binary(nil, file_data["url"])
        found = true
      end
      if not found then
        error("Did not find any download.")
      end
      for _, locale in pairs(details["localeDropdown"]) do
        check("https://www.microsoft.com/" .. locale["cultureCode"] .. "/download/details.aspx?id=" .. item_value)
      end
    end
    if string.match(url, "/Search%.aspx%?q=") then
      local found = 0
      for updateid in string.gmatch(html, "goToDetails%(\"([0-9a-f%-]+)\"%);") do
        discover_item(discovered_updateids, "id:" .. updateid)
        found = found + 1
      end
      if found == 0
        and not string.match(html, "We did not find") then
        error("Found no IDs, but also not message saying there aren't any.")
      end
      if item_type == "uuid-search"
        and (
          string.match(html, " of 1000 ")
          or string.match(html, "To narrow your search")
          or string.match(html, "Only the first [0-9]+ are returned%.")
        )
        and string.len(context["star_term"]) < 6 then
        for char in string.gmatch("0123456789abcdef", "(.)") do
          discover_item(discovered_items, item_type .. ":" .. context["star_term"] .. char .. ":" .. context["search_term"])
        end
      end
      local pages = string.match(html, "%(page [0-9]+ of ([0-9]+)%)")
      if pages then
        pages = tonumber(pages)
        if pages > 40 then
          error("Did not expect more than 40 pages.")
        end
        for i = 0, pages - 1 do
          check(set_new_params(url, {["p"]=tostring(i)}))
        end
      end
    end
    for newurl in string.gmatch(string.gsub(html, "&quot;", "\""), "([^\"]+)") do
      checknewurl(newurl)
    end
    for newurl in string.gmatch(string.gsub(html, "&#039;", "'"), "([^']+)") do
      checknewurl(newurl)
    end
    for newurl in string.gmatch(html, "[^%-]href='([^']+)'") do
      checknewshorturl(newurl)
    end
    for newurl in string.gmatch(html, "[^%-]href=\"([^\"]+)\"") do
      checknewshorturl(newurl)
    end
    for newurl in string.gmatch(html, ":%s*url%(([^%)]+)%)") do
      checknewurl(newurl)
    end
    html = string.gsub(html, "&gt;", ">")
    html = string.gsub(html, "&lt;", "<")
    for newurl in string.gmatch(html, ">%s*([^<%s]+)") do
      checknewurl(newurl)
    end
  end

  return urls
end

wget.callbacks.dedup_response = function(url, digest)
  if is_binary_item(item_type) then
    local b32digest = b32digests[item_value]
    if b32digest == "" then
      b32digest = context["digest"]
    end
    local matching = digest == "sha1:" .. b32digest
    if context["matches"][url] == 404 then
      matching = nil
    end
    context["matches"][url] = matching
  end
end

wget.callbacks.write_to_warc = function(url, http_stat)
  status_code = http_stat["statcode"]
  set_item(url["url"])
  url_count = url_count + 1
  io.stdout:write(url_count .. "=" .. status_code .. " " .. url["url"] .. " \n")
  io.stdout:flush()
  logged_response = true
  if not item_name then
    error("No item name found.")
  end
  is_initial_url = false
  if is_binary_item(item_type)
    and http_stat["statcode"] == 404 then
    context["matches"][url["url"]] = 404
  end
  if http_stat["statcode"] == 404
    and item_type == "id"
    and string.match(url["url"], "[%?&]revisionstart=[0-9]+&revisionend=[0-9]+") then
    retry_url = true
    return false
  end
  if http_stat["statcode"] ~= 200
    and http_stat["statcode"] ~= 404
    and not (
      item_type == "id"
      and (
        (
          http_stat["statcode"] == 500
          and string.match(url["url"], "[%?&]revisionstart=[0-9]+&revisionend=[0-9]+")
        )
        or (
          http_stat["statcode"] == 302
          and context["metadata_seen"]
          and (
            string.match(url["url"], "/ScopedView[A-Za-z]*%.aspx%?updateid=")
            or string.match(url["url"], "/DownloadDialog%.aspx")
          )
        )
      )
    ) then
    retry_url = true
    return false
  end
  if http_stat["len"] == 0
    and http_stat["statcode"] < 300
    and not string.match(url["url"], "/ScopedViewRedirect%.aspx%?updateid=") then
    retry_url = true
    return false
  end
  if abortgrab then
    print("Not writing to WARC.")
    return false
  end
  if is_binary_item(item_type)
    and http_stat["statcode"] == 200 then
    local digest = openssl_digest.new("sha1")
    local file = assert(io.open(http_stat["local_file"], "rb"))
    while true do
      local data = file:read(1024 * 1024)
      if not data then
        break
      end
      digest:update(data)
    end
    file:close()
    local b32digest = basexx.to_base32(digest:final())
    local expected_digest = b32digests[item_value]
    if expected_digest == "" and context["digest_checked"] then
      expected_digest = context["digest"]
    end
    if expected_digest == "" then
      if not context["digest"] then
        context["digest"] = b32digest
        retry_url = true
        return false
      elseif context["digest"] ~= b32digest then
        error("Second download did not match previous digest.")
      end
      context["digest_checked"] = true
      context["matches"][url["url"]] = true
    else
      local matching = b32digest == expected_digest
      context["matches"][url["url"]] = matching
      if not matching then
        if not context["retried"][url["url"]] then
          context["retried"][url["url"]] = true
          retry_url = true
          return false
        end
      end
    end
  end
  retry_url = false
  tries = 0
  return true
end

wget.callbacks.httploop_result = function(url, err, http_stat)
  status_code = http_stat["statcode"]

  if not logged_response then
    url_count = url_count + 1
    io.stdout:write(url_count .. "=" .. status_code .. " " .. url["url"] .. " \n")
    io.stdout:flush()
  end
  logged_response = false

  if killgrab then
    return wget.actions.ABORT
  end

  set_item(url["url"])
  if not item_name then
    error("No item name found.")
  end

  if abortgrab then
    abort_item()
    return wget.actions.EXIT
  end

  if status_code == 0 or retry_url then
    io.stdout:write("Server returned bad response. ")
    io.stdout:flush()
    tries = tries + 1
    local maxtries = 11
    if status_code == 302
      or status_code == 401
      or status_code == 403 then
      tries = maxtries + 1
    end
    if tries > maxtries then
      io.stdout:write(" Skipping.\n")
      io.stdout:flush()
      tries = 0
      abort_item()
      return wget.actions.EXIT
    end
    local sleep_time = math.random(
      math.floor(math.pow(2, tries-0.5)),
      math.floor(math.pow(2, tries))
    )
    io.stdout:write("Sleeping " .. sleep_time .. " seconds.\n")
    io.stdout:flush()
    os.execute("sleep " .. sleep_time)
    return wget.actions.CONTINUE
  else
    if status_code == 200 then
      if not seen_200[url["url"]] then
        seen_200[url["url"]] = 0
      end
      seen_200[url["url"]] = seen_200[url["url"]] + 1
    end
    downloaded[url["url"]] = true
  end

  if status_code >= 300 and status_code <= 399 then
    local newloc = urlparse.absolute(url["url"], http_stat["newloc"])
    if processed(newloc) or not allowed(newloc, url["url"]) then
      tries = 0
      return wget.actions.EXIT
    end
  end

  tries = 0

  return wget.actions.NOTHING
end

wget.callbacks.finish = function(start_time, end_time, wall_time, numurls, total_downloaded_bytes, total_download_time)
  finish_item()
  local function submit_backfeed(items, key)
    local tries = 0
    local maxtries = 5
    while tries < maxtries do
      if killgrab then
        return false
      end
      local body, code, headers, status = http.request(
        "https://legacy-api.arpa.li/backfeed/legacy/" .. key,
        items .. "\0"
      )
      if code == 200 and body ~= nil and cjson.decode(body)["status_code"] == 200 then
        io.stdout:write(string.match(body, "^(.-)%s*$") .. "\n")
        io.stdout:flush()
        return nil
      end
      io.stdout:write("Failed to submit discovered URLs." .. tostring(code) .. tostring(body) .. "\n")
      io.stdout:flush()
      os.execute("sleep " .. math.floor(math.pow(2, tries)))
      tries = tries + 1
    end
    kill_grab()
    error()
  end

  local file = io.open(item_dir .. "/" .. warc_file_base .. "_bad-items.txt", "w")
  for url, _ in pairs(bad_items) do
    file:write(url .. "\n")
  end
  file:close()

  for key, data in pairs({
    ["microsoftupdate-0ht48j5nl9fbsyhs?skipbloom=1"] = discovered_items,
    ["microsoftupdate-stash-binaries-j1vid2nfyvyr87qn?skipbloom=1"] = discovered_binaries,
    ["microsoftupdate-stash-updateids-79v5pmmyyrzolvjt?skipbloom=1"] = discovered_updateids,
    ["microsoftupdate-stash-classifications-h7g4q3w9x2n8c6vk?skipbloom=1"] = discovered_classifications,
    ["microsoftupdate-stash-periodic-3fdbcc9ad6b4efa0?skipbloom=1"] = discovered_periodic,
    ["urls-mkn69fkj7zufcejb"] = discovered_outlinks
  }) do
    print("queuing for", string.match(key, "^(.+)%-"))
    local items = nil
    local count = 0
    for item, _ in pairs(data) do
      print("found item", item)
      if items == nil then
        items = item
      else
        items = items .. "\0" .. item
      end
      count = count + 1
      if count == 1000 then
        submit_backfeed(items, key)
        items = nil
        count = 0
      end
    end
    if items ~= nil then
      submit_backfeed(items, key)
    end
  end
end

wget.callbacks.before_exit = function(exit_status, exit_status_string)
  if killgrab then
    return wget.exits.IO_FAIL
  end
  if abortgrab then
    abort_item()
  end
  return exit_status
end

