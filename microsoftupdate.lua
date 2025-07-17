local urlparse = require("socket.url")
local http = require("socket.http")
local https = require("ssl.https")
local cjson = require("cjson")
local utf8 = require("utf8")
local html_entities = require("htmlEntities")
local base64 = require("base64")
local basexx = require("basexx")

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
  local value = nil
  local type_ = nil
  for pattern, name in pairs({
    ["^https?://www%.catalog%.update%.microsoft%.com/ScopedViewInline%.aspx%?updateid=([0-9a-f%-]+)$"]="id",
    ["^https?://catalog%.s%.download%.windowsupdate%.com/(.+)$"]="bin",
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

finish_item = function()
  if item_type ~= "bin" then
    return true
  end
  local count = 0
  for url, matches in pairs(context["matches"]) do
    if matches ~= 404 then
      if not matches then
        error("Incorrect matching SHA1 found.")
      end
      count = count + 1
    end
  end
  if count ~= 1 then
    error("Incorrect number of matching URLs found.")
  end
  return true
end

set_item = function(url)
  found = find_item(url)
  if found then
    local newcontext = {["matches"]={}}
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
      local search_term, star_term = string.match(new_item_value, "^(.-)([0-9a-f]+)%*$")
      if search_term == " " then
        search_term = ""
      end
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
    local extra = ""
    if new_item_type == "bin" then
      local b32digest = b32digests[new_item_value]
      extra = b32digest .. ":"
    end
    new_item_name = new_item_type .. ":" .. extra .. new_item_value
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

percent_encode_url = function(url)
  temp = ""
  for c in string.gmatch(url, "(.)") do
    local b = string.byte(c)
    if b < 32 or b > 126 then
      c = string.format("%%%02X", b)
    end
    temp = temp .. c
  end
  return temp
end

allowed = function(url, parenturl)
  local noscheme = string.match(url, "^https?://(.*)$")

  if ids[url]
    or (noscheme and ids[string.lower(noscheme)]) then
    return true
  end

  if ids[string.match(url, "^https?://[^/]+/(.*)$")]
    or ids[string.match(url, "^https?://[^/]+/[^/]+/(.*)$")]
    or (item_type == "id" and string.match(url, "/DownloadDialog%.aspx")) then
    return true
  end

  if not string.match(url, "^https?://[^/]*update%.microsoft%.com/")
    and not string.match(url, "^https?://[^/]*download%.windowsupdate%.com/") then
    discover_item(discovered_outlinks, string.match(percent_encode_url(url), "^([^%s]+)"))
    return false
  end

  for _, pattern in pairs({
    "([0-9a-f%-]+)",
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
      if b < 32 or b > 126 then
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
    if not processed(url_ .. tostring(post_data))
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
      elseif post_data then
        error("Did not expect post data.")
      else
        table.insert(urls, {
          url=url_,
          headers=headers
        })
      end
      addedtolist[url_.. tostring(post_data)] = true
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

  if item_type == "bin" then
    if status_code == 200 then
      local domains = {
        "https://catalog.s.download.windowsupdate.com/",
        "http://download.windowsupdate.com/",
        "http://b1.download.windowsupdate.com/"
      }
      for _, domain in pairs(domains) do
        if string.match(url, "^(https?://[^/]+/)") == domain then
          for _, domain2 in pairs(domains) do
            check(domain2 .. item_value)
         end
       end
     end
    end
    for _, path in pairs({"/", "/c/", "/d/"}) do
      check(urlparse.absolute(url, path .. item_value))
    end
  end

  if allowed(url)
    and status_code < 300
    and item_type ~= "bin" then
    html = read_file(file)
    if string.match(url, "/ScopedViewInline%.aspx%?updateid=") then
      post_data = 
        "updateIDs=%5B%7B%22size%22%3A0%2C%22languages%22%3A%22%22%2C%22uidInfo%22%3A%22" .. item_value .. "%22%2C%22updateID%22%3A%22" .. item_value .. "%22%7D%5D"
        .. "&updateIDsBlockedForImport=&wsusApiPresent=&contentImport=&sku=&serverName=&ssl=&portNumber=&version="
      for _, params in pairs({"", "?updateid=" .. item_value, "?scopedview=true"}) do
        check("https://www.catalog.update.microsoft.com/DownloadDialog.aspx" .. params)
      end
      post_data = nil
      check("https://www.catalog.update.microsoft.com/ScopedView.aspx?updateid=" .. item_value)
    end
    if string.match(url, "/DownloadDialog%.aspx") then
      local found = false
      for download_information in string.gmatch(html, "downloadInformation%[([0-9]+)%]%s*=") do
        if download_information ~= "0" then
          error("Unexpected download_information ID " .. download_information .. ".")
        end
        local base_s = "downloadInformation%[" .. download_information .. "%]%.files%["
        local max_num = 0
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
          error("Count incorrect file count.")
        end
        for _, file_data in pairs(files) do
          local b32digest = basexx.to_base32(base64.decode(file_data["digest"]))
          local domain, path = string.match(file_data["url"], "^https?://([^/]+)/(.+)$")
          if domain ~= "catalog.s.download.windowsupdate.com"
            and domain ~= "download.windowsupdate.com" then
            error("Found unexpected address " .. domain .. ".")
          end
          local temp = string.match(path, "^[cd]/(.+)$")
          if temp then
            path = temp
          end
          local new_item = "bin:" .. b32digest .. ":" .. path
          discover_item(discovered_binaries, new_item)
          found = true
        end
      end
      if not found then
        error("Did not find any download.")
      end
    end
    if string.match(url, "/Search%.aspx%?q=") then
      for updateid in string.gmatch(html, "goToDetails%(\"([0-9a-f%-]+)\"%);") do
        discover_item(discovered_updateids, "id:" .. updateid)
      end
      if item_type == "uuid-search"
        and (
          string.match(html, " of 1000 ")
          or string.match(html, "To narrow your search")
          or string.match(html, "Only the first [0-9]+ are returned%.")
        ) then
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
        for i = 0 , pages-1 do
          check(set_new_params(url, {["p"]=tostring(i)}))
        end
      end
    end
    for newurl in string.gmatch(string.gsub(html, "&[qQ][uU][oO][tT];", '"'), '([^"]+)') do
      checknewurl(newurl)
    end
    for newurl in string.gmatch(string.gsub(html, "&#039;", "'"), "([^']+)") do
      checknewurl(newurl)
    end
    for newurl in string.gmatch(html, "[^%-]href='([^']+)'") do
      checknewshorturl(newurl)
    end
    for newurl in string.gmatch(html, '[^%-]href="([^"]+)"') do
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
  if item_type == "bin" then
    local matching = digest == "sha1:" .. b32digests[item_value]
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
  if item_type == "bin"
    and http_stat["statcode"] == 404 then
    context["matches"][url["url"]] = 404
  end
  if http_stat["statcode"] ~= 200
    and http_stat["statcode"] ~= 404 then
    retry_url = true
    return false
  end
  if http_stat["len"] == 0
    and http_stat["statcode"] < 300 then
    retry_url = true
    return false
  end
  if abortgrab then
    print("Not writing to WARC.")
    return false
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
    if status_code == 401 or status_code == 403
      or (status_code == 302 and string.match(url["url"], "/ScopedViewInline%.aspx%?updateid=")) then
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
    ["microsoftupdate-binaries-r6n8hwu8ui3vx2lt?skipbloom=1"] = discovered_binaries,
    ["microsoftupdate-updateids-tkyzhuuhy1kwn54k?skipbloom=1"] = discovered_updateids,
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


