#!/bin/bash

for package in cabextract
do
  if ! dpkg-query -Wf'${Status}' "${package}" 2>/dev/null | grep -q '^i'
  then
    echo "Installing ${package}..."
    sudo apt-get update
    sudo apt-get install -y --no-install-recommends "${package}" || exit 1
    sudo rm -rf /var/lib/apt/lists/*
  fi
done

exit 0
