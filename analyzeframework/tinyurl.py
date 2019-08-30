#! /usr/local/bin/python3.6
"""
URL shorten with TinyURL API
"""
import requests
import urllib


URL = "http://tinyurl.com/api-create.php"

def shorten(url_long):
    url = URL + "?" \
        + urllib.parse.urlencode({"url": url_long})
    resp = requests.get(url)
    if resp.status_code == 200:
        return resp.text
    else:
        return 'Input URI was too long'
