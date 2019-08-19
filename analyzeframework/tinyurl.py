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
    return requests.get(url).text
