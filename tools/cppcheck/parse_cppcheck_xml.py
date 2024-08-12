#!/usr/bin/env python3

import xml.etree.ElementTree as ET
import sys
from sys import exit
import re
import os

XML_FILE = sys.argv[1]
CPPCHECK_MIN_VERSION = 2.14

def main():

    count = 0
    # Parse the XML data for cppcheck version
    tree = ET.parse(XML_FILE)
    root = tree.getroot()

    for attr in root.findall('./cppcheck'):
        cppcheck_version = attr.get('version')
        cppcheck_version = float(re.search(r'([\d.]+)', cppcheck_version).group(1))

    node_name = 'error'
    for node in root.iter():
        if(node.tag == node_name):
             count += 1

    print(count)

    # check for cppcheck_version, signal not ok if greater than doc version
    if(cppcheck_version >= CPPCHECK_MIN_VERSION):
        sys.exit(1)
    else:
        sys.exit(0)

if __name__ == '__main__':
	main()
