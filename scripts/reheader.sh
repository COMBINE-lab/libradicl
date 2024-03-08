#!/usr/bin/env bash

if ! command -v licenseheaders &> /dev/null
then
    echo "licenseheaders could not be found; please install this program to use the script (pip install licenseheaders)."
    exit 1
fi


licenseheaders -d ../src -y 2020-2024 -t bsd-3.tmpl -o COMBINE-lab -n libradicl -u https://www.github.com/COMBINE-lab/libradicl -D -E rs
