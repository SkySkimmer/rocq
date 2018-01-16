#!/usr/bin/env bash

if [ -z "$(tail -c 1 "$1")" ]
then
    exit 0
else
    echo >> "$1"
    exit 0
fi
