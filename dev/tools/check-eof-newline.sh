#!/usr/bin/env bash

if ! dev/tools/should-check-whitespace.sh "$1" || [ -z "$(tail -c 1 "$1")" ]
then
    exit 0
else
    echo "No newline at end of file $1!"
    exit 1
fi
