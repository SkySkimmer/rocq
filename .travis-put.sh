#!/usr/bin/env bash

FILE="Coq-travis-${TRAVIS_BUILD_ID}.zip"

cp bin/fake_ide cache/bin/
zip -r "$FILE" cache config/Makefile

megaput -u "$MEGANAME" -p "$MEGAPASS" "$FILE"
