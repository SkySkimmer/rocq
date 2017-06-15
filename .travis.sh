#!/usr/bin/env bash

set -e
if "$USEMEGA";
then
    if [ "$TEST_TARGET" = install ]
    then PREFIX="-prefix cache"
    else
        FILE="Coq-travis-${TRAVIS_BUILD_ID}.zip"
        megaget -u "$MEGANAME" -p "$MEGAPASS" "/Root/$FILE"
        unzip "$FILE"
    fi
fi

if [ "!" "(" -d cache ")" ];
then
    echo 'Configuring Coq...' && echo -en 'travis_fold:start:coq.config\\r'
    ./configure ${PREFIX} -usecamlp5 -native-compiler yes ${EXTRA_CONF}
    echo -en 'travis_fold:end:coq.config\\r'

    echo 'Building Coq...' && echo -en 'travis_fold:start:coq.build\\r'

    make -j ${NJOBS};
    echo -en 'travis_fold:end:coq.build\\r'
fi

echo 'Running tests...' && echo -en 'travis_fold:start:coq.test\\r'
make -j ${NJOBS} ${TEST_TARGET}
echo -en 'travis_fold:end:coq.test\\r'

set +e
