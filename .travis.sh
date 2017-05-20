#!/usr/bin/env bash

TEST_TARGET="$1"

if [ "$TEST_TARGET" = install ]
then PREFIX="-prefix cache"
fi

set -e

echo 'Configuring Coq...' && echo -en 'travis_fold:start:coq.config\\r'
./configure ${PREFIX} -usecamlp5 -native-compiler yes ${EXTRA_CONF}
echo -en 'travis_fold:end:coq.config\\r'

echo 'Building Coq...' && echo -en 'travis_fold:start:coq.build\\r'
if [ "(" -d cache ")" -a "(" "$PREFIX" != "-local" ")" ];
then rm -rf cache;
fi

if [ ! "(" -d cache ")" ];
then make -j ${NJOBS};
else find cache;
fi
echo -en 'travis_fold:end:coq.build\\r'

echo 'Running tests...' && echo -en 'travis_fold:start:coq.test\\r'
make -j ${NJOBS} ${TEST_TARGET}
echo -en 'travis_fold:end:coq.test\\r'

set +e
