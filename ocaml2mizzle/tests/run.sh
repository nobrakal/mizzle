#! /usr/bin/env bash

set -eou pipefail

. tests/common.sh

for test in $test_dir/*.ml ; do
	test="${test%.*}"

	$ocamlopt "$test.ml"
	$ocaml2mizzle "$test.cmt" "$test_dir"

	if diff "${test}__types.v" "${test}__types.exp" > /dev/null \
	&& diff "${test}__code.v" "${test}__code.exp" > /dev/null
	then
		echo "test successful: $(basename $test)"
	else
		echo "test failed: $(basename $test)"
		exit 1
	fi
done
