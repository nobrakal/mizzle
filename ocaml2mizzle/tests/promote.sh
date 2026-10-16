#! /usr/bin/env bash

set -eou pipefail

. tests/common.sh

if [[ 0 < $# ]] ; then
	tests="$@"
	tests="${tests/#/$test_dir/}"
	tests="${tests/%/.ml}"
else
  tests="$(ls $test_dir/*.ml)"
fi

for test in $tests ; do
	if [ ! -f "$test" ] ; then
		echo "error: test does not exist: $test"
		exit 1
	fi

	test="${test%.*}"

	$ocamlopt "$test.ml"
	$ocaml2mizzle "$test.cmt" "$test_dir"

	cp "${test}__types.v" "${test}__types.exp"
	cp "${test}__code.v" "${test}__code.exp"

  echo "test promoted: $(basename $test)"
done
