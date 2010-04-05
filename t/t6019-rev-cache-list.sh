#!/bin/sh

test_description='git rev-cache tests'
. ./test-lib.sh

test_cmp_sorted() {
	grep -io "[a-f0-9]*" $1 | sort >.tmpfile1 &&
	grep -io "[a-f0-9]*" $2 | sort >.tmpfile2 &&
	test_cmp .tmpfile1 .tmpfile2
}

# we want a totally wacked out branch structure...
# we need branching and merging of sizes up through 3, tree
# addition/deletion, and enough branching to exercise path
# reuse
test_expect_success 'init repo' '
	echo bla >file &&
	git add . &&
	git commit -m "bla" &&

	git branch b1 &&
	git checkout b1 &&
	echo blu >file2 &&
	mkdir d1 &&
	echo bang >d1/filed1 &&
	git add . &&
	git commit -m "blu" &&

	git checkout master &&
	git branch b2 &&
	git checkout b2 &&
	echo kaplaa >>file &&
	git commit -a -m "kaplaa" &&

	git checkout master &&
	mkdir smoke &&
	echo omg >smoke/bong &&
	git add . &&
	git commit -m "omg" &&

	git branch b4 &&
	git checkout b4 &&
	echo shazam >file8 &&
	git add . &&
	git commit -m "shazam" &&
	git merge -m "merge b2" b2 &&

	echo bam >smoke/pipe &&
	git add .
	git commit -m "bam" &&

	git checkout master &&
	echo pow >file7 &&
	git add . &&
	git commit -m "pow" &&
	git merge -m "merge b4" b4 &&

	git checkout b1 &&
	echo stuff >d1/filed1 &&
	git commit -a -m "stuff" &&

	git branch b11 &&
	git checkout b11 &&
	echo wazzup >file3 &&
	git add file3 &&
	git commit -m "wazzup" &&

	git checkout b1 &&
	mkdir d1/d2 &&
	echo lol >d1/d2/filed2 &&
	git add . &&
	git commit -m "lol" &&

	git checkout master &&
	git merge -m "triple merge" b1 b11 &&
	git rm -r d1 &&
	git commit -a -m "oh noes"
'

git rev-list HEAD --not HEAD~3 >proper_commit_list_limited
git rev-list HEAD >proper_commit_list
git rev-list HEAD --objects >proper_object_list

test_expect_success 'make cache slice' '
	git rev-cache add HEAD 2>output.err &&
	grep "final return value: 0" output.err
'

test_expect_success 'remake cache slice' '
	git rev-cache add HEAD 2>output.err &&
	grep "final return value: 0" output.err
'

#check core mechanics and rev-list hook for commits
test_expect_success 'test rev-caches walker directly (limited)' '
	git rev-cache walk HEAD --not HEAD~3 >list &&
	test_cmp_sorted list proper_commit_list_limited
'

test_expect_success 'test rev-caches walker directly (unlimited)' '
	git rev-cache walk HEAD >list &&
	test_cmp_sorted list proper_commit_list
'

#do the same for objects
test_expect_success 'test rev-caches walker with objects' '
	git rev-cache walk --objects HEAD >list &&
	test_cmp_sorted list proper_object_list
'

test_done
