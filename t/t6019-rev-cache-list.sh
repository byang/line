#!/bin/sh

test_description='git rev-cache tests'
. ./test-lib.sh

test_cmp_sorted() {
# note that we're tip-toeing around the corner case of two objects/names
# for the same SHA-1 => discrepencies between cached and non-cached walks
	sort $1 >.tmpfile1 &&
	sort $2 >.tmpfile2 &&
	test_cmp .tmpfile1 .tmpfile2
}

# we want a totally wacked out branch structure...
# we need branching and merging of sizes up through 3, tree
# addition/deletion, and enough branching to exercise path
# reuse
test_expect_success 'init repo' '
	echo bla >file &&
	mkdir amaindir &&
	echo watskeburt >amaindir/file &&
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

	sleep 2 &&
	git branch b4 &&
	git checkout b4 &&
	echo shazam >file8 &&
	git add . &&
	git commit -m "shazam" &&
	git merge -m "merge b2" b2 &&

	echo bam >smoke/pipe &&
	git add . &&
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

	sleep 2 &&
	git checkout master &&
	git merge -m "triple merge" b1 b11 &&
	git rm -r d1 &&
	sleep 2 &&
	git commit -a -m "oh noes"
'

max_date=`git rev-list --timestamp HEAD~1 --max-count=1 | grep -e "^[0-9]*" -o`
min_date=`git rev-list --timestamp b4 --max-count=1 | grep -e "^[0-9]*" -o`

git rev-list --topo-order HEAD --not HEAD~3 >proper_commit_list_limited
git rev-list --topo-order HEAD --not HEAD~2 >proper_commit_list_limited2
git rev-list --topo-order HEAD >proper_commit_list
git rev-list --objects HEAD >proper_object_list
git rev-list HEAD --max-age=$min_date --min-age=$max_date >proper_list_date_limited
git rev-cache test HEAD :HEAD~2 >proper_shallow_list 2>/dev/null

cache_sha1=`git rev-cache add HEAD 2>output.err`

test_expect_success 'make cache slice' '
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

test_expect_success 'test rev-list traversal (limited)' '
	git rev-list HEAD --not HEAD~3 >list &&
	test_cmp list proper_commit_list_limited
'

test_expect_success 'test rev-list traversal (unlimited)' '
	git rev-list HEAD >list &&
	test_cmp list proper_commit_list
'

#do the same for objects
test_expect_success 'test rev-caches walker with objects' '
	git rev-cache walk --objects HEAD >list &&
	test_cmp_sorted list proper_object_list
'

test_expect_success 'test rev-list with objects (topo order)' '
	git rev-list --topo-order --objects HEAD >list &&
	test_cmp_sorted list proper_object_list
'

test_expect_success 'test rev-list with objects (no order)' '
	git rev-list --objects HEAD >list &&
	test_cmp_sorted list proper_object_list
'

#verify age limiting
test_expect_success 'test rev-list date limiting (topo order)' '
	git rev-list --topo-order --max-age=$min_date --min-age=$max_date HEAD >list &&
	test_cmp_sorted list proper_list_date_limited
'

test_expect_success 'test rev-list date limiting (no order)' '
	git rev-list --max-age=$min_date --min-age=$max_date HEAD >list &&
	test_cmp_sorted list proper_list_date_limited
'

#check partial cache slice
test_expect_success 'saving old cache and generating partial slice' '
	cp ".git/rev-cache/$cache_sha1" .git/rev-cache/.old &&
	rm ".git/rev-cache/$cache_sha1" .git/rev-cache/index &&

	git rev-cache add HEAD~2 2>output.err &&
	grep "final return value: 0" output.err
'

test_expect_success 'rev-list with wholly interesting partial slice' '
	git rev-list --topo-order HEAD >list &&
	test_cmp list proper_commit_list
'

test_expect_success 'rev-list with partly uninteresting partial slice' '
	git rev-list --topo-order HEAD --not HEAD~3 >list &&
	test_cmp list proper_commit_list_limited
'

test_expect_success 'rev-list with wholly uninteresting partial slice' '
	git rev-list --topo-order HEAD --not HEAD~2 >list &&
	test_cmp list proper_commit_list_limited2
'

#try out index generation and fuse (note that --all == HEAD in this case)
#probably should make a test for that too...
test_expect_success 'test (non-)fusion of one slice' '
	git rev-cache fuse >output.err &&
	grep "nothing to fuse" output.err
'

test_expect_success 'make fresh slice' '
	git rev-cache add --all --fresh 2>output.err &&
	grep "final return value: 0" output.err
'

test_expect_success 'check dual slices' '
	git rev-list --topo-order HEAD~2 HEAD >list &&
	test_cmp list proper_commit_list
'

test_expect_success 'regenerate index' '
	rm .git/rev-cache/index &&
	git rev-cache index 2>output.err &&
	grep "final return value: 0" output.err
'

test_expect_success 'fuse slices' '
	test -e .git/rev-cache/.old &&
	git rev-cache fuse 2>output.err &&
	grep "final return value: 0" output.err &&
	test_cmp .git/rev-cache/$cache_sha1 .git/rev-cache/.old
'

#make sure we can smoothly handle corrupted caches
test_expect_success 'corrupt slice' '
	echo bla >.git/rev-cache/$cache_sha1
'

test_expect_success 'test rev-list traversal (limited) (corrupt slice)' '
	git rev-list --topo-order HEAD --not HEAD~3 >list &&
	test_cmp list proper_commit_list_limited
'

test_expect_success 'test rev-list traversal (unlimited) (corrupt slice)' '
	git rev-list HEAD >list &&
	test_cmp_sorted list proper_commit_list
'

test_expect_success 'corrupt index' '
	echo blu >.git/rev-cache/index
'

test_expect_success 'test rev-list traversal (limited) (corrupt index)' '
	git rev-list --topo-order HEAD --not HEAD~3 >list &&
	test_cmp list proper_commit_list_limited
'

test_expect_success 'test rev-list traversal (unlimited) (corrupt index)' '
	git rev-list HEAD >list &&
	test_cmp_sorted list proper_commit_list
'

#test --ignore-size in fuse
rm .git/rev-cache/*
cache_sha1=`git rev-cache add HEAD~2 2>output.err`

test_expect_success 'make fragmented slices' '
	git rev-cache add HEAD~1 --not HEAD~2 2>>output.err &&
	git rev-cache add HEAD --fresh 2>>output.err &&
	test `grep "final return value: 0" output.err | wc -l` -eq 3
'

cache_size=$(wc -c < .git/rev-cache/$cache_sha1)
test_expect_success 'test --ignore-size function in fuse' '
	git rev-cache fuse --ignore-size=$cache_size 2>output.err &&
	grep "final return value: 0" output.err &&
	test -e .git/rev-cache/$cache_sha1
'

#test graft handling
test_expect_success 'check graft handling' '
	git rev-cache test HEAD :HEAD~2 >list
	test_cmp list proper_shallow_list
'

test_done
