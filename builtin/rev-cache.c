#include "cache.h"
#include "object.h"
#include "commit.h"
#include "diff.h"
#include "revision.h"
#include "rev-cache.h"
#include "list-objects.h"

unsigned long default_ignore_size = 50 * 1024 * 1024; /* 50mb */

/* porcelain for rev-cache.c */
static int handle_add(int argc, const char *argv[]) /* args beyond this command */
{
	struct rev_info revs;
	struct rev_cache_info rci;
	char dostdin = 0;
	unsigned int flags = 0;
	int i, retval;
	unsigned char cache_sha1[20];
	struct commit_list *starts = 0, *ends = 0;
	struct commit *commit;

	init_revisions(&revs, 0);
	init_rev_cache_info(&rci);

	for (i = 0; i < argc; i++) {
		if (!strcmp(argv[i], "--stdin"))
			dostdin = 1;
		else if (!strcmp(argv[i], "--fresh") || !strcmp(argv[i], "--incremental"))
			starts_from_slices(&revs, UNINTERESTING, 0, 0);
		else if (!strcmp(argv[i], "--not"))
			flags ^= UNINTERESTING;
		else if (!strcmp(argv[i], "--legs") || !strcmp(argv[i], "--close"))
			rci.legs = 1;
		else if (!strcmp(argv[i], "--no-objects"))
			rci.objects = 0;
		else if (!strcmp(argv[i], "--all")) {
			const char *args[2];
			int argn = 0;

			args[argn++] = "rev-list";
			args[argn++] = "--all";
			setup_revisions(argn, args, &revs, 0);
		} else
			handle_revision_arg(argv[i], &revs, flags, 1);
	}

	if (dostdin) {
		char line[1000];

		flags = 0;
		while (fgets(line, sizeof(line), stdin)) {
			int len = strlen(line);
			while (len && (line[len - 1] == '\n' || line[len - 1] == '\r'))
				line[--len] = 0;

			if (!len)
				break;

			if (!strcmp(line, "--not"))
				flags ^= UNINTERESTING;
			else
				handle_revision_arg(line, &revs, flags, 1);
		}
	}

	retval = make_cache_slice(&rci, &revs, &starts, &ends, cache_sha1);
	if (retval < 0)
		return retval;

	printf("%s\n", sha1_to_hex(cache_sha1));

	fprintf(stderr, "endpoints:\n");
	while ((commit = pop_commit(&starts)))
		fprintf(stderr, "S %s\n", sha1_to_hex(commit->object.sha1));
	while ((commit = pop_commit(&ends)))
		fprintf(stderr, "E %s\n", sha1_to_hex(commit->object.sha1));

	return 0;
}

static void show_commit(struct commit *commit, void *data)
{
	printf("%s\n", sha1_to_hex(commit->object.sha1));
}

static void show_object(struct object *obj, const struct name_path *path, const char *last)
{
	printf("%s\n", sha1_to_hex(obj->sha1));
}

static int test_rev_list(int argc, const char *argv[])
{
	struct rev_info revs;
	unsigned int flags = 0;
	int i;

	init_revisions(&revs, 0);

	for (i = 0; i < argc; i++) {
		if (!strcmp(argv[i], "--not"))
			flags ^= UNINTERESTING;
		else if (!strcmp(argv[i], "--objects"))
			revs.tree_objects = revs.blob_objects = 1;
		else {
			struct commit_graft graft;

			if (argv[i][0] == ':') {
				handle_revision_arg(argv[i] + 1, &revs, flags, 1);

				hashcpy(graft.sha1, revs.pending.objects[revs.pending.nr - 1].item->sha1);
				graft.nr_parent = -1;
				register_commit_graft(&graft, 0);
			} else
				handle_revision_arg(argv[i], &revs, flags, 1);
		}
	}

	setup_revisions(0, 0, &revs, 0);
	revs.topo_order = 1;
	revs.lifo = 1;
	prepare_revision_walk(&revs);

	traverse_commit_list(&revs, show_commit, show_object, 0);

	return 0;
}

static int handle_walk(int argc, const char *argv[])
{
	struct commit *commit;
	struct rev_info revs;
	struct commit_list *queue, *work, **qp;
	unsigned char *sha1p, *sha1pt;
	unsigned long date = 0;
	unsigned int flags = 0;
	int retval, slop = 5, i;

	init_revisions(&revs, 0);

	for (i = 0; i < argc; i++) {
		if (!strcmp(argv[i], "--not"))
			flags ^= UNINTERESTING;
		else if (!strcmp(argv[i], "--objects"))
			revs.tree_objects = revs.blob_objects = 1;
		else
			handle_revision_arg(argv[i], &revs, flags, 1);
	}

	work = 0;
	sha1p = 0;
	for (i = 0; i < revs.pending.nr; i++) {
		commit = lookup_commit(revs.pending.objects[i].item->sha1);

		sha1pt = get_cache_slice(commit);
		if (!sha1pt)
			die("%s: not in a cache slice", sha1_to_hex(commit->object.sha1));

		if (!i)
			sha1p = sha1pt;
		else if (sha1p != sha1pt)
			die("walking porcelain is /per/ cache slice; commits cannot be spread out amoung several");

		insert_by_date(commit, &work);
	}

	if (!sha1p)
		die("nothing to traverse!");

	revs.pending.nr = 0;
	queue = 0;
	qp = &queue;
	commit = pop_commit(&work);
	retval = traverse_cache_slice(&revs, sha1p, commit, &date, &slop, &qp, &work);
	if (retval < 0)
		return retval;

	fprintf(stderr, "queue:\n");
	while ((commit = pop_commit(&queue)) != 0) {
		printf("%s\n", sha1_to_hex(commit->object.sha1));
	}

	fprintf(stderr, "work:\n");
	while ((commit = pop_commit(&work)) != 0) {
		printf("%s\n", sha1_to_hex(commit->object.sha1));
	}

	fprintf(stderr, "pending:\n");
	for (i = 0; i < revs.pending.nr; i++) {
		struct object *obj = revs.pending.objects[i].item;
		const char *name = revs.pending.objects[i].name;

		/* unfortunately, despite our careful generation, object duplication *is* a possibility...
		 * (eg. same object introduced into two different branches) */
		if (obj->flags & SEEN)
			continue;

		printf("%s %s\n", sha1_to_hex(revs.pending.objects[i].item->sha1), name);
		obj->flags |= SEEN;
	}

	return 0;
}

static int handle_fuse(int argc, const char *argv[])
{
	struct rev_info revs;
	struct rev_cache_info rci;
	const char *args[5];
	int t, i, argn = 0;
	char add_all = 0;

	init_revisions(&revs, 0);
	init_rev_cache_info(&rci);
	args[argn++] = "rev-list";

	for (i = 0; i < argc; i++) {
		t = 1;
		if (!strcmp(argv[i], "--all")) {
			args[argn++] = "--all";
			setup_revisions(argn, args, &revs, 0);
			add_all = 1;
		} else if (!strcmp(argv[i], "--no-objects"))
			rci.objects = 0;
		else if (!strncmp(argv[i], "--ignore-size", 13) ||
			(t = !strncmp(argv[i], "--keep-size", 11))) {
			unsigned long sz;

			t = t ? 13 : 11;
			if (argv[i][t] == '=')
				git_parse_ulong(argv[i] + t + 1, &sz);
			else
				sz = default_ignore_size;

			rci.ignore_size = sz;
		} else
			continue;
	}

	if (!add_all)
		starts_from_slices(&revs, 0, 0, 0);

	return fuse_cache_slices(&rci, &revs);
}

static int handle_index(int argc, const char *argv[])
{
	return regenerate_cache_index(0);
}

static int handle_alt(int argc, const char *argv[])
{
	if (argc < 1)
		return -1;

	return make_cache_slice_pointer(0, argv[0]);
}

static int handle_help(void)
{
	char *usage = "\
usage:\n\
git-rev-cache COMMAND [options] [<commit>...]\n\
commands:\n\
  add    - add revisions to the cache.  reads commit ids from stdin, \n\
	   START = 'interesting', END = boundary of 'uninterestingness'\n\
	   options:\n\
	    --all                  use all branch heads as starts\n\
	    --fresh/--incremental  exclude everything already in a cache slice\n\
	    --stdin                also read commit ids from stdin (same form\n\
				   as cmd)\n\
	    --legs/--close         ensure branch is entirely self-contained\n\
	    --no-objects           don't add non-commit objects to slice\n\
  walk   - walk a cache slice based on set of commits; formatted as add\n\
	   options:\n\
	   --objects               include non-commit objects in traversals\n\
  fuse   - coalesce cache slices into a single cache.\n\
	   options:\n\
	    --all                  include all objects in repository\n\
	    --no-objects           don't add non-commit objects to slice\n\
	    --ignore-size[=N]      ignore slices of size >= N; defaults to ~5MB\n\
	    --keep-size[=N]\n\
  index  - regnerate the cache index.\n\
  alt    - create a slice pointer to slice identified by a passed path";

	puts(usage);

	return 0;
}

static int rev_cache_config(const char *k, const char *v, void *cb)
{
	/* this could potentially be related to pack.windowmemory, but we want a max around 50mb,
	 * and .windowmemory is often >700mb, with *large* variations */
	if (!strcmp(k, "revcache.ignoresize")) {
		int t;

		t = git_config_ulong(k, v);
		if (t)
			default_ignore_size = t;
	}

	return 0;
}

int cmd_rev_cache(int argc, const char *argv[], const char *prefix)
{
	const char *arg;
	int r;

	git_config(git_default_config, NULL);
	git_config(rev_cache_config, NULL);

	if (argc > 1)
		arg = argv[1];
	else
		arg = "";

	argc -= 2;
	argv += 2;
	if (!strcmp(arg, "add"))
		r = handle_add(argc, argv);
	else if (!strcmp(arg, "fuse"))
		r = handle_fuse(argc, argv);
	else if (!strcmp(arg, "walk"))
		r = handle_walk(argc, argv);
	else if (!strcmp(arg, "index"))
		r = handle_index(argc, argv);
	else if (!strcmp(arg, "test"))
		r = test_rev_list(argc, argv);
	else if (!strcmp(arg, "alt"))
		r = handle_alt(argc, argv);
	else
		return handle_help();

	fprintf(stderr, "final return value: %d\n", r);

	return 0;
}
