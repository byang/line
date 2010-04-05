#include "cache.h"
#include "object.h"
#include "commit.h"
#include "diff.h"
#include "revision.h"
#include "rev-cache.h"

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
			starts_from_slices(&revs, UNINTERESTING);
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

		/* unfortunately, despite our careful generation, object duplication *is* a possibility...
		 * (eg. same object introduced into two different branches) */
		if (obj->flags & SEEN)
			continue;

		printf("%s\n", sha1_to_hex(revs.pending.objects[i].item->sha1));
		obj->flags |= SEEN;
	}

	return 0;
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

int cmd_rev_cache(int argc, const char *argv[], const char *prefix)
{
	const char *arg;
	int r;

	git_config(git_default_config, NULL);

	if (argc > 1)
		arg = argv[1];
	else
		arg = "";

	argc -= 2;
	argv += 2;
	if (!strcmp(arg, "add"))
		r = handle_add(argc, argv);
	else if (!strcmp(arg, "walk"))
		r = handle_walk(argc, argv);
	else
		return handle_help();

	fprintf(stderr, "final return value: %d\n", r);

	return 0;
}
