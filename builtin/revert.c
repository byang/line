#include "cache.h"
#include "builtin.h"
#include "object.h"
#include "commit.h"
#include "tag.h"
#include "wt-status.h"
#include "run-command.h"
#include "exec_cmd.h"
#include "utf8.h"
#include "parse-options.h"
#include "cache-tree.h"
#include "diff.h"
#include "revision.h"
#include "rerere.h"
#include "merge-recursive.h"
#include "refs.h"

/*
 * This implements the builtins revert and cherry-pick.
 *
 * Copyright (c) 2007 Johannes E. Schindelin
 *
 * Based on git-revert.sh, which is
 *
 * Copyright (c) 2005 Linus Torvalds
 * Copyright (c) 2005 Junio C Hamano
 */

static const char * const revert_usage[] = {
	"git revert [options] <commit-ish>",
	NULL
};

static const char * const cherry_pick_usage[] = {
	"git cherry-pick [options] <commit-ish>",
	NULL
};

static int edit, no_replay, no_commit, mainline, signoff, allow_ff;
static enum { REVERT, CHERRY_PICK } action;
static struct commit *commit;
static const char *commit_name;
static int allow_rerere_auto;

static const char *me;

#define GIT_REFLOG_ACTION "GIT_REFLOG_ACTION"

static char *get_encoding(const char *message);

static void parse_args(int argc, const char **argv)
{
	const char * const * usage_str =
		action == REVERT ?  revert_usage : cherry_pick_usage;
	unsigned char sha1[20];
	int noop;
	struct option options[] = {
		OPT_BOOLEAN('n', "no-commit", &no_commit, "don't automatically commit"),
		OPT_BOOLEAN('e', "edit", &edit, "edit the commit message"),
		OPT_BOOLEAN('x', NULL, &no_replay, "append commit name when cherry-picking"),
		OPT_BOOLEAN('r', NULL, &noop, "no-op (backward compatibility)"),
		OPT_BOOLEAN('s', "signoff", &signoff, "add Signed-off-by:"),
		OPT_INTEGER('m', "mainline", &mainline, "parent number"),
		OPT_RERERE_AUTOUPDATE(&allow_rerere_auto),
		OPT_END(),
		OPT_END(),
		OPT_END(),
	};

	if (action == CHERRY_PICK) {
		struct option cp_extra[] = {
			OPT_BOOLEAN(0, "ff", &allow_ff, "allow fast-forward"),
			OPT_END(),
		};
		if (parse_options_concat(options, ARRAY_SIZE(options), cp_extra))
			die("program error");
	}

	if (parse_options(argc, argv, NULL, options, usage_str, 0) != 1)
		usage_with_options(usage_str, options);

	commit_name = argv[0];
	if (get_sha1(commit_name, sha1))
		die ("Cannot find '%s'", commit_name);
	commit = lookup_commit_reference(sha1);
	if (!commit)
		exit(1);
}

struct commit_message {
	char *parent_label;
	const char *label;
	const char *subject;
	char *reencoded_message;
	const char *message;
};

static int get_message(const char *raw_message, struct commit_message *out)
{
	const char *encoding;
	const char *p, *abbrev, *eol;
	char *q;
	int abbrev_len, oneline_len;

	if (!raw_message)
		return -1;
	encoding = get_encoding(raw_message);
	if (!encoding)
		encoding = "UTF-8";
	if (!git_commit_encoding)
		git_commit_encoding = "UTF-8";
	if ((out->reencoded_message = reencode_string(raw_message,
					git_commit_encoding, encoding)))
		out->message = out->reencoded_message;

	abbrev = find_unique_abbrev(commit->object.sha1, DEFAULT_ABBREV);
	abbrev_len = strlen(abbrev);

	/* Find beginning and end of commit subject. */
	p = out->message;
	while (*p && (*p != '\n' || p[1] != '\n'))
		p++;
	if (*p) {
		p += 2;
		for (eol = p + 1; *eol && *eol != '\n'; eol++)
			; /* do nothing */
	} else
		eol = p;
	oneline_len = eol - p;

	out->parent_label = xmalloc(strlen("parent of ") + abbrev_len +
			      strlen("... ") + oneline_len + 1);
	q = out->parent_label;
	q = mempcpy(q, "parent of ", strlen("parent of "));
	out->label = q;
	q = mempcpy(q, abbrev, abbrev_len);
	q = mempcpy(q, "... ", strlen("... "));
	out->subject = q;
	q = mempcpy(q, p, oneline_len);
	*q = '\0';
	return 0;
}

static void free_message(struct commit_message *msg)
{
	free(msg->parent_label);
	free(msg->reencoded_message);
}

static char *get_encoding(const char *message)
{
	const char *p = message, *eol;

	if (!p)
		die ("Could not read commit message of %s",
				sha1_to_hex(commit->object.sha1));
	while (*p && *p != '\n') {
		for (eol = p + 1; *eol && *eol != '\n'; eol++)
			; /* do nothing */
		if (!prefixcmp(p, "encoding ")) {
			char *result = xmalloc(eol - 8 - p);
			strlcpy(result, p + 9, eol - 8 - p);
			return result;
		}
		p = eol;
		if (*p == '\n')
			p++;
	}
	return NULL;
}

static struct lock_file msg_file;
static int msg_fd;

static void add_to_msg(const char *string)
{
	int len = strlen(string);
	if (write_in_full(msg_fd, string, len) < 0)
		die_errno ("Could not write to MERGE_MSG");
}

static void add_message_to_msg(const char *message)
{
	const char *p = message;
	while (*p && (*p != '\n' || p[1] != '\n'))
		p++;

	if (!*p)
		add_to_msg(sha1_to_hex(commit->object.sha1));

	p += 2;
	add_to_msg(p);
	return;
}

static void set_author_ident_env(const char *message)
{
	const char *p = message;
	if (!p)
		die ("Could not read commit message of %s",
				sha1_to_hex(commit->object.sha1));
	while (*p && *p != '\n') {
		const char *eol;

		for (eol = p; *eol && *eol != '\n'; eol++)
			; /* do nothing */
		if (!prefixcmp(p, "author ")) {
			char *line, *pend, *email, *timestamp;

			p += 7;
			line = xmemdupz(p, eol - p);
			email = strchr(line, '<');
			if (!email)
				die ("Could not extract author email from %s",
					sha1_to_hex(commit->object.sha1));
			if (email == line)
				pend = line;
			else
				for (pend = email; pend != line + 1 &&
						isspace(pend[-1]); pend--);
					; /* do nothing */
			*pend = '\0';
			email++;
			timestamp = strchr(email, '>');
			if (!timestamp)
				die ("Could not extract author time from %s",
					sha1_to_hex(commit->object.sha1));
			*timestamp = '\0';
			for (timestamp++; *timestamp && isspace(*timestamp);
					timestamp++)
				; /* do nothing */
			setenv("GIT_AUTHOR_NAME", line, 1);
			setenv("GIT_AUTHOR_EMAIL", email, 1);
			setenv("GIT_AUTHOR_DATE", timestamp, 1);
			free(line);
			return;
		}
		p = eol;
		if (*p == '\n')
			p++;
	}
	die ("No author information found in %s",
			sha1_to_hex(commit->object.sha1));
}

static char *help_msg(const char *name)
{
	struct strbuf helpbuf = STRBUF_INIT;
	char *msg = getenv("GIT_CHERRY_PICK_HELP");

	if (msg)
		return msg;

	strbuf_addstr(&helpbuf, "  After resolving the conflicts,\n"
		"mark the corrected paths with 'git add <paths>' or 'git rm <paths>'\n"
		"and commit the result");

	if (action == CHERRY_PICK) {
		strbuf_addf(&helpbuf, " with: \n"
			"\n"
			"        git commit -c %s\n",
			name);
	}
	else
		strbuf_addch(&helpbuf, '.');
	return strbuf_detach(&helpbuf, NULL);
}

static struct tree *empty_tree(void)
{
	struct tree *tree = xcalloc(1, sizeof(struct tree));

	tree->object.parsed = 1;
	tree->object.type = OBJ_TREE;
	pretend_sha1_file(NULL, 0, OBJ_TREE, tree->object.sha1);
	return tree;
}

static NORETURN void die_dirty_index(const char *me)
{
	if (read_cache_unmerged()) {
		die_resolve_conflict(me);
	} else {
		if (advice_commit_before_merge)
			die("Your local changes would be overwritten by %s.\n"
			    "Please, commit your changes or stash them to proceed.", me);
		else
			die("Your local changes would be overwritten by %s.\n", me);
	}
}

static int fast_forward_to(const unsigned char *to, const unsigned char *from)
{
	struct ref_lock *ref_lock;

	read_cache();
	if (checkout_fast_forward(from, to))
		exit(1); /* the callee should have complained already */
	ref_lock = lock_any_ref_for_update("HEAD", from, 0);
	return write_ref_sha1(ref_lock, to, "cherry-pick");
}

static int revert_or_cherry_pick(int argc, const char **argv)
{
	unsigned char head[20];
	struct commit *base, *next, *parent;
	const char *base_label, *next_label;
	int i, index_fd, clean;
	struct commit_message msg = { NULL, NULL, NULL, NULL, NULL };
	char *defmsg = NULL;
	struct merge_options o;
	struct tree *result, *next_tree, *base_tree, *head_tree;
	static struct lock_file index_lock;

	git_config(git_default_config, NULL);
	me = action == REVERT ? "revert" : "cherry-pick";
	setenv(GIT_REFLOG_ACTION, me, 0);
	parse_args(argc, argv);

	/* this is copied from the shell script, but it's never triggered... */
	if (action == REVERT && !no_replay)
		die("revert is incompatible with replay");

	if (allow_ff) {
		if (signoff)
			die("cherry-pick --ff cannot be used with --signoff");
		if (no_commit)
			die("cherry-pick --ff cannot be used with --no-commit");
		if (no_replay)
			die("cherry-pick --ff cannot be used with -x");
		if (edit)
			die("cherry-pick --ff cannot be used with --edit");
	}

	if (read_cache() < 0)
		die("git %s: failed to read the index", me);
	if (no_commit) {
		/*
		 * We do not intend to commit immediately.  We just want to
		 * merge the differences in, so let's compute the tree
		 * that represents the "current" state for merge-recursive
		 * to work on.
		 */
		if (write_cache_as_tree(head, 0, NULL))
			die ("Your index file is unmerged.");
	} else {
		if (get_sha1("HEAD", head))
			die ("You do not have a valid HEAD");
		if (index_differs_from("HEAD", 0))
			die_dirty_index(me);
	}
	discard_cache();

	if (!commit->parents) {
		if (action == REVERT)
			die ("Cannot revert a root commit");
		parent = NULL;
	}
	else if (commit->parents->next) {
		/* Reverting or cherry-picking a merge commit */
		int cnt;
		struct commit_list *p;

		if (!mainline)
			die("Commit %s is a merge but no -m option was given.",
			    sha1_to_hex(commit->object.sha1));

		for (cnt = 1, p = commit->parents;
		     cnt != mainline && p;
		     cnt++)
			p = p->next;
		if (cnt != mainline || !p)
			die("Commit %s does not have parent %d",
			    sha1_to_hex(commit->object.sha1), mainline);
		parent = p->item;
	} else if (0 < mainline)
		die("Mainline was specified but commit %s is not a merge.",
		    sha1_to_hex(commit->object.sha1));
	else
		parent = commit->parents->item;

	if (allow_ff && !hashcmp(parent->object.sha1, head))
		return fast_forward_to(commit->object.sha1, head);

	if (parent && parse_commit(parent) < 0)
		die("%s: cannot parse parent commit %s",
		    me, sha1_to_hex(parent->object.sha1));

	if (get_message(commit->buffer, &msg) != 0)
		die("Cannot get commit message for %s",
				sha1_to_hex(commit->object.sha1));

	/*
	 * "commit" is an existing commit.  We would want to apply
	 * the difference it introduces since its first parent "prev"
	 * on top of the current HEAD if we are cherry-pick.  Or the
	 * reverse of it if we are revert.
	 */

	defmsg = git_pathdup("MERGE_MSG");
	msg_fd = hold_lock_file_for_update(&msg_file, defmsg,
					   LOCK_DIE_ON_ERROR);

	index_fd = hold_locked_index(&index_lock, 1);

	if (action == REVERT) {
		base = commit;
		base_label = msg.label;
		next = parent;
		next_label = msg.parent_label;
		add_to_msg("Revert \"");
		add_to_msg(msg.subject);
		add_to_msg("\"\n\nThis reverts commit ");
		add_to_msg(sha1_to_hex(commit->object.sha1));

		if (commit->parents->next) {
			add_to_msg(", reversing\nchanges made to ");
			add_to_msg(sha1_to_hex(parent->object.sha1));
		}
		add_to_msg(".\n");
	} else {
		base = parent;
		base_label = msg.parent_label;
		next = commit;
		next_label = msg.label;
		set_author_ident_env(msg.message);
		add_message_to_msg(msg.message);
		if (no_replay) {
			add_to_msg("(cherry picked from commit ");
			add_to_msg(sha1_to_hex(commit->object.sha1));
			add_to_msg(")\n");
		}
	}

	read_cache();
	init_merge_options(&o);
	o.ancestor = base ? base_label : "(empty tree)";
	o.branch1 = "HEAD";
	o.branch2 = next ? next_label : "(empty tree)";

	head_tree = parse_tree_indirect(head);
	next_tree = next ? next->tree : empty_tree();
	base_tree = base ? base->tree : empty_tree();

	clean = merge_trees(&o,
			    head_tree,
			    next_tree, base_tree, &result);

	if (active_cache_changed &&
	    (write_cache(index_fd, active_cache, active_nr) ||
	     commit_locked_index(&index_lock)))
		die("%s: Unable to write new index file", me);
	rollback_lock_file(&index_lock);

	if (!clean) {
		add_to_msg("\nConflicts:\n\n");
		for (i = 0; i < active_nr;) {
			struct cache_entry *ce = active_cache[i++];
			if (ce_stage(ce)) {
				add_to_msg("\t");
				add_to_msg(ce->name);
				add_to_msg("\n");
				while (i < active_nr && !strcmp(ce->name,
						active_cache[i]->name))
					i++;
			}
		}
		if (commit_lock_file(&msg_file) < 0)
			die ("Error wrapping up %s", defmsg);
		fprintf(stderr, "Automatic %s failed.%s\n",
			me, help_msg(commit_name));
		rerere(allow_rerere_auto);
		exit(1);
	}
	if (commit_lock_file(&msg_file) < 0)
		die ("Error wrapping up %s", defmsg);
	fprintf(stderr, "Finished one %s.\n", me);

	/*
	 *
	 * If we are cherry-pick, and if the merge did not result in
	 * hand-editing, we will hit this commit and inherit the original
	 * author date and name.
	 * If we are revert, or if our cherry-pick results in a hand merge,
	 * we had better say that the current user is responsible for that.
	 */

	if (!no_commit) {
		/* 6 is max possible length of our args array including NULL */
		const char *args[6];
		int i = 0;
		args[i++] = "commit";
		args[i++] = "-n";
		if (signoff)
			args[i++] = "-s";
		if (!edit) {
			args[i++] = "-F";
			args[i++] = defmsg;
		}
		args[i] = NULL;
		return execv_git_cmd(args);
	}
	free_message(&msg);
	free(defmsg);

	return 0;
}

int cmd_revert(int argc, const char **argv, const char *prefix)
{
	if (isatty(0))
		edit = 1;
	no_replay = 1;
	action = REVERT;
	return revert_or_cherry_pick(argc, argv);
}

int cmd_cherry_pick(int argc, const char **argv, const char *prefix)
{
	no_replay = 0;
	action = CHERRY_PICK;
	return revert_or_cherry_pick(argc, argv);
}
