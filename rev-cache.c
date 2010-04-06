#include "cache.h"
#include "object.h"
#include "commit.h"
#include "tree.h"
#include "tree-walk.h"
#include "blob.h"
#include "tag.h"
#include "diff.h"
#include "revision.h"
#include "rev-cache.h"
#include "run-command.h"
#include "string-list.h"


struct bad_slice {
	unsigned char sha1[20];
	struct bad_slice *next;
};

struct name_list {
	unsigned char sha1[20];
	unsigned int len;
	struct name_list *next;

	char buf[FLEX_ARRAY];
};

struct cache_slice_pointer {
	char signature[8]; /* REVCOPTR */
	char version;
	char path[PATH_MAX + 1];
};

/* list resembles pack index format */
static uint32_t fanout[0xff + 2];

static unsigned char *idx_map;
static int idx_size;
static struct rc_index_header idx_head;
static char no_idx, add_to_pending, add_names;
static unsigned char *idx_caches;

static struct bad_slice *bad_slices;
static struct name_list *name_lists, *cur_name_list;

static struct strbuf *acc_name_buffer;
static struct strbuf *acc_buffer;

#define SLOP			5

#define INDEX_ENTRY_SIZE		(\
	20 +						\
	1 +							\
	4							\
)

#define OBJECT_ENTRY_SIZE	(\
	1 +						\
	20 +					\
	1 +						\
	1 +						\
	1 +						\
	4 +						\
	2						\
)

#define SLICE_HEADER_SIZE		(\
	8 +							\
	1 +							\
	4 +							\
	4 +							\
	2 +							\
	4 +							\
	20 +						\
	4							\
)

#define INDEX_HEADER_SIZE		(\
	8 +							\
	1 +							\
	4 +							\
	4 +							\
	1 +							\
	4							\
)

/* initialization */

#define UNPACK_UINT32(p)		((uint32_t)*(p) << 24 | (uint32_t)*((p) + 1) << 16 | \
									(uint32_t)*((p) + 2) << 8 | (uint32_t)*((p) + 3))

#define PACK_UINT32(p, n)		do {		\
	*(p) = (unsigned char)((n) >> 24);			\
	*((p) + 1) = (unsigned char)((n) >> 16);	\
	*((p) + 2) = (unsigned char)((n) >> 8);		\
	*((p) + 3) = (unsigned char)(n);			\
} while (0)

#define UNPACK_UINT16(p)		((uint16_t)*(p) << 8 | (uint16_t)*((p) + 1))

#define PACK_UINT16(p, n)		do {		\
	*(p) = (unsigned char)((n) >> 8);			\
	*((p) + 1) = (unsigned char)(n);			\
} while (0)

struct rc_index_entry *from_disked_rc_index_entry(unsigned char *src, struct rc_index_entry *dst)
{
	static struct rc_index_entry entry[4];
	static int cur;

	if (!dst)
		dst = &entry[cur++ & 0x3];

	dst->sha1 = (unsigned char *)src;
	dst->is_start = !!(src[20] & 0x80);
	dst->cache_index = src[20] & 0x7f;
	dst->pos = UNPACK_UINT32(src + 21);

	return dst;
}

unsigned char *to_disked_rc_index_entry(struct rc_index_entry *src, unsigned char **dstp)
{
	static unsigned char entry[4][INDEX_ENTRY_SIZE];
	static int cur;
	unsigned char *dst = *dstp;

	if (!dstp || !*dstp) {
		dst = entry[cur++ & 0x3];

		if (dstp)
			*dstp = dst;
	} else
		dst = *dstp;

	if (dst != src->sha1)
		hashcpy(dst, src->sha1);
	dst[20] = (unsigned char)src->is_start << 7 | (unsigned char)src->cache_index;
	PACK_UINT32(dst + 21, src->pos);

	return dst;
}

struct rc_object_entry *from_disked_rc_object_entry(unsigned char *src, struct rc_object_entry *dst)
{
	static struct rc_object_entry entry[4];
	static int cur;

	if (!dst)
		dst = &entry[cur++ & 0x3];

	dst->type = *src >> 5;
	dst->is_end = !!(*src & 0x10);
	dst->is_start = !!(*src & 0x08);
	dst->has_objects = !!(*src & 0x04);
	dst->flag = *src & 0x03;

	dst->sha1 = (unsigned char *)(src + 1);
	dst->merge_nr = *(src + 21);
	dst->split_nr = *(src + 22);

	dst->size_size = *(src + 23) >> 5 & 0x03;
	dst->name_size = *(src + 23) >> 2 & 0x03;
	dst->padding = *(src + 23) & 0x02;

	dst->date = UNPACK_UINT32(src + 24);
	dst->path = UNPACK_UINT16(src + 28);

	return dst;
}

unsigned char *to_disked_rc_object_entry(struct rc_object_entry *src, unsigned char **dstp)
{
	static unsigned char entry[4][OBJECT_ENTRY_SIZE];
	static int cur;
	unsigned char *dst;

	if (!dstp || !*dstp) {
		dst = entry[cur++ & 0x3];

		if (dstp)
			*dstp = dst;
	} else
		dst = *dstp;

	*dst  = (unsigned char)src->type << 5;
	*dst |= (unsigned char)src->is_end << 4;
	*dst |= (unsigned char)src->is_start << 3;
	*dst |= (unsigned char)src->has_objects << 2;
	*dst |= (unsigned char)src->flag;

	if (dst + 1 != src->sha1)
		hashcpy(dst + 1, src->sha1);
	*(dst + 21) = src->merge_nr;
	*(dst + 22) = src->split_nr;

	*(dst + 23)  = (unsigned char)src->size_size << 5;
	*(dst + 23) |= (unsigned char)src->name_size << 2;
	*(dst + 23) |= (unsigned char)src->padding;

	PACK_UINT32(dst + 24, src->date);
	PACK_UINT16(dst + 28, src->path);

	return dst;
}

static void mark_bad_slice(unsigned char *sha1)
{
	struct bad_slice *bad;

	bad = xcalloc(sizeof(struct bad_slice), 1);
	hashcpy(bad->sha1, sha1);

	bad->next = bad_slices;
	bad_slices = bad;
}

static int is_bad_slice(unsigned char *sha1)
{
	struct bad_slice *bad = bad_slices;

	while (bad) {
		if (!hashcmp(bad->sha1, sha1))
			return 1;
		bad = bad->next;
	}

	return 0;
}

static int get_index_head(unsigned char *map, int len, struct rc_index_header *head, uint32_t *fanout, unsigned char **caches)
{
	int i, index = INDEX_HEADER_SIZE;

	if (memcmp(map, "REVINDEX", 8) || *(map + 8) != SUPPORTED_REVINDEX_VERSION)
		return -1;

	memcpy(head->signature, "REVINDEX", 8);
	head->version = *(map + 8);
	head->ofs_objects = UNPACK_UINT32(map + 9);
	head->object_nr = UNPACK_UINT32(map + 13);
	head->cache_nr = *(map + 17);
	head->max_date = UNPACK_UINT32(map + 18);

	if (len < index + head->cache_nr * 20 + 0x100 * sizeof(uint32_t))
		return -2;

	*caches = xmalloc(head->cache_nr * 20);
	memcpy(*caches, map + index, head->cache_nr * 20);
	index += head->cache_nr * 20;

	memcpy(fanout, map + index, 0x100 * sizeof(uint32_t));
	for (i = 0; i <= 0xff; i++)
		fanout[i] = ntohl(fanout[i]);
	fanout[0x100] = len;

	return 0;
}

/* added in init_index */
static void cleanup_cache_slices(void)
{
	if (idx_map) {
		free(idx_caches);
		munmap(idx_map, idx_size);
		idx_map = 0;
	}

	while (name_lists) {
		struct name_list *nl = name_lists->next;
		free(name_lists);
		name_lists = nl;
	}

}

static int init_index(void)
{
	int fd;
	struct stat fi;

	fd = open(git_path("rev-cache/index"), O_RDONLY);
	if (fd == -1 || fstat(fd, &fi))
		goto end;
	if (fi.st_size < INDEX_HEADER_SIZE)
		goto end;

	idx_size = fi.st_size;
	idx_map = xmmap(0, idx_size, PROT_READ, MAP_PRIVATE, fd, 0);
	close(fd);
	if (idx_map == MAP_FAILED)
		goto end;
	if (get_index_head(idx_map, fi.st_size, &idx_head, fanout, &idx_caches))
		goto end;

	atexit(cleanup_cache_slices);

	return 0;

end:
	idx_map = 0;
	no_idx = 1;
	return -1;
}

/* this assumes index is already loaded */
static unsigned char *search_index_1(unsigned char *sha1)
{
	int start, end, starti, endi, i, len, r;
	unsigned char *iep;

	if (!idx_map)
		return 0;

	/* binary search */
	start = fanout[(int)sha1[0]];
	end = fanout[(int)sha1[0] + 1];
	len = (end - start) / INDEX_ENTRY_SIZE;
	if (!len || len * INDEX_ENTRY_SIZE != end - start)
		return 0;

	starti = 0;
	endi = len - 1;
	for (;;) {
		i = (endi + starti) / 2;
		iep = idx_map + start + i * INDEX_ENTRY_SIZE;
		r = hashcmp(sha1, iep);

		if (r) {
			if (starti + 1 == endi) {
				starti++;
				continue;
			} else if (starti == endi)
				break;

			if (r > 0)
				starti = i;
			else /* r < 0 */
				endi = i;
		} else
			return iep;
	}

	return 0;
}

static struct rc_index_entry *search_index(unsigned char *sha1)
{
	unsigned char *ied = search_index_1(sha1);

	if (ied)
		return from_disked_rc_index_entry(ied, 0);

	return 0;
}

unsigned char *get_cache_slice(struct commit *commit)
{
	struct rc_index_entry *ie;
	unsigned char *sha1;

	if (!idx_map) {
		if (no_idx)
			return 0;
		init_index();
	}

	if (commit->date > idx_head.max_date)
		return 0;

	ie = search_index(commit->object.sha1);
	if (ie && ie->cache_index < idx_head.cache_nr) {
		sha1 = idx_caches + ie->cache_index * 20;

		if (is_bad_slice(sha1))
			return 0;
		return sha1;
	}

	return 0;
}


/* traversal */

static unsigned long decode_size(unsigned char *str, int len);

/* on failure */
static void restore_commit(struct commit *commit)
{
	commit->object.flags &= ~(ADDED | SEEN | FACE_VALUE);

	if (!commit->object.parsed) {
		while (pop_commit(&commit->parents))
			;

		parse_commit(commit);
	}

}

static void handle_noncommit(struct rev_info *revs, struct commit *commit, unsigned char *ptr, struct rc_object_entry *entry)
{
	struct blob *blob;
	struct tree *tree;
	struct object *obj;
	unsigned long size, name_index;

	size = decode_size(ptr + RC_ENTRY_SIZE_OFFSET(entry), entry->size_size);
	switch (entry->type) {
	case OBJ_TREE:
		if (!revs->tree_objects)
			return;

		tree = lookup_tree(entry->sha1);
		if (!tree)
			return;

		tree->size = size;
		commit->tree = tree;
		obj = (struct object *)tree;
		break;

	case OBJ_BLOB:
		if (!revs->blob_objects)
			return;

		blob = lookup_blob(entry->sha1);
		if (!blob)
			return;

		obj = (struct object *)blob;
		break;

	default:
		/* tag objects aren't really supposed to be here */
		return;
	}

	if (add_names && cur_name_list) {
		name_index = decode_size(ptr + RC_ENTRY_NAME_OFFSET(entry), entry->name_size);

		if (name_index >= cur_name_list->len)
			name_index = 0;
	} else
		name_index = 0;

	obj->flags |= FACE_VALUE;
	if (add_to_pending) {
		char *name = "";

		if (name_index)
			name = cur_name_list->buf + name_index;

		add_pending_object(revs, obj, name);
	}
}

struct entrance_point {
	int pos;
	char uninteresting;
};

static int eps_sort_callback(const void *a, const void *b)
{
	struct entrance_point *aep, *bep;

	aep = (struct entrance_point *)a;
	bep = (struct entrance_point *)b;

	if (aep->pos == bep->pos)
		return 0;

	return aep->pos > bep->pos ? 1 : -1;
}

static int setup_traversal(struct rc_slice_header *head, struct entrance_point **peps, int *peplen,
	struct commit *commit, struct commit_list **work,
	struct commit_list **unwork, int *ipath_nr, int *upath_nr, char *ioutside)
{
	struct rc_index_entry *iep;
	struct commit_list *prev, *wp, **wpp;
	struct entrance_point *eps;
	int retval, curep = 1, eplen = 10;

	eps = xcalloc(1, eplen * sizeof(struct entrance_point));
	iep = search_index(commit->object.sha1);
	if (commit->object.flags & UNINTERESTING) {
		++*upath_nr;
		eps[0].uninteresting = 1;
	} else
		++*ipath_nr;

	eps[0].pos = iep->pos;
	retval = iep->pos;

	/* include any others in the work array */
	prev = 0;
	wpp = work;
	wp = *work;
	while (wp) {
		struct object *obj = &wp->item->object;
		struct commit *co;

		/* is this in our cache slice? */
		iep = search_index(obj->sha1);
		if (!iep || hashcmp(idx_caches + iep->cache_index * 20, head->sha1)) {
			/* there are interesing objects outside the slice */
			if (!(obj->flags & UNINTERESTING))
				*ioutside = 1;

			prev = wp;
			wp = wp->next;
			wpp = &wp;
			continue;
		}

		if (iep->pos < retval)
			retval = iep->pos;

		/* mark this for later */
		if (curep == eplen) {
			eplen += 10;
			eps = xrealloc(eps, eplen * sizeof(struct entrance_point));
		}

		eps[curep].pos = iep->pos;
		eps[curep].uninteresting = !!(obj->flags & UNINTERESTING);
		curep++;

		/* count even if not in slice so we can stop enumerating if possible */
		if (obj->flags & UNINTERESTING)
			++*upath_nr;
		else
			++*ipath_nr;

		/* remove from work list */
		co = pop_commit(wpp);
		wp = *wpp;
		if (prev)
			prev->next = wp;

		/* ...and store in temp list so we can restore work on failure */
		commit_list_insert(co, unwork);
	}

	qsort(eps, curep, sizeof(struct entrance_point), eps_sort_callback);
	*peps = eps;
	*peplen = curep;
	return retval;
}

#define IPATH				0x40
#define UPATH				0x80

#define GET_COUNT(x)		((x) & 0x3f)
#define SET_COUNT(x, s)		((x) = ((x) & ~0x3f) | ((s) & 0x3f))

static int traverse_cache_slice_1(struct rc_slice_header *head, unsigned char *map,
	struct rev_info *revs, struct commit *commit,
	unsigned long *date_so_far, int *slop_so_far,
	struct commit_list ***queue, struct commit_list **work)
{
	struct commit_list *insert_cache = 0, *myq = 0, **myqp = &myq, *mywork = 0, **myworkp = &mywork, *unwork = 0;
	struct commit **last_objects, *co;
	unsigned long date = date_so_far ? *date_so_far : ~0ul;
	int i, ipath_nr = 0, upath_nr = 0, orig_obj_nr = 0,
		total_path_nr = head->path_nr, retval = -1, slop = slop_so_far ? *slop_so_far : SLOP;
	char consume_children = 0, ioutside = 0;
	unsigned char *paths;
	struct entrance_point *eps;
	int eplen, curep = 0;

	/* take note in case we need to regress */
	orig_obj_nr = revs->pending.nr;

	i = setup_traversal(head, &eps, &eplen, commit, work, &unwork, &ipath_nr, &upath_nr, &ioutside);
	if (i < 0)
		return -1;

	paths = xcalloc(total_path_nr, sizeof(uint16_t));
	last_objects = xcalloc(total_path_nr, sizeof(struct commit *));

	/* i already set */
	while (i < head->size) {
		struct rc_object_entry *entry = RC_OBTAIN_OBJECT_ENTRY(map + i);
		int path = entry->path;
		struct object *obj;
		int index = i;
		char uninteresting;

		i += RC_ACTUAL_OBJECT_ENTRY_SIZE(entry);

		/* add extra objects if necessary */
		if (entry->type != OBJ_COMMIT) {
			if (consume_children)
				handle_noncommit(revs, co, map + index, entry);

			continue;
		} else
			consume_children = 0;

		if (path >= total_path_nr)
			goto end;

		/* in one of our branches?
		 * uninteresting trumps interesting */
		if (curep < eplen && index == eps[curep].pos)
			paths[path] |= eps[curep++].uninteresting ? UPATH : IPATH;
		else if (!paths[path])
			continue;

		/* date stuff */
		if (revs->max_age != -1 && entry->date < revs->max_age)
			paths[path] |= UPATH;

		/* lookup object */
		co = lookup_commit(entry->sha1);
		obj = &co->object;

		if (obj->flags & UNINTERESTING)
			paths[path] |= UPATH;

		if ((paths[path] & IPATH) && (paths[path] & UPATH)) {
			paths[path] = UPATH;
			ipath_nr--;

			/* mark edge */
			if (last_objects[path]) {
				parse_commit(last_objects[path]);

				/* we needn't worry about the unique field; that will be valid as
				 * long as we're not a end entry */
				last_objects[path]->object.flags &= ~FACE_VALUE;
				last_objects[path] = 0;
			}
			obj->flags |= BOUNDARY;
		}

		/* now we gotta re-assess the whole interesting thing... */
		uninteresting = !!(paths[path] & UPATH);

		/* first close paths */
		if (entry->split_nr) {
			int j, off = index + OBJECT_ENTRY_SIZE + RC_PATH_SIZE(entry->merge_nr);

			for (j = 0; j < entry->split_nr; j++) {
				unsigned short p = ntohs(*(uint16_t *)(map + off + RC_PATH_SIZE(j)));

				if (p >= total_path_nr)
					goto end;

				/* boundary commit? */
				if ((paths[p] & IPATH) && uninteresting) {
					if (last_objects[p]) {
						parse_commit(last_objects[p]);

						last_objects[p]->object.flags &= ~FACE_VALUE;
						last_objects[p] = 0;
					}
					obj->flags |= BOUNDARY;
				} else if (last_objects[p] && !last_objects[p]->object.parsed) {
					commit_list_insert(co, &last_objects[p]->parents);
				}

				/* can't close a merge path until all are parents have been encountered */
				if (GET_COUNT(paths[p])) {
					SET_COUNT(paths[p], GET_COUNT(paths[p]) - 1);

					if (GET_COUNT(paths[p]))
						continue;
				}

				if (paths[p] & IPATH)
					ipath_nr--;
				else
					upath_nr--;

				paths[p] = 0;
				last_objects[p] = 0;
			}
		}

		/* make topo relations */
		if (last_objects[path] && !last_objects[path]->object.parsed) {
			commit_list_insert(co, &last_objects[path]->parents);
		}

		/* we've been here already */
		if (obj->flags & ADDED) {
			if (uninteresting && !(obj->flags & UNINTERESTING)) {
				obj->flags |= UNINTERESTING;
				mark_parents_uninteresting(co);
				upath_nr--;
			} else if (!uninteresting)
				ipath_nr--;

			paths[path] = 0;
			continue;
		}

		/* initialize commit */
		if (!entry->is_end) {
			co->date = entry->date;
			obj->flags |= ADDED;
			if (entry->has_objects)
				obj->flags |= FACE_VALUE;
		} else
			parse_commit(co);

		obj->flags |= SEEN;

		if (uninteresting)
			obj->flags |= UNINTERESTING;
		else if (co->date < date)
			date = co->date;

		/* we need to know what the edges are */
		last_objects[path] = co;

		/* add to list */
		if (slop && !(revs->min_age != -1 && co->date > revs->min_age)) {

			if (!(obj->flags & UNINTERESTING) || revs->show_all) {
				if (entry->is_end)
					myworkp = &commit_list_insert(co, myworkp)->next;
				else
					myqp = &commit_list_insert(co, myqp)->next;

				/* add children to list as well */
				if (obj->flags & UNINTERESTING)
					consume_children = 0;
				else
					consume_children = 1;
			}

		}

		/* should we continue? */
		if (!slop) {
			if (!upath_nr) {
				break;
			} else if (ioutside || revs->show_all) {
				/* pass it back to rev-list
				 * we purposely ignore everything outside this cache, so we don't needlessly traverse the whole
				 * thing on uninteresting, but that does mean that we may need to bounce back
				 * and forth a few times with rev-list */
				myworkp = &commit_list_insert(co, myworkp)->next;

				paths[path] = 0;
				upath_nr--;
			} else {
				break;
			}
		} else if (!ipath_nr && co->date <= date)
			slop--;
		else if (!ipath_nr && !upath_nr)
			break;
		else
			slop = SLOP;

		/* before opening further topo-relations, check if the parenting has had medical attention */
		if (obj->graft) {
			struct commit_list *list;

			parse_commit(co);
			obj->flags &= ~FACE_VALUE;
			last_objects[path] = 0;

			/* we're only interested in its indirect influence */
			for (list = co->parents; list; list = list->next) {
				struct rc_index_entry *iep;
				struct object *po = &list->item->object;

				iep = search_index(po->sha1);
				if (!iep || hashcmp(idx_caches + 20 * iep->cache_index, head->sha1)) {
					if (!(obj->flags & UNINTERESTING) && !(po->flags & UNINTERESTING))
						ioutside = 1;
				}
			}

			/* an abrupt end */
			myworkp = &commit_list_insert(co, myworkp)->next;
			if (uninteresting)
				upath_nr--;
			else
				ipath_nr--;
			paths[path] = 0;
			continue;
		}

		/* open parents */
		if (entry->merge_nr) {
			int j, off = index + OBJECT_ENTRY_SIZE;
			char flag = uninteresting ? UPATH : IPATH;

			for (j = 0; j < entry->merge_nr; j++) {
				unsigned short p = ntohs(*(uint16_t *)(map + off + RC_PATH_SIZE(j)));

				if (p >= total_path_nr)
					goto end;

				if (paths[p] & flag)
					continue;

				if (flag == IPATH)
					ipath_nr++;
				else
					upath_nr++;

				paths[p] |= flag;
			}

			/* make sure we don't use this path before all our parents have had their say */
			SET_COUNT(paths[path], entry->merge_nr);
		}

	}

	if (date_so_far)
		*date_so_far = date;
	if (slop_so_far)
		*slop_so_far = slop;
	retval = 0;

	/* success: attach to given lists */
	if (myqp != &myq) {
		**queue = myq;
		*queue = myqp;
	}

	while ((co = pop_commit(&mywork)) != 0)
		insert_by_date_cached(co, work, insert_cache, &insert_cache);

	/* free backup */
	while (pop_commit(&unwork))
		;

end:
	free(paths);
	free(last_objects);
	free(eps);

	/* failure: restore work to previous condition
	 * (cache corruption should *not* be fatal) */
	if (retval) {
		while ((co = pop_commit(&unwork)) != 0) {
			restore_commit(co);
			co->object.flags |= SEEN;
			insert_by_date(co, work);
		}

		/* free lists */
		while ((co = pop_commit(&myq)) != 0)
			restore_commit(co);

		while ((co = pop_commit(&mywork)) != 0)
			restore_commit(co);

		/* truncate object array */
		for (i = orig_obj_nr; i < revs->pending.nr; i++) {
			struct object *obj = revs->pending.objects[i].item;

			obj->flags &= ~FACE_VALUE;
		}
		revs->pending.nr = orig_obj_nr;
	}

	return retval;
}

static struct name_list *get_cache_slice_name_list(struct rc_slice_header *head, int fd)
{
	struct name_list *nl = name_lists;

	while (nl) {
		if (!hashcmp(nl->sha1, head->sha1))
			break;
		nl = nl->next;
	}

	if (nl)
		return nl;

	nl = xcalloc(1, sizeof(struct name_list) + head->name_size);
	nl->len = head->name_size;
	hashcpy(nl->sha1, head->sha1);

	lseek(fd, head->size, SEEK_SET);
	read_in_full(fd, nl->buf, head->name_size);

	nl->next = name_lists;
	name_lists = nl;

	return nl;
}

static int get_cache_slice_header(int fd, unsigned char *cache_sha1, int len, struct rc_slice_header *head)
{
	int t;
	unsigned char whead[SLICE_HEADER_SIZE];

	if (xread(fd, whead, SLICE_HEADER_SIZE) != SLICE_HEADER_SIZE)
		return -1;

	memcpy(head->signature, whead, 8);
	head->version = *(whead + 8);
	head->ofs_objects = UNPACK_UINT32(whead + 9);

	head->object_nr = UNPACK_UINT32(whead + 13);
	head->path_nr = UNPACK_UINT16(whead + 17);
	head->size = UNPACK_UINT32(whead + 19);

	hashcpy(head->sha1, whead + 23);
	head->name_size = UNPACK_UINT32(whead + 43);

	if (memcmp(head->signature, "REVCACHE", 8))
		return -1;
	if (head->version != SUPPORTED_REVCACHE_VERSION)
		return -2;
	if (hashcmp(head->sha1, cache_sha1))
		return -3;
	t = SLICE_HEADER_SIZE;
	if (t != head->ofs_objects)
		return -4;
	if (head->size + head->name_size != len)
		return -5;

	return 0;
}

int open_cache_slice(unsigned char *sha1, int flags)
{
	int fd;
	char signature[8];

	fd = open(git_path("rev-cache/%s", sha1_to_hex(sha1)), flags);
	if (fd <= 0)
		goto end;

	if (read(fd, signature, 8) != 8)
		goto end;

	/* a normal revision slice */
	if (!memcmp(signature, "REVCACHE", 8)) {
		lseek(fd, 0, SEEK_SET);
		return fd;
	}

	/* slice pointer */
	if (!memcmp(signature, "REVCOPTR", 8)) {
		struct cache_slice_pointer ptr;

		if (read(fd, &ptr.version, 1) != 1 || ptr.version > SUPPORTED_REVCOPTR_VERSION)
			goto end;

		if (read_in_full(fd, ptr.path, sizeof(ptr.path)) != sizeof(ptr.path))
			goto end;

		close(fd);
		fd = open(ptr.path, flags);

		return fd;
	}

end:
	if (fd > 0)
		close(fd);

	return -1;
}

int traverse_cache_slice(struct rev_info *revs,
	unsigned char *cache_sha1, struct commit *commit,
	unsigned long *date_so_far, int *slop_so_far,
	struct commit_list ***queue, struct commit_list **work)
{
	int fd = -1, t, retval;
	struct stat fi;
	struct rc_slice_header head;
	struct rev_cache_info *rci;
	unsigned char *map = MAP_FAILED;

	/* the index should've been loaded already to find cache_sha1, but it's good
	 * to be absolutely sure... */
	if (!idx_map)
		init_index();
	if (!idx_map)
		return -1;

	/* load options */
	rci = &revs->rev_cache_info;
	add_to_pending = rci->add_to_pending;
	add_names = rci->add_names;

	memset(&head, 0, sizeof(struct rc_slice_header));
#	define ERROR(x)		do { retval = (x); goto end; } while (0);

	fd = open_cache_slice(cache_sha1, O_RDONLY);
	if (fd == -1)
		ERROR(-1);
	if (fstat(fd, &fi) || fi.st_size < SLICE_HEADER_SIZE)
		ERROR(-2);

	if ((t = get_cache_slice_header(fd, cache_sha1, fi.st_size, &head)) < 0)
		ERROR(-t);
	if (add_names)
		cur_name_list = get_cache_slice_name_list(&head, fd);

	map = xmmap(0, head.size, PROT_READ, MAP_PRIVATE, fd, 0);
	if (map == MAP_FAILED)
		ERROR(-3);

	retval = traverse_cache_slice_1(&head, map, revs, commit, date_so_far, slop_so_far, queue, work);

end:
	if (map != MAP_FAILED)
		munmap(map, head.size);
	if (fd != -1)
		close(fd);

	/* remember this! */
	if (retval)
		mark_bad_slice(cache_sha1);

#	undef ERROR
	return retval;
}



/* generation */

static int is_endpoint(struct commit *commit)
{
	struct commit_list *list = commit->parents;

	while (list) {
		if (!(list->item->object.flags & UNINTERESTING))
			return 0;

		list = list->next;
	}

	return 1;
}

/* ensures branch is self-contained: parents are either all interesting or all uninteresting */
static void make_legs(struct rev_info *revs)
{
	struct commit_list *list, **plist;
	int total = 0;

	/* attach plist to end of commits list */
	list = revs->commits;
	while (list && list->next)
		list = list->next;

	if (list)
		plist = &list->next;
	else
		return;

	/* duplicates don't matter, as get_revision() ignores them */
	for (list = revs->commits; list; list = list->next) {
		struct commit *item = list->item;
		struct commit_list *parents = item->parents;

		if (item->object.flags & UNINTERESTING)
			continue;
		if (is_endpoint(item))
			continue;

		while (parents) {
			struct commit *p = parents->item;
			parents = parents->next;

			if (!(p->object.flags & UNINTERESTING))
				continue;

			p->object.flags &= ~UNINTERESTING;
			parse_commit(p);
			plist = &commit_list_insert(p, plist)->next;

			if (!(p->object.flags & SEEN))
				total++;
		}
	}

	if (total)
		sort_in_topological_order(&revs->commits, 1);

}


struct path_track {
	struct commit *commit;
	int path; /* for keeping track of children */

	struct path_track *next, *prev;
};

static unsigned char *paths;
static int path_nr = 1, path_sz;

static struct path_track *path_track;
static struct path_track *path_track_alloc;

#define PATH_IN_USE			0x80 /* biggest bit we can get as a char */

static int get_new_path(void)
{
	int i;

	for (i = 1; i < path_nr; i++)
		if (!paths[i])
			break;

	if (i == path_nr) {
		if (path_nr >= path_sz) {
			path_sz += 50;
			paths = xrealloc(paths, path_sz);
			memset(paths + path_sz - 50, 0, 50);
		}
		path_nr++;
	}

	paths[i] = PATH_IN_USE;
	return i;
}

static void remove_path_track(struct path_track **ppt, char total_free)
{
	struct path_track *t = *ppt;

	if (t->next)
		t->next->prev = t->prev;
	if (t->prev)
		t->prev->next = t->next;

	t = t->next;

	if (total_free)
		free(*ppt);
	else {
		(*ppt)->next = path_track_alloc;
		path_track_alloc = *ppt;
	}

	*ppt = t;
}

static struct path_track *make_path_track(struct path_track **head, struct commit *commit)
{
	struct path_track *pt;

	if (path_track_alloc) {
		pt = path_track_alloc;
		path_track_alloc = pt->next;
	} else
		pt = xmalloc(sizeof(struct path_track));

	memset(pt, 0, sizeof(struct path_track));
	pt->commit = commit;

	pt->next = *head;
	if (*head)
		(*head)->prev = pt;
	*head = pt;

	return pt;
}

static void add_path_to_track(struct commit *commit, int path)
{
	make_path_track(&path_track, commit);
	path_track->path = path;
}

static void handle_paths(struct commit *commit, struct rc_object_entry *object, struct strbuf *merge_str, struct strbuf *split_str)
{
	int child_nr, parent_nr, open_parent_nr, this_path;
	struct commit_list *list;
	struct commit *first_parent;
	struct path_track **ppt, *pt;

	/* we can only re-use a closed path once all it's children have been encountered,
	 * as we need to keep track of commit boundaries */
	ppt = &path_track;
	pt = *ppt;
	child_nr = 0;
	while (pt) {
		if (pt->commit == commit) {
			uint16_t write_path;

			if (paths[pt->path] != PATH_IN_USE)
				paths[pt->path]--;

			/* make sure we can handle this */
			child_nr++;
			if (child_nr > 0x7f)
				die("%s: too many branches!  rev-cache can only handle %d parents/children per commit",
					sha1_to_hex(object->sha1), 0x7f);

			/* add to split list */
			object->split_nr++;
			write_path = htons((uint16_t)pt->path);
			strbuf_add(split_str, &write_path, sizeof(uint16_t));

			remove_path_track(ppt, 0);
			pt = *ppt;
		} else {
			pt = pt->next;
			ppt = &pt;
		}
	}

	/* initialize our self! */
	if (!commit->indegree) {
		commit->indegree = get_new_path();
		object->is_start = 1;
	}

	this_path = commit->indegree;
	paths[this_path] = PATH_IN_USE;
	object->path = this_path;

	/* count interesting parents */
	parent_nr = open_parent_nr = 0;
	first_parent = 0;
	for (list = commit->parents; list; list = list->next) {
		if (list->item->object.flags & UNINTERESTING) {
			object->is_end = 1;
			continue;
		}

		parent_nr++;
		if (!list->item->indegree)
			open_parent_nr++;
		if (!first_parent)
			first_parent = list->item;
	}

	if (!parent_nr)
		return;

	if (parent_nr == 1 && open_parent_nr == 1) {
		first_parent->indegree = this_path;
		return;
	}

	/* bail out on obscene parent/child #s */
	if (parent_nr > 0x7f)
		die("%s: too many parents in merge!  rev-cache can only handle %d parents/children per commit",
			sha1_to_hex(object->sha1), 0x7f);

	/* make merge list */
	object->merge_nr = parent_nr;
	paths[this_path] = parent_nr;

	for (list = commit->parents; list; list = list->next) {
		struct commit *p = list->item;
		uint16_t write_path;

		if (p->object.flags & UNINTERESTING)
			continue;

		/* unfortunately due to boundary tracking we can't re-use merge paths
		 * (unable to guarantee last parent path = this -> last won't always be able to
		 * set this as a boundary object */
		if (!p->indegree)
			p->indegree = get_new_path();

		write_path = htons((uint16_t)p->indegree);
		strbuf_add(merge_str, &write_path, sizeof(uint16_t));

		/* make sure path is properly ended */
		add_path_to_track(p, this_path);
	}

}


static int encode_size(unsigned long size, unsigned char *out)
{
	int len = 0;

	while (size) {
		*out++ = (unsigned char)(size & 0xff);
		size >>= 8;
		len++;
	}

	return len;
}

static unsigned long decode_size(unsigned char *str, int len)
{
	unsigned long size = 0;
	int shift = 0;

	while (len--) {
		size |= (unsigned long)*str << shift;
		shift += 8;
		str++;
	}

	return size;
}


#define NL_HASH_TABLE_SIZE		(0xffff + 1)
#define NL_HASH_NUMBER			(NL_HASH_TABLE_SIZE >> 3)

struct name_list_hash {
	int ind;
	struct name_list_hash *next;
};

static struct name_list_hash **nl_hash_table;
static unsigned char *nl_hashes;

/* FNV-1a hash */
static unsigned int hash_name(const char *name)
{
	unsigned int hash = 2166136261ul;
	const char *p = name;

	while (*p) {
		hash ^= *p++;
		hash *= 16777619ul;
	}

	return hash & 0xffff;
}

static int name_in_list(const char *name)
{
	unsigned int h = hash_name(name);
	struct name_list_hash *entry = nl_hash_table[h];

	while (entry && strcmp(acc_name_buffer->buf + entry->ind, name))
		entry = entry->next;

	if (entry)
		return entry->ind;

	/* add name to buffer and create hash reference */
	entry = xcalloc(1, sizeof(struct name_list_hash));
	entry->ind = acc_name_buffer->len;
	strbuf_add(acc_name_buffer, name, strlen(name) + 1);

	entry->next = nl_hash_table[h];
	nl_hash_table[h] = entry;

	nl_hashes[h / 8] |= h % 8;

	return entry->ind;
}

static void init_name_list_hash(void)
{
	nl_hash_table = xcalloc(NL_HASH_TABLE_SIZE, sizeof(struct name_list_hash));
	nl_hashes = xcalloc(NL_HASH_NUMBER, 1);
}

static void cleanup_name_list_hash(void)
{
	int i;

	for (i = 0; i < NL_HASH_NUMBER; i++) {
		int j, ind = nl_hashes[i];

		if (!ind)
			continue;

		for (j = 0; j < 8; j++) {
			struct name_list_hash **entryp;

			if (!(ind & 1 << j))
				continue;

			entryp = &nl_hash_table[i * 8 + j];
			while (*entryp) {
				struct name_list_hash *t = (*entryp)->next;

				free(*entryp);
				*entryp = t;
			}
		}
	} /* code overhang! */

	free(nl_hashes);
	free(nl_hash_table);
}

static void add_object_entry(const unsigned char *sha1, struct rc_object_entry *entryp,
	struct strbuf *merge_str, struct strbuf *split_str, char *name, unsigned long size)
{
	struct rc_object_entry entry;
	unsigned char size_str[7], name_str[7];
	enum object_type type;
	void *data;

	if (entryp)
		sha1 = entryp->sha1;

	if (!size) {
		/* retrieve size data */
		data = read_sha1_file(sha1, &type, &size);

		if (data)
			free(data);
	}

	/* initialize! */
	if (!entryp) {
		memset(&entry, 0, sizeof(entry));
		entry.sha1 = (unsigned char *)sha1;
		entry.type = type;

		if (merge_str)
			entry.merge_nr = merge_str->len / sizeof(uint16_t);
		if (split_str)
			entry.split_nr = split_str->len / sizeof(uint16_t);

		entryp = &entry;
	}

	entryp->size_size = encode_size(size, size_str);

	if (name)
		entryp->name_size = encode_size(name_in_list(name), name_str);

	/* write the muvabitch */
	strbuf_add(acc_buffer, to_disked_rc_object_entry(entryp, 0), OBJECT_ENTRY_SIZE);

	if (merge_str)
		strbuf_add(acc_buffer, merge_str->buf, merge_str->len);
	if (split_str)
		strbuf_add(acc_buffer, split_str->buf, split_str->len);

	strbuf_add(acc_buffer, size_str, entryp->size_size);

	if (name)
		strbuf_add(acc_buffer, name_str, entryp->name_size);
}

/* returns non-zero to continue parsing, 0 to skip */
typedef int (*dump_tree_fn)(const unsigned char *, const char *, unsigned int); /* sha1, path, mode */

/* we need to walk the trees by hash, so unfortunately we can't use traverse_trees in tree-walk.c */
static int dump_tree(struct tree *tree, dump_tree_fn fn, char *base)
{
	struct tree_desc desc;
	struct name_entry entry;
	struct tree *subtree;
	char concatpath[PATH_MAX];
	int r, baselen;

	if (parse_tree(tree))
		return -1;

	baselen = strlen(base);
	strcpy(concatpath, base);

	init_tree_desc(&desc, tree->buffer, tree->size);
	while (tree_entry(&desc, &entry)) {
		if (baselen + strlen(entry.path) + 1 >= PATH_MAX)
			die("we have a problem: %s%s is too big for me to handle", base, entry.path);
		strcpy(concatpath + baselen, entry.path);

		switch (fn(entry.sha1, concatpath, entry.mode)) {
		case 0:
			goto continue_loop;
		default:
			break;
		}

		if (S_ISDIR(entry.mode)) {
			subtree = lookup_tree(entry.sha1);
			if (!subtree)
				return -2;

			strcat(concatpath, "/");
			if ((r = dump_tree(subtree, fn, concatpath)) < 0)
				return r;
		}

continue_loop:
		continue;
	}

	return 0;
}

static int dump_tree_callback(const unsigned char *sha1, const char *path, unsigned int mode)
{
	strbuf_add(acc_buffer, sha1, 20);
	strbuf_add(acc_buffer, (char *)&acc_name_buffer->len, sizeof(size_t));

	strbuf_add(acc_name_buffer, path, strlen(path) + 1);

	return 1;
}

static void tree_addremove(struct diff_options *options,
	int whatnow, unsigned mode,
	const unsigned char *sha1,
	const char *concatpath, unsigned dirty_sub)
{
	strbuf_add(acc_buffer, sha1, 20);
	strbuf_add(acc_buffer, (char *)&acc_name_buffer->len, sizeof(size_t));

	strbuf_add(acc_name_buffer, concatpath, strlen(concatpath) + 1);
}

static void tree_change(struct diff_options *options,
	unsigned old_mode, unsigned new_mode,
	const unsigned char *old_sha1,
	const unsigned char *new_sha1,
	const char *concatpath,
	unsigned old_dirty_sub, unsigned new_dirty_sub)
{
	strbuf_add(acc_buffer, new_sha1, 20);
	strbuf_add(acc_buffer, (char *)&acc_name_buffer->len, sizeof(size_t));

	strbuf_add(acc_name_buffer, concatpath, strlen(concatpath) + 1);
}

static int add_unique_objects(struct commit *commit)
{
	struct commit_list *list;
	struct strbuf os, ost, names, *orig_name_buf, *orig_buf;
	struct diff_options opts;
	int i, j, next;
	char is_first = 1;

	/* ...no, calculate unique objects */
	strbuf_init(&os, 0);
	strbuf_init(&ost, 0);
	strbuf_init(&names, 0);
	orig_buf = acc_buffer;
	orig_name_buf = acc_name_buffer;
	acc_name_buffer = &names;

	diff_setup(&opts);
	DIFF_OPT_SET(&opts, RECURSIVE);
	DIFF_OPT_SET(&opts, TREE_IN_RECURSIVE);
	opts.change = tree_change;
	opts.add_remove = tree_addremove;
#	define ENTRY_SIZE (20 + sizeof(size_t))

	/* this is only called for non-ends (ie. all parents interesting) */
	for (list = commit->parents; list; list = list->next) {
		if (is_first)
			acc_buffer = &os;
		else
			acc_buffer = &ost;

		strbuf_setlen(acc_buffer, 0);
		diff_tree_sha1(list->item->tree->object.sha1, commit->tree->object.sha1, "", &opts);
		qsort(acc_buffer->buf, acc_buffer->len / ENTRY_SIZE, ENTRY_SIZE, (int (*)(const void *, const void *))hashcmp);

		/* take intersection */
		if (!is_first) {
			for (next = i = j = 0; i < os.len; i += ENTRY_SIZE) {
				while (j < ost.len && hashcmp((unsigned char *)(ost.buf + j), (unsigned char *)(os.buf + i)) < 0)
					j += ENTRY_SIZE;

				if (j >= ost.len || hashcmp((unsigned char *)(ost.buf + j), (unsigned char *)(os.buf + i)))
					continue;

				if (next != i)
					memcpy(os.buf + next, os.buf + i, ENTRY_SIZE);
				next += ENTRY_SIZE;
			}

			if (next != i)
				strbuf_setlen(&os, next);
		} else
			is_first = 0;
	}

	/* no parents (!) */
	if (is_first) {
		acc_buffer = &os;
		dump_tree(commit->tree, dump_tree_callback, "");
	}

	/* the ordering of non-commit objects dosn't really matter, so we're not gonna bother */
	acc_buffer = orig_buf;
	acc_name_buffer = orig_name_buf;
	for (i = 0; i < os.len; i += ENTRY_SIZE)
		add_object_entry((unsigned char *)(os.buf + i), 0, 0, 0, names.buf + *(size_t *)(os.buf + i + 20), 0);

	/* last but not least, the main tree */
	add_object_entry(commit->tree->object.sha1, 0, 0, 0, 0, 0);

	strbuf_release(&ost);
	strbuf_release(&os);
	strbuf_release(&names);

	return i / ENTRY_SIZE + 1;
#	undef ENTRY_SIZE
}

static int add_objects_verbatim_1(struct rev_cache_slice_map *mapping, int *index)
{
	int i = *index, object_nr = 0;
	unsigned char *map = mapping->map;
	struct rc_object_entry *entry = RC_OBTAIN_OBJECT_ENTRY(map + i);
	unsigned long size;

	i += RC_ACTUAL_OBJECT_ENTRY_SIZE(entry);
	while (i < mapping->size) {
		char *name;
		int name_index, pos = i;

		entry = RC_OBTAIN_OBJECT_ENTRY(map + i);
		i += RC_ACTUAL_OBJECT_ENTRY_SIZE(entry);

		if (entry->type == OBJ_COMMIT) {
			*index = pos;
			return object_nr;
		}

		name_index = decode_size(map + pos + RC_ENTRY_NAME_OFFSET(entry), entry->name_size);
		if (name_index && name_index < mapping->name_size)
			name = mapping->names + name_index;
		else
			name = 0;

		size = decode_size(map + pos + RC_ENTRY_SIZE_OFFSET(entry), entry->size_size);

		add_object_entry(0, entry, 0, 0, name, size);
		object_nr++;
	}

	*index = 0;
	return object_nr;
}

static int add_objects_verbatim(struct rev_cache_info *rci, struct commit *commit)
{
	struct rev_cache_slice_map *map;
	char found = 0;
	struct rc_index_entry *ie;
	struct rc_object_entry *entry;
	int object_nr, i;

	if (!rci->maps)
		return -1;

	/* check if we can continue where we left off */
	map = rci->last_map;
	if (!map)
		goto search_me;

	i = map->last_index;
	entry = RC_OBTAIN_OBJECT_ENTRY(map->map + i);
	if (hashcmp(entry->sha1, commit->object.sha1))
		goto search_me;

	found = 1;

search_me:
	if (!found) {
		ie = search_index(commit->object.sha1);
		if (!ie || ie->cache_index >= idx_head.cache_nr)
			return -2;

		map = rci->maps + ie->cache_index;
		if (!map->size)
			return -3;

		i = ie->pos;
		entry = RC_OBTAIN_OBJECT_ENTRY(map->map + i);
		if (entry->type != OBJ_COMMIT || hashcmp(entry->sha1, commit->object.sha1))
			return -4;
	}

	/* can't handle end commits */
	if (entry->is_end)
		return -5;

	object_nr = add_objects_verbatim_1(map, &i);

	/* remember this */
	if (i) {
		rci->last_map = map;
		map->last_index = i;
	} else
		rci->last_map = 0;

	return object_nr;
}

static void init_revcache_directory(void)
{
	struct stat fi;

	if (stat(git_path("rev-cache"), &fi) || !S_ISDIR(fi.st_mode))
		if (mkdir(git_path("rev-cache"), 0777))
			die("can't make rev-cache directory");

}

void init_rev_cache_info(struct rev_cache_info *rci)
{
	memset(rci, 0, sizeof(struct rev_cache_info));

	rci->objects = 1;
	rci->legs = 0;
	rci->make_index = 1;
	rci->fuse_me = 0;

	rci->overwrite_all = 0;

	rci->add_to_pending = 1;
	rci->add_names = 1;

	rci->ignore_size = 0;
}

void maybe_fill_with_defaults(struct rev_cache_info *rci)
{
	static struct rev_cache_info def_rci;

	if (rci)
		return;

	init_rev_cache_info(&def_rci);
	rci = &def_rci;
}

int make_cache_slice(struct rev_cache_info *rci,
	struct rev_info *revs, struct commit_list **starts, struct commit_list **ends,
	unsigned char *cache_sha1)
{
	struct rev_info therevs;
	struct strbuf buffer, startlist, endlist;
	struct rc_slice_header head;
	struct commit *commit;
	unsigned char sha1[20], whead[SLICE_HEADER_SIZE];
	struct strbuf merge_paths, split_paths, namelist;
	int object_nr, total_sz, fd;
	char file[PATH_MAX], null, *newfile;
	struct rev_cache_info *trci;
	git_SHA_CTX ctx;

	maybe_fill_with_defaults(rci);

	init_revcache_directory();
	strcpy(file, git_path("rev-cache/XXXXXX"));
	fd = xmkstemp(file);

	strbuf_init(&buffer, 0);
	strbuf_init(&startlist, 0);
	strbuf_init(&endlist, 0);
	strbuf_init(&merge_paths, 0);
	strbuf_init(&split_paths, 0);
	strbuf_init(&namelist, 0);
	acc_buffer = &buffer;
	acc_name_buffer = &namelist;

	null = 0;
	strbuf_add(&namelist, &null, 1);
	init_name_list_hash();

	if (!revs) {
		revs = &therevs;
		init_revisions(revs, 0);

		/* we're gonna assume no one else has already traversed this... */
		while ((commit = pop_commit(starts)))
			add_pending_object(revs, &commit->object, 0);

		while ((commit = pop_commit(ends))) {
			commit->object.flags |= UNINTERESTING;
			add_pending_object(revs, &commit->object, 0);
		}
	}

	/* write head placeholder */
	memset(&head, 0, sizeof(head));
	memset(&whead, 0, SLICE_HEADER_SIZE);
	head.ofs_objects = SLICE_HEADER_SIZE;
	xwrite(fd, &whead, SLICE_HEADER_SIZE);

	/* init revisions! */
	revs->tree_objects = 1;
	revs->blob_objects = 1;
	revs->topo_order = 1;
	revs->lifo = 1;

	/* re-use info from other caches if possible */
	trci = &revs->rev_cache_info;
	init_rev_cache_info(trci);
	trci->add_to_pending = 0;
	trci->add_names = 0;

	setup_revisions(0, 0, revs, 0);
	if (prepare_revision_walk(revs))
		die("died preparing revision walk");

	if (rci->legs)
		make_legs(revs);

	object_nr = total_sz = 0;
	while ((commit = get_revision(revs)) != 0) {
		struct rc_object_entry object;
		int t;

		strbuf_setlen(&merge_paths, 0);
		strbuf_setlen(&split_paths, 0);

		memset(&object, 0, sizeof(object));
		object.type = OBJ_COMMIT;
		object.date = commit->date;
		object.sha1 = commit->object.sha1;

		handle_paths(commit, &object, &merge_paths, &split_paths);

		if (object.is_end) {
			strbuf_add(&endlist, object.sha1, 20);
			if (ends)
				commit_list_insert(commit, ends);
		}
		/* the two *aren't* mutually exclusive */
		if (object.is_start) {
			strbuf_add(&startlist, object.sha1, 20);
			if (starts)
				commit_list_insert(commit, starts);
		}

		if (rci->objects)
			object.has_objects = 1;

		commit->indegree = 0;

		add_object_entry(0, &object, &merge_paths, &split_paths, 0, 0);
		object_nr++;

		if (rci->objects && !object.is_end) {
			if (rci->fuse_me && (t = add_objects_verbatim(rci, commit)) >= 0)
				/* yay!  we did it! */
				object_nr += t;
			else
				/* add all unique children for this commit */
				object_nr += add_unique_objects(commit);
		}

		/* print every ~1MB or so */
		if (buffer.len > 1000000) {
			write_in_full(fd, buffer.buf, buffer.len);
			total_sz += buffer.len;

			strbuf_setlen(&buffer, 0);
		}
	}

	if (buffer.len) {
		write_in_full(fd, buffer.buf, buffer.len);
		total_sz += buffer.len;
	}

	/* write path name lookup list */
	head.name_size = namelist.len;
	write_in_full(fd, namelist.buf, namelist.len);

	/* go ahead a free some stuff... */
	strbuf_release(&buffer);
	strbuf_release(&merge_paths);
	strbuf_release(&split_paths);
	strbuf_release(&namelist);
	cleanup_name_list_hash();
	if (path_sz)
		free(paths);
	while (path_track_alloc)
		remove_path_track(&path_track_alloc, 1);

	/* the meaning of the hash name is more or less irrelevant, it's the uniqueness that matters */
	strbuf_add(&endlist, startlist.buf, startlist.len);
	git_SHA1_Init(&ctx);
	git_SHA1_Update(&ctx, endlist.buf, endlist.len);
	git_SHA1_Final(sha1, &ctx);

	/* initialize header */
	strcpy(head.signature, "REVCACHE");
	head.version = SUPPORTED_REVCACHE_VERSION;

	head.object_nr = object_nr;
	head.size = head.ofs_objects + total_sz;
	head.path_nr = path_nr;
	hashcpy(head.sha1, sha1);

	/* ...and whead */
	memcpy(whead, "REVCACHE", 8);
	*(whead + 8) = head.version;
	PACK_UINT32(whead + 9, head.ofs_objects);

	PACK_UINT32(whead + 13, head.object_nr);
	PACK_UINT16(whead + 17, head.path_nr);

	PACK_UINT32(whead + 19, head.size);
	hashcpy(whead + 23, head.sha1);

	PACK_UINT32(whead + 43, head.name_size);

	/* some info! */
	fprintf(stderr, "objects: %d\n", object_nr);
	fprintf(stderr, "paths: %d\n", path_nr);

	lseek(fd, 0, SEEK_SET);
	xwrite(fd, &whead, SLICE_HEADER_SIZE);

	if (rci->make_index && make_cache_index(rci, sha1, fd, head.size) < 0)
		die("can't update index");

	close(fd);

	newfile = git_path("rev-cache/%s", sha1_to_hex(sha1));
	if (rename(file, newfile))
		die("can't move temp file");

	/* let our caller know what we've just made */
	if (cache_sha1)
		hashcpy(cache_sha1, sha1);

	strbuf_release(&endlist);
	strbuf_release(&startlist);

	return 0;
}


static int index_sort_hash(const void *a, const void *b)
{
	return hashcmp(((struct rc_index_entry_ondisk *)a)->sha1, ((struct rc_index_entry_ondisk *)b)->sha1);
}

static int write_cache_index(struct strbuf *body)
{
	unsigned char whead[INDEX_HEADER_SIZE];
	struct lock_file *lk;
	int fd, i;

	/* clear index map if loaded */
	if (idx_map) {
		munmap(idx_map, idx_size);
		idx_map = 0;
	}

	lk = xcalloc(sizeof(struct lock_file), 1);
	fd = hold_lock_file_for_update(lk, git_path("rev-cache/index"), 0);
	if (fd < 0) {
		free(lk);
		return -1;
	}

	/* endianness yay! */
	memcpy(whead, "REVINDEX", 8);
	*(whead + 8) = idx_head.version;
	PACK_UINT32(whead + 9, idx_head.ofs_objects);
	PACK_UINT32(whead + 13, idx_head.object_nr);
	*(whead + 17) = idx_head.cache_nr;
	PACK_UINT32(whead + 18, idx_head.max_date);

	write(fd, &whead, INDEX_HEADER_SIZE);
	write_in_full(fd, idx_caches, idx_head.cache_nr * 20);

	for (i = 0; i <= 0xff; i++)
		fanout[i] = htonl(fanout[i]);
	write_in_full(fd, fanout, 0x100 * sizeof(uint32_t));

	write_in_full(fd, body->buf, body->len);

	if (commit_lock_file(lk) < 0)
		return -2;

	/* lk freed by lockfile.c */

	return 0;
}

int make_cache_index(struct rev_cache_info *rci, unsigned char *cache_sha1,
	int fd, unsigned int size)
{
	struct strbuf buffer;
	int i, cache_index, cur;
	unsigned char *map;
	unsigned long max_date;

	maybe_fill_with_defaults(rci);

	if (!idx_map)
		init_index();

	lseek(fd, 0, SEEK_SET);
	map = xmmap(0, size, PROT_READ, MAP_PRIVATE, fd, 0);
	if (map == MAP_FAILED)
		return -1;

	strbuf_init(&buffer, 0);
	if (idx_map) {
		strbuf_add(&buffer, idx_map + fanout[0], fanout[0x100] - fanout[0]);
	} else {
		/* not an update */
		memset(&idx_head, 0, sizeof(struct rc_index_header));
		idx_caches = 0;

		strcpy(idx_head.signature, "REVINDEX");
		idx_head.version = SUPPORTED_REVINDEX_VERSION;
		idx_head.ofs_objects = INDEX_HEADER_SIZE + 0x100 * sizeof(uint32_t);
	}

	/* are we remaking a slice? */
	for (i = 0; i < idx_head.cache_nr; i++)
		if (!hashcmp(idx_caches + i * 20, cache_sha1))
			break;

	if (i == idx_head.cache_nr) {
		cache_index = idx_head.cache_nr++;
		idx_head.ofs_objects += 20;

		fprintf(stderr, "bla: %d\n", idx_head.cache_nr * 20);
		idx_caches = xrealloc(idx_caches, idx_head.cache_nr * 20);
		hashcpy(idx_caches + cache_index * 20, cache_sha1);
	} else
		cache_index = i;

	i = SLICE_HEADER_SIZE; /* offset */
	max_date = idx_head.max_date;
	while (i < size) {
		struct rc_index_entry index_entry, *entry;
		unsigned char *disked_entry;
		struct rc_object_entry *object_entry = RC_OBTAIN_OBJECT_ENTRY(map + i);
		unsigned long date;
		int off, pos = i;

		i += RC_ACTUAL_OBJECT_ENTRY_SIZE(object_entry);

		if (object_entry->type != OBJ_COMMIT)
			continue;

		/* don't include ends; otherwise we'll find ourselves in loops */
		if (object_entry->is_end)
			continue;

		/* handle index duplication
		 * -> keep old copy unless new one is a start -- based on expected usage, older ones will be more
		 * likely to lead to greater slice traversals than new ones */
		date = object_entry->date;
		if (date > idx_head.max_date) {
			disked_entry = 0;
			if (date > max_date)
				max_date = date;
		} else
			disked_entry = search_index_1(object_entry->sha1);

		if (disked_entry && !object_entry->is_start && !rci->overwrite_all)
			continue;
		else if (disked_entry) {
			/* mmm, pointer arithmetic... tasty */  /* (entry - idx_map = offset, so cast is valid) */
			off = (unsigned int)((unsigned char *)disked_entry - idx_map) - fanout[0];
			disked_entry = (unsigned char *)(buffer.buf + off);
			entry = from_disked_rc_index_entry(disked_entry, 0);
		} else
			entry = &index_entry;

		memset(entry, 0, sizeof(index_entry));
		entry->sha1 = object_entry->sha1;
		entry->is_start = object_entry->is_start;
		entry->cache_index = cache_index;
		entry->pos = pos;

		if (entry == &index_entry) {
			strbuf_add(&buffer, to_disked_rc_index_entry(entry, 0), INDEX_ENTRY_SIZE);
			idx_head.object_nr++;
		} else
			to_disked_rc_index_entry(entry, &disked_entry);

	}

	idx_head.max_date = max_date;
	qsort(buffer.buf, buffer.len / INDEX_ENTRY_SIZE, INDEX_ENTRY_SIZE, index_sort_hash);

	/* generate fanout */
	cur = 0x00;
	for (i = 0; i < buffer.len; i += INDEX_ENTRY_SIZE) {
		struct rc_index_entry_ondisk *entry = (struct rc_index_entry_ondisk *)(buffer.buf + i);

		while (cur <= entry->sha1[0])
			fanout[cur++] = i + idx_head.ofs_objects;
	}

	while (cur <= 0xff)
		fanout[cur++] = idx_head.ofs_objects + buffer.len;

	/* BOOM! */
	if (write_cache_index(&buffer))
		return -1;

	munmap(map, size);
	strbuf_release(&buffer);

	/* idx_map is unloaded without cleanup_cache_slices(), so regardless of previous index existence
	 * we can still free this up */
	free(idx_caches);

	return 0;
}


void starts_from_slices(struct rev_info *revs, unsigned int flags, unsigned char *which, int n)
{
	struct commit *commit;
	int i;

	if (!idx_map)
		init_index();
	if (!idx_map)
		return;

	for (i = idx_head.ofs_objects; i < idx_size; i += INDEX_ENTRY_SIZE) {
		struct rc_index_entry *entry = RC_OBTAIN_INDEX_ENTRY(idx_map + i);

		if (!entry->is_start)
			continue;

		/* only include entries in 'which' slices */
		if (n) {
			int j;

			for (j = 0; j < n; j++)
				if (!hashcmp(idx_caches + entry->cache_index * 20, which + j * 20))
					break;

			if (j == n)
				continue;
		}

		commit = lookup_commit(entry->sha1);
		if (!commit)
			continue;

		commit->object.flags |= flags;
		add_pending_object(revs, &commit->object, 0);
	}

}


struct slice_fd_time {
	unsigned char sha1[20];
	int fd;
	struct stat fi;
};

int slice_time_sort(const void *a, const void *b)
{
	unsigned long at, bt;

	at = ((struct slice_fd_time *)a)->fi.st_ctime;
	bt = ((struct slice_fd_time *)b)->fi.st_ctime;

	if (at == bt)
		return 0;

	return at > bt ? 1 : -1;
}

int regenerate_cache_index(struct rev_cache_info *rci)
{
	DIR *dirh;
	int i;
	struct slice_fd_time info;
	struct strbuf slices;

	/* first remove old index if it exists */
	unlink_or_warn(git_path("rev-cache/index"));

	strbuf_init(&slices, 0);

	dirh = opendir(git_path("rev-cache"));
	if (dirh) {
		struct dirent *de;
		struct stat fi;
		int fd;
		unsigned char sha1[20];

		while ((de = readdir(dirh))) {
			if (de->d_name[0] == '.')
				continue;

			if (get_sha1_hex(de->d_name, sha1))
				continue;

			/* open with RDWR because of mmap call in make_cache_index() */
			fd = open_cache_slice(sha1, O_RDONLY);
			if (fd < 0 || fstat(fd, &fi)) {
				warning("bad cache found [%s]; fuse recommended", de->d_name);
				if (fd > 0)
					close(fd);
				continue;
			}

			hashcpy(info.sha1, sha1);
			info.fd = fd;
			memcpy(&info.fi, &fi, sizeof(struct stat));

			strbuf_add(&slices, &info, sizeof(info));
		}

		closedir(dirh);
	}

	/* we want oldest first -> upon overlap, older slices are more likely to have a larger section,
	 * as of the overlapped commit */
	qsort(slices.buf, slices.len / sizeof(info), sizeof(info), slice_time_sort);

	for (i = 0; i < slices.len; i += sizeof(info)) {
		struct slice_fd_time *infop = (struct slice_fd_time *)(slices.buf + i);
		struct stat *fip = &infop->fi;
		int fd = infop->fd;

		if (make_cache_index(rci, infop->sha1, fd, fip->st_size) < 0)
			die("error writing cache");

		close(fd);
	}

	strbuf_release(&slices);

	return 0;
}

static int add_slices_for_fuse(struct rev_cache_info *rci, struct string_list *files, struct strbuf *ignore)
{
	unsigned char sha1[20];
	char base[PATH_MAX];
	int baselen, i, slice_nr = 0;
	struct stat fi;
	DIR *dirh;
	struct dirent *de;

	strncpy(base, git_path("rev-cache"), sizeof(base));
	baselen = strlen(base);

	dirh = opendir(base);
	if (!dirh)
		return 0;

	while ((de = readdir(dirh))) {
		if (de->d_name[0] == '.')
			continue;

		base[baselen] = '/';
		strncpy(base + baselen + 1, de->d_name, sizeof(base) - baselen - 1);

		if (get_sha1_hex(de->d_name, sha1)) {
			/* whatever it is, we don't need it... */
			string_list_insert(base, files);
			continue;
		}

		/* _theoretically_ it is possible a slice < ignore_size to map objects not covered by, yet reachable from,
		 * a slice >= ignore_size, meaning that we could potentially delete an 'unfused' slice; but if that
		 * ever *did* happen their cache structure'd be so fucked up they might as well refuse the entire thing.
		 * and at any rate the worst it'd do is make rev-list revert to standard walking in that (small) bit.
		 */
		if (rci->ignore_size) {
			if (stat(base, &fi))
				warning("can't query file %s\n", base);
			else if (fi.st_size >= rci->ignore_size) {
				strbuf_add(ignore, sha1, 20);
				continue;
			}
		} else {
			/* check if a pointer */
			struct cache_slice_pointer ptr;
			int fd = open(base, O_RDONLY);

			if (fd < 0)
				goto dont_save;
			if (sizeof(ptr) != read_in_full(fd, &ptr, sizeof(ptr)))
				goto dont_save;

			close(fd);
			if (!strcmp(ptr.signature, "REVCOPTR")) {
				strbuf_add(ignore, sha1, 20);
				continue;
			}
		}

dont_save:
		for (i = idx_head.cache_nr - 1; i >= 0; i--) {
			if (!hashcmp(idx_caches + i * 20, sha1))
				break;
		}

		if (i >= 0)
			rci->maps[i].size = 1;

		string_list_insert(base, files);
		slice_nr++;
	}

	closedir(dirh);

	return slice_nr;
}

/* the most work-intensive attributes in the cache are the unique objects and size, both
 * of which can be re-used.  although path structures will be isomorphic, path generation is
 * not particularly expensive, and at any rate we need to re-sort the commits */
int fuse_cache_slices(struct rev_cache_info *rci, struct rev_info *revs)
{
	unsigned char cache_sha1[20];
	struct string_list files = {0, 0, 0, 1}; /* dup */
	struct strbuf ignore;
	int i;

	maybe_fill_with_defaults(rci);

	if (!idx_map)
		init_index();
	if (!idx_map)
		return -1;

	strbuf_init(&ignore, 0);
	rci->maps = xcalloc(idx_head.cache_nr, sizeof(struct rev_cache_slice_map));
	if (add_slices_for_fuse(rci, &files, &ignore) <= 1) {
		printf("nothing to fuse\n");
		return 1;
	}

	if (ignore.len) {
		starts_from_slices(revs, UNINTERESTING, (unsigned char *)ignore.buf, ignore.len / 20);
		strbuf_release(&ignore);
	}

	/* initialize mappings */
	for (i = idx_head.cache_nr - 1; i >= 0; i--) {
		struct rev_cache_slice_map *map = rci->maps + i;
		struct stat fi;
		struct rc_slice_header head;
		int fd;

		if (!map->size)
			continue;
		map->size = 0;

		/* pointers are never fused, so we can use open directly */
		fd = open(git_path("rev-cache/%s", sha1_to_hex(idx_caches + i * 20)), O_RDONLY);
		if (fd <= 0 || fstat(fd, &fi))
			continue;
		if (fi.st_size < sizeof(struct rc_slice_header))
			continue;
		if (get_cache_slice_header(fd, idx_caches + i * 20, fi.st_size, &head))
			continue;

		map->map = xmmap(0, head.size, PROT_READ, MAP_PRIVATE, fd, 0);
		if (map->map == MAP_FAILED)
			continue;

		lseek(fd, head.size, SEEK_SET);
		map->names = xcalloc(head.name_size, 1);
		read_in_full(fd, map->names, head.name_size);

		close(fd);
		map->size = head.size;
		map->name_size = head.name_size;
	}

	rci->make_index = 0;
	rci->fuse_me = 1;
	if (make_cache_slice(rci, revs, 0, 0, cache_sha1) < 0)
		die("can't make cache slice");

	printf("%s\n", sha1_to_hex(cache_sha1));

	/* clean up time! */
	for (i = idx_head.cache_nr - 1; i >= 0; i--) {
		struct rev_cache_slice_map *map = rci->maps + i;

		if (!map->size)
			continue;

		free(map->names);
		munmap(map->map, map->size);
	}
	free(rci->maps);
	cleanup_cache_slices();

	for (i = 0; i < files.nr; i++) {
		char *name = files.items[i].string;

		fprintf(stderr, "removing %s\n", name);
		unlink_or_warn(name);
	}

	string_list_clear(&files, 0);

	return regenerate_cache_index(rci);
}

static int verify_cache_slice(const char *slice_path, unsigned char *sha1)
{
	struct rc_slice_header head;
	int fd, len, retval = -1;
	struct stat fi;

	len = strlen(slice_path);
	if (len < 40)
		return -2;
	if (get_sha1_hex(slice_path + len - 40, sha1))
		return -3;

	fd = open(slice_path, O_RDONLY);
	if (fd == -1)
		goto end;
	if (fstat(fd, &fi) || fi.st_size < sizeof(head))
		goto end;

	if (get_cache_slice_header(fd, sha1, fi.st_size, &head))
		goto end;

	retval = 0;

end:
	if (fd > 0)
		close(fd);

	return retval;
}

int make_cache_slice_pointer(struct rev_cache_info *rci, const char *slice_path)
{
	struct cache_slice_pointer ptr;
	int fd;
	unsigned char sha1[20];

	maybe_fill_with_defaults(rci);
	rci->overwrite_all = 1;

	if (verify_cache_slice(slice_path, sha1) < 0)
		return -1;

	strcpy(ptr.signature, "REVCOPTR");
	ptr.version = SUPPORTED_REVCOPTR_VERSION;
	strcpy(ptr.path, make_nonrelative_path(slice_path));

	fd = open(git_path("rev-cache/%s", sha1_to_hex(sha1)), O_RDWR | O_CREAT | O_TRUNC, 0666);
	if (fd < 0)
		return -2;

	/* tread carefully with structures... */
	write(fd, ptr.signature, sizeof(ptr.signature));
	write(fd, &ptr.version, 1);
	write_in_full(fd, ptr.path, sizeof(ptr.path));
	make_cache_index(rci, sha1, fd, sizeof(ptr));

	close(fd);

	return 0;
}
