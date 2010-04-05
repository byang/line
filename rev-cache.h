#ifndef REV_CACHE_H
#define REV_CACHE_H

#define SUPPORTED_REVCACHE_VERSION 		1
#define SUPPORTED_REVINDEX_VERSION		1
#define SUPPORTED_REVCOPTR_VERSION		1

#define RC_PATH_SIZE(x)	(2 * (x))

#define RC_OBTAIN_OBJECT_ENTRY(p)			from_disked_rc_object_entry((unsigned char *)(p), 0)
#define RC_OBTAIN_INDEX_ENTRY(p)			from_disked_rc_index_entry((unsigned char *)(p), 0)

#define RC_ACTUAL_OBJECT_ENTRY_SIZE(e)	(\
	OBJECT_ENTRY_SIZE + \
	RC_PATH_SIZE((e)->merge_nr + (e)->split_nr) + \
	(e)->size_size + \
	(e)->name_size\
)
#define RC_ENTRY_SIZE_OFFSET(e)			(RC_ACTUAL_OBJECT_ENTRY_SIZE(e) - (e)->name_size - (e)->size_size)
#define RC_ENTRY_NAME_OFFSET(e)			(RC_ACTUAL_OBJECT_ENTRY_SIZE(e) - (e)->name_size)

/* single index maps objects to cache files */
struct rc_index_header {
	char signature[8]; /* REVINDEX */
	unsigned char version;
	uint32_t ofs_objects;

	uint32_t object_nr;
	unsigned char cache_nr;

	uint32_t max_date;
};

struct rc_index_entry_ondisk {
	unsigned char sha1[20];
	unsigned char flags;
	uint32_t pos;
};

struct rc_index_entry {
	unsigned char *sha1;
	unsigned is_start:1;
	unsigned cache_index:7;
	uint32_t pos;
};


/* structure for actual cache file */
struct rc_slice_header {
	char signature[8]; /* REVCACHE */
	unsigned char version;
	uint32_t ofs_objects;

	uint32_t object_nr;
	uint16_t path_nr;
	uint32_t size;

	unsigned char sha1[20];

	uint32_t name_size;
};

struct rc_object_entry_ondisk {
	unsigned char flags;
	unsigned char sha1[20];

	unsigned char merge_nr;
	unsigned char split_nr;
	unsigned char sizes;

	uint32_t date;
	uint16_t path;
};

struct rc_object_entry {
	unsigned type:3;
	unsigned is_end:1;
	unsigned is_start:1;
	unsigned has_objects:1;
	unsigned flag:2; /* unused */
	unsigned char *sha1; /* 20 byte */

	unsigned char merge_nr; /* : 7 */
	unsigned char split_nr; /* : 7 */
	unsigned size_size:3;
	unsigned name_size:3;
	unsigned padding:2;

	uint32_t date;
	uint16_t path;

	/* merge paths */
	/* split paths */
	/* size */
	/* name id */
};

struct rc_index_entry *from_disked_rc_index_entry(unsigned char *src, struct rc_index_entry *dst);
unsigned char *to_disked_rc_index_entry(struct rc_index_entry *src, unsigned char **dst);
struct rc_object_entry *from_disked_rc_object_entry(unsigned char *src, struct rc_object_entry *dst);
unsigned char *to_disked_rc_object_entry(struct rc_object_entry *src, unsigned char **dst);

extern unsigned char *get_cache_slice(struct commit *commit);
extern int open_cache_slice(unsigned char *sha1, int flags);
extern int traverse_cache_slice(struct rev_info *revs,
	unsigned char *cache_sha1, struct commit *commit,
	unsigned long *date_so_far, int *slop_so_far,
	struct commit_list ***queue, struct commit_list **work);

extern void init_rev_cache_info(struct rev_cache_info *rci);
extern int make_cache_slice(struct rev_cache_info *rci,
	struct rev_info *revs, struct commit_list **starts, struct commit_list **ends,
	unsigned char *cache_sha1);
extern int make_cache_index(struct rev_cache_info *rci, unsigned char *cache_sha1,
	int fd, unsigned int size);

extern void starts_from_slices(struct rev_info *revs, unsigned int flags, unsigned char *which, int n);
extern int fuse_cache_slices(struct rev_cache_info *rci, struct rev_info *revs);
extern int regenerate_cache_index(struct rev_cache_info *rci);
extern int make_cache_slice_pointer(struct rev_cache_info *rci, const char *slice_path);

#endif
