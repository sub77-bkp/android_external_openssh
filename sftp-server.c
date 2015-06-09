/* $OpenBSD: sftp-server.c,v 1.94 2011/06/17 21:46:16 djm Exp $ */
/*
 * Copyright (c) 2000-2004 Markus Friedl.  All rights reserved.
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */

#include "includes.h"

#include <sys/types.h>
#include <sys/param.h>
#include <sys/stat.h>
#ifdef HAVE_SYS_TIME_H
# include <sys/time.h>
#endif
#ifdef HAVE_SYS_MOUNT_H
#include <sys/mount.h>
#endif
#ifdef HAVE_SYS_STATVFS_H
#include <sys/statvfs.h>
#endif

#include <sys/xattr.h>
#ifndef ENOATTR
#define ENOATTR ENODATA
#endif

#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <pwd.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <pwd.h>
#include <time.h>
#include <unistd.h>
#include <stdarg.h>

#include "xmalloc.h"
#include "buffer.h"
#include "log.h"
#include "misc.h"
#include "uidswap.h"

#include "sftp.h"
#include "sftp-common.h"

#define MAX_XATTR_DATA_LEN 100000

/* helper */
#define get_int64()			buffer_get_int64(&iqueue);
#define get_int()			buffer_get_int(&iqueue);
#define get_string(lenp)		buffer_get_string(&iqueue, lenp);

/* Our verbosity */
LogLevel log_level = SYSLOG_LEVEL_ERROR;

/* Our client */
struct passwd *pw = NULL;
char *client_addr = NULL;

/* input and output queue */
Buffer iqueue;
Buffer oqueue;

/* Version of client */
u_int version;

/* Disable writes */
int readonly;

/* xattr extension */
int xattr_caching;

typedef struct Xattrib Xattrib;

struct Xattrib {
	char *name;
	void *value;
	size_t size;
};

/* portable attributes, etc. */

typedef struct Stat Stat;

struct Stat {
	char *name;
	char *long_name;
	Attrib attrib;
	Xattrib *xattrib;
	size_t xa_size;
};

static int
errno_to_portable(int unixerrno)
{
	int ret = 0;

	switch (unixerrno) {
	case 0:
		ret = SSH2_FX_OK;
		break;
	case ENOENT:
	case ENOTDIR:
	case EBADF:
	case ELOOP:
		ret = SSH2_FX_NO_SUCH_FILE;
		break;
	case EPERM:
	case EACCES:
	case EFAULT:
		ret = SSH2_FX_PERMISSION_DENIED;
		break;
	case ENAMETOOLONG:
	case EINVAL:
		ret = SSH2_FX_BAD_MESSAGE;
		break;
	case ENOSYS:
		ret = SSH2_FX_OP_UNSUPPORTED;
		break;
	case ENOATTR:
		ret = SSH2_FX_ENOATTR;
		break;
	case ENOSPC:
	case EDQUOT:
		ret = SSH2_FX_ENOSPC;
		break;
	case ENOTSUP:
		ret = SSH2_FX_ENOTSUP;
		break;
	case ERANGE:
		ret = SSH2_FX_ERANGE;
		break;
	case EMSGSIZE:
		ret = SSH2_FX_EMSGSIZE;
		break;
	default:
		ret = SSH2_FX_FAILURE;
		break;
	}
	return ret;
}

static int
flags_from_portable(int pflags)
{
	int flags = 0;

	if ((pflags & SSH2_FXF_READ) &&
	    (pflags & SSH2_FXF_WRITE)) {
		flags = O_RDWR;
	} else if (pflags & SSH2_FXF_READ) {
		flags = O_RDONLY;
	} else if (pflags & SSH2_FXF_WRITE) {
		flags = O_WRONLY;
	}
	if (pflags & SSH2_FXF_CREAT)
		flags |= O_CREAT;
	if (pflags & SSH2_FXF_TRUNC)
		flags |= O_TRUNC;
	if (pflags & SSH2_FXF_EXCL)
		flags |= O_EXCL;
	return flags;
}

static const char *
string_from_portable(int pflags)
{
	static char ret[128];

	*ret = '\0';

#define PAPPEND(str)	{				\
		if (*ret != '\0')			\
			strlcat(ret, ",", sizeof(ret));	\
		strlcat(ret, str, sizeof(ret));		\
	}

	if (pflags & SSH2_FXF_READ)
		PAPPEND("READ")
	if (pflags & SSH2_FXF_WRITE)
		PAPPEND("WRITE")
	if (pflags & SSH2_FXF_CREAT)
		PAPPEND("CREATE")
	if (pflags & SSH2_FXF_TRUNC)
		PAPPEND("TRUNCATE")
	if (pflags & SSH2_FXF_EXCL)
		PAPPEND("EXCL")

	return ret;
}

static Attrib *
get_attrib(void)
{
	return decode_attrib(&iqueue);
}

/* handle handles */

typedef struct Handle Handle;
struct Handle {
	int use;
	DIR *dirp;
	int fd;
	char *name;
	u_int64_t bytes_read, bytes_write;
	int next_unused;
};

enum {
	HANDLE_UNUSED,
	HANDLE_DIR,
	HANDLE_FILE
};

Handle *handles = NULL;
u_int num_handles = 0;
int first_unused_handle = -1;

static void handle_unused(int i)
{
	handles[i].use = HANDLE_UNUSED;
	handles[i].next_unused = first_unused_handle;
	first_unused_handle = i;
}

static int
handle_new(int use, const char *name, int fd, DIR *dirp)
{
	int i;

	if (first_unused_handle == -1) {
		if (num_handles + 1 <= num_handles)
			return -1;
		num_handles++;
		handles = xrealloc(handles, num_handles, sizeof(Handle));
		handle_unused(num_handles - 1);
	}

	i = first_unused_handle;
	first_unused_handle = handles[i].next_unused;

	handles[i].use = use;
	handles[i].dirp = dirp;
	handles[i].fd = fd;
	handles[i].name = xstrdup(name);
	handles[i].bytes_read = handles[i].bytes_write = 0;

	return i;
}

static int
handle_is_ok(int i, int type)
{
	return i >= 0 && (u_int)i < num_handles && handles[i].use == type;
}

static int
handle_to_string(int handle, char **stringp, int *hlenp)
{
	if (stringp == NULL || hlenp == NULL)
		return -1;
	*stringp = xmalloc(sizeof(int32_t));
	put_u32(*stringp, handle);
	*hlenp = sizeof(int32_t);
	return 0;
}

static int
handle_from_string(const char *handle, u_int hlen)
{
	int val;

	if (hlen != sizeof(int32_t))
		return -1;
	val = get_u32(handle);
	if (handle_is_ok(val, HANDLE_FILE) ||
	    handle_is_ok(val, HANDLE_DIR))
		return val;
	return -1;
}

static char *
handle_to_name(int handle)
{
	if (handle_is_ok(handle, HANDLE_DIR)||
	    handle_is_ok(handle, HANDLE_FILE))
		return handles[handle].name;
	return NULL;
}

static DIR *
handle_to_dir(int handle)
{
	if (handle_is_ok(handle, HANDLE_DIR))
		return handles[handle].dirp;
	return NULL;
}

static int
handle_to_fd(int handle)
{
	if (handle_is_ok(handle, HANDLE_FILE))
		return handles[handle].fd;
	return -1;
}

static void
handle_update_read(int handle, ssize_t bytes)
{
	if (handle_is_ok(handle, HANDLE_FILE) && bytes > 0)
		handles[handle].bytes_read += bytes;
}

static void
handle_update_write(int handle, ssize_t bytes)
{
	if (handle_is_ok(handle, HANDLE_FILE) && bytes > 0)
		handles[handle].bytes_write += bytes;
}

static u_int64_t
handle_bytes_read(int handle)
{
	if (handle_is_ok(handle, HANDLE_FILE))
		return (handles[handle].bytes_read);
	return 0;
}

static u_int64_t
handle_bytes_write(int handle)
{
	if (handle_is_ok(handle, HANDLE_FILE))
		return (handles[handle].bytes_write);
	return 0;
}

static int
handle_close(int handle)
{
	int ret = -1;

	if (handle_is_ok(handle, HANDLE_FILE)) {
		ret = close(handles[handle].fd);
		xfree(handles[handle].name);
		handle_unused(handle);
	} else if (handle_is_ok(handle, HANDLE_DIR)) {
		ret = closedir(handles[handle].dirp);
		xfree(handles[handle].name);
		handle_unused(handle);
	} else {
		errno = ENOENT;
	}
	return ret;
}

static void
handle_log_close(int handle, char *emsg)
{
	if (handle_is_ok(handle, HANDLE_FILE)) {
		logit("%s%sclose \"%s\" bytes read %llu written %llu",
		    emsg == NULL ? "" : emsg, emsg == NULL ? "" : " ",
		    handle_to_name(handle),
		    (unsigned long long)handle_bytes_read(handle),
		    (unsigned long long)handle_bytes_write(handle));
	} else {
		logit("%s%sclosedir \"%s\"",
		    emsg == NULL ? "" : emsg, emsg == NULL ? "" : " ",
		    handle_to_name(handle));
	}
}

static void
handle_log_exit(void)
{
	u_int i;

	for (i = 0; i < num_handles; i++)
		if (handles[i].use != HANDLE_UNUSED)
			handle_log_close(i, "forced");
}

static int
get_handle(void)
{
	char *handle;
	int val = -1;
	u_int hlen;

	handle = get_string(&hlen);
	if (hlen < 256)
		val = handle_from_string(handle, hlen);
	xfree(handle);
	return val;
}

/* send replies */

static void
send_msg(Buffer *m)
{
	int mlen = buffer_len(m);

	buffer_put_int(&oqueue, mlen);
	buffer_append(&oqueue, buffer_ptr(m), mlen);
	buffer_consume(m, mlen);
}

static const char *
status_to_message(u_int32_t status)
{
	const char *status_messages[] = {
		"Success",			/* SSH_FX_OK */
		"End of file",			/* SSH_FX_EOF */
		"No such file",			/* SSH_FX_NO_SUCH_FILE */
		"Permission denied",		/* SSH_FX_PERMISSION_DENIED */
		"Failure",			/* SSH_FX_FAILURE */
		"Bad message",			/* SSH_FX_BAD_MESSAGE */
		"No connection",		/* SSH_FX_NO_CONNECTION */
		"Connection lost",		/* SSH_FX_CONNECTION_LOST */
		"Operation unsupported",	/* SSH_FX_OP_UNSUPPORTED */
		"No such attribute",		/* SSH2_FX_ENOATTR */
		"No space",			/* SSH2_FX_ENOSPC */
		"Not supported",		/* SSH2_FX_ENOTSUP */
		"Range error",			/* SSH2_FX_ERANGE */
		"Message size error",		/* SSH2_FX_EMSGSIZE */
		"Unknown error"			/* Others */
	};
	return (status_messages[MIN(status,SSH2_FX_MAX)]);
}

static void
send_status(u_int32_t id, u_int32_t status)
{
	Buffer msg;

	debug3("request %u: sent status %u", id, status);
	if (log_level > SYSLOG_LEVEL_VERBOSE ||
	    (status != SSH2_FX_OK && status != SSH2_FX_EOF))
		logit("sent status %s", status_to_message(status));
	buffer_init(&msg);
	buffer_put_char(&msg, SSH2_FXP_STATUS);
	buffer_put_int(&msg, id);
	buffer_put_int(&msg, status);
	if (version >= 3) {
		buffer_put_cstring(&msg, status_to_message(status));
		buffer_put_cstring(&msg, "");
	}
	send_msg(&msg);
	buffer_free(&msg);
}
static void
send_data_or_handle(char type, u_int32_t id, const char *data, int dlen)
{
	Buffer msg;

	buffer_init(&msg);
	buffer_put_char(&msg, type);
	buffer_put_int(&msg, id);
	buffer_put_string(&msg, data, dlen);
	send_msg(&msg);
	buffer_free(&msg);
}

static void
send_data(u_int32_t id, const char *data, int dlen)
{
	debug("request %u: sent data len %d", id, dlen);
	send_data_or_handle(SSH2_FXP_DATA, id, data, dlen);
}

static void
send_handle(u_int32_t id, int handle)
{
	char *string;
	int hlen;

	handle_to_string(handle, &string, &hlen);
	debug("request %u: sent handle handle %d", id, handle);
	send_data_or_handle(SSH2_FXP_HANDLE, id, string, hlen);
	xfree(string);
}

static void
write_allxattr_data(Buffer *msg, Xattrib *xa, size_t xa_size) {
	buffer_put_int(msg, xa_size);
	if (xa_size == (size_t)-1)
		buffer_put_int(msg, *(int*)xa);
	else if (xa_size != 0) {
		size_t j;
		for (j=0; j<xa_size; ++j) {
			buffer_put_cstring(msg, xa[j].name);
			buffer_put_int(msg, xa[j].size);
			if (xa[j].size == (size_t)-1)
				buffer_put_int(msg, *(int*)xa[j].value);
			else if (xa[j].size != 0)
				buffer_append(msg, xa[j].value, xa[j].size);
		}
	}
}

static void
send_names_start(Buffer *msg, u_int32_t id)
{
	debug("send_names_start %u", id);
	buffer_init(msg);
	buffer_put_char(msg, SSH2_FXP_NAME);
	buffer_put_int(msg, id);
	buffer_put_int(msg, 0);
}

static void
send_names_next(Buffer *msg, u_int32_t id, const Stat *stats)
{
	buffer_put_cstring(msg, stats->name);
	buffer_put_cstring(msg, stats->long_name);
	encode_attrib(msg, &stats->attrib);
	if (xattr_caching)
		write_allxattr_data(msg, stats->xattrib, stats->xa_size);
}

static void
send_names_end(Buffer *msg, int count)
{
	char buf[4];
	put_u32(buf, count);
	memcpy((char*)buffer_ptr(msg) + 5, buf, 4);
	send_msg(msg);
	buffer_free(msg);
}

static void
send_names(u_int32_t id, int count, const Stat *stats)
{
	Buffer msg;
	int i;

	send_names_start(&msg, id);
	debug("request %u: sent names count %d", id, count);
	for (i = 0; i < count; i++) {
		send_names_next(&msg, id, stats + i);
	}
	send_names_end(&msg, count);
}

static void
send_attrib(u_int32_t id, const Attrib *a)
{
	Buffer msg;

	debug("request %u: sent attrib have 0x%x", id, a->flags);
	buffer_init(&msg);
	buffer_put_char(&msg, SSH2_FXP_ATTRS);
	buffer_put_int(&msg, id);
	encode_attrib(&msg, a);
	send_msg(&msg);
	buffer_free(&msg);
}

static void
send_statvfs(u_int32_t id, struct statvfs *st)
{
	Buffer msg;
	u_int64_t flag;

	flag = (st->f_flag & ST_RDONLY) ? SSH2_FXE_STATVFS_ST_RDONLY : 0;
	flag |= (st->f_flag & ST_NOSUID) ? SSH2_FXE_STATVFS_ST_NOSUID : 0;

	buffer_init(&msg);
	buffer_put_char(&msg, SSH2_FXP_EXTENDED_REPLY);
	buffer_put_int(&msg, id);
	buffer_put_int64(&msg, st->f_bsize);
	buffer_put_int64(&msg, st->f_frsize);
	buffer_put_int64(&msg, st->f_blocks);
	buffer_put_int64(&msg, st->f_bfree);
	buffer_put_int64(&msg, st->f_bavail);
	buffer_put_int64(&msg, st->f_files);
	buffer_put_int64(&msg, st->f_ffree);
	buffer_put_int64(&msg, st->f_favail);
	buffer_put_int64(&msg, FSID_TO_ULONG(st->f_fsid));
	buffer_put_int64(&msg, flag);
	buffer_put_int64(&msg, st->f_namemax);
	send_msg(&msg);
	buffer_free(&msg);
}

/* parse incoming */

static void
process_init(void)
{
	Buffer msg;

	version = get_int();
	verbose("received client version %u", version);
	buffer_init(&msg);
	buffer_put_char(&msg, SSH2_FXP_VERSION);
	buffer_put_int(&msg, SSH2_FILEXFER_VERSION);
	/* POSIX rename extension */
	buffer_put_cstring(&msg, "posix-rename@openssh.com");
	buffer_put_cstring(&msg, "1"); /* version */
	/* statvfs extension */
	buffer_put_cstring(&msg, "statvfs@openssh.com");
	buffer_put_cstring(&msg, "2"); /* version */
	/* fstatvfs extension */
	buffer_put_cstring(&msg, "fstatvfs@openssh.com");
	buffer_put_cstring(&msg, "2"); /* version */
	/* hardlink extension */
	buffer_put_cstring(&msg, "hardlink@openssh.com");
	buffer_put_cstring(&msg, "1"); /* version */
	/* xattr extensions */
	buffer_put_cstring(&msg, "setxattr@openssh.com");
	buffer_put_cstring(&msg, "1"); /* version */
	buffer_put_cstring(&msg, "getxattr@openssh.com");
	buffer_put_cstring(&msg, "1"); /* version */
	buffer_put_cstring(&msg, "listxattr@openssh.com");
	buffer_put_cstring(&msg, "1"); /* version */
	buffer_put_cstring(&msg, "removexattr@openssh.com");
	buffer_put_cstring(&msg, "1"); /* version */
	buffer_put_cstring(&msg, "cachexattr@openssh.com");
	buffer_put_cstring(&msg, "1"); /* version */
	buffer_put_cstring(&msg, "getallxattr@openssh.com");
	buffer_put_cstring(&msg, "1"); /* version */
	send_msg(&msg);
	buffer_free(&msg);
}

static void
process_open(void)
{
	u_int32_t id, pflags;
	Attrib *a;
	char *name;
	int handle, fd, flags, mode, status = SSH2_FX_FAILURE;

	id = get_int();
	name = get_string(NULL);
	pflags = get_int();		/* portable flags */
	debug3("request %u: open flags %d", id, pflags);
	a = get_attrib();
	flags = flags_from_portable(pflags);
	mode = (a->flags & SSH2_FILEXFER_ATTR_PERMISSIONS) ? a->perm : 0666;
	logit("open \"%s\" flags %s mode 0%o",
	    name, string_from_portable(pflags), mode);
	if (readonly &&
	    ((flags & O_ACCMODE) == O_WRONLY || (flags & O_ACCMODE) == O_RDWR))
		status = SSH2_FX_PERMISSION_DENIED;
	else {
		fd = open(name, flags, mode);
		if (fd < 0) {
			status = errno_to_portable(errno);
		} else {
			handle = handle_new(HANDLE_FILE, name, fd, NULL);
			if (handle < 0) {
				close(fd);
			} else {
				send_handle(id, handle);
				status = SSH2_FX_OK;
			}
		}
	}
	if (status != SSH2_FX_OK)
		send_status(id, status);
	xfree(name);
}

static void
process_close(void)
{
	u_int32_t id;
	int handle, ret, status = SSH2_FX_FAILURE;

	id = get_int();
	handle = get_handle();
	debug3("request %u: close handle %u", id, handle);
	handle_log_close(handle, NULL);
	ret = handle_close(handle);
	status = (ret == -1) ? errno_to_portable(errno) : SSH2_FX_OK;
	send_status(id, status);
}

static void
process_read(void)
{
	char buf[64*1024];
	u_int32_t id, len;
	int handle, fd, ret, status = SSH2_FX_FAILURE;
	u_int64_t off;

	id = get_int();
	handle = get_handle();
	off = get_int64();
	len = get_int();

	debug("request %u: read \"%s\" (handle %d) off %llu len %d",
	    id, handle_to_name(handle), handle, (unsigned long long)off, len);
	if (len > sizeof buf) {
		len = sizeof buf;
		debug2("read change len %d", len);
	}
	fd = handle_to_fd(handle);
	if (fd >= 0) {
		if (lseek(fd, off, SEEK_SET) < 0) {
			error("process_read: seek failed");
			status = errno_to_portable(errno);
		} else {
			ret = read(fd, buf, len);
			if (ret < 0) {
				status = errno_to_portable(errno);
			} else if (ret == 0) {
				status = SSH2_FX_EOF;
			} else {
				send_data(id, buf, ret);
				status = SSH2_FX_OK;
				handle_update_read(handle, ret);
			}
		}
	}
	if (status != SSH2_FX_OK)
		send_status(id, status);
}

static void
process_write(void)
{
	u_int32_t id;
	u_int64_t off;
	u_int len;
	int handle, fd, ret, status;
	char *data;

	id = get_int();
	handle = get_handle();
	off = get_int64();
	data = get_string(&len);

	debug("request %u: write \"%s\" (handle %d) off %llu len %d",
	    id, handle_to_name(handle), handle, (unsigned long long)off, len);
	fd = handle_to_fd(handle);
	
	if (fd < 0)
		status = SSH2_FX_FAILURE;
	else if (readonly)
		status = SSH2_FX_PERMISSION_DENIED;
	else {
		if (lseek(fd, off, SEEK_SET) < 0) {
			status = errno_to_portable(errno);
			error("process_write: seek failed");
		} else {
/* XXX ATOMICIO ? */
			ret = write(fd, data, len);
			if (ret < 0) {
				error("process_write: write failed");
				status = errno_to_portable(errno);
			} else if ((size_t)ret == len) {
				status = SSH2_FX_OK;
				handle_update_write(handle, ret);
			} else {
				debug2("nothing at all written");
				status = SSH2_FX_FAILURE;
			}
		}
	}
	send_status(id, status);
	xfree(data);
}

static void
process_do_stat(int do_lstat)
{
	Attrib a;
	struct stat st;
	u_int32_t id;
	char *name;
	int ret, status = SSH2_FX_FAILURE;

	id = get_int();
	name = get_string(NULL);
	debug3("request %u: %sstat", id, do_lstat ? "l" : "");
	verbose("%sstat name \"%s\"", do_lstat ? "l" : "", name);
	ret = do_lstat ? lstat(name, &st) : stat(name, &st);
	if (ret < 0) {
		status = errno_to_portable(errno);
	} else {
		stat_to_attrib(&st, &a);
		send_attrib(id, &a);
		status = SSH2_FX_OK;
	}
	if (status != SSH2_FX_OK)
		send_status(id, status);
	xfree(name);
}

static void
process_stat(void)
{
	process_do_stat(0);
}

static void
process_lstat(void)
{
	process_do_stat(1);
}

static void
process_fstat(void)
{
	Attrib a;
	struct stat st;
	u_int32_t id;
	int fd, ret, handle, status = SSH2_FX_FAILURE;

	id = get_int();
	handle = get_handle();
	debug("request %u: fstat \"%s\" (handle %u)",
	    id, handle_to_name(handle), handle);
	fd = handle_to_fd(handle);
	if (fd >= 0) {
		ret = fstat(fd, &st);
		if (ret < 0) {
			status = errno_to_portable(errno);
		} else {
			stat_to_attrib(&st, &a);
			send_attrib(id, &a);
			status = SSH2_FX_OK;
		}
	}
	if (status != SSH2_FX_OK)
		send_status(id, status);
}

static struct timeval *
attrib_to_tv(const Attrib *a)
{
	static struct timeval tv[2];

	tv[0].tv_sec = a->atime;
	tv[0].tv_usec = 0;
	tv[1].tv_sec = a->mtime;
	tv[1].tv_usec = 0;
	return tv;
}

static void
process_setstat(void)
{
	Attrib *a;
	u_int32_t id;
	char *name;
	int status = SSH2_FX_OK, ret;

	id = get_int();
	name = get_string(NULL);
	a = get_attrib();
	debug("request %u: setstat name \"%s\"", id, name);
	if (readonly) {
		status = SSH2_FX_PERMISSION_DENIED;
		a->flags = 0;
	}
	if (a->flags & SSH2_FILEXFER_ATTR_SIZE) {
		logit("set \"%s\" size %llu",
		    name, (unsigned long long)a->size);
		ret = truncate(name, a->size);
		if (ret == -1)
			status = errno_to_portable(errno);
	}
	if (a->flags & SSH2_FILEXFER_ATTR_PERMISSIONS) {
		logit("set \"%s\" mode %04o", name, a->perm);
		ret = chmod(name, a->perm & 07777);
		if (ret == -1)
			status = errno_to_portable(errno);
	}
	if (a->flags & SSH2_FILEXFER_ATTR_ACMODTIME) {
		char buf[64];
		time_t t = a->mtime;

		strftime(buf, sizeof(buf), "%Y%m%d-%H:%M:%S",
		    localtime(&t));
		logit("set \"%s\" modtime %s", name, buf);
		ret = utimes(name, attrib_to_tv(a));
		if (ret == -1)
			status = errno_to_portable(errno);
	}
	if (a->flags & SSH2_FILEXFER_ATTR_UIDGID) {
		logit("set \"%s\" owner %lu group %lu", name,
		    (u_long)a->uid, (u_long)a->gid);
		ret = chown(name, a->uid, a->gid);
		if (ret == -1)
			status = errno_to_portable(errno);
	}
	send_status(id, status);
	xfree(name);
}

static void
process_fsetstat(void)
{
	Attrib *a;
	u_int32_t id;
	int handle, fd, ret;
	int status = SSH2_FX_OK;

	id = get_int();
	handle = get_handle();
	a = get_attrib();
	debug("request %u: fsetstat handle %d", id, handle);
	fd = handle_to_fd(handle);
	if (fd < 0)
		status = SSH2_FX_FAILURE;
	else if (readonly)
		status = SSH2_FX_PERMISSION_DENIED;
	else {
		char *name = handle_to_name(handle);

		if (a->flags & SSH2_FILEXFER_ATTR_SIZE) {
			logit("set \"%s\" size %llu",
			    name, (unsigned long long)a->size);
			ret = ftruncate(fd, a->size);
			if (ret == -1)
				status = errno_to_portable(errno);
		}
		if (a->flags & SSH2_FILEXFER_ATTR_PERMISSIONS) {
			logit("set \"%s\" mode %04o", name, a->perm);
#ifdef HAVE_FCHMOD
			ret = fchmod(fd, a->perm & 07777);
#else
			ret = chmod(name, a->perm & 07777);
#endif
			if (ret == -1)
				status = errno_to_portable(errno);
		}
		if (a->flags & SSH2_FILEXFER_ATTR_ACMODTIME) {
			char buf[64];
			time_t t = a->mtime;

			strftime(buf, sizeof(buf), "%Y%m%d-%H:%M:%S",
			    localtime(&t));
			logit("set \"%s\" modtime %s", name, buf);
#ifdef HAVE_FUTIMES
			ret = futimes(fd, attrib_to_tv(a));
#else
			ret = utimes(name, attrib_to_tv(a));
#endif
			if (ret == -1)
				status = errno_to_portable(errno);
		}
		if (a->flags & SSH2_FILEXFER_ATTR_UIDGID) {
			logit("set \"%s\" owner %lu group %lu", name,
			    (u_long)a->uid, (u_long)a->gid);
#ifdef HAVE_FCHOWN
			ret = fchown(fd, a->uid, a->gid);
#else
			ret = chown(name, a->uid, a->gid);
#endif
			if (ret == -1)
				status = errno_to_portable(errno);
		}
	}
	send_status(id, status);
}

static void
process_opendir(void)
{
	DIR *dirp = NULL;
	char *path;
	int handle, status = SSH2_FX_FAILURE;
	u_int32_t id;

	id = get_int();
	path = get_string(NULL);
	debug3("request %u: opendir", id);
	logit("opendir \"%s\"", path);
	dirp = opendir(path);
	if (dirp == NULL) {
		status = errno_to_portable(errno);
	} else {
		handle = handle_new(HANDLE_DIR, path, 0, dirp);
		if (handle < 0) {
			closedir(dirp);
		} else {
			send_handle(id, handle);
			status = SSH2_FX_OK;
		}

	}
	if (status != SSH2_FX_OK)
		send_status(id, status);
	xfree(path);
}

static void delete_xattr(Xattrib *xattr, size_t xa_size)
{
	if (xa_size != 0) {
		if (xa_size != (size_t)-1) {
			size_t i;
			for (i=0; i<xa_size; ++i) {
				xfree(xattr[i].name);
				if (xattr[i].size != 0) {
					xfree(xattr[i].value);
				}
			}
		}
		xfree(xattr);
	}
}

static size_t get_xattr(const char *path, Xattrib **xattrib)
{
	size_t lsize = 1024;
	char *list = xmalloc(lsize);
	size_t lret;
	Xattrib *xattr = NULL;
	do {
		lret = llistxattr(path, list, lsize);
		if (lret == (size_t)-1) {
			if (errno == ERANGE) {
				lret = llistxattr(path, list, 0);
				if (lret != (size_t)-1) {
					if (lret > MAX_XATTR_DATA_LEN) {
						lret = (size_t)-1;
						errno = EMSGSIZE;
					}
					else {
						lsize = lret;
						list = xrealloc(list, lsize, 1);
						continue;
					}
				}
			}
		}
		break;
	} while (1);
	debug3("get_xattr: lret=%ld", lret);

	if (lret == (size_t)-1) {
		xattr = xmalloc(sizeof(int));
		*(int*)xattr = errno_to_portable(errno);
	} else if (lret != 0) {
		char *p;
		char *list_end = list + lret;
		int cnt = 0;
		for (p=list; p<list_end; ++p)
			if (!*p)
				++cnt;
		debug3("get_xattr: cnt=%d", cnt);
		xattr = xcalloc(cnt, sizeof(Xattrib));
		size_t vsize = 1024;
		void *value = xmalloc(vsize);
		char *name = list;
		int i;
		size_t tot_siz = 0;
		for (i=0; i<cnt; ++i) {
			size_t nlen = strlen(name);
			size_t gret;
			do {
				gret = lgetxattr(path, name, value, vsize);
				//debug3("get_xattr: gret=%d, errno=%d(%d), name=%s, size=%ld, value=%s\n", gret, errno, ERANGE, name, vsize, value);
				if (gret == (size_t)-1) {
					if (errno == ERANGE) {
						gret = lgetxattr(path, name, value, 0);
						//debug3("get_xattr: gret=%d, errno=%d(%d), name=%s\n", gret, errno, ERANGE, name);
						if (gret != (size_t)-1) {
							if (gret > MAX_XATTR_DATA_LEN) {
								gret = (size_t)-1;
								errno = EMSGSIZE;
							}
							else {
								vsize = gret;
								value = xrealloc(value, vsize, 1);
								continue;
							}
						}
					}
				}
				break;
			} while (1);
			tot_siz += gret;
			if (tot_siz > MAX_XATTR_DATA_LEN)
				break;
			xattr[i].name = xstrdup(name);
			xattr[i].size = gret;
			if (gret == (size_t)-1) {
				xattr[i].value = xmalloc(sizeof(int));
				*(int*)xattr[i].value = errno_to_portable(errno);
			} else if (gret != 0) {
				xattr[i].value = xmalloc(gret);
				memcpy(xattr[i].value, value, gret);
			}
			//debug3("get_xattr: name=%s, size=%ld, value=%s\n", xattr[i].name, xattr[i].size, xattr[i].value);
			name += nlen+1;
		}
		if (i<cnt) {
			delete_xattr(xattr, i);
			xattr = xmalloc(sizeof(int));
			*(int*)xattr = errno_to_portable(EMSGSIZE);
		}
		xfree(value);
		lret = cnt;
	}
	xfree(list);
	*xattrib = xattr;
	return lret;
}

static void
process_readdir(void)
{
	DIR *dirp;
	struct dirent *dp;
	char *path;
	int handle;
	u_int32_t id;

	id = get_int();
	handle = get_handle();
	debug("request %u: readdir \"%s\" (handle %d)", id,
	    handle_to_name(handle), handle);
	dirp = handle_to_dir(handle);
	path = handle_to_name(handle);
	if (dirp == NULL || path == NULL) {
		send_status(id, SSH2_FX_FAILURE);
	} else {
		struct stat st;
		char pathname[MAXPATHLEN];
		Stat stats;
		int count = 0;
		Buffer msg;
		int max_entrysize = 256 + MAXPATHLEN + 32 + 1024;
		debug3("readdir: xattr_caching=%d", xattr_caching);
		if (xattr_caching)
			max_entrysize += MAX_XATTR_DATA_LEN;
		send_names_start(&msg, id);

		while ((dp = readdir(dirp)) != NULL) {
			snprintf(pathname, sizeof pathname, "%s%s%s", path,
			    strcmp(path, "/") ? "/" : "", dp->d_name);
			if (lstat(pathname, &st) < 0)
				continue;
			stat_to_attrib(&st, &stats.attrib);
			stats.name = xstrdup(dp->d_name);
			stats.long_name = ls_file(dp->d_name, &st, 0, 0);
			stats.xa_size = 0;
			if (xattr_caching)
				stats.xa_size = get_xattr(pathname, &stats.xattrib);
			debug3("readdir: stats.xa_size=%ld", stats.xa_size);
			send_names_next(&msg, id, &stats);
			xfree(stats.name);
			xfree(stats.long_name);
			delete_xattr(stats.xattrib, stats.xa_size);
			count++;
			if (buffer_len(&msg) + max_entrysize > SFTP_MAX_MSG_LENGTH)
				break;
		}
		if (count > 0) {
			debug3("readdir: count=%d", count);
			send_names_end(&msg, count);
		} else {
			buffer_free(&msg);
			send_status(id, SSH2_FX_EOF);
		}
	}
}

static void
process_remove(void)
{
	char *name;
	u_int32_t id;
	int status = SSH2_FX_FAILURE;
	int ret;

	id = get_int();
	name = get_string(NULL);
	debug3("request %u: remove", id);
	logit("remove name \"%s\"", name);
	if (readonly)
		status = SSH2_FX_PERMISSION_DENIED;
	else {
		ret = unlink(name);
		status = (ret == -1) ? errno_to_portable(errno) : SSH2_FX_OK;
	}
	send_status(id, status);
	xfree(name);
}

static void
process_mkdir(void)
{
	Attrib *a;
	u_int32_t id;
	char *name;
	int ret, mode, status = SSH2_FX_FAILURE;

	id = get_int();
	name = get_string(NULL);
	a = get_attrib();
	mode = (a->flags & SSH2_FILEXFER_ATTR_PERMISSIONS) ?
	    a->perm & 07777 : 0777;
	debug3("request %u: mkdir", id);
	logit("mkdir name \"%s\" mode 0%o", name, mode);
	if (readonly)
		status = SSH2_FX_PERMISSION_DENIED;
	else {
		ret = mkdir(name, mode);
		status = (ret == -1) ? errno_to_portable(errno) : SSH2_FX_OK;
	}
	send_status(id, status);
	xfree(name);
}

static void
process_rmdir(void)
{
	u_int32_t id;
	char *name;
	int ret, status;

	id = get_int();
	name = get_string(NULL);
	debug3("request %u: rmdir", id);
	logit("rmdir name \"%s\"", name);
	if (readonly)
		status = SSH2_FX_PERMISSION_DENIED;
	else {
		ret = rmdir(name);
		status = (ret == -1) ? errno_to_portable(errno) : SSH2_FX_OK;
	}
	send_status(id, status);
	xfree(name);
}

static void
process_realpath(void)
{
	char resolvedname[MAXPATHLEN];
	u_int32_t id;
	char *path;

	id = get_int();
	path = get_string(NULL);
	if (path[0] == '\0') {
		xfree(path);
		path = xstrdup(".");
	}
	debug3("request %u: realpath", id);
	verbose("realpath \"%s\"", path);
	if (realpath(path, resolvedname) == NULL) {
		send_status(id, errno_to_portable(errno));
	} else {
		Stat s;
		attrib_clear(&s.attrib);
		s.xa_size = 0;
		s.name = s.long_name = resolvedname;
		send_names(id, 1, &s);
	}
	xfree(path);
}

static void
process_rename(void)
{
	u_int32_t id;
	char *oldpath, *newpath;
	int status;
	struct stat sb;

	id = get_int();
	oldpath = get_string(NULL);
	newpath = get_string(NULL);
	debug3("request %u: rename", id);
	logit("rename old \"%s\" new \"%s\"", oldpath, newpath);
	status = SSH2_FX_FAILURE;
	if (readonly)
		status = SSH2_FX_PERMISSION_DENIED;
	else if (lstat(oldpath, &sb) == -1)
		status = errno_to_portable(errno);
	else if (S_ISREG(sb.st_mode)) {
		/* Race-free rename of regular files */
		if (link(oldpath, newpath) == -1) {
			if (errno == EOPNOTSUPP || errno == ENOSYS
#ifdef EXDEV
			    || errno == EXDEV
#endif
#ifdef LINK_OPNOTSUPP_ERRNO
			    || errno == LINK_OPNOTSUPP_ERRNO
#endif
			    ) {
				struct stat st;

				/*
				 * fs doesn't support links, so fall back to
				 * stat+rename.  This is racy.
				 */
				if (stat(newpath, &st) == -1) {
					if (rename(oldpath, newpath) == -1)
						status =
						    errno_to_portable(errno);
					else
						status = SSH2_FX_OK;
				}
			} else {
				status = errno_to_portable(errno);
			}
		} else if (unlink(oldpath) == -1) {
			status = errno_to_portable(errno);
			/* clean spare link */
			unlink(newpath);
		} else
			status = SSH2_FX_OK;
	} else if (stat(newpath, &sb) == -1) {
		if (rename(oldpath, newpath) == -1)
			status = errno_to_portable(errno);
		else
			status = SSH2_FX_OK;
	}
	send_status(id, status);
	xfree(oldpath);
	xfree(newpath);
}

static void
process_readlink(void)
{
	u_int32_t id;
	int len;
	char buf[MAXPATHLEN];
	char *path;

	id = get_int();
	path = get_string(NULL);
	debug3("request %u: readlink", id);
	verbose("readlink \"%s\"", path);
	if ((len = readlink(path, buf, sizeof(buf) - 1)) == -1)
		send_status(id, errno_to_portable(errno));
	else {
		Stat s;

		buf[len] = '\0';
		attrib_clear(&s.attrib);
		s.xa_size = 0;
		s.name = s.long_name = buf;
		send_names(id, 1, &s);
	}
	xfree(path);
}

static void
process_symlink(void)
{
	u_int32_t id;
	char *oldpath, *newpath;
	int ret, status;

	id = get_int();
	oldpath = get_string(NULL);
	newpath = get_string(NULL);
	debug3("request %u: symlink", id);
	logit("symlink old \"%s\" new \"%s\"", oldpath, newpath);
	/* this will fail if 'newpath' exists */
	if (readonly)
		status = SSH2_FX_PERMISSION_DENIED;
	else {
		ret = symlink(oldpath, newpath);
		status = (ret == -1) ? errno_to_portable(errno) : SSH2_FX_OK;
	}
	send_status(id, status);
	xfree(oldpath);
	xfree(newpath);
}

static void
process_extended_posix_rename(u_int32_t id)
{
	char *oldpath, *newpath;
	int ret, status;

	oldpath = get_string(NULL);
	newpath = get_string(NULL);
	debug3("request %u: posix-rename", id);
	logit("posix-rename old \"%s\" new \"%s\"", oldpath, newpath);
	if (readonly)
		status = SSH2_FX_PERMISSION_DENIED;
	else {
		ret = rename(oldpath, newpath);
		status = (ret == -1) ? errno_to_portable(errno) : SSH2_FX_OK;
	}
	send_status(id, status);
	xfree(oldpath);
	xfree(newpath);
}

static void
process_extended_statvfs(u_int32_t id)
{
	char *path;
	struct statvfs st;

	path = get_string(NULL);
	debug3("request %u: statfs", id);
	logit("statfs \"%s\"", path);

	if (statvfs(path, &st) != 0)
		send_status(id, errno_to_portable(errno));
	else
		send_statvfs(id, &st);
        xfree(path);
}

static void
process_extended_fstatvfs(u_int32_t id)
{
	int handle, fd;
	struct statvfs st;

	handle = get_handle();
	debug("request %u: fstatvfs \"%s\" (handle %u)",
	    id, handle_to_name(handle), handle);
	if ((fd = handle_to_fd(handle)) < 0) {
		send_status(id, SSH2_FX_FAILURE);
		return;
	}
	if (fstatvfs(fd, &st) != 0)
		send_status(id, errno_to_portable(errno));
	else
		send_statvfs(id, &st);
}

static void
process_extended_hardlink(u_int32_t id)
{
	char *oldpath, *newpath;
	int ret, status;

	oldpath = get_string(NULL);
	newpath = get_string(NULL);
	debug3("request %u: hardlink", id);
	logit("hardlink old \"%s\" new \"%s\"", oldpath, newpath);
	if (readonly)
		status = SSH2_FX_PERMISSION_DENIED;
	else {
		ret = link(oldpath, newpath);
		status = (ret == -1) ? errno_to_portable(errno) : SSH2_FX_OK;
	}
	send_status(id, status);
	xfree(oldpath);
	xfree(newpath);
}

static void
process_extended_setxattr(u_int32_t id)
{
	char *path, *name;
	void *value = NULL;
	u_int size;
	int pflags, ret, status;

	path  = get_string(NULL);
	name  = get_string(NULL);
	value = get_string(&size);
	pflags = get_int();
	debug3("request %u: setxattr", id);
	if (readonly) {
		status = SSH2_FX_PERMISSION_DENIED;
		errno = EACCES;
	} else {
		int flags;
		flags  = (pflags & SSH2_FXE_XATTR_CREATE ) ? XATTR_CREATE  : 0;
		flags |= (pflags & SSH2_FXE_XATTR_REPLACE) ? XATTR_REPLACE : 0;
		logit("setxattr path \"%s\" name \"%s\" size=%d flags=%d", path, name, size, flags);
		ret = lsetxattr(path, name, value, size, flags);
		status = (ret == -1) ? errno_to_portable(errno) : SSH2_FX_OK;
	}
	send_status(id, status);
	xfree(path);
	xfree(name);
	xfree(value);
}

void send_xattr_data (u_int32_t id, const char *data, size_t ret, size_t size) {
	if ((ret != (size_t)-1) && (ret > MAX_XATTR_DATA_LEN) && (size != 0)) {
		debug3("send_xattr_data EMSGSIZE: ret=%ld size=%ld ", ret, size);
		errno = EMSGSIZE;
		ret = (size_t)-1;
	}
	Buffer msg;
	buffer_init(&msg);
	buffer_put_char(&msg, SSH2_FXP_EXTENDED_REPLY);
	buffer_put_int(&msg, id);
	int err_no_p = errno_to_portable(errno);
	debug3("send_xattr_data ret=%ld errno=%d err_no_p=%d", ret, errno, err_no_p);
	buffer_put_int(&msg, ret);
	if (ret == (size_t)-1) {
		buffer_put_int(&msg, err_no_p);
	} else if (size != 0) {
		buffer_append(&msg, data, ret);
	}
	send_msg(&msg);
	buffer_free(&msg);
}

static void
process_extended_getxattr(u_int32_t id)
{
	char *path, *name;
	size_t size;
	size_t ret;

	path  = get_string(NULL);
	name  = get_string(NULL);
	size  = get_int();
	void *value = xmalloc(size+1);

	debug3("request %u: getxattr", id);
	logit("getxattr path \"%s\" name \"%s\" size=%ld", path, name, size);
	ret = lgetxattr(path, name, value, size);
	send_xattr_data(id, value, ret, size);
	xfree(path);
	xfree(name);
	xfree(value);
}

static void
process_extended_listxattr(u_int32_t id)
{
	char *path;
	size_t size;
	size_t ret;

	path  = get_string(NULL);
	size  = get_int();
	void *list = xmalloc(size+1);

	debug3("request %u: listxattr", id);
	logit("listxattr path \"%s\" size=%ld", path, size);
	ret = llistxattr(path, list, size);
	send_xattr_data(id, list, ret, size);
	xfree(path);
	xfree(list);
}

static void
process_extended_removexattr(u_int32_t id)
{
	char *path, *name;
	int ret, status;

	path  = get_string(NULL);
	name  = get_string(NULL);
	debug3("request %u: removexattr", id);
	logit("removexattr path \"%s\" name \"%s\"", path, name);
	if (readonly) {
		status = SSH2_FX_PERMISSION_DENIED;
		errno = EACCES;
	} else {
		ret = lremovexattr(path, name);
		status = (ret == -1) ? errno_to_portable(errno) : SSH2_FX_OK;
	}
	send_status(id, status);
	xfree(path);
	xfree(name);
}

static void
process_extended_cachexattr(u_int32_t id)
{
	debug3("request %u: cachexattr", id);
	xattr_caching = 1;
	send_status(id, SSH2_FX_OK);
}

static void
process_extended_getallxattr(u_int32_t id)
{
	char *path;
	Xattrib *xattrib;
	size_t xa_size;

	path  = get_string(NULL);
	debug3("request %u: getallxattr", id);
	logit("getallxattr path \"%s\"", path);
	xa_size = get_xattr(path, &xattrib);
	debug3("getallxattr: xa_size=%ld", xa_size);

	Buffer msg;
	buffer_init(&msg);
	buffer_put_char(&msg, SSH2_FXP_EXTENDED_REPLY);
	buffer_put_int(&msg, id);
	write_allxattr_data(&msg, xattrib, xa_size);
	send_msg(&msg);
	buffer_free(&msg);
	xfree(path);
	delete_xattr(xattrib, xa_size);
}

static void
process_extended(void)
{
	u_int32_t id;
	char *request;

	id = get_int();
	request = get_string(NULL);
	if (strcmp(request, "posix-rename@openssh.com") == 0)
		process_extended_posix_rename(id);
	else if (strcmp(request, "statvfs@openssh.com") == 0)
		process_extended_statvfs(id);
	else if (strcmp(request, "fstatvfs@openssh.com") == 0)
		process_extended_fstatvfs(id);
	else if (strcmp(request, "hardlink@openssh.com") == 0)
		process_extended_hardlink(id);
	else if (strcmp(request, "setxattr@openssh.com") == 0)
		process_extended_setxattr(id);
	else if (strcmp(request, "getxattr@openssh.com") == 0)
		process_extended_getxattr(id);
	else if (strcmp(request, "listxattr@openssh.com") == 0)
		process_extended_listxattr(id);
	else if (strcmp(request, "removexattr@openssh.com") == 0)
		process_extended_removexattr(id);
	else if (strcmp(request, "cachexattr@openssh.com") == 0)
		process_extended_cachexattr(id);
	else if (strcmp(request, "getallxattr@openssh.com") == 0)
		process_extended_getallxattr(id);
	else
		send_status(id, SSH2_FX_OP_UNSUPPORTED);	/* MUST */
	xfree(request);
}

/* stolen from ssh-agent */

static void
process(void)
{
	u_int msg_len;
	u_int buf_len;
	u_int consumed;
	u_int type;
	u_char *cp;

	buf_len = buffer_len(&iqueue);
	if (buf_len < 5)
		return;		/* Incomplete message. */
	cp = buffer_ptr(&iqueue);
	msg_len = get_u32(cp);
	if (msg_len > SFTP_MAX_MSG_LENGTH) {
		error("bad message from %s local user %s",
		    client_addr, pw->pw_name);
		sftp_server_cleanup_exit(11);
	}
	if (buf_len < msg_len + 4)
		return;
	buffer_consume(&iqueue, 4);
	buf_len -= 4;
	type = buffer_get_char(&iqueue);
	debug3("request type: %d", type);
	switch (type) {
	case SSH2_FXP_INIT:
		process_init();
		break;
	case SSH2_FXP_OPEN:
		process_open();
		break;
	case SSH2_FXP_CLOSE:
		process_close();
		break;
	case SSH2_FXP_READ:
		process_read();
		break;
	case SSH2_FXP_WRITE:
		process_write();
		break;
	case SSH2_FXP_LSTAT:
		process_lstat();
		break;
	case SSH2_FXP_FSTAT:
		process_fstat();
		break;
	case SSH2_FXP_SETSTAT:
		process_setstat();
		break;
	case SSH2_FXP_FSETSTAT:
		process_fsetstat();
		break;
	case SSH2_FXP_OPENDIR:
		process_opendir();
		break;
	case SSH2_FXP_READDIR:
		process_readdir();
		break;
	case SSH2_FXP_REMOVE:
		process_remove();
		break;
	case SSH2_FXP_MKDIR:
		process_mkdir();
		break;
	case SSH2_FXP_RMDIR:
		process_rmdir();
		break;
	case SSH2_FXP_REALPATH:
		process_realpath();
		break;
	case SSH2_FXP_STAT:
		process_stat();
		break;
	case SSH2_FXP_RENAME:
		process_rename();
		break;
	case SSH2_FXP_READLINK:
		process_readlink();
		break;
	case SSH2_FXP_SYMLINK:
		process_symlink();
		break;
	case SSH2_FXP_EXTENDED:
		process_extended();
		break;
	default:
		error("Unknown message %d", type);
		break;
	}
	/* discard the remaining bytes from the current packet */
	if (buf_len < buffer_len(&iqueue)) {
		error("iqueue grew unexpectedly");
		sftp_server_cleanup_exit(255);
	}
	consumed = buf_len - buffer_len(&iqueue);
	if (msg_len < consumed) {
		error("msg_len %d < consumed %d", msg_len, consumed);
		sftp_server_cleanup_exit(255);
	}
	if (msg_len > consumed)
		buffer_consume(&iqueue, msg_len - consumed);
}

/* Cleanup handler that logs active handles upon normal exit */
void
sftp_server_cleanup_exit(int i)
{
	if (pw != NULL && client_addr != NULL) {
		handle_log_exit();
		logit("session closed for local user %s from [%s]",
		    pw->pw_name, client_addr);
	}
	_exit(i);
}

static void
sftp_server_usage(void)
{
	extern char *__progname;

	fprintf(stderr,
	    "usage: %s [-ehR] [-f log_facility] [-l log_level] [-u umask]\n",
	    __progname);
	exit(1);
}

int
sftp_server_main(int argc, char **argv, struct passwd *user_pw)
{
	fd_set *rset, *wset;
	int in, out, max, ch, skipargs = 0, log_stderr = 0;
	ssize_t len, olen, set_size;
	SyslogFacility log_facility = SYSLOG_FACILITY_AUTH;
	char *cp, buf[4*4096];
	long mask;

	extern char *optarg;
	extern char *__progname;

	__progname = ssh_get_progname(argv[0]);
	log_init(__progname, log_level, log_facility, log_stderr);

	while (!skipargs && (ch = getopt(argc, argv, "f:l:u:cehR")) != -1) {
		switch (ch) {
		case 'R':
			readonly = 1;
			break;
		case 'c':
			/*
			 * Ignore all arguments if we are invoked as a
			 * shell using "sftp-server -c command"
			 */
			skipargs = 1;
			break;
		case 'e':
			log_stderr = 1;
			break;
		case 'l':
			log_level = log_level_number(optarg);
			if (log_level == SYSLOG_LEVEL_NOT_SET)
				error("Invalid log level \"%s\"", optarg);
			break;
		case 'f':
			log_facility = log_facility_number(optarg);
			if (log_facility == SYSLOG_FACILITY_NOT_SET)
				error("Invalid log facility \"%s\"", optarg);
			break;
		case 'u':
			errno = 0;
			mask = strtol(optarg, &cp, 8);
			if (mask < 0 || mask > 0777 || *cp != '\0' ||
			    cp == optarg || (mask == 0 && errno != 0))
				fatal("Invalid umask \"%s\"", optarg);
			(void)umask((mode_t)mask);
			break;
		case 'h':
		default:
			sftp_server_usage();
		}
	}

	log_init(__progname, log_level, log_facility, log_stderr);

	if ((cp = getenv("SSH_CONNECTION")) != NULL) {
		client_addr = xstrdup(cp);
		if ((cp = strchr(client_addr, ' ')) == NULL) {
			error("Malformed SSH_CONNECTION variable: \"%s\"",
			    getenv("SSH_CONNECTION"));
			sftp_server_cleanup_exit(255);
		}
		*cp = '\0';
	} else
		client_addr = xstrdup("UNKNOWN");

	pw = pwcopy(user_pw);

	logit("session opened for local user %s from [%s]",
	    pw->pw_name, client_addr);

	in = STDIN_FILENO;
	out = STDOUT_FILENO;

#ifdef HAVE_CYGWIN
	setmode(in, O_BINARY);
	setmode(out, O_BINARY);
#endif

	max = 0;
	if (in > max)
		max = in;
	if (out > max)
		max = out;

	buffer_init(&iqueue);
	buffer_init(&oqueue);

	set_size = howmany(max + 1, NFDBITS) * sizeof(fd_mask);
	rset = (fd_set *)xmalloc(set_size);
	wset = (fd_set *)xmalloc(set_size);

	for (;;) {
		memset(rset, 0, set_size);
		memset(wset, 0, set_size);

		/*
		 * Ensure that we can read a full buffer and handle
		 * the worst-case length packet it can generate,
		 * otherwise apply backpressure by stopping reads.
		 */
		if (buffer_check_alloc(&iqueue, sizeof(buf)) &&
		    buffer_check_alloc(&oqueue, SFTP_MAX_MSG_LENGTH))
			FD_SET(in, rset);

		olen = buffer_len(&oqueue);
		if (olen > 0)
			FD_SET(out, wset);

		if (select(max+1, rset, wset, NULL, NULL) < 0) {
			if (errno == EINTR)
				continue;
			error("select: %s", strerror(errno));
			sftp_server_cleanup_exit(2);
		}

		/* copy stdin to iqueue */
		if (FD_ISSET(in, rset)) {
			len = read(in, buf, sizeof buf);
			if (len == 0) {
				debug("read eof");
				sftp_server_cleanup_exit(0);
			} else if (len < 0) {
				error("read: %s", strerror(errno));
				sftp_server_cleanup_exit(1);
			} else {
				buffer_append(&iqueue, buf, len);
			}
		}
		/* send oqueue to stdout */
		if (FD_ISSET(out, wset)) {
			len = write(out, buffer_ptr(&oqueue), olen);
			if (len < 0) {
				error("write: %s", strerror(errno));
				sftp_server_cleanup_exit(1);
			} else {
				buffer_consume(&oqueue, len);
			}
		}

		/*
		 * Process requests from client if we can fit the results
		 * into the output buffer, otherwise stop processing input
		 * and let the output queue drain.
		 */
		if (buffer_check_alloc(&oqueue, SFTP_MAX_MSG_LENGTH))
			process();
	}
}
