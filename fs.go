// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// HTTP file system request handler

package main

import (
	"archive/tar"
	"archive/zip"
	"bytes"
	"encoding/base64"
	"errors"
	"fmt"
	"io"
	"io/fs"
	"math/rand"
	"mime"
	"mime/multipart"
	"net/http"
	"net/textproto"
	"net/url"
	"os"
	"os/exec"
	"path"
	"path/filepath"
	"sort"
	"strconv"
	"strings"
	"time"
)

// A Dir implements FileSystem using the native file system restricted to a
// specific directory tree.
//
// While the FileSystem.Open method takes '/'-separated paths, a Dir's string
// value is a filename on the native file system, not a URL, so it is separated
// by filepath.Separator, which isn't necessarily '/'.
//
// Note that Dir could expose sensitive files and directories. Dir will follow
// symlinks pointing out of the directory tree, which can be especially dangerous
// if serving from a directory in which users are able to create arbitrary symlinks.
// Dir will also allow access to files and directories starting with a period,
// which could expose sensitive directories like .git or sensitive files like
// .htpasswd. To exclude files with a leading period, remove the files/directories
// from the server or create a custom FileSystem implementation.
//
// An empty Dir is treated as ".".
type Dir string

// mapOpenError maps the provided non-nil error from opening name
// to a possibly better non-nil error. In particular, it turns OS-specific errors
// about opening files in non-directories into fs.ErrNotExist. See Issues 18984 and 49552.
func mapOpenError(originalErr error, name string, sep rune, stat func(string) (fs.FileInfo, error)) error {
	if errors.Is(originalErr, fs.ErrNotExist) || errors.Is(originalErr, fs.ErrPermission) {
		return originalErr
	}

	parts := strings.Split(name, string(sep))
	for i := range parts {
		if parts[i] == "" {
			continue
		}
		fi, err := stat(strings.Join(parts[:i+1], string(sep)))
		if err != nil {
			return originalErr
		}
		if !fi.IsDir() {
			return fs.ErrNotExist
		}
	}
	return originalErr
}

// Open implements FileSystem using os.Open, opening files for reading rooted
// and relative to the directory d.
func (d Dir) Open(name string) (File, error) {
	return http.Dir(string(d)).Open(name)
}

// A FileSystem implements access to a collection of named files.
// The elements in a file path are separated by slash ('/', U+002F)
// characters, regardless of host operating system convention.
// See the FileServer function to convert a FileSystem to a Handler.
//
// This interface predates the fs.FS interface, which can be used instead:
// the FS adapter function converts an fs.FS to a FileSystem.
type FileSystem interface {
	Open(name string) (File, error)
}

// A File is returned by a FileSystem's Open method and can be
// served by the FileServer implementation.
//
// The methods should behave the same as those on an *os.File.
type File interface {
	io.Closer
	io.Reader
	io.Seeker
	Readdir(count int) ([]fs.FileInfo, error)
	Stat() (fs.FileInfo, error)
}

type anyDirs interface {
	len() int
	name(i int) string
	isDir(i int) bool
}

type fileInfoDirs []fs.FileInfo

func (d fileInfoDirs) len() int          { return len(d) }
func (d fileInfoDirs) isDir(i int) bool  { return d[i].IsDir() }
func (d fileInfoDirs) name(i int) string { return d[i].Name() }

type dirEntryDirs []fs.DirEntry

func (d dirEntryDirs) len() int          { return len(d) }
func (d dirEntryDirs) isDir(i int) bool  { return d[i].IsDir() }
func (d dirEntryDirs) name(i int) string { return d[i].Name() }

func dirList(w http.ResponseWriter, r *http.Request, f File) {
	// Prefer to use ReadDir instead of Readdir,
	// because the former doesn't require calling
	// Stat on every entry of a directory on Unix.
	var dirs anyDirs
	var err error
	if d, ok := f.(fs.ReadDirFile); ok {
		var list dirEntryDirs
		list, err = d.ReadDir(-1)
		dirs = list
	} else {
		var list fileInfoDirs
		list, err = f.Readdir(-1)
		dirs = list
	}

	if err != nil {
		http.Error(w, "Error reading directory", http.StatusInternalServerError)
		return
	}
	sort.Slice(dirs, func(i, j int) bool { return dirs.name(i) < dirs.name(j) })

	w.Header().Set("Content-Type", "text/html; charset=utf-8")
	fmt.Fprintf(w, `
	<!doctype html>
	<html lang="en">
	  <head>
		<meta charset="utf-8">
		<meta name="viewport" content="width=device-width, initial-scale=1">
		<title>Browsile</title>
		<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/bulma@0.9.4/css/bulma.min.css">
	  </head>
	  <body>	
	  <section class="section">
	  <div class="container columns is-multiline is-variable is-desktop">
	  <div class="card column">
	  <div class="card-content">
		  <div class="content">
		  <a href="..">..</a>
		  </div>
		  <div class="buttons">
		  <a class="button is-primary" href="..">..</a>
	  </div>
		</div>
		</div>
	`)
	fmt.Fprintf(w, "\n")

	for i, n := 0, dirs.len(); i < n; i++ {
		name := dirs.name(i)
		if dirs.isDir(i) {
			name += "/"
		}
		// name may contain '?' or '#', which must be escaped to remain
		// part of the URL path, and not indicate the start of a query
		// string or fragment.
		urln := url.URL{Path: name}
		urlImageView := url.URL{Path: name}
		if !strings.HasSuffix(name, "/") {
			urlImageView.RawQuery = url.Values{
				"thumb": {"true"},
			}.Encode()
		}

		if dirs.isDir(i) {
			dirImg, _ := url.Parse("data:image/png;base64,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")
			urlImageView = *dirImg
		}

		name = htmlReplacer.Replace(name)

		mpvBtnClass := "is-hidden"
		if !strings.HasSuffix(name, "/") {
			mpvBtnClass = ""
		}

		dirTarBtnClass := "is-hidden"
		if strings.HasSuffix(name, "/") {
			dirTarBtnClass = ""
		}

		fmt.Fprintf(w, `
		<div class="card column">
		<div class="card-image">
			<figure class="image is-4by3">
				<img loading="lazy" src="%s" alt="Thumbnail">
			</figure>
		</div>
		<div class="card-content">
			<div class="content">
			<a href="%s">%s</a>
			</div>
			<div class="buttons">
				<a class="button is-primary %s" href="%s?archive=tar">tar</a>
				<a class="button is-primary %s" href="%s?dl=true">dl</a>
				<button class="button is-link %s" onclick="javascript:{ 
					const linkSource = `+"`intent://${window.location.host.toString() + window.location.pathname.toString()}%s#Intent;type=video/any;package=is.xyz.mpv;scheme=${window.location.protocol.slice(0, -1)};end;`"+`;
					const downloadLink = document.createElement('a');
					downloadLink.href = linkSource;
					console.log(downloadLink)
					downloadLink.click();
				 }">mpv</button>
			</div>
		</div>
	</div>`, urlImageView.String(), urln.String(), name, dirTarBtnClass, urln.String(), mpvBtnClass, urln.String(), mpvBtnClass, urln.String())

	}
	fmt.Fprintf(w, `
	</div>
	</section>
	</body>
	</html>	
	`)
}

var htmlReplacer = strings.NewReplacer(
	"&", "&amp;",
	"<", "&lt;",
	">", "&gt;",
	// "&#34;" is shorter than "&quot;".
	`"`, "&#34;",
	// "&#39;" is shorter than "&apos;" and apos was not in HTML until HTML5.
	"'", "&#39;",
)

// ServeContent replies to the request using the content in the
// provided ReadSeeker. The main benefit of ServeContent over io.Copy
// is that it handles Range requests properly, sets the MIME type, and
// handles If-Match, If-Unmodified-Since, If-None-Match, If-Modified-Since,
// and If-Range requests.
//
// If the response's Content-Type header is not set, ServeContent
// first tries to deduce the type from name's file extension and,
// if that fails, falls back to reading the first block of the content
// and passing it to DetectContentType.
// The name is otherwise unused; in particular it can be empty and is
// never sent in the response.
//
// If modtime is not the zero time or Unix epoch, ServeContent
// includes it in a Last-Modified header in the response. If the
// request includes an If-Modified-Since header, ServeContent uses
// modtime to decide whether the content needs to be sent at all.
//
// The content's Seek method must work: ServeContent uses
// a seek to the end of the content to determine its size.
//
// If the caller has set w's ETag header formatted per RFC 7232, section 2.3,
// ServeContent uses it to handle requests using If-Match, If-None-Match, or If-Range.
//
// Note that *os.File implements the io.ReadSeeker interface.
func ServeContent(w http.ResponseWriter, req *http.Request, name string, modtime time.Time, content io.ReadSeeker) {
	sizeFunc := func() (int64, error) {
		size, err := content.Seek(0, io.SeekEnd)
		if err != nil {
			return 0, errSeeker
		}
		_, err = content.Seek(0, io.SeekStart)
		if err != nil {
			return 0, errSeeker
		}
		return size, nil
	}
	serveContent(w, req, name, modtime, sizeFunc, content)
}

// errSeeker is returned by ServeContent's sizeFunc when the content
// doesn't seek properly. The underlying Seeker's error text isn't
// included in the sizeFunc reply so it's not sent over HTTP to end
// users.
var errSeeker = errors.New("seeker can't seek")

// errNoOverlap is returned by serveContent's parseRange if first-byte-pos of
// all of the byte-range-spec values is greater than the content size.
var errNoOverlap = errors.New("invalid range: failed to overlap")

// if name is empty, filename is unknown. (used for mime type, before sniffing)
// if modtime.IsZero(), modtime is unknown.
// content must be seeked to the beginning of the file.
// The sizeFunc is called at most once. Its error, if any, is sent in the HTTP response.
func serveContent(w http.ResponseWriter, r *http.Request, name string, modtime time.Time, sizeFunc func() (int64, error), content io.ReadSeeker) {
	if r.URL.Query().Get("dl") == "true" {
		w.Header().Set("Content-Disposition", "attachment; filename="+strconv.Quote(filepath.Base(name)))
		w.Header().Set("Content-Type", "application/octet-stream")
	}
	setLastModified(w, modtime)
	done, rangeReq := checkPreconditions(w, r, modtime)
	if done {
		return
	}

	code := http.StatusOK

	// If Content-Type isn't set, use the file's extension to find it, but
	// if the Content-Type is unset explicitly, do not sniff the type.
	ctypes, haveType := w.Header()["Content-Type"]
	var ctype string
	if !haveType {
		ctype = mime.TypeByExtension(filepath.Ext(name))
		if ctype == "" {
			// read a chunk to decide between utf-8 text and binary
			var buf [512]byte
			n, _ := io.ReadFull(content, buf[:])
			ctype = http.DetectContentType(buf[:n])
			_, err := content.Seek(0, io.SeekStart) // rewind to output whole file
			if err != nil {
				http.Error(w, "seeker can't seek", http.StatusInternalServerError)
				return
			}
		}
		w.Header().Set("Content-Type", ctype)
	} else if len(ctypes) > 0 {
		ctype = ctypes[0]
	}

	size, err := sizeFunc()
	if err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}
	if size < 0 {
		// Should never happen but just to be sure
		http.Error(w, "negative content size computed", http.StatusInternalServerError)
		return
	}

	// handle Content-Range header.
	sendSize := size
	var sendContent io.Reader = content
	ranges, err := parseRange(rangeReq, size)
	switch err {
	case nil:
	case errNoOverlap:
		if size == 0 {
			// Some clients add a Range header to all requests to
			// limit the size of the response. If the file is empty,
			// ignore the range header and respond with a 200 rather
			// than a 416.
			ranges = nil
			break
		}
		w.Header().Set("Content-Range", fmt.Sprintf("bytes */%d", size))
		fallthrough
	default:
		http.Error(w, err.Error(), http.StatusRequestedRangeNotSatisfiable)
		return
	}

	if sumRangesSize(ranges) > size {
		// The total number of bytes in all the ranges
		// is larger than the size of the file by
		// itself, so this is probably an attack, or a
		// dumb client. Ignore the range request.
		ranges = nil
	}
	switch {
	case len(ranges) == 1:
		// RFC 7233, Section 4.1:
		// "If a single part is being transferred, the server
		// generating the 206 response MUST generate a
		// Content-Range header field, describing what range
		// of the selected representation is enclosed, and a
		// payload consisting of the range.
		// ...
		// A server MUST NOT generate a multipart response to
		// a request for a single range, since a client that
		// does not request multiple parts might not support
		// multipart responses."
		ra := ranges[0]
		if _, err := content.Seek(ra.start, io.SeekStart); err != nil {
			http.Error(w, err.Error(), http.StatusRequestedRangeNotSatisfiable)
			return
		}
		sendSize = ra.length
		code = http.StatusPartialContent
		w.Header().Set("Content-Range", ra.contentRange(size))
	case len(ranges) > 1:
		sendSize = rangesMIMESize(ranges, ctype, size)
		code = http.StatusPartialContent

		pr, pw := io.Pipe()
		mw := multipart.NewWriter(pw)
		w.Header().Set("Content-Type", "multipart/byteranges; boundary="+mw.Boundary())
		sendContent = pr
		defer pr.Close() // cause writing goroutine to fail and exit if CopyN doesn't finish.
		go func() {
			for _, ra := range ranges {
				part, err := mw.CreatePart(ra.mimeHeader(ctype, size))
				if err != nil {
					pw.CloseWithError(err)
					return
				}
				if _, err := content.Seek(ra.start, io.SeekStart); err != nil {
					pw.CloseWithError(err)
					return
				}
				if _, err := io.CopyN(part, content, ra.length); err != nil {
					pw.CloseWithError(err)
					return
				}
			}
			mw.Close()
			pw.Close()
		}()
	}

	w.Header().Set("Accept-Ranges", "bytes")
	if w.Header().Get("Content-Encoding") == "" {
		w.Header().Set("Content-Length", strconv.FormatInt(sendSize, 10))
	}

	w.WriteHeader(code)

	if r.Method != "HEAD" {
		io.CopyN(w, sendContent, sendSize)
	}
}

// scanETag determines if a syntactically valid ETag is present at s. If so,
// the ETag and remaining text after consuming ETag is returned. Otherwise,
// it returns "", "".
func scanETag(s string) (etag string, remain string) {
	s = textproto.TrimString(s)
	start := 0
	if strings.HasPrefix(s, "W/") {
		start = 2
	}
	if len(s[start:]) < 2 || s[start] != '"' {
		return "", ""
	}
	// ETag is either W/"text" or "text".
	// See RFC 7232 2.3.
	for i := start + 1; i < len(s); i++ {
		c := s[i]
		switch {
		// Character values allowed in ETags.
		case c == 0x21 || c >= 0x23 && c <= 0x7E || c >= 0x80:
		case c == '"':
			return s[:i+1], s[i+1:]
		default:
			return "", ""
		}
	}
	return "", ""
}

// etagStrongMatch reports whether a and b match using strong ETag comparison.
// Assumes a and b are valid ETags.
func etagStrongMatch(a, b string) bool {
	return a == b && a != "" && a[0] == '"'
}

// etagWeakMatch reports whether a and b match using weak ETag comparison.
// Assumes a and b are valid ETags.
func etagWeakMatch(a, b string) bool {
	return strings.TrimPrefix(a, "W/") == strings.TrimPrefix(b, "W/")
}

// condResult is the result of an HTTP request precondition check.
// See https://tools.ietf.org/html/rfc7232 section 3.
type condResult int

const (
	condNone condResult = iota
	condTrue
	condFalse
)

func checkIfMatch(w http.ResponseWriter, r *http.Request) condResult {
	im := r.Header.Get("If-Match")
	if im == "" {
		return condNone
	}
	for {
		im = textproto.TrimString(im)
		if len(im) == 0 {
			break
		}
		if im[0] == ',' {
			im = im[1:]
			continue
		}
		if im[0] == '*' {
			return condTrue
		}
		etag, remain := scanETag(im)
		if etag == "" {
			break
		}
		if etagStrongMatch(etag, w.Header().Get("Etag")) {
			return condTrue
		}
		im = remain
	}

	return condFalse
}

func checkIfUnmodifiedSince(r *http.Request, modtime time.Time) condResult {
	ius := r.Header.Get("If-Unmodified-Since")
	if ius == "" || isZeroTime(modtime) {
		return condNone
	}
	t, err := http.ParseTime(ius)
	if err != nil {
		return condNone
	}

	// The Last-Modified header truncates sub-second precision so
	// the modtime needs to be truncated too.
	modtime = modtime.Truncate(time.Second)
	if ret := modtime.Compare(t); ret <= 0 {
		return condTrue
	}
	return condFalse
}

func checkIfNoneMatch(w http.ResponseWriter, r *http.Request) condResult {
	inm := r.Header.Get("If-None-Match")
	if inm == "" {
		return condNone
	}
	buf := inm
	for {
		buf = textproto.TrimString(buf)
		if len(buf) == 0 {
			break
		}
		if buf[0] == ',' {
			buf = buf[1:]
			continue
		}
		if buf[0] == '*' {
			return condFalse
		}
		etag, remain := scanETag(buf)
		if etag == "" {
			break
		}
		if etagWeakMatch(etag, w.Header().Get("Etag")) {
			return condFalse
		}
		buf = remain
	}
	return condTrue
}

func checkIfModifiedSince(r *http.Request, modtime time.Time) condResult {
	if r.Method != "GET" && r.Method != "HEAD" {
		return condNone
	}
	ims := r.Header.Get("If-Modified-Since")
	if ims == "" || isZeroTime(modtime) {
		return condNone
	}
	t, err := http.ParseTime(ims)
	if err != nil {
		return condNone
	}
	// The Last-Modified header truncates sub-second precision so
	// the modtime needs to be truncated too.
	modtime = modtime.Truncate(time.Second)
	if ret := modtime.Compare(t); ret <= 0 {
		return condFalse
	}
	return condTrue
}

func checkIfRange(w http.ResponseWriter, r *http.Request, modtime time.Time) condResult {
	if r.Method != "GET" && r.Method != "HEAD" {
		return condNone
	}
	ir := r.Header.Get("If-Range")
	if ir == "" {
		return condNone
	}
	etag, _ := scanETag(ir)
	if etag != "" {
		if etagStrongMatch(etag, w.Header().Get("Etag")) {
			return condTrue
		} else {
			return condFalse
		}
	}
	// The If-Range value is typically the ETag value, but it may also be
	// the modtime date. See golang.org/issue/8367.
	if modtime.IsZero() {
		return condFalse
	}
	t, err := http.ParseTime(ir)
	if err != nil {
		return condFalse
	}
	if t.Unix() == modtime.Unix() {
		return condTrue
	}
	return condFalse
}

var unixEpochTime = time.Unix(0, 0)

// isZeroTime reports whether t is obviously unspecified (either zero or Unix()=0).
func isZeroTime(t time.Time) bool {
	return t.IsZero() || t.Equal(unixEpochTime)
}

func setLastModified(w http.ResponseWriter, modtime time.Time) {
	if !isZeroTime(modtime) {
		w.Header().Set("Last-Modified", modtime.UTC().Format(http.TimeFormat))
	}
}

func writeNotModified(w http.ResponseWriter) {
	// RFC 7232 section 4.1:
	// a sender SHOULD NOT generate representation metadata other than the
	// above listed fields unless said metadata exists for the purpose of
	// guiding cache updates (e.g., Last-Modified might be useful if the
	// response does not have an ETag field).
	h := w.Header()
	delete(h, "Content-Type")
	delete(h, "Content-Length")
	delete(h, "Content-Encoding")
	if h.Get("Etag") != "" {
		delete(h, "Last-Modified")
	}
	w.WriteHeader(http.StatusNotModified)
}

// checkPreconditions evaluates request preconditions and reports whether a precondition
// resulted in sending http.StatusNotModified or http.StatusPreconditionFailed.
func checkPreconditions(w http.ResponseWriter, r *http.Request, modtime time.Time) (done bool, rangeHeader string) {
	// This function carefully follows RFC 7232 section 6.
	ch := checkIfMatch(w, r)
	if ch == condNone {
		ch = checkIfUnmodifiedSince(r, modtime)
	}
	if ch == condFalse {
		w.WriteHeader(http.StatusPreconditionFailed)
		return true, ""
	}
	switch checkIfNoneMatch(w, r) {
	case condFalse:
		if r.Method == "GET" || r.Method == "HEAD" {
			writeNotModified(w)
			return true, ""
		} else {
			w.WriteHeader(http.StatusPreconditionFailed)
			return true, ""
		}
	case condNone:
		if checkIfModifiedSince(r, modtime) == condFalse {
			writeNotModified(w)
			return true, ""
		}
	}

	rangeHeader = r.Header.Get("Range")
	if rangeHeader != "" && checkIfRange(w, r, modtime) == condFalse {
		rangeHeader = ""
	}
	return false, rangeHeader
}

// name is '/'-separated, not filepath.Separator.
func serveFile(w http.ResponseWriter, r *http.Request, fs FileSystem, name string, redirect bool) {
	const indexPage = "/index.html"

	// redirect .../index.html to .../
	// can't use Redirect() because that would make the path absolute,
	// which would be a problem running under StripPrefix
	if strings.HasSuffix(r.URL.Path, indexPage) {
		localRedirect(w, r, "./")
		return
	}

	f, err := fs.Open(name)
	if err != nil {
		msg, code := toHTTPError(err)
		http.Error(w, msg, code)
		return
	}
	defer f.Close()

	d, err := f.Stat()
	if err != nil {
		msg, code := toHTTPError(err)
		http.Error(w, msg, code)
		return
	}

	if redirect {
		// redirect to canonical path: / at end of directory url
		// r.URL.Path always begins with /
		url := r.URL.Path
		if d.IsDir() {
			if url[len(url)-1] != '/' {
				localRedirect(w, r, path.Base(url)+"/")
				return
			}
		} else {
			if url[len(url)-1] == '/' {
				localRedirect(w, r, "../"+path.Base(url))
				return
			}
		}
	}

	if d.IsDir() {
		url := r.URL.Path
		// redirect if the directory name doesn't end in a slash
		if url == "" || url[len(url)-1] != '/' {
			localRedirect(w, r, path.Base(url)+"/")
			return
		}

		// use contents of index.html for directory, if present
		index := strings.TrimSuffix(name, "/") + indexPage
		ff, err := fs.Open(index)
		if err == nil {
			defer ff.Close()
			dd, err := ff.Stat()
			if err == nil {
				d = dd
				f = ff
			}
		}
	}

	// Still a directory? (we didn't find an index.html file)
	if d.IsDir() {
		if checkIfModifiedSince(r, d.ModTime()) == condFalse {
			writeNotModified(w)
			return
		}
		setLastModified(w, d.ModTime())
		dirList(w, r, f)
		return
	}

	// serveContent will check modification time
	sizeFunc := func() (int64, error) { return d.Size(), nil }
	serveContent(w, r, d.Name(), d.ModTime(), sizeFunc, f)
}

// toHTTPError returns a non-specific HTTP error message and http.Status code
// for a given non-nil error value. It's important that toHTTPError does not
// actually return err.Error(), since msg and httphttp.Status are returned to users,
// and historically Go's ServeContent always returned just "404 Not Found" for
// all errors. We don't want to start leaking information in error messages.
func toHTTPError(err error) (msg string, status int) {
	if errors.Is(err, fs.ErrNotExist) {
		return "404 page not found", http.StatusNotFound
	}
	if errors.Is(err, fs.ErrPermission) {
		return "403 Forbidden", http.StatusForbidden
	}
	// Default:
	return "500 Internal Server Error", http.StatusInternalServerError
}

// localRedirect gives a Moved Permanently response.
// It does not convert relative paths to absolute paths like Redirect does.
func localRedirect(w http.ResponseWriter, r *http.Request, newPath string) {
	if q := r.URL.RawQuery; q != "" {
		newPath += "?" + q
	}
	w.Header().Set("Location", newPath)
	w.WriteHeader(http.StatusMovedPermanently)
}

// ServeFile replies to the request with the contents of the named
// file or directory.
//
// If the provided file or directory name is a relative path, it is
// interpreted relative to the current directory and may ascend to
// parent directories. If the provided name is constructed from user
// input, it should be sanitized before calling ServeFile.
//
// As a precaution, ServeFile will reject requests where r.URL.Path
// contains a ".." path element; this protects against callers who
// might unsafely use filepath.Join on r.URL.Path without sanitizing
// it and then use that filepath.Join result as the name argument.
//
// As another special case, ServeFile redirects any request where r.URL.Path
// ends in "/index.html" to the same path, without the final
// "index.html". To avoid such redirects either modify the path or
// use ServeContent.
//
// Outside of those two special cases, ServeFile does not use
// r.URL.Path for selecting the file or directory to serve; only the
// file or directory provided in the name argument is used.
func ServeFile(w http.ResponseWriter, r *http.Request, name string) {
	if containsDotDot(r.URL.Path) {
		// Too many programs use r.URL.Path to construct the argument to
		// serveFile. Reject the request under the assumption that happened
		// here and ".." may not be wanted.
		// Note that name might not contain "..", for example if code (still
		// incorrectly) used filepath.Join(myDir, r.URL.Path).
		http.Error(w, "invalid URL path", http.StatusBadRequest)
		return
	}
	dir, file := filepath.Split(name)
	serveFile(w, r, Dir(dir), file, false)
}

func containsDotDot(v string) bool {
	if !strings.Contains(v, "..") {
		return false
	}
	for _, ent := range strings.FieldsFunc(v, isSlashRune) {
		if ent == ".." {
			return true
		}
	}
	return false
}

func isSlashRune(r rune) bool { return r == '/' || r == '\\' }

type fileHandler struct {
	root FileSystem
}

type ioFS struct {
	fsys fs.FS
}

type ioFile struct {
	file fs.File
}

func (f ioFS) Open(name string) (File, error) {
	if name == "/" {
		name = "."
	} else {
		name = strings.TrimPrefix(name, "/")
	}
	file, err := f.fsys.Open(name)
	if err != nil {
		return nil, mapOpenError(err, name, '/', func(path string) (fs.FileInfo, error) {
			return fs.Stat(f.fsys, path)
		})
	}
	return ioFile{file}, nil
}

func (f ioFile) Close() error               { return f.file.Close() }
func (f ioFile) Read(b []byte) (int, error) { return f.file.Read(b) }
func (f ioFile) Stat() (fs.FileInfo, error) { return f.file.Stat() }

var errMissingSeek = errors.New("io.File missing Seek method")
var errMissingReadDir = errors.New("io.File directory missing ReadDir method")

func (f ioFile) Seek(offset int64, whence int) (int64, error) {
	s, ok := f.file.(io.Seeker)
	if !ok {
		return 0, errMissingSeek
	}
	return s.Seek(offset, whence)
}

func (f ioFile) ReadDir(count int) ([]fs.DirEntry, error) {
	d, ok := f.file.(fs.ReadDirFile)
	if !ok {
		return nil, errMissingReadDir
	}
	return d.ReadDir(count)
}

func (f ioFile) Readdir(count int) ([]fs.FileInfo, error) {
	d, ok := f.file.(fs.ReadDirFile)
	if !ok {
		return nil, errMissingReadDir
	}
	var list []fs.FileInfo
	for {
		dirs, err := d.ReadDir(count - len(list))
		for _, dir := range dirs {
			info, err := dir.Info()
			if err != nil {
				// Pretend it doesn't exist, like (*os.File).Readdir does.
				continue
			}
			list = append(list, info)
		}
		if err != nil {
			return list, err
		}
		if count < 0 || len(list) >= count {
			break
		}
	}
	return list, nil
}

// FS converts fsys to a FileSystem implementation,
// for use with FileServer and NewFileTransport.
// The files provided by fsys must implement io.Seeker.
func FS(fsys fs.FS) FileSystem {
	return ioFS{fsys}
}

// FileServer returns a handler that serves HTTP requests
// with the contents of the file system rooted at root.
//
// As a special case, the returned file server redirects any request
// ending in "/index.html" to the same path, without the final
// "index.html".
//
// To use the operating system's file system implementation,
// use http.Dir:
//
//	http.Handle("/", http.FileServer(http.Dir("/tmp")))
//
// To use an fs.FS implementation, use http.FS to convert it:
//
//	http.Handle("/", http.FileServer(http.FS(fsys)))
func FileServer(root FileSystem) http.Handler {
	return &fileHandler{root}
}

const FileImg = `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`

func (f *fileHandler) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	upath := r.URL.Path
	if r.URL.Query().Get("thumb") == "true" {
		filePath := r.URL.Path
		args := []string{}
		args = append(args, "-s", "0", "-q", "10")
		args = append(args, "-t", strconv.Itoa(rand.Intn(100)))

		args = append(args, "-i", filePath, "-o", "/dev/stdout", "-cpng")
		cmd := exec.Command("ffmpegthumbnailer", args...)
		cmd.Stderr = os.Stderr
		body, err := cmd.Output()
		if err != nil {
			fimg, _ := base64.StdEncoding.DecodeString(FileImg)
			http.ServeContent(w, r, "", time.Now(), bytes.NewReader(fimg))
			return
		}
		http.ServeContent(w, r, "", time.Now(), bytes.NewReader(body))
		return
	}

	if !strings.HasPrefix(upath, "/") {
		upath = "/" + upath
		r.URL.Path = upath
	}
	if strings.HasSuffix(upath, "/") {
		if r.URL.Query().Get("archive") == "tar" {
			TarDir(path.Clean(upath), w, filepath.Base(upath))
			return
		}
		if r.URL.Query().Get("archive") == "zip" {
			ZipDir(path.Clean(upath), w, filepath.Base(upath))
			return
		}
	}
	serveFile(w, r, f.root, path.Clean(upath), true)
}

func TarDir(dirpath string, w http.ResponseWriter, name string) {
	w.Header().Set("Content-Type", "application/x-tar")
	w.Header().Set("Content-disposition", `attachment; filename="`+name+`.tar"`)
	w.WriteHeader(http.StatusOK)
	tw := tar.NewWriter(w)
	defer tw.Close()

	_ = filepath.WalkDir(dirpath, func(p string, de fs.DirEntry, err error) error {
		if err != nil {
			return err
		}

		info, ierr := de.Info()
		if ierr != nil {
			return ierr
		}

		if !info.Mode().IsRegular() {
			return nil
		}

		rel, err := filepath.Rel(dirpath, p)
		if err != nil {
			return err
		}
		f, err := os.Open(p)
		if err != nil {
			return err
		}
		defer f.Close()

		h, err := tar.FileInfoHeader(info, "")
		if err != nil {
			return err
		}
		h.Name = rel
		if err := tw.WriteHeader(h); err != nil {
			return err
		}
		n, err := io.Copy(tw, f)
		if info.Size() != n {
			return fmt.Errorf("mismatch of size with %s", rel)
		}
		return err
	})
}

func ZipDir(dirpath string, w http.ResponseWriter, name string) {
	w.Header().Set("Content-Type", "application/zip")
	w.Header().Set("Content-disposition", `attachment; filename="`+name+`.zip"`)
	w.WriteHeader(http.StatusOK)
	zw := zip.NewWriter(w)
	defer zw.Close()

	_ = filepath.WalkDir(dirpath, func(p string, de fs.DirEntry, err error) error {
		if err != nil {
			return err
		}

		info, ierr := de.Info()
		if ierr != nil {
			return ierr
		}

		if !info.Mode().IsRegular() {
			return nil
		}

		rel, err := filepath.Rel(dirpath, p)
		if err != nil {
			return err
		}
		f, err := os.Open(p)
		if err != nil {
			return err
		}
		defer f.Close()

		h, err := zip.FileInfoHeader(info)
		if err != nil {
			return err
		}

		h.Name = rel
		//h.Method = zip.Deflate

		zf, err := zw.CreateHeader(h)
		if err != nil {
			return err
		}

		n, err := io.Copy(zf, f)
		if info.Size() != n {
			return fmt.Errorf("mismatch of size with %s", rel)
		}

		return err

	})

}

// httpRange specifies the byte range to be sent to the client.
type httpRange struct {
	start, length int64
}

func (r httpRange) contentRange(size int64) string {
	return fmt.Sprintf("bytes %d-%d/%d", r.start, r.start+r.length-1, size)
}

func (r httpRange) mimeHeader(contentType string, size int64) textproto.MIMEHeader {
	return textproto.MIMEHeader{
		"Content-Range": {r.contentRange(size)},
		"Content-Type":  {contentType},
	}
}

// parseRange parses a Range header string as per RFC 7233.
// errNoOverlap is returned if none of the ranges overlap.
func parseRange(s string, size int64) ([]httpRange, error) {
	if s == "" {
		return nil, nil // header not present
	}
	const b = "bytes="
	if !strings.HasPrefix(s, b) {
		return nil, errors.New("invalid range")
	}
	var ranges []httpRange
	noOverlap := false
	for _, ra := range strings.Split(s[len(b):], ",") {
		ra = textproto.TrimString(ra)
		if ra == "" {
			continue
		}
		start, end, ok := strings.Cut(ra, "-")
		if !ok {
			return nil, errors.New("invalid range")
		}
		start, end = textproto.TrimString(start), textproto.TrimString(end)
		var r httpRange
		if start == "" {
			// If no start is specified, end specifies the
			// range start relative to the end of the file,
			// and we are dealing with <suffix-length>
			// which has to be a non-negative integer as per
			// RFC 7233 Section 2.1 "Byte-Ranges".
			if end == "" || end[0] == '-' {
				return nil, errors.New("invalid range")
			}
			i, err := strconv.ParseInt(end, 10, 64)
			if i < 0 || err != nil {
				return nil, errors.New("invalid range")
			}
			if i > size {
				i = size
			}
			r.start = size - i
			r.length = size - r.start
		} else {
			i, err := strconv.ParseInt(start, 10, 64)
			if err != nil || i < 0 {
				return nil, errors.New("invalid range")
			}
			if i >= size {
				// If the range begins after the size of the content,
				// then it does not overlap.
				noOverlap = true
				continue
			}
			r.start = i
			if end == "" {
				// If no end is specified, range extends to end of the file.
				r.length = size - r.start
			} else {
				i, err := strconv.ParseInt(end, 10, 64)
				if err != nil || r.start > i {
					return nil, errors.New("invalid range")
				}
				if i >= size {
					i = size - 1
				}
				r.length = i - r.start + 1
			}
		}
		ranges = append(ranges, r)
	}
	if noOverlap && len(ranges) == 0 {
		// The specified ranges did not overlap with the content.
		return nil, errNoOverlap
	}
	return ranges, nil
}

// countingWriter counts how many bytes have been written to it.
type countingWriter int64

func (w *countingWriter) Write(p []byte) (n int, err error) {
	*w += countingWriter(len(p))
	return len(p), nil
}

// rangesMIMESize returns the number of bytes it takes to encode the
// provided ranges as a multipart response.
func rangesMIMESize(ranges []httpRange, contentType string, contentSize int64) (encSize int64) {
	var w countingWriter
	mw := multipart.NewWriter(&w)
	for _, ra := range ranges {
		mw.CreatePart(ra.mimeHeader(contentType, contentSize))
		encSize += ra.length
	}
	mw.Close()
	encSize += int64(w)
	return
}

func sumRangesSize(ranges []httpRange) (size int64) {
	for _, ra := range ranges {
		size += ra.length
	}
	return
}
