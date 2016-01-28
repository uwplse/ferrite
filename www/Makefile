.PHONY: all clean deploy

all: _site/index.html

BUILDARGS :=
_site/index.html:
	jekyll build --config _config.yml $(BUILDARGS)

_site/index.html: $(wildcard *.html) _config.yml _layouts/default.html
clean:
	$(RM) -r _site

CSEHOST := bicycle.cs.washington.edu
CSEPATH := /cse/web/research/sandcat/ferrite
RSYNCARGS := --compress --recursive --checksum --itemize-changes \
	--delete -e ssh --perms --chmod=ug+rw

rsync:
	rsync $(RSYNCARGS) _site/ $(CSEHOST):$(CSEPATH)

deploy: clean all rsync
