SHELL=/bin/bash
FILES=LICENSE $(wildcard *.lisp)
ACL2S=/Users/jmitesh/acl2/cgen-trunk/acl2s-modes/
LIBPATH=/Users/jmitesh/acl2/cgen-trunk/acl2s-modes/acl2s-lib.jar

.PHONY: all clean
.SECONDARY:

all: data-struct.cert op-semantics.cert scalar-vector.cert

%.cert: %.lisp %.acl2
	${ACL2S}certify-book.sh "$<"

%.acl2: %.lisp
	java -cp "$(LIBPATH)" acl2s.lib.certify.MaybeExtractPreamble "$<"

op-semantics.cert: data-struct.cert
scalar-vector.cert: op-semantics.cert


clean:
	rm -rf *.{o,port,cert,acl2,out,fasl,dx64fsl,dx32fsl,lx64fsl,lx32fsl,wx64fsl,wx32fsl} *expansion.lsp TAGS
