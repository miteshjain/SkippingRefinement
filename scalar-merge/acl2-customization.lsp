(include-book "acl2s/cgen/top" :dir :system :ttags :all)

;; ;; check if ccg is needed
;; (include-book "ccg"  :ttags ((:ccg)) :load-compiled-file nil)
;; (ld "ccg-settings.lsp")

(in-package "ACL2S")

(include-book "data-structures/list-defthms" :dir :system)

(acl2s-defaults :set testing-enabled nil)

;; (add-include-book-dir :acl2s-modes "/Users/jmitesh/acl2/cgen-trunk/acl2s-modes")
;; (ld "acl2s-mode.lsp" :dir :acl2s-modes)
;; (reset-prehistory t)
;; (add-include-book-dir :sv "/Users/jmitesh/projects/skipping/scaler-merge/vectorizing-compiler-case-study-2/")
