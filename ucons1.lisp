;; -*- mode: common-lisp; package: ucons; -*-
;(provide 'ucons1)

(in-package :mma)

(use-package 'excl)
;(require 'hcons)
(load "hcons")
(import 'excl:hcons)
;; copies of all re-usable expressions will be in ucons::uniqtab
;; (export '(ucons uniq ulist uappend umapcar))
(defvar uniqtab (make-hash-table :test #'eq))
  
;; this hashtable is used for uniq copies of non-fixnum
;; atoms like 1/2, #c(0 1), or bignums. Although a vector is
;; officially an atom in common lisp, this will not unique-ify it,
;; since eql doesn't do that.  Equalp does, in case we're tempted.

(defvar uniqatoms (make-hash-table :test #'eql))
  
(defun ucons(a b)
  (hcons a b uniqtab))

;; analog of lisp list function
(defmacro ulist(&rest l)(cond ((null l)nil)
			      (t `(hcons ,(car l) (ulist ,@(cdr l)) uniqtab))))

;; analog of lisp append function
(defun uappend(r s)(cond ((null r)s)
			 (t (ucons (car r)(uappend (cdr r) s)))))

(defmacro uconsm(a b)`(hcons ,a ,b uniqtab))

(defun umapcar(f x)(cond((null x)nil)
			(t (ucons (funcall f (car x))(umapcar f (cdr x))))))
  
;; uniq(h) ;; provide a unique copy of a tree
;; Note that this really is limited to acyclic directed graphs.
;; Shared substructure is handled correctly,
;;but a cyclic structure will loop until memory or patience is exhausted.
    	      
(defun uniq(h)
    (cond ((consp h)
           (hcons (uniq (car h)) (uniq (cdr h)) uniqtab h))
          ((or (fixnump h) (symbolp h)) h)
	  ((gethash h uniqatoms))
	  (t (excl::%puthash h uniqatoms h)
             h)))

