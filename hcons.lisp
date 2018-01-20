
;; -*- mode: common-lisp; package: hcons; -*-
;;
;; patch to hash.cl to provide hcons and hlist
;;
;;				-[Mon Jan 29 22:30:51 1990 by layer]-
;; 
;; copyright (c) 1985, 1986 Franz Inc, Alameda, Ca. 
;; copyright (c) 1986-1990 Franz Inc, Berkeley, Ca.
;;
;; The software, data and information contained herein are proprietary
;; to, and comprise valuable trade secrets of, Franz, Inc.  They are
;; given in confidence by Franz, Inc. pursuant to a written license
;; agreement, and stored only in accordance with the terms of such license.
;;
;; Restricted Rights Legend
;; ------------------------
;; Use, duplication, and disclosure by the Government are subject to
;; restrictions of Restricted Rights for Commercial Software developed
;; at private expense as specified in DOD FAR 52.227-7013 (c) (1) (ii).

(in-package :excl)
;;(provide 'hcons)
(export '(hcons hlist maphcons))
(export 'maphcons)

;; macros needed to compile the hcons function

(eval-when (compile)

(defmacro ha-check (x)
   `(cond ((not (hash-table-p ,x))
	   (error "~s is not a hashtable " ,x))))

(defmacro quick-integer-rem (x y)
   `(multiple-value-bind (.a. .b.)
	  (comp::.primcall 'sys::integer-divide ,x ,y)
       (declare (ignore .a.))
       .b.))
(defmacro svector-length (sv)
   `(if* (svectorp ,sv)
       then (sv_size ,sv)
       else  (error "Expected a simple vector, got ~s " ,sv)))

(defmacro hash-table-table-macro (h)
   (if* (symbolp h)
      then `(progn (ha-check ,h) (ha_table ,h))
      else (let ((v (gensym)))
	      `(let ((,v ,h))
		  (ha-check ,v)
		  (ha_table ,v)))))

(defmacro eq-hash (object)
  "Gives us a hashing of an object such that (eq a b) implies
   (= (eq-hash a) (eq-hash b))"
  `(the fixnum (pointer-to-positive-fixnum ,object)))

(defmacro eql-hash (object)
  "Gives us a hashing of an object such that (eql a b) implies
   (= (eql-hash a) (eql-hash b))"
  `(if* (complexp ,object)
      then (abs (truncate (realpart ,object)))
    elseif (numberp ,object)
       then (abs (truncate ,object))
       else (pointer-to-positive-fixnum ,object)))

(defmacro equal-hash (object)
  "Gives us a hashing of an object such that (equal a b) implies
   (= (equal-hash a) (equal-hash b))"
  `(the fixnum (sxhash ,object)))

(defmacro dual-key-hash (hash-func key1 key2)
  `(logxor (,hash-func ,key1) (,hash-func ,key2)))

(defmacro grow-size (table)
  "Returns a fixnum for the next size of a growing hash-table."
  `(let ((rehash-size (ha_rehash-size ,table)))
     (almost-primify
	(if* (floatp rehash-size)
	   then (ceiling (* rehash-size (ha_buckets ,table)))
	   else (+ rehash-size (ha_buckets ,table))))))

(defmacro grow-rehash-threshold (table new-length)
  table
  new-length)


;;; Hashop dispatches on the kind of hash table we've got, rehashes if
;;; necessary, and binds Vector to the hash vector, Index to the index
;;; into that vector that the Key points to, and Size to the size of the
;;; hash vector.  The body is unrolled three times, replacing *test-op*
;;; with eq, eql, and equal to get the different pieces.

(defmacro hashop (&rest body)
    `(xhashop (:eq-hash (eq-hash key)
	       :eql-hash (eql-hash key)
	       :equal-hash (equal-hash key)
	       :rehash rehash)
	,@body))


(defmacro xhashop ((&key eq-hash eql-hash equal-hash rehash) &rest body)
   `(let* ((vector (hash-table-table-macro hash-table)) ; does ha-check
	  (size (svector-length vector))
	  (index 0))
     (declare (simple-vector vector))
     (declare (fixnum size index))
     (case (ha_kind hash-table)
       (equal
	(excl::without-interrupts
	    (setq index (quick-integer-rem ,equal-hash size))
	    ,@(subst 'equal '*test-op* body)))
       (eq
	(eq-rehash-if-needed ,rehash)
	(excl::without-interrupts
	    (setq index (quick-integer-rem ,eq-hash size))
	    ,@(subst 'eq '*test-op* body)))
       (eql
	(eq-rehash-if-needed ,rehash)
	(excl::without-interrupts
	    (setq index (quick-integer-rem ,eql-hash size))
	    ,@(subst 'eql '*test-op* body))))))

(defmacro eq-rehash-if-needed (rehash)
    `(cond ((ha_rehashp hash-table)
	    (,rehash hash-table vector size)
	    (setq vector (ha_table hash-table)))
	   ((> (ha_number-entries hash-table)
	       (ha_rehash-threshold hash-table))
	    (,rehash hash-table vector (grow-size hash-table))
	    (setq vector (ha_table hash-table))
	    (setq size (svector-length vector)))))

(defmacro rehash-if-needed (rehash)
  `(let ((size (sv_size vector)))
     (declare (fixnum size))
     (cond ((ha_rehashp hash-table)
	    (,rehash hash-table vector size)
	    (setq vector (ha_table hash-table))
	    (setq size (sv_size vector)))
	   ((> (ha_number-entries hash-table)
	       (ha_rehash-threshold hash-table))
	    (,rehash hash-table vector (grow-size hash-table))
	    (setq vector (ha_table hash-table))
	    (setq size (sv_size vector))))))


(defmacro hash-set (vector key.value hashkey hashfunc length)
  "Used for rehashing.  Enters the value for the key into the vector
   by hashing.  Never grows the vector.  Assumes the key is not yet
   entered."
  `(let ((index (quick-integer-rem
		   (funcall ,hashfunc ,hashkey)
		   (the fixnum ,length))))
     (declare (fixnum index))
     (setf (svref (the simple-vector ,vector) index)
	   (cons ,key.value
		 (svref (the simple-vector ,vector) index)))))
)

(defun hcons (kcar kcdr hash-table &optional kcons)
  "Returns a unique cons cell (modulo hash-table) with car and cdr
   specified by kcar and kcdr.  If there is already a cons cell in
   hash-table with car and cdr equal to kcar and kcdr (modulo the
   :test function of hash-table), that cell is returned.
   Otherwise a new cell is created, stored in the table, and returned.
   *** Note that gethash, remhash, etc cannot be applied to a ***
   *** hash-table used for hcons                              ***"
   (xhashop
      (:eq-hash (dual-key-hash eq-hash kcar kcdr)
       :eql-hash (dual-key-hash eql-hash kcar kcdr)
       :equal-hash (dual-key-hash equal-hash kcar kcdr)
       :rehash rehash-hcons)
     (let ((bucketlist (aref vector index)))
       (do ((bucket bucketlist (cdr bucket)))
	   ((null bucket)
	      (let ((newcons (if (and (consp kcons)
				      (eq kcar (car kcons))
				      (eq kcdr (cdr kcons)))
				 kcons
				 (cons kcar kcdr))))
		(setf (aref vector index) (cons newcons bucketlist))
		(setf (ha_number-entries hash-table)
		      (+ 1 (ha_number-entries hash-table)))
		(rehash-if-needed rehash-hcons)
		newcons))
	   (when (and (*test-op* kcar (caar bucket))
		      (*test-op* kcdr (cdar bucket)))
		 (return-from hcons (car bucket)))))))


(defun rehash-hcons (structure hash-vector new-length)
  (declare (simple-vector hash-vector))
  (declare (fixnum new-length))
  "Rehashes an hcons hash table and replaces the table entry in the structure if
   someone hasn't done so already.  New vector is of new-length."
  ;; (print "hcons rehashing to size ") (print new-length) (terpri)
  (loop
    (setf (ha_rehashp structure) nil)
    (do ((new-vector (make-array new-length))
         (i 0 (1+ i))
         (size (ha_buckets structure))
         (hashing-function
	    (case (ha_kind structure)
		(eq #'(lambda (x) (dual-key-hash eq-hash (car x) (cdr x))))
		(eql #'(lambda (x) (dual-key-hash eql-hash (car x) (cdr x))))
		(equal #'(lambda (x)
			   (dual-key-hash equal-hash (car x) (cdr x)))))))
        ((eql i size)
         (cond ((eq hash-vector (ha_table structure))
	        (setf (ha_table structure) new-vector)
	        (cond ((> new-length size)
		       (setf (ha_rehash-threshold structure)
			     (grow-rehash-threshold structure new-length))
		       (setf (ha_buckets structure) new-length)))))
         )
      (declare (fixnum i size))
      (do ((bucket (aref hash-vector i) (cdr bucket)))
	  ((null bucket))
        (hash-set new-vector (car bucket) (car bucket)
		hashing-function new-length)))
    (if* (null (ha_rehashp structure))
       then (return))
    (setq hash-vector (ha_table structure))))


(defun maphcons (function hash-table)
  "For each entry in hash-table, calls function on the entry; returns t."
  (let ((vector (hash-table-table-macro hash-table))) ; does ha-check
    (declare (simple-vector vector))
    (rehash-if-needed rehash-hcons)
    (do ((i 0 (1+ i))
	 (size (ha_buckets hash-table)))
	((eql i size))
      (declare (fixnum i size))
      (do ((bucket (aref vector i) (cdr bucket)))
	  ((null bucket))
	(funcall function (car bucket))))))

;;;Bob Rorschach           INTERNET: rfr@franz.com
;;;Franz Inc.              UUCP:     uunet!franz!rfr

