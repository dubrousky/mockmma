;;(provide 'ucons1)

;; (c) 1990, 1991, Richard J. Fateman

(in-package :mma)
;; alternative to ucons1 file
;; for non-Allegro CL.  This is a much inferior version in
;; efficiency of the unique-ification, and any CL could do
;; better. But maybe not the same way.

;;Simplest way to make the substitution would be to rename this
;; file ucons1.lisp.



(defvar *uniq-table* (make-hash-table :test #'eq))
(defvar *uniq-atom-table* (make-hash-table :test #'equal))

(defun uniq (x)
  "Return a canonical representation that is EQUAL to x,
  such that (equal x y) => (eq (uniq x) (uniq y))"
  (typecase x
    ((or fixnum symbol) x)
    (atom (or (gethash x *uniq-atom-table*)
              (setf (gethash x *uniq-atom-table*) x)))
    (cons (ucons (uniq (car x))   ; this could check in 
                                  ; *uniq-table* first...
                 (uniq (cdr x))))))

(defun ucons (x y)
  "Unique cons: (eq (ucons x y) (ucons x y)) is always true."
;; Look up the car, x, in the hash-table *uniq-table*.
;; If there a table there, then we have already hashed an
;; item with this car in the table.
;; If it is missing, create a hash-table for the purpose of
;; storing the new (cons x y) in the next step.

  (let ((car-table (or (gethash x *uniq-table*)
	               (setf (gethash x *uniq-table*)
                             (make-hash-table :test #'eq :size 10)))))

;;  At this point, car-table is a hash-table that either has
;;  (cons x y) in it, hashed under the key y, or we create 
;;  such an item and store it.

    (or (gethash y car-table)
        (setf (gethash y car-table) (cons x y)))))



(defun umapcar(f x)(cond((null x)nil)
			(t (ucons (funcall f (car x))(umapcar f (cdr x))))))

(defmacro ulist(&rest l)(cond ((null l)nil)
			      (t `(ucons ,(car l) (ulist ,@(cdr l))))))

(defun uappend(r s)(cond ((null r)s)
			 (t (ucons (car r)(uappend (cdr r) s)))))

