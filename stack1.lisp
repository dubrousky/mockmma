;; Stack handling routines for lmath
;; (c) Copyright 1990, Richard J. Fateman

(provide 'stack1)

;; Two parallel stacks for names (vars) and values (vals)
;; are maintained. There's only one instance of this stack, reducing
;; benefit of using defstruct.
(in-package :mma )
;;(export '(stack make-stack spush spushframe spopframe spop sfind schange
;;		stack-ptr stack-frameptr sfindd stackprinter env))

(defstruct (stack (:print-function stackprinter))
  (size 100 :type fixnum) ;if no size is specified, how about 100?
  ;; ptr points to top of stack.  0<=ptr<size : the index in which to
  ;; store at the next "push".
  (ptr 0 :type fixnum) 
  ;;frameptr points to the bottom of current call-frame 
  ;; a pair that looks like  <name of function> <next lower frameptr>
  ;; -1 <= frameptr < ptr
  (frameptr -1 :type fixnum) 
  (vars (make-array size))
  (vals (make-array size)))

(defun spush(s var val)
  (setf (aref (stack-vars s) (stack-ptr s)) var)
  (setf (aref (stack-vals s) (stack-ptr s)) val)
  ;;could check for overflow here
  (incf (stack-ptr s))
  s)

;; establish a new call frame

(defun spushframe(s &optional (name 'anony))
  (spush s name (stack-frameptr s)) ;; push old frame pointer on stack
  ;; set frameptr to current top-of-stack.
  (setf (stack-frameptr s) (1-(stack-ptr s)))
  s)

;; Popframe.  Reset stack to remove all items from this "call"

(defun spopframe(s)
  ;; could check that s is a stack and is non-empty, but we don't
  (setf (stack-ptr s)(stack-frameptr s))
  (setf (stack-frameptr s)(aref (stack-vals s) (stack-ptr s)))
    s)


;; this version of pop returns 2 values  (variable, value) of the
;; item that was on the top of the stack, but has been removed.
;; If an additional argument n > 1 is supplied,  n-1 extra items
;; are removed, and then one is popped off.

(defun spop(s &optional (n 1))
  ;; could check that s is a stack and is non-empty, but we don't
 (let ((p  (decf (stack-ptr s) n)))
   (values (aref (stack-vars s)p)
	   (aref (stack-vals s)p))))

;; to find an entry, use sfind.  A multiple value is returned.
;; first value is value found, if any
;; second value is nil, if no value was found, otherwise, the index

(defun sfind(s var)
  (let ((loc (position var (stack-vars s)
		       :start (1+(stack-frameptr s)) :end (stack-ptr s))))
    (if loc (values (aref (stack-vals s) loc) loc) ; found: 2nd val is index
      (values var loc)  ;;2nd value will be nil, first will be var itself
      )))

;; to change an entry, use schange -- change the binding of var

(defun schange (s var val)
  (let ((loc (position var (stack-vars s)
		       :start (1+ (stack-frameptr s)) :end (stack-ptr s))))
    (if loc (setf (aref (stack-vals s) loc) val)
      (spush s var val) ;; arguable alternative: push the value
      )))

;; a variation similar to gethash default usage. If you don't
;; find the variable on the stack, return the default value.

(defun sfindd(s var default)
  (let ((loc (position var (stack-vars s)
		       :from-end 't :end (stack-ptr s))))
    (if loc (aref (stack-vals s)loc) default)))

(defun stackprinter(a stream pl)
  (let ((fp (1- (stack-frameptr a)))
	(sp (stack-ptr a)))
  ;;pl, print-level, is not used			
  ;; we don't print the size of the stack. Should we?
    (if (= 0 sp) (format stream "Empty Stack~%")  
      
    (do((i (1- sp) (1- i)))
     ((< i 0) nil)

     (cond((eql i (1+ fp))
	   (format stream "** bottom of frame ~s **~%" (aref (stack-vars a) i))
	   (setq fp (1- (aref (stack-vals a) i))))
	  (t  (format stream 
	     "~s ~5t-> ~s~%"  ;;two column format separated by tab to col 5
	     (aref (stack-vars a) i)
	     (aref (stack-vals a) i)))
)))))


(defvar env (make-stack))
(spushframe env 'bot)



