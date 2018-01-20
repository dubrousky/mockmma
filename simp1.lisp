;;; -*- Mode:Common-Lisp; Package:simp; Base:10 -*-
;;
;; Written by: Tak W. Yan
;; modified by Richard Fateman

;; Contains: procedures that convert between lisp prefix form 
;;           and representation of rat's and also the simplifier itself

;;; (c) Copyright 1990 Richard J. Fateman, Tak Yan

;;; Basically three functions are provided.
;;;     into-rat:  take an expression parsed by parser, simplify it, and
;;;                represent it as a "rat"
;;;     outof-rat: take a rat and translate it back to Mathematica (tm)-like
;;;                language
;;;     simp:      simplify an expression by converting it back and forth

(provide 'simp1)

(proclaim '(optimize (speed 3) (safety 0) (space 0) (compilation-speed 0)))

;; export what needs to be exported
;;(require "ucons1")
;;(require "poly")
;;(require "rat1")
;;(require "mma") ;; need the symbols like Plus
(in-package :mma)
;; don't export. Make everyone do (in-package :mma).
#+ignore (export '(into-rat outof-rat simp varcount vartab revtab reptab 
		   fintol intol look-up-var disreptab))


(defvar varcount 0)
(defvar vartab (make-hash-table :test #'equal)) ;; map from kernels to integers
(defvar revtab (make-hash-table :test #'eql)) ;; map from integers to kernels
;; reptab should use eq, if we believe that expressions will be
;; "unique" coming from the parser or other transformation programs.
;; (see what happens coming out of "outof-rat" for example.)
;;
(defvar reptab (make-hash-table :test #'eq)) ;; map from expressions to rats
(defvar disreptab (make-hash-table :test #'eq)) ;; map from rats to expressions

;; look-up-var: look up a variable in the hash-table; if exists,
;;    	        return the value of it; otherwise, increment varcount
;;              and add variable to hash-table

(defun look-up-var (x)
  (cond ((gethash x vartab))
	(t (setf (gethash (setq varcount (1+ varcount)) revtab) x)
	   (setf (gethash x vartab) varcount))))

;;; into the rat representation

;; into-rat: represent as a rat

(defun into-rat (x)
  (cond ((integerp x) (coef2rat x))
	((rationalp x) (make-rat :numerator `((,(numerator x) . 1))
				 :denominator `((,(denominator x) . 1))))
	((typep x 'rat) x)
	((gethash x reptab))       ; see if remembered
	((setf (gethash x reptab) (into-rat-1 x)))))

;; into-rat-1: actually do the work

(defun into-rat-1 (x)
  (let (h)
    (cond ((symbolp x) (var2rat x))
	  ((atom (setq h (car x)))
	   (cond ((eq h 'Integer) (coef2rat (cadr x)))
		 ((eq h 'Times)
		  (reduce-rat #'rat* (into-rat (cadr x)) (cddr x)))
		 ((eq h 'Plus)
		  (reduce-rat #'rat+ (into-rat (cadr x)) (cddr x)))
		 ((eq h 'Power) (into-rat-2 x))
		 ;; out of place here
#+ignore	 ((eq h 'SetLevel)
		  (cond ((eq (cadr x) 'gcd)
			 (setq *rat-gcd-level* 'gcd))
			((eq (cadr x) 'cd)
			 (setq *rat-gcd-level* 'cd)))
		  (var2rat x))

#+ignore	 ((eq h 'SquareFree) 
		  (make-rat :numerator
			(fpe-squarefree (rat-numerator (into-rat (cadr x)))
						(look-up-var (caddr x)))
				  :denominator (list (cons 1 1))))
		 (t (var2rat (umapcar #'simp x)))))
	  (t (var2rat (umapcar #'simp x))))))

;; into-rat-2: handle the case of powering

(defun into-rat-2 (x)
  (let* ((exp (into-rat (caddr x)))
	 (exp-n (rat-numerator exp))
	 (exp-d (rat-denominator exp)))
    (cond ((and (fpe-coef-p exp-n) (fpe-coef-p exp-d))
	   (cond ((fpe-coefone-p exp-d) (rat^ (into-rat (cadr x))
					      (fpe-expand exp-n)))
		 (t (rat^ (var2rat (ulist 'Power
					  (simp (cadr x))
					  (ulist 'Times 1
						 (ulist 
						  'Power
						  (fpe-expand exp-d) -1))))
			  (fpe-expand exp-n)))))
	  (t (var2rat (ulist 'Power (simp (cadr x)) (outof-rat exp)))))))

;; var2rat: convert a variable into a rat

(defun var2rat (x)
  (make-rat :numerator (make-fpe (vector (look-up-var x) 0 1) 1)
	    :denominator (make-fpe (coefone) 1)))

;; coef2rat: convert a coef into a rat

(defun coef2rat (x)
  (make-rat :numerator (make-fpe x 1)
	    :denominator (make-fpe (coefone) 1)))

;; reduce-rat: apply fn to r and the result of applying fn recursively to
;;             the terms in l

(defun reduce-rat (fn r l)
  (cond ((null l) r)
	(t (funcall fn r (reduce-rat fn (into-rat (car l)) (cdr l))))))

;;; out of the rat representation

;; outof-rat: translate back to Mathematica (tm)-like lists

(defun outof-rat (r)
  (cond ((gethash r disreptab))
	((setf (gethash r disreptab)
  (let ((n (fintol (rat-numerator r)))
	(d (fintol (rat-denominator r))))    
    ;; here we remember the output simplified form
    ;; so that if it is fed back in, you get exactly the same rat rep.
    ;; In fact, by re-collecting terms in a different order, it might
    ;; sometimes change. E.g. (x^2+2x) results from (x+1)^2-1,
    ;; but if you type it in, you'll get x*(x+2)!
    (let ((ans (outof-rat-1 n d)))
      (setf (gethash ans reptab) r) ;; controversy here
      ans))))))


;; outof-rat-1: take 2 fpe's, n and d, and translate 
;;              into list form; n is numerator and d is denominator;


(defun outof-rat-1 (n d)
  (cond ((equal 1 d) n) ;; e.g. 3
	((equal 1 n) 
	 (cond ((and (consp d)(eq (car d) 'Power))
		(cond ((numberp (caddr d));; e.g. y^(-4)
		       (ulist 'Power (cadr d)(- (caddr d))))
		      (t ;; e.g. y^(-x)
		       (ulist 'Power (cadr d)(ulist 'Times -1 (caddr d))))))
	       ((numberp d)(expt d -1)) ;; 1/3
	       (t (ulist 'Power d -1)))) ;; x^-1
	((and (numberp n)(numberp d)) (/ n d)) ;; e.g. 1/2
	((numberp d)(ulist 'Times (outof-rat-1 1 d) n)) ;; e.g. 1/30(x^2+1)
	(t (ulist 'Times n 
		  (outof-rat-1 1 d)))))

;; fintol: convert a fpe into list form; the fpe must be normal,
 
(defun fintol (f)
  (let ((c (caar f))); constant term
    (do ((j (cdr f)(cdr j))
	 (lis nil))
	((null j)
	 (cond ((null lis) c)
	       ((and (coefonep c)(null(cdr lis)))
		(car lis))
	       (t (cond ((coefonep c) (ucons 'Times (uniq(nreverse lis))))
			(t (ucons 'Times(ucons c (uniq (nreverse lis)))))))))
	;; the loop body:
	(setq lis (cons (fintol2 (caar j)(cdar j)) lis)))))



;; fintol2: break a pair in a fpe into list form

(defun fintol2 (p e)
  (cond ((eq e 1) (intol p))
	(t (ulist 'Power (intol p) e))))

;; intol: convert a polynomial in vector form into list form

(defun intol (p)
       (cond ((vectorp p)
	      ;; look up what the kernel is from revtab
	      (intol+ (intol2 p (gethash (svref p 0) revtab
					 ;;in case (svref p 0) is not 
					 ;; in hashtable, use it literally
					 (svref p 0)))))
	     (t p)))

;; intol2: help intol

(defun outof-rat-check(x)
  (cond ((rat-p x) (outof-rat x))
	(t (intol x))))

(defun intol2 (p var)
  (let (res term)
    (do ((i (1- (length p)) (1- i)))
	((= i 0) res)
	(setq term (intol* (outof-rat-check (svref p i)) (intol^ (1- i) var)) )
	(cond ((eq term 0))
	      (t (setq res (ucons term res)))))))

;; intol^: handle the case for powering

(defun intol^ (n var)
       (cond ((zerop n) 1)
	     ((equal n 1) var)
	     (t (ulist 'Power var n))))

;; intol+: handle +

(defun intol+ (p)
  (cond ((null (cdr p)) (car p))
	((IsPlus (car p)) (uappend (car p) (cdr p)))
	(t (ucons 'Plus p))))

;; intol*: handle *

(defun intol* (a b)
  (cond ((eql a 0) 0)
	((eq a 1) b)
	((eq b 1) a)
	(t (ucons 'Times 
		  (uappend (intol*chk a) (intol*chk b))))))

;; into*chk: help into*

(defun intol*chk (a)
  (if (IsTimes a) (cdr a) (ulist a)))

;; IsPlus: check if a is led by a 'Plus

(defun IsPlus (a) (and (consp a) (eq (car a) 'Plus)))

;; IsTimes: check if a is led by 'Times

(defun IsTimes (a) (and (consp a) (eq (car a) 'Times)))

;;; simplify by converting back and forth

;; simp: simplify the expression x
;; assumes that all kernels that are non-identical are algebraically
;; independent. Clearly false for e.g. Sin[x], Cos[x], E^x, E^(2*x)

(defun simp (x) (outof-rat (into-rat x)))

;; This gives a list of kernels assumed to be independent.
;; If they are NOT, then the simplification may be incomplete.
;; In general, the search for the "simplest" set of kernels is
;; difficult, and leads to (for example) the Risch structure
;; theorem, Grobner basis decompositions, solution of equations
;; in closed form algebraically or otherwise.  Don't believe me?
;; what if the kernels are Rootof[x^2-3],Rootof[y^4-9], Log[x/2],
;; Log[x], Exp[x], Integral[Exp[x],x] ....

(defun Kernelsin(x)(cons 'List
			  (mapcar #'(lambda(x)(gethash x revtab))
			    (collectvars (into-rat x)))))





