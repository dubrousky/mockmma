;;; -*- Mode:Common-Lisp; Package:RAT; Base:10 -*-

;;
;; Written by: Tak W. Yan, Richard J. Fateman
;; File: rat.lisp
;; Contains: rational function (in partially-factored form) arithmetic 
(provide 'rat1)

;;; (c) Copyright 1990, 1991 Richard J. Fateman, Tak W. Yan

;;; A fpe is a (possibly) factored polynomial expression implemented
;;; as a list of pairs of polynomials and exponents. For example,
;;;
;;;                             2  2         4
;;;                   12 (x + 1) (y  + y - 5)
;;;
;;; is represented as a list of three pairs, the first pair being the
;;; the number 12 and the exponent 1, the second being the 
;;; polynomial (x + 1) and the exponent 2, and the third being the
;;; polynomial (y^2 + y - 5) and the exponent 4.
;;; Currently, the first pair is always  an integer with exponent 1.

;;; Although the polynomials could have coefficients in any ring
;;; for some operations, the idea of gcd as used here assumes coefs form a
;;; unique factorization domain, and therefore it is principally useful
;;; to have integer coefficients.  (Rationals are not a UFD since
;;;  1/2*2 = 1/3*3 = 1 etc.)

;;; Getting back to our representation --
;;; There is a first pair that always looks like (integer . 1).
;;; Subsequent pairs consist of
;;; distinct polynomials with integer coefficients, and
;;; exponents which are integers >= 1.
;;; It is not required that polys  be squarefree, monic, irreducible
;;; or restricted in some other ways.  Examples of possible pairs:

;;;  ( (x^2) . 2)  ;   ( (3 x^2 - 3 x) . 1)
;;;  actually, the polynomials will be in some better form, so it is
;;; more accurate to depict these examples as 
;;;  ( #(1 0 0 1) . 2)  ;  ( #(1 0 -3 3) . 1)   where x <--> 1

;;; The polynomials in an fpe, except for intermediate forms produced
;;; during gcd computation, are maintained in lexicographically
;;; increasing order. Note that two polynomials in fpe form 
;;; may not be IDENTICAL even though they are mathematically
;;; equivalent, because of different factorings.

;;; For example,  ((1 . 1) ( (x^2+2x+1) . 1))  and ((1 . 1) ((x+1) . 2))
;;; are equivalent but not identical.  If they were added together,
;;; the result would be  (if we refrained from computing
;;; gcds)
;;;  ((1 . 1) ((2x^2+4*x+2) . 1))

;;; Another equivalent answer (more effort to compute .. we don't do
;;; this...) would get
;;;  ((2 . 1) ((x+1) . 2))

;;; On the other hand, if we were adding ((1 . 1) ((x+1) . 2)) and
;;; ((1 . 1) ((x+1) . 3)), the common factor of x+1 would be obvious
;;; and we would get  ((1 . 1) ((x+1) . 2) ((x+2) . 1))

(proclaim '(optimize (speed 3) (safety 0) (space 0) (compilation-speed 0)))

(require 'poly) ;; need macro defs
(in-package :mma)
;; export what other modules may need
#+ignore (export '(make-fpe fpe-expand fpe-coef-p fpe-coefone-p fpe-negativep
		   fpe-insert fpe-coefzero-p
		   make-rat rat-p rat make-good-rat rat-numerator 
		   rat-denominator  rat+ rat* rat^ rat/ poly2rat
		   *rat-gcd-level*))

;; default is to compute the gcd, but only between factors of
;; the numerator with factors of the denominator.

(defvar *rat-gcd-level* 'gcd) 
(defvar *expand* nil)

;; other possible settings:
;;  cdi: just find the obvious common factors by identity. That is
;;  u and v have a common divisor iff u = v.

;; cdd: common divisor by division.  That is, u and v have a
;; common divisor if one divides the other exactly.

;; current implementation uses gcd as default.


;; NOT IMPLEMENTED techniques:


;; supergcd: all gcds of factors in numerator OR denominator are
;; considered for pair-wise gcds.  That is, (x^2-1)*(x+1) --> (x+1)^2*(x-1)

;; square-free: all factors are run through a square-free factorization
;; program. (they are tagged as square-free to save redundant calculations).

;; factors: all are factored over the integers. (also tagged)

;; make-fpe: make a "normal" fpe p^e from a polynomial p, exponent e>=0
;; examples:

;;  (make-fpe poly 4) -->  (( 1 . 1) (poly 4)) ;;usual case
;;  (make-fpe 0 1)    -->  (( 0   . 1))
;;   by virtue of using fpe-insert with monomial flag = t, if
;;   make-fpe is given something like p = 3x^2y^3, e=2, it will
;;   produce ((9 . 1) ( #(x 0 1) . 4) (#(y 0 1) . 6)).
;;   {actually, you won't see x and y, but some number-encoding of them.}

(defun make-fpe (p e) 
  (cond ((coefp p) 
	 (list (cons (coef^ p e) 1)))
	(t (fpe-insert p e '((1 . 1)) t))))

(defun poly2rat (p e)
  (cond ((>= e 0)(make-rat :numerator (make-fpe p e)
			  :denominator (list '(1 . 1))))
	(t (make-good-rat (list '(1 . 1))
		      (make-fpe p (- e))))))
	
;; fpe-copy: return a copy of the fpe u

(defun fpe-copy (u) (copy-tree u))

;; fpe-expand: expand the fpe into a fully-expanded form; the result
;;             is returned as a polynomial

(defun fpe-expand (u)
  (let ((*expand* t))
  (do ((ul u (cdr ul)) (p 1))
      ((null ul) p)
      (setq p (p* p (p^ (caar ul) (cdar ul)))))))

;;; A fpe is "normal" if its first factor is an integer and it has
;;; no other integer factors. Also, the coefficient of all
;;; monomial factors should be 1. (reason: they look odd otherwise...
;;; consider 3*x^2*4*y^2  instead of 12*x^2*y^2)
;;; The factors are unique, and
;;; sorted. All coefficients in the domain
;;; are represented as c^1, including coefzero and coefone.

;; fpe-norm: normalize a fpe

;;; this program could be reprogrammed to do much less consing.

(defun fpe-norm (u &aux ctest (const 1))
  (labels
   ((fn1(ul) ; aux function to sort terms.
	(cond ((null ul) nil)
	      ((coefp (caar ul)) ; stick coefs up front
	       (setq const (coef* const
				  (coef^ (caar ul)(cdar ul))))
	       (fn1 (cdr ul)))
	      (t 
	       (fn1-insert (car ul) (fn1 (cdr ul))))))
    (fn1-insert (h ul)
		(cond ((null ul)
		       ;; Since factor (car h) is nowhere to be seen further in
		       ;; this fpe, make the pair of this factor and its power
		       ;; appear at the end of the list.
		       (cons h ul))
		      ((eq 'e (setq ctest (pcompare (car h) (caar ul))))
		       ;; We found this factor. Increment the exponent
		       (cons (cons (car h)(+ (cdr h)(cdar ul))) (cdr ul)))
		      ;; Otherwise we keep looking for the factor.
		      ((eq 'l ctest)
		       ;; this poly is less in ordering that (caar ul),
		       ;; so place it right here.
		       (cons h ul))
		      ;; This keep searching 
		      (t 
		       (cons  (car ul)(fn1-insert h (cdr ul)))
			 ul)))
    )					; end of local fns
			  
   (setq u (fn1 u))
   (cons  (cons const 1) u)))
			 
  
(defun fpe-coef-p (u) (null(cdr u)))

(defun fpe-coefone-p (u) (and (null (cdr u)) (coefonep (caar u))))

(defun fpe-coefzero-p (u) (coefzerop (caar u)))



;; fpe-insert: insert a pair of polynomial and exponent into the fpe u.
;;             This checks to see whether the polynomial already exists in
;;             the fpe; if yes, increment the exponent; otherwise
;;             adds the pair to the fpe. This will not change u.

;; in effect, this multiplies u in fpe form, by poly^u. 
;; compare to fpe-*, which multiplies 2 polys in fpe form.
;; if monom is t, then maybe poly is a monomial. Check it
;; and insert it in pieces if appropriate.

(defun fpe-insert (poly exp u &optional (monom nil) &aux ctest)
  (labels
   ((fi1(ul)
	     ;; this routine recurses down the list of factors
	     (cond ((null ul)
		    ;; Since this factor is nowhere to be seen in
		    ;; this fpe, insert the new factor and its power
		    ;; at the end of the list.
		    (list (cons poly exp)))
		   
		   ((eq 'e (setq ctest (pcompare poly (caar ul))))
		    ;; We found this factor. Increment the exponent.
		    (cons (cons (caar ul) (+ exp (cdar ul)))(cdr ul)))
		   ;; Otherwise we keep looking for the factor.
		   ((eq 'l ctest)
		    ;; this poly is less in ordering than (caar ul),
		    ;; so place it right here.
		    (cons (cons poly exp) ul))
		   ;; This keep searching 
		   (t (cons (car ul)(fi1 (cdr ul)))))))
	(cond ((coefp poly)
	       ;; inserting an integer factor: modify the first element
	       (cond ((coefonep poly) u)
		     ((coefzerop poly) (make-fpe 0 1))
		     (t (cons (cons (coef* (caar u)
						 (coef^ poly exp))
					  1)
			      (cdr u)))))
	      ((= exp 0) u) ;;multiplying u by z^0 gives u
	      ((and monom (monomialp poly)(or (> (degree poly) 1)
					      (not (coefonep (lc poly)))))
	       ;; the poly is something like (3*x^2) ^4
	       ;; insert 81  (i.e. 3^4) into  1*(x)^8.
	       ;; should work recursively for (3*y^2*x^2)^4
	       
	       (fpe-insert (lc poly) exp (fpe-insert 
					  (vector (svref poly 0) 0 1)
					  (* (degree poly) exp) u )
			   monom))
	      
	      ;; we can, more generally, not insist on monomial,
	      ;; but only 0 x^1 term.  That is,
	      ;; (a*x^5+b*x^2) --> x^2*(a*x^3+b).  or
	      ;; (x^5+x^2)^3 --> x^6*(x^3+1)^3. etc.
	      ;; note that 0 constant term is not useful because
	      ;;  x is encoded as (vector n 0 1) and has 0 const term

	      ((and monom 
		    (not *expand*)
		    (coefzerop(constc poly))
		    (> (length (the simple-vector poly)) 3)
		    (coefzerop (svref poly 2)))
	       (do ((i 2 (1+ i)))
		   ((null (coefzerop (svref poly i)));there's a non-0
		    (fpe-insert
		     (vector (svref poly 0) 0 1)
		     (* exp (1- i))  ;; the degree of the factor
		     (fpe-insert (polyshift poly (1- i)) exp u)))
		   (declare (fixnum i))
		   ;; no do-body
		   ))
		    		    
	      (t (fi1 u)))))

(defun polyshift(p i)  ;; this divides a poly in x by x^i
  (let ((z(subseq p i)))
    (setf (svref z 0) (svref p 0)) z))


;; fpe-*  multiplies two fpe's u and v. To be canonical,
;;identical polynomials will appear only once in the result.
;; Both u and v are preserved.  No wasted conses.

(defun fpe-* (u v &aux ctest)
  (labels ((fm1(ul vl)
	    (cond ((null ul) vl)
		  ((null vl) ul)
		  ((eq 'e (setq ctest (pcompare (caar ul) (caar vl))))
		   (cons (cons (caar ul) (+ (cdar ul)(cdar vl)))
			 (fm1 (cdr ul)(cdr vl))))
		   ((eq 'l ctest)
		    ;; (caar ul) is less in ordering that (caar vl),
		    ;; so place it right here.
		    (cons (car ul) (fm1 (cdr ul) vl)))
		   ;; Otherwise (car vl) goes here
		   (t (cons (car vl)(fm1 ul (cdr vl)))))))

	(cond ((and (null (cdr u)) (coefonep (caar u))) v)    ;; u is coefone
	      ((and (null (cdr v)) (coefonep (caar v))) u)    ;; v is coefone
	      
	      (t (cons (cons (coef* (caar u)(caar v)) 1) ; mult consts.
		       (fm1 (cdr u)(cdr v)))))))

(defun fpe-^ (a n) ;;powering an fpe is "easy"
  ;; presumably n is a positive integer, although if it is some
  ;; other number, this program won't break.
  (labels((fp^1 (a)
	      (cond ((null a)nil)
		    (t (cons (cons (caar a) (* n (cdar a)))
			     (fp^1 (cdr a)))))))
       (cons (cons (expt (caar a) n) 1)
	     (fp^1 (cdr a)))))

(defun fpe-negative-p (u) (coef-negative-p (caar u)))

(defun fpe-negate (u)
  (cons (cons (coefneg (caar u))(cdar u))(cdr u)))

;;; These procedures are concerned with finding the gcd and cd of fpe's.
;;; They are independent of the implementation of fpe's.

;; fpe-gcd-cofac: 
;; returns 3 values: g= the gcd of u and v;
;;                   ubyg = u/g;
;;                   vbyg = v/g.

;; u and v are unchanged, though any of the outputs may share structure.
;; all values are fpe in normal form.

(defun fpe-gcd-cofac (u v)
  (setq u (append u nil) v (append v nil));; copy only top levels of inputs
  (let((g '((1 . 1))))	;  g= gcd = 1, initially

    (do ((i u (cdr i))) 
	;; for each polynomial in u do the following
	;; until we run off the end of u. Then return the triple 
	;; <gcd, u/gcd, v/gcd>.
	
	((null i) (values g (fpe-norm u)(fpe-norm v)))
	(if (not(coefonep (caar i)))  ;; do this only if (caar i) is not 1

	(do ((j v (cdr j)));; for each polynomial in v do the following
	    ((null j))
	    (if (not (coefonep (caar j))) ;otherwise next j
	    (let* ((up (caar i))	;  next poly in u
		   (vp (caar j))	;  next poly in v
		   (ue (cdar i))
		   (ve (cdar j)))
	      (multiple-value-bind 
	       (gp uq vq)		;gcd, up/gp, vp/gp
	       (pgcdswitch-cofac up vp)
	       (cond ((coefonep gp))	; no non-trivial divisor! just advance i,j.
		     (t
		      ;; ok, we've found a common factor gp
		      (let ((ge (min ue ve)));; gcd is really gp^ge
			;; add the factor to the ones already found.
			;; incidentally, this factor may already be
			;; in g because of some earlier discovered gcd.
			(setq g (fpe-insert gp ge g t));; g = g*gp^ge
			
			;; blot out the two factors in u and v.
			;; we may have to put some remnants at the end, though.
			;; splice in what's left of powers of up and powers
			;; of vp, if any, and then consider up/gp and vp/gp
			
			;; possible missed factorization here.. if we compute
			;; gcd of x^2-1 and (x^2*y^2-y^2)^3 we get a 
			;; co-factor of y^2.  This is a monomial. It would be
			;; better to put y^6 on the factor list, rather than
			;; (y^2)^3.  Could check in fpe-norm for monomials,
			;; but this would add to expense.

			(cond ((= ge ue)
			       (setf (car i) (cons uq ue))
			       (setq up uq))
			      (t ; that is, ge < ue
			       ;; first decrement the exponent on this factor
			       ;; to make it reflect the number of times
			       ;; we've divided out gp
			       (setf (car i)(cons gp (- ue ge)))
			       (setq up gp)
			       (if (coefonep uq) nil
				 (nconc i (list (cons uq ue))))))
			(cond ((= ge ve)
			       (setf (car j) (cons vq ve))
			       (setq vp vq))
			      (t ; that is, ge < ve
			       (setf (car j)(cons gp (- ve ge)))
			       (setq vp gp)
			       (if (coefonep vq) nil
				 (nconc j (list (cons vq ve))))))
			)))))))))))

(defun pgcdswitch-cofac(u v)
  (case *rat-gcd-level*
	(gcd 
	 ;;compute the gcd. Which algorithm depends perhaps
	 ;; on other switches in polynomial package.
	 (pgcd-cofac u v))
	(cdi
	 ;; look for identical common factors only
	 ;; equalp checks element by element in arrays
	 (if (equalp u v)(values u 1 1)(values 1 u v)))
	(cdd
	 ;; look to see if u divides v or vice versa
	 (let (r)
	   (cond ((setq r (p/-test u v)) (values v r 1))
		 ((setq r (p/-test v u)) (values u 1 r))
		 (t (values 1 u v)))))
	   
	;; put other choices here
	(t ; use gcd as default
	 (pgcd-cofac u v))))
	 

;;; A rat is a rational polynomial implemented as a structure
;;; consisting of two fpe's: the numerator and the denominator.

(defstruct rat numerator denominator)

;;; A "good" rat is one whose denominator is always positive.
;;; If the rat as a whole is negative, the negative sign
;;; is in the numerator.

;; make-good-rat

(defun make-good-rat (n d)
  (cond ((fpe-negative-p d)
	 (setq d (fpe-negate d))
	 (setq n (fpe-negate n))))
  (make-rat :numerator n :denominator d))

;;; The following procedures perform simple arithmetic on rats.
;;; The returned rats from these procedures will be "normal,"
;;; provided that the arguments are "normal." A rat is said to
;;; be "normal" if
;;;       1) it is in reduced form (no common factors between numerator
;;;          and denominator).
;;;       2) each polynomial in a fpe that makes up the numerator
;;;          or the denominator appears only once within that rat.
;;;       3) the fpe's are themselves normal: leading coefficient followed
;;;          by terms sorted etc.

;; rat*: non-destructively multiply two rats r1 and r2
;;       reference - W. S.  Brown's paper


(defun rat* (r1 r2) ;;  r1 * r2 = a/b * c/d
  (let ((a (rat-numerator r1))    
	(b (rat-denominator r1))  
	(c (rat-numerator r2))    
	(d (rat-denominator r2))  
	g num den)
    ;; we assume that gcd(a,b)=1, and also that gcd(c,d)=1.
    ;; This may not be, strictly speaking, true, depending on *rat-gcd-level*.
    (if (or (fpe-coefzero-p a)
	    (fpe-coefzero-p c))
	    (return-from rat* (poly2rat 0 1)))
    ;; First, if a and c have any factors in common,
    ;; set them aside, because if g is a factor of a, then gcd(g,b)
    ;; is predictably 1, so no need to compute it.  
    ;; We could set aside all common factors regardless of multiplicity
    ;; as an additional optimization. (Tak -- this is what you were
    ;; doing, I guess).  An alternative would be to save all poly gcd
    ;; results in an eq-hash table..what do you think?  We'd have
    ;; to be careful not to make equal but not-eq polynomials... RJF
    
    (multiple-value-setq (num  a c) (fpe-gcd-cofac a c))
    ;; Ditto for b and d
    (multiple-value-setq (den  b d) (fpe-gcd-cofac b d))
    ;; we can conclude that gcd(num,den)=1 by construction, and
    ;; that with these new values, r1*r2 = (num^2*a*c)/(den^2*b*d),
    ;; subject, however, to more gcd removal. Next,
    ;; remove the common factors from a and d,  then from b and c.
    (multiple-value-setq (g a d)(fpe-gcd-cofac a d))
    (multiple-value-setq (g b c)(fpe-gcd-cofac b c))
    ;; put back the factors that were removed
    (setq a (fpe-* a (fpe-^ num 2)))
    (setq b (fpe-* b (fpe-^ den 2)))
    ;; finally put the pieces together
    (make-good-rat  (fpe-* a c) (fpe-* b d))))

;; division. almost same as *.  
(defun rat/ (r1 r2) ;;  r1 * r2 = a/b  / d/c
  (let ((a (rat-numerator r1))    
	(b (rat-denominator r1))  
	(d (rat-numerator r2))      ;; note change from rat*
	(c (rat-denominator r2))    ;;  ditto
	g num den)
    (if (fpe-coefzero-p a) (return-from rat/ (poly2rat 0 1)))
    (if (fpe-coefzero-p d) (error "Rational division by zero"))

    (multiple-value-setq (num  a c) (fpe-gcd-cofac a c))
    (multiple-value-setq (den  b d) (fpe-gcd-cofac b d))

    (multiple-value-setq (g a d)(fpe-gcd-cofac a d))
    (multiple-value-setq (g b c)(fpe-gcd-cofac b c))

    (setq a (fpe-* a (fpe-^ num 2)))
    (setq b (fpe-* b (fpe-^ den 2)))

    (make-good-rat  (fpe-* a c) (fpe-* b d))))


;; rat+: non-destructively add two rats r1 and r2

(defun rat+ (r1 r2)
  (let ((a (rat-numerator r1))
	(b (rat-denominator r1))
	(c (rat-numerator r2))   ;; want to perform
	(d (rat-denominator r2)) ;;  a/b + c/d
	(n (make-fpe (coefone) 1))
	num den	g)
    (if (fpe-coefzero-p a) (return-from rat+ r2))
    (if (fpe-coefzero-p c) (return-from rat+ r1))
    
    ;; extract common factors from a and b, also b and d.
    (multiple-value-setq
     (num a c)(fpe-gcd-cofac a c))
    (multiple-value-setq
     (den b d)(fpe-gcd-cofac b d))
    
    ;; now r1+r2 = (num/den)* (a/b+c/d) and gcd(b,d)=1.
    ;; n=ad+bc
    (setq n (pnorm(p+ (fpe-expand (fpe-* a d));  n is a polynomial
		(fpe-expand (fpe-* b c)))))
    (if (coefzerop n) (return-from rat+ (make-rat :numerator '((0 . 1))
						  :denominator '((1 . 1)))))
    (setq n (make-fpe n 1)) ; now n is an fpe.

    (setq den(fpe-* den (fpe-* b d))) ;; set denom to bd * den
        
    ;; remove common factors between  ad+bc and bd*den
    (multiple-value-setq (g n den)(fpe-gcd-cofac n den))
    (setq num (fpe-* num n)); set num to num *(ad + bc)
    (make-good-rat num den)))

;; rat^: raise r to the power e

(defun rat^ (r e)
	 (cond ((= e 0) (make-rat :numerator '((1 . 1))
				  :denominator '((1 . 1))))
	       ((> e 0)
		(make-rat :numerator (fpe-^ (rat-numerator r) e)
			  :denominator (fpe-^ (rat-denominator r) e)))
	       (t (if (fpe-coefzero-p (rat-numerator r))
		      (error "Rational division by zero"))
		  (make-good-rat ;check sign of denom..
		    (fpe-^ (rat-denominator r) (- e))
		    (fpe-^ (rat-numerator r) (- e))))))


