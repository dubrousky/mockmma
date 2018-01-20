;;; -*- Mode:Common-Lisp; Package:mma; Base:10 -*-
;;
;; Written by: Richard J. Fateman
;; File: poly.lisp
;; Contains: vector-based polynomial recursive representation arithmetic

;;; (c) Copyright 1990 Richard J. Fateman, Peter Klier, Peter Norvig, Tak Yan

;;;(provide 'poly)
;;; A polynomial is either a number (integer -- for now)
;;; or a vector of length d+2 where d>0 is the degree of S
;;; S=#(mainvar coeff coeff ... coeff).
;;;              ^                ^
;;;              |                |-coeff of mainvar^d : non-zero
;;;              |-coeff of mainvar^0  
;;; e.g.
;;; 4 + 5*x + x^2  = #(mainvar 4 5 1), where mainvar is an integer
;;; representing x in the system.

;;; Coeffs can be polynomials in other variables.

;;; Note: this is not the shortest code, but it should not be much slower
;;; than the fastest code absolutely necessary to get the job done.

;;(provide 'vector-math)
(declaim (optimize (speed 3) (safety 0) (space 0) (compilation-speed 0)))
(declaim (inline svref = eql make-array))

(in-package :mma)

;; don't export: make everyone else do (in-package :mma).
#+ignore (export '(coefp coef+ coef- coef* coef/ coef^
                coefzero coefzerop coefzeropfun coef-negative-p
                coefone coefonep coefrem coefneg mainvar
                samevar var> degree lc  monomialp))

#+ignore (export '(p+ p- p* p/ pnegate pnorm p^ p/-and-barf p/-test prem pgcdsr
             pgcd-cofac pcontentsr pcontentxsr ppartsr pcompare))
;; coefp: is defined to return true (non-nil, anyway)
;;        for an element of the coefficient domain. By default, we
;;        use integers.  This could be changed in concert with other
;;        programs to support other domains (see coef+).
;;        Coefp is usually called to see if its argument is
;;        (recursively) a polynomial in yet more variables, or is the
;;        ``base case'' of a polynomial which is, in fact, a coefficient.
;;        By defining it as "numberp" rather than "integerp" it works more
;;        smoothly (no change needed for rationals or floats).

(defmacro coefp (x) `(numberp ,x))

;; mainvar:  extract the main variable from a polynomial

(defmacro mainvar (x) `(svref (the simple-vector ,x) 0))

;; samevar:  see if two polynomials have the same main variable

(defmacro samevar (x y) `(eq (mainvar ,x) (mainvar ,y)))

;; degree: extract the degree from a polynomial (degree in main variable)

(defmacro degree (x) `(- (length (the simple-vector ,x)) 2))

;; lc:  extract the leading coefficient of a polynomial

(defmacro lc (x) `(svref ,x (1- (length ,x))))

;; constc: extract the constant coefficient of a polynomial
;; with respect to its main variable

(defmacro constc(x) `(svref ,x 1))

;; monomialp: check if v is a monomial (like x, or 3x^2)

(defun monomialp (v)
  (declare (simple-vector v))
  (= (length v) (1+ (position-if-not #'(lambda(x) (equal x 0)) v :start 1))))

;; var>:  an ordering predicate on variables to determine which
;;        is more "main". We could use strings or symbols for the variables
;;        instead of numbers, and use alphabetic ordering for var>.
;;        This seems simpler overall, since the variables might be more
;;        complicated in applications (e.g. (cos z)).
;;        Some easy encoding of names to numbers can be used (e.g. the
;;        first symbol mentioned is 1, and then count up.)

(defmacro var> (x y) `(> ,x ,y))

;;  The next set of macro definitions supplies the arithmetic
;;  for coefficients.  In general, any domain that can support
;;  the coefficient operations below is fair game for the package.
;;  More advanced operations may place additional requirements
;;  on the coefficient domain (E.g. they form an algebraic Ring or Field).

;;  Add/subtract/multiply two coefficients, etc.

(defmacro coef+ (x y) `(+ ,x ,y))
(defmacro coef- (x y) `(- ,x ,y))
(defmacro coef* (x y) `(* ,x ,y))
(defmacro coef> (x y) `(> ,x ,y))

;; Dividing two coefficients is not so obvious.  If the coefficient
;; domain is the common-lisp rational numbers (an algebraic field) and
;; if y is non-zero, then (/ x y) is also in the same field.  If the
;; coefficient domain is the integers, then division may throw the
;; computation out of that domain.  (/ 1 2) is not an integer.
;; Here we assume the person or program using coef/ is knowledgeable
;; about its uses.  Actually, we go further than that here. We
;; don't use coef/ in this file at all.  In the places we use
;; division (in p/ ) we make the (perhaps unwarranted) assumption
;; that exact division over the integers is required. See p/.

(defmacro coef/ (x y) `(/ ,x ,y))

;;  coef^ computer a coefficient to an integer power n

(defmacro coef^ (x n) `(expt ,x ,n))

;; some extra pieces just in case they're needed: remainder, negation, and
;; absolute value

(defmacro coefrem (x y) `(mod ,x ,y))
(defun coefneg (x) (- x))
(defun coefabs (x) (abs x))

;; Tests for zero and unity are important, as are constructors

(defmacro coefzero () 0)               ;;  zero in the coefficient domain
(defmacro coefone  () 1)               ;; unity in the coefficient domain
(defmacro coefzerop (x) `(eql 0 ,x))
(defmacro coefonep (x) `(eql 1 ,x))
(defmacro coef-negative-p (x) `(and (coefp ,x) (< ,x 0)))
(defun coefzerofunp (x) (eql 0 x))    ;;  to funcall, we need a function

;;; This product function preserves both arguments and returns the product
;;; of two polynomials.

;; p*: return the product of v1*v2

(defun p* (v1 v2)
  (declare (inline make-array))
  (cond ((coefp v1) (p*cv v1 v2)) ;; call function to multiply coef*poly
	((coefp v2) (p*cv v2 v1))
	((samevar v1 v2)
	 ;; two polynomials in the same main variable
	 ;; do  n X m multiplications
	 (let (ilim jlim index ival res)
	   (declare (fixnum ilim jlim index i j))
	   (setq ilim (1- (length v1)) jlim (1- (length v2)))
	   (setq res (make-array (+ ilim jlim) :initial-element 0))
	   (setf (svref res 0) (mainvar v1))
	   (do ((i 1 (1+ i)))
	       ((> i ilim) res)
	       (setq ival (svref v1 i))
	       (unless (coefzerop ival)	;; shortcut 0 * anything = 0
		       (do ((j 1 (1+ j)))
			   ((> j jlim))
			   (declare (fixnum i j))
			   (setq index (+ i j -1))
			   (setf (svref res index)
				 (p+vv-zero-check (svref res index)
						(p* ival (svref v2 j)))))))))
	((var> (mainvar v1) (mainvar v2)) (p*cv v2 v1))
	(t (p*cv v1 v2))))

;; p*cv: coefficient times polynomial vector;
;;       preserves both inputs and although the result can
;;       share substructure with the vector v, the top-level
;;       vector is new. (true recursively)

(defun p*cv (c v)
  (declare (inline make-array))
  (cond
   ((coefp v) (coef* c v))
   ((coefzerop c) (coefzero)) ;; 0 * anything is 0	
   ((coefonep c) v) ;; 1 * v = v. 
   ;; run down the length of the vector, multiplying.
   ;; p* is not destructive of its arguments either.
   (t (let* ((v v) (len (length (the simple-vector v))) u)
      (declare (simple-vector v u) (fixnum len) (inline svref setf mainvar))
      (setq u (make-array len))
      (setf (mainvar u) (mainvar v))
      (do
       ((i (1- len) (1- i)))
       ((= i 0) u)
       (declare (fixnum i))
       (setf (svref u i) (p* c (svref v i))))))))

;; pnegate: negate p
;; there are trivial other ways of doing this
;; like multiplying by -1. This takes less time
;; and space.

(defun pnegate(v)
  (declare (simple-vector v))
  (if (coefp v)
      (coefneg v)
      (let ((u (make-array (length v))))
        (declare (simple-vector u))
        (setf (svref u 0)(svref v 0))
        (do ((i (1-(length v)) (1- i)))
            ((= i 0) u)  ;; no need to call pnorm since -u is normalized
            (declare (fixnum i))
            (setf (svref u i)(pnegate (svref v i)))))))

;; p+: sum two polynomials as vectors, non-destructively

(defun p+ (v1 v2)
  (cond ((coefp v1) (p+cv v1 v2))
        ((coefp v2) (p+cv v2 v1)) ;; reverse args
        ((samevar v1 v2) ;; same main var
	 (let
	   ((lv1 (length (the simple-vector v1)))
	    (lv2 (length (the simple-vector v2)))
	    (v1 v1) (v2 v2)) ;; not redundant
	   (declare (simple-vector v1 v2) (fixnum lv1 lv2))
	   (cond ((> lv1 lv2)
		  (p+into v2 v1 lv2 lv1)) ;; v1 is longer
		 (t (p+into v1 v2 lv1 lv2)))))
	((var> (mainvar v1) (mainvar v2)) (p+cv v2 v1))
	(t (p+cv v1 v2))))

;; p-: compute difference of two polynomials as vectors, non-destructively
;; this could be done trivially by u+(-v) but this is
;; faster and uses less space.

(defun p- (v1 v2)
  (declare (simple-vector v1 v2))
  (cond ((coefp v1) (p+cv v1 (pnegate v2)))
        ((coefp v2) (p+cv (pnegate v2) v1))
        ((samevar v1 v2);; same main var
         ;;; aw, could do this in a pickier fashion...
         (p+ v1 (pnegate v2)))
        ((var> (mainvar v1) (mainvar v2))(p+cv (pnegate v2) v1))
        (t (p+cv v1 (pnegate v2)))))

;; p+cv: add coeff to vector, non-destructively

(defun p+cv(c v)
  (if (coefp v)
      (coef+ c v)
      (let ((v (copy-seq v)))
	(declare (simple-vector v))
	(setf (svref v 1) (p+ c (svref v 1)))
	v)))

;; p+into: add terms from one polynomial v1 into another

(defun p+into (v1 v2 shorter longer)
  (let (res)
    (declare (fixnum shorter longer)
	     (simple-vector v1 v2 res)
	     (inline p+vv-zero-check))
    (setq res (make-array longer))
    (setf (svref res 0) (mainvar v2))
    (do ((i 1 (1+ i)))
	((= i shorter))	
	(declare (fixnum i)) 
	(setf (svref res i) (p+vv-zero-check (svref v1 i) (svref v2 i))))
    (do ((i shorter (1+ i)))
	((= i longer) (pnorm res))
	(declare (fixnum i))
	(setf (svref res i) (svref v2 i)))))

;; p+vv-zero-check: helper for p+into

(defun p+vv-zero-check (place form) 
  (if (coefzerop place) form (p+ place form)))

;; pnorm converts a polynomial into a normal form in case it is
;; really zero or a constant or has trailing (high degree) zero
;; coeffs.  pnorm is destructive. pnorm is Not recursive except
;; in converting constant terms to manifest non-vectors.
;; Assume x is an arbitrary main-variable index:
;; #(x 5) -> 5.  #(x 5 4 3 0 0) -> #(x 5 4 3).  #(x 0 0) -> 0. 
;; #(x 0 1) -> #(x 0 1) [no change]

;; pnorm: return the normal form of x

(defun pnorm (x)
  (if (coefp x)
      x
      (let ((x x) pos)
	(declare (simple-vector x) (fixnum pos)
		 (inline position-if-not coefzerofunp delete-if))
	(setq pos (position-if-not #'coefzerofunp x :from-end t))
	(cond ((= pos 0)
	       (coefzero)) ;; nothing left but the header: zero polynomial
	      ((= pos 1) ;; just the constant itself
	       (pnorm (svref x 1))) ;; constant polynomial
	      ((= pos (1- (length x))) x)
	      (t #-kcl (delete-if #'coefzerofunp x :start pos)
		 ;fix bug in kcl delete-if
		 #+kcl (setq x  (delete-if #'coefzerofunp x :start pos))
		 )))))

;; p^v: this may seem like a dumb way to compute powers, but it's not
;; Repeated multiplication is generally faster than squaring.  In this
;; representation, binomial expansion, a good bet for sparse representation,
;; is only sometimes advantageous, and then not by very much, usually.

(defun p^ (x n)             ;; x^n -  n integer, x polynomial
  (cond ((integerp n)
	 (cond ((minusp n) (error "negative powers not allowed"))
	       ((zerop n) 1) ;; x^0 = 1 (even if x = 0)
	       ((eql n 1) x) ;; x^1 = x
	       ((coefp x) (expt x n))
	       (t (p* x (p^ x (1- n))))))
	(t (error "only integer powers allowed"))))

;; p/: divide p by s; only exact divisions are performed, and
;;            the result is q such that q*s = p; exact means that p, q,
;;            and s all have integer coefficients.

;; This does NOT work over random coefficient domains that you might
;; construct.

;; Ordinarily a single value is returned unless there is an
;; error condition, in which case the first value is nil and the second
;; is a string which describes the problem.

;; Call p/-test if you want a "semi-predicate."
;; Look at the first (or only value). If it is non-nil, you've got
;; the exact quotient.

;; Call p/-and-barf if you want to signal an error in case
;; an exact division is not possible.

(defun p/-and-barf (p s)
  (multiple-value-bind (v err)
		       (catch 'p/ (p/ p s))
		       (cond ((null v) (error err))
			     (t v))))

(defun p/-test(p s)
  (catch 'p/ (p/ p s)))

(defun p/ (p s)	
  (cond ((coefzerop s) (throw 'p/ (values nil "Division by zero")))
	((coefonep s) p)
        ((coefzerop p) p)
        ((coefp p)
         (cond ((coefp s)
                (cond ((eql 0 (mod p s))(/ p s))
                      (t (throw 'p/
				(values nil "Inexact integer division")))))
               (t (throw	
                   'p/
                   (values nil "Division by a polynomial of higher degree")))))
        ((or (coefp s) (var> (mainvar p) (mainvar s))) (p/vc p s))
        ((var> (mainvar s) (mainvar p))
         (throw 'p/
                (values nil "Division by a polynomial of higher <degree")))
        (t (p/helper p s))))

(defun p/vc (p s)
  (let ((q (copy-seq p)))
    (do ((i (1- (length p)) (1- i)))
        ((= i 0) q)
        (setf (svref q i) (p/ (svref q i) s)))))

(defun p/helper (p s)
  (declare (simple-vector p s))
  (let ((l1 (length p)) (l2 (length s)))
    (cond ((> l2 l1)
           (throw 'p/
                  (values nil "Division by a polynomial of higher degree")))
          (t (let ((q (make-array (+ 2 l1 (- l2)) :initial-element 0))
		   (sneg (pnegate s))
		   (slc (lc s)))
	       (setf (mainvar q) (mainvar p))
	       (do* ((i l1 (length p)))
		    ((< i l2) (throw 'p/
				     (values nil "Quotient not exact")))
		    (setf (svref q (+ 1 i (- l2))) (p/ (lc p) slc))
		    (setq p (pnorm (p+ p (p* (subseq q 0 (+ 2 i (- l2)))
						 sneg))))
		    (if (coefzerop p) (return (pnorm q)))
		    (if (coefp p)
			(throw 'p/
			       (values nil "Quotient not exact")))))))))

;; prem: return the pseudo remainder when p is divided by s
;; (You didn't learn this in high school.) Ref. Knuth, Art of Comptr. Prog.
;; vol. 2.  This turns out to be important for GCD computations.

(defun prem (p s)
  (cond ((coefzerop s) (error "Division by zero"))
	((coefzerop p) p)
        ((coefp p)
         (cond ((coefp s) (coefrem p s))
               (t p)))
        ((or (coefp s) (var> (mainvar p) (mainvar s))) (coefzero))
        ((var> (mainvar s) (mainvar p)) p)
	(t (prem2 p s))))

;; prem2: return the pseudo remainder when p is divided by s; p and s
;;        must have the same variable. This is the usual situation.

(defun prem2 (p s)
  (if (> (length s) (length p))
      p
    (let* ((slc (lc s))
	     (l (- (length p) (length s)))
	     (temp (make-array (+ 2 l) :initial-element 0)))
	(setf (mainvar temp) (mainvar p))       
	(do ((k l m)
	     (m))
	    (nil)
	  #-kcl(delete-if #' identity temp :start (+ 2 k))
	  ;; fix bug in kcl delete-if, which is non-destructive
	  #+kcl (setq temp (delete-if #' identity temp :start (+ 2 k)))
	    (setf (lc temp) (lc p))
	    (setq p (pnorm (p+ (p* p slc) (p*cv -1 (p* temp s)))))
	    (cond ((or (coefp p)		
		       (var> (mainvar s) (mainvar p))) 
		   (return p))		
		  ((< (setq m (- (length p) (length s))) 0) 
		   (return (cond ((= k 0) p) 
				 (t (p* p (p^ slc k)))))))  
	    (if (> (1- k) m)	
		(setq p (p* p (p^ slc (- (1- k) m)))))))))

;; Subresultant polynomial gcd.
;; See Knuth vol 2 2nd ed p 410. or TOMS Sept. 1978.
;; pgcdsr: return the gcd of u and v;

(defun pgcdsr (u v)
  (cond ((coefzerop u) v)
	((coefzerop v) u)
	((coefp u) (cond ((coefp v) (gcd u v))
			 (t (pcontentxsr v u))))
	((coefp v) (pcontentxsr u v))
	((var> (mainvar v) (mainvar u)) (pcontentxsr v u))
	((var> (mainvar u) (mainvar v)) (pcontentxsr u v))
	(t (pgcd2sr u v))))

;; pgcd2sr: return the gcd of u and v, which have the same main variable
;; p and q must have the same main variable.

(defun pgcd2sr (p q)
  ;; set up so q is of same or lower degree
  (cond ((> (length q) (length p)) (rotatef p q)))
  ;; next, remove the content
  (let*((pcont (pcontentsr p))
	(qcont (pcontentsr q))
	(content (pgcdsr pcont qcont)))
    
    (do ((g 1 (lc p))
	 (h 1 (p/ (p^ g d) hpow))
	 (d (- (length p)(length q)) (- (length p)(length q)))
	 (hpow 1 (if (= h 1) 1 (p^ h (1- d)))))
	(nil)
	(psetq p q
	       q (p/ (prem p q)(p* g (p* h hpow))))
		
;	(format  t "~%p=~s~%q=~s~% d=~s, h=~s" p q d h)
	(if (coefzerop q) ;; poly remainder seq ended with zero
	    (return (p* content p)))
	(if (or (coefp q) (var> (mainvar p) (mainvar q)))
	    ;; the remainder sequence ended with non-zero, just
	    ;;return the gcd of the contents.
	    (return content)))))


;; this is a primitive prs, just like pgcd2sr but not as fast sometimes
(defun pgcd2prim (u v)
  (cond ((> (length v) (length u)) (rotatef u v)))
  (let ((ucont (pcontentsr u))
	(vcont (pcontentsr v)))
    (do ((c (p/ u ucont) d)
	 (d (p/ v vcont) (ppartsr (prem c d))))
	(nil)
	(if (coefzerop d)
	    (return (p* (pgcdsr ucont vcont) c)))
	(if (or (coefp d) (var> (mainvar c) (mainvar d)))
	    (return (pgcdsr ucont vcont))))))

;; pcontentsr: return the content of p (see Knuth, op. cit)
;; the content is the GCD of the coefficient of the top-level in the
;; polynomial p.

(defun pcontentsr (p)
  (cond ((coefzerop p) p)
        ((coefp p) (coefone))
	(t (let ((len (length p)))
	     (do ((i 2 (1+ i)) (g (svref p 1) (pgcdsr g (svref p i))))
		 ((or (= i len) (coefonep g)) g))))))

; pcontentxsr: return the gcd of u and the content of p
;; this is a handy time-saver

(defun pcontentxsr (p u)
  (cond ((coefzerop p) u)
        ((coefp p) (gcd p u))
	(t (do ((i (1- (length p)) (1- i)) (g u (pgcdsr g (svref p i))))
	       ((or (coefonep g) (= i 0)) g)))))

; ppartsr: return the primitive part of p

(defun ppartsr (p)
  (cond ((or (coefzerop p) (coefp p)) p)
        (t (p/ p (pcontentsr p)))))

;; in some of the algorithms, the cofactors will be "free".  Here we're
;; just dividing the inputs by the gcd.

(defun pgcd-cofac (u v)(let ((g (pgcdsr u v)))
			    (values  g (p/ u g)(p/ v g))))

;; this program provides an ordering on polynomials, lexicographically.
;; it returns 'l (less than) 'e (equal)  or 'g (greater than).

;; this ordering is recursive by main variable.  There are other orderings,
;; like total degree ordering.

(defun pcompare (u v) 
  (cond ((eq u v) 'e) ;; quick check for equality
	;; if u and v are coefficients, then compare their numerical values.
	((coefp u)(cond ((coefp v)(cond((coef> v u) 'l)
				       ((coef> u v) 'g)
				       (t           'e)))
			;;u is coefficient, v is not, so  u << v
			(t 'l)))
	;; v is coefficient, u is not, so u >> v
	((coefp v) 'g)
	;; neither is a coefficient
	(t (let ((um (mainvar u))
		 (vm (mainvar v))
		 (ud (degree u))
		 (vd (degree v))
		 (ctest nil))
	     (cond ((var> um vm) 'g)  ; u has a more-main variable than v
		   ((var> vm um) 'l)  ; the reverse case
		   ((> ud vd)  'g) ; u is higher degree  u >> v
		   ((> vd ud)  'l) ; v is higher degree, so  v >> u
		   ;; Same main variable, same degree.
		   ;; Compare the coefficients, starting from the highest
		   ;; degree. The first one that differs determines
		   ;; which direction the comparison goes.
		   
		   (t (do ((i (1+ ud) (1- i)))
			  ((= i 0) 'e); no differences found.  u = v
			  (setq ctest (pcompare (svref u i)(svref v i)))
			  (if (eq ctest 'e) nil (return ctest))
			  )))))))


;; compute the derivative wrt v, the encoding of a variable.
;; This assumes that there are no other dependencies on kernels, etc.

(defun pderiv (p v)
  (labels
   ((pd1 (p &aux r)
	 (cond ((coefp p) 0)
	       ((var> v (svref p 0)) 0)
	       ((eql (svref p 0) v)
		(setq r (make-array (1- (length p))))
		(setf (svref r 0) v)
		(do ((i (1- (length p)) (1- i)))
		    ((= i 1) (pnorm r))
		    (setf (svref r (1- i))(p* (- i 1) (svref p i)))))
	       (t (setq r(copy-seq p))
		  (do ((i (1- (length r))(1- i)))
		      ((= i 0) (pnorm r))
		      (setf (svref r i)(pd1 (svref r i))))))))
   (pd1 p)))

