;; -*- Mode:Common-Lisp;Package:mma; Base:10 -*-
;;; version 15 does not include
;;; flat+orderless. or Optional. or Condition-on-replacement
;;; version 16 doesn't work as well.  This doesn't work so well either...


;; note: I'm equivocating somewhat on the use of 'True and 'False
;; as Boolean values in Mma. Problem: most lisp functions naturally
;; use nil for false, and "anything else" but sometimes just 't
;; for true.  

;; Here's the decision: 
;;   Common   Our       WRI's             Meaning
;;    Lisp    mma       Mathematica (tm)
;; ----------------------------------
;; non-nil     t         True            Boolean Truth
;;    nil     nil        False           Boolean False
;;    nil     Null       Null            Null value 
;;    nil    (List)     {} (i.e. List[]) Empty List

;; possible problem: setting t in lisp is a no-no. Can be averted in
;; the parser, I suppose, or maybe abandon the use of lisp atom space
;; for global name space.

;;(provide 'match)
;;(require "stack1")
(in-package :mma)

;;; definition: a patternobject is like an expression but it can
;;; have (Pattern ...) or (Blank ..) subexpressions in it.

;;; All that matches in version 16
;;; (a) structurally identical matches.
;;; (b) (Blank) matches <anything>
;;;     (Blank foo) matches anything with a car of foo or
;;;     in the case of a match to an atom x, it will match
;;;     if (typep x foo) is true, foo is in {Integer, Rational ..?}

;;; (c) (Pattern x <patternobject>) matches whatever would
;;;   otherwise be matched by <patternobject> but  binds the value of
;;;   patternobject to the name x.  From that time onward during the match
;;;   x will only match identical items.

;;; That is, f[x_,x_] will match f[3,3] but not f[3,4].
;;; f[x_,x_^2] will match f[a,a^2].  But not f[3,9]. (sorry).

;;; (d)  (BlankSequence ...) or __ inside (non-Orderless) functions. Note:
;;;  If f is "Flat" then f[a,x_] matches f[a,z,w]
;;;   with x-> f[z,w]. 
;;;  If f is "Flat" then f[b,x__] matches f[b,z,w]
;;;   with x-> (z,w) .  That's Sequence[z,w]. Look it up...

;;; (e) (BlankNullSequence ...) or ___ inside (non-Orderless) functions.

;;; (f) Orderless functions are matched only if they have a fixed
;;; number of arguments.

;;; (g) (PatternTest <patternobj> Test) matches whatever <patternobj> would
;;; match, but only if (Test <patternobj>) returns lisp t.  Question:
;;; perhaps we should ask that (meval (list Test <patternobj>)) be True not t?
;;; we keep to t.

;;; g[x__,x__] matches g[1,2,3,1,2,3]  with x->(1,2,3)

;;; Some Flat functions are Plus, Times.  There are hardly any
;;; others.  Plus is also orderless (see below) complicating
;;; the matching considerably.  

;;; Functions which are both Flat and Orderless functions are
;;; not handled by this version.


;;; Orderless is handled...  (not, "If you can't eat it all, order less"  but
;;; "The universe tends toward a state without order -- orderless"..)

;;; if (say) Plus is orderless, then Plus[x_,Sin[x_]] matches
;;; Plus[3,Sin[3]] or Plus[Sin[3],3].

;;; Also allowed: x_Integer, x_foo,  or x:f[_] .   The form x_foo has the
;;; meaning that x's Head must be foo, or x must be of type foo.
;;;  x_foo parses into (Pattern x (Blank foo))
;;; x:f[_] parses into (Pattern x (f (Blank)))

;;; Return value for a match is  nil or non-nil.
;;; If the value is non-nil, the stack structure env
;;; will have a set
;;; of bindings of all the pattern-variable bindings. If the return value
;;; is nil, env will be unchanged.

;; define match stack, using up to 100 pattern variables if no-one else
;; has done it.

(defvar env (make-stack :size 100))

;; match provides a top level match of pattern to expression.
;; both pattern and expression are assumed to be Lisp lists
;; from the parser (lmath:parser)

;; Usually match won't be used by a program ... rather, it will use m1.
;; Typical usage would then be as follows...

;; match pat and exp in an environment which is a stack (perhaps empty)

(declaim (special env phead isflat isorderless isfol))

;; a note on the data structuring.  
;; It would be possible to "abstract way" some of the cars and cdrs
;; but the representation from the parser is fairly definitive, close
;; to Mma, and unlikely to benefit from revision. Consequently it would
;; seem to be mostly coyness to pretend that we didn't know how things
;; were stored, and frankly, defining map-over-args as mapcar and
;; (head x) as (car x) gets tiresome, especially when you "pun" and
;; use argument lists as lisp lists. Of course, if we change the
;; data representation, this program will be harder to change as a
;; result of this decision.

;; a simple test function

(defun trial(pat exp &optional (env (make-stack :size 20) wasitprovided))
  (spushframe env 'trialmatch)
  (if  (m1 pat exp)
      (format t "~%Match Succeeded. Binding Stack = ~%~s" env)
    (format t "~%Match Failed~%"))

  ;; reset ptr to former position if environment was provided
  (if wasitprovided (spopframe env)))

;; match returns  t/nil depending on whether it matches or not. Typically
;; if match returns non-nil, then the global variable 
;; env will be returned with some bindings: a stack-frame called "match"
;; or "matchlist". 
;; Therefore
;; the caller of match (res. matchlist)  should do an (spopframe env) after
;; appropriate use of the environment env for (say) the evaluation of
;; the rhs of a pattern-replacement rule.

(defun match (pat exp)
  (spushframe env 'match)
  (m1 pat exp)) ;;won't work for condition on exp

(defun matchlist(pl el)  ;;alternative top level for simultaneous matches
  (spushframe env 'matchlist)
    (mlist pl el nil t))

(defun m1 (p e)
  (cond ((atom p)(equal p e)) 
	((eq p e) t)
	((equal p e) t) ;; remove this if it isnt saving time..
	(t (let ((phead (car p)))
	     (declare (special phead))
	     ;;(format t "~%phead = ~s" phead)
	     (cond ((eq phead 'Blank)(mblank (cdr p) e)) ;do Blank matching
		   
		   ((eq phead 'Pattern)

		    ;; (cadr p) is the name to be used for the
		    ;; pattern variable if the pattern object (caddr p)
		    ;; matches the expression e.
		    (mpat (cadr p) (caddr p) e))
		   ((eq phead 'PatternTest)
		    (let ((result (m1 (cadr p) e)))
		      (cond (result
			     (funcall (caddr p)(meval e)))
			    (t nil))))
		   ((eq phead 'Condition)
		    (let ((result (m1 (cadr p) e)))
		      (cond ((and result 
			      (meval (caddr p))) t)
			    (t nil))))
		   ((atom e) nil) ; non-atom, non-blank p can't match atom.
		   ;; now both p and e are expressions.
		   ;; we match (recursively) their heads, and match,
		   ;; in sequence, elements in their cdrs, by mlist.
		   ;; Before calling mlist, we bind a spec variable phead
		   ;; to phead and note properties (Flat, Orderless) of it
		   ;; on spec variables isflat, isorderless, isfol.
		   
		   ((m1 phead (car e)) ;first check that heads match
		    (let* ((isflat (flatp phead))
			   (isorderless (orderlessp phead))
			   (isfol (and isflat isorderless)))
		      ;; if phead is not flat, it is convenient to
		      ;; set it to Sequence when matching __.
		      (if isflat nil (setq phead 'Sequence))
		      
		      (cond(isfol ;;Flat AND Orderless
			    ;; this is not written yet
			    ;; needed for Plus, Times, but not much
			    ;; else other than these important cases.
			    ;; (maybe "Bag"?)
			    (mlistfol (cdr p)(cdr e) 0 (1-(length e))))
			   
			   (isorderless ;; Orderless, but not Flat
			    ;; There are lots of commutative operators,
			    ;; including symmetric ones (e.g. x=y).
			    ;; this version is not quite right. see defun.
			    (mlistol (cdr p)(cdr e) 0 (1-(length e))))
			   
			   (t ;; Flat or not, ordered.
			    ;; we must match in sequence all elements.
			    (mlist (cdr p)(cdr e) nil t)) ;;condition t??
			   ))))))))

;;******makeshift for now..********

(defun orderlessp(x)(member x '(ol Plus Times) :test #'eq))

(defun flatp (x)(member x '(flat Plus Times) :test #'eq))


;;*********************************

;; mblank matches a (Blank h) or (Blank). This works if the test
;; headtest = (h) is nil, 
;; or if the head of e is (car headtest)
;;   (i.e. (Blank foo) matches (foo ...))
;; or if headtest is the "type" of e.  
;;   (i.e. (Blank Integer) matches 3.

(defun mblank(headtest e)
  (if headtest (mtypep e (car headtest)) t))
     
(defun mblank2 (headtest e) ;; hardly enough for _ _ or _ _ _.
  (if headtest (mtypep e (car headtest)) t))

(defun blank1p(x)
  (and (consp x)
       (eq (car x) 'Blank)))

  (defun blank2p(x)
  (and (consp x)
       (eq (car x) 'BlankSequence)))


(defun blank3p(x)
  (and (consp x)
       (eq (car x) 'BlankNullSequence)))


(defun patternp(x)(and (consp x)(eq (car x) 'Pattern)))

;; match two lists, ordered. If the pl (pattern list)
;; contains a Blank (_), BlankSequence (_), or BlankNullSequence (___).
;; then special routines must be used.
;; If phead has attribute flat, (isflat is true), then Blank matching
;; operates the same as BlankSequence.  Why?  So
;; a+x_ matches a+b+c with x-> b+c, instead of
;;                         x-> Sequence[b,c]

(defun mlist(pl el name condition)
  (cond ((null pl) 
	 (and(null el) (meval-to-bool condition)));; both must end at the same time to match
	
	((patternp (car pl))
	 ;; must to assign the matched stuff to
	 ;; (cadar pl), the name..
	 ;; might try to avoid this cons...
	 (mlist (cons (caddar pl)(cdr pl)) el (cadar pl) condition ))
	
	((blank2p (car pl))
	 ;;since this is NOT orderless, we must match these suckers in
	 ;;order, or not at all. We look for the shortest sequence
	 ;;of length ONE or more that matches.
	 
	 ;; Mma semantics requires the following glitch..
	 (if isflat (setq phead 'Sequence))

	 (ml2 (cadar pl) (cdr pl) el name 1))
	
	((blank3p (car pl))
	 ;;this one, BlankNullSequence (_ _ _) requires
	 ;; the shortest sequence of ZERO or more elements.
	 (ml2 (cadar pl) (cdr pl) el name 0))	   	 
	
	((and isflat (blank1p (car pl)))
	 ;; for a flat operator, treat f[...,x_,...] like f[...,x__,...].
	 ;; So says Mma semantics.
	 (ml2 (cadar pl) (cdr pl) el name 1))
	(name (and(mpat name (car pl)(car el))
		  (mlist (cdr pl)(cdr el) nil condition)))
	((m1 (car pl)(car el))
	 ;; if the cars match, so must the elements of the cdrs
	 (mlist (cdr pl)(cdr el) nil condition))))

;; match patobj h against minmatch or more initial elements of el. Succeed only
;; if matching all of pl against the rest of el succeeds.
;; if name is non-nil, the matching of h will result in the
;; binding of name to the value matched.
;; As usual, el is an expression list, and pl is a list of pattern objs.
;; This is called to match BlankSequence with minmatch=1, and
;; to match BlankNullSequence with minmatch=0

(defun ml2(h pl el name minmatch condition &aux (ptr (stack-ptr env)))
  (cond ((null el)
	 ;; If there are no expressions left in the list then
	 ;; if it is acceptable for h to match "no" elements
	 ;; and if this is consistent with any previous assignments
	 ;; to "name", and the remaining patterns in the pattern list can
	 ;; also be matched to "no" elements, we will succeed here.
	 (let ((r (list phead)) )
	   (cond
	   ((and (= minmatch 0) (if name (mpat name r r) t))
	    (cond((mlist pl nil nil t) t)
		 (t (setf (stack-ptr env) ptr) nil)))
	   (t (setf (stack-ptr env) ptr)nil)) ))

;;remove the ;; below if you want to use the special end case.   
;;	((null pl)(ml2quick h pl el name))

	(t (let ((lel (length el)) )
	     ;; Starting with the minimum number (0, 1) of elements
	     ;; to match, try to match  h
	     (do ((k minmatch (1+ k))
		  (collect nil nil))
		 ;; termination with failure if we exhaust all
		 ;; the elements up to the length of el, and
		 ;; still haven't gotten a match. Reset the
		 ;; stack pointer if we've changed it, and
		 ;; return nil
		 ((> k lel) (setf (stack-ptr env) ptr) nil)
		 
		 ;; try to match h against 1st, then 1 thru 2, then 1 thru lel
		 ;; of the elements in el. This program can't skip any elements
		 ;; since it is not for "orderless"  heads.
		 ;;		 (format t "~%k=~s" k) ;debug

		 (do ((j el (cdr j)) 
		      ;; j is the list of expressions in el
		      ;; starting with el itself, and stepping down..
		      (count 1 (1+ count))
		      ;; the count mirrors j's length..
		      )
		     
		     ;;termination check: when we've looked at the first k els
		     ;; and haven't jumped out, we let the rest of the pattern
		     ;; have a chance.

		     ((> count k)
		      ;; note that phead will be a function
		      ;; head f if f is flat, else Sequence.
		      ;; q? should use uniq/ucons here
		      (setq collect (cons phead (reverse collect)))
;;		      (format t "~%Collected so far .. ~s" collect)
		      ;; if we've been provided a non-nil name, then
		      ;; check it against previous bindings if any;
		      ;; push the value for future checks.
		      (and (if name (mpat name collect collect) t)
		      ;; match the rest, if you can.
		      (cond((mlist pl j nil condition) 
			    (return-from ml2 t))
			   (t
			    ;; else un-assert this binding and try k:=k+1
			    (setf (stack-ptr env) ptr)
			    nil))))
		 
		     
		     ;; the do-loop body
;;		     (format t "~% j = ~s" j)
		     (cond ((mblank2 h (car j))
			    (setq collect (cons (car j) collect))
;;			    (format t "~% consed onto collect: ~s" collect)
			    ;; reset stack pointer after collection
			    (setf (stack-ptr env) ptr))
			   ;; it should be possible to expedite failure here.
			   ;; If p fails to match e[j+n], then p's predecessor
			   ;; should be advanced n places. But the control
			   ;; flow is too messy to contemplate for now.
			   ;;. (e.g. f[x__,p_pred])
			   ;; But, anyway, the predicate failed.
			   (t (setf (stack-ptr env) ptr)
			      (return-from ml2 nil)))))))))
  
;; special case in above..
;; if you have the last pattern element, you can be sure that either
;; it matches the rest of the expressions, or the pattern fails.
  
(defun ml2quick (h pl el name condition)	
  ;; the BlankSequence is at the end: try to match against
  ;; all the rest of the elements
  (let ((collect nil)
	(ptr (stack-ptr env)))
    (do ((j el (cdr j)))
	       
	;;termination check: when we've exhausted expr. list
	;; and haven't jumped out, we've absorbed all of el.
	((null j)
	 ;; note that phead will be a function
	 ;; head f if f is flat, else Sequence.
	 (setq collect (cons phead (nreverse collect)))
	 ;; if we've been provided a non-nil name, then
	 ;; check it against previous bindings if any;
	 ;; push the value for future checks. Return.
	 (if name (mpat name collect collect) (meval-to-bool condition)))
	       
	;; the do-loop body
	(cond ((mblank2 h (car j))
	       (setq collect (cons (car j) collect))
	       ;; reset stack pointer after collection
	       (setf (stack-ptr env) ptr))
	      (t (return nil))))))


;; match two lists, orderless, not flat or allowing BlankSequence
;; start with element i of expressionlist el, length of el is h.
;; This program is not directly applicable to Mma since BlankSequence
;; is allowed anywhere..

(defun mlistol (pl el i h condition)

  (cond ((null pl) (null el));; success if we run out of p and e together
	((= i h) nil);;exhausted all possibilities. fail
	(t (let ((p (car pl))
		 (ptr (stack-ptr env)))
	     (do ((count 0 (1+ count))
		  (index i (mod (1+ index) h)))
		 ((> count h)
		  ;; we never matched  p=(car pl), starting at (elt el i).
		  ;; try matching p again, but starting at (elt el (1+ i))

		  (mlistol pl el (1+ i) h))
		 
		 (cond ((m1 p (elt el index))
			;; if success, we leave a binding for (car p) on env,
			;; remove (elt el index) from el, 
			;; and try next pattern.
			;;debug	(format t "~%matched ~s to ~s " p (elt el index))
			(cond ((mlistol
				(cdr pl)
				(remove nil el
					:test #'true2 :start index
					:count 1)
				0
				(1- h)
				condition)
			       (return (meval-to-bool condition))))))
		 ;; failure to match p to (elt el i)
		 ;; or perhaps failure at another level below -->
		 ;; reset bindings, restore el, and keep trying
		 (setf (stack-ptr env) ptr))))))


;; this one handles orderless and flat and blanks..
;; try to match (car pl) against 0 or more elements of el.
;; start with element i of expressionlist el, length of el is h.

;;this program is not structurally correct...
#+ignore (defun mlistolf (pl el i h name condition)

  (cond ((null pl) (null el));; success if we run out of p and e together
	((= i h) nil);;exhausted all possibilities. Can't match (car pl). Fail.
	(t (let ((p (car pl))
		 (ptr (stack-ptr env)))
	     
	     (cond 
	      ((patternp (car pl))
	       ;; pick out the name and call for a match
	       ;;               patobj                       name
	       (mlistolf2 (cons (caddr p) (cdr pl)) el i h  (cadr p)))

	      ((and (blank1p (car pl)) (not isflat))
	       ;; match exactly one expression, somewhere
	       (do ((count 0 (1+ count))
		    (index i (mod (1+ index) h)))
		   ((> count h)
		    ;; we never matched  p=(car pl), starting at (elt el i).
		    ;; try matching p again, but starting at (elt el (1+ i))

		    (mlistolf pl el (1+ i) h))
		 
		   (cond ((m1 p (elt el index))
			  ;; if success, we leave a binding for (car p) on env,
			  ;; remove (elt el index) from el, 
			  ;; and try next pattern.
			  ;;debug	(format t "~%matched ~s to ~s " p (elt el index))
			  (cond ((mlistolf
				  (cdr pl)
				  (remove nil el
					  :test #'true2 :start index
					  :count 1)
				  0
				  (1- h))
				 (return t)))))
		   ;; failure to match p to (elt el i)
		   ;; or perhaps failure at another level below -->
		   ;; reset bindings, restore el, and keep trying
		   (setf (stack-ptr env) ptr)))
	      
	      ((or (blank1p p);; and isflat
		   (blank2p p))
     (let (collect trialval (ptr (stack-ptr env)))	       
      (do ((count 0 (1+ count))
	   (index i (1+ index)))
	  ((> count h)
	   ;; we never matched  p=(car pl), starting at (elt el i).
	   ;; try matching p again, but starting at (elt el (1+ i))

	   (mlistolf pl el (1+ i) h name))
		 
	  (cond ((m1 p (elt el index))
		 ;; if success, we place the binding for (car p) 
		 ;; on the list collect.
		 ;; remove (elt el index) from el, 
		 ;; and try next pattern.
		 ;;debug	(format t "~%matched ~s to ~s " p (elt el index))
		 (setq collect (cons (elt el index) collect))
		 (setf (stack-ptr env) ptr)
		 (setq trialval (cons phead (reverse collect)))
		 (cond ((or (null name) (mpat name trialval trialval))
			(cond ((mlistolf
				(cdr pl)
				(remove nil el
					:test #'true2 :start index
					:count 1)
				0
				(1- h) nil)
			       (return t)))))
		 ;; failure to match p to (elt el i)
		 ;; or perhaps failure at another level below -->
		 ;; reset bindings, restore el, and keep trying.  Two
		 ;; ways to keep trying, though.
		 ;; (a) retract p, or
		 ;; (b) extend p to more terms so that the lower level
		 ;; will match. We do (a) first, and then (b).
		 ;;; GOTTA PUT THIS IN HERE. HOW?
		 (setf (stack-ptr env) ptr)))
	  
	  (t
	   ;; regular case: match a constant pattern subexpression,
	   ;; more or less, against (some) constant expression
	   
				 
	       )))))))))
	     		 
(defun true2 (x y) t)		
	       
;; match a pattern and an expression
;; Changed from version 1 to allow for pattern vars to appear repeated
;; Changed from version 2 and 3 to deal with a:f[_]  etc.


(defun mpat (name patobj e)
  ;; to match (Pattern name patobj) to e, 
  ;; first see if name has a value - if so, test for equality of value to e.
  ;; we assume the user has not done f[x_foo,x_bar] (different tests...)
  ;; Otherwise just bind name to e
  

  (multiple-value-bind (val found)(sfind env name)
		       (cond (found (equal val e))
			     ((m1 patobj e)(spush env name e) t)
			     (t nil))))
     
;; if x is atomic, if typ is not a type, or x is not of type typ, return nil.
;; in case x is a cons, see if its head is eq to typ.

(defun mtypep(x typ)(if (atom x)
			(multiple-value-bind 
			 (isnoerr val)
			 (errorset  ;;excl returns nil if no err, value of form
			  (typep x typ))
			 (if isnoerr val nil))
		      (eq (car x) typ)))

;;these cause problems if Integer and integer are the same as INTEGER

#-(or lucid kcl) (deftype Integer() 'integer)
#-(or lucid kcl) (deftype Rational() 'rational)
;;; etc could do single-float, double-float, complex, number, cons, ...

;; extra cases to consider: 

;;  x_.
;;    = (Optional (Pattern x (Blank))) 

;; Also, Orderless + Flat.  Any other Attributes?  How about Defaults?,
;; repeated, what else?

;; also f[x_]:=g[x]  /; x>0


;;; some sample programs for combinatorial matching.
;;; mapcomb applies the function f to each combination of
;;; elements in l. Non-destructive.  Try (mapcomb 'print '(1 2 3))

(defun mapcomb(f l)
  (labels((mc (l c)
	      (cond ((null l) (funcall f c))
		    (t (mc (cdr l) c)
		       (mc (cdr l) (cons (car l) c))))))
	 (mc (reverse l) nil)))



;; map over all combinations of l, and return the first combination c
;; for which (f c) is true.

(defun mapcomb-if(f l)
  (labels((mc (l c)
	      (cond ((null l)
		     (if (funcall f c) (return-from mapcomb-if c)))
		    (t (mc (cdr l) c)
		       (mc (cdr l) (cons (car l) c))))))
	 (mc (reverse l) nil)))


;; list of permutations. 

(defun permlist (l)
  (cond ((null l) nil)
	((null (cdr l)) (list l))
	(t (let*((res nil)
		 (this (list(car l)))
		 (prev (permlist (cdr l))))
	     ;; insert this in each position in elements in prev
	     ;; and put on the list res
	     (do ((p prev (cdr p)))
		 ((null p) res)
		 (do* ((left nil (append left (list (car right))))
		       (right (car p) (cdr right)) )
		      ((null right) 
		       (setq res (cons (append left this right) res)))
		     (setq res (cons (append left this right) res))))))))

;; these are not part of the matcher, but they are often used in
;; the matching process.  For the moment, we'll keep them in the
;; same file.
		 
(defun IntegerQ (x)(integerp x))
(defun EvenQ (x)(and (integerp x)(evenp x)))
(defun OddQ (x)(and (integerp x)(oddp x)))
(defun NumberQ(x)(numberp x))

;; have not defined PrimeQ PolynomialQ VectorQ MatrixQ ValueQ OrderedQ UnSameQ

(defun SameQ(x y)(if(equal x y) t))

;; this is really cute:  if x matches an element of l, return true
;; e.g. if pat = (m1 x l) (PatternTest (Pattern x (Blank)) IntegerQ) 
;; then (MemberQ '(a b 3 z) pat)  will return True

(defun MemberQ(l x)(if (member x l :test #'match) t)) 


(defun FreeQ (l x) 
  (labels((freeqx (h)(FreeQ h x))
	  (dependsx (h)(null (FreeQ h x))))  ;;returns t or nil
	 (cond ((MatchQ l x) nil)
	       ((consp l)(if (some #'dependsx (cdr l))
			     nil t))
	       (t t))))
	       

(defun MatchQ(l x)(if (match x l) t nil))

(defun AtomQ(x)(if(atom x) t))

(defun Greater(x y)(cond ((and (numberp x)(numberp y))
			  (> x y))
			 (t `(Inequality ,x Greater ,y))))
(defun Less (x y)(cond ((and (numberp x)(numberp y))
			  (< x y))
			 (t `(Inequality ,x Less ,y))))
(defun Equal(x y)(cond 
		  ((member x '(Indeterminate Infinity) :test #'eq)
		   `(Inequality ,x Equal ,y))
		  ((equalp x y)  t) ;; handles numbers too, if equal
		  ((and(numberp x)(numberp y)) nil)
		  ;; for now, we dump anything we can't prove into Inequality
		  (t `(Inequality ,x Equal ,y))))

;; need LessEqual  etc.

;; this is NOT consistent with Mathematica's program, exactly,
;; since 2 numbers of different precision may be SameQ in mma.

(defun SameQ(x y) (equal x y))

(defun meval-to-bool(x)(cond((eq x t) t)
			    ((null x) nil)
			    ((eq (meval x) t) t)
			    (t nil) ;; that is, anything not t is untrue
			    ))


