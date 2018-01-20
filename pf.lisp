;;;;
;;;;
;;;; (c) Copyright 1990 Richard J. Fateman, Derek T. Lai
;;;;     FILE -- pf.lisp
;;;;
;;;; pf.lisps of procedures that accept the outpdata s prefixs prefix
;;;; form such as would be produced by the parser (p) in parser.lisp, and
;;;; produces lists which resemble the
;;;; PrintForm output of Mathematica.  
;;;;
;;;; For example, if we type (x+y)^2 as input, the parser will return
;;;; 
;;;;           (POWER (PLUS X Y) 2)
;;;;
;;;; The procedures in this file will convert the above expression into
;;;; the "PrintForm" list as below:
;;;;
;;;;   (HORIZONTALFORM 8 2 0 0 POWER 190 RIGHT
;;;;	    ((HORIZONTALFORM 7 1 0 0 SEQUENCE 1000 NONE
;;;;           ("(" (HORIZONTALFORM 5 1 0 0 PLUS 140 NONE (X " + " Y)) ")"))
;;;;		 (VERTICALFORM 1 1 0 -1 SUPERSCRIPT 260 NONE 2)))
;;;;
;;;;
;;(provide 'pf)
;;(require "mma")
(in-package :mma)

;;;  exported functions:
(export '(MakeHForm MakeVForm formatwidth formatheight atomwidth
		   BuildFormat))



;;  "formatstruct" is the structure representing the HorizontalForm
;;  and the VerticalForm "PrintForm" lists.
;;
;;  The meaning of its attributes are as follows:
;;    width    --  width of box
;;    height   --  height of box
;;    hoffset  --  horizontal offset
;;    voffset  --  vertical offset, distance from the base of box
;;    op       --  name of operator represented by this box
;;    prec     --  precedence of the operator
;;    asso     --  associativity of the operator
;;    ls       --  can be another HorizontalForm, VerticalForm,
;;                 or some atoms or strings.
;;
;;  In the context below, "PrintForm" lists, "format", "form" are basically
;;  referring to the same thing.

(defstruct (formatstruct (:type list))
  (form nil)
  (width 0 :type fixnum)
  (height 1 :type fixnum)
  (hoffset 0 :type fixnum)
  (voffset 0 :type fixnum)
  (op nil)
  (prec 0 :type fixnum)
  (asso 'none) (ls nil))



;;  MakeVForm & MakeHForm:   
;;          functions that create horizontal and vertical forms respectively.

(defun MakeVForm (w h hof vof op prc as l)
  (make-formatstruct :form 'VerticalForm
		     :width w :height h
		     :hoffset hof :voffset vof
		     :op op :prec prc :asso as :ls l))

(defun MakeHForm (w h hof vof op prc as l)
  (make-formatstruct :form 'HorizontalForm
		     :width w :height h
		     :hoffset hof :voffset vof
		     :op op :prec prc :asso as :ls l))



;;  HFormp & VFormp:
;;          boolean functions that test whether a given form is Horizontal 
;;          or Vertical.

(defun HFormp (form)
  (if (atom form)
      nil
    (string= (car form) 'HorizontalForm)))

(defun VFormp (form)
  (if (atom form)
      nil
    (string= (car form) 'VerticalForm)))



;;  DivideFormp, RepStrFormp, SeqFormp:
;;          These functions tests some commonly encountered forms.
;;          They check whether a given form is a Divide form, a 
;;          RepeatedString Form or a Sequence Form respectively.

(defun DivideFormp (f)
  (if (atom f)
      nil
    (equal (formatstruct-op f) 'Divide)))
  
(defun RepStrFormp (f)
  (if (atom f)
      nil
    (equal (car f) 'RepeatedString)))

(defun SeqFormp (f)
  (if (atom f)
      nil
    (equal (formatstruct-op f) 'Sequence)))



;;  tp:   procedure for repeatedly testing the parser

(defun tp ()
  (format t "~s" (mma::p))
  (terpri)
  (tp))



;;  printform:
;;        procedure that repeatedly (by giving prompts) takes 
;;        Mathematica-acceptable (ordinary) mathematical expressions, 
;;        pass them to the parser whose output is further passwd to 
;;        BuildFormat to form the
;;        "PrintForm" lists.

(defun printform ()
  (format t "~s" (BuildFormat (mma::p)))
  ;; repeat, ad naseum
  (terpri)
  (terpri)
  (printform))



;;  formatwidth & formatheight:   
;;          gets the width and height of a format respectively.

(defun formatwidth (x)
  (if (atom x)
      (atomwidth x)
    (formatstruct-width x)))

(defun formatheight (x)
  (if (atom x)
      1
    (formatstruct-height x)))



;;  Set the precedences of the operators.  This list is arranged in order of
;;  increasing precedence.  

(setf (get 'Set `stringprec) 120)
(setf (get 'Rule 'stringprec) 130)
(setf (get 'Plus 'stringprec) 140)
(setf (get 'Times 'stringprec) 150)
(setf (get 'Divide 'stringprec) 160)
(setf (get 'Minus 'stringprec) 170)
(setf (get 'Power 'stringprec) 190)
(setf (get 'Dot 'stringprec) 210)
(setf (get 'Sequence 'stringprec) 1000)


;;  Set the correct formatter (function name to be dispatched) corresponding 
;;  to the operators
(setf (get 'Rule 'formatter) 'ruleformatter)
(setf (get 'Plus 'formatter) 'plusformatter)
(setf (get 'Times 'formatter) 'timesformatter)
(setf (get 'Power 'formatter) 'powerformatter)
(setf (get 'List 'formatter) 'listformatter)
(setf (get 'Dot 'formatter) 'dotformatter)
(setf (get 'Real 'formatter) 'realformatter)
(setf (get 'Set 'formatter) 'setformatter)
                

;;  Get precedence:  
;;          get the precedence of a given operator.  Default value is 260.

(defun prec (x)
  (if (consp x) 260  ;; I guess.. this is for operators
  (let ((p (get x 'stringprec)))
    (if p
	p
      260)))
	)
            

;;  lessprec:
;;          checks if the operator of a given form "f" has a lower
;;          precedence than a given operator "op"

(defun lessprec (f op)
  (and (not (atom f))
       (< (prec (formatstruct-op f)) (prec op))))
      


;;  atomwidth:  
;;          returns the width of an atom, a number or a string
;;          (but not a formatstruct).

#+ignore (defun atomwidth (x) (length (format nil "~a" x)))

(defun atomwidth(x)(typecase x
			     (string (length (the string x)))
			     (symbol (length (the string (symbol-name x))))
			     (integer (if (minusp x) 
					  (1+ (integer-length-base-10 (- x)))
					(integer-length-base-10 x)))
			     (t (length (the string (format nil "~a" x))))))

#+ignore (defun integer-length-base-10 (x)
  (let* ((fg (floor (integer-length x)
		    3.3219280948873626d0  ))
        ;; that number is log of 10 base 2
	 (try (expt 10 fg)))
    (if (and(<= try x) (> (* 10 try) x))
	(1+ fg)  fg)))

;; this is assuming IEEE arithmetic.  Also a decent logarithm.
;; Funny about that..

(defun integer-length-base-10(x)
    (typecase x
	      ((integer 0 9) 1) ;; most common cases
	      ((integer 10 99) 2)
	      ((integer 100 999) 3)
	      ((integer 0 1000000)(1+(floor (log x 10.0))))
	      ((integer 0 1000000000000000)(1+(floor (log x 10.0d0))))
	      (integer   ;; rest of the cases
	       (let* ((fg (floor (ash (integer-length x) 19) ;mult by 2^19
				 1741647))
			(try (expt 10 fg)))
		   (if (<= try x)   (1+ fg)  fg)))))

;; we could mess with this
;(defvar log10b2 (rationalize(log 10.0d0 2.0d0)))
;(defvar bigint (truncate most-positive-long-float))
#+ignore
(defun log2(x)
  (let* ((r (1- (integer-length x)))
	 (rest ( x (ash 1 r ))))
        (+ (/ r log10b2)(log10 rest))))

#+ignore 
(defun log10(x) (if (< x bigint) (log x 10.0d0)
		  (/ (log2 x) log10b2)))

;;  TopBotHs:
;;          Compare max numerator and denominator heights and
;;          returns a height-packet of cons.

(defun TopBotHs (f maxtoph maxbotmh)
  (let ((toph (- (formatstruct-height f) (formatstruct-voffset f)))
	(botmh (formatstruct-voffset f)))
    (if (> botmh maxbotmh)
	(setq maxbotmh botmh))
    (if (> toph maxtoph)
	(setq maxtoph toph))
    (cons maxtoph maxbotmh)))



;;  BuildFormat:  
;;          This function takes the output lisp expression from the parser,
;;          look at its outermost operator (if any) and pass the whole list
;;          to the appropriate formatter function.

(defun BuildFormat (x)
  (cond 
   
   ((atom x) (cond
	      ;; structures that might be around either
	      ;; have special format/display stuff, or
	      ;; conversions to general list form
	      ((typep x 'symbol) (if x x 'False)) ;; nil is False
	      ;;might want to break out numbers by type, better.
	      ;; here we worry only about complex..
	      ((typep x '(and number (not complex)))
		   (if (minusp x) (minusformatter (abs x)) x))
				  
	      ((typep x 'rat) (BuildFormat(outof-rat x)))
	      ((typep x 'complex)
	       (complexnumformatter x))

	      ;; some other kind of atom  (what? maybe string?)
	      (t x)))
   ((atom (car x))
    (let* ((op (car x))
	     (fun (get op 'formatter)))
	     (if fun
		 (funcall fun x) 
	       (deflt-buildformat x))))
   (t ;; car is not an atom. a fancy operator then, Perhaps (Derivative 1)
    (deflt-buildformat-op x))))



;;  deflt-buildformat:
;;          If we do not know anything else about a given function (that is,
;;          it is not one of plus, times, dot etc.), deflt-buildformat 
;;          (default-buildformat) will take care of it.  In short, 
;;          default-buildformat handles all general functions f[x].
;;
;;          For example, it converts (f x y z) to
;;
;;          (HORIZONTALFORM 10 1 0 0 F 260 LEFT (F "[" X ", " Y ", " Z "]"))

(defun deflt-buildformat (x)
  (let ((op (car x))
	(width 0)
	(maxtoph 1)
        (maxbotmh 0)
	(hoffset 0)
	(voffset 0)
	(ls nil)
	(heightpacket nil)
	ret_format)
    (do ((args (cdr x) (cdr args)))
	((null args)
	 (MakeHForm (+ width (atomwidth op))
		    (+ maxtoph maxbotmh) hoffset voffset op
		    (prec op) 'left
		    `(,op "[",@(cdr (nreverse ls)),"]")))
	(setq ret_format (BuildFormat (car args)))
	(cond ((atom ret_format)
	       (incf width (+ (atomwidth ret_format) 2))
	       (setq ls `( ,ret_format ", ",@ls)))
	      (t
	       (setq heightpacket (TopBotHs ret_format maxtoph maxbotmh))
	       (setq maxtoph (car heightpacket))
	       (setq maxbotmh (cdr heightpacket))
	       (incf width (+ (formatstruct-width  ret_format) 2))
	       (setq voffset (max  voffset (formatstruct-voffset ret_format)))
	       (incf hoffset (formatstruct-hoffset ret_format))
	       (setf ls `( ,ret_format ", "  ,@ls))
	       )))))

(defun deflt-buildformat-op (x)
  (let ((op (BuildFormat(car x)))
	(width 0)
	(maxtoph 1)
        (maxbotmh 0)
	(hoffset 0)
	(voffset 0)
	(ls nil)
	(heightpacket nil)
	ret_format)
    (do ((args (cdr x) (cdr args))) ;; also format "op"
	((null args)
	 (MakeHForm (+ width (formatstruct-width op))
		    (+ maxtoph maxbotmh) hoffset voffset (car x)
		    260  'left ;; will 260 do??
		    `(,op "[",@(cdr (nreverse ls)),"]")))
	(setq ret_format (BuildFormat (car args)))
	(cond ((atom ret_format)
	       (incf width (+ (atomwidth ret_format) 2))
	       (setq ls `( ,ret_format ", ",@ls)))
	      (t
	       (setq heightpacket (TopBotHs ret_format maxtoph maxbotmh))
	       (setq maxtoph (car heightpacket))
	       (setq maxbotmh (cdr heightpacket))
	       (incf width (+ (formatstruct-width  ret_format) 2))
	       (setq voffset (max  voffset (formatstruct-voffset ret_format)))
	       (incf hoffset (formatstruct-hoffset ret_format))
	       (setf ls `( ,ret_format ", "  ,@ls))
	       )))))

;;  listformatter:
;;          This function handle things like {a,b,c}.  It takes
;;          (list a b c) and returns
;;
;;          (HORIZONTALFORM 9 1 0 0 SEQUENCE 1000 NONE ("{" A ", " B ", " C "}"))

(defun listformatter (x)
  (let ((width 0)
	(maxtoph 1)
        (maxbotmh 0)
	(hoffset 0)
	(voffset 0)
	(ls nil)
	(heightpacket nil)
	ret_format)
    (do ((args (cdr x) (cdr args)))
	((null args)
	 (MakeHForm width
		    (+ maxtoph maxbotmh) hoffset voffset 'Sequence
		    (prec 'Sequence) 'none
		    `("{",@(cdr (nreverse ls)),"}")))
	(setq ret_format (BuildFormat (car args)))
	(cond ((atom ret_format)
	       (incf width (+ (atomwidth ret_format) 2))
	       (setq ls `( ,ret_format ", ",@ls)))
	      (t
	       (setq heightpacket (TopBotHs ret_format maxtoph maxbotmh))
	       (setq maxtoph (car heightpacket))
	       (setq maxbotmh (cdr heightpacket))
	       (incf width (+ (formatstruct-width  ret_format) 2))
	       (setq voffset (max  voffset (formatstruct-voffset ret_format)))
	       (incf hoffset (formatstruct-hoffset ret_format))
	       (setf ls `( ,ret_format ", "  ,@ls))
	       )))))


;;  dotformatter:
;;          This functions handles a.b.c .  It takes (Dot a b c)
;;          and returns
;;
;;          (HORIZONTALFORM 9 1 0 0 DOT 210 NONE (A " . " B " . " C))

(defun dotformatter (x)
  (let ((width 0)
	(maxtoph 1)
        (maxbotmh 0)
	(hoffset 0)
	(voffset 0)
	(ls nil)
	(heightpacket nil)
	ret_format)
    (do ((args (cdr x) (cdr args)))
	((null args)
	 (MakeHForm (- width 3)
		    (+ maxtoph maxbotmh) hoffset voffset 'Dot
		    (prec 'Dot) 'none
		    (cdr (nreverse ls))))
	(setq ret_format (BuildFormat (car args)))
	(cond ((atom ret_format)
	       (incf width (+ (atomwidth ret_format) 3))
	       (setq ls `( ,ret_format " . ",@ls)))
	      (t
	       (if (lessprec ret_format 'Dot)
		   (setq ret_format (parenformatter ret_format)))
	       (setq heightpacket (TopBotHs ret_format maxtoph maxbotmh))
	       (setq maxtoph (car heightpacket))
	       (setq maxbotmh (cdr heightpacket))
	       (incf width (+ (formatstruct-width  ret_format) 3))
	       (setq voffset (max  voffset (formatstruct-voffset ret_format)))
	       (incf hoffset (formatstruct-hoffset ret_format))
	       (setf ls `( ,ret_format " . " ,@ls))
	       )))))


(defun ruleformatter(x) (genformatter x 'Rule))

(setf (get 'Rule 'stringsym) " -> ")
(setf (get 'Rule 'stringsymlen) 4)

(defun andformatter(x)(genformatter x 'And))
(setf (get 'And 'stringsym) " && ")
(setf (get 'And 'stringsymlen) 4)
(setf (get 'And 'stringprec) 215)
(setf (get 'And 'formatter) 'andformatter)

(defun orformatter(x)(genformatter x 'Or))
(setf (get 'Or 'stringsym) " || ")
(setf (get 'Or 'stringsymlen) 4)
(setf (get 'Or 'stringprec) 214)
(setf (get 'Or 'formatter) 'orformatter)

;; this will format most infix forms (binary, n-ary) from declarative info

(defun genformatter (x head)
  (let ((width 0)
	(maxtoph 1)
        (maxbotmh 0)
	(hoffset 0)
	(voffset 0)
	(ls nil)
	(heightpacket nil)
	(sym (get head 'stringsym))
	(len (get head 'stringsymlen))
	     
	ret_format)
    (do ((args (cdr x) (cdr args)))
	((null args)
	 (MakeHForm (- width len)
		    (+ maxtoph maxbotmh) hoffset voffset head
		    (prec head) 'none
		    (cdr (nreverse ls))))
	(setq ret_format (BuildFormat (car args)))
	(cond ((atom ret_format)
	       (incf width (+ (atomwidth ret_format) len))
	       (setq ls `( ,ret_format  ,sym ,@ls)))
	      (t
	       (if (lessprec ret_format head)
		   (setq ret_format (parenformatter ret_format)))
	       (setq heightpacket (TopBotHs ret_format maxtoph maxbotmh))
	       (setq maxtoph (car heightpacket))
	       (setq maxbotmh (cdr heightpacket))
	       (incf width (+ (formatstruct-width  ret_format) len))
	       (setq voffset (max  voffset (formatstruct-voffset ret_format)))
	       (incf hoffset (formatstruct-hoffset ret_format))
	       (setf ls `( ,ret_format ,sym ,@ls))
	       )))))


;;  plusformatter:
;;          This function handles a+b+c .  It converts (Plus a b c)
;;          into
;;
;;          (HORIZONTALFORM 9 1 0 0 PLUS 140 NONE (A " + " B " + " C))

(defun plusformatter (x)
  (let ((width 0)
	(hoffset 0)
	(voffset 0)
	(ls nil)
	(maxtoph 1) 
	(maxbotmh 0)
	(heightpacket nil)
	ret_format)
    (do ((args (cdr x) (cdr args)))
	((null args)
	 (MakeHForm (- width 3);; adjust spacing
		    (+ maxtoph maxbotmh) hoffset voffset 'Plus
		    (prec 'Plus)
		    'none (cdr (nreverse ls))))
	(setq ret_format (BuildFormat (car args)))
	(cond ((atom ret_format)
	       (incf width (+ (atomwidth ret_format) 3))
	       (setq ls `(, ret_format, " + ",@ls)))
	      ;; beware of minuses like -x
	      ;; case 1: if a plus exp begins with a minus exp, we do NOT
	      ;; change the form of that minus exp
	      ((equal (formatstruct-op ret_format) 'Minus)
	       (cond ((equal args (cdr x))
		      (incf width (+ (formatstruct-width ret_format) 3))
		      (setq heightpacket (TopBotHs ret_format maxtoph maxbotmh))
		      (setq maxtoph (car heightpacket))
		      (setq maxbotmh (cdr heightpacket))
		      (setq ls `(, ret_format, " - ",@ls)))
		     (t
		      (let ((ham (cadr (formatstruct-ls ret_format))))
			(cond ((atom ham)
			       (incf width (+ (atomwidth ham) 3)))
			      ;; check if ham is parenthesized, handle cases like
			      ;; a - b c which should not become a - (b c)
			      (t
			       (if (equal (formatstruct-op ham) 'Sequence)
				   (let ((noparenham (cadr (formatstruct-ls ham))))
				     (if (and (not (lessprec noparenham 'Plus))
					      ;; fix a-(b-c) case
					      (not (equal (formatstruct-op noparenham) 'Plus)))
					 (setq ham noparenham))))
			       (incf width (+ 3 (formatstruct-width ham)))
			       (setq heightpacket (TopBotHs ham maxtoph maxbotmh))
			       (setq maxtoph (car heightpacket))
			       (setq maxbotmh (cdr heightpacket))
			       (incf hoffset (formatstruct-hoffset ham))
			       (setf voffset (max voffset (formatstruct-voffset ham)))))
			(setq ls `(, ham, " - ",@ls))))))
	      ;; Non-minus stuff
	      (t
	       (incf width (+  3 (formatstruct-width ret_format)))
	       (setq heightpacket (TopBotHs ret_format maxtoph maxbotmh))
	       (setq maxtoph (car heightpacket))
	       (setq maxbotmh (cdr heightpacket))
	       (incf hoffset (formatstruct-hoffset ret_format))
	       (setf voffset (max voffset (formatstruct-voffset ret_format)))
	       (setq ls `(, ret_format, " + ",@ls)))))))



;;  timesformatter:
;;          It takes (times a b) and returns
;;
;;          (HORIZONTALFORM 3 1 0 0 TIMES 150 NONE (A " " B))

(defun timesformatter (x)
  (let ((width 0)
	(hoffset 0)
	(voffset 0)
	(ls nil)
        (maxtoph 1)
        (maxbotmh 0)
        (heightpacket nil)
	ret_format
	(signs 0) ;; handle cases like (-x) (-z) (-z)
	(x (TimesReorg x)) ;; reorganize x to a better form.
	)
    (cond
     ;; If the times in fact stands for a Divide expression
     ((IsDivide x) (divideformatter x))
     ;; check for cases like (Times -1 Y ...), let minusformatter handle it
     ;; we'd have to change this for other kinds of negatives, e.g. bigfloats.
     ((and(typep (cadr x) '(and number (not complex)))(minusp (cadr x)))
      
      (if (and (equal (cadr x) -1)(null (cdddr x)))
	  (minusformatter (caddr x))
	;; else modify its lisp form to suit the routine
	(minusformatter `(Times ,(- (cadr x)),@ (cddr x)))))
      ;; if no negative number, proceed as usual
     (t
      (do ((args (cdr x) (cdr args)))
	  ((null args)
	   ;; if odd number of minuses is encountered in this times exp
	   ;; then pass to minusformatter
	   (if (oddp signs)
	       (let ((ret_form (MakeHForm (- width 1);; adjust spacing
					  (+ maxtoph maxbotmh) hoffset voffset
					  'Times (prec 'Times) 'none
					  (cdr (nreverse ls)))))
		 (if (lessprec ret_form 'Minus)
		     (setq ret_form (parenformatter ret_form)))
		 (MakeHForm (+ width 2) (+ maxtoph maxbotmh) hoffset voffset
			    'Minus (prec 'Minus)
			    'left `(,"-",ret_form)))
	     (MakeHForm (- width 1);; adjust spacing
			(+ maxtoph maxbotmh) hoffset voffset
			'Times (prec 'Times) 'none
			(cdr (nreverse ls)))))
	  (setq ret_format (BuildFormat (car args)))
	  ;; count minuses, extract +ve form from it if necessary
	  ;; is this necessary?? rjf 1/91
;;	  (format t "~%testing ~s" (formatstruct-op ret_format))
	  (cond ((and (not (atom ret_format))
		      (eq (formatstruct-op ret_format) 'Minus))
		 (setq ret_format
		       (cadr (formatstruct-ls ret_format)))
		 (setq signs (1+ signs))))
	  (cond ((atom ret_format)
		 (incf width (+ (atomwidth ret_format) 1)))
		(t
		 (if (lessprec ret_format 'Times)
		     (setq ret_format (parenformatter ret_format)))
		 (incf width (+ 1 (formatstruct-width ret_format)))
		 (setq heightpacket (TopBotHs ret_format maxtoph maxbotmh))
		 (setq maxtoph (car heightpacket))
		 (setq maxbotmh (cdr heightpacket))
		 (incf hoffset (formatstruct-hoffset ret_format))
		 (setf voffset (max voffset (formatstruct-voffset ret_format)))))
	  (setq ls `( ,ret_format ," " ,@ls))
	  )))))


;;  TimesReorg:
;;         Reorganize the times expression to form a proper
;;         Divide expression (Times exp (power exp -1)) if
;;         necessary.

(defun TimesReorg(x) x) ;; leave arg alone.

;; This was written by Derek Lai
;; keep this in reserve.  I think it's unnecessary -- RJF.
#+ignore (defun TimesReorg (x)
  (let ((numerList nil)
	(denomList nil))
    (do ((args (cdr x) (cdr args)))
	((null args)
	 (cond ((null numerList)
		(cond ((> (length denomList) 1)
		       (setq denomList (cons 'Times denomList)))
		      (t
		       (setq denomList (car denomList))))
		(setq denomList (list 'Power denomList '-1))
		(cons 'Times (cons 1 (list denomList))))
	       ((null denomList)
		(cond ((cdr numerList)
		       (setq numerList (cons 'Times numerList)))
		      (t
		       (setq numerList (car numerList)))))
	       (t
                (cond ((cdr denomList)
                       (setq denomList (cons 'Times denomList)))
                      (t
                       (setq denomList (car denomList))))
		(setq denomList (list 'Power denomList -1))
		(cond ((> (length numerList) 1)
                       (setq numerList (cons 'Times numerList)))
                      (t
                       (setq numerList (car numerList))))
		(cons 'Times (append (list numerList) (list denomList))))))
	(let ((ham (car args)))
	  (cond ((atom ham)
		 (setq numerList (append numerList (list ham))))
		((and (equal (car ham) 'Power)
		      (equal (caddr ham) '-1))
		 (setq denomList (append denomList (list (cadr ham)))))
		(t
		 (setq numerList (append numerList (list ham)))))))))

;;  powerformatter:
;;         This function takes care of cases like e^x.  It takes (POWER E X)
;;         and returns
;;
;;         (HORIZONTALFORM 2 2 0 0 POWER 190 RIGHT
;;              (E (VERTICALFORM 1 1 0 -1 SUPERSCRIPT 260 NONE X)))

(defun powerformatter (x)
  (let ((base_ret_format (BuildFormat (cadr x)))
	(expo_ret_format (BuildFormat (caddr x)))
	(expo_form nil))
    (if (atom expo_ret_format)
	(setq expo_form (MakeVForm (atomwidth expo_ret_format)
				   1 0 -1 'Superscript (prec 'Superscript)
				   'none
				   expo_ret_format))
      (setq expo_form (MakeVForm (formatstruct-width expo_ret_format)
				 (formatstruct-height expo_ret_format)
				 0 -1 'Superscript (prec 'Superscript)
				 'none
				 expo_ret_format)))
    (cond ((atom base_ret_format)
	   (MakeHForm (+ (atomwidth base_ret_format)
			 (formatstruct-width expo_form))
		      (+ 1 (formatstruct-height expo_form))
		      0 0 'Power (prec 'Power) 'right `(, base_ret_format, expo_form)))
	  (t
	   (let ((paren_base_ret_format
		  (parenformatter base_ret_format)))
	     ;; find out whether expo is higher than numerator
	     (let ((toph (max (- (formatstruct-height base_ret_format)
				 (formatstruct-voffset base_ret_format))
			      (+ 1 (formatstruct-height expo_form)))))
	       (MakeHForm (+ (formatstruct-width expo_form)
			     (formatstruct-width paren_base_ret_format))
			  (+ toph (formatstruct-voffset paren_base_ret_format))
			  0 (formatstruct-voffset
			     paren_base_ret_format) 'Power (prec 'Power) 'right
			     `(, paren_base_ret_format, expo_form))))))))



;;  realformatter:
;;          This function takes a Lisp prefix form of a real number
;;          and convert it to a real number string.

(defun realformatter (x)
  (let* ((p1 (cadr x)) (p2 (caddr x))
	 (temp (format nil "~D.~D" p1 p2)))
    temp))



;;  parenformatter:
;;          Wrap a given formatstruct with parentheses.

(defun parenformatter (f)
  (MakeHForm (+ (formatstruct-width f) 2)
	     (formatstruct-height f)
	     0
	     (formatstruct-voffset f)
	     'Sequence (prec 'Sequence) 'none `(,"(", f, ")")))
		  


;;  minusformatter:
;;          This function takes X and makes
;;          a horizontal minus form (that is, for - X).
;;
;;          (HORIZONTALFORM 2 1 0 0 MINUS 170 LEFT ("-" X))

(defun minusformatter (x)
  (let ((ret_form (BuildFormat x)))
    (cond ((atom ret_form)
	   (MakeHForm (+ 1 (atomwidth ret_form))
		      1 0 0 'Minus (prec 'Minus) 'left `(,"-", ret_form)))
	  (t
	   (if (< (prec (formatstruct-op ret_form)) (prec 'Minus))
	       (setq ret_form (parenformatter ret_form)))
	   (MakeHForm (+ 1 (formatstruct-width ret_form))
		      (formatstruct-height ret_form)
		      0
		      (formatstruct-voffset ret_form)
		      'Minus (prec 'Minus) 'left `(,"-", ret_form))))))



;;  IsDivide:
;;          Checks if a Lisp prefix form expression in fact
;;          corresponds to a division expression.
;;          For example, IsDivide returns TRUE with the following
;;          input expression:
;;
;;          (TIMES A (POWER B -1))

(defun IsDivide (x)
  (if (/= (length x) 3)
      nil
    (let ((bool nil) (p1 (cadr x)) (p2 (caddr x)))
      (if (not (atom p2))
	  (if (and (equal (car p2) 'Power)
		   (equal (caddr p2) '-1))
	      (setq bool t)))
      ;; the first part of x must be a non -1 power
      (if (not (atom p1))
	  (if (and (equal (car p1) 'Power)
		   (equal (caddr p1) '-1))
	      (setq bool nil)))
      bool)))



;;  divideformatter:
;;          In general, after a given Lisp prefix is identified as 
;;          a division expression by the function "IsDivide" (above),
;;          it is passed to divideformatter.  For example, it converts
;;          (TIMES A (POWER B -1)) to
;;
;;          (VERTICALFORM 1 3 0 1 DIVIDE 160 LEFT
;;                                  (A (REPEATEDSTRING "-" 1) B))

(defun divideformatter (x)
  (let* ((p1 (cadr x)) (p2 (caddr x))
	 (retf1 (BuildFormat p1))
	 (retf2 
	  (let ((temp (BuildFormat (cadr p2))))
	    (if (DivideFormp temp) ;; due to associativity
		(parenformatter temp)
	      temp)))
	 (w1 (formatwidth retf1))
	 (w2 (formatwidth retf2))
	 (barwidth (max w1 w2)))
    ;; stuff space
    (if (> (abs (- w1 w2)) 1)
	(if (> w1 w2)
	    (setq retf2 (StuffSpace retf2 barwidth))
	  (setq retf1 (StuffSpace retf1 barwidth))))
    (MakeVForm barwidth 
	       (+ 1 (formatheight retf1) (formatheight retf2))
	       0 (formatheight retf2)
	       'Divide (prec 'Divide) 'left
	       `(, retf1, (MakeRepStr barwidth "-") ,retf2))))

;; handle complex numbers only.
;; perhaps this should be user-defined? (Could be over-ridden by
;; an appropriate mechanism like ComplexFormatter[] ... )

(defun complexnumformatter (x)
  (let ((imag (cond ((= (imagpart x) 0) nil)
		    ((= (imagpart x) 1) 'I)
		    (t `(Times ,(imagpart x) I)))))
    (BuildFormat (cond ((null imag)(realpart x))
		       ((= 0 (realpart x)) imag)
		       (t (list 'Plus (realpart x)imag))))))


;; handle the output of "Set" forms

(setf (get 'Set 'stringsym) " = ")
(setf (get 'Set 'stringsymlen) 3)

;; based on dotformatter

(defun setformatter (x)
  (let ((width 0)
	(maxtoph 1)
        (maxbotmh 0)
	(hoffset 0)
	(voffset 0)
	(ls nil)
	(heightpacket nil)
	ret_format)
    (do ((args (cdr x) (cdr args)))
	((null args)
	 (MakeHForm (- width 3)
		    (+ maxtoph maxbotmh) hoffset voffset 'Set
		    (prec 'Set) 'none
		    (cdr (nreverse ls))))
	(setq ret_format (BuildFormat (car args)))
	(cond ((atom ret_format)
	       (incf width (+ (atomwidth ret_format) 3))
	       (setq ls `( ,ret_format " = ",@ls)))
	      (t
	       (if (lessprec ret_format 'Set)
		   (setq ret_format (parenformatter ret_format)))
	       (setq heightpacket (TopBotHs ret_format maxtoph maxbotmh))
	       (setq maxtoph (car heightpacket))
	       (setq maxbotmh (cdr heightpacket))
	       (incf width (+ (formatstruct-width  ret_format) 3))
	       (setq voffset (max  voffset (formatstruct-voffset ret_format)))
	       (incf hoffset (formatstruct-hoffset ret_format))
	       (setf ls `( ,ret_format " = " ,@ls))
	       )))))


;;we can do this for now, since the results are similar
;;for formatting + and *.  However the precedences are different.
;; also, perhaps the formatting symbol for Times is merely adjacency.


	       


;;  StuffSpace:
;;          This function puts in spaces as, say,
;;          (RepeatedString " " 6).

(defun StuffSpace (f framewidth)
  (let ((numspace (floor (- framewidth (formatwidth f)) 2)))
  (MakeHForm (+ (formatwidth f) numspace)
	     (formatheight f)
	     0
	     (if (atom f)
		 0
	       (formatstruct-voffset f))
	     'Sequence (prec 'Sequence) 'none
	     `(, (MakeRepStr numspace " "), f))))



;;  MakeRepStr:
;;          It constructs repeated strings.

(defun MakeRepStr (x symb)
  (list 'RepeatedString symb x))