;; -*- mode: common-lisp; package: mma; -*-
;;; display package for pseudo-mathematica
;;; written by Derek Lai, rewritten in parts by Richard Fateman
;;; (c) 1990, 1991, Richard J. Fateman, Derek Lai.

;;(provide 'disp1)
(in-package :mma)
;;(require "mma")
;;(export '(COL disp dispstruct))

(proclaim '(optimize (speed 3)(safety 0)))
;; number of columns of screen
;;; % COL should be a parameter obtained from the CL system
(defvar COL 65)


(defstruct dispstruct
  (str nil)
  (x 0 :type fixnum) (y 0 :type fixnum))


;; testing display routine
(defun td ()
  (disp (BuildFormat (mma::p)))
  (terpri)
  (terpri)
  (td))

(defvar stream t "default is to send output to display")


(defun disp (form &optional (stream t))
  (let ((LIST nil))
	(format stream "~%")
	(cond ((atom form)
	       (if (<= (atomwidth form) COL)
		   (format stream "~a" form)
		 (let ((hform (MakeHForm (atomwidth form)
					 1 0 0 nil nil nil form)))
		   (TestAndDisplay (disp-helper hform 1 1 nil) hform))))
	      (t
	       (setq LIST (disp-helper form 1
					(formatstruct-height form)
					LIST))
	       (TestAndDisplay LIST form)))))


(defun disp-list (form)
  (let ((LIST nil))
	(format stream "~%")
	(cond ((atom form) form)
	      (t
	       (setq LIST (disp-helper form 1
					(formatstruct-height form)
					LIST))
	       (setq LIST (sort LIST #'listyorderp))
	       (setq LIST (sort LIST #'listxorderp))))))



(defun disp-helper (form x y l)
  (let ((f nil) (vof 0))
    (cond ((or (VFormp form) (HFormp form))
	   (setq f (formatstruct-ls form))
	   (setq vof (formatstruct-voffset form)))
	  (t
	   (setq f form)))
    (cond ((VFormp form)
	   (cond ((DivideFormp form)
		  (setq l (disp-helper (car f) x (- y (+ 1 vof)) l))
		  (setq l (AppendList x (- y vof)
				      (make-string
				       (cadr (cdadr f)) :initial-element
				       #\-) l))
		  (disp-helper (caddr f) x y l))
		 (t ;; should be due to exponents
		  (setq y (1- y))

	  (disp-helper f x (- y vof) l))))
	  ((RepStrFormp form)
	   (AppendList x y (make-string (caddr form) :initial-element
			    (character (cadr form))) l))
	  (t
	   (do ((args (if (atom f)
			  (list f)
			f) (cdr args)))
	       ((null args) (return l))
	       (let ((ham (car args)))
		 (cond ((atom ham)
			(setq l (AppendList x (- y vof) ham l))
			(setq x (+ x (atomwidth ham))))
		       ((RepStrFormp ham)
			(setq l (disp-helper ham x (- y vof) l))
			(setq x (+ x (caddr ham))))
		       (t
			(setq l (disp-helper ham x
					     (+ (- y vof)
						(formatstruct-voffset ham))
					     l))
			(setq x (+ x (formatstruct-width ham)))))))))))


(defun AppendList (x y ham l)
  ;; do I believe this is really safe? I think it is
  ;; a better way would have been to cons up a list and
  ;; (n)reverse it at the end (if necessary)... 1/23/91 RJF
  (nconc l (list (make-dispstruct :str ham :x x :y y)))
  ;; (append l (list (make-dispstruct :str ham :x x :y y)))
  )


(defun listyorderp (a b)  (< (the fixnum (dispstruct-y a))
			     (the fixnum (dispstruct-y b))))

(defun listxorderp (a b)  (< (the fixnum (dispstruct-x a))
			     (the fixnum (dispstruct-x b))))

;; Breaklinex and display.  Right now COL is the limit per line
;; 2 tests are performed:  1) if the dls is shorter than COL chars,
;; display it right away and exit.  2) if not, breaklines, "compress"
;; the Vertical forms if necessary.

(defun TestAndDisplay (dls form)
  (setq dls (sort dls #'listyorderp))
  (cond ((< (formatwidth form) COL)
	 (FinalDisplay dls (- (formatheight form)
			      (formatstruct-voffset form)) ))
	(t
	 (let (brkptset)
	   (loop
	    (setq brkptset (GetBrkPtSet (copy-list dls) form))
	    (when brkptset
		  (Display dls brkptset (- (formatheight form)
					   (formatstruct-voffset form)))
		  (return 'DONE))
	    (setq dls (disp-list (Compress form))))))))


;; brkptset is in the form of (74 145 224 ...)
;; dls will get shorter and shorter within this procedure
;; The function Compressible is not written yet.

(defun GetBrkPtSet (dls form)
  (let ((cursor 1) (cPlus -1) (cMinus -1) (cTimes -1)
	(cComma -1) (cDot -1) (brkptset nil))
    (setq  dls (sort dls #'listyorderp))
    (setq  dls (sort dls #'listxorderp))
    (loop
     (when (null dls) (return brkptset))
     (setq cPlus  (GetClosest " + " dls
			      (- (formatheight form)
				 (formatstruct-voffset form)) cursor))
     (setq cMinus (GetClosest " - " dls
			      (- (formatheight form)
				 (formatstruct-voffset form)) cursor))
     (setq cComma (GetClosest ", " dls
			      (- (formatheight form)
                                 (formatstruct-voffset form)) cursor))
     (setq cDot (GetClosest " . " dls
                              (- (formatheight form)
                                 (formatstruct-voffset form)) cursor))
     (if (and (< (- cPlus cursor) COL) (< (- cMinus cursor) COL)
	      (< (- cComma cursor) COL) (< (- cDot cursor) COL))
	 (setq cPlus (max cPlus cMinus cComma cDot))
       (setq cPlus (min cPlus cMinus cComma cDot)))
     (setq cTimes (GetClosest " " dls
			      (- (formatheight form)
				 (formatstruct-voffset form)) cursor))
     (cond ((> (- cPlus cursor) COL)
	    (cond ((> (- cTimes cursor) COL)
		   (cond ((Compressible form cursor) (return nil))
			 (t
			  (setq brkptset (append brkptset
						 (list (+ cursor COL))))
			  ;; questionable....
			  (setq cursor (+ cursor COL)))))
		  (t
		   (setq brkptset (append brkptset (list (1+ cTimes))))
		   ;; brute force break
		   (setq cursor (1+ cTimes)))))
	   (t
	    (cond ((= cComma cPlus) ;; then it is cComma in fact
		   (setq brkptset (append brkptset (list (+ cComma 2))))
		   (setq cursor (+ cComma 2)))
		  (t
		   (setq brkptset (append brkptset (list (+ cPlus 3))))
		   (setq cursor (+ cPlus 3))))))
     (setq dls (RmvHead dls cursor)))))


(defun RmvHead (dls cursor)
  (loop
   (when (null dls)
	 (return nil))
   (when (> (dispstruct-x (car dls)) cursor)
	 (return dls))
   (setq dls (cdr dls))))


;; Endpt takes a dispstruct and returns the endpt of it
;; i.e.  the place where the last char of the string lies.

(defun Endpt (dst)
  (- (+ (the fixnum(dispstruct-x dst))
	(the fixnum (atomwidth (dispstruct-str dst)))
	) 1))


;; axis = main axis y-coord
;; Closest sumbolpt (which this function finds) is defined as the place of the first character of
;; " + " , " - " or " "
;; Closest breakpt is defined as the place immediately following these symbols

(defun GetClosest (symb dls yaxis cursor)
  (let (x)
    (declare (fixnum x COL cursor yaxis)
	     (function Endpt (t) fixnum))
    (loop
     (when (null dls) (return x))
     (when (> (- (the fixnum (Endpt (car dls)))
		 cursor)
	      COL)
	   (if x
	       (return x)
	     (return (Endpt (car dls)))))
     (if (and (= (the fixnum (dispstruct-y (car dls))) yaxis)
	      (equal   symb (dispstruct-str (car dls)))
	      (<= (- (Endpt (car dls)) cursor) COL))
	 (setq x (dispstruct-x (car dls))))
     (if (null (cdr dls))
	 (setq x (1+ (Endpt (car dls)))))
     (setq dls (cdr dls)))))

     

;; Compressible is not written yet

(defun Compressible (form cursor)
  nil)


;; Compress is not written yet

(defun Compress (form)
  form)


;; input is an unsorted list and a brkptset
;; not written yet

(defun Display (dls brkptset yaxis)
  (let ((cursor 1) (tempdls nil) (ham1 nil) (ham2 nil) (bksl nil)
	)
    (setq dls (sort dls #'listxorderp))
    (loop
     (when (null dls)
	   (setq tempdls (sort tempdls #'listyorderp))
	   (FinalDisplay tempdls yaxis)
	   (return 'DONE))
     (cond ((>= (Endpt (car dls)) (car brkptset))
	    (cond ((< (dispstruct-x (car dls)) (car brkptset))
		   ;; brute force breakline

		   (setq ham1 (make-dispstruct :str
	       (subseq (format nil "~a"  (dispstruct-str (car dls)))
		       0
		       (- (car brkptset)
			  (dispstruct-x (car dls))))
	       :x (- (dispstruct-x (car dls)) (1- cursor))
	       :y (dispstruct-y (car dls))))
		   (setq bksl (make-dispstruct :str #\\
					       :x (1+ (dispstruct-x ham1))
					       :y (dispstruct-y (car dls))))
		   
		   (setq tempdls (append tempdls (list ham1) (list bksl)))
		   
		   (setq ham2
			 (make-dispstruct 
			  :str
			  (subseq (format nil "~a"
					  (dispstruct-str (car dls)))
				  (- (car brkptset)
				     (dispstruct-x (car dls)))
				  (atomwidth (dispstruct-str (car dls))))
			  :x (car brkptset)
			  :y (dispstruct-y (car dls))))
		   (setq dls (sort (the list (append (list ham2) (cdr dls))) #'listxorderp)))
		  (t
		   (FinalDisplay tempdls yaxis)
		   (terpri)
		   (terpri)
		   (setq tempdls nil)
		   (setq cursor (car brkptset))
		   (if (cdr brkptset)
		       (setq brkptset (cdr brkptset))
		     (setq brkptset (list (+ COL (car brkptset)))))))) ;; set brkptset to some "dont-care" value
	   (t
	    (setq tempdls
		  (append tempdls
			  (list (make-dispstruct :str (dispstruct-str (car dls))
						 :x (- (dispstruct-x (car dls)) (1- cursor))
						 :y (dispstruct-y (car dls))))))
	    (setq dls (cdr dls)))))))

;; Display the final output list.       
;; yaxis isn't used.. 
(defun FinalDisplay (dls yaxis)
  (let (old (x 1) (y 1) )
 (declare (fixnum x y))
     (setq dls (sort (the list dls) #'listyorderp))
     (loop
      (setf (dispstruct-x (car dls)) (dispstruct-x (car dls)))
     (loop (when (>= y (dispstruct-y (car dls)))
		 (return 'done))
	   (format stream "~%")
	   (setq y (1+ y)))
     ;; tab to the right column and print..
     (format stream "~v,0t~a"
	     (1- (setq x (dispstruct-x (car dls))))
	     (dispstruct-str (car dls)))
     (setq old (car dls))
     (setq dls (cdr dls))
     (when (null dls) (return 'done))
     (if (= y (dispstruct-y (car dls)))
	 (setq x (+ x (atomwidth (dispstruct-str old))))
       (setq x 1))))
)





