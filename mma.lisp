;; -*- Mode:Common-Lisp;Package:mma; Base:10 -*-
;; Mock MMA (A Lisp language mathematica-like system)
;;(c) copyright 1990, 1991 by Richard J. Fateman

;; this file should be loaded in at COMPILE time for every file in
;; the mma package.  It should also be loaded in (once) when the
;; mma package is set up.


;; Mathematica, on which this is based,
;; is described in S. Wolfram: Mathematica, a
;; System for Doing Mathematics By Computer, (Addison-Wesley).

;; this line is not quite enough. Need to do, prior to compiling this

(eval-when (compile load eval)
	   #+Allegro(cond((eq *current-case-mode* :case-sensitive-lower))
		(t (set-case-mode :case-sensitive-lower))))

;; obsolete (provide 'mma)

(defpackage :mma (:nicknames "MockMMA") (:use :common-lisp :excl))
(in-package :mma)
;; this next line is not enough.. need to have these macros
;; available at compile time.
;;(declaim (ftype macro ulist uconsm))
;;(load "ucons1")
(defvar built-in-syms
  ;; these are the atoms used by the parser, evaluator, display,
  ;; etc.  They must be the same in each of the separate packages,
  ;; and so each package should be in this package ( :mma).
	  
  '(AddTo Alias And Apply Blank BlankNullSequence BlankSequence 
	  CompoundExpression Condition Delayed Derivative DivideBy Dot
	  Equal Exit 
	  Factorial Factorial2 Function Greater GreaterEqual If In Increment
	  Inequality Integer Less LessEqual List Map MapAll MessageName
	  NonCommutativeMultiply Not Null Optional Or Out Part Pattern
	  PatternTest Plus Power PreDecrement PreIncrement Put PutAppend
	  Real Repeated RepeatedNull Replace ReplaceAll ReplaceRepeated
	  Rule RuleDelayed SameQ Sequence Set SetDelayed Slot SlotSequence
	  SubtractFrom TagSet TagSetDelayed Times TimesBy UnAlias Unequal
	  UnSameQ UnSet UpSet UpSetDelayed $Line  Quote)  ;; we added Quote.
  )

;; from eval
(export '(tl mread1))






