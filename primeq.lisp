;;; -*- Mode: LISP; Syntax: Common-lisp; Package: USER -*-

;;;; Modular Arithmetic

;;; References
;;;   Robert Solovay and Volker Strassen,
;;;     "A Fast Monte-Carlo Test for Primality,"
;;;     SIAM Journal on Computing, 1977, pp 84-85.
;;;   R. L. Rivest, A. Shamir, and L Adleman
;;;     "A Method for Obtaining Digital Signatures and Public-Key Cryptosystems"
;;;     Communications of the ACM,
;;;     Vol 21, Number 2, February 1978, pages 120-126

;;;  (c) Copyright Gerald Roylance 1983, 1984, 1985, 1986
;;;      All Rights Reserved.
;;;  This file may be distributed noncommercially provided
;;;  that this notice is not removed.

;;; modified slightly by RJF  2/5/91
;;;; Greatest Common Divisor Algorithms

;;; find A and B such that
;;;    A * X + B * Y = Z

;;; initial equations:
;;;    1 * X + 0 * Y = X
;;;    0 * X + 1 * Y = Y

(defun gcd-extended (X Y)
  (do ((A1 1 A2)
       (B1 0 B2)
       (Z1 X Z2)
       (A2 0 (- A1 (* d A2)))
       (B2 1 (- B1 (* d B2)))
       (Z2 Y (- Z1 (* d Z2)))
       (d  0))
      ((zerop Z2) (values A1 X B1 Y Z1))
    (setq d (floor Z1 Z2))
    ))

;;; find b such that a * b is congruent to 1  (modulo modulus)

(defun modinv (a modulus)
  (multiple-value-bind (a1 x b1 y z1)
		       (gcd-extended a modulus)
    (if (= z1 1) a1
	(error "MODINV:  no inverse: modulus not prime")
	)))


;;;; (EXPT A N) MOD M

(defun modpower (number expon modulus)
  (do ((exp  expon  (floor exp 2))		; speedier to break into
						;  2**24 bit chunks?
       (sqr  number (mod (* sqr sqr) modulus))
       (ans  1))
      ((zerop exp) ans)
    (if (oddp exp)
	(setq ans (mod (* ans sqr) modulus)))))


;;; Generate a random bignum that is L bits long

;;; generate random substrings of say 20 bits and
;;; paste them together to make a longer random string
;;; of course, this is a crock

(defun random-big-1 (length)
  (do ((l    length (- l k))			; number of bits to make
       (k    0)					; number of bits to make this pass
       (bits 0))				; rand bits so far
      ((<= l 0) bits)
    (declare (fixnum l k))
    (setq k (min l 20.))
    (setq bits (+ (* bits (ash 1 k))		; shift left k bits
		  (random (ash 1 k))))		; add in k bits
    ))

;;;; Jacobi-Symbol

;;; The hairy exponent stuff here is just a hack to look
;;; at the lsbs of the bignums.  It has been hacked here
;;; to make it moderately fast without bumming it beyond
;;; recognition.

;;; the Jacobi-Symbol is always +1, -1, or 0

;;; (-1)**exp the easy way....
;;;
(defmacro jacobi-expt-1 (exp)
  `(if (oddp ,exp) -1 1))

;;; version from Sussman's notes
;;;
(defun JacobiSymbol (P Q)
  (let ((PP (mod P 16.))			; only need low order bits for
	(QQ (mod Q 16.)))			;  sometimes.  Used in place of
    (declare (fixnum PP QQ))			;  P or Q where it matters

    (cond ((equal P 0) 0)			; not in GJS notes
	  ((equal P 1) 1)
	  ((oddp PP)
	   (* (JacobiSymbol (mod Q P) P)
	      (jacobi-expt-1 (truncate (* (- PP 1) (- QQ 1)) 4))))  ;was /
	  (t
	   (* (JacobiSymbol (floor P 2) Q)
	      (jacobi-expt-1 (truncate (- (* QQ QQ) 1) 8))))))) ; was /


;;;; Prime Number Test:  Solovay-Strassen

;;; Solovay-Strassen Prime Test
;;;   if n is prime, then J(a,n) is congruent mod n to a**((n-1)/2)
;;;
(defun prime-test-1 (a n)
  (and (= (gcd a n) 1)
       (= (mod (- (jacobi-symbol a n) (modpower a (floor (- n 1) 2) n)) n) 0)))

;;; checks if n is prime.  Returns nil if not prime. True if (probably) prime.
;;;   probability of a mistake = (expt 2 (- trials))
;;;     choosing TRIALS=30 should be enough
;;;
(defun PrimeQ (n &optional (trials 30.))
  (setq n (abs n))
  (cond ((< n 2) nil)
	((= n 2) 'True)
	((= n 3) 'True)
	((and (> n 100)				; cheap test
	      (not (= 1 (gcd n 223092870 
			     ;;= (* 2.  3.  5.  7. 11 13 17 19 23)
			     ))))
	 nil)
	(t
	 (do ((i 0 (1+ i))
	      (a (random n) (random n)))
	     ((> i trials) 'True) ;probably prime
	   (declare (fixnum i))
	   (cond ((zerop a)			; this test is no good
		  (setq i (1- i)))
		 ((not (prime-test-1 a n))
		  (return nil)))))))



