; leftpad.lisp - some definitions and proofs in ACL2 about a leftpad()
; function.

; Author: Keshav Kini <keshav.kini@gmail.com>
; Date: 2020-02-17

(in-package "ACL2")

; ==============================================================================

; Here is a simple recursive definition of leftpad().  ACL2 is an untyped
; language, so this function is total (in the ACL2 logic, though not
; necessarily at runtime) with c, n, and s being any ACL2 values.

(defun leftpad (c n s)
  (if (< (len s) (nfix n))
      (cons c (leftpad c (- n 1) s))
    s))

; Property #1: The length of leftpad(c, n, s) is equal to max(len(s), n).

; Note that in the conclusion, n is written as (NFIX N), which coerces it to a
; natural number.  The alternative is to add a hypothesis (NATP N), requiring
; that n is a natural number to start with, but phrasing it this way likely
; makes it more useful as a rewrite rule since it will always fire and simplify
; away the call to leftpad without needing to backchain and prove the (NATP N)
; hypothesis first.

(defthm len-of-leftpad
  (equal (len (leftpad c n s))
         (max (len s) (nfix n))))

; A dummy function whose induction scheme will be used in proving subsequent
; theorems.

(defun induction-scheme (i c n s)
  (declare (xargs :measure (nfix n))
           (irrelevant c))
  (and (natp i)
       (natp n)
       (< (len s) n)
       (induction-scheme (- i 1) c (- n 1) s)))

; Property #2: The i-th character of leftpad(c, n, s) is equal to c if i is
; less than n - len(s), i.e. if i points to the "prefix" of leftpad(c, n, s).

(defthm prefix-of-leftpad
  (implies (and (natp n)
                (natp i)
                (< i (- n (len s))))
           (equal (nth i (leftpad c n s))
                  c))
  :hints (("Goal" :induct (induction-scheme i c n s))))

; Property #3: The i-th character of (leftpad c n s) is equal to the (i -
; max(0, (n - len(s))))-th character of s if i is greater than or equal to n -
; len(s), i.e. if i points to the "suffix" of leftpad(c, n, s).

(defthm suffix-of-leftpad
  (implies (and (natp n)
                (natp i)
                (>= i (- n (len s))))
           (equal (nth i (leftpad c n s))
                  (nth (- i (max 0 (- n (len s)))) s)))
  :hints (("Goal" :induct (induction-scheme i c n s))))

; Below is NTH-OF-LEFTPAD, a combined formulation of Properties #2 and #3 which
; is phrased as an unconditional (except for type information) rewrite of (NTH
; I (LEFTPAD C N S)) to an if-expression, making it a "splitter rule" that,
; when applied during a proof, will case split on the if-condition.

; This can sometimes be more useful than writing two separate theorems, one
; conditional on some hypothesis P and the other conditional on ~P.  To use one
; of the two separate theorems, ACL2 would either have to be able to prove P or
; ~P at that moment, whereas with the "splitter rule" approach, ACL2 can do the
; case split and move on, and resolve the cases later.

; Note that the induction hint doesn't need to be provided here because ACL2
; uses the already-proven theorems PREFIX-OF-LEFTPAD and SUFFIX-OF-LEFTPAD to
; prove NTH-OF-LEFTPAD without inductive reasoning.

(defthm nth-of-leftpad
  (implies (and (natp n)
                (natp i))
           (equal (nth i (leftpad c n s))
                  (if (< i (- n (len s)))
                      c
                    (nth (- i (max 0 (- n (len s)))) s)))))

; Another formulation of Property #3.  Not very useful as a rewrite rule, since
; (NTH (- (LEN (LEFTPAD C N S)) I) (LEFTPAD C N S)) is unlikely to show up as a
; term needing to be simplified in any proof.  ACL2 uses the already-proven
; theorem LEN-OF-LEFTPAD to help prove this theorem.

(defthm suffix-of-leftpad-2
  (implies (and (natp n)
                (posp i)
                (<= i (len s)))
           (equal (nth (- (len (leftpad c n s)) i) (leftpad c n s))
                  (nth (- (len s) i) s))))

; ==============================================================================

; The leftpad() function we've defined above is not one that we'd want to use
; in practice.  We might want a non-recursive implementation which could be
; faster (especially since our recursion wasn't even tail-recursion).  Also, we
; might want a leftpad() function that actually operated on the native string
; datatype, rather than lists of characters, both for speed reasons and because
; a string value is more likely to be something you'd want to pad than a list
; of characters is.

; ACL2 has a feature called MBE ("must be equal"), where you can define a
; function with two bodies, one which is used as the logical definition of the
; function, and another which is the one that is used in practice to execute
; the function at runtime.  ACL2 will only admit such a definition if it can
; prove that the two bodies are always equal under the assumption that the
; guards of the function are satisfied.  (Guards are a precondition for
; execution that you can specify when defining a function.)

; Below, we define a function FAST-LEFTPAD using the above ideas.

; First we load some useful libraries; these define the functions IMPLODE,
; EXPLODE, STR::CAT, and REPEAT which we'll be using, as well as some useful
; theorems and the computed hint EQUAL-BY-NTHS-HINT.

(include-book "std/strings/coerce" :dir :system)
(include-book "std/strings/cat" :dir :system)
(include-book "std/lists/repeat" :dir :system)
(include-book "std/lists/nth" :dir :system)
(include-book "std/lists/append" :dir :system)

; This is a lemma needed to guard-verify LEFTPAD-STRING, which we will define
; next.

(defthm character-listp-of-repeat-of-characterp
  (implies (characterp c)
           (character-listp (repeat n c)))
  :hints (("Goal" :in-theory (enable repeat))))

; This is a function LEFTPAD-STRING which provides the runtime implementation
; of the FAST-LEFTPAD function we'll eventually create.  Note that this could
; be optimized further if ACL2's subset of Common Lisp included the standard
; Common Lisp function MAKE-STRING; then we could have written (MAKE-STRING
; ... :INITIAL-ELEMENT C) instead of (IMPLODE (REPEAT ... C)), which is likely
; slower.

(defun leftpad-string (c n s)
  (declare (xargs :guard (and (characterp c)
                              (natp n)
                              (stringp s))))
  (str::cat (implode (repeat (nfix (- n (length s))) c)) s))

; This theorem mirrors NTH-OF-LEFTPAD from earlier, and will help us use the
; EQUAL-BY-NTHS proof strategy to prove the equivalence between the logical and
; runtime definitions of FAST-LEFTPAD later by comparing the elements of their
; output at each i-th index.

(defthm nth-of-leftpad-string
  (implies (and (natp n)
                (natp i)
                (characterp c)
                (stringp s))
           (equal (nth i (explode (leftpad-string c n s)))
                  (if (< i (- n (length s)))
                      c
                    (nth (- i (max 0 (- n (length s)))) (explode s))))))

; This lemma is needed to prove the next theorem.

(defthm character-listp-of-leftpad
  (implies (and (characterp c)
                (character-listp s))
           (character-listp (leftpad c n s))))

; This theorem rewrites a call of LEFTPAD on an exploded string to an exploded
; call of LEFTPAD-STRING on the underlying string, which is the main result
; used to justify the use of MBE in the definition of FAST-LEFTPAD.

(defthm leftpad-string-leftpad
  (implies (and (characterp c)
                (natp n)
                (stringp s))
           (equal (leftpad c n (explode s))
                  (explode (leftpad-string c n s))))
  :hints ((equal-by-nths-hint)))

; Here, finally, is the definition of FAST-LEFTPAD.

(defun fast-leftpad (c n s)
  (declare (xargs :guard (and (characterp c)
                              (natp n)
                              (stringp s))))
  (mbe :exec (leftpad-string c n s)
       :logic (implode (leftpad c n (explode s)))))
