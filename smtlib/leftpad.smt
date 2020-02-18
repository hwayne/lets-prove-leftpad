;
; Proving Leftpad with SMT-LIB and Z3.
;

; The 3 arguments of the leftpad function.
(declare-const s String)
(declare-const n Int)
(declare-const c String)

; The output string i.e. the padded version of the input string.
(declare-const out String)

; A "helper" value that stores the prefix for padding the string.
(declare-const prefix String)

; The max of two integers.
(define-fun max ((x Int) (y Int)) Int (ite (< x y) y x))

; Assumption that 'c' is a single character. There is no character primitive 
; type so we state this assumption explicitly, which is acceptable since this would
; normally be enforced by a type system.
(assert (= (str.len c) 1))

; Checks whether a given string is a single character repeated.
(define-fun is-repeated-char ((st String) (ch String)) Bool
    (forall ((i Int)) 
                (implies 
                    (and (>= i 0) (< i (str.len st))) 
                    (= (str.at st i) ch))))

; Define the length of the padding prefix.
(define-fun prefix-length () Int (max 0 (- n (str.len s))))

; Define the prefix string for padding, which is a string containing all pad characters.
(assert (= (str.len prefix) prefix-length))
(assert (is-repeated-char prefix c))

; The main computational step of leftpad. 
; We add the padding prefix to the input string to produce the padded output string.
(assert (= out (str.++ prefix s)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Define and verify the correctness properties of leftpad. 
;
; We assert the negations of these properties and see if we can find a model satisfying them. 
; If we cannot, we take this as proof of their correctness. We verify them independently of each 
; other using push/pop calls just to make sure there is no interaction between them. It also makes it
; easier to see if one of them fails independently of the others.

(push)
; Correctness property 1: Output string length is max(len(in), n).
(display "check length-property.")
(define-fun length-property () Bool (= (str.len out) (max (str.len s) n)))
(assert (not length-property))
(check-sat)
(get-model)
(pop)

(push)
; Correctness property 2: Output string has only pad characters as prefix.
(display "check prefix-property.")
(define-fun prefix-property () Bool 
    (is-repeated-char (str.substr out 0 prefix-length) c))
(assert (not prefix-property))
(check-sat)
(get-model)
(pop)

(push)
; Correctness property 3: Input string is a suffix of the output string.
(display "check suffix-property.")
(define-fun suffix-property () Bool (str.suffixof s out))
(assert (not suffix-property))
(check-sat)
(get-model)
(pop)

;
; Some concrete examples to demonstrate the Leftpad logic.
;

(display "test cases")

(push)
(assert (and (= s "he") (= n 5) (= c "p")))
(check-sat)
(get-model)
(pop)

(push)
(assert (and (= s "hello") (= n 3) (= c "p")))
(check-sat)
(get-model)
(pop)

(push)
(assert (and (= s "hello") (= n 5) (= c "p")))
(check-sat)
(get-model)
(pop)