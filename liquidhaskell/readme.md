# [LiquidHaskell](https://ucsd-progsys.github.io/liquidhaskell-blog/)

## About LiquidHaskell

LiquidHaskell is a static verifier for Haskell, based on Liquid Types which
refines Haskell's types with logical predicates that let you specify and 
verify properties at compile time. 

See[the blog](https://ucsd-progsys.github.io/liquidhaskell-blog/) for more details.

You can [run LH on the LeftPad proof here](http://goto.ucsd.edu:8090/index.html#?demo=LeftPad.hs).

## About the Proof

The implementation and proof shown in  [LeftPad.lhs](LeftPad.lhs) 
is a literate Haskell file with a detailed explanation about the proof. 

The most unique aspect about this proof relative to those using dependent 
types or proof assistants (e.g. Coq, Isabelle, Idris), is the use of 
SMT-based decision procedures for automating reasoning over arithmetic.

Dually, the most unique aspect relative to those using SMT solvers 
(e.g. Dafny, F-star, Spark), is to _limit_ SMT queries to decidable 
logics -- where SMT solvers behave in a predictable manner --  by 
eschewing axioms and quantifiers, instead using a form of type-level computation 
that we call [proof by logical evaluation](https://arxiv.org/pdf/1711.03842).

## About Me 

I am [Ranjit Jhala](https://twitter.com/RanjitJhala) one of the 
developers of LH and a professor of Computer Science and Engineering 
at the [University of California, San Diego](http://ranjitjhala.github.io/).

