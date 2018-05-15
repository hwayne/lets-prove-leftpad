# Let's Prove Leftpad

This is a repository of provably-correct versions of Leftpad.

## What is "provably-correct"?

**Provably correct code** is code that you can totally guarantee does what you say it does. You do this by providing a **proof** that a computer can check. If the proof is wrong, the code won't compile. 

Compare to something like testing: even if you test your function for 1,000 different inputs, you still don't know _for sure_ that the 1,001st test will pass. With a proof, though, you know your function will work for all inputs, regardless of whether you try a thousand or ten trillion different test cases. Proving code correct is really, really powerful. It's also mindboggling hard, which is why most programmers don't do it.

This is a sampler of all the different tools we can use to prove code correct, standardized by all being proofs for Leftpad.

## What is "leftpad"?

Leftpad is a function that takes a character, a length, and a string, and pads the string to that length. It pads it by adding the character to the left. So it's adding *padding* on the *left*. Leftpad.

```
>> leftpad('!', 5, "foo")
!!foo
>> leftpad('!', 0, "foo")
foo
```

## Why are we proving leftpad?

Because it's funny.

And because leftpad is a great demo for different proof techniques. The idea is simple, the implemenation is simple, but the **specification** (what you actually, formally want it to do) is surpisingly tricky. Specifically, you need to prove things for it to be leftpad:

1. The length of the output is `max(n, len(str))`
2. The prefix of the output is padding characters and nothing but padding characters
3. The suffix of the output is the original string.

A proof of leftpad is going to be small enough to be (mostly) grokkable by Formal Methods outsiders, while being complex enough to differentiate the ways we prove code correct.

## I want to contribute!

We'd love to have you! Please [read the contribution guidelines](https://github.com/hwayne/lets-prove-leftpad/blob/master/CONTRIBUTING.md), and then submit your favorite proofs!

### Plug

If you want to learn more about formal methods, I shout at clouds on my [website](https://hillelwayne.com) and on [twitter](https://twitter.com/Hillelogram). 
