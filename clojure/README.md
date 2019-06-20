# [Clojure](https://clojure.org/)

## About Clojure

Clojure is a functional language that encourages immutability and runs on the Java platform. It is a dialect of Lisp and shares its code-as-data philosophy. Clojure comes with a contract system called [Spec](https://clojure.org/guides/spec) and a property based testing library called [`test.check`](https://github.com/clojure/test.check).

## About the Proof

This proof describes all possible inputs, outputs, and the [three statements](https://github.com/hwayne/lets-prove-leftpad#why-are-we-proving-leftpad) Hillel made on the main readme. It then uses that specification to do property based testing on our leftpad implementation. In the code walkthrough below, I show examples of what it looks like when property based tests fail. The failures include shrinking to show you the simplest case that illustrates the problem.

## About me

I'm [Brian Maddy](https://twitter.com/bmaddy). I'm an independent software developer with an interest in programming languages. You can find me on [Twitter](https://twitter.com/bmaddy), [Github](https://github.com/bmaddy), and elsewhere as bmaddy.

## Code walkthrough

Clojure is a very interactive language. When writing code, people generally have a [REPL](https://clojure.org/guides/repl/introduction) attached to their editor and constantly send code over to it. Because of that, I'll present the description a an interactive repl session and show some of the property based testing features along the way.

[Install Clojure](https://clojure.org/guides/getting_started), then run `clj` to start the clojure repl (or even better, start it in your favorite editor). If it's not clear what some of the functions below are, a good place to look them up is at [ClojureDocs](http://clojuredocs.org/).

First, load some libraries we'll be needing
```clojure
user> (ns leftpad.core
        (:require [clojure.spec.alpha :as s]
                  [clojure.spec.gen.alpha :as gen]
                  [clojure.spec.test.alpha :as stest]
                  [expound.alpha :as expound]
                  [clojure.string :as str]))
nil
```
Let's write a placeholder leftpad function
```clojure
leftpad.core> (defn leftpad
                [pad n string]
                :todo)
#'leftpad.core/leftpad

;; Let's try it out
leftpad.core> (leftpad \! 5 "foo")
:todo
```
Great, now let's make a spec that describes the first input: any single character. Many predicate functions in Clojure have built-in specs associated with them. That's the case for `char?`, the character predicate. We'll build a generator from it and use that to generate a few random values.
```clojure
leftpad.core> (gen/generate (s/gen char?))
\¬
leftpad.core> (gen/generate (s/gen char?))
\,

;; We can do the same for our other arguments
leftpad.core> (gen/generate (s/gen int?))
10327
leftpad.core> (gen/generate (s/gen string?))
"E2Iswb0G15Aj1Bv33m"

;; Combine these into a new spec that describes possible inputs to our function
leftpad.core> (gen/generate (s/gen (s/cat :pad char?
                                          :n int?
                                          :string string?)))
(\u -60 "74R0AaNR3xGCn5")
```
Let's make a first draft of the spec that describes leftpad.
```clojure
leftpad.core> (s/fdef leftpad
                      :args (s/cat :pad char? :n int? :string string?))
leftpad.core/leftpad
```
Time to run our spec against our function. `stest/check` will run our function with random arguments a bunch of times and report any issues. We aren't actually describing anything it does yet, so everything should pass.
```clojure
;; This just initializes a library get us a more readable output
leftpad.core> (set! s/*explain-out* expound/printer)
#function[expound.alpha/printer]

leftpad.core> (expound/explain-results
               (stest/check `leftpad))
== Checked leftpad.core/leftpad =============

Success!
nil
```
Now we can update our spec to say it should reutrn a string
```clojure
leftpad.core> (s/fdef leftpad
                      :args (s/cat :pad char? :n int? :string string?)
                      :ret string?)
leftpad.core/leftpad

;; Run the spec again to see a problem with our function.
leftpad.core> (expound/explain-results
               (stest/check `leftpad))
== Checked leftpad.core/leftpad =============

-- Function spec failed -----------

  (leftpad.core/leftpad \^@ 0 "")

returned an invalid value.

  :todo

should satisfy

  string?

-------------------------
Detected 1 error
nil
```
In reality, it probably failed on a much more complex input than `\^@ 0 ""`, but when it finds an error it shrinks it to the simplest failing case. Let's improve our function.
```clojure
leftpad.core> (defn leftpad
                [pad n string]
                "todo")
#'leftpad.core/leftpad

leftpad.core> (expound/explain-results
               (stest/check `leftpad))
== Checked leftpad.core/leftpad =============

Success!
nil
```
That fixed things. It's time for constraints that depend on arguments to the function. Make a helper predicate for the first constraint.
```clojure
leftpad.core> (defn correct-length-of-output?
                "Returns true if the length of the output is max(n, len(str))"
                [n string out]
                (= (count out)
                   (max n (count string))))
#'leftpad.core/correct-length-of-output?
```
Add this constraint to our spec. We use an [anonymous function](https://clojure.org/guides/weird_characters#_anonymous_function) to grab the arguments and return value we need to pass to our predicate.
```clojure
leftpad.core> (s/fdef leftpad
                      :args (s/cat :pad char? :n int? :string string?)
                      :ret string?
                      :fn #(correct-length-of-output? (-> % :args :n) (-> % :args :string) (:ret %)))
leftpad.core/leftpad

leftpad.core> (expound/explain-results
               (stest/check `leftpad))
== Checked leftpad.core/leftpad =============

-- Function spec failed -----------

  (leftpad.core/leftpad \^@ 0 "")

failed spec. Function arguments and return value

  {:args {:pad \^@, :n 0, :string ""}, :ret "todo"}

should satisfy

  (fn
   [%]
   (leftpad.core/correct-length-of-output?
    (-> % :args :n)
    (-> % :args :string)
    (:ret %)))

-------------------------
Detected 1 error
nil
```
As you can see, "todo" is not the correct length for n = 0 and string = "". Here's an improved function.
```clojure
leftpad.core> (defn leftpad
                [pad n string]
                (str/join (concat (repeat (- n (count string)) \a)
                                  (repeat (count string) \b))))
#'leftpad.core/leftpad

leftpad.core> (leftpad \! 5 "foo")
"aabbb"
leftpad.core> (leftpad \! 0 "foo")
"bbb"

;; We're limiting the number of tests here because our version of leftpad was
;; written for readability, not performance.
leftpad.core> (expound/explain-results
               (stest/check `leftpad {:clojure.spec.test.check/opts {:num-tests 30}}))
== Checked leftpad.core/leftpad =============

Success!
nil
```
Now we make another predicate for the next constraint and add that to the spec.
```clojure
leftpad.core> (defn prefix-is-pad?
                "Returns true if The prefix of the output is padding characters and nothing
                but padding characters"
                [pad string out]
                (every? (fn [c] (= pad c))
                        (subs out 0 (- (count out)
                                       (count string)))))
#'leftpad.core/prefix-is-pad?

leftpad.core> (s/fdef leftpad
                      :args (s/cat :pad char? :n int? :string string?)
                      :ret string?
                      :fn (s/and
                           #(correct-length-of-output? (-> % :args :n) (-> % :args :string) (:ret %))
                           #(prefix-is-pad? (-> % :args :pad) (-> % :args :string) (:ret %))))
leftpad.core/leftpad

leftpad.core> (expound/explain-results
               (stest/check `leftpad {:clojure.spec.test.check/opts {:num-tests 30}}))
== Checked leftpad.core/leftpad =============

-- Function spec failed -----------

  (leftpad.core/leftpad \^@ 1 "")

failed spec. Function arguments and return value

  {:args {:pad \^@, :n 1, :string ""}, :ret "a"}

should satisfy

  (fn
   [%]
   (leftpad.core/prefix-is-pad?
    (-> % :args :pad)
    (-> % :args :string)
    (:ret %)))

-------------------------
Detected 1 error
nil
```
It found our next problem. The simplest example of it shows us that the output doesn't start with `\^@`. Let's improve things further.
```clojure
leftpad.core> (defn leftpad
                [pad n string]
                (str/join (concat (repeat (- n (count string)) pad)
                                  (repeat (count string) \b))))
#'leftpad.core/leftpad

leftpad.core> (expound/explain-results
               (stest/check `leftpad {:clojure.spec.test.check/opts {:num-tests 30}}))
== Checked leftpad.core/leftpad =============

Success!
nil
```
Time to add the final constraint.
```clojure
leftpad.core> (defn suffix-is-original-string?
                "Returns true if the suffix of the output is the original string"
                [string out]
                (= string
                   (subs out (- (count out)
                                (count string)))))
#'leftpad.core/suffix-is-original-string?

leftpad.core> (s/fdef leftpad
                      :args (s/cat :pad char? :n int? :string string?)
                      :ret string?
                      :fn (s/and
                           #(correct-length-of-output? (-> % :args :n) (-> % :args :string) (:ret %))
                           #(prefix-is-pad? (-> % :args :pad) (-> % :args :string) (:ret %))
                           #(suffix-is-original-string? (-> % :args :string) (:ret %))))
leftpad.core/leftpad

leftpad.core> (expound/explain-results
               (stest/check `leftpad {:clojure.spec.test.check/opts {:num-tests 30}}))
== Checked leftpad.core/leftpad =============

-- Function spec failed -----------

  (leftpad.core/leftpad \^@ 0 "0")

failed spec. Function arguments and return value

  {:args {:pad \^@, :n 0, :string "0"}, :ret "b"}

should satisfy

  (fn
   [%]
   (leftpad.core/suffix-is-original-string?
    (-> % :args :string)
    (:ret %)))

-------------------------
Detected 1 error
nil
```
Now, our final version of leftpad and test it.
```clojure
leftpad.core> (defn leftpad
                [pad n string]
                (str/join (concat (repeat (- n (count string)) pad)
                                  [string])))
#'leftpad.core/leftpad

leftpad.core> (expound/explain-results
               (stest/check `leftpad {:clojure.spec.test.check/opts {:num-tests 30}}))
== Checked leftpad.core/leftpad =============

Success!
nil
```
We did it!
```clojure
leftpad.core> (leftpad \! 5 "foo")
"!!foo"
leftpad.core> (leftpad \! 0 "foo")
"foo"
```
