(ns leftpad.core
  (:require [clojure.spec.alpha :as s]
            [clojure.spec.gen.alpha :as gen]
            [clojure.spec.test.alpha :as stest]
            [expound.alpha :as expound]
            [clojure.string :as str]))

;; This just helps us get a more readable output
(set! s/*explain-out* expound/printer)

(defn leftpad
  [pad n string]
  (str/join (concat (repeat (- n (count string)) pad)
                    [string])))

(comment
  (leftpad \! 5 "foo")
  (leftpad \! 0 "foo")
  )

(defn correct-length-of-output?
  "Returns true if the length of the output is max(n, len(str))"
  [n string out]
  (= (count out)
     (max n (count string))))

(defn prefix-is-pad?
  "Returns true if The prefix of the output is padding characters and nothing
  but padding characters"
  [pad string out]
  (every? (fn [c] (= pad c))
          (subs out 0 (- (count out)
                         (count string)))))

(defn suffix-is-original-string?
  "Returns true if the suffix of the output is the original string"
  [string out]
  (= string
     (subs out (- (count out)
                  (count string)))))

(s/fdef leftpad
        :args (s/cat :pad char? :n int? :string string?)
        :ret string?
        :fn (s/and
             #(correct-length-of-output? (-> % :args :n) (-> % :args :string) (:ret %))
             #(prefix-is-pad? (-> % :args :pad) (-> % :args :string) (:ret %))
             #(suffix-is-original-string? (-> % :args :string) (:ret %))))

(comment
  (expound/explain-results
   (stest/check `leftpad {:clojure.spec.test.check/opts {:num-tests 30}}))
  )
