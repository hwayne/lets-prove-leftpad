import groovy.transform.TypeChecked
import groovy.contracts.Requires
import groovy.contracts.Ensures
import groovy.contracts.Decreases

// Verified at COMPILE TIME by groovy-verify (https://github.com/paulk-asert/groovy-verify).
// No loops, no mutation: the recursion's own @Ensures is its induction hypothesis (sound
// because @Decreases proves termination), and the length property is DERIVED by a theorem
// method from a padding-length lemma — the spec-function / proof-function structure.
@TypeChecked(extensions = 'verification.VerifyChecker')
class Leftpad {
    // The specification is STRUCTURAL: the result IS the padding block followed by the
    // original string. This single equality pins properties 2 and 3 exactly (prefix is
    // nothing but pad characters; suffix is s), stronger than the usual index clauses.
    @Requires({ pad != null && s != null && pad.length() == 1 })
    @Ensures({ (s.length() >= n ==> result == s) &&
               (s.length() < n ==> result == pads(pad, n - s.length()) + s) })
    @Decreases({ n - s.length() })
    static String leftpad(String pad, int n, String s) {
        s.length() >= n ? s : pad + leftpad(pad, n - 1, s)
    }

    // The padding block, defined recursively (a pure "ghost" builder).
    static String pads(String pad, int k) {
        k <= 0 ? '' : pad + pads(pad, k - 1)
    }

    // Lemma: |pads(pad, k)| == k, by induction on k (the recursive call is the hypothesis).
    @Requires({ pad != null && pad.length() == 1 && k >= 0 })
    @Ensures({ pads(pad, k).length() == k })
    @Decreases({ k })
    static void padsLen(String pad, int k) {
        if (k > 0) { padsLen(pad, k - 1) }
    }

    // Theorem: property 1, |leftpad(pad, n, s)| == n when padding happens (== max(n, |s|)
    // overall, with the identity case giving |s| when |s| >= n). Derived from leftpad's
    // structural postcondition plus the padsLen lemma: |pads(n-|s|) + s| = (n-|s|) + |s|.
    @Requires({ pad != null && s != null && pad.length() == 1 && s.length() < n })
    @Ensures({ result.length() == n })
    static String lengthTheorem(String pad, int n, String s) {
        padsLen(pad, n - s.length())
        return leftpad(pad, n, s)
    }

}
