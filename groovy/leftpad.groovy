import groovy.transform.TypeChecked
import groovy.contracts.Requires
import groovy.contracts.Ensures
import groovy.contracts.Invariant
import groovy.contracts.Decreases

// Verified at COMPILE TIME by groovy-verify (https://github.com/paulk-asert/groovy-verify):
// the @TypeChecked extension discharges every contract below with Z3 while javac-style
// compilation runs — a wrong invariant or postcondition is a compile ERROR with a
// concrete counterexample. groovy-contracts checks the same annotations at runtime.
@TypeChecked(extensions = 'verification.VerifyChecker')
class Leftpad {
    @Requires({ s != null && n >= 0 })
    @Ensures({ result.length == (n > s.length ? n : s.length) &&
               (0..<(n > s.length ? n - s.length : 0)).every { int i -> result[i] == c } &&
               (0..<s.length).every { int i -> result[(n > s.length ? n - s.length : 0) + i] == s[i] } })
    static int[] leftpad(int c, int n, int[] s) {
        int pad = n > s.length ? n - s.length : 0
        int[] r = new int[pad + s.length]
        int i = 0
        @Invariant({ 0 <= i && i <= pad &&
                     pad == (n > s.length ? n - s.length : 0) &&
                     r.length == pad + s.length &&
                     (0..<i).every { int q -> r[q] == c } })
        @Decreases({ pad - i })
        while (i < pad) {
            r[i] = c
            i = i + 1
        }
        int j = 0
        @Invariant({ 0 <= j && j <= s.length &&
                     pad == (n > s.length ? n - s.length : 0) &&
                     r.length == pad + s.length &&
                     (0..<pad).every { int q -> r[q] == c } &&
                     (0..<j).every { int q -> r[pad + q] == s[q] } })
        @Decreases({ s.length - j })
        while (j < s.length) {
            r[pad + j] = s[j]
            j = j + 1
        }
        return r
    }

}
