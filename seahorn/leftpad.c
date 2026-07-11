/* Leftpad, proved with SeaHorn: https://seahorn.github.io/
 *
 * Verify with:  sea pf leftpad.c
 * "unsat" means the verification conditions are unsatisfiable,
 * i.e. no execution can violate an assertion: leftpad is correct.
 */
#include "seahorn/seahorn.h"
#include <stdlib.h>

/* External functions with no definition are treated by SeaHorn as
 * returning an arbitrary (nondeterministic) value. */
extern int nd_int(void);
extern char nd_char(void);

static int max(int a, int b) { return a > b ? a : b; }

/* The code under verification. Pads string `s` of length `len` on the
 * left with `c` up to length `n`, writing into `out`. Returns the
 * number of characters written. */
int leftpad(char c, int n, const char *s, int len, char *out) {
  int pad = n - len;
  if (pad < 0)
    pad = 0;
  for (int i = 0; i < pad; ++i)
    out[i] = c;
  for (int i = 0; i < len; ++i)
    out[pad + i] = s[i];
  return pad + len;
}

/* The verification harness. Every value is arbitrary, so proving the
 * assertions here proves them for ALL inputs. */
int main(void) {
  char c = nd_char();
  int n = nd_int();
  int len = nd_int();
  assume(len >= 0); /* a string's length is non-negative */

  int expected = max(n, len);
  int pad = expected - len;

  /* Specs 2 and 3 are universally quantified over positions, so we
   * check them at an arbitrary symbolic index j. Since j is arbitrary,
   * proving the assertion proves it for every position at once. We
   * pick j *before* the loops run, so that the loop invariants Spacer
   * must infer only concern the single cell out[j] and stay
   * quantifier-free. j is only constrained to be non-negative: the
   * guards below decide whether it falls in the prefix, the suffix,
   * or (when j >= expected) outside the output, where there is
   * nothing to assert. Additionally assuming j < expected (i.e.
   * assume(j >= 0 && j < expected)) would make the combined
   * assumption unsatisfiable when expected == 0, silently pruning
   * those inputs and leaving Spec 1 unverified for them. */
  int j = nd_int();
  assume(j >= 0);

  /* An arbitrary string: `len` nondeterministic characters. */
  char *s = malloc(len);
  for (int i = 0; i < len; ++i)
    s[i] = nd_char();
  char *out = malloc(expected);

  int outlen = leftpad(c, n, s, len, out);

  /* Spec 1: the length of the output is max(n, len). */
  sassert(outlen == expected);
  if (j < pad)
    /* Spec 2: the prefix is padding characters, and nothing else. */
    sassert(out[j] == c);
  else if (j < expected)
    /* Spec 3: the suffix is the original string. */
    sassert(out[j] == s[j - pad]);

  return 0;
}
