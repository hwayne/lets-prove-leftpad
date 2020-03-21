#include <string.h>

/*@ requires \valid(s + (0..n));
    requires valid_string(s);
    requires c != 0;

    behavior no_padding:
      assumes strlen(s) >= n;
      assigns \nothing;

    behavior padding:
      assumes strlen(s) < n;
      ensures valid_string(s);
      ensures \let l = strlen{Pre}(s); \let p = n - l;
        (\forall integer x; 0 <= x < p ==> s[x] == c) &&
        memcmp{Pre, Post}(s, s + p, l + 1) == 0 &&
        strlen(s) == n;
      assigns s[0 .. n];

    complete behaviors;
    disjoint behaviors;
 */
void leftpad(char c, size_t n, char *s) {
  size_t l = strlen(s);
  if (n > l) {
    size_t p = n - l;

    // This loop is equivalent to memmove(s+p, s, l+1)
    /*@ loop invariant x_range: 0 <= x <= l;
        loop invariant s_state: \forall integer i; 0 <= i <= n ==>
          (i <= x+p ==> s[i] == \at(s[i], LoopEntry)) &&
          (i >  x+p ==> s[i] == \at(s[i-p], LoopEntry));
        loop assigns x, s[p..n];
        loop variant x;
     */
    for (size_t x = l;; x--) {
      s[x+p] = s[x];
      if (x == 0) {
        break;
      }
    }

    // These assertions are not strictly necessary, but they speed up the verification
    //@ assert same_chars: memcmp{Pre, Here}(s, s+p, l+1) == 0 && s[n] == 0;
    //@ assert valid_str: valid_string(s+p);
    //@ assert same_len: strlen(s+p) == l;

    // This loop is equivalent to memset(s, c, p)
    /*@ loop invariant x_range2: 0 <= x <= p;
        loop invariant still_same: memcmp{Pre, LoopCurrent}(s, s+p, l+1) == 0 && s[n] == 0;
        loop invariant valid_grows: valid_string(s + p - x);
        loop invariant padding_grows: \forall integer i; p - x <= i < p ==> s[i] == c;
        loop assigns x, s[0..p-1];
        loop variant p - x;
     */
    for (size_t x = 0; x < p; x++) {
      s[p-1-x] = c;
    }
  }
}
