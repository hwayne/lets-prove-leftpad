#include <string.h>
//@ #include <listex.gh>

/*@

lemma void all_eq_mem<t>(list<t> xs, t x, t x0)
    requires all_eq(xs, x) && mem(x0, xs);
    ensures x0 == x;
{
    switch (xs) {
        case nil:
        case cons(x1, xs1):
            if (x1 != x0)
                all_eq_mem(xs1, x, x0);
    }
}

lemma void chars_string_join(char *s)
    requires chars(s, ?n, ?cs0) &*& string(s + n, ?cs1) &*& !mem(0, cs0);
    ensures string(s, append(cs0, cs1));
{
    open chars(s, n, cs0);
    if (n > 0) {
        chars_string_join(s + 1);
        close string(s, append(cs0, cs1));
    }
}

@*/

void leftpad(char c, size_t n, char *s)
/*@
requires
    c != 0 &*&
    string(s, ?cs) &*&
    length(cs) < n ?
        (s + length(cs) + 1)[..n - length(cs)] |-> _
    :
        true;
@*/
/*@
ensures
    string(s, ?cs1) &*&
    length(cs1) >= n &*&
    all_eq(take(length(cs1) - length(cs), cs1), c) == true &*&
    drop(length(cs1) - length(cs), cs1) == cs;
@*/
//@ terminates;
{
  size_t l = strlen(s);
  if (n > l) {
    size_t p = n - l;
    //@ string_limits(s);
    //@ chars__limits(s + length(cs) + 1);
    memmove(s + p, s, l + 1);
    memset(s, c, p);
    //@ assert chars(s, p, ?cspad);
    //@ if (mem(0, cspad)) { all_eq_mem(cspad, c, 0); assert false; }
    //@ chars_string_join(s);
    //@ take_append(p, cspad, cs);
    //@ take_append(length(cs), cs, {0});
    //@ drop_append(p, cspad, cs);
  }
}
