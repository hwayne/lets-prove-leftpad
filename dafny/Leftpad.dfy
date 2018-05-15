// see https://rise4fun.com/Dafny/nbNTl

function method max(a: int, b: int): int
{
    if a > b then a else b
}

method LeftPad(c: char, n: int, s: seq<char>) returns (v: seq<char>)
ensures |v| == max(n, |s|)
ensures forall i :: 0 <= i < n - |s| ==> v[i] == c
ensures forall i :: 0 <= i < |s| ==> v[max(n - |s|, 0)+i] == s[i]
{
    
    var pad, i := max(n - |s|, 0), 0;
    v := s;
    while i < pad decreases pad - i
    invariant 0 <= i <= pad
    invariant |v| == |s| + i
    invariant forall j :: 0 <= j < i ==> v[j] == c
    invariant forall j :: 0 <= j < |s| ==> v[i+j] == s[j]
    {
        v := [c] + v;
        i := i + 1;
    }
}

method Main() {
    var l1 := LeftPad('0', 5, "foo");
    var l2 := LeftPad('0', 1, "foo");
    print l1 + "\n\n";
    print l2;
}
