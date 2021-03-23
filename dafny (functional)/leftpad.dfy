function method leftpad(pad: char, n: int, s: string): string
    decreases n - |s|
    ensures |s| >= n ==> leftpad(pad, n, s) == s
    ensures |s| < n ==> |leftpad(pad, n, s)| == n
    ensures |s| < n ==> forall i :: 0 <= i < n - |s| ==> leftpad(pad, n, s)[i] == pad 
    ensures |s| < n ==> forall i :: n - |s| <= i < n ==> leftpad(pad, n, s)[i] == s[i - n + |s|]
{
    if |s| >= n then s else leftpad(pad, n, [pad] + s)
}

method Main() {
    var toPrint := [
        leftpad('!', 5, "foo"),
        leftpad('!', 0, "foo"),
        leftpad(':', 7, "hello !"),
        leftpad('l', 7, "eftpad"),
        leftpad('0', 10, "1")
    ];
    
    var i := 0;
    while i < |toPrint| 
        invariant 0 <= i <= |toPrint|
    {
        print toPrint[i];
        print "\n";
        i := i + 1;
    }
}