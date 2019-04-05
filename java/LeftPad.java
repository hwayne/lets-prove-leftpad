public class LeftPad {
    //@ requires n >= 0;
    //@ requires s != null;
    //@ ensures \result.length == Math.max(n, s.length);
    //@ ensures \forall int i; i >= 0 && i < Math.max(n - s.length, 0); \result[i] == c;
    //@ ensures \forall int i; i >= 0 && i < s.length; \result[Math.max(n - s.length, 0) + i] == s[i];
    static char[] leftPad(char c, int n, char[] s) {
        int pad = Math.max(n - s.length, 0);
        char[] v = new char[pad + s.length];
        int i = 0;

        //@ maintaining i >= 0 && i <= pad;
        //@ maintaining \forall int j; j >= 0 && j < i; v[j] == c;
        for(; i<pad; i++) v[i] = c;
        
        //@ maintaining i >= pad;
        //@ maintaining \forall int j; j >= 0 && j < pad; v[j] == c;
        //@ maintaining \forall int j; j >= pad && j < i; v[j] == s[j - pad];
        for(i = pad; i < v.length; i++) v[i] = s[i - pad];
        
        return v;
    }
}
