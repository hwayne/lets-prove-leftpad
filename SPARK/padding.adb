package body Padding with SPARK_Mode is

   function Left_Pad (S : String; Pad_Char : Character; Len : Natural)
                      return String
   -- (Len - S'Length) is the number of required padding chars. We create a
   -- string of that length with only Pad_Chars, and then concatenate this
   -- with S.
   is ((1 .. Len - S'Length => Pad_Char) & S);

end Padding;
