package Padding with SPARK_Mode is

   --  add [Pad_Char] characters to the left of the string [S] so that its
   --  length becomes [Len] if greater than [S'Length]
   function Left_Pad (S : String; Pad_Char : Character; Len : Natural)
                      return String
   with Contract_Cases =>
      --  if the string is shorter than the desired length ...
     (Len > S'Length =>
        --  length of the result is [Len]
        Left_Pad'Result'Length = Len and then
        --  and looking at all characters in the result ...
        (for all I in Left_Pad'Result'Range =>
           Left_Pad'Result (I) =
              --  characters before those from [S] are equal to [Pad_Char]
             (if I <= Len - S'Length then
                Pad_Char
              --  remaining characters are those from [S]
              else
                S (I - (Len - S'Length + 1) + S'First))),
      --  if not, the result is equal to the input string [S]
      others => Left_Pad'Result = S);

end Padding;
