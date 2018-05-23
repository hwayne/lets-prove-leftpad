with Ada.Text_IO;
with Padding;

procedure Test_Padding is
begin
   Ada.Text_IO.Put_Line(Padding.Left_Pad ("Alice", ' ', 8));
   Ada.Text_IO.Put_Line(Padding.Left_Pad ("Bob", ' ', 8));
   Ada.Text_IO.Put_Line(Padding.Left_Pad ("Carol", ' ', 8));
end Test_Padding;
