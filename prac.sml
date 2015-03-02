let
  val x = ref 3
in
  x := 2;
  !x + 2
end
