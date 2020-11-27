function div(x: int, y: int):int 
  requires y != 0;
{
  x/y
}

method test() {
  var a := [1,2,3];
  assert a[1] == 2;
}