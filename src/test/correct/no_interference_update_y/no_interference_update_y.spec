Globals:
x: int
y: int

L: x -> true, y -> true
Rely: y == old(y)
Guarantee: x == old(x)

Subroutine: main
Ensures: y == 1bv32