L: x -> true
Rely: x == old(x) || x == 5
Guarantee: old(x) == 5 || old(x) == 6 ==> x == 5 || x == 6

Subroutine: main
Requires: x == 0
Ensures: x == 1 || x == 5 || x == 6