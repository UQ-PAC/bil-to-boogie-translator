L: z -> true, x -> z == 0
Rely: z == old(z) && x == old(x)
Guarantee: old(z) == 0 ==> x == old(x) && z == old(z)