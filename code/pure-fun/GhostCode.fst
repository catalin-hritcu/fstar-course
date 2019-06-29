module GhostCode

[@expect_failure]
let f1 (g:unit -> GTot nat) : Tot (n:nat{n = g ()}) = g ()

[@expect_failure]
let f2 (g:unit -> Dv nat) : Tot (n:nat{n = g ()}) = g ()

let f3 (g:unit -> GTot (n:nat{n = 4})) : Tot (n:nat{n = g ()}) = 4

let f4 (g:unit -> Tot nat) : GTot (n:nat{n = g ()}) = g ()

let f5 (g:unit -> GTot prop) : Tot prop = g ()

let f6 (g:unit -> GTot Type0) : Tot Type0 = g ()

let f7 (g:unit -> GTot unit) : Tot unit = g ()
