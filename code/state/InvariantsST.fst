module InvariantsST

open FStar.Ref

type nlist = xs:list int{Cons? xs}

let create (x:int) : St (ref nlist) = alloc #nlist [x]

let add (x:int) (r:ref nlist) : St unit =  r := x :: !r

let main() : St unit =
  let r = create 1 in
  add 2 r;
  add 3 r
  (* r := []  -- fails: expected type nlist; got type list int *)
