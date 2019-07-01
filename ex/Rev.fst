module Rev

let snoc l h = List.append l [h]

val rev : #a:Type -> list a -> Tot (list a)

let rec rev (#a:Type) l =
  match l with
  | []     -> []
  | hd::tl -> snoc (rev tl) hd

val rev_snoc : #a:Type -> l:list a -> h:a ->
                                        Lemma (rev (snoc l h) == h::rev l)

let rec rev_snoc (#a:Type) l h =
  match l with
  | []     -> ()
  | hd::tl -> rev_snoc tl h

val rev_involutive : #a:Type -> l:list a -> Lemma (rev (rev l) == l)

let rec rev_involutive (#a:Type) l =
  match l with
  | []     -> ()
  | hd::tl -> rev_involutive tl; admit() (* ; rev_snoc (rev tl) hd *)
(*
Know: rev (rev (hd::tl)) = rev (snoc (rev tl) hd)
Know (IH): rev (rev tl) == tl
To show: rev (rev (hd::tl)) == hd::tl
by lemma: rev (rev (hd::tl)) = rev (snoc (rev tl) hd) =(!) hd :: rev (rev tl)
Still to show: hd :: rev (rev tl) == hd::tl -- by IH + injectivity of Consmodule Sum

open FStar.Mul

let rec sum_rec (n:nat) = if n > 0 then n + sum_rec (n - 1) else 0

let sum_tot (n:nat) : nat = ((n + 1) * n) / 2

let rec sum_rec_correct (n:nat) : Lemma (sum_rec n = sum_tot n) =

  admit()                       (* replace this admit with a real proof *)
*)
