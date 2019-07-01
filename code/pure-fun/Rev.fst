module Rev

// BEGIN: rev
let snoc l h = l @ [h]

val rev: #a:Type -> list a -> Tot (list a)
let rec rev (#a:Type) l =
  match l with
  | [] -> []
  | hd::tl -> snoc (rev tl) hd
// END: rev

// BEGIN: rev_snoc
val rev_snoc: #a:Type -> l:list a -> h:a -> Lemma (rev (snoc l h) == h::rev l)
let rec rev_snoc (#a:Type) l h =
  match l with
  | [] -> ()
  | hd::tl -> rev_snoc tl h
// END: rev_snoc

// BEGIN: rev_involutive
val rev_involutive: #a:Type -> l:list a -> Lemma (rev (rev l) == l)
let rec rev_involutive (#a:Type) l =
  match l with
  | [] -> ()
  | hd::tl -> rev_involutive tl; rev_snoc (rev tl) hd
// END: rev_involutive
(*
Know (computation): rev (rev (hd::tl)) = rev (snoc (rev tl) hd)
Know (IH): rev (rev tl) == tl
To show: rev (rev (hd::tl)) == hd::tl
by lemma: rev (rev (hd::tl)) = rev (snoc (rev tl) hd) =(!) hd :: rev (rev tl)
Still to show: hd :: rev (rev tl) == hd::tl -- by IH + injectivity of Consmodule Sum
*)

// BEGIN: rev_snoc2
val rev_snoc2 : #a:Type -> l:list a -> h:a -> Lemma (rev (snoc l h) == h::rev l)
                             (* ADDED THIS --> *)   [SMTPat (rev (snoc l h))]
let rec rev_snoc2 (#a:Type) l h =
  match l with
  | []     -> ()
  | hd::tl -> rev_snoc2 tl h
// END: rev_snoc2

// BEGIN: rev_involutive2
val rev_involutive2: #a:Type -> l:list a -> Lemma (rev (rev l) == l)
let rec rev_involutive2 (#a:Type) l =
  match l with
  | [] -> ()
  | hd::tl -> rev_involutive2 tl(* ; rev_snoc (rev tl) hd *)
// END: rev_involutive2
