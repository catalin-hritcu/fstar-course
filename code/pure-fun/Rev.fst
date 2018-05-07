module Rev

let snoc l h = l @ [h]

val reverse: #a:Type -> list a -> Tot (list a)
let rec reverse (#a:Type) l =
  match l with
  | [] -> []
  | hd::tl -> snoc (reverse tl) hd

val rev_snoc: #a:Type -> l:list a -> h:a ->
  Lemma (reverse (snoc l h) == h::reverse l)
let rec rev_snoc (#a:Type) l h =
  match l with
  | [] -> ()
  | hd::tl -> rev_snoc tl h

val rev_involutive: #a:Type -> l:list a -> Lemma (reverse (reverse l) == l)
let rec rev_involutive (#a:Type) l =
  match l with
  | [] -> ()
  | hd::tl -> rev_involutive tl; rev_snoc (reverse tl) hd
