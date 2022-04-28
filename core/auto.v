From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq eqtype.
From fcsl Require Import options.

(***************************************************************************)
(* Common infrastructure for syntactifying expressions in automated lemmas *)
(***************************************************************************)

(* Two helper concepts for searching in sequences:                       *)
(*                                                                       *)
(* - onth: like nth, but returns None when the element is not found      *)
(* - prefix: a prefix relation on sequences, used for growing            *)
(*   interpretation contexts                                             *)

Section Prefix.
Variable A : Type.

Fixpoint onth (s : seq A) n : option A :=
  if s is x::sx then if n is nx.+1 then onth sx nx else Some x else None.

Definition prefix s1 s2 : Prop :=
  forall n x, onth s1 n = some x -> onth s2 n = some x.

(* Theory of onth + prefix *)

Lemma size_onth s n : n < size s -> exists x, onth s n = some x.
Proof.
elim: s n=>[//|a s IH] [|n] /=; first by exists a.
by rewrite -(addn1 n) -(addn1 (size s)) ltn_add2r; apply: IH.
Qed.

Lemma onth_size s n x : onth s n = some x -> n < size s.
Proof. by elim: s n=>[//|a s IH] [//|n]; apply: IH. Qed.

Lemma prefix_refl s : prefix s s.
Proof. by move=>n x <-. Qed.

Lemma prefix_trans s2 s1 s3 : prefix s1 s2 -> prefix s2 s3 -> prefix s1 s3.
Proof. by move=>H1 H2 n x E; apply: H2; apply: H1. Qed.

Lemma prefix_cons x s1 s2 : prefix (x :: s1) (x :: s2) <-> prefix s1 s2.
Proof. by split=>E n; [apply: (E n.+1) | case: n]. Qed.

Lemma prefix_cons' x y s1 s2 :
        prefix (x :: s1) (y :: s2) -> x = y /\ prefix s1 s2.
Proof. by move=>H; case: (H 0 x (erefl _)) (H)=>-> /prefix_cons. Qed.

Lemma prefix_size s1 s2 : prefix s1 s2 -> size s1 <= size s2.
Proof.
elim: s1 s2=>[//|a s1 IH] [|b s2] H; first by move: (H 0 a (erefl _)).
by rewrite ltnS; apply: (IH _ (proj2 (prefix_cons' H))).
Qed.

Lemma prefix_onth s t x : x < size s -> prefix s t -> onth s x = onth t x.
Proof.
elim:s t x =>[//|a s IH] [|b t] x H1 H2; first by move: (H2 0 a (erefl _)).
by case/prefix_cons': H2=><- H2; case: x H1=>[|n] //= H1; apply: IH.
Qed.

Lemma onth_nth s n : onth s n = nth None (map some s) n.
Proof. by elim: s n=> [|x s IH] [|n] /=. Qed.

End Prefix.

#[export]
Hint Resolve prefix_refl : core.

Lemma onth_mem {A : eqType} (s : seq A) n x : onth s n = Some x -> x \in s.
Proof.
by elim: s n=>//= a s IH [[->]|n /IH]; rewrite inE ?eq_refl // orbC => ->.
Qed.

(* In cancellation algorithms for automated lemmas, we iterate over the   *)
(* first expression e1 and remove each of its components from the second  *)
(* expression e2. But, typically, we want to remove only one occurrence   *)
(* of that component.                                                     *)
(*                                                                        *)
(* First, almost always, only one occurrence will exist, lest e2 be       *)
(* undefined. Thus, it's a waste of effort to traverse e2 in full once    *)
(* we've found an occurrence.                                             *)
(*                                                                        *)
(* Second, in some symmetric cancellation problems, e.g., dom_eq e1 e2,   *)
(* we *want* to remove only one occurrence from e2 for each component in  *)
(* e1. Otherwise, we will not produce a sound reduction. E.g.,            *)
(* dom (x \+ x) (x \+ x) is valid, since both expressions are undef.      *)
(* However, after removing x from the left side, and both x's from the    *)
(* right side, we get dom x Unit, which is not valid.                     *)
(*                                                                        *)
(* Thus, as a matter of principle, we want a filter that removes just one *)
(* occurrence of a list element.                                          *)
(*                                                                        *)
(* We write it with p pulled out in a section in order to get it to       *)
(* simplify automatically.                                                *)

Section OneShotFilter.
Variables (A : Type) (p : pred A).

(* a variant of filter that removes only the first occurence *)

Fixpoint rfilter {A} (p : pred A) (ts : seq A) : seq A :=
  if ts is t :: ts' then if p t then ts' else t :: rfilter p ts' else [::].

End OneShotFilter.

(* rfilter can also be thought of as a generalization of rem *)
Lemma rfilter_rem {T : eqType} (ts : seq T) x :
rfilter (pred1 x) ts = rem x ts.
Proof. by elim: ts=> [|t ts IH] //=; case: eqP=>//= _; rewrite IH. Qed.

(* A canonical structure program for searching and inserting in a list *)

Section XFind.
Variable A : Type.

Structure tagged_elem := XTag {xuntag :> A}.

Definition extend_tag := XTag.
Definition recurse_tag := extend_tag.
Canonical found_tag x := recurse_tag x.

(* Main structure:                                                  *)
(* - xs1 : input sequence                                           *)
(* - xs2 : output sequence; if pivot is found, then xs2 = xs1, else *)
(*   xs2 = pivot :: xs1                                             *)
(* - i : output index of pivot in xs2                               *)

Definition axiom xs1 xs2 i (pivot : tagged_elem) :=
  onth xs2 i = Some (xuntag pivot) /\ prefix xs1 xs2.
Structure xfind (xs1 xs2 : seq A) (i : nat) :=
  Form {pivot :> tagged_elem; _ : axiom xs1 xs2 i pivot}.

(* found the elements *)
Lemma found_pf x t : axiom (x :: t) (x :: t) 0 (found_tag x).
Proof. by []. Qed.
Canonical found_form x t := Form (@found_pf x t).

(* recurse *)
Lemma recurse_pf i x xs1 xs2 (f : xfind xs1 xs2 i) :
        axiom (x :: xs1) (x :: xs2) i.+1 (recurse_tag (xuntag f)).
Proof. by case: f=>pv [H1 H2]; split=>//; apply/prefix_cons. Qed.
Canonical recurse_form i x xs1 xs2 f := Form (@recurse_pf i x xs1 xs2 f).

(* failed to find; attach the element to output *)
Lemma extend_pf x : axiom [::] [:: x] 0 (extend_tag x).
Proof. by []. Qed.
Canonical extend_form x := Form (@extend_pf x).

End XFind.