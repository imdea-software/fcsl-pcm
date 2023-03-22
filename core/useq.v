From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From mathcomp Require Import seq choice fintype path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* sequence of unique elements *)

Section UseqDef.
Variable (T : eqType).

Structure useq : Type := Useq {uval :> seq T; _ : uniq uval}.

Canonical useq_subType := Eval hnf in [subType for uval].

Implicit Type t : useq.

Lemma uniq_useq t : uniq t.
Proof. exact: (valP t). Qed.

Definition mkUseq t mkT : useq :=
  mkT (let: Useq _ tP := t return uniq t in tP).

Lemma mkUseqE t : mkUseq (fun sP => @Useq t sP) = t.
Proof. by case: t. Qed.

End UseqDef.

Section UseqEq.
Variable (T : eqType).

Definition useq_eqMixin := Eval hnf in [eqMixin of useq T by <:].
Canonical useq_eqType := Eval hnf in EqType (useq T) useq_eqMixin.

Canonical useq_predType := PredType (pred_of_seq : useq T -> pred T).

Lemma memtE (t : useq T) : mem t = mem (uval t).
Proof. by []. Qed.

End UseqEq.

Definition useq_choiceMixin (T : choiceType) :=
  [choiceMixin of useq T by <:].

Canonical useq_choiceType (T : choiceType) :=
  Eval hnf in ChoiceType (useq T) (useq_choiceMixin T).

Definition useq_countMixin (T : countType) :=
  [countMixin of useq T by <:].

Canonical useq_countType (T : countType) :=
  Eval hnf in CountType (useq T) (useq_countMixin T).

Canonical useq_subCountType (T : countType) :=
  Eval hnf in [subCountType of useq T].

  Canonical nil_useq (T : eqType) := Useq (isT : @uniq T [::]).

(* all operations that permute or drop values are safe *)

Section SeqUseq.
Variables (n : nat) (T U : eqType).
Implicit Type t : useq T.

Lemma behead_useqP t : uniq (behead t).
Proof. by rewrite -drop1 /=; apply/drop_uniq/uniq_useq. Qed.
Canonical behead_useq t := Useq (behead_useqP t).

Lemma filter_useqP p t : uniq (filter p t).
Proof. by apply/filter_uniq/uniq_useq. Qed.
Canonical filter_useq p t := Useq (filter_useqP p t).

Lemma take_useqP t : uniq (take n t).
Proof. by apply/take_uniq/uniq_useq. Qed.
Canonical take_useq t := Useq (take_useqP t).

Lemma drop_useqP t : uniq (drop n t).
Proof. by apply/drop_uniq/uniq_useq. Qed.
Canonical drop_useq t := Useq (drop_useqP t).

Lemma rev_useqP t : uniq (rev t).
Proof. by rewrite rev_uniq; apply: uniq_useq. Qed.
Canonical rev_useq t := Useq (rev_useqP t).

Lemma rot_useqP t : uniq (rot n t).
Proof. by rewrite rot_uniq; apply: uniq_useq. Qed.
Canonical rot_useq t := Useq (rot_useqP t).

Lemma rotr_useqP t : uniq (rotr n t).
Proof. by rewrite rotr_uniq; apply: uniq_useq. Qed.
Canonical rotr_useq t := Useq (rotr_useqP t).

Lemma sort_useqP r t : uniq (sort r t).
Proof. by rewrite sort_uniq; apply: uniq_useq. Qed.
Canonical sort_useq r t := Useq (sort_useqP r t).

End SeqUseq.

(* operations that grow the sequence split into left+right versions *)
Section UseqGrow.
Variables (T : eqType).
Implicit Type t : useq T.

(* cons that preserves the added element *)
Definition uconsl (x : T) (s : seq T) := x :: rem x s.

Lemma uconsl_cons x (s : seq T) : x \notin s -> uconsl x s = x :: s.
Proof. by move=>H; rewrite /uconsl (rem_id H). Qed.

Lemma uconsl_useqP x t : uniq (uconsl x t).
Proof.
rewrite /uconsl /=; apply/andP; split.
- by rewrite mem_rem_uniqF //; apply: uniq_useq.
by apply/rem_uniq/uniq_useq.
Qed.
Canonical uconsl_useq x t := Useq (uconsl_useqP x t).

(* cons that preserves the sequence *)
Definition uconsr (x : T) (s : seq T) := if x \in s then s else x :: s.

Lemma uconsr_cons x (s : seq T) : x \notin s -> uconsr x s = x :: s.
Proof. by move=>H; rewrite /uconsr (negbTE H). Qed.

Lemma uconsr_useqP x t : uniq (uconsr x t).
Proof.
by rewrite /uconsr; case/boolP: (x \in t)=>/= [_|->] /=;
  apply: uniq_useq.
Qed.
Canonical ucons_useq x t := Useq (uconsr_useqP x t).

(* cat that preserves the left seq *)
Fixpoint ucatl (s1 s2 : seq T) :=
  if s1 is x1::s1' then
    uconsl x1 (ucatl s1' s2)
  else s2.

Lemma ucatl_cat1 (s1 s2 : seq T) :
  uniq s1 -> ~~ has (mem s2) s1 ->
  ucatl s1 s2 = s1 ++ s2.
Proof.
elim: s1=>//= x1 s1 IH.
case/andP=>Hx1 U1; rewrite negb_or; case/andP=>Hx2 N /=.
by rewrite (IH U1 N) uconsl_cons // mem_cat negb_or Hx1.
Qed.

Lemma ucatl_cat2 (s1 s2 : seq T) :
  uniq s1 -> ~~ has (mem s1) s2 ->
  ucatl s1 s2 = s1 ++ s2.
Proof.
move=>U N; apply: ucatl_cat1=>//.
apply: contra N; case/hasP=>/= x Hx1 Hx2.
by apply/hasP; exists x.
Qed.

Lemma ucatl_useqP (t1 t2 : useq T) : uniq (ucatl t1 t2).
Proof.
case: t1; elim=>/=[_|x1 t1 IH]; first by apply: uniq_useq.
case/andP=>Hx1 /IH {}IH; apply/andP; split.
- by rewrite mem_rem_uniqF.
by apply: rem_uniq.
Qed.
Canonical ucatl_useq t1 t2 := Useq (ucatl_useqP t1 t2).

(* cat that preserves the right seq *)
Fixpoint ucatr (s1 s2 : seq T) :=
  if s1 is x1::s1' then
    uconsr x1 (ucatr s1' s2)
  else s2.

Lemma ucatr_cat1 (s1 s2 : seq T) :
  uniq s1 -> ~~ has (mem s2) s1 ->
  ucatr s1 s2 = s1 ++ s2.
Proof.
elim: s1=>//= x1 s1 IH.
case/andP=>Hx1 U1; rewrite negb_or; case/andP=>Hx2 N /=.
by rewrite (IH U1 N) uconsr_cons // mem_cat negb_or Hx1.
Qed.

Lemma ucatr_cat2 (s1 s2 : seq T) :
  uniq s1 -> ~~ has (mem s1) s2 ->
  ucatr s1 s2 = s1 ++ s2.
Proof.
move=>U N; apply: ucatr_cat1=>//.
apply: contra N; case/hasP=>/= x Hx1 Hx2.
by apply/hasP; exists x.
Qed.

Lemma ucatr_useqP (t1 t2 : useq T) : uniq (ucatr t1 t2).
Proof.
case: t1; elim=>/=[_|x1 t1 IH]; first by apply: uniq_useq.
by case/andP=>Hx1 /IH {}IH; rewrite /uconsr; case: ifP=>//= ->.
Qed.
Canonical ucatr_useq t1 t2 := Useq (ucatr_useqP t1 t2).

(* rcons that preserves the sequence *)
Definition urconsl (s : seq T) (x : T) := if x \in s then s else rcons s x.

Lemma urconsl_rcons x (s : seq T) : x \notin s -> urconsl s x = rcons s x.
Proof. by move=>H; rewrite /urconsl (negbTE H). Qed.

Lemma urconsl_useqP t x : uniq (urconsl t x).
Proof.
rewrite /urconsl /=; case/boolP: (x \in t)=>/= [_|].
- by apply: uniq_useq.
move=>N; rewrite -cats1 cat_uniq /= negb_or /= N !andbT.
by apply: uniq_useq.
Qed.
Canonical urconsl_useq t x := Useq (urconsl_useqP t x).

(* rcons that preserves the added element *)
Definition urconsr (s : seq T) (x : T) := rcons (rem x s) x.

Lemma urconsr_cons x (s : seq T) : x \notin s -> urconsr s x = rcons s x.
Proof. by move=>H; rewrite /urconsr (rem_id H). Qed.

Lemma urconsr_useqP t x : uniq (urconsr t x).
Proof.
rewrite /urconsr -cats1 cat_uniq /= negb_or !andbT.
apply/andP; split.
- by apply/rem_uniq/uniq_useq.
by rewrite mem_rem_uniqF //; apply: uniq_useq.
Qed.
Canonical urcons_useq t x := Useq (urconsr_useqP t x).

(* interaction *)

Lemma ucatl0s s : ucatl [::] s = s.
Proof. by []. Qed.

Lemma ucatr0s s : ucatr [::] s = s.
Proof. by []. Qed.

Lemma ucatl1s x s : ucatl [:: x] s = uconsl x s.
Proof. by []. Qed.

Lemma ucatr1s x s : ucatr [:: x] s = uconsr x s.
Proof. by []. Qed.

Lemma ucatls1 x s : uniq s -> ucatl s [:: x] = urconsl s x.
Proof.
elim: s=>//= y s IH; case/andP=>Ny U.
rewrite (IH U) /uconsl /urconsl /= inE.
case: ifP=>Hxs; first by rewrite orbT (rem_id Ny).
rewrite orbF; case: eqVneq=>/= [->|Nxy]; congr (y :: _).
- rewrite rem_filter; last by rewrite rcons_uniq Ny.
  rewrite -cats1 filter_cat /= eqxx /= cats0.
  by apply/all_filterP/allP=>z Hz /=; apply: contra Ny=>/eqP<-.
by apply: rem_id; rewrite mem_rcons inE negb_or eq_sym Nxy.
Qed.

Lemma ucatrs1 x s : uniq s -> ucatr s [:: x] = urconsr s x.
Proof.
elim: s=>//= y s IH; case/andP=>Ny U.
rewrite (IH U) /uconsr /urconsr /= mem_rcons inE.
case: eqVneq=>[E|Nyx] /=; first by rewrite rem_id // -E.
by rewrite rem_filter // mem_filter /= (negbTE Ny) andbF.
Qed.

End UseqGrow.

(* map also splits *)
Section UseqMap.
Variables (T S : eqType).
Implicit Types (t : useq T) (f : T -> S).

(* "map" that preserves the leftmost element when getting duplicates *)
Fixpoint umapl f (s : seq T) :=
  if s is x::s' then
    uconsl (f x) (umapl f s')
  else [::].

Lemma umapl_map f s :
  injective f -> uniq s ->
  umapl f s = map f s.
Proof.
move=>Hf; elim: s=>//= x s IH.
by case/andP=>Hx U; rewrite (IH U) uconsl_cons // mem_map.
Qed.

Lemma umapl_useqP f t : uniq (umapl f t).
Proof.
case: t; elim=>//= x t IH; case/andP=>_ /IH {}IH.
rewrite rem_filter //; apply/andP; split.
- by rewrite mem_filter /= eqxx.
by apply: filter_uniq.
Qed.
Canonical umapl_useq f t := Useq (umapl_useqP f t).

(* "map" that preserves the rightmost element when getting duplicates *)
Fixpoint umapr (f : T -> S) (s : seq T) :=
  if s is x::s' then
    uconsr (f x) (umapr f s')
  else [::].

Lemma umapr_map f s :
  injective f -> uniq s ->
  umapr f s = map f s.
Proof.
move=>Hf; elim: s=>//= x s IH.
by case/andP=>Hx U; rewrite (IH U) uconsr_cons // mem_map.
Qed.

Lemma umapr_useqP f t : uniq (umapr f t).
Proof.
case: t; elim=>//= x t IH; case/andP=>_ /IH {}IH.
by rewrite /uconsr; case: ifP=>//= ->.
Qed.
Canonical umapr_useq f t := Useq (umapr_useqP f t).

End UseqMap.
