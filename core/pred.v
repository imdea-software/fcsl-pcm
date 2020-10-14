(*
Copyright 2010 IMDEA Software Institute
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*)

(******************************************************************************)
(* This file re-implements some of ssrbool's entities in Prop universe        *)
(******************************************************************************)

From Coq Require Import ssreflect ssrbool ssrfun Setoid.
From mathcomp Require Import ssrnat seq eqtype.
From fcsl Require Import prelude.
From fcsl Require Import options.
Set Warnings "-projection-no-head-constant".

(* First some basic propositional equalities *)

Lemma andTp p : True /\ p <-> p.      Proof. by intuition. Qed.
Lemma andpT p : p /\ True <-> p.      Proof. by intuition. Qed.
Lemma andFp p : False /\ p <-> False. Proof. by intuition. Qed.
Lemma andpF p : p /\ False <-> False. Proof. by intuition. Qed.
Lemma orTp p : True \/ p <-> True.    Proof. by intuition. Qed.
Lemma orpT p : p \/ True <-> True.    Proof. by intuition. Qed.
Lemma orFp p : False \/ p <-> p.      Proof. by intuition. Qed.
Lemma orpF p : p \/ False <-> p.      Proof. by intuition. Qed.

Lemma iffC p q : (p <-> q) <-> (q <-> p). Proof. by intuition. Qed.

Declare Scope rel_scope.
Delimit Scope rel_scope with rel.
Open Scope rel_scope.

(**************************************************************************)
(* We follow ssrbool, and provide four different types of predicates.     *)
(*                                                                        *)
(* (1) Pred is the type of propositional functions                        *)
(* (2) Simpl_Pred is the type of predicates that automatically simplify   *)
(*     when used in an applicative position.                              *)
(* (3) Mem_Pred is for predicates that support infix notation x \In P     *)
(* (4) PredType is the structure for interpreting various types, such as  *)
(* lists, tuples, etc. as predicates.                                     *)
(*                                                                        *)
(* Important point is that custom lemmas over predicates can be stated in *)
(* terms of Pred, while Simpl_Pred, Mem_Pred and PredType are for         *)
(* technical developments used in this file only. More on this point      *)
(* can be found in ssrbool.                                               *)
(**************************************************************************)

Definition Pred T := T -> Prop.
Identity Coercion fun_of_Pred : Pred >-> Funclass.

Notation xPred0 := (fun _ => False).
Notation xPred1 := (fun x y => x = y).
Notation xPredT := (fun _ => True).
Notation xPredI := (fun (p1 p2 : Pred _) x => p1 x /\ p2 x).
Notation xPredU := (fun (p1 p2 : Pred _) x => p1 x \/ p2 x).
Notation xPredC := (fun (p : Pred _) x => ~ p x).
Notation xPredD := (fun (p1 p2 : Pred _) x => ~ p2 x /\ p1 x).
Notation xPreim := (fun f (p : Pred _) x => p (f x)).

Section Predicates.
Variable T : Type.

(* simple predicates *)

Definition Simpl_Pred := simpl_fun T Prop.
Definition SimplPred (p : Pred T) : Simpl_Pred := SimplFun p.
Coercion Pred_of_Simpl (p : Simpl_Pred) : Pred T := p : T -> Prop.

(* it's useful to declare the operations as simple predicates, so that *)
(* complex expressions automatically reduce when used in applicative   *)
(* positions *)

Definition Pred0 := SimplPred xPred0.
Definition Pred1 x := SimplPred (xPred1 x).
Definition PredT := SimplPred xPredT.
Definition PredI p1 p2 := SimplPred (xPredI p1 p2).
Definition PredU p1 p2 := SimplPred (xPredU p1 p2).
Definition PredC p := SimplPred (xPredC p).
Definition PredD p1 p2 := SimplPred (xPredD p1 p2).
Definition Preim rT f (d : Pred rT) := SimplPred (xPreim f d).

(* membership predicates *)

Variant Mem_Pred : Type := MemProp of Pred T.
Definition isMem pT toPred mem := mem = (fun p : pT => MemProp [eta toPred p]).

(* the general structure for predicates *)

Structure PredType : Type := PropPredType {
  Pred_Sort :> Type;
  toPred : Pred_Sort -> Pred T;
  _ : {mem | isMem toPred mem}}.

Definition mkPredType pT toP := PropPredType (exist (@isMem pT toP) _ (erefl _)).

(* Pred, SimplPred, Mem_Pred, pred and simpl_pred are PredType's *)
Canonical Structure PredPredType := Eval hnf in @mkPredType (Pred T) id.
Canonical Structure SimplPredPredType := Eval hnf in mkPredType Pred_of_Simpl.
Canonical Structure PropfunPredType := Eval hnf in @mkPredType (T -> Prop) id.
Coercion Pred_of_Mem mp : Pred_Sort PredPredType :=
  let: MemProp p := mp in [eta p].
Canonical Structure MemPredType := Eval hnf in mkPredType Pred_of_Mem.
Canonical Structure predPredType := Eval hnf in @mkPredType (pred T) id.
Canonical Structure simplpredPredType :=
  Eval hnf in @mkPredType (simpl_pred T) (fun p x => p x).

End Predicates.

Arguments Pred0 {T}.
Arguments PredT {T}.
Prenex Implicits Pred0 PredT PredI PredU PredC PredD Preim.

Notation "r1 +p r2" := (PredU r1 r2 : Pred _)
  (at level 55, right associativity) : rel_scope.
Notation "r1 *p r2" := (xPredI r1 r2 : Pred _)
  (at level 45, right associativity) : rel_scope.

Notation "[ 'Pred' : T | E ]" := (SimplPred (fun _ : T => E))
  (at level 0, format "[ 'Pred' :  T  |  E ]") : fun_scope.
Notation "[ 'Pred' x | E ]" := (SimplPred (fun x => E))
  (at level 0, x ident, format "[ 'Pred'  x  |  E ]") : fun_scope.
Notation "[ 'Pred' x : T | E ]" := (SimplPred (fun x : T => E))
  (at level 0, x ident, only parsing) : fun_scope.
Notation "[ 'Pred' x y | E ]" := (SimplPred (fun t => let: (x, y) := t in E))
  (at level 0, x ident, y ident, format "[ 'Pred'  x  y  |  E ]") : fun_scope.
Notation "[ 'Pred' x y : T | E ]" :=
  (SimplPred (fun t : (T*T) => let: (x, y) := t in E))
  (at level 0, x ident, y ident, only parsing) : fun_scope.

Definition repack_Pred T pT :=
  let: PropPredType _ a mP := pT return {type of @PropPredType T for pT} -> _ in
   fun k => k a mP.

Notation "[ 'PredType' 'of' T ]" := (repack_Pred (fun a => @PropPredType _ T a))
  (at level 0, format "[ 'PredType'  'of'  T ]") : form_scope.

Notation Pred_Class := (Pred_Sort (PredPredType _)).
Coercion Sort_of_Simpl_Pred T (p : Simpl_Pred T) : Pred_Class := p : Pred T.

Definition PredArgType := Type.
Coercion Pred_of_argType (T : PredArgType) : Simpl_Pred T := PredT.

Notation "{ :: T }" := (T%type : PredArgType)
  (at level 0, format "{ ::  T }") : type_scope.

(* These must be defined outside a Section because "cooking" kills the *)
(* nosimpl tag. *)
Definition Mem T (pT : PredType T) : pT -> Mem_Pred T :=
  nosimpl (let: PropPredType _ _ (exist mem _) := pT return pT -> _ in mem).
Definition InMem T x mp := nosimpl Pred_of_Mem T mp x.

Prenex Implicits Mem.

(* Membership Predicates can be used as simple ones *)
Coercion Pred_of_Mem_Pred T mp := [Pred x : T | InMem x mp].

(* equality and subset *)

Definition EqPredType T (pT : PredType T) (p1 p2 : pT) :=
  forall x : T, toPred p1 x <-> toPred p2 x.

Definition SubPredType T (pT : PredType T) (p1 p2 : pT) :=
  forall x : T, toPred p1 x -> toPred p2 x.

Definition EqSimplPred T (p1 p2 : Simpl_Pred T) := EqPredType p1 p2.
Definition SubSimplPred T (p1 p2 : Simpl_Pred T) := SubPredType p1 p2.

Definition EqPredFun T1 T2 (pT2 : PredType T2) p1 p2 :=
  forall x : T1, @EqPredType T2 pT2 (p1 x) (p2 x).
Definition SubPredFun T1 T2 (pT2 : PredType T2) p1 p2 :=
  forall x : T1, @SubPredType T2 pT2 (p1 x) (p2 x).

Definition EqMem T p1 p2 := forall x : T, InMem x p1 <-> InMem x p2.
Definition SubMem T p1 p2 := forall x : T, InMem x p1 -> InMem x p2.

Notation "A <~> B" := (@EqPredType _ _ A B)
  (at level 70, no associativity) : rel_scope.
Notation "A ~> B" := (@SubPredType _ _ A B)
  (at level 70, no associativity) : rel_scope.
Notation "A <~1> B" := (@EqPredFun _ _ _ A B)
  (at level 70, no associativity) : rel_scope.
Notation "A ~1> B" := (@SubPredFun _ _ _ A B)
  (at level 70, no associativity) : rel_scope.

Notation "x \In A" := (InMem x (Mem A))
  (at level 70, no associativity) : rel_scope.
Notation "x \Notin A" := (~ (x \In A))
  (at level 70, no associativity) : rel_scope.
Notation "A =p B" := (EqMem (Mem A) (Mem B))
  (at level 70, no associativity) : type_scope.
Notation "A <=p B" := (SubMem (Mem A) (Mem B))
  (at level 70, no associativity) : type_scope.

(* Some notation for turning PredTypes into Pred or Simple Pred *)
Notation "[ 'Mem' A ]" := (Pred_of_Simpl (Pred_of_Mem_Pred (Mem A)))
  (at level 0, only parsing) : fun_scope.
Notation "[ 'PredI' A & B ]" := (PredI [Mem A] [Mem B])
  (at level 0, format "[ 'PredI'  A  &  B ]") : fun_scope.
Notation "[ 'PredU' A & B ]" := (PredU [Mem A] [Mem B])
  (at level 0, format "[ 'PredU'  A  &  B ]") : fun_scope.
Notation "[ 'PredD' A & B ]" := (PredD [Mem A] [Mem B])
  (at level 0, format "[ 'PredD'  A  &  B ]") : fun_scope.
Notation "[ 'PredC' A ]" := (PredC [Mem A])
  (at level 0, format "[ 'PredC'  A ]") : fun_scope.
Notation "[ 'Preim' f 'of' A ]" := (Preim f [Mem A])
  (at level 0, format "[ 'Preim'  f  'of'  A ]") : fun_scope.

Notation "[ 'Pred' x \In A ]" := [Pred x | x \In A]
  (at level 0, x ident, format "[ 'Pred'  x  \In  A ]") : fun_scope.
Notation "[ 'Pred' x \In A | E ]" := [Pred x | (x \In A) /\ E]
  (at level 0, x ident, format "[ 'Pred'  x  \In  A  |  E ]") : fun_scope.
Notation "[ 'Pred' x y \In A & B | E ]" :=
  [Pred x y | (x \In A) /\ (y \In B) /\ E]
  (at level 0, x ident, y ident,
   format "[ 'Pred'  x  y  \In  A  &  B  |  E ]") : fun_scope.
Notation "[ 'Pred' x y \In A & B ]" := [Pred x y | (x \In A) /\ (y \In B)]
  (at level 0, x ident, y ident,
   format "[ 'Pred'  x  y  \In  A  &  B ]") : fun_scope.
Notation "[ 'Pred' x y \In A | E ]" := [Pred x y \In A & A | E]
  (at level 0, x ident, y ident,
   format "[ 'Pred'  x  y  \In  A  |  E ]") : fun_scope.
Notation "[ 'Pred' x y \In A ]" := [Pred x y \In A & A]
  (at level 0, x ident, y ident,
   format "[ 'Pred'  x  y  \In  A ]") : fun_scope.

Section Simplifications.
Variables (T : Type) (pT : PredType T).

Lemma Mem_toPred : forall (p : pT), Mem (toPred p) = Mem p.
Proof. by rewrite /Mem; case: pT => T1 app1 [mem1  /= ->]. Qed.

Lemma toPredE x (p : pT) : toPred p x = (x \In p).
Proof. by rewrite -Mem_toPred. Qed.

Lemma In_Simpl x (p : Simpl_Pred T) : (x \In p) = p x.
Proof. by []. Qed.

Lemma Simpl_PredE (p : Pred T) : p <~> [Pred x | p x].
Proof. by []. Qed.

Lemma Mem_Simpl (p : Simpl_Pred T) : Mem p = p :> Pred T.
Proof. by []. Qed.

Definition MemE := Mem_Simpl. (* could be extended *)

Lemma Mem_Mem (p : pT) : (Mem (Mem p) = Mem p) * (Mem [Mem p] = Mem p).
Proof. by rewrite -Mem_toPred. Qed.

End Simplifications.

(**************************************)
(* Definitions and lemmas for setoids *)
(**************************************)

Section RelProperties.
Variables (T : Type) (pT : PredType T).

Lemma EqPredType_refl (r : pT) : EqPredType r r. Proof. by []. Qed.
Lemma SubPredType_refl (r : pT) : SubPredType r r. Proof. by []. Qed.

Lemma EqPredType_sym (r1 r2 : pT) : EqPredType r1 r2 -> EqPredType r2 r1.
Proof. by move=>H1 x; split; move/H1. Qed.

Lemma EqPredType_trans' (r1 r2 r3 : pT) :
  EqPredType r1 r2 -> EqPredType r2 r3 -> EqPredType r1 r3.
Proof. by move=>H1 H2 x; split; [move/H1; move/H2 | move/H2; move/H1]. Qed.

Lemma SubPredType_trans' (r1 r2 r3 : pT) :
  SubPredType r1 r2 -> SubPredType r2 r3 -> SubPredType r1 r3.
Proof. by move=>H1 H2 x; move/H1; move/H2. Qed.

Definition EqPredType_trans r2 r1 r3 := @EqPredType_trans' r1 r2 r3.
Definition SubPredType_trans r2 r1 r3 := @SubPredType_trans' r1 r2 r3.
End RelProperties.

Hint Resolve EqPredType_refl SubPredType_refl : core.

(* Declaration of relations *)

(* Unfortunately, Coq setoids don't seem to understand implicit coercions *)
(* and canonical structures so we have to repeat relation declarations    *)
(* for all instances. This is really annoying, but at least we don't have *)
(* to reprove the lemmas on refl, sym and trans.                          *)

Add Parametric Relation T (pT : PredType T) : pT (@EqPredType _ pT)
   reflexivity proved by (@EqPredType_refl _ _)
  symmetry proved by (@EqPredType_sym _ _)
  transitivity proved by (@EqPredType_trans' _ _) as EqPredType_rel.

Add Parametric Relation T : (Simpl_Pred T) (@EqSimplPred _)
  reflexivity proved by (@EqPredType_refl _ _)
  symmetry proved by (@EqPredType_sym _ _)
  transitivity proved by (@EqPredType_trans' _ _) as EqSimplPred_rel.

Add Parametric Relation T : (Simpl_Pred T) (@SubSimplPred _)
  reflexivity proved by (@SubPredType_refl _ _)
  transitivity proved by (@SubPredType_trans' _ _) as SubSimplPred_rel.

Add Parametric Relation T : (Mem_Pred T) (@EqMem T)
  reflexivity proved by (@EqPredType_refl _ _)
  symmetry proved by (@EqPredType_sym _ _)
  transitivity proved by (@EqPredType_trans' _ _) as EqMem_rel.

Add Parametric Relation T : (Mem_Pred T) (@SubMem _)
  reflexivity proved by (@SubPredType_refl _ _)
  transitivity proved by (@SubPredType_trans' _ _) as SubMem_rel.

(* Declaring morphisms. *)

Add Parametric Morphism T : (@Pred_of_Simpl T) with signature
      @EqSimplPred _ ==> @EqPredType T (PredPredType T) as Pred_of_Simpl_morph.
Proof. by []. Qed.

Add Parametric Morphism T (pT : PredType T) : (@EqPredType T pT) with signature
    @EqPredType _ _ ==> @EqPredType _ _ ==> iff as EqPredType_morph.
Proof. by move=>r1 s1 H1 r2 s2 H2; rewrite H1 H2. Qed.

Add Parametric Morphism T (pT : PredType T) : (@SubPredType T pT) with signature
    @EqPredType _ _ ==> @EqPredType _ _ ==> iff as SubPred_morph.
Proof. by move=>r1 s1 H1 r2 s2 H2; split=>H x; move/H1; move/H; move/H2. Qed.

Add Parametric Morphism T : (@InMem T) with signature
    @eq _ ==> @EqMem _ ==> iff as InMem_morph.
Proof. by move=>x r s H; split; move/H. Qed.

Add Parametric Morphism T (pT : PredType T) : (@Mem T pT) with signature
  @EqPredType _ _ ==> @EqMem _ as Mem_morhp.
Proof. by move=>x y H p; rewrite /EqPredType -!toPredE in H *; rewrite H. Qed.

Add Parametric Morphism T : (@PredU T) with signature
    @EqPredType _ _ ==> @EqPredType _ _ ==> @EqSimplPred _ as predU_morph.
Proof.
move=>r1 s1 H1 r2 h2 H2 x; split;
by case; [move/H1 | move/H2]=>/=; auto.
Qed.

Add Parametric Morphism T : (@PredI T) with signature
    @EqPredType _ _ ==> @EqPredType _ _ ==> @EqPredType _ _ as predI_morph.
Proof.
move=>r1 s1 H1 r2 s2 H2 x; split;
by case; move/H1=>T1; move/H2=>T2.
Qed.

Add Parametric Morphism T : (@PredC T) with signature
    @EqPredType _ _ ==> @EqPredType _ _ as predC_morph.
Proof. by move=>r s H x; split=>H1; apply/H. Qed.

Section RelLaws.
Variable (T : Type).
Implicit Type r : Pred T.

Lemma orrI r : r +p r <~> r.
Proof.  by move=>x; split; [case | left]. Qed.

Lemma orrC r1 r2 : r1 +p r2 <~> r2 +p r1.
Proof. move=>x; split=>/=; tauto. Qed.

Lemma orr0 r : r +p Pred0 <~> r.
Proof. by move=>x; split; [case | left]. Qed.

Lemma or0r r : Pred0 +p r <~> r.
Proof. by rewrite orrC orr0. Qed.

Lemma orrCA r1 r2 r3 : r1 +p r2 +p r3 <~> r2 +p r1 +p r3.
Proof. by move=>x; split=>/=; intuition. Qed.

Lemma orrAC r1 r2 r3 : (r1 +p r2) +p r3 <~> (r1 +p r3) +p r2.
Proof. by move=>?; split=>/=; intuition. Qed.

Lemma orrA r1 r2 r3 : (r1 +p r2) +p r3 <~> r1 +p r2 +p r3.
Proof. by rewrite (orrC r2) orrCA orrC. Qed.

(* absorption *)
Lemma orrAb r1 r2 : r1 <~> r1 +p r2 <-> r2 ~> r1.
Proof.
split; first by move=>-> x /=; auto.
move=>H x /=; split; first by auto.
by case=>//; move/H.
Qed.

Lemma sub_orl r1 r2 : r1 ~> r1 +p r2. Proof. by left. Qed.
Lemma sub_orr r1 r2 : r2 ~> r1 +p r2. Proof. by right. Qed.

End RelLaws.

Section SubMemLaws.
Variable T : Type.
Implicit Type p q : Pred T.

Lemma subp_refl p : p <=p p.
Proof. by []. Qed.

Lemma subp_asym p1 p2 : p1 <=p p2 -> p2 <=p p1 -> p1 =p p2.
Proof. by move=>H1 H2 x; split; [move/H1 | move/H2]. Qed.

Lemma subp_trans p2 p1 p3 : p1 <=p p2 -> p2 <=p p3 -> p1 <=p p3.
Proof. by move=>H1 H2 x; move/H1; move/H2. Qed.

Lemma subp_or p1 p2 q : p1 <=p q /\ p2 <=p q <-> p1 +p p2 <=p q.
Proof.
split=>[[H1] H2 x|H1]; first by case; [move/H1 | move/H2].
by split=>x H2; apply: H1; [left | right].
Qed.

Lemma subp_and p1 p2 q : q <=p p1 /\ q <=p p2 <-> q <=p p1 *p p2.
Proof.
split=>[[H1] H2 x|] H; last by split=>x; case/H.
by split; [apply: H1 | apply: H2].
Qed.

Lemma subp_orl p1 p2 q : p1 <=p p2 -> p1 +p q <=p p2 +p q.
Proof. by move=>H x; case; [move/H; left|right]. Qed.

Lemma subp_orr p1 p2 q : p1 <=p p2 -> q +p p1 <=p q +p p2.
Proof. by move=>H x; case; [left | move/H; right]. Qed.

Lemma subp_andl p1 p2 q : p1 <=p p2 -> p1 *p q <=p p2 *p q.
Proof. by by move=>H x [H1 H2]; split; [apply: H|]. Qed.

Lemma subp_andr p1 p2 q : p1 <=p p2 -> q *p p1 <=p q *p p2.
Proof. by move=>H x [H1 H2]; split; [|apply: H]. Qed.

End SubMemLaws.

Hint Resolve subp_refl : core.

Section ListMembership.
Variable T : Type.

Fixpoint Mem_Seq (s : seq T) :=
  if s is y::s' then (fun x => x = y \/ Mem_Seq s' x) else xPred0.

Definition EqSeq_Class := seq T.
Identity Coercion seq_of_EqSeq : EqSeq_Class >-> seq.

Coercion Pred_of_Eq_Seq (s : EqSeq_Class) : Pred_Class := [eta Mem_Seq s].

Canonical Structure seq_PredType := Eval hnf in @mkPredType T (seq T) Pred_of_Eq_Seq.
(* The line below makes Mem_Seq a canonical instance of topred. *)
Canonical Structure Mem_Seq_PredType := Eval hnf in mkPredType Mem_Seq.

Lemma In_cons y s x : (x \In y :: s) <-> (x = y) \/ (x \In s).
Proof. by []. Qed.

Lemma In_nil x : (x \In [::]) <-> False.
Proof. by []. Qed.

Lemma Mem_Seq1 x y : (x \In [:: y]) <-> (x = y).
Proof. by rewrite In_cons orpF. Qed.

Definition InE := (Mem_Seq1, In_cons, In_Simpl).

Lemma Mem_cat x : forall s1 s2, (x \In s1 ++ s2) <-> x \In s1 \/ x \In s2.
Proof.
elim=>[|y s1 IH] s2 /=; first by split; [right | case].
rewrite !InE /=.
split.
- case=>[->|/IH]; first by left; left.
  by case; [left; right | right].
case; first by case; [left | move=>H; right; apply/IH; left].
by move=>H; right; apply/IH; right.
Qed.

Lemma In_split x s : x \In s -> exists s1 s2, s = s1 ++ x :: s2.
Proof.
elim:s=>[|y s IH] //=; rewrite InE.
case=>[<-|]; first by exists [::], s.
by case/IH=>s1 [s2 ->]; exists (y :: s1), s2.
Qed.

End ListMembership.

Lemma Mem_map T T' (f : T -> T') x (s : seq T) :
         x \In s -> f x \In (map f s).
Proof.
elim: s=>[|y s IH] //; rewrite InE /=.
by case=>[<-|/IH]; [left | right].
Qed.

Lemma Mem_map_inv T T' (f : T -> T') x (s : seq T) :
        x \In (map f s) -> exists y, x = f y /\ y \In s.
Proof.
elim: s=>[|y s IH] //=; rewrite InE /=.
case; first by move=>->; exists y; split=>//; left.
by case/IH=>z [->]; exists z; split=>//; right.
Qed.

Prenex Implicits Mem_map_inv.

(* for equality types, membership predicates coincide *)
Lemma mem_seqP (A : eqType) x (s : seq A) : reflect (x \In s) (x \in s).
Proof.
elim: s=>[|y s IH]; first by constructor.
rewrite inE; case: eqP=>[<-|H /=]; first by constructor; left.
by apply: equivP IH _; rewrite InE; split; [right | case].
Qed.

(* Setoids for extensional equality of functions *)
Add Parametric Relation A B : (A -> B) (@eqfun _ _)
  reflexivity proved by (@frefl B A)
  symmetry proved by (@fsym B A)
  transitivity proved by (@ftrans B A) as eqfun_morph.

(***********************************)
(* Image of a collective predicate *)
(***********************************)

Section Image.
Variables (A B : Type) (P : Pred A) (f : A -> B).

Inductive image_spec b : Prop := Im_mem a of b = f a & a \In P.

Definition Image' : Pred B := image_spec.

End Image.

(* swap to make the notation consider P before E; helps inference *)
Notation Image f P := (Image' P f).

Notation "[ 'Image' E | i <- s ]" := (Image (fun i => E) s)
  (at level 0, E at level 99, i ident,
   format "[ '[hv' 'Image'  E '/ '  |  i  <-  s ] ']'") : rel_scope.

Notation "[ 'Image' E | i <- s & C ]" := [Image E | i <- [PredI s & C]]
  (at level 0, E at level 99, i ident,
   format "[ '[hv' 'Image'  E '/ '  |  i  <-  s '/ '  &  C ] ']'") : rel_scope.

Notation "[ 'Image' E | i : T <- s ]" := (Image (fun i : T => E) s)
  (at level 0, E at level 99, i ident, only parsing) : rel_scope.

Notation "[ 'Image' E | i : T <- s & C ]" :=
  [Image E | i : T <- [PredI s & C]]
  (at level 0, E at level 99, i ident, only parsing) : rel_scope.

Lemma Image_mem A B (f : A -> B) (P : Pred A) x : x \In P -> f x \In Image f P.
Proof. by apply: Im_mem. Qed.

Lemma Image_inj_sub A B (f : A -> B) (X1 X2 : Pred A) :
        injective f -> Image f X1 <=p Image f X2 -> X1 <=p X2.
Proof. by move=>H E x /(Image_mem f) /E [y] /H ->. Qed.

Lemma Image_inj_eqmem A B (f : A -> B) (X1 X2 : Pred A) :
        injective f -> Image f X1 =p Image f X2 -> X1 =p X2.
Proof. by move=>H E; split; apply: Image_inj_sub H _ _; rewrite E. Qed.

Lemma ImageU A B (f : A -> B) (X1 X2 : Pred A) :
        Image f (PredU X1 X2) =p [PredU Image f X1 & Image f X2].
Proof.
move=>x; split.
- by case=>y -> [H|H]; [left | right]; apply: Image_mem.
by case; case=>y -> H; apply: Image_mem; [left | right].
Qed.

Lemma ImageIm A B C (f1 : B -> C) (f2 : A -> B) (X : Pred A) :
        Image f1 (Image f2 X) =p Image (f1 \o f2) X.
Proof.
move=>x; split; first by case=>_ -> [x' ->] H; exists x'.
by case=>a -> H; exists (f2 a)=>//; exists a.
Qed.

Lemma ImageEq A B (f1 f2 : A -> B) (X : Pred A) :
        f1 =1 f2 -> Image f1 X =p Image f2 X.
Proof. by move=>H x; split; case=>a ->; exists a. Qed.


(**********************************)
(**********************************)
(*      Theory of relations       *)
(**********************************)
(**********************************)

(* Not a definition to avoid universe inconsistencies. *)

Local Notation Rel A := (A -> A -> Prop).

(**********************************)
(*   Special cases of relations   *)
(**********************************)

Section RelationProperties.

Variables (A : Type) (R : Rel A).

Definition Total := forall x y, R x y \/ R y x.
Definition Transitive := forall y x z, R x y -> R y z -> R x z.

Definition Symmetric := forall x y, R x y <-> R y x.
Definition pre_Symmetric := forall x y, R x y -> R y x.
Definition Antisymmetric := forall x y, R x y -> R y x -> x = y.

Lemma sym_iff_pre_sym : pre_Symmetric <-> Symmetric.
Proof. by split=> S x y; [split; apply: S | rewrite S]. Qed.

(* Do NOT use Reflexive for actual lemmas, because auto does not unfold definitions,
   so Hint Resolve lemma_refl won't work *)
Definition Reflexive := forall x, R x x.
Definition Irreflexive := forall x, R x x -> False.

Definition left_Transitive := forall x y, R x y -> forall z, R x z <-> R y z.
Definition right_Transitive := forall x y, R x y -> forall z, R z x <-> R z y.

(** Partial equivalence relation *)
Section PER.

Hypotheses (symR : Symmetric) (trR : Transitive).

Lemma sym_left_Transitive : left_Transitive.
Proof. by move=> x y Rxy z; split; apply: trR; rewrite // symR. Qed.

Lemma sym_right_Transitive : right_Transitive.
Proof. by move=> x y Rxy z; rewrite !(symR z); apply: sym_left_Transitive. Qed.

End PER.

(* We define the equivalence property with prenex quantification so that it   *)
(* can be localized using the {in ..., ..} form defined below.                *)

Definition Equivalence_rel := forall x y z, R z z /\ (R x y -> R x z <-> R y z).

Lemma Equivalence_relP : Equivalence_rel <-> Reflexive /\ left_Transitive.
Proof.
split=> [eqiR | [Rxx ltrR] x y z]; last by split=>// Rxy; apply: ltrR.
by split=> [x | x y Rxy z]; [case: (eqiR x x x)| case: (eqiR x y z)=> _ /(_ Rxy)].
Qed.

Lemma Equivalence_relS : Equivalence_rel <-> [/\ Reflexive, Symmetric & Transitive].
Proof.
split; last first.
- case=>r s t; split; first by apply: r.
  by move=>Rxy; split; apply: t=>//; apply/s.
case/Equivalence_relP=>r t; split=>//; last first.
- by move=>x y z Ryx Rxz; rewrite (t y x Ryx).
move=>x y; split.
- by move=>Rxy; rewrite -(t x y Rxy); apply: r.
by move=>Ryx; rewrite -(t y x Ryx); apply: r.
Qed.

(** _Functional_ (a.k.a. deterministic) relation *)
Definition functional := forall x y1 y2, R x y1 -> R x y2 -> y1 = y2.
(* a relation preserves the resource invariant *)
Definition preserved (P : A -> Prop) R := forall x y, R x y -> P x -> P y.
Definition bpreserved (P : A -> Prop) R := forall x y, R x y -> P y -> P x.

End RelationProperties.

Arguments sym_iff_pre_sym {A R}.


(* Lifting equivalence relation to option type *)

Section OptionRel.
Variables (A : Type) (R : Rel A).

Definition optionR (a1 a2 : option A) :=
  match a1, a2 with
    Some e1, Some e2 => R e1 e2
  | None, None => True
  | _, _ => False
  end.

Lemma Reflexive_optionR : Reflexive R -> Reflexive optionR.
Proof. by move=>r; case. Qed.

Lemma Symmetric_optionR : Symmetric R -> Symmetric optionR.
Proof. by move=>s; case=>[x|]; case=>[y|] //=. Qed.

Lemma Transitive_optionR : Transitive R -> Transitive optionR.
Proof. by move=>t; case=>[x|]; case=>[y|]; case=>[z|] //=; apply: t. Qed.

Lemma Equivalence_optionR : Equivalence_rel R -> Equivalence_rel optionR.
Proof.
case/Equivalence_relS=>r s t; apply/Equivalence_relS; split.
- by apply: Reflexive_optionR.
- by apply: Symmetric_optionR.
by apply: Transitive_optionR.
Qed.

End OptionRel.

(* Lifting equivalence relation to sum type *)
Section SumRel.
Variables (A1 A2 : Type) (R1 : Rel A1) (R2 : Rel A2).

Definition sumR (x y : A1 + A2) :=
  match x, y with
    inl x1, inl y1 => R1 x1 y1
  | inr x2, inr y2 => R2 x2 y2
  | _, _ => False
  end.

Lemma Reflexive_sumR : Reflexive R1 -> Reflexive R2 -> Reflexive sumR.
Proof. by move=>r1 r2; case. Qed.

Lemma Symmetric_sumR : Symmetric R1 -> Symmetric R2 -> Symmetric sumR.
Proof. by move=>s1 s2; case=>x; case=>y //=. Qed.

Lemma Transitive_sumR : Transitive R1 -> Transitive R2 -> Transitive sumR.
Proof. by move=>t1 t2; case=>x; case=>y; case=>z //; [apply:t1 | apply:t2]. Qed.

Lemma Equivalence_sumR :
        Equivalence_rel R1 -> Equivalence_rel R2 -> Equivalence_rel sumR.
Proof.
case/Equivalence_relS=>r1 s1 t1 /Equivalence_relS [r2 s2 t2].
apply/Equivalence_relS; split.
- by apply: Reflexive_sumR.
- by apply: Symmetric_sumR.
by apply: Transitive_sumR.
Qed.

End SumRel.


(****************)
(* Transitivity *)
(****************)

Section Transitivity.
Variables (A : Type) (R : Rel A).

Lemma trans_imp (F : A -> Prop) : Transitive (fun x y => F x -> F y).
Proof. by move=>x y z H1 H2 /H1. Qed.

Lemma trans_eq B (f : A -> B) : Transitive (fun x y => f x = f y).
Proof. by move=>x y z ->. Qed.

Lemma rev_Trans : Transitive R -> Transitive (fun x y => R y x).
Proof. by move=> trR x y z Ryx Rzy; apply: trR Rzy Ryx. Qed.
End Transitivity.

Hint Resolve trans_imp trans_eq : core.

(**********************************************)
(* Reflexive-Transitive closure of a relation *)
(**********************************************)

Fixpoint iter' T (g : T -> T -> Prop) n s1 s2 :=
  if n is n'.+1 then exists s, g s1 s /\ iter' g n' s s2 else s1 = s2.
Definition iter T (g : T -> T -> Prop) s1 s2 := exists n, iter' g n s1 s2.
(* curry the iteration *)
Definition iterc A T (g : A -> T -> A -> T -> Prop) a1 s1 a2 s2 :=
  iter (fun '(a1, a2) '(b1, b2) => g a1 a2 b1 b2) (a1, s1) (a2, s2).

Section IteratedRels.
Variable T : Type.
Implicit Type g : T -> T -> Prop.

Lemma iter_refl g s : iter g s s.
Proof. by exists 0. Qed.

Lemma iter_trans g : Transitive (iter g).
Proof.
move=> s2 s1 s3; case=>n; elim: n s1 =>[|n IH] s1 /=; first by move=>->.
by case=>s [H1 H2] /(IH _ H2) [m]; exists m.+1, s.
Qed.

Lemma iterS g n s1 s2 : iter' g n.+1 s1 s2 <-> exists s, iter' g n s1 s /\ g s s2.
Proof.
elim: n s1=>[|n IH] s1.
- by split; [case=>s [H <-]; exists s1 | case=>s [<- H]; exists s2].
split; first by case=>s [H1] /IH [s'][H G]; exists s'; split=>//; exists s.
by case=>s [[s'][H1 H G]]; exists s'; split=>//; apply/IH; exists s.
Qed.

Lemma iter'_sub g g' n s1 s2 :
        (forall s1 s2, g s1 s2 -> g' s1 s2) ->
        iter' g n s1 s2 -> iter' g' n s1 s2.
Proof. by move=>H; elim: n s1=>[|n IH] s1 //= [s][/H G] /IH; exists s. Qed.

Lemma iter_sub g g' s1 s2 :
        (forall s1 s2, g s1 s2 -> g' s1 s2) -> iter g s1 s2 -> iter g' s1 s2.
Proof. by move=>H [n]; exists n; apply: iter'_sub H _. Qed.

Lemma iter1 g s1 s2 : g s1 s2 -> iter g s1 s2.
Proof. by exists 1, s2. Qed.

Lemma iter'_add g n1 n2 s1 s2 s3 :
        iter' g n1 s1 s2 -> iter' g n2 s2 s3 ->
        iter' g (n1 + n2) s1 s3.
Proof.
elim: n1 s1 s2=>[|n1 IH] s1 s2 /=; first by rewrite add0n=>->.
by case=>s [H1 H2] /(IH _ _ H2); exists s.
Qed.

Lemma iter'_split g n1 n2 s1 s2 :
        iter' g (n1 + n2) s1 s2 ->
        exists s, iter' g n1 s1 s /\ iter' g n2 s s2.
Proof.
elim: n1 s1 s2=>[|n1 IH] s1 s2 /=; first by rewrite add0n; exists s1.
by case=>s [H1] {}/IH [s'][H2 H3]; exists s'; split=>//; exists s.
Qed.

End IteratedRels.

Lemma iter2 A T (g : A -> T -> A -> T -> Prop) x1 s1 x2 s2 :
        g x1 s1 x2 s2 -> iterc g x1 s1 x2 s2.
Proof. by apply: iter1. Qed.

Lemma iter_pres' A (g : Rel A) n C : preserved C g -> preserved C (iter' g n).
Proof.
move=>coh; elim: n=>[|n IH] x y /=; first by move=><-.
by case=>z [/coh H1] H2 /H1; apply: IH.
Qed.

Lemma iter_pres A (g : Rel A) C : preserved C g -> preserved C (iter g).
Proof. by move=>pres x y [n] /(iter_pres' pres). Qed.

Prenex Implicits iter1 iter2.
Arguments iter_refl {T g s}.
Hint Resolve iter_refl : core.

(*****************************************************)
(* Induction lemmas for Reflexive Transitive closure *)
(*****************************************************)

Section ReflexiveTransitiveClosureInductions.
Variables (A : Type) (R : Rel A).
Implicit Types (C P Q : A -> Prop) (F : Rel A).

Lemma iterf_ind C F :
        (forall x, C x -> F x x) ->
        Transitive F ->
        (forall x y, R x y -> C x -> C y /\ F x y) ->
        forall x y, iter R x y -> C x -> F x y.
Proof.
move=>X Y H x y [n]; elim: n x=>[|n IH] x; first by move=>->; apply: X.
by case=>z [O] {}/IH Z /(H _ _ O) [/Z] H1 H2; apply: Y H2 H1.
Qed.

Lemma iterb_ind C F :
        (forall x, C x -> F x x) ->
        Transitive F ->
        (forall x y, R x y -> C y -> C x /\ F x y) ->
        forall x y, iter R x y -> C y -> F x y.
Proof.
move=>X Y H x y [n]; elim: n x y=>[|n IH] x y; first by move=>->; apply: X.
by case/iterS=>z[]{}/IH Z O /(H _ _ O) [/Z]; apply: Y.
Qed.

Lemma iter_ind C :
        (forall x y, R x y -> C x -> C y) ->
        forall x y, iter R x y -> C x -> C y.
Proof.
move=>H x y /(@iterf_ind (fun => True) (fun x y => C x -> C y)).
by apply=>// t1 t2 /H X _.
Qed.

(* induction under a stable condition; this is always what we have *)
Lemma iters_ind C F :
        (forall x, C x -> F x x) -> Transitive F ->
        (forall x y, iter R x y -> C x -> C y) ->
        (forall x y, R x y -> C x -> F x y) ->
         forall x y, iter R x y -> C x -> F x y.
Proof.
move=>H1 H2 H3 H x y; apply: iterf_ind x y=>// x y.
by move=>H4 H5; split; [apply: H3 (iter1 H4) H5 | apply: H H5].
Qed.

(* can relax the transitivity condition *)
Lemma iters_ind' C F :
        (forall x, C x -> F x x) ->
        (forall x y z, C x -> C y -> C z -> F x y -> F y z -> F x z) ->
        (forall x y, iter R x y -> C x -> C y) ->
        (forall x y, R x y -> C x -> F x y) ->
         forall x y, iter R x y -> C x -> F x y.
Proof.
move=>H1 H2 H3 H4 x y [n]; elim: n x=>[|n IH] x.
- by move=>->; apply: H1.
case=>z [O] H Cx; move: (H3 _ _ (iter1 O) Cx)=>Cz.
by apply: H2 (IH _ H Cz)=>//; [apply: H3 Cz; exists n | apply: H4].
Qed.

Lemma pres_iterf_ind P Q F :
        preserved P R ->
        (forall x, P x -> Q x -> F x x) ->
        Transitive F ->
        (forall x y, R x y -> P x -> Q x -> Q y /\ F x y) ->
        forall x y, iter R x y -> P x -> Q x -> F x y.
Proof.
move=>pres H1 H2 H3 x y O X1 X2; move: x y {X1 X2} O (conj X1 X2).
apply: iterf_ind=>//; first by move=>s []; apply: H1.
by move=>x y O [X Y]; case: (H3 _ _ O X Y) (pres _ _ O X).
Qed.

Lemma pres_iterb_ind P Q F :
        bpreserved P R ->
        (forall x, P x -> Q x -> F x x) ->
        Transitive F ->
        (forall x y, R x y -> P y -> Q y -> Q x /\ F x y) ->
        forall x y, iter R x y -> P y -> Q y -> F x y.
Proof.
move=>pres H1 H2 H3 x y O X1 X2; move: x y {X1 X2} O (conj X1 X2).
apply: iterb_ind=>//; first by move=>s []; apply: H1.
by move=>x y O [X Y]; case: (H3 _ _ O X Y) (pres _ _ O X).
Qed.

Lemma pres_iters_ind P Q F :
        preserved P R ->
        (forall x, P x -> Q x -> F x x) ->
        Transitive F ->
        (forall x y, iter R x y -> P x -> Q x -> Q y) ->
        (forall x y, R x y -> P x -> Q x -> F x y) ->
        forall x y, iter R x y -> P x -> Q x -> F x y.
Proof.
move=>pres H1 H2 H3 H4 x y O X1 X2; move: x y {X1 X2} O (conj X1 X2).
apply: iterf_ind=>//; first by move=>s []; apply: H1.
by move=>x y O [X Y]; move: (H3 _ _ (iter1 O) X Y) (H4 _ _ O X Y) (pres _ _ O X).
Qed.

End ReflexiveTransitiveClosureInductions.

Section ReflexiveTransitiveClosureInductionsCurry.
Variables (A T : Type) (R : A -> T -> A -> T -> Prop) .
Variables (C P Q : A -> T -> Prop) (F : A -> T -> A -> T -> Prop).

Notation Rc := (fun '(a, x) '(b, y) => R a x b y).
Notation Cc := (fun '(a, x) => C a x).
Notation Fc := (fun '(a, x) '(b, y)=> F a x b y).
Notation Pc := (fun '(a, x) => P a x).
Notation Qc := (fun '(a, x) => Q a x).

Lemma itercf_ind :
        (forall a x, C a x -> F a x a x) ->
        Transitive Fc ->
        (forall a x b y, R a x b y -> C a x -> C b y /\ F a x b y) ->
        forall a x b y, iterc R a x b y -> C a x -> F a x b y.
Proof.
move=>H1 H2 H3 a x b y; apply: (@iterf_ind _ Rc Cc Fc)=>//.
- by case=>a' x'; apply: H1.
by case=>a' x' [b' y']; apply: H3.
Qed.

Lemma itercb_ind :
        (forall a x, C a x -> F a x a x) ->
        Transitive Fc ->
        (forall a x b y, R a x b y -> C b y -> C a x /\ F a x b y) ->
        forall a x b y, iterc R a x b y -> C b y -> F a x b y.
Proof.
move=>H1 H2 H3 a x b y; apply: (@iterb_ind _ Rc Cc Fc)=>//.
- by case=>a' x'; apply: H1.
by case=>a' x' [b' y']; apply: H3.
Qed.

Lemma iterc_ind :
        (forall a x b y, R a x b y -> C a x -> C b y) ->
        forall a x b y, iterc R a x b y -> C a x -> C b y.
Proof.
move=>H a x b y; apply: (@iter_ind _ Rc Cc)=>//.
by case=>a' x' [b' y']; apply: H.
Qed.

Lemma itercs_ind :
        (forall a x, C a x -> F a x a x) -> Transitive Fc ->
        (forall a x b y, iterc R a x b y -> C a x -> C b y) ->
        (forall a x b y, R a x b y -> C a x -> F a x b y) ->
         forall a x b y, iterc R a x b y -> C a x -> F a x b y.
Proof.
move=>H1 H2 H3 H4 a x b y; apply: (@iters_ind _ Rc Cc Fc)=>//.
- by case=>a' x'; apply: H1.
- by case=>a' x' [b' y']; apply: H3.
by case=>a' x' [b' y']; apply: H4.
Qed.

Lemma pres_itercf_ind :
        preserved Pc Rc ->
        (forall a x, P a x -> Q a x -> F a x a x) ->
        Transitive Fc ->
        (forall a x b y, R a x b y -> P a x -> Q a x -> Q b y /\ F a x b y) ->
        forall a x b y, iterc R a x b y -> P a x -> Q a x -> F a x b y.
Proof.
move=>H1 H2 H3 H4 a x b y; apply: (@pres_iterf_ind _ Rc Pc Qc Fc)=>//.
- by case=>a' x' [b' y']; apply: (H1 (a', x') (b', y')).
- by case=>a' x'; apply: H2.
by case=>a' x' [b' y']; apply: H4.
Qed.

Lemma pres_itercs_ind :
        preserved Pc Rc ->
        (forall a x, P a x -> Q a x -> F a x a x) ->
        Transitive Fc ->
        (forall a x b y, iterc R a x b y -> P a x -> Q a x -> Q b y) ->
        (forall a x b y, R a x b y -> P a x -> Q a x -> F a x b y) ->
        forall a x b y, iterc R a x b y -> P a x -> Q a x -> F a x b y.
Proof.
move=>H1 H2 H3 H4 H5 a x b y; apply: (@pres_iters_ind _ Rc Pc Qc Fc)=>//.
- by case=>a' x' [b' y']; apply: (H1 (a', x') (b', y')).
- by case=>a' x'; apply: H2.
- by case=>a' x' [b' y']; apply: H4.
by case=>a' x' [b' y']; apply: H5.
Qed.

End ReflexiveTransitiveClosureInductionsCurry.


Section SomeBasicConstructions.
Variable (A : Type).
Implicit Types (P : A -> Prop) (R : Rel A).

(** _Empty_ relation *)
Section EmptyRelation.
Definition emp_rel : Rel A := fun x y => False.

Lemma emp_rel_func : functional emp_rel.
Proof. by []. Qed.
Lemma emp_rel_pres P : preserved P emp_rel.
Proof. by []. Qed.
End EmptyRelation.

(** _Full_ (a.k.a _unversal_) relation *)
Section FullRelation.
Definition full_rel : Rel A := fun x y => True.

Lemma full_rel_refl : forall x, full_rel x x.
Proof. by []. Qed.
Lemma full_rel_sym : Symmetric full_rel.
Proof. by []. Qed.
Lemma full_rel_trans : Transitive full_rel.
Proof. by []. Qed.
Lemma full_rel_tot : Total full_rel.
Proof. by move=> ??; left. Qed.
End FullRelation.

(**_Identity_ relation *)
Section IdentityRelation.
Definition id_rel : Rel A := fun x y => y = x.

Lemma id_rel_refl : forall x, id_rel x x.
Proof. by []. Qed.
Lemma id_rel_sym : Symmetric id_rel.
Proof. by []. Qed.
Lemma id_rel_trans : Transitive id_rel.
Proof. by move=> x y z ->->. Qed.
Lemma id_rel_func : functional id_rel.
Proof. by move=> x y1 y2 ->->. Qed.
Lemma id_rel_pres P : preserved P id_rel.
Proof. by move=>x y ->. Qed.
End IdentityRelation.

(** Imposing "precondition" on a relation *)
Section PreConditionalRelation.
Definition pre_rel P R := fun x y => P x /\ R x y.

Lemma pre_rel_func R P : functional R -> functional (pre_rel P R).
Proof. by move=> funcR x y1 y2 [_ Rxy1] [_ /(funcR _ _ _ Rxy1)]. Qed.
End PreConditionalRelation.


(** Imposing "postcondition" on a relation *)
Section PostConditionalRelation.
Definition post_rel R Q := fun x y => R x y /\ Q y.

Lemma reinv_rel_func R Q : functional R -> functional (post_rel R Q).
Proof. by move=> funcR x y1 y2 [Rxy1 _] [/(funcR _ _ _ Rxy1)]. Qed.
End PostConditionalRelation.


Section ProductRelation.
Variables (B : Type) (R : Rel A) (S : Rel B).

Definition prod_rel : Rel (A * B) :=
  fun '(a1, b1) '(a2, b2) => R a1 a2 /\ S b1 b2.

Lemma prod_rel_refl : (forall a, R a a) -> (forall b, S b b) -> forall p, prod_rel p p.
Proof. by move=> pR pS [a b] /=. Qed.

Lemma prod_rel_sym : Symmetric R -> Symmetric S -> Symmetric prod_rel.
Proof. by move=> pR pS [a1 b1] [a2 b2] /=; rewrite pR pS. Qed.

Lemma prod_rel_trans : Transitive R -> Transitive S -> Transitive prod_rel.
Proof.
move=> pR pS [a2 b2] [a1 b1] [a3 b3] [??] [??] /=.
by split; [apply: (pR a2) | apply: (pS b2)].
Qed.

Lemma prod_rel_asym : Antisymmetric R -> Antisymmetric S -> Antisymmetric prod_rel.
Proof.
move=> pR pS [a1 b1] [a2 b2] [R12 S12] [R21 S21].
by rewrite (pR _ _ R12 R21) (pS _ _ S12 S21).
Qed.

Lemma prod_rel_pre_sym : pre_Symmetric R -> pre_Symmetric S -> pre_Symmetric prod_rel.
Proof. by rewrite !sym_iff_pre_sym; apply: prod_rel_sym. Qed.

Lemma prod_rel_irrefl : Irreflexive R -> Irreflexive S -> Irreflexive prod_rel.
Proof. by move=> pR _ [a b] /= [] /pR. Qed.

Lemma prod_rel_ltrans : left_Transitive R -> left_Transitive S -> left_Transitive prod_rel.
Proof.
move=> pR pS [a1 b1] [a2 b2] [R12 S12] [a3 b3] /=.
by rewrite (pR _ _ R12 a3) (pS _ _ S12 b3).
Qed.

Lemma prod_rel_rtrans : right_Transitive R -> right_Transitive S -> right_Transitive prod_rel.
Proof.
move=> pR pS [a1 b1] [a2 b2] [R12 S12] [a3 b3] /=.
by rewrite (pR _ _ R12 a3) (pS _ _ S12 b3).
Qed.

Lemma prod_rel_func : functional R -> functional S -> functional prod_rel.
Proof.
move=> pR pS [a2 b2] [a1 b1] [a3 b3] [R21 S21] [R23 S23] /=.
by rewrite (pR _ _ _ R21 R23) (pS _ _ _ S21 S23).
Qed.

End ProductRelation.


Section UnionRelation.
Variables (R S : Rel A).

Definition Union_rel : Rel A := fun x y => R x y \/ S x y.

Definition fcompatible := forall x y1 y2, R x y1 -> S x y2 -> y1 = y2.

Lemma union_rel_func : functional R -> functional S ->
        fcompatible -> functional Union_rel.
Proof.
move=> fR fS fC x y1 y2; case=> [hR1 | hS1]; case=> [hR2 | hS2].
- by apply: fR hR1 hR2.
- apply: fC hR1 hS2.
- apply/esym; apply: fC hR2 hS1.
by apply: fS hS1 hS2.
Qed.

End UnionRelation.

End SomeBasicConstructions.

Arguments id_rel [A] _ _ /.
Arguments pre_rel [A] P R _ _ /.
Arguments post_rel [A] R Q _ _ /.


(*************************)
(* Property localization *)
(*************************)

Local Notation "{ 'All1' P }" := (forall x, P x : Prop) (at level 0).
Local Notation "{ 'All2' P }" := (forall x y, P x y : Prop) (at level 0).
Local Notation "{ 'All3' P }" := (forall x y z, P x y z: Prop) (at level 0).
Local Notation ph := (phantom _).

Section LocalProperties.

Variables T1 T2 T3 : Type.

Variables (d1 : T1 -> Prop) (d2 : T2 -> Prop) (d3 : T3 -> Prop).
Local Notation ph := (phantom Prop).

Definition Prop_in1 P & ph {All1 P} :=
  forall x, d1 x -> P x.

Definition Prop_in11 P & ph {All2 P} :=
  forall x y, d1 x -> d2 y -> P x y.

Definition Prop_in2 P & ph {All2 P} :=
  forall x y, d1 x -> d1 y -> P x y.

Definition Prop_in111 P & ph {All3 P} :=
  forall x y z, d1 x -> d2 y -> d3 z -> P x y z.

Definition Prop_in12 P & ph {All3 P} :=
  forall x y z, d1 x -> d2 y -> d2 z -> P x y z.

Definition Prop_in21 P & ph {All3 P} :=
  forall x y z, d1 x -> d1 y -> d2 z -> P x y z.

Definition Prop_in3 P & ph {All3 P} :=
  forall x y z, d1 x -> d1 y -> d1 z -> P x y z.

End LocalProperties.

Definition inPhantom := Phantom Prop.

Notation "{ 'In' d , P }" :=
  (Prop_in1 d (inPhantom P))
  (at level 0, format "{ 'In'  d ,  P }") : type_scope.

Notation "{ 'In' d1 & d2 , P }" :=
  (Prop_in11 d1 d2 (inPhantom P))
  (at level 0, format "{ 'In'  d1  &  d2 ,  P }") : type_scope.

Notation "{ 'In' d & , P }" :=
  (Prop_in2 d (inPhantom P))
  (at level 0, format "{ 'In'  d  & ,  P }") : type_scope.

Notation "{ 'In' d1 & d2 & d3 , P }" :=
  (Prop_in111 d1 d2 d3 (inPhantom P))
  (at level 0, format "{ 'In'  d1  &  d2  &  d3 ,  P }") : type_scope.

Notation "{ 'In' d1 & & d3 , P }" :=
  (Prop_in21 d1 d3 (inPhantom P))
  (at level 0, format "{ 'In'  d1  &  &  d3 ,  P }") : type_scope.

Notation "{ 'In' d1 & d2 & , P }" :=
  (Prop_in12 d1 d2 (inPhantom P))
  (at level 0, format "{ 'In'  d1  &  d2  & ,  P }") : type_scope.

Notation "{ 'In' d & & , P }" :=
  (Prop_in3 d (inPhantom P))
  (at level 0, format "{ 'In'  d  &  & ,  P }") : type_scope.


(* Weakening and monotonicity lemmas for localized predicates.                *)
(* Note that using these lemmas in backward reasoning will force expansion of *)
(* the predicate definition, as Coq needs to expose the quantifier to apply   *)
(* these lemmas. We define a few specialized variants to avoid this for some  *)
(* of the ssrfun predicates.                                                  *)

Section LocalGlobal.

Variables T1 T2 T3 : Type.
Variables (D1 : T1 -> Prop) (D2 : T2 -> Prop) (D3 : T3 -> Prop).
Variables (P1 : T1 -> Prop) (P2 : T1 -> T2 -> Prop).
Variable P3 : T1 -> T2 -> T3 -> Prop.
Variables (d1 d1' : T1 -> Prop).

Local Notation "{ 'All1' P }" := (forall x, P x : Prop) (at level 0).
Local Notation "{ 'All2' P }" := (forall x y, P x y : Prop) (at level 0).
Local Notation "{ 'All3' P }" := (forall x y z, P x y z: Prop) (at level 0).
Local Notation ph := (phantom _).

Lemma In1W : {All1 P1} -> {In D1, {All1 P1}}.
Proof. by move=> ? ?. Qed.
Lemma In2W : {All2 P2} -> {In D1 & D2, {All2 P2}}.
Proof. by move=> ? ?. Qed.
Lemma In3W : {All3 P3} -> {In D1 & D2 & D3, {All3 P3}}.
Proof. by move=> ? ?. Qed.

End LocalGlobal.
