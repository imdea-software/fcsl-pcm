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

From Stdlib Require Import ssreflect ssrbool ssrfun Setoid Basics.
From mathcomp Require Import ssrnat seq eqtype bigop.
From pcm Require Import options.

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
Open Scope function_scope.

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
Identity Coercion Fun_Of_Pred : Pred >-> Funclass.

Definition SubPred T (p1 p2 : Pred T) := forall x : T, p1 x -> p2 x.

Notation xPred0 := (fun _ => False).
Notation xPred1 := (fun x => eq^~ x).
Notation xPredT := (fun _ => True).
Notation xPredI := (fun (p1 p2 : Pred _) x => p1 x /\ p2 x).
Notation xPredU := (fun (p1 p2 : Pred _) x => p1 x \/ p2 x).
Notation xPredC := (fun (p : Pred _) x => ~ p x).
Notation xPredD := (fun (p1 p2 : Pred _) x => ~ p2 x /\ p1 x).
Notation xPreim := (fun f (p : Pred _) x => p (f x)).

(* The packed class interface for pred-like types. *)

Structure PredType T :=
   PropPredType {Pred_Sort :> Type; toPred : Pred_Sort -> Pred T}.

Definition Clone_Pred T U :=
  fun pT & @Pred_Sort T pT -> U =>
  fun toP (pT' := @PropPredType T U toP) & phant_id pT' pT => pT'.
Notation "[ 'PredType' 'of' T ]" := (@Clone_Pred _ T _ id _ id) : form_scope.

Canonical PredPredType T := PropPredType (@id (Pred T)).
Canonical PropFunPredType T := PropPredType (@id (T -> Prop)).

Notation "{ 'Pred' T }" := (Pred_Sort (PredPredType T)) 
  (format "{ 'Pred'  T }") : type_scope.

Definition Eq_Pred {T} (pT : PredType T) (mp1 mp2 : pT) := 
  forall x : T, toPred mp1 x <-> toPred mp2 x.
Definition Sub_Pred {T} (pT : PredType T) (mp1 mp2 : pT) := 
  forall x : T, toPred mp1 x -> toPred mp2 x.
Definition Eq_PredFun {T1 T2} (pT2 : PredType T2) p1 p2 := 
  forall x : T1, @Eq_Pred T2 pT2 (p1 x) (p2 x).
Definition Sub_PredFun T1 T2 (pT2 : PredType T2) p1 p2 :=
  forall x : T1, @Sub_Pred T2 pT2 (p1 x) (p2 x).

Notation "A <~> B" := (@Eq_Pred _ _ A B)
  (at level 70, no associativity) : rel_scope.
Notation "A ~> B" := (@Sub_Pred _ _ A B)
  (at level 70, no associativity) : rel_scope.
Notation "A <~1> B" := (@Eq_PredFun _ _ _ A B)
  (at level 70, no associativity) : rel_scope.
Notation "A ~1> B" := (@Sub_PredFun _ _ _ A B)
  (at level 70, no associativity) : rel_scope.

(* The type of self-simplifying collective predicates. *)

Definition Simpl_Pred T := simpl_fun T Prop.
Definition PropSimplPred {T} (p : Pred T) : Simpl_Pred T := SimplFun p.

(* Some Simple_Pred constructors *)

Definition Pred0 {T} := @PropSimplPred T xPred0.
Definition PredT {T} := @PropSimplPred T xPredT.
Definition Pred1 {T} (x : T) := PropSimplPred (xPred1 x).
Definition PredI {T} (p1 p2 : Pred T) := PropSimplPred (xPredI p1 p2).
Definition PredU {T} (p1 p2 : Pred T) := PropSimplPred (xPredU p1 p2).
Definition PredC {T} (p : Pred T) := PropSimplPred (xPredC p).
Definition PredD {T} (p1 p2 : Pred T) := PropSimplPred (xPredD p1 p2).
Definition Preim {aT rT} (f : aT -> rT) (d : Pred rT) := 
  PropSimplPred (xPreim f d).

Notation "[ 'Pred' : T | E ]" := (PropSimplPred (fun _ : T => E))
  (format "[ 'Pred' :  T  |  E ]") : function_scope.
Notation "[ 'Pred' x | E ]" := (PropSimplPred (fun x => E))
  (x name, format "[ 'Pred'  x  |  E ]") : function_scope.
Notation "[ 'Pred' x : T | E ]" := (PropSimplPred (fun x : T => E))
  (x name, only parsing) : function_scope.
Notation "[ 'Pred' x | E1 & E2 ]" := [Pred x | E1 /\ E2 ] 
  (x name) : function_scope.
Notation "[ 'Pred' x : T | E1 & E2 ]" := [Pred x : T | E1 /\ E2 ] 
  (x name, only parsing) : function_scope.

(* coercion for Simpl_Pred *)

Module PredOfSimpl.
Definition Coerce T (sp : Simpl_Pred T) : Pred T := fun_of_simpl sp.
End PredOfSimpl.
Notation Pred_Of_Simpl := PredOfSimpl.Coerce.
Coercion Pred_Of_Simpl : Simpl_Pred >-> Pred.
Canonical SimplPredType T := PropPredType (@Pred_Of_Simpl T).

Module Type PropPredSortOfSimplSignature.
Parameter Coerce : forall T, Simpl_Pred T -> {Pred T}.
End PropPredSortOfSimplSignature.
Module PropDeclarePredSortOfSimpl 
  (PropPredSortOfSimpl : PropPredSortOfSimplSignature).
Coercion PropPredSortOfSimpl.Coerce : Simpl_Pred >-> Pred_Sort.
End PropDeclarePredSortOfSimpl.
Module Export PropPredSortOfSimplCoercion := 
  PropDeclarePredSortOfSimpl PredOfSimpl.

Definition PredArgType := Type.
Bind Scope type_scope with PredArgType.
Identity Coercion Sort_Of_PredArgType : PredArgType >-> Sortclass.
Coercion Pred_Of_ArgType (T : PredArgType) : Simpl_Pred T := PredT.
Notation "{ :: T }" := (T%type : PredArgType) : type_scope.

(* prop relations *)

Definition Rel T := T -> Pred T.
Identity Coercion Fun_Of_Rel : Rel >-> Funclass.

Definition eqRel {T} (R1 R2 : Rel T) := forall x y, R1 x y <-> R2 x y.
Definition subRel {T} (R1 R2 : Rel T) := forall x y : T, R1 x y -> R2 x y.

Notation "A <~2> B" := (eqRel A B)
  (at level 70, no associativity) : rel_scope.
Notation "A ~2> B" := (subRel A B)
  (at level 70, no associativity) : rel_scope.

(* composing relation and function *)

Definition Rel_app A B (D : Rel A) (f : B -> A) : Rel B := 
  fun x y => D (f x) (f y).

Arguments Rel_app {A B} D f _ _ /.
Notation "D \\o f" := (@Rel_app _ _ D f) 
  (at level 42, left associativity).

Lemma rel_app1 T (g : T -> T -> Prop) : g \\o id <~2> g. 
Proof. by []. Qed.

(* simplifying relations *)

Definition Simpl_Rel T := T -> Simpl_Pred T.

Coercion Rel_Of_Simpl T (sr : Simpl_Rel T) : Rel T := fun x : T => sr x.
Arguments Rel_Of_Simpl {T} sr x /.

Notation xRelU := (fun (r1 r2 : Rel _) x y => r1 x y \/ r2 x y).
Notation xRelPre := (fun f (r : Rel _) x y => r (f x) (f y)).

Definition PropSimplRel {T} (r : Rel T) : Simpl_Rel T := 
  fun x => PropSimplPred (r x).
Definition RelU {T} (r1 r2 : Rel T) := PropSimplRel (xRelU r1 r2).
Definition RelPre {aT rT} (f : aT -> rT) (r : Rel rT) := PropSimplRel (xRelPre f r).

Notation "[ 'Rel' x y | E ]" := (PropSimplRel (fun x y => E))
  (x name, y name, only parsing) : function_scope.
Notation "[ 'Rel' x y : T | E ]" := (PropSimplRel (fun x y : T => E)) 
  (x name, y name, only parsing) : function_scope.

Lemma subRelUl T (r1 r2 : Rel T) : subRel r1 (RelU r1 r2).
Proof. by left. Qed.

Lemma subRelUr T (r1 r2 : Rel T) : subRel r2 (RelU r1 r2).
Proof. by right. Qed.

(* Variant of Simpl_Pred specialised to the membership operator. *)

Variant Mem_Pred T := PropMem of Pred T.

Coercion Pred_Of_Mem {T} mp : {Pred T} := let: PropMem p := mp in [eta p].
Canonical MemPredType T := PropPredType (@Pred_Of_Mem T).

Definition In_Mem {T} (x : T) mp := Pred_Of_Mem mp x.
Definition Eq_Mem {T} mp1 mp2 := forall x : T, In_Mem x mp1 <-> In_Mem x mp2. 
Definition Sub_Mem {T} mp1 mp2 := forall x : T, In_Mem x mp1 -> In_Mem x mp2.

Arguments In_Mem {T} x mp : simpl never.
Global Typeclasses Opaque Eq_Mem Sub_Mem.

(*
The Simpl_Of_Mem; Pred_Of_Simpl path provides a new Mem_Pred >-> Pred
  coercion, but does not override the Pred_Of_Mem : Mem_Pred >-> Pred_sort
  explicit coercion declaration above.
*)
 
Coercion Simpl_Of_Mem {T} mp := PropSimplPred (fun x : T => In_Mem x mp).

Lemma Sub_Refl T (mp : Mem_Pred T) : Sub_Mem mp mp.
Proof. by []. Qed.
Arguments Sub_Refl {T mp} [x] mp_x.

Definition Mem T (pT : PredType T) : pT -> Mem_Pred T :=
  let: PropPredType _ toP := pT in fun A => PropMem [eta toP A].
Arguments Mem {T pT} A : rename, simpl never.

Notation "x \In A" := (In_Mem x (Mem A))
  (at level 70, no associativity) : rel_scope.
Notation "x \Notin A" := (~ (x \In A))
  (at level 70, no associativity) : rel_scope.
Notation "A =p B" := (Eq_Mem (Mem A) (Mem B))
  (at level 70, no associativity) : type_scope.
Notation "A <=p B" := (Sub_Mem (Mem A) (Mem B))
  (at level 70, no associativity) : type_scope.

(* conversions *)
Lemma eq_conv T (A B : Pred T) : (A <~> B) = (A =p B).
Proof. by []. Qed.
Lemma sub_conv T (A B : Pred T) : (A ~> B) = (A <=p B).
Proof. by []. Qed.

Notation "[ 'Mem' A ]" :=
  (Pred_Of_Simpl (Simpl_Of_Mem (Mem A))) (only parsing) : function_scope.

Notation "[ 'PredI' A & B ]" := (PredI [Mem A] [Mem B])
  (format "[ 'PredI'  A  &  B ]") : function_scope.
Notation "[ 'PredU' A & B ]" := (PredU [Mem A] [Mem B])
  (format "[ 'PredU'  A  &  B ]") : function_scope.
Notation "[ 'PredD' A & B ]" := (PredD [Mem A] [Mem B])
  (format "[ 'PredD'  A  &  B ]") : function_scope.
Notation "[ 'PredC' A ]" := (PredC [Mem A])
  (format "[ 'PredC'  A ]") : function_scope.
Notation "[ 'Preim' f 'of' A ]" := (Preim f [Mem A])
  (format "[ 'Preim'  f  'of'  A ]") : function_scope.

Notation "[ 'Pred' x 'In' A ]" := [Pred x | x \In A] 
  (x name) : function_scope.
Notation "[ 'Pred' x 'In' A | E ]" := [Pred x | (x \In A) /\ E] 
  (x name) : function_scope.
Notation "[ 'Pred' x 'In' A | E1 & E2 ]" := 
  [Pred x | x \In A & E1 /\ E2 ] 
  (x name) : function_scope.

(* infix notation for PredU and PredI *)
(* is sometimes more readable *) 

Notation "A \+p B" := (PredOfSimpl.Coerce (PredU A B))
  (at level 55, right associativity) : rel_scope.
Notation "A \*p B" := (PredOfSimpl.Coerce (PredI A B))
  (at level 45, right associativity) : rel_scope.

Notation "[ 'Rel' x y 'In' A & B | E ]" :=
  [Rel x y | (x \In A) /\ (y \In B) /\ E]
  (at level 0, x name, y name,
   format "[ 'Rel'  x  y  'In'  A  &  B  |  E ]") : function_scope.
Notation "[ 'Rel' x y 'In' A & B ]" := [Rel x y | (x \In A) /\ (y \In B)]
  (at level 0, x name, y name,
   format "[ 'Rel'  x  y  'In'  A  &  B ]") : function_scope.
Notation "[ 'Rel' x y 'In' A | E ]" := [Rel x y In A & A | E]
  (at level 0, x name, y name,
   format "[ 'Rel'  x  y  'In'  A  |  E ]") : function_scope.
Notation "[ 'Rel' x y 'In' A ]" := [Rel x y In A & A]
  (at level 0, x name, y name,
   format "[ 'Rel'  x  y  'In' A ]") : function_scope.

Definition Applicative_Pred T := Pred T.
Definition Collective_Pred T := Pred T.
Coercion Applicative_Pred_Of_Simpl T (sp : Simpl_Pred T) : Applicative_Pred T :=
  fun_of_simpl sp.
Coercion Collective_Pred_Of_Simpl T (sp : Simpl_Pred T) : Collective_Pred T :=
  let: SimplFun p := sp in p.

(* Explicit simplification rules for predicate application and membership.  *)
Section PredicateSimplification.
Variables T : Type.
Implicit Types (p : Pred T) (pT : PredType T) (sp : Simpl_Pred T).
Implicit Types (mp : Mem_Pred T).

Structure Registered_Applicative_Pred p := PropRegisteredApplicativePred {
  Applicative_Pred_Value :> Pred T;
  _ : Applicative_Pred_Value = p
}.
Definition PropApplicativePred p := PropRegisteredApplicativePred (erefl p).
Canonical Applicative_Pred_Applicative sp :=
  PropApplicativePred (Applicative_Pred_Of_Simpl sp).

Structure Manifest_Simpl_Pred p := PropManifestSimplPred {
  Simpl_Pred_Value :> Simpl_Pred T;
  _ : Simpl_Pred_Value = PropSimplPred p
}.
Canonical Expose_Simpl_Pred p := PropManifestSimplPred (erefl (PropSimplPred p)).

Structure Manifest_Mem_Pred p := PropManifestMemPred {
  Mem_Pred_Value :> Mem_Pred T;
  _ : Mem_Pred_Value = PropMem [eta p]
}.
Canonical Expose_Mem_Pred p := PropManifestMemPred (erefl (PropMem [eta p])).

Structure Applicative_Mem_Pred p :=
  PropApplicativeMemPred {Applicative_Mem_Pred_Value :> Manifest_Mem_Pred p}.
Canonical Check_Applicative_Mem_Pred p (ap : Registered_Applicative_Pred p) :=
  [eta @PropApplicativeMemPred ap].

Lemma Mem_toPred pT (pp : pT) : Mem (toPred pp) = Mem pp.
Proof. by case: pT pp. Qed.

Lemma toPredE pT x (pp : pT) : toPred pp x = (x \In pp).
Proof. by case: pT pp. Qed.

Lemma App_PredE x p (ap : Registered_Applicative_Pred p) : ap x = (x \In p).
Proof. by case: ap=>ap /= ->. Qed.

Lemma In_Applicative x p (amp : Applicative_Mem_Pred p) : In_Mem x amp = p x.
Proof. by case: amp; case=>amp /= ->. Qed.

Lemma In_Collective x p (msp : Manifest_Simpl_Pred p) :
        (x \In Collective_Pred_Of_Simpl msp) = p x.
Proof. by case: msp=>msp pf; rewrite -toPredE /= pf. Qed.

Lemma In_Simpl x p (msp : Manifest_Simpl_Pred p) :
  In_Mem x (PropMem [eta Pred_Of_Simpl msp]) = p x.
Proof. by case: msp=>msp /= ->. Qed.

Lemma Unfold_In x p : (x \In ([eta p] : Pred T)) = p x.
Proof. by []. Qed.

Lemma Simpl_PredE p : PropSimplPred p =1 p.
Proof. by []. Qed.

Lemma Mem_Simpl sp : Mem sp = sp :> Pred T.
Proof. by []. Qed.

Definition MemE := Mem_Simpl.
Lemma Mem_Mem mp :
  (Mem mp = mp) * (Mem (mp : Simpl_Pred T) = mp) * (Mem (mp : Pred T) = mp).
Proof. by case: mp. Qed.

End PredicateSimplification.

(* Qualifiers and keyed predicates.  *)

Variant Qualifier (q : nat) T := PropQualifier of {Pred T}.

Coercion Has_Quality n T (q : Qualifier n T) : {Pred T} :=
  fun x => let: PropQualifier p := q in p x.
Arguments Has_Quality n {T}.

Lemma QualifE n T p x : (x \In @PropQualifier n T p) = p x.
Proof. by []. Qed.

Notation "x \Is A" := (x \In Has_Quality 0 A) 
  (at level 0, only parsing) : function_scope.
Notation "x \Is A" := (x \In Has_Quality 0 A) 
  (at level 0, only printing) : function_scope.
Notation "x \Is 'a' A" := (x \In Has_Quality 1 A) 
  (at level 0, only parsing) : function_scope.
Notation "x \Is 'a' A" := (x \In Has_Quality 1 A) 
  (at level 0, only printing) : function_scope.
Notation "x \Is 'an' A" := (x \In Has_Quality 2 A) 
  (at level 0, only parsing) : function_scope.
Notation "x \Is 'an' A" := (x \In Has_Quality 2 A) 
  (at level 0, only printing) : function_scope.
Notation "x \Isn't A" := (x \Notin Has_Quality 0 A) 
  (at level 0) : function_scope.
Notation "x \Isn't 'a' A" := (x \Notin Has_Quality 1 A) 
  (at level 0) : function_scope.
Notation "x \Isn't 'an' A" := (x \Notin Has_Quality 2 A) 
  (at level 0) : function_scope.
Notation "[ 'Qualify' x | P ]" := (PropQualifier 0 (fun x => P)) : form_scope.
Notation "[ 'Qualify' x : T | P ]" :=
  (PropQualifier 0 (fun x : T => P)) (only parsing) : form_scope.
Notation "[ 'Qualify' 'a' x | P ]" := 
  (PropQualifier 1 (fun x => P)) : form_scope.
Notation "[ 'Qualify' 'a' x : T | P ]" :=
  (PropQualifier 1 (fun x : T => P)) (only parsing) : form_scope.
Notation "[ 'Qualify' 'an' x | P ]" :=
  (PropQualifier 2 (fun x => P)) : form_scope.
Notation "[ 'Qualify' 'an' x : T | P ]" :=
  (PropQualifier 2 (fun x : T => P)) (only parsing) : form_scope.

(* Keyed predicates: support for property-bearing predicate interfaces. *)

Section KeyPred.
Variable T : Type.
Variant Pred_Key (p : {Pred T}) : Prop := PropDefaultPredKey.

Variable p : {Pred T}.
Structure Keyed_Pred (k : Pred_Key p) :=
  PropPackKeyedPred {Unkey_Pred :> {Pred T}; _ : Unkey_Pred =p p}.

Variable k : Pred_Key p.
Definition PropKeyedPred := @PropPackKeyedPred k p (fun x => iff_refl _).

Variable k_p : Keyed_Pred k.
Lemma Keyed_PredE : k_p =p p.
Proof. by case: k_p. Qed.

Canonical Keyed_Mem :=
  @PropPackKeyedPred k (Pred_Of_Mem (Mem k_p)) Keyed_PredE.
Canonical Leyed_Mem_Simpl :=
  @PropPackKeyedPred k (Pred_Of_Simpl (Mem k_p)) Keyed_PredE.

End KeyPred.

Local Notation In_Unkey x S := (x \In @Unkey_Pred _ S _ _) (only parsing).
Notation "x \In S" := (In_Unkey x S) (only printing) : function_scope.

Section KeyedQualifier.
Variables (T : Type) (n : nat) (q : Qualifier n T).

Structure Keyed_Qualifier (k : Pred_Key q) :=
  PropPackKeyedQualifier {Unkey_Qualifier; _ : Unkey_Qualifier = q}.
Definition PropKeyedQualifier k := PropPackKeyedQualifier k (erefl q).
Variables (k : Pred_Key q) (k_q : Keyed_Qualifier k).
Fact Keyed_Qualifier_Subproof : Unkey_Qualifier k_q =p q.
Proof. by case: k_q=>kq pf x /=; rewrite pf. Qed.
Canonical Keyed_Qualifier_Keyed := PropPackKeyedPred k Keyed_Qualifier_Subproof.

End KeyedQualifier.

Notation "x \Is A" :=
  (In_Unkey x (Has_Quality 0 A)) (only printing) : function_scope.
Notation "x \Is 'a' A" :=
  (In_Unkey x (Has_Quality 1 A)) (only printing) : function_scope.
Notation "x \Is 'an' A" :=
  (In_Unkey x (Has_Quality 2 A)) (only printing) : function_scope.

Module DefaultKeying.
Canonical Default_Keyed_Pred T p := PropKeyedPred (@PropDefaultPredKey T p).
Canonical Default_Keyed_Qualifier T n (q : Qualifier n T) :=
  PropKeyedQualifier (PropDefaultPredKey q).
End DefaultKeying.


(**************************************)
(* Definitions and lemmas for setoids *)
(**************************************)

(* Declaration of relations *)

Section EqPred.
Context {T : Type} {pT : PredType T}.
Lemma EqPred_refl (r : pT) : Eq_Pred r r. Proof. by []. Qed.
Lemma EqPred_sym (r1 r2 : pT) : Eq_Pred r1 r2 -> Eq_Pred r2 r1.
Proof. by move=>H1 x; split; move/H1. Qed.
Lemma EqPred_trans' (r1 r2 r3 : pT) :
        Eq_Pred r1 r2 -> Eq_Pred r2 r3 -> Eq_Pred r1 r3.
Proof. by move=>H1 H2 x; split; [move/H1; move/H2 | move/H2; move/H1]. Qed.
Definition EqPred_trans r2 r1 r3 := @EqPred_trans' r1 r2 r3.
End EqPred.

#[export] Hint Resolve EqPred_refl : core.

(* declare relations for all Eq_Pred and Eq_Mem *)

Add Parametric Relation T (pT : PredType T) : pT (@Eq_Pred _ pT)
  reflexivity proved by (@EqPred_refl _ _)
  symmetry proved by (@EqPred_sym _ _)
  transitivity proved by (@EqPred_trans' _ _) as EqPred_rel.

(* do we need to add relations for mem_pred as well? *)
Add Parametric Relation T : (Mem_Pred T) (@Eq_Mem T)
  reflexivity proved by (@EqPred_refl _ _)
  symmetry proved by (@EqPred_sym _ _)
  transitivity proved by (@EqPred_trans' _ _) as EqMem_rel.

Section SubPred.
Context {T : Type} {pT : PredType T}.
Lemma SubPred_refl (r : pT) : Sub_Pred r r. Proof. by []. Qed.
Lemma SubPred_trans' (r1 r2 r3 : pT) :
        Sub_Pred r1 r2 -> Sub_Pred r2 r3 -> Sub_Pred r1 r3.
Proof. by move=>H1 H2 x; move/H1; move/H2. Qed.
Definition SubPred_trans r2 r1 r3 := @SubPred_trans' r1 r2 r3.
End SubPred.

#[export] Hint Resolve SubPred_refl : core.

Add Parametric Relation T (pT : PredType T) : pT (@Sub_Pred _ pT)   
  reflexivity proved by (@SubPred_refl _ _)                         
  transitivity proved by (@SubPred_trans' _ _) as SubPred_rel.  

Add Parametric Relation T : (Mem_Pred T) (@Sub_Mem _)
  reflexivity proved by (@SubPred_refl _ _)
  transitivity proved by (@SubPred_trans' _ _) as SubMem_rel.

Section EqRel.
Context {T : Type}.
Lemma eqRel_refl (R : Rel T) : eqRel R R. Proof. by []. Qed.
Lemma eqRel_sym {R1 R2 : Rel T} : eqRel R1 R2 -> eqRel R2 R1. 
Proof. by move=>H x y; rewrite H. Qed.
Lemma eqRel_trans {R1 R2 R3 : Rel T} : 
        eqRel R1 R2 -> eqRel R2 R3 -> eqRel R1 R3.
Proof. by move=>H1 H2 x y; rewrite H1 H2. Qed.
End EqRel.

#[export] Hint Resolve eqRel_refl : core.

Add Parametric Relation (T : Type) : (Rel T) (@eqRel T)
  reflexivity proved by (@eqRel_refl T)
  symmetry proved by (@eqRel_sym T)
  transitivity proved by (@eqRel_trans T) as eqRel_rel.

Section SubRel.
Context {T : Type}.
Lemma subRel_refl (R : Rel T) : subRel R R. Proof. by []. Qed.
Lemma subRel_trans (R1 R2 R3 : Rel T) : 
        subRel R1 R2 -> subRel R2 R3 -> subRel R1 R3.
Proof. by move=>H1 H2 x y /H1/H2. Qed.
End SubRel.

#[export] Hint Resolve subRel_refl : core.

Add Parametric Relation (T : Type) : (Rel T) (@subRel T)
  reflexivity proved by (@subRel_refl T)
  transitivity proved by (@subRel_trans T) as subRel_rel.

(* Declaring morphisms. *)


(*
Add Parametric Morphism T : (@Pred_of_Simpl T) with signature
  @EqSimplPred _ ==> @EqPredType T (PredPredType T) as Pred_of_Simpl_morph.
Proof. by []. Qed.
*)


Add Parametric Morphism T (pT : PredType T) : (@Eq_Pred T pT) 
  with signature
  @Eq_Pred _ _ ==> @Eq_Pred _ _ ==> iff as EqPred_morph.
Proof. by move=>r1 s1 H1 r2 s2 H2; rewrite H1 H2. Qed.

Add Parametric Morphism T (pT : PredType T) : (@Sub_Pred T pT) 
  with signature
  @Eq_Pred _ _ ==> @Eq_Pred _ _ ==> iff as SubPred_morph.
Proof. by move=>r1 s1 H1 r2 s2 H2; split=>H x; move/H1; move/H; move/H2. Qed.

Add Parametric Morphism T : (@Eq_Mem T) 
  with signature @Eq_Mem _ ==> @Eq_Mem _ ==> iff as EqMem_morph.
Proof. by move=>r1 s1 H1 r2 s2 H2; rewrite H1 H2. Qed.

Add Parametric Morphism T : (@Sub_Mem T)
  with signature @Eq_Mem _ ==> @Eq_Mem _ ==> iff as SubMem_morph.
Proof. by move=>r1 s1 H1 r2 s2 H2; split=>H x; move/H1; move/H; move/H2. Qed.

Add Parametric Morphism T : (@Eq_Pred T _) 
  with signature @Eq_Mem _ ==> @Eq_Mem _ ==> iff as EqPred_Mem_morph.
Proof. 
move=>x y H x0 y0 H0; split=>X p /=; move: (H p) (H0 p)=>{}H {}H0;
rewrite /In_Mem /= in H H0.
- by rewrite -H -H0; apply/X.
by rewrite H H0; apply/X.
Qed.

Add Parametric Morphism T : (@In_Mem T) with signature
  @eq _ ==> @Eq_Mem _ ==> iff as InMem_morph.
Proof. by move=>x r s H; split; move/H. Qed.

(* to rewrite under [Mem], must enable rewriting under *)
(* Mem, Simpl_Of_Mem and Pred_Of_Simpl *)

(* rewriting by Eq_Pred under Mem *)
Add Parametric Morphism T (pT : PredType T) : (@Mem T pT) 
  with signature @Eq_Pred _ _ ==> @Eq_Pred _ _ as Mem_morph.
Proof. by case: pT=>pT F /= x y; apply. Qed.

(* and under Eq_Mem \o Mem *)
Add Parametric Morphism T (pT : PredType T) : (@Mem T pT) 
  with signature @Eq_Pred _ _ ==> @Eq_Mem _ as Mem_morph'.
Proof. by move=>x y H p; rewrite /Eq_Pred -!toPredE in H *; apply: H. Qed.

(* rewriting under Simpl_Of_Mem *)
Add Parametric Morphism T : (@Simpl_Of_Mem T) 
  with signature @Eq_Pred _ _ ==> @Eq_Pred _ _ as SimplOfMem_morph.
Proof. by []. Qed.

(* rewriting under Pred_Of_Simpl *)
Add Parametric Morphism T : (@Pred_Of_Simpl T) 
  with signature @Eq_Pred _ _ ==> @Eq_Pred _ _ as Pred_Of_Simpl_morph.
Proof. by []. Qed.

(* rewriting by Eq_Mem under Eq_Pred *)
Add Parametric Morphism T : (@Mem T _)
  with signature @Eq_Mem _ ==> @Eq_Pred _ _ as Mem_Morph.
Proof. by []. Qed.

Add Parametric Morphism T : (@Simpl_Of_Mem T) 
  with signature @Eq_Mem _ ==> @Eq_Pred _ _ as SimplOfMem_morph'.
Proof. by []. Qed.

(* rewriting under Pred_Of_Simpl *)
Add Parametric Morphism T : (@Pred_Of_Simpl T) 
  with signature @Eq_Mem _ ==> @Eq_Pred _ _ as Pred_Of_Simpl_morph'.
Proof. by []. Qed.

Add Parametric Morphism T : (@PredU T) with signature
  @Eq_Pred T _ ==> @Eq_Pred T _ ==> @Eq_Pred T _ as predU_morph.
Proof.
move=>r1 s1 H1 r2 h2 H2 x; split;
by case; [move/H1 | move/H2]=>/=; auto.
Qed.

Add Parametric Morphism T : (@PredI T) with signature
  @Eq_Pred _ _ ==> @Eq_Pred _ _ ==> @Eq_Pred _ _ as predI_morph.
Proof.
move=>r1 s1 H1 r2 s2 H2 x; split;
by case; move/H1=>T1; move/H2=>T2.
Qed.

Add Parametric Morphism T : (@PredC T) with signature
  @Eq_Pred _ _ ==> @Eq_Pred _ _ as predC_morph.
Proof. by move=>r s H x; split=>H1; apply/H. Qed.

Add Parametric Morphism A : (@subRel A) with signature 
  eqRel ==> eqRel ==> iff as subrel_eq.
Proof. by move=>x y H x1 y1 H1; split=>X a b /H/X/H1. Qed.

Add Parametric Morphism A B : (@Rel_app A B) with signature
  eqRel ==> eq ==> eqRel as Relapp_eq.
Proof. by move=>x y H f s s'; split=>/H. Qed.

Add Parametric Morphism A B : (@Rel_app A B) with signature
  subRel ==> eq ==> subRel as Relapp_sub.
Proof. by move=>x y H f s s' /H. Qed.

(* Can we declare relation application as morphism? *)
(* We can, but it isn't picked up in practice. *)
(* This is so because application is a special term *)
(* that apprently can't be matched on. *)
(* If we want to rewrite under application *)
(* the choices are: *)
(*   a) don't use setoids, but prove equalites *)
(*   b) move to collective predicates where *)
(*      function application is user-level term *)
(*
Add Parametric Morphism A : (fun (R : Rel A) (x y : A) => R x y) 
  with signature eqrel ==> eq ==> eq ==> iff as app_eq.
Proof. by move=>r1 r2 E x y; split=>/E. Qed.
*)

Section RelLaws.
Variable T : Type.
Implicit Type r : Pred T.

Lemma orrI r : r \+p r <~> r.
Proof.  by move=>x; split; [case | left]. Qed.

Lemma orrC r1 r2 : r1 \+p r2 <~> r2 \+p r1. 
Proof. by split; (case=>/=; [right|left]). Qed.

Lemma orr0 r : r \+p Pred0 <~> r.
Proof. by move=>x; split; [case | left]. Qed.

Lemma or0r r : Pred0 \+p r <~> r.
Proof. by rewrite orrC orr0. Qed.

Lemma orrCA r1 r2 r3 : 
        r1 \+p r2 \+p r3 <~> r2 \+p r1 \+p r3.  simpl.
Proof. by move=>x /=; intuition. Qed.

Lemma orrAC r1 r2 r3 : 
        (r1 \+p r2) \+p r3 <~> (r1 \+p r3) \+p r2.
Proof. by move=>x /=; intuition. Qed.

Lemma orrA r1 r2 r3 : 
        (r1 \+p r2) \+p r3 <~> r1 \+p r2 \+p r3.
Proof. by rewrite (orrC r2) orrCA (orrC r3). Qed.

(* absorption *)
Lemma orrAb r1 r2 : 
        r1 <~> r1 \+p r2 <-> 
        r2 <=p r1.
Proof.
split; first by move=>-> x; rewrite -!toPredE /=; auto.
move=>H x /=; split; first by auto.
by case=>//; move/H.
Qed.

Lemma sub_orl r1 r2 : r1 <=p r1 \+p r2. Proof. by left. Qed.
Lemma sub_orr r1 r2 : r2 <=p r1 \+p r2. Proof. by right. Qed.
End RelLaws.

Section SubMemLaws.
Variable T : Type.
Implicit Type p q : Pred T.

Lemma subp_refl p : p <=p p.
Proof. by []. Qed.

Lemma subp_asym p1 p2 : p1 <=p p2 -> p2 <=p p1 -> p1 <~> p2.
Proof. by move=>H1 H2 x; split; [move/H1 | move/H2]. Qed.

Lemma subp_trans p2 p1 p3 : p1 <=p p2 -> p2 <=p p3 -> p1 <=p p3.
Proof. by move=>H1 H2 x; move/H1; move/H2. Qed.

Lemma subp_or p1 p2 q : 
        p1 <=p q /\ p2 <=p q <-> p1 \+p p2 <=p q.
Proof.
split=>[[H1] H2 x|H1]; first by case; [move/H1 | move/H2].
by split=>x H2; apply: H1; [left | right].
Qed.

Lemma subp_and p1 p2 q : 
        q <=p p1 /\ q <=p p2 <-> q <=p p1 \*p p2.
Proof.
split=>[[H1] H2 x|] H; last by split=>x; case/H.
by split; [apply: H1 | apply: H2].
Qed.

Lemma subp_orl p1 p2 q : 
        p1 <=p p2 -> p1 \+p q <=p p2 \+p q.
Proof. by move=>H x; case; [move/H; left|right]. Qed.

Lemma subp_orr p1 p2 q : 
        p1 <=p p2 -> q \+p p1 <=p q \+p p2.
Proof. by move=>H x; case; [left | move/H; right]. Qed.

Lemma subp_andl p1 p2 q : 
       p1 <=p p2 -> p1 \*p q <=p p2 \*p q.
Proof. by by move=>H x [H1 H2]; split; [apply: H|]. Qed.

Lemma subp_andr p1 p2 q : 
        p1 <=p p2 -> q \*p p1 <=p q \*p p2.
Proof. by move=>H x [H1 H2]; split; [|apply: H]. Qed.

End SubMemLaws.

#[export] Hint Resolve subp_refl : core.

Section ListMembership.
Variable T : Type.

Fixpoint Mem_Seq (s : seq T) :=
  if s is y::s' then (fun x => x = y \/ Mem_Seq s' x) else xPred0.

Definition EqSeq_Class := seq T.
Identity Coercion seq_of_EqSeq : EqSeq_Class >-> seq.
Coercion Pred_Of_Seq (s : EqSeq_Class) : {Pred T} := [eta Mem_Seq s].
Canonical Structure seq_PredType := 
  PropPredType (Pred_Of_Seq : seq T -> Pred T).
(* The line below makes mem_seq a canonical instance of topred. *)
Canonical Structure Mem_Seq_PredType := PropPredType Mem_Seq.

Lemma In_cons y s x : (x \In y :: s) <-> (x = y) \/ (x \In s).
Proof. by []. Qed.

Lemma In_nil x : (x \In [::]) <-> False.
Proof. by []. Qed.

Lemma Mem_Seq1 x y : (x \In [:: y]) <-> (x = y).
Proof. by rewrite In_cons orpF. Qed.

Definition InE := 
  (Mem_Seq1, In_cons, 
     (In_Applicative, In_Simpl, Simpl_PredE)).

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
elim: s=>[|y s IH] //=; rewrite InE.
case=>[<-|]; first by exists [::], s.
by case/IH=>s1 [s2 ->]; exists (y :: s1), s2.
Qed.

End ListMembership.

Prenex Implicits In_split.

(* for equality types, membership predicates coincide *)
Lemma mem_seqP (A : eqType) x (s : seq A) : reflect (x \In s) (x \in s).
Proof.
elim: s=>[|y s IH]; first by constructor.
rewrite inE; case: eqP=>[<-|H /=]; first by constructor; left.
by apply: equivP IH _; rewrite InE; split; [right | case].
Qed.

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

Lemma MapP T1 T2 (f : T1 -> T2) (s : seq T1) (y : T2) :
        y \In map f s <-> exists2 x, x \In s & y = f x.
Proof.
elim: s => [|x s IHs] /=; first by split=>//; case.
rewrite In_cons; split.
- case=>[->|]; first by exists x=>//; apply/In_cons; left.
  by case/IHs=>k H ->; exists k=>//; apply/In_cons; right.
case=>k /In_cons [->|H E]; first by left.
by right; apply/IHs; exists k.
Qed.

Lemma mapPP T1 (T2 : eqType) (f : T1 -> T2) (s : seq T1) y :
        reflect (exists2 x, x \In s & y = f x) (y \in map f s).
Proof. by apply: (iffP idP)=>[/mem_seqP/MapP|/MapP/mem_seqP]. Qed.

Lemma Mem_filter (T : Type) (a : pred T) (x : T) (s : seq T) :
        x \In filter a s <-> a x /\ x \In s.
Proof.
elim: s; first by split; case.
move=>y s IHs /=; rewrite 2!fun_if /=.
case E: (a y).
- rewrite InE IHs; split; last first.
  - by case=>H1 /In_cons [->|]; [left | right].
  case=>[->|]; first by split=>//; apply/In_cons; left.
  by case=>H1 H2; split=>//; apply/In_cons; right.
rewrite IHs; split.
- by case=>H1 H2; split=>//; apply/In_cons; right.
by case=>H1 /In_cons [] // ?; subst y; rewrite E in H1.
Qed.

Lemma eq_In_filter (T : Type) a1 a2 (s : seq T) :
        (forall x, x \In s -> a1 x = a2 x) ->
        filter a1 s = filter a2 s.
Proof.
elim: s => //= x s IHs eq_a.
rewrite eq_a; last by rewrite InE; left.
rewrite IHs // => y s_y; apply: eq_a.
by rewrite InE; right.
Qed.

Lemma eq_In_map S T (f g : S -> T) (s : seq S) :
        (forall x, x \In s -> f x = g x) <->
        map f s = map g s.
Proof.
elim: s=>[|x s IH] //=; split=>[H|[H1 /IH H2 k]].
- by congr (_ :: _); [apply: H; left|apply/IH=>k K; apply: H; right].
by rewrite InE; case=>[->|/H2].
Qed.


(* Big \In equivalences for all and has *)

Section allhasP.
Context {T : Type}.
Variables (p : pred T).

Lemma allPIn (s : seq T) :
        reflect (forall x, x \In s -> p x) (all p s).
Proof.
elim: s=>[|x s IHs] /=; first by constructor.
case: andP=>[[H1 H2]|H]; constructor.
- by move=>z /In_cons [->|/(IHs H2)].
move=>H1; elim: H; split; first by apply/H1/In_cons; left.
by apply/IHs=>z H; apply/H1/In_cons; right.
Qed.

Lemma allPnIn (s : seq T) :
        reflect (exists2 x, x \In s & ~~ p x) (~~ all p s).
Proof.
elim: s => [|x s IHs] /=; first by constructor=> [[x Hx _]].
rewrite /= andbC negb_and; case: IHs => IHs /=.
- by constructor; case: IHs => y Hy Hay; exists y=>//; apply/In_cons; right.
apply: (iffP idP) => [|[y]]; first by exists x=>//; apply/In_cons; left.
by case/In_cons=>[->//|H1 H2]; elim: IHs; exists y.
Qed.

Lemma hasPIn (s : seq T) :
        reflect (exists2 x, x \In s & p x) (has p s).
Proof.
elim: s => [|y s IHs] /=; first by right; case.
case Py: (p y); first by left; exists y=>//; apply/In_cons; left.
apply: (iffP IHs)=>[] [x ysx Px]; exists x => //; first by apply/In_cons; right.
by case/In_cons: ysx Px Py=>[->->|].
Qed.

Lemma hasPnIn (s : seq T) :
        reflect (forall x, x \In s -> ~~ p x) (~~ has p s).
Proof.
apply: (iffP (negPP (hasPIn s)))=>H.
- by move=>x Hx; apply: contra_notN H=>Px; exists x.
by case=>x Hx; apply/negP/H.
Qed.

(* implication form of hasPIn is frequently used *)
(* and if you don't have it, causes fluff in proofs *)

Lemma hasPInX x xs : x \In xs -> p x -> has p xs.
Proof. by move=>H1 H2; apply/hasPIn; exists x. Qed.

End allhasP.

Arguments hasPInX {T p x xs}.

Section AllHasP.
Context {T : Type}.
Variables (P : Pred T).

Fixpoint All xs := if xs is x :: xs then P x /\ All xs else True.

Lemma AllP xs : All xs <-> forall x, x \In xs -> P x.
Proof.
elim: xs=>[|x xs IH] //=.
split; first by case=>H1 /IH H2 z; rewrite InE; case=>[->//|]; apply: H2.
move=>H; split; first by apply: H; rewrite InE; left.
by apply/IH=>z Z; apply: H; rewrite InE; right.
Qed.

Lemma All_cat (s1 s2 : seq T) :
        All (s1 ++ s2) <-> All s1 /\ All s2.
Proof.
split.
- by move/AllP=>H; split; apply/AllP=>x Hx; apply/H/Mem_cat; [left|right].
by case=>/AllP H1 /AllP H2; apply/AllP=>x /Mem_cat; case=>Hx; [apply: H1| apply: H2].
Qed.

Fixpoint Has xs := if xs is x :: xs then P x \/ Has xs else False.

Lemma HasP xs : Has xs <-> exists2 x, x \In xs & P x.
Proof.
elim: xs=>[|x xs IH] /=; first by split=>//; case.
split.
- case=>[H|/IH]; first by exists x=>//; rewrite InE; left.
  by case=>y H1 H2; exists y=>//; rewrite InE; right.
case=>y; rewrite InE; case=>[->|H1 H2]; first by left.
by right; apply/IH; exists y.
Qed.

Lemma Has_cat (s1 s2 : seq T) :
        Has (s1 ++ s2) <-> Has s1 \/ Has s2.
Proof.
split.
- by move/HasP=>[x] /Mem_cat; case=>Hx Px; [left|right]; apply/HasP; exists x.
by case=>/HasP [x Hx Px]; apply/HasP; exists x=>//; apply/Mem_cat; [left|right].
Qed.

End AllHasP.

Section AllHasT.
Context {T : Type}.
Variables (P : T -> Type).

Fixpoint AllT xs : Type := if xs is x :: xs then P x * AllT xs else unit.

Fixpoint HasT xs : Type := if xs is x :: xs then P x + HasT xs else Empty_set.

End AllHasT.

(* prop uniqueness *)
Fixpoint Uniq T (xs : seq T) := 
  if xs is x :: xs then x \Notin xs /\ Uniq xs else True.

Lemma UniqP (T : eqType) (xs : seq T) : 
        reflect (Uniq xs) (uniq xs).
Proof.
elim: xs=>[|x xs IH] //=; first by apply: ReflectT.
case: andP=>H; constructor.
- by case: H=>/mem_seqP H /IH.
by case=>/mem_seqP H1 /IH H2; elim: H.
Qed.

Lemma map_Uniq T1 (T2 : eqType) (f : T1 -> T2) (s : seq T1) :
        uniq [seq f i | i <- s] -> Uniq s.
Proof.
elim: s=>//= x s IH /andP [nsfx /IH H]; split=>//.
apply: contraNnot nsfx=>Hx.
by apply/mapPP; exists x.
Qed.

(* \In and big operators *)

Lemma Big_rec R (K : R -> Type) (idx : R) (op : R -> R -> R) :
        K idx ->
        forall I (r : seq I) (P : pred I) (F : I -> R),
        (forall (i : I) (x : R), i \In r -> P i -> K x -> K (op (F i) x)) ->
        K (\big[op/idx]_(i <- r | P i) F i).
Proof.
rewrite unlock; move=>Kid I r P F; elim: r=>[|x r IH] Kop //=.
case: ifP=>H; last by apply: IH=>i x0 X; apply: Kop; right.
apply: (Kop)=>//; first by left.
by apply: IH=>i x0 X; apply: Kop; right.
Qed.

Lemma Big_rec2 R1 R2 (K : R1 -> R2 -> Type) (id1 : R1)
         (op1 : R1 -> R1 -> R1) (id2 : R2) (op2 : R2 -> R2 -> R2) :
       K id1 id2 ->
       forall I (r : seq I) (P : pred I) (F1 : I -> R1) (F2 : I -> R2),
       (forall (i : I) (y1 : R1) (y2 : R2),
         i \In r -> P i -> K y1 y2 ->
         K (op1 (F1 i) y1) (op2 (F2 i) y2)) ->
         K (\big[op1/id1]_(i <- r | P i) F1 i)
           (\big[op2/id2]_(i <- r | P i) F2 i).
Proof.
move=>Kid I r P F1 F2; rewrite unlock.
elim: r=>[|x r IH] //=.
case: ifP=>H K_F; last by apply: IH=>i y1 y2 X; apply: K_F; right.
apply: (K_F)=>//; first by left.
by apply: IH=>i y1 y2 X; apply: K_F; right.
Qed.

Lemma eq_Bigr R (idx : R) (op : R -> R -> R) I (r : seq I)
           (P : pred I) F1 F2 :
         (forall i, i \In r -> P i -> F1 i = F2 i) ->
         \big[op/idx]_(i <- r | P i) F1 i = \big[op/idx]_(i <- r | P i) F2 i.
Proof.
by move=>eqF12; elim/Big_rec2: _=>// i x y2 X /(eqF12 _ X) ->->.
Qed.

Lemma eq_bigR R (idx : R) (op : R -> R -> R) (I : eqType) (r : seq I)
           (P : pred I) F1 F2 :
         (forall i, i \in r -> P i -> F1 i = F2 i) ->
         \big[op/idx]_(i <- r | P i) F1 i = \big[op/idx]_(i <- r | P i) F2 i.
Proof. by move=>eqF12; apply: eq_Bigr=>i /mem_seqP/eqF12. Qed.


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
  (at level 0, E at level 99, i name,
   format "[ '[hv' 'Image'  E '/ '  |  i  <-  s ] ']'") : rel_scope.

Notation "[ 'Image' E | i <- s & C ]" := [Image E | i <- [PredI s & C]]
  (at level 0, E at level 99, i name,
   format "[ '[hv' 'Image'  E '/ '  |  i  <-  s '/ '  &  C ] ']'") : rel_scope.

Notation "[ 'Image' E | i : T <- s ]" := (Image (fun i : T => E) s)
  (at level 0, E at level 99, i name, only parsing) : rel_scope.

Notation "[ 'Image' E | i : T <- s & C ]" :=
  [Image E | i : T <- [PredI s & C]]
  (at level 0, E at level 99, i name, only parsing) : rel_scope.

Lemma Image_mem A B (f : A -> B) (P : Pred A) x : 
        x \In P -> 
        f x \In Image f P.
Proof. by apply: Im_mem. Qed.

Lemma Image_inj_sub A B (f : A -> B) (X1 X2 : Pred A) :
        injective f -> 
        Image f X1 <=p Image f X2 -> 
        X1 <=p X2.
Proof. by move=>H E x /(Image_mem f) /E [y] /H ->. Qed.

Lemma Image_inj_eqmem A B (f : A -> B) (X1 X2 : Pred A) :
        injective f -> 
        Image f X1 <~> Image f X2 -> 
        X1 <~> X2.
Proof. by move=>H E; split; apply: Image_inj_sub H _ _; rewrite E. Qed.

Lemma ImageU A B (f : A -> B) (X1 X2 : Pred A) :
        Image f (PredU X1 X2) <~> PredU (Image f X1) (Image f X2).
Proof.
move=>x; split.
- by case=>y -> [H|H]; [left | right]; apply: Image_mem.
by case; case=>y -> H; apply: Image_mem; [left | right].
Qed.

Lemma ImageIm A B C (f1 : B -> C) (f2 : A -> B) (X : Pred A) :
        Image f1 (Image f2 X) <~> Image (f1 \o f2) X.
Proof.
move=>x; split; first by case=>_ -> [x' ->] H; exists x'.
by case=>a -> H; exists (f2 a)=>//; exists a.
Qed.

Lemma ImageEq A B (f1 f2 : A -> B) (X : Pred A) :
        f1 =1 f2 -> 
        Image f1 X <~> Image f2 X.
Proof. by move=>H x; split; case=>a ->; exists a. Qed.

(********************************)
(* Relation preserving function *)
(********************************)

Definition rel_on_func A B (f : B -> A) (p : Pred B) (g : Rel A) := 
  forall x y, p x -> g (f x) y -> 
    exists y', [/\ y = f y', p y' & (g \\o f) x y'].

Notation "'on-' f" := (rel_on_func f) 
 (at level 1, format "'on-' f").

(* last conjunct can be dropped *)
Lemma onE A B (f : B -> A) p g :  
        on-f p g <->
        forall x y, p x -> g (f x) y -> exists2 y', y = f y' & p y'.
Proof.
split=>H x y C /[dup] X /(H _ _ C).
- by case=>y' []; exists y'.
by case=>y' E; exists y'; rewrite /Rel_app -E.
Qed.

Add Parametric Morphism A B : (@rel_on_func A B) with signature
  eq ==> @Eq_Pred _ _ ==> eqRel ==> iff as relon_eq.
Proof.
move=>f p1 p2 H r1 r2 E; split=>X;
by apply/onE=>x y /H /= P /E /(X _ _ P) [y'][-> /H]; eauto. 
Qed.

Add Parametric Morphism A B : (@rel_on_func A B) with signature
  eq ==> @Eq_Pred _ _ ==> subRel ==> flip impl as relon_sub.
Proof.
move=>f p1 p2 H r1 r2 E X.
by apply/onE=>x y /H /= P /E /(X _ _ P) [y'][-> /H]; eauto. 
Qed.

(**********************************)
(**********************************)
(*      Theory of relations       *)
(**********************************)
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

(* Do NOT use Reflexive for actual lemmas *)
(* because auto does not unfold definitions, *)
(* so Hint Resolve lemma_refl won't work *)
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

#[export] Hint Resolve trans_imp trans_eq : core.


(**********************************************)
(* Reflexive-Transitive closure of a relation *)
(**********************************************)

Fixpoint iter' T (g : T -> T -> Prop) n s1 s2 :=
  if n is n'.+1 then exists s, g s1 s /\ iter' g n' s s2 else s1 = s2.
Definition iter T (g : T -> T -> Prop) s1 s2 := exists n, iter' g n s1 s2.

Section IteratedRels.
Variable T : Type.
Implicit Type g : T -> T -> Prop.

Lemma iter'_add g n1 n2 s1 s2 s3 :
        iter' g n1 s1 s2 -> iter' g n2 s2 s3 -> iter' g (n1 + n2) s1 s3.
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

Lemma iterS g n s1 s2 : 
        iter' g n.+1 s1 s2 <-> exists s, iter' g n s1 s /\ g s s2.
Proof.
rewrite -addn1; split; first by case/iter'_split=>s [H1] [s'][H2 <-]; exists s.
by case=>s [H1 H2]; apply: iter'_add H1 _; exists s2.
Qed.

Lemma iter_refl g s : iter g s s.
Proof. by exists 0. Qed.

Lemma iter_trans g : Transitive (iter g).
Proof.
move=> s2 s1 s3; case=>n; elim: n s1 =>[|n IH] s1 /=; first by move=>->.
by case=>s [H1 H2] /(IH _ H2) [m]; exists m.+1, s.
Qed.

Lemma iter_sub g g' : g ~2> g' -> iter g ~2> iter g'.
Proof.
move=>H s s' [n X]; exists n; elim: n s s' X=>[|n IH] s s' //=.
by case=>x [/H G] /IH; exists x. 
Qed.

Lemma iter_eq g g' : g <~2> g' -> iter g <~2> iter g'.
Proof. by move=>H s s'; split; apply/iter_sub; rewrite H. Qed.

Lemma iter1 g : g ~2> iter g.
Proof. by move=>s s'; exists 1, s'. Qed.

Lemma iter_app T' g (f : T' -> T) : iter (g \\o f) ~2>  iter g \\o f.
Proof. 
move=>s s' [n] H; exists n; elim: n s s' H=>[|n IH] s s' /=; first by move=>->.
by case=>x [H] /IH; exists (f x). 
Qed.

Lemma iter_on T' (f : T' -> T) p g : on-f p g -> on-f p (iter g).
Proof.
move=>O; apply/onE=>x y C [n].
elim: n x y C=>[|n IH] x y /= C; first by move=><-; exists x. 
case=>_ [/(O _ _ C)] [x'][->] X' H /(IH _ _ X') [y' ->] Y'.
by exists y'.
Qed.

Lemma iter_subf T' g (f : T' -> T) : iter (g \\o f) ~2> iter g \\o f.
Proof. 
move=>s s' [n] H; exists n.
elim: n s s' H=>[|n IH] s s'; first by move=>->.
by case=>x [H1] {}/IH; exists (f x).
Qed.

Lemma iter_fsub T' g (f : T' -> T) : 
        injective f ->
        on-f xpredT g ->      
        iter g \\o f ~2> iter (g \\o f).
Proof. 
move=>H1 H2 s s' [n] H; exists n.
elim: n s s' H =>[|n IH] s s' /=; first by move/H1.
by case=>_ [] /(H2 _ _ erefl) [x][-> _ X] {}/IH; exists x. 
Qed.

Lemma iter_eqf T' g (f : T' -> T) : 
        injective f ->
        on-f xpredT g ->
        iter g \\o f <~2> iter (g \\o f).
Proof. by move=>??; split; [apply: iter_fsub|apply: iter_subf]. Qed.

(* localized variant of iter_fsub *)
Lemma iter_fsubl T' g (f : T' -> T) p s s' : 
        injective f ->
        on-f p g ->
        p s ->
        (iter g \\o f) s s' -> iter (g \\o f) s s'.
Proof.
move=>H1 H2 P [n] H; exists n.
elim: n s s' P H=>[|n IH] s s' /= Ps; first by move/H1=>->.
by case=>_ [] /(H2 _ _ Ps) [x][-> Px H] /(IH _ _ Px); exists x.
Qed.

End IteratedRels.

Lemma iter_pair {T} {g : unit*T -> unit*T -> Prop} :
        iter g \\o pair tt <~2> iter (g \\o pair tt).
Proof. by apply: iter_eqf=>[x y []|x [[y]]] //; exists y. Qed.

Add Parametric Morphism A : (@iter A) with signature
  eqRel ==> eqRel as iter_eq'.
Proof. by move=>x y H x1 y1; rewrite (iter_eq H _). Qed.

Add Parametric Morphism A : (@iter A) with signature
  subRel ==> subRel as iter_sub'.
Proof. by move=>x y H x1 y1; apply: iter_sub. Qed.

Lemma iter_pres' A (g : Rel A) n C : preserved C g -> preserved C (iter' g n).
Proof.
move=>coh; elim: n=>[|n IH] x y /=; first by move=><-.
by case=>z [/coh H1] H2 /H1; apply: IH.
Qed.

Lemma iter_pres A (g : Rel A) C : preserved C g -> preserved C (iter g).
Proof. by move=>pres x y [n] /(iter_pres' pres). Qed.

Arguments iter1 {T}%_type_scope {g _ _}.
Arguments iter_app {T T'}%_type_scope {g f}. 
Arguments iter_refl {T g s}.

#[export] Hint Resolve iter_refl : core.


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
Proof. by split. Qed.
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

Arguments id_rel {A} _ _ /.
Arguments pre_rel {A} P R _ _ /.
Arguments post_rel {A} R Q _ _ /.

Lemma union_eq A (x1 y1 x2 y2 : Rel A) :
        eqRel x1 y1 -> eqRel x2 y2 -> 
        eqRel (Union_rel x1 x2) (Union_rel y1 y2).
Proof. by rewrite /eqRel/Union_rel=>E1 E2 x y; rewrite E1 E2. Qed.

Arguments union_eq {A x1 y1 x2 y2}.
Prenex Implicits union_eq.

Add Parametric Morphism A : (@Union_rel A) with signature
  eqRel ==> eqRel ==> eqRel as union_eq'. 
Proof. by move=>*; apply: union_eq. Qed.

Lemma union_sub A (x1 y1 x2 y2 : Rel A) :
        subRel x1 y1 -> subRel x2 y2 -> 
        subRel (Union_rel x1 x2) (Union_rel y1 y2).
Proof. by move=>E1 E2 x y [/E1|/E2]; [left | right]. Qed.

Arguments union_sub {A x1 y1 x2 y2}.
Prenex Implicits union_sub.

Add Parametric Morphism A : (@Union_rel A) with signature
  subRel ==> subRel ==> subRel as union_sub1. 
Proof. by move=>*; apply: union_sub. Qed.

Lemma subrelL A (x y : Rel A) : x ~2> Union_rel x y.
Proof. by left. Qed.

Lemma subrelR A (x y : Rel A) : y ~2> Union_rel x y.
Proof. by right. Qed.

#[export]
Instance eqrel_subrel A : subrelation (@eqRel A) (@subRel A).
Proof. by move=>x y H ?? /H. Qed.

Lemma union_app A B D1 D2 (f : B -> A) :
        Union_rel D1 D2 \\o f <~2>
        Union_rel (D1 \\o f) (D2 \\o f).
Proof. by apply: union_eq. Qed.

Arguments union_app {A B}%_type_scope {D1 D2 f}%_function_scope.
Prenex Implicits union_app.

Lemma on_union A B D1 D2 (f : B -> A) p :
        on-f p D1 -> 
        on-f p D2 ->
        on-f p (Union_rel D1 D2).
Proof.
move=>H1 H2; apply/onE=>x y P; case.
- by case/(H1 _ _ P)=>y' [->] P'; exists y'.
by case/(H2 _ _ P)=>y' [->] P'; exists y'.
Qed.

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

(* we can now state localized version of iter_fsubl *)
Lemma iter_fsubl' T T' (g : Rel T) (f : T' -> T) p : 
        injective f ->
        on-f p g ->
        {In p & xPredT, iter g \\o f ~2> iter (g \\o f)}.
Proof. by move=>H1 H2 x y H _; apply: iter_fsubl H1 H2 H. Qed.


