(*
Copyright 2013 IMDEA Software Institute
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
(* This file contains the reference implementation of finite maps with keys   *)
(* satisfying condition p and supporting disjoint union via a top element.    *)
(*                                                                            *)
(* Union maps signature definitions:                                          *)
(*       from f == union map f converted to a base finite map.                *)
(*         to m == finite map m converted to a union map.                     *)
(*    defined f == union map f is valid.                                      *)
(*     um_undef == an undefined (i.e., invalid) instance of a union map.      *)
(*        empty == a valid empty instance of a union map.                     *)
(*    upd k v f == union map f with key-value pair (k,v) inserted. If key k   *)
(*                 already exists in t, its corresponding value is            *)
(*                 overwritten with v.                                        *)
(*        dom f == a sequence of keys for union map f.                        *)
(* dom_eq f1 f2 == the sets of keys are equal for union maps f1 and f2.       *)
(*     assocs t == a sequence of key-value pairs in union map t.              *)
(*     free f k == union map f without the key k and its corresponding value. *)
(*     find k f == a value corresponding to key k in union map f, wrapped in  *)
(*                 an option type.                                            *)
(*  union f1 f2 == a union map formed by taking a disjoint union of maps f1   *)
(*                 and f2. If the maps are not disjoint, the result is        *)
(*                 undefined.                                                 *)
(*       empb f == union map f is valid and empty.                            *)
(*     undefb f == union map f is undefined.                                  *)
(*      pts k v == a fresh instance of a union map containing a single        *)
(*                 key-value pair (k,v).                                      *)
(*                                                                            *)
(* Defined notions:                                                           *)
(*    um_preim p f k == a value corresponding to key k exists in union map f  *)
(*                      and satisfies predicate p.                            *)
(*           range f == a sequence of values for union map f.                 *)
(*         um_mono f == values of union map f are in a monotonically          *)
(*                      increasing order.                                     *)
(* um_foldl a z0 d f == if f is valid, a result of a left fold over its       *)
(*                      key-value pairs using function a and starting         *)
(*                      value z0, d otherwise.                                *)
(* um_foldr a z0 d f == if f is valid, a result of a right fold over its      *)
(*                      key-value pairs using function a and starting         *)
(*                      value z0, d otherise.                                 *)
(*          omap a f == the result of applying a generalized                  *)
(*                      mapping/filtering function a to union map t. The      *)
(*                      function may inspect both the key and the value and   *)
(*                      return either a new value wrapped in Some, or None if *)
(*                      the key-value pair is to be excluded.                 *)
(*         omapv a f == same as omap, but function a may only inspect the     *)
(*                      value.                                                *)
(*          mapv a f == same as omapv, but function a may only return the new *)
(*                      value, i.e. it is a standard functional mapping.      *)
(*     um_filter p f == the result of applying a filtering function p to      *)
(*                      union map f. Function f may inspect both the key and  *)
(*                      the value.                                            *)
(*    um_filterk p f == same as um_filter, but function p may only inspect    *)
(*                      the key.                                              *)
(*    um_filterv p f == same as um_filter, but function p may only inspect    *)
(*                      the value.                                            *)
(*   oeval a ks f z0 == the result of iteratively applying function a to      *)
(*                      key-value pairs in union map f, in the order          *)
(*                      indicated by sequence of keys ks.                     *)
(*     eval a p f z0 == the result of iteratively applying function a to      *)
(*                      all key-value pairs satisfying predicate p in union   *)
(*                      map f.                                                *)
(*      um_count p f == the number of key-values pairs satisfying predicate p *)
(*                      in union map f.                                       *)
(*         dom_map f == a union map f converted to a finite set, i.e., all    *)
(*                      its values are replaced by tt.                        *)
(*         inverse f == a union map f with its keys and values swapped, i.e., *)
(*                      the values are now serving as keys and vice versa.    *)
(*       um_comp g f == a union map obtained by composing union maps g and f. *)
(*                      The keys taken from f, and their corresponding values *)
(*                      are treated as keys in g for looking up the final     *)
(*                      values.                                               *)
(*        um_all P f == type-level predicate P holds for all key-value pairs  *)
(*                      in union map f.                                       *)
(*       um_allb p f == predicate p holds for all key-value pairs in union    *)
(*                      map f.                                                *)
(*   um_all2 P f1 f2 == binary type-level predicate P holds for all values of *)
(*                      equal keys in union maps f1 and f2.                   *)
(******************************************************************************)

From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path.
From fcsl Require Import prelude finmap seqperm pcm morphism pred.
From fcsl Require Export ordtype.
From fcsl Require Import options.

(* I decided to have union_map_class be a class, rather than a
structure. The class packages a condition on keys. Ordinary union_maps
have a trivially true condition. Heaps have a condition that the
pointers are non-null.  Then ordinary union maps, as well as heaps,
are declared as instances of this class, to automatically inherit all
the lemmas about the operations.

An alternative implementation would have been to define
union_map_class as a structure parametrized by the condition, and then
obtain heaps by taking the parameter condition of non-null pointers,
and ordinary union_maps by taking parameter condition to true.

I decided on the more complicated design to avoid the universe
jump. Heap values are dynamic, and live in Type(1), while most of the
times, ordinary union_maps store values from Type(0), and can be
nested. If the two structures (heaps and ordinary union maps) share
the same code, they will both lift to the common universe of Type(1),
preventing me from using maps at Type(0), and storing them in the heap.

With the class design, no code is shared, only the lemmas (i.e., only
the class type, but that can freely live in an arbitrary
universe). The price to pay is that the code of the methods has to be
duplicated when declaring instances (such as in heaps.v, or below for
union_mapUMC), just to keep the universes from jumping.  *)

Module UM.
Section UM.
Variables (K : ordType) (C : pred K) (V : Type).

Inductive base :=
  Undef | Def (f : finMap K V) of all C (supp f).

Section FormationLemmas.
Variable (f g : finMap K V).

Lemma all_supp_insP (k : K) v :
        C k -> all C (supp f) -> all C (supp (ins k v f)).
Proof.
move=>H1 H2; apply/allP=>x; rewrite supp_ins inE /=.
by case: eqP=>[->|_] //=; move/(allP H2).
Qed.

Lemma all_supp_remP k : all C (supp f) -> all C (supp (rem k f)).
Proof.
move=>H; apply/allP=>x; rewrite supp_rem inE /=.
by case: eqP=>[->|_] //=; move/(allP H).
Qed.

Lemma all_supp_fcatP :
        all C (supp f) -> all C (supp g) -> all C (supp (fcat f g)).
Proof.
move=>H1 H2; apply/allP=>x; rewrite supp_fcat inE /=.
by case/orP; [move/(allP H1) | move/(allP H2)].
Qed.

Lemma all_supp_kfilterP q :
        all C (supp f) -> all C (supp (kfilter q f)).
Proof.
move=>H; apply/allP=>x; rewrite supp_kfilt mem_filter.
by case/andP=>_ /(allP H).
Qed.

Lemma all_supp_mapfP (a : K -> V -> V) :
        all C (supp f) -> all C (supp (mapf a f)).
Proof.
by move=>H; apply/allP=>x; rewrite supp_mapf; move/(allP H).
Qed.

End FormationLemmas.

Implicit Types (k : K) (v : V) (f g : base).

Lemma umapE (f g : base) :
        f = g <-> match f, g with
                    Def f' pf, Def g' pg => f' = g'
                  | Undef, Undef => true
                  | _, _ => false
                  end.
Proof.
split; first by move=>->; case: g.
case: f; case: g=>// f pf g pg E; rewrite {g}E in pg *.
by congr Def; apply: eq_irrelevance.
Qed.

Definition valid f := if f is Def _ _ then true else false.

Definition empty := @Def (finmap.nil K V) is_true_true.

Definition upd k v f :=
  if f is Def fs fpf then
    if decP (@idP (C k)) is left pf then
      Def (all_supp_insP v pf fpf)
    else Undef
  else Undef.

Definition dom f : seq K :=
  if f is Def fs _ then supp fs else [::].

Definition dom_eq f1 f2 :=
  match f1, f2 with
    Def fs1 _, Def fs2 _ => supp fs1 == supp fs2
  | Undef, Undef => true
  | _, _ => false
  end.

Definition assocs f : seq (K * V) :=
  if f is Def fs _ then seq_of fs else [::].

Definition free f k :=
  if f is Def fs pf then Def (all_supp_remP k pf) else Undef.

Definition find k f := if f is Def fs _ then fnd (K:=K) k fs else None.

Definition union f1 f2 :=
  if (f1, f2) is (Def fs1 pf1, Def fs2 pf2) then
    if disj fs1 fs2 then
      Def (all_supp_fcatP pf1 pf2)
    else Undef
  else Undef.

Definition empb f := if f is Def fs _ then supp fs == [::] else false.

Definition undefb f := if f is Undef then true else false.

Definition pts k v := upd k v empty.

(* forward induction *)
Lemma base_indf (P : base -> Prop) :
         P Undef -> P empty ->
         (forall k v f, P f -> valid (union (pts k v) f) ->
                        path ord (k : [ordType of K]) (dom f) ->
                        P (union (pts k v) f)) ->
         forall f, P f.
Proof.
rewrite /empty => H1 H2 H3; apply: base_ind=>//.
apply: fmap_ind'=>[|k v f S IH] H.
- by set f := Def _ in H2; rewrite (_ : Def H = f) // /f umapE.
have N : k \notin supp f by apply: notin_path S.
have [T1 T2] : C k /\ all C (supp f).
- split; first by apply: (allP H k); rewrite supp_ins inE /= eq_refl.
- apply/allP=>x T; apply: (allP H x).
  by rewrite supp_ins inE /= T orbT.
have E : FinMap (sorted_ins' k v (sorted_nil K V)) = ins k v (@nil K V) by [].
have: valid (union (pts k v) (Def T2)).
- rewrite /valid /union /pts /upd /=.
  case: decP; last by rewrite T1.
  by move=>T; case: ifP=>//; rewrite E disjC disj_ins N disj_nil.
move/(H3 k v _ (IH T2)).
rewrite (_ : union (pts k v) (Def T2) = Def H).
- by apply.
rewrite umapE /union /pts /upd /=.
case: decP=>// T; rewrite /disj /= N /=.
by rewrite E fcat_inss // fcat0s.
Qed.

(* backward induction *)
Lemma base_indb (P : base -> Prop) :
         P Undef -> P empty ->
         (forall k v f, P f -> valid (union f (pts k v)) ->
                        (forall x : [ordType of K], x \in dom f -> ord x k) ->
                        P (union (pts k v) f)) ->
         forall f, P f.
Proof.
rewrite /empty => H1 H2 H3; apply: base_ind=>//.
apply: fmap_ind''=>[|k v f S IH] H.
- by set f := Def _ in H2; rewrite (_ : Def H = f) // /f umapE.
have N : k \notin supp f by apply/negP; move/S; rewrite ordtype.irr.
have [T1 T2] : C k /\ all C (supp f).
- split; first by apply: (allP H k); rewrite supp_ins inE /= eq_refl.
- apply/allP=>x T; apply: (allP H x).
  by rewrite supp_ins inE /= T orbT.
have E : FinMap (sorted_ins' k v (sorted_nil K V)) = ins k v (@nil K V) by [].
have: valid (union (Def T2) (pts k v)).
- rewrite /valid /union /pts /upd /=.
  case: decP; last by rewrite T1.
  by move=>T; case: ifP=>//; rewrite E disj_ins N disj_nil.
move/(H3 k v _ (IH T2)).
rewrite (_ : union (pts k v) (Def T2) = Def H); first by apply; apply: S.
rewrite umapE /union /pts /upd /=.
case: decP=>// T; rewrite /disj /= N /=.
by rewrite E fcat_inss // fcat0s.
Qed.

End UM.
End UM.

(* a class of union_map types *)

Module UMC.
Section MixinDef.
Variables (K : ordType) (C : pred K) (V : Type).

Structure mixin_of (T : Type) := Mixin {
  defined_op : T -> bool;
  empty_op : T;
  undef_op : T;
  upd_op : K -> V -> T -> T;
  dom_op : T -> seq K;
  dom_eq_op : T -> T -> bool;
  assocs_op : T -> seq (K * V);
  free_op : T -> K -> T;
  find_op : K -> T -> option V;
  union_op : T -> T -> T;
  empb_op : T -> bool;
  undefb_op : T -> bool;
  pts_op : K -> V -> T;

  from_op : T -> UM.base C V;
  to_op : UM.base C V -> T;
  _ : forall b, from_op (to_op b) = b;
  _ : forall f, to_op (from_op f) = f;
  _ : forall f, defined_op f = UM.valid (from_op f);
  _ : undef_op = to_op (UM.Undef C V);
  _ : empty_op = to_op (UM.empty C V);
  _ : forall k v f, upd_op k v f = to_op (UM.upd k v (from_op f));
  _ : forall f, dom_op f = UM.dom (from_op f);
  _ : forall f1 f2, dom_eq_op f1 f2 = UM.dom_eq (from_op f1) (from_op f2);
  _ : forall f, assocs_op f = UM.assocs (from_op f);
  _ : forall f k, free_op f k = to_op (UM.free (from_op f) k);
  _ : forall k f, find_op k f = UM.find k (from_op f);
  _ : forall f1 f2,
        union_op f1 f2 = to_op (UM.union (from_op f1) (from_op f2));
  _ : forall f, empb_op f = UM.empb (from_op f);
  _ : forall f, undefb_op f = UM.undefb (from_op f);
  _ : forall k v, pts_op k v = to_op (UM.pts C k v)}.

End MixinDef.

Section ClassDef.
Variables (K : ordType) (C : pred K) (V : Type).

Notation class_of := mixin_of (only parsing).

Structure type : Type := Pack {sort : Type; _ : class_of C V sort}.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of C V cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Definition pack (m : @mixin_of K C V T) :=
  @Pack T m.

Definition from := from_op class.
Definition to := to_op class.
Definition defined := defined_op class.
Definition um_undef := undef_op class.
Definition empty := empty_op class.
Definition upd : K -> V -> cT -> cT := upd_op class.
Definition dom : cT -> seq K := dom_op class.
Definition dom_eq := dom_eq_op class.
Definition assocs : cT -> seq (K * V) := assocs_op class.
Definition free : cT -> K -> cT := free_op class.
Definition find : K -> cT -> option V := find_op class.
Definition union := union_op class.
Definition empb := empb_op class.
Definition undefb := undefb_op class.
Definition pts : K -> V -> cT := pts_op class.

End ClassDef.

Arguments to {K C V cT}.
Arguments um_undef {K C V cT}.
Arguments empty {K C V cT}.
Arguments pts [K C V cT] _ _.
Prenex Implicits pts.

Section Lemmas.
Variables (K : ordType) (C : pred K) (V : Type) (U : type C V).
Local Coercion sort : type >-> Sortclass.
Implicit Type f : U.

Lemma ftE (b : UM.base C V) : from (to b : U) = b.
Proof. by case: U b =>x [*]. Qed.

Lemma tfE f : to (from f) = f.
Proof. by case: U f=>x [*]. Qed.

Lemma eqE (b1 b2 : UM.base C V) :
        to b1 = to b2 :> U <-> b1 = b2.
Proof. by split=>[E|-> //]; rewrite -[b1]ftE -[b2]ftE E. Qed.

Lemma defE f : defined f = UM.valid (from f).
Proof. by case: U f=>x [*]. Qed.

Lemma undefE : um_undef = to (UM.Undef C V) :> U.
Proof. by case: U=>x [*]. Qed.

Lemma emptyE : empty = to (UM.empty C V) :> U.
Proof. by case: U=>x [*]. Qed.

Lemma updE k v f : upd k v f = to (UM.upd k v (from f)).
Proof. by case: U k v f=>x [*]. Qed.

Lemma domE f : dom f = UM.dom (from f).
Proof. by case: U f=>x [*]. Qed.

Lemma dom_eqE f1 f2 : dom_eq f1 f2 = UM.dom_eq (from f1) (from f2).
Proof. by case: U f1 f2=>x [*]. Qed.

Lemma assocsE f : assocs f = UM.assocs (from f).
Proof. by case: U f=>x [*]. Qed.

Lemma freeE f k : free f k = to (UM.free (from f) k).
Proof. by case: U k f=>x [*]. Qed.

Lemma findE k f : find k f = UM.find k (from f).
Proof. by case: U k f=>x [*]. Qed.

Lemma unionE f1 f2 : union f1 f2 = to (UM.union (from f1) (from f2)).
Proof. by case: U f1 f2=>x [*]. Qed.

Lemma empbE f : empb f = UM.empb (from f).
Proof. by case: U f=>x [*]. Qed.

Lemma undefbE f : undefb f = UM.undefb (from f).
Proof. by case: U f=>x [*]. Qed.

Lemma ptsE k v : pts k v = to (UM.pts C k v) :> U.
Proof. by case: U k v=>x [*]. Qed.

End Lemmas.

Module Exports.
Coercion sort : type >-> Sortclass.
Notation union_map_class := type.
Notation UMCMixin := Mixin.
Notation UMC T m := (@pack _ _ _ T m).

Notation "[ 'umcMixin' 'of' T ]" := (class _ _ _ _ : mixin_of T)
  (at level 0, format "[ 'umcMixin'  'of'  T ]") : form_scope.
Notation "[ 'um_class' 'of' T 'for' C ]" := (@clone _ _ _ T C _ idfun)
  (at level 0, format "[ 'um_class'  'of'  T  'for'  C ]") : form_scope.
Notation "[ 'um_class' 'of' T ]" := (@clone _ _ _ T _ _ id)
  (at level 0, format "[ 'um_class'  'of'  T ]") : form_scope.

Notation um_undef := um_undef.
Notation upd := upd.
Notation dom := dom.
Notation dom_eq := dom_eq.
Notation assocs := assocs.
Notation free := free.
Notation find := find.
Notation empb := empb.
Notation undefb := undefb.
Notation pts := pts.

Definition umEX :=
  (ftE, tfE, eqE, undefE, defE, emptyE, updE, domE, dom_eqE, assocsE,
   freeE, findE, unionE, empbE, undefbE, ptsE, UM.umapE).

End Exports.

End UMC.

Export UMC.Exports.


(***********************)
(* monoidal properties *)
(***********************)

Module UnionMapClassPCM.
Section UnionMapClassPCM.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map_class C V).
Implicit Type f : U.

Local Notation "f1 \+ f2" := (@UMC.union _ _ _ _ f1 f2)
  (at level 43, left associativity).
Local Notation valid := (@UMC.defined _ _ _ U).
Local Notation unit := (@UMC.empty _ _ _ U).

Lemma joinC f1 f2 : f1 \+ f2 = f2 \+ f1.
Proof.
rewrite !umEX /UM.union.
case: (UMC.from f1)=>[|f1' H1]; case: (UMC.from f2)=>[|f2' H2] //.
by case: ifP=>E; rewrite disjC E // fcatC.
Qed.

Lemma joinCA f1 f2 f3 : f1 \+ (f2 \+ f3) = f2 \+ (f1 \+ f3).
Proof.
rewrite !umEX /UM.union /=.
case: (UMC.from f1) (UMC.from f2) (UMC.from f3)=>[|f1' H1][|f2' H2][|f3' H3] //.
case E1: (disj f2' f3'); last first.
- by case E2: (disj f1' f3')=>//; rewrite disj_fcat E1 andbF.
rewrite disj_fcat andbC.
case E2: (disj f1' f3')=>//; rewrite disj_fcat (disjC f2') E1 /= andbT.
by case E3: (disj f1' f2')=>//; rewrite fcatAC // E1 E2 E3.
Qed.

Lemma joinA f1 f2 f3 : f1 \+ (f2 \+ f3) = (f1 \+ f2) \+ f3.
Proof. by rewrite (joinC f2) joinCA joinC. Qed.

Lemma validL f1 f2 : valid (f1 \+ f2) -> valid f1.
Proof. by rewrite !umEX; case: (UMC.from f1). Qed.

Lemma unitL f : unit \+ f = f.
Proof.
rewrite -[f]UMC.tfE !umEX /UM.union /UM.empty.
by case: (UMC.from f)=>[//|f' H]; rewrite disjC disj_nil fcat0s.
Qed.

Lemma validU : valid unit.
Proof. by rewrite !umEX. Qed.

End UnionMapClassPCM.

Module Exports.
Section Exports.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map_class C V).

(* generic structure for PCM for *all* union maps *)
(* I will add specific ones too for individual types *)
(* so that the projections can match against a concrete type *)
(* not against another projection, as is the case *)
(* with the generic class here *)
Definition union_map_classPCMMix :=
  PCMMixin (@joinC K C V U) (@joinA K C V U) (@unitL K C V U)
           (@validL K C V U) (validU U).
Canonical union_map_classPCM := Eval hnf in PCM U union_map_classPCMMix.

End Exports.
End Exports.

End UnionMapClassPCM.

Export UnionMapClassPCM.Exports.


(*****************)
(* Cancelativity *)
(*****************)

Module UnionMapClassCPCM.
Section Cancelativity.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map_class C V).
Implicit Type f : U.

Lemma joinKf f1 f2 f : valid (f1 \+ f) -> f1 \+ f = f2 \+ f -> f1 = f2.
Proof.
rewrite -{3}[f1]UMC.tfE -{2}[f2]UMC.tfE !pcmE /= !umEX /UM.valid /UM.union.
case: (UMC.from f) (UMC.from f1) (UMC.from f2)=>
[|f' H]; case=>[|f1' H1]; case=>[|f2' H2] //;
case: ifP=>//; case: ifP=>// D1 D2 _ E.
by apply: fcatsK E; rewrite D1 D2.
Qed.

End Cancelativity.

Module Exports.
Section Exports.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map_class C V).

Definition union_map_classCPCMMix := CPCMMixin (@joinKf K C V U).
Canonical union_map_classCPCM := Eval hnf in CPCM U union_map_classCPCMMix.

End Exports.
End Exports.

End UnionMapClassCPCM.

Export UnionMapClassCPCM.Exports.


(********************)
(* Topped structure *)
(********************)

Module UnionClassTPCM.
Section UnionClassTPCM.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map_class C V).
Implicit Type f : U.

Lemma empbP f : reflect (f = Unit) (empb f).
Proof.
rewrite pcmE /= !umEX /UM.empty /UM.empb -{1}[f]UMC.tfE.
case: (UMC.from f)=>[|f' F]; first by apply: ReflectF; rewrite !umEX.
case: eqP=>E; constructor; rewrite !umEX.
- by move/supp_nilE: E=>->.
by move=>H; rewrite H in E.
Qed.

Lemma valid_undefN : ~~ valid (um_undef: U).
Proof. by rewrite pcmE /= !umEX. Qed.

Lemma undef_join f : um_undef \+ f = um_undef.
Proof. by rewrite pcmE /= !umEX. Qed.

End UnionClassTPCM.

Module Exports.

Definition union_map_classTPCMMix K C V (U : union_map_class C V) :=
  TPCMMixin (@empbP K C V U) (@valid_undefN K C V U) (@undef_join _ _ _ U).
Canonical union_map_classTPCM K C V (U : union_map_class C V) :=
  Eval hnf in TPCM _ (@union_map_classTPCMMix K C V U).
End Exports.
End UnionClassTPCM.

Export UnionClassTPCM.Exports.


(*********************************************************)
(* if V is an equality type, then union_map_class is too *)
(*********************************************************)

Module UnionMapEq.
Section UnionMapEq.
Variables (K : ordType) (C : pred K) (V : eqType).
Variables (T : Type) (m : @UMC.mixin_of K C V T).

Definition unionmap_eq (f1 f2 : UMC T m) :=
  match (UMC.from f1), (UMC.from f2) with
  | UM.Undef, UM.Undef => true
  | UM.Def f1' pf1, UM.Def f2' pf2 => f1' == f2'
  | _, _ => false
  end.

Lemma unionmap_eqP : Equality.axiom unionmap_eq.
Proof.
move=>x y; rewrite -{1}[x]UMC.tfE -{1}[y]UMC.tfE /unionmap_eq.
case: (UMC.from x)=>[|f1 H1]; case: (UMC.from y)=>[|f2 H2] /=.
- by constructor.
- by constructor; move/(@UMC.eqE _ _ _ (UMC T m)).
- by constructor; move/(@UMC.eqE _ _ _ (UMC T m)).
case: eqP=>E; constructor; rewrite (@UMC.eqE _ _ _ (UMC T m)).
- by rewrite UM.umapE.
by case.
Qed.

End UnionMapEq.

Module Exports.
Section Exports.
Variables (K : ordType) (C : pred K) (V : eqType).
Variables (T : Type) (m : @UMC.mixin_of K C V T).

Definition union_map_class_eqMix := EqMixin (@unionmap_eqP K C V T m).

End Exports.
End Exports.

End UnionMapEq.

Export UnionMapEq.Exports.


(*******)
(* dom *)
(*******)

Section DomLemmas.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map_class C V).
Implicit Types (k : K) (v : V) (f g : U).

Lemma dom_undef : dom (undef : U) = [::].
Proof. by rewrite /undef /= !umEX. Qed.

Lemma dom0 : dom (Unit : U) = [::].
Proof. by rewrite pcmE /= !umEX. Qed.

Lemma dom0E f : valid f -> dom f =i pred0 -> f = Unit.
Proof.
rewrite !pcmE /= !umEX /UM.valid /UM.dom /UM.empty -{3}[f]UMC.tfE.
case: (UMC.from f)=>[|f' S] //= _; rewrite !umEX fmapE /= {S}.
by case: f'; case=>[|kv s] //= P /= /(_ kv.1); rewrite inE eq_refl.
Qed.

Lemma domU k v f :
        dom (upd k v f) =i
        [pred x | C k & if x == k then valid f else x \in dom f].
Proof.
rewrite pcmE /= !umEX /UM.dom /UM.upd /UM.valid /=.
case: (UMC.from f)=>[|f' H] /= x.
- by rewrite !inE /= andbC; case: ifP.
case: decP; first by move=>->; rewrite supp_ins.
by move/(introF idP)=>->.
Qed.

Lemma domF k f :
        dom (free f k) =i
        [pred x | if k == x then false else x \in dom f].
Proof.
rewrite !umEX; case: (UMC.from f)=>[|f' H] x; rewrite inE /=;
by case: ifP=>// E; rewrite supp_rem inE /= eq_sym E.
Qed.

Lemma domUn f1 f2 :
        dom (f1 \+ f2) =i
        [pred x | valid (f1 \+ f2) & (x \in dom f1) || (x \in dom f2)].
Proof.
rewrite !pcmE /= !umEX /UM.dom /UM.valid /UM.union.
case: (UMC.from f1) (UMC.from f2)=>[|f1' H1] // [|f2' H2] // x.
by case: ifP=>E //; rewrite supp_fcat.
Qed.

Lemma dom_valid k f : k \in dom f -> valid f.
Proof. by rewrite pcmE /= !umEX; case: (UMC.from f). Qed.

Lemma dom_cond k f : k \in dom f -> C k.
Proof. by rewrite !umEX; case: (UMC.from f)=>[|f' F] // /(allP F). Qed.

Lemma cond_dom k f : ~~ C k -> k \in dom f = false.
Proof. by apply: contraTF=>/dom_cond ->. Qed.

Lemma dom_inIL k f1 f2 :
        valid (f1 \+ f2) -> k \in dom f1 -> k \in dom (f1 \+ f2).
Proof. by rewrite domUn inE => ->->. Qed.

Lemma dom_inIR k f1 f2 :
        valid (f1 \+ f2) -> k \in dom f2 -> k \in dom (f1 \+ f2).
Proof. by rewrite joinC; apply: dom_inIL. Qed.

Lemma dom_NNL k f1 f2 :
        valid (f1 \+ f2) -> k \notin dom (f1 \+ f2) -> k \notin dom f1.
Proof. by move=> D; apply/contra/dom_inIL. Qed.

Lemma dom_NNR k f1 f2 :
        valid (f1 \+ f2) -> k \notin dom (f1 \+ f2) -> k \notin dom f2.
Proof. by move=> D; apply/contra/dom_inIR. Qed.

Lemma dom_free k f : k \notin dom f -> free f k = f.
Proof.
rewrite -{3}[f]UMC.tfE !umEX /UM.dom /UM.free.
by case: (UMC.from f)=>[|f' H] //; apply: rem_supp.
Qed.

Variant dom_find_spec k f : bool -> Type :=
| dom_find_none' : find k f = None -> dom_find_spec k f false
| dom_find_some' v : find k f = Some v ->
    f = upd k v (free f k) -> dom_find_spec k f true.

Lemma dom_find k f : dom_find_spec k f (k \in dom f).
Proof.
rewrite !umEX /UM.dom -{1}[f]UMC.tfE.
case: (UMC.from f)=>[|f' H].
- by apply: dom_find_none'; rewrite !umEX.
case: suppP (allP H k)=>[v|] H1 I; last first.
- by apply: dom_find_none'; rewrite !umEX.
apply: (dom_find_some' (v:=v)); rewrite !umEX // /UM.upd /UM.free.
case: decP=>H2; last by rewrite I in H2.
apply/fmapP=>k'; rewrite fnd_ins.
by case: ifP=>[/eqP-> //|]; rewrite fnd_rem => ->.
Qed.

Lemma find_some k v f : find k f = Some v -> k \in dom f.
Proof. by case: dom_find =>// ->. Qed.

Lemma find_none k f : find k f = None <-> k \notin dom f.
Proof. by case: dom_find=>// v ->. Qed.

Lemma cond_find k f : ~~ C k -> find k f = None.
Proof. by move/(cond_dom f); case: dom_find. Qed.

Lemma dom_prec f1 f2 g1 g2 :
        valid (f1 \+ g1) ->
        f1 \+ g1 = f2 \+ g2 ->
        dom f1 =i dom f2 -> f1 = f2.
Proof.
rewrite -{4}[f1]UMC.tfE -{3}[f2]UMC.tfE !pcmE /= !umEX.
rewrite /UM.valid /UM.union /UM.dom; move=>D E.
case: (UMC.from f1) (UMC.from f2) (UMC.from g1) (UMC.from g2) E D=>
[|f1' F1][|f2' F2][|g1' G1][|g2' G2] //;
case: ifP=>// D1; case: ifP=>// D2 E _ E1; apply/fmapP=>k.
move/(_ k): E1=>E1.
case E2: (k \in supp f2') in E1; last first.
- by move/negbT/fnd_supp: E1=>->; move/negbT/fnd_supp: E2=>->.
suff L: forall m s, k \in supp m -> disj m s ->
          fnd k m = fnd k (fcat m s) :> option V.
- by rewrite (L _ _ E1 D1) (L _ _ E2 D2) E.
by move=>m s S; case: disjP=>//; move/(_ _ S)/negbTE; rewrite fnd_fcat=>->.
Qed.

Lemma domK f1 f2 g1 g2 :
        valid (f1 \+ g1) -> valid (f2 \+ g2) ->
        dom (f1 \+ g1) =i dom (f2 \+ g2) ->
        dom f1 =i dom f2 -> dom g1 =i dom g2.
Proof.
rewrite !pcmE /= !umEX /UM.valid /UM.union /UM.dom.
case: (UMC.from f1) (UMC.from f2) (UMC.from g1) (UMC.from g2)=>
[|f1' F1][|f2' F2][|g1' G1][|g2' G2] //.
case: disjP=>// D1 _; case: disjP=>// D2 _ E1 E2 x.
move: {E1 E2} (E2 x) (E1 x); rewrite !supp_fcat !inE /= => E.
move: {D1 D2} E (D1 x) (D2 x)=><- /implyP D1 /implyP D2.
case _ : (x \in supp f1') => //= in D1 D2 *.
by move/negbTE: D1=>->; move/negbTE: D2=>->.
Qed.

Lemma sorted_dom f : sorted (@ord K) (dom f).
Proof. by rewrite !umEX; case: (UMC.from f)=>[|[]]. Qed.

Lemma sorted_dom_oleq f : sorted (@oleq K) (dom f).
Proof. by apply: sorted_oleq (sorted_dom f). Qed.

Lemma uniq_dom f : uniq (dom f).
Proof.
apply: sorted_uniq (sorted_dom f);
by [apply: ordtype.trans | apply: ordtype.irr].
Qed.

Lemma all_dom f : all C (dom f).
Proof. by rewrite !umEX; case: (UMC.from f). Qed.

Lemma perm_domUn f1 f2 :
        valid (f1 \+ f2) -> perm_eq (dom (f1 \+ f2)) (dom f1 ++ dom f2).
Proof.
move=>Vh; apply: uniq_perm; last 1 first.
- by move=>x; rewrite mem_cat domUn inE Vh.
- by apply: uniq_dom.
rewrite cat_uniq !uniq_dom /= andbT; apply/hasPn=>x.
rewrite !pcmE /= !umEX /UM.valid /UM.union /UM.dom in Vh *.
case: (UMC.from f1) (UMC.from f2) Vh=>// f1' H1 [//|f2' H2].
by case: disjP=>// H _; apply: contraL (H x).
Qed.

Lemma size_domUn f1 f2 :
        valid (f1 \+ f2) ->
        size (dom (f1 \+ f2)) = size (dom f1) + size (dom f2).
Proof. by move/perm_domUn/seq.perm_size; rewrite size_cat. Qed.

Lemma size_domF k f :
        k \in dom f -> size (dom (free f k)) = (size (dom f)).-1.
Proof.
rewrite !umEX; case: (UMC.from f)=>[|f'] //=; case: f'=>f' F /= _.
rewrite /supp /= !size_map size_filter=>H.
move/(sorted_uniq (@trans K) (@irr K))/count_uniq_mem: F=>/(_ k).
rewrite {}H count_map /ssrbool.preim /= => H.
by rewrite -(count_predC [pred x | key x == k]) H addnC addn1.
Qed.

Lemma size_domU k v f :
        valid (upd k v f) ->
        size (dom (upd k v f)) =
        if k \in dom f then size (dom f) else (size (dom f)).+1.
Proof.
rewrite pcmE /= !umEX /UM.valid /UM.upd /UM.dom.
case: (UMC.from f)=>[|f'] //= H; case: decP=>// P _.
by case: f' H=>f' F H; rewrite /supp /= !size_map size_ins'.
Qed.

End DomLemmas.

Hint Resolve sorted_dom uniq_dom all_dom : core.
Prenex Implicits find_some find_none.

(* when we compare doms of two differently-typed maps *)
Lemma domE K C V1 V2 (U1 : @union_map_class K C V1) (U2 : @union_map_class K C V2)
           (f1 : U1) (f2 : U2) :
        dom f1 =i dom f2 <-> dom f1 = dom f2.
Proof.
split=>[|->] //.
apply: (@eq_sorted_irr _ ord);
by [apply: trans|apply: irr|apply: sorted_dom|apply: sorted_dom].
Qed.

(*********)
(* valid *)
(*********)

Section ValidLemmas.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map_class C V).
Implicit Types (k : K) (v : V) (f g : U).

Lemma invalidE f : ~~ valid f <-> f = undef.
Proof.
by rewrite /undef !pcmE /= !umEX -2![f]UMC.tfE !umEX; case: (UMC.from f).
Qed.

Lemma validU k v f : valid (upd k v f) = C k && valid f.
Proof.
rewrite !pcmE /= !umEX /UM.valid /UM.upd.
case: (UMC.from f)=>[|f' F]; first by rewrite andbF.
by case: decP=>[|/(introF idP)] ->.
Qed.

Lemma validF k f : valid (free f k) = valid f.
Proof. by rewrite !pcmE /= !umEX; case: (UMC.from f). Qed.

Variant validUn_spec f1 f2 : bool -> Type :=
| valid_false1 of ~~ valid f1 : validUn_spec f1 f2 false
| valid_false2 of ~~ valid f2 : validUn_spec f1 f2 false
| valid_false3 k of k \in dom f1 & k \in dom f2 : validUn_spec f1 f2 false
| valid_true of valid f1 & valid f2 &
    (forall x, x \in dom f1 -> x \notin dom f2) : validUn_spec f1 f2 true.

Lemma validUn f1 f2 : validUn_spec f1 f2 (valid (f1 \+ f2)).
Proof.
rewrite !pcmE /= !umEX -{1}[f1]UMC.tfE -{1}[f2]UMC.tfE.
rewrite /UM.valid /UM.union /=.
case: (UMC.from f1) (UMC.from f2)=>[|f1' F1][|f2' F2] /=.
- by apply: valid_false1; rewrite pcmE /= !umEX.
- by apply: valid_false1; rewrite pcmE /= !umEX.
- by apply: valid_false2; rewrite pcmE /= !umEX.
case: ifP=>E.
- apply: valid_true; try by rewrite !pcmE /= !umEX.
  by move=>k; rewrite !umEX => H; case: disjP E=>//; move/(_ _ H).
case: disjP E=>// k T1 T2 _.
by apply: (valid_false3 (k:=k)); rewrite !umEX.
Qed.

Lemma validUnAE f1 f2 :
        valid (f1 \+ f2) =
        [&& valid f1, valid f2 & all [predC dom f1] (dom f2)].
Proof.
apply/idP/idP.
- case: validUn=>// ->-> H _; apply/allP=>k.
  by apply: contraL (H _).
case/and3P=>V1 V2 /allP /= D; case: validUn=>//.
- by rewrite V1.
- by rewrite V2.
by move=>k X1 X2; move: (D k X2); rewrite X1.
Qed.

Lemma validUnAEC f1 f2 :
        valid (f1 \+ f2) =
        [&& valid f1, valid f2 & all [predC dom f2] (dom f1)].
Proof. by rewrite validUnAE all_predC_sym. Qed.

Lemma validUnHE f1 f2 :
        valid (f1 \+ f2) =
        [&& valid f1, valid f2 & ~~ has [mem dom f1] (dom f2)].
Proof. by rewrite validUnAE all_predC. Qed.

Lemma validUnHC f1 f2 :
        valid (f1 \+ f2) =
        [&& valid f1, valid f2 & ~~ has [mem dom f2] (dom f1)].
Proof. by rewrite validUnHE has_sym. Qed.

Lemma validFUn k f1 f2 :
        valid (f1 \+ f2) -> valid (free f1 k \+ f2).
Proof.
case: validUn=>// V1 V2 H _; case: validUn=>//; last 1 first.
- by move=>k'; rewrite domF inE; case: eqP=>// _ /H/negbTE ->.
by rewrite validF V1.
by rewrite V2.
Qed.

Lemma validUnF k f1 f2 :
        valid (f1 \+ f2) -> valid (f1 \+ free f2 k).
Proof. by rewrite !(joinC f1); apply: validFUn. Qed.

Lemma validUnU k v f1 f2 :
        k \in dom f2 -> valid (f1 \+ upd k v f2) = valid (f1 \+ f2).
Proof.
move=>D; apply/esym; move: D; case: validUn.
- by move=>V' _; apply/esym/negbTE; apply: contra V'; move/validL.
- move=>V' _; apply/esym/negbTE; apply: contra V'; move/validR.
  by rewrite validU; case/andP.
- move=>k' H1 H2 _; case: validUn=>//; rewrite validU => D1 /andP [/= H D2].
  by move/(_ k' H1); rewrite domU !inE H D2 H2; case: ifP.
move=>V1 V2 H1 H2; case: validUn=>//.
- by rewrite V1.
- by rewrite validU V2 (dom_cond H2).
move=>k'; rewrite domU (dom_cond H2) inE /= V2; move/H1=>H3.
by rewrite (negbTE H3); case: ifP H2 H3=>// /eqP ->->.
Qed.

Lemma validUUn k v f1 f2 :
        k \in dom f1 -> valid (upd k v f1 \+ f2) = valid (f1 \+ f2).
Proof. by move=>D; rewrite -!(joinC f2); apply: validUnU D. Qed.

Lemma dom_inNL k f1 f2 :
        valid (f1 \+ f2) -> k \in dom f1 -> k \notin dom f2.
Proof. by case: validUn=>//_ _ H _; apply: H. Qed.

Lemma dom_inNR k f1 f2 :
        valid (f1 \+ f2) -> k \in dom f2 -> k \notin dom f1.
Proof. by rewrite joinC; apply: dom_inNL. Qed.

End ValidLemmas.


(************)
(* um_unitb *)
(************)

(* AKA empb *)

Section UnitbLemmas.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map_class C V).
Implicit Types (k : K) (v : V) (f : U).

Lemma um_unitbU k v f : unitb (upd k v f) = false.
Proof.
rewrite /unitb /= !umEX /UM.empb /UM.upd.
case: (UMC.from f)=>[|f' F] //; case: decP=>// H.
suff: k \in supp (ins k v f') by case: (supp _).
by rewrite supp_ins inE /= eq_refl.
Qed.

Lemma um_unitbUn f1 f2 : unitb (f1 \+ f2) = unitb f1 && unitb f2.
Proof.
rewrite /unitb !pcmE /= !umEX /UM.empb /UM.union.
case: (UMC.from f1) (UMC.from f2)=>[|f1' F1][|f2' F2] //.
- by rewrite andbF.
case: ifP=>E; case: eqP=>E1; case: eqP=>E2 //; last 2 first.
- by move: E2 E1; move/supp_nilE=>->; rewrite fcat0s; case: eqP.
- by move: E1 E2 E; do 2![move/supp_nilE=>->]; case: disjP.
- by move/supp_nilE: E2 E1=>-> <-; rewrite fcat0s eq_refl.
have [k H3]: exists k, k \in supp f1'.
- case: (supp f1') {E1 E} E2=>[|x s _] //.
  by exists x; rewrite inE eq_refl.
suff: k \in supp (fcat f1' f2') by rewrite E1.
by rewrite supp_fcat inE /= H3.
Qed.

(* some transformation lemmas *)

(* AKA conicity *)
Lemma join0E f1 f2 : f1 \+ f2 = Unit <-> f1 = Unit /\ f2 = Unit.
Proof. by rewrite !unitbE um_unitbUn; case: andP. Qed.

Lemma validEb f : reflect (valid f /\ forall k, k \notin dom f) (unitb f).
Proof.
case: unitbP=>E; constructor; first by rewrite E valid_unit dom0.
case=>V' H; apply: E; move: V' H.
rewrite !pcmE /= !umEX /UM.valid /UM.dom /UM.empty -{3}[f]UMC.tfE.
case: (UMC.from f)=>[|f' F] // _ H; rewrite !umEX.
apply/supp_nilE; case: (supp f') H=>// x s /(_ x).
by rewrite inE eq_refl.
Qed.

Lemma validUnEb f : valid (f \+ f) = unitb f.
Proof.
case E: (unitb f); first by move/unitbE: E=>->; rewrite unitL valid_unit.
case: validUn=>// V' _ L; case: validEb E=>//; case; split=>// k.
by case E: (k \in dom f)=>//; move: (L k E); rewrite E.
Qed.

End UnitbLemmas.


(**********)
(* undefb *)
(**********)

Section UndefbLemmas.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map_class C V).
Implicit Types (k : K) (v : V) (f : U).

Lemma undefb_undef : undefb (undef : U).
Proof. by rewrite /undef /= !umEX. Qed.

Lemma undefbP f : reflect (f = undef) (undefb f).
Proof.
rewrite /undef /= !umEX /UM.undefb -{1}[f]UMC.tfE.
by case: (UMC.from f)=>[|f' F]; constructor; rewrite !umEX.
Qed.

Lemma undefbE f : f = undef <-> undefb f.
Proof. by case: undefbP. Qed.

End UndefbLemmas.


(**********)
(* dom_eq *)
(**********)

Section DomEqLemmas.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map_class C V).
Implicit Type f : U.

Lemma domeqP f1 f2 :
        reflect (valid f1 = valid f2 /\ dom f1 =i dom f2) (dom_eq f1 f2).
Proof.
rewrite !pcmE /= !umEX /UM.valid /UM.dom /UM.dom_eq /in_mem.
case: (UMC.from f1) (UMC.from f2)=>[|f1' F1][|f2' F2] /=.
- by constructor.
- by constructor; case.
- by constructor; case.
by case: eqP=>H; constructor; [rewrite H | case=>_ /suppE].
Qed.

Lemma domeq0E f : dom_eq f Unit -> f = Unit.
Proof. by case/domeqP; rewrite valid_unit dom0; apply: dom0E. Qed.

Lemma domeq_refl f : dom_eq f f.
Proof. by case: domeqP=>//; case. Qed.

Hint Resolve domeq_refl : core.

Lemma domeq_sym f1 f2 : dom_eq f1 f2 = dom_eq f2 f1.
Proof.
suff L f f' : dom_eq f f' -> dom_eq f' f by apply/idP/idP; apply: L.
by case/domeqP=>H1 H2; apply/domeqP; split.
Qed.

Lemma domeq_trans f1 f2 f3 :
        dom_eq f1 f2 -> dom_eq f2 f3 -> dom_eq f1 f3.
Proof.
case/domeqP=>E1 H1 /domeqP [E2 H2]; apply/domeqP=>//.
by split=>//; [rewrite E1 E2 | move=>x; rewrite H1 H2].
Qed.

Lemma domeqVUnE f1 f2 f1' f2' :
        dom_eq f1 f2 -> dom_eq f1' f2' ->
        valid (f1 \+ f1') = valid (f2 \+ f2').
Proof.
have L f f' g : dom_eq f f' -> valid (f \+ g) -> valid (f' \+ g).
- case/domeqP=>E F; case: validUn=>// Vg1 Vf H _; case: validUn=>//.
  - by rewrite -E Vg1.
  - by rewrite Vf.
  by move=>x; rewrite -F; move/H/negbTE=>->.
move=>H H'; case X: (valid (f1 \+ f1')); apply/esym.
- by move/(L _ _ _ H): X; rewrite !(joinC f2); move/(L _ _ _ H').
rewrite domeq_sym in H; rewrite domeq_sym in H'.
apply/negbTE; apply: contra (negbT X); move/(L _ _ _ H).
by rewrite !(joinC f1); move/(L _ _ _ H').
Qed.

Lemma domeqVUn f1 f2 f1' f2' :
        dom_eq f1 f2 -> dom_eq f1' f2' ->
        valid (f1 \+ f1') -> valid (f2 \+ f2').
Proof. by move=>D /(domeqVUnE D) ->. Qed.

Lemma domeqUn f1 f2 f1' f2' :
        dom_eq f1 f2 -> dom_eq f1' f2' ->
        dom_eq (f1 \+ f1') (f2 \+ f2').
Proof.
suff L f f' g : dom_eq f f' -> dom_eq (f \+ g) (f' \+ g).
- move=>H H'; apply: domeq_trans (L _ _ _ H).
  by rewrite !(joinC f1); apply: domeq_trans (L _ _ _ H').
move=>F; case/domeqP: (F)=>E H.
apply/domeqP; split; first by apply: domeqVUnE F _.
move=>x; rewrite !domUn /= inE.
by rewrite (domeqVUnE F (domeq_refl g)) H.
Qed.

Lemma domeqfUn f f1 f2 f1' f2' :
        dom_eq (f \+ f1) f2 -> dom_eq f1' (f \+ f2') ->
        dom_eq (f1 \+ f1') (f2 \+ f2').
Proof.
move=>D1 D2; apply: (domeq_trans (f2:=f1 \+ f \+ f2')).
- by rewrite -joinA; apply: domeqUn.
by rewrite -joinA joinCA joinA; apply: domeqUn.
Qed.

Lemma domeqUnf f f1 f2 f1' f2' :
        dom_eq f1 (f \+ f2) -> dom_eq (f \+ f1') f2' ->
        dom_eq (f1 \+ f1') (f2 \+ f2').
Proof.
by move=>D1 D2; rewrite (joinC f1) (joinC f2); apply: domeqfUn D2 D1.
Qed.

Lemma domeqK f1 f2 f1' f2' :
        valid (f1 \+ f1') ->
        dom_eq (f1 \+ f1') (f2 \+ f2') ->
        dom_eq f1 f2 -> dom_eq f1' f2'.
Proof.
move=>V1 /domeqP [E1 H1] /domeqP [E2 H2]; move: (V1); rewrite E1=>V2.
apply/domeqP; split; first by rewrite (validE2 V1) (validE2 V2).
by apply: domK V1 V2 H1 H2.
Qed.

Lemma domeqfU k v f : k \in dom f -> dom_eq f (upd k v f).
Proof.
move=>D; apply/domeqP; rewrite validU (dom_cond D) (dom_valid D).
by split=>// x; rewrite domU inE (dom_cond D) (dom_valid D); case: eqP=>// ->.
Qed.

Lemma domeqUf k v f : k \in dom f -> dom_eq (upd k v f) f.
Proof. by rewrite domeq_sym; apply: domeqfU. Qed.

End DomEqLemmas.

Hint Resolve domeq_refl : core.


(***********)
(* dom_eq2 *)
(***********)

(* for maps of different types *)

Section DomEq2Def.
Variable (K : ordType) (C : pred K) (V1 V2 : Type).
Variable U1 : union_map_class C V1.
Variable U2 : union_map_class C V2.

Definition dom_eq2 (f1 : U1) (f2 : U2) :=
  (valid f1 == valid f2) && (dom f1 == dom f2).

End DomEq2Def.

Section DomEq2Lemmas.
Variable (K : ordType) (C : pred K) (V1 V2 V3 : Type).
Variable U1 : union_map_class C V1.
Variable U2 : union_map_class C V2.
Variable U3 : union_map_class C V3.

Lemma domeq2_undef : dom_eq2 (undef : U1) (undef : U2).
Proof. by rewrite /dom_eq2 !valid_undef !dom_undef. Qed.

Lemma domeq2P (f1 : U1) (f2 : U2) :
        reflect (valid f1 = valid f2 /\ dom f1 = dom f2) (dom_eq2 f1 f2).
Proof.
case E: (dom_eq2 f1 f2); constructor; first by case/andP: E=>/eqP -> /eqP ->.
by case=>V D; move/negbT/negP: E; apply; rewrite /dom_eq2 V D !eq_refl.
Qed.

Lemma domeq2_refl (f : U1) : dom_eq2 f f.
Proof. by rewrite /dom_eq2 !eq_refl. Qed.

Lemma domeq2_sym (f1 : U1) (f2 : U2) : dom_eq2 f1 f2 -> dom_eq2 f2 f1.
Proof. by case/andP=>V D; apply/andP; rewrite (eqP V) (eqP D). Qed.

Lemma domeq2_trans (f1 : U1) (f2 : U2) (f3 : U3) :
        dom_eq2 f1 f2 -> dom_eq2 f2 f3 -> dom_eq2 f1 f3.
Proof. by rewrite /dom_eq2=>/andP [/eqP -> /eqP ->]. Qed.

Lemma domeq2VUnE (f1 f1' : U1) (f2 f2' : U2) :
        dom_eq2 f1 f2 -> dom_eq2 f1' f2' ->
        valid (f1 \+ f1') = valid (f2 \+ f2').
Proof.
suff L V1' V2' (U1' : union_map_class C V1')
  (U2' : union_map_class C V2') (g1 g1' :  U1') (g2 g2' : U2') :
  dom_eq2 g1 g2 -> dom_eq2 g1' g2' ->
  valid (g1 \+ g1') -> valid (g2 \+ g2').
- by move=>D D'; apply/idP/idP; apply: L=>//; apply: domeq2_sym.
case/andP=>/eqP E /eqP D /andP [/eqP E' /eqP D']; case: validUn=>// V V' G _.
case: validUn=>//; rewrite -?E ?V -?E' ?V' //.
by move=>k; rewrite -D -D'=>/G/negbTE ->.
Qed.

Lemma domeq2VUn (f1 f1' : U1) (f2 f2' : U2) :
        dom_eq2 f1 f2 -> dom_eq2 f1' f2' ->
        valid (f1 \+ f1') -> valid (f2 \+ f2').
Proof. by move=>D D'; rewrite -(domeq2VUnE D D'). Qed.

Lemma domeq2Un (f1 f1' : U1) (f2 f2' : U2) :
        dom_eq2 f1 f2 -> dom_eq2 f1' f2' ->
        dom_eq2 (f1 \+ f1') (f2 \+ f2').
Proof.
move=>D D'; case/andP: (D)=>V E; case/andP: (D')=>V' E'.
apply/andP; rewrite (domeq2VUnE D D') eq_refl; split=>//.
apply/eqP; apply: eq_sorted_ord; try by apply: sorted_dom.
by move=>k; rewrite !domUn !inE (domeq2VUnE D D') (eqP E) (eqP E').
Qed.

End DomEq2Lemmas.

Hint Resolve domeq2_refl : core.


(**********)
(* update *)
(**********)

Section UpdateLemmas.
Variable (K : ordType) (C : pred K) (V : Type) (U : union_map_class C V).
Implicit Types (k : K) (v : V) (f : U).

Lemma upd_undef k v : upd k v undef = undef :> U.
Proof. by rewrite /undef /= !umEX. Qed.

Lemma upd_condN k v f : ~~ C k -> upd k v f = undef.
Proof.
rewrite /undef /= !umEX /UM.upd.
case: (UMC.from f)=>[|f' H']=>//.
by case: decP=>//= ->.
Qed.

Lemma upd_inj k v1 v2 f :
        valid f -> C k -> upd k v1 f = upd k v2 f -> v1 = v2.
Proof.
rewrite !pcmE /= !umEX /UM.valid /UM.upd.
case: (UMC.from f)=>[|f' F] // _; case: decP=>// H _ E.
have: fnd k (ins k v1 f') = fnd k (ins k v2 f') by rewrite E.
by rewrite !fnd_ins eq_refl; case.
Qed.

Lemma updU k1 k2 v1 v2 f :
        upd k1 v1 (upd k2 v2 f) =
        if k1 == k2 then upd k1 v1 f else upd k2 v2 (upd k1 v1 f).
Proof.
rewrite !umEX /UM.upd.
case: (UMC.from f)=>[|f' H']; case: ifP=>// E;
case: decP=>H1; case: decP=>H2 //; rewrite !umEX.
- by rewrite ins_ins E.
- by rewrite (eqP E) in H2 *.
by rewrite ins_ins E.
Qed.

Lemma updF k1 k2 v f :
        upd k1 v (free f k2) =
        if k1 == k2 then upd k1 v f else free (upd k1 v f) k2.
Proof.
rewrite !umEX /UM.dom /UM.upd /UM.free.
case: (UMC.from f)=>[|f' F] //; case: ifP=>// H1;
by case: decP=>H2 //; rewrite !umEX ins_rem H1.
Qed.

Lemma updUnL k v f1 f2 :
        upd k v (f1 \+ f2) =
        if k \in dom f1 then upd k v f1 \+ f2 else f1 \+ upd k v f2.
Proof.
rewrite !pcmE /= !umEX /UM.upd /UM.union /UM.dom.
case: (UMC.from f1) (UMC.from f2)=>[|f1' F1][|f2' F2] //=.
- by case: ifP=>//; case: decP.
case: ifP=>// D; case: ifP=>// H1; case: decP=>// H2.
- rewrite disjC disj_ins disjC D !umEX; case: disjP D=>// H _.
  by rewrite (H _ H1) /= fcat_inss // (H _ H1).
- by rewrite disj_ins H1 D /= !umEX fcat_sins.
- by rewrite disjC disj_ins disjC D andbF.
by rewrite disj_ins D andbF.
Qed.

Lemma updUnR k v f1 f2 :
        upd k v (f1 \+ f2) =
        if k \in dom f2 then f1 \+ upd k v f2 else upd k v f1 \+ f2.
Proof. by rewrite joinC updUnL (joinC f1) (joinC f2). Qed.

Lemma updL k v f1 f2 :
        k \in dom f1 -> upd k v (f1 \+ f2) = upd k v f1 \+ f2.
Proof. by move=>D; rewrite updUnL D. Qed.

Lemma updR k v f1 f2 :
        k \in dom f2 -> upd k v (f1 \+ f2) = f1 \+ upd k v f2.
Proof. by move=>D; rewrite updUnR D. Qed.

End UpdateLemmas.


(********)
(* free *)
(********)

Section FreeLemmas.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map_class C V).
Implicit Types (k : K) (v : V) (f : U).

Lemma free0 k : free Unit k = Unit :> U.
Proof. by rewrite !pcmE /= !umEX /UM.free /UM.empty rem_empty. Qed.

Lemma free_undef k : free undef k = undef :> U.
Proof. by rewrite /undef /= !umEX. Qed.

Lemma freeU k1 k2 v f :
        free (upd k2 v f) k1 =
        if k1 == k2 then
          if C k2 then free f k1 else undef
        else upd k2 v (free f k1).
Proof.
rewrite /undef /= !umEX /UM.free /UM.upd.
case: (UMC.from f)=>[|f' F]; first by case: ifP=>H1 //; case: ifP.
case: ifP=>H1; case: decP=>H2 //=.
- by rewrite H2 !umEX rem_ins H1.
- by case: ifP H2.
by rewrite !umEX rem_ins H1.
Qed.

Lemma freeF k1 k2 f :
        free (free f k2) k1 =
        if k1 == k2 then free f k1 else free (free f k1) k2.
Proof.
rewrite !umEX /UM.free.
by case: (UMC.from f)=>[|f' F]; case: ifP=>// E; rewrite !umEX rem_rem E.
Qed.

Lemma freeUn k f1 f2 :
        free (f1 \+ f2) k =
        if k \in dom (f1 \+ f2) then free f1 k \+ free f2 k
        else f1 \+ f2.
Proof.
rewrite !pcmE /= !umEX /UM.free /UM.union /UM.dom.
case: (UMC.from f1) (UMC.from f2)=>[|f1' F1][|f2' F2] //.
case: ifP=>// E1; rewrite supp_fcat inE /=.
case: ifP=>E2; last by rewrite !umEX rem_supp // supp_fcat inE E2.
rewrite disj_rem; last by rewrite disjC disj_rem // disjC.
rewrite !umEX; case/orP: E2=>E2.
- suff E3: k \notin supp f2' by rewrite -fcat_rems // (rem_supp E3).
  by case: disjP E1 E2=>// H _; move/H.
suff E3: k \notin supp f1' by rewrite -fcat_srem // (rem_supp E3).
by case: disjP E1 E2=>// H _; move/contra: (H k); rewrite negbK.
Qed.

Lemma freeUnV k f1 f2 :
        valid (f1 \+ f2) -> free (f1 \+ f2) k = free f1 k \+ free f2 k.
Proof.
move=>V'; rewrite freeUn domUn V' /=; case: ifP=>//.
by move/negbT; rewrite negb_or; case/andP=>H1 H2; rewrite !dom_free.
Qed.

Lemma freeUnL k f1 f2 : k \notin dom f1 -> free (f1 \+ f2) k = f1 \+ free f2 k.
Proof.
move=>V1; rewrite freeUn domUn inE (negbTE V1) /=.
case: ifP; first by case/andP; rewrite dom_free.
move/negbT; rewrite negb_and; case/orP=>V2; last by rewrite dom_free.
suff: ~~ valid (f1 \+ free f2 k) by move/invalidE: V2=>-> /invalidE ->.
apply: contra V2; case: validUn=>// H1 H2 H _.
case: validUn=>//; first by rewrite H1.
- by move: H2; rewrite validF => ->.
move=>x H3; move: (H _ H3); rewrite domF inE /=.
by case: ifP H3 V1=>[|_ _ _]; [move/eqP=><- -> | move/negbTE=>->].
Qed.

Lemma freeUnR k f1 f2 : k \notin dom f2 -> free (f1 \+ f2) k = free f1 k \+ f2.
Proof. by move=>H; rewrite joinC freeUnL // joinC. Qed.

Lemma freeND k f : k \notin dom f -> free f k = f.
Proof. by move=>W; rewrite -[f]unitR freeUnL // free0. Qed.

Lemma freeL k f1 f2 :
        valid (f1 \+ f2) -> k \in dom f1 -> free (f1 \+ f2) k = free f1 k \+ f2.
Proof. by move=>W /(dom_inNL W) D; rewrite freeUnR. Qed.

Lemma freeR k f1 f2 :
        valid (f1 \+ f2) -> k \in dom f2 -> free (f1 \+ f2) k = f1 \+ free f2 k.
Proof. by rewrite !(joinC f1); apply: freeL. Qed.

End FreeLemmas.


(********)
(* find *)
(********)

Section FindLemmas.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map_class C V).
Implicit Types (k : K) (v : V) (f : U).

Lemma find0E k : find k (Unit : U) = None.
Proof. by rewrite pcmE /= !umEX /UM.find /= fnd_empty. Qed.

Lemma find_undef k : find k (undef : U) = None.
Proof. by rewrite /undef /= !umEX /UM.find. Qed.

Lemma find_cond k f : ~~ C k -> find k f = None.
Proof.
simpl.
rewrite !umEX /UM.find; case: (UMC.from f)=>[|f' F] // H.
suff: k \notin supp f' by case: suppP.
by apply: contra H; case: allP F=>// F _ /F.
Qed.

Lemma findU k1 k2 v f :
        find k1 (upd k2 v f) =
        if k1 == k2 then
          if C k2 && valid f then Some v else None
        else if C k2 then find k1 f else None.
Proof.
rewrite pcmE /= !umEX /UM.valid /UM.find /UM.upd.
case: (UMC.from f)=>[|f' F]; first by rewrite andbF !if_same.
case: decP=>H; first by rewrite H /= fnd_ins.
by rewrite (introF idP H) /= if_same.
Qed.

Lemma findF k1 k2 f :
        find k1 (free f k2) = if k1 == k2 then None else find k1 f.
Proof.
rewrite !umEX /UM.find /UM.free.
case: (UMC.from f)=>[|f' F]; first by rewrite if_same.
by rewrite fnd_rem.
Qed.

Lemma findUnL k f1 f2 :
        valid (f1 \+ f2) ->
        find k (f1 \+ f2) = if k \in dom f1 then find k f1 else find k f2.
Proof.
rewrite !pcmE /= !umEX /UM.valid /UM.find /UM.union /UM.dom.
case: (UMC.from f1) (UMC.from f2)=>[|f1' F1][|f2' F2] //.
case: ifP=>// D _; case: ifP=>E1; last first.
- rewrite fnd_fcat; case: ifP=>// E2.
  by rewrite fnd_supp ?E1 // fnd_supp ?E2.
suff E2: k \notin supp f2' by rewrite fnd_fcat (negbTE E2).
by case: disjP D E1=>// H _; apply: H.
Qed.

Lemma findUnR k f1 f2 :
        valid (f1 \+ f2) ->
        find k (f1 \+ f2) = if k \in dom f2 then find k f2 else find k f1.
Proof. by rewrite joinC=>D; rewrite findUnL. Qed.

Lemma find_eta f1 f2 :
        valid f1 -> valid f2 ->
        (forall k, find k f1 = find k f2) -> f1 = f2.
Proof.
rewrite !pcmE /= !umEX /UM.valid /UM.find -{2 3}[f1]UMC.tfE -{2 3}[f2]UMC.tfE.
case: (UMC.from f1) (UMC.from f2)=>[|f1' F1][|f2' F2] // _ _ H.
by rewrite !umEX; apply/fmapP=>k; move: (H k); rewrite !umEX.
Qed.

End FindLemmas.

(* if maps store units, i.e., we keep them just for sets *)
(* then we can simplify the find_eta lemma a bit *)

Lemma domeq_eta (K : ordType) (C : pred K) (U : union_map_class C unit) (f1 f2 : U) :
        dom_eq f1 f2 -> f1 = f2.
Proof.
case/domeqP=>V E; case V1 : (valid f1); last first.
- by move: V1 (V1); rewrite {1}V; do 2![move/negbT/invalidE=>->].
apply: find_eta=>//; first by rewrite -V.
move=>k; case D : (k \in dom f1); move: D (D); rewrite {1}E.
- by do 2![case: dom_find=>// [[-> _]]].
by do 2![case: dom_find=>// ->].
Qed.



(**********)
(* assocs *)
(**********)

Section AssocsLemmas.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map_class C V).
Implicit Type f : U.

Lemma assocs_valid k f : k \In assocs f -> valid f.
Proof. by rewrite !pcmE /= !umEX; case: (UMC.from f). Qed.

Lemma assocs0 : assocs (Unit : U) = [::].
Proof. by rewrite pcmE /= !umEX. Qed.

Lemma assocs_undef : assocs (undef : U) = [::].
Proof. by rewrite /undef /= !umEX. Qed.

Lemma assocsPt k v :
        assocs (pts k v : U) =
        if C k then [:: (k, v)] else [::].
Proof.
rewrite !umEX /UM.assocs/UM.pts /=.
by case E: decP=>[a|a] /=; [rewrite a | case: ifP].
Qed.

Lemma assocsUnPt f k v :
        valid (f \+ pts k v) -> all (ord^~ k) (dom f) ->
        assocs (f \+ pts k v) = rcons (assocs f) (k, v).
Proof.
rewrite !pcmE /= !umEX /UM.assocs/UM.union/UM.pts/UM.dom/supp /=.
case: (UMC.from f)=>//=; case: decP=>//= H1 g H2; case: ifP=>//= _ _.
by case: allP=>//; case: g H2=>// s1 H2 H3 H4 _; apply: first_ins' H4.
Qed.

Lemma assocsPtUn f k v :
        valid (pts k v \+ f) -> all (ord k) (dom f) ->
        assocs (pts k v \+ f) = (k, v) :: (assocs f).
Proof.
rewrite !pcmE /= !umEX /UM.assocs/UM.union/UM.pts/UM.dom/supp /=.
case: decP=>// H1; case: (UMC.from f)=>//= g H2.
rewrite /disj /= andbT; case: ifP=>//= D _ H3.
rewrite (fcat_inss _ (@nil K V) D) fcat0s.
case: g H2 D H3=>//= g P H2 D H3.
by apply: last_ins'; rewrite path_min_sorted //.
Qed.

Lemma assocs_perm f1 f2 :
        valid (f1 \+ f2) -> perm (assocs (f1 \+ f2)) (assocs f1 ++ assocs f2).
Proof.
rewrite !pcmE /= !umEX /UM.assocs/UM.union/UM.pts/UM.dom/supp /=.
case: (UMC.from f1)=>//= g1 H1; case: (UMC.from f2)=>//= g2 H2.
by case: ifP=>// D _; apply: seqof_fcat_perm D.
Qed.

Lemma assocs_dom f : dom f = map fst (assocs f).
Proof. by rewrite !umEX; case: (UMC.from f). Qed.

Lemma size_assocs f : size (assocs f) = size (dom f).
Proof. by rewrite assocs_dom size_map. Qed.

End AssocsLemmas.

Lemma uniq_assocs K C (V : eqType) (U : @union_map_class K C V) (f : U) :
        uniq (assocs f).
Proof.
rewrite !umEX /UM.assocs /=; case: (UMC.from f)=>[|[s H _]] //=.
by move/(sorted_uniq (@trans K) (@irr K)): H; apply: map_uniq.
Qed.

Lemma assocs_map K C (V : Type) (U : @union_map_class K C V) (f : U) k v1 v2 :
        (k, v1) \In assocs f -> (k, v2) \In assocs f -> v1 = v2.
Proof.
rewrite !umEX; case: (UMC.from f)=>//= g _; case: g=>g S /= H1 H2.
have {S} S' : uniq [seq key i | i <- g].
- by apply: sorted_uniq S; [apply: trans | apply: irr].
have X : forall (g : seq (K*V)) k v, (k, v) \In g -> k \in map fst g.
- elim=>[|[ka va] h IH] // kb vb.
  - rewrite !InE; case; first by case=>-> _; rewrite inE eq_refl.
  by move/IH; rewrite inE=>->; rewrite orbT.
elim: g k v1 v2 S' H1 H2=>[|[ka va] g IH] //= k v1 v2.
case/andP=>U1 U2; rewrite !InE.
case; first by case=>->->; case=>[[]|/X] //; rewrite (negbTE U1).
move=>H1 H2; case: H2 H1.
- by case=>->-> /X; rewrite (negbTE U1).
by move=>H1 H2; apply: IH H2 H1.
Qed.

(*********************************)
(* Interaction of subset and dom *)
(*********************************)

Section Interaction.
Variables (K : ordType) (C : pred K) (A : Type) (U : union_map_class C A).
Implicit Types (x y a b : U) (p q : pred K).

(* Some equivalent forms for subset with dom *)

Lemma subdom_indomE p x : {subset dom x <= p} = {in dom x, p =1 predT}.
Proof. by []. Qed.

(* Some equivalent forms for subset expressing disjointness *)

Lemma subset_disjE p q : {subset p <= predC q} <-> [predI p & q] =1 pred0.
Proof.
split=>H a /=; first by case X: (a \in p)=>//; move/H/negbTE: X.
by move=>D; move: (H a); rewrite inE /= D; move/negbT.
Qed.

Lemma subset_disjC p q : {subset p <= predC q} <-> {subset q <= predC p}.
Proof. by split=>H a; apply: contraL (H a). Qed.

Lemma valid_subdom x y : valid (x \+ y) -> {subset dom x <= [predC dom y]}.
Proof. by case: validUn. Qed.

Lemma subdom_valid x y :
        {subset dom x <= [predC dom y]} ->
        valid x -> valid y -> valid (x \+ y).
Proof. by move=>H X Y; case: validUn; rewrite ?X ?Y=>// k /H /negbTE /= ->. Qed.

Lemma subdom_validL x y a :
        valid a ->
        valid (x \+ y) -> {subset dom a <= dom x} -> valid (a \+ y).
Proof.
rewrite !validUnAE=>-> /and3P [_ -> D] S.
by apply: sub_all D=>z /(contra (S z)).
Qed.

End Interaction.


(****************************)
(* Generic points-to lemmas *)
(****************************)

(* Instances of union_maps have different definition of points-to, so
they need separate intances of each of following lemmas. I give the
lemmas complicated names prefixed by gen, because they are not
supposed to be used in applications *)

Section PointsToLemmas.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map_class C V).
Implicit Types (k : K) (v : V) (f : U).

Lemma ptsU k v : pts k v = upd k v Unit :> U.
Proof. by rewrite !pcmE /= !umEX /UM.pts /UM.upd; case: decP. Qed.

Lemma pts_condN k v : ~~ C k -> pts k v = undef :> U.
Proof. by move=>C'; rewrite ptsU upd_condN. Qed.

Lemma domPtK k v : dom (pts k v : U) = if C k then [:: k] else [::].
Proof.
rewrite !umEX /= /UM.dom /supp /UM.pts /UM.upd /UM.empty /=.
by case D : (decP _)=>[a|a] /=; rewrite ?a ?(introF idP a).
Qed.

(* a weaker legacy version of gen_domPtK *)
Lemma domPt k v : dom (pts k v : U) =i [pred x | C k & k == x].
Proof.
by move=>x; rewrite ptsU domU !inE eq_sym valid_unit dom0; case: eqP.
Qed.

Lemma validPt k v : valid (pts k v : U) = C k.
Proof. by rewrite ptsU validU valid_unit andbT. Qed.

Lemma domeqPt k v1 v2 : dom_eq (pts k v1 : U) (pts k v2).
Proof. by apply/domeqP; rewrite !validPt; split=>// x; rewrite !domPt. Qed.

Lemma findPt k v : find k (pts k v : U) = if C k then Some v else None.
Proof. by rewrite ptsU findU eq_refl /= valid_unit andbT. Qed.

Lemma findPt2 k1 k2 v :
        find k1 (pts k2 v : U) =
        if (k1 == k2) && C k2 then Some v else None.
Proof.
by rewrite ptsU findU valid_unit andbT find0E; case: ifP=>//=; case: ifP.
Qed.

Lemma findPt_inv k1 k2 v w :
        find k1 (pts k2 v : U) = Some w -> [/\ k1 = k2, v = w & C k2].
Proof.
rewrite ptsU findU; case: eqP; last by case: ifP=>//; rewrite find0E.
by move=>->; rewrite valid_unit andbT; case: ifP=>// _ [->].
Qed.

Lemma freePt2 k1 k2 v :
        C k2 ->
        free (pts k2 v : U) k1 = if k1 == k2 then Unit else pts k2 v.
Proof. by move=>N; rewrite ptsU freeU free0 N. Qed.

Lemma freePt k v :
        C k -> free (pts k v : U) k = Unit.
Proof. by move=>N; rewrite freePt2 // eq_refl. Qed.

Lemma cancelPt k v1 v2 :
        valid (pts k v1 : U) -> pts k v1 = pts k v2 :> U -> v1 = v2.
Proof. by rewrite validPt !ptsU; apply: upd_inj. Qed.

Lemma cancelPt2 k1 k2 v1 v2 :
        valid (pts k1 v1 : U) ->
        pts k1 v1 = pts k2 v2 :> U -> (k1, v1) = (k2, v2).
Proof.
move=>H E; have : dom (pts k1 v1 : U) = dom (pts k2 v2 : U) by rewrite E.
rewrite !domPtK -(validPt _ v1) -(validPt _ v2) -E H.
by case=>E'; rewrite -{k2}E' in E *; rewrite (cancelPt H E).
Qed.

Lemma updPt k v1 v2 : upd k v1 (pts k v2) = pts k v1 :> U.
Proof. by rewrite !ptsU updU eq_refl. Qed.

Lemma um_unitbPt k v : unitb (pts k v : U) = false.
Proof. by rewrite ptsU um_unitbU. Qed.

(* valid *)

Lemma validPtUn k v f :
        valid (pts k v \+ f) = [&& C k, valid f & k \notin dom f].
Proof.
case: validUn=>//; last 1 first.
- rewrite validPt=>H1 -> H2; rewrite H1 (H2 k) //.
  by rewrite domPtK H1 inE.
- by rewrite validPt; move/negbTE=>->.
- by move/negbTE=>->; rewrite andbF.
rewrite domPtK=>x; case: ifP=>// _.
by rewrite inE=>/eqP ->->; rewrite andbF.
Qed.

Lemma validUnPt k v f :
        valid (f \+ pts k v) = [&& C k, valid f & k \notin dom f].
Proof. by rewrite joinC; apply: validPtUn. Qed.

Lemma validPtUnE v2 v1 k f : valid (pts k v1 \+ f) = valid (pts k v2 \+ f).
Proof. by rewrite !validPtUn. Qed.

Lemma validUnPtE v2 v1 k f : valid (f \+ pts k v1) = valid (f \+ pts k v2).
Proof. by rewrite !validUnPt. Qed.

Lemma validPtPt v1 v2 k : valid (pts k v1 \+ pts k v2 : U) = false.
Proof. by rewrite (validPtUnE v2) validUnEb um_unitbPt. Qed.

(* the projections from validPtUn are often useful *)

Lemma validPtUnI v1 k f :
        valid (pts k v1 \+ f) -> [&& C k, valid f & k \notin dom f].
Proof. by rewrite validPtUn. Qed.

Lemma validUnPtI v1 k f :
        valid (f \+ pts k v1) -> [&& C k, valid f & k \notin dom f].
Proof. by rewrite validUnPt. Qed.

Lemma validPtUn_cond k v f : valid (pts k v \+ f) -> C k.
Proof. by rewrite validPtUn; case/and3P. Qed.

Lemma validUnPt_cond k v f : valid (f \+ pts k v) -> C k.
Proof. by rewrite joinC; apply: validPtUn_cond. Qed.

Lemma validPtUnD k v f : valid (pts k v \+ f) -> k \notin dom f.
Proof. by rewrite validPtUn; case/and3P. Qed.

Lemma validUnPtD k v f : valid (f \+ pts k v) -> k \notin dom f.
Proof. by rewrite joinC; apply: validPtUnD. Qed.

(* dom *)

Lemma domPtUn k v f :
        dom (pts k v \+ f) =i
        [pred x | valid (pts k v \+ f) & (k == x) || (x \in dom f)].
Proof.
move=>x; rewrite domUn !inE !validPtUn domPt !inE.
by rewrite -!andbA; case: (C k).
Qed.

Lemma domUnPt k v f :
        dom (f \+ pts k v) =i
        [pred x | valid (f \+ pts k v) & (k == x) || (x \in dom f)].
Proof. by rewrite joinC; apply: domPtUn. Qed.

Lemma domPtUnE k v f : k \in dom (pts k v \+ f) = valid (pts k v \+ f).
Proof. by rewrite domPtUn inE eq_refl andbT. Qed.

Lemma domUnPtE k v f : k \in dom (f \+ pts k v) = valid (f \+ pts k v).
Proof. by rewrite joinC; apply: domPtUnE. Qed.

Lemma domPtUnE2 k v1 v2 f : dom (pts k v1 \+ f) = dom (pts k v2 \+ f).
Proof. by apply/domE=>x; rewrite !domPtUn !validPtUn. Qed.

Lemma domUnPtE2 k v1 v2 f : dom (f \+ pts k v1) = dom (f \+ pts k v2).
Proof. by rewrite !(joinC f); apply: domPtUnE2. Qed.

Lemma validxx f : valid (f \+ f) -> dom f =i pred0.
Proof. by case: validUn=>// _ _ L _ z; case: (_ \in _) (L z)=>//; elim. Qed.

Lemma domPtUnK k v f :
        valid (pts k v \+ f) ->
        all (ord k) (dom f) ->
        dom (pts k v \+ f) = k :: dom f.
Proof.
move=>W H; apply: (@eq_sorted_irr K ord) =>//=.
- by rewrite path_min_sorted //; apply: sorted_dom.
by move=>x; rewrite domPtUn !inE W eq_sym.
Qed.

Lemma domUnPtK k v f :
        valid (f \+ pts k v) ->
        all (ord^~k) (dom f) ->
        dom (f \+ pts k v) = rcons (dom f) k.
Proof.
move=>W H; apply: (@eq_sorted_irr K ord)=>//=.
- rewrite -(rev_sorted (fun x=>ord^~x)) rev_rcons /=.
  by rewrite path_min_sorted ?rev_sorted // all_rev.
by move=>x; rewrite domUnPt inE W mem_rcons inE eq_sym.
Qed.

Lemma size_domPtUn k v f :
        valid (pts k v \+ f) -> size (dom (pts k v \+ f)) = 1 + size (dom f).
Proof. by move=>W; rewrite size_domUn // domPtK (validPtUn_cond W). Qed.

(* dom_eq *)

Lemma domeqPtUn k v1 v2 f1 f2 :
        dom_eq f1 f2 -> dom_eq (pts k v1 \+ f1) (pts k v2 \+ f2).
Proof. by apply: domeqUn=>//; apply: domeqPt. Qed.

Lemma domeqUnPt k v1 v2 f1 f2 :
        dom_eq f1 f2 -> dom_eq (f1 \+ pts k v1) (f2 \+ pts k v2).
Proof. by rewrite (joinC f1) (joinC f2); apply: domeqPtUn. Qed.

(* find *)

Lemma findPtUn k v f :
        valid (pts k v \+ f) -> find k (pts k v \+ f) = Some v.
Proof.
move=>V'; rewrite findUnL // domPt inE.
by rewrite ptsU findU eq_refl valid_unit (validPtUn_cond V').
Qed.

Lemma findUnPt k v f :
        valid (f \+ pts k v) -> find k (f \+ pts k v) = Some v.
Proof. by rewrite joinC; apply: findPtUn. Qed.

Lemma findPtUn2 k1 k2 v f :
         valid (pts k2 v \+ f) ->
         find k1 (pts k2 v \+ f) =
         if k1 == k2 then Some v else find k1 f.
Proof.
move=>V'; rewrite findUnL // domPt inE eq_sym.
by rewrite findPt2 (validPtUn_cond V') andbT /=; case: ifP=>// ->.
Qed.

Lemma findUnPt2 k1 k2 v f :
         valid (f \+ pts k2 v) ->
         find k1 (f \+ pts k2 v) =
         if k1 == k2 then Some v else find k1 f.
Proof. by rewrite joinC; apply: findPtUn2. Qed.

(* free *)

Lemma freePtUn2 k1 k2 v f :
        valid (pts k2 v \+ f) ->
        free (pts k2 v \+ f) k1 =
        if k1 == k2 then f else pts k2 v \+ free f k1.
Proof.
move=>V'; rewrite freeUn domPtUn inE V' /= eq_sym.
rewrite ptsU freeU (validPtUn_cond V') free0.
case: eqP=>/= E; first by rewrite E unitL (dom_free (validPtUnD V')).
by case: ifP=>// N; rewrite dom_free // N.
Qed.

Lemma freeUnPt2 k1 k2 v f :
        valid (f \+ pts k2 v) ->
        free (f \+ pts k2 v) k1 =
        if k1 == k2 then f else free f k1 \+ pts k2 v.
Proof. by rewrite !(joinC _ (pts k2 v)); apply: freePtUn2. Qed.

Lemma freePtUn k v f :
        valid (pts k v \+ f) -> free (pts k v \+ f) k = f.
Proof. by move=>V'; rewrite freePtUn2 // eq_refl. Qed.

Lemma freeUnPt k v f :
        valid (f \+ pts k v) -> free (f \+ pts k v) k = f.
Proof. by rewrite joinC; apply: freePtUn. Qed.

(* Frequently we introduce existentials to name *)
(* the "rest" of a map in a representation with a union of a pointer *)
(* This lemma bridges between such representation and one with free *)
Lemma freeX k v f1 f2 : valid f1 -> f1 = pts k v \+ f2 -> f2 = free f1 k.
Proof. by move=>W E; rewrite E freePtUn // -E. Qed.

(* upd *)

Lemma updPtUn k v1 v2 f : upd k v1 (pts k v2 \+ f) = pts k v1 \+ f.
Proof.
case V1 : (valid (pts k v2 \+ f)).
- by rewrite updUnL domPt inE eq_refl updPt (validPtUn_cond V1).
have V2 : valid (pts k v1 \+ f) = false.
- by rewrite !validPtUn in V1 *.
move/negbT/invalidE: V1=>->; move/negbT/invalidE: V2=>->.
by apply: upd_undef.
Qed.

Lemma updUnPt k v1 v2 f : upd k v1 (f \+ pts k v2) = f \+ pts k v1.
Proof. by rewrite !(joinC f); apply: updPtUn. Qed.

Lemma upd_eta k v f : upd k v f = pts k v \+ free f k.
Proof.
case W : (valid f); last first.
- by move/negbT/invalidE: W=>->; rewrite upd_undef free_undef join_undef.
case H : (C k); last first.
- by move/negbT: H=>H; rewrite (upd_condN v) // pts_condN // undef_join.
have W' : valid (pts k v \+ free f k).
- by rewrite validPtUn H validF W domF inE eq_refl.
apply: find_eta=>//; first by rewrite validU H W.
by move=>k'; rewrite findU H W findPtUn2 // findF; case: eqP.
Qed.

(* um_unitb *)

Lemma um_unitbPtUn k v f : unitb (pts k v \+ f) = false.
Proof. by rewrite um_unitbUn um_unitbPt. Qed.

Lemma um_unitbUnPt k v f : unitb (f \+ pts k v) = false.
Proof. by rewrite joinC; apply: um_unitbPtUn. Qed.

(* undef *)

Lemma pts_undef k v : pts k v = undef :> U <-> ~~ C k.
Proof. by rewrite -(validPt k v) invalidE. Qed.

Lemma pts_undef2 k v1 v2 : pts k v1 \+ pts k v2 = undef :> U.
Proof.
apply/invalidE; rewrite validPtUn validPt domPt !negb_and negb_or eq_refl.
by case: (C k).
Qed.

(* umpleq *)

Lemma umpleq_dom k v f : valid f -> [pcm pts k v <= f] -> k \in dom f.
Proof. by move=>W [z E]; subst f; rewrite domPtUn inE W eq_refl. Qed.

(* others *)

Lemma um_eta k f :
        k \in dom f -> exists v, find k f = Some v /\ f = pts k v \+ free f k.
Proof.
case: dom_find=>// v E1 E2 _; exists v; split=>//.
by rewrite {1}E2 -{1}[free f k]unitL updUnR domF inE /= eq_refl ptsU.
Qed.

Lemma um_eta2 k v f : find k f = Some v -> f = pts k v \+ free f k.
Proof. by move=>E; case/um_eta: (find_some E)=>v' []; rewrite E; case=><-. Qed.

Lemma cancel k v1 v2 f1 f2 :
        valid (pts k v1 \+ f1) ->
        pts k v1 \+ f1 = pts k v2 \+ f2 -> [/\ v1 = v2, valid f1 & f1 = f2].
Proof.
move=>V' E.
have: find k (pts k v1 \+ f1) = find k (pts k v2 \+ f2) by rewrite E.
rewrite !findPtUn -?E //; case=>X.
by rewrite -{}X in E *; rewrite -(joinxK V' E) (validE2 V').
Qed.

Lemma cancel2 k1 k2 f1 f2 v1 v2 :
        valid (pts k1 v1 \+ f1) ->
        pts k1 v1 \+ f1 = pts k2 v2 \+ f2 ->
        if k1 == k2 then v1 = v2 /\ f1 = f2
        else [/\ free f2 k1 = free f1 k2,
                 f1 = pts k2 v2 \+ free f2 k1 &
                 f2 = pts k1 v1 \+ free f1 k2].
Proof.
move=>V1 E; case: ifP=>X.
- by rewrite -(eqP X) in E; case/(cancel V1): E.
move: (V1); rewrite E => V2.
have E' : f2 = pts k1 v1 \+ free f1 k2.
- move: (erefl (free (pts k1 v1 \+ f1) k2)).
  rewrite {2}E freeUn E domPtUn inE V2 eq_refl /=.
  by rewrite ptsU freeU eq_sym X free0 -ptsU freePtUn.
suff E'' : free f1 k2 = free f2 k1.
- by rewrite -E''; rewrite E' joinCA in E; case/(cancel V1): E.
move: (erefl (free f2 k1)).
by rewrite {1}E' freePtUn // -E' (validE2 V2).
Qed.

Lemma um_contra k v f g : f = pts k v \+ g \+ f -> ~~ valid f.
Proof.
move=>E; rewrite E -joinAC -joinA validPtUn.
rewrite {2}E -!joinA domPtUn !inE.
by rewrite eq_refl andbT !joinA -E andbN andbF.
Qed.

(* induction over union maps, expressed with pts and \+ *)

(* forward progressing over keys *)
Lemma um_indf (P : U -> Prop) :
         P undef -> P Unit ->
         (forall k v f, P f -> valid (pts k v \+ f) ->
             path ord k (dom f) ->
             P (pts k v \+ f)) ->
         forall f, P f.
Proof.
rewrite !pcmE /undef /= !umEX => H1 H2 H3 f; rewrite -[f]UMC.tfE.
apply: (UM.base_indf (P := (fun b => P (UMC.to b))))=>//.
move=>k v g H V1; move: (H3 k v _ H); rewrite !pcmE /= !umEX.
by apply.
Qed.

(* unordered progressing over keys *)
Lemma um_ind' (P : U -> Prop) :
         P undef -> P Unit ->
         (forall k v f, P f -> valid (pts k v \+ f) -> P (pts k v \+ f)) ->
         forall f, P f.
Proof. by move=>H1 H2 H3; apply: um_indf=>// k v f H4 H5 _; apply: H3. Qed.

(* backward progressing over keys *)
Lemma um_indb (P : U -> Prop) :
         P undef -> P Unit ->
         (forall k v f, P f -> valid (f \+ pts k v) ->
            (forall x, x \in dom f -> ord x k) ->
            P (pts k v \+ f)) ->
         forall f, P f.
Proof.
rewrite !pcmE /undef /= !umEX => H1 H2 H3 f; rewrite -[f]UMC.tfE.
apply: (UM.base_indb (P := (fun b => P (UMC.to b))))=>//.
move=>k v g H V1; move: (H3 k v _ H); rewrite !pcmE /= !umEX.
by apply.
Qed.

(* validity holds pairwise *)
Lemma um_valid3 f1 f2 f3 :
        valid (f1 \+ f2 \+ f3) =
        [&& valid (f1 \+ f2), valid (f2 \+ f3) & valid (f1 \+ f3)].
Proof.
apply/idP/and3P; first by move=>W; rewrite !(validLE3 W).
case=>V1 V2 V3; case: validUn=>//; rewrite ?V1 ?(validE2 V2) // => k.
by rewrite domUn inE V1; case/orP; [move: V3 | move: V2];
   case: validUn =>// _ _ X _ /X /negbTE ->.
Qed.

(* points-to is a prime element of the monoid *)
Lemma um_prime f1 f2 k v :
        C k ->
        f1 \+ f2 = pts k v ->
        f1 = pts k v /\ f2 = Unit \/
        f1 = Unit /\ f2 = pts k v.
Proof.
move: f1 f2; apply: um_indf=>[f1|f2 _|k2 w2 f1 _ _ _ f X E].
- rewrite undef_join -(validPt _ v)=>W E.
  by rewrite -E in W; rewrite valid_undef in W.
- by rewrite unitL=>->; right.
have W : valid (pts k2 w2 \+ (f1 \+ f)).
- by rewrite -(validPt _ v) -E -joinA in X.
rewrite -[pts k v]unitR -joinA in E.
move/(cancel2 W): E; case: ifP.
- by move/eqP=>-> [->] /join0E [->->]; rewrite unitR; left.
by move=>_ [_ _] /esym/unitbP; rewrite um_unitbPtUn.
Qed.

(* also a simple rearrangment equation *)
Definition pullk (k : K) (v : V) (f : U) := pull (pts k v) f.

End PointsToLemmas.

Hint Resolve domeqPt domeqPtUn domeqUnPt : core.
Prenex Implicits validPtUn_cond findPt_inv um_eta2 um_contra.
Prenex Implicits validPtUnD validUnPtD.


(******************************************************)
(******************************************************)
(* Defined notions that don't appear in the signature *)
(******************************************************)
(******************************************************)

(************)
(* um_preim *)
(************)

Section PreimDefLemmas.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map_class C V).
Implicit Types (k : K) (v : V) (f : U) (p : pred V).

Definition um_preim p f k := oapp p false (find k f).

Lemma umpreim_undef p : um_preim p undef =1 pred0.
Proof. by move=>x; rewrite /um_preim find_undef. Qed.

Lemma umpreim0 p : um_preim p Unit =1 pred0.
Proof. by move=>x; rewrite /um_preim find0E. Qed.

Lemma umpreimUn p f1 f2 :
        valid (f1 \+ f2) ->
        um_preim p (f1 \+ f2) =1 predU (um_preim p f1) (um_preim p f2).
Proof.
move=>v x; rewrite /um_preim findUnL //=.
case X: (find x f1)=>[a|]; case Y: (find x f2)=>[b|] /=.
- by move: (dom_inNL v (find_some X)); rewrite (find_some Y).
- by rewrite ifT ?(find_some X) // orbC.
- by rewrite ifN //; apply/find_none.
by rewrite ifN //; apply/find_none.
Qed.

Lemma umpreim_pred0 f : um_preim pred0 f =1 pred0.
Proof. by move=>x; rewrite /um_preim; by case: (find x f). Qed.

Lemma umpreim_dom f : um_preim predT f =1 mem (dom f).
Proof.
move=>x; rewrite /um_preim /=.
case X: (find x f)=>[a|] /=; first by rewrite (find_some X).
by apply/esym/negbTE/find_none.
Qed.

End PreimDefLemmas.


(****************************)
(* map membership predicate *)
(****************************)

Section MapMembership.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map_class C V).
Implicit Type f : U.

Definition Mem_UmMap f :=
  fun x : K * V => valid f /\ [pcm pts x.1 x.2 <= f].

Canonical Structure um_PredType :=
  Eval hnf in @mkPredType (K*V) U Mem_UmMap.

(* This makes Mem_UmMap a canonical instance of topred. *)
Canonical Structure Mem_UmMap_PredType :=
  Eval hnf in mkPredType Mem_UmMap.

Lemma In_undef x : x \In (undef : U) -> False.
Proof. by case; rewrite valid_undef. Qed.

Lemma In0 x : x \In (Unit : U) -> False.
Proof. by case=>_; case=>z /esym/unitbP; rewrite um_unitbPtUn. Qed.

Lemma In_find k v f : (k, v) \In f <-> find k f = Some v.
Proof.
split=>[[W] /= [z E]|E]; first by rewrite E findPtUn // -E.
split; first by move/find_some/dom_valid: E.
by move/um_eta2: E=>->; exists (free f k).
Qed.

Lemma In_fun k v1 v2 f : (k, v1) \In f -> (k, v2) \In f -> v1 = v2.
Proof. by move/In_find=>H1 /In_find; rewrite H1; case. Qed.

Lemma InUn x f1 f2 : x \In (f1 \+ f2) -> x \In f1 \/ x \In f2.
Proof.
move/In_find=>F; move/find_some: (F); rewrite domUn inE=>/andP [W D].
case/orP: D F=>D; first by rewrite findUnL // D=>/In_find; left.
by rewrite findUnR // D=>/In_find; right.
Qed.

Lemma InL x f1 f2 : valid (f1 \+ f2) -> x \In f1 -> x \In (f1 \+ f2).
Proof. by move=>W /In_find E; apply/In_find; rewrite findUnL // (find_some E). Qed.

Lemma InR x f1 f2 : valid (f1 \+ f2) -> x \In f2 -> x \In (f1 \+ f2).
Proof. by rewrite joinC; apply: InL. Qed.

Lemma InPt x k v : x \In pts k v -> x = (k, v) /\ C k.
Proof.
by case: x=>a b /In_find; rewrite findPt2; case: ifP=>//; case/andP=>/eqP ->-> [->].
Qed.

Lemma In_condPt k v : C k -> (k, v) \In pts k v.
Proof. by split; [rewrite validPt | exists Unit; rewrite unitR]. Qed.

Lemma In_dom f x : x \In f -> x.1 \in dom f.
Proof. by case=>W [z E]; subst f; rewrite domPtUn inE W eq_refl. Qed.

Lemma In_cond f x : x \In f -> C x.1.
Proof. by move/In_dom/dom_cond. Qed.

Lemma In_domX k f : reflect (exists v, (k, v) \In f) (k \in dom f).
Proof.
case: dom_find=>[E|v /In_find H E]; constructor; last by exists v.
by case=>v /In_find; rewrite E.
Qed.

Lemma InPtUnE x k v f :
        valid (pts k v \+ f) ->
        x \In pts k v \+ f <-> x = (k, v) \/ x \In f.
Proof.
move=>W; split; last by case=>[->|/(InR W)].
by case/InUn; [case/InPt=>->; left|right].
Qed.

Lemma InPtUnL k v f : valid (pts k v \+ f) -> (k, v) \In pts k v \+ f.
Proof. by move/InPtUnE=>->; left. Qed.

Lemma InPtUnEN k v x f :
        valid (pts k v \+ f) ->
        x \In (pts k v \+ f) <-> x = (k, v) \/ x \In f /\ x.1 != k.
Proof.
move=>W; rewrite InPtUnE //; split; last by case; [left|case; right].
case=>[->|H]; first by left.
right; split=>//; move/In_dom: H=>H.
case: validUn W=>//; rewrite validPt=>W W' /(_ k).
rewrite domPt inE W eq_refl /= => /(_ (erefl _)).
by case: eqP H=>// ->->.
Qed.

Lemma InPtUn x k v f :
        x \In pts k v \+ f ->
        (forall w, valid (pts k w \+ f)) /\
        (x = (k, v) /\ C k \/ x \In f /\ x.1 != k).
Proof.
move=>H; have W w : valid (pts k w \+ f).
- by rewrite (validPtUnE v); apply: dom_valid (In_dom H).
split=>//; move/(InPtUnEN _ (W v)): H (W v).
by case=>[-> /validPtUn_cond|]; [left | right].
Qed.

Lemma InPtUnK k v w f :
        valid (pts k v \+ f) ->
        (k, w) \In (pts k v \+ f) <-> v = w.
Proof.
move=>W; rewrite InPtUnEN //; split=>[|->]; last by left.
by case=>[[->]|[]] //=; rewrite eq_refl.
Qed.

Lemma In_domY k f : k \in dom f -> sigT (fun v => (k, v) \In f).
Proof. by case: dom_find=>// v /In_find; exists v. Qed.

Lemma umemE f x : x \In assocs f <-> x \In f.
Proof.
move: f; apply: um_indf=>[||k v f IH W /(order_path_min (@trans K)) P].
- by rewrite assocs_undef; split=>// /In_undef.
- by rewrite assocs0; split=>// /In0.
by rewrite assocsPtUn ?InE // InPtUnE // IH.
Qed.

Lemma umem_eq f1 f2 :
        valid f1 -> valid f2 ->
        (forall x, x \In f1 <-> x \In f2) -> f1 = f2.
Proof.
move=>V1 V2 H; apply: find_eta=>// k.
case K1 : (find k f1)=>[a1|]; case K2 : (find k f2)=>[a2|] //.
- by move/In_find/H/In_find: K1; rewrite K2.
- by move/In_find/H/In_find: K1; rewrite K2.
by move/In_find/H/In_find: K2; rewrite K1.
Qed.

Lemma InU x k v f :
        x \In upd k v f <->
        [/\ valid (upd k v f) & if x.1 == k then x.2 = v else x \In f].
Proof.
case: x=>x1 v1; split; last first.
- case=>W /= H; split=>//=; exists (free (upd k v f) x1); apply: um_eta2.
  move: (W); rewrite validU=>/andP [C' W']; rewrite findU C' W' /=.
  by case: eqP H=>[_ ->|_ /In_find].
move=>H; move: (In_dom H)=>/= D; move: (dom_valid D) (dom_valid D)=>W.
rewrite {1}validU=>/andP [C' W']; split=>//.
move: (D); rewrite domU inE C'  /= W'; case: H=>/= _ [z E].
case: ifP D E=>[/eqP -> D E _|N _ E D].
- have: find k (upd k v f) = Some v by rewrite findU eq_refl C' W'.
  by rewrite E findPtUn -?E //; case=>->.
have: find x1 (pts x1 v1 \+ z) = Some v1 by rewrite findPtUn // -E.
by rewrite -E findU N C'=>/In_find.
Qed.

Lemma InF x k f :
        x \In free f k <->
        [/\ valid (free f k), x.1 != k & x \In f].
Proof.
case: x=>x1 v1; split; last first.
- by case=>W /= N /In_find E; apply/In_find; rewrite findF (negbTE N).
case=>W /= H; rewrite W; case: H=>z E.
have : find x1 (pts x1 v1 \+ z) = Some v1 by rewrite findPtUn // -E.
by rewrite -E findF; case: eqP=>//= _ /In_find.
Qed.

Lemma In_eta k v f : (k, v) \In f -> f = pts k v \+ free f k.
Proof. by move=>H; case/In_dom/um_eta: (H)=>w [/In_find/(In_fun H) ->]. Qed.

End MapMembership.

Arguments In_condPt {K C V U k}.
Prenex Implicits InPt In_eta InPtUn In_dom.

(*********)
(* range *)
(*********)

Section Range.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map_class C V).
Implicit Types f : U.

Definition range f := map snd (assocs f).

Lemma size_range f : size (range f) = size (dom f).
Proof. by rewrite assocs_dom !size_map. Qed.

Lemma range_undef : range undef = [::].
Proof. by rewrite /range assocs_undef. Qed.

Lemma range0 : range Unit = [::].
Proof. by rewrite /range assocs0. Qed.

Lemma In_rangeX v f : v \In range f <-> exists k, (k, v) \In f.
Proof.
elim/um_indf: f v=>[v|v|k w f IH W P v].
- by rewrite range_undef; split=>//; case=>x /In_undef.
- by rewrite range0; split=>//; case=>x /In0.
move: (order_path_min (@trans K) P)=>A.
rewrite /range assocsPtUn //= InE; split.
- case=>[->|/IH [k' H]]; first by exists k; rewrite InPtUnE //; left.
  by exists k'; rewrite InPtUnE //; right.
case=>k'; rewrite InPtUnE //; case; first by case; left.
by move=>H; right; apply/IH; exists k'.
Qed.

Lemma In_range_valid k f : k \In range f -> valid f.
Proof. by case/In_rangeX=>v /In_dom/dom_valid. Qed.

Lemma In_range k v f : (k, v) \In f -> v \In range f.
Proof. by move=>H; apply/In_rangeX; exists k. Qed.

Lemma In_rangeUn f1 f2 x :
        x \In range (f1 \+ f2) ->
        x \In range f1 \/ x \In range f2.
Proof. by rewrite !In_rangeX; case=>k /InUn [] H; [left | right]; exists k. Qed.

Lemma In_rangeL f1 f2 x :
        valid (f1 \+ f2) -> x \In range f1 -> x \In range (f1 \+ f2).
Proof. by move=>W; rewrite !In_rangeX; case=>k H; exists k; apply/InL. Qed.

Lemma In_rangeR f1 f2 x :
        valid (f1 \+ f2) -> x \In range f2 -> x \In range (f1 \+ f2).
Proof. by move=>W; rewrite !In_rangeX; case=>k H; exists k; apply/InR. Qed.

Lemma In_rangePt k :
        C k -> forall v x, x \In range (pts k v) <-> (x = v).
Proof.
move=>C' v x; rewrite In_rangeX. split.
- by case=>w /InPt [[]].
by move=>->; exists k; apply: In_condPt.
Qed.

Lemma In_rangePtUn k v f x :
        valid (pts k v \+ f) ->
        x \In range (pts k v \+ f) <-> x = v \/ x \In range f.
Proof.
move=>W; split.
- case/In_rangeUn; last by right.
  by move/(In_rangePt (validPtUn_cond W)); left.
case=>[->|]; last by apply: In_rangeR.
by apply/(In_rangeL W)/(In_rangePt (validPtUn_cond W)).
Qed.

End Range.

Prenex Implicits In_range_valid In_range In_rangeUn.

(* decidable versions, when V is eqtype *)

Section DecidableRange.
Variables (K : ordType) (C : pred K) (V : eqType) (U : union_map_class C V).
Implicit Types f : U.

Lemma uniq_rangeP f :
        reflect (forall k1 k2 v, (k1, v) \In f -> (k2, v) \In f -> k1 = k2)
                (uniq (range f)).
Proof.
case W : (valid f); last first.
- move/negbT/invalidE: W=>->; rewrite range_undef.
  by constructor=>k1 k2 v /In_undef.
case H : (uniq (range f)); constructor; last first.
- move=>H'; move/negbT/negP: H; elim.
  rewrite map_inj_in_uniq; first by apply: uniq_assocs.
  case=>/= k1 v [k2 v'] /mem_seqP/umemE H1 /mem_seqP/umemE H2 /= H3.
  by rewrite -H3 in H2 *; rewrite (H' _ _ _ H1 H2).
move/uniqP: H=>H k1 k2 v H1 H2.
set j1 := index k1 (dom f).
set j2 := index k2 (dom f).
have [D1 D2] : k1 \in dom f /\ k2 \in dom f.
- by move/In_dom: H1; move/In_dom: H2.
have [R1 R2] : j1 < size (assocs f) /\ j2 < size (assocs f).
- by rewrite size_assocs !index_mem.
have [M1 M2] : j1 < size (dom f) /\ j2 < size (dom f).
- by rewrite !index_mem.
have [A1 A2] : (k1, v) \in assocs f /\ (k2, v) \in assocs f.
- by move/umemE/mem_seqP: H1=>->; move/umemE/mem_seqP: H2=>->.
have InjF : {in assocs f &, injective fst}.
- case=>a1 v1 [a2 v2] /mem_seqP X1 /mem_seqP X2 /= E.
  by move: E X1 X2 => -> X1 /(assocs_map X1) ->.
have /eqP E1 : j1 == index (k1,v) (assocs f).
- rewrite -(nth_uniq (k1,v) R1 _ (uniq_assocs _)); last by rewrite index_mem.
  by rewrite /j1 assocs_dom (nth_index_map _ InjF A1) nth_index.
have /eqP E2 : j2 == index (k2,v) (assocs f).
- rewrite -(nth_uniq (k2,v) R2 _ (uniq_assocs _)); last by rewrite index_mem.
  by rewrite /j2 assocs_dom (nth_index_map _ InjF A2) nth_index.
have E : nth v (range f) j1 = nth v (range f) j2.
- rewrite /range (nth_map (k1,v) v _ R1) (nth_map (k2,v) v _ R2).
  by rewrite E1 E2 !nth_index.
have : j1 = j2 by apply: H E; rewrite inE size_range.
by move/eqP; rewrite -(nth_uniq k1 M1 M2 (uniq_dom _)) !nth_index // =>/eqP.
Qed.

(* this is just a renaming of mem_seqP for easier finding *)
Lemma mem_rangeP x f : reflect (x \In range f) (x \in range f).
Proof. by apply: mem_seqP. Qed.

Lemma mem_rangeX v f : v \in range f <-> exists k, (k, v) \In f.
Proof. by split; [move/mem_seqP/In_rangeX|move/In_rangeX/mem_seqP]. Qed.

Lemma range_valid k f : k \in range f -> valid f.
Proof. by move/mem_seqP/In_range_valid. Qed.

Lemma mem_range k v f : (k, v) \In f -> v \in range f.
Proof. by move/In_range/mem_seqP. Qed.

Lemma rangeUn f1 f2 :
        range (f1 \+ f2) =i
        [pred x | valid (f1 \+ f2) && ((x \in range f1) || (x \in range f2))].
Proof.
move=>k; apply/idP/idP; last first.
- case/andP=>W /orP [] /mem_seqP H; apply/mem_seqP;
  by [apply/(In_rangeL W) | apply/(In_rangeR W)].
move/mem_seqP=>H; rewrite (In_range_valid H) inE /=.
by case/In_rangeUn: H=>/mem_seqP -> //; rewrite orbT.
Qed.

Lemma rangePtK k v : C k -> range (U:=U) (pts k v) = [:: v].
Proof. by move=>C'; rewrite /range assocsPt C'. Qed.

Lemma rangePt x k v : C k -> x \in range (U:=U) (pts k v) = (x == v).
Proof. by move=>C'; rewrite /range assocsPt C' inE. Qed.

Lemma rangePtUn k v f :
        range (pts k v \+ f) =i
        [pred x | valid (pts k v \+ f) & (v == x) || (x \in range f)].
Proof.
move=>x; rewrite rangeUn !inE; case W : (valid _)=>//=.
by rewrite rangePt ?(validPtUn_cond W) // eq_sym.
Qed.

Lemma rangePtUnK k v f :
        valid (pts k v \+ f) ->
        all (ord k) (dom f) ->
        range (pts k v \+ f) = v :: range f.
Proof. by move=>W H; rewrite /range assocsPtUn. Qed.

Lemma rangeUnPtK k v f :
        valid (f \+ pts k v) ->
        all (ord^~ k) (dom f) ->
        range (f \+ pts k v) = rcons (range f) v.
Proof. by move=>W H; rewrite /range assocsUnPt // map_rcons. Qed.

Lemma uniq_rangeUn f1 f2 :
        valid (f1 \+ f2) ->
        uniq (range (f1 \+ f2)) = uniq (range f1 ++ range f2).
Proof.
move=>W; apply/esym; case: uniq_rangeP=>H; last first.
- apply/negP; rewrite cat_uniq=>/and3P [H1 /hasP H2 H3].
  elim: H=>k1 k2 v /InUn [] F1 /InUn []; move: F1.
  - by move/uniq_rangeP: H1; apply.
  - by move/mem_range=>F1 /mem_range F2; elim: H2; exists v.
  - by move/mem_range=>F1 /mem_range F2; elim: H2; exists v.
  by move/uniq_rangeP: H3; apply.
rewrite cat_uniq; apply/and3P; split; last 1 first.
- by apply/uniq_rangeP=>k1 k2 v F1 F2; apply: (H k1 k2 v); apply/InR.
- by apply/uniq_rangeP=>k1 k2 v F1 F2; apply: (H k1 k2 v); apply/InL.
case: hasP=>//; case=>x /mem_rangeX [k1 H1] /mem_rangeX [k2 H2].
have [G1 G2] : (k1, x) \In f1 \+ f2 /\ (k2, x) \In f1 \+ f2.
- by split; [apply/InR|apply/InL].
rewrite -(H k1 k2 x G1 G2) in H2.
by move: (dom_inNR W (In_dom H1)); rewrite (In_dom H2).
Qed.

Lemma uniq_rangePtUn k v f :
        valid (pts k v \+ f) ->
        uniq (range (pts k v \+ f)) = uniq (v :: range f).
Proof. by move=>W; rewrite uniq_rangeUn // rangePtK // (validPtUn_cond W). Qed.

Lemma uniq_rangeL f1 f2 :
        valid (f1 \+ f2) -> uniq (range (f1 \+ f2)) -> uniq (range f1).
Proof. by move=>W; rewrite uniq_rangeUn // cat_uniq; case/and3P. Qed.

Lemma uniq_rangeR f1 f2 :
        valid (f1 \+ f2) -> uniq (range (f1 \+ f2)) -> uniq (range f2).
Proof. by move=>W; rewrite uniq_rangeUn // cat_uniq; case/and3P. Qed.

Lemma uniq_rangeF k f : uniq (range f) -> uniq (range (free f k)).
Proof.
case W: (valid f); last first.
- by move/negbT/invalidE: W=>->; rewrite free_undef !range_undef.
case D : (k \in dom f); last by move/negbT/dom_free: D=>E; rewrite -{1}E.
by case: (um_eta D) W=>x [_] E; rewrite {1 2}E; apply: uniq_rangeR.
Qed.

End DecidableRange.


(********************)
(* Map monotonicity *)
(********************)

Section MapMonotonicity.
Variables (K V : ordType) (C : pred K) (U : union_map_class C V).
Implicit Types f : U.

Definition um_mono f := sorted ord (range f).
Definition um_mono_lt f := forall k k' v v',
  (k, v) \In f -> (k', v') \In f -> ord k k' -> ord v v'.
Definition um_mono_ltE f := forall k k' v v',
  (k, v) \In f -> (k', v') \In f -> ord k k' <-> ord v v'.
Definition um_mono_leE f := forall k k' v v',
  (k, v) \In f -> (k', v') \In f -> oleq k k' <-> oleq v v'.

Lemma ummonoP f : reflect (um_mono_lt f) (um_mono f).
Proof.
rewrite /um_mono/um_mono_lt/range.
apply/(equivP idP); elim/um_indf: f=>[||k v f IH W P].
- by rewrite assocs_undef; split=>// _ ???? /In_undef.
- by rewrite assocs0; split=>// _ ???? /In0.
rewrite assocsPtUn ?(order_path_min (@trans _) P) //=; split=>H; last first.
- rewrite path_min_sorted; first by apply/IH=>??????; apply: H; apply/InR.
  apply/allP=>x /mapP [[y w]] /mem_seqP/umemE X ->.
  by apply: H (path_mem (@trans K) P (In_dom X)); [apply/InPtUnL|apply/InR].
move=>x x' w w'; rewrite !InPtUnE //.
case=>[[->->]|H1]; case=>[[->->]|H2]; first by rewrite irr.
- suff: w' \in [seq i.2 | i <- assocs f] by move/(path_mem (@trans V) H).
  by move/umemE/mem_seqP: H2=>H2; apply/mapP; exists (x',w').
- by move/In_dom/(path_mem (@trans K) P): H1; case: ordP.
by move/path_sorted/IH: H; apply.
Qed.

Lemma ummono_undef : um_mono undef.
Proof. by apply/ummonoP=>???? /In_undef. Qed.

Lemma ummono0 : um_mono Unit.
Proof. by apply/ummonoP=>???? /In0. Qed.

Lemma ummonoUnL f1 f2 : valid (f1 \+ f2) -> um_mono (f1 \+ f2) -> um_mono f1.
Proof. by move=>W /ummonoP H; apply/ummonoP=>??????; apply: H; apply/InL. Qed.

Lemma ummonoUnR f1 f2 : valid (f1 \+ f2) -> um_mono (f1 \+ f2) -> um_mono f2.
Proof. by rewrite joinC; apply: ummonoUnL. Qed.

Lemma ummonoPtUn k' v' f :
        valid (pts k' v' \+ f) ->
        (forall k v, (k, v) \In f -> ord k k' /\ ord v v') ->
        um_mono (pts k' v' \+ f) = um_mono f.
Proof.
move=>W H; apply/idP/idP=>/ummonoP X; apply/ummonoP=>x x' w w' Y Y'.
- by apply: X; apply/InR.
case/(InPtUnE _ W): Y'=>[[->->]|]; case/(InPtUnE _ W): Y=>[[->->]|];
by [rewrite irr|case/H|case/H; case: ordP|apply: X].
Qed.

Lemma In_mono_fun k v1 v2 f :
        um_mono f -> (v1, k) \In f -> (v2, k) \In f -> v1 = v2.
Proof.
move/ummonoP=>M H1 H2; case: (ordP v1 v2).
- by move/(M _ _ _ _ H1 H2); rewrite irr.
- by move/eqP.
by move/(M _ _ _ _ H2 H1); rewrite irr.
Qed.

Lemma In_mono_range k f1 f2 :
        valid (f1 \+ f2) -> um_mono (f1 \+ f2) ->
        k \in range f1 -> k \in range f2 -> false.
Proof.
move=>W M /mem_seqP/In_rangeX [v1 H1] /mem_seqP/In_rangeX [v2 H2].
have H1' : (v1, k) \In f1 \+ f2 by apply/InL.
have H2' : (v2, k) \In f1 \+ f2 by apply/InR.
rewrite -{v2 H1' H2'}(In_mono_fun M H1' H2') in H2.
move/In_dom: H2; move/In_dom: H1=>H1.
by rewrite (negbTE (dom_inNL W H1)).
Qed.

Lemma ummono_ltP f : reflect (um_mono_ltE f) (um_mono f).
Proof.
case: ummonoP=>M; constructor; last first.
- by move=>N; elim: M=>x x' y y' X1 X2 /N; apply.
move=>x x' y y' X1 X2.
move: (M _ _ _ _ X1 X2) (M _ _ _ _ X2 X1)=>O1 O2.
split=>// N; case: ordP=>// Y1.
- by move/O2: Y1; case: ordP N.
by move/eqP: Y1=>?; subst x'; rewrite (In_fun X1 X2) irr in N.
Qed.

Lemma ummono_leP f : um_mono f -> um_mono_leE f.
Proof.
move/ummonoP=>M x x' y y' X1 X2.
move: (M _ _ _ _ X1 X2) (M _ _ _ _ X2 X1)=>O1 O2.
rewrite /oleq (eq_sym x) (eq_sym y).
case: ordP=>Y1; case: ordP=>Y2 //=.
- by move/O2: Y1; rewrite (eqP Y2) irr.
- by move/O2: Y1; case: ordP Y2.
- by rewrite (eqP Y1) in X2; rewrite (In_fun X1 X2) irr in Y2.
by move/O1: Y1; case: ordP Y2.
Qed.

Lemma index_mem_dom_range f k t :
        (k, t) \In f -> uniq (range f) -> index k (dom f) = index t (range f).
Proof.
rewrite /range assocs_dom.
elim/um_indf: f k t=>[||k' t' f IH W /(order_path_min (@trans K)) P] k t.
- by move/In_undef.
- by move/In0.
rewrite assocsPtUn // !map_cons /= InPtUnE //=.
case=>[[->->]|H1 H2]; first by rewrite !eq_refl.
case: eqP (In_dom H1) W=>[-> D|_ _ W].
- by rewrite validPtUn D !andbF.
case: eqP (In_range H1) H2=>[-> /mem_seqP ->//|_ _ /andP [H2 H3]].
by rewrite (IH _ _ H1).
Qed.

Lemma index_dom_range_mem f k t :
        index k (dom f) = index t (range f) ->
        index k (dom f) != size (dom f) -> (k, t) \In f.
Proof.
rewrite /range assocs_dom.
elim/um_indf: f k t=>[||k' t' f IH W /(order_path_min (@trans K)) P] k t.
- by rewrite assocs_undef.
- by rewrite assocs0.
rewrite assocsPtUn // map_cons /=.
case: eqP=>[|_]; first by case: eqP=>// <-<- _ _; apply/InPtUnE=>//; left.
case: eqP=>// _ [H1]; rewrite eqSS=>H2.
by apply/InPtUnE=>//; right; apply: IH H1 H2.
Qed.

End MapMonotonicity.


(**********************)
(* um_foldl, um_foldr *)
(**********************)

(* Induction lemmas over PCMs in the proofs *)

Section FoldDefAndLemmas.
Variables (K : ordType) (C : pred K) (V R : Type) (U : union_map_class C V).
Implicit Type f : U.

Definition um_foldl (a : R -> K -> V -> R) (z0 d : R) f :=
  if valid f then foldl (fun z kv => a z kv.1 kv.2) z0 (assocs f) else d.

Definition um_foldr (a : K -> V -> R -> R) (z0 d : R) f :=
  if valid f then foldr (fun kv z => a kv.1 kv.2 z) z0 (assocs f) else d.

Lemma umfoldl_undef a z0 d : um_foldl a z0 d undef = d.
Proof. by rewrite /um_foldl valid_undef. Qed.

Lemma umfoldr_undef a z0 d : um_foldr a z0 d undef = d.
Proof. by rewrite /um_foldr valid_undef. Qed.

Lemma umfoldl0 a z0 d : um_foldl a z0 d Unit = z0.
Proof. by rewrite /um_foldl assocs0 valid_unit. Qed.

Lemma umfoldr0 a z0 d : um_foldr a z0 d Unit = z0.
Proof. by rewrite /um_foldr assocs0 valid_unit. Qed.

Lemma umfoldlPt a (z0 d : R) k v :
        um_foldl a z0 d (pts k v) =
        if C k then a z0 k v else d.
Proof. by rewrite /um_foldl validPt assocsPt; case: (C k). Qed.

Lemma umfoldrPt a (z0 d : R) k v :
        um_foldr a z0 d (pts k v) =
        if C k then a k v z0 else d.
Proof. by rewrite /um_foldr validPt assocsPt; case: (C k). Qed.

Lemma umfoldlPtUn a k v z0 d f :
        valid (pts k v \+ f) -> all (ord k) (dom f) ->
        um_foldl a z0 d (pts k v \+ f) = um_foldl a (a z0 k v) d f.
Proof. by move=>W H; rewrite /um_foldl /= W (validR W) assocsPtUn. Qed.

Lemma umfoldrPtUn a k v z0 d f :
        valid (pts k v \+ f) -> all (ord k) (dom f) ->
        um_foldr a z0 d (pts k v \+ f) = a k v (um_foldr a z0 d f).
Proof. by move=>W H; rewrite /um_foldr W (validR W) assocsPtUn. Qed.

Lemma umfoldlUnPt a k v z0 d f :
        valid (f \+ pts k v) -> all (ord^~ k) (dom f) ->
        um_foldl a z0 d (f \+ pts k v) = a (um_foldl a z0 d f) k v.
Proof.
by move=>W H; rewrite /um_foldl W (validL W) assocsUnPt // -cats1 foldl_cat.
Qed.

Lemma umfoldrUnPt a k v z0 d f :
        valid (f \+ pts k v) -> all (ord^~ k) (dom f) ->
        um_foldr a z0 d (f \+ pts k v) = um_foldr a (a k v z0) d f.
Proof.
by move=>W H; rewrite /um_foldr W (validL W) assocsUnPt // -cats1 foldr_cat.
Qed.

Lemma umfoldlUn a z0 d f1 f2 :
        valid (f1 \+ f2) -> {in dom f1 & dom f2, forall x y, ord x y} ->
        um_foldl a z0 d (f1 \+ f2) = um_foldl a (um_foldl a z0 d f1) d f2.
Proof.
move: f2; apply: um_indb=>[W H|W H|k v f2 IH W' P W H].
- by rewrite join_undef !umfoldl_undef.
- by rewrite unitR umfoldl0.
rewrite -(joinC f2) joinA in W *; rewrite umfoldlUnPt //; last first.
- apply/allP=>x; rewrite domUn inE (validL W).
  case/orP=>[/H|]; last by apply: P.
  by apply; rewrite domPtUn inE joinC W' eq_refl.
rewrite umfoldlUnPt ?(validAR W) //; last by apply/allP.
rewrite (IH (validL W)) // => k1 k2 D1 D2; apply: H D1 _.
by rewrite domPtUn inE joinC W' D2 orbT.
Qed.

Lemma umfoldrUn a z0 d f1 f2 :
        valid (f1 \+ f2) -> {in dom f1 & dom f2, forall x y, ord x y} ->
        um_foldr a z0 d (f1 \+ f2) = um_foldr a (um_foldr a z0 d f2) d f1.
Proof.
move: f1; apply: um_indf=>[W H|W H|k v f1 IH W' P W H].
- by rewrite undef_join !umfoldr_undef.
- by rewrite unitL umfoldr0.
rewrite -!joinA in W *; rewrite umfoldrPtUn //.
- rewrite umfoldrPtUn ?(order_path_min (@trans K) P) // (IH (validR W)) //.
  by move=>k1 k2 D1; apply: H; rewrite domPtUn inE W' D1 orbT.
apply/allP=>x; rewrite domUn inE (validR W) /=.
case/orP; last by apply: H; rewrite domPtUn inE W' eq_refl.
by apply/allP/(order_path_min (@trans K) P).
Qed.

Lemma umfoldlPtUnE v2 v1 a t (z0 d : R) f :
        (forall r, a r t v1 = a r t v2) ->
        um_foldl a z0 d (pts t v1 \+ f) =
        um_foldl a z0 d (pts t v2 \+ f).
Proof.
move=>H.
case W : (valid (pts t v1 \+ f)); last first.
- move/invalidE: (negbT W)=>->; rewrite umfoldl_undef.
  rewrite (validPtUnE v2) in W.
  by move/invalidE: (negbT W)=>->; rewrite umfoldl_undef.
elim/um_indf: f z0 W=>[|z0|k v f IH V' P z0 W];
rewrite ?join_undef ?unitR ?umfoldlPt ?(H z0) //.
case: (ordP k t) W=>E W; last 2 first.
- by move/validAL: W; rewrite (eqP E) (validPtUnE v) validUnEb um_unitbPt.
- have D w : all (ord t) (dom (pts k w \+ f)).
  - apply/allP=>x; rewrite domPtUn inE=>/andP [_] /orP [/eqP <-|] //.
    by apply: path_mem (@trans K) _; apply: ord_path (@trans K) E P.
  by rewrite !(umfoldlPtUn a (k:=t)) ?(validPtUnE v1) // H.
have D w : all (ord k) (dom (pts t w \+ f)).
- apply/allP=>x; rewrite domPtUn inE=>/andP [_] /orP [/eqP <-|] //.
  by apply: path_mem (@trans K) P.
rewrite !(joinCA _ (pts k v)) in W *.
rewrite !(umfoldlPtUn a (k:=k)) // ?IH ?(validR W) //.
by rewrite joinCA (validPtUnE v1) joinCA.
Qed.

Lemma umfoldlUnPtE v2 v1 a t (z0 d : R) f :
        (forall r, a r t v1 = a r t v2) ->
        um_foldl a z0 d (f \+ pts t v1) =
        um_foldl a z0 d (f \+ pts t v2).
Proof. by rewrite !(joinC f); apply: umfoldlPtUnE. Qed.

Lemma umfoldl_defE a z0 d1 d2 f :
        valid f -> um_foldl a z0 d1 f = um_foldl a z0 d2 f.
Proof.
move: f z0; elim/um_indf=>[z0|z0|k v f IH W /(order_path_min (@trans K)) P z0 _];
by rewrite ?valid_undef ?umfoldl0 // !umfoldlPtUn // IH // (validR W).
Qed.

Lemma umfoldl_ind (P : R -> Prop) a z0 d f :
        valid f -> P z0 ->
        (forall z0 k v, (k, v) \In f -> P z0 -> P (a z0 k v)) ->
        P (um_foldl a z0 d f).
Proof.
move=>W H1 H2; elim/um_indf: f z0 W H1 H2=>[||k v f IH W O] z0;
rewrite ?valid_undef ?umfoldl0 // => _ H1 H2; rewrite umfoldlPtUn //;
last by apply: order_path_min O; apply: trans.
apply: IH (validR W) _ _; first by apply: H2 (InPtUnL W) H1.
by move=>z1 k0 v0 F; apply: H2 (InR W F).
Qed.

Lemma umfoldr_ind (P : R -> Prop) a z0 d f :
        valid f -> P z0 ->
        (forall z0 k v, (k, v) \In f -> P z0 -> P (a k v z0)) ->
        P (um_foldr a z0 d f).
Proof.
move=>W H1 H2; elim/um_indb: f z0 W H1 H2=>[||k v f IH W /allP O] z0;
rewrite ?valid_undef ?umfoldr0 // => _ H1 H2.
rewrite joinC umfoldrUnPt //; rewrite joinC in W.
apply: IH (validR W) _ _; first by apply: H2 (InPtUnL W) H1.
by move=>z1 k0 v0 F; apply: H2 (InR W F).
Qed.

End FoldDefAndLemmas.

Section PCMFold.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map_class C V).
Variables (R : pcm) (a : R -> K -> V -> R).
Hypothesis frame : forall x y k v, a (x \+ y) k v = a x k v \+ y.

Lemma umfoldl0_frame z0 d (f : U) :
        valid f -> um_foldl a z0 d f = um_foldl a Unit d f \+ z0.
Proof.
move=>W; elim/um_indf: f W d z0
  =>[||k v f IH _ /(order_path_min (@trans K)) P] W d z0.
- by rewrite valid_undef in W.
- by rewrite !umfoldl0 unitL.
rewrite !umfoldlPtUn // IH 1?[in X in _ = X]IH ?(validR W) //.
by rewrite -joinA -frame unitL.
Qed.

Lemma umfoldlUn_frame z0 d (f1 f2 : U) :
        valid (f1 \+ f2) ->
        um_foldl a z0 d (f1 \+ f2) =
        um_foldl a Unit d f1 \+ um_foldl a Unit d f2 \+ z0.
Proof.
move=>W; rewrite /um_foldl W (validL W) (validR W).
set b := fun z kv => _.
have X x y kv : b (x \+ y) kv = b x kv \+ y by rewrite /b frame.
rewrite (foldl_perm X _ (assocs_perm W)).
rewrite foldl_cat -{1}[z0]unitL (foldl_init X).
rewrite (foldl_init X) -{1}[foldl b _ (assocs f1)]unitL.
by rewrite (foldl_init X) -!joinA joinCA.
Qed.

End PCMFold.

(* Special notation for boolean predicates over K*V *)

Notation "[ 'pts' k v | E ]" :=
 (fun kv => let '(k, v) := kv in E%B)
 (at level 0, k ident, v ident, format "[ 'pts'  k  v  |  E ]").
Notation "[ 'pts' k ( v : V ) | E ]" :=
 (fun kv : _*V =>let '(k, v) := kv in E%B)
 (at level 0, k ident, v ident, only parsing).
Notation "[ 'pts' ( k : K ) v | E ]" :=
 (fun kv : K*_ => let '(k, v) := kv in E%B)
 (at level 0, k ident, v ident, only parsing).
Notation "[ 'pts' ( k : K ) ( v : V ) | E ]" :=
 (fun kv : K*V => let '(k, v) := kv in E%B)
 (at level 0, k ident, v ident, only parsing).


(********)
(* omap *)
(********)

(* Combines map and filter by having the filtering function *)
(* return an option *)

Section OMapDefLemmas.
Variables (K : ordType) (C : pred K) (V V' : Type).
Variables (U : union_map_class C V) (U' : union_map_class C V').
Implicit Types (f : U).

Definition omap (a : K * V -> option V') f : U' :=
  if valid f then
    foldl (fun z kv => if a kv is Some v' then z \+ pts kv.1 v' else z)
          Unit (assocs f)
  else undef.

Lemma omap_undef a : omap a undef = undef.
Proof. by rewrite /omap valid_undef. Qed.

Lemma omap0 a : omap a Unit = Unit.
Proof. by rewrite /omap valid_unit assocs0. Qed.

Lemma omapPt a k v :
        omap a (pts k v) =
        if C k then
          if a (k, v) is Some w then pts k w else Unit
        else undef.
Proof.
rewrite /omap validPt assocsPt; case C': (C k)=>//=.
by case: (a (k, v))=>// x; rewrite unitL.
Qed.

Lemma omapUn a f1 f2 :
        valid (f1 \+ f2) ->
        omap a (f1 \+ f2) = omap a f1 \+ omap a f2.
Proof.
move=>W; rewrite /omap W (validL W) (validR W); set b := fun z kv => _.
have H x y kv : b (x \+ y) kv = b x kv \+ y.
- by rewrite /b; case: (a kv)=>// z; rewrite joinAC.
rewrite (foldl_perm H _ (assocs_perm W)) foldl_cat.
by rewrite joinC -(foldl_init H) unitL.
Qed.

Lemma omapPtUn a k v f :
        omap a (pts k v \+ f) =
        if valid (pts k v \+ f) then
          if a (k, v) is Some v' then pts k v' \+ omap a f else omap a f
        else undef.
Proof.
case: ifP=>X; last first.
- by move/invalidE: (negbT X)=>->; rewrite omap_undef.
rewrite omapUn // omapPt (validPtUn_cond X).
by case: (a _)=>//; rewrite unitL.
Qed.

Lemma omapUnPt a k v f :
        omap a (f \+ pts k v) =
        if valid (f \+ pts k v) then
          if a (k, v) is Some v' then omap a f \+ pts k v' else omap a f
        else undef.
Proof.
rewrite joinC omapPtUn; case: ifP=>// W.
by case: (a _)=>// x; rewrite joinC.
Qed.

Lemma eq_in_omap a1 a2 f :
        (forall kv, kv \In f -> a1 kv = a2 kv) ->
        omap a1 f = omap a2 f.
Proof.
elim/um_indf: f=>[||k v f IH W P H]; rewrite ?omap_undef ?omap0 //.
rewrite !omapPtUn W; move/H: (InPtUnL W)=>->.
by case E2: (a2 _)=>[b2|]; (rewrite IH; last by move=>kv /(InR W)/H).
Qed.

Lemma dom_omap_sub a f : {subset dom (omap a f) <= dom f}.
Proof.
elim/um_indf: f=>[||k v f IH W P] x.
- by rewrite omap_undef dom_undef.
- by rewrite omap0 dom0.
rewrite omapPtUn W domPtUn W !inE /=.
case E : (a _)=>[b|]; last by move/IH=>->; rewrite orbT.
rewrite domPtUn inE; case/andP=>W2.
by case/orP=>[->//|/IH ->]; rewrite orbT.
Qed.

Lemma valid_omap a f : valid (omap a f) = valid f.
Proof.
elim/um_indf: f=>[||k v f IH W P].
- by rewrite omap_undef !valid_undef.
- by rewrite omap0 !valid_unit.
rewrite omapPtUn W; case X : (a _)=>[b|]; last by rewrite IH (validR W).
rewrite validPtUn (validPtUn_cond W) IH (validR W).
by apply: contra (notin_path P); apply: dom_omap_sub.
Qed.

Lemma In_omap_raw a k v f :
        (k, v) \In omap a f <->
        exists w, [/\ C k, valid (omap a f),
                      (k, w) \In f & a (k, w) = Some v].
Proof.
elim/um_indf: f k v=>[||x w f IH W P] k v.
- by rewrite omap_undef; split=>[/In_undef|[w][]] //; rewrite valid_undef.
- by rewrite omap0; split=>[/In0|[w][??] /In0].
split=>[H|[w1][C' V1 H E]].
- move: (dom_valid (In_dom H)); rewrite omapPtUn W in H *.
  case E: (a (x, w)) H=>[z|] H W1; last first.
  - by case/IH: H=>w1 []; exists w1; split=>//; apply/InR.
  move: H; rewrite InPtUnE //.
  case; first by case=>->->; exists w; rewrite (validPtUn_cond W1).
  by case/IH=>w1 []; exists w1; split=>//; apply/InR.
rewrite omapPtUn W in V1 *; move/(InPtUnE _ W): H=>H.
case: H E V1; first by case=>->->-> V1; apply/InPtUnE=>//; left.
case: (a (x, w))=>[b|] H E V1; last by apply/IH; exists w1.
by rewrite InPtUnE //; right; apply/IH; exists w1; rewrite (validR V1).
Qed.

Lemma In_omapX a k v f :
        (k, v) \In omap a f <->
        exists2 w, (k, w) \In f & a (k, w) = Some v.
Proof.
rewrite In_omap_raw; split; first by case=>w []; exists w.
case=>w H X; exists w; split=>//.
- by move/In_dom/dom_cond: H.
by rewrite valid_omap //; move/In_dom/dom_valid: H.
Qed.

Lemma In_omap a k v w f :
        (k, w) \In f -> a (k, w) = Some v ->
        (k, v) \In omap a f.
Proof. by move=>H1 H2; apply/In_omapX=>//; exists w. Qed.

Lemma In_dom_omap a k f :
        reflect (exists v w, (k, w) \In f /\ a (k, w) = Some v)
                (k \in dom (omap a f)).
Proof.
case: In_domX=>H; constructor.
- by case: H=>v /In_omapX [w H1 H2]; exists v, w.
by case=>v [w][X /(In_omap X) Y]; elim: H; exists v.
Qed.

(* if the map is total, we have some stronger lemmas *)
Lemma dom_omap_some a f :
        (forall x, x \In f -> oapp predT false (a x)) -> dom (omap a f) = dom f.
Proof.
move=>H; apply/domE=>k; apply/idP/idP=>/In_domX [w].
- by case/In_omapX=>// v /In_dom.
case A : (a (k, w)) {H} (H (k, w))=>[v|] // H1 H2; last by move/H1: H2.
suff : (k, v) \In omap a f by apply: In_dom.
by apply/In_omapX=>//; exists w.
Qed.

(* if the map is total on f1, f2, don't need validity condition for union *)
Lemma omapUn_some a f1 f2 :
        (forall x, x \In f1 -> oapp predT false (a x)) ->
        (forall x, x \In f2 -> oapp predT false (a x)) ->
        omap a (f1 \+ f2) = omap a f1 \+ omap a f2.
Proof.
move=>H1 H2; have Ev : valid (omap a f1 \+ omap a f2) = valid (f1 \+ f2).
- by rewrite !validUnAE !valid_omap // !dom_omap_some.
case W : (valid (f1 \+ f2)); first by rewrite omapUn.
move: W (W); rewrite -{1}Ev=>/negbT/invalidE -> /negbT/invalidE ->.
by rewrite omap_undef.
Qed.

Lemma path_omap a f x : path ord x (dom f) -> path ord x (dom (omap a f)).
Proof.
apply: subseq_order_path; first by apply: trans.
apply: (sorted_subset_subseq (leT := ord)); last by apply: dom_omap_sub.
- by apply: irr.
- by apply: trans.
- by apply: sorted_dom.
by apply: sorted_dom.
Qed.

Lemma omap_predU (a1 a2 : K*V -> option V') f :
        (forall kv, a1 kv = None \/ a2 kv = None) ->
        omap a1 f \+ omap a2 f =
        omap (fun kv => if a1 kv is Some v' then Some v'
                        else if a2 kv is Some v' then Some v'
                        else None) f.
Proof.
move=>E; elim/um_indf: f=>[||k v f IH W /(order_path_min (@trans K)) P].
- by rewrite !omap_undef undef_join.
- by rewrite !omap0 unitL.
rewrite !omapPtUn W /= -IH.
case E1 : (a1 (k, v))=>[b1|]; case E2 : (a2 (k, v))=>[b2|] //.
- by move: (E (k, v)); rewrite E1 E2; case.
- by rewrite joinA.
by rewrite joinCA.
Qed.

Lemma domeq2_omap (a : K*V -> option V') f :
        (forall kv, kv \In f -> isSome (a kv)) ->
        dom_eq2 (omap a f) f.
Proof.
move=>H; rewrite /dom_eq2 valid_omap // eq_refl /=.
apply/eqP; apply: eq_sorted_ord=>// k.
apply/idP/idP; first by case/In_dom_omap=>// x [w][] /In_dom.
case/In_domX=>x X; apply/In_dom_omap=>//.
by case F : (a (k, x)) (H _ X)=>[v|] //; exists v, x.
Qed.

Lemma dom_omapUn (a : K*V -> option V') f1 f2 :
        dom (omap a (f1 \+ f2)) =i
          [pred x | valid (f1 \+ f2) &
                    (x \in dom (omap a f1)) || (x \in dom (omap a f2))].
Proof.
move=>x; case W: (valid (f1 \+ f2)); last first.
- by move/negbT/invalidE: W=>->; rewrite omap_undef dom_undef.
by rewrite omapUn // domUn !inE -omapUn // valid_omap // W.
Qed.

Lemma In_range_omapUn (a : K*V -> option V') f1 f2 x :
        x \In range (omap a (f1 \+ f2)) <->
        valid (f1 \+ f2) /\ (x \In range (omap a f1) \/ x \In range (omap a f2)).
Proof.
split.
- case W : (valid (f1 \+ f2)); first by rewrite omapUn // => /In_rangeUn.
  by move/negbT/invalidE: W=>->; rewrite omap_undef range_undef.
case=>W H; rewrite omapUn //; case: H=>H.
- by apply: In_rangeL H; rewrite -omapUn // valid_omap.
by apply: In_rangeR H; rewrite -omapUn // valid_omap.
Qed.

Lemma omap_morph_ax a : morph_axiom (@sepT _) (omap a).
Proof.
split=>[|x y W _]; first by rewrite omap0.
by rewrite -omapUn // valid_omap.
Qed.

Canonical omap_morph a := Morphism' (omap a) (omap_morph_ax a).

Lemma valid_omapPtUn a k v f :
        [&& C k, valid f & k \notin dom f] ->
        valid (pts k v \+ omap a f).
Proof.
move/and3P => [H1 H2 H3].
rewrite validPtUn H1 valid_omap // H2 /=.
by apply: contra H3; apply: dom_omap_sub.
Qed.

Lemma valid_omapUnPt a k v f :
        [&& C k, valid f & k \notin dom f] ->
        valid (omap a f \+ pts k v).
Proof. by move=>H; rewrite joinC; apply: valid_omapPtUn. Qed.

Lemma valid_omapUn a1 a2 f1 f2 :
        valid (f1 \+ f2) -> valid (omap a1 f1 \+ omap a2 f2).
Proof.
move=>W; rewrite validUnAE !valid_omap // (validL W) (validR W) /=.
apply/allP=>z /In_dom_omap [] //= x1 [w1][/In_dom /= D1 _].
apply/negP=>/In_dom_omap [] //= x2 [w2][/In_dom /=].
by move/(dom_inNR W)/negbTE: D1=>->.
Qed.

Lemma find_omap a k f :
        find k (omap a f) =
        if find k f is Some v then a (k, v) else None.
Proof.
case E1 : (find k (omap a f))=>[b|].
- by move/In_find: E1=>/In_omapX [] // x /In_find ->.
move/find_none/negP: E1=>E1.
case E2 : (find k f)=>[c|] //; move/In_find: E2=>E2.
case E3: (a (k, c))=>[d|] //; elim: E1.
by apply/In_dom_omap=>//; exists d, c.
Qed.

End OMapDefLemmas.

Arguments omap [K C V V' U U'].
Arguments dom_omap_sub [K C V V' U U' a f] _.
Prenex Implicits dom_omap_sub.

Section OmapComp.
Variables (K : ordType) (C : pred K) (V1 V2 V3 : Type).
Variables (U1 : union_map_class C V1).
Variables (U2 : union_map_class C V2).
Variables (U3 : union_map_class C V3).
Variables (a1 : K * V1 -> option V2) (a2 : K * V2 -> option V3).

Lemma omap_comp (f : U1) :
        omap a2 (omap a1 f : U2) =
        omap (fun x => obind (fun v => a2 (x.1, v)) (a1 x)) f :> U3.
Proof.
elim/um_indf: f=>[||k v f IH W P]; rewrite ?omap_undef ?omap0 //.
rewrite !omapPtUn W; case: (a1 (k, v))=>[w|//].
rewrite omapPtUn validPtUn (validPtUn_cond W) valid_omap // (validR W) IH.
by rewrite (contra _ (validPtUnD W)) //; apply: dom_omap_sub.
Qed.

End OmapComp.

(* special notation for some common variants of omap *)

(* when we don't supply the key *)
Notation omapv f := (omap (f \o snd)).
(* when the don't supply the key and the map is total *)
Notation mapv f := (omapv (Some \o f)).

Section OmapvLemmas.
Variables (K : ordType) (C : pred K) (V : Type).
Variables (U : union_map_class C V).

Variables (V1 V2 V3 : Type).
Variables (U1 : union_map_class C V1).
Variables (U2 : union_map_class C V2).
Variables (U3 : union_map_class C V3).
Variables (a1 : V1 -> option V2) (a2 : V2 -> option V3).

Lemma omapv_comp (f : U1) :
        omapv a2 (omapv a1 f : U2) = omapv (obind a2 \o a1) f :> U3.
Proof. by apply: omap_comp. Qed.

End OmapvLemmas.

Section MapvLemmas.
Variables (K : ordType) (C : pred K) (V : Type).
Variables (U : union_map_class C V).

Lemma mapv_id (f : U) : mapv id f = f.
Proof.
elim/um_indf: f=>[||k v f IH W P].
- by rewrite omap_undef.
- by rewrite omap0.
by rewrite omapPtUn W /= IH.
Qed.

(* A bit of a nicer-looking statements can be given for total maps. *)
(* It's the same theorem as omap_comp, but avoids obinds. *)

Variables (V1 V2 V3 : Type).
Variables (U1 : union_map_class C V1).
Variables (U2 : union_map_class C V2).
Variables (U3 : union_map_class C V3).
Variables (a1 : V1 -> V2) (a2 : V2 -> option V3).

Lemma mapv_comp (f : U1) : omapv a2 (mapv a1 f : U2) = omapv (a2 \o a1) f :> U3.
Proof. by apply: omap_comp. Qed.

Lemma In_mapv (f : U1) k x :
        injective a1 -> (k, a1 x) \In (mapv a1 f : U2) <-> (k, x) \In f.
Proof.
by move=>G; rewrite In_omapX //=; split; [case=>w H [] /G <-| exists x].
Qed.

End MapvLemmas.


Section OmapFreeUpd.
Variables (K : ordType) (C : pred K) (V V' : Type).
Variables (U : union_map_class C V) (U' : union_map_class C V').
Variables (a : K * V -> option V').

Lemma omapFE k (f : U) :
        free f k = omap (fun kv => if kv.1 == k then None else Some kv.2) f.
Proof.
case W : (valid f); last first.
- by move/negbT/invalidE: W=>->; rewrite free_undef omap_undef.
apply: umem_eq.
- by rewrite validF.
- by rewrite valid_omap.
case=>x w; rewrite InF In_omapX /= validF W; split.
- by case=>_ /negbTE ->; exists w.
by case=>w' H; case: eqP=>// N [<-].
Qed.

Lemma omapF k (f : U) :
        omap a (free f k) = free (omap a f) k :> U'.
Proof.
case W : (valid f); last first.
- by move/negbT/invalidE: W=>->; rewrite free_undef omap_undef free_undef.
apply: umem_eq.
- by rewrite valid_omap // validF.
- by rewrite validF valid_omap.
case=>x v; split.
- case/In_omapX=>v' /InF /= [_ N M E].
  apply/InF; rewrite validF valid_omap //=; split=>//.
  by apply/In_omapX; exists v'.
case/InF=>/= _ N /In_omapX [v'] M E.
by apply/In_omapX; exists v'=>//; apply/InF; rewrite validF.
Qed.

Lemma omapU k (v : V) (f : U) :
        omap a (upd k v f) =
        if C k then
          if a (k, v) is Some v' then upd k v' (omap a f)
          else free (omap a f) k : U'
        else undef.
Proof.
case: ifP=>// W; last first.
- have: ~~ valid (upd k v f) by rewrite validU W.
  by move/invalidE=>->; apply omap_undef.
case H: (valid f); last first.
- move: H; move/negbT/invalidE=>->; rewrite upd_undef omap_undef free_undef.
  by case: (a (k, v)) =>// a0; rewrite upd_undef.
rewrite upd_eta // omapPtUn validPtUn W validF H domF inE eq_refl /=.
case E: (a (k, v))=>[xa|]; last by rewrite omapF.
by rewrite upd_eta omapF.
Qed.

End OmapFreeUpd.

(* Other extra lemmas on omap that require different U's *)

Section OmapExtras.
Variables (K : ordType) (C : pred K) (V V' : Type).
Variables (U : union_map_class C V) (U' : union_map_class C V').

Lemma omap_some (a : K * V -> option V) (f : U) :
        (forall kv, kv \In f -> a kv = Some kv.2) ->
        omap a f = f.
Proof. by move/eq_in_omap=>->; apply: mapv_id. Qed.

Lemma omap_none (a : K * V -> option V') (f : U) :
        valid f ->
        (forall kv, kv \In f -> a kv = None) ->
        omap a f = Unit :> U'.
Proof.
move=>W /eq_in_omap ->.
elim/um_indf: f W=>[||k v f IH W P]; rewrite ?valid_undef ?omap0 // => _.
by rewrite omapPtUn W IH // (validR W).
Qed.

Lemma omap_noneR (a : K * V -> option V') (f : U) :
        omap a f = Unit :> U' -> forall kv, kv \In f -> a kv = None.
Proof.
elim/um_indf: f=>[H|H|k v f IH W P O] kv.
- by move/In_undef.
- by move/In0.
move: O; rewrite omapPtUn W.
case E: (a (k, v)).
- by move=>/unitbP; rewrite um_unitbPtUn.
move=>O /InUn [/InPt [->]|] //.
by apply: IH =>//; move: W; rewrite validPtUn; case/and3P.
Qed.

End OmapExtras.


(*************)
(* um_filter *)
(*************)

(* filter that works over both domain and range at once *)

Section FilterDefLemmas.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map_class C V).
Implicit Type f : U.
Implicit Type p q : pred (K * V).

Definition um_filter p f : U :=
  omap (fun kv => if p kv then Some kv.2 else None) f.

Lemma umfilt0 p : um_filter p Unit = Unit.
Proof. by rewrite /um_filter omap0. Qed.

Lemma umfilt_undef p : um_filter p undef = undef.
Proof. by rewrite /um_filter omap_undef. Qed.

Lemma umfiltPt p k v :
        um_filter p (pts k v) =
        if C k then
          if p (k, v) then pts k v else Unit
       else undef.
Proof. by rewrite /um_filter omapPt; case: (ifP (p (k, v))). Qed.

Lemma umfiltUn p f1 f2 :
        valid (f1 \+ f2) ->
        um_filter p (f1 \+ f2) = um_filter p f1 \+ um_filter p f2.
Proof. by move=>W; rewrite /um_filter omapUn. Qed.

Lemma umfiltPtUn p k v f :
        um_filter p (pts k v \+ f) =
        if valid (pts k v \+ f) then
          if p (k, v) then pts k v \+ um_filter p f else um_filter p f
        else undef.
Proof. by rewrite /um_filter omapPtUn; case: (ifP (p (k, v))). Qed.

Lemma umfiltUnPt p k v f :
        um_filter p (f \+ pts k v) =
        if valid (f \+ pts k v) then
          if p (k, v) then um_filter p f \+ pts k v else um_filter p f
        else undef.
Proof. by rewrite /um_filter omapUnPt; case: (ifP (p (k, v))). Qed.

Lemma dom_umfilt_subset p f :
        {subset dom (um_filter p f) <= dom f}.
Proof. by rewrite /um_filter; apply: dom_omap_sub. Qed.

Lemma valid_umfilt p f : valid (um_filter p f) = valid f.
Proof. by rewrite /um_filter valid_omap. Qed.

Lemma In_umfilt x p f : x \In um_filter p f <-> p x /\ x \In f.
Proof.
case: x => k v; rewrite In_omapX; split=>[[w H]|[I H]].
- by case E: (p (k, w))=>//=; case=><-.
by exists v=>//; rewrite I.
Qed.

Lemma dom_umfilt p f k :
        reflect (exists v, [/\ p (k, v) & (k, v) \In f])
                (k \in dom (um_filter p f)).
Proof.
case: In_domX=>H; constructor.
- by case: H=>v /In_umfilt []; exists v.
by case=>v [Hp Hf]; elim: H; exists v; apply/In_umfilt.
Qed.

Lemma valid_umfiltUnL f1 f2 p :
        valid (f1 \+ f2) -> valid (um_filter p f1 \+ f2).
Proof.
move=>VH; case: validUn=>//; rewrite ?valid_umfilt ?(validL VH) ?(validR VH) //.
by move=>k /dom_umfilt [v1][_ /In_dom] /(dom_inNL VH) /negbTE ->.
Qed.

Lemma valid_umfiltUnR f1 f2 p :
        valid (f1 \+ f2) -> valid (f1 \+ um_filter p f2).
Proof. by rewrite !(joinC f1); apply: valid_umfiltUnL. Qed.

Lemma valid_umfiltUn p1 p2 f1 f2 :
        valid (f1 \+ f2) -> valid (um_filter p1 f1 \+ um_filter p2 f2).
Proof. by move=>W; apply: valid_umfiltUnL (valid_umfiltUnR _ W). Qed.

Lemma dom_umfiltE p f :
        dom (um_filter p f) =
        filter (fun k => if find k f is Some v then p (k, v) else false)
               (dom f).
Proof.
apply: (@eq_sorted_irr _ ord); [apply: trans|apply: irr|apply: sorted_dom| | ].
- by apply: sorted_filter; [apply: trans | apply: sorted_dom].
move=>k; rewrite mem_filter; apply/idP/idP.
- by case/dom_umfilt=>w [H1 H2]; move/In_find: H2 (H2) H1=>-> /In_dom ->->.
case X: (find k f)=>[v|] // /andP [H1 _]; move/In_find: X=>H2.
by apply/dom_umfilt; exists v.
Qed.

Lemma umfilt_pred0 f : valid f -> um_filter pred0 f = Unit.
Proof. by move=>W; apply: omap_none. Qed.

Lemma umfilt_predT f : um_filter predT f = f.
Proof. by apply: omap_some. Qed.

Lemma umfilt_predI p1 p2 f :
        um_filter (predI p1 p2) f = um_filter p1 (um_filter p2 f).
Proof.
rewrite /um_filter omap_comp; apply: eq_in_omap; case=>k v H /=.
by case: (ifP (p2 (k, v))); rewrite ?andbT ?andbF.
Qed.

Lemma eq_in_umfilt p1 p2 f :
        (forall kv, kv \In f -> p1 kv = p2 kv) <->
        um_filter p1 f = um_filter p2 f.
Proof.
split.
- by move=> H; apply /eq_in_omap => kv In; rewrite H.
move=>H x [W][z E]; subst f.
rewrite !umfiltPtUn W -prod_eta in H.
case: ifP H; case: ifP=>// H1 H2 E.
- have: x.1 \in dom (um_filter p2 z).
  - by rewrite -E domPtUn inE E eq_refl valid_umfilt (validR W).
  by move/dom_umfilt_subset; rewrite (negbTE (validPtUnD W)).
have: x.1 \in dom (um_filter p1 z).
- by rewrite E domPtUn inE -E eq_refl valid_umfilt (validR W).
by move/dom_umfilt_subset; rewrite (negbTE (validPtUnD W)).
Qed.

Lemma eq_in_umfiltI p1 p2 f :
        (forall kv, kv \In f -> p1 kv = p2 kv) ->
        um_filter p1 f = um_filter p2 f.
Proof. by move/eq_in_umfilt. Qed.

(* common use omits the localization part *)
Lemma eq_in_umfiltE p1 p2 f :
        p1 =1 p2 -> um_filter p1 f = um_filter p2 f.
Proof. by move=>S; apply/eq_in_umfilt=>kv _; apply: S. Qed.

Lemma umfiltC p1 p2 f :
        um_filter p1 (um_filter p2 f) = um_filter p2 (um_filter p1 f).
Proof.
by rewrite -!umfilt_predI; apply: eq_in_umfiltE=>x /=; rewrite andbC.
Qed.

Lemma umfilt_predU p1 p2 f :
        um_filter (predU p1 p2) f =
        um_filter p1 f \+ um_filter (predD p2 p1) f.
Proof.
rewrite /um_filter omap_predU /=.
- apply /eq_in_omap; case=> k v H /=.
  by case: (p1 (k, v))=>/=; case: (p2 (k, v))=>/=.
by case=> k v; case: (p1 (k, v))=>/=; [right|left].
Qed.

Lemma umfilt_predD p1 p2 f :
        subpred p1 p2 ->
        um_filter p2 f = um_filter p1 f \+ um_filter (predD p2 p1) f.
Proof.
move=>S; rewrite -umfilt_predU -eq_in_umfilt=>kv _ /=.
by case E: (p1 _)=>//; apply: S E.
Qed.

Lemma umfilt_dpredU f p q :
        subpred p (predC q) ->
        um_filter (predU p q) f = um_filter p f \+ um_filter q f.
Proof.
move=>D; rewrite umfilt_predU.
suff : forall kv, kv \In f -> predD q p kv = q kv by move/eq_in_umfilt=>->.
by move=>kv _ /=; case X: (p _)=>//=; move/D/negbTE: X.
Qed.

Lemma umfiltUnK p f1 f2 :
        valid (f1 \+ f2) ->
        um_filter p (f1 \+ f2) = f1 ->
        um_filter p f1 = f1 /\ um_filter p f2 = Unit.
Proof.
move=>V'; rewrite (umfiltUn _ V') => E.
have W' : valid (um_filter p f1 \+ um_filter p f2).
- by rewrite E; move/validL: V'.
have F : dom (um_filter p f1) =i dom f1.
- move=>x; apply/idP/idP; first by apply: dom_umfilt_subset.
  move=>D; move: (D); rewrite -{1}E domUn inE W' /=.
  by case/orP=>// /dom_umfilt_subset; case: validUn V'=>// _ _ /(_ _ D) /negbTE ->.
rewrite -{2}[f1]unitR in E F; move/(dom_prec W' E): F=>X.
by rewrite X in E W' *; rewrite (joinxK W' E).
Qed.

Lemma umfiltU p k v f :
        um_filter p (upd k v f) =
        if C k then
           if p (k, v) then upd k v (um_filter p f)
           else free (um_filter p f) k
        else undef.
Proof. by rewrite /um_filter omapU //; case: (p (k, v)). Qed.

Lemma umfiltF p k f : um_filter p (free f k) = free (um_filter p f) k.
Proof. by rewrite /um_filter omapF. Qed.

Lemma umfilt_morph_ax p : morph_axiom (@sepT _) (um_filter p).
Proof. by rewrite /um_filter; apply: omap_morph_ax. Qed.

Canonical umfilt_morph p :=
  Eval hnf in Morphism' (um_filter p) (umfilt_morph_ax p).

Lemma umfoldl_umfilt R (a : R -> K -> V -> R) (p : pred (K * V)) f z0 d:
        um_foldl a z0 d (um_filter p f) =
        um_foldl (fun r k v => if p (k, v) then a r k v else r) z0 d f.
Proof.
move: f z0; elim/um_indf=>[||k v f IH W P] z0 /=.
- by rewrite !umfilt_undef !umfoldl_undef.
- by rewrite !umfilt0 !umfoldl0.
have V1 : all (ord k) (dom f) by apply/allP=>x; apply: path_mem (@trans K) P.
have V2 : all (ord k) (dom (um_filter p f)).
- apply/allP=>x /dom_umfilt [w][_] /In_dom.
  by apply: path_mem (@trans K) P.
have : valid (um_filter p (pts k v \+ f)) by rewrite valid_umfilt W.
by rewrite !umfiltPtUn W; case: ifP=>E V3; rewrite !umfoldlPtUn // E IH.
Qed.

Lemma umfilt_mem0 p f :
        um_filter p f = Unit -> forall k v, (k, v) \In f -> ~~ p (k, v).
Proof.
rewrite /um_filter => H k v I.
have: ((if p (k, v) then Some v else None) = None).
- by apply: (omap_noneR H).
by case: (p (k, v)).
Qed.

Lemma umfilt_mem0L p f :
        valid f -> (forall k v, (k, v) \In f -> ~~ p (k, v)) ->
        um_filter p f = Unit.
Proof.
rewrite /um_filter => VF H.
apply: omap_none => //.
by case=> k v I; rewrite (negbTE (H k v I)).
Qed.

Lemma umfilt_idemp p f :
        um_filter p (um_filter p f) = um_filter p f.
Proof.
rewrite -umfilt_predI; apply/eq_in_umfilt.
by case=>k v H /=; rewrite andbb.
Qed.

Lemma assocs_umfilt p f :
        assocs (um_filter p f) = filter p (assocs f).
Proof.
elim/um_indf: f=>[||k v f IH W /(order_path_min (@trans K)) P].
- by rewrite umfilt_undef assocs_undef.
- by rewrite umfilt0 assocs0.
rewrite umfiltPtUn W assocsPtUn //=.
case: ifP W=>// H W; rewrite assocsPtUn; first by rewrite IH.
- suff: valid (um_filter p (pts k v \+ f)) by rewrite umfiltPtUn W H.
  by rewrite valid_umfilt.
by apply/allP=>x; move/allP: P=>P; move/dom_umfilt_subset/P.
Qed.

Lemma find_umfilt k p f :
       find k (um_filter p f) =
       if find k f is Some v then
         if p (k, v) then Some v else None
       else None.
Proof.
elim/um_indf: f k=>[||k' v f IH W /(order_path_min (@trans K)) P] k.
- by rewrite umfilt_undef find_undef.
- by rewrite umfilt0 find0E.
have W' : valid (pts k' v \+ um_filter p f).
- rewrite validPtUn (validPtUn_cond W)valid_umfilt (validR W).
  by apply: contra (validPtUnD W)=>/dom_umfilt [x][_] /In_dom.
rewrite umfiltPtUn W; case: ifP=>E; rewrite !findPtUn2 //;
case: eqP=>// ->; rewrite E // IH.
by move/validPtUnD: W; case: dom_find=>// ->.
Qed.

Lemma unitb_umfilt p f : unitb f -> unitb (um_filter p f).
Proof. by move/unitbE->; rewrite umfilt0 unitb0. Qed.

(* filter p x is lower bound for x *)
Lemma umfilt_pleqI x p : [pcm um_filter p x <= x].
Proof.
exists (um_filter (predD predT p) x); rewrite -umfilt_predU.
by rewrite -{1}[x]umfilt_predT; apply/eq_in_umfilt=>a; rewrite /= orbT.
Qed.

Hint Resolve umfilt_pleqI : core.

End FilterDefLemmas.

Hint Extern 0 [pcm um_filter _ ?X <= ?X] =>
  apply: umfilt_pleqI : core.

Notation um_filterk p f := (um_filter (p \o fst) f).
Notation um_filterv p f := (um_filter (p \o snd) f).

Section FilterKLemmas.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map_class C V).
Implicit Type f : U.
Implicit Type p q : pred K.

Lemma dom_umfiltk_filter p f : dom (um_filterk p f) = filter p (dom f).
Proof.
apply: (@eq_sorted_irr _ ord).
- by apply: trans.
- by apply: irr.
- by apply: sorted_dom.
- by apply: sorted_filter; [apply: trans | apply: sorted_dom].
move=>k; rewrite mem_filter; apply/idP/idP.
- by case/dom_umfilt=>v [/= -> /In_dom].
by case/andP=>H1 /In_domX [v H2]; apply/dom_umfilt; exists v.
Qed.

Lemma dom_umfiltk p f : dom (um_filterk p f) =i predI p (mem (dom f)).
Proof. by move=>k; rewrite dom_umfiltk_filter mem_filter. Qed.

Lemma umfiltk_dom f1 f2 :
        valid (f1 \+ f2) -> um_filterk (mem (dom f1)) (f1 \+ f2) = f1.
Proof.
move=>W; apply/umem_eq; first by rewrite valid_umfilt.
- by rewrite (validL W).
case=>k v; rewrite In_umfilt; split=>[|H].
- by case=>H /InUn [] // /In_dom; rewrite (negbTE (dom_inNL W H)).
by split; [apply: In_dom H | apply: InL].
Qed.

Lemma eq_in_umfiltk p1 p2 f :
        {in dom f, p1 =1 p2} -> um_filterk p1 f = um_filterk p2 f.
Proof. by move=>H; apply/eq_in_umfilt; case=>k v /In_dom; apply: H. Qed.

(* filter p x is lower bound for p *)
Lemma subdom_umfiltk p f : {subset dom (um_filterk p f) <= p}.
Proof. by move=>a; rewrite dom_umfiltk; case/andP. Qed.

Lemma subdom_umfiltkE p f : {subset dom f <= p} <-> um_filterk p f = f.
Proof.
split; last by move=><- a; rewrite dom_umfiltk; case/andP.
by move/eq_in_umfiltk=>->; rewrite umfilt_predT.
Qed.

(* specific consequence of subdom_umfiltkE *)
Lemma umfiltk_memdomE f : um_filterk (mem (dom f)) f = f.
Proof. by apply/subdom_umfiltkE. Qed.

Lemma find_umfiltk k (p : pred K) f :
        find k (um_filter (p \o fst) f) = if p k then find k f else None.
Proof. by rewrite find_umfilt /=; case: (find _ _)=>[a|]; case: ifP. Qed.

Lemma subdom_umfiltk0 p f :
        valid f -> {subset dom f <= predC p} <-> um_filterk p f = Unit.
Proof.
move=>W; split=>H.
- by rewrite (eq_in_umfiltk (p2:=pred0)) ?umfilt_pred0 // => a /H /negbTE ->.
move=>k X; case: dom_find X H=>// a _ -> _; rewrite umfiltU !inE /=.
case: (ifP (p k)) =>// _ /unitbE.
by case: ifP; [rewrite um_unitbU | rewrite unitb_undef].
Qed.

Lemma umfiltkPt p k v :
        um_filterk p (pts k v : U) =
        if p k then pts k v else if C k then Unit else undef.
Proof.
rewrite ptsU umfiltU umfilt0 free0 /=.
by case: ifP=>//; move/negbT=>N; rewrite upd_condN // if_same.
Qed.

Lemma umfiltkPtUn p k v f :
        um_filterk p (pts k v \+ f) =
        if valid (pts k v \+ f) then
          if p k then pts k v \+ um_filterk p f else um_filterk p f
        else undef.
Proof.
case: ifP=>X; last by move/invalidE: (negbT X)=>->; rewrite umfilt_undef.
rewrite umfiltUn // umfiltPt (validPtUn_cond X) /=.
by case: ifP=>//; rewrite unitL.
Qed.

Lemma umfiltk_preimUn (q : pred V) f1 f2 :
        valid (f1 \+ f2) ->
        um_filterk (um_preim q (f1 \+ f2)) f1 = um_filterk (um_preim q f1) f1.
Proof.
move=>v; apply: eq_in_umfiltk; move=>x xf1; rewrite umpreimUn // inE orbC.
have -> : um_preim q f2 x = false=>//.
by move: (dom_inNL v xf1); rewrite /um_preim; case: dom_find=>//->.
Qed.

Lemma umfiltk_omap V' (U' : union_map_class C V') a p f :
        omap a (um_filterk p f) = um_filterk p (omap a f) :> U'.
Proof.
rewrite /um_filter !omap_comp //= /obind/oapp /=.
by apply: eq_in_omap; case=>k v /=; case: ifP; case: a.
Qed.

Definition omap_umfiltk := umfiltk_omap.

Lemma umfiltkU p k v f :
        um_filterk p (upd k v f) =
        if p k then upd k v (um_filterk p f) else
          if C k then um_filterk p f else undef.
Proof.
rewrite umfiltU /=; case: ifP; case: ifP=>// Hp Hc.
- by apply: dom_free; rewrite dom_umfiltk inE Hp.
by rewrite upd_condN // Hc.
Qed.

Lemma umfiltkF p k f :
        um_filterk p (free f k) =
        if p k then free (um_filterk p f) k else um_filterk p f.
Proof.
rewrite umfiltF; case: ifP=>// N.
by rewrite dom_free // dom_umfiltk inE N.
Qed.

End FilterKLemmas.


Section FilterVLemmas.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map_class C V).
Implicit Type f : U.
Implicit Type p q : pred V.

Lemma eq_in_umfiltv (q1 q2 : pred V) f :
        (forall v, v \In range f -> q1 v = q2 v) ->
        um_filterv q1 f = um_filterv q2 f.
Proof. by move=>H; apply/eq_in_umfilt; case=>k v /In_range; apply: H. Qed.

Lemma umfiltv_predD (q1 q2 : pred V) f :
        subpred q1 q2 ->
        um_filterv q2 f = um_filterv q1 f \+ um_filterv (predD q2 q1) f.
Proof. by move=>H; apply: umfilt_predD; case. Qed.

End FilterVLemmas.


Section OmapMembershipLemmas.
Variables aT rT : Type.
Variables (K : ordType) (C : pred K) (Ua : union_map_class C aT) (Ur : union_map_class C rT).
Variables (f : rT -> option aT) (g : aT -> rT).

Lemma omapv_mapv (h : Ur) :
        ocancel f g ->
        mapv g (omapv f h : Ua) = um_filterv (isSome \o f) h.
Proof.
move=>O; rewrite /um_filter omap_comp //=.
apply: eq_in_omap; case=>k v H /=.
by case X : (f v)=>[a|] //=; rewrite -(O v) X.
Qed.

Lemma In_omapv (h : Ur) k x :
        ocancel f g -> pcancel g f ->
        (k, x) \In (omapv f h : Ua) <-> (k, g x) \In h.
Proof.
move=>O P; rewrite -(In_mapv Ur _ _ _ (pcan_inj P)).
by rewrite omapv_mapv // In_umfilt /= P; split=>//; case.
Qed.

Lemma In_rangev (h : Ur) (x : aT) :
        ocancel f g -> pcancel g f ->
        x \In range (omapv f h : Ua) <-> g x \In range h.
Proof.
move=>O P; rewrite !In_rangeX; split; case=>k H; exists k;
by [rewrite -In_omapv | rewrite In_omapv].
Qed.

End OmapMembershipLemmas.


Section OmapMembershipBool.
Variables aT rT : eqType.
Variables (K : ordType) (C : pred K) (Ua : union_map_class C aT) (Ur : union_map_class C rT).
Variables (f : rT -> option aT) (g : aT -> rT).

(* decidable version of In_rangev *)

Lemma mem_rangev (h : Ur) (x : aT) :
        ocancel f g -> pcancel g f ->
        x \in range (omapv f h : Ua) = (g x \in range h).
Proof.
by move=>O P; apply/idP/idP; move/mem_seqP/(In_rangev _ _ _ O P)/mem_seqP.
Qed.

End OmapMembershipBool.


(************************)
(* PCM-induced ordering *)
(************************)

(* Union maps and PCM ordering. *)

Section UmpleqLemmas.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map_class C V).
Implicit Types (x y a b : U) (p : pred K).

Lemma umpleq_undef x : [pcm x <= undef].
Proof. by exists undef; rewrite join_undef. Qed.

Hint Resolve umpleq_undef : core.

(* PCM-induced preorder, is an order in the case of union maps *)

Lemma umpleq_asym x y : [pcm x <= y] -> [pcm y <= x] -> x = y.
Proof.
case=>a -> [b]; case W : (valid x); last first.
- by move/invalidE: (negbT W)=>->; rewrite undef_join.
rewrite -{1 2}[x]unitR -joinA in W *.
by case/(joinxK W)/esym/join0E=>->; rewrite unitR.
Qed.

(* lemmas on the PCM ordering and um_filter(k) *)

Lemma umfilt_pleq_mono x y (p : pred (K * V)) :
        [pcm x <= y] -> [pcm um_filter p x <= um_filter p y].
Proof.
move=>H; case W : (valid y).
- by case: H W=>a -> W; rewrite umfiltUn //; eexists _.
by move/invalidE: (negbT W)=>->; rewrite umfilt_undef; apply: umpleq_undef.
Qed.

(* filter p f is largest lower bound for f and p *)
Lemma umpleq_filtk_meet a p f :
        {subset dom a <= p} -> [pcm a <= f] -> [pcm a <= um_filterk p f].
Proof. by move=>D /(umfilt_pleq_mono (p \o fst)); rewrite (eq_in_umfiltk D) umfilt_predT. Qed.

(* in valid case, we can define the order by means of filter *)
Lemma umpleqk_pleqE a x :
        valid x -> [pcm a <= x] <->
                   um_filterk (mem (dom a)) x = a.
Proof.
move=>W; split=>[|<-] // H; case: H W=>b ->.
by apply: umfiltk_dom.
Qed.

(* join is the least upper bound *)
Lemma umpleq_join a b f :
        valid (a \+ b) -> [pcm a <= f] -> [pcm b <= f] -> [pcm a \+ b <= f].
Proof.
case Vf: (valid f); last by move/invalidE: (negbT Vf)=>->; move: umpleq_undef.
move=>W /(umpleqk_pleqE _ Vf) <- /(umpleqk_pleqE _ Vf) <-.
rewrite -umfilt_dpredU //.
by case=>/= a0 _; move: a0; apply: valid_subdom W.
Qed.

(* x <= y and subdom *)
Lemma umpleq_subdom x y : valid y -> [pcm x <= y] -> {subset dom x <= dom y}.
Proof. by move=>W H; case: H W=>a -> W b D; rewrite domUn inE W D. Qed.

Lemma subdom_umpleq a (x y : U) :
        valid (x \+ y) -> [pcm a <= x \+ y] ->
        {subset dom a <= dom x} -> [pcm a <= x].
Proof.
move=>W H Sx; move: (umpleq_filtk_meet Sx H); rewrite umfiltUn //.
rewrite umfiltk_memdomE; move/subset_disjC: (valid_subdom W).
by move/(subdom_umfiltk0 _ (validR W))=>->; rewrite unitR.
Qed.

(* meet is the greatest lower bound *)
Lemma umpleq_meet a (x y1 y2 : U) :
        valid (x \+ y1 \+ y2) ->
        [pcm a <= x \+ y1] -> [pcm a <= x \+ y2] -> [pcm a <= x].
Proof.
rewrite um_valid3=> /and3P[V1 V12 V2] H1 H2.
apply: subdom_umpleq (V1) (H1) _ => k D.
move: {D} (umpleq_subdom V1 H1 D) (umpleq_subdom V2 H2 D).
rewrite !domUn !inE V1 V2 /=; case : (k \in dom x)=>//=.
by case: validUn V12=>// _ _ L _ /L /negbTE ->.
Qed.

(* some/none lemmas *)

Lemma umpleq_some x1 x2 t s :
        valid x2 -> [pcm x1 <= x2] -> find t x1 = Some s -> find t x2 = Some s.
Proof. by move=>W H; case: H W=>a -> W H; rewrite findUnL // (find_some H). Qed.

Lemma umpleq_none x1 x2 t :
        valid x2 -> [pcm x1 <= x2] -> find t x2 = None -> find t x1 = None.
Proof. by case E: (find t x1)=>[a|] // W H <-; rewrite (umpleq_some W H E). Qed.

End UmpleqLemmas.


(********************)
(* Precision lemmas *)
(********************)

Section Precision.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map_class C V).
Implicit Types (x y : U).

Lemma prec_flip x1 x2 y1 y2 :
        valid (x1 \+ y1) -> x1 \+ y1 = x2 \+ y2 ->
        valid (y2 \+ x2) /\ y2 \+ x2 = y1 \+ x1.
Proof. by move=>X /esym E; rewrite joinC E X joinC. Qed.

Lemma prec_domV x1 x2 y1 y2 :
        valid (x1 \+ y1) -> x1 \+ y1 = x2 \+ y2 ->
        reflect {subset dom x1 <= dom x2} (valid (x1 \+ y2)).
Proof.
move=>V1 E; case V12 : (valid (x1 \+ y2)); constructor.
- move=>n Hs; have : n \in dom (x1 \+ y1) by rewrite domUn inE V1 Hs.
  rewrite E domUn inE -E V1 /= orbC.
  by case: validUn V12 Hs=>// _ _ L _ /L /negbTE ->.
move=>Hs; case: validUn V12=>//.
- by rewrite (validE2 V1).
- by rewrite E in V1; rewrite (validE2 V1).
by move=>k /Hs; rewrite E in V1; case: validUn V1=>// _ _ L _ /L /negbTE ->.
Qed.

Lemma prec_filtV x1 x2 y1 y2 :
        valid (x1 \+ y1) -> x1 \+ y1 = x2 \+ y2 ->
        reflect (x1 = um_filterk (mem (dom x1)) x2) (valid (x1 \+ y2)).
Proof.
move=>V1 E; case X : (valid (x1 \+ y2)); constructor; last first.
- case: (prec_domV V1 E) X=>// St _ H; apply: St.
  by move=>n; rewrite H dom_umfiltk inE; case/andP.
move: (umfiltk_dom V1); rewrite E umfiltUn -?E //.
rewrite (eq_in_umfiltk (f:=y2) (p2:=pred0)).
- by rewrite umfilt_pred0 ?unitR //; rewrite E in V1; rewrite (validE2 V1).
by move=>n; case: validUn X=>// _ _ L _ /(contraL (L _)) /negbTE.
Qed.

End Precision.


(****************)
(* Ordered eval *)
(****************)

(* a version of eval, where the user provides a new order of evaluation *)
(* essentially as a list of timestamps, which are then read in-order. *)

Section OrdEvalDefLemmas.
Variables (K : ordType) (C : pred K) (V R : Type) (U : union_map_class C V).
Implicit Type f : U.
Implicit Type a : R -> K -> V -> R.
Implicit Type p q : pred (K * V).
Implicit Type ks : seq K.

Fixpoint oeval a ks f z0 :=
  if ks is k :: ks' then
    oeval a ks' f (if find k f is Some v then a z0 k v else z0)
  else z0.

Lemma oev_undef a ks z0 : oeval a ks undef z0 = z0.
Proof. by elim: ks=>[|k ks IH] //=; rewrite find_undef. Qed.

Lemma oev0 a ks z0 : oeval a ks Unit z0 = z0.
Proof. by elim: ks=>[|k ks IH] //=; rewrite find0E. Qed.

Lemma oev_dom0 a ks f z0 : dom f =i [::] -> oeval a ks f z0 = z0.
Proof.
case W : (valid f); first by move/(dom0E W)=>->; apply: oev0.
by move/negbT/invalidE: W=>-> _; apply: oev_undef.
Qed.

(* interaction with constructors that build the ordering mask *)

Lemma oev_nil a f z0 : oeval a [::] f z0 = z0.
Proof. by []. Qed.

Lemma oev_consP a k v ks f z0 :
        (k, v) \In f -> oeval a (k :: ks) f z0 = oeval a ks f (a z0 k v).
Proof. by move/In_find=>/= ->. Qed.

Lemma oev_consN a k ks f z0 :
        k \notin dom f -> oeval a (k :: ks) f z0 = oeval a ks f z0.
Proof. by case: dom_find=>//= ->. Qed.

Lemma oev_rconsE a ks k f z0 :
        oeval a (rcons ks k) f z0 =
        if find k f is Some v then a (oeval a ks f z0) k v
        else oeval a ks f z0.
Proof. by elim: ks z0=>[|k' ks IH] z0 /=. Qed.

Lemma oev_rconsP a k v ks f z0 :
        (k, v) \In f ->
        oeval a (rcons ks k) f z0 = a (oeval a ks f z0) k v.
Proof. by rewrite oev_rconsE=>/In_find ->. Qed.

Lemma oev_rconsN a k ks f z0 :
        k \notin dom f -> oeval a (rcons ks k) f z0 = oeval a ks f z0.
Proof. by rewrite oev_rconsE=>/find_none ->. Qed.

Lemma oev_cat a ks1 ks2 f z0 :
        oeval a (ks1 ++ ks2) f z0 = oeval a ks2 f (oeval a ks1 f z0).
Proof. by elim: ks1 z0=>/=. Qed.

(* equalities of oeval wrt. each component *)

Lemma eq_in_oevA a1 a2 ks f z0 :
        (forall r k v, a1 r k v = a2 r k v) ->
        oeval a1 ks f z0 = oeval a2 ks f z0.
Proof.
move=>H; elim: ks z0=>[|k ks IH] z0 //=.
by case E : (find k f)=>[b|] //; rewrite IH H.
Qed.

Lemma eq_in_oevK a ks1 ks2 f z0 :
        [seq k <- ks1 | k \in dom f] = [seq k <- ks2 | k \in dom f] ->
        oeval a ks1 f z0 = oeval a ks2 f z0.
Proof.
suff oevFK ks : oeval a ks f z0 =
  oeval a [seq k <- ks | k \in dom f] f z0.
- by move=>E; rewrite oevFK E -oevFK.
by elim: ks z0=>[|k' ks IH] z0 //=; case: dom_find=>[->|v /= -> _]; rewrite IH.
Qed.

Lemma eq_in_oevF a ks f1 f2 z0 :
        (forall k v, k \in ks -> (k, v) \In f1 <-> (k, v) \In f2) ->
        oeval a ks f1 z0 = oeval a ks f2 z0.
Proof.
elim: ks z0=>[|k ks IH] z0 //= H.
case E1: (find k f1)=>[v1|].
- move/In_find: E1; rewrite H ?(inE,eq_refl) // => /In_find ->.
  by apply: IH=>k' v' D; apply: H; rewrite inE D orbT.
case E2: (find k f2)=>[v2|].
- by move/In_find: E2; rewrite -H ?(inE,eq_refl) // => /In_find; rewrite E1.
by apply: IH=>k' v' D; apply: H; rewrite inE D orbT.
Qed.

(* restrictions that a, ks, f impose on each other *)

Lemma oevFK a ks f z0 :
        oeval a ks f z0 = oeval a [seq k <- ks | k \in dom f] f z0.
Proof.
by elim: ks z0=>[|k' ks IH] z0 //=; case: dom_find=>[->|v /= -> _]; rewrite IH.
Qed.

Lemma oevFA a ks f z0 :
        oeval a ks f z0 =
        oeval (fun r k v => if k \in dom f then a r k v else r) ks f z0.
Proof.
elim: ks a z0=>[|k ks IH] a z0 //=.
by case E: (find k f)=>[b|] //; rewrite (find_some E).
Qed.

Lemma oevKF a ks f z0 :
        oeval a ks f z0 =
        oeval a ks (um_filter (fun x => x.1 \in ks) f) z0.
Proof.
elim: ks f z0=>[|k ks IH] f z0 //=.
rewrite find_umfilt /= inE eq_refl [in LHS]IH [in RHS]IH /=.
congr oeval; last by case: (find k f).
by rewrite -umfilt_predI; apply/eq_in_umfilt=>kv /= D; rewrite orKb.
Qed.

Lemma oevKA a ks f z0 :
        oeval a ks f z0 =
        oeval (fun r k v => if k \in ks then a r k v else r) ks f z0.
Proof.
elim: ks a z0=>[|k ks IH] a z0 //=; rewrite inE eq_refl [in LHS]IH [in RHS]IH.
by apply: eq_in_oevA=>r k' v; case: ifP=>// D; rewrite inE D orbT.
Qed.

(* interaction with map constructions *)

Lemma oev_umfilt a ks p f z0 :
        oeval a ks (um_filter p f) z0 =
        oeval a [seq k <- ks | if find k f is Some v
                               then p (k, v) else false] f z0.
Proof.
elim: ks z0=>[|k ks IH] z0 //=; rewrite IH find_umfilt.
by case E: (find k f)=>[b|] //; case: ifP=>//= P; rewrite E.
Qed.

Lemma oev_filter a ks (p : pred K) f z0 :
        oeval a (filter p ks) f z0 =
        oeval a ks (um_filterk p f) z0.
Proof.
rewrite oev_umfilt oevFK -filter_predI; congr oeval.
by apply: eq_in_filter=>k D /=; case: dom_find=>[->|v ->].
Qed.

Lemma oev_umfiltA a ks p f z0 :
        oeval a ks (um_filter p f) z0 =
        oeval (fun r k v => if p (k, v) then a r k v else r) ks f z0.
Proof.
elim: ks z0=>[|k ks IH] z0 //=; rewrite IH find_umfilt.
by case E : (find k f)=>[b|] //; case: ifP=>//.
Qed.

(* convenient derived lemma *)
Lemma oev_dom_umfilt a p f z0 :
        oeval a (dom (um_filter p f)) f z0 =
        oeval a (dom f) (um_filter p f) z0.
Proof.
rewrite dom_umfiltE oev_filter; apply: eq_in_oevF=>k v _.
by rewrite !In_umfilt /=; split; case=>H Y; move/In_find: Y (Y) H=>->.
Qed.

Lemma oevF a ks f z0 k :
        k \notin ks -> oeval a ks f z0 = oeval a ks (free f k) z0.
Proof.
move=>H; apply: eq_in_oevF=>k' v' D; rewrite InF /= validF.
by case: eqP H D=>[-> /negbTE -> //|???]; split; [move=>H; case: (H) | case].
Qed.

Lemma oevUE a k ks v1 v2 f (z0 : R) :
        (forall r, a r k v1 = a r k v2) ->
        oeval a ks (upd k v1 f) z0 = oeval a ks (upd k v2 f) z0.
Proof.
move=>H; elim: ks z0=>[|k' ks IH] z0 //=.
rewrite !findU; case: eqP=>// ->; rewrite IH.
by congr oeval; case: ifP.
Qed.

Lemma oevU a k ks v1 v2 f z0 :
        (k, v2) \In f ->
        (forall r, a r k v1 = a r k v2) ->
        oeval a ks (upd k v1 f) z0 = oeval a ks f z0.
Proof.
move=>X H.
have [C' W] : C k /\ valid f by move/In_dom/dom_cond: (X); case: (X).
rewrite [in RHS](_ : f = upd k v2 f); first by apply: oevUE.
apply: umem_eq=>//; first by rewrite validU C' W.
case=>k' v'; rewrite InU validU C' W /=.
case: ifP=>[/eqP ->|_]; last by split=>//; case.
by split=>[/(In_fun X)|[_] ->].
Qed.

Lemma oevPtUn a k ks v z0 f :
        valid (pts k v \+ f) -> {subset ks <= dom f} ->
        oeval a ks (pts k v \+ f) z0 =
        oeval a ks f z0.
Proof.
move=>W S; apply: eq_in_oevF=> k0 v0 H.
rewrite InPtUnE //; split; last by move=> H2; right.
by case=>//; case=>E _; move: (S _ H); rewrite E (negbTE (validPtUnD W)).
Qed.

Lemma oevPtUnE a k ks v1 v2 f z0 :
        (forall r, a r k v1 = a r k v2) ->
        oeval a ks (pts k v1 \+ f) z0 = oeval a ks (pts k v2 \+ f) z0.
Proof.
move=>H; case W1 : (valid (pts k v1 \+ f)); last first.
- have W2 : valid (pts k v2 \+ f) = false by rewrite !validPtUn in W1 *.
  move/invalidE: (negbT W1)=>->; move/invalidE: (negbT W2)=>->.
  by rewrite oev_undef.
elim: ks z0=>[|k' ks IH] z0 //=.
have W2 : valid (pts k v2 \+ f) by rewrite !validPtUn in W1 *.
by rewrite !findPtUn2 //; case: eqP=>// ->; rewrite H; apply: IH.
Qed.

Lemma oev_sub_filter a ks (p : pred K) (h : U) z0 :
        {subset dom h <= p} ->
        oeval a (filter p ks) h z0 = oeval a ks h z0.
Proof.
move=>S; rewrite oev_filter (eq_in_umfiltI (p2:=predT)) ?umfilt_predT //=.
by case=>k v /In_dom /S.
Qed.

(* Ideally (- \In f) part would have been folded into p *)
(* but can't because p is decidable and (- \In f) isn't. *)
(* So (- \In f) must be separate. *)
Lemma oev_ind {P : R -> Prop} f ks a z0 :
        P z0 ->
        (forall k v z0, (k, v) \In f -> k \in ks -> P z0 -> P (a z0 k v)) ->
        P (oeval a ks f z0).
Proof.
elim: ks z0=>[|k ks IH] z0 //= Z H; apply: IH; last first.
- by move=>k' v' z' X D; apply: H=>//; rewrite inE D orbT.
case E: (find k f)=>[b|] //; move/In_find: E=>E.
by apply: H=>//; rewrite inE eq_refl.
Qed.

End OrdEvalDefLemmas.

Arguments oev_sub_filter [K C V R U a ks p] _.

Notation oevalv a ks f z0 := (oeval (fun r _ => a r) ks f z0).

Section OrdEvalRelationalInduction1.
Variables (K : ordType) (C : pred K) (V R1 R2 : Type) (U : union_map_class C V).

Lemma oev_ind2 {P : R1 -> R2 -> Prop} (f : U) ks a1 a2 z1 z2 :
        P z1 z2 ->
        (forall k v z1 z2, (k, v) \In f -> k \in ks ->
           P z1 z2 -> P (a1 z1 k v) (a2 z2 k v)) ->
        P (oeval a1 ks f z1) (oeval a2 ks f z2).
Proof.
elim: ks a1 a2 z1 z2=>[|k ks IH] a1 a2 z1 z2 Z H //=.
apply: IH; last first.
- by move=>k' v' z1' z2' H' K'; apply: H=>//; rewrite inE K' orbT.
case H' : (find k f)=>[b|] //; move/In_find: H'=>H'.
by apply: H=>//; rewrite inE eq_refl.
Qed.

End OrdEvalRelationalInduction1.

Section OrdEvalPCM.

Variables (K : ordType) (C : pred K) (V : Type) (R : pcm) (U : union_map_class C V).
Implicit Type f : U.
Variable (a : R -> K -> V -> R).
Implicit Type p q : pred (K * V).
Implicit Type ks : seq K.
Hypothesis frame : forall x y k v, a (x \+ y) k v = a x k v \+ y.

Lemma oev1 ks f z0 : oeval a ks f z0 = oeval a ks f Unit \+ z0.
Proof.
apply: (oev_ind2 (P:=fun r1 r2 => r1 = r2 \+ z0)); first by rewrite unitL.
by move=>k v z1 z2 H1 H2 ->; apply: frame.
Qed.

Lemma oevUn ks (f1 f2 : U) (z0 : R) :
        valid (f1 \+ f2) ->
        oeval a ks (f1 \+ f2) z0 = oeval a ks f1 (oeval a ks f2 z0).
Proof.
move=>W; elim: ks z0=>[|k ks IH] z0 //=; rewrite findUnL //.
case: dom_find=>[E|v E _]; rewrite E IH //.
move/In_find/In_dom/(dom_inNL W)/find_none: E=>->; congr oeval; apply/esym.
by rewrite oev1 joinC frame joinC -oev1.
Qed.

End OrdEvalPCM.


(********)
(* eval *)
(********)

(* A special case of oeval with the initial value used *)
(* as default for undefined maps. *)

Section EvalDefLemmas.
Variables (K : ordType) (C : pred K) (V R : Type) (U : union_map_class C V).
Implicit Type f : U.
Implicit Type a : R -> K -> V -> R.
Implicit Type p q : pred (K * V).

Definition eval a p f z0 :=
  oeval a (dom (um_filter p f)) f z0.

Lemma eval_oevUmfilt a p f z0 :
        eval a p f z0 =
        oeval a (dom (um_filter p f)) (um_filter p f) z0.
Proof.
apply: eq_in_oevF =>k v H; rewrite In_umfilt.
split; last by case.
split=>//; move: H; move/dom_umfilt => [v' [H H1]].
by rewrite (In_fun H1 H0) in H.
Qed.

Lemma eval_undef a p z0 : eval a p undef z0 = z0.
Proof.
by rewrite /eval oev_undef.
Qed.

Lemma eval0 a p z0 : eval a p Unit z0 = z0.
Proof.
by rewrite /eval oev0.
Qed.

Lemma eval_dom0 a p f z0 : dom f =i [::] -> eval a p f z0 = z0.
Proof.
by move=> H; rewrite /eval oev_dom0.
Qed.

Lemma evalPt a p (z0 : R) k v :
        eval a p (pts k v) z0 = if C k && p (k, v) then a z0 k v else z0.
Proof.
rewrite /eval umfiltPt.
case E1: (C k); last by rewrite dom_undef oev_nil.
case: (p (k, v)); last by rewrite dom0 oev_nil.
by rewrite domPtK E1 /= findPt E1.
Qed.

Lemma evalPtUn a p k v z0 f :
        valid (pts k v \+ f) -> all (ord k) (dom f) ->
        eval a p (pts k v \+ f) z0 =
        eval a p f (if p (k, v) then a z0 k v else z0).
Proof.
move=>W /allP H; have: valid (um_filter p (pts k v \+ f)) by rewrite valid_umfilt.
rewrite /eval umfiltPtUn W.
case: (p (k, v))=>W'; last by apply/oevPtUn/dom_umfilt_subset.
rewrite domPtUnK //=; last by apply/allP=>x /dom_umfilt_subset /H.
by rewrite findPtUn // oevPtUn //; apply: dom_umfilt_subset.
Qed.

Lemma evalUnPt a p k v z0 f :
        valid (f \+ pts k v) -> all (ord^~ k) (dom f) ->
        eval a p (f \+ pts k v) z0 =
        if p (k, v) then a (eval a p f z0) k v else eval a p f z0.
Proof.
move=>W /allP H; have: valid (um_filter p (f \+ pts k v)) by rewrite valid_umfilt.
rewrite /eval umfiltUnPt W.
case: (p (k, v))=>W'; last first.
- by rewrite joinC; apply/oevPtUn/dom_umfilt_subset; rewrite joinC.
rewrite domUnPtK //=; last by apply/allP=>x /dom_umfilt_subset /H.
by rewrite (oev_rconsP _ (v:=v)) // joinC oevPtUn //;
   [rewrite joinC | apply: dom_umfilt_subset].
Qed.

Lemma evalUn a p z0 f1 f2 :
        valid (f1 \+ f2) -> {in dom f1 & dom f2, forall x y, ord x y} ->
        eval a p (f1 \+ f2) z0 = eval a p f2 (eval a p f1 z0).
Proof.
elim/um_indb: f2=>[||k v f2 IH W' P W H].
- by rewrite join_undef valid_undef.
- by rewrite dom0 !unitR eval0.
rewrite -(joinC f2) joinA in W *; rewrite evalUnPt //; last first.
- apply/allP=>x; rewrite domUn inE (validL W).
  case/orP=>[/H|]; last by apply: P.
  by apply; rewrite domPtUn inE joinC W' eq_refl.
rewrite evalUnPt //; last by apply/allP.
rewrite (IH (validL W)) // => k1 k2 D1 D2; apply: H D1 _.
by rewrite domPtUn inE joinC W' D2 orbT.
Qed.

Lemma evalPtUnE v2 v1 a p k (z0 : R) f :
        (forall r, (if p (k, v1) then a r k v1 else r) =
                   (if p (k, v2) then a r k v2 else r)) ->
        eval a p (pts k v1 \+ f) z0 = eval a p (pts k v2 \+ f) z0.
Proof.
move=>H; rewrite /eval !oev_dom_umfilt !oev_umfiltA.
by rewrite (domPtUnE2 k v1 v2); apply: oevPtUnE.
Qed.

Lemma evalUEU v2 v1 a p k (z0 : R) f :
        (forall r, (if p (k, v1) then a r k v1 else r) =
                   (if p (k, v2) then a r k v2 else r)) ->
        eval a p (upd k v1 f) z0 = eval a p (upd k v2 f) z0.
Proof.
move=>H; rewrite /eval !oev_dom_umfilt !oev_umfiltA.
rewrite (oevUE _ _ _ H); apply: eq_in_oevK; congr filter.
by apply/domE=>x; rewrite !domU.
Qed.

Lemma evalUE v2 v1 a p k (z0 : R) f :
        (k, v2) \In f ->
        (forall r, (if p (k, v1) then a r k v1 else r) =
                   (if p (k, v2) then a r k v2 else r)) ->
        eval a p (upd k v1 f) z0 = eval a p f z0.
Proof.
move=>X H; rewrite (evalUEU _ _ H) (_ : upd k v2 f = f) //.
have [C' W] : C k /\ valid f by move/In_dom/dom_cond: (X); case: (X).
apply: umem_eq=>//; first by rewrite validU C' W.
case=>k' v'; rewrite InU validU C' W /=.
by case: ifP=>[/eqP ->|_]; [split=>[[_] ->|/(In_fun X)] | split=>[[]|]].
Qed.

Lemma eval_ifP a p z0 f :
        eval a p f z0 =
        eval (fun r k v => if p (k, v) then a r k v else r) predT f z0.
Proof. by rewrite /eval umfilt_predT oev_dom_umfilt oev_umfiltA. Qed.

Lemma eq_filt_eval a p1 p2 z0 f1 f2 :
        um_filter p1 f1 = um_filter p2 f2 ->
        eval a p1 f1 z0 = eval a p2 f2 z0.
Proof. by rewrite !eval_oevUmfilt=>->. Qed.

Lemma eval_pred0 a z0 f : eval a xpred0 f z0 = z0.
Proof.
case W : (valid f); last first.
- by move/negbT/invalidE: W=>->; rewrite eval_undef.
by rewrite /eval umfilt_pred0 // dom0 /=.
Qed.

Lemma eval_predI a p q z0 f :
        eval a p (um_filter q f) z0 = eval a (predI p q) f z0.
Proof. by rewrite !eval_oevUmfilt -!umfilt_predI. Qed.

Lemma eval_umfilt p z0 f a :
        eval a p f z0 = eval a xpredT (um_filter p f) z0.
Proof. by rewrite eval_predI; apply: eq_filt_eval; apply/eq_in_umfilt. Qed.

Lemma eq_in_eval p q z0 f a :
        (forall kv, kv \In f -> p kv = q kv) ->
        eval a p f z0 = eval a q f z0.
Proof.
by rewrite (eval_umfilt p) (eval_umfilt q); move/eq_in_umfilt=>->.
Qed.

Lemma eval_ind {P : R -> Prop} f p a z0 :
        P z0 ->
        (forall k v z0, (k, v) \In f -> p (k, v) -> P z0 -> P (a z0 k v)) ->
        P (eval a p f z0).
Proof.
move=>Z H; elim/um_indf: f z0 Z H=>[||k v h IH W T] z0 Z H;
rewrite ?eval_undef ?eval0 // evalPtUn // ?(order_path_min (@trans K) T) //.
by apply: IH=>[|k0 v0 z1 /(InR W)]; [case: ifP=>Pk //=; apply: H | apply: H].
Qed.

End EvalDefLemmas.


Section EvalOmapLemmas.

Variables (K : ordType) (C : pred K) (V V' R : Type).
Variables (U : union_map_class C V) (U' : union_map_class C V').

Lemma eval_omap (b : R -> K -> V' -> R) p a (f : U) z0 :
        eval b p (omap a f : U') z0 =
        eval (fun r k v =>
               if a (k, v) is Some v' then b r k v' else r)
             (fun kv =>
               if a kv is Some v' then p (kv.1, v') else false)
             f z0.
Proof.
elim/um_indf: f z0=>[||k v f IH W /(order_path_min (@trans K)) P] z0.
- by rewrite omap_undef !eval_undef.
- by rewrite omap0 !eval0.
rewrite omapPtUn W evalPtUn //=; case D : (a (k, v))=>[w|]; last by apply: IH.
rewrite evalPtUn //; last by move/allP: P=>H; apply/allP=>x /dom_omap_sub /H.
rewrite (_ : pts k w \+ omap a f = omap a (pts k v \+ f)) ?valid_omap //.
by rewrite omapPtUn W D.
Qed.

End EvalOmapLemmas.


Section EvalRelationalInduction1.
Variables (K : ordType) (C : pred K) (V R1 R2 : Type) (U : union_map_class C V).

Lemma eval_ind2 {P : R1 -> R2 -> Prop} (f : U) p0 p1 a0 a1 z0 z1 :
        P z0 z1 ->
        (forall k v z0 z1, (k, v) \In f -> P z0 z1 ->
           P (if p0 (k, v) then a0 z0 k v else z0)
             (if p1 (k, v) then a1 z1 k v else z1)) ->
        P (eval a0 p0 f z0) (eval a1 p1 f z1).
Proof.
move=>Z H; elim/um_indf: f z0 z1 Z H=>[||k v h IH W T] z0 z1 Z H;
rewrite ?eval_undef ?eval0 // !evalPtUn // ?(order_path_min (@trans K) T) //=.
apply: IH; first by case: ifPn (H k v z0 z1 (InPtUnL W) Z).
by move=>k0 v0 w1 w2 X; apply: H (InR W X).
Qed.

End EvalRelationalInduction1.


Section EvalRelationalInduction2.
Variables (K1 K2 : ordType) (C1 : pred K1) (C2 : pred K2) (V1 V2 R1 R2 : Type).
Variables (U1 : union_map_class C1 V1) (U2 : union_map_class C2 V2).
Variables (U : union_map_class C1 K2) (P : R1 -> R2 -> Prop).

(* generalization of eval_ind2 to different maps, but related by a bijection *)

(* f1 and f2 evaluate the same if there exists a monotone bijection *)
(* phi between their timestamps, so that the filtering and *)
(* stepping functions are invariant under the bijection *)

Lemma eval_ind3 (phi : U)
        (f1 : U1) (p1 : pred (K1*V1)) (a1 : R1 -> K1 -> V1 -> R1) (z1 : R1)
        (f2 : U2) (p2 : pred (K2*V2)) (a2 : R2 -> K2 -> V2 -> R2) (z2 : R2) :
        um_mono phi -> dom phi = dom f1 -> range phi = dom f2 ->
        P z1 z2 ->
        (forall k1 v1 k2 v2 z1 z2,
           (k1, k2) \In phi -> (k1, v1) \In f1 -> (k2, v2) \In f2 ->
           P z1 z2 ->
           P (if p1 (k1, v1) then a1 z1 k1 v1 else z1)
             (if p2 (k2, v2) then a2 z2 k2 v2 else z2)) ->
        P (eval a1 p1 f1 z1) (eval a2 p2 f2 z2).
Proof.
elim/um_indf: f1 f2 phi z1 z2 =>[||k1 v1 f1 IH W Po]
  f2 phi1 z1 z2 /ummonoP M1 D1 R Hz H.
- rewrite eval_undef eval_dom0 // -R; move/domE: D1; rewrite dom_undef.
  case W1 : (valid phi1); first by move/(dom0E W1)=>->; rewrite range0.
  by move/negbT/invalidE: W1=>->; rewrite dom_undef range_undef.
- rewrite eval0 eval_dom0 // -R; move/domE: D1; rewrite dom0.
  case W1 : (valid phi1); first by move/(dom0E W1)=>->; rewrite range0.
  by move/negbT/invalidE: W1=>->; rewrite dom_undef range_undef.
have A1 : all (ord k1) (dom f1) by apply: order_path_min Po; apply: trans.
case W1 : (valid phi1); last first.
- by move/negbT/invalidE: W1 D1 R=>->; rewrite dom_undef domPtUnK.
rewrite domPtUnK // in D1 *; rewrite evalPtUn //.
have [k2 I1] : exists k2, (k1, k2) \In phi1.
- by apply/In_domX; rewrite D1 inE eq_refl.
have I2 : (k1, v1) \In pts k1 v1 \+ f1 by apply/InPtUnE=>//; left.
have [v2 I3] : exists v2, (k2, v2) \In f2.
- by apply/In_domX; rewrite -R; apply/mem_seqP/(In_range I1).
move: (H _ _ _ _ _ _ I1 I2 I3 Hz)=>Hp.
set phi2 := free phi1 k1.
have W2 : valid f2 by move/In_dom/dom_valid: I3.
have E2 : f2 = pts k2 v2 \+ free f2 k2 by apply/In_eta: I3.
have A2 : all (ord k2) (dom (free f2 k2)).
- apply/allP=>x; rewrite domF inE E2 domPtUn inE -E2 W2 /= domF inE.
  case: eqP=>//= N; rewrite -R =>R'; move/mem_seqP/In_rangeX: (R').
  case=>k' H1; apply: M1 (I1) (H1) _; move/allP: A1; apply.
  move/In_dom: H1 (H1); rewrite D1 inE; case/orP=>//= /eqP ->.
  by move/(In_fun I1)/N.
rewrite E2 evalPtUn -?E2 //.
have M2 : um_mono phi2.
- by apply/ummonoP=>???? /InF [_ _ /M1] X /InF [_ _]; apply: X.
have D2 : dom phi2 = dom f1.
- apply/domE=>x; rewrite domF inE D1 inE eq_sym.
  by case: eqP=>// ->{x}; rewrite (negbTE (validPtUnD W)).
have R2' : range phi2 = dom (free f2 k2).
  move/In_eta: (I1) (R)=>E1; rewrite E1 rangePtUnK.
  - by rewrite {1}E2 domPtUnK //; [case | rewrite -E2].
  - by rewrite -E1.
  apply/allP=>x; rewrite domF inE D1 inE eq_sym.
  by case: eqP=>//= _; apply/allP/A1.
have {}H x1 w1 x2 w2 t1 t2 : (x1, x2) \In phi2 -> (x1, w1) \In f1 ->
  (x2, w2) \In free f2 k2 -> P t1 t2 ->
  P (if p1 (x1, w1) then a1 t1 x1 w1 else t1)
    (if p2 (x2, w2) then a2 t2 x2 w2 else t2).
- case/InF=>_ _ F1 F2 /InF [_ _ F3].
  by apply: H F1 _ F3; apply/(InPtUnE _ W); right.
by case: ifP Hp=>L1; case: ifP=>L2 Hp; apply: IH M2 D2 R2' Hp H.
Qed.

End EvalRelationalInduction2.


(* Evaluating frameable functions *)
Section EvalFrame.
Variables (K : ordType) (C : pred K) (V : Type) (R : pcm) (U : union_map_class C V).
Variables (a : R -> K -> V -> R) (p : pred (K * V)).
Hypothesis frame : (forall x y k v, a (x \+ y) k v = a x k v \+ y).

Implicit Type f : U.

(* a lemma on eval update only makes sense if the function a is frameable, *)
(* so that the result is independent of the order of k *)
Lemma evalFPtUn k v z0 f :
        valid (pts k v \+ f) ->
        eval a p (pts k v \+ f) z0 =
        if p (k, v) then a Unit k v \+ eval a p f z0 else eval a p f z0.
Proof.
move=>W; rewrite /eval umfiltPtUn W.
have D : k \notin dom f by apply: (validPtUnD W).
have Ck : C k by apply: (validPtUn_cond W).
case: ifP=>_; last by apply: oevPtUn=>//; apply: dom_umfilt_subset.
rewrite oevUn // -(oev_sub_filter (p:=mem [:: k])) ?(domPtK,Ck) //.
rewrite -dom_umfiltk_filter umfiltPtUn /= valid_umfiltUnR // inE eq_refl.
rewrite umfilt_mem0L ?(inE,valid_umfilt,validR W) //=; first last.
- by move=>?? /In_umfilt [] _ /In_dom Df; rewrite inE; case: eqP Df D=>// ->->.
rewrite unitR domPtK Ck /= findPt Ck -frame unitL.
rewrite -(oev_sub_filter (p:=mem (dom f))) //.
rewrite -dom_umfiltk_filter  umfiltPtUn /= valid_umfiltUnR // (negbTE D).
congr (a (oeval a (dom _) f z0) k v).
by rewrite -subdom_umfiltkE; apply: dom_umfilt_subset.
Qed.

Lemma evalFU k v z0 f :
        valid (upd k v f) ->
        eval a p (upd k v f) z0 =
        if p (k, v) then a Unit k v \+ eval a p (free f k) z0
        else eval a p (free f k) z0.
Proof.
move=>W; move: (W); rewrite validU =>/andP [C1 _].
have /um_eta2 E : find k (upd k v f) = Some v.
- by rewrite findU eq_refl -(validU k v) W.
by rewrite E evalFPtUn -?E // freeU eq_refl C1.
Qed.

End EvalFrame.

Notation evalv a p f z0 := (eval (fun r _ => a r) p f z0).


(************)
(* um_count *)
(************)

Section CountDefLemmas.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map_class C V).
Implicit Type f : U.
Implicit Type p : pred (K * V).

Definition um_count p f := size (dom (um_filter p f)).

Lemma umcnt0 p : um_count p Unit = 0.
Proof. by rewrite /um_count umfilt0 dom0. Qed.

Lemma umcnt_undef p : um_count p undef = 0.
Proof. by rewrite /um_count umfilt_undef dom_undef. Qed.

Lemma umcntPt p k v :
        um_count p (pts k v) = if C k && p (k, v) then 1 else 0.
Proof.
rewrite /um_count umfiltPt; case C': (C k); last by rewrite dom_undef.
by case: ifP; [rewrite domPtK C' | rewrite dom0].
Qed.

Lemma umcntUn p f1 f2 :
        valid (f1 \+ f2) ->
        um_count p (f1 \+ f2) = um_count p f1 + um_count p f2.
Proof.
move=>W; rewrite /um_count umfiltUn // size_domUn //.
by rewrite -umfiltUn // valid_umfilt.
Qed.

Lemma umcntPtUn p k v f :
        valid (pts k v \+ f) ->
        um_count p (pts k v \+ f) = (if p (k, v) then 1 else 0) + um_count p f.
Proof. by move=>W; rewrite umcntUn // umcntPt (validPtUn_cond W). Qed.

Lemma umcntUnPt p k v f :
        valid (f \+ pts k v) ->
        um_count p (f \+ pts k v) = um_count p f + if p (k, v) then 1 else 0.
Proof. by rewrite joinC=>W; rewrite umcntPtUn // addnC. Qed.

Lemma umcntF p k v f :
        (k, v) \In f ->
        um_count p (free f k) =
        if p (k, v) then (um_count p f).-1 else um_count p f.
Proof.
move=>H; move/In_dom: (H)=>/= D; rewrite /um_count.
case E: (k \in dom (um_filter p f)).
- case/dom_umfilt: E=>w [H1 H2].
  rewrite -{w H2}(In_fun H H2) in H1 *.
  rewrite H1 umfiltF size_domF ?subn1 //.
  by apply/dom_umfilt; exists v.
rewrite umfiltF; case: ifP=>P; last by rewrite dom_free // E.
by move/negP: E; elim; apply/dom_umfilt; exists v.
Qed.

Lemma umcntU p k v w f :
        (k, w) \In f ->
        um_count p (upd k v f) =
        if p (k, v) then
          if p (k, w) then um_count p f else (um_count p f).+1
        else
          if p (k, w) then (um_count p f).-1 else um_count p f.
Proof.
move=>H; have E : f = pts k w \+ free f k.
- by apply: um_eta2; apply/In_find.
have W1 : valid f by move/In_dom/dom_valid: H.
have W2 : valid (pts k v \+ free f k).
- by rewrite {1}E !validPtUn in W1 *.
have W3 : valid (pts k w \+ free f k).
- by rewrite {1}E !validPtUn in W1 *.
rewrite {1}E updPtUn umcntPtUn // (umcntF p H).
case: ifP=>H1; case: ifP=>H2; rewrite ?add0n ?add1n //.
have: um_count p f > 0; first by rewrite E umcntPtUn // H2.
by case X: (um_count p f).
Qed.

Lemma eq_in_umcnt p1 p2 f :
        (forall kv, kv \In f -> p1 kv = p2 kv) ->
        um_count p1 f = um_count p2 f.
Proof. by rewrite /um_count=>/eq_in_umfilt ->. Qed.

(* common case *)
Lemma eq_in_umcnt2 p1 p2 f :
        p1 =1 p2 -> um_count p1 f = um_count p2 f.
Proof. by move=>S; apply: eq_in_umcnt=>kv _; apply: S. Qed.

Lemma umcnt_leq p1 p2 f :
        subpred p1 p2 -> um_count p1 f <= um_count p2 f.
Proof.
move=>S; case W: (valid f); last first.
- by move/negbT/invalidE: W=>->; rewrite !umcnt_undef.
rewrite /um_count (umfilt_predD _ S) size_domUn ?leq_addr //.
by rewrite -umfilt_predD // valid_umfilt.
Qed.

Lemma umcnt_count q f : count q (dom f) = um_count (q \o fst) f.
Proof.
rewrite assocs_dom /um_count -size_assocs.
by rewrite assocs_umfilt /= size_filter count_map.
Qed.

Lemma umcnt_umfilt p q f :
        um_count p (um_filter q f) = um_count (predI p q) f.
Proof. by rewrite /um_count umfilt_predI. Qed.

Lemma umcnt_umfiltC p q f :
        um_count p (um_filter q f) = um_count q (um_filter p f).
Proof. by rewrite !umcnt_umfilt; apply: eq_in_umcnt=>x; rewrite /= andbC. Qed.

Lemma umcnt_pred0 f : um_count pred0 f = 0.
Proof.
case W : (valid f); last first.
- by move/invalidE: (negbT W)=>->; rewrite umcnt_undef.
by rewrite /um_count umfilt_pred0 // dom0.
Qed.

Lemma umcnt_predT f : um_count predT f = size (dom f).
Proof. by rewrite /um_count umfilt_predT. Qed.

Lemma umcnt_predU p1 p2 f :
        um_count (predU p1 p2) f =
        um_count p1 f + um_count (predD p2 p1) f.
Proof.
case W: (valid f); last first.
- by move/invalidE: (negbT W)=>->; rewrite !umcnt_undef.
rewrite /um_count umfilt_predU size_domUn //.
case: validUn=>//; rewrite ?(valid_umfilt,W) //.
move=>k /dom_umfilt [v1 [P1 H1]] /dom_umfilt [v2 [/= P2 H2]].
by rewrite -(In_fun H1 H2) P1 in P2.
Qed.

Lemma umcnt_predD p1 p2 f :
        subpred p1 p2 ->
        um_count p2 f = um_count p1 f + um_count (predD p2 p1) f.
Proof.
move=>S; rewrite -umcnt_predU //; apply: eq_in_umcnt=>kv /= _.
by case E: (p1 kv)=>//; apply: S.
Qed.

Lemma umcnt_predDE p1 p2 f :
        um_count (predD p2 p1) f =
        um_count p2 f - um_count (predI p1 p2) f.
Proof.
have S1 : p2 =1 predU (predD p2 p1) (predI p1 p2).
- by move=>x /=; case: (p1 x)=>//; rewrite orbF.
have S2: predD (predI p1 p2) (predD p2 p1) =1 predI p1 p2.
- by move=>x /=; case: (p1 x)=>//; rewrite andbF.
rewrite {1}(eq_in_umcnt2 _ S1) umcnt_predU // (eq_in_umcnt2 _ S2).
by rewrite -addnBA // subnn addn0.
Qed.

Lemma umcnt_umfiltU p f q1 q2 :
        um_count p (um_filter (predU q1 q2) f) =
        um_count p (um_filter q1 f) + um_count p (um_filter (predD q2 q1) f).
Proof.
rewrite umcnt_umfiltC umcnt_predU ?valid_umfilt //.
by rewrite !(umcnt_umfiltC p).
Qed.

Lemma umcnt_umfilt0 f :
        valid f -> forall p, um_count p f = 0 <-> um_filter p f = Unit.
Proof.
move=>W; split; last by rewrite /um_count=>->; rewrite dom0.
by move/size0nil=>D; apply: dom0E; rewrite ?valid_umfilt ?D.
Qed.

Lemma umcnt_eval0 R a p f (z0 : R) : um_count p f = 0 -> eval a p f z0 = z0.
Proof.
case W : (valid f); last first.
- by move/invalidE: (negbT W)=>->; rewrite eval_undef.
by move/(umcnt_umfilt0 W)=>E; rewrite eval_umfilt E eval0.
Qed.

Lemma umcnt_mem0 p f :
        um_count p f = 0 <-> (forall k v, (k, v) \In f -> ~~ p (k, v)).
Proof.
case W : (valid f); last first.
- by move/invalidE: (negbT W)=>->; rewrite umcnt_undef; split=>// _ k v /In_undef.
split; first by move/(umcnt_umfilt0 W)/umfilt_mem0.
by move=>H; apply/(umcnt_umfilt0 W); apply/umfilt_mem0L.
Qed.

Lemma umcnt_size p f : um_count p f <= size (dom f).
Proof. by rewrite -umcnt_predT; apply: umcnt_leq. Qed.

Lemma umcnt_memT p f :
        um_count p f = size (dom f) <->
        forall k v, (k, v) \In f -> p (k, v).
Proof.
elim/um_indf: f=>[||k v f IH W P].
- by rewrite umcnt_undef dom_undef; split=>// _ k v /In_undef.
- by rewrite umcnt0 dom0; split=>// _ k v /In0.
rewrite umcntPtUn // size_domPtUn //.
case: ifP=>H; split.
- move/eqP; rewrite !add1n eqSS=>/eqP/IH=>H1 k1 v1.
  by case/InPtUnE=>//; [case=>->-> | apply: H1].
- move=>H1; apply/eqP; rewrite !add1n eqSS; apply/eqP.
  by apply/IH=>k1 v1 H2; apply: H1; apply/InR.
- by rewrite add0n=>X; move: (umcnt_size p f); rewrite X add1n ltnn.
by move/(_ k v)/(_ (InPtUnL W)); rewrite H.
Qed.

Lemma umcnt_filt_eq p f : um_count p f = size (dom f) <-> f = um_filter p f.
Proof.
rewrite umcnt_memT -{2}[f]umfilt_predT -eq_in_umfilt.
by split=>H; [case=>k v /H | move=>k v /H].
Qed.

Lemma umcnt_eval p f : um_count p f = eval (fun n _ _ => n.+1) p f 0.
Proof.
elim/um_indf: f=>[||k v f IH W /(order_path_min (@trans K)) P].
- by rewrite umcnt_undef eval_undef.
- by rewrite umcnt0 eval0.
rewrite umcntPtUn // evalPtUn //=; case: ifP=>// H.
by rewrite /eval oev1 // IH addnC; congr (_ + _).
Qed.

End CountDefLemmas.


(***********)
(* dom_map *)
(***********)

(* Taking a domain as a finite set, instead of a sequence *)
(* useful when needing to state disjointness of maps that *)
(* have different types *)

Section DomMap.
Variables (K : ordType) (C : pred K) (V : Type).
Variables (U : union_map_class C V) (U' : union_map_class C unit).

Definition dom_map (x : U) : U' := omap (fun => Some tt) x.

Lemma dom_map0 : dom_map (Unit : U) = Unit.
Proof. by rewrite /dom_map omap0. Qed.

Lemma dom_map_undef : dom_map undef = undef.
Proof. by rewrite /dom_map omap_undef. Qed.

Lemma dom_mapE x : dom (dom_map x) = dom x.
Proof. by apply: dom_omap_some. Qed.

Lemma valid_dom_map x : valid (dom_map x) = valid x.
Proof. by rewrite /dom_map valid_omap. Qed.

Lemma dom_mapUn (x y : U) :
        dom_map (x \+ y) = dom_map x \+ dom_map y.
Proof.
case W : (valid (x \+ y)); first by rewrite /dom_map omapUn.
rewrite /dom_map; move/invalidE: (negbT W)=>->; rewrite omap_undef.
case: validUn W=>//.
- by move/invalidE=>->; rewrite omap_undef undef_join.
- by move/invalidE=>->; rewrite omap_undef join_undef.
move=>k D1 D2 _; suff : ~~ valid (dom_map x \+ dom_map y).
- by move/invalidE=>->.
by case: validUn=>// _ _ /(_ k); rewrite !dom_mapE=>/(_ D1); rewrite D2.
Qed.

Lemma domeq2_dom_mapL x : dom_eq2 (dom_map x) x.
Proof. by rewrite /dom_eq2 valid_dom_map dom_mapE !eq_refl. Qed.

Lemma domeq2_dom_mapR x : dom_eq2 x (dom_map x).
Proof. by apply: domeq2_sym; apply: domeq2_dom_mapL. Qed.

End DomMap.

Arguments dom_map [K C V U U'] _.

(* composing dom_map *)

Section DomMapIdempotent.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map_class C V).
Variables (U' : union_map_class C unit) (U'' : union_map_class C unit).

Lemma dom_map_idemp (x : U) : dom_map (dom_map x : U') = dom_map x :> U''.
Proof. by rewrite /dom_map omap_comp. Qed.

End DomMapIdempotent.


(*****************)
(* Map inversion *)
(*****************)

Section MapInverse.
Variables (K V : ordType) (C : pred K) (C' : pred V) (U : union_map_class C V) (U' : union_map_class C' K).

Definition inverse (f : U) : U' :=
  um_foldl (fun r k v => r \+ pts v k) Unit undef f.

Lemma inverse_undef : inverse undef = undef.
Proof. by rewrite /inverse umfoldl_undef. Qed.

Lemma inverse0 : inverse Unit = Unit.
Proof. by rewrite /inverse umfoldl0. Qed.

Lemma inverseUn f1 f2 :
        valid (f1 \+ f2) -> inverse (f1 \+ f2) = inverse f1 \+ inverse f2.
Proof.
move=>W; rewrite /inverse umfoldlUn_frame ?unitR //.
by move=>*; rewrite joinAC.
Qed.

Lemma inversePt k v : C k -> inverse (pts k v) = pts v k.
Proof. by move=>C''; rewrite /inverse umfoldlPt unitL C''. Qed.

Lemma inversePtUn k v f :
        valid (pts k v \+ f) ->
        inverse (pts k v \+ f) = pts v k \+ inverse f.
Proof. by move=>W; rewrite inverseUn // inversePt // (validPtUn_cond W). Qed.

Lemma dom_inverse f : valid (inverse f) -> dom (inverse f) =i range f.
Proof.
rewrite /inverse/um_foldl/range; case: ifP=>_; last by rewrite valid_undef.
elim: (assocs f)=>[|x g IH] /= W k; first by rewrite dom0.
rewrite foldl_init in W *; last by move=>*; rewrite joinAC.
by rewrite domUnPt !inE W /= eq_sym IH // (validL W).
Qed.

Lemma valid_inverse f :
        valid (inverse f) =
        [&& valid f, uniq (range f) & all C' (range f)].
Proof.
elim/um_indf: f=>[||k v f IH W /(order_path_min (@trans K)) P].
- by rewrite inverse_undef !valid_undef.
- by rewrite inverse0 !valid_unit range0.
rewrite inversePtUn W //= rangePtUnK // validPtUn /=.
rewrite IH (validR W) /=; bool_congr; rewrite andbC -!andbA.
rewrite andbC [in X in _ = X]andbC.
case X1 : (uniq (range f)) IH=>//=.
case X2 : (all C' (range f))=>//=.
by rewrite (validR W)=>/dom_inverse ->.
Qed.

(* The next few lemmas that depend on valid (inverse f) *)
(* can be strenghtened to require just uniq (range f) and *)
(* all C' (range f). *)
(* However, the formulation with the hypothesis valid (inverse f) *)
(* is packaged somewhat better, and is what's encountered in practice. *)

Lemma range_inverse f : valid (inverse f : U') -> range (inverse f) =i dom f.
Proof.
elim/um_indf: f=>[||k v f IH W P].
- by rewrite inverse_undef valid_undef.
- by rewrite inverse0 range0 dom0.
rewrite inversePtUn // => W' x.
rewrite rangePtUn inE W' domPtUn inE W /=.
by case: eqP=>//= _; rewrite IH // (validR W').
Qed.

Lemma In_inverse k v f :
        valid (inverse f) -> (k, v) \In f <-> (v, k) \In inverse f.
Proof.
elim/um_indf: f k v=>[||x w f IH W /(order_path_min (@trans K)) P] k v.
- by rewrite inverse_undef valid_undef.
- by rewrite inverse0; split=>/In0.
move=>W'; rewrite inversePtUn // !InPtUnE //; last by rewrite -inversePtUn.
rewrite IH; first by split; case=>[[->->]|]; auto.
rewrite !valid_inverse rangePtUnK // (validR W) in W' *.
by case/and3P: W'=>_ /= /andP [_ ->] /andP [_ ->].
Qed.

Lemma uniq_range_inverse f : uniq (range (inverse f)).
Proof.
case W : (valid (inverse f)); last first.
- by move/invalidE: (negbT W)=>->; rewrite range_undef.
rewrite /range map_inj_in_uniq.
- by apply: (@map_uniq _ _ fst); rewrite -assocs_dom; apply: uniq_dom.
case=>x1 x2 [y1 y] /= H1 H2 E; rewrite {x2}E in H1 *.
move/mem_seqP/umemE/(In_inverse _ _ W): H1=>H1.
move/mem_seqP/umemE/(In_inverse _ _ W): H2=>H2.
by rewrite (In_fun H1 H2).
Qed.

Lemma all_range_inverse f : all C (range (inverse f)).
Proof.
apply: (@sub_all _ (fun k => k \in dom f)); first by move=>x /dom_cond.
by apply/allP=>x H; rewrite -range_inverse //; apply: range_valid H.
Qed.

Lemma sorted_range_inverse f :
        valid (inverse f) ->
        sorted ord (range f) -> sorted ord (range (inverse f)).
Proof.
move=>W /ummonoP X; apply/ummonoP=>v v' k k'.
move/(In_inverse _ _ W)=>H1 /(In_inverse _ _ W) H2.
apply: contraTT; case: ordP=>//= E _; first by case: ordP (X _ _ _ _ H2 H1 E).
by move/eqP: E H2=>-> /(In_fun H1) ->; rewrite irr.
Qed.

End MapInverse.

Arguments inverse [K V C C' U U'].


Section InverseLaws.
Variables (K V : ordType) (C : pred K) (C' : pred V) (U : union_map_class C V) (U' : union_map_class C' K).

Lemma valid_inverse_idemp (f : U) :
        valid (inverse (inverse f : U') : U) = valid (inverse f : U').
Proof.
by rewrite valid_inverse uniq_range_inverse all_range_inverse !andbT.
Qed.

Lemma inverse_idemp (f : U) :
        valid (inverse f : U') -> inverse (inverse f : U') = f.
Proof.
move=>W; apply/umem_eq.
- by rewrite valid_inverse_idemp.
- by move: W; rewrite valid_inverse; case/and3P.
move=>x; split=>H.
- by apply/(In_inverse _ _ W); apply/(@In_inverse _ _ _ _ _ U) =>//; case: H.
case: x H=>k v /(In_inverse _ _ W)/In_inverse; apply.
by rewrite valid_inverse_idemp.
Qed.

End InverseLaws.


(***************************)
(* Composition of two maps *)
(***************************)

Section MapComposition.
Variables (K1 K2 : ordType) (C1 : pred K1) (C2 : pred K2) (V : Type).
Variables (Uf : union_map_class C1 K2).
Variables (Ug : union_map_class C2 V).
Variables (U : union_map_class C1 V).
Implicit Types (f : Uf) (g : Ug).

Definition um_comp g f : U :=
  um_foldl (fun r k v => if find v g is Some w
                         then pts k w \+ r else r) Unit undef f.

Lemma umcomp_undeff f : valid f -> um_comp undef f = Unit.
Proof.
move=>W; apply: (umfoldl_ind (P:=fun r => r = Unit))=>//.
by move=>*; rewrite find_undef.
Qed.
Lemma umcomp_fundef g : um_comp g undef = undef.
Proof. by rewrite /um_comp umfoldl_undef. Qed.

Lemma umcomp0f f : valid f -> um_comp Unit f = Unit.
Proof.
move=>W; apply: (umfoldl_ind (P:=fun r => r = Unit))=>//.
by move=>*; rewrite find0E.
Qed.

Lemma umcompf0 g : um_comp g Unit = Unit.
Proof. by rewrite /um_comp umfoldl0. Qed.

Lemma dom_umcomp_sub g f : {subset dom (um_comp g f) <= dom f}.
Proof.
rewrite /um_comp; elim/um_indf: f=>[||k v f IH W P] x.
- by rewrite umfoldl_undef dom_undef.
- by rewrite umfoldl0 dom0.
rewrite umfoldlUn_frame //;
last by move=>*; case: (find _ _)=>// a; rewrite joinA.
rewrite unitR umfoldlPt (validPtUn_cond W).
case E : (find v g)=>[b|]; last first.
- by rewrite unitL=>/IH; rewrite domPtUn inE W =>->; rewrite orbT.
rewrite unitR domPtUn inE; case/andP=>_ /orP [/eqP <-|/IH].
- by rewrite domPtUn inE W eq_refl.
by rewrite domPtUn inE W=>->; rewrite orbT.
Qed.

Lemma valid_umcomp g f : valid (um_comp g f) = valid f.
Proof.
rewrite /um_comp; elim/um_indf: f=>[||k v f IH W P].
- by rewrite umfoldl_undef !valid_undef.
- by rewrite umfoldl0 !valid_unit.
rewrite umfoldlUn_frame //;
  last by move=>*; case: (find _ _)=>// a; rewrite joinA.
rewrite unitR W umfoldlPt (validPtUn_cond W).
case: (find v g)=>[a|]; last by rewrite unitL IH (validR W).
rewrite unitR validPtUn (validPtUn_cond W) IH (validR W).
by apply: contra (notin_path P); apply: dom_umcomp_sub.
Qed.

Lemma umcompUnf g1 g2 f :
        valid (g1 \+ g2) -> um_comp (g1 \+ g2) f = um_comp g1 f \+ um_comp g2 f.
Proof.
rewrite /um_comp=>Wg; elim/um_indf: f=>[||k v f IH P W].
- by rewrite !umfoldl_undef undef_join.
- by rewrite !umfoldl0 unitL.
rewrite !umfoldlUn_frame //;
try by move=>*; case: (find _ _)=>// a; rewrite joinA.
rewrite !unitR !umfoldlPt; case: ifP=>C; last by rewrite !undef_join.
rewrite {}IH joinAC [in X in _ = X]joinA [in X in _ = X]joinAC;
rewrite -[in X in _ = X]joinA; congr (_ \+ _).
case: validUn (Wg)=>// W1 W2 X _; rewrite findUnL //.
by case: ifP=>[/X|]; case: dom_find=>// ->; rewrite ?unitL ?unitR.
Qed.

Lemma umcompfUn g f1 f2 :
        valid (f1 \+ f2) -> um_comp g (f1 \+ f2) = um_comp g f1 \+ um_comp g f2.
Proof.
rewrite /um_comp=>W; rewrite umfoldlUn_frame ?unitR //.
by move=>*; case: (find _ _)=>// a; rewrite joinA.
Qed.

Lemma umcompfPt g k v :
        um_comp g (pts k v) =
        if C1 k then
          if find v g is Some w then pts k w else Unit
        else undef.
Proof.
rewrite /um_comp umfoldlPt; case: ifP=>C //.
by case: (find _ _)=>// a; rewrite unitR.
Qed.

Lemma umcompfPtUn g f k v :
        valid (pts k v \+ f) ->
        um_comp g (pts k v \+ f) =
        if find v g is Some w then pts k w \+ um_comp g f
        else um_comp g f.
Proof.
move=>W; rewrite umcompfUn // umcompfPt (validPtUn_cond W).
by case: (find _ _)=>[a|] //; rewrite unitL.
Qed.

Lemma umcompPtf f k v :
        um_comp (pts k v) f =
        if C2 k then
          omap (fun x => if x.2 == k then Some v else None) f
        else if valid f then Unit else undef.
Proof.
elim/um_indf: f=>[||x w f IH W P].
- rewrite umcomp_fundef omap_undef.
  by case: ifP=>//; rewrite valid_undef.
- rewrite umcompf0 omap0.
  by case: ifP=>//; rewrite valid_unit.
rewrite umcompfUn // umcompfPt (validPtUn_cond W) omapPtUn.
rewrite W findPt2 andbC.
case C: (C2 k) IH=>/= IH; last by rewrite IH (validR W) unitL.
by case: eqP=>_; rewrite IH // unitL.
Qed.

Lemma umcompPtUnf g f k v :
        valid (pts k v \+ g) ->
        um_comp (pts k v \+ g) f =
        omap (fun x => if x.2 == k then Some v else None) f \+ um_comp g f.
Proof.
by move=>W; rewrite umcompUnf // umcompPtf (validPtUn_cond W).
Qed.

Lemma In_umcomp g f k v :
        (k, v) \In um_comp g f <->
        valid (um_comp g f) /\ exists k', (k, k') \In f /\ (k', v) \In g.
Proof.
split=>[H|[W][k'][]].
- split; first by case: H.
  elim/um_indf: f H=>[||x w f IH P W].
  - by rewrite umcomp_fundef=>/In_undef.
  - by rewrite umcompf0=>/In0.
  rewrite /um_comp umfoldlUn_frame //;
  last by move=>*; case: (find _ _)=>// a; rewrite joinA.
  rewrite unitR !umfoldlPt; case: ifP=>C; last first.
  - by rewrite undef_join=>/In_undef.
  case/InUn; last by case/IH=>k' [H1 H2]; exists k'; split=>//; apply/InR.
  case E: (find _ _)=>[b|]; last by move/In0.
  rewrite unitR=>/InPt; case; case=>?? _; subst x b.
  by exists w; split=>//; apply/In_find.
elim/um_indf: f W k'=>[||x w f IH P W] W' k'.
- by move/In_undef.
- by move/In0.
rewrite umcompfPtUn // in W'; rewrite InPtUnE //.
case=>[[??] G|H1 H2].
- subst x w; rewrite umcompfPtUn //.
  by move/In_find: (G)=>E; rewrite E in W' *; apply/InPtUnL.
rewrite umcompfPtUn //.
case E: (find _ _) W'=>[b|] W'; last by apply: IH H1 H2.
by apply/InR=>//; apply:IH H1 H2; rewrite (validR W').
Qed.

End MapComposition.


(**********)
(* um_all *)
(**********)

Section AllDefLemmas.
Variables (K : ordType) (C : pred K) (V : Type).
Variables (U : union_map_class C V) (P : K -> V -> Prop).
Implicit Types (k : K) (v : V) (f : U).

Definition um_all f := forall k v, (k, v) \In f -> P k v.

Lemma umall_undef : um_all undef.
Proof. by move=>k v /In_undef. Qed.

Lemma umall0 : um_all Unit.
Proof. by move=>k v /In0. Qed.

Hint Resolve umall_undef umall0 : core.

Lemma umallUn f1 f2 : um_all f1 -> um_all f2 -> um_all (f1 \+ f2).
Proof. by move=>X Y k v /InUn [/X|/Y]. Qed.

Lemma umallUnL f1 f2 : valid (f1 \+ f2) -> um_all (f1 \+ f2) -> um_all f1.
Proof. by move=>W H k v F; apply: H; apply/InL. Qed.

Lemma umallUnR f1 f2 : valid (f1 \+ f2) -> um_all (f1 \+ f2) -> um_all f2.
Proof. by rewrite joinC; apply: umallUnL. Qed.

Lemma umallPt k v : P k v -> um_all (pts k v : U).
Proof. by move=>X k1 v1 /InPt [[->->]]. Qed.

Lemma umallPtUn k v f : P k v -> um_all f -> um_all (pts k v \+ f).
Proof. by move/(umallPt (k:=k)); apply: umallUn. Qed.

Lemma umallUnPt k v f : P k v -> um_all f -> um_all (f \+ pts k v).
Proof. by rewrite joinC; apply: umallPtUn. Qed.

Lemma umallPtE k v : C k -> um_all (pts k v : U) -> P k v.
Proof. by move/(In_condPt v)=>C'; apply. Qed.

Lemma umallPtUnE k v f :
        valid (pts k v \+ f) -> um_all (pts k v \+ f) -> P k v /\ um_all f.
Proof.
move=>W H; move: (umallUnL W H) (umallUnR W H)=>{H} H1 H2.
by split=>//; apply: umallPtE H1; apply: validPtUn_cond W.
Qed.

End AllDefLemmas.

Hint Resolve umall_undef umall0 : core.


(***********)
(* um_allb *)
(***********)

(* decidable um_all *)

Section MapAllDecidable.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map_class C V).
Implicit Types (f : U) (p : pred (K*V)).

Definition um_allb p f := um_count p f == size (dom f).

Lemma umallb_undef p : um_allb p undef.
Proof. by rewrite /um_allb umcnt_undef dom_undef. Qed.

Lemma umallb0 p : um_allb p Unit.
Proof. by rewrite /um_allb umcnt0 dom0. Qed.

Lemma umallbP p f : reflect (forall x, x \In f -> p x) (um_allb p f).
Proof.
apply/(equivP idP); split=>[/eqP | H].
- by rewrite umcnt_memT=>H [k v]; apply: H.
by apply/eqP; rewrite umcnt_memT=>k v; apply: H.
Qed.

Lemma umallbUn p f1 f2 :
        valid (f1 \+ f2) -> um_allb p (f1 \+ f2) = um_allb p f1 && um_allb p f2.
Proof.
move=>W; apply/idP/idP.
- by move/umallbP=>H; apply/andP; split; apply/umallbP=>x X;
  apply: H; [apply: InL | apply: InR].
clear W.
case/andP=>/umallbP X1 /umallbP X2; apply/umallbP=>x.
by case/InUn; [apply: X1 | apply: X2].
Qed.

Lemma umallbPt p k v : C k -> um_allb p (pts k v) = p (k, v).
Proof. by move=>C'; rewrite /um_allb umcntPt domPtK C' /=; case: (p (k, v)). Qed.

Lemma umallbPtUn p k v f :
        valid (pts k v \+ f) ->
        um_allb p (pts k v \+ f) = p (k, v) && um_allb p f.
Proof. by move=>W; rewrite umallbUn // umallbPt // (validPtUn_cond W). Qed.

Lemma umallbU p k v f :
        valid (upd k v f) ->
        um_allb p (upd k v f) = p (k, v) && um_allb p (free f k).
Proof.
rewrite validU=>/andP [W1 W2]; rewrite upd_eta // umallbPtUn //.
by rewrite validPtUn W1 validF W2 domF inE eq_refl.
Qed.

Lemma umallbF p k f : um_allb p f -> um_allb p (free f k).
Proof. by move/umallbP=>H; apply/umallbP=>kv /InF [_ _ /H]. Qed.

End MapAllDecidable.


(************************************)
(* Zipping a relation over two maps *)
(************************************)

(* Binary version of um_all, where comparison is done over values of *)
(* equal keys in both maps. *)

Section BinaryMapAll.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map_class C V) (P : V -> V -> Prop).
Implicit Types (k : K) (v : V) (f : U).

Definition um_all2 (f1 f2 : U) := forall k, optionR P (find k f1) (find k f2).

Lemma umall2_refl f : Reflexive P -> um_all2 f f.
Proof. by move=>R k; apply: Reflexive_optionR. Qed.

Lemma umall2_sym : Symmetric P -> Symmetric um_all2.
Proof. by move=>S x y; split=>H k; apply/Symmetric_optionR. Qed.

Lemma umall2_trans : Transitive P -> Transitive um_all2.
Proof. by move=>T x y z H1 H2 k; apply: Transitive_optionR (H1 k) (H2 k). Qed.

Lemma umall2_eq : Equivalence_rel P -> Equivalence_rel um_all2.
Proof.
case/Equivalence_relS=>R S T; apply/Equivalence_relS; split.
- by move=>f; apply: umall2_refl.
- by apply: umall2_sym.
by apply: umall2_trans.
Qed.

Lemma umall20 : um_all2 Unit Unit.
Proof. by move=>k; rewrite /optionR /= find0E. Qed.

Lemma umall2_undef : um_all2 undef undef.
Proof. by move=>k; rewrite /optionR /= find_undef. Qed.

Lemma umall2_dom f1 f2 : um_all2 f1 f2 -> dom f1 = dom f2.
Proof.
move=>H; apply/domE=>k; apply/idP/idP;
move: (H k); rewrite /optionR /=;
by case: dom_find =>// v ->; case: dom_find=>// ->.
Qed.

Lemma umall2_umfilt f1 f2 p :
        (forall k v1 v2,
           (k, v1) \In f1 -> (k, v2) \In f2 -> P v1 v2 ->
           p (k, v1) = p (k, v2)) ->
        um_all2 f1 f2 -> um_all2 (um_filter p f1) (um_filter p f2).
Proof.
move=>E H k; move: (H k); rewrite /optionR /= !find_umfilt.
case E1: (find k f1)=>[v1|]; case E2: (find k f2)=>[v2|] // X.
move/In_find: E1=>E1; move/In_find: E2=>E2.
by rewrite -(E k v1 v2 E1 E2) //; case: ifP.
Qed.

Lemma umall2_umfilt_inv f1 f2 p :
        um_all2 (um_filter p f1) (um_filter p f2) ->
        forall k, match find k f1, find k f2 with
           Some v1, Some v2 => p (k, v1) && p (k, v2) -> P v1 v2
         | Some v1, None => ~~ p (k, v1)
         | None, Some v2 => ~~ p (k, v2)
         | None, None => True
        end.
Proof.
move=>H k; move: (H k); rewrite !find_umfilt.
case: (find k f1)=>[a1|]; case: (find k f2)=>[a2|] //.
- by case: ifP; case: ifP.
- by case: ifP.
by case: ifP.
Qed.

Lemma umall2_umfilt_ord f1 f2 t :
        um_all2 (um_filter (fun kv => ord kv.1 t) f1)
                (um_filter (fun kv=>ord kv.1 t) f2) <->
        forall k, ord k t -> optionR P (find k f1) (find k f2).
Proof.
split=>[H k X|H k]; last first.
- move: (H k); rewrite !find_umfilt.
  case: (find k f1)=>[a1|]; case: (find k f2)=>[a2|] //=;
  by case: ifP=>// X; apply.
move/umall2_umfilt_inv/(_ k): H=>/=.
case: (find k f1)=>[v1|]; case: (find k f2)=>[v2|] //=.
- by rewrite X; apply.
- by rewrite X.
by rewrite X.
Qed.

Lemma umall2_umfilt_oleq f1 f2 t :
        um_all2 (um_filter (fun kv => oleq kv.1 t) f1)
                (um_filter (fun kv=>oleq kv.1 t) f2) <->
        forall k, oleq k t -> optionR P (find k f1) (find k f2).
Proof.
split=>[H k X|H k]; last first.
- move: (H k); rewrite !find_umfilt.
  case: (find k f1)=>[a1|]; case: (find k f2)=>[a2|] //=;
  by case: ifP=>// X; apply.
move/umall2_umfilt_inv/(_ k): H=>/=.
case: (find k f1)=>[v1|]; case: (find k f2)=>[v2|] //=.
- by rewrite X; apply.
- by rewrite X.
by rewrite X.
Qed.

Lemma umall2_umcnt f1 f2 p :
        (forall k v1 v2,
           (k, v1) \In f1 -> (k, v2) \In f2 -> P v1 v2 ->
           p (k, v1) = p (k, v2)) ->
        um_all2 f1 f2 -> um_count p f1 = um_count p f2.
Proof. by move=>*; congr size; apply: umall2_dom; apply: umall2_umfilt. Qed.

Lemma umall2_find X f1 f2 (f : option V -> X) t :
        (forall k v1 v2,
           (k, v1) \In f1 -> (k, v2) \In f2 -> P v1 v2 ->
           f (Some v1) = f (Some v2)) ->
        um_all2 f1 f2 -> f (find t f1) = f (find t f2).
Proof.
move=>E /(_ t).
case E1: (find t f1)=>[v1|]; case E2: (find t f2)=>[v2|] //=.
by move/In_find: E1=>E1; move/In_find: E2=>E2; apply: E E1 E2.
Qed.

Lemma umall2fUn f f1 f2 :
        Reflexive P ->
        valid f1 = valid f2 -> um_all2 f1 f2 -> um_all2 (f \+ f1) (f \+ f2).
Proof.
move=>R Ev X; have De : dom_eq f1 f2.
- by apply/domeqP; rewrite (umall2_dom X) Ev.
move=>k; case V1 : (valid (f \+ f1)) (domeqVUnE (domeq_refl f) De)=>/esym V2;
last first.
- by move/negbT/invalidE: V1 V2=>-> /negbT/invalidE ->; rewrite find_undef.
rewrite /optionR /= !findUnL //; case: ifP=>D; last by apply: X.
by case/In_domX: D=>v /In_find ->; apply: R.
Qed.

Lemma umall2Unf f f1 f2 :
        Reflexive P ->
        valid f1 = valid f2 -> um_all2 f1 f2 -> um_all2 (f1 \+ f) (f2 \+ f).
Proof. by rewrite -!(joinC f); apply: umall2fUn. Qed.

Lemma umall2Un f1 f2 g1 g2 :
        Reflexive P -> Transitive P ->
        valid f1 = valid f2 -> valid g1 = valid g2 ->
        um_all2 f1 f2 -> um_all2 g1 g2 ->
        um_all2 (f1 \+ g1) (f2 \+ g2).
Proof.
move=>R T Ef Eg Uf Ug; apply: (@umall2_trans T (f2 \+ g1));
by [apply: umall2Unf | apply: umall2fUn].
Qed.

Lemma umall2Pt2 k1 k2 v1 v2 :
        um_all2 (pts k1 v1) (pts k2 v2) <->
        if k1 == k2 then C k1 -> P v1 v2
        else ~~ C k1 && ~~ C k2.
Proof.
split; last first.
- case: eqP=>[-> H|N /andP [C1 C2]] k.
  - by rewrite /optionR /= !findPt2; case: ifP=>// /andP [].
  by rewrite /optionR /= !findPt2 (negbTE C1) (negbTE C2) !andbF.
move=>X; move: (X k1) (X k2).
rewrite /optionR !findPt !findPt2 (eq_sym k2 k1) /=.
case: (k1 =P k2)=>[<-|N] /=; first by case: ifP.
by do 2![case: ifP].
Qed.

Lemma umall2Pt k v1 v2 :
        C k ->
        um_all2 (pts k v1) (pts k v2) <-> P v1 v2.
Proof. by move=>C'; rewrite umall2Pt2 eq_refl; split=>//; apply. Qed.

Lemma umall2cancel k v1 v2 f1 f2 :
        valid (pts k v1 \+ f1) -> valid (pts k v2 \+ f2) ->
        um_all2 (pts k v1 \+ f1) (pts k v2 \+ f2) ->
        P v1 v2 /\ um_all2 f1 f2.
Proof.
move=>V1 V2 X; split=>[|x].
- by move: (X k); rewrite !findPtUn.
move: (X x); rewrite !findPtUn2 //; case: ifP=>// /eqP -> _.
by case: dom_find (validPtUnD V1)=>// ->; case: dom_find (validPtUnD V2)=>// ->.
Qed.

Lemma umall2PtUn k v1 v2 f1 f2 :
        Reflexive P -> Transitive P ->
        valid f1 = valid f2 -> um_all2 f1 f2 ->
        P v1 v2 ->
        um_all2 (pts k v1 \+ f1) (pts k v2 \+ f2).
Proof.
move=>R T; case W : (valid (pts k v1 \+ f1)).
- move=>H1 H2 H3; apply: umall2Un=>//.
  - by rewrite !validPt (validPtUn_cond W).
  by apply/(@umall2Pt _ _ _ (validPtUn_cond W)).
case: validUn W=>//.
- rewrite validPt=>H _ _ _ _.
  have L v : pts k v = undef :> U by apply/pts_undef.
  by rewrite !L !undef_join; apply: umall2_undef.
- move=>W _; rewrite (negbTE W)=>/esym.
  move/invalidE: W=>-> /negbT/invalidE -> _ _; rewrite !join_undef.
  by apply: umall2_undef.
move=>x; rewrite domPt inE=>/andP [X /eqP <- D1] _ W /umall2_dom E _.
suff : ~~ valid (pts k v1 \+ f1) /\ ~~ valid (pts k v2 \+ f2).
- by case=>/invalidE -> /invalidE ->; apply: umall2_undef.
by rewrite !validPtUn X -W -E D1 (dom_valid D1).
Qed.

Lemma umall2fK f f1 f2 :
        valid (f \+ f1) -> valid (f \+ f2) ->
        um_all2 (f \+ f1) (f \+ f2) -> um_all2 f1 f2.
Proof.
move=>V1 V2 X k; move: (X k); rewrite !findUnL //; case: ifP=>// D _.
by case: dom_find (dom_inNL V1 D)=>// ->; case: dom_find (dom_inNL V2 D)=>// ->.
Qed.

Lemma umall2KL f1 f2 g1 g2 :
        Equivalence_rel P ->
        valid (f1 \+ g1) -> valid (f2 \+ g2) ->
        um_all2 (f1 \+ g1) (f2 \+ g2) ->
        um_all2 f1 f2 -> um_all2 g1 g2.
Proof.
move=>E; case/Equivalence_relS: E=>R S T.
move=>V1 V2 H1 Ha; have /(umall2_sym S) H2: um_all2 (f1 \+ g1) (f2 \+ g1).
- by apply: umall2Unf Ha=>//; rewrite (validL V1) (validL V2).
apply: umall2fK (V2) _; last first.
- by apply: umall2_trans H2 H1.
apply: domeqVUn (V1)=>//; apply/domeqP.
by rewrite (validL V1) (validL V2) (umall2_dom Ha).
Qed.

Lemma umall2KR f1 f2 g1 g2 :
        Equivalence_rel P ->
        valid (f1 \+ g1) -> valid (f2 \+ g2) ->
        um_all2 (f1 \+ g1) (f2 \+ g2) ->
        um_all2 g1 g2 -> um_all2 f1 f2.
Proof. by rewrite (joinC f1) (joinC f2); apply: umall2KL. Qed.

End BinaryMapAll.


(********************************************************)
(********************************************************)
(* Instance of union maps with trivially true condition *)
(********************************************************)
(********************************************************)

(* We build it over the base type with a trival condition on keys. *)
(* We seal the definition to avoid any slowdowns (just in case). *)

Module Type UMSig.
Parameter tp : ordType -> Type -> Type.

Section Params.
Variables (K : ordType) (V : Type).
Notation tp := (tp K V).

Parameter um_undef : tp.
Parameter defined : tp -> bool.
Parameter empty : tp.
Parameter upd : K -> V -> tp -> tp.
Parameter dom : tp -> seq K.
Parameter dom_eq : tp -> tp -> bool.
Parameter assocs : tp -> seq (K * V).
Parameter free : tp -> K -> tp.
Parameter find : K -> tp -> option V.
Parameter union : tp -> tp -> tp.
Parameter empb : tp -> bool.
Parameter undefb : tp -> bool.
Parameter pts : K -> V -> tp.

Parameter from : tp -> @UM.base K xpredT V.
Parameter to : @UM.base K xpredT V -> tp.

Axiom ftE : forall b, from (to b) = b.
Axiom tfE : forall f, to (from f) = f.
Axiom undefE : um_undef = to (@UM.Undef K xpredT V).
Axiom defE : forall f, defined f = UM.valid (from f).
Axiom emptyE : empty = to (@UM.empty K xpredT V).

Axiom updE : forall k v f, upd k v f = to (UM.upd k v (from f)).
Axiom domE : forall f, dom f = UM.dom (from f).
Axiom dom_eqE : forall f1 f2, dom_eq f1 f2 = UM.dom_eq (from f1) (from f2).
Axiom assocsE : forall f, assocs f = UM.assocs (from f).
Axiom freeE : forall f k, free f k = to (UM.free (from f) k).
Axiom findE : forall k f, find k f = UM.find k (from f).
Axiom unionE : forall f1 f2, union f1 f2 = to (UM.union (from f1) (from f2)).
Axiom empbE : forall f, empb f = UM.empb (from f).
Axiom undefbE : forall f, undefb f = UM.undefb (from f).
Axiom ptsE : forall k v, pts k v = to (@UM.pts K xpredT V k v).

End Params.

End UMSig.


Module UMDef : UMSig.
Section UMDef.
Variables (K : ordType) (V : Type).

Definition tp : Type := @UM.base K xpredT V.

Definition um_undef := @UM.Undef K xpredT V.
Definition defined f := @UM.valid K xpredT V f.
Definition empty := @UM.empty K xpredT V.
Definition upd k v f := @UM.upd K xpredT V k v f.
Definition dom f := @UM.dom K xpredT V f.
Definition dom_eq f1 f2 := @UM.dom_eq K xpredT V f1 f2.
Definition assocs f := @UM.assocs K xpredT V f.
Definition free f k := @UM.free K xpredT V f k.
Definition find k f := @UM.find K xpredT V k f.
Definition union f1 f2 := @UM.union K xpredT V f1 f2.
Definition empb f := @UM.empb K xpredT V f.
Definition undefb f := @UM.undefb K xpredT V f.
Definition pts k v := @UM.pts K xpredT V k v.

Definition from (f : tp) : @UM.base K xpredT V := f.
Definition to (b : @UM.base K xpredT V) : tp := b.

Lemma ftE b : from (to b) = b. Proof. by []. Qed.
Lemma tfE f : to (from f) = f. Proof. by []. Qed.
Lemma undefE : um_undef = to (@UM.Undef K xpredT V). Proof. by []. Qed.
Lemma defE f : defined f = UM.valid (from f). Proof. by []. Qed.
Lemma emptyE : empty = to (@UM.empty K xpredT V). Proof. by []. Qed.
Lemma updE k v f : upd k v f = to (UM.upd k v (from f)). Proof. by []. Qed.
Lemma domE f : dom f = UM.dom (from f). Proof. by []. Qed.
Lemma dom_eqE f1 f2 : dom_eq f1 f2 = UM.dom_eq (from f1) (from f2).
Proof. by []. Qed.
Lemma assocsE f : assocs f = UM.assocs (from f). Proof. by []. Qed.
Lemma freeE f k : free f k = to (UM.free (from f) k). Proof. by []. Qed.
Lemma findE k f : find k f = UM.find k (from f). Proof. by []. Qed.
Lemma unionE f1 f2 : union f1 f2 = to (UM.union (from f1) (from f2)).
Proof. by []. Qed.
Lemma empbE f : empb f = UM.empb (from f). Proof. by []. Qed.
Lemma undefbE f : undefb f = UM.undefb (from f). Proof. by []. Qed.
Lemma ptsE k v : pts k v = to (@UM.pts K xpredT V k v). Proof. by []. Qed.

End UMDef.
End UMDef.

Notation union_map := UMDef.tp.

Definition unionmapMixin K V :=
  UMCMixin (@UMDef.ftE K V) (@UMDef.tfE K V) (@UMDef.defE K V)
           (@UMDef.undefE K V) (@UMDef.emptyE K V) (@UMDef.updE K V)
           (@UMDef.domE K V) (@UMDef.dom_eqE K V) (@UMDef.assocsE K V)
           (@UMDef.freeE K V) (@UMDef.findE K V) (@UMDef.unionE K V)
           (@UMDef.empbE K V) (@UMDef.undefbE K V) (@UMDef.ptsE K V).

Canonical union_mapUMC K V :=
  Eval hnf in UMC (union_map K V) (@unionmapMixin K V).

(* We add the canonical projections matching against naked type *)
(* thus, there are two ways to get a PCM for a union map: *)
(* generic one going through union_map_classPCM, and another by going *)
(* through union_mapPCM. Luckily, they produce equal results *)
(* and this is just a matter of convenience *)
(* Ditto for the equality type *)

Definition union_mapPCMMix K V :=
  union_map_classPCMMix (union_mapUMC K V).
Canonical union_mapPCM K V :=
  Eval hnf in PCM (union_map K V) (@union_mapPCMMix K V).

Definition union_mapCPCMMix K V :=
  union_map_classCPCMMix (@union_mapUMC K V).
Canonical union_mapCPCM K V :=
  Eval hnf in CPCM (union_map K V) (@union_mapCPCMMix K V).

Definition union_mapTPCMMix K V :=
  union_map_classTPCMMix (@union_mapUMC K V).
Canonical union_mapTPCM K V :=
  Eval hnf in TPCM (union_map K V) (@union_mapTPCMMix K V).

Definition union_map_eqMix K (V : eqType) :=
  @union_map_class_eqMix K xpredT V _ (@unionmapMixin K V).
Canonical union_map_eqType K (V : eqType) :=
  Eval hnf in EqType (union_map K V) (@union_map_eqMix K V).

Definition um_pts (K : ordType) V (k : K) (v : V) :=
  @UMC.pts K xpredT V (@union_mapUMC K V) k v.

Notation "x \\-> v" := (@um_pts _ _ x v) (at level 30).


(* Finite sets are just union maps with unit range *)
Notation fset T := (@union_map T unit).
Notation "# x" := (x \\-> tt) (at level 20).


(* Since the union map constructors are opaque, the decidable equality *)
(* does not simplify automatically; we need to export explicit equations *)
(* for simplification. *)
(* So far, the ones we need are really just for points-to. *)

Section UMDecidableEquality.
Variables (K : ordType) (V : eqType).

Lemma umPtPtE (k1 k2 : K) (v1 v2 : V) :
        (k1 \\-> v1 == k2 \\-> v2) = (k1 == k2) && (v1 == v2).
Proof.
rewrite {1}/eq_op /= /UnionMapEq.unionmap_eq /um_pts !umEX /=.
by rewrite {1}/eq_op /= /feq eqseq_cons andbT.
Qed.

Lemma umPt0E (k : K) (v : V) : (k \\-> v == Unit) = false.
Proof. by apply: (introF idP)=>/eqP/unitbP; rewrite um_unitbPt. Qed.

Lemma um0PtE (k : K) (v : V) :
        (@Unit [pcm of union_map K V] == k \\-> v) = false.
Proof. by rewrite eq_sym umPt0E. Qed.

Lemma umPtUndefE (k : K) (v : V) : (k \\-> v == undef) = false.
Proof. by rewrite /eq_op /undef /= /UnionMapEq.unionmap_eq /um_pts !umEX. Qed.

Lemma umUndefPtE (k : K) (v : V) :
       ((undef : union_map_eqType K V) == k \\-> v) = false.
Proof. by rewrite eq_sym umPtUndefE. Qed.

Lemma umUndef0E : ((undef : union_map_eqType K V) == Unit) = false.
Proof. by apply/eqP/undef0. Qed.

Lemma um0UndefE : ((Unit : union_mapPCM K V) == undef) = false.
Proof. by rewrite eq_sym umUndef0E. Qed.

Lemma umPtUE (k : K) (v : V) f : (k \\-> v \+ f == Unit) = false.
Proof. by apply: (introF idP)=>/eqP/join0E/proj1/eqP; rewrite umPt0E. Qed.

Lemma umUPtE (k : K) (v : V) f : (f \+ k \\-> v == Unit) = false.
Proof. by rewrite joinC umPtUE. Qed.

Lemma umPtUPtE (k1 k2 : K) (v1 v2 : V) f :
        (k1 \\-> v1 \+ f == k2 \\-> v2) = [&& k1 == k2, v1 == v2 & unitb f].
Proof.
apply/idP/idP; last first.
- by case/and3P=>/eqP -> /eqP -> /unitbP ->; rewrite unitR.
move/eqP/(um_prime _); case=>//; case.
- move/(cancelPt2 _); rewrite validPt=>/(_ (erefl _)).
  by case=>->->->; rewrite !eq_refl unitb0.
by move/unitbP; rewrite um_unitbPt.
Qed.

Lemma umPtPtUE (k1 k2 : K) (v1 v2 : V) f :
        (k1 \\-> v1 == k2 \\-> v2 \+ f) = [&& k1 == k2, v1 == v2 & unitb f].
Proof. by rewrite eq_sym umPtUPtE (eq_sym k1) (eq_sym v1). Qed.

Lemma umUPtPtE (k1 k2 : K) (v1 v2 : V) f :
        (f \+ k1 \\-> v1 == k2 \\-> v2) = [&& k1 == k2, v1 == v2 & unitb f].
Proof. by rewrite joinC umPtUPtE. Qed.

Lemma umPtUPt2E (k1 k2 : K) (v1 v2 : V) f :
        (k1 \\-> v1 == f \+ k2 \\-> v2) = [&& k1 == k2, v1 == v2 & unitb f].
Proof. by rewrite joinC umPtPtUE. Qed.

Definition umE := ((((umPtPtE, umPt0E), (um0PtE, umPtUndefE)),
                    ((umUndefPtE, um0UndefE), (umUndef0E, umPtUE))),
                   (((umUPtE, umPtUPtE), (umPtPtUE, umUPtPtE, umPtUPt2E)),
                    (* plus a bunch of safe simplifications *)
                    ((unitL, unitR), (validPt, valid_unit))), (((eq_refl, unitb0),
                   (um_unitbPt, undef_join)), (join_undef, unitb_undef))).

End UMDecidableEquality.
