(*
Copyright 2017 IMDEA Software Institute
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

From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype.
From fcsl Require Import options axioms prelude.
From fcsl Require Import pcm.

(*****************)
(*****************)
(* PCM Morphisms *)
(*****************)
(*****************)

(* separating relations are generalization of disjointness *)
(* Bart Jacobs calls this orthogonality *)

Definition orth_axiom (U : pcm) (orth : rel U) :=
  [/\ (* unit is separated from unit *)
      orth Unit Unit,
      (* sep is commutative *)
      forall x y, orth x y = orth y x,
      (* sep implies validity *)
      forall x y, orth x y -> valid (x \+ y),
      (* is x is in the domain (i.e., x is considered) *)
      (* then it is separate from at least Unit *)
      forall x y, orth x y -> orth x Unit &
      (* associativity *)
      forall x y z, orth x y -> orth (x \+ y) z -> orth y z && orth x (y \+ z)].


(* separating relation doesn't have the validity requirement *)
(* this is just a pragmatic issue; removing validity makes proof obligations *)
(* much simpler. Nothing is lost by removing validity, as we always *)
(* obtain it in other ways. Though, the axioms require validity as hypothesis *)
Definition seprel_axiom (U : pcm) (sep : rel U) :=
  [/\ (* unit is separated from unit *)
      sep Unit Unit,
      (* sep is commutative *)
      (* the validity pre is necessary to get equivalence with orth *)
      (* will it be bothersome in practice? *)
      forall x y, valid (x \+ y) -> sep x y = sep y x,
      (* is x is in the domain (i.e., x is considered) *)
      (* then it is separate from at least Unit *)
      forall x y, valid (x \+ y) -> sep x y -> sep x Unit &
      (* associativity *)
      forall x y z, valid (x \+ y \+ z) ->
         sep x y -> sep (x \+ y) z -> sep y z && sep x (y \+ z)].

Lemma orth_sep (U : pcm) (sep : rel U) :
        seprel_axiom sep <-> orth_axiom (fun x y => valid (x \+ y) && sep x y).
Proof.
split.
- case=>H1 H2 H3 H4; split=>[|x y|x y|x y|x y z].
  - by rewrite unitL valid_unit H1.
  - by apply/andP/andP; case=> V; rewrite H2 (validE2 V).
  - by case/andP.
  - by case/andP=> V S; rewrite unitR (H3 x y) ?(validE2 V).
  case/andP=>_ S1 /andP [V2 S2].
  by rewrite !(andX (H4 _ _ _ V2 S1 S2)) !(validLE3 V2).
case=>H1 H2 H3 H4 H5; split=>[|x y V|x y V S|x y z V H S].
- by case/andP: H1.
- by move: (H2 x y); rewrite !(validE2 V).
- by rewrite (andX (H4 x y _)) // V S.
by move: (@H5 x y z); rewrite !(validLE3 V) H S => /(_ erefl erefl).
Qed.

(* seprel equality *)

(* because we have stripped compatability relations of the requirement *)
(* that valid (x \+ y), we have to put it back before we can prove *)
(* that cinv equals the equalizer between the given morphisms *)
Definition seprel_eq (U : pcm) (D1 D2 : rel U) :=
  forall x y, valid (x \+ y) -> D1 x y = D2 x y.

Notation "D1 =s D2" := (seprel_eq D1 D2) (at level 30).

Lemma sepEQ (U : pcm) (D1 D2 : rel U) :
        D1 =s D2 <->
        (fun x y => valid (x \+ y) && D1 x y) =2
        (fun x y => valid (x \+ y) && D2 x y).
Proof.
split; first by move=>S=>x y; case: (valid (x \+ y)) (S x y)=>// ->.
by move=>S x y V; move: (S x y); rewrite V.
Qed.

Lemma orthXEQ (U : pcm) (D1 D2 : rel U) :
        D1 =2 D2 -> orth_axiom D1 <-> orth_axiom D2.
Proof.
move=>H; split; case=>H1 H2 H3 H4 H5.
- by split=>[|x y|x y|x y|x y z]; rewrite -!H;
     [apply: H1 | apply: H2 | apply: H3 | apply: H4 | apply: H5].
by split=>[|x y|x y|x y|x y z]; rewrite !H;
   [apply: H1 | apply: H2 | apply: H3 | apply: H4 | apply: H5].
Qed.

Lemma sepXEQ (U : pcm) (D1 D2 : rel U) :
        D1 =s D2 -> seprel_axiom D1 <-> seprel_axiom D2.
Proof. by move/sepEQ=>H; rewrite !orth_sep; apply: orthXEQ. Qed.

(* Hence, given a separating relation R *)
(* we say that x \orth_R y iff valid (x \+ y) and R x y *)
(* Similarly, when R is the sep relatio of a morphism f *)
(* we will write x \orth_f y iff valid (x \+ y) and sep f x y *)

Module SepRel.
Section SepRelDef.
Variable U : pcm.

Structure mixin_of (sep : rel U) := Mixin {
  _ : seprel_axiom sep}.

Section ClassDef.

Notation class_of := mixin_of (only parsing).

Structure type : Type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> rel.

Variable (p : rel U) (cp : type).
Definition class := let: Pack _ c as cT' := cp return class_of cT' in c.
Definition clone c of phant_id class c := @Pack p c.
Definition pack c := @Pack p c.

End ClassDef.
End SepRelDef.

Module Exports.
Coercion sort : type >-> rel.
Notation sep_rel := type.

Notation "[ 'seprelMixin' 'of' R ]" := (class _ : mixin_of R)
  (at level 0, format "[ 'seprelMixin'  'of'  R ]") : pcm_scope.
Notation "[ 'seprel' 'of' R 'for' S ]" := (@clone _ R S _ idfun)
  (at level 0, format "[ 'seprel'  'of'  R  'for'  S ]") : pcm_scope.
Notation "[ 'seprel' 'of' R ]" := (@clone _ R _ _ id)
  (at level 0, format "[ 'seprel'  'of'  R ]") : pcm_scope.

Definition seprel (U : pcm) (sep : rel U) :=
  fun pf : seprel_axiom sep => @pack U sep (Mixin pf).
Arguments seprel {U}.

Section Laws.
Variables (U : pcm) (sep : sep_rel U).

Lemma sepax : seprel_axiom sep.
Proof. by case: sep=>s []. Qed.

Lemma sep00 : sep Unit Unit.
Proof. by case: sep=>r [[H ???]]; apply: H. Qed.

Lemma sepC x y : valid (x \+ y) -> sep x y = sep y x.
Proof. by case: sep=>r [[? H ??]]; apply: H. Qed.

Lemma sepx0 x y : valid (x \+ y) -> sep x y -> sep x Unit.
Proof. by case: sep=>r [[?? H ?]]; apply: H. Qed.

(* The order of the rewrite rules in the conclusion is important for
   backwards reasoning: [sep x (y \+ z)] is more specific than [sep y z] and
   hence [rewrite] should be able to do its work;
   had we chosen to put [sep y z] first, [rewrite] would fail because of
   the indefinite pattern *)
Lemma sepAx x y z :
        valid (x \+ y \+ z) ->
        sep x y -> sep (x \+ y) z -> sep x (y \+ z) * sep y z.
Proof.
by case: sep=>r [[??? H]] V R1 R2 /=; rewrite !(andX (H _ _ _ V R1 R2)).
Qed.

(* derived lemmas *)

Lemma sep0x x y : valid (x \+ y) -> sep x y -> sep Unit y.
Proof.
rewrite joinC=>V.
by rewrite -!(@sepC y) ?unitR ?(validE2 V) //; apply: sepx0.
Qed.

Lemma sep0E x y : valid (x \+ y) -> sep x y -> sep x Unit * sep y Unit.
Proof.
by move=>V S; rewrite (sepx0 V S) sepC ?unitR ?(validE2 V) // (sep0x V S).
Qed.

(* This is a helper lemma -- in most cases you may want to use
   sepAxx or sepxxA instead *)
Lemma sepAx23_helper x y z :
        valid (x \+ y \+ z) ->
        sep x y -> sep (x \+ y) z ->
        ((sep x z * sep z x) * (sep y z * sep z y)) *
        ((sep x (y \+ z) * sep x (z \+ y)) *
         (sep y (x \+ z) * sep y (z \+ x))).
Proof.
move=>V S1 S2.
rewrite !(@sepC z) ?(validLE3 V) // !(joinC z) !(sepAx V S1 S2).
rewrite sepC ?(validLE3 V) // in S1; rewrite (joinC x) in V S2.
by rewrite !(sepAx V S1 S2).
Qed.

(* This is useful for backward reasoning, because we don't want to
   depend on the exact permutation of x, y, z the rewrite rules (see below)
   will choose *)
Lemma sepxA x y z :
        valid (x \+ (y \+ z)) ->
        sep y z -> sep x (y \+ z) -> sep (x \+ y) z * sep x y.
Proof.
move=>V S1; rewrite sepC // => S2.
rewrite (@sepC _ z) -?joinA //; rewrite joinC in V.
by rewrite (@sepC _ y) ?(validLE3 V) // !(sepAx23_helper V S1 S2).
Qed.

(* nested pairs are a workaround for https://github.com/coq/coq/issues/8304 *)
Lemma sepAxx x y z :
        valid (x \+ y \+ z) ->
        sep x y -> sep (x \+ y) z ->
        (((sep x (y \+ z) * sep x (z \+ y)) *
          (sep y (x \+ z) * sep y (z \+ x))) *
         ((sep z (x \+ y) * sep z (y \+ x)) *
          (sep (y \+ z) x * sep (z \+ y) x))) *
        (((sep (x \+ z) y * sep (z \+ x) y) *
          (sep (x \+ y) z * sep (y \+ x) z)) *
         (((sep x y * sep y x) *
           (sep x z * sep z x)))) *
        (sep y z * sep z y).
Proof.
move=>V S1 S2; rewrite S1 S2 !(sepAx23_helper V S1 S2).
rewrite -(sepC (validL V)) S1.
rewrite (joinC y) -sepC // S2;
rewrite -(joinC y) sepC 1?joinC ?joinA // (sepAx23_helper V S1 S2).
by rewrite -(joinC x) sepC 1?joinAC // (sepAx23_helper V S1 S2).
Qed.

(* same results, flipped hypotheses *)
(* nested pairs are a workaround for https://github.com/coq/coq/issues/8304 *)
Lemma sepxxA x y z :
        valid (x \+ (y \+ z)) ->
        sep y z -> sep x (y \+ z) ->
        (((sep x (y \+ z) * sep x (z \+ y)) *
          (sep y (x \+ z) * sep y (z \+ x))) *
         ((sep z (x \+ y) * sep z (y \+ x)) *
          (sep (y \+ z) x * sep (z \+ y) x))) *
        (((sep (x \+ z) y * sep (z \+ x) y) *
          (sep (x \+ y) z * sep (y \+ x) z)) *
         (((sep x y * sep y x) *
           (sep x z * sep z x)))) *
        (sep y z * sep z y).
Proof.
rewrite joinA=> V; rewrite {1}(@sepC x) ?(validLE3 V) // => S1 S2.
by apply: (sepAxx V); rewrite (joinC x) joinAC in V; rewrite !(sepAxx V S1 S2).
Qed.

Lemma sepU0 x y : valid (x \+ y) -> sep x y -> sep (x \+ y) Unit.
Proof.
move=>V S1. move/(sepx0 V): S1 (S1)=>S1 S2.
rewrite -[x]unitR in V S2.
by rewrite sepC ?(sepAxx V S1 S2) // joinAC.
Qed.

Lemma sep0U x y : valid (x \+ y) -> sep x y -> sep Unit (x \+ y).
Proof. by move=>V S; rewrite sepC ?unitL //; apply: sepU0. Qed.

End Laws.

(* some example sep relations *)

(* always-true relation *)
Definition sepT U (x y : U) := true.

Lemma sepT_seprel_ax (U : pcm) : seprel_axiom (@sepT U).
Proof. by []. Qed.

Canonical sepT_seprel (U : pcm) :=
  Eval hnf in seprel (@sepT U) (@sepT_seprel_ax U).

#[export]
Hint Resolve sepT_seprel : core.

(* always-unit relation *)
(* always-false relation is not seprel, because we need sep0 Unit Unit *)
(* i.e., sep0 is really the smallest seprel we can have *)
Definition sep0 (U : tpcm) (x y : U) := unitb x && unitb y.

Prenex Implicits sep0.

Lemma sep0_seprel_ax (U : tpcm) : seprel_axiom (@sep0 U).
Proof.
rewrite /sep0; split=>[|x y|x y|x y z].
- by rewrite tpcmE.
- by rewrite andbC.
- by move=>V /andP [->]; rewrite tpcmE.
move=>V /andP [/unitbP -> /unitbP ->] /andP [_ /unitbP ->].
by rewrite unitL !tpcmE.
Qed.

Canonical sepU_seprel U := Eval hnf in seprel (@sep0 U) (@sep0_seprel_ax U).

(* conjunction of seprels is seprel *)

Definition sepI U (R1 R2 : rel U) (x y : U) := R1 x y && R2 x y.

Lemma sepI_seprel_ax (U : pcm) (R1 R2 : sep_rel U) : seprel_axiom (sepI R1 R2).
Proof.
rewrite /sepI; split=>[|x y|x y|x y z].
- by rewrite !sep00.
- by move=>D; rewrite sepC //= [in X in _ && X]sepC.
- by move=>D /andP [X H]; rewrite (sepx0 D X) (sepx0 D H).
move=>D /andP [S1 H1] /andP [S2 H2].
by rewrite !(sepAxx D S1 S2) !(sepAxx D H1 H2).
Qed.

Canonical sepI_seprel U (R1 R2 : sep_rel U) :=
  Eval hnf in seprel (sepI R1 R2) (@sepI_seprel_ax U R1 R2).

(* three-way conjunction is also useful *)
Definition sep3I U (R1 R2 R3 : rel U) (x y : U) :=
  [&& R1 x y, R2 x y & R3 x y].

Lemma sep3I_seprel_ax (U : pcm) (R1 R2 R3 : sep_rel U) :
        seprel_axiom (sep3I R1 R2 R3).
Proof.
rewrite /sep3I; split=>[|x y|x y|x y z].
- by rewrite !sep00.
- by move=>D; rewrite (sepC R1 D) (sepC R2 D) (sepC R3 D).
- move=>D /and3P [X1 X2 X3].
  by rewrite (sepx0 D X1) (sepx0 D X2) (sepx0 D X3).
move=>D /and3P [X11 X12 X13] /and3P [X21 X22 X23].
by rewrite !(sepAxx D X11 X21) !(sepAxx D X12 X22) !(sepAxx D X13 X23).
Qed.

Canonical sep3I_seprel U (R1 R2 R3 : sep_rel U) :=
  Eval hnf in seprel (sep3I R1 R2 R3) (@sep3I_seprel_ax U R1 R2 R3).

(* pairwise product of seprels is seprel *)

Definition sep_prod U1 U2 (R1 : rel U1) (R2 : rel U2) (x y : U1 * U2) :=
  R1 x.1 y.1 && R2 x.2 y.2.

Lemma sep_prod_seprel_ax U1 U2 (R1 : sep_rel U1) (R2 : sep_rel U2) :
  seprel_axiom (sep_prod R1 R2).
Proof.
rewrite /sep_prod; split=>[|x y|x y|x y z].
- by rewrite !sep00.
- by case/andP=>/sepC -> /sepC ->.
- by case/andP=>?? /andP [/sepx0 -> // /sepx0 ->].
case/andP=>V1 V2 /andP [D1 D2] /andP [/= Z1 Z2].
by rewrite !(sepAxx V1 D1 Z1) !(sepAxx V2 D2 Z2).
Qed.

Canonical sep_prod_seprel U1 U2 (R1 : sep_rel U1) (R2 : sep_rel U2) :=
  Eval hnf in seprel (sep_prod R1 R2) (sep_prod_seprel_ax R1 R2).

End Exports.
End SepRel.

Export SepRel.Exports.


(* Now we can define a morphism to come with a sep relation *)
(* on which it is valid *)

Definition morph_axiom (U V : pcm) (sep : rel U) (f : U -> V) :=
  [/\ (* f preserves unit *)
      f Unit = Unit &
      (* f is defined on the domain and preserves joins on the domain *)
      forall x y, valid (x \+ y) -> sep x y ->
                  valid (f x \+ f y) /\ f (x \+ y) = f x \+ f y].

Section MorphismStructure.
Variables U V : pcm.

Structure morphism (D : rel U) : Type := Morphism' {
  mfun :> U -> PCM.sort V;
  _ : morph_axiom D mfun}.

Definition morphism_for (D : rel U) of phant V := morphism D.

Definition clone_morphism (D : rel U) f :=
  let: @Morphism' _ _ pf := f
    return {type of @Morphism' D for f} ->
      morphism_for D (Phant V)
  in fun k => k pf.

End MorphismStructure.

Arguments Morphism' [U V D] mfun _.

Notation "{ 'morphism' D >-> V }" := (morphism_for D (Phant V))
  (at level 0, format "{ 'morphism'  D  >->  V }") : pcm_scope.
Notation "[ 'morphism' D 'of' f ]" :=
  (clone_morphism (@Morphism' _ _ D f))
  (at level 0, format "[ 'morphism'  D  'of'  f ]") : pcm_scope.
Notation "[ 'morphism' 'of' f ]" :=
  (clone_morphism (@Morphism' _ _ _ f))
  (at level 0, format "[ 'morphism'  'of'  f ]") : pcm_scope.

Definition Morphism (U V : pcm) (D : rel U) f :=
  fun (p1 : f Unit = Unit)
      (p2 : forall x y, valid (x \+ y) -> D x y ->
              valid (f x \+ f y) /\ f (x \+ y) = f x \+ f y) =>
    @Morphism' U V D f (conj p1 p2).
Arguments Morphism [U V].

Section Laws.
Variables (U V : pcm) (D : rel U) (f : {morphism D >-> V}).

Lemma pfmorph_ax : morph_axiom D f.
Proof. by case: f. Qed.

Lemma pfunit : f Unit = Unit.
Proof. by case: f=>g [H1 H2]; apply: H1. Qed.

Lemma pfjoinV x y :
        valid (x \+ y) -> D x y ->
        valid (f x \+ f y) /\ f (x \+ y) = f x \+ f y.
Proof. by case: f=>g [H1 H2]; apply: H2. Qed.

(* derived laws *)

Lemma pfV2 x y : valid (x \+ y) -> D x y -> valid (f x \+ f y).
Proof. by move=>H S; case: (pfjoinV H S). Qed.

Lemma pfjoin x y : valid (x \+ y) -> D x y -> f (x \+ y) = f x \+ f y.
Proof. by move=>H S; case: (pfjoinV H S). Qed.

Lemma joinpf x y : valid (x \+ y) -> D x y -> f x \+ f y = f (x \+ y).
Proof. by move=>*; rewrite pfjoin. Qed.

End Laws.

(* some lemmas when D is a seprel *)

Lemma pfV (U : pcm) V (D : rel U) (f : @morphism U V D) x :
        valid x -> D x Unit -> valid (f x).
Proof. by rewrite -{1 3}[x]unitR=>W S; rewrite pfjoin //; apply: pfV2. Qed.

Lemma pfV3 (U : pcm) V (D : rel U) (f : @morphism U V D) x y z:
  valid (x \+ y \+ z) -> D x y -> D (x \+ y) z -> valid (f x \+ f y \+ f z).
Proof. by move=>W D1 D2;rewrite -pfjoin ?(validL W) // pfV2 //=. Qed.

(* a version of pfV2 where the morphism structure *)
(* is inferred from phantoms *)

Lemma pfV2_phant U V D (f : @morphism U V D) of phantom (_ -> _) f :
        forall x y, valid (x \+ y) -> D x y -> valid (f x \+ f y).
Proof. by move=>x y; apply: pfV2. Qed.

Notation pfVf f := (@pfV2_phant _ _ _ _ (Phantom (_ -> _) f)).

(* Domain sep_rel, preimage, kernel, restriction of morphism *)
(* use phantoms to infer the morphism structure *)
(* and uncover D *)
(* we make these constructions only when D is a seprel *)
(* because it's strange in lemmas when they are not *)

Definition sep (U : pcm) V D (f : @morphism U V D)
  of phantom (U -> V) f := D : rel U.

Definition preim (U : pcm) V (D : rel U) (f : @morphism U V D) (R : rel V)
  of phantom (U -> V) f : rel U :=
  fun x y => D x y && R (f x) (f y).

(* kernel is given with a tpcm range because we need decidable test for unit *)
(* we may have gone with eqpcms too, which have decidable tests for everything, *)
(* unit included *)

Definition ker (U : pcm) (V : tpcm) (D : rel U) (f : @morphism U V D)
  of phantom (U -> V) f : rel U :=
  fun x y => D x y && sep0 (f x) (f y).

(* res requires a tpcm range because it needs to make a result undefined *)
Definition res (U : pcm) (V : tpcm) (f : U -> V) (S : rel U) :=
  fun x : U => if S x Unit then f x else undef.

(* equalizer *)
Definition eqlz (U : pcm) (V : eqpcm) (D1 D2 : rel U)
                (f1 : @morphism U V D1) (f2 : @morphism U V D2)
  of phantom (U -> V) f1 & phantom (U -> V) f2 : rel U :=
  fun x y => [&& D1 x y, D2 x y, f1 x == f2 x & f1 y == f2 y].

(* sep-rel of a join *)
Definition sep_join (U V : pcm) (D1 D2 : rel U)
                    (f1 : @morphism U V D1) (f2 : @morphism U V D2)
  of phantom (U -> V) f1 & phantom (U -> V) f2 :=
  fun x y => [&& D1 x y, D2 x y & valid ((f1 x \+ f2 x) \+ (f1 y \+ f2 y))].

(* join *)
Definition join (U V : pcm) (D1 D2 : rel U)
                (f1 : @morphism U V D1) (f2 : @morphism U V D2)
  of phantom (U -> V) f1 & phantom (U -> V) f2 :=
  fun x : U => f1 x \+ f2 x.

(* Notation for the ops *)
Notation "''sep' f" := (sep (Phantom (_ -> _) f))
  (at level 10, f at level 8, format "''sep'  f") : pcm_scope.

Notation "''preim' f R" := (preim R (Phantom (_ -> _) f))
  (at level 10, f at level 2, R at level 8, format "''preim'  f  R") : pcm_scope.

Notation "''ker' f" := (ker (Phantom (_ -> _) f))
  (at level 10, f at level 8, format "''ker'  f") : pcm_scope.

Notation "''res_' S f" := (res f S)
  (at level 10, S at level 2, f at level 8, format "''res_' S  f") : pcm_scope.

Notation "''eqlz' f1 f2" := (eqlz (Phantom (_ -> _) f1) (Phantom (_ -> _) f2))
  (at level 10, f1 at level 2, f2 at level 2,
      format "''eqlz'  f1  f2") : pcm_scope.

Notation "''sep_join' f1 f2" :=
  (sep_join (Phantom (_ -> _) f1) (Phantom (_ -> _) f2))
  (at level 10, f1 at level 2, f2 at level 2,
      format "''sep_join'  f1  f2") : pcm_scope.

Notation "''join' f1 f2" := (join (Phantom (_ -> _) f1) (Phantom (_ -> _) f2))
  (at level 10, f1 at level 2, f2 at level 2,
      format "''join'  f1  f2") : pcm_scope.

(* unfolding the defs to get rid of phantoms *)
Lemma sepX (U : pcm) V (D : rel U) (f : @morphism U V D) : 'sep f = D.
Proof. by []. Qed.

Lemma preimX (U : pcm) V (D : rel U) (f : @morphism U V D) (R : rel V) x y :
        'preim f R x y = D x y && R (f x) (f y).
Proof. by []. Qed.

Lemma kerX (U : pcm) (V : tpcm) (D : rel U) (f : @morphism U V D) x y :
        'ker f x y = [&& D x y, unitb (f x) & unitb (f y)].
Proof. by []. Qed.

Lemma resX U (V : tpcm) D (f : @morphism U V D) S x :
        'res_S f x = if S x Unit then f x else undef.
Proof. by []. Qed.

Lemma eqlzX (U : pcm) (V : eqpcm) D1 D2
            (f1 : @morphism U V D1) (f2 : @morphism U V D2) x y :
        'eqlz f1 f2 x y = [&& D1 x y, D2 x y, f1 x == f2 x & f1 y == f2 y].
Proof. by []. Qed.

Lemma sep_joinX (U V : pcm) D1 D2
                 (f1 : @morphism U V D1) (f2 : @morphism U V D2) x y :
        'sep_join f1 f2 x y =
        [&& D1 x y, D2 x y & valid ((f1 x \+ f2 x) \+ (f1 y \+ f2 y))].
Proof. by []. Qed.

Lemma joinX (U V : pcm) D1 D2
            (f1 : @morphism U V D1) (f2 : @morphism U V D2) x :
        'join f1 f2 x = f1 x \+ f2 x.
Proof. by []. Qed.

(* most of the time we just want to unfold everything *)
Definition sepE := (((sepX, preimX), (kerX, resX)), ((eqlzX, sep_joinX), joinX)).

(* lemmas that obtain when D's are seprels *)
Section MorphPCMLemmas.
Variables (U V : pcm) (D : sep_rel U) (f : {morphism D >-> V}).

Lemma sep_seprel_ax : seprel_axiom D.
Proof. by case: D=>r []. Qed.

Canonical sep_seprel := Eval hnf in seprel ('sep f) sep_seprel_ax.

Variable R : sep_rel V.

Lemma preim_seprel_ax : seprel_axiom ('preim f R).
Proof.
rewrite /preim; split=>[|x y|x y|x y z]; first by rewrite !pfunit !sep00.
- move=>H; rewrite sepC //=; case S: (D y x)=>//=.
  by rewrite -sepC // pfV2 // joinC.
- move=>H /andP [H1 H2].
  by rewrite !pfunit (sep0E H H1) (sep0E _ H2) // pfV2.
move=>H /andP [G1 F1] /andP [G2 F2].
rewrite pfjoin ?(validLE3 H) // in F2.
rewrite pfjoin ?(validLE3 H) ?(sepAxx H G1 G2) //=.
move: (pfVf f H G2); rewrite pfjoin ?(validLE3 H) // => D2.
by rewrite !(sepAxx D2 F1 F2).
Qed.

Canonical preim_seprel :=
  Eval hnf in seprel ('preim f R) preim_seprel_ax.

End MorphPCMLemmas.


Section MorphTPCMLemmas.
Variable (U : pcm) (V : tpcm) (D : sep_rel U) (f : {morphism D >-> V}).

Lemma ker_seprel_ax : seprel_axiom ('ker f).
Proof. by apply: preim_seprel_ax. Qed.

Canonical ker_seprel := Eval hnf in seprel ('ker f) ker_seprel_ax.

Variable S : sep_rel U.

Lemma res_morph_ax : morph_axiom (sepI S D) ('res_S f).
Proof.
rewrite /res; split=>[|x y]; first by rewrite sep00 pfunit.
by move=>W /andP [X H]; rewrite !(sep0E W X) (sepU0 W X) pfjoin // pfV2.
Qed.

Canonical res_morph := Morphism' ('res_S f) res_morph_ax.

End MorphTPCMLemmas.


(* equalizer is a sep_rel (i.e., compatibility relation) *)
Section MorphEQLZLemmas.
Variables (U : pcm) (V : eqpcm) (D1 D2 : sep_rel U).
Variables (f1 : @morphism U V D1) (f2 : @morphism U V D2).

Lemma eqlz_seprel_ax : seprel_axiom ('eqlz f1 f2).
Proof.
rewrite /eqlz; split=>[|x y W|x y W|x y z W].
- by rewrite !sep00 !pfunit eq_refl.
- by rewrite !andbA andbAC (sepC D1) // (sepC D2).
- by case/and4P=>V1 V2 -> _; rewrite (sepx0 W V1) (sepx0 W V2) !pfunit eq_refl.
case/and4P=>V1 V2 Ex Ey /and4P [W1 W2 _ Ez].
set j1 := (sepAxx W V1 W1); set j2 := (sepAxx W V2 W2).
by rewrite !pfjoin ?j1 ?j2 ?(validLE3 W) //= Ex (eqP Ey) (eqP Ez) !eq_refl.
Qed.

Canonical eqlz_seprel := Eval hnf in seprel ('eqlz f1 f2) eqlz_seprel_ax.

End MorphEQLZLemmas.

(* join of morphisms is a morphism *)
Section MorphJoinLemmas.
Variables (U V : pcm) (D1 D2 : sep_rel U).
Variables (f1 : @morphism U V D1) (f2 : @morphism U V D2).

Lemma sepjoin_seprel_ax : seprel_axiom ('sep_join f1 f2).
Proof.
rewrite /sep_join; split=>[|x y W|x y W|x y z W].
- by rewrite !sep00 ?unitL !pfunit ?unitL valid_unit.
- by rewrite (sepC D1) // (sepC D2) // (joinC (f1 x \+ f2 x)).
- case/and3P=>V1 V2; rewrite (sepx0 W V1) (sepx0 W V2) !pfunit // !unitR.
  by apply: validL.
case/and3P=>V1 V2 Wa /and3P [W1 W2].
set j1 := (sepAxx W V1 W1); set j2 := (sepAxx W V2 W2).
rewrite !pfjoin ?j1 ?j2 ?(validLE3 W) //=.
rewrite !(pull (f2 y)) !joinA !(pull (f1 y)) !joinA.
rewrite !(pull (f2 x)) !joinA  !(pull (f1 x)) -!joinA=>Wb.
by rewrite !(validRE3 Wb).
Qed.

Canonical sepjoin_seprel :=
  Eval hnf in seprel ('sep_join f1 f2) sepjoin_seprel_ax.

Lemma join_morph_ax : morph_axiom ('sep_join f1 f2) ('join f1 f2).
Proof.
rewrite /join; split=>[|x y]; first by rewrite !pfunit unitL.
move=>W /and3P [V1 V2]; rewrite !pfjoin // !joinA.
by rewrite !(pull (f2 x)) !joinA !(pull (f1 x)).
Qed.

Canonical join_morph := Morphism' ('join f1 f2) join_morph_ax.

End MorphJoinLemmas.


(* morphisms compose *)
Section CategoricalDefs.
Variables (U V W : pcm) (Du : rel U) (Dv : rel V).
Variable f : {morphism Du >-> V}.
Variable g : {morphism Dv >-> W}.

(* identity is a morphism *)
Lemma id_morph_ax : morph_axiom (@sepT U) (@idfun U).
Proof. by []. Qed.

Canonical id_morph := Eval hnf in Morphism' (@idfun U) id_morph_ax.

Lemma comp_morph_ax : morph_axiom ('preim f Dv) (g \o f).
Proof.
split=>[|x y] /=; first by rewrite !pfunit.
by rewrite /preim => D /andP [H1 H2]; rewrite !pfjoin // !pfV2.
Qed.

Canonical comp_morph := Morphism' (g \o f) comp_morph_ax.

End CategoricalDefs.

(* morphism equality is function equality *)
(* ie. we don't take domains into consideration *)
(* thus, the categorical laws trivially hold *)
Section CategoricalLaws.
Variables U V W X : pcm.
Variables (Df : rel V) (f : {morphism Df >-> U}).
Variables (Dg : rel W) (g : {morphism Dg >-> V}).
Variables (Dh : rel W) (h : {morphism Dh >-> W}).

Lemma morph0L : f \o idfun = f. Proof. by []. Qed.
Lemma morph0R : idfun \o f = f. Proof. by []. Qed.
Lemma morphA : f \o (g \o h) = (f \o g) \o h. Proof. by []. Qed.

End CategoricalLaws.

(* pairwise product of morphisms is a morphism *)
Section ProdMorph.
Variables U1 U2 V1 V2 : pcm.
Variables (D1 : rel U1) (f1 : {morphism D1 >-> V1}).
Variables (D2 : rel U2) (f2 : {morphism D2 >-> V2}).

Lemma fprod_morph_ax : morph_axiom (sep_prod D1 D2) (f1 \* f2).
Proof.
rewrite /fprod; split=>[|x y]; first by rewrite !pfunit.
by case/andP=>/= W1 W2 /andP [H1 H2]; rewrite !pfV2 /= ?(pfjoin,W1,W2).
Qed.

Canonical fprod_morph := Morphism' (f1 \* f2) fprod_morph_ax.

End ProdMorph.


(* projections are morphisms *)
Section ProjectionsMorph.
Variables (U1 U2 : pcm).

Lemma fst_morph_ax : morph_axiom (@sepT (prodPCM U1 U2)) fst.
Proof. by split=>[|x y]; rewrite ?pcmPE //= =>/andP []. Qed.

Canonical fst_morph := Morphism' fst fst_morph_ax.

Lemma snd_morph_ax : morph_axiom (@sepT (prodPCM U1 U2)) snd.
Proof. by split=>[|x y]; rewrite ?pcmPE //= =>/andP []. Qed.

Canonical snd_morph := Morphism' snd snd_morph_ax.
End ProjectionsMorph.

(* also for explicit triples *)
Section ProjectionsMorph3.
Variables (U1 U2 U3 : pcm).

Lemma pcm31_morph_ax : morph_axiom (@sepT (prod3_PCM U1 U2 U3)) pcm31.
Proof. by split=>[|x y]; rewrite !pcmE /= !pcmE //= =>/and3P []. Qed.
Canonical pcm31_morph := Morphism' pcm31 pcm31_morph_ax.

Lemma pcm32_morph_ax : morph_axiom (@sepT (prod3_PCM U1 U2 U3)) pcm32.
Proof. by split=>[|x y]; rewrite !pcmE /= !pcmE // =>/and3P []. Qed.
Canonical pcm32_morph := Morphism' pcm32 pcm32_morph_ax.

Lemma pcm33_morph_ax : morph_axiom (@sepT (prod3_PCM U1 U2 U3)) pcm33.
Proof. by split=>[|x y]; rewrite !pcmE /= !pcmE // =>/and3P []. Qed.
Canonical pcm3_morph := Morphism' pcm33 pcm33_morph_ax.
End ProjectionsMorph3.

(* also for explicit 4-tuples *)
Section ProjectionsMorph4.
Variables (U1 U2 U3 U4 : pcm).

Lemma pcm41_morph_ax : morph_axiom (@sepT (prod4_PCM U1 U2 U3 U4)) pcm41.
Proof. by split=>[|x y]; rewrite !pcmE /= !pcmE //= =>/and4P []. Qed.
Canonical pcm41_morph := Morphism' pcm41 pcm41_morph_ax.

Lemma pcm42_morph_ax : morph_axiom (@sepT (prod4_PCM U1 U2 U3 U4)) pcm42.
Proof. by split=>[|x y]; rewrite !pcmE /= !pcmE //= =>/and4P []. Qed.
Canonical pcm42_morph := Morphism' pcm42 pcm42_morph_ax.

Lemma pcm43_morph_ax : morph_axiom (@sepT (prod4_PCM U1 U2 U3 U4)) pcm43.
Proof. by split=>[|x y]; rewrite !pcmE /= !pcmE //= =>/and4P []. Qed.
Canonical pcm43_morph := Morphism' pcm43 pcm43_morph_ax.

Lemma pcm44_morph_ax : morph_axiom (@sepT (prod4_PCM U1 U2 U3 U4)) pcm44.
Proof. by split=>[|x y]; rewrite !pcmE /= !pcmE //= =>/and4P []. Qed.
Canonical pcm44_morph := Morphism' pcm44 pcm44_morph_ax.
End ProjectionsMorph4.

(* and 5-tuples *)
Section ProjectionsMorph5.
Variables (U1 U2 U3 U4 U5 : pcm).

Lemma pcm51_morph_ax : morph_axiom (@sepT (prod5_PCM U1 U2 U3 U4 U5)) pcm51.
Proof. by split=>[|x y]; rewrite !pcmE /= !pcmE //= =>/and4P []. Qed.
Canonical pcm51_morph := Morphism' pcm51 pcm51_morph_ax.

Lemma pcm52_morph_ax : morph_axiom (@sepT (prod5_PCM U1 U2 U3 U4 U5)) pcm52.
Proof. by split=>[|x y]; rewrite !pcmE /= !pcmE //= =>/and4P []. Qed.
Canonical pcm52_morph := Morphism' pcm52 pcm52_morph_ax.

Lemma pcm53_morph_ax : morph_axiom (@sepT (prod5_PCM U1 U2 U3 U4 U5)) pcm53.
Proof. by split=>[|x y]; rewrite !pcmE /= !pcmE //= =>/and4P []. Qed.
Canonical pcm53_morph := Morphism' pcm53 pcm53_morph_ax.

Lemma pcm54_morph_ax : morph_axiom (@sepT (prod5_PCM U1 U2 U3 U4 U5)) pcm54.
Proof. by split=>[|x y]; rewrite !pcmE /= !pcmE //= =>/and5P []. Qed.
Canonical pcm54_morph := Morphism' pcm54 pcm54_morph_ax.

Lemma pcm55_morph_ax : morph_axiom (@sepT (prod5_PCM U1 U2 U3 U4 U5)) pcm55.
Proof. by split=>[|x y]; rewrite !pcmE /= !pcmE //= =>/and5P []. Qed.
Canonical pcm55_morph := Morphism' pcm55 pcm55_morph_ax.

End ProjectionsMorph5.

(* and 6-tuples *)
Section ProjectionsMorph6.
Variables (U1 U2 U3 U4 U5 U6 : pcm).

Lemma pcm61_morph_ax : morph_axiom (@sepT (prod6_PCM U1 U2 U3 U4 U5 U6)) pcm61.
Proof. by split=>[|x y]; rewrite !pcmE /= !pcmE //= =>/and6P []. Qed.
Canonical pcm61_morph := Morphism' pcm61 pcm61_morph_ax.

Lemma pcm62_morph_ax : morph_axiom (@sepT (prod6_PCM U1 U2 U3 U4 U5 U6)) pcm62.
Proof. by split=>[|x y]; rewrite !pcmE /= !pcmE //= =>/and6P []. Qed.
Canonical pcm62_morph := Morphism' pcm62 pcm62_morph_ax.

Lemma pcm63_morph_ax : morph_axiom (@sepT (prod6_PCM U1 U2 U3 U4 U5 U6)) pcm63.
Proof. by split=>[|x y]; rewrite !pcmE /= !pcmE //= =>/and6P []. Qed.
Canonical pcm63_morph := Morphism' pcm63 pcm63_morph_ax.

Lemma pcm64_morph_ax : morph_axiom (@sepT (prod6_PCM U1 U2 U3 U4 U5 U6)) pcm64.
Proof. by split=>[|x y]; rewrite !pcmE /= !pcmE //= =>/and6P []. Qed.
Canonical pcm64_morph := Morphism' pcm64 pcm64_morph_ax.

Lemma pcm65_morph_ax : morph_axiom (@sepT (prod6_PCM U1 U2 U3 U4 U5 U6)) pcm65.
Proof. by split=>[|x y]; rewrite !pcmE /= !pcmE //= =>/and6P []. Qed.
Canonical pcm65_morph := Morphism' pcm65 pcm65_morph_ax.

Lemma pcm66_morph_ax : morph_axiom (@sepT (prod6_PCM U1 U2 U3 U4 U5 U6)) pcm66.
Proof. by split=>[|x y]; rewrite !pcmE /= !pcmE //= =>/and6P []. Qed.
Canonical pcm66_morph := Morphism' pcm66 pcm66_morph_ax.

End ProjectionsMorph6.

(* and 7-tuples *)
Section ProjectionsMorph7.
Variables (U1 U2 U3 U4 U5 U6 U7 : pcm).

Lemma pcm71_morph_ax : morph_axiom (@sepT (prod7_PCM U1 U2 U3 U4 U5 U6 U7)) pcm71.
Proof. by split=>[|x y]; rewrite !pcmE /= !pcmE //= =>/and7P []. Qed.
Canonical pcm71_morph := Morphism' pcm71 pcm71_morph_ax.

Lemma pcm72_morph_ax : morph_axiom (@sepT (prod7_PCM U1 U2 U3 U4 U5 U6 U7)) pcm72.
Proof. by split=>[|x y]; rewrite !pcmE /= !pcmE //= =>/and7P []. Qed.
Canonical pcm72_morph := Morphism' pcm72 pcm72_morph_ax.

Lemma pcm73_morph_ax : morph_axiom (@sepT (prod7_PCM U1 U2 U3 U4 U5 U6 U7)) pcm73.
Proof. by split=>[|x y]; rewrite !pcmE /= !pcmE //= =>/and7P []. Qed.
Canonical pcm73_morph := Morphism' pcm73 pcm73_morph_ax.

Lemma pcm74_morph_ax : morph_axiom (@sepT (prod7_PCM U1 U2 U3 U4 U5 U6 U7)) pcm74.
Proof. by split=>[|x y]; rewrite !pcmE /= !pcmE //= =>/and7P []. Qed.
Canonical pcm74_morph := Morphism' pcm74 pcm74_morph_ax.

Lemma pcm75_morph_ax : morph_axiom (@sepT (prod7_PCM U1 U2 U3 U4 U5 U6 U7)) pcm75.
Proof. by split=>[|x y]; rewrite !pcmE /= !pcmE //= =>/and7P []. Qed.
Canonical pcm75_morph := Morphism' pcm75 pcm75_morph_ax.

Lemma pcm76_morph_ax : morph_axiom (@sepT (prod7_PCM U1 U2 U3 U4 U5 U6 U7)) pcm76.
Proof. by split=>[|x y]; rewrite !pcmE /= !pcmE //= =>/and7P []. Qed.
Canonical pcm76_morph := Morphism' pcm76 pcm76_morph_ax.

Lemma pcm77_morph_ax : morph_axiom (@sepT (prod7_PCM U1 U2 U3 U4 U5 U6 U7)) pcm77.
Proof. by split=>[|x y]; rewrite !pcmE /= !pcmE //= =>/and7P []. Qed.
Canonical pcm77_morph := Morphism' pcm77 pcm77_morph_ax.

End ProjectionsMorph7.

(* product morphism of morphisms is a morphism *)
Section PMorphMorph.
Variables (U V1 V2 : pcm).
Variables (D1 : rel U) (f1 : {morphism D1 >-> V1}).
Variables (D2 : rel U) (f2 : {morphism D2 >-> V2}).

Lemma pmorph_morph_ax :  morph_axiom (sepI D1 D2) (f1 \** f2).
Proof.
split=>[|x y] /=; first by rewrite !pcmPE !pfunit.
by move=>V /andP [S1 S2]; rewrite !pcmPE (pfV2 f1 V S1) (pfV2 f2 V S2) !pfjoin.
Qed.

Canonical pmorph_morph :=
  Morphism' (f1 \** f2) pmorph_morph_ax.

End PMorphMorph.

(* Can we say anything about pairing as a morphism *)
(* (-, -) : U -> V -> U * V *)
(* Because of currying, we first need to define a PCM of functions *)
(* That's easy, as join and unit can be defined pointwise *)
(* In that PCM, we can ask if pairing is a morphism in either argument *)
(* e.g. if we focus on the first argument, is *)
(* (x \+ y, _) = (x, _) \+ (y, _) *)
(* It isn't, since _ has to be replaced by the same value everywhere *)

(***********************************************************)
(* Subpcm comes with an injection pval and retraction psub *)
(***********************************************************)

Module SubPCM.
Section ClassDef.
Variables (V : pcm) (D : rel V).

(* we demand a sep-rel here, because I couldn't prove *)
(* the sep_pers lemmas in world.v otherwise *)
(* i.e., for constructing sub-resources, we really want this relation *)
(* to be a seprel *)
Record mixin_of (U : pcm) : Type := Mixin {
  pval_op : {morphism (@sepT U) >-> V};
  psub_op : {morphism D >-> U};
  (* separated in V iff images separated in U *)
  _ : forall x y, valid (psub_op x \+ psub_op y) ->
        valid (x \+ y) && D x y;
  (* inject then retract is id *)
  _ : forall x, psub_op (pval_op x) = x;
  (* retract then inject is id on valids *)
  _ : forall x, valid x -> D x Unit -> pval_op (psub_op x) = x;
  (* injection separates valids from invalids in U *)
  (* this axiom needed so that transitions in subresources *)
  (* don't need to add side-conditions on validity *)
  _ : forall x, valid (pval_op x) -> valid x}.

(* we base the inheritance on type instead of pcm *)
(* thus, we can infer the sub_pcm structure out of the type *)
(* used in the sub_pcm construction *)
Record class_of (U : Type) := Class {
  base : PCM.mixin_of U;
  mixin: mixin_of (PCM.Pack base)}.
Local Coercion base : class_of >->  PCM.mixin_of.

Structure type : Type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c  as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).
Definition clone c of phant_id class c := @Pack T c.
Definition pack (b0 : PCM.mixin_of T) (m0 : mixin_of (PCM.Pack b0)) :=
  fun    m & phant_id m0 m => Pack (@Class T b0 m).

Definition pcmType := @PCM.Pack cT xclass.

End ClassDef.

Module Exports.
Coercion base : class_of >-> PCM.mixin_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope pcm_scope with sort.
Coercion pcmType : type >-> PCM.type.
Canonical pcmType.
Notation sub_pcm := type.
Notation subPCMMix := (@Mixin _ _).
Notation subPCM T m := (@pack _ _ T _ m _ id).

Definition pval V D (U : @sub_pcm V D) : {morphism (@sepT U) >-> V} :=
  pval_op (mixin (class U)).
Definition psub V D (U : @sub_pcm V D) : {morphism D >-> U} :=
  psub_op (mixin (class U)).

Arguments pval {V D U}.
Arguments psub {V D}.
Prenex Implicits pval psub.

Section Lemmas.
Variables (V : pcm) (D : rel V) (U : sub_pcm D).
Notation pval := (@pval V D U).
Notation psub := (@psub V D U).

Lemma valid_psubU (x y : V) :
        valid (psub x \+ psub y) = valid (x \+ y) && D x y.
Proof.
case: U x y=>U' [b][v s H1] *.
by apply/idP/idP; [apply: H1 | case/andP; apply: pfV2].
Qed.

Lemma psub_pval (x : U) : psub (pval x) = x.
Proof. by case: U x=>U' [b][v s H1 H2 H3 H4] T; apply: H2. Qed.

Lemma pval_psub x : valid x -> D x Unit -> pval (psub x) = x.
Proof. by case: U x=>U' [b][v s H1 H2 H3 H4] T; apply: H3. Qed.

(* derived lemmas *)

Lemma pval_inj : injective pval.
Proof. by move=>x y E; rewrite -[x]psub_pval -[y]psub_pval E. Qed.

(* this is a weaker version of valid_psubU *)
(* we can prove valid_sep from valid_psubU, but not vice-versa *)
Lemma valid_sep (x y : U) :
         valid (x \+ y) =
         valid (pval x \+ pval y) && D (pval x) (pval y).
Proof. by rewrite -valid_psubU !psub_pval. Qed.

Lemma valid_sepI (x y : U) :
        valid (x \+ y) -> valid (pval x \+ pval y) && D (pval x) (pval y).
Proof. by rewrite valid_sep. Qed.

Lemma valid_sep1 (x : U) : valid x = valid (pval x) && D (pval x) Unit.
Proof. by rewrite -[x]unitR valid_sep pfunit !unitR. Qed.

Lemma valid_sep1I (x : U) : valid x -> valid (pval x) && D (pval x) Unit.
Proof. by rewrite valid_sep1. Qed.

Lemma valid_sep3 (x y z : U) :
        valid (x \+ y \+ z) =
        [&& valid (pval x \+ pval y \+ pval z),
            D (pval x) (pval y) &
            D (pval x \+ pval y) (pval z)].
Proof.
apply/idP/idP.
- move=>W; case/valid_sepI/andP: (W).
  rewrite pfjoin ?(validL W) // =>->-> /=.
  by rewrite andbT; case/validL/valid_sepI/andP: W.
case/and3P=>W D1 D2; rewrite valid_sep pfjoin ?W ?D2 //.
by rewrite valid_sep (validL W) D1.
Qed.

Lemma valid_sep3I (x y z : U) :
        valid (x \+ y \+ z) ->
        [&& valid (pval x \+ pval y \+ pval z),
            D (pval x) (pval y) &
            D (pval x \+ pval y) (pval z)].
Proof. by rewrite valid_sep3. Qed.

(* thus, if we limit to single variable, we get the following *)
Lemma valid_pval x : valid (pval x) = valid x.
Proof.
apply/idP/idP; first by case: U x=>U' [b][v s H1 H2 H3 H4] T; apply: H4.
move=> Vx; move: (Vx); rewrite -[x]unitL pfjoin //; last by rewrite unitL.
by rewrite valid_sep => /andP[].
Qed.

(* however, valid_sep only really extracts the part of D that *)
(* applies to both arguments. if D doesn't have such part *)
(* but simply restricts x and y separately, then valid_sep *)
(* can be weakened still *)
Lemma valid_pval2 (x y : U) :
        D (pval x) (pval y) = D (pval x) Unit && D (pval y) Unit ->
        valid (x \+ y) = valid (pval x \+ pval y).
Proof.
move=>E; rewrite valid_sep {}E; case W : (valid _)=>//=.
move: (validL W) (validR W); rewrite !valid_pval !valid_sep1.
by case/andP=>_ -> /andP [_ ->].
Qed.

Lemma valid_psub x : valid (psub x) = valid x && D x Unit.
Proof. by rewrite -{2}[x]unitR -valid_psubU pfunit unitR. Qed.

Lemma valid_psub1 x : valid (psub x) -> valid x.
Proof. by rewrite valid_psub; case/andP. Qed.

Lemma valid_psub2 x : valid (psub x) -> D x Unit.
Proof. by rewrite valid_psub; case/andP. Qed.

Lemma pval_psub1 x : valid (psub x) -> pval (psub x) = x.
Proof. by rewrite valid_psub=>/andP [H1 H2]; apply: pval_psub. Qed.

(* this is a convenient composition of the above *)
Lemma valid_sep1P (x : U) : valid x -> D (pval x) Unit.
Proof. by rewrite valid_sep1=>/andP []. Qed.

(* this just uses iff instead of equality *)
(* i keep both lemmas for convenience (valid_pvalE can use views) *)
Lemma valid_pvalE x : valid (pval x) <-> valid x.
Proof. by split; rewrite valid_pval. Qed.

Lemma psub_inj x y : valid (psub x) -> psub x = psub y -> x = y.
Proof.
move=>W E; move: (W) (W).
rewrite {1}E !valid_psub=>/andP [W2 H2] /andP [W1 H1].
have : pval (psub x) = pval (psub y) by rewrite E.
by rewrite !pval_psub.
Qed.

Lemma valid_psubXUn x y :
        valid (psub x \+ y) = valid (x \+ pval y) && D x (pval y).
Proof. by rewrite -{1}(psub_pval y) valid_psubU. Qed.

Lemma valid_psubUnX x y :
        valid (x \+ psub y) = valid (pval x \+ y) && D (pval x) y.
Proof. by rewrite -{1}(psub_pval x) valid_psubU. Qed.

Lemma pvalXUn x y :
       valid (psub x \+ y) -> x \+ pval y = pval (psub x \+ y).
Proof.
move=>W; rewrite pfjoin //.
move/validL: W; rewrite valid_psub=>/andP [V1 V2].
by rewrite pval_psub.
Qed.

Lemma pvalUnX x y :
        valid (x \+ psub y) -> pval x \+ y = pval (x \+ psub y).
Proof. by rewrite joinC=>/pvalXUn <-; rewrite joinC. Qed.

Lemma psubXUn x y :
        valid (x \+ psub y) -> x \+ psub y = psub (pval x \+ y).
Proof.
by rewrite valid_psubUnX=>/andP [W H]; rewrite pfjoin // psub_pval.
Qed.

Lemma psubUnX x y :
        valid (psub x \+ y) -> psub x \+ y = psub (x \+ pval y).
Proof.
by rewrite valid_psubXUn=>/andP [W H]; rewrite pfjoin // psub_pval.
Qed.

End Lemmas.

Arguments valid_psubU [V D] U.
Arguments valid_psub [V D] U.
Arguments valid_psub1 [V D] U.
Arguments valid_psub2 [V D] U.
Prenex Implicits valid_psubU valid_psub valid_psub1 valid_psub2 psub_inj.
Prenex Implicits valid_psubXUn valid_psubUnX pvalXUn pvalUnX psubXUn psubUnX.

End Exports.
End SubPCM.

Export SubPCM.Exports.

(* In the case of TPCMs *)

Lemma psub_undef (V : tpcm) (D : rel V) (U : sub_pcm D) : ~~ valid (psub U undef).
Proof. by rewrite valid_psub tpcmE. Qed.

(* cancelativity is preserved by subPCM construction *)

Section SubCPCM.
Variables (V : cpcm) (D : sep_rel V) (U : sub_pcm D).

Lemma subPCM_cancel (x1 x2 x : U) :
        valid (x1 \+ x) -> x1 \+ x = x2 \+ x -> x1 = x2.
Proof.
move=>W E; move: (W) (W); rewrite {1}E !valid_sep=>/andP [W2 D2] /andP [W1 D1].
move: E; rewrite -(psub_pval x1) -(psub_pval x2) -(psub_pval x).
rewrite -pfjoin // -[R in _ = R]pfjoin //; move/psub_inj.
by rewrite valid_psub W1 sepU0 // => /(_ (erefl _))  /(joinKx W1) ->.
Qed.

Definition subCPCMMix := CPCMMixin subPCM_cancel.
Canonical subCPCM := Eval hnf in CPCM U subCPCMMix.
End SubCPCM.

(* specific construction of a sub-pcm obtained *)
(* by modding out with a separating relation *)
(* but requires starting with a tpcm *)

Module SepSubPCM.
Section SepSubPCM.
Variables (U : tpcm) (D : sep_rel U).

Notation orth1 x := (valid x && D x Unit).
Notation orth2 x y := (valid (x \+ y) && D x y).

(* Constructing the subset type that we care about *)

Definition xsepP x := orth1 x \/ x = undef.
Inductive xsep := ex_sep x of xsepP x.

Definition xval x := let: ex_sep v _ := x in v.

Lemma xsep_eq x y pfx pfy : x = y -> @ex_sep x pfx = @ex_sep y pfy.
Proof. by move=>E; subst y; congr ex_sep; apply: pf_irr. Qed.

Lemma xval_inj x y : xval x = xval y -> x = y.
Proof. by case: x y=>x Hx [y Hy] /= E; subst y; rewrite (pf_irr Hx). Qed.

Lemma xsep_unitP : xsepP (Unit : U).
Proof. by rewrite /xsepP valid_unit sep00; left. Qed.

Definition xsep_valid x := locked (orth1 (xval x)).
Definition xsep_unit := locked (ex_sep xsep_unitP).

Definition xsep_join' x y :=
  if orth2 (xval x) (xval y) then xval x \+ xval y else undef.

Lemma xsep_joinP x y : xsepP (xsep_join' x y).
Proof.
rewrite /xsepP /xsep_join'; case: ifP; last by right.
by case/andP=>V /(sepU0 V) ->; rewrite V; left.
Qed.

Definition xsep_join x y := locked (ex_sep (xsep_joinP x y)).

(* the subset type is actually a pcm *)

Lemma xsep_joinC : commutative xsep_join.
Proof.
case=>x Hx [y Hy]; apply: xval_inj; rewrite /= /xsep_join -!lock /xsep_join' /=.
by rewrite joinC; case V: (valid _)=>//=; rewrite -sepC.
Qed.

Lemma xsep_joinAC : right_commutative xsep_join.
Proof.
case=>a Ha [b Hb][c Hc]; apply: xval_inj; rewrite /= /xsep_join -!lock /xsep_join' /=.
case Sab: (orth2 a b); case Sac: (orth2 a c); rewrite ?tpcmE //=; last first.
- case/andP: Sac=>_ Sac; case: andP=>//; case=>V Sacb.
  by rewrite (sepAxx V Sac Sacb) andbT (validLE3 V) in Sab.
- case/andP: Sab=>_ Sab; case: andP=>//; case=>V Sabc.
  by rewrite (sepAxx V Sab Sabc) andbT (validLE3 V) in Sac.
case/andP: Sab=>_ Sab; case/andP: Sac=>_ Sac.
case Sabc: (orth2 (a \+ b) c).
- case/andP: Sabc=>V Sabc; rewrite sepC (joinAC a c b) V //.
  by rewrite (sepAxx V Sab Sabc).
case Sacb: (orth2 (a \+ c) b)=>//.
case/andP: Sacb=>V Sacb; rewrite sepC (joinAC a b c) V // in Sabc.
by rewrite (sepAxx V Sac Sacb) in Sabc.
Qed.

Lemma xsep_joinA : associative xsep_join.
Proof. by move=>a b c; rewrite !(xsep_joinC a) xsep_joinAC. Qed.

Lemma xsep_unitL : left_id xsep_unit xsep_join.
Proof.
case=>x qf; apply: xval_inj; rewrite /= /xsep_join/xsep_join'/xsep_unit -!lock /=.
rewrite unitL; case: qf=>[|->]; last by rewrite tpcmE.
by case/andP=>V E; rewrite sepC ?unitL // V E.
Qed.

Lemma xsep_validL a b : xsep_valid (xsep_join a b) -> xsep_valid a.
Proof.
rewrite /xsep_valid /xsep_join -!lock /= /xsep_join'.
case: ifP; last by rewrite tpcmE.
by case/andP=>V E; rewrite !(validE2 V) (sepx0 V E).
Qed.

Lemma xsep_valid_unit : xsep_valid xsep_unit.
Proof. by rewrite /xsep_valid/xsep_unit /= -!lock valid_unit sep00. Qed.

(* the pcm *)
Definition xsepPCMMix :=
  PCMMixin xsep_joinC xsep_joinA xsep_unitL xsep_validL xsep_valid_unit.
Canonical xsepPCM := Eval hnf in PCM _ xsepPCMMix.

(* the topped pcm *)

Definition xsep_unitb x := unitb (xval x).

Lemma xsep_undefP : xsepP undef.
Proof. by right. Qed.

Definition xsep_undef : xsepPCM := locked (ex_sep xsep_undefP).

Lemma xsep_unitbP x : reflect (x = Unit) (xsep_unitb x).
Proof.
rewrite /Unit /= /xsep_unit -!lock /xsep_unitb; case: x=>x H /=.
case: unitbP=>X; constructor; last by case=>/X.
by rewrite X in H *; rewrite (pf_irr H xsep_unitP).
Qed.

Lemma xsep_valid_undef : ~~ valid xsep_undef.
Proof. by rewrite pcmE /= /xsep_valid /= /xsep_undef -!lock /= tpcmE. Qed.

Lemma xsep_undef_join x : xsep_undef \+ x = xsep_undef.
Proof.
apply: xval_inj; rewrite /= pcm_joinE /xsep_undef /=.
by rewrite /xsep_join -!lock /= /xsep_join' !tpcmE.
Qed.

Definition xsepTPCMMix :=
  TPCMMixin xsep_unitbP xsep_valid_undef xsep_undef_join.
Canonical xsepTPCM := Eval hnf in TPCM xsep xsepTPCMMix.


(* and we have the sub_pcm instance *)

Lemma xval_morphP : morph_axiom (sepT_seprel xsepPCM) xval.
Proof.
split=>[|x y]; first by rewrite pcmE /= /xsep_unit /= -!lock.
rewrite {1}/valid /= /xsep_valid /= pcm_joinE /=
/xsep_join -!lock /xsep_join' /=;
by case: ifP; rewrite ?tpcmE //; case/andP.
Qed.

Canonical xval_pmorph := Morphism' xval xval_morphP.

Definition xpsub x :=
  if decP (@idP (orth1 x)) is left pf
  then ex_sep (or_introl pf) else ex_sep (or_intror (erefl _)).

Lemma xpsub_morphP : morph_axiom D xpsub.
Proof.
rewrite /xpsub; split=>[|x y V E].
- by apply: xval_inj; case: decP=>//; rewrite pfunit /= valid_unit sep00.
case: decP=>Hx; last by rewrite (sep0E V E) (validE2 V) in Hx.
case: decP=>Hy; last by rewrite (sep0E V E) (validE2 V) in Hy.
case: decP=>H; last by rewrite V (sepU0 V E) in H.
rewrite /valid /= /xsep_valid /= !pcm_joinE /= /xsep_join /= -!lock /= /xsep_join' /=.
rewrite {1 2}V {1 2}E {1}V {1}(sepU0 V E) /=.
by split=>//; apply: xval_inj; rewrite /= /xsep_join' V E.
Qed.

Canonical xpsub_pmorph := Morphism' xpsub xpsub_morphP.

Lemma valid_xpsubU x y : valid (xpsub x \+ xpsub y) -> orth2 x y.
Proof.
rewrite /xpsub {1}/valid /= -?lock /xsep_valid /= !pcm_joinE /= /xsep_join
       -!lock /xsep_join' /= -pcmE.
by case: decP=>Hx; case: decP=>Hy; case H: (orth2 x y) Hx Hy;
rewrite /= ?tpcmE //=; case/andP: H=>V H.
Qed.

Lemma xpsub_xval x : xpsub (xval x) = x.
Proof. by apply: xval_inj; rewrite /xpsub; case: decP; case: x=>// x []. Qed.

Lemma xval_xpsub x : valid x -> D x Unit -> xval (xpsub x) = x.
Proof. by rewrite /xpsub /= => V H; case: decP=>//=; rewrite V H. Qed.

Lemma xvalid_pval x : valid (xval x) -> valid x.
Proof.
rewrite {2}/valid /= /xsep_valid /= -!lock.
by case: x=>x /= [/andP [->->]|] // ->; rewrite tpcmE.
Qed.

Definition xsepSubMix := subPCMMix valid_xpsubU xpsub_xval xval_xpsub xvalid_pval.
Canonical xsepSubPCM : sub_pcm D := Eval hnf in subPCM xsepPCM xsepSubMix.

End SepSubPCM.

Module Exports.
Notation xsepPCM := xsepPCM.
Notation xsepTPCM := xsepTPCM.
Notation xsepSubPCM := xsepSubPCM.
Canonical xsepPCM.
Canonical xsepTPCM.
Canonical xsepSubPCM.
Canonical xval_pmorph.
Canonical xpsub_pmorph.

Prenex Implicits xval xpsub.
Notation xval := xval.
Notation xpsub := xpsub.

Section Extras.
Variables (U : tpcm) (D : sep_rel U).

Lemma xval_undef : xval (@undef (xsepTPCM D)) = undef.
Proof. by case: U D=>U' H' D'; rewrite /undef /= /xsep_undef /= -!lock. Qed.

Lemma xsub_undef : xpsub D undef = undef.
Proof. by rewrite -xval_undef xpsub_xval. Qed.

Lemma xsepP (x : xsepSubPCM D) : x = undef \/ valid x.
Proof.
rewrite (valid_sep1 x); case: x=>x [H|H]; [right=>//| left].
by subst x; apply: pval_inj; rewrite /= xval_undef.
Qed.

End Extras.

End Exports.
End SepSubPCM.


(* We want to keep the definition of xsep abstract to improve performance *)
Module Type SepSubSig.
Parameter xsep : forall U : tpcm, sep_rel U -> Type.
Parameter xsepPCMMix : forall (U : tpcm) (D : sep_rel U),
                         PCM.mixin_of (xsep D).
Canonical xsepPCM U D :=
  Eval hnf in PCM (@xsep U D) (@xsepPCMMix U D).
Parameter xsepTPCMMix : forall (U : tpcm) (D : sep_rel U),
                          TPCM.mixin_of (@xsepPCM U D).
Canonical xsepTPCM U D :=
  Eval hnf in TPCM (@xsep U D) (@xsepTPCMMix U D).
Parameter xsepSubMix : forall (U : tpcm) (D : sep_rel U),
                         SubPCM.mixin_of D (xsepPCM D).
Canonical xsepSubPCM (U : tpcm) (D : sep_rel U) : sub_pcm D :=
  Eval hnf in subPCM (@xsepPCM U D) (@xsepSubMix U D).
Parameter xsep_undef : forall (U : tpcm) (D : sep_rel U),
  @pval U D (@xsepSubPCM U D) (@undef (@xsepTPCM U D)) = undef.

Parameter xsepP : forall (U : tpcm) (D : sep_rel U)
                    (x : @xsepSubPCM U D), x = undef \/ valid x.
End SepSubSig.

Module SepSub : SepSubSig.
Section SepSub.
Variables (U : tpcm) (D : sep_rel U).
Definition xsep := @SepSubPCM.xsep U D.
Definition xsepPCMMix := @SepSubPCM.xsepPCMMix U D.
Canonical xsepPCM := Eval hnf in PCM xsep xsepPCMMix.
Definition xsepTPCMMix := @SepSubPCM.xsepTPCMMix U D.
Canonical xsepTPCM := Eval hnf in TPCM xsep xsepTPCMMix.
Definition xsepSubMix := @SepSubPCM.xsepSubMix U D.
Canonical xsepSubPCM : sub_pcm D :=
  Eval hnf in subPCM xsepPCM xsepSubMix.
Lemma xsep_undef : pval (U:=xsepSubPCM) undef = undef.
Proof. by apply: SepSubPCM.Exports.xval_undef. Qed.
Lemma xsepP (x : xsepSubPCM) : x = undef \/  valid x.
Proof. by apply: SepSubPCM.Exports.xsepP. Qed.
End SepSub.
End SepSub.

(* Furthermore, locking U and D improves performance still *)
(* The following is a version which defines canonicals for *)
(* the xsep constructor *)

Module SepSub2.

Notation xsep D :=
  (@SepSub.xsep (locked _)
                (cast (fun U : tpcm => sep_rel U) (esym (lock _)) D)).

Section SepSubExports.
Variables (U : tpcm) (D : sep_rel U).

Lemma eq1 : xsep D = SepSub.xsep D.
Proof. by move: (esym _); rewrite -lock=>eq1'; rewrite eqc. Qed.

Definition xsepPCMMix := cast PCM.mixin_of eq1 (SepSub.xsepPCMMix D).
Canonical xsepPCM := Eval hnf in PCM (xsep D) xsepPCMMix.

Lemma eq2 : xsepPCM = SepSub.xsepPCM D.
Proof.
rewrite /xsepPCM/xsepPCMMix; move: eq1.
by rewrite eq1=>eq1'; rewrite !eqc.
Qed.

Definition xsepTPCMMix := cast TPCM.mixin_of eq2 (SepSub.xsepTPCMMix D).
Canonical xsepTPCM := Eval hnf in TPCM (xsep D) xsepTPCMMix.

Lemma eq3 : (D, xsepTPCM) = (D, SepSub.xsepTPCM D).
Proof.
rewrite /xsepTPCM/SepSub.xsepTPCM/xsepTPCMMix/xsepPCMMix; move: eq2.
rewrite /xsepPCM/xsepPCMMix; move: eq1.
by rewrite !eq1=>eq1'; rewrite !eqc=>eq2'; rewrite !eqc.
Qed.

Definition xsepSubMix :=
  cast (fun W : sep_rel U * tpcm => SubPCM.mixin_of W.1 W.2)
       eq3
       (SepSub.xsepSubMix D).
Canonical xsepSubPCM := Eval hnf in subPCM xsepPCM xsepSubMix.

Lemma xsep_undef : pval (U:=xsepSubPCM) undef = undef.
Proof.
rewrite -(SepSub.xsep_undef D)/pval/undef/xsepSubPCM/xsepSubMix; move: eq3.
rewrite /xsepTPCM/xsepTPCMMix/xsepPCMMix; move: eq2.
rewrite /xsepPCM/xsepPCMMix; move: eq1.
by rewrite !eq1=>eq1'; rewrite !eqc=>eq2'; rewrite !eqc=>eq3'; rewrite !eqc.
Qed.

Lemma xsepP (x : xsepSubPCM) : x = undef \/  valid x.
Proof.
move: x; rewrite /xsepSubPCM/undef/valid /= /xsepTPCMMix /xsepPCMMix /=; move: eq2.
rewrite /xsepPCM/xsepPCMMix; move: eq1.
rewrite !eq1=>eq1'; rewrite !eqc=>eq2'; rewrite !eqc.
by apply: SepSub.xsepP.
Qed.

Lemma xsep_psub_undef : psub xsepSubPCM undef = undef.
Proof. by rewrite -xsep_undef psub_pval. Qed.

End SepSubExports.
End SepSub2.


Module SepSub3.

Notation xsep D := (locked (@SepSub.xsep _ D)).

Section SepSubExports.
Variables (U : tpcm) (D : sep_rel U).

Lemma eq1 : xsep D = SepSub.xsep D.
Proof. by rewrite -lock. Qed.

Definition xsepPCMMix := cast PCM.mixin_of eq1 (SepSub.xsepPCMMix D).
Definition xsepPCM := Eval hnf in PCM (xsep D) xsepPCMMix.

Lemma eq2 : xsepPCM = SepSub.xsepPCM D.
Proof.
rewrite /xsepPCM/xsepPCMMix; move: eq1.
by rewrite eq1=>eq1'; rewrite !eqc.
Qed.

Definition xsepTPCMMix := cast TPCM.mixin_of eq2 (SepSub.xsepTPCMMix D).
Definition xsepTPCM := Eval hnf in TPCM (xsep D) xsepTPCMMix.

Lemma eq3 : (D, xsepTPCM) = (D, SepSub.xsepTPCM D).
Proof.
rewrite /xsepTPCM/SepSub.xsepTPCM/xsepTPCMMix/xsepPCMMix; move: eq2.
rewrite /xsepPCM/xsepPCMMix; move: eq1.
by rewrite !eq1=>eq1'; rewrite !eqc=>eq2'; rewrite !eqc.
Qed.

Definition xsepSubMix :=
  cast (fun W : sep_rel U * tpcm => SubPCM.mixin_of W.1 W.2)
       eq3
       (SepSub.xsepSubMix D).
Definition xsepSubPCM := Eval hnf in subPCM xsepPCM xsepSubMix.

Lemma xsep_undef : pval (U:=xsepSubPCM) (@undef xsepTPCM) = undef.
Proof.
rewrite -(SepSub.xsep_undef D)/pval/undef/xsepSubPCM/xsepSubMix; move: eq3.
rewrite /xsepTPCM/xsepTPCMMix/xsepPCMMix; move: eq2.
rewrite /xsepPCM/xsepPCMMix; move: eq1.
by rewrite !eq1=>eq1'; rewrite !eqc=>eq2'; rewrite !eqc=>eq3'; rewrite !eqc.
Qed.

Lemma xsepP (x : xsepSubPCM) : x = @undef xsepTPCM \/  valid x.
Proof.
move: x; rewrite /xsepSubPCM/undef/valid /= /xsepTPCMMix /xsepPCMMix /=; move: eq2.
rewrite /xsepPCM/xsepPCMMix; move: eq1.
rewrite !eq1=>eq1'; rewrite !eqc=>eq2'; rewrite !eqc.
by apply: SepSub.xsepP.
Qed.

Lemma xsep_psub_undef : psub xsepSubPCM undef = undef :> xsepTPCM.
Proof. by rewrite -xsep_undef psub_pval. Qed.

End SepSubExports.
End SepSub3.

(* In general, typechecking is fastest if each individual *)
(* type defined using either of the 3 versions of xsep above, *)
(* is itself hidden using the module system. Thus, the xsep *)
(* type should probably never be used directly itself, without the hiding *)
(* so it doesn't matter which of the three versions we export *)

(* We will export SepSub2 for those rare (or unexpected) cases *)
(* when we want to have canonicals on xsep, but we want to be *)
(* faster than the nakes SepSub *)

Export SepSub2.


(* We can use the xsep construction to provide a product TPCM *)
(* which is *normal*; that is, has only undef as the invalid element. *)
(* The way to do so is to mod out the plain product (T)PCM by a *)
(* trivial sep relation, via the xsep construction. *)

Module Type PairingSig.

Parameter pprod : tpcm -> tpcm -> Type.

Section PairingSig.
Variables U1 U2 : tpcm.
Parameter pprodPCMMix : PCM.mixin_of (pprod U1 U2).
Canonical pprodPCM := Eval hnf in PCM (pprod U1 U2) pprodPCMMix.
Parameter pprodTPCMMix : TPCM.mixin_of pprodPCM.
Canonical pprodTPCM := Eval hnf in TPCM (pprod U1 U2) pprodTPCMMix.
Parameter pprodSubMix :
  SubPCM.mixin_of [seprel of @sepT (U1 * U2)] pprodPCM.
Canonical pprodSubPCM :=
  Eval hnf in subPCM (pprod U1 U2) pprodSubMix.
Parameter pprod_pval_undef : pval (@undef pprodTPCM) = undef.
Parameter pprodP : forall x : pprod U1 U2, x = undef \/ valid x.
End PairingSig.
End PairingSig.


Module Pairing : PairingSig.
Section Pairing.
Variables U1 U2 : tpcm.

Local Definition Uraw := [tpcm of U1 * U2].
Local Definition Draw := [seprel of @sepT Uraw].

Definition pprod := @SepSubPCM.xsep Uraw Draw.
Definition pprodPCMMix := @SepSubPCM.xsepPCMMix Uraw Draw.
Canonical pprodPCM := Eval hnf in PCM pprod pprodPCMMix.
Definition pprodTPCMMix := @SepSubPCM.xsepTPCMMix Uraw Draw.
Canonical pprodTPCM := Eval hnf in TPCM pprod pprodTPCMMix.
Definition pprodSubMix := @SepSubPCM.xsepSubMix Uraw Draw.
Canonical pprodSubPCM : sub_pcm Draw :=
  Eval hnf in subPCM pprod pprodSubMix.

Lemma pprod_pval_undef : pval (@undef pprodTPCM) = undef.
Proof. by apply: SepSubPCM.Exports.xval_undef. Qed.

Lemma pprodP (x : pprod) : x = undef \/ valid x.
Proof. by apply: SepSubPCM.Exports.xsepP. Qed.

End Pairing.
End Pairing.

Export Pairing.

Section PairingLemmas.
Variables U1 U2 : tpcm.

Notation U := (pprod U1 U2).

Definition pfst : U -> _ := fst \o pval.
Canonical pfst_morph := [morphism of pfst].

Definition psnd : U -> _ := snd \o pval.
Canonical psnd_morph := [morphism of psnd].

Definition ppair : U1 * U2 -> U := psub (pprodSubPCM U1 U2).
Lemma ppair_morph_ax : morph_axiom (@sepT _) ppair.
Proof. by split; [apply: pfunit | apply: pfjoinV]. Qed.
Canonical ppair_morph := Morphism' ppair ppair_morph_ax.

Lemma pairing_undef :
        (pfst undef = undef) *
        (psnd undef = undef) *
        (forall x, ~~ valid x -> ppair x = undef).
Proof.
split; first by rewrite /pfst/psnd /= pprod_pval_undef.
case=>a b Vab; case: (pprodP (ppair (a, b)))=>//.
by rewrite valid_psub (negbTE Vab).
Qed.

Lemma pairing_valid :
        (forall x, valid (pfst x) = valid x) *
        (forall x, valid (psnd x) = valid x) *
        (forall x, valid (ppair x) = valid x).
Proof.
split=>[|x].
- split=>x; (case: (pprodP x)=>[->|V]; first by rewrite pairing_undef !tpcmE);
  by case/valid_pvalE/andP: V (V)=>/= E1 E2 ->; rewrite ?(E1,E2).
by rewrite valid_psub andbT.
Qed.

Lemma pprojPV1 x : valid x = valid (pfst x) && valid (psnd x).
Proof. by rewrite valid_sep1 pcmPV andbT. Qed.

Lemma pprojPV2 x y :
        valid (x \+ y) = valid (pfst x \+ pfst y) && valid (psnd x \+ psnd y).
Proof. by rewrite valid_sep pcmPV andbT. Qed.

Lemma ppairPV1 x : valid (ppair x) = valid x.
Proof. by rewrite valid_psub andbT. Qed.

Lemma ppairPV2 x y : valid (ppair x \+ ppair y) = valid (x \+ y).
Proof. by rewrite valid_psubU andbT. Qed.

Definition pprodPV := (pprojPV1, pprojPV2, ppairPV1, ppairPV2).

Lemma pfst_ppair x : valid x -> pfst (ppair x) = x.1.
Proof. by move=>V; rewrite /pfst/= pval_psub. Qed.

Lemma psnd_ppair x : valid x -> psnd (ppair x) = x.2.
Proof. by move=>V; rewrite /psnd/= pval_psub. Qed.

Lemma pprod_eta x : x = ppair (pfst x, psnd x).
Proof. by rewrite -prod_eta psub_pval. Qed.

Definition pprodPE := (pfst_ppair, psnd_ppair, pprodPV).

End PairingLemmas.

Prenex Implicits pfst psnd ppair.
