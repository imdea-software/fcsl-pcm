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
(* This file contains an implementation of invertible PCM morphisms and their *)
(* separating relations.                                                      *)
(******************************************************************************)

From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype.
From fcsl Require Import options axioms prelude.
From fcsl Require Import pcm morphism.

Section Invertible.
  Variables (U V : pcm) (D : rel U).

(* in the POPL21 paper, we use the following notation
   x D y D z =def= x D y /\ (x \+ y) D z
*)
Definition inv_rel :=
  forall a1 a2 a',
    valid (a1 \+ a2 \+ a') ->
    D a1 (a2 \+ a') -> D a2 (a1 \+ a') ->
    D a1 a2 && D (a1 \+ a2) a'.

Definition inv_morph_axiom (f : morphism V D) :=
  forall (a : U) (b1 b2 : V),
    valid a -> D a Unit -> f a = b1 \+ b2 ->
    exists a1 a2, [/\ a = a1 \+ a2, valid (a1 \+ a2),
                      D a1 a2, f a1 = b1 & f a2 = b2 ].

Definition inv_morph f := inv_rel /\ inv_morph_axiom f.

End Invertible.

(* trivial seprel in invertible *)
Lemma inv_sepT U : inv_rel (@sepT_seprel U). Proof. by []. Qed.

Lemma inv_idfun (U : pcm) : inv_morph [morphism of @idfun U].
Proof. by split=>// a b1 b2 V _ E; exists b1, b2; rewrite -E. Qed.

(* composition of invertible morhpsisms is invertible *)
Lemma inv_comp (U V W : pcm) (C : sep_rel V) (D : sep_rel U)
               (f : morphism V D) (g : morphism W C) :
        inv_morph g -> inv_morph f -> inv_morph [morphism of g \o f].
Proof.
case=>HC Hg [HD Hf]; split=>[a1 a2 a' V1|a b1 b2 V1] /andP [].
- move=>/(HD _ _ _ V1) H1 H2 /andP [/H1] /andP [D1 D2].
  rewrite !sepE !pfjoin ?(validLE3 V1, sepAxx V1 D1 D2) //= in H2 *.
  by apply: HC H2; apply: pfV3.
move=>D1; rewrite pfunit=>C1.
case/(Hg _ _ _ (pfV f V1 D1) C1)=>c1 [c2][Ef Vc Xc <-<-].
case/(Hf _ _ _ V1 D1): Ef Xc=>a1 [a2][-> Va Xc <-<- Xd].
by exists a1, a2; rewrite !sepE Xc Xd.
Qed.

(* morphism product is invertible *)

Lemma inv_cprod (U1 U2 V1 V2 : pcm) (D1 : sep_rel U1)  (D2 : sep_rel U2)
                (f : morphism V1 D1) (g : morphism V2 D2) :
        inv_morph f -> inv_morph g -> inv_morph [morphism of f \* g].
Proof.
case=>HD1 Hf [HD2 Hg]; split=>[a1 a2 a'|]; rewrite /sep_prod /=.
- case/andP=>Va Vb /andP [/(HD1 _ _ _ Va) H1 /(HD2 _ _ _ Vb) H2].
  by case/andP=>/H1 /andP [->->] /H2 /andP [->->].
move=>/= a1 b1 b2 /andP [Va Vb] /andP [H1 H2][].
case/(Hf _ _ _ Va H1)=>c1 [c2][E1 Vc1 Y1 Fc1 Fc2].
case/(Hg _ _ _ Vb H2)=>d1 [d2][E2 Vd1 Y2 Fd1 Fd2].
exists (c1, d1), (c2, d2); rewrite /fprod /= Vc1 Vd1.
by rewrite Fc1 Fc2 Fd1 Fd2 Y1 Y2 pcmPE -E1 -E2 -!prod_eta.
Qed.

(* the construction of ker requires the range to be topped *)

Lemma inv_ker U (V : tpcm) (D : sep_rel U) (f : morphism V D) :
        inv_rel D -> inv_rel ('ker f).
Proof.
move=>HD a1 a2 a' W; rewrite !sepE /=.
case/and3P=>D1 /unitbP Eq1 _ /and3P [D2 /unitbP Eq2 /unitbP].
case/andP: (HD _ _ _ W D1 D2)=>{}D1 {}D2.
rewrite !pfjoin ?(validLE3 W) //; last by rewrite (sepAxx W).
by rewrite Eq1 Eq2 D1 D2 !unitL =>->; rewrite tpcmE.
Qed.

(* the construction of eqlz requires the range to be eqpcm *)
(* for now, we just assume cancellativity as a hypothesis *)

Lemma inv_eqlz U (V : eqpcm) (D1 D2 : sep_rel U)
               (f : morphism V D1) (g : morphism V D2) :
        (forall x x1 x2 : EQPCM.pcm V, valid (x \+ x1) ->
           x \+ x1 = x \+ x2 -> x1 = x2) ->
        inv_rel D1 -> inv_rel D2 -> inv_rel ('eqlz f g).
Proof.
move=>K HD1 HD2 x y z W; rewrite !sepE /=.
case/and4P=>X1 X2 Ex _ /and4P [Y1 Y2] Ey /eqP.
case/andP: (HD1 _ _ _ W X1 Y1)=>E1 E1'.
case/andP: (HD2 _ _ _ W X2 Y2)=>E2 E2'.
rewrite E1 E2 Ex Ey E1' E2' !pfjoin ?(validLE3 W) 2?(sepAxx W) //=.
rewrite -(eqP Ex) (eqP Ey) eq_refl=>/K ->; first by rewrite eq_refl.
by rewrite pfV2 // ?(validLE3 W)// (sepAxx W).
Qed.

(* this theorem generalizes the one from the POPL21 paper *)
(* to work with arbitrary sub-pcm over matching seprel *)
(* (the one in the paper worked with xsub explicitly) *)
(* can be further generalised to any D' that is compatible with D *)

Lemma inv_comp_sub (U : tpcm) (V : pcm) (D : sep_rel U) (W : sub_pcm D)
                   (f : {morphism D >-> V}) :
        inv_morph f -> inv_morph [morphism of f \o @pval U D W].
Proof.
case=>HD Hf; split=>[a1 a2 a' V1|].
- by rewrite !sepE !pfjoin ?(validLE3 V1) //; apply: HD; apply: pfV3.
move=>a b1 b2 V1; rewrite !sepE pfunit /= => H1.
case/(Hf _ _ _ (pfV _ V1 (erefl _)) H1)=>c1 [c2][Eq Vc H2 F1 F2].
exists (psub _ c1), (psub _ c2); rewrite !sepE -!pfjoin // -Eq psub_pval //=.
by rewrite !pval_psub ?(validL Vc, validR Vc, sep0E Vc).
Qed.
