(*
Copyright 2024 IMDEA Software Institute
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

From HB Require Import structures.
From Stdlib Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import choice ssrnat eqtype ssrint ssrnum order.
From pcm Require Import options axioms prelude pcm mutex morphism.

(*************************)
(*************************)
(* PCMs with subtraction *)
(*************************)
(*************************)

(* PCMS = PCM + Subtraction where *)
(* Subtraction = PCM operation that inverts join *)

(* x \- y is defined to be z iff x = y \+ z disjointly *)
Definition pcms_axiom (U : pcm) (minus : U -> U -> U) := 
  forall x y z, valid x /\ x = y \+ z <-> minus x y = z /\ valid z.

HB.mixin Record isPCMS (U : Type) of PCM U := {
  unjoin : U -> U -> U;
  pcms_subproof : pcms_axiom unjoin}.

(* every pcms should be cpcm; hence embedding *)
(* cancellativity to facilitate inheritance *)
#[short(type="pcms")]
HB.structure Definition PCMS := {U of isPCMS U & CPCM U}.

(* tpcms = pcms with top *)
#[short(type="tpcms")]
HB.structure Definition TPCMS := {U of CTPCM U & isPCMS U}.

(* eqpcms = pcms with decidable equality *)
#[short(type="eqpcms")]
HB.structure Definition EQPCMS := {U of EQCPCM U & isPCMS U}.

(* eqtpcms = tpcms with decidable equality *)
#[short(type="eqtpcms")]
HB.structure Definition EQTPCMS := {U of EQCTPCM U & isPCMS U}.

(* normal tpcms *)
#[short(type="normal_tpcms")]
HB.structure Definition Normal_TPCMS := {U of TPCMS U & isNormal_TPCM U}.

(* adding conical *)

(* conical pcms *)
#[short(type="pcmsc")]
HB.structure Definition PCMSC := {U of isPCMS U & CPCMC U}.

(* conical tpcms *)
#[short(type="tpcmsc")]
HB.structure Definition TPCMSC := {U of CTPCMC U & isPCMS U}.

(* conical eqpcms *)
#[short(type="eqpcmsc")]
HB.structure Definition EQPCMSC := {U of EQCPCMC U & isPCMS U}.

(* conical tpcms with decidable equality *)
#[short(type="eqtpcmsc")]
HB.structure Definition EQTPCMSC := {U of EQCTPCMC U & isPCMS U}.

(* conical normal tpcms *)
#[short(type="normal_tpcmsc")]
HB.structure Definition Normal_TPCMSC := {U of TPCMSC U & isNormal_TPCM U}.

(* Infix "\-" := unjoin (at level 42, left associativity) : pcm_scope.   *)
Infix "\-" := unjoin (at level 50, left associativity) : pcm_scope.

(* cancellativity substructure follows from pcms_axiom *)
HB.builders Context U of isPCMS U.
Lemma pcms_is_cpcm : cpcm_axiom U.
Proof. 
have subJx (x y : U) : valid (x \+ y) -> unjoin (x \+ y) x = y.
- by move=>V; case/pcms_subproof: (conj V (erefl (x \+ y))). 
have subxJ (x y : U) : valid (x \+ y) -> unjoin (x \+ y) y = x.
- by rewrite joinC; apply: subJx. 
by move=>x y z V H; rewrite -(subxJ _ _ V) H subxJ // -H. 
Qed.

HB.instance Definition _ := isCPCM.Build U pcms_is_cpcm.
HB.end.

Section Repack.
Variable U : pcms.
Implicit Type x y : U.

Lemma validSL x y : valid (x \- y) -> valid x.
Proof. by case/(conj (erefl (x \- y)))/pcms_subproof. Qed.

Lemma validSR x y : valid (x \- y) -> valid y.
Proof. by case/(conj (erefl (x \- y)))/pcms_subproof=>/[swap] -> /validL. Qed.

(* +/- interaction *)

Lemma joinxS x y : valid (x \- y) -> y \+ (x \- y) = x.
Proof. by case/(conj (erefl (x \- y)))/pcms_subproof. Qed.

Lemma joinSx x y : valid (x \- y) -> x \- y \+ y = x.
Proof. by rewrite joinC; apply: joinxS. Qed.

Lemma subJx x y : valid (x \+ y) -> (x \+ y) \- x = y.
Proof. by move=>V; case/pcms_subproof: (conj V (erefl (x \+ y))). Qed.

Lemma subxJ x y : valid (x \+ y) -> x \+ y \- y = x.
Proof. by rewrite joinC; apply: subJx. Qed.

Lemma subxx x : valid x -> x \- x = Unit.
Proof. by rewrite -{1 2}[x]unitR; apply: subJx. Qed.

Lemma subx0 x : valid x -> x \- Unit = x.
Proof. by rewrite -{1 2}[x]unitL; apply: subJx. Qed.

Lemma sub_eq0 x y : x \- y = Unit -> x = y.
Proof. by move=>E; rewrite -[RHS]unitR -E joinxS // E. Qed.

(* monotonicity of subtraction: *)
(* if we subtracted more, we could subtract less *)

Lemma mono_subL x y z : 
        valid (x \- (y \+ z)) -> 
        valid (x \- y).
Proof.
move=>V; move/pcms_subproof: (conj (erefl (x \- (y \+ z))) V).
by rewrite -joinA=>/pcms_subproof [<-].
Qed.

Lemma mono_subR x y z : 
        valid (x \- (y \+ z)) -> 
        valid (x \- z).
Proof. by rewrite joinC=>/mono_subL. Qed.

(* lemmas for moving subtractions around equality *)
(* names read the rule upside-down *)

(* (left) subtraction of y -> (right) join y left *)
Lemma sub_joinL x y z : 
         valid x -> 
         x = y \+ z -> 
         x \- y = z.
Proof. by move/[swap]=>-> /subJx. Qed.

Lemma sub_joinR x y z : 
         valid x -> 
         x = z \+ y -> 
         x \- y = z.
Proof. by rewrite joinC; apply: sub_joinL. Qed.

Lemma joinL_sub x y z : 
         valid z -> 
         x \- y = z -> 
         x = y \+ z.
Proof. by move/[swap]=><- /joinxS. Qed.

Lemma joinR_sub x y z : 
         valid z -> 
         x \- y = z -> 
         x = z \+ y.
Proof. by rewrite joinC; apply: joinL_sub. Qed.

(* x - y is defined iff it's disjoint from y *)
Lemma validSE x y : valid (x \- y \+ y) = valid (x \- y).
Proof. by apply/idP/idP=>[/validL//|V]; rewrite joinSx // (validSL V). Qed.

Lemma validSX x y : 
        valid (x \- y) <-> valid x /\ x = x \- y \+ y.
Proof.
split=>[V|[/[swap] E]]; last by rewrite {1}E=>/validL. 
by rewrite (validSL V) joinSx.
Qed.

(* associativity of +/- *)

(* if left side valid, equality holds *)
Lemma subDAL x y z : 
        valid (x \- (y \+ z)) ->
        x \- (y \+ z) = x \- y \- z.
Proof.
move=>V; apply/esym/(sub_joinL (mono_subL V)).
by apply/(sub_joinL (validSL V)); rewrite joinA joinxS.
Qed.

(* if right side valid, equality holds *)
Lemma subDAR x y z : 
        valid (x \- y \- z) ->
        x \- (y \+ z) = x \- y \- z.
Proof.
move=>V; apply/(sub_joinL (validSL (validSL V))).
rewrite -joinA; apply/joinL_sub/joinL_sub=>//.
by rewrite joinC validSE.
Qed.

(* which side is valid doesn't matter *)
Lemma validDA x y z: 
        valid (x \- (y \+ z)) = valid (x \- y \- z).
Proof. by apply/idP/idP=>V; [rewrite -subDAL|rewrite subDAR]. Qed.

(* if x is such that adding z doesn't overflow *)
(* and subtracting y doesn't overflow, then *)
(* the order of adding/subtracting doesn't matter *)
Lemma subADL x y z : 
        valid (x \+ z) ->
        valid (x \- y) ->
        x \- y \+ z = x \+ z \- y.
Proof.
move=>V1 V2; apply/esym/sub_joinR=>//.
by rewrite joinAC joinSx.
Qed.

(* distribution and validity *)

Lemma validDL x y z : 
        valid ((x \+ y) \- (x \+ z)) = 
        valid (x \+ y) && valid (y \- z).
Proof.
apply/idP/idP=>[V|/andP [V1 V2]]; last by rewrite subDAR subJx.
by move: (V); rewrite subDAL // subJx (validSL V).
Qed.

Lemma validDR x y z : 
        valid ((x \+ y) \- (z \+ y)) = 
        valid (x \+ y) && valid (x \- z).
Proof. by rewrite -!(joinC y); apply: validDL. Qed.

(* distribution and equality *)

Lemma subDL1 x y z : 
        valid ((x \+ y) \- (x \+ z)) ->
        (x \+ y) \- (x \+ z) = y \- z.
Proof. by move=>V; rewrite subDAL // subJx // (validSL V). Qed.

Lemma subDL2 x y z : 
        valid (x \+ y) && valid (y \- z) ->
        (x \+ y) \- (x \+ z) = y \- z.
Proof. by rewrite -validDL; apply/subDL1. Qed.

Lemma subDR1 x y z : 
        valid ((x \+ y) \- (z \+ y)) ->
        (x \+ y) \- (z \+ y) = x \- z.
Proof. by rewrite -!(joinC y); apply: subDL1. Qed.

Lemma subDR2 x y z : 
        valid (x \+ y) && valid (x \- z) ->
        (x \+ y) \- (z \+ y) = x \- z.
Proof. by rewrite -validDR; apply/subDR1. Qed.

End Repack.

(* if U is normal tpcm, side-condition in subD lemmas simplifies *)

Lemma subDA (U : normal_tpcms) (x y z : U) : 
        x \- (y \+ z) = x \- y \- z.
Proof.
case: (normalP (x \- y \- z)) (validDA x y z)=>[->|_ V].
- by case: normalP. 
by apply: subDAL.
Qed.

Lemma subDL (U : normal_tpcms) (x y z : U) : 
        valid (x \+ y) ->
        (x \+ y) \- (x \+ z) = y \- z. 
Proof.
move=>V.
case: (normalP (y \- z)) (validDL x y z)=>[->|V1 V2].
- by rewrite andbF; case: normalP.
rewrite andbT in V2 V.
by rewrite subDL1 // validDL V V1.
Qed.

Lemma validS0x (U : pcmsc) (x : U) : 
        valid (Unit \- x) = unitb x.
Proof.
apply/idP/idP; last by move/unitbP=>->; rewrite subx0.
by move/joinxS/unitbP/join0L.
Qed.

Lemma sub0x (U : normal_tpcmsc) (x : U) :
        Unit \- x = if unitb x then Unit else undef.
Proof.
case: ifPn (validS0x x)=>[|_]; last by case: normalP.
by move/unitbP=>->; rewrite subx0.
Qed.

(**********************)
(**********************)
(* PCMS constructions *)
(**********************)
(**********************)

(* mutex is pcms *)
Definition mutex_minus (T : eqType) (x y : mutex T) : mutex T := 
  match (x, y) with 
  | (mx x1, mx x2) => 
      if x1 == x2 then nown else undef
  | (mx x1, nown) => mx x1
  | (nown, mx _) => undef
  | (nown, nown) => nown
  | _ => undef
  end.

Arguments mutex_minus {T} x y /.

Lemma mutex_is_pcms T : pcms_axiom (@mutex_minus T).
Proof.
case=>[||x][||y][||z]; try by [split; case];
rewrite !pcmE /=; split; case=>//.
- by move=>_ [->]; rewrite eqxx.
- by case: (x =P y)=>// ->.
by case: (x =P y).
Qed.

HB.instance Definition _ (T : eqType) := 
  isPCMS.Build (mutex T) (@mutex_is_pcms T). 

(* int is pcms *)

Section IntPCM. 
Import ssrint.intZmod ssralg.GRing.

Lemma int_is_pcm : pcm_axiom (T:=int) xpredT add 0 (eq_op^~ 0).
Proof.
by split=>[|||||x] //; [apply: addrC|apply: addrA|apply: add0r|
case: eqP=>[->|N]; constructor].
Qed.

#[export] HB.instance Definition _ := isPCM.Build int int_is_pcm.

Lemma int_is_pcms : pcms_axiom (U:=int) (fun x => add x \o opp). 
Proof. 
split=>[[_ ->]|[<- _]] /=.
- by rewrite addrAC (addrC y) addNr add0r.
by rewrite !pcmE /= addrCA addrN addr0.
Qed.

#[export] HB.instance Definition _ := isPCMS.Build int int_is_pcms.

End IntPCM.

(* product of pcms-s is pcms *)

Section ProdPCMS.
Variables U1 U2 : pcms.

Definition prod_minus (x y : U1 * U2) : U1 * U2 := 
  (x.1 \- y.1, x.2 \- y.2).

Lemma prod_is_pcms : pcms_axiom prod_minus.
Proof.
rewrite /prod_minus; case=>[x1 x2][y1 y2][z1 z2] /=; split.
- case=>/[swap][[->->]] /andP [/= V1 V2].
  by rewrite !subJx // pcmE /= (validR V1) (validR V2).
case; case=><-<- /andP [/= V1 V2].
by rewrite !pcmE /= !joinxS // (validSL V1) (validSL V2).
Qed.

HB.instance Definition _ := isPCMS.Build (U1 * U2)%type prod_is_pcms.
End ProdPCMS.

Arguments prod_minus {U1 U2} x y /.

Section Prod3PCMS.
Variables U1 U2 U3 : pcms.

Definition prod3_minus (x y : Prod3 U1 U2 U3) : Prod3 U1 U2 U3 := 
  mk3 (proj31 x \- proj31 y) (proj32 x \- proj32 y) (proj33 x \- proj33 y).

Lemma prod3_is_pcms : pcms_axiom prod3_minus.
Proof.
rewrite /prod3_minus; case=>[x1 x2 x3][y1 y2 y3][z1 z2 z3] /=; split.
- case=>/[swap][[->->->]] /and3P [/= V1 V2 V3].
  by rewrite !subJx // pcmE /= (validR V1) (validR V2) (validR V3).
case; case=><-<-<- /and3P [/= V1 V2 V3].
by rewrite !pcmE /= !joinxS // (validSL V1) (validSL V2) (validSL V3).
Qed.

HB.instance Definition _ := isPCMS.Build (Prod3 U1 U2 U3) prod3_is_pcms.
End Prod3PCMS.

Arguments prod3_minus {U1 U2 U3} x y /.

(* option of PCMS is PCMS *)
Section OptionPCMS.
Variable U : pcms.

Definition option_minus (x y : option U) := 
  if (x, y) is (Some x, Some y) then 
    if valid (x \- y) then Some (x \- y) else None
  else None.

Lemma option_is_pcms : pcms_axiom option_minus.
Proof.
rewrite /option_minus; case=>[x|][y|][z|]; split; case=>//=.
- move/[swap]; case=>-> V.
  by rewrite subJx // (validR V) /valid /= (validR V).
case: ifP=>// V [<-{z}] _.
by rewrite /valid /= (validSL V) pcmE /= joinxS.
Qed.

HB.instance Definition _ := isPCMS.Build (option U) option_is_pcms.
End OptionPCMS.

Arguments option_minus {U} x y /.

(**********************************)
(* subtraction-preserving seprels *)
(**********************************)

Definition sseprel_axiom (U : pcms) (sep : rel U) := 
  forall x y, valid (x \- y) -> sep x Unit -> sep y Unit ->
    sep (x \- y) Unit -> sep (x \- y) y.

HB.mixin Record isSseprel (U : pcms) (sep : rel U) of Seprel U sep := {
  sseprel_subproof : sseprel_axiom sep}.

#[short(type="sseprel")]
HB.structure Definition Sseprel (U : pcms) := 
  {sep of isSseprel U sep & Seprel U sep}.

Lemma sepSy (U : pcms) (sep : sseprel U) (x y : U) :
        valid (x \- y) ->
        sep x Unit ->
        sep y Unit ->
        sep (x \- y) Unit ->
        sep (x \- y) y.
Proof. by apply: sseprel_subproof. Qed.

Lemma sepyS (U : pcms) (sep : sseprel U) (x y : U) :
        valid (x \- y) ->
        sep x Unit ->
        sep y Unit ->
        sep (x \- y) Unit ->
        sep y (x \- y).
Proof. 
move=>V Sx Sy S; rewrite sepC; first by apply: sepSy.
by rewrite joinxS // (validSL V).
Qed.

(* quotient of tpcms by sseprel is pcms *)

Section XSepPCMS.
Variables (U : tpcms) (R : sseprel U).

Definition sub_minus (x y : xsep R) : xsep R := 
  psub (xsub R) (pval (xsub R) x \- pval (xsub R) y).

Lemma sub_is_tpcms : pcms_axiom sub_minus.
Proof.
move=>x y z; split=>[[V E]|[H V]].
- rewrite {x}E in V *; split; last by rewrite (validR V).
  rewrite -[RHS](psub_pval (xsub R)).
  by rewrite /sub_minus pfjoinT //= subJx // valid_pvalUn.
rewrite -H in V *; case/fpVI: V=>/[dup] V /=. 
rewrite validSX valid_pvalE; case=>Vx _ S; split=>//. 
move: (validSR V). rewrite valid_pvalE. move=>Vy.
case/(valid_sep (xsub R)): Vx=>Vx Sx.
case/(valid_sep (xsub R)): Vy=>Vy Sy.
rewrite -{1}(psub_pval (xsub R) y) -pfjoin /=.
- by rewrite joinxS // psub_pval.
- by rewrite joinxS.
by rewrite /sepx /= sepyS. 
Qed.

HB.instance Definition _ := isPCMS.Build (xsep R) sub_is_tpcms.
End XSepPCMS.

(*******************************)
(* Option pair PCM with bounds *)
(*******************************)


Definition oint2 := option (int * int).
HB.instance Definition _ := TPCMS.on oint2.

Module RWsep.
Import intZmod intOrdered ssralg.GRing ssralg.GRing.Theory Num.Theory Num.Def.
Import order.Order.TTheory order.Order.DefaultProdOrder order.Order.ProdSyntax.
Import order.Order.DefaultProdLexiOrder order.Order.LexiSyntax.  
Local Open Scope order_scope.
Local Open Scope ring_scope.

(* positive pairs, lexi smaller than (1, 0) *)
(* describes the valid states of a rw-lock *)
(* we either have no writers and any positive number of readers *)
(* or 1 writer and no readers *)
Definition bnd2 (x : int *l int) := 
  ((0,0)%Z <=^p x) && (x <=^l (1,0)%Z).

(* here want to use \+ from pcm scope *)
Definition rwsep : rel oint2 := 
  fun x y => if (x, y) is (Some x, Some y) then 
    [&& bnd2 x, bnd2 y & bnd2 (x \+ y)%pcm] else true.

Lemma rwsep_is_seprel : seprel_axiom rwsep.
Proof.
rewrite /rwsep; split=>[|[[x1 x2]|][[y1 y2]|]|
[[x1 x2]|][[y1 y2]|]|[[x1 x2]|][[y1 y2]|][[z1 z2]|]] //= _.
- by rewrite andbCA pcm.joinC.
- by rewrite unitR andbb; case/and3P.
do ![rewrite !pcmE /=]; case/and3P=>X Y _ /and3P [_ Z H].
rewrite -!addrA in H; rewrite X Y Z H andbT /= andbb.
case/andP: X=>/andP [/= X1 X2] _; case/andP: Y=>/andP [/= Y1 Y2] _.
case/andP: Z=>/andP [/= Z1 Z2] _; case/andP: H=>_ /andP [/= H1 H2].
rewrite /bnd2/Order.le/=/Order.ProdOrder.le/Order.ProdLexiOrder.le /=.
apply/andP; split=>[{X1 X2 H1 H2}|{Y1 Y2 Z1 Z2}].  
- by rewrite !addr_ge0.
rewrite (le_eqVlt 1%Z) ltNge (le_trans _ H1) ?lerDr ?orbF //=.
case: (ltgtP _ (add y1 z1)) X1 H1 X2 H2=>//= <-.
rewrite gerDr lerDr=>-> /= _ X2 H2.
by rewrite -(lerD2l x2) ler_wpDl.
Qed.

#[export] HB.instance Definition _ := 
  isSeprel.Build oint2 rwsep rwsep_is_seprel.

(* rwsep preserves subtraction *)
Lemma rwsep_is_sseprel : sseprel_axiom rwsep.
Proof.
rewrite /rwsep; case=>[[x1 x2]|][[y1 y2]|] //= _.
do ![rewrite pcmE /unjoin /=].
by rewrite -!addrA !addNr !addr0 !andbb =>->->->. 
Qed.

#[export] HB.instance Definition _ := 
  isSseprel.Build oint2 rwsep rwsep_is_sseprel.

Definition rw := xsep rwsep.
Definition rwsub : sub_struct rw oint2 := xsub rwsep.
HB.instance Definition _ := TPCMS.on rw.
HB.instance Definition _ := SubTPCM_struct.on rwsub.

Lemma rw_is_conic : pcmc_axiom rw.
Proof.
move=>x y; case: normalP=>// /[dup] V /(valid_sepUnS rwsub).
rewrite -!(unitb_pval rwsub) pfjoinT //= {V}.
case: {x}(pval _ x)=>[[x1 x2]|//]; case: {y}(pval _ y)=>[[y1 y2]|//].
rewrite /sepx/=/rwsep; do ![rewrite pcmE /= /unitb]; rewrite !addr_eq0.
case: (x1 =P opp y1)=>// ->{x1}; case: (x2 =P opp y2)=>// ->{x2}.
rewrite /bnd2/Order.le/=/Order.ProdOrder.le/Order.ProdLexiOrder.le /=.
rewrite !oppr_eq0 !oppr_ge0 oppr_le0.
by case: (ltgtP y1 0); case: (ltgtP y2 0)=>//=; rewrite andbF.
Qed.

#[export] HB.instance Definition _ := isPCMC.Build rw rw_is_conic.

(* extracting number of writers and number of readers out of rw state *)
(* explicitly made out to be nats, not ints *)

Definition wr_no (x : rw) := oapp (absz \o fst) 0 (pval rwsub x).  
Definition rd_no (x : rw) := oapp (absz \o snd) 0 (pval rwsub x).

Module Exports. 
Notation rwsep := rwsep.
Notation rw := rw.
Notation rwsub := rwsub.

Notation "#w x" := (wr_no x) (at level 1).
Notation "#r x" := (rd_no x) (at level 1).

(* generic lemmas to relate x to the pair (#w x, #r x) *)

Lemma psub_rwsub (x : rw) : 
        valid x -> 
        x = psub rwsub (Some (#w x %:Z, #r x %:Z)).
Proof.
move/[dup]/(valid_sepS rwsub). 
rewrite -{2 3}(psub_pval rwsub x) /wr_no/rd_no/oapp /=. 
case: (pval rwsub x)=>[[x1 x2]|] /=; last first. 
- by rewrite (negbTE (psub_undef _)).
case/andP=>/andP [/andP [/= X1 X2]] _ _ _.
by case: x1 x2 X1 X2=>// x1 [].
Qed.

Lemma pval_rwsub (x : rw) : 
        valid x -> 
        pval rwsub x = Some (#w x %:Z, #r x %:Z).
Proof. by move=>V; rewrite {1}(psub_rwsub V) valid_psubS //= -psub_rwsub. Qed.

Lemma rwlex x : (#w x, #r x) <=^l (1, 0) :> (nat *l nat).
Proof.
case: (normalP x)=>[->|V].
- by rewrite /wr_no/rd_no !pfundef.
move: (valid_sepS rwsub V); rewrite pval_rwsub //=.
by case/andP=>/andP []. 
Qed.

HB.reexport. 
End Exports.
End RWsep.
HB.export RWsep.Exports.

