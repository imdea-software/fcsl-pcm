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
From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq eqtype.
From pcm Require Import options prelude auto.

(**********************************************************)
(**********************************************************)
(* Canonical structure lemmas for automating three tasks  *)
(* given hypothesis uniq s, of uniqueness of elements of  *)
(* sequence s.                                            *)
(*                                                        *)
(* 1. Automate inferring uniq s', when s' contains subset *)
(* of elements of s                                       *)
(*                                                        *)
(* 2. Automate inferring facts of the form x != y         *)
(* when x and y are both in s                             *)
(*                                                        *)
(* 3. Automate inferring facts of the form x \notin s'    *)
(* when x::s' contains subset of elements of s            *)
(**********************************************************)
(**********************************************************)


Section UniqReflectionContexts.
Variable A : eqType.

Structure ctx := Context {keyx : seq A; varx : seq (seq A)}.
Definition empx := Context [::] [::].

(* sub-context *)
Definition sub_ctx (i j : ctx) :=
  Prefix (keyx i) (keyx j) /\ Prefix (varx i) (varx j).

Lemma sc_refl i : sub_ctx i i.
Proof. by []. Qed.

Lemma sc_trans i j k : 
        sub_ctx i j -> 
        sub_ctx j k -> 
        sub_ctx i k.
Proof. 
by case=>K1 V1 [K2 V2]; split; [move: K2|move: V2]; apply: Prefix_trans. 
Qed.

End UniqReflectionContexts.

Section UniqReflection.
Variable A : eqType.
Implicit Type i : ctx A.
Inductive term := Pts of nat | Var of nat.

Definition eq_term t1 t2 : bool :=
  match t1, t2 with 
  | Pts n1, Pts n2 => n1 == n2
  | Var x1, Var x2 => x1 == x2
  | _, _ => false
  end.
Lemma eq_termP : Equality.axiom eq_term.
Proof. 
case=>n; case=>m /=; try by [constructor];
by case: eqP=>[->|N]; constructor=>//; case=>/N.
Qed.

HB.instance Definition _ := hasDecEq.Build term eq_termP.

(* interpretation for terms *) 
Definition interp' i (t : term) : seq A := 
 match t with
    Pts n => if onth (keyx i) n is Some k then [:: k] else [::]
  | Var n => if onth (varx i) n is Some f then f else [::]
  end.

(* interpretation for term sequences *)
Definition interp (i : ctx A) (ts : seq term) : seq A := 
  foldr (fun t s => interp' i t ++ s) [::] ts.

Lemma interp_cat k ts1 ts2 :
        interp k (ts1 ++ ts2) = interp k ts1 ++ interp k ts2.
Proof. by elim: ts1=>[|t ts1 IH] //=; rewrite -catA IH. Qed.

(* interpretation is invariant under context weakening *)
(* under assumption that the interpreted term is well-formed *)
Definition wf i t :=
  match t with
  | Pts n => n < size (keyx i)
  | Var n => n < size (varx i)
  end.

Lemma sc_wf i j ts : 
        sub_ctx i j -> 
        all (wf i) ts -> all (wf j) ts.
Proof.
case=>/Prefix_size H1 /Prefix_size H2; elim: ts=>[|t ts IH] //=.
case/andP=>H /IH ->; rewrite andbT.
by case: t H=>n H; apply: leq_trans H _.
Qed.

Lemma sc_interp i j ts :
        sub_ctx i j -> 
        all (wf i) ts -> 
        interp i ts = interp j ts.
Proof.
case=>H1 H2; elim: ts=>[|t ts IH] //= /andP [H] /IH ->.
by case: t H=>n /= /Prefix_onth <-.
Qed.

Definition key n t := if t is Pts m then n == m else false.
Definition var n t := if t is Var m then n == m else false.
Definition kfree n t := rfilter (key n) t.
Definition vfree n t := rfilter (var n) t.

Lemma kfree_sub ts n : {subset kfree n ts <= ts}.  
Proof.
elim: ts=>[|x ts IH] // z; rewrite /kfree/= inE.
case: ifP=>[_ ->|_]; first by rewrite orbT. 
by rewrite inE; case: (z =P x)=>//= _ /IH.
Qed.

Lemma vfree_sub ts n : {subset vfree n ts <= ts}.  
Proof.
elim: ts=>[|x ts IH] // z; rewrite /vfree/= inE.
case: ifP=>[_ ->|_]; first by rewrite orbT. 
by rewrite inE; case: (z =P x)=>//= _ /IH.
Qed.

Lemma wf_kfree i n ts : 
        all (wf i) ts -> 
        all (wf i) (kfree n ts).
Proof. 
rewrite /kfree; elim: ts=>//= -[]t ts IH /=; last first.
- by case/andP=>-> /IH.
by case: (n =P t)=>[_ /andP []|/= _ /andP [->] /IH].
Qed.

Lemma wf_vfree i n ts : 
        all (wf i) ts -> 
        all (wf i) (vfree n ts).
Proof. 
rewrite /vfree; elim: ts=>//= -[]t ts IH /=. 
- by case/andP=>-> /IH.
by case: (n =P t)=>[_ /andP []|/= _ /andP [->] /IH].
Qed.

Lemma keyN i n ts : 
        ~~ has (key n) ts -> 
        perm_eq (interp i (kfree n ts)) (interp i ts).
Proof. 
elim: ts=>[|t ts IH] //=; rewrite negb_or; case/andP=>H1.
move/IH=>E; rewrite /kfree /= (negbTE H1) /=.
by rewrite perm_cat2l E.
Qed.

Lemma varN i n ts : 
        ~~ has (var n) ts -> 
        perm_eq (interp i (vfree n ts)) (interp i ts).
Proof.
elim: ts=>[|t ts IH] //=; rewrite negb_or; case/andP=>H1.
move/IH=>E; rewrite /vfree /= (negbTE H1) /=.
by rewrite perm_cat2l E.
Qed.

Lemma keyP i n k ts :
        has (key n) ts -> 
        onth (keyx i) n = Some k ->
        perm_eq (interp i ts) (k :: interp i (kfree n ts)).
Proof.
rewrite /kfree; elim: ts=>[|[]t ts IH] //=.
- case: (n =P t)=>[-> _ ->//|/= _ H /(IH H) {}IH]. 
  case: (onth _ t)=>[a|] //; rewrite -(cat1s k).  
  apply: perm_trans (perm_cat _ IH) _=>//.
  by rewrite -(cat1s k) !catA perm_cat // perm_catC.
move=>H /(IH H) {}IH.
case: (onth _ t)=>[a|] //=; rewrite -(cat1s k).
apply: perm_trans (perm_cat _ IH) _=>//.
by rewrite -(cat1s k) !catA perm_cat // perm_catC.
Qed.
  
Lemma varP i n u ts :
        has (var n) ts -> 
        onth (varx i) n = Some u ->
        perm_eq (interp i ts) (u ++ interp i (vfree n ts)).
Proof.
rewrite /vfree; elim: ts=>[|[]t ts IH] //=.
- move=>H /(IH H) {}IH.
  case: (onth _ t)=>[a|] //=; rewrite -(cat1s a).
  apply: perm_trans (perm_cat _ IH) _=>//. 
  by rewrite -(cat1s a (interp _ _)) !catA perm_cat // perm_catC.
case: (n =P t)=>[-> _ ->//|/= _ H /(IH H) {}IH]. 
case: (onth _ t)=>[a|] //=. 
apply: perm_trans (perm_cat _ IH) _=>//. 
by rewrite !catA perm_cat // perm_catC.
Qed.

End UniqReflection.

(* deciding if ts1 represents a subterm of ts2 *)

Section Subterm.
Variable A : eqType. 
Implicit Types (i : ctx A) (ts : seq term).

Fixpoint subterm ts1 ts2 :=
  match ts1 with
  | Pts n :: tsx1 =>
      if has (key n) ts2 then subterm tsx1 (kfree n ts2) else false
 | Var n :: tsx1 =>
      if has (var n) ts2 then subterm tsx1 (vfree n ts2) else false
  | [::] => true
  end.

(* the procedure is sound for deciding *)
(* subset and uniqueness properties *)

Lemma subterm_sound_sub i ts1 ts2 :
        all (wf i) ts1 -> 
        all (wf i) ts2 -> 
        subterm ts1 ts2 ->
        {subset interp i ts1 <= interp i ts2}.
Proof.
elim: ts1 ts2=>[|t ts1 IH] ts2 //= A1 A2.
case/andP: A1; case: t=>t /= /size_onth [k] X A1; rewrite X;
case: ifP=>Y // /(IH _ A1) S z.
- rewrite inE; case/orP=>[/eqP ->|].
  - by rewrite (perm_mem (keyP Y X)) inE eqxx.
  move/(S (wf_kfree _ A2)).
  by rewrite (perm_mem (keyP Y X)) inE orbC=>->.
rewrite mem_cat (perm_mem (varP Y X)) mem_cat.
case/orP=>[->//|] /(S (wf_vfree _ A2)) ->. 
by rewrite orbC.
Qed.

Lemma subterm_sound_uniq i ts1 ts2 :
        all (wf i) ts1 -> 
        all (wf i) ts2 -> 
        subterm ts1 ts2 ->
        uniq (interp i ts2) ->
        uniq (interp i ts1).
Proof. 
elim: ts1 ts2=>[|[]t ts1 IH] ts2 //= /andP [] /size_onth [k] /[dup] X -> 
A1 A2; case: ifP=>// Y S.
- move: (IH _ A1 (wf_kfree _ A2) S)=>{}IH.
  rewrite (perm_uniq (keyP Y X)) /=. 
  case/andP=>K /IH ->; rewrite andbT (contra _ K) //.
  by apply: (subterm_sound_sub A1 (wf_kfree _ A2) S).
move: (IH _ A1 (wf_vfree _ A2) S)=>{}IH.
rewrite (perm_uniq (varP Y X)) /= !cat_uniq.  
case/and3P=>-> /= H /IH ->; rewrite andbT (contra _ H) //.
case/hasP=>x /(subterm_sound_sub A1 (wf_vfree _ A2) S) V K.
by apply/hasP; exists x.
Qed.

End Subterm.

Module Syntactify.
Section Syntactify.
Variables (A : eqType).
Implicit Types (i : ctx A) (ts : seq term).

(* a tagging structure to control the flow of computation *)
Structure tagged_map := Tag {untag : seq A}.

Local Coercion untag : tagged_map >-> seq.

(* in reversed order; first test for unions, then cons, rcons, empty, and vars *)
Definition var_tag := Tag.
Definition empty_tag := var_tag. 
Definition rcons_tag := empty_tag. 
Definition cons_tag := rcons_tag. 
Canonical Structure union_tag hc := cons_tag hc.

(* Main structure                                    *)
(* - i : input context                               *)
(* - j : output context                              *)
(* - ts : syntactification of sequence using context j *)

Definition axiom i j ts (pivot : tagged_map) :=
  [/\ interp j ts = untag pivot, sub_ctx i j & all (wf j) ts].
Structure form i j ts := Form {pivot : tagged_map; _ : axiom i j ts pivot}.

Local Coercion pivot : form >-> tagged_map.

Lemma union_pf i j k ts1 ts2 (f1 : form i j ts1) (f2 : form j k ts2) :
        axiom i k (ts1 ++ ts2) (union_tag (untag f1 ++ untag f2)).
Proof.
case: f1 f2=>f1 [E1 S1 W1][f2][E2 S2 W2]; split=>/=.
- by rewrite interp_cat -(sc_interp S2 W1) E1 E2.
- by apply: sc_trans S1 S2.
by rewrite all_cat (sc_wf S2 W1) W2.
Qed.

Canonical union_form i j k ts1 ts2 f1 f2 :=
  Form (@union_pf i j k ts1 ts2 f1 f2).

(* check for cons *) 
Lemma cons_pf i keys2 k j ts (f1 : xfind (keyx i) keys2 k) 
          (f2 : form (Context keys2 (varx i)) j ts) :
        axiom i j (Pts k :: ts) (cons_tag (xuntag f1 :: untag f2)).
Proof.
case: f1 f2=>f1 [E1 H1][f2][E2 H2 W2]; split=>/=. 
- by rewrite -(Prefix_onth (onth_size E1) (proj1 H2)) E1 /= E2.
- by apply: sc_trans H2. 
by rewrite W2 andbT (leq_trans (onth_size E1)) // (Prefix_size (proj1 H2)).
Qed.

Canonical cons_form i keys2 k j ts f1 f2 :=
  Form (@cons_pf i keys2 k j ts f1 f2).

(* check for rcons *) 
Lemma rcons_pf i j ts keys2 k (f1 : form i j ts) 
           (f2 : xfind (keyx j) keys2 k) :
        axiom i (Context keys2 (varx j))
          (rcons ts (Pts k)) (rcons_tag (rcons (untag f1) (xuntag f2))).
Proof.
case: f1 f2=>f1 [E1 H1 W1][f2][E2 H2].
have H3 : sub_ctx j (Context keys2 (varx j)) by [].
split=>/=.
- by rewrite -cats1 interp_cat /= E2 -(sc_interp H3) // cats1 E1.
- by apply: (sc_trans H1 H3).
by rewrite all_rcons /= (onth_size E2) (sc_wf H3 W1).
Qed.

Canonical rcons_form i j ts keys2 k f1 f2 := 
  Form (@rcons_pf i j ts keys2 k f1 f2).

(* check if reached empty *)

Lemma empty_pf i : axiom i i [::] (empty_tag [::]).
Proof. by split. Qed.

Canonical empty_form i := Form (@empty_pf i).

(* check for var (default case) *)
Lemma var_pf i vars2 n (f : xfind (varx i) vars2 n) :
        axiom i (Context (keyx i) vars2)
              [:: Var n] (var_tag (xuntag f)).
Proof. 
case: f=>f [E H]; split=>//=; first by rewrite E cats0.
by rewrite (onth_size E).
Qed. 

Canonical var_form i vars2 n f := Form (@var_pf i vars2 n f).

End Syntactify.

Module Exports.
Coercion untag : tagged_map >-> seq.
Coercion pivot : form >-> tagged_map.
Canonical union_tag.
Canonical union_form.
Canonical cons_form.
Canonical rcons_form. 
Canonical empty_form. 
Canonical var_form.

End Exports.
End Syntactify.

Export Syntactify.Exports.

(*********************************************************************)
(* Overloaded lemma for concluding uniq facts out of uniq hypothesis *)
(*********************************************************************)

Module UniqX.
Section UniqX.
Variable A : eqType.
Implicit Types (j : ctx A) (ts : seq term).
Notation form := Syntactify.form.
Notation untag := Syntactify.untag.

Structure packed_map (m : seq A) := Pack {unpack : seq A}.
Canonical equate (m : seq A) := Pack m m.

Definition raxiom j ts1 m (b : bool) (pivot : packed_map m) :=
  all (wf j) ts1 -> uniq (interp j ts1) -> b -> uniq (unpack pivot).

Structure rform j ts1 m b :=
  RForm {pivot :> packed_map m; _ : raxiom j ts1 b pivot}.

(* start instance: note how subterm ts2 ts1 is unified with *)
(* the boolean component of rform *)

Lemma start_pf j k ts1 ts2 (f2 : form j k ts2) :
        @raxiom j ts1 (untag f2) (subterm ts2 ts1) (equate f2).
Proof.
case: f2=>f2 [E S A2] A1; rewrite (sc_interp S A1)=>V.
move/(subterm_sound_uniq A2 (sc_wf S A1))=>H /=.
by rewrite -E (H V).
Qed.

Canonical start j k ts1 ts2 f2 := RForm (@start_pf j k ts1 ts2 f2).

End UniqX.

Module Exports.
Canonical equate.
Canonical start.

Section Exports.
Variable A : eqType.
Implicit Types (j : ctx A) (ts : seq term).
Notation form := Syntactify.form.
Notation untag := Syntactify.untag.

(* main lemma *)
(* boolean component of rform is set to true *)
(* so that the lemma succeeds only if the subterm checks suceeds *)
Lemma uniqO m j ts1 (f1 : form (empx A) j ts1) (g : rform j ts1 m true) :
        uniq (untag f1) -> uniq (unpack (pivot g)).
Proof. 
case: g f1; case=>pivot H [f1][<- Sc X] /=.
by move/H; apply.
Qed.

End Exports.

Arguments uniqO {A m j ts1 f1 g}.

End Exports.
End UniqX.

Export UniqX.Exports.

(***********************************************************************)
(* Overloaded lemma for concluding _ != _ facts out of uniq hypothesis *)
(***********************************************************************)

Module NeqX.
Section NeqX.
Variable A : eqType.
Implicit Types (j : ctx A) (ts : seq term).
Notation form := Syntactify.form.
Notation untag := Syntactify.untag.

Structure packed_elem (x : A) := Pack {unpack : A}.
Canonical equate m := Pack m m.

Definition raxiom j ts1 (n : nat) m b (pivot : packed_elem m) :=
  all (wf j) ts1 -> uniq (interp j ts1) -> b -> 
    interp j [:: Pts n] != [:: unpack pivot].

Structure rform j ts1 (n : nat) m b :=
  RForm {pivot :> packed_elem m; _ : raxiom j ts1 n b pivot}.

Lemma start_pf j keys2 ts1 n m (f2 : xfind (keyx j) keys2 m) :
        @raxiom j ts1 n (xuntag f2) 
           (subterm [:: Pts n; Pts m] ts1) 
           (equate (xuntag f2)).
Proof.
case: f2; case=>f2 [O P] Aw U S.
have [Pn Pm] : Pts n \in ts1 /\ Pts m \in ts1.
- move: S=>/=; case: ifP=>//; case: ifP=>//.
  case/hasP=>/= -[] xm /kfree_sub Pm //= /eqP ->. 
  by case/hasP=>/= -[] xn //= Pn /eqP ->.
have Sn : wf j (Pts n) by move/allP: Pn; apply. 
have Sm : wf j (Pts m) by move/allP: Pm; apply.
have Ax: all (wf j) [:: Pts n; Pts m] by apply/and3P.
move: (subterm_sound_uniq Ax Aw S U)=>/=.
rewrite (Prefix_onth Sm P) O /= cat_uniq cats0.
case: (onth _ _)=>//= a; rewrite orbF andbT inE.
by apply: contra=>/eqP [->].
Qed.

Canonical start j keys2 ts1 n m f2 := RForm (@start_pf j keys2 ts1 n m f2).

End NeqX.

Module Exports.
Canonical equate.
Canonical start.

Section Exports.
Variable A : eqType.
Implicit Types (j : ctx A) (ts : seq term).
Notation form := Syntactify.form.
Notation untag := Syntactify.untag.

(* main lemma *)
Lemma neqO n m i keys2 ts1 (f : form (empx A) i ts1) 
          (x : xfind (keyx i) keys2 n) 
          (y : rform (Context keys2 (varx i)) ts1 n m true) :
        uniq (untag f) -> xuntag x != unpack (pivot y).
Proof.
case: f=>f [Ef S Aw]; case: x=>x [O P]; case: y=>y H.
rewrite /raxiom/= -Ef O cats0 in H *.
have {}S : sub_ctx i (Context keys2 (varx i)) by [].
rewrite -(sc_interp S) // (sc_wf S) // in H.
by move/(H erefl)=>/(_ erefl); apply: contra=>/eqP ->.
Qed.

Lemma test (x y z : A) : 
        uniq [:: x; y; z] ->
        (z != y)*(z != x) * (x != y).
Proof. by move=>U; rewrite !(neqO _ _ U). Abort.

End Exports.

Arguments neqO {A n m i keys2 ts1 f x y}.

End Exports.
End NeqX.

Export NeqX.Exports.

(***************************************************************************)
(* Overloaded lemma for concluding _ \notin _ facts out of uniq hypothesis *)
(***************************************************************************)

Module NotinX.
Section NotinX.
Variable A : eqType.
Implicit Types (j : ctx A) (ts : seq term).
Notation form := Syntactify.form.
Notation untag := Syntactify.untag.

Structure packed_map (x : seq A) := Pack {unpack : seq A}.
Canonical equate m := Pack m m.

Definition raxiom j ts1 (n : nat) m b (pivot : packed_map m) :=
  all (wf j) ts1 -> uniq (interp j ts1) -> b -> 
    uniq (interp j [:: Pts n] ++ unpack pivot).

Structure rform j ts1 (n : nat) m b :=
  RForm {pivot :> packed_map m; _ : raxiom j ts1 n b pivot}.

Lemma start_pf j k ts1 ts2 n (f2 : form j k ts2) :
        @raxiom j ts1 n (untag f2) 
           (subterm [:: Pts n & ts2] ts1) 
           (equate f2).
Proof.
case: f2=>f2 [E S A2] A1 U X /=.
have Pn : Pts n \in ts1.
- by move: X=>/=; case: ifP=>// /hasP [][] // xn /[swap] /eqP=>->. 
have Sn : wf j (Pts n) by move/allP: Pn; apply.
rewrite (sc_interp S A1) in U; move/(sc_wf S): A1=>A1.
have Ax : all (wf k) (Pts n :: ts2). 
- by apply/andP; split=>//; move/allP: Pn; apply.
move: (subterm_sound_uniq Ax A1 X U). 
by rewrite (Prefix_onth Sn (proj1 S)) cats0 -E.
Qed.

Canonical start j k ts1 ts2 n f2 := RForm (@start_pf j k ts1 ts2 n f2).

End NotinX.

Module Exports.
Canonical equate.
Canonical start.

Section Exports.
Variable A : eqType.
Implicit Types (j : ctx A) (ts : seq term).
Notation form := Syntactify.form.
Notation untag := Syntactify.untag.

(* main lemma *)
Lemma notinO n m i keys2 ts1 (f : form (empx A) i ts1) 
          (x : xfind (keyx i) keys2 n) 
          (y : rform (Context keys2 (varx i)) ts1 n m true) :
        uniq (untag f) -> xuntag x \notin unpack (pivot y).
Proof.
case: f=>f [Ef S Aw]; case: x=>x [O P]; case: y=>y H.
rewrite /raxiom/= -Ef O cats0 in H *.
have {}S : sub_ctx i (Context keys2 (varx i)) by [].
rewrite -(sc_interp S) // (sc_wf S) // in H.
by move/(H erefl)=>/(_ erefl) /andP [].
Qed.

Lemma test (x y z : A) : 
        uniq [:: x; y; z] ->
        (x \notin [:: z; y]) * (y \notin [:: x; z]).
Proof. by move=>U; rewrite !(notinO _ _ U). Abort.

End Exports.

Arguments notinO {A n m i keys2 ts1 f x y}.

End Exports.
End NotinX.

Export NotinX.Exports.

(* packaging the three automated lemmas into one *)
(* stating them in the form X = false instead of ~~ X *)
(* so that rewrites apply to positive terms as well *)
Lemma uniqX' (A : eqType) i ts1 (f1 : Syntactify.form (empx A) i ts1) :
        uniq f1 -> 
          (forall m (g : UniqX.rform i ts1 m true), 
             uniq (UniqX.unpack (UniqX.pivot g))) * 
          (forall n keys2 (x : xfind (keyx i) keys2 n),
             ((forall m (y : NeqX.rform (Context keys2 (varx i)) ts1 n m true),
               xuntag x == NeqX.unpack (NeqX.pivot y) = false) * 
             (forall m (y : NotinX.rform (Context keys2 (varx i)) ts1 n m true),
               xuntag x \in NotinX.unpack (NotinX.pivot y) = false))).
Proof. 
by move=>U; split; [|split]=>*; first by [apply: uniqO U];
apply/negbTE; [apply: neqO U|apply: notinO U].
Qed.

(* adding common goal transformations *)
(* that appear when reasoning about uniq *)
Definition uniqX {A i ts1 f1} U := 
  (mem_rcons, mem_cat, inE, negb_or, rcons_uniq, cat_uniq, andbT, orbF, 
   @uniqX' A i ts1 f1 U).

