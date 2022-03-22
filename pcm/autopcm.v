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
From mathcomp Require Import ssrnat eqtype seq.
From fcsl Require Import options pred.
From fcsl Require Import pcm.

(**************************************************************************)
(**************************************************************************)
(* Canonical structure lemmas for automating the following:               *)
(*                                                                        *)
(* Extracting the residual TPCM expression by cancelling all terms from a *)
(* given expression e2 in e1.                                             *)
(*                                                                        *)
(**************************************************************************)
(**************************************************************************)


(* First, two general helper concepts for searching in sequences. They will be *)
(* useful in syntactifying the expressions e1 and e2 for both tasks. The       *)
(* contepts are:                                                               *)
(*                                                                             *)
(* - onth: returns None to signal that an element is not found                 *)
(* - prefix: a prefix relation on sequences, will be used for growing          *)
(*   interpretation contexts                                                   *)

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

Lemma onth_mem (A : eqType) (s : seq A) n x : onth s n = some x -> x \in s.
Proof.
by elim: s n=>//= a s IH [[->]|n /IH]; rewrite inE ?eq_refl // orbC => ->.
Qed.

(* Context structure for reflection of unionmap expressions. We          *)
(* reflect the keys and the variables of the map expression. (The        *)
(* variables are all expressions that are not recognized as a key, or as *)
(* a disjoint union). We reflect disjoint union as a sequence.           *)
(*                                                                       *)
(* The context of keys is thus seq K. The context of vars is seq U.      *)

Section ReflectionContexts.
Variables (U : pcm).

Structure ctx := Context {expx : seq U}.

Definition empx := Context [::].

(* because contexts grow during computation, *)
(* we need a notion of sub-context *)

Definition sub_ctx (i j : ctx) :=
  prefix (expx i) (expx j).

Lemma sc_refl i : sub_ctx i i.
Proof. by []. Qed.

Lemma sc_trans i j k : sub_ctx i j -> sub_ctx j k -> sub_ctx i k.
Proof. by apply: prefix_trans. Qed.

End ReflectionContexts.

(* Expr and map variables are syntactified as De Bruijn indices in the context. *)
(* Disjoint union is syntactified as concatenation of lists.                    *)
(*                                                                              *)
(* Expr n : syntax for "expression indexed the context under number n"          *)
(* Var n : syntax for "expression indexed in the context under number n"        *)

(* In the cancellation algorithms, we iterate over the first              *)
(* expression e1 and remove each of its components from the second        *)
(* expression e2. But, typically, we want to remove only one occurrence   *)
(* of that component.                                                     *)
(*                                                                        *)
(* First, almost always, only one occurrence will exist, lest e2 be       *)
(* undefined. Thus, it's a waste of effort to traverse e2 in full once    *)
(* we've found an occurrence.                                             *)
(*                                                                        *)
(* Second, in some symmetric cancellation problems, e.g., dom_eq e1 e2,   *)
(* we *want* to remove only one occurrence from e2 for each component in  *)
(* e1. Otherwise, we will not produce a sound reduction. E.g.  dom (x \+  *)
(* x) (x \+ x) is valid, since both expressions are undef. However, after *)
(* removing x from the left side, and both x's from the right side, we    *)
(* get dom x Unit, which is not valid.                                    *)
(*                                                                        *)
(* Thus, as a matter of principle, we want a filter that removes just one *)
(* occurrence of a list element.                                          *)
(*                                                                        *)
(* We write it with p pulled out in a section in order to get it to       *)
(* simplify automatically.                                                *)

Section OneShotFilter.
Variables (A : Type) (p : pred A).

(* a variant of filter that removes only the first occurence *)

Fixpoint rfilter (ts : seq A) : seq A :=
  if ts is t :: ts' then if p t then ts' else t :: rfilter ts' else [::].

End OneShotFilter.

(* rfilter can also be thought of as a generalization of rem *)
Lemma rfilter_rem {T : eqType} (ts : seq T) x :
        rfilter (pred1 x) ts = rem x ts.
Proof. by elim: ts=> [|t ts IH] //=; case: eqP=>//= _; rewrite IH. Qed.

(* now for reflection *)

Section Reflection.
Variables (U : pcm).
Implicit Type i : ctx U.

Variant term := Expr of nat.

Definition nat_of (t : term) : nat :=
  let: Expr n := t in n.

(* interpretation function for elements *)
Definition interp' (i : ctx U) (t : term) : option U :=
  let: Expr n := t in
  onth (expx i) n.

(* PCMs lifted to options, TODO move to pcm? *)
(*
Definition ojoin (x y : option U) : option U :=
  if x is Some a then
    if y is Some b
      then Some (a \+ b)
      else None
    else None.

Definition ovalid (x : option U) :=
  if x is Some a then valid a else false.

Definition ounit : option U := Some Unit.

Lemma ojoinC x y : ojoin x y = ojoin y x.
Proof. by case: x; case: y=>//=b a; rewrite joinC. Qed.

Lemma ojoinA x y z : ojoin x (ojoin y z) = ojoin (ojoin x y) z.
Proof. by case: x; case: y; case: z=>//=c b a; rewrite joinA. Qed.

(* sanity check *)
Lemma ovalidL x y : ovalid (ojoin x y) -> ovalid x.
Proof. by case x=>//=a; case: y=>//=b /validL. Qed.

Lemma ovalidR x y : ovalid (ojoin x y) -> ovalid y.
Proof. by rewrite ojoinC => /ovalidL. Qed.

Lemma ounitL x : ojoin ounit x = x.
Proof. by case: x=>//=a; rewrite unitL. Qed.

Lemma ounitR x : ojoin x ounit = x.
Proof. by case: x=>//=a; rewrite unitR. Qed.

Lemma ojoinCA x y z : ojoin x (ojoin y z) = ojoin y (ojoin x z).
Proof. by case: x; case: y; case: z=>//=c b a; rewrite joinCA. Qed.
*)
(* main interpretation function *)
Notation fx i := (fun t f => interp' i t \+ f).
Definition interp (i : ctx U) (ts : seq term) : option U :=
  foldr (fx i) Unit ts.

Lemma fE i ts x : foldr (fx i) x ts = x \+ interp i ts.
Proof. by elim: ts x=>[|t ts IH] x /=; rewrite ?unitR // IH /= joinCA. Qed.

Lemma interp_rev i ts : interp i (rev ts) = interp i ts.
Proof.
elim: ts=>[|t ts IH] //=; rewrite rev_cons -cats1.
by rewrite /interp foldr_cat fE /= unitR IH.
Qed.

(* we also need a pretty-printer, which works the same as interp *)
(* but removes trailing Unit's *)

Fixpoint pprint i ts :=
  if ts is t :: ts' then
    if ts' is [::] then interp' i t else interp' i t \+ pprint i ts'
  else Unit.

Lemma pp_interp i ts : pprint i ts = interp i ts.
Proof. by elim: ts=>[|t ts /= <-] //; case: ts=>//; rewrite unitR. Qed.

Definition exp n t := let: Expr m := t in n == m.

Definition efree n t := rfilter (exp n) t.

Lemma expN i n ts : ~~ has (exp n) ts -> interp i (efree n ts) = interp i ts.
Proof. by elim: ts=>[|t ts IH] //=; case: ifP=>//= _ /IH ->. Qed.

Lemma expP i n ts :
        has (exp n) ts ->
        interp i ts = onth (expx i) n \+ interp i (efree n ts).
Proof.
elim: ts=>[|t ts IH] //=; case: ifP=>/= [|_ H].
- by case: t=>/= m /eqP->.
by rewrite (IH H) joinCA.
Qed.

(* interpretation is invariant under context weakening *)
(* under assumption that the interpreted term is well-formed *)

Definition wf i t :=
  let: Expr n := t in n < size (expx i).

Lemma sc_wf i j ts : sub_ctx i j -> all (wf i) ts -> all (wf j) ts.
Proof.
move/prefix_size=>H; elim: ts=>[|t ts IH] //=.
case/andP=>Hi /IH ->; rewrite andbT.
by case: t Hi=>v /= Hi; apply: leq_trans H.
Qed.

Lemma sc_interp i j ts :
        sub_ctx i j -> all (wf i) ts -> interp i ts = interp j ts.
Proof.
move=>H; elim: ts=>[|t ts IH] //= /andP [H0] /IH ->.
by case: t H0=>n /= /prefix_onth <-.
Qed.

Lemma valid_wf i ts : valid (interp i ts) -> all (wf i) ts.
Proof.
elim: ts=>[|t ts IH] //= V; rewrite (IH (validR V)) andbT.
case: t {V IH} (validL V)=>n /=.
by case X: (onth _ _)=>[a|] //=; rewrite (onth_size X).
Qed.

Lemma wf_some i ts : all (wf i) ts -> exists u, interp i ts = Some u.
Proof.
elim: ts=>[|t ts IH] /=; first by move=>_; exists Unit.
case/andP; case: t=>n /= /size_onth [u1->] /IH [u2 ->].
by exists (u1 \+ u2).
Qed.

Lemma wf_efree i n ts : all (wf i) ts -> all (wf i) (efree n ts).
Proof. by elim: ts=>//= t ts IH; case: ifP=>_ /andP [] //= -> /IH ->. Qed.

(* sometimes we want to get keys in a list, not in a predicate *)
(*
Definition getexprs :=
  foldr (fun t es => if t is Expr e then e :: es else es) [::].

Lemma has_getexprs ts n : n \in getexprs ts = has (exp n) ts.
Proof. by elim: ts=>//= t ts IH; case: t=>m //; rewrite inE IH. Qed.
*)
End Reflection.


(**********************************************************************)
(**********************************************************************)
(* Purely functional decision procedures for the three tasks. Further *)
(* below, they will be embedded into the canonical programs validX    *)
(* and domeqX and invalidX respectively.                              *)
(**********************************************************************)
(**********************************************************************)

(* subterm is purely functional version of validX *)

(* subtract is purely functional version of domeqX *)

Section Subtract.
Variables (U : pcm).
Implicit Types (i : ctx U) (ts : seq term).

(* We need a subterm lemma that returns the residiual of ts1. *)
(* xs accumulates uncancelled part of ts1, starting as nil *)

Fixpoint subtract ts1 ts2 xs : option (seq term) :=
  match ts1 with
    Expr n :: tsx1 =>
      if has (exp n) ts2 then subtract tsx1 (efree n ts2) xs
      else subtract tsx1 ts2 (Expr n :: xs)
  | [::] => if ts2 is [::] then Some xs else None
  end.

Lemma subtract_sound i ts1 ts2 rs1 xs :
        all (wf i) ts1 -> all (wf i) ts2 ->
        subtract ts1 ts2 xs = Some rs1 ->
        interp i ts1 \+ interp i xs = interp i rs1 \+ interp i ts2.
Proof.
elim: ts1 ts2 xs=>[|t ts1 IH] ts2 xs /= =>[_|/andP [At A1]].
- by case: ts2=>//=_; case=>->; rewrite unitR unitL.
case: t At=>n /= /size_onth [x X] A2; case: ifP=>Y.
- rewrite -joinA; move: (expP i Y)=>-> /(IH _ _ A1 (wf_efree n A2))->.
  by rewrite joinCA.
by move/(IH _ _ A1 A2)=><-/=; rewrite joinCA joinA.
Qed.

End Subtract.


(********************************)
(********************************)
(* Canonical structure programs *)
(********************************)
(********************************)

(* first a helper program for searching and inserting in a list *)

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




Module Syntactify.
Section Syntactify.
Variables (U : pcm).
Implicit Types (i : ctx U) (ts : seq term).

(* a tagging structure to control the flow of computation *)
Structure tagged_pcm := Tag {untag : U}.

Local Coercion untag : tagged_pcm >-> PCM.sort.

(* in reversed order; first test for unions, then empty, and exprs *)
Definition expr_tag := Tag.
Definition empty_tag := expr_tag.
Canonical Structure union_tag hc := empty_tag hc.

(* Main structure                                 *)
(* - i : input context                            *)
(* - j : output context                           *)
(* - ts : syntactification of pcm using context j *)

Definition axiom i j ts (pivot : tagged_pcm) :=
  [/\ interp j ts = Some (untag pivot), sub_ctx i j & all (wf j) ts].
Structure form i j ts := Form {pivot : tagged_pcm; _ : axiom i j ts pivot}.

Local Coercion pivot : form >-> tagged_pcm.

(* check for union *)

Lemma union_pf i j k ts1 ts2 (f1 : form i j ts1) (f2 : form j k ts2) :
        axiom i k (ts1 ++ ts2) (union_tag (untag f1 \+ untag f2)).
Proof.
case: f1 f2 =>[[u1]] /= [E1 S1 W1][[u2]][E2 S2 W2]; split=>/=.
- by rewrite /interp foldr_cat !fE unitL joinC -(sc_interp S2 W1) E1 E2.
- by apply: sc_trans S1 S2.
by rewrite all_cat (sc_wf S2 W1) W2.
Qed.

Canonical union_form i j k ts1 ts2 (f1 : form i j ts1) (f2 : form j k ts2) :=
  @Form i k (ts1 ++ ts2) (union_tag (untag f1 \+ untag f2)) (@union_pf i j k ts1 ts2 f1 f2).

(* check if reached empty *)

Lemma empty_pf i : axiom i i [::] (empty_tag Unit).
Proof. by split. Qed.

Canonical empty_form i := 
  @Form i i nil (empty_tag Unit) (@empty_pf i).

(* check for expr *)

Lemma expr_pf exprs1 exprs2 n (f : xfind exprs1 exprs2 n) :
        axiom (Context exprs1) (Context exprs2)
              [:: Expr n] (expr_tag (xuntag f)).
Proof.
case: f=>p [E H]; split=>//=; first by rewrite unitR.
by rewrite andbT (onth_size E).
Qed.

Canonical expr_form exprs1 exprs2 n (f : xfind exprs1 exprs2 n) := 
  @Form (Context exprs1) (Context exprs2) [:: Expr n] 
        (expr_tag (xuntag f)) (@expr_pf exprs1 exprs2 n f).

End Syntactify.

Module Exports.
Coercion untag : tagged_pcm >-> PCM.sort.
Coercion pivot : form >-> tagged_pcm.
Canonical union_tag.
Canonical union_form.
Canonical empty_form.
Canonical expr_form.

End Exports.
End Syntactify.

Export Syntactify.Exports.

(*
Lemma blah (j : ctx natPCM) (ts : seq term) (e : Syntactify.form (Context [::]) j ts) x : 
         Syntactify.untag (Syntactify.pivot e) = x -> j = j -> ts = ts -> Syntactify.untag (Syntactify.pivot e) = x. 
by [].
Qed.

Lemma blah1 : 1 \+ 2 \+ 3 = 4.
apply: blah. 
*)


(*********************)
(* Automating domeqX *)
(*********************)

Module SubtractX.
Section SubtractX.
Variables (U : pcm).
Implicit Types (j : ctx U) (ts : seq term).
Notation form := Syntactify.form.
Notation untag := Syntactify.untag.

Structure packed_pcm (m : U) := Pack {unpack : U}.
Canonical equate (m : U) := Pack m m.

(* TODO move to prelude *)
Definition someb {A} (x : option A) : bool :=
  if x isn't None then true else false.

(* j   : input context                        *)
(* ts1  : the syntactification of subtractee in j *)
(* k   : output context                       *)
(* ts2 : syntactification of goal             *)
(* rs  : syntactification of residual         *)
(* b   : witness of rs being valid (not None) *)

Definition raxiom (j k : ctx U) (ts1 : seq term) (ts2 : seq term) (rs : seq term) (b : bool) g (pivot : packed_pcm g) := True.


Structure rform j k ts1 ts2 rs b g :=
  RForm {pivot :> packed_pcm g; _ : @raxiom j k ts1 ts2 rs b g pivot}.

(* start instance: note how subtract ts1 ts2 [::] is unified with *)
(* the b component of rform thus passing the residual terms *)

(*
Lemma start_pf j k ts1 ts2 (f2 : form j k ts2) :
  let sub := subtract ts1 ts2 [::] in
  @raxiom j k ts1 sub (someb sub) (untag f2) (equate f2).
Proof.
case: f2=>f2 [E1 S A2]; case E : (subtract _ _ _)=>[rs|] //= A1 _.
by move/(subtract_sound (sc_wf S A1) A2): E=>/=; rewrite unitR joinC E1=>->.
Qed.
*)

Canonical start j ts1 k ts2 b res := 

@RForm j ts1 k g ts2 (f2 : form j k ts2) b res (equate f2)    (@start_pf j k ts1 ts2 f2).

End SubtractX.

Module Exports.
Canonical equate.
Canonical start.

Section Exports.
Variables (U : pcm).
Implicit Types (j : ctx U) (ts : seq term).
Notation form := Syntactify.form.
Notation untag := Syntactify.untag.

(* the main lemma; notice how residuals rs1, rs2 are passed to g to compute *)

Lemma subtractX m j k ts1 rs (f1 : form (empx U) j ts1)
                             (g : rform j k ts1 true m rs) :
        untag f1 = unpack (pivot g) \+ odflt Unit (obind (pprint k) rs).
Proof.
case: g f1; case=>pivot R [f1][E _ A1] /=.
case/(_ A1 erefl): R =>S /=; rewrite -(sc_interp S A1) E.
case: rs=>/= [trs|]; last by rewrite !unitR; case.
by rewrite pp_interp; case: (interp k trs)=>//= u2; case.
Qed.

Lemma subtractX' m j tsm (fm : form (empx U) j tsm)
                 k wh rs
                 (g : rform j k m true wh rs) x :
        untag fm = m -> 
        g = g -> k = k -> rs = rs ->
        unpack (pivot g) = x.
Admitted.

End Exports.

Arguments subtractX [U] m {j k ts1 rs f1 g}.

Example ex0 (x y z : nat) :
          1 \+ x \+ 2 \+ y \+ 3 \+ z = 0.
Proof.
apply: (subtractX' xxxx).

apply: (subtractX' (m:=(1 \+ x))).

rewrite (subtractX (1 \+ x)).

move: (@subtractX natPCM (1 \+ x)) =>/=.
rewrite (subtractX (1 \+ x)).
apply: domeqX=>/=. Abort.

End Exports.
End SubtractX.

Export SubtractX.Exports.






















Module SubtractX.
Section SubtractX.
Variables (U : pcm).
Implicit Types (j : ctx U) (ts : seq term).
Notation form := Syntactify.form.
Notation untag := Syntactify.untag.

Structure packed_pcm (m : U) := Pack {unpack : U}.
Canonical equate (m : U) := Pack m m.

(* TODO move to prelude *)
Definition someb {A} (x : option A) : bool :=
  if x isn't None then true else false.

(* j   : input context                        *)
(* k   : output context                       *)
(* ts1 : syntactification of left PCM         *)
(* rs  : syntactification of residual         *)
(* b   : witness of rs being valid (not None) *)
(* m   : the right PCM                        *)
Definition raxiom j k ts1 rs b m (pivot : packed_pcm m) :=
  all (wf j) ts1 -> b -> sub_ctx j k /\
  interp k ts1 = Some (unpack pivot) \+ interp k (odflt [::] rs).

Structure rform j k ts1 b m res :=
  RForm {pivot :> packed_pcm m; _ : raxiom j k ts1 res b pivot}.

(* start instance: note how subtract ts1 ts2 [::] is unified with *)
(* the b component of rform thus passing the residual terms *)

Lemma start_pf j k ts1 ts2 (f2 : form j k ts2) :
  let sub := subtract ts1 ts2 [::] in
  @raxiom j k ts1 sub (someb sub) (untag f2) (equate f2).
Proof.
case: f2=>f2 [E1 S A2]; case E : (subtract _ _ _)=>[rs|] //= A1 _.
by move/(subtract_sound (sc_wf S A1) A2): E=>/=; rewrite unitR joinC E1=>->.
Qed.

Canonical start j k ts1 ts2 f2 := RForm (@start_pf j k ts1 ts2 f2).

End SubtractX.

Module Exports.
Canonical equate.
Canonical start.

Section Exports.
Variables (U : pcm).
Implicit Types (j : ctx U) (ts : seq term).
Notation form := Syntactify.form.
Notation untag := Syntactify.untag.

(* the main lemma; notice how residuals rs1, rs2 are passed to g to compute *)

Lemma subtractX m j k ts1 rs (f1 : form (empx U) j ts1)
                             (g : rform j k ts1 true m rs) :
        untag f1 = unpack (pivot g) \+ odflt Unit (obind (pprint k) rs).
Proof.
case: g f1; case=>pivot R [f1][E _ A1] /=.
case/(_ A1 erefl): R =>S /=; rewrite -(sc_interp S A1) E.
case: rs=>/= [trs|]; last by rewrite !unitR; case.
by rewrite pp_interp; case: (interp k trs)=>//= u2; case.
Qed.

Lemma subtractX' m j tsm (fm : form (empx U) j tsm)
                 k wh rs
                 (g : rform j k m true wh rs) x :
        untag fm = m -> 
        g = g -> k = k -> rs = rs ->
        unpack (pivot g) = x.
Admitted.

End Exports.

Arguments subtractX [U] m {j k ts1 rs f1 g}.

Example ex0 (x y z : nat) :
          1 \+ x \+ 2 \+ y \+ 3 \+ z = 0.
Proof.
apply: (subtractX' xxxx).

apply: (subtractX' (m:=(1 \+ x))).

rewrite (subtractX (1 \+ x)).

move: (@subtractX natPCM (1 \+ x)) =>/=.
rewrite (subtractX (1 \+ x)).
apply: domeqX=>/=. Abort.

End Exports.
End SubtractX.

Export SubtractX.Exports.

