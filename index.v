Require Import Strings.String.
Local Open Scope string_scope. 
Local Open Scope list_scope.
Scheme Equality for string.

Fixpoint seq (start len:nat) : list nat :=
    match len with
      | 0 => nil
      | S len => start :: seq (S start) len
    end.

Inductive array1 : Set :=
| O : array1
| S : nat -> array1 -> array1.
Check S 2 (S 2 (S 3 O)).


Inductive ErrorNat :=
  | error_nat : ErrorNat
  | num : nat -> ErrorNat.

Inductive ErrorBool :=
  | error_bool : ErrorBool
  | boolean : bool -> ErrorBool.
Coercion num: nat >-> ErrorNat.
Coercion boolean: bool >-> ErrorBool.

Inductive Result :=
  | err_undecl : Result
  | err_assign : Result
  | default : Result
  | res_nat : ErrorNat -> Result
  | res_bool : ErrorBool -> Result.

Scheme Equality for Result.

Inductive strNum :=
| snum : nat -> strNum
| snstr : string -> strNum.

Inductive Var := x | y | z | n.
Scheme Equality for Var.
Inductive Exp :=
| anum : nat -> Exp
| avar : Var -> Exp   
| astrNum: strNum -> Exp 
| aplus : Exp -> Exp -> Exp
| aaray: array1 -> nat -> Exp
| amul : Exp -> Exp -> Exp
| btrue : Exp
| bfalse : Exp
| blessthan : Exp -> Exp -> Exp
| bnot : Exp -> Exp
| band : Exp -> Exp -> Exp.

Coercion anum : nat >-> Exp.
Coercion avar : Var >-> Exp.
Notation "A +' B" := (aplus A B) (at level 50).
Notation "A *' B" := (amul A B) (at level 46).
Notation "A <=' B" := (blessthan A B) (at level 53).
Notation "'new_arr' A " := (aaray A) (at level 53).

Definition State := Var -> nat.
Definition sigma0 : State := fun n => 0.

Definition update (sigma : State)
           (x : Var) (v : nat) : State :=
  fun y => if (Var_beq x y)
           then v
           else (sigma y).
Definition sigma1 := (update sigma0 x 10).

Reserved Notation "E =[ S ]=> E'" (at level 60).

Inductive eval_exp : Exp -> State -> Exp -> Prop :=
| const : forall n st, anum n =[ st ]=> n
| lookup : forall x st, avar x =[ st ]=> (st x)
| add_1 : forall a1 a1' a2 a st,
    a1 =[ st ]=> a1' ->
    a = a1' +' a2 ->
    a1 +' a2 =[ st ]=> a
| add_2 : forall a1 a2 a2' a st,
    a2 =[ st ]=> a2' ->
    a = a1 +' a2' ->
    a1 +' a2 =[ st ]=> a
| add : forall i i1 i2 st,
    i = i1 + i2 ->
    anum i1 +' anum i2 =[ st ]=> i
| mul_1 : forall a1 a1' a2 a st,
    a1 =[ st ]=> a1' ->
    a = a1' *' a2 ->
    a1 *' a2 =[ st ]=> a
| mul_2 : forall a1 a2 a2' a st,
    a2 =[ st ]=> a2' ->
    a = a1 *' a2' ->
    a1 *' a2 =[ st ]=> a
| mul : forall i i1 i2 st,
    i = i1 * i2 ->
    anum i1 *' anum i2 =[ st ]=> i
| true : forall st, btrue =[ st ]=> btrue
| false : forall st, bfalse =[ st ]=> bfalse
| lessthan_1 : forall a1 a1' a2 st,
    a1 =[ st ]=> a1' -> 
    a1 <=' a2 =[ st ]=> a1' <=' a2
| lessthan_2 : forall i1 a2 a2' st,
    a2 =[ st ]=> a2' ->
    (anum i1) <=' a2 =[ st ]=> (anum i1) <=' a2'
| lessthan : forall b i1 i2 st,
    b = (if (Nat.leb i1 i2) then btrue else bfalse) ->
    (anum i1) <=' (anum i2) =[ st ]=> b 
| not : forall b b' st,
    b =[ st ]=> b' ->
    (bnot b) =[ st ]=> (bnot b')
| not_true : forall st,
    (bnot btrue) =[ st ]=> bfalse
| not_false : forall st,
    (bnot bfalse) =[ st ]=> btrue
| and : forall b1 b1' b2 st,
    b1 =[ st ]=> b1' ->
    (band b1 b2) =[ st ]=> (band b1' b2) 
| and_true : forall b2 st,
    (band btrue b2) =[ st ]=> b2 
| and_false : forall b2 st,
    (band bfalse b2) =[ st ]=> bfalse
where "E =[ S ]=> E'" := (eval_exp E S E').

Reserved Notation "E =[ S ]>* E'" (at level 60).

Inductive eval_exp_clos : Exp -> State -> Exp -> Prop :=
| refl : forall e st, e =[ st ]>* e
| tran : forall e1 e2 e3 st,
    e1 =[ st ]=> e2 -> e2 =[ st ]>* e3 -> e1 =[ st ]>* e3
where "E =[ S ]>* E'" := (eval_exp_clos E S E').

Inductive Typ : Type := Bool | Nat.
Print Exp.
Inductive type_of : Exp -> Typ -> Prop :=
| typ_num : forall n, type_of (anum n) Nat
| typ_var : forall x, type_of (avar x) Nat
| typ_plus : forall a1 a2,
    type_of a1 Nat ->
    type_of a2 Nat -> 
    type_of (a1 +' a2) Nat
| typ_mul : forall a1 a2,
    type_of a1 Nat ->
    type_of a2 Nat -> 
    type_of (a1 *' a2) Nat
| typ_true : type_of btrue Bool
| typ_false : type_of bfalse Bool
| typ_less : forall e1 e2,
    type_of e1 Nat ->
    type_of e2 Nat ->
    type_of (e1 <=' e2) Bool
| typ_not : forall b,
    type_of b Bool -> 
    type_of (bnot b) Bool
| typ_and : forall b1 b2,
    type_of b1 Bool ->
    type_of b2 Bool ->
    type_of (band b1 b2) Bool.

Inductive nat_value : Exp -> Prop :=
| nat_val : forall n, nat_value (anum n).

Inductive bool_value : Exp -> Prop :=
| b_true : bool_value btrue
| b_false : bool_value bfalse.

Definition value (e : Exp) := nat_value e \/ bool_value e.

Lemma bool_canonical :
  forall e,
    type_of e Bool ->
    value e ->
    bool_value e.
Proof.
  intros e H H'.
  inversion H'; trivial.
  inversion H0; subst; inversion H.
Qed.

Lemma nat_canonical :
  forall e,
    type_of e Nat ->
    value e ->
    nat_value e.
Proof.
  intros e H H'.
  inversion H'; trivial.
  inversion H0; subst; inversion H.
Qed.

Hint Constructors eval_exp.
Hint Constructors eval_exp_clos.
Hint Constructors nat_value.
Hint Constructors bool_value.
Hint Constructors type_of.


(* Progress *)
Theorem progress:
  forall e T st,
    type_of e T ->
    value e \/ exists e', e =[ st ]=> e'.
Proof.
  intros.
  induction H.
  - left. unfold value. left. eapply nat_val.
  - right. eexists. eauto.
  - destruct IHtype_of1 as [IH1 | IH2].
    + destruct IHtype_of2 as [IH3 | IH4].
      * inversion IH1.
        ** inversion IH3.
           *** inversion H1. inversion H2. subst.
               right. eexists. eapply add. eauto.
           *** inversion H2; subst; inversion H0.
        ** inversion H1; subst; inversion H.
      * right. destruct IH4 as [e IH4]. eexists.
        eapply add_2. eauto. eauto.
    + right.
      destruct IHtype_of2 as [IH3 | IH4].
      * destruct IH2 as [e' IH2].
        eexists. eapply add_1. eauto. eauto.
      * destruct IH2 as [e1' IH2].
        destruct IH4 as [e2' IH4].
        eexists. eapply add_1; eauto.
  - destruct IHtype_of1 as [IH1 | IH2].
    + destruct IHtype_of2 as [IH3 | IH4].
      * inversion IH1.
        ** inversion IH3.
           *** inversion H1. inversion H2. subst.
               right. eexists. eapply mul. eauto.
           *** inversion H2; subst; inversion H0.
        ** inversion H1; subst; inversion H.
      * right. destruct IH4 as [e IH4]. eexists.
        eapply mul_2. eauto. eauto.
    + right.
      destruct IHtype_of2 as [IH3 | IH4].
      * destruct IH2 as [e' IH2].
        eexists. eapply mul_1. eauto. eauto.
      * destruct IH2 as [e1' IH2].
        destruct IH4 as [e2' IH4].
        eexists. eapply mul_1; eauto.
  - left. unfold value. right. apply b_true.
  - left. unfold value. right. apply b_false.
  - destruct IHtype_of1 as [IH1 | IH2].
    + destruct IHtype_of2 as [IH3 | IH4].
      * inversion IH1.
        ** inversion IH3.
           *** inversion H1. inversion H2. subst.
               right. eexists. eapply lessthan. eauto.
           *** inversion H2; subst; inversion H0.
        ** inversion H1; subst; inversion H.
      * right. destruct IH4 as [e IH4]. eexists.
        unfold value in IH1.
        destruct IH1 as [IH1 | IH1].
        ** inversion IH1. subst. 
           eapply lessthan_1. eauto.
        ** inversion IH1; subst; inversion H.
    + right.
      destruct IHtype_of2 as [IH3 | IH4].
      * destruct IH2 as [e' IH2].
        eexists. eapply lessthan_1. eauto. 
      * destruct IH2 as [e1' IH2].
        destruct IH4 as [e2' IH4].
        eexists. eapply lessthan_1; eauto.
  - destruct IHtype_of as [IH | IH].
    + inversion IH.
      * inversion H0; subst; inversion H.
      * inversion H0; subst.
        ** right. eexists. eapply not_true.
        ** right. eexists. eapply not_false.
    + destruct IH as [e' IH].
      right. eexists. eapply not; eauto.
  - destruct IHtype_of1 as [IH1 | IH2].
    + destruct IHtype_of2 as [IH3 | IH4].
      * inversion IH1.
        ** inversion IH3.
           *** inversion H1. inversion H2. subst. inversion H.
           *** inversion H1. subst. inversion H.
        ** inversion IH3.
           *** inversion H2. subst. inversion H0.
           *** inversion H1; subst.
               **** inversion H2; subst; right; eexists; apply and_true.
               **** inversion H2; subst; right; eexists; apply and_false.
      * right. destruct IH4 as [e'  IH4].
        inversion IH1.
        ** inversion H1. subst. inversion H.
        ** inversion H1; subst; eexists.
           *** apply and_true.
           *** apply and_false.
    + destruct IHtype_of2 as [IH3 | IH4].
      * destruct IH2 as [e' IH2].
        inversion IH3; right; eexists; eapply and; eauto.
      * right.
        destruct IH2 as [e1' IH2].
        destruct IH4 as [e2' IH4].
        eexists.
        eapply and. eauto.
Qed.


(* Type preservation *)
Theorem preservation:
  forall e T e' st,
  type_of e T ->
  e =[ st ]=> e' ->
  type_of e' T.
Proof.
  intros.
  revert e' H0.
  induction H; intros e' H'; inversion H'; subst; eauto.
  case_eq (Nat.leb i1 i2); intros; eauto.
Qed. 

(* Soundness *)
Corollary soundness:
  forall e T e' st,
    type_of e T ->
    e =[ st ]>* e' ->
    value e' \/ exists e'',  e' =[ st ]=> e''.
Proof.
  intros.
  induction H0.
  - eapply progress; eauto.
  - eapply IHeval_exp_clos.
    eapply preservation; eauto.
Qed.
