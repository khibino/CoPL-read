Require Import Relations.
Require Import Logic.

Inductive Plus : nat -> nat -> nat -> Prop :=
| P_Zero : forall {n}, Plus 0 n n
| P_Succ : forall {n1 n2 n3},
             Plus n1 n2 n3 ->
             Plus (S n1) n2 (S n3)
.

Check Plus_ind.

(* 2.1 (1) *)
Lemma plusIdLeft : forall n, Plus 0 n n.
Proof.
  intro n.
  exact P_Zero.
Qed.

Print plusIdLeft.

(* 2.1 (2) *)
Lemma plusIdRight : forall {n}, Plus n 0 n.
Proof.
  induction n as [ | n' IHn ].

  (* n = 0 *)
  exact P_Zero.

  (* n = S n' *)
  apply P_Succ.
  exact IHn.
Qed.

Print plusIdRight.

Lemma foo :
  forall n1 n2,
    Plus 0 n1 n2 ->
    n1 = n2.
Proof.
  intros n1 n2 H.

  inversion H as [ n | ].
  reflexivity.
Qed.

Print foo.

Print False_ind.
Print False_rect.

(* 2.2 *)
Lemma plusUnique :
  forall n1 n2 n3 n4,
    Plus n1 n2 n3 ->
    Plus n1 n2 n4 ->
    n3 = n4.
Proof.
  intros n1 n2 n3 n4 PX.
  generalize dependent n4.
  induction PX as [ n | n1 n2 n3 PP IHPX ]
  ; intros n4 PY.

    (* PX is P_Zero *)
    inversion PY; reflexivity.

    (* PX is P_Succ *)
    destruct n4 as [ | n4'].

      (* n4 = 0 *)
      inversion PY.

      (* n4 = S n4' *)
      inversion PY; subst.
      apply (f_equal S).
      apply IHPX.
      exact H2.
Qed.

(* 2.2 x *)
(*
Lemma plusUnique' :
  forall n1 n2 n3 n4,
    Plus n1 n2 n3 ->
    Plus n1 n2 n4 ->
    n3 = n4.
Proof.
  intros n1 n2.

  induction n3 as [ | n3' ].

    (* n3 = 0 *)
    intros n4 PX PY.
    inversion PX; subst.
    inversion PY; subst.
    reflexivity.

    (* n3 = S n3' *)
    intros n4 PX PY.

    destruct n4 as [ | n4' ].

      (* n4 = 0 *)
      inversion PY; subst. inversion PX.

      (* n4 = S n4' *)
      destruct n1 as [ | n1' ].

        (* n1 = 0 *)
        inversion PX; subst.
        inversion PY; subst.
        reflexivity.

        (* n1 = S n1' *)
        inversion PX; subst.
        inversion PY; subst.
        reflexivity.

      inversion PX; subst.


Qed.
*)

Print ex.

Lemma plusExist' :
  forall n1 n2, (ex (fun n3 => Plus n1 n2 n3)).

(* 2.3 *)
Lemma plusExist :
  forall n1 n2, exists n3, Plus n1 n2 n3.
Proof.
  intros n1 n2.
  induction n1 as [ | n1' IHn1 ].

    (* n1 = 0 *)
    exists n2. exact P_Zero.

    (* n1 = S n1' *)
    destruct IHn1 as [ n3' P123 ].
    exists (S n3').
    exact (P_Succ P123).
Qed.

Lemma plusSuccR :
  forall {n1 n2 n3},
    Plus n1 n2 n3 ->
    Plus n1 (S n2) (S n3).
Proof.
  intros n1 n2 n3 H.
  induction H as [ n | n1 n2 n3 PH IHH ].

    (* H is P_Zero *)
    exact P_Zero.

    (* H is P_Succ *)
    apply P_Succ.
    exact IHH.
Qed.

(* 2.4 *)
Lemma plusCommutative :
  forall n1 n2 n3,
    Plus n1 n2 n3 -> Plus n2 n1 n3.
Proof.
  intros n1 n2 n3 LH.

  induction LH as [ n | n1 n2 n3 PH IHLH ].

  (* LH is P_Zero *)
  exact plusIdRight.

  (* LH is P_Succ *)
  apply plusSuccR.
  exact IHLH.
Qed.


(* 2.5 *)
Lemma plusAssociative :
  forall n1 n2 n3 n4 n5,
    Plus n1 n2 n4 ->
    Plus n4 n3 n5 ->
    exists n6, Plus n2 n3 n6 /\ Plus n1 n6 n5.
Proof.
  intros n1 n2 n3 n4 n5 LH.
  generalize dependent n5.
  generalize dependent n3.

  induction LH as [ n2' | n1' n2' n4' LPP IHLH ]
  ; intros n3 n5 RH.

    (* LH is P_Zero *)
    exists n5.
    split.
    exact RH.
    exact P_Zero.

    (* LH is P_Succ *)
    destruct n5 as [ | n5' ].

      (* n5 = 0 *)
      inversion RH.

      (* n5 = S n5' *)
      inversion RH; subst.
      destruct (IHLH n3 n5' H2) as [ n6x [ IHL IHR ] ].
      exists n6x. split.
      exact IHL.
      apply P_Succ; exact IHR.
Qed.

Lemma plusIdRightEq :
  forall {n1 n3}, Plus n1 0 n3 -> n1 = n3.
Proof.
  intros n1 n3 PH.
  generalize dependent n3.

  induction n1 as [ | n1' ]
  ; intros n3 PH.

    (* n1 = 0 *)
    inversion PH; subst.
    reflexivity.

    (* n1 = S n1' *)
    destruct n3 as [ | n3' ].

      (* n3 = 0 *)
      inversion PH.

      (* n3 = S n3' *)
      apply (f_equal S).
      apply IHn1'.
      inversion PH; subst.
      exact H2.
Qed.


Inductive Times : nat -> nat -> nat -> Prop :=
| T_Zero : forall n, Times 0 n 0
| T_Succ : forall n1 n2 n3 n4,
             Times n1 n2 n3 ->
             Plus  n2 n3 n4 ->
             Times (S n1) n2 n4
.

(* n1 * n2 = n3 *)
(* n2 + n3 = n4 *)
(* (1 + n1) * n2 = n4 *)

Check Times_ind.

(* 2.6 *)
Lemma timesUnique :
  forall n1 n2 n3 n4,
    Times n1 n2 n3 ->
    Times n1 n2 n4 ->
    n3 = n4.
Proof.
  induction n1 as [ | n1' IHn1 ]
  ; intros n2 n3 n4 TX TY
  ; inversion TX; inversion TY; subst.

    (* n1 = 0 *)
    reflexivity.

    (* n1 = S n1' *)
    assert (n5 = n9) as E.
    apply (IHn1 n2); assumption.
    rewrite <- E in H6.
    apply (plusUnique n2 n5 n3 n4); assumption.
Qed.

(* 2.7 *)
Lemma timesExist :
  forall n1 n2, exists n3, Times n1 n2 n3.
Proof.
  intros n1 n2.
  induction n1 as [ | n1' IHn1 ].

    (* n1 = 0 *)
    exists 0. exact (T_Zero n2).

    (* n1 = S n1' *)
    destruct IHn1 as [ n4 ].
    destruct (plusExist n2 n4) as [ n3' ].
    exists n3'.
    apply (T_Succ n1' n2 n4); assumption.
Qed.

(* 2.8 *)
Lemma timesZeroLeft : forall n, Times 0 n 0.
Proof. exact T_Zero. Qed.

(* 2.9 *)
Lemma timesZeroRight : forall n, Times n 0 0.
Proof.
  induction n as [ | n' IHn ].

    (* n = 0 *)
    exact (T_Zero 0).

    (* n = S n' *)
    apply (T_Succ n' 0 0).
    assumption.
    exact P_Zero.
Qed.

Lemma timesZeroLeft': forall n1 n2, Times 0 n1 n2 -> n2 = 0.
Proof.
  intros n1 n2 TH.
  exact (timesUnique 0 n1 n2 0 TH (timesZeroLeft n1)).
Qed.

Lemma timesZeroRight': forall n1 n2, Times n1 0 n2 -> n2 = 0.
Proof.
  intros n1 n2 TH.
  exact (timesUnique n1 0 n2 0 TH (timesZeroRight n1)).
Qed.

Lemma plusTimesDistRight :
  forall n1 n2 n12 n3 n45,
    Plus n1 n2 n12 ->
    Times n12 n3 n45 ->
    exists n4 n5, Times n1 n3 n4 /\ Times n2 n3 n5 /\ Plus n4 n5 n45.
Proof.
  intros n1 n2 n12 n3 n45 PH TH.
  destruct (timesExist n1 n3) as [ n4' T4 ].
  destruct (timesExist n2 n3) as [ n5' T5 ].
  exists n4'; exists n5'.

  split. assumption.
  split. assumption.

  generalize dependent n2.
  generalize dependent n1.

  induction n3 as [ | n3' ].

    intros n1 T4 n2 PH T5.

      (* n3 = 0 *)
      rewrite -> (timesZeroRight' n12 n45 TH).
      rewrite -> (timesZeroRight' n1 n4' T4 ).
      rewrite -> (timesZeroRight' n2 n5' T5).
      exact P_Zero.

      (* n3 = S n3' *)
      intros n1 T4 n2 PH T5.

  inversion TH; subst.
Admitted.

(*
 *)

SearchAbout nat.

(* 2.10 *)
Lemma timesAssociative :
  forall n1 n2 n3 n4 n5,
    Times n1 n2 n4 ->
    Times n4 n3 n5 ->
    exists n6, Times n2 n3 n6 /\ Times n1 n6 n5.
Proof.
  induction n1 as [ | n1' IHn1 ]
  ; intros n2 n3 n4 n5 LH RH
  ; destruct (timesExist n2 n3) as [ n6' TH23 ]; exists n6'.

    (* n1 = 0 *)
    inversion LH; subst.
    inversion RH; subst.
    split ; [ assumption | exact (T_Zero n6') ].

    (* n1 = S n1' *)
    split.
    assumption.


    destruct (timesExist n1' n2) as [ n4' TH12' ].
    destruct (timesExist n4' n3) as [ n5' TH43' ].
    destruct (IHn1 n2 n3 n4' n5' TH12' TH43') as [ n6'' [TH23' TH16'] ].

    assert (n6'' = n6') as E6.
    exact (timesUnique n2 n3 n6'' n6' TH23' TH23).
    subst.

    destruct (plusExist n6' n5') as [ n5'' PH65' ].
    assert (Times (S n1') n6' n5'') as T.
    exact (T_Succ n1' n6' n5' n5'' TH16' PH65').

Admitted.

(*
    assert (n5'' = n5) as E5.
    exact (timesUnique (S n1') n3 n6'' n6' TH23' TH23).


Check (T_Succ n1' n6' n5' n5'' TH16' PH65').

     (T_Succ n1' n6' n5' n5'' TH16' PH65').


  intros n1 n2 n3 n4 n5 LH.
  generalize dependent n5.
  generalize dependent n3.

  induction LH as [ n2' | n1' n2' n4' n7 LT' IHLT' LP ]
  ; subst; intros n3 n5 RH
  ; destruct (timesExist n2' n3) as [ n6' TH23 ]; exists n6'.

    (* LH is T_Zero *)
    inversion RH; subst.
    split; [ assumption | exact (T_Zero n6') ].

    (* LH is T_Succ *)
    split.
    assumption.
    destruct (timesExist n1' n6') as [ n5' TH123 ].
    apply (T_Succ n1' n6' n5').
    assumption.
 *)




    (* n1' * n2' = n4' *)
    (* n2' + n4' = n7 *)
    (* n2' + n1' * n2' = n7 *)

    (* S n1' * n2' = n7 *)

(*
 *)

(*
Print or.

Inductive Either (A {B} : Type :=
| Left  : A -> Either A B
| Right : B -> Either A B
.
 *)

(*
Lemma solvePlus :
  forall n1 n2 n3 : nat,
    plusJudge n1 n2 n3  \/ ~ plusJudge n1 n2 n3.
Proof.
 *)

Inductive NatExp : Set :=
| NE_Value  : nat -> NatExp
| NE_Plus   : NatExp -> NatExp -> NatExp
| NE_Times  : NatExp -> NatExp -> NatExp
.

Eval simpl in (NE_Value 3).

Eval simpl in (NE_Plus (NE_Value 1) (NE_Value 2)).
Eval simpl in (1 + 2).

Fixpoint evalNat e : nat :=
  match e with
    | NE_Value n      =>  n
    | NE_Plus  e1 e2  =>  evalNat e1 + evalNat e2
    | NE_Times e1 e2  =>  evalNat e1 * evalNat e2
  end.

Print evalNat.

(*
O   + n = n
S n + m = S (n + m)
 *)

Lemma plusCoq :
  forall n1 n2 n3,
    n1 + n2 = n3 <-> Plus n1 n2 n3.
Proof.
  intros n1 n2 n3.
  generalize dependent n3.
  generalize dependent n2.

  induction n1 as [ | n1' IHn1 ].

  split.
  intros H. simpl in H. rewrite <- H.
  exact P_Zero.

  intros H. inversion H; subst. reflexivity.

  destruct n3 as [ | n3' ].

  split.
  intros H. simpl in H.
Admitted.


Lemma timesCoq :
  forall n1 n2 n3,
    n1 * n2 = n3 <-> Times n1 n2 n3.
  Admitted.

Inductive EvalNatExp : NatExp -> nat -> Prop :=
| E_Const : forall n, EvalNatExp (NE_Value n) n
| E_Plus  : forall e1 n1 e2 n2 n,
              EvalNatExp e1 n1 ->
              EvalNatExp e2 n2 ->
              Plus n1 n2 n ->
              EvalNatExp (NE_Plus e1 e2) n
| E_Times : forall e1 n1 e2 n2 n,
              EvalNatExp e1 n1 ->
              EvalNatExp e2 n2 ->
              Times n1 n2 n ->
              EvalNatExp (NE_Times e1 e2) n
.

Notation "e '||' n" := (EvalNatExp e n) (at level 50, left associativity).

(* 2.15 *)
Lemma evalNatExpExists :
  forall e, exists n, e || n.
Proof.
  induction e as [ n | e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2 ].
    (* NE_Value *)  exists n. exact (E_Const n).

    (* NE_Plus *)
    destruct IHe1 as [ n1 EH1 ].
    destruct IHe2 as [ n2 EH2 ].
    destruct (plusExist n1 n2) as [n PH].
    exists n. apply E_Plus with (n1 := n1) (n2 := n2); assumption.
      (* exact (E_Plus e1 n1 e2 n2 n EH1 EH2 PH). *)

    (* NE_Times *)
    destruct IHe1 as [ n1 EH1 ].
    destruct IHe2 as [ n2 EH2 ].
    destruct (timesExist n1 n2) as [n TH].
    exists n. apply E_Times with (n1 := n1) (n2 := n2); assumption.
Qed.

(* 2.16 *)
Lemma natExpPlusUnique :
  forall e n1 n2,
    e || n1 -> e || n2 -> n1 = n2.
Proof.
  intros e n1 n2 E1.
  generalize dependent n2.
  induction E1 as
      [
      | eL nL eR nR n EL IHE1_L ER IHE1_R PH
      | eL nL eR nR n EL IHE1_L ER IHE1_R TH ]
  ; [ (* NE_Value *)
      intros n2 E2
      ; inversion E2; subst
      ; reflexivity
    | | ].

    (* NE_Plus *)
    intros n12 EP.
    inversion EP as [ | eL' nL' eR' nR' n' EL' ER' PH' | ]; subst.
    rewrite <- (IHE1_L nL' EL') in PH'.
    rewrite <- (IHE1_R nR' ER') in PH'.

    apply (plusUnique nL nR); assumption.

    (* NE_Times *)
    intros n12 ET.
    inversion ET as [ | | eL' nL' eR' nR' n' EL' ER' TH' ]; subst.
    rewrite <- (IHE1_L nL' EL') in TH'.
    rewrite <- (IHE1_R nR' ER') in TH'.

    apply (timesUnique nL nR); assumption.
Qed.

Reserved Notation "e '==>' v" (at level 71, left associativity).

Inductive ReduceNatExp : NatExp -> NatExp -> Prop :=
| R_Plus  : forall n1 n2 n3,
              Plus n1 n2 n3 ->
              NE_Plus (NE_Value n1) (NE_Value n2) ==> NE_Value n3
| R_Times : forall n1 n2 n3,
              Times n1 n2 n3 ->
              NE_Times (NE_Value n1) (NE_Value n2) ==> NE_Value n3
| R_PlusL : forall e1 e1' e2,
              e1 ==> e1' ->
              NE_Plus e1 e2 ==> NE_Plus e1' e2
| R_PlusR : forall e1 e2 e2',
              e2 ==> e2' ->
              NE_Plus e1 e2 ==> NE_Plus e1 e2'
| R_TimesL : forall e1 e1' e2,
               e1 ==> e1' ->
               NE_Times e1 e2 ==> NE_Times e1' e2
| R_TimesR : forall e1 e2 e2',
               e2 ==> e2' ->
               NE_Times e1 e2 ==> NE_Times e1 e2'
 where "e '==>' v" := (ReduceNatExp e v)
.

Print relation.

(* 2.21 *)
Theorem reduceNatProgressive :
  forall e, exists e', e ==> e' \/ exists n, e = NE_Value n.
Proof.
  (* induction e as [  ]. *)
  Admitted.

Definition normalForm {X:Type} (R:relation X) (t:X) : Prop :=
  ~ exists t', R t t'.

Theorem neValueNormalForm :
  forall n, normalForm ReduceNatExp (NE_Value n).
Proof.
  intros n N.
  inversion N.
  inversion H.
Qed.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  inversion contra. Qed.

(* 2.22 *)
Theorem reduceNatConfluence :
  forall e1 e2 e3,
    e1 ==> e2 ->
    ~ normalForm ReduceNatExp e2 ->
    e1 ==> e3 ->
    ~ normalForm ReduceNatExp e3 ->
    exists e4, e2 ==> e4 /\ e3 ==> e4.
Proof.
  intros e1 e2 e3 R2 N2 R3 N3.
  induction R2 as
      [ (* R_Plus *)
      | (* R_Times *)
      | ie1 ie1' ie2  RL (* R_PlusL *)
      |
      |
      |
      ].

  (* R_Plus *)
  apply ex_falso_quodlibet.
  apply N2.
  exact (neValueNormalForm n3).

  (* R_Times *)
  apply ex_falso_quodlibet.
  apply N2.
  exact (neValueNormalForm n3).

  (* R_PlusL *)
  (* e2 = ie1' + ie2 *)

Admitted.

Reserved Notation "e '==>*' v" (at level 81, left associativity).

Inductive NatExpMR : NatExp -> NatExp -> Prop :=
| MR_Zero : forall e, e ==>* e
| MR_One  : forall e e', e ==> e' -> e ==>* e'
| MR_Multi : forall e e' e'',
               e ==>* e'   ->
               e' ==>* e'' ->
               e ==>* e''
 where "e1 '==>*' e2" := (NatExpMR e1 e2)
.

(* 2.28 *)
Theorem natExpReduceEval :
  forall e n, e ==>* NE_Value n -> e || n.
Proof.
  intros e n RH.
  inversion RH; subst.

  (* MR_Zero *)
  exact (E_Const n).

  (* MR_One *)
  inversion H; subst.

    (* R_Plus *)
    apply E_Plus with (n1 := n1) (n2 := n2) .
    exact (E_Const n1).
    exact (E_Const n2).
    assumption.

    (* R_Times *)
    apply E_Times with (n1 := n1) (n2 := n2) .
    exact (E_Const n1).
    exact (E_Const n2).
    assumption.

  (* MR_Multi *)
  inversion H0; subst.

    inversion e'; subst.

  induction e' as [ n' | e1 e2 IHe' | e1 e2 IHe' ].
