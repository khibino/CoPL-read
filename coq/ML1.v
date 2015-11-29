(* Close Scope nat_scope. *)

Require Import ZArith.

(* SearchAbout "int". *)
(* Import Z_as_Int. *)
(* Import Int. *)

Open Scope Z_scope.

Definition int := Z.

Check (fun x y => x + y).

Inductive Value : Set :=
| V_Int  : int  -> Value
| V_Bool : bool -> Value
.

Inductive Prim : Set :=
| P_Plus
| P_Minus
| P_Times
| P_LT
.

Inductive Exp : Set :=
| EX_Int  : int  -> Exp
| EX_Bool : bool -> Exp
| EX_Prim : Prim -> Exp -> Exp -> Exp
| EX_If   : Exp -> Exp -> Exp -> Exp
.

Print Exp_ind.


Inductive Plus : Value -> Value -> Value -> Prop :=
| B_Plus  : forall i1 i2 i3 : int,
              i1 + i2 = i3 -> Plus (V_Int i1) (V_Int i2) (V_Int i3).

Notation "i1 'plus' i2 'is' i3" :=
  (Plus i1 i2 i3) (at level 31, left associativity).

Inductive Minus : Value -> Value -> Value -> Prop :=
| B_Minus : forall i1 i2 i3 : int,
              i1 - i2 = i3 -> Minus (V_Int i1) (V_Int i2) (V_Int i3).

Notation "i1 'minus' i2 'is' i3" :=
  (Minus i1 i2 i3) (at level 31, left associativity).

Inductive Times : Value -> Value -> Value -> Prop :=
| B_Times : forall i1 i2 i3 : int,
              i1 * i2 = i3 -> Times (V_Int i1) (V_Int i2) (V_Int i3).

Notation "i1 'times' i2 'is' i3" :=
  (Times i1 i2 i3) (at level 31, left associativity).

Check Z.compare.
Print comparison.

Definition Zlt x y :=
  match Z.compare x y with
    | Lt => true
    | Eq => false
    | Gt => false
  end.

Inductive LT : Value -> Value -> Value -> Prop :=
| B_LT : forall (i1 i2 : int) (b : bool),
           (Zlt i1 i2) = b -> LT (V_Int i1) (V_Int i2) (V_Bool b).

Notation "i1 'less' 'than' i2 'is' b3" :=
  (LT i1 i2 b3) (at level 31, left associativity).

(* Inductive LT : Value -> *)

Infix "+!" := (EX_Prim P_Plus) (at level 51, left associativity).

Infix "-!" := (EX_Prim P_Minus) (at level 51, left associativity).

Infix "*!" := (EX_Prim P_Times) (at level 41, left associativity).

Infix "<!" := (EX_Prim P_LT) (at level 61, left associativity).

Reserved Notation "e '||!' v" (at level 71, left associativity).

Inductive Eval1 : Exp -> Value -> Prop :=
| E_Int   : forall i, EX_Int i ||! V_Int i
| E_Bool  : forall b, EX_Bool b ||! V_Bool b
| E_IfT   : forall e1 e2 e3 v,
              e1 ||! V_Bool true ->
              e2 ||! v ->
              EX_If e1 e2 e3 ||! v
| E_IfF   : forall e1 e2 e3 v,
              e1 ||! V_Bool false ->
              e3 ||! v ->
              EX_If e1 e2 e3 ||! v
| E_Plus  : forall e1 e2 i1 i2 i3,
              e1 ||! i1 ->
              e2 ||! i2 ->
              i1 plus i2 is i3 ->
              e1 +! e2 ||! i3
| E_Minus : forall e1 e2 i1 i2 i3,
              e1 ||! i1 ->
              e2 ||! i2 ->
              i1 minus i2 is i3 ->
              e1 -! e2 ||! i3
| E_Times : forall e1 e2 i1 i2 i3,
              e1 ||! i1 ->
              e2 ||! i2 ->
              i1 times i2 is i3 ->
              e1 *! e2 ||! i3
| E_LT    : forall e1 e2 i1 i2 b3,
              e1 ||! i1 ->
              e2 ||! i2 ->
              i1 less than i2 is b3 ->
              e1 <! e2 ||! b3
where "e '||!' v" := (Eval1 e v)
.

(* 3.2 *)
Lemma eval1Unique :
  forall e v1 v2, e ||! v1 -> e ||! v2 -> v1 = v2.
Proof.
  induction e as [ i | b | p e1 IHe1 e2 IHe2 | eP IHeP eT IHeT eE IHeE ]
  ; intros v1 v2 E1 E2.

    (* EX_Int *)
    inversion E1; subst.
    inversion E2; subst.
    reflexivity.

    (* EX_Bool *)
    inversion E1; subst.
    inversion E2; subst.
    reflexivity.

    (* EX_Prim *)
    destruct p

    ; inversion E1 as [ | | |
                        | e1e1 e1e2 e1i1 e1i2 e1v e1E1H e1E2H e1BH
                        | e1e1 e1e2 e1i1 e1i2 e1v e1E1H e1E2H e1BH
                        | e1e1 e1e2 e1i1 e1i2 e1v e1E1H e1E2H e1BH
                        | e1e1 e1e2 e1i1 e1i2 e1v e1E1H e1E2H e1BH
                      ]
    ; subst
    ; inversion E2 as [ | | |
                        | e2e1 e2e2 e2i1 e2i2 e2v1 e2E1H e2E2H e2BH (* EX_Plus *)
                        | e2e1 e2e2 e2i1 e2i2 e2v1 e2E1H e2E2H e2BH (* EX_Minus *)
                        | e2e1 e2e2 e2i1 e2i2 e2v1 e2E1H e2E2H e2BH (* EX_Times *)
                        | e2e1 e2e2 e2i1 e2i2 e2v1 e2E1H e2E2H e2BH (* EX_LT *)
                      ]
    ; subst

    ; rewrite <- (IHe1 e1i1 e2i1 e1E1H e2E1H) in e2BH
    ; rewrite <- (IHe2 e1i2 e2i2 e1E2H e2E2H) in e2BH
    ; inversion e1BH; subst
    ; inversion e2BH; subst
    ; reflexivity.

    (* EX_If *)
    inversion E1 as [ |
                      | e1e1 e1e2 e1e3 e1v e1PH e1H
                      | e1e1 e1e2 e1e3 e1v e1PH e1H
                      | | | | ]
    ; subst
    ; inversion E2 as [ |
                        | e2e1 e2e2 e2e3 e2v e2PH e2H
                        | e2e1 e2e2 e2e3 e2v e2PH e2H
                        | | | | ]; subst.

    exact (IHeT v1 v2 e1H e2H).

    assert (V_Bool true = V_Bool false) as N by
          exact (IHeP (V_Bool true) (V_Bool false) e1PH e2PH)
    ; inversion N.

    assert (V_Bool false = V_Bool true) as N by
          exact (IHeP (V_Bool false) (V_Bool true) e1PH e2PH)
    ; inversion N.

    exact (IHeE v1 v2 e1H e2H).
Qed.
