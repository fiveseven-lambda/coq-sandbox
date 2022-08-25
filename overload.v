(* 変数名 x, y, z *)
Definition var := nat.
Definition eqb := Nat.eqb.

(* 型名 S, T *)
Inductive type :=
  | tyBool
  | tyFun : type -> type -> type.

(* 文脈 C *)
Definition context := var -> type -> Prop.
(* C, x1 : T1 *)
Definition append (C:context) x1 T1 x2 T2 := x1 = x2 /\ T1 = T2 \/ C x2 T2.
(* 空の文脈 *)
Definition empty_context:context := fun x T => False.

(* 値 u, v，項 s, t *)
Inductive term :=
  | tmVal : value -> term
  | tmIf : term -> term -> term -> term (* if t then t else t *)
  | tmVar : var -> term
  | tmApp : term -> term -> term (* t t *)
with value :=
  | vTrue | vFalse
  | vAbs : nat -> type -> term -> value  (* λx:T.t *).

Definition tmTrue := tmVal vTrue.
Definition tmFalse := tmVal vFalse.
Definition tmAbs x T t := tmVal (vAbs x T t).

(* C ⊢ t : T *)
Fixpoint is_type_candidate C t T {struct t} :=
  match t, T with
  | tmVal vTrue, tyBool => True
  | tmVal vFalse, tyBool => True
  | tmVal (vAbs x T1 t1), tyFun T2 T3 => T1 = T2 /\ is_type_candidate (append C x T1) t1 T3
  | tmIf t1 t2 t3, T1 => is_type_candidate C t1 tyBool /\ is_type_candidate C t2 T1 /\ is_type_candidate C t3 T1
  | tmVar x, T1 => C x T1
  | tmApp t1 t2, T1 => exists T2, is_type_candidate C t1 (tyFun T2 T1) /\ is_type_candidate C t2 T2
  | _, _ => False
  end.

Definition is_typed t T :=
  is_type_candidate empty_context t T
  /\ forall S, is_type_candidate empty_context t S -> S = T.

Example type_of_true : is_typed tmTrue tyBool.
Proof.
  split.
  - simpl.
    trivial.
  - destruct S.
    reflexivity.
    contradiction.
Qed.
Example type_of_false : is_typed tmFalse tyBool.
Proof.
  split.
  - simpl.
    trivial.
  - destruct S.
    reflexivity.
    contradiction.
Qed.

Goal
  let t := (tmAbs 0 tyBool (tmAbs 0 (tyFun tyBool tyBool) (tmApp (tmVar 0) (tmVar 0)))) in
  let T := (tyFun tyBool (tyFun (tyFun tyBool tyBool) tyBool)) in
  is_typed t T.
Proof.
  intros t T.
  assert (is_type_candidate empty_context t T). {
    split. reflexivity. split. reflexivity.
    exists tyBool. split.
    - left. split. reflexivity. reflexivity.
    - right. left. split. reflexivity. reflexivity.
  }
  split. exact H. destruct S.
  - contradiction.
  - destruct S2 as [| S21 S22].
    + intros [_ H0]. contradiction.
    + destruct S22.
      * intros [HS1 [HS21 _]].
        rewrite <-HS1, <-HS21.
        reflexivity.
      * intros [_[_[S22[[[_ HS221]|[[_ HS222]|HS223]] _]]]].
        discriminate. discriminate. contradiction.
Qed.