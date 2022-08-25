(* 変数名 x, y, z *)
Definition var := nat.
Definition eqb := Nat.eqb.

(* 型名 S, T *)
Inductive type :=
  | tyBool
  | tyFun : type -> type -> type.

(* 文脈 C *)
Definition context := var -> type -> Prop.

Definition append (C:context) x1 t1 x2 t2 := x1 = x2 /\ t1 = t2 \/ C x2 t2.
Definition empty_context:context := fun x t => False.

(* 値  u, v，項 s, t *)
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

(* [x -> v] t *)
Fixpoint substitute (t:term) (x:var) (v:value) :=
  match t with
  | tmVal (vAbs y T t') => tmAbs y T (if eqb x y then t' else substitute t' x v)
  | tmVal _ => t
  | tmIf t1 t2 t3 => tmIf (substitute t1 x v) (substitute t2 x v) (substitute t3 x v)
  | tmVar y => if eqb x y then tmVal v else tmVar y
  | tmApp t1 t2 => tmApp (substitute t1 x v) (substitute t2 x v)
  end.

Fixpoint evaluates_to s t :=
  match s, t with
  | tmIf (tmVal vTrue) s2 _, t => s2 = t
  | tmIf (tmVal vFalse) _ s3, t => s3 = t
  | tmIf s1 s2 s3, tmIf t1 t2 t3 => evaluates_to s1 t1 /\ s2 = t2 /\ s3 = t3
  | tmApp (tmVal (vAbs x T s1)) (tmVal v), t => t = substitute s1 x v
  | tmApp (tmVal (vAbs x T s1)) s2, tmApp t1 t2 => tmAbs x T s1 = t1 /\ evaluates_to s2 t2
  | tmApp s1 s2, tmApp t1 t2 => evaluates_to s1 t1 /\ s2 = t2
  | _, _ => False
  end.

Definition is_value t := match t with tmVal _ => True | _ => False end.
Definition is_normal s := forall t, ~ evaluates_to s t.

Theorem value_normal t : is_value t -> is_normal t.
Proof.
  destruct t.
  - intros _ t H. contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
Qed.

Goal ~ forall t, is_normal t -> is_value t.
Proof.
  intro.
  apply (H (tmIf (tmAbs 0 tyBool tmTrue) tmTrue tmTrue)).
  intros t H0. simpl in H0. destruct t. trivial. destruct H0. trivial. trivial. trivial.
Qed.

Theorem determinacy : forall s t t', evaluates_to s t /\ evaluates_to s t' -> t = t'.
Proof.
  induction s.
  - intros t t' [H _]. contradiction.
  - destruct s1.
    + destruct v.
      * intros t t' [H0 H1]. simpl in H0, H1. rewrite <- H0, H1. reflexivity.
      * intros t t' [H0 H1]. simpl in H0, H1. rewrite <- H0, H1. reflexivity.
      * intros t1 t' [H _]. simpl in H. destruct t1. contradiction. destruct H. contradiction. contradiction. contradiction.
    + intros t t' [H0 H1]. destruct t, t'.
      * contradiction. * contradiction. * contradiction. * contradiction. * contradiction.
      * destruct (IHs1 t1 t'1). split. apply H0. apply H1.
        destruct H0 as [_ [H00 H01]].
        destruct H1 as [_ [H10 H11]].
        rewrite <- H00, <- H01, <- H10, <- H11.
        reflexivity.
      * contradiction. * contradiction. * contradiction. * contradiction. * contradiction.
      * contradiction. * contradiction. * contradiction. * contradiction. * contradiction.
    + intros t t' [H0 H1]. destruct t, t'.
      * contradiction. * contradiction. * contradiction. * contradiction. * contradiction.
      * destruct H0. contradiction.
      * contradiction. * contradiction. * contradiction. * contradiction. * contradiction.
      * contradiction. * contradiction. * contradiction. * contradiction. * contradiction.
    + intros t t' [H0 H1]. destruct t, t'.
      * contradiction. * contradiction. * contradiction. * contradiction. * contradiction.
      * destruct (IHs1 t1 t'1). split. apply H0. apply H1.
        destruct H0 as [_ [H00 H01]].
        destruct H1 as [_ [H10 H11]].
        rewrite <- H00, <- H01, <- H10, <- H11.
        reflexivity.
      * contradiction. * contradiction. * contradiction. * contradiction. * contradiction.
      * contradiction. * contradiction. * contradiction. * contradiction. * contradiction.
  - intros t t' [H _]. contradiction.
  - destruct s1.
    + intros t t' [H0 H1]. destruct v.
      * destruct t, t'.
        -- contradiction. -- contradiction. 
        -- destruct s2.
          ++ contradiction. ++ contradiction. ++ contradiction. ++ contradiction.
        -- contradiction. -- contradiction. -- contradiction. -- contradiction. -- contradiction.
        -- contradiction. -- contradiction. -- contradiction. -- contradiction. -- contradiction.
        -- contradiction. -- contradiction.
        -- destruct H0. contradiction.
      * destruct t, t'.
        -- contradiction. -- contradiction. 
        -- destruct s2.
          ++ contradiction. ++ contradiction. ++ contradiction. ++ contradiction.
        -- contradiction. -- contradiction. -- contradiction. -- contradiction. -- contradiction.
        -- contradiction. -- contradiction. -- contradiction. -- contradiction. -- contradiction.
        -- contradiction. -- contradiction.
        -- destruct H0. contradiction.
      * destruct s2.
        -- simpl in H0, H1. rewrite H0, H1. reflexivity.
        -- destruct t, t'.
           ++ contradiction. ++ contradiction. ++ contradiction. ++ contradiction. ++ contradiction.
           ++ contradiction. ++ contradiction. ++ contradiction. ++ contradiction. ++ contradiction.
           ++ contradiction. ++ contradiction. ++ contradiction. ++ contradiction. ++ contradiction.
           ++ destruct (IHs2 t3 t'2). split. apply H0. apply H1.
              destruct H0 as [H00 _]. destruct H1 as [H10 _].
              rewrite <- H00, <- H10. reflexivity.
        -- destruct t, t'.
           ++ contradiction. ++ contradiction. ++ contradiction. ++ contradiction. ++ contradiction.
           ++ contradiction. ++ contradiction. ++ contradiction. ++ contradiction. ++ contradiction.
           ++ contradiction. ++ contradiction. ++ contradiction. ++ contradiction. ++ contradiction.
           ++ destruct H0. contradiction.
        -- destruct t, t'.
           ++ contradiction. ++ contradiction. ++ contradiction. ++ contradiction. ++ contradiction.
           ++ contradiction. ++ contradiction. ++ contradiction. ++ contradiction. ++ contradiction.
           ++ contradiction. ++ contradiction. ++ contradiction. ++ contradiction. ++ contradiction.
           ++ destruct (IHs2 t3 t'2). split. apply H0. apply H1.
              destruct H0 as [H00 _]. destruct H1 as [H10 _].
              rewrite <- H00, <- H10. reflexivity.
    + intros t t' [H0 H1]. destruct t, t'.
      * contradiction. * contradiction. * contradiction. * contradiction. * contradiction.
      * contradiction. * contradiction. * contradiction. * contradiction. * contradiction.
      * contradiction. * contradiction. * contradiction. * contradiction. * contradiction.
      * destruct (IHs1 t1 t'1). split. apply H0. apply H1.
        destruct H0 as [_ H01]. destruct H1 as [_ H11].
        rewrite <- H01, <- H11. reflexivity.
    + intros t t' [H _]. destruct t.
      * contradiction. * contradiction. * contradiction.
      * destruct H. contradiction.
    + intros t t'[H0 H1]. destruct t, t'.
      * contradiction. * contradiction. * contradiction. * contradiction. * contradiction.
      * contradiction. * contradiction. * contradiction. * contradiction. * contradiction.
      * contradiction. * contradiction. * contradiction. * contradiction. * contradiction.
      * destruct (IHs1 t1 t'1). split. apply H0. apply H1.
        destruct H0 as [_ H01]. destruct H1 as [_ H11].
        rewrite <- H01, <- H11. reflexivity.
Qed.