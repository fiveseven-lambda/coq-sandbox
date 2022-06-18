Inductive term :=
  | true_t | false_t
  | if_t : term -> term -> term -> term
  | zero_t
  | succ_t : term -> term
  | pred_t : term -> term
  | iszero_t : term -> term.

Fixpoint is_numeric_value t :=
  match t with
  | zero_t => True
  | succ_t t1 => is_numeric_value t1
  | _ => False
  end.

Definition is_value t :=
  match t with
  | true_t | false_t => True
  | _ => is_numeric_value t
  end.

Variant type := Bool | Nat.

Fixpoint evaluates_to t t' :=
  match t, t' with
  | if_t true_t t2 _, t2' => t2 = t2'
  | if_t false_t _ t3, t3' => t3 = t3'
  | if_t t1 t2 t3, if_t t1' t2' t3' => evaluates_to t1 t1' /\ t2 = t2' /\ t3 = t3'
  | succ_t t1, succ_t t1' => evaluates_to t1 t1'
  | pred_t zero_t, zero_t => True
  | pred_t (succ_t t1), t1' => t1 = t1'
  | pred_t t1, pred_t t1' => evaluates_to t1 t1'
  | iszero_t zero_t, true_t => True
  | iszero_t (succ_t t1), false_t => True
  | iszero_t t1, iszero_t t1' => evaluates_to t1 t1'
  | _, _ => False
  end.

Fixpoint is_typed t T :=
  match t, T with
  | true_t, Bool | false_t, Bool => True
  | if_t t1 t2 t3, T1 => is_typed t1 Bool /\ is_typed t2 T1 /\ is_typed t3 T1
  | zero_t, Nat => True
  | succ_t t1, Nat | pred_t t1, Nat | iszero_t t1, Bool => is_typed t1 Nat
  | _, _ => False
  end.

Lemma inv_true T: is_typed true_t T -> T = Bool.
Proof.
  simpl.
  destruct T.
  reflexivity.
  contradiction.
Qed.

Lemma inv_false T: is_typed false_t T -> T = Bool.
Proof.
  simpl.
  destruct T.
  reflexivity.
  contradiction.
Qed.

Lemma inv_if t1 t2 t3 T: is_typed (if_t t1 t2 t3) T -> is_typed t1 Bool /\ is_typed t2 T /\ is_typed t3 T.
Proof. trivial. Qed.

Lemma inv_zero T: is_typed zero_t T -> T = Nat.
Proof.
  simpl.
  destruct T.
  contradiction.
  reflexivity.
Qed.

Lemma inv_succ t1 T: is_typed (succ_t t1) T -> T = Nat /\ is_typed t1 Nat.
Proof.
  simpl.
  destruct T.
  - contradiction.
  - split.
    + reflexivity.
    + exact H.
Qed.

Lemma inv_pred t1 T: is_typed (pred_t t1) T -> T = Nat /\ is_typed t1 Nat.
Proof.
  simpl.
  destruct T.
  - contradiction.
  - split.
    + reflexivity.
    + exact H.
Qed.

Lemma inv_iszero t1 T: is_typed (iszero_t t1) T -> T = Bool /\ is_typed t1 Nat.
Proof.
  simpl.
  destruct T.
  - split.
    + reflexivity.
    + exact H.
  - contradiction.
Qed.

Theorem uniqueness t T1 T2: is_typed t T1 /\ is_typed t T2 -> T1 = T2.
Proof.
  induction t.
  - intros [H1 H2].
    apply inv_true in H1, H2.
    rewrite H1, H2.
    reflexivity.
  - intros [H1 H2].
    apply inv_false in H1, H2.
    rewrite H1, H2.
    reflexivity.
  - intros [H1 H2].
    apply inv_if in H1, H2.
    apply IHt2.
    split.
    + apply H1.
    + apply H2.
  - intros [H1 H2].
    apply inv_zero in H1, H2.
    rewrite H1, H2.
    reflexivity.
  - intros [H1 H2].
    apply inv_succ in H1, H2.
    destruct H1 as [H1 _].
    destruct H2 as [H2 _].
    rewrite H1, H2.
    reflexivity.
  - intros [H1 H2].
    apply inv_pred in H1, H2.
    destruct H1 as [H1 _].
    destruct H2 as [H2 _].
    rewrite H1, H2.
    reflexivity.
  - intros [H1 H2].
    apply inv_iszero in H1, H2.
    destruct H1 as [H1 _].
    destruct H2 as [H2 _].
    rewrite H1, H2.
    reflexivity.
Qed.