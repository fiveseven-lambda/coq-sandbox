Inductive term :=
  | true_t | false_t
  | if_t : term -> term -> term -> term.

Definition is_value t :=
  match t with
  | true_t | false_t => True
  | _ => False
  end.

Fixpoint evaluates_to t t' :=
  match t, t' with
  | if_t true_t t2 _, t2' => t2 = t2'
  | if_t false_t _ t3, t3' => t3 = t3'
  | if_t t1 t2 t3, if_t t1' t2' t3' => t2 = t2' /\ t3 = t3' /\ evaluates_to t1 t1'
  | _, _ => False
  end.

Definition is_normal t := forall t', ~ evaluates_to t t'.

Theorem if_if_evaluates t1 t1' t2 t3 : evaluates_to t1 t1' -> evaluates_to (if_t t1 t2 t3) (if_t t1' t2 t3).
Proof.
  destruct t1.
  - simpl.
    intro. contradiction.
  - simpl.
    intro. contradiction.
  - intro.
    simpl.
    split.
    + reflexivity.
    + split.
      * reflexivity.
      * exact H.
Qed.

Theorem if_evaluates: forall t1 t2 t3, exists t', evaluates_to (if_t t1 t2 t3) t'.
Proof.
  intro t1.
  induction t1.
  - intros. exists t2. reflexivity.
  - intros. exists t3. reflexivity.
  - destruct (IHt1_1 t1_2 t1_3).
    intros.
    exists (if_t x t2 t3).
    apply if_if_evaluates.
    exact H.
Qed.

Theorem if_is_not_normal t1 t2 t3 : ~ is_normal (if_t t1 t2 t3).
Proof.
  intro.
  unfold is_normal in H.
  destruct (if_evaluates t1 t2 t3).
  destruct (H x).
  exact H0.
Qed.

Theorem value_normal t : is_value t <-> is_normal t.
Proof.
  split.
  - destruct t.
    + intro. intro. intro. contradiction.
    + intro. intro. intro. contradiction.
    + intro. contradiction.
  - destruct t.
    + intro. unfold is_value. trivial.
    + intro. unfold is_value. trivial.
    + apply if_is_not_normal.
Qed.