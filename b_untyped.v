Inductive term : Set :=
  | true_t : term
  | false_t : term
  | if_t : term -> term -> term -> term.

Definition is_value (t:term) : Prop :=
  match t with
  | true_t | false_t => True
  | _ => False
  end.

Fixpoint evaluates_to (t t':term) : Prop :=
  match t, t' with
  | if_t true_t t2 _, t2' => t2 = t2'
  | if_t false_t _ t3, t3' => t3 = t3'
  | if_t t1 t2 t3, if_t t1' t2' t3' => t2 = t2' /\ t3 = t3' /\ evaluates_to t1 t1'
  | _, _ => False
  end.

Example ex1: evaluates_to (if_t true_t false_t true_t) false_t.
Proof. simpl. reflexivity. Qed.

Example ex2: ~ evaluates_to (if_t true_t false_t true_t) true_t.
Proof. simpl. congruence. Qed.

Theorem Determinacy: forall t t' t'': term, evaluates_to t t' /\ evaluates_to t t'' -> t' = t''.
Admitted. (* 無理〜〜〜〜 *)