Inductive numeric_value :=
  | nvZero
  | nvSucc : numeric_value -> numeric_value.

Inductive term :=
  | tmTrue | tmFalse
  | tmIf : term -> term -> term -> term
  | tmNv : numeric_value -> term
  | tmSucc : term -> term
  | tmPred : term -> term
  | tmIszero : term -> term.

Fixpoint evaluates_to s t :=
  match s, t with
  | tmIf tmTrue s2 _, t => s2 = t
  | tmIf tmFalse _ s3, t => s3 = t
  | tmIf s1 s2 s3, tmIf t1 t2 t3 => evaluates_to s1 t1 /\ s2 = t2 /\ s3 = t3
  | tmSucc (tmNv sv), tmNv (nvSucc tv) => sv = tv
  | tmSucc s1, tmSucc t1 => evaluates_to s1 t1
  | tmPred (tmNv nvZero), tmNv nvZero => True
  | tmPred (tmNv (nvSucc sv)), tmNv tv => sv = tv
  | tmPred s1, tmPred t1 => evaluates_to s1 t1
  | tmIszero (tmNv nvZero), tmTrue => True
  | tmIszero (tmNv (nvSucc _)), tmFalse => True
  | tmIszero s1, tmIszero t1 => evaluates_to s1 t1
  | _, _ => False
  end.

Theorem if_determinacy s1 s2 s3 t :
    evaluates_to (tmIf s1 s2 s3) t
    -> s1 = tmTrue /\ s2 = t
    \/ s1 = tmFalse /\ s3 = t
    \/ exists t1, t = tmIf t1 s2 s3 /\ evaluates_to s1 t1.
Proof.
  destruct s1.
  - simpl. intro. left. split. reflexivity. exact H.
  - simpl. intro. right. left. split. reflexivity. exact H.
  - intro. right. right. destruct t.
    + contradiction.
    + contradiction.
    + exists t1.
      destruct H as [H1 [H2 H3]].
      split.
      * rewrite H2. rewrite H3. reflexivity.
      * apply H1.
    + contradiction.
    + contradiction.
    + contradiction.
    + contradiction.
  - intro. destruct t.
    + contradiction.
    + contradiction.
    + simpl in H. destruct H. contradiction.
    + contradiction.
    + contradiction.
    + contradiction.
    + contradiction.
  - intro. right. right. destruct t.
    + contradiction.
    + contradiction.
    + exists t1.
      destruct H as [H1 [H2 H3]].
      split.
      * rewrite H2. rewrite H3. reflexivity.
      * apply H1.
    + contradiction.
    + contradiction.
    + contradiction.
    + contradiction.
  - intro. right. right. destruct t.
    + contradiction.
    + contradiction.
    + exists t1.
      destruct H as [H1 [H2 H3]].
      split.
      * rewrite H2. rewrite H3. reflexivity.
      * apply H1.
    + contradiction.
    + contradiction.
    + contradiction.
    + contradiction.
  - intro. right. right. destruct t.
    + contradiction.
    + contradiction.
    + exists t1.
      destruct H as [H1 [H2 H3]].
      split.
      * rewrite H2. rewrite H3. reflexivity.
      * apply H1.
    + contradiction.
    + contradiction.
    + contradiction.
    + contradiction.
Qed.

Theorem succ_determinacy s1 t :
  evaluates_to (tmSucc s1) t
  -> (exists sv, s1 = tmNv sv /\ t = tmNv (nvSucc sv))
  \/ (exists t1, t = tmSucc t1 /\ evaluates_to s1 t1).
Proof.
  intro. destruct s1, t.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - right. exists t. split. reflexivity. apply H.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - left. exists n. split.
      * reflexivity.
      * destruct n0.
        -- contradiction.
        -- rewrite H. reflexivity.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - right. exists t. split. reflexivity. apply H.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - right. exists t. split. reflexivity. apply H.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - right. exists t. split. reflexivity. apply H.
  - contradiction.
  - contradiction.
Qed.

Theorem pred_determinacy s1 t :
    evaluates_to (tmPred s1) t
    -> s1 = tmNv nvZero /\ t = tmNv nvZero
    \/ (exists nv, s1 = tmNv (nvSucc nv) /\ t = tmNv nv)
    \/ (exists t1, t = tmPred t1 /\ evaluates_to s1 t1).
Proof.
  intro.
  destruct s1, t.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - right. right. exists t. split. reflexivity. apply H.
  - contradiction.
  - destruct n. contradiction. contradiction.
  - destruct n. contradiction. contradiction.
  - destruct n. contradiction. contradiction.
  - destruct n.
    + left. split. reflexivity. destruct n0. reflexivity. contradiction.
    + right. left. exists n. split. reflexivity. rewrite H. reflexivity.
  - destruct n. contradiction. contradiction.
  - destruct n. contradiction. contradiction.
  - destruct n. contradiction. contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - right. right. exists t. split. reflexivity. apply H.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - right. right. exists t. split. reflexivity. apply H.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - right. right. exists t. split. reflexivity. apply H.
  - contradiction.
Qed.

Theorem iszero_determinacy s1 t:
  evaluates_to (tmIszero s1) t
  -> s1 = tmNv nvZero /\ t = tmTrue
  \/ (t = tmFalse /\ exists nv, s1 = tmNv (nvSucc nv))
  \/ (exists t1, t = tmIszero t1 /\ evaluates_to s1 t1).
Proof.
  intro.
  destruct s1, t.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - right. right. exists t. split. reflexivity. apply H.
  - destruct n.
    + left. split. reflexivity. reflexivity.
    + contradiction.
  - destruct n.
    + contradiction.
    + right. left. split. reflexivity. exists n. reflexivity.
  - destruct n. contradiction. contradiction.
  - destruct n. contradiction. contradiction.
  - destruct n. contradiction. contradiction.
  - destruct n. contradiction. contradiction.
  - destruct n. contradiction. contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - right. right. exists t. split. reflexivity. apply H.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - right. right. exists t. split. reflexivity. apply H.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - right. right. exists t. split. reflexivity. apply H.
Qed.

Theorem determinacy : forall s t t', evaluates_to s t /\ evaluates_to s t' -> t = t'.
Proof.
  induction s.
  - intros t t' [H _]. contradiction.
  - intros t t' [H _]. contradiction.
  - intros t t' [H H'].
    destruct (if_determinacy s1 s2 s3 t) as [[Hs1T Hs2]|[[Hs1F Hs3]|[t1[Ht Ht1]]]].
    + exact H.
    + rewrite Hs1T in H'. rewrite <- Hs2. apply H'.
    + rewrite Hs1F in H'. rewrite <- Hs3. apply H'.
    + destruct (if_determinacy s1 s2 s3 t') as [[Hs1T Hs2]|[[Hs1F Hs3]|[t1'[Ht' Ht1']]]].
      * exact H'.
      * rewrite Hs1T in H. rewrite <- H. exact Hs2.
      * rewrite Hs1F in H. rewrite <- H. exact Hs3.
      * rewrite Ht, Ht'. rewrite (IHs1 t1 t1'). reflexivity. split. exact Ht1. exact Ht1'.
  - intros t t' [H _]. contradiction.
  - intros t t' [H H'].
    destruct (succ_determinacy s t, succ_determinacy s t') as ([[sv[Hs Ht]]|[t1[Ht Ht1]]], [[sv'[Hs' Ht']]|[t1'[Ht' Ht1']]]).
    + exact H.
    + exact H'.
    + rewrite Hs in Hs'. injection Hs'. intro. rewrite Ht'. rewrite <- H0. exact Ht.
    + rewrite Hs in Ht1'. contradiction.
    + exact H'.
    + rewrite Hs' in Ht1. contradiction.
    + rewrite Ht, Ht'. rewrite (IHs t1 t1'). reflexivity. split. exact Ht1. exact Ht1'.
  - intros t t' [H H'].
    destruct (pred_determinacy s t, pred_determinacy s t') as ([[Hs Ht]|[[nv[Hs Ht]]|[t1[Ht Hs]]]], [[Hs' Ht']|[[nv'[Hs' Ht']]|[t1'[Ht' Hs']]]]).
    + exact H.
    + exact H'.
    + rewrite Ht, Ht'. reflexivity.
    + rewrite Hs in Hs'. discriminate.
    + rewrite Hs in Hs'. contradiction.
    + exact H'.
    + rewrite Hs in Hs'. discriminate.
    + rewrite Hs in Hs'. injection Hs'. intro. rewrite Ht, Ht', H0. reflexivity.
    + rewrite Hs in Hs'. contradiction.
    + exact H'.
    + rewrite Hs' in Hs. contradiction.
    + rewrite Hs' in Hs. contradiction.
    + rewrite Ht, Ht', (IHs t1 t1'). reflexivity. split. exact Hs. exact Hs'.
  - intros t t' [H H'].
    destruct (iszero_determinacy s t, iszero_determinacy s t') as ([[Hs Ht]|[[Ht[nv Hs]]|[t1[Ht Hs]]]], [[Hs' Ht']|[[Ht'[nv' Hs']]|[t1'[Ht' Hs']]]]).
    + exact H.
    + exact H'.
    + rewrite Ht, Ht'. reflexivity.
    + rewrite Hs in Hs'. discriminate.
    + rewrite Hs in Hs'. contradiction.
    + exact H'.
    + rewrite Hs in Hs'. discriminate.
    + rewrite Ht, Ht'. reflexivity.
    + rewrite Hs in Hs'. contradiction.
    + exact H'.
    + rewrite Hs' in Hs. contradiction.
    + rewrite Hs' in Hs. contradiction.
    + rewrite Ht, Ht', (IHs t1 t1'). reflexivity. split. exact Hs. exact Hs'.
Qed.

Variant type := Bool | Nat.

Fixpoint is_typed t T :=
  match t, T with
  | tmTrue, Bool | tmFalse, Bool => True
  | tmIf t1 t2 t3, T1 => is_typed t1 Bool /\ is_typed t2 T1 /\ is_typed t3 T1
  | tmNv _, Nat => True
  | tmSucc t1, Nat | tmPred t1, Nat | tmIszero t1, Bool => is_typed t1 Nat
  | _, _ => False
  end.

Lemma inv_true T: is_typed tmTrue T -> T = Bool.
Proof.
  simpl.
  destruct T.
  reflexivity.
  contradiction.
Qed.

Lemma inv_false T: is_typed tmFalse T -> T = Bool.
Proof.
  simpl.
  destruct T.
  reflexivity.
  contradiction.
Qed.

Lemma inv_if t1 t2 t3 T: is_typed (tmIf t1 t2 t3) T -> is_typed t1 Bool /\ is_typed t2 T /\ is_typed t3 T.
Proof. trivial. Qed.

Lemma inv_zero nv T: is_typed (tmNv nv) T -> T = Nat.
Proof.
  simpl.
  destruct T.
  contradiction.
  reflexivity.
Qed.

Lemma inv_succ t1 T: is_typed (tmSucc t1) T -> T = Nat /\ is_typed t1 Nat.
Proof.
  simpl.
  destruct T.
  - contradiction.
  - split.
    + reflexivity.
    + exact H.
Qed.

Lemma inv_pred t1 T: is_typed (tmPred t1) T -> T = Nat /\ is_typed t1 Nat.
Proof.
  simpl.
  destruct T.
  - contradiction.
  - split.
    + reflexivity.
    + exact H.
Qed.

Lemma inv_iszero t1 T: is_typed (tmIszero t1) T -> T = Bool /\ is_typed t1 Nat.
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
