

Definition Regular_Induction := forall P, (P(0) /\ (forall k, P(k) -> P(S k)))
                                            -> (forall n, P(n)).
Definition Strong_Induction := forall P, (P(0) /\
                                         (forall k, (forall m, m <= k -> P(m)) -> P(S k)))
                                            -> (forall n, P(n)).

Definition Generalized_Strong_Induction := forall P, P(0) /\
                                                     (forall k, (forall m, m <= k -> P(m)) -> P(S k))
                                                     -> forall n m, m <= n -> P(m).


Lemma regular_implies_generalized_strong:
  Regular_Induction -> Generalized_Strong_Induction.
Proof.
  unfold Regular_Induction. unfold Generalized_Strong_Induction.
  intros RI P H1.
  induction n.
  - intros m H2. inversion H2.  destruct H1. assumption.
  - intros m H2. inversion H2.
    + destruct H1. apply H1. intros m0 H3. apply IHn. assumption.
    + apply IHn. assumption.
Qed.



Lemma generalized_strong_implies_strong:
  Generalized_Strong_Induction -> Strong_Induction.
  unfold Generalized_Strong_Induction. unfold Strong_Induction.
  intros. specialize (H P). pose proof (H H0) as H1.
  specialize (H1 n). specialize (H1 n).  apply H1. constructor.
Qed.

Lemma regular_implies_strong:
  Regular_Induction -> Strong_Induction.
Proof.
  intro H.
  apply generalized_strong_implies_strong.
  apply regular_implies_generalized_strong.
  assumption.
Qed.


Lemma strong_implies_regular: Strong_Induction -> Regular_Induction.
Proof.
  unfold Strong_Induction.  unfold Regular_Induction.
  intros SI P H.
  apply SI.
  split.
  - destruct H. apply H.
  - intro k. intro A.
    destruct H.  apply H0. apply A. auto.
Qed.

Theorem strong_equals_regular: Strong_Induction <-> Regular_Induction.
  split.
  apply strong_implies_regular.
  apply regular_implies_strong.
Qed.