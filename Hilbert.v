Require Import ssreflect.

Section HilbertSaxiom.
  Variables A B C : Prop.

  (* "move=>H...": intros
     "move:H": revert
     "move:(H)": generalize

     "apply: H": move: H; apply. *)
  Lemma HilbertS : (A -> B -> C) -> (A -> B) -> A -> C.
  Proof.
    move=> hAiBiC hAiB hA.
    move: hAiBiC.
    apply.
    by [].
    by apply: hAiB.
  Qed.

  Hypothesis (hAiBiC : A -> B -> C) (hAiB : A -> B) (hA : A).

  (* "exact: H": move: H; exact. (exact is a sort of combination between apply and by []). *)
  Lemma HilbertS2 : C.
  Proof.
    apply: hAiBiC; first by apply: hA.
    exact: hAiB.
  Qed.

  Lemma HilbertS3 : C.
  Proof. by apply: hAiBiC; last exact: hAiB. Qed.

  Check (hAiB hA). (* B *)
  Check (hAiBiC hA). (* B -> C *)

  Lemma HilbertS4 : C.
  (* (((A -> B -> C) A) ((A -> B) A)) *)
  Proof. exact: (hAiBiC _ (hAiB _)). Qed.

  Lemma HilbertS5 : C.
  Proof. exact: hAiBiC (hAiB _). Qed.

  Lemma HilbertS6 : C.
  Proof. exact HilbertS5. Qed.
End HilbertSaxiom.

