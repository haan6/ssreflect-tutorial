From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Import ss
Import ssreflect.SsrSyntax.

Section Symmetric_Conjunction_Disjunction.

  Lemma andb_sym : forall A B : bool, A && B -> B && A.
  Proof.
    case. (* case splitting among the constructor *)
      by case.
    by [].
  Qed.
  
  Lemma andb_sym2 : forall A B : bool, A && B -> B && A.
  Proof. by case; case. Qed.

  Lemma andb_sym3 : forall A B : bool, A && B -> B && A.
  (* case; case *)
  Proof. by do 2! case. Qed.

  Lemma and_sym : forall A B : Prop, A /\ B -> B /\ A.
  (* move=> A1 B; case *)
  Proof. by move=> A1 B []. Qed.

  Lemma or_sym : forall A B : Prop, A \/ B -> B \/ A.
  Proof. by move=> A B [hA | hB]; [apply: or_intror | apply: or_introl]. Qed.

  Lemma or_sym2 : forall A B : bool, A \/ B -> B \/ A.
  (* "move=> [] [] AorB": case; case; move=> AorB
     "apply/orP": rephrases the goal using the reflection lemma
     "move/orP : AorB": move: AorB; move/orP *)
  Proof. by move=> [] [] AorB; apply/orP; move/orP : AorB.
  Qed.
End Symmetric_Conjunction_Disjunction.

Section R_sym_trans.
  
  Variables (D : Type) (R : D -> D -> Prop).
  Hypothesis R_sym : forall x y, R x y -> R y x.
  Hypothesis R_trans : forall x y z, R x y -> R y z -> R x z.

  Lemma refl_if : forall x : D, (exists y, R x y) -> R x x.
  Proof.
    move=> x [y Rxy].
    by apply: R_trans _ (R_sym _ y _).
  Qed.
End R_sym_trans.

Section Smullyan_drinker.
  Variables (D : Type) (P : D -> Prop).
  Hypothesis (d : D) (EM : forall A, A \/ ~A).

  Lemma drinker : exists x, P x -> forall y, P y.
  Proof.
    (* "case: (EM (exists y, ~P y))": move: (EM (exists y, ~P y)); case. *)
    case: (EM (exists y, ~P y)) => [[y notPy] | nonotPy]; first by exists y. (* It can be replaced with "have [[y notPy] | nonotPy] := EM (exists y, ~P y)" *)

    (* // tries to solve trival subgoals *)
    exists d => _ y; case: (EM (P y)) => // notPy.
    by case: nonotPy; exists y.
  Qed.
End Smullyan_drinker.

(*Section Equality.*)
(*  Variable f : nat -> nat.*)
(**)
(*  Hypothesis f00 : f 0 = 0.*)
(**)
(*  Lemma fkk : forall k, k = 0 -> f k = k.*)
(*  Proof.*)
(*    move=> k k0.*)
(*    by rewrite k0.*)
(*    Qed.*)
(**)
(*  Lemma fkk2 : forall k, k = 0 -> f k = k.*)
(*  (* "move=> k ->": move=> k hyp; rewrite {} hyp. *)*)
(*  Proof. by move=> k ->. Qed.*)
(**)
(*  Variable f10 : f 1 = f 0.*)
(**)
(*  Lemma ff10 : f (f 1) = 0.*)
(*  Proof. by rewrite f10 f00. Qed.*)
(**)
(*  Variables (D : eqType) (x y : D).*)
(*  Lemma eq_prop_bool : x = y -> x == y.*)
(*  Proof. by move/eqP. Qed.*)
(*  Lemma eq_bool_prop : x == y -> x = y.*)
(*  Proof. by move/eqP. Qed.*)
(**)
(*End Equality.*)

