(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Relation_Operators.
Require Import Transitive_Closure.
From Equations Require Import Equations.

Derive Signature for Relation_Operators.lexprod.

Section WfLexicographic_Product_Closed.
  Variable A : Type.
  Variable B : A -> Type.
  Variable leA : A -> A -> Prop.
  Variable leB : forall x:A, B x -> B x -> Prop.

  Notation LexProd := (@Relation_Operators.lexprod A B leA leB).

  Lemma acc_A_B_lexprod_closed :
    forall x:A,
      Acc leA x ->
      (forall x0:A, clos_trans A leA x0 x -> well_founded (leB x0)) ->
      forall y:B x, Acc (leB x) y -> Acc LexProd (existT B x y).
  Proof.
    induction 1 as [x _ IHAcc]; intros H2 y.
    induction 1 as [x0 H IHAcc0]; intros.
    apply Acc_intro.
    destruct y as [x2 y1]; intro H6.
    depelim H6.
    - cut (leA x2 x); intros.
      + apply IHAcc; auto with sets.
        * intros.
          apply H2.
          apply t_trans with x2; auto with sets.

        * red in H2.
          apply H2.
          auto with sets.

      + assumption.

    - apply IHAcc0.
      assumption.
  Defined.

  Theorem wf_lexprod_closed :
    well_founded leA ->
    (forall x:A, well_founded (leB x)) -> well_founded LexProd.
  Proof.
    intros wfA wfB; unfold well_founded.
    destruct a.
    apply acc_A_B_lexprod_closed; auto with sets; intros.
    red in wfB.
    auto with sets.
  Defined.

End WfLexicographic_Product_Closed.
