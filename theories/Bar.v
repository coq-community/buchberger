(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

From Coq Require Import List.

Set Default Proof Using "Type".

Definition Pred (A : Type) := A -> Prop.

Definition Rel (A : Type) := A -> A -> Prop.

Inductive ExistsL (A : Type) (P : Pred A) : list A -> Type :=
  | FoundE : forall (a : A) (l : list A), P a -> ExistsL A P (a :: l)
  | SearchE :
      forall (a : A) (l : list A), ExistsL A P l -> ExistsL A P (a :: l).

Global Hint Resolve FoundE SearchE : core.

Lemma monExistsL1 :
 forall (A : Type) (P : Pred A) (xs bs : list A),
 ExistsL A P bs -> ExistsL A P (xs ++ bs).
Proof.
intros A P xs; elim xs; simpl in |- *; auto.
Qed.

Global Hint Resolve monExistsL1 : core.

Lemma monExistsL :
 forall (A : Type) (P : Pred A) (xs bs cs : list A),
 ExistsL A P (xs ++ bs) -> ExistsL A P (xs ++ cs ++ bs).
Proof.
intros A P xs; elim xs; simpl in |- *; auto.
intros a l H' bs cs H'0; inversion H'0; auto.
Qed.

Global Hint Resolve monExistsL : core.

Inductive GoodR (A : Type) (R : Rel A) : list A -> Type :=
  | FoundG :
      forall (a : A) (l : list A),
      ExistsL A (fun x : A => R x a) l -> GoodR A R (a :: l)
  | SearchG : forall (a : A) (l : list A), GoodR A R l -> GoodR A R (a :: l).

Global Hint Resolve FoundG SearchG : core.

Lemma monGoodR1 :
 forall (A : Type) (R : Rel A) (xs bs : list A),
 GoodR A R bs -> GoodR A R (xs ++ bs).
Proof.
intros A R xs; elim xs; simpl in |- *; auto.
Qed.

Global Hint Resolve monGoodR1 : core.

Lemma monGoodR :
 forall (A : Type) (R : Rel A) (xs bs cs : list A),
  GoodR A R (xs ++ bs) -> GoodR A R (xs ++ cs ++ bs).
Proof.
intros A R xs bs cs; elim xs; simpl in |- *; auto.
intros a l H' H'0; inversion H'0; simpl in |- *; auto.
Qed.

Global Hint Resolve monGoodR : core.

Lemma subPredExistsL :
 forall (A B : Type) (P : Pred A) (S : Pred B) (f : A -> B),
 (forall a : A, P a -> S (f a)) ->
 forall l : list A, ExistsL A P l -> ExistsL B S (map f l).
Proof.
intros A B P S f H' l H'0; elim H'0; simpl in |- *; auto.
Qed.

Lemma subRelGoodR :
 forall (A B : Type) (R : Rel A) (S : Rel B) (f : A -> B),
 (forall a b : A, R a b -> S (f a) (f b)) ->
 forall l : list A, GoodR A R l -> GoodR B S (map f l).
Proof.
intros A B R S f H' l H'0; elim H'0; simpl in |- *; auto.
intros a l0 H'1; apply FoundG; auto.
apply subPredExistsL with (P := fun x : A => R x a); auto.
Qed.

Inductive Bar (A : Type) (P : list A -> Type) : list A -> Type :=
  | Base : forall l : list A, P l -> Bar A P l
  | Ind : forall l : list A, (forall a : A, Bar A P (a :: l)) -> Bar A P l.

Global Hint Resolve Base Ind : core.

Definition GRBar (A : Type) (R : Rel A) := Bar A (GoodR A R).

Definition WR (A : Type) (R : Rel A) := GRBar A R nil.

Global Hint Unfold GRBar WR : core.

Lemma subRelGRBar :
 forall (A B : Type) (R : Rel A) (S : Rel B) (f : A -> B),
 (forall a b : A, R a b -> S (f a) (f b)) ->
 (forall b : B, {a : A | b = f a}) ->
 forall l : list A, GRBar A R l -> GRBar B S (map f l).
Proof.
intros A B R S f H' H'0 l H'1; elim H'1; simpl in |- *; auto.
intros l0 H'2.
red in |- *; apply Base; auto.
unfold GRBar in |- *.
apply subRelGoodR with (R := R); auto.
intros l0 H'2 H'3; red in |- *; apply Ind; auto.
intros a; case (H'0 a); auto.
intros x H'4; rewrite H'4; auto.
unfold GRBar in H'3; apply H'3; auto.
Qed.

Lemma consGRBar :
 forall (A : Type) (R : Rel A) (l : list A),
 GRBar A R l -> forall a : A, GRBar A R (a :: l).
Proof.
intros A R l H'; elim H'; auto.
Qed.

Global Hint Resolve consGRBar : core.

Lemma nilGRBar :
 forall (A : Type) (R : Rel A),
 GRBar A R nil -> forall l : list A, GRBar A R l.
Proof.
intros A R H' l; elim l; auto.
Qed.

Lemma monGRBarAux :
 forall (A : Type) (R : Rel A) (l : list A),
 GRBar A R l ->
 forall xs bs cs : list A, l = xs ++ cs -> GRBar A R (xs ++ bs ++ cs).
Proof.
intros A R l H'; elim H'; auto.
intros l0 H'0 xs bs cs H'1; red in |- *; rewrite H'1 in H'0; auto.
intros l0 H'0 H'1 xs bs cs H'2; rewrite H'2 in H'1; auto.
red in |- *; apply Ind.
intros a.
change (Bar A (GoodR A R) ((a :: xs) ++ bs ++ cs)) in |- *.
unfold GRBar in H'1; apply H'1 with (a := a); auto.
Qed.

Lemma monGRBar :
 forall (A : Type) (R : Rel A) (xs bs cs : list A),
 GRBar A R (xs ++ cs) -> GRBar A R (xs ++ bs ++ cs).
Proof.
intros A R xs bs cs H'.
apply monGRBarAux with (l := xs ++ cs); auto.
Qed.

Global Hint Resolve monGRBar : core.

Section lems.
Variable trm : Type.
Variable tdiv : trm -> trm -> Prop.

Definition Bad (M : list trm) := GoodR trm tdiv M -> False.

Lemma tdivExists_trmHd_lem :
 forall (F : list trm) (f : trm),
 (forall g : trm, In g F -> ~ tdiv g f) ->
 ExistsL trm (fun g : trm => tdiv g f) F -> False.
Proof.
intros F; elim F; simpl in |- *; auto.
intros f H' H'0; inversion H'0; auto.
intros a l H' f H'0 H'1; inversion H'1; auto.
lapply (H'0 a); [ intro H'3; apply H'3 | idtac ]; auto.
apply H' with (f := f); auto.
Qed.

Lemma tdivGoodP :
 forall (F : list trm) (f : trm),
 Bad F -> (forall g : trm, In g F -> ~ tdiv g f) -> Bad (f :: F).
Proof.
intros F f H' H'0; red in |- *.
intros H'1; inversion H'1; auto.
apply tdivExists_trmHd_lem with (F := F) (f := f); auto.
Qed.

End lems.
