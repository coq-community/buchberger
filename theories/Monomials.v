(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(* ************************************************************************
                                                                           
          Buchberger : the monomials                                       
                                                                           
          Laurent Thery 	                                             
                                                                           
   ************************************************************************ *)

From Coq Require Import Arith Compare Compare_dec Peano_dec.
From Coq Require Import Relation_Definitions EqdepFacts Eqdep_dec Max.

Set Default Proof Using "Type".

Section Monomials.

Inductive mon : nat -> Set :=
  | n_0 : mon 0
  | c_n : forall d : nat, nat -> mon d -> mon (S d).

(*
Realizer [d: nat][m:(mon d)](Cases  m of n_0 => O | (c_n _ n _) => n end).
*)
Definition pmon1 : forall d : nat, mon d -> nat.
intros d m; case m.
exact 0.
intros d' n p; exact n.
Defined.

(*
Realizer [d:nat] [m:mon](<mon>Case m of n_0 [a:nat] [b:nat] [m':mon]m' end).
*)
Definition pmon2 : forall d : nat, mon d -> mon (pred d).
intros d m; case m.
exact n_0.
intros d' n p; exact p.
Defined.

(* Realizer [d:nat] [m:mon]
         (<mon>Case d of
           (False_rec mon) [d':nat](c_n d' (pmon1 (S d') m) (pmon2 (S d') m))
           end).
*)
Definition recomp : forall d : nat, d <> 0 -> mon d -> mon d.
intros d; case d.
intros H'; apply False_rec; case H'; auto.
intros d' H m; exact (c_n d' (pmon1 (S d') m) (pmon2 (S d') m)).
Defined.

Lemma recomp_ok : forall (d : nat) (h : d <> 0) (m : mon d), recomp d h m = m.
Proof.
intros d h m.
generalize h; clear h.
elim m.
intros h; elim h; auto.
intros; simpl in |- *; unfold recomp in |- *; auto.
Qed.

Lemma proj_ok :
 forall (d : nat) (m : mon (S d)), c_n d (pmon1 (S d) m) (pmon2 (S d) m) = m.
Proof.
intros d m; cut (S d <> 0); auto.
intros H; cut (recomp (S d) H m = m); auto.
apply recomp_ok; auto.
Qed.

(* Generator *)

Definition gen_mon : forall d : nat, nat -> mon d.
intros d; elim d.
intros n; exact n_0.
intros n H' n'; case n'.
exact (c_n n 1 (H' n)).
intros n''; exact (c_n n 0 (H' n'')).
Defined.

(* Multiplication of monomials *)

Definition mult_mon : forall d : nat, mon d -> mon d -> mon d.
intros d; elim d.
intros H' H'0; exact n_0.
intros n Rec S1 S2.
exact
 (c_n n (pmon1 (S n) S1 + pmon1 (S n) S2)
    (Rec (pmon2 (S n) S1) (pmon2 (S n) S2))).
Defined.

Theorem mult_mon_com :
 forall (d : nat) (a b : mon d), mult_mon d a b = mult_mon d b a.
Proof.
intros d; elim d; simpl in |- *; auto.
intros n H' a b.
rewrite (H' (pmon2 (S n) a) (pmon2 (S n) b)); auto.
rewrite (Nat.add_comm (pmon1 (S n) a) (pmon1 (S n) b)); auto.
Qed.

Theorem mult_mon_assoc :
 forall (d : nat) (a b c : mon d),
 mult_mon d a (mult_mon d b c) = mult_mon d (mult_mon d a b) c.
Proof.
intros d; elim d; simpl in |- *; auto.
intros n H' a b c.
rewrite (H' (pmon2 (S n) a) (pmon2 (S n) b) (pmon2 (S n) c)); auto.
rewrite (Nat.add_assoc (pmon1 (S n) a) (pmon1 (S n) b) (pmon1 (S n) c)); auto.
Qed.

(* Zero *)

Definition zero_mon : forall d : nat, mon d.
intros d; elim d.
exact n_0.
intros n Rec; exact (c_n n 0 Rec).
Defined.

Theorem mult_mon_zero_r :
 forall (d : nat) (a : mon d), mult_mon d a (zero_mon d) = a.
Proof.
intros d a; elim a; auto.
simpl in |- *.
intros d0 n m H'; rewrite H'; auto.
rewrite (Nat.add_comm n 0); auto.
Qed.

Theorem mult_mon_zero_l :
 forall (d : nat) (a : mon d), mult_mon d (zero_mon d) a = a.
Proof.
intros d a; elim a; auto.
simpl in |- *.
intros d0 n m H'; rewrite H'; auto.
Qed.

(* Division of monomials *)

Inductive mdiv : forall d : nat, mon d -> mon d -> Prop :=
  | mdiv_nil : mdiv 0 n_0 n_0
  | mdiv_cons :
      forall (d : nat) (v v' : mon d) (n n' : nat),
      n <= n' -> mdiv d v v' -> mdiv (S d) (c_n d n v) (c_n d n' v').

Local Hint Resolve mdiv_nil mdiv_cons : core.

Lemma mdiv_proj :
 forall (d : nat) (m m' : mon (S d)),
 pmon1 (S d) m <= pmon1 (S d) m' ->
 mdiv d (pmon2 (S d) m) (pmon2 (S d) m') -> mdiv (S d) m m'.
Proof.
intros d m m' H' H'0; rewrite <- (proj_ok d m); rewrite <- (proj_ok d m');
 auto.
Qed.

Lemma mdiv_inv : forall d x y,
  mdiv d x y <->
  match d return mon d -> mon d -> Prop with
  | 0 => fun x y => n_0 = x /\ n_0 = y
  | S d => fun x y => exists v v' n n', n <= n' /\ mdiv d v v' /\ c_n d n v = x /\ c_n d n' v' = y
  end x y.
Proof.
intros d x y;split.
- intros m;destruct m;eauto 8.
- destruct d;intros m.
  + destruct m as [[] []];constructor.
  + destruct m as [? [? [? [? [? [? [[] []]]]]]]].
    constructor;assumption.
Defined.

(* Division is transitive *)

Lemma mdiv_trans : forall d : nat, transitive (mon d) (mdiv d).
Proof.
intros d; elim d; unfold transitive in |- *; auto.
- intros x y z mxy myz.
  apply mdiv_inv in mxy;apply mdiv_inv in myz.
  apply mdiv_inv.
  intuition.
- intros n Rec x y z mxy myz.
  apply mdiv_inv in mxy;apply mdiv_inv in myz.
  destruct mxy as [vxy [vxy' [nxy [nxy' [Hnxy [Hdivxy [eq1 eq2]]]]]]].
  destruct myz as [vyz [vyz' [nyz [nyz' [Hnyz [Hdivyz [eq3 eq4]]]]]]].
  destruct eq1,eq2,eq4.
  injection eq3;clear eq3;intros eqv eqn.
  destruct eqn.
  pose proof (eq_sigT_snd eqv) as eqv'.
  rewrite (UIP_refl_nat n _) in eqv'.
  simpl in eqv';destruct eqv';clear eqv.
  apply mdiv_cons.
  * apply Nat.le_trans with (m := nyz); assumption.
  * apply Rec with (y := vyz); assumption.
Qed.

(* Division of monomials (total function!) *)

Definition div_mon : forall d : nat, mon d -> mon d -> mon d.
intros d; elim d.
intros H' H'0; exact n_0.
intros n Rec S1 S2.
exact
 (c_n n (pmon1 (S n) S1 - pmon1 (S n) S2)
    (Rec (pmon2 (S n) S1) (pmon2 (S n) S2))).
Defined.

Theorem mdiv_div :
 forall (d : nat) (a b : mon d),
 mdiv d b a -> mult_mon d (div_mon d a b) b = a.
Proof.
intros d a b H'; elim H'; simpl in |- *; auto.
intros d0 v v' n n' H'0 H'1 H'2.
rewrite Nat.sub_add; auto.
rewrite H'2; auto.
Qed.

(* Division of monomials (total function!) *)

Definition div_mon_clean : forall d : nat, mon d -> mon d -> mon d * bool.
intros d; elim d.
intros H' H'0; exact (n_0, true).
intros n Rec S1 S2.
case (le_lt_dec (pmon1 (S n) S2) (pmon1 (S n) S1)).
case (Rec (pmon2 (S n) S1) (pmon2 (S n) S2)).
intros res b H'1; exact (c_n n (pmon1 (S n) S1 - pmon1 (S n) S2) res, b).
intros H'; exact (S1, false).
Defined.

Definition is_nil : forall d : nat, mon d -> mon d.
intros d; case d.
intros H'; exact n_0.
intros n H'; exact H'.
Defined.

Theorem is_nil_id : forall (d : nat) (a : mon d), a = is_nil d a.
Proof.
intros d a; elim a; simpl in |- *; auto.
Qed.

Theorem mon_0 : forall a : mon 0, a = n_0.
Proof.
intros a; generalize (is_nil_id 0 a); simpl in |- *; auto.
Qed.

Local Hint Resolve mon_0 : core.

Definition eqmon_dec : forall (d : nat) (x y : mon d), {x = y} + {x <> y}.
intros d; elim d; auto.
intros x y; left.
rewrite (mon_0 x); rewrite (mon_0 y); auto.
intros n H' x y.
elim (eq_nat_dec (pmon1 (S n) x) (pmon1 (S n) y)); intros H'2.
elim (H' (pmon2 (S n) x) (pmon2 (S n) y)); intros H'3.
left.
rewrite <- (proj_ok n x).
rewrite <- (proj_ok n y).
rewrite H'3; rewrite H'2; auto.
right; rewrite <- (proj_ok n x); rewrite <- (proj_ok n y); red in |- *;
 intros H'0.
apply H'3.
change
  (pmon2 (S n) (c_n n (pmon1 (S n) x) (pmon2 (S n) x)) =
   pmon2 (S n) (c_n n (pmon1 (S n) y) (pmon2 (S n) y)) :>
   mon n) in |- *.
rewrite H'0; auto.
right; red in |- *; rewrite <- (proj_ok n x); rewrite <- (proj_ok n y);
 intros H'0; apply H'2; injection H'0; auto.
Defined.

Theorem mult_div_com :
 forall (d : nat) (a b : mon d), div_mon d (mult_mon d a b) b = a.
Proof.
intros d; elim d; simpl in |- *; auto.
intros n H' a b.
rewrite (H' (pmon2 (S n) a) (pmon2 (S n) b)); auto.
rewrite Nat.add_sub.
apply proj_ok; auto.
Qed.

Theorem mult_div_id :
 forall (d : nat) (a : mon d), div_mon d a a = zero_mon d.
Proof.
intros d a; elim a; simpl in |- *; auto.
intros d0 n m H'; rewrite H'; auto.
rewrite Nat.sub_diag; auto.
Qed.

Let gb : forall d : nat, mon d * bool -> bool.
intros d H'; case H'; auto.
Defined.

Let gm : forall d : nat, mon d * bool -> mon d.
intros d H'; case H'; auto.
Defined.

Theorem minus_lt_0 : forall m n : nat, n < m -> n - m = 0.
Proof.
intros m; elim m; simpl in |- *; auto.
intros n H; absurd (n < 0); auto with arith.
intros n H' n0; case n0; simpl in |- *; auto with arith.
Qed.

Theorem div_clean_dec2 :
 forall (d : nat) (a b : mon d),
 gb d (div_mon_clean d a b) = false -> mult_mon d (div_mon d a b) b <> a.
Proof.
intros d; elim d; simpl in |- *; auto.
intros a H' H'0; inversion H'0; auto.
intros n H' a b.
case (le_lt_dec (pmon1 (S n) b) (pmon1 (S n) a)); simpl in |- *; auto.
intros l; generalize (H' (pmon2 (S n) a) (pmon2 (S n) b)).
case (div_mon_clean n (pmon2 (S n) a) (pmon2 (S n) b)); simpl in |- *; auto.
intros H'0 b0 H'1 H'2; red in |- *; intros H'3.
lapply H'1; [ intros H'4; apply H'4; clear H'1 | clear H'1 ]; auto.
change
  (pmon2 (S n)
     (c_n n (pmon1 (S n) a - pmon1 (S n) b + pmon1 (S n) b)
        (mult_mon n (div_mon n (pmon2 (S n) a) (pmon2 (S n) b))
           (pmon2 (S n) b))) = pmon2 (S n) a :>mon n) 
 in |- *.
rewrite H'3; auto.
intros H'0 H'1; red in |- *; intros H'2;
 absurd (pmon1 (S n) a - pmon1 (S n) b + pmon1 (S n) b = pmon1 (S n) a); 
 auto.
2: change
     (pmon1 (S n)
        (c_n n (pmon1 (S n) a - pmon1 (S n) b + pmon1 (S n) b)
           (mult_mon n (div_mon n (pmon2 (S n) a) (pmon2 (S n) b))
              (pmon2 (S n) b))) = pmon1 (S n) a :>nat) 
    in |- *.
2: rewrite H'2; auto.
rewrite (minus_lt_0 (pmon1 (S n) b) (pmon1 (S n) a)); simpl in |- *; auto.
red in |- *; intros H'3; absurd (pmon1 (S n) a < pmon1 (S n) b); auto.
apply Nat.le_ngt; auto.
rewrite H'3; auto.
Qed.

Theorem div_clean_dec1 :
 forall (d : nat) (a b : mon d),
 gb d (div_mon_clean d a b) = true ->
 gm d (div_mon_clean d a b) = div_mon d a b /\
 mult_mon d (div_mon d a b) b = a.
Proof.
intros d; elim d; simpl in |- *; auto.
intros n H' a b; case (le_lt_dec (pmon1 (S n) b) (pmon1 (S n) a));
 simpl in |- *; auto.
2: intros H'0 H'1; inversion H'1.
intros l; generalize (H' (pmon2 (S n) a) (pmon2 (S n) b)).
case (div_mon_clean n (pmon2 (S n) a) (pmon2 (S n) b)); simpl in |- *; auto.
intros m b' H1 H2.
case (H1 H2); intros H3 H4; split; auto.
rewrite H3; auto.
rewrite Nat.sub_add; auto.
rewrite H4; auto.
exact (proj_ok n a).
Qed.

Definition ppcm_mon : forall d : nat, mon d -> mon d -> mon d.
intros d; elim d.
intros m1 m2; exact n_0.
intros n Rec S1 S2.
exact
 (c_n n (Nat.max (pmon1 (S n) S1) (pmon1 (S n) S2))
    (Rec (pmon2 (S n) S1) (pmon2 (S n) S2))).
Defined.

Theorem ppcm_com :
 forall (d : nat) (a b : mon d), ppcm_mon d a b = ppcm_mon d b a.
Proof.
intros d; elim d; simpl in |- *; auto.
intros n H' a b; rewrite (H' (pmon2 (S n) a) (pmon2 (S n) b)).
rewrite (Nat.max_comm (pmon1 (S n) a) (pmon1 (S n) b)); auto.
Qed.

Theorem ppcm_prop_l :
 forall (d : nat) (a b : mon d),
 ppcm_mon d a b = mult_mon d (div_mon d (ppcm_mon d a b) a) a.
Proof.
intros d; elim d; simpl in |- *; auto.
intros n H' a b;
 pattern (ppcm_mon n (pmon2 (S n) a) (pmon2 (S n) b)) at 1 in |- *;
 rewrite (H' (pmon2 (S n) a) (pmon2 (S n) b)).
pattern (Nat.max (pmon1 (S n) a) (pmon1 (S n) b)) at 1 in |- *;
rewrite Nat.sub_add; auto.
apply Nat.le_max_l; auto.
Qed.

Theorem ppcm_prop_r :
 forall (d : nat) (a b : mon d),
 ppcm_mon d a b = mult_mon d (div_mon d (ppcm_mon d a b) b) b.
Proof.
intros d; elim d; simpl in |- *; auto.
intros n H' a b;
 pattern (ppcm_mon n (pmon2 (S n) a) (pmon2 (S n) b)) at 1 in |- *;
 rewrite (H' (pmon2 (S n) a) (pmon2 (S n) b)).
pattern (Nat.max (pmon1 (S n) a) (pmon1 (S n) b)) at 1 in |- *;
 rewrite Nat.sub_add; auto.
apply Nat.le_max_r; auto.
Qed.

Theorem plus_minus_le : forall a b : nat, a - b + b = a -> b <= a.
Proof.
intros a; elim a; simpl in |- *; auto.
intros b H'; rewrite H'; auto.
intros n H' b; case b; simpl in |- *; auto with arith.
intros n0; rewrite (Nat.add_comm (n - n0) (S n0)); simpl in |- *; auto.
rewrite (Nat.add_comm n0 (n - n0)); auto with arith.
Qed.

Theorem ppcm_mom_is_ppcm :
 forall (d : nat) (a b c : mon d),
 c = mult_mon d (div_mon d c a) a ->
 c = mult_mon d (div_mon d c b) b ->
 c = mult_mon d (div_mon d c (ppcm_mon d a b)) (ppcm_mon d a b).
Proof.
intros d; elim d; simpl in |- *; auto.
intros n H' a b c H'0 H'1.
rewrite <- (H' (pmon2 (S n) a) (pmon2 (S n) b) (pmon2 (S n) c)); auto.
2: change
     (pmon2 (S n) c =
      pmon2 (S n)
        (c_n n (pmon1 (S n) c - pmon1 (S n) a + pmon1 (S n) a)
           (mult_mon n (div_mon n (pmon2 (S n) c) (pmon2 (S n) a))
              (pmon2 (S n) a))) :>mon n) in |- *; auto.
2: rewrite <- H'0; auto.
2: change
     (pmon2 (S n) c =
      pmon2 (S n)
        (c_n n (pmon1 (S n) c - pmon1 (S n) b + pmon1 (S n) b)
           (mult_mon n (div_mon n (pmon2 (S n) c) (pmon2 (S n) b))
              (pmon2 (S n) b))) :>mon n) in |- *; auto.
2: rewrite <- H'1; auto.
rewrite Nat.sub_add; auto.
rewrite <- (proj_ok n c); auto.
apply Nat.max_case; auto.
apply plus_minus_le; auto.
change
  (pmon1 (S n)
     (c_n n (pmon1 (S n) c - pmon1 (S n) a + pmon1 (S n) a)
        (mult_mon n (div_mon n (pmon2 (S n) c) (pmon2 (S n) a))
           (pmon2 (S n) a))) = pmon1 (S n) c :>nat) 
 in |- *; auto.
rewrite <- H'0; auto.
apply plus_minus_le; auto.
change
  (pmon1 (S n)
     (c_n n (pmon1 (S n) c - pmon1 (S n) b + pmon1 (S n) b)
        (mult_mon n (div_mon n (pmon2 (S n) c) (pmon2 (S n) b))
           (pmon2 (S n) b))) = pmon1 (S n) c :>nat) 
 in |- *; auto.
rewrite <- H'1; auto.
Qed.

End Monomials.
