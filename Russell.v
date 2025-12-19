Require Import Coq.Program.Equality.

(* Use Type in Type. *)
Unset Universe Checking.

(* We can use a predictor to encode a subset of some type. so that (a in A) iff (A a) holds. *)
Definition set (A : Type) := A -> Type. 

(* The V type can be seen as a type of all sets.  *)
Definition V := { A : Type & set A }.
Definition mkV (A : Type) (P : set A ) : V := existT _ A P.

Module UseUIP.
  
(* We are using ITT, we don't need this in ETT *)
Definition transp {A B : Type} (eq : A = B) (a : A) : B := match eq with eq_refl => a end.
(* Prove this type derived reduction requires UIP. *)
Axiom transp_eq : forall {A : Type} (a : A) (eq : A = A), transp eq a = a. 

(* 
Inductive Elem {A : Type} : A -> V -> Type := 
  mk : forall (P : set A) (a : A), P a -> Elem a (mkV A P). 

  Fording this inductive defintion. *)
Definition Elem (A : Type) (a : A) (s : V) : Type := 
  { eq : A = projT1 s & projT2 s (transp eq a) }.

Definition ElemV := Elem V.

(* Russell's set : R := {x | x not in x} *)
Definition R : V := mkV V (fun x => ~ ElemV x x).

(* Rest is easy. *)
Theorem nRinR : ~ ElemV R R.
Proof.  
  intro H.
  pose proof H as H1.
  destruct H as [eq H].
  simpl in eq, H.
  apply H.
  rewrite transp_eq.
  assumption.
Qed.

Theorem RinR : ElemV R R.
Proof.
  simpl.
  exists eq_refl.
  apply nRinR.
Qed.
  
Theorem Boom: False.
Proof.
  apply nRinR.
  apply RinR.
Qed.

End UseUIP.


(* Use inductive type, no need UIP. *)
Module UseInductive.
  
Inductive Elem {A : Type} : A -> V -> Type := 
  mk : forall (P : set A) (a : A), P a -> Elem a (mkV A P). 

Definition ElemV := @Elem V.

(* Russell's set : R := {x | x not in x} *)
Definition R : V := mkV V (fun x => ~ ElemV x x).

Theorem nRinR : ~ ElemV R R.
Proof.
  intro H.
  inversion H.
  subst a.
  dependent induction H2. (* this use JMeq *)
  auto.
Qed.

Theorem RinR : ElemV R R.
Proof.
  simpl.
  constructor.
  apply nRinR.
Qed.

End UseInductive.
