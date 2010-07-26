(*
Damned CoqIde hate that:

Set Printing Universes.
*)

(*******************************************)
(* Code and interpretation of Descriptions *)
(*******************************************)

Inductive Desc : Type := 
    Id : Desc
  | Const : Type -> Desc
  | Prod : Desc -> Desc -> Desc
  | Sigma : forall s : Type, (s -> Desc) -> Desc
  | Pi : forall s : Type, (s -> Desc) -> Desc.

(* To check universes: *)
Print Desc.
Print Universes.
(* Desc : Type_1 *)

Fixpoint descOp (D : Desc)(X : Type){struct D} : Type :=
    match D with
    | Id => X
    | Const K => K
    | Prod D D' => { x : descOp D X & descOp D' X }
    | Sigma s T => { x : s & descOp (T x) X }
    | Pi s T => forall x : s, descOp (T x) X
end.

Print descOp.
Print Universes.
(* descOp (D : Desc)(X : Type_0) : Type_0 *)

(*******************************************)
(*     Misc. predicates (ignore them)      *)
(*******************************************)

Definition isId (D : Desc) : bool :=
    match D with
     | Id => true
     | _  => false
end.

Definition isConst (D : Desc) : bool :=
    match D with
    | Const _ => true
    | _       => false
end.

Definition isProd (D : Desc) : bool :=
    match D with
    | Prod _ _ => true
    | _        => false
end.

Definition isSigma (D : Desc) : bool :=
    match D with
    | Sigma _ _ => true
    | _         => false
end.

Definition isPi (D : Desc) : bool :=
    match D with
    | Pi _ _ => true
    | _      => false
end.

Require Import Coq.Bool.Bool.

Definition ConstSet (D : Desc)(p : Is_true (isConst D)) : Type.
intro D.
case D; intros; try elim p.
    (* Case: D = Const P *)
    exact T.
Defined.

Definition ProdFst (D : Desc)(p : Is_true (isProd D)) : Desc.
intro D.
case D; try (intros; elim p; fail).
     (* Case: D = Prod d d0 *)
     intros D1 D2 _.
     exact D1.
Defined.

Definition ProdSnd (D : Desc)(p : Is_true (isProd D)) : Desc.
intro D.
case D; try (intros; elim p; fail).
     (* Case: D = Prod D1 D2 *)
     intros D1 D2 _.
     exact D2.
Defined.

Definition SigmaHd (D : Desc)(p : Is_true (isSigma D)) : Type.
intro D.
case D; intros; try elim p.
   (* Case: D = Sigma s d *)
   exact s.
Defined.

Definition SigmaTl (D : Desc)(p : Is_true (isSigma D))(s : SigmaHd D p) : Desc.
intro D.
case D; try (intros; elim p; fail).
    (* Case: D = Sigma s d *)
    intros s d p.
    case p.
    intro x.
    exact (d x).
Defined.

Definition PiHd (D : Desc)(p : Is_true (isPi D)) : Type.
intro D.
case D; intros; try elim p.
   (* Case: D = Pi s d *)
   exact s.
Defined.

Definition PiTl (D : Desc)(p : Is_true (isPi D))(s : PiHd D p) : Desc.
intro D.
case D; try (intros; elim p; fail).
    (* Case: D = Pi s d *)
    intros s d p.
    case p.
    intro x.
    exact (d x).
Defined.



(*******************************************)
(*         Fix-point, a la Matthes         *)
(*******************************************)


(*
Inductive Mu (D : Desc) : Type :=
    con : descOp D (Mu D) -> Mu D.
*)

Inductive MuU (R : Desc)(D : Desc) : Type :=
    id : forall p : Is_true (isId D),
         MuU R R -> MuU R D
  | const : forall p : Is_true (isConst D),
            ConstSet D p -> MuU R D
  | prod : forall p : Is_true (isProd D),
           { x : MuU R (ProdFst D p) & MuU R (ProdSnd D p)} ->
           MuU R D
  | sigma : forall p : Is_true (isSigma D),
            { s : SigmaHd D p & MuU R (SigmaTl D p s)} -> 
            MuU R D
  | pi : forall p : Is_true (isPi D),
         (forall s : PiHd D p, MuU R (PiTl D p s)) ->
         MuU R D
.

Definition Mu (D : Desc) : Type := MuU D D.

Print Mu.
Print Universes.
(* Mu : Desc -> Type_0 *)

(*******************************************)
(*            Levitation!                  *)
(*******************************************)


Inductive DescChoice : Set :=
    CId : DescChoice
  | CConst : DescChoice
  | CProd : DescChoice
  | CSigma : DescChoice
  | CPi : DescChoice
.

Definition DescCases : DescChoice -> Desc.
intro choice.
induction choice.
    (* Case: D = Id *)
    exact (Const unit).

    (* Case: D = Const K *)
    exact (Sigma Type (fun _ => Const unit)).

    (* Case: D = Prod D1 D2 *)
    exact (Prod Id Id).

    (* Case: D = Sigma s d *)
    exact (Sigma Type (fun S => Pi S (fun _ => Id))).

    (* Case: D = Pi s d *)
    exact (Sigma Type (fun S => Pi S (fun _ => Id))).
Defined.

Definition DescD : Desc := Sigma DescChoice DescCases.

Print DescD.
(* DescD : Desc *)

Definition Desc' : Type := Mu DescD.

Print Desc'.
Print Universes.
(* Desc' : Type_1 *)


