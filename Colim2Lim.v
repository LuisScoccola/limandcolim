Require Import HoTT.
Require Import Definitions.

Context (G : graph).


(*
  given a diagram [D] and a type [A] we construct the diagram [hom(D,A)]
*)

Definition representable_apply_diag
               (D : diagram G) (A : Type) :
                 diagram (reverse_graph G).
Proof.
  set (cg_diag_0 (i: reverse_graph G) := D i -> A).
  exists cg_diag_0.
  intros i j f.
  exact (fun g => g o ((diagram1 D) j i f)).
Defined.

(*
  given a cocone [X] over [D] and a type [A] we get a cone [hom(X,A)]
  over [hom(D,A)].
  For this we need funext (right?).
*)
Definition representable_apply_cone `{Funext}
             {D : diagram G}
               (C : Type) (c : graph_cocone D C) (A : Type) :
                 graph_cone (representable_apply_diag D A) (C -> A).
Proof.
  exists (fun i h =>  h o (graph_cocone_pr1 c i)).
  intros.
  intro x.
  refine (path_arrow _ _ _).
  intro. simpl.
  set (happ := (graph_cocone_pr2 c f)).
  exact (ap x (happ x0)).
Defined.


(*
  Given a diagram [D] and two types [L] and [A],
  there is an equivalence  [(L -> CoCone(D,A)) ~ Cone(hom(D,A),L)]
  given by the following map
*)
Definition coconetocone `{Funext}
             (D : diagram G) (A L : Type) :
                 (L -> graph_cocone D A) ->
                   graph_cone (representable_apply_diag D A) L.
Proof.
  intro.
  exists (fun i l => graph_cocone_pr1 (X l) i).
  intros.
  intro l.
  refine (path_arrow _ _ _).
  exact (graph_cocone_pr2 (X l) f).
Defined.


(* we can go back *)
Definition conetococone
             (D : diagram G) (A L : Type) :
                 graph_cone (representable_apply_diag D A) L ->
                   (L -> graph_cocone D A).
Proof.
  intros X l.
  exists (fun i => graph_cone_pr1 X i l).
  intros.
  exact (happly (graph_cone_pr2 X f l)).
Defined.


(* and this is an equivalence *)
Definition isEquiv_conetococone `{Funext}
             (D : diagram G) (A L : Type) :
               IsEquiv (conetococone D A L).
Proof.
  refine (isequiv_adjointify (conetococone D A L) (coconetocone D A L) _ _).
    intro.
    refine (path_arrow _ _ _).
    intro l.
    refine (path_sigma _ _ _ _ _).
      Unshelve. Focus 3. trivial.
    do 3 (refine (path_forall _ _ _) ; intro).
    refine (path_forall _ _ _).
    refine (ap10_path_arrow _ _ _).

    intro.
    refine (path_sigma _ _ _ _ _).
      Unshelve. Focus 2. trivial.
    refine (path_forall _ _ _).
    do 3 (intro ; refine (path_forall _ _ _)).
    intro. refine (eta_path_forall _ _ _).
Defined.

Definition isEquiv_coconetocone `{Funext}
             (D : diagram G) (A L : Type) :
               IsEquiv (coconetocone D A L).
Proof.
  refine (isequiv_adjointify (coconetocone D A L) (conetococone D A L) _ _).
    intro.
    refine (path_sigma _ _ _ _ _).
      Unshelve. Focus 3. trivial.
    repeat (refine (path_forall _ _ _) ; intro).
    refine (eta_path_forall _ _ _).
 
    intro.
    refine (path_arrow _ _ _).
    intro l.
    refine (path_sigma _ _ _ _ _).
      Unshelve. Focus 2. trivial.
    refine (path_forall _ _ _).
    repeat (intro ; refine (path_forall _ _ _)).
    refine (ap10_path_arrow _ _ _).
Defined.

(*
  by post composition with the cocone of [C] we have a map
  [(L -> hom(C,A)) -> (L -> CoCone(D,A))]
*)
Definition postcompose_with_cocone
             {D : diagram G} {C : Type}
               (c : graph_cocone D C) (A L : Type) :
                 (L -> C -> A) -> (L -> graph_cocone D A)
:= fun f => (map_to_graph_cocone c A) o f. 


(* and if [C] is a colimit, then this is an equivalence *)
Definition isEquiv_postcompose_with_cocone `{Funext}
             {D : diagram G} {C : Type} {c : graph_cocone D C}
               (lc : is_colimit_cocone c) (A L : Type) :
                 IsEquiv (postcompose_with_cocone c A L).
Proof.
  set (the_equivalence := lc A).
  exact (isequiv_postcompose (map_to_graph_cocone c A)).
Defined.


(*
  [map_to_graph_cone] factors through the equivalence [conetococone]
*)
Definition map_to_graph_cone_factors_conetococone `{Funext}
             {D : diagram G} {C : Type}
               (c : graph_cocone D C) (A : Type) (L : Type) :
                   (coconetocone D A L) o (postcompose_with_cocone c A L) =
                     (map_to_graph_cone (representable_apply_cone C c A) L).
Proof.
  refine (path_arrow _ _ _).
  intro.
  refine (path_sigma _ _ _ _ _).
    Unshelve. Focus 2. trivial.
  repeat (refine (path_forall _ _ _) ; intro).
  trivial.
Defined.


(*
  given a *limit* cocone [X] over [D] and a type [A], we get a limit cone [hom(X,A)]
  over [hom(D,A)]. i.e. hom(-,A) maps limits to colimits
*)

Definition homisexact `{Funext}
             {D : diagram G} {C : Type}
               (c : graph_cocone D C) (cl : is_colimit_cocone c) (A : Type) :
                 is_limit_cone (representable_apply_cone C c A).
Proof.
  intro L.
  refine (isequiv_homotopic _ _).
  set (equiv1 := isEquiv_postcompose_with_cocone cl A L).
  set (equiv2 := isEquiv_coconetocone D A L).
  refine (isequiv_compose' (postcompose_with_cocone c A L) equiv1 (coconetocone D A L) equiv2 ).
  intro f.
  exact (happly (map_to_graph_cone_factors_conetococone c A L) f).
 Defined.
