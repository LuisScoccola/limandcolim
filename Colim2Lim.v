Require Import HoTT.

(* The definitions [todo: which ones] in this file are due to [todo: who] *)

(* graph *)
Record graph :=
  { graph0 :> Type;
    graph1 :> graph0 -> graph0 -> Type }.


(* reverse graph *)
Definition reverse_graph (G : graph) : graph.
Proof.
  set (graph0' := graph0 G).
  exists graph0'.
  exact (fun i j => (graph1 G) j i).
Defined.


(* diagram over graph *)
Record diagram (G : graph) :=
  { diagram0 :> G -> Type;
    diagram1 : forall (i j : G), G i j -> (diagram0 i -> diagram0 j) }.

Global Arguments diagram0 [G] D i : rename.
Global Arguments diagram1 [G] D [i j] f x : rename.

Notation "D .1" := (@diagram1 _ D _ _) (at level 3).


(* cone over diagram *)
Definition graph_cone {G : graph} (D : diagram G) (X : Type)
:= { tau : forall i : G, X -> D i
     & forall (i j : G) (f : G i j), (D.1 f o tau i) == tau j }.


Definition mk_graph_cone {G : graph} {D : diagram G} {X} tau tau1 : graph_cone D X
:= existT _ tau tau1.


Definition graph_cone_pr1 {G : graph} {D : diagram G} {X} (tau : graph_cone D X)
  := pr1 tau.
Coercion graph_cone_pr1 : graph_cone >-> Funclass.


Definition graph_cone_pr2 {G : graph} {D : diagram G} {X} (tau: graph_cone D X)
  {i j} (f : G i j) (x:X)
:= pr2 tau i j f x.


(*cocone over diagram*)
Definition graph_cocone {G : graph} (D : diagram G) (X : Type)
:= { tau : forall i : G, D i -> X
     & forall (i j : G) (f : G i j), (tau j o D.1 f) == tau i }.


Definition mk_graph_cocone {G : graph} {D : diagram G} {X} tau tau1 : graph_cocone D X
:= existT _ tau tau1.


Definition graph_cocone_pr1 {G : graph} {D : diagram G} {X} (tau : graph_cocone D X)
  := pr1 tau.
Coercion graph_cocone_pr1 : graph_cocone >-> Funclass.


Definition graph_cocone_pr2 {G : graph} {D : diagram G} {X} (tau: graph_cocone D X)
  {i j} (f : G i j) (x:D i)
:= pr2 tau i j f x.


(*
  given a diagram [D] and a type [A] we construct the diagram [hom(D,A)]
*)

Definition representable_apply_diag {G : graph} (D : diagram G) (A : Type) : diagram (reverse_graph G).
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
Definition representable_apply_cone `{Funext} {G : graph} {D : diagram G} (C : Type) (c : graph_cocone D C)
             (A : Type) : graph_cone (representable_apply_diag D A) (C -> A).
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
Definition coconetocone `{Funext} {G : graph} {D : diagram G} {A L : Type} :
                          (L -> graph_cocone D A) -> graph_cone (representable_apply_diag D A) L.
Proof.
  intro.
  exists (fun i l => graph_cocone_pr1 (X l) i).
  intros.
  intro l.
  refine (path_arrow _ _ _).
  exact (graph_cocone_pr2 (X l) f).
Defined.


(* we can go back *)
Definition conetococone {G : graph} {D : diagram G} {A L : Type} :
                          graph_cone (representable_apply_diag D A) L -> (L -> graph_cocone D A).
Proof.
  intros X l.
  exists (fun i => graph_cone_pr1 X i l).
  intros.
  exact (happly (graph_cone_pr2 X f l)).
Defined.


(* and this is an equivalence *)
Definition isEquiv_conetococone `{Funext} {G : graph} {D : diagram G} {A L : Type} :
                                IsEquiv (@conetococone G D A L).
Proof.
  refine (isequiv_adjointify conetococone coconetocone _ _).
    intro.
    refine (path_arrow _ _ _).
    intro l.
    refine (path_sigma _ _ _ _ _).
      Unshelve. Focus 3. trivial.
    refine (path_forall _ _ _).
    intro. refine (path_forall _ _ _).
    intro. refine (path_forall _ _ _).
    intro. refine (path_forall _ _ _).
    refine (ap10_path_arrow _ _ _).

    intro.
    refine (path_sigma _ _ _ _ _).
      Unshelve. Focus 2. trivial.
    refine (path_forall _ _ _).
    intro. refine (path_forall _ _ _).
    intro. refine (path_forall _ _ _).
    intro. refine (path_forall _ _ _).
    intro. refine (eta_path_forall _ _ _).
Defined.


Definition map_to_graph_cone {G : graph} {D : diagram G}
  {X} (C : graph_cone D X) (Y:Type) (f : Y -> X)
: graph_cone D Y.
Proof.
  exists (fun i y => C i (f y)).
  intros i j a y. apply (graph_cone_pr2 C).
Defined.


(* limit *)
Definition is_limit_cone {G : graph} {D : diagram G} {L} (C : graph_cone D L)
:= forall (X : Type), IsEquiv (map_to_graph_cone C X).


Definition map_to_graph_cocone {G : graph} {D : diagram G}
  {X} (C : graph_cocone D X) (Y:Type) (f : X -> Y)
: graph_cocone D Y.
Proof.
  exists (fun i d => f (C i d)).
  intros i j a x.
  exact (ap f (graph_cocone_pr2 C a x)).
Defined.                                                                     


(* colimit *)
Definition is_colimit_cocone {G : graph} {D : diagram G} {L} (C : graph_cocone D L)
:= forall (X : Type), IsEquiv (map_to_graph_cocone C X).


(*
  by post composition with the cocone of [C] we have a map
  [(L -> hom(C,A)) -> (L -> CoCone(D,A))]
*)
Definition postcompose_with_cocone {G : graph} {D : diagram G} {C : Type}
                                   (c : graph_cocone D C) {A L : Type} :
                                   (L -> C -> A) -> (L -> graph_cocone D A)
:= fun f => (map_to_graph_cocone c A) o f. 


(* and if [C] is a colimit, then this is an equivalence *)
Definition isEquiv_postcompose_with_cocone `{Funext}
                                           {G : graph} {D : diagram G} {C : Type}
                                           {c : graph_cocone D C} {lc : is_colimit_cocone c}
                                           {A L : Type} :
                                           IsEquiv (@postcompose_with_cocone G D C c A L).
Proof.
  set (the_equivalence := lc A).
  exact (isequiv_postcompose (map_to_graph_cocone c A)).
Defined.


(*
  [map_to_graph_cone] factors through the equivalence [conetococone]
*)
Definition map_to_graph_cone_factors_conetococone `{Funext}
             {G : graph} {D : diagram G} {C : Type}
             {A : Type} {c : graph_cocone D C} (L : Type) :
               coconetocone o (postcompose_with_cocone c) =
                 (map_to_graph_cone (representable_apply_cone C c A) L).
Proof.
  refine (path_arrow _ _ _).
  intro.
  refine (path_sigma _ _ _ _ _).
    Unshelve. Focus 2. trivial.
  refine (path_forall _ _ _). intro.
  refine (path_forall _ _ _). intro.
  refine (path_forall _ _ _). intro.
  refine (path_forall _ _ _). intro.
  trivial.
Defined.


(*
  given a *limit* cocone [X] over [D] and a type [A], we get a limit cone [hom(X,A)]
  over [hom(D,A)]. i.e. [-,A] maps limits to colimits
*)

Definition homisexact `{Funext}
           {G : graph} {D : diagram G} {C : Type}
           (c : graph_cocone D C) (cl : is_colimit_cocone c)
           (A : Type) : is_limit_cone (representable_apply_cone C c A).
Proof.
  intro L.
  refine (isequiv_homotopic _ _).
  set (equiv1 := @isEquiv_postcompose_with_cocone _ _ _ _ c A L).
  set (equiv2 := isEquiv_conetococone).
  exact (isequiv_compose ( ) ( ).
    Focus 2. trivial.
  set (the_equivalence := coconetocone o (postcompose_with_cocone c)).
