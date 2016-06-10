Require Import HoTT.


(*
  These definitions are taken from [ github.com/peterlefanulumsdaine/hott-limits.git ]
  and dualized.
  Authors: Jeremy Avigad, Krzysztof Kapulkin, Peter LeFanu Lumsdaine.
*)


(* graph *)
Record graph :=
  { graph0 :> Type;
    graph1 :> graph0 -> graph0 -> Type }.


(* graph^op *)
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



(* limit *)
Definition map_to_graph_cone {G : graph} {D : diagram G}
  {X} (C : graph_cone D X) (Y:Type) (f : Y -> X)
: graph_cone D Y.
Proof.
  exists (fun i y => C i (f y)).
  intros i j a y. apply (graph_cone_pr2 C).
Defined.


(* limit def *)
Definition is_limit_cone {G : graph} {D : diagram G} {L} (C : graph_cone D L)
:= forall (X : Type), IsEquiv (map_to_graph_cone C X).


(* colimit *)
Definition map_to_graph_cocone {G : graph} {D : diagram G}
  {X} (C : graph_cocone D X) (Y:Type) (f : X -> Y)
: graph_cocone D Y.
Proof.
  exists (fun i d => f (C i d)).
  intros i j a x.
  exact (ap f (graph_cocone_pr2 C a x)).
Defined.                                                                     


(* colimit def *)
Definition is_colimit_cocone {G : graph} {D : diagram G} {L} (C : graph_cocone D L)
:= forall (X : Type), IsEquiv (map_to_graph_cocone C X).