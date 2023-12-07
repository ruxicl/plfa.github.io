---
title     : "Planarity: Formalising planar graphs"
permalink : courses/TSPL/2023/Essay/planarity.lagda.md
---

## Ruxandra Icleanu, s2011447@.ed.ac.uk


```
module project.planarity where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; sym; trans; cong; _≢_)
  open import Relation.Binary.Definitions using (DecidableEquality)
  
  open import Data.Nat using (ℕ; _≟_)
  
  open import Data.List using (List; _∷_; []; _++_)
  open import Data.List.Relation.Unary.Any using (Any; here; there)
  open import Data.List.Membership.Propositional using (_∈_)
  open import Data.String using (String)
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Data.Product
    using (_×_; proj₁; proj₂; ∃; ∃-syntax)
    renaming (_,_ to ⟨_,_⟩)
  
```

## Introduction

A planar graph is a graph that can be drawn in the plane without any
crossings, that is no two edges intersect except at a vertex they are
incident with. We call such a drawing a plane drawing.

For example, the complete graph (i.e. the graph in which any two vertices
are connected) with 4 vertices (known as K₄) can be drawn in the plane in
multiple ways:

![K4-1](graph1.png)
![K4-2](graph2.png)

We note that only the second drawing is a plane drawing, and so K₄
is a planar graph.

In what follows, we want to develop a definition of planar graphs based on
"Formalization of Planar graphs" by H. Yamamoto et. al (with substantial changes -
the paper uses HOL, a higher-order logic theorem proving system). The approach
we will consider is based on the key observation that (as it will be explained later,
a very wide class of) planar graphs can be constructed in an inductive fashion starting
from a cycle which is clearly planar, and carefully adding sequences of edges.

We also briefly discuss other approaches. 

To show the validity of our definition, we want to prove Euler's formula.


## Preliminaries

We will restrict our attention to a specific (but common) type of graphs, namely
2-connected graphs, i.e. graphs that remain connected after the removal of any one vertex.

The following theorem from [4] proves that esthablishing a criterion for this type of graph will immediately lead to a criterion for a general graph.

Theorem: A graph is planar if and only if its 2-connected (or biconnected) components are planar.

We will assume that any graph mentioned from now on is 2-connected, unless otherwise specified.


## Circular lists
We first develop a theory of cycles.

```agda
  pattern [_] z = z ∷ []
  pattern [_,_] y z = y ∷ z ∷ []
  pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
```

-- goal: define a circular list

  ```agda

  deleteEdge : List (ℕ × ℕ) → (ℕ × ℕ) → List (ℕ × ℕ)
  deleteEdge [] _ = []
  deleteEdge (⟨ a , b ⟩ ∷ xs) ⟨ c , d ⟩ with a ≟ c | b ≟ d
  ... | yes _ | yes _ = deleteEdge xs ⟨ c , d ⟩
  ... | _     | _     = ⟨ a , b ⟩ ∷ deleteEdge xs ⟨ c , d ⟩

  _ : deleteEdge [ ⟨ 1 , 1 ⟩ ] ⟨ 1 , 1 ⟩ ≡ []
  _ = refl

  _ : deleteEdge [ ⟨ 1 , 1 ⟩ ] ⟨ 1 , 2 ⟩ ≡ [ ⟨ 1 , 1 ⟩ ]
  _ = refl

  -- it's sufficient to check if v appears in the first component

  -- can you add condition that cycle is indeed cycle? or

  -- isVertexNotInCycle : ℕ → List (ℕ × ℕ) → Set
  -- isVertexNotInCycle v cycle = (w : ℕ) → ¬ (⟨ v , w ⟩ ∈ cycle)

  isVertexNotInCycle : ℕ → List ℕ → Set
  isVertexNotInCycle v elemOfCycle = ¬ (v ∈ elemOfCycle)


  -- but you should use these just for cycles?
  -- cycDom
  cycleElem : List (ℕ × ℕ) → List ℕ
  cycleElem [] = []
  cycleElem (⟨ a , b ⟩ ∷ xs) = a ∷ cycleElem xs
  
  

  _ : cycleElem [ ⟨ 1 , 2 ⟩ , ⟨ 2 , 1 ⟩ ] ≡ [ 1 , 2 ]
  _ = refl

  -- CYC_DOM from the paper
  

  -- a cycle is a list of pairs representing edges
  
  -- predicate that checks if something is a cycle

  data isCycle : List (ℕ × ℕ)  → Set where
    self-loop : ∀ (x : ℕ) → isCycle [ ⟨ x , x ⟩ ]
    insert-vertex : ∀ (x y z : ℕ) (s : List (ℕ × ℕ))
      → isCycle s
      → ⟨ x , z ⟩ ∈ s
      → isVertexNotInCycle y (cycleElem s) -- need to change cycleElem
      -- final version is cycleElem' which needs to have datatype Cycle defined
      → isCycle (deleteEdge s ⟨ x , z ⟩ ++ [ ⟨ x , y ⟩ , ⟨ y , z ⟩ ])


  data Cycle : Set where
    makeCycle : (c : List (ℕ × ℕ)) → isCycle c → Cycle

  cycle1 : Cycle
  cycle1 = makeCycle [ ⟨ 2 , 2 ⟩ ] (self-loop 2)

  cycleElem' : Cycle → List ℕ
  cycleElem' (makeCycle c cIsCycle) = getElem c
    where
      getElem : List (ℕ × ℕ) → List ℕ
      getElem [] = []
      getElem (⟨ a , b ⟩ ∷ xs) = a ∷ getElem xs
  

  -- FORW
  -- vertex of a cycle
  
  -- add an extra argument to check x is one of the elem of c

  isElemInCycle : Cycle → ℕ → Set
  isElemInCycle cycle x = x ∈ (cycleElem' cycle) 

  nextElem : (cycle : Cycle) → (x : ℕ) → ℕ
  nextElem (makeCycle c cIsCycle) x  = findElem c x
    where
      findElem : List (ℕ × ℕ) → ℕ → ℕ
      findElem [] x = 0
      findElem (⟨ a , b ⟩ ∷ xs) x with a ≟ x
      ... | yes _ = b
      ... | no  _ = findElem xs x

  _ : nextElem cycle1 2 ≡ 2
  _ = refl


  -- CYC-CONTRACT
  -- contractCycle 

  -- CYC_BASE = self-loop
  -- CYC-INSERT = add-vertex
  
   

-- we represent them as lists but the order should not matter? or it matters but they should be circular
-- alternatives: finite sets, partial maps (see sltc chapter from Software Foundations)
    
  ```

We can prove the validty of the following cycle [insert picture]
Since we can construct it. This is similar to the story of creation of naturals.

From a given set of vertices, we get the following.

We need to equality in a smart way so [⟨ 1 , 2 ⟩ , ⟨ 2 , 3 ⟩ , ⟨ 3 , 1 ⟩ ] is equal to
[ ⟨ 2 , 3 ⟩ , ⟨ 3 , 1 ⟩ , ⟨ 1 , 2⟩ ]


-- we could define edges as functions instead of pairs
-- see ex. from Lambda "show that Context is isomorphic to List (Id × Type)"


```agda

  _ : [] ++ [ 1 ] ≡ [ 1 ]
  _ = refl

  _ : [] ≡ []
  _ = refl { A = List (ℕ × ℕ) }

```

```agda
  _ : isCycle [ ⟨ 1 , 1 ⟩ ]
  _ = (self-loop 1)

  _ : deleteEdge [ ⟨ 1 , 1 ⟩ ] ⟨ 1 , 1 ⟩ ≡ []
  _ = refl

  -- need to define equality for sigma types _≟Σ_

  _ : [ 1 ] ++ [ 2 , 3 ] ≡ [ 1 , 2 , 3 ]
  _ = refl

  _ : [ ⟨ 1 , 2 ⟩ ] ++ [ ⟨ 2 , 4 ⟩  ] ≡  [ ⟨ 1 , 2 ⟩ , ⟨ 2 , 4 ⟩ ]
  _ = refl { A = List (ℕ × ℕ) }

  _ :  [ ⟨ 1 , 2 ⟩ ] ≡ [ ⟨ 1 , 2 ⟩ ]
  _ = refl { A = List (ℕ × ℕ) }

  _ : 1 ∈ [ 1 , 2 ]
  _ = here refl

  -- _∈-×_ : ∀ {A : Set} (x : A) (xs : List A) → Set
  -- x ∈ xs = Any (x ≡_ {A = List (ℕ × ℕ)}) xs

  _ :  ⟨ 1 , 1 ⟩ ∈ [ ⟨ 1 , 1 ⟩ ]
  _ = here (refl { A = ℕ × ℕ })

  not-in : isVertexNotInCycle 2  [ 1 ]
  not-in (here ())
  not-in (there ())
  

  cycle2IsCycle : isCycle [ ⟨ 1 , 2 ⟩ , ⟨ 2 , 1 ⟩ ]
  cycle2IsCycle = insert-vertex 1 2 1 [ ⟨ 1 , 1 ⟩ ] (self-loop 1)
                                  ( here (refl { A = ℕ × ℕ }) ) (not-in)

  cycle2 : Cycle
  cycle2 = makeCycle [ ⟨ 1 , 2 ⟩ , ⟨ 2 , 1 ⟩ ] cycle2IsCycle

  _ : cycleElem' cycle2 ≡ [ 1 , 2 ]
  _ = refl

```


- discussion about how to define equality of different structures

- define face
- define infinite face - note: any face can choosen to be the infinite face

We define a plane drawing of a graph to be a quadruple: the set of vertices, the set of edges, the set of faces, and the infinite face

We f

-- define cycle equality


```agda
  areEdgesEq : (c c′ : Cycle) → Set
  areEdgesEq c c′ = (x : ℕ) → (x ∈ cycleElem' c → nextElem c x ≡ nextElem c′ x)
  
  -- _≡C_ (c c′ : Cycle) : Set where
  --  refl-C : cycleElem' c ≡ cycleElem' c′ → areEdgesEq c c′ → c ≡C c′
```
  

## Inductive definition

```agda
  record Graph : Set where
    constructor graph
    field
      vertices : List ℕ
      edges : List (ℕ × ℕ)
      regions : List Cycle
      outerRegion : Cycle
```

  data isPlanar : Graph → Cycle → Set
    base-case : ∀ (g : Graph) (c : Cycle) → vertices ≡ cycleElem' c → isPlanar g c

 

```agda
{-
  record Graph : Set₁ where
    field
      vertices : Set
      edges : Set
-}
```

```agda
{-
  record PlaneDrawing : Set₁ where
    field
      vertices : Set
      edges : Set
      faces : Set
      infiniteFace : Set
-}
```

We define a face to be a circular (cyclic) list of vertices.

We define a predicate as following

```agda
  -- data isPlanar : ∀ (G : PlaneDrawing) → Set
  -- isPlanar G record {vertices = vertices; edges = edges; faces = faces; infiniteFace = infiniteFace } = 
```


## Topological graph theory
This section is based on "Planar graphs in Homotopy type theory" - J. Prieto-Cuibides

Simple and undirected graphs


We define two predicates.

-- these def are from the Hott book


```agda
{-

  -- there is a unique term of type A
  isProp : ∀ (A : Set) → Set
  -- unimath uses Id instead of ≡
  isProp A = (x y : A) → (Id x y)

  -- two elements of a set are equal in just one way
  isSet : ∀ (A : Set) → Set
  isSet A = {x y : A} (p q : Id x y) → (Id p q)
-}
```

```agda
  -- data vs record - which one to use?
{-
  record Graph′ : Set₁ where
    field
      vertex : Set
      edge : vertex → vertex → Set
      vertices-form-set : (isSet vertex)
      no-multiple-edges : (x y : vertex) → isProp (edge x y)
      undirected-edges : (x y : vertex) → (edge x y)
-}
```

```agda
  -- data ClassicSet : List (ℕ × ℕ)
    

  {--
  data isCycle : List (ℕ × ℕ)  → Set where
    self-loop : ∀ (x : ℕ) → isCycle [ ⟨ x , x ⟩ ]
    add-vertex : ∀ (x y z : ℕ) (s : List (ℕ × ℕ))
      → isCycle s
      → ⟨ x , z ⟩ ∈ s
      → isVertexNotInCycle y [ 1 ]
      → isCycle (deleteEdge s ⟨ x , z ⟩ ++ [ ⟨ x , y ⟩ , ⟨ y , z ⟩ ])
  --}

```

## Future work

The most recent version of this is can be found [here](https://github.com/ruxicl/plfa.github.io/tree/tspl-project/courses/TSPL/2023/Essay).

To do:
- vertices have type ℕ, but might want to change to String


## References

[1] On Planarity of Graphs in Homotopy Type Theory - Jonathan Prieto-Cubides, Hakon Robbestad Gylterud

[2] Formalization of Planar Graphs - Mitsuharu Yamamoto, Shin-ya Nishizaki, Masami Hagiya, and Yozo Toda

[3] Introduction to graph theory (5th edition) - Robin J. Wilson

[4] J. E. Hopcroft and R. E. Tarjan. Efficient planarity testing. J. ACM, 21(4):549–568, 1974.
