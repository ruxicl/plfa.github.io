---
title : "Planarity: Formalising planar graphs"
---

```agda
module planarity where
  open 
```

[introduction about planairity]

## Inductive definition

This is based on "Formalization of Planar graphs" - Yamamoto

```agda

```


## Topological graph theory
This section is based on "Planar graphs in Homotopy type theory" - J. Prieto-Cuibides

Simple and undirected graphs


We define two predicates.

```agda
  isProp ∀ (A : Set) → Set
  isProp A = ((x y : A) → x ≡ y)
```

```agda
  -- data vs record - which one to use?
  record Graph : Set₁ where
    field
      Vertex : Set
      Edge : Vertex → Vertex → Set
```
