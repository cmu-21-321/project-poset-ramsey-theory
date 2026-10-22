import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Subset
import Mathlib.Combinatorics.Digraph.Basic


/-!
This creates a subset digraph under inclusion.
Vertices are elements of P(n).
-/

abbrev vertex (n : ℕ) := Finset (Fin n)
abbrev Coloring (k : ℕ) (V : Type) : Type := V → (Fin k)
def relation {n : ℕ} (v1 v2 : vertex n) : Prop :=  v1 ⊂ v2


def Q (n : ℕ) : Digraph (vertex n) where --Q is big graph.
  Adj s t := relation s t


def singleton (n : ℕ) := Finset.powersetCard 1 (Finset.univ : Finset (Fin n))


def diamondVertices (n : ℕ) : Finset (Finset (Fin n)) :=
  Finset.powersetCard 0 (Finset.univ : Finset (Fin n)) ∪
  Finset.powersetCard 1 (Finset.univ : Finset (Fin n)) ∪
  Finset.powersetCard n (Finset.univ : Finset (Fin n))
def D (n : ℕ) : Digraph (diamondVertices n) where --D are diamonds
  Adj s t := relation s.1 t.1


--We will define the Qn graphs.

--H ⊆ G, and H has one color.
def MonochromeSubgraph {V : Type} {k : ℕ} (G H : Digraph V) (χ : Coloring k V) : Prop :=
  (∀ u v, H.Adj u v → G.Adj u v) ∧ (∀u v, H.Adj u v → χ u = χ v)
