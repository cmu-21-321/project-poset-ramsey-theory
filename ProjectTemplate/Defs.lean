import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Subset

def vertex (n : ℕ) := Finset (Fin n)
def relation {n : ℕ} (v1 v2 : vertex n) : Prop :=  ∀(x ∈ v1) (x ∈ v2)

--We will define the Qn graphs.
