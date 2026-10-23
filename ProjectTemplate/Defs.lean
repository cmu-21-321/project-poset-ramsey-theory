import Mathlib.Order.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Basic

/-!
This creates the n-boolean cube as a poset under subset inclusion.
Vertices are elements of P(n).
-/

def BooleanLattice (n : ℕ) : Type := Finset (Fin n)

instance (n : ℕ) : PartialOrder (BooleanLattice n) :=
  inferInstanceAs (PartialOrder (Finset (Fin n)))

/-
This sets up the n-diamond as a poset and proves that the relation satsifies the poset axioms.
Underlyingly, we are representing it as a set of n+2 elements, with 0 being the bottom and n+1 being
the top.
-/

def Diamond (n : ℕ) : Type := Fin (n + 2)

def DiamondOrder {n : ℕ} : Diamond n → Diamond n → Prop :=
  fun x y ↦ x.val = 0 ∨ y.val = n + 1 ∨ x.val = y.val

theorem DiamondRefl {n : ℕ} : ∀ (a : Diamond n), DiamondOrder a a := by
  intro a
  exact Or.inr (Or.inr (Fin.val_eq_of_eq (Eq.refl a)))

theorem DiamondTrans {n : ℕ} : ∀ (a b c : Diamond n),
    DiamondOrder a b → DiamondOrder b c → DiamondOrder a c := by
  sorry
  /- lots of casework, will do later -/

theorem DiamondAntisymm {n : ℕ} : ∀ (a b : Diamond n),
    DiamondOrder a b → DiamondOrder b a → a = b := by
  intro a b hab hba
  apply Fin.eq_of_val_eq
  rcases hab with abot | btop | equal
  · rcases hba with bbot | atop | equal
    · rw [abot, bbot]
    · rw [abot] at atop
      trivial
    · rw [equal]
  · rcases hba with bbot | atop | equal
    · rw [btop] at bbot
      trivial
    · rw [btop, atop]
    · rw [equal]
  · rw [equal]

instance (n : ℕ) : PartialOrder (Diamond n) where
  le := DiamondOrder
  le_refl := DiamondRefl
  le_trans := DiamondTrans
  le_antisymm := DiamondAntisymm

def Coloring (k : ℕ) (V : Type) : Type := V → (Fin k)

def IsInducedCopy {P Q : Type} [PartialOrder P] [PartialOrder Q] (f : P → Q) : Prop :=
  ∀ (a b : P), a ≤ b ↔ f a ≤ f b

def HasMonochromeSubposet (P Q : Type) [PartialOrder P] [PartialOrder Q] (k : ℕ)
    (χ : Coloring k Q) : Prop :=
  ∃ (c : Fin k), ∃ (f : P → Q), IsInducedCopy f ∧ ∀ (x : P), χ (f x) = c
