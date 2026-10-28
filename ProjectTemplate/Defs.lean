import Mathlib.Order.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Basic
set_option linter.style.header false

/-!
This creates the n-boolean cube as a poset under subset inclusion.
Vertices are elements of P(n).
-/

def BooleanLattice (n : ℕ) : Type := Finset (Fin n)
instance (n : ℕ) : PartialOrder (BooleanLattice n) :=
  inferInstanceAs (PartialOrder (Finset (Fin n)))
instance (n : ℕ) : Fintype (BooleanLattice n) :=
  inferInstanceAs (Fintype (Finset (Fin n)))

theorem BooleanLatticeCard (n : ℕ) : Fintype.card (BooleanLattice n) = 2 ^ n := by
  change Fintype.card (Finset (Fin n)) = 2 ^ n
  simp

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
  intro a b c hab hbc
  rcases hab with abot | btop | equal
  · exact Or.inl abot
  · rcases hbc with bbot | ctop | equal
    · rw [bbot] at btop
      trivial
    · exact Or.inr (Or.inl ctop)
    · rw [equal] at btop
      exact Or.inr (Or.inl btop)
  · unfold DiamondOrder
    rw [equal]
    exact hbc

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



--Wedges/Fans. Theorem about fan cardinality is included to make math easier.
def Wedge (n : ℕ) : Type := Fin (n + 1)
instance (n : ℕ) : Fintype (Wedge n) := inferInstanceAs (Fintype (Fin (n + 1)))

theorem WedgeCard (n : ℕ) : Fintype.card (Wedge n) = n + 1 :=
  Fintype.card_fin (n + 1)

def WedgeOrder {n : ℕ} : Wedge n → Wedge n → Prop :=
  fun x y ↦ y.val = n ∨ x.val = y.val

theorem WedgeRefl {n : ℕ} : ∀ (a : Wedge n), WedgeOrder a a := by
  intro a
  exact Or.inr (Fin.val_eq_of_eq (Eq.refl a))

theorem WedgeTrans {n : ℕ} : ∀ (a b c : Wedge n),
    WedgeOrder a b → WedgeOrder b c → WedgeOrder a c := by
  intro a b c hab hbc
  rcases hab with btop | equal
  · rcases hbc with ctop | equal
    · exact Or.inl ctop
    · rw [equal] at btop
      exact Or.inl btop
  · unfold WedgeOrder
    rw [equal]
    exact hbc

theorem WedgeAntisymm {n : ℕ} : ∀ (a b : Wedge n),
    WedgeOrder a b → WedgeOrder b a → a = b := by
  intro a b hab hba
  apply Fin.eq_of_val_eq
  rcases hab with btop | equal
  · rcases hba with atop | equal
    · rw [btop, atop]
    · rw [equal]
  · rw [equal]

instance (n : ℕ) : PartialOrder (Wedge n) where
  le := WedgeOrder
  le_refl := WedgeRefl
  le_trans := WedgeTrans
  le_antisymm := WedgeAntisymm

def Coloring (k : ℕ) (V : Type) : Type := V → (Fin k)

def IsInducedCopy {P Q : Type} [PartialOrder P] [PartialOrder Q] (f : P → Q) : Prop :=
  ∀ (a b : P), a ≤ b ↔ f a ≤ f b

def HasMonochromeSubposet (P Q : Type) [PartialOrder P] [PartialOrder Q] (k : ℕ)
    (χ : Coloring k Q) : Prop :=
  ∃ (c : Fin k), ∃ (f : P → Q), IsInducedCopy f ∧ ∀ (x : P), χ (f x) = c

def IsMulticolorRamseyUpperBound (P : Type) [PartialOrder P] (k : ℕ) (N : ℕ) : Prop :=
  ∀ (n : ℕ), n ≥ N → ∀ (χ : Coloring k (BooleanLattice n)),
    HasMonochromeSubposet P (BooleanLattice n) k χ

def IsMulticolorRamseyLowerBound (P : Type) [PartialOrder P] (k : ℕ) (N : ℕ) : Prop :=
  ∀ (n : ℕ), n < N → ∃ (χ : Coloring k (BooleanLattice n)),
    ¬HasMonochromeSubposet P (BooleanLattice n) k χ

def IsMulticolorRamseyNumber (P : Type) [PartialOrder P] (k : ℕ) (N : ℕ) : Prop :=
  IsMulticolorRamseyLowerBound P k N ∧ IsMulticolorRamseyUpperBound P k N
