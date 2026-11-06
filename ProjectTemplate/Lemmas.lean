import ProjectTemplate.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

import Mathlib.Tactic.Linter.Header
set_option linter.flexible false



theorem ExistsUniqueRamsey (P : Type) [PartialOrder P] (k : ℕ) :
    ∃! (N : ℕ), IsMulticolorRamseyNumber P k N := by
  sorry

#check Finset.map
#check Fin.castLE
#check Finset.map
#check Finset.map_injective
#check Function.Injective.of_comp_iff

def restrict (k m n : ℕ) (h : m ≥ n) : Coloring k (BooleanLattice m) →
    Coloring k (BooleanLattice n) :=
  fun χ x ↦ χ (x.map ⟨Fin.castLE h, Fin.castLE_injective h⟩)

/-
States that to prove R(P; k) ≤ N, it's enough to prove that the monochromatic posets are forced for
Q_N specifically.
-/
theorem EnoughToProveUpperAtN (P : Type) [PartialOrder P] (k : ℕ) (N : ℕ) :
    IsMulticolorRamseyUpperBound P k N ↔ ∀ n ≥ N, IsMulticolorRamseyUpperBound P k n := by
  unfold IsMulticolorRamseyUpperBound
  constructor
  · intro hRamsey n hn χ
    unfold HasMonochromeSubposet
    specialize hRamsey (restrict k n N hn χ)
    unfold HasMonochromeSubposet at hRamsey
    rcases hRamsey with ⟨c, f, ⟨hfInjective, hInduced⟩, hMonochrome⟩
    use c, Finset.map ⟨Fin.castLE hn, Fin.castLE_injective hn⟩ ∘ f
    constructor
    · constructor
      · have hInjective : Function.Injective
            (Finset.map ⟨Fin.castLE hn, Fin.castLE_injective hn⟩) :=
          Finset.map_injective ⟨Fin.castLE hn, Fin.castLE_injective hn⟩
        exact (Function.Injective.of_comp_iff hInjective f).mpr hfInjective
      · intro a b
        sorry
    · sorry
  · sorry

/-
States that to prove R(P; k) ≥ N, it's enough to prove that the monochromatic posets can be avoided
for Q_N specifically.
-/
theorem EnoughToProveLowerAtN (P : Type) [PartialOrder P] (k : ℕ) (N : ℕ) :
    IsMulticolorRamseyLowerBound P k N ↔ ∀ n ≥ N, IsMulticolorRamseyLowerBound P k n := by
  sorry

theorem FanUpperBound (k : ℕ) (hk : k ≥ 1) : IsMulticolorRamseyUpperBound (Wedge 2) k (k + 1) := by
  induction k, hk using Nat.le_induction with
  | base =>
      intro n hn χ
      use 0

      have hχ : χ = fun _ ↦ 0 := by
        funext this
        exact Subsingleton.elim _ _

      have h0 : 0 < n := by omega
      have h1 : 1 < n := by omega
      let a : Fin n := ⟨0, h0⟩
      let b : Fin n := ⟨1, h1⟩
      let hab : a ≠ b := by
        intro h
        have := congrArg Fin.val h
        simp [a, b] at this

      --pretty sure this explicit morphism works
      let f : (Wedge 2 → Finset (Fin n)) := fun i ↦ if i.val = 0 then ({a} : Finset (Fin n))
                                              else if i.val = 1 then ({b} : Finset (Fin n))
                                              else ({a,b} : Finset (Fin n))
      --here {a}, {b} are viewed as posets in Booleanlattice n

      use f
      constructor
      · intro p q
        have hp : p.val < 3 := p.isLt
        have hq : q.val < 3 := q.isLt
        change WedgeOrder p q ↔ (f p : Finset (Fin n)) ≤ (f q : Finset (Fin n))
        rcases (by omega : p.val = 0 ∨ p.val = 1 ∨ p.val = 2) with h | h | h <;>
        rcases (by omega : q.val = 0 ∨ q.val = 1 ∨ q.val = 2) with h' | h' | h' <;>
        simp [f, WedgeOrder, h, h', hab, hab.symm]
        intro h
        apply hab
        have := Finset.ext_iff.mp h b
        simp at this
        exact this.symm
      · simp[hχ]
  | succ n hn ih => sorry


--R (F2, k) = k+1
theorem FanLowerBound (k : ℕ) (hk : k ≥ 1) : IsMulticolorRamseyLowerBound (Wedge 2) k (k + 1) := by
  induction k, hk using Nat.le_induction with
  | base =>
    · use fun _ => 0
      rintro ⟨c, iso, inducedCopy, contra⟩
      have hn' : n ≤ 1 := by
        exact Nat.le_of_lt_succ hn

      have hinj : Function.Injective iso := by
        intro a b hab
        apply le_antisymm
        · exact (inducedCopy a b).2 hab.le
        · exact (inducedCopy b a).2 hab.ge

      have hcard := Fintype.card_le_of_injective iso hinj
      rw [WedgeCard, BooleanLatticeCard] at hcard
      have hInequal : 2^n ≤ 2 := by
        calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by linarith) hn'
          _ = 2 := by rfl
      omega
  | succ n hn ih => sorry

/-
The mixed Ramsey upper bound for P and Q with zero colors for Q is equivalent to
the single-poset Ramsey upper bound for P.
-/
lemma ObviousLemma {P Q : Type} [PartialOrder P] [PartialOrder Q] {a N : ℕ}:
    IsMixedRamseyUpperBound P Q a 0 N ↔ IsMulticolorRamseyUpperBound P a N := by
  sorry

/-
The mixed Ramsey number used in our main upper bound lemma.
-/
def MixedRamseyNumber (a b : ℕ) : ℕ :=
  match b with
  | .zero => 2 * a
  | .succ _ => 2 * a + b + 1

/-
Our main upper bound lemma: R(Q_2^a, D_2^b) ≤ the number specified above.
-/
lemma MainLemma : ∀ (a b : ℕ), (a ≥ 1 ∨ b ≥ 1) →
    IsMixedRamseyUpperBound (Diamond 2) (Wedge 2) a b (MixedRamseyNumber a b) := by
  sorry

/-
R(Q_2; k) ≥ 2k.
-/
lemma MainTheoremLower : ∀ (k : ℕ), k ≥ 1 → IsMulticolorRamseyLowerBound (Diamond 2) k (2 * k) := by
  sorry

/-
R(Q_2; k) ≤ 2k.
-/
lemma MainTheoremUpper : ∀ (k : ℕ), k ≥ 1 → IsMulticolorRamseyUpperBound (Diamond 2) k (2 * k) := by
  sorry

/-
Our main result: R(Q_2; k) = 2k.
-/
theorem MainTheorem : ∀ (k : ℕ), k ≥ 1 → IsMulticolorRamseyNumber (Diamond 2) k (2 * k) := by
  intro k hk
  constructor
  · exact MainTheoremLower k hk
  · exact MainTheoremUpper k hk
