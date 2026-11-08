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

/-
Given a k-coloring on a boolean cube Q_m, this defines a k-coloring on a smaller cube Q_n by simply
restricting the domain and copying over the same colors.
-/
def restrict (k m n : ℕ) (h : m ≥ n) : Coloring k (BooleanLattice m) →
    Coloring k (BooleanLattice n) :=
  fun χ x ↦ χ (x.map ⟨Fin.castLE h, Fin.castLE_injective h⟩)

/-
States that proving R(P; k) ≤ N is equivalent to proving that the monochromatic posets are forced
for Q_N specifically.
-/
theorem EnoughToProveUpperAtN (P : Type) [PartialOrder P] (k : ℕ) (N : ℕ) :
    IsMulticolorRamseyUpperBound P k N ↔ ∀ n ≥ N, IsMulticolorRamseyUpperBound P k n := by
  unfold IsMulticolorRamseyUpperBound
  constructor
  · intro hRamsey n hn χ
    specialize hRamsey (restrict k n N hn χ)
    rcases hRamsey with ⟨c, f, ⟨hfInjective, hInduced⟩, hMonochrome⟩
    use c, Finset.map ⟨Fin.castLE hn, Fin.castLE_injective hn⟩ ∘ f
    constructor
    · constructor
      · have hInjective : Function.Injective
            (Finset.map ⟨Fin.castLE hn, Fin.castLE_injective hn⟩) :=
          Finset.map_injective ⟨Fin.castLE hn, Fin.castLE_injective hn⟩
        exact (Function.Injective.of_comp_iff hInjective f).mpr hfInjective
      · intro s t
        constructor
        · intro hst x hxs
          rcases Finset.mem_map.mp hxs with ⟨y, hy, hyx⟩
          apply Finset.mem_map.mpr
          use y
          constructor
          · exact Set.mem_of_subset_of_mem ((hInduced s t).mp hst) hy
          · exact hyx
        · intro hSubset
          apply (hInduced s t).mpr
          intro x hxs
          have h : Fin.castLE hn x ∈ (Finset.map ⟨Fin.castLE hn, Fin.castLE_injective hn⟩ ∘ f) s :=
            Finset.mem_map.mpr ⟨x, hxs, rfl⟩
          have h2 : Fin.castLE hn x ∈ (Finset.map ⟨Fin.castLE hn, Fin.castLE_injective hn⟩ ∘ f) t :=
            Set.mem_of_subset_of_mem hSubset h
          apply Finset.mem_map.mp at h2
          rcases h2 with ⟨a, haft, hax⟩
          apply Fin.castLE_injective at hax
          rw [←hax]
          exact haft
    · intro x
      exact hMonochrome x
  · intro hRamsey
    exact hRamsey N (Nat.le_refl N)

/-
States that to prove R(P; k) ≥ N, it's enough to prove that the monochromatic posets can be avoided
for Q_N specifically.
-/
theorem EnoughToProveLowerAtN (P : Type) [PartialOrder P] (k : ℕ) (N : ℕ) :
    IsMulticolorRamseyLowerBound P k N ↔ ∀ n ≤ N, IsMulticolorRamseyLowerBound P k n := by
  constructor
  · intro hRamsey n hn
    unfold IsMulticolorRamseyLowerBound
    by_contra h
    push Not at h
    apply (EnoughToProveUpperAtN P k n).mp at h
    rcases hRamsey with ⟨χ, hχ⟩
    specialize h N hn.ge χ
    exact hχ h
  · intro hRamsey
    exact hRamsey N (Nat.le_refl N)

theorem FanUpperBound (k : ℕ) (hk : k ≥ 1) : IsMulticolorRamseyUpperBound (Wedge 2) k (k + 1) := by
  induction k, hk using Nat.le_induction with
  | base =>
      intro χ
      use 0

      have hχ : χ = fun _ ↦ 0 := by
        funext this
        exact Subsingleton.elim _ _

      --pretty sure this explicit morphism works
      let f : (Wedge 2 → Finset (Fin 2)) := fun i ↦ if i.val = 0 then {0}
                                              else if i.val = 1 then {1}
                                              else {0,1}

      have hf : ∀ p q : Wedge 2, WedgeOrder p q ↔ f p ⊆ f q := by
        intro p q
        obtain ⟨i, hi⟩ := p
        obtain ⟨j, hj⟩ := q
        interval_cases i <;> interval_cases j <;> simp [WedgeOrder] <;> decide
      use f
      constructor
      · constructor
        · intro p q hpq
          apply le_antisymm
          · exact (hf p q).2 hpq.le
          · exact (hf q p).2 hpq.symm.le
        · intro p q
          exact hf p q
      · simp[hχ]
  | succ n hn ih => sorry


--R (F2, k) = k+1
theorem FanLowerBound (k : ℕ) (hk : k ≥ 1) : IsMulticolorRamseyLowerBound (Wedge 2) k k := by
  induction k, hk using Nat.le_induction with
  | base =>
    · use fun _ => 0
      rintro ⟨c, iso, inducedCopy, contra⟩
      rcases inducedCopy with ⟨hinj, hx⟩
      have hcard := Fintype.card_le_of_injective iso hinj
      rw [WedgeCard, BooleanLatticeCard] at hcard
      norm_num at hcard
  | succ n hn ih => sorry

/-
The mixed Ramsey upper bound for P and Q with zero colors for Q is equivalent to
the single-poset Ramsey upper bound for P.
-/
lemma ObviousLemma {P Q : Type} [PartialOrder P] [PartialOrder Q] {a N : ℕ} :
    IsMixedRamseyUpperBound P Q a 0 N ↔ IsMulticolorRamseyUpperBound P a N := by
  constructor
  · intro hMixed χ
    rcases hMixed χ with hasP | hasQ
    · rcases hasP with ⟨c, _, _⟩
      use c
    · rcases hasQ with ⟨c, hc, h⟩
      exfalso
      rcases Finset.mem_filter.mp hc with ⟨_, hca⟩
      apply lt_iff_not_ge.mp c.isLt
      exact ge_iff_le.mp hca
  · intro hRamsey χ
    left
    unfold HasSpecifiedMonochromeSubposet
    unfold IsMulticolorRamseyUpperBound at hRamsey
    specialize hRamsey χ
    unfold HasMonochromeSubposet at hRamsey
    rcases hRamsey with ⟨c, hc⟩
    use c
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨Fintype.complete c, c.isLt⟩
    · exact hc

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

-- Nat.le_iff_lt_add_one.mp (Finset.card_le_univ x)

/-
Defines the coloring of Q_(2k-1) where each color gets two layers, which is used in the lower bound
proof.
This is ugly, will need to clean up
-/
def LayerColoring (k : ℕ) (hk : k ≥ 1) : Coloring k (BooleanLattice (2 * k - 1)) :=
  fun x ↦ ⟨x.card / 2, by
      have h := Finset.card_le_univ x
      apply Nat.le_iff_lt_add_one.mp at h
      simp at h
      have h1 : 1 ≤ 2 * k := by exact Nat.one_le_of_lt (Nat.le_mul_of_pos_right 2 hk)
      rw [Nat.sub_add_cancel h1] at h
      have h2 : 2 ∣ (2 * k) := Nat.dvd_mul_right 2 k
      have h3 := Nat.div_lt_div_of_lt_of_dvd h2 h
      have h4 : 0 < 2 := by exact Nat.zero_lt_two
      have h5 : 2 * k / 2 = k := by exact Nat.mul_div_cancel_left k h4
      rw [h5] at h3
      exact h3
      ⟩

/-
R(Q_2; k) ≥ 2k.
-/
lemma MainTheoremLower : ∀ (k : ℕ), k ≥ 1 → IsMulticolorRamseyLowerBound (Diamond 2) k (2*k-1) := by
  intro k hk
  use LayerColoring k hk
  unfold HasMonochromeSubposet
  push Not
  intro c f hf
  sorry

/-
R(Q_2; k) ≤ 2k.
-/
lemma MainTheoremUpper : ∀ (k : ℕ), k ≥ 1 → IsMulticolorRamseyUpperBound (Diamond 2) k (2 * k) := by
  intro k hk
  have h := MainLemma k 0 (Or.inl hk)
  have hN : MixedRamseyNumber k 0 = 2 * k := rfl
  rw[hN] at h
  exact ObviousLemma.mp h

/-
Our main result: R(Q_2; k) = 2k.
-/
theorem MainTheorem : ∀ (k : ℕ), k ≥ 1 → IsMulticolorRamseyNumber (Diamond 2) k (2 * k) := by
  intro k hk
  constructor
  · exact MainTheoremLower k hk
  · exact MainTheoremUpper k hk
