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
The identity function, mapping elements from a smaller boolean cube Q_n to themselves in a
larger Q_m.
-/
def ProjectUp {n m : ℕ} (h : n ≤ m) : BooleanLattice n → BooleanLattice m :=
  Finset.map ⟨Fin.castLE h, Fin.castLE_injective h⟩

lemma ProjectUpInj {n m : ℕ} (h : n ≤ m) : Function.Injective (ProjectUp h) := by
  exact Finset.map_injective ⟨Fin.castLE h, Fin.castLE_injective h⟩

lemma ProjectUpInduced {n m : ℕ} (h : n ≤ m) : ∀ (s t : BooleanLattice n),
    s ≤ t ↔ ProjectUp h s ≤ ProjectUp h t := by
  intro s t
  constructor
  · intro hst x hxs
    rcases Finset.mem_map.mp hxs with ⟨y, hy, hyx⟩
    apply Finset.mem_map.mpr
    use y
    constructor
    · exact hst hy
    · exact hyx
  · intro hSubset
    unfold ProjectUp at hSubset
    intro x hxs
    have h2 : Fin.castLE h x ∈ (ProjectUp h) s :=
      Finset.mem_map.mpr ⟨x, hxs, rfl⟩
    have h3 : Fin.castLE h x ∈ (ProjectUp h) t :=
      Set.mem_of_subset_of_mem hSubset h2
    rcases Finset.mem_map.mp h3 with ⟨a, haft, hax⟩
    apply Fin.castLE_injective at hax
    rw [←hax]
    exact haft

/-
Given a k-coloring on a boolean cube Q_m, this defines a k-coloring on a smaller cube Q_n by simply
restricting the domain and copying over the same colors.
-/
def RestrictColoring (k m n : ℕ) (h : m ≥ n) : Coloring k (BooleanLattice m) →
    Coloring k (BooleanLattice n) :=
  fun χ x ↦ χ (ProjectUp h x)

/-
States that proving R(P; k) ≤ N is equivalent to proving that the monochromatic posets are forced
for Q_N specifically.
-/
lemma EnoughToProveUpperAtN (P : Type) [PartialOrder P] (k : ℕ) (N : ℕ) :
    IsMulticolorRamseyUpperBound P k N ↔ ∀ n ≥ N, IsMulticolorRamseyUpperBound P k n := by
  unfold IsMulticolorRamseyUpperBound
  constructor
  · intro hRamsey n hn χ
    specialize hRamsey (RestrictColoring k n N hn χ)
    rcases hRamsey with ⟨c, f, ⟨hfInjective, hInduced⟩, hMonochrome⟩
    use c, (ProjectUp hn) ∘ f
    constructor
    · constructor
      · exact (Function.Injective.of_comp_iff (ProjectUpInj hn) f).mpr hfInjective
      · intro a b
        exact (hInduced a b).trans (ProjectUpInduced hn (f a) (f b))
    · intro x
      exact hMonochrome x
  · intro hRamsey
    exact hRamsey N (Nat.le_refl N)

/-
States that to prove R(P; k) ≥ N, it's enough to prove that the monochromatic posets can be avoided
for Q_N specifically.
-/
lemma EnoughToProveLowerAtN (P : Type) [PartialOrder P] (k : ℕ) (N : ℕ) :
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

/-
Defines a map from a color set Fin (k + 1) to Fin k by removing a color and shifting things down.
-/
def RemoveColor {k : ℕ} (c : Fin (k + 1)) (d : Fin (k + 1)) (hx : d ≠ c) : Fin k :=
  if hc : c = Fin.last k then d.castPred (ne_of_ne_of_eq hx hc)
  else Fin.predAbove (c.castPred hc) d

/-
Defines the inverse of the above map.
-/
def InvertRemoveColor {k : ℕ} (c : Fin (k + 1)) (d : Fin k) : Fin (k + 1) :=
  c.succAbove d

/-
Proves that it is indeed the inverse.
-/
lemma RemovingIsInvertible {k : ℕ} (c : Fin (k + 1)) (d : Fin (k + 1)) (hx : d ≠ c) :
    InvertRemoveColor c (RemoveColor c d hx) = d := by
  unfold RemoveColor
  unfold InvertRemoveColor
  by_cases hc : c = Fin.last k
  · simp [hc]
  · simp [hc]
    have h := Fin.castSucc_castPred c hc
    nth_rw 1 [←h]
    rw [←h] at hx
    exact Fin.succAbove_predAbove hx

/-
Given that some color never appears in a (k+1)-coloring of P, constructs a k-coloring of P with the
other colors.
-/
def ShrinkColoring {P : Type} {k : ℕ} (χ : Coloring (k + 1) P) (c : Fin (k + 1))
    (hMiss : ∀ (x : P), χ x ≠ c) : Coloring k P :=
  fun x ↦ RemoveColor c (χ x) (hMiss x)

/-
A monochrome copy of P exists in a k+1-coloring of Q where some color c is unused iff it also exists
when we shrink it into a k-coloring.
-/
lemma ShrinkPreserve {P Q : Type} [PartialOrder P] [Nonempty P] [PartialOrder Q] {k : ℕ}
    (χ : Coloring (k + 1) Q) (c : Fin (k + 1)) (hMiss : ∀ (x : Q), χ x ≠ c) :
    HasMonochromeSubposet P Q (k + 1) χ ↔ HasMonochromeSubposet P Q k (ShrinkColoring χ c hMiss)
    := by
  unfold HasMonochromeSubposet
  constructor
  · rintro ⟨d, f, hInduced, hColor⟩
    obtain ⟨x⟩ := ‹Nonempty P›
    use RemoveColor c d (ne_of_eq_of_ne (hColor x).symm (hMiss (f x))), f
    constructor
    · assumption
    · intro y
      specialize hColor y
      subst hColor
      rfl
  · rintro ⟨d, f, hInduced, hColor⟩
    use InvertRemoveColor c d, f
    constructor
    · assumption
    · intro x
      unfold ShrinkColoring at hColor
      specialize hColor x
      calc
        χ (f x) = InvertRemoveColor c (RemoveColor c (χ (f x)) (hMiss (f x))) :=
          (RemovingIsInvertible c (χ (f x)) (hMiss (f x))).symm
        _ = InvertRemoveColor c d := by rw [hColor]

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
  | succ k hk ih =>
      intro χ
      by_cases h : ∃ (i : Fin (k + 2)), ∀ (s : BooleanLattice (k + 2)), s ≠ ∅ → χ s = χ ⊤ → i ∈ s
      · sorry
      · sorry


#check congrArg

--R (F2, k) = k+1
theorem FanLowerBound (k : ℕ) (hk : k ≥ 1) : IsMulticolorRamseyLowerBound (Wedge 2) k k := by
  let χ : BooleanLattice k → (Fin k) :=
    fun set ↦ ⟨Finset.card set - 1, by
    have hle : set.card ≤ k := by
      calc
      set.card ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ set)
      _ = k := by simp
    omega⟩
  use χ
  intro h
  rcases h with ⟨c, f, hf, hmono⟩
  rcases hf with ⟨hfi, horder⟩
  let x₀ : Wedge 2 := ⟨0, by norm_num⟩
  let x₁ : Wedge 2 := ⟨1, by norm_num⟩
  let x₂ : Wedge 2 := ⟨2, by norm_num⟩
  let A := f x₀
  let B := f x₁
  let C := f x₂ --the top of the wedge
  have hAnC : A ≠ C := by
    intro h
    have : (⟨0, by norm_num⟩ : Wedge 2) =
         ⟨2, by norm_num⟩ := hfi h
    norm_num at this
  have hBnC : B ≠ C := by
    intro h
    have : (⟨1, by norm_num⟩ : Wedge 2) =
         ⟨2, by norm_num⟩ := hfi h
    norm_num at this

  have hA : A ≤ C := by
    apply (horder x₀ x₂).mp
    change x₂.val = 2 ∨ x₀.val = x₂.val
    left
    rfl
  have hB : B ≤ C := by
    apply (horder x₁ x₂).mp
    change x₂.val = 2 ∨ x₁.val = x₂.val
    left
    rfl

  have hAC : A.card - 1 = C.card - 1 := congrArg Fin.val
      ((hmono x₀).trans (hmono x₂).symm)
  by_cases hC : C.card ≤ 1
  · have hAc : A.card ≤ 1 := by
      exact le_trans (Finset.card_le_card hA) hC
    have hBc : B.card ≤ 1 := by
      exact le_trans (Finset.card_le_card hB) hC

    by_cases hC0 : C.card = 0
    · by_cases hA0 : A.card = 0
      · have hAeC : A = C := (Finset.card_eq_zero.mp hA0).trans (Finset.card_eq_zero.mp hC0).symm
        exact hAnC hAeC
      · have hA0 : Finset.card A = 1 := by omega
        sorry --only need this case (|A| = 1, |C| = 0. Plan to contradict via A ≤ C)
    · have hC1 : C.card = 1 := by omega
      by_cases hA0 : A.card = 0
      · by_cases hB0 : B.card = 0
        · have hAB : A = B := (Finset.card_eq_zero.mp hA0).trans (Finset.card_eq_zero.mp hB0).symm
          have contra : x₀ = x₁ := hfi hAB
          dsimp[x₀, x₁] at contra --bro imma crash out i literally got 0=1 here
          sorry

        · have hB0 : B.card = 1 := by omega
          have hBC : B.card = C.card := by omega
          exact hBnC ((Finset.subset_iff_eq_of_card_le (ge_of_eq hBC)).mp hB)
      · have hAC : A.card = C.card := by omega
        exact hAnC ((Finset.subset_iff_eq_of_card_le (ge_of_eq hAC)).mp hA)
  · have hC : Finset.card C ≥ 2 := by omega
    have hAC : A.card = C.card := by omega
    exact hAnC ((Finset.subset_iff_eq_of_card_le (ge_of_eq hAC)).mp hA)

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
