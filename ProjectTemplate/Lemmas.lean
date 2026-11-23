import ProjectTemplate.SupplementaryLemmas

import Mathlib.Tactic.Linter.Header

/-! Shows that Rκ(F2) ≤ k + 1 -/
set_option linter.flexible false in
set_option linter.style.haveILetI false in
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
      · unfold HasMonochromeSubposet
        rcases h with ⟨i, hi⟩
        let χ' := RestrictColoring (SkipElement i) χ
        have hMiss : ∀ (x : BooleanLattice (k + 1)),
            x ≠ ∅ → χ' x ≠ χ ⊤ := by
          intro x hNonempty hEq
          have hnonempty : (SkipElement i).φ x ≠ ∅ :=
            Function.Injective.ne (SkipElement i).injective hNonempty
          specialize hi ((SkipElement i).φ x) hnonempty hEq
          exact ItActuallySkips i x hi
        haveI : Nontrivial (Fin (k + 1)) := Fin.nontrivial_iff_two_le.2 (by omega)
        obtain ⟨d, hd⟩ : ∃ d : Fin (k + 1), d ≠ χ ⊤ := by
          by_cases hc : (χ ⊤).val = 0
          · refine ⟨⟨1, by omega⟩, fun h ↦ ?_⟩
            have h' := congrArg Fin.val h
            change 1 = (χ ⊤).val at h'
            omega
          · refine ⟨⟨0, by omega⟩, fun h ↦ ?_⟩
            have h' := congrArg Fin.val h
            change 0 = (χ ⊤).val at h'
            omega
        -- recolor ∅ with d, so that χ ⊤ is missed everywhere
        let χ₁ : Coloring (k + 1) (BooleanLattice (k + 1)) :=
          fun x ↦ if x = ∅ then d else χ' x
        have hMiss₁ : ∀ x, χ₁ x ≠ χ ⊤ := by
          intro x
          by_cases hx : x = ∅
          · change (if x = ∅ then d else χ' x) ≠ χ ⊤
            rw [ite_eq_left hx]
            exact hd
          · change (if x = ∅ then d else χ' x) ≠ χ ⊤
            rw [ite_eq_right hx]
            exact hMiss x hx
        -- apply the induction hypothesis to the k-coloring
        specialize ih (ShrinkColoring χ₁ (χ ⊤) hMiss₁)
        rcases ih with ⟨c, f, hInduced, hColor⟩
        refine ⟨InvertRemoveColor (χ ⊤) c, fun x ↦ (SkipElement i).φ (f x), ?_, ?_⟩
        · exact IsInducedCopy.comp hInduced (SkipElement_isInducedCopy i)
        · intro x
          -- the wedge avoids ∅, so the recolouring didn't affect it
          have hne := wedge_ne_empty hInduced x
          have h1 : χ₁ (f x) = InvertRemoveColor (χ ⊤) c :=
            ShrinkColoring_spec χ₁ (χ ⊤) hMiss₁ (f x) c (hColor x)
          calc χ ((SkipElement i).φ (f x)) = χ' (f x) := rfl
            _ = χ₁ (f x) := (ite_eq_right hne).symm
            _ = InvertRemoveColor (χ ⊤) c := h1
      · push Not at h
        classical
        have htop : (⊤ : BooleanLattice (k + 2)) ≠ ∅ := by
          rw [Finset.top_eq_univ]; exact Finset.univ_nonempty.ne_empty
        let S : Finset (BooleanLattice (k + 2)) :=
          Finset.univ.filter (fun s ↦ s ≠ ∅ ∧ χ s = χ ⊤)
        have hSne : S.Nonempty :=
          ⟨⊤, Finset.mem_filter.2 ⟨Finset.mem_univ _, htop, rfl⟩⟩
        obtain ⟨s₀, hs₀, hmin⟩ := Finset.exists_min_image S Finset.card hSne
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hs₀ hmin
        obtain ⟨hs₀ne, hs₀c⟩ := hs₀
        obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hs₀ne
        obtain ⟨t, htne, htc, hit⟩ := h i
        obtain ⟨T, hT⟩ : ∃ T : BooleanLattice (k + 2), T = ⊤ := ⟨_, rfl⟩
        have hs₀T : s₀ ⊆ T := by rw [hT]; exact le_top
        have htT  : t ⊆ T  := by rw [hT]; exact le_top
        have hTc  : χ T = χ ⊤ := by rw [hT]
        have h01 : ¬ s₀ ⊆ t := fun hsub ↦ hit (hsub hi)
        have h10 : ¬ t ⊆ s₀ := by
          intro hsub
          have hle : s₀.card ≤ t.card := hmin t ⟨Finset.Nonempty.ne_empty htne, htc⟩
          exact hit ((Finset.eq_of_subset_of_card_le hsub hle) ▸ hi)
        have h20 : ¬ T ⊆ s₀ := fun hsub ↦ h10 (htT.trans hsub)
        have h21 : ¬ T ⊆ t  := fun hsub ↦ h01 (hs₀T.trans hsub)
        let f : Wedge 2 → BooleanLattice (k + 2) :=
          fun w ↦ if w.val = 0 then s₀ else if w.val = 1 then t else T
        have hf : ∀ p q : Wedge 2, WedgeOrder p q ↔ f p ≤ f q := by
          intro p q
          obtain ⟨a, ha⟩ := p
          obtain ⟨b, hb⟩ := q
          interval_cases a <;> interval_cases b <;>
            simp [WedgeOrder, f, h01, h10, h20, h21, hs₀T, htT]
        refine ⟨χ ⊤, f, ⟨?_, hf⟩, ?_⟩
        · intro p q hpq
          exact le_antisymm ((hf p q).2 hpq.le) ((hf q p).2 hpq.symm.le)
        · intro x
          obtain ⟨a, ha⟩ := x
          interval_cases a <;> simp [f, hs₀c, htc, hTc]

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
        have contra : Finset.card A ≤ Finset.card C := Finset.card_le_card hA
        linarith
    · have hC1 : C.card = 1 := by omega
      by_cases hA0 : A.card = 0
      · by_cases hB0 : B.card = 0
        · have hAB : A = B := (Finset.card_eq_zero.mp hA0).trans (Finset.card_eq_zero.mp hB0).symm
          have contra : x₀ = x₁ := hfi hAB
          have realcontra : x₀ ≠ x₁ := by
            have h := congr_arg Fin.val contra
            simp at h
          exact realcontra contra
        · have hB0 : B.card = 1 := by omega
          have hBC : B.card = C.card := by omega
          exact hBnC ((Finset.subset_iff_eq_of_card_le (ge_of_eq hBC)).mp hB)
      · have hAC : A.card = C.card := by omega
        exact hAnC ((Finset.subset_iff_eq_of_card_le (ge_of_eq hAC)).mp hA)
  · have hC : Finset.card C ≥ 2 := by omega
    have hAC : A.card = C.card := by omega
    exact hAnC ((Finset.subset_iff_eq_of_card_le (ge_of_eq hAC)).mp hA)




lemma Case_SingletonQ2 (a b N : ℕ) (hN : N = 2 * a + b + 4)
    (IH : IsMixedRamseyUpperBound (Diamond 2) (Wedge 2) a (b + 2)
            (MixedRamseyNumber a (b + 2)))
    (χ : Coloring (a + 1 + (b + 1)) (BooleanLattice N))
    (S : BooleanLattice N) (hS : S.card = 1) (hc : (χ S).val < a + 1) :
    HasSpecifiedMonochromeSubposet (Diamond 2) (BooleanLattice N) (a + 1 + (b + 1)) χ
      (FirstAofK (a + 1) (a + 1 + (b + 1))) ∨
    HasSpecifiedMonochromeSubposet (Wedge 2) (BooleanLattice N) (a + 1 + (b + 1)) χ
      (LastBofK (b + 1) (a + 1 + (b + 1))) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨2 * a + b + 3, by omega⟩
  have e : MixedRamseyNumber a (b + 2) = M := by
    rw [MainPos (by omega)]; omega
  rw [e] at IH
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hS
  exact SingletonQ2_core a b M
    ((MixedIgnoreEmptySet (P := Diamond 2) (show b + 2 > 0 by omega)).1 IH) χ i hc

lemma Case_NoSingletonQ2 (a b N : ℕ) (hN : N = 2 * a + b + 4)
    (IH : IsMixedRamseyUpperBound (Diamond 2) (Wedge 2) (a + 1) b
            (MixedRamseyNumber (a + 1) b))
    (χ : Coloring (a + 1 + (b + 1)) (BooleanLattice N))
    (h : ∀ S : BooleanLattice N, S.card = 1 → a + 1 ≤ (χ S).val) :
    HasSpecifiedMonochromeSubposet (Diamond 2) (BooleanLattice N) (a + 1 + (b + 1)) χ
      (FirstAofK (a + 1) (a + 1 + (b + 1))) ∨
    HasSpecifiedMonochromeSubposet (Wedge 2) (BooleanLattice N) (a + 1 + (b + 1)) χ
      (LastBofK (b + 1) (a + 1 + (b + 1))) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨2 * a + b + 3, by omega⟩
  have hM : M = 2 * a + b + 3 := by omega
  exact NoSingleton_core a b M (ModifiedFromMixed a b M hM IH) χ h

/-
Our main upper bound lemma: R(Q_2^a, D_2^b) ≤ the number specified above.
-/
set_option linter.flexible false in
lemma MainLemma : ∀ (a b : ℕ), a ≥ 1 ∨ b ≥ 1 →
    IsMixedRamseyUpperBound (Diamond 2) (Wedge 2) a b (MixedRamseyNumber a b) := by
  intro a
  induction a with
  | zero =>
      intro b hab
      rcases hab with ha | hb
      · trivial
      · have hnonzero : b ≠ 0 := by linarith
        simp [MixedRamseyNumber, hnonzero]
        exact ObviousLemma2.mpr (FanUpperBound b hb)
  | succ a iha =>
      intro b hab
      clear hab
      induction b with
    | zero =>
      have h2 := iha 1 (Or.inr le_rfl)
      have hN : MixedRamseyNumber (a + 1) 0 = 2 * (a + 1) := MainZero (a + 1)
      rw [hN]
      apply ObviousLemma.mpr
      intro χ
      have h := CanPermuteColoring (FirstAofK a (a + 1)) (LastBofK 1 (a + 1)) ((Equiv.swap (χ ∅)
      (Fin.last a)) ∘ χ) (Equiv.swap (χ ∅) (Fin.last a)) (h2 ((Equiv.swap (χ ∅) (Fin.last a)) ∘ χ))
      rcases h with ⟨c, _, f, hfInduced, hColor⟩ | ⟨c, hc, f, hfInduced, hColor⟩
      · use c, f
        constructor
        · assumption
        · intro x
          specialize hColor x
          simp at hColor
          assumption
      · rcases diamond_of_wedge hfInduced (fun w ↦ Finset.empty_subset (f w))
          (fun w h ↦ wedge_ne_empty hfInduced w (Finset.subset_empty.mp h)) with
          ⟨g, hgInduced, hgColor⟩
        use c, g
        constructor
        · assumption
        · intro x
          simp [LastBofK] at hc
          rcases hc with ⟨y, hy, hswap⟩
          have hya : y.val = a := le_antisymm (Nat.le_of_lt_add_one y.isLt) hy
          rcases hgColor x with hEmpty | ⟨w, hw⟩
          · have hylast : y = Fin.last a := Eq.symm (Fin.eq_of_val_eq (id (Eq.symm hya)))
            simp [hylast] at hswap
            rw [hEmpty, hswap]
          · specialize hColor w
            simp at hColor
            rw [hw, hColor]
    | succ b ihb =>
          intro χ
          have hN : MixedRamseyNumber (a + 1) (b + 1) = 2 * a + b + 4 := by
            rw [MainPos (by omega)]; omega
          -- case on whether there is a set w Q2 avoiding color
          by_cases hSingle : ∃ (S : BooleanLattice (MixedRamseyNumber (a + 1) (b + 1))),
              S.card = 1 ∧ (χ S).val < a + 1
          · obtain ⟨S, hS1, hSc⟩ := hSingle
            exact Case_SingletonQ2 a b _ hN (iha (b + 2) (Or.inr (by omega))) χ S hS1 hSc
          · -- hSingle : ∀ S, S.card = 1 → a + 1 ≤ (χ S).val
            push Not at hSingle
            exact Case_NoSingletonQ2 a b _ hN ihb χ hSingle

#check Finset.empty_subset
#check Finset.subset_empty
#check Nat.le_of_lt_add_one

/-
Defines the coloring of Q_(2k-1) where each color gets two layers, which is used in the lower bound
proof.
This is ugly, will need to clean up
-/
set_option linter.flexible false in
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
lemma MainTheoremLower : ∀ (k : ℕ), k ≥ 1 →
    IsMulticolorRamseyLowerBound (Diamond 2) k (2 * k - 1) := by
  intro k hk
  use LayerColoring k hk
  unfold HasMonochromeSubposet
  push Not
  intro c f hf
  by_contra hcon
  have hall : ∀ x, LayerColoring k hk (f x) = c := by
      intro x
      by_contra hne
      exact hcon ⟨x, hne⟩
  obtain ⟨b, hb⟩ : ∃ b : Diamond 2, b.val = 0 := ⟨⟨0, by decide⟩, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : Diamond 2, x.val = 1 := ⟨⟨1, by decide⟩, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : Diamond 2, t.val = 2 + 1 := ⟨⟨2 + 1, by decide⟩, rfl⟩
  have hbx : b ≤ x := Or.inl hb
  have hxt : x ≤ t := Or.inr (Or.inl ht)
  have hbx_ne : b ≠ x := fun h ↦ by
    rw [h] at hb
    omega
  have hxt_ne : x ≠ t := fun h ↦ by
    rw [h] at hx
    omega
  have hsub1 : f b ⊆ f x := (hf.2 b x).1 hbx
  have hsub2 : f x ⊆ f t := (hf.2 x t).1 hxt
  have hss1 : f b ⊂ f x :=
    Finset.ssubset_iff_subset_ne.2 ⟨hsub1, hf.1.ne hbx_ne⟩
  have hss2 : f x ⊂ f t :=
    Finset.ssubset_iff_subset_ne.2 ⟨hsub2, hf.1.ne hxt_ne⟩
  have hc1 := Finset.card_lt_card hss1
  have hc2 := Finset.card_lt_card hss2
  -- all three have the same color, i.e. the same card / 2
  have hcb := congrArg Fin.val (hall b)
  have hct := congrArg Fin.val (hall t)
  change (f b).card / 2 = c.val at hcb
  change (f t).card / 2 = c.val at hct
  omega


/-
R(Q_2; k) ≤ 2k.
-/
lemma MainTheoremUpper : ∀ (k : ℕ), k ≥ 1 → IsMulticolorRamseyUpperBound (Diamond 2) k (2 * k) := by
  intro k hk
  have h := MainLemma k 0 (Or.inl hk)
  have hN : MixedRamseyNumber k 0 = 2 * k := rfl
  rw [hN] at h
  exact ObviousLemma.mp h
