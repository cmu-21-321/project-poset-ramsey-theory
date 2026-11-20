import ProjectTemplate.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Finset.Max

import Mathlib.Tactic.Linter.Header

/-! ... -/
set_option linter.flexible false


/-
Any FinMap can be extended to a BooleanLatticeMap, where the FinMap is simply applied to all
elements.
-/
def Extend {n m : ℕ} (map : FinMap n m) : BooleanLatticeMap n m where
  φ := Finset.map ⟨map.f, map.injective⟩
  injective := by apply Finset.map_injective
  induced := by
    intro s t
    constructor
    · intro hst x hxs
      rcases Finset.mem_map.mp hxs with ⟨y, hy, hyx⟩
      apply Finset.mem_map.mpr
      use y
      constructor
      · exact hst hy
      · exact hyx
    · intro hSubset x hxs
      have h2 : map.f x ∈ Finset.map ⟨map.f, map.injective⟩ s := Finset.mem_map.mpr ⟨x, hxs, rfl⟩
      have h3 : map.f x ∈ Finset.map ⟨map.f, map.injective⟩ t := Set.mem_of_subset_of_mem hSubset h2
      rcases Finset.mem_map.mp h3 with ⟨a, haft, hax⟩
      apply map.injective at hax
      rw [←hax]
      exact haft

/-
The identity function from Fin n to Fin m, where n ≤ m, is one such injective map.
-/
def ProjectUp {n m : ℕ} (h : n ≤ m) : FinMap n m where
  f := Fin.castLE h
  injective := Fin.castLE_injective h

/-
The corresponding embedding.
-/
abbrev EmbedUp {n m : ℕ} (h : n ≤ m) : BooleanLatticeMap n m := Extend (ProjectUp h)

/-
The function from Fin n to Fin (n+1) that skips some element of Fin (n+1) is one such injective map.
-/
def AddOne {n : ℕ} (i : Fin (n + 1)) : FinMap n (n + 1) where
  f := i.succAbove
  injective := Fin.succAbove_right_injective

/-
The corresponding embedding.
-/
abbrev SkipElement {n : ℕ} (i : Fin (n + 1)) : BooleanLatticeMap n (n + 1) := Extend (AddOne i)

/-
Proves that this embedding always skips the element i.
-/
lemma ItActuallySkips {n : ℕ} (i : Fin (n + 1)) : ∀ (x : BooleanLattice n),
    i ∉ (SkipElement i).φ x := by
  intro x hi
  rcases Finset.mem_map.mp hi with ⟨a, hax, hai⟩
  exact Fin.succAbove_ne i a hai

/-
Give an k-coloring on a boolean cube Q_m and a map from Q_n to Q_m, it extends the coloring to Q_n
by transferring it over the map.
-/
abbrev RestrictColoring {k n m : ℕ} (map : BooleanLatticeMap n m)
    (χ : Coloring k (BooleanLattice m)) : Coloring k (BooleanLattice n) :=
  fun x ↦ χ (map.φ x)

/-
States that proving R(P; k) ≤ N is equivalent to proving that the monochromatic posets are forced
for Q_N specifically.
-/
lemma EnoughToProveUpperAtN (P : Type) [PartialOrder P] (k : ℕ) (N : ℕ) :
    IsMulticolorRamseyUpperBound P k N ↔ ∀ n ≥ N, IsMulticolorRamseyUpperBound P k n := by
  unfold IsMulticolorRamseyUpperBound
  constructor
  · intro hRamsey n hn χ
    specialize hRamsey (RestrictColoring (EmbedUp hn) χ)
    rcases hRamsey with ⟨c, f, ⟨hfInjective, hInduced⟩, hMonochrome⟩
    use c, (EmbedUp hn).φ ∘ f
    constructor
    · constructor
      · exact (Function.Injective.of_comp_iff (EmbedUp hn).injective f).mpr hfInjective
      · intro a b
        exact (hInduced a b).trans ((EmbedUp hn).induced (f a) (f b))
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
abbrev InvertRemoveColor {k : ℕ} (c : Fin (k + 1)) (d : Fin k) : Fin (k + 1) :=
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

theorem wedge_ne_empty {m : ℕ} {f : Wedge 2 → BooleanLattice m}
    (hf : IsInducedCopy f) (x : Wedge 2) : f x ≠ ∅ := by
  intro hx
  obtain ⟨a, ha⟩ := x
  have key : ∀ y : Wedge 2, WedgeOrder ⟨a, ha⟩ y := by
    intro y
    exact (hf.2 _ y).2 (by rw [hx]; exact Finset.empty_subset _)
  have h0 := key ⟨0, by decide⟩
  have h1 := key ⟨1, by decide⟩
  simp [WedgeOrder] at h0 h1
  omega

/-
Proves that R(F_2; k) ≤ N ↔ R*(F_2; k) ≤ N.
-/
lemma WedgeIgnoreEmptySet {k N : ℕ} (hk : k ≥ 1) :
    IsMulticolorRamseyUpperBound (Wedge 2) k N ↔ IsModifiedRamseyUpperBound (Wedge 2) k N := by
  constructor
  · intro hRamsey χ
    let χ' : Coloring k (BooleanLattice N) := fun s ↦ if h : s = ∅ then Fin.mk 0 hk else χ ⟨s, h⟩
    rcases hRamsey χ' with ⟨c, f, hfInduced, hfColor⟩
    let f' : Wedge 2 → NonemptyBooleanLattice N := fun x ↦ ⟨f x, wedge_ne_empty hfInduced x⟩
    use c, f'
    constructor
    · rcases hfInduced with ⟨hfInj, hfInd⟩
      constructor
      · intro x y hxy
        apply hfInj
        exact congrArg Subtype.val hxy
      · exact hfInd
    · intro x
      have hNonempty : f x ≠ ∅ := wedge_ne_empty hfInduced x
      calc
        χ (f' x) = χ' (f x) := by simp [χ', hNonempty, f']
        _ = c := hfColor x
  · intro hRamsey χ
    rcases hRamsey (χ ∘ Subtype.val) with ⟨c, f, ⟨hfInj, hfInd⟩, hfColor⟩
    use c, (Subtype.val ∘ f)
    constructor
    · constructor
      · exact Function.Injective.comp Subtype.val_injective hfInj
      · exact hfInd
    · exact hfColor

/-
Proves that if b > 0, R(P^a, F_2^b) ≤ N ↔ R*(P^a, F_2^b) ≤ N.
-/
lemma MixedIgnoreEmptySet {a b N : ℕ} {P : Type} [PartialOrder P] (hb : b > 0) :
    IsMixedRamseyUpperBound P (Wedge 2) a b N ↔ IsModifiedMixedRamseyUpperBound P (Wedge 2) a b N
    := by
  constructor
  · intro hRamsey χ
    let cola : Fin (a + b) := Fin.mk a (by linarith)
    let χ' : Coloring (a + b) (BooleanLattice N) :=
      fun s ↦ if h : s = ∅ then cola else χ ⟨s, h⟩
    rcases hRamsey χ' with hP | hWedge
    · left
      rcases hP with ⟨c, hc, f, hfInduced, hfColor⟩
      have hNonempty : ∀ (x : P), f x ≠ ∅ := by
        intro x hEmpty
        specialize hfColor x
        simp [χ', hEmpty] at (hfColor)
        rw [←hfColor] at hc
        unfold FirstAofK at hc
        simp at hc
        change a < a at hc
        linarith
      let f' : P → NonemptyBooleanLattice N := fun x ↦ ⟨f x, hNonempty x⟩
      use c, hc, f'
      constructor
      · rcases hfInduced with ⟨hfInj, hfInd⟩
        constructor
        · intro x y hxy
          apply hfInj
          exact congrArg Subtype.val hxy
        · exact hfInd
      · intro x
        calc
          χ (f' x) = χ' (f x) := by simp [χ', hNonempty, f']
          _ = c := hfColor x
    · right
      rcases hWedge with ⟨c, hc, f, hfInduced, hfColor⟩
      let f' : Wedge 2 → NonemptyBooleanLattice N := fun x ↦ ⟨f x, wedge_ne_empty hfInduced x⟩
      use c, hc, f'
      constructor
      · rcases hfInduced with ⟨hfInj, hfInd⟩
        constructor
        · intro x y hxy
          apply hfInj
          exact congrArg Subtype.val hxy
        · exact hfInd
      · intro x
        have hNonempty : f x ≠ ∅ := wedge_ne_empty hfInduced x
        calc
          χ (f' x) = χ' (f x) := by simp [χ', hNonempty, f']
          _ = c := hfColor x
  · intro hRamsey χ
    rcases hRamsey (χ ∘ Subtype.val) with hP | hWedge
    · left
      rcases hP with ⟨c, hc, f, ⟨hfInj, hfInd⟩, hfColor⟩
      use c, hc, (Subtype.val ∘ f)
      constructor
      · constructor
        · exact Function.Injective.comp Subtype.val_injective hfInj
        · exact hfInd
      · exact hfColor
    · right
      rcases hWedge with ⟨c, hc, f, ⟨hfInj, hfInd⟩, hfColor⟩
      use c, hc, (Subtype.val ∘ f)
      constructor
      · constructor
        · exact Function.Injective.comp Subtype.val_injective hfInj
        · exact hfInd
      · exact hfColor

theorem IsInducedCopy.comp {P Q R : Type} [PartialOrder P] [PartialOrder Q] [PartialOrder R]
    {f : P → Q} {g : Q → R} (hf : IsInducedCopy f) (hg : IsInducedCopy g) :
    IsInducedCopy (fun x ↦ g (f x)) :=
  ⟨hg.1.comp hf.1, fun a b ↦ (hf.2 a b).trans (hg.2 (f a) (f b))⟩

theorem SkipElement_isInducedCopy {k : ℕ} (i : Fin (k + 2)) :
    IsInducedCopy (SkipElement i).φ :=
  ⟨(SkipElement i).injective, fun a b ↦ by
    show a ⊆ b ↔ (SkipElement i).φ a ⊆ (SkipElement i).φ b
    exact Finset.map_subset_map.symm⟩

theorem ShrinkColoring_spec {k : ℕ} {V : Type} (χ : Coloring (k + 1) V) (c : Fin (k + 1))
    (h : ∀ x, χ x ≠ c) (x : V) (c' : Fin k)
    (hx : ShrinkColoring χ c h x = c') :
    χ x = InvertRemoveColor c c' := by
  change RemoveColor c (χ x) (h x) = c' at hx
  rw [← hx]
  exact (RemovingIsInvertible c (χ x) (h x)).symm

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

lemma ObviousLemma2 {P Q : Type} [PartialOrder P] [PartialOrder Q] {a b N : ℕ} :
    IsMixedRamseyUpperBound P Q a b N ↔ IsMixedRamseyUpperBound Q P b a N := by
  constructor
  · intro hMixed χ
    rw [add_comm] at χ
    rcases hMixed (Fin.rev ∘ χ) with hP | hQ
    · right
      rcases hP with ⟨c, hc, h⟩
      rw [add_comm] at c
      simp [FirstAofK] at hc
      sorry
    sorry
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
lemma MainLemma : ∀ (a b : ℕ), a ≥ 1 →
    IsMixedRamseyUpperBound (Diamond 2) (Wedge 2) a b (MixedRamseyNumber a b) := by
  intro a b ha
  --induction
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
  have h := MainLemma k 0 (hk)
  have hN : MixedRamseyNumber k 0 = 2 * k := rfl
  rw [hN] at h
  exact ObviousLemma.mp h

/-
Our main result: R(Q_2; k) = 2k.
-/
theorem MainTheorem : ∀ (k : ℕ), k ≥ 1 → IsMulticolorRamseyNumber (Diamond 2) k (2 * k) := by
  intro k hk
  constructor
  · exact MainTheoremLower k hk
  · exact MainTheoremUpper k hk
