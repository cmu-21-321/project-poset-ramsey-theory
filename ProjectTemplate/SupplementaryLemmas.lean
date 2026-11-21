import ProjectTemplate.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Finset.Max

/-!
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
set_option linter.flexible false in
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

/-
If a coloring of R has monochrome induced copies of P and Q in some specified colors, then permuting
the colors preserves this property.
-/
lemma CanPermuteColoring {P Q R : Type} [PartialOrder P] [PartialOrder Q] [PartialOrder R]
    (k : ℕ) (setA setB : Finset (Fin k)) (χ : Coloring k R) (σ : Equiv.Perm (Fin k)) :
    HasSpecifiedMonochromeSubposet P R k χ setA ∨ HasSpecifiedMonochromeSubposet Q R k χ setB →
    HasSpecifiedMonochromeSubposet P R k (σ ∘ χ) (Finset.image σ setA) ∨
    HasSpecifiedMonochromeSubposet Q R k (σ ∘ χ) (Finset.image σ setB) := by
  intro h
  rcases h with ⟨c, hc, f, hInduced, hColor⟩ | ⟨c, hc, f, hInduced, hColor⟩
  · left
    use σ c, Finset.mem_image_of_mem σ hc, f
    exact ⟨hInduced, fun x ↦ congrArg σ (hColor x)⟩
  · right
    use σ c, Finset.mem_image_of_mem σ hc, f
    exact ⟨hInduced, fun x ↦ congrArg σ (hColor x)⟩

/-
Proves that no induced map of F_2 into Q_n has ∅ in its image.
-/
lemma wedge_ne_empty {m : ℕ} {f : Wedge 2 → BooleanLattice m}
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
set_option linter.flexible false in
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
    specialize hRamsey χ
    rcases hRamsey with ⟨c, hc⟩
    use c
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨Fintype.complete c, c.isLt⟩
    · exact hc

/-
The symmetric version of the previous lemma.
-/
lemma ObviousLemma2 {P Q : Type} [PartialOrder P] [PartialOrder Q] {b N : ℕ} :
    IsMixedRamseyUpperBound P Q 0 b N ↔ IsMulticolorRamseyUpperBound Q b N := by
  constructor
  · intro hMixed χ
    rcases hMixed (Fin.cast (zero_add b).symm ∘ χ) with hasP | hasQ
    · rcases hasP with ⟨c, hc, _⟩
      simp [FirstAofK] at hc
    · rcases hasQ with ⟨c, hc, f, hInduced, hColor⟩
      use c.cast (zero_add b), f
      constructor
      · assumption
      · intro x
        specialize hColor x
        calc
          χ (f x) = Fin.cast (zero_add b) ((Fin.cast (zero_add b).symm ∘ χ) (f x)) := rfl
          _ = Fin.cast (zero_add b) c := by rw [hColor]
  · intro hRamsey χ
    right
    specialize hRamsey (Fin.cast (zero_add b) ∘ χ)
    rcases hRamsey with ⟨c, f, hInduced, hColor⟩
    use c.cast (zero_add b).symm
    constructor
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_univ
      · simp
    · use f
      constructor
      · assumption
      · intro x
        specialize hColor x
        calc
          χ (f x) = Fin.cast (zero_add b).symm ((Fin.cast (zero_add b) ∘ χ) (f x)) := rfl
          _ = Fin.cast (zero_add b).symm c := by rw [hColor]
