import ProjectTemplate.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Finset.Max

/-!
The mixed Ramsey number used in our main upper bound lemma.
-/
abbrev MixedRamseyNumber (a b : ℕ) : ℕ :=
  if b = 0 then 2 * a else 2 * a + b + 1



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
    {k : ℕ} (setA setB : Finset (Fin k)) (χ : Coloring k R) (σ : Equiv.Perm (Fin k)) :
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


lemma MainZero (a : ℕ) : MixedRamseyNumber a 0 = 2 * a := by
  unfold MixedRamseyNumber
  rw [ite_eq_left rfl]

lemma MainPos {a b : ℕ} (hb : b ≠ 0) : MixedRamseyNumber a b = 2 * a + b + 1 := by
  unfold MixedRamseyNumber
  rw [ite_eq_right hb]


/-- Adding `i` back to the image of `SkipElement i` is still an induced embedding. -/
lemma insert_skip_subset_iff {M : ℕ} (i : Fin (M + 1)) (s t : BooleanLattice M) :
    insert i ((SkipElement i).φ s) ⊆ insert i ((SkipElement i).φ t) ↔ s ⊆ t := by
  constructor
  · intro hle
    refine ((SkipElement i).induced s t).2 ?_
    intro x hx
    have hx' := hle (Finset.mem_insert_of_mem hx)
    rcases Finset.mem_insert.1 hx' with rfl | hx2
    · exact absurd hx (ItActuallySkips _ s)
    · exact hx2
  · intro hst
    exact Finset.insert_subset_insert _ (((SkipElement i).induced s t).1 hst)

/-- `x ↦ insert i (skip_i x)`: an induced copy of `Q_n` onto the strict-superset-or-equal
part of `{i}` in `Q_{n+1}`; nonempty `x` land strictly above `{i}`. -/
def LiftAbove {n : ℕ} (i : Fin (n + 1)) : BooleanLatticeMap n (n + 1) where
  φ x := insert i ((SkipElement i).φ x)
  injective := by
    intro x y hxy
    exact Finset.Subset.antisymm
      ((insert_skip_subset_iff i x y).1 (le_of_eq hxy))
      ((insert_skip_subset_iff i y x).1 (le_of_eq hxy.symm))
  induced := fun s t ↦ (insert_skip_subset_iff i s t).symm

lemma LiftAbove_isInducedCopy {n : ℕ} (i : Fin (n + 1)) : IsInducedCopy (LiftAbove i).φ :=
  ⟨(LiftAbove i).injective, (LiftAbove i).induced⟩

lemma LiftAbove_mem {n : ℕ} (i : Fin (n + 1)) (x : BooleanLattice n) :
    i ∈ (LiftAbove i).φ x :=
  Finset.mem_insert_self _ _

lemma LiftAbove_ne_empty {n : ℕ} (i : Fin (n + 1)) (x : BooleanLattice n) :
    (LiftAbove i).φ x ≠ ∅ :=
  Finset.ne_empty_of_mem (LiftAbove_mem i x)

lemma LiftAbove_singleton_subset {n : ℕ} (i : Fin (n + 1)) (x : BooleanLattice n) :
    ({i} : BooleanLattice (n + 1)) ⊆ (LiftAbove i).φ x :=
  Finset.singleton_subset_iff.2 (LiftAbove_mem i x)

/-- For nonempty `x`, the lifted set is strictly bigger than `{i}`. -/
lemma not_LiftAbove_subset_singleton {n : ℕ} (i : Fin (n + 1)) {x : BooleanLattice n}
    (hx : x ≠ ∅) : ¬ (LiftAbove i).φ x ⊆ ({i} : BooleanLattice (n + 1)) := by
  intro hsub
  have hne : (SkipElement i).φ x ≠ ∅ :=
    Function.Injective.ne (SkipElement i).injective hx
  obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.2 hne
  have hz' : z ∈ (LiftAbove i).φ x := Finset.mem_insert_of_mem hz
  have hzi : z = i := Finset.mem_singleton.1 (hsub hz')
  subst hzi
  exact ItActuallySkips _ x hz

/-- Transport an induced copy living in `Q_m \ ∅` along an induced map `Q_m → Q_N`. -/
lemma IsInducedCopy.of_nonempty {m N : ℕ} {P : Type} [PartialOrder P]
    {ψ : BooleanLattice m → BooleanLattice N} (hψ : IsInducedCopy ψ)
    {f : P → NonemptyBooleanLattice m} (hf : IsInducedCopy f) :
    IsInducedCopy (fun x ↦ ψ (f x).val) := by
  have key : ∀ x y : P, x ≤ y ↔ ψ (f x).val ≤ ψ (f y).val :=
    fun x y ↦ Iff.trans (hf.2 x y) (hψ.2 (f x).val (f y).val)
  exact ⟨fun x y hxy ↦ le_antisymm ((key x y).2 (le_of_eq hxy))
    ((key y x).2 (le_of_eq hxy.symm)), key⟩

/-- General fact: with zero colors for `Q`, the `*`-version holds one level up.
(Used for the `b = 0` case of `ModifiedFromMixed`; contains no `MixedRamseyNumber`.) -/
lemma ModifiedFromMixed_zero {P Q : Type} [PartialOrder P] [PartialOrder Q] {a N : ℕ}
    (h : IsMixedRamseyUpperBound P Q a 0 N) :
    IsModifiedMixedRamseyUpperBound P Q a 0 (N + 1) := by
  intro χ
  let χ' : Coloring (a + 0) (BooleanLattice N) := fun T ↦
    χ ⟨(LiftAbove (Fin.last N)).φ T, LiftAbove_ne_empty _ _⟩
  rcases h χ' with ⟨c, hc, f, hf, hcol⟩ | ⟨c, hc, _⟩
  · left
    refine ⟨c, hc, fun x ↦ ⟨(LiftAbove (Fin.last N)).φ (f x), LiftAbove_ne_empty _ _⟩,
      ⟨fun x y hxy ↦ hf.1 ((LiftAbove (Fin.last N)).injective (congrArg Subtype.val hxy)),
        fun x y ↦ (hf.2 x y).trans ((LiftAbove (Fin.last N)).induced (f x) (f y))⟩,
      fun x ↦ hcol x⟩
  · exfalso
    have h1 : c.val ≥ a + 0 - 0 := (Finset.mem_filter.1 hc).2
    have h2 := c.isLt
    omega


/-- Two incomparable sets `A, B` below `C` give an induced wedge. -/
lemma wedge_of_three {m : ℕ} {A B C : BooleanLattice m}
    (hAC : A ⊆ C) (hBC : B ⊆ C) (hAB : ¬ A ⊆ B) (hBA : ¬ B ⊆ A) :
    ∃ f : Wedge 2 → BooleanLattice m, IsInducedCopy f ∧
      ∀ x : Wedge 2, f x = A ∨ f x = B ∨ f x = C := by
  classical
  have h20 : ¬ C ⊆ A := fun h ↦ hBA (hBC.trans h)
  have h21 : ¬ C ⊆ B := fun h ↦ hAB (hAC.trans h)
  let f : Wedge 2 → BooleanLattice m :=
    fun w ↦ if w.val = 0 then A else if w.val = 1 then B else C
  have hf : ∀ p q : Wedge 2, WedgeOrder p q ↔ f p ≤ f q := by
    intro p q
    obtain ⟨i, hi⟩ := p
    obtain ⟨j, hj⟩ := q
    interval_cases i <;> interval_cases j <;>
      simp [WedgeOrder, f, hAB, hBA, h20, h21, hAC, hBC]
  refine ⟨f, ⟨?_, hf⟩, ?_⟩
  · intro p q hpq
    exact le_antisymm ((hf p q).2 hpq.le) ((hf q p).2 hpq.symm.le)
  · intro x
    obtain ⟨i, hi⟩ := x
    interval_cases i <;> simp [f]

/-- Value of `Fin.succAbove` as a natural number. -/
lemma succAbove_val {n : ℕ} (p : Fin (n + 1)) (c : Fin n) :
    (p.succAbove c).val = if c.val < p.val then c.val else c.val + 1 := by
  by_cases h : c.val < p.val
  · have h' : c.castSucc < p := by exact h
    rw [Fin.succAbove_of_castSucc_lt p c h', ite_eq_left h]
    all_goals simp
  · have h' : p ≤ c.castSucc := by exact Nat.not_lt.1 h
    rw [Fin.succAbove_of_le_castSucc p c h', ite_eq_right h]
    all_goals simp

/-! ### The shifting map φ -/

section Shift

variable {n k : ℕ} (χ : Coloring k (BooleanLattice (n + 1))) (ck : Fin k)

/-- `T` avoids `0` and contains a nonempty `ck`-colored set. -/
def ShiftSet (T : BooleanLattice (n + 1)) : Prop :=
  (0 : Fin (n + 1)) ∉ T ∧ ∃ S : BooleanLattice (n + 1), S ⊆ T ∧ S ≠ ∅ ∧ χ S = ck

open Classical in
noncomputable def ShiftUp (T : BooleanLattice (n + 1)) : BooleanLattice (n + 1) :=
  if ShiftSet χ ck T then insert (0 : Fin (n + 1)) T else T

lemma ShiftUp_of_mem {T : BooleanLattice (n + 1)} (h : ShiftSet χ ck T) :
    ShiftUp χ ck T = insert (0 : Fin (n + 1)) T := by
  unfold ShiftUp; rw [ite_eq_left h]

lemma ShiftUp_of_not_mem {T : BooleanLattice (n + 1)} (h : ¬ ShiftSet χ ck T) :
    ShiftUp χ ck T = T := by
  unfold ShiftUp; rw [ite_eq_right h]

lemma subset_ShiftUp (T : BooleanLattice (n + 1)) : T ⊆ ShiftUp χ ck T := by
  by_cases h : ShiftSet χ ck T
  · rw [ShiftUp_of_mem χ ck h]; exact Finset.subset_insert _ _
  · exact (ShiftUp_of_not_mem χ ck h).symm.le

lemma ShiftUp_subset_insert (T : BooleanLattice (n + 1)) :
    ShiftUp χ ck T ⊆ insert (0 : Fin (n + 1)) T := by
  by_cases h : ShiftSet χ ck T
  · exact (ShiftUp_of_mem χ ck h).le
  · rw [ShiftUp_of_not_mem χ ck h]; exact Finset.subset_insert _ _

lemma ShiftSet_mono {T₁ T₂ : BooleanLattice (n + 1)} (h : ShiftSet χ ck T₁)
    (hsub : T₁ ⊆ T₂) (h0 : (0 : Fin (n + 1)) ∉ T₂) : ShiftSet χ ck T₂ := by
  obtain ⟨_, S, hS, hne, hc⟩ := h
  exact ⟨h0, S, hS.trans hsub, hne, hc⟩

/-- φ is an induced embedding on sets avoiding `0`. -/
lemma ShiftUp_subset_iff {T₁ T₂ : BooleanLattice (n + 1)}
    (h1 : (0 : Fin (n + 1)) ∉ T₁) (h2 : (0 : Fin (n + 1)) ∉ T₂) :
    ShiftUp χ ck T₁ ⊆ ShiftUp χ ck T₂ ↔ T₁ ⊆ T₂ := by
  constructor
  · intro hφ x hx
    have hx' : x ∈ insert (0 : Fin (n + 1)) T₂ :=
      ShiftUp_subset_insert χ ck T₂ (hφ (subset_ShiftUp χ ck T₁ hx))
    rcases Finset.mem_insert.1 hx' with rfl | hx2
    · exact absurd hx h1
    · exact hx2
  · intro hsub
    by_cases u1 : ShiftSet χ ck T₁
    · rw [ShiftUp_of_mem χ ck u1, ShiftUp_of_mem χ ck (ShiftSet_mono χ ck u1 hsub h2)]
      exact Finset.insert_subset_insert _ hsub
    · rw [ShiftUp_of_not_mem χ ck u1]
      exact hsub.trans (subset_ShiftUp χ ck T₂)

/-- If there is no monochromatic wedge in the colors `S ∋ ck`, then φ T never has color `ck`
(for nonempty `T` avoiding `0`). -/
lemma ShiftUp_color_ne (S : Finset (Fin k)) (hck : ck ∈ S)
    (hck0 : χ {0} = ck)
    (hNoWedge : ¬ HasSpecifiedMonochromeSubposet (Wedge 2) (BooleanLattice (n + 1)) k χ S)
    {T : BooleanLattice (n + 1)} (h0 : (0 : Fin (n + 1)) ∉ T) (hT : T ≠ ∅) :
    χ (ShiftUp χ ck T) ≠ ck := by
  by_cases hU : ShiftSet χ ck T
  · rw [ShiftUp_of_mem χ ck hU]
    intro hc
    obtain ⟨_, S', hST, hne, hSc⟩ := hU
    have h0S : (0 : Fin (n + 1)) ∉ S' := fun h ↦ h0 (hST h)
    obtain ⟨f, hf, hcases⟩ := wedge_of_three
      (A := ({0} : Finset (Fin (n + 1)))) (B := S') (C := insert (0 : Fin (n + 1)) T)
      (Finset.singleton_subset_iff.2 (Finset.mem_insert_self _ _))
      (hST.trans (Finset.subset_insert _ _))
      (fun h ↦ h0S (Finset.singleton_subset_iff.1 h))
      (fun h ↦ by
        obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 hne
        have hx0 : x = 0 := Finset.mem_singleton.1 (h hx)
        subst hx0
        exact h0S hx)
    apply hNoWedge
    refine ⟨ck, hck, f, hf, fun x ↦ ?_⟩
    rcases hcases x with h | h | h <;> rw [h]
    · exact hck0
    · exact hSc
    · exact hc
  · rw [ShiftUp_of_not_mem χ ck hU]
    intro hc
    exact hU ⟨h0, T, Finset.Subset.refl _, hT, hc⟩

end Shift


/-- The Case 2 map `ShiftUp ∘ skip_0` is an induced copy of `Q_n` in `Q_{n+1}`. -/
lemma ShiftSkip_isInducedCopy {n k : ℕ} (χ : Coloring k (BooleanLattice (n + 1)))
    (ck : Fin k) :
    IsInducedCopy (fun x : BooleanLattice n ↦
      ShiftUp χ ck ((SkipElement (0 : Fin (n + 1))).φ x)) := by
  have hψ : ∀ x y : BooleanLattice n,
      ShiftUp χ ck ((SkipElement (0 : Fin (n + 1))).φ x) ⊆
        ShiftUp χ ck ((SkipElement (0 : Fin (n + 1))).φ y) ↔ x ⊆ y := fun x y ↦
    (ShiftUp_subset_iff χ ck (ItActuallySkips (0 : Fin (n + 1)) x)
      (ItActuallySkips (0 : Fin (n + 1)) y)).trans
      ((SkipElement (0 : Fin (n + 1))).induced x y).symm
  exact ⟨fun x y hxy ↦ Finset.Subset.antisymm ((hψ x y).1 (le_of_eq hxy))
    ((hψ y x).1 (le_of_eq hxy.symm)), fun x y ↦ (hψ x y).symm⟩



/-! ### Getting the nonempty version of the induction hypothesis at M = 2a+b+3 -/

lemma ModifiedFromMixed (a b M : ℕ) (hM : M = 2 * a + b + 3)
    (h : IsMixedRamseyUpperBound (Diamond 2) (Wedge 2) (a + 1) b
          (MixedRamseyNumber (a + 1) b)) :
    IsModifiedMixedRamseyUpperBound (Diamond 2) (Wedge 2) (a + 1) b M := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · -- b = 0: the bound is 2a+2 = M-1, so embed Q_{M-1} into Q_M \ ∅ by adding the last element
    obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨2 * a + 2, by omega⟩
    have hM' : MixedRamseyNumber (a + 1) 0 = M' := by
      rw [MainZero]; omega
    rw [hM'] at h
    intro χ
    let χ' : Coloring (a + 1 + 0) (BooleanLattice M') := fun T ↦
      χ ⟨insert (Fin.last M') ((SkipElement (Fin.last M')).φ T), Finset.insert_ne_empty _ _⟩
    have key : ∀ s t : BooleanLattice M',
        insert (Fin.last M') ((SkipElement (Fin.last M')).φ s) ⊆
          insert (Fin.last M') ((SkipElement (Fin.last M')).φ t) ↔ s ⊆ t := by
      intro s t
      constructor
      · intro hle
        refine ((SkipElement (Fin.last M')).induced s t).2 ?_
        intro x hx
        have hx' := hle (Finset.mem_insert_of_mem hx)
        rcases Finset.mem_insert.1 hx' with rfl | hx2
        · exact absurd hx (ItActuallySkips _ s)
        · exact hx2
      · intro hst
        exact Finset.insert_subset_insert _ (((SkipElement (Fin.last M')).induced s t).1 hst)
    rcases h χ' with ⟨c, hc, f, hf, hcol⟩ | ⟨c, hc, _⟩
    · left
      let f' : Diamond 2 → NonemptyBooleanLattice (M' + 1) := fun x ↦
        ⟨insert (Fin.last M') ((SkipElement (Fin.last M')).φ (f x)),
          Finset.insert_ne_empty _ _⟩
      refine ⟨c, hc, f', ⟨fun x y hxy ↦ ?_, fun x y ↦ ?_⟩, fun x ↦ hcol x⟩
      · have h1 := congrArg Subtype.val hxy
        apply hf.1
        exact Finset.Subset.antisymm ((key (f x) (f y)).1 h1.subset)
          ((key (f y) (f x)).1 h1.symm.subset)
      · exact (hf.2 x y).trans (key (f x) (f y)).symm
    · exfalso
      have h1 : c.val ≥ a + 1 + 0 - 0 := (Finset.mem_filter.1 hc).2
      have h2 := c.isLt
      omega
  · have e : MixedRamseyNumber (a + 1) b = M := by
      rw [MainPos (by omega)]; omega
    rw [e] at h
    exact (MixedIgnoreEmptySet (P := Diamond 2) hb).1 h

/-! ### The core of Case 2, with N = M + 1 -/

lemma NoSingleton_core (a b M : ℕ)
    (IH : IsModifiedMixedRamseyUpperBound (Diamond 2) (Wedge 2) (a + 1) b M)
    (χ : Coloring (a + 1 + (b + 1)) (BooleanLattice (M + 1)))
    (h : ∀ S : BooleanLattice (M + 1), S.card = 1 → a + 1 ≤ (χ S).val) :
    HasSpecifiedMonochromeSubposet (Diamond 2) (BooleanLattice (M + 1)) (a + 1 + (b + 1)) χ
      (FirstAofK (a + 1) (a + 1 + (b + 1))) ∨
    HasSpecifiedMonochromeSubposet (Wedge 2) (BooleanLattice (M + 1)) (a + 1 + (b + 1)) χ
      (LastBofK (b + 1) (a + 1 + (b + 1))) := by
  classical
  by_cases hW : HasSpecifiedMonochromeSubposet (Wedge 2) (BooleanLattice (M + 1))
      (a + 1 + (b + 1)) χ (LastBofK (b + 1) (a + 1 + (b + 1)))
  · exact Or.inr hW
  left
  -- the F2-avoiding color ck of the singleton {0}
  obtain ⟨ck, hckdef⟩ : ∃ ck, ck = χ ({0} : BooleanLattice (M + 1)) := ⟨_, rfl⟩
  have hck : a + 1 ≤ ck.val := by
    rw [hckdef]; exact h {0} (Finset.card_singleton _)
  have hck0 : χ {0} = ck := hckdef.symm
  have hmem : ck ∈ LastBofK (b + 1) (a + 1 + (b + 1)) := by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    show ck.val ≥ a + 1 + (b + 1) - (b + 1)
    omega
  -- the shifted embedding Q_M → Q_{M+1}
  let ψ : BooleanLattice M → BooleanLattice (M + 1) :=
    fun x ↦ ShiftUp χ ck ((SkipElement (0 : Fin (M + 1))).φ x)
  have hskip : ∀ x : BooleanLattice M,
      (0 : Fin (M + 1)) ∉ (SkipElement (0 : Fin (M + 1))).φ x :=
    fun x ↦ ItActuallySkips (0 : Fin (M + 1)) x
  have hskipne : ∀ x : BooleanLattice M, x ≠ ∅ →
      (SkipElement (0 : Fin (M + 1))).φ x ≠ ∅ := fun x hx ↦
    Function.Injective.ne (SkipElement (0 : Fin (M + 1))).injective hx
  have hψ : ∀ x y : BooleanLattice M, ψ x ⊆ ψ y ↔ x ⊆ y := by
    intro x y
    refine (ShiftUp_subset_iff χ ck (hskip x) (hskip y)).trans ?_
    exact ((SkipElement (0 : Fin (M + 1))).induced x y).symm
  -- no ck on nonempty sets
  have hMiss : ∀ x : NonemptyBooleanLattice M, χ (ψ x.val) ≠ ck := fun x ↦
    ShiftUp_color_ne χ ck (LastBofK (b + 1) (a + 1 + (b + 1))) hmem hck0 hW
      (hskip x.val) (hskipne x.val x.property)
  -- induced copies in Q_M \ ∅ transport to Q_{M+1}
  have transport : ∀ {P : Type} [PartialOrder P] (f : P → NonemptyBooleanLattice M),
      IsInducedCopy f → IsInducedCopy (fun x ↦ ψ (f x).val) := by
    intro P _ f hf
    have key : ∀ x y : P, x ≤ y ↔ ψ (f x).val ⊆ ψ (f y).val :=
      fun x y ↦ (hf.2 x y).trans (hψ (f x).val (f y).val).symm
    refine ⟨fun x y hxy ↦ ?_, key⟩
    exact le_antisymm ((key x y).2 hxy.subset) ((key y x).2 hxy.symm.subset)
  -- delete the color ck
  let χ₀ : Coloring (a + 1 + b + 1) (NonemptyBooleanLattice M) := fun x ↦ χ (ψ x.val)
  have hMiss₀ : ∀ x, χ₀ x ≠ ck := hMiss
  let χ' : Coloring (a + 1 + b) (NonemptyBooleanLattice M) := ShrinkColoring χ₀ ck hMiss₀
  rcases IH χ' with ⟨c, hc, f, hf, hcol⟩ | ⟨c, hc, f, hf, hcol⟩
  · -- a diamond in a Q2 color: pull it back
    have hc' : c.val < a + 1 := (Finset.mem_filter.1 hc).2
    refine ⟨InvertRemoveColor (k := a + 1 + b) ck c, ?_, fun x ↦ ψ (f x).val,
      transport f hf, fun x ↦ ?_⟩
    · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      change (Fin.succAbove (n := a + 1 + b) ck c).val < a + 1
      rw [succAbove_val]
      split_ifs with hlt
      · exact hc'
      · exact absurd (lt_of_lt_of_le hc' hck) hlt
    · exact ShrinkColoring_spec χ₀ ck hMiss₀ (f x) c (hcol x)
  · -- a wedge in a wedge color: contradicts hW
    have hc' : a + 1 ≤ c.val := by
      have : c.val ≥ a + 1 + b - b := (Finset.mem_filter.1 hc).2
      omega
    refine absurd ?_ hW
    refine ⟨InvertRemoveColor (k := a + 1 + b) ck c, ?_, fun x ↦ ψ (f x).val,
      transport f hf, fun x ↦ ?_⟩
    · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      change (Fin.succAbove (n := a + 1 + b) ck c).val ≥ a + 1 + (b + 1) - (b + 1)
      rw [succAbove_val]
      split_ifs <;> omega
    · exact ShrinkColoring_spec χ₀ ck hMiss₀ (f x) c (hcol x)

lemma swap_val_lt {m a : ℕ} (c a' z : Fin m) (_ : c.val ≤ a) (ha' : a'.val = a)
    (hz : z.val < a) : (Equiv.swap c a' z).val < a + 1 := by
  by_cases hzc : z = c
  · rw [hzc, Equiv.swap_apply_left]; omega
  · rw [Equiv.swap_apply_of_ne_of_ne hzc (fun h ↦ by rw [h] at hz; omega)]; omega

lemma swap_of_ge {m a : ℕ} (c a' z : Fin m) (hc : c.val ≤ a) (ha' : a'.val = a)
    (hz : a + 1 ≤ z.val) : Equiv.swap c a' z = z :=
  Equiv.swap_apply_of_ne_of_ne (fun h ↦ by rw [h] at hz; omega)
    (fun h ↦ by rw [h] at hz; omega)

/-- Four sets forming a diamond give an induced `Diamond 2`. -/
lemma diamond_of_four {m : ℕ} {A B₁ B₂ C : BooleanLattice m}
    (hAB₁ : A ⊆ B₁) (hAB₂ : A ⊆ B₂) (hB₁C : B₁ ⊆ C) (hB₂C : B₂ ⊆ C)
    (hB₁₂ : ¬ B₁ ⊆ B₂) (hB₂₁ : ¬ B₂ ⊆ B₁) (hB₁A : ¬ B₁ ⊆ A) (hB₂A : ¬ B₂ ⊆ A) :
    ∃ f : Diamond 2 → BooleanLattice m, IsInducedCopy f ∧
      ∀ x : Diamond 2, f x = A ∨ f x = B₁ ∨ f x = B₂ ∨ f x = C := by
  classical
  have hAC : A ⊆ C := hAB₁.trans hB₁C
  have hCA : ¬ C ⊆ A := fun h ↦ hB₁A (hB₁C.trans h)
  have hCB₁ : ¬ C ⊆ B₁ := fun h ↦ hB₂₁ (hB₂C.trans h)
  have hCB₂ : ¬ C ⊆ B₂ := fun h ↦ hB₁₂ (hB₁C.trans h)
  let f : Diamond 2 → BooleanLattice m := fun w ↦
    if w.val = 0 then A else if w.val = 1 then B₁ else if w.val = 2 then B₂ else C
  have hf : ∀ p q : Diamond 2, DiamondOrder p q ↔ f p ≤ f q := by
    intro p q
    obtain ⟨i, hi⟩ := p
    obtain ⟨j, hj⟩ := q
    interval_cases i <;> interval_cases j <;>
      simp [DiamondOrder, f, hAB₁, hAB₂, hAC, hB₁C, hB₂C, hB₁₂, hB₂₁, hB₁A, hB₂A,
        hCA, hCB₁, hCB₂]
  refine ⟨f, ⟨?_, hf⟩, ?_⟩
  · intro p q hpq
    exact le_antisymm ((hf p q).2 hpq.le) ((hf q p).2 hpq.symm.le)
  · intro x
    obtain ⟨i, hi⟩ := x
    interval_cases i <;> simp [f]

/-- An induced wedge strictly above a set `A` extends to an induced diamond with bottom `A`. -/
lemma diamond_of_wedge {m : ℕ} {f : Wedge 2 → BooleanLattice m} (hf : IsInducedCopy f)
    {A : BooleanLattice m} (hA : ∀ w, A ⊆ f w) (hA' : ∀ w, ¬ f w ⊆ A) :
    ∃ g : Diamond 2 → BooleanLattice m, IsInducedCopy g ∧
      ∀ x, g x = A ∨ ∃ w, g x = f w := by
  have h01 : ¬ f ⟨0, by decide⟩ ⊆ f ⟨1, by decide⟩ := fun h ↦ by
    have h' : WedgeOrder (⟨0, by decide⟩ : Wedge 2) ⟨1, by decide⟩ :=
      (hf.2 ⟨0, by decide⟩ ⟨1, by decide⟩).2 h
    simp [WedgeOrder] at h'
  have h10 : ¬ f ⟨1, by decide⟩ ⊆ f ⟨0, by decide⟩ := fun h ↦ by
    have h' : WedgeOrder (⟨1, by decide⟩ : Wedge 2) ⟨0, by decide⟩ :=
      (hf.2 ⟨1, by decide⟩ ⟨0, by decide⟩).2 h
    simp [WedgeOrder] at h'
  have h02 : f ⟨0, by decide⟩ ⊆ f ⟨2, by decide⟩ :=
    (hf.2 ⟨0, by decide⟩ ⟨2, by decide⟩).1
      (show WedgeOrder (⟨0, by decide⟩ : Wedge 2) ⟨2, by decide⟩ from Or.inl rfl)
  have h12 : f ⟨1, by decide⟩ ⊆ f ⟨2, by decide⟩ :=
    (hf.2 ⟨1, by decide⟩ ⟨2, by decide⟩).1
      (show WedgeOrder (⟨1, by decide⟩ : Wedge 2) ⟨2, by decide⟩ from Or.inl rfl)
  obtain ⟨g, hg, hcases⟩ := diamond_of_four (A := A) (B₁ := f ⟨0, by decide⟩)
    (B₂ := f ⟨1, by decide⟩) (C := f ⟨2, by decide⟩)
    (hA _) (hA _) h02 h12 h01 h10 (hA' _) (hA' _)
  refine ⟨g, hg, fun x ↦ ?_⟩
  rcases hcases x with h | h | h | h
  · exact Or.inl h
  · exact Or.inr ⟨⟨0, by decide⟩, h⟩
  · exact Or.inr ⟨⟨1, by decide⟩, h⟩
  · exact Or.inr ⟨⟨2, by decide⟩, h⟩

/-! ### Core of Case 1, with N = M + 1 -/

lemma SingletonQ2_core (a b M : ℕ)
    (IH : IsModifiedMixedRamseyUpperBound (Diamond 2) (Wedge 2) a (b + 2) M)
    (χ : Coloring (a + 1 + (b + 1)) (BooleanLattice (M + 1)))
    (i : Fin (M + 1)) (hc0 : (χ {i}).val < a + 1) :
    HasSpecifiedMonochromeSubposet (Diamond 2) (BooleanLattice (M + 1)) (a + 1 + (b + 1)) χ
      (FirstAofK (a + 1) (a + 1 + (b + 1))) ∨
    HasSpecifiedMonochromeSubposet (Wedge 2) (BooleanLattice (M + 1)) (a + 1 + (b + 1)) χ
      (LastBofK (b + 1) (a + 1 + (b + 1))) := by
  classical
  have e : a + 1 + (b + 1) = a + (b + 2) := by omega
  obtain ⟨c, hcdef⟩ : ∃ c, c = χ ({i} : BooleanLattice (M + 1)) := ⟨_, rfl⟩
  have hc : c.val < a + 1 := by rw [hcdef]; exact hc0
  have hc' : c.val ≤ a := by omega
  let a' : Fin (a + 1 + (b + 1)) := ⟨a, by omega⟩
  have ha' : a'.val = a := rfl
  -- recoloring: swap c and a', then cast
  let g : Fin (a + 1 + (b + 1)) → Fin (a + (b + 2)) :=
    fun d ↦ Fin.cast e (Equiv.swap c a' d)
  have recolor : ∀ (y : Fin (a + 1 + (b + 1))) (d : Fin (a + (b + 2))), g y = d →
      y = Equiv.swap c a' (Fin.cast e.symm d) := by
    intro y d h
    have h1 : Equiv.swap c a' y = Fin.cast e.symm d := by
      apply Fin.ext
      have := congrArg Fin.val h
      simpa [g] using this
    rw [← h1, Equiv.swap_apply_self]
  -- copies in Q_M \ ∅ transport along the embedding onto strict supersets of {i}
  have transport : ∀ {P : Type} [PartialOrder P] (f : P → NonemptyBooleanLattice M),
      IsInducedCopy f → IsInducedCopy (fun x ↦ (LiftAbove i).φ (f x).val) :=
    fun f hf ↦ IsInducedCopy.of_nonempty (LiftAbove_isInducedCopy i) hf
  -- recolored coloring of Q_M \ ∅
  let χ' : Coloring (a + (b + 2)) (NonemptyBooleanLattice M) :=
    fun x ↦ g (χ ((LiftAbove i).φ x.val))
  rcases IH χ' with ⟨d, hd, f, hf, hcol⟩ | ⟨d, hd, f, hf, hcol⟩
  · -- diamond in a Q2 color of the new problem: also a Q2 color of the old one
    have hd' : d.val < a := (Finset.mem_filter.1 hd).2
    left
    refine ⟨Equiv.swap c a' (Fin.cast e.symm d), ?_,
      fun x ↦ (LiftAbove i).φ (f x).val, transport f hf,
      fun x ↦ recolor (χ ((LiftAbove i).φ (f x).val)) d (hcol x)⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    show (Equiv.swap c a' (Fin.cast e.symm d)).val < a + 1
    exact swap_val_lt c a' _ hc' ha' hd'
  · -- wedge in a wedge color of the new problem
    have hd' : a ≤ d.val := by
      have : d.val ≥ a + (b + 2) - (b + 2) := (Finset.mem_filter.1 hd).2
      omega
    by_cases hda : d.val = a
    · -- the swapped-in color is exactly c: put {i} under the wedge to get a diamond
      left
      have hd0 : Fin.cast e.symm d = a' := Fin.ext hda
      have hcolor : ∀ x, χ ((LiftAbove i).φ (f x).val) = c := fun x ↦ by
        rw [recolor (χ ((LiftAbove i).φ (f x).val)) d (hcol x), hd0, Equiv.swap_apply_right]
      obtain ⟨gD, hgD, hcases⟩ := diamond_of_wedge (transport f hf) (A := {i})
        (fun w ↦ LiftAbove_singleton_subset i (f w).val)
        (fun w ↦ not_LiftAbove_subset_singleton i (f w).property)
      refine ⟨c, Finset.mem_filter.2 ⟨Finset.mem_univ _, hc⟩, gD, hgD, fun x ↦ ?_⟩
      rcases hcases x with h | ⟨w, h⟩
      · rw [h]; exact hcdef.symm
      · rw [h]; exact hcolor w
    · -- genuinely a wedge color: the swap does nothing
      right
      have hge : a + 1 ≤ d.val := by omega
      refine ⟨Equiv.swap c a' (Fin.cast e.symm d), ?_,
        fun x ↦ (LiftAbove i).φ (f x).val, transport f hf,
        fun x ↦ recolor (χ ((LiftAbove i).φ (f x).val)) d (hcol x)⟩
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      rw [swap_of_ge c a' _ hc' ha' hge]
      change d.val ≥ a + 1 + (b + 1) - (b + 1)
      omega
