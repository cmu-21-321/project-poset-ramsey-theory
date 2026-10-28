import ProjectTemplate.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith



theorem ExistsUniqueRamsey (P : Type) [PartialOrder P] (k : ℕ) :
    ∃! (N : ℕ), IsMulticolorRamseyNumber P k N := by
  sorry

--R (F2, k) = k+1
theorem FanBound (k : ℕ) (hk : k ≥ 1) : IsMulticolorRamseyNumber (Wedge 2) k (k + 1) := by
  induction k, hk using Nat.le_induction with
  | base =>
    constructor
    · intro n hn
      use fun _ => 0
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


    · intro n hn χ
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

      let f : (Wedge 2 → BooleanLattice n) := fun i ↦ if i.val = 0 then ({a} : Finset (Fin n))
                                              else if i.val = 1 then ({b} : Finset (Fin n))
                                              else ({a,b} : Finset (Fin n))
      use f
      constructor
      · sorry --just need to case on values.
      · simp[hχ]
  | succ n hn ih => sorry
