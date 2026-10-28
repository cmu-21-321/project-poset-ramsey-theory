import ProjectTemplate.Defs
import Mathlib.Tactic.FinCases

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
      rintro ⟨n, iso, inducedCopy, d⟩

      have hnz : n = 0 := by
        fin_cases n
        rfl
      sorry

    · sorry
  | succ n hn ih => sorry
