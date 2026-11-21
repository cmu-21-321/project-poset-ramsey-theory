import ProjectTemplate.Lemmas


/-!
Our main result: R(Q_2; k) = 2k.
-/
theorem MainTheorem : ∀ (k : ℕ), k ≥ 1 → IsMulticolorRamseyNumber (Diamond 2) k (2 * k) := by
  intro k hk
  constructor
  · exact MainTheoremLower k hk
  · exact MainTheoremUpper k hk
