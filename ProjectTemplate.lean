import ProjectTemplate.Basic
import ProjectTemplate.Defs.lean
#eval hello

--uses fall files there.



theorem ramseyPoset (k n : ℕ) (hn : n ≥ 2) (hk : k ≥ 1):=
  ∀(χ : Coloring k) (MonochromeSubgraph (Q (n * k)) (D n)) χ := by
    sorry
