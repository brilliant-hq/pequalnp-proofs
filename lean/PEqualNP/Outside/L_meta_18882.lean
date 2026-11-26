import PEqualNP.Defs

set_option maxHeartbeats 10000 in
theorem PEqualNP.Outside.L_meta_18882 : PEqualNP.TopForm.NoFourCycle (SimpleGraph.fromRel fun (x1 x2 : Fin (26 : ℕ)) => ↑x1 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x2 ∧ (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) := by
  first
  | solve | rfl
  | solve | intros; assumption
  | solve | intro prior; intros; apply prior <;> first | assumption | exact le_rfl | omega
  | solve | dsimp only; intros; grind only
  | solve | intros; omega
  | solve | simp_all
  | solve | decide +revert +kernel
