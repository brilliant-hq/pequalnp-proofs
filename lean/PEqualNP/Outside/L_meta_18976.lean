import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_18976 : ∀ (x1 : Finset (Fin (13 : ℕ))), x1.card ≤ (3 : ℕ) → ∃ x3 ∈ [(67100672 : ℕ), (25018369 : ℕ), (7962627 : ℕ), (24444933 : ℕ), (7405575 : ℕ), (6815755 : ℕ), (23330829 : ℕ), (5799955 : ℕ), (22282261 : ℕ), (21757977 : ℕ), (19988517 : ℕ), (19415081 : ℕ), (6619269 : ℕ), (2179233 : ℕ)], ∃ x4 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∃ (x5 : Fin (13 : ℕ)), ∀ (x6 : Fin (13 : ℕ)), Decidable.decide (x6 ∈ x1) = x3.testBit ↑(x4 * x6 + x5) := by
  decide +kernel
