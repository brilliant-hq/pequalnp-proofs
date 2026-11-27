import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19026 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.GenericRejection.ComputesIncidence PEqualNP.HeptadCover.singerLines3 x1 → PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x1 (2 : ℕ) → (64 : ℕ) ≤ x1.size) := by
    intro c hm hc hd
    first
    | exact?
    | apply? <;> first | assumption | decide | omega | exact?
    | change 13 * 4 + 13 - 1 ≤ c.size
      exact?
    | refine Nat.le_trans ?num ?bound
      case bound =>
        first
        | exact? using hc, hd
        | exact? using hc
        | exact? using hd
      case num => first | decide | omega | exact?
    | by_contra hn
      have hlt : c.size < 64 := by omega
      have hle : c.size ≤ 63 := by omega
      first
      | exact?
      | revert hd
        exact?
      | revert hc
        exact?
      | grind +suggestions
      | grind +suggestions [PEqualNP.CircuitLowerBounds.HasLineDegree, PEqualNP.GenericRejection.ComputesIncidence, PEqualNP.MetaComplexity.Monotone2]
      | simp_all [PEqualNP.CircuitLowerBounds.HasLineDegree, PEqualNP.GenericRejection.ComputesIncidence, PEqualNP.MetaComplexity.Monotone2] <;> first | omega | exact? | grind
