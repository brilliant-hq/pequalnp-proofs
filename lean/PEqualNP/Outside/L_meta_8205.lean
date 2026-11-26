import Mathlib
import PEqualNP.Defs

/-!
L-meta-8205
A step toward: Search: an order-3 plane circuit of at most 63 fan-in-two AND/OR gates,
true at incident pairs, false at every generic maximal false input (step 1 of 2)

This file contains the exact posted statement. The circuit witness is still being constructed.
-/

namespace PEqualNP.Outside.L_meta_8205

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

-- The difference set for PG(2,3)
def D : Finset (Fin 13) := {0, 1, 3, 9}

-- Placeholder for the required circuit of size ≤ 32.
-- A concrete construction meeting NestedCover.ReadsBack and the incidence conditions
-- is the remaining work.
def C : Circuit := {
  gates := []
  output := 0
}

/-- Exact statement from the desk. -/
theorem L_meta_8205 :
  ∃ (C : Circuit),
    Monotone2 C ∧
    NestedCover.ReadsBack 27 C ∧
    C.size ≤ 32 ∧
    C.output < 27 + C.size ∧
    (∀ (x5 x6 : Fin 13), ↑x6 < 7 →
      (∃ x4 ∈ D, x5 = x6 + x4) →
      circuitFun 27 C (fun x9 => decide (x9 = Fin.castAdd 13 x5 ∨ x9 = Fin.natAdd 13 x6)) = true) ∧
    (∀ (x5 : Fin 26 → Bool),
      (∀ (x6 x7 : Fin 13), (∃ x4 ∈ D, x6 = x7 + x4) → x5 (Fin.castAdd 13 x6) = true → x5 (Fin.natAdd 13 x7) ≠ true) →
      (¬∃ (x7 : Fin 13), ∀ (x8 : Fin 13), x5 (Fin.castAdd 13 x8) = true → (∃ x4 ∈ D, x8 = x7 + x4)) →
      (¬∃ (x8 : Fin 13), ∀ (x9 : Fin 13), x5 (Fin.natAdd 13 x9) = true → (∃ x4 ∈ D, x8 = x9 + x4)) →
      circuitFun 27 C (fun i => if i.val < 26 then x5 ⟨i.val, by omega⟩ else false) = false) := by
  sorry

end PEqualNP.Outside.L_meta_8205
