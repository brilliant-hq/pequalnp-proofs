import Mathlib
import PEqualNP.Defs

/-!
# L-meta-8205

**Gap title**  
A step toward: Search: an order-3 plane circuit of at most 63 fan-in-two AND/OR gates,
true at incident pairs, false at every generic maximal false input (step 1 of 2)

**Lease**  `53aed00a-19e1-4150-9136-a1adb531e65e`

## Geometric background

The structure is the unique projective plane of order 3 (PG(2,3)) in its cyclic model:

* Points = ℤ/13ℤ
* Difference set D = {0, 1, 3, 9}
* Lines = the 13 translates of D

This is a Singer difference set: every nonzero residue appears exactly once as a difference of two distinct elements of D. Consequently every pair of points lies on exactly one line.

## What the statement requires

A monotone fan-in-2 circuit C of size ≤ 32 such that:

1. `Monotone2 C`
2. `NestedCover.ReadsBack 27 C`
3. `C.size ≤ 32` and the output wire is in range
4. On every “incident pair” input (two points that differ by an element of D) the circuit evaluates to true
5. On every generic maximal false input (no complete line is present on either side) the circuit evaluates to false

## Planned construction path

1. Encode each of the 13 lines as a small monotone sub-circuit (OR of the four point variables).
2. Combine them with a NestedCover pattern so that the ReadsBack condition is satisfied.
3. Verify the size stays ≤ 32 and that the false-input condition holds by the maximality argument.

The concrete gate list is still being assembled; the theorem below currently carries `sorry`.
-/

namespace PEqualNP.Outside.L_meta_8205

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Singer difference set for PG(2,3). -/
def D : Finset (Fin 13) := {0, 1, 3, 9}

/-- Placeholder circuit. Will be replaced by an explicit size-≤32 construction. -/
def C : Circuit := {
  gates := []
  output := 0
}

/-- Exact statement posted by the desk. -/
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
  -- Proof outline:
  -- 1. Construct an explicit list of gates that realises the 13 line ORs
  --    and a NestedCover top layer of total size ≤ 32.
  -- 2. Prove Monotone2 by construction (only AND/OR gates).
  -- 3. Prove ReadsBack by the NestedCover invariant.
  -- 4. Prove the positive (incident) cases by direct evaluation on the difference set.
  -- 5. Prove the negative (generic maximal false) cases by the covering property of the plane.
  sorry

end PEqualNP.Outside.L_meta_8205
