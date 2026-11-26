import PEqualNP.Defs

-- Circuit wiring adapted from ArtSabintsev, L-meta-20344, upstream PR 27055.
-- The two input permutations transport that witness to the assigned matrix.

namespace Experiment033
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[
  ⟨.or, [4, 9]⟩,
  ⟨.or, [5, 10]⟩,
  ⟨.or, [6, 16]⟩,
  ⟨.or, [3, 13]⟩,
  ⟨.or, [7, 11]⟩,
  ⟨.or, [2, 15]⟩,
  ⟨.or, [0, 8]⟩,
  ⟨.or, [15, 12]⟩,
  ⟨.or, [17, 1]⟩,
  ⟨.or, [24, 14]⟩,
  ⟨.or, [19, 1]⟩,
  ⟨.or, [26, 12]⟩,
  ⟨.or, [21, 7]⟩,
  ⟨.or, [28, 14]⟩,
  ⟨.or, [18, 3]⟩,
  ⟨.or, [16, 19]⟩,
  ⟨.or, [31, 21]⟩,
  ⟨.or, [18, 17]⟩,
  ⟨.or, [33, 20]⟩,
  ⟨.or, [34, 12]⟩,
  ⟨.and, [22, 35]⟩,
  ⟨.and, [25, 32]⟩,
  ⟨.and, [27, 29]⟩,
  ⟨.and, [30, 20]⟩,
  ⟨.and, [6, 23]⟩,
  ⟨.or, [36, 37]⟩,
  ⟨.or, [38, 39]⟩,
  ⟨.or, [41, 42]⟩,
  ⟨.or, [43, 40]⟩], 44⟩

def binaryAO (g : Gate) : Bool :=
  (match g.op with
   | .and | .or => true
   | _ => false) && (g.inputs.length ≤ 2)

theorem checked_types : Monotone2 witness := by
  have h : witness.gates.all binaryAO = true := by decide +kernel
  intro g hg
  have hy := List.all_eq_true.mp h g hg
  simp only [binaryAO, Bool.and_eq_true, decide_eq_true_eq] at hy
  refine ⟨?_, hy.2⟩
  cases hk : g.op <;> simp [hk] at hy ⊢

end Experiment033

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_20315 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3718182521909076510 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨Experiment033.witness, Experiment033.checked_types, by decide +kernel, by decide +kernel⟩
