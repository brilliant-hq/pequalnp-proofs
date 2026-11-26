import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20030_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [6, 10]⟩, ⟨.or, [3, 14]⟩, ⟨.or, [7, 17]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [4, 19]⟩, ⟨.and, [9, 20]⟩, ⟨.or, [5, 11]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [22, 23]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [24, 25]⟩, ⟨.and, [13, 26]⟩, ⟨.or, [2, 25]⟩, ⟨.or, [18, 28]⟩, ⟨.or, [6, 22]⟩, ⟨.or, [18, 30]⟩, ⟨.or, [23, 28]⟩, ⟨.and, [31, 32]⟩, ⟨.or, [8, 33]⟩, ⟨.and, [29, 34]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [30, 36]⟩, ⟨.and, [15, 37]⟩, ⟨.or, [35, 38]⟩, ⟨.or, [27, 39]⟩, ⟨.or, [7, 24]⟩, ⟨.or, [3, 16]⟩, ⟨.and, [41, 42]⟩, ⟨.or, [40, 43]⟩, ⟨.or, [21, 44]⟩], 45⟩

def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

theorem witnessFit : Monotone2 witness := by
  have legal : witness.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩

end PEqualNP.Outside.L_meta_20030_aux

theorem PEqualNP.Outside.L_meta_20030 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1700870159931663465 : ℕ).testBit (8 * u.val + v.val)) 31) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  exact ⟨PEqualNP.Outside.L_meta_20030_aux.witness, PEqualNP.Outside.L_meta_20030_aux.witnessFit, by decide, by decide +kernel⟩
