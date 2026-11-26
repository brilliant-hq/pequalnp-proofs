import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20017_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [8, 11]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [16, 17]⟩, ⟨.and, [3, 18]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [17, 20]⟩, ⟨.and, [7, 21]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [23, 24]⟩, ⟨.and, [0, 25]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [24, 27]⟩, ⟨.and, [4, 28]⟩, ⟨.or, [16, 20]⟩, ⟨.and, [5, 30]⟩, ⟨.or, [29, 31]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [23, 33]⟩, ⟨.and, [2, 34]⟩, ⟨.or, [32, 35]⟩, ⟨.or, [26, 36]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [27, 38]⟩, ⟨.and, [1, 39]⟩, ⟨.or, [33, 38]⟩, ⟨.and, [6, 41]⟩, ⟨.or, [40, 42]⟩, ⟨.or, [37, 43]⟩, ⟨.or, [22, 44]⟩, ⟨.or, [19, 45]⟩], 46⟩

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

end PEqualNP.Outside.L_meta_20017_aux

theorem PEqualNP.Outside.L_meta_20017 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12886077434404292460 : ℕ).testBit (8 * u.val + v.val)) 31) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  exact ⟨PEqualNP.Outside.L_meta_20017_aux.witness, PEqualNP.Outside.L_meta_20017_aux.witnessFit, by decide, by decide +kernel⟩
