import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19800_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [1, 4]⟩, ⟨.or, [5, 16]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [3, 18]⟩, ⟨.or, [17, 19]⟩, ⟨.and, [10, 20]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [5, 23]⟩, ⟨.or, [22, 24]⟩, ⟨.and, [11, 25]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [5, 27]⟩, ⟨.or, [3, 23]⟩, ⟨.or, [28, 29]⟩, ⟨.and, [8, 30]⟩, ⟨.or, [26, 31]⟩, ⟨.or, [21, 32]⟩, ⟨.or, [3, 27]⟩, ⟨.or, [22, 34]⟩, ⟨.and, [15, 35]⟩, ⟨.or, [18, 28]⟩, ⟨.and, [14, 37]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [17, 39]⟩, ⟨.and, [12, 40]⟩, ⟨.or, [38, 41]⟩, ⟨.or, [36, 42]⟩, ⟨.or, [19, 39]⟩, ⟨.and, [13, 44]⟩, ⟨.or, [43, 45]⟩, ⟨.or, [16, 29]⟩, ⟨.and, [9, 47]⟩, ⟨.or, [46, 48]⟩, ⟨.or, [33, 49]⟩], 50⟩

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

end PEqualNP.Outside.L_meta_19800_aux

theorem PEqualNP.Outside.L_meta_19800 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (4317929078742808305 : ℕ).testBit (8 * u.val + v.val)) 37) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  exact ⟨PEqualNP.Outside.L_meta_19800_aux.witness, PEqualNP.Outside.L_meta_19800_aux.witnessFit, by decide, by decide +kernel⟩
