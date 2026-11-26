import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_20639

def witness : Circuit :=
  ⟨[⟨.and, [3, 5]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [5, 12]⟩, ⟨.and, [11, 13]⟩], 14⟩

def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

theorem witnessMono : Monotone2 witness := by
  have legal : witness.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩

end PEqualNP.Outside.L_meta_20639

open PEqualNP.Outside.L_meta_20639 in
theorem PEqualNP.Outside.L_meta_20639 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (7372800 : ℕ).testBit (5 * u.val + v.val)) 5 := by
  exact ⟨witness, witnessMono, by decide, by decide +kernel⟩
