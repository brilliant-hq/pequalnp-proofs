import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_23152

def witness : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [5, 11]⟩, ⟨.or, [1, 12]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [6, 14]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [13, 15]⟩, ⟨.or, [16, 17]⟩], 18⟩

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

end PEqualNP.Outside.L_meta_23152

open PEqualNP.Outside.L_meta_23152 in
theorem PEqualNP.Outside.L_meta_23152 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (30456 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  exact ⟨witness, witnessMono, by decide, by decide +kernel⟩
