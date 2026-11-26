import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_24187_aux
open PEqualNP.CircuitLowerBounds
def witness : Circuit := ⟨[⟨.or, [1, 4]⟩, ⟨.or, [3, 2]⟩, ⟨.or, [5, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [5, 6]⟩, ⟨.and, [7, 0]⟩, ⟨.or, [10, 6]⟩, ⟨.not, [8]⟩, ⟨.or, [11, 1]⟩, ⟨.not, [9]⟩, ⟨.and, [12, 3]⟩, ⟨.and, [12, 14]⟩, ⟨.and, [16, 13]⟩], 17⟩
end PEqualNP.Outside.L_meta_24187_aux
open PEqualNP.Outside.L_meta_24187_aux in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.L_meta_24187 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266846 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, (by
    intro g hg
    have h : witness.gates.all (fun x => (match x.op with | .and | .or | .not => true | _ => false) && Nat.ble x.inputs.length 2) = true := by decide +kernel
    have q := List.all_eq_true.mp h g hg
    simp only [Bool.and_eq_true, Nat.ble_eq] at q
    refine ⟨?_, q.2⟩
    cases e : g.op <;> simp [e] at q ⊢), by decide +kernel, by decide +kernel⟩
