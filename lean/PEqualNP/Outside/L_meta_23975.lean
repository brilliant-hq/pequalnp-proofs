import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_23975_aux
open PEqualNP.CircuitLowerBounds
def witness : Circuit := ⟨[⟨.and, [3, 2]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [1, 0]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [9, 8]⟩, ⟨.and, [11, 10]⟩], 12⟩
end PEqualNP.Outside.L_meta_23975_aux
open PEqualNP.Outside.L_meta_23975_aux in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.L_meta_23975 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (9118 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, (by
    intro g hg
    have h : witness.gates.all (fun x => (match x.op with | .and | .or | .not => true | _ => false) && Nat.ble x.inputs.length 2) = true := by decide +kernel
    have q := List.all_eq_true.mp h g hg
    simp only [Bool.and_eq_true, Nat.ble_eq] at q
    refine ⟨?_, q.2⟩
    cases e : g.op <;> simp [e] at q ⊢), by decide +kernel, by decide +kernel⟩
