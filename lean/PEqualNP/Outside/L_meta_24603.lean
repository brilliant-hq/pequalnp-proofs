import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_24603_aux
open PEqualNP.CircuitLowerBounds
def witness : Circuit := ⟨[⟨.or, [0, 5]⟩, ⟨.or, [3, 2]⟩, ⟨.and, [7, 4]⟩, ⟨.or, [8, 6]⟩, ⟨.not, [9]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [5, 2]⟩, ⟨.or, [10, 11]⟩], 13⟩
end PEqualNP.Outside.L_meta_24603_aux
open PEqualNP.Outside.L_meta_24603_aux in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.L_meta_24603 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270583712 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, (by
    intro g hg
    have h : witness.gates.all (fun x => (match x.op with | .and | .or | .not => true | _ => false) && Nat.ble x.inputs.length 2) = true := by decide +kernel
    have q := List.all_eq_true.mp h g hg
    simp only [Bool.and_eq_true, Nat.ble_eq] at q
    refine ⟨?_, q.2⟩
    cases e : g.op <;> simp [e] at q ⊢), by decide +kernel, by decide +kernel⟩
