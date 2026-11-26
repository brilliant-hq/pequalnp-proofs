import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_24034_aux
open PEqualNP.CircuitLowerBounds
def witness : Circuit := ⟨[⟨.or, [4, 3]⟩, ⟨.or, [5, 1]⟩, ⟨.and, [6, 0]⟩, ⟨.and, [5, 6]⟩, ⟨.and, [5, 8]⟩, ⟨.not, [1]⟩, ⟨.or, [5, 0]⟩, ⟨.not, [11]⟩, ⟨.or, [12, 7]⟩], 13⟩
end PEqualNP.Outside.L_meta_24034_aux
open PEqualNP.Outside.L_meta_24034_aux in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.L_meta_24034 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4314 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, (by
    intro g hg
    have h : witness.gates.all (fun x => (match x.op with | .and | .or | .not => true | _ => false) && Nat.ble x.inputs.length 2) = true := by decide +kernel
    have q := List.all_eq_true.mp h g hg
    simp only [Bool.and_eq_true, Nat.ble_eq] at q
    refine ⟨?_, q.2⟩
    cases e : g.op <;> simp [e] at q ⊢), by decide +kernel, by decide +kernel⟩
