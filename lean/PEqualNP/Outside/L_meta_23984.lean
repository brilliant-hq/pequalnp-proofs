import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_23984_aux
open PEqualNP.CircuitLowerBounds
def witness : Circuit := ⟨[⟨.not, [4]⟩, ⟨.not, [1]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [10, 0]⟩, ⟨.and, [11, 8]⟩], 12⟩
end PEqualNP.Outside.L_meta_23984_aux
open PEqualNP.Outside.L_meta_23984_aux in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.L_meta_23984 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (13085 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, (by
    intro g hg
    have h : witness.gates.all (fun x => (match x.op with | .and | .or | .not => true | _ => false) && Nat.ble x.inputs.length 2) = true := by decide +kernel
    have q := List.all_eq_true.mp h g hg
    simp only [Bool.and_eq_true, Nat.ble_eq] at q
    refine ⟨?_, q.2⟩
    cases e : g.op <;> simp [e] at q ⊢), by decide +kernel, by decide +kernel⟩
