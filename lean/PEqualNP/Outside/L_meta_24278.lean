import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_24278_aux
open PEqualNP.CircuitLowerBounds
def witness : Circuit := ⟨[⟨.not, [4]⟩, ⟨.not, [3]⟩, ⟨.not, [5]⟩, ⟨.or, [1, 7]⟩, ⟨.and, [6, 8]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [0, 11]⟩], 12⟩
end PEqualNP.Outside.L_meta_24278_aux
open PEqualNP.Outside.L_meta_24278_aux in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.L_meta_24278 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17343 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, (by
    intro g hg
    have h : witness.gates.all (fun x => (match x.op with | .and | .or | .not => true | _ => false) && Nat.ble x.inputs.length 2) = true := by decide +kernel
    have q := List.all_eq_true.mp h g hg
    simp only [Bool.and_eq_true, Nat.ble_eq] at q
    refine ⟨?_, q.2⟩
    cases e : g.op <;> simp [e] at q ⊢), by decide +kernel, by decide +kernel⟩
