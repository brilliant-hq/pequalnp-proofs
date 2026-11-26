import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_23986_aux
open PEqualNP.CircuitLowerBounds
def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [5, 4]⟩, ⟨.and, [7, 2]⟩, ⟨.or, [2, 1]⟩, ⟨.or, [9, 5]⟩, ⟨.not, [8]⟩, ⟨.and, [10, 11]⟩], 12⟩
end PEqualNP.Outside.L_meta_23986_aux
open PEqualNP.Outside.L_meta_23986_aux in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.L_meta_23986 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (13147 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, (by
    intro g hg
    have h : witness.gates.all (fun x => (match x.op with | .and | .or | .not => true | _ => false) && Nat.ble x.inputs.length 2) = true := by decide +kernel
    have q := List.all_eq_true.mp h g hg
    simp only [Bool.and_eq_true, Nat.ble_eq] at q
    refine ⟨?_, q.2⟩
    cases e : g.op <;> simp [e] at q ⊢), by decide +kernel, by decide +kernel⟩
