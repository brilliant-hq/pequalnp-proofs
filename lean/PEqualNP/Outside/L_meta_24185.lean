import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_24185_aux
open PEqualNP.CircuitLowerBounds
def witness : Circuit := ⟨[⟨.and, [4, 1]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [4, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [8, 4]⟩, ⟨.or, [9, 7]⟩, ⟨.or, [11, 6]⟩, ⟨.not, [12]⟩, ⟨.or, [12, 6]⟩, ⟨.or, [12, 4]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [13, 16]⟩], 17⟩
end PEqualNP.Outside.L_meta_24185_aux
open PEqualNP.Outside.L_meta_24185_aux in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.L_meta_24185 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266770 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, (by
    intro g hg
    have h : witness.gates.all (fun x => (match x.op with | .and | .or | .not => true | _ => false) && Nat.ble x.inputs.length 2) = true := by decide +kernel
    have q := List.all_eq_true.mp h g hg
    simp only [Bool.and_eq_true, Nat.ble_eq] at q
    refine ⟨?_, q.2⟩
    cases e : g.op <;> simp [e] at q ⊢), by decide +kernel, by decide +kernel⟩
