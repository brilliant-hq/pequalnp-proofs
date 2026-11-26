import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_19667_aux
open PEqualNP.CircuitLowerBounds
def witness : Circuit := ⟨[⟨.or, [6, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.not, [1]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [0, 11]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [5, 16]⟩, ⟨.and, [12, 17]⟩, ⟨.or, [13, 18]⟩], 19⟩
end PEqualNP.Outside.L_meta_19667_aux
open PEqualNP.Outside.L_meta_19667_aux in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.L_meta_19667 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7373913 : ℕ).testBit (5 * u.val + v.val)) C) := by
  exact ⟨witness, (by
    intro g hg
    have h : witness.gates.all (fun x => (match x.op with | .and | .or | .not => true | _ => false) && Nat.ble x.inputs.length 2) = true := by decide +kernel
    have q := List.all_eq_true.mp h g hg
    simp only [Bool.and_eq_true, Nat.ble_eq] at q
    refine ⟨?_, q.2⟩
    cases e : g.op <;> simp [e] at q ⊢), by decide +kernel, by decide +kernel⟩
