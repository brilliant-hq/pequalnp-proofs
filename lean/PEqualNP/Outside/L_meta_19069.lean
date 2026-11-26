import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_19069_aux
open PEqualNP.CircuitLowerBounds
def witness : Circuit := ⟨[⟨.and, [2, 4]⟩, ⟨.not, [4]⟩, ⟨.and, [0, 9]⟩, ⟨.not, [7]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [8, 13]⟩], 14⟩
end PEqualNP.Outside.L_meta_19069_aux
open PEqualNP.Outside.L_meta_19069_aux in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.L_meta_19069 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (382 : ℕ).testBit (4 * u.val + v.val)) C) := by
  exact ⟨witness, (by
    intro g hg
    have h : witness.gates.all (fun x => (match x.op with | .and | .or | .not => true | _ => false) && Nat.ble x.inputs.length 2) = true := by decide +kernel
    have q := List.all_eq_true.mp h g hg
    simp only [Bool.and_eq_true, Nat.ble_eq] at q
    refine ⟨?_, q.2⟩
    cases e : g.op <;> simp [e] at q ⊢), by decide +kernel, by decide +kernel⟩
