import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_19505_aux
open PEqualNP.CircuitLowerBounds
def witness : Circuit := ⟨[⟨.or, [5, 4]⟩, ⟨.or, [9, 0]⟩, ⟨.not, [10]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [13, 8]⟩, ⟨.and, [13, 5]⟩, ⟨.not, [14]⟩, ⟨.or, [11, 10]⟩, ⟨.or, [12, 16]⟩, ⟨.and, [18, 17]⟩], 19⟩
end PEqualNP.Outside.L_meta_19505_aux
open PEqualNP.Outside.L_meta_19505_aux in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.L_meta_19505 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7882302 : ℕ).testBit (5 * u.val + v.val)) C) := by
  exact ⟨witness, (by
    intro g hg
    have h : witness.gates.all (fun x => (match x.op with | .and | .or | .not => true | _ => false) && Nat.ble x.inputs.length 2) = true := by decide +kernel
    have q := List.all_eq_true.mp h g hg
    simp only [Bool.and_eq_true, Nat.ble_eq] at q
    refine ⟨?_, q.2⟩
    cases e : g.op <;> simp [e] at q ⊢), by decide +kernel, by decide +kernel⟩
