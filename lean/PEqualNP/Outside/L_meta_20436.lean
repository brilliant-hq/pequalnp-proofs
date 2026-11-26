import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_20436_aux
open PEqualNP.CircuitLowerBounds
def witness : Circuit := ⟨[⟨.or, [1, 9]⟩, ⟨.not, [10]⟩, ⟨.or, [5, 4]⟩, ⟨.or, [5, 4]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [14, 0]⟩, ⟨.and, [13, 11]⟩, ⟨.and, [15, 10]⟩, ⟨.or, [17, 16]⟩], 18⟩
end PEqualNP.Outside.L_meta_20436_aux
open PEqualNP.Outside.L_meta_20436_aux in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.L_meta_20436 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (15762641 : ℕ).testBit (5 * u.val + v.val)) C) := by
  exact ⟨witness, (by
    intro g hg
    have h : witness.gates.all (fun x => (match x.op with | .and | .or | .not => true | _ => false) && Nat.ble x.inputs.length 2) = true := by decide +kernel
    have q := List.all_eq_true.mp h g hg
    simp only [Bool.and_eq_true, Nat.ble_eq] at q
    refine ⟨?_, q.2⟩
    cases e : g.op <;> simp [e] at q ⊢), by decide +kernel, by decide +kernel⟩
