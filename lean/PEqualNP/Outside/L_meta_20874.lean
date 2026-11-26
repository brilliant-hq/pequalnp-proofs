import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_20874_aux
open PEqualNP.CircuitLowerBounds
def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [5, 10]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [4, 12]⟩, ⟨.or, [11, 15]⟩, ⟨.or, [4, 14]⟩, ⟨.and, [16, 17]⟩, ⟨.or, [13, 18]⟩], 19⟩
end PEqualNP.Outside.L_meta_20874_aux
open PEqualNP.Outside.L_meta_20874_aux in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.L_meta_20874 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (31660065 : ℕ).testBit (5 * u.val + v.val)) 10) := by
  exact ⟨witness, (by
    intro g hg
    have h : witness.gates.all (fun x => (match x.op with | .and | .or => true | _ => false) && Nat.ble x.inputs.length 2) = true := by decide +kernel
    have q := List.all_eq_true.mp h g hg
    simp only [Bool.and_eq_true, Nat.ble_eq] at q
    refine ⟨?_, q.2⟩
    cases e : g.op <;> simp [e] at q ⊢), by decide +kernel, by decide +kernel⟩
