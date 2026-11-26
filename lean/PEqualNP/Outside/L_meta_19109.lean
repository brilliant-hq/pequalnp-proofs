import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19109
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def okOp : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | GateOp.not => true
  | _ => false
theorem okOp_mem {o : GateOp} (h : okOp o = true) :
    o ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) := by
  cases o <;> simp_all [okOp]
def okGate (g : Gate) : Bool := okOp g.op && decide (g.inputs.length ≤ 2)
def circ : Circuit := ⟨[⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [6, 9]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.and, [8, 11]⟩, ⟨GateOp.or, [13, 14]⟩], 15⟩
theorem allOk : circ.gates.all okGate = true := by decide
theorem fan : FanInTwo circ := by
  intro g hg
  have h := List.all_eq_true.mp allOk g hg
  simp only [okGate, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨okOp_mem h.1, h.2⟩
theorem sz : circ.size ≤ 8 := by decide
theorem rep : Represents (fun u v : Fin 4 => (15838 : ℕ).testBit (4 * u.val + v.val)) circ := by decide +kernel
end PEqualNP.Outside.L_meta_19109

theorem PEqualNP.Outside.L_meta_19109 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (15838 : ℕ).testBit (4 * u.val + v.val)) C) :=
  ⟨PEqualNP.Outside.L_meta_19109.circ, PEqualNP.Outside.L_meta_19109.fan, PEqualNP.Outside.L_meta_19109.sz, PEqualNP.Outside.L_meta_19109.rep⟩
