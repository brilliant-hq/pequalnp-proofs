import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19096
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
def circ : Circuit := ⟨[⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.or, [3, 9]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.not, [13]⟩], 14⟩
theorem allOk : circ.gates.all okGate = true := by decide
theorem fan : FanInTwo circ := by
  intro g hg
  have h := List.all_eq_true.mp allOk g hg
  simp only [okGate, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨okOp_mem h.1, h.2⟩
theorem sz : circ.size ≤ 7 := by decide
theorem rep : Represents (fun u v : Fin 4 => (1981 : ℕ).testBit (4 * u.val + v.val)) circ := by decide +kernel
end PEqualNP.Outside.L_meta_19096

theorem PEqualNP.Outside.L_meta_19096 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (1981 : ℕ).testBit (4 * u.val + v.val)) C) :=
  ⟨PEqualNP.Outside.L_meta_19096.circ, PEqualNP.Outside.L_meta_19096.fan, PEqualNP.Outside.L_meta_19096.sz, PEqualNP.Outside.L_meta_19096.rep⟩
