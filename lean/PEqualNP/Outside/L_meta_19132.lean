import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19132

open PEqualNP.CircuitLowerBounds

def circ : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [14, 15]⟩], 16⟩

theorem mono : PEqualNP.MetaComplexity.Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : PEqualNP.Represents.Represents (fun u v : Fin 5 => !(decide (u = 0) && decide (v = 0))) circ := by
  decide

end PEqualNP.Outside.L_meta_19132

theorem PEqualNP.Outside.L_meta_19132 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => !(decide (u = 0) && decide (v = 0))) 7) :=
  ⟨PEqualNP.Outside.L_meta_19132.circ, PEqualNP.Outside.L_meta_19132.mono, by decide, PEqualNP.Outside.L_meta_19132.rep⟩
