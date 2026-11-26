import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21258

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- Ten gates; wires 0 to 3 are the left vertices, 4 to 8 the right ones. -/
def circ : Circuit :=
  ⟨[⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [9, 2]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [0, 5]⟩,
    ⟨GateOp.and, [11, 12]⟩, ⟨GateOp.or, [13, 1]⟩, ⟨GateOp.or, [12, 10]⟩, ⟨GateOp.or, [15, 3]⟩,
    ⟨GateOp.or, [14, 4]⟩, ⟨GateOp.and, [17, 16]⟩], 18⟩

theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 5) => (36317 : ℕ).testBit (5 * u.val + v.val))
    circ := by
  decide

end PEqualNP.Outside.L_meta_21258

theorem PEqualNP.Outside.L_meta_21258 :
    PEqualNP.Represents.RepSizeAtMost
      (fun (u : Fin 4) (v : Fin 5) => (36317 : ℕ).testBit (5 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_21258.circ, PEqualNP.Outside.L_meta_21258.mono, by decide,
    PEqualNP.Outside.L_meta_21258.rep⟩
