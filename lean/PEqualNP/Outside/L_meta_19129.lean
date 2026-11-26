import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19129_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 5]⟩,
      ⟨GateOp.and, [0, 5]⟩,
      ⟨GateOp.not, [11]⟩,
      ⟨GateOp.and, [10, 12]⟩
    ]
    output := 13 }

theorem C_fanInTwo : FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

theorem C_size : C.size ≤ 4 := by decide

theorem C_rep : Represents (fun u v : Fin 5 => xor (decide (u = 0)) (decide (v = 0))) C := by
  rintro ⟨u, hu⟩ ⟨v, hv⟩
  match u, v with
  | 0, 0 => rfl | 0, 1 => rfl | 0, 2 => rfl | 0, 3 => rfl | 0, 4 => rfl
  | 1, 0 => rfl | 1, 1 => rfl | 1, 2 => rfl | 1, 3 => rfl | 1, 4 => rfl
  | 2, 0 => rfl | 2, 1 => rfl | 2, 2 => rfl | 2, 3 => rfl | 2, 4 => rfl
  | 3, 0 => rfl | 3, 1 => rfl | 3, 2 => rfl | 3, 3 => rfl | 3, 4 => rfl
  | 4, 0 => rfl | 4, 1 => rfl | 4, 2 => rfl | 4, 3 => rfl | 4, 4 => rfl
  | _ + 5, _ => omega
  | _, _ + 5 => omega

end PEqualNP.Outside.L_meta_19129_aux

theorem PEqualNP.Outside.L_meta_19129 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => xor (decide (u = 0)) (decide (v = 0))) C :=
  ⟨PEqualNP.Outside.L_meta_19129_aux.C,
   PEqualNP.Outside.L_meta_19129_aux.C_fanInTwo,
   PEqualNP.Outside.L_meta_19129_aux.C_size,
   PEqualNP.Outside.L_meta_19129_aux.C_rep⟩
