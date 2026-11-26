import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19996

def circuit : PEqualNP.CircuitLowerBounds.Circuit :=
  { gates := [⟨.or, [8, 10]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [8, 11]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [9, 13]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.or, [19, 13]⟩,
    ⟨.or, [17, 14]⟩,
    ⟨.or, [16, 15]⟩,
    ⟨.or, [12, 21]⟩,
    ⟨.or, [16, 22]⟩,
    ⟨.or, [17, 22]⟩,
    ⟨.or, [18, 23]⟩,
    ⟨.or, [20, 24]⟩,
    ⟨.or, [23, 24]⟩,
    ⟨.or, [18, 25]⟩,
    ⟨.or, [20, 25]⟩,
    ⟨.or, [22, 25]⟩,
    ⟨.and, [0, 33]⟩,
    ⟨.and, [1, 27]⟩,
    ⟨.and, [2, 26]⟩,
    ⟨.and, [3, 32]⟩,
    ⟨.and, [4, 29]⟩,
    ⟨.and, [5, 31]⟩,
    ⟨.and, [6, 30]⟩,
    ⟨.and, [7, 28]⟩,
    ⟨.or, [34, 35]⟩,
    ⟨.or, [42, 36]⟩,
    ⟨.or, [43, 37]⟩,
    ⟨.or, [44, 38]⟩,
    ⟨.or, [45, 39]⟩,
    ⟨.or, [46, 40]⟩,
    ⟨.or, [47, 41]⟩]
    output := 48 }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 100000 in
lemma size_bound : circuit.size ≤ 33 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma represented : PEqualNP.Represents.Represents
    (fun u v : Fin 8 => (5748802764708593400 : ℕ).testBit (8 * u.val + v.val)) circuit := by
  decide

end PEqualNP.Outside.L_meta_19996

theorem PEqualNP.Outside.L_meta_19996 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5748802764708593400 : ℕ).testBit (8 * u.val + v.val)) 33 := by
  exact ⟨PEqualNP.Outside.L_meta_19996.circuit, PEqualNP.Outside.L_meta_19996.monotone,
    PEqualNP.Outside.L_meta_19996.size_bound, PEqualNP.Outside.L_meta_19996.represented⟩
