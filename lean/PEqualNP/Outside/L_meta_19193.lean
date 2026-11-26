import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19193

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- A pair is accepted when both vertices are 1, or when neither is 1 and either vertex is 0.
private def witness : Circuit :=
  ⟨[⟨.and, [1, 5]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩,
    ⟨.not, [10]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [8, 12]⟩], 13⟩

theorem six_gate_representation :
    ∃ C : Circuit, FanInTwo C ∧ C.size = 6 ∧
      Represents (fun u v : Fin 4 => (4397 : ℕ).testBit (4 * u.val + v.val)) C :=
  ⟨witness, by simp [FanInTwo, witness], by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19193

open PEqualNP.Outside.L_meta_19193 in
theorem PEqualNP.Outside.L_meta_19193 :
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4397 : ℕ).testBit (4 * u.val + v.val)) C := by
  obtain ⟨C, hfan, hsize, hrep⟩ := six_gate_representation
  exact ⟨C, hfan, by omega, hrep⟩
