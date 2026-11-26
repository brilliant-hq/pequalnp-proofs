import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19557

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.and, [1, 9]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [5, 11]⟩, ⟨.or, [0, 12]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [14, 15]⟩, ⟨.not, [16]⟩, ⟨.and, [13, 17]⟩], 18⟩

theorem legal : FanInTwo witness := by
  simp [FanInTwo, witness]

end PEqualNP.Outside.L_meta_19557

theorem PEqualNP.Outside.L_meta_19557 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3247678 : ℕ).testBit (5 * u.val + v.val)) C) := by
  exact ⟨PEqualNP.Outside.L_meta_19557.witness, PEqualNP.Outside.L_meta_19557.legal, by decide, by decide +kernel⟩
