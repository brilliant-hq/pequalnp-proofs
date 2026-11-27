import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1208

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.and, [4, 6]⟩, ⟨.or, [3, 0]⟩, ⟨.or, [4, 0]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [8, 12]⟩, ⟨.and, [10, 2]⟩, ⟨.or, [14, 13]⟩, ⟨.and, [5, 11]⟩, ⟨.or, [16, 15]⟩], 17⟩

end PEqualNP.Outside.L_meta_1208

set_option maxHeartbeats 8000000 in
open PEqualNP.Outside.L_meta_1208 in
theorem PEqualNP.Outside.L_meta_1208 :
∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 7)) x
:= by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.FanInTwo, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩
