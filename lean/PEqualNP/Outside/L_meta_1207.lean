import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1207

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [3, 4]⟩, ⟨.and, [6, 7]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [4, 0]⟩, ⟨.and, [11, 2]⟩, ⟨.or, [10, 9]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [1, 14]⟩, ⟨.or, [13, 12]⟩, ⟨.or, [16, 15]⟩], 17⟩

end PEqualNP.Outside.L_meta_1207

set_option maxHeartbeats 8000000 in
open PEqualNP.Outside.L_meta_1207 in
theorem PEqualNP.Outside.L_meta_1207 :
∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 6 && x 7)) x
:= by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.FanInTwo, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩
