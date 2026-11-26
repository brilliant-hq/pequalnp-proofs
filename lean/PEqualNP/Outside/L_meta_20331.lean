import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20331

open PEqualNP.CircuitLowerBounds

private def gateMono2 (g : Gate) : Bool :=
  (match g.op with | .and => true | .or => true | _ => false) && g.inputs.length ≤ 2

private theorem gateMono2_sound (g : Gate) (h : gateMono2 g = true) :
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  cases ho : g.op <;> simp [gateMono2, ho] at h ⊢
  · exact h
  · exact h

private theorem monotone2_of_all (C : Circuit) (h : C.gates.all gateMono2 = true) :
    PEqualNP.MetaComplexity.Monotone2 C := by
  intro g hg
  exact gateMono2_sound g ((List.all_eq_true.mp h) g hg)

private def witness : Circuit :=
  ⟨[⟨.or, [1, 12]⟩, ⟨.or, [0, 13]⟩, ⟨.or, [5, 11]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [3, 14]⟩,
    ⟨.or, [7, 8]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [6, 15]⟩, ⟨.or, [23, 16]⟩, ⟨.or, [24, 19]⟩,
    ⟨.or, [2, 10]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [27, 20]⟩, ⟨.or, [28, 21]⟩, ⟨.or, [19, 20]⟩,
    ⟨.or, [6, 17]⟩, ⟨.or, [31, 21]⟩, ⟨.or, [3, 15]⟩, ⟨.or, [4, 16]⟩, ⟨.and, [22, 25]⟩,
    ⟨.and, [26, 29]⟩, ⟨.and, [30, 32]⟩, ⟨.and, [33, 34]⟩, ⟨.and, [8, 7]⟩, ⟨.or, [35, 36]⟩,
    ⟨.or, [40, 37]⟩, ⟨.or, [41, 38]⟩, ⟨.or, [42, 39]⟩], 43⟩

end PEqualNP.Outside.L_meta_20331

theorem PEqualNP.Outside.L_meta_20331 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5146091177712921810 : ℕ).testBit (8 * u.val + v.val)) 29) := by
  refine ⟨PEqualNP.Outside.L_meta_20331.witness,
    PEqualNP.Outside.L_meta_20331.monotone2_of_all _ (by decide),
    by decide, ?_⟩
  decide +kernel
