import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20159

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
  ⟨[⟨.or, [3, 6]⟩, ⟨.or, [16, 7]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [1, 5]⟩,
    ⟨.or, [20, 6]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [22, 7]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [10, 14]⟩,
    ⟨.or, [8, 9]⟩, ⟨.or, [26, 15]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [28, 15]⟩, ⟨.or, [8, 11]⟩,
    ⟨.or, [30, 25]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [34, 13]⟩,
    ⟨.and, [3, 25]⟩, ⟨.and, [17, 27]⟩, ⟨.and, [18, 29]⟩, ⟨.and, [19, 31]⟩, ⟨.and, [21, 32]⟩,
    ⟨.and, [23, 33]⟩, ⟨.and, [24, 35]⟩, ⟨.or, [36, 37]⟩, ⟨.or, [43, 38]⟩, ⟨.or, [44, 39]⟩,
    ⟨.or, [45, 40]⟩, ⟨.or, [46, 41]⟩, ⟨.or, [47, 42]⟩], 48⟩

end PEqualNP.Outside.L_meta_20159

theorem PEqualNP.Outside.L_meta_20159 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16399645806311595450 : ℕ).testBit (8 * u.val + v.val)) 33) := by
  refine ⟨PEqualNP.Outside.L_meta_20159.witness,
    PEqualNP.Outside.L_meta_20159.monotone2_of_all _ (by decide),
    by decide, ?_⟩
  decide +kernel
