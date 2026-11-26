import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22666

def circuit : PEqualNP.CircuitLowerBounds.Circuit :=
  { gates := [
    { op := .or, inputs := [2, 8] },
    { op := .or, inputs := [5, 9] },
    { op := .or, inputs := [6, 11] },
    { op := .or, inputs := [0, 5] },
    { op := .or, inputs := [0, 6] },
    { op := .and, inputs := [12, 13] },
    { op := .or, inputs := [7, 14] },
    { op := .or, inputs := [1, 4] },
    { op := .or, inputs := [16, 17] },
    { op := .or, inputs := [15, 17] },
    { op := .and, inputs := [10, 18] },
    { op := .or, inputs := [3, 16] },
    { op := .and, inputs := [19, 21] },
    { op := .or, inputs := [20, 22] }],
    output := 23 }

lemma monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma represents : PEqualNP.Represents.Represents
    (fun (u : Fin 4) (v : Fin 6) => (841527 : ℕ).testBit (6 * u.val + v.val)) circuit := by
  decide +kernel

end PEqualNP.Outside.L_meta_22666

theorem PEqualNP.Outside.L_meta_22666 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841527 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  exact ⟨PEqualNP.Outside.L_meta_22666.circuit, PEqualNP.Outside.L_meta_22666.monotone, by decide, PEqualNP.Outside.L_meta_22666.represents⟩
