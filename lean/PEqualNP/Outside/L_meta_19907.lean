import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19907

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- The graph: bit (8 u + v) of the mask is the entry at (u, v).

def mask : ℕ := 3937228359801398220

def graph (u v : Fin 8) : Bool := mask.testBit (8 * u.val + v.val)

-- The circuit of 32 gates given on the desk. Wire u is the left input u (u below 8), wire 8 + v
-- the right input v, and gate k writes wire 16 + k.

def gates : List Gate := [
  ⟨.or, [8, 13]⟩, ⟨.or, [11, 15]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [9, 16]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [17, 20]⟩,
  ⟨.and, [0, 21]⟩, ⟨.or, [14, 19]⟩, ⟨.and, [1, 23]⟩, ⟨.or, [17, 18]⟩, ⟨.and, [2, 25]⟩, ⟨.or, [11, 12]⟩,
  ⟨.or, [27, 16]⟩, ⟨.and, [3, 28]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [30, 20]⟩, ⟨.and, [4, 31]⟩, ⟨.or, [12, 14]⟩,
  ⟨.or, [33, 17]⟩, ⟨.and, [5, 34]⟩, ⟨.or, [15, 19]⟩, ⟨.and, [6, 36]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [38, 18]⟩,
  ⟨.and, [7, 39]⟩, ⟨.or, [22, 24]⟩, ⟨.or, [41, 26]⟩, ⟨.or, [42, 29]⟩, ⟨.or, [43, 32]⟩, ⟨.or, [44, 35]⟩,
  ⟨.or, [45, 37]⟩, ⟨.or, [46, 40]⟩]

def circ : Circuit := ⟨gates, 47⟩

theorem gateBasis : ∀ g ∈ gates,
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [gates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl <;> simp

theorem monotone2 : Monotone2 circ := gateBasis

theorem sizeOk : circ.size ≤ 32 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem represents : Represents graph circ := by
  intro u v
  fin_cases u <;> fin_cases v <;> decide +kernel

end PEqualNP.Outside.L_meta_19907

open PEqualNP.Outside.L_meta_19907

theorem PEqualNP.Outside.L_meta_19907 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3937228359801398220 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨circ, monotone2, sizeOk, represents⟩
