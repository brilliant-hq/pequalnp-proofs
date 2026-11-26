import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19784_aux

private def witness : Circuit :=
  ⟨[⟨.or, [8, 9]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [11, 14]⟩,
    ⟨.or, [13, 15]⟩,
    ⟨.or, [14, 16]⟩,
    ⟨.or, [15, 18]⟩,
    ⟨.or, [13, 17]⟩,
    ⟨.or, [22, 18]⟩,
    ⟨.and, [0, 23]⟩,
    ⟨.or, [19, 20]⟩,
    ⟨.and, [1, 25]⟩,
    ⟨.or, [8, 11]⟩,
    ⟨.or, [27, 12]⟩,
    ⟨.or, [28, 19]⟩,
    ⟨.and, [2, 29]⟩,
    ⟨.or, [16, 21]⟩,
    ⟨.and, [3, 31]⟩,
    ⟨.or, [11, 16]⟩,
    ⟨.or, [33, 17]⟩,
    ⟨.and, [4, 34]⟩,
    ⟨.or, [10, 13]⟩,
    ⟨.or, [36, 20]⟩,
    ⟨.and, [5, 37]⟩,
    ⟨.or, [17, 21]⟩,
    ⟨.and, [6, 39]⟩,
    ⟨.or, [9, 17]⟩,
    ⟨.or, [41, 19]⟩,
    ⟨.and, [7, 42]⟩,
    ⟨.or, [24, 26]⟩,
    ⟨.or, [44, 30]⟩,
    ⟨.or, [45, 32]⟩,
    ⟨.or, [46, 35]⟩,
    ⟨.or, [47, 38]⟩,
    ⟨.or, [48, 40]⟩,
    ⟨.or, [49, 43]⟩], 50⟩

private def allowed (g : Gate) : Bool :=
  match g.op with
  | .and | .or => true
  | _ => false

private theorem allowed_sound (g : Gate) (h : allowed g = true) :
    g.op = .and ∨ g.op = .or := by
  cases hg : g.op <;> simp [allowed, hg] at h ⊢

private theorem shaped : Monotone2 witness := by
  have h : witness.gates.all (fun g => allowed g && decide (g.inputs.length ≤ 2)) = true :=
    by decide +kernel
  intro g hg
  have legal := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at legal
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using allowed_sound g legal.1,
    legal.2⟩

end PEqualNP.Outside.L_meta_19784_aux

open PEqualNP.Outside.L_meta_19784_aux in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.L_meta_19784 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13176519996038833020 : ℕ).testBit (8 * u.val + v.val)) 35) := by
  exact ⟨witness, shaped, by decide, by decide +kernel⟩
