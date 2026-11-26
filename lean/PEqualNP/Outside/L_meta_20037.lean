import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_20037

def witness : Circuit :=
  ⟨[⟨.or, [0, 14]⟩,
   ⟨.or, [1, 9]⟩,
   ⟨.or, [2, 10]⟩,
   ⟨.or, [3, 11]⟩,
   ⟨.or, [4, 12]⟩,
   ⟨.or, [5, 13]⟩,
   ⟨.or, [6, 8]⟩,
   ⟨.or, [7, 15]⟩,
   ⟨.or, [18, 19]⟩,
   ⟨.or, [22, 24]⟩,
   ⟨.and, [16, 25]⟩,
   ⟨.or, [19, 21]⟩,
   ⟨.or, [23, 27]⟩,
   ⟨.and, [17, 28]⟩,
   ⟨.or, [23, 24]⟩,
   ⟨.and, [20, 30]⟩,
   ⟨.or, [22, 23]⟩,
   ⟨.and, [21, 32]⟩,
   ⟨.and, [2, 10]⟩,
   ⟨.and, [6, 8]⟩,
   ⟨.or, [26, 29]⟩,
   ⟨.or, [31, 33]⟩,
   ⟨.or, [34, 35]⟩,
   ⟨.or, [36, 37]⟩,
   ⟨.or, [38, 39]⟩], 40⟩

def positiveOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or => true
  | _ => false

theorem positiveOp_sound (g : Gate) (h : positiveOp g = true) :
    g.op = .and ∨ g.op = .or := by
  cases hg : g.op <;> simp [positiveOp, hg] at h ⊢

theorem monotone : Monotone2 witness := by
  have hc : witness.gates.all (fun g =>
      positiveOp g && decide (g.inputs.length ≤ 2)) = true := by decide +kernel
  intro g member
  have hg := List.all_eq_true.mp hc g member
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using positiveOp_sound g hg.1, hg.2⟩

end PEqualNP.Outside.L_meta_20037

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_20037 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3630327413337270285 : ℕ).testBit (8 * u.val + v.val)) 28) := by
  refine ⟨PEqualNP.Outside.L_meta_20037.witness, PEqualNP.Outside.L_meta_20037.monotone, by decide, ?_⟩
  decide +kernel
