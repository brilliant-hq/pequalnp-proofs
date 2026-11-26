import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22680

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [8, 9]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [3, 10]⟩,
    ⟨.or, [6, 14]⟩,
    ⟨.or, [2, 14]⟩,
    ⟨.or, [5, 16]⟩,
    ⟨.or, [7, 17]⟩,
    ⟨.and, [11, 18]⟩,
    ⟨.and, [12, 15]⟩,
    ⟨.and, [2, 13]⟩,
    ⟨.or, [19, 20]⟩,
    ⟨.or, [22, 21]⟩], 23⟩

def isMonoOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or => true
  | _ => false

theorem isMonoOp_sound (g : Gate) (h : isMonoOp g = true) :
    g.op = .and ∨ g.op = .or := by
  cases hg : g.op <;> simp [isMonoOp, hg] at h ⊢

theorem witness_mono : Monotone2 witness := by
  have h : witness.gates.all (fun g => isMonoOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have hp := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using isMonoOp_sound g hp.1,
    hp.2⟩

theorem main_aux :
    RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843066 : ℕ).testBit (6 * u.val + v.val)) 14 :=
  ⟨witness, witness_mono, by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_22680

theorem PEqualNP.Outside.L_meta_22680 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843066 : ℕ).testBit (6 * u.val + v.val)) 14) :=
  PEqualNP.Outside.L_meta_22680.main_aux
