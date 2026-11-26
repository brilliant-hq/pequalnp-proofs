import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20222

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def monotone2Bool (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with
     | .and => true
     | .or => true
     | _ => false) && decide (g.inputs.length ≤ 2)

theorem monotone2_of_bool (C : Circuit) (h : monotone2Bool C = true) : Monotone2 C := by
  intro g hg
  have hall := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hall
  refine ⟨?_, hall.2⟩
  cases hop : g.op <;> simp [hop] at hall ⊢

def witness : Circuit :=
  ⟨[
    ⟨.or, [0, 11]⟩,
    ⟨.or, [6, 13]⟩,
    ⟨.or, [7, 12]⟩,
    ⟨.or, [3, 18]⟩,
    ⟨.or, [1, 19]⟩,
    ⟨.or, [4, 16]⟩,
    ⟨.or, [17, 21]⟩,
    ⟨.or, [8, 15]⟩,
    ⟨.or, [18, 23]⟩,
    ⟨.and, [20, 24]⟩,
    ⟨.or, [14, 25]⟩,
    ⟨.or, [4, 26]⟩,
    ⟨.or, [14, 16]⟩,
    ⟨.or, [15, 20]⟩,
    ⟨.and, [28, 29]⟩,
    ⟨.or, [10, 30]⟩,
    ⟨.or, [2, 31]⟩,
    ⟨.or, [8, 32]⟩,
    ⟨.or, [3, 33]⟩,
    ⟨.or, [17, 32]⟩,
    ⟨.or, [15, 35]⟩,
    ⟨.or, [1, 36]⟩,
    ⟨.or, [12, 34]⟩,
    ⟨.and, [22, 34]⟩,
    ⟨.or, [9, 39]⟩,
    ⟨.or, [5, 40]⟩,
    ⟨.or, [22, 38]⟩,
    ⟨.and, [41, 42]⟩,
    ⟨.and, [27, 37]⟩,
    ⟨.or, [43, 44]⟩
  ], 45⟩

theorem hMono : Monotone2 witness :=
  monotone2_of_bool witness (by decide)

theorem hSize : witness.size ≤ 30 := by
  decide

theorem hRep : Represents (fun u v : Fin 8 => (17030148307327572375 : ℕ).testBit (8 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_20222

open PEqualNP.Outside.L_meta_20222 in
theorem PEqualNP.Outside.L_meta_20222 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17030148307327572375 : ℕ).testBit (8 * u.val + v.val)) 30) := by
  exact ⟨witness, hMono, hSize, hRep⟩
