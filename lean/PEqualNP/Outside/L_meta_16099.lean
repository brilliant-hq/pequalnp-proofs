import Mathlib.Tactic.IntervalCases
import PEqualNP.Defs

-- Partial handoff for L-meta-16099. The separate NOT requirement is open.
namespace PEqualNP.Outside.L_meta_16099

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 5 → Bool) : Bool :=
  tableFun 5 (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1] : List ℕ).map (fun b => b == 1)) x

def witness : Circuit :=
  ⟨[⟨.and, [0, 3]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [1, 2]⟩,
    ⟨.and, [7, 4]⟩, ⟨.or, [5, 8]⟩, ⟨.and, [3, 4]⟩,
    ⟨.or, [6, 10]⟩, ⟨.and, [9, 11]⟩], 12⟩

theorem fanIn : FanInTwo witness := by
  simp [FanInTwo, witness]

theorem readsBack : NestedCover.ReadsBack 5 witness := by
  intro j hj
  have bounded : j < 8 := by simpa [witness] using hj
  interval_cases j <;> simp [NestedCover.gateAt, witness]

theorem witnessSize : witness.size = 8 := rfl

theorem witnessCorrect : ∀ x : Fin 5 → Bool, witness.eval (List.ofFn x) = target x := by
  decide +kernel

theorem noDeadGates :
    ∀ j < witness.size, witness.output = 5 + j ∨
      ∃ i < witness.size, j < i ∧
        5 + j ∈ (witness.gates.getD i ⟨.and, []⟩).inputs := by
  intro j h
  rw [witnessSize] at h
  interval_cases j
  · exact Or.inr ⟨4, by decide, by decide, by simp [witness]⟩
  · exact Or.inr ⟨6, by decide, by decide, by simp [witness]⟩
  · exact Or.inr ⟨3, by decide, by decide, by simp [witness]⟩
  · exact Or.inr ⟨4, by decide, by decide, by simp [witness]⟩
  · exact Or.inr ⟨7, by decide, by decide, by simp [witness]⟩
  · exact Or.inr ⟨6, by decide, by decide, by simp [witness]⟩
  · exact Or.inr ⟨7, by decide, by decide, by simp [witness]⟩
  · exact Or.inl rfl

theorem noNotReadsNot :
    ∀ g ∈ witness.gates, g.op = .not → 5 ≤ g.inputs.headD 0 →
      (witness.gates.getD (g.inputs.headD 0 - 5) ⟨.and, []⟩).op ≠ .not := by
  intro g member notGate _
  simp [witness] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases notGate

-- An internal NOT takes ten gates in this construction.
def witnessWithNot : Circuit :=
  ⟨[⟨.and, [0, 3]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [1, 2]⟩,
    ⟨.and, [7, 4]⟩, ⟨.not, [5]⟩, ⟨.and, [8, 9]⟩,
    ⟨.or, [5, 10]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [6, 12]⟩,
    ⟨.and, [11, 13]⟩], 14⟩

theorem withNotFanIn : FanInTwo witnessWithNot := by
  simp [FanInTwo, witnessWithNot]

theorem withNotReadsBack : NestedCover.ReadsBack 5 witnessWithNot := by
  intro j hj
  have bounded : j < 10 := by simpa [witnessWithNot] using hj
  interval_cases j <;> simp [NestedCover.gateAt, witnessWithNot]

theorem withNotSize : witnessWithNot.size = 10 := rfl

theorem withNotCorrect :
    ∀ x : Fin 5 → Bool, witnessWithNot.eval (List.ofFn x) = target x := by
  decide +kernel

theorem withNotNoDead :
    ∀ j < witnessWithNot.size, witnessWithNot.output = 5 + j ∨
      ∃ i < witnessWithNot.size, j < i ∧
        5 + j ∈ (witnessWithNot.gates.getD i ⟨.and, []⟩).inputs := by
  intro j h
  rw [withNotSize] at h
  interval_cases j
  · exact Or.inr ⟨4, by decide, by decide, by simp [witnessWithNot]⟩
  · exact Or.inr ⟨8, by decide, by decide, by simp [witnessWithNot]⟩
  · exact Or.inr ⟨3, by decide, by decide, by simp [witnessWithNot]⟩
  · exact Or.inr ⟨5, by decide, by decide, by simp [witnessWithNot]⟩
  · exact Or.inr ⟨5, by decide, by decide, by simp [witnessWithNot]⟩
  · exact Or.inr ⟨6, by decide, by decide, by simp [witnessWithNot]⟩
  · exact Or.inr ⟨9, by decide, by decide, by simp [witnessWithNot]⟩
  · exact Or.inr ⟨8, by decide, by decide, by simp [witnessWithNot]⟩
  · exact Or.inr ⟨9, by decide, by decide, by simp [witnessWithNot]⟩
  · exact Or.inl rfl

theorem withNotNoNotReadsNot :
    ∀ g ∈ witnessWithNot.gates, g.op = .not → 5 ≤ g.inputs.headD 0 →
      (witnessWithNot.gates.getD (g.inputs.headD 0 - 5) ⟨.and, []⟩).op ≠ .not := by
  intro g member notGate _
  simp [witnessWithNot] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [witnessWithNot]

theorem hasInternalNot :
    ∃ g ∈ witnessWithNot.gates, g.op = .not ∧ 5 ≤ g.inputs.headD 0 :=
  ⟨⟨.not, [5]⟩, by simp [witnessWithNot], rfl, by decide⟩

end PEqualNP.Outside.L_meta_16099
