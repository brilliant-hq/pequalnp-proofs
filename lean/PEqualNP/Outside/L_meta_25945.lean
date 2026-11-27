import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25945
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit := ⟨[
      ⟨.or, [1, 0]⟩,
      ⟨.and, [4, 8]⟩,
      ⟨.not, [9]⟩,
      ⟨.or, [4, 8]⟩,
      ⟨.and, [5, 2]⟩,
      ⟨.or, [11, 12]⟩,
      ⟨.and, [10, 13]⟩], 14⟩

def allowed (op : GateOp) : Bool :=
  match op with
  | .and | .or | .not => true
  | _ => false

theorem basis : FanInTwo circuit := by
  have h : circuit.gates.all (fun g => allowed g.op && decide (g.inputs.length ≤ 2)) = true := by decide
  intro g hg
  obtain ⟨kind, arity⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp h g hg)
  refine ⟨?_, of_decide_eq_true arity⟩
  cases op : g.op <;> rw [op] at kind <;> simp_all [allowed]


end PEqualNP.Outside.L_meta_25945

theorem PEqualNP.Outside.L_meta_25945 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([14, 14, 3, 1] : List ℕ).getD u.val 0).testBit v.val) C) := by
  refine ⟨PEqualNP.Outside.L_meta_25945.circuit, PEqualNP.Outside.L_meta_25945.basis, by decide, ?_⟩
  intro u v
  fin_cases u <;> fin_cases v <;> decide +kernel
