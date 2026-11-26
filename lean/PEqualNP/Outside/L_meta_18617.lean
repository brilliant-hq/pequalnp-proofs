import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18617_aux
open PEqualNP.CircuitLowerBounds

private def edges : List (Fin 13 × Fin 13) := [(1, 0), (1, 5), (1, 11), (2, 2), (2, 6), (2, 12), (4, 3), (4, 4), (4, 8), (10, 7), (10, 9), (10, 10)]

private def circ : Circuit := ⟨[⟨.or, [13,18]⟩, ⟨.or, [27,24]⟩, ⟨.and, [1,28]⟩, ⟨.or, [15,19]⟩, ⟨.or, [30,25]⟩, ⟨.and, [2,31]⟩, ⟨.or, [16,17]⟩, ⟨.or, [33,21]⟩, ⟨.and, [4,34]⟩, ⟨.or, [20,22]⟩, ⟨.or, [36,23]⟩, ⟨.and, [10,37]⟩, ⟨.or, [29,32]⟩, ⟨.or, [39,35]⟩, ⟨.or, [40,38]⟩], 41⟩

private lemma incidence (p l : Fin 13) :
    (p ∈ ([1,2,4,10] : List (Fin 13)) ∧ l ≠ 1 ∧ (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9)) ↔ (p,l) ∈ edges := by
  revert p l
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem build : ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      C.size ≤ 15 ∧ 27 ≤ C.output ∧ C.output < 27 + C.size ∧
      PEqualNP.TopForm.IsAO2 27 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
      ∀ x : Fin 26 → Bool,
        C.eval (List.ofFn x ++ [x 1 || x 2]) = true ↔
          ∃ p l : Fin 13, p ∈ ([1, 2, 4, 10] : List (Fin 13)) ∧ l ≠ 1 ∧
            (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
            x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
  refine ⟨circ,by decide,by decide,by decide,by decide +kernel,by decide +kernel,?_⟩
  intro x
  have ev : circ.eval (List.ofFn x ++ [x 1 || x 2]) = edges.any
      (fun z => x (Fin.castAdd 13 z.1) && x (Fin.natAdd 13 z.2)) := by
    simp [circ,Circuit.eval,Circuit.wires,GateOp.eval,List.getD_eq_getElem?_getD, List.ofFn_succ,edges,
      Bool.and_or_distrib_left]
    simp only [Bool.and_comm, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc]
  rw [ev,List.any_eq_true]
  constructor
  · rintro ⟨⟨p,l⟩,hm,h⟩
    exact ⟨p,l,(incidence p l).mpr hm |>.1,(incidence p l).mpr hm |>.2.1,
      (incidence p l).mpr hm |>.2.2,(Bool.and_eq_true_iff.mp h).1,(Bool.and_eq_true_iff.mp h).2⟩
  · rintro ⟨p,l,hp,hl,he,ha,hb⟩
    exact ⟨(p,l),(incidence p l).mp ⟨hp,hl,he⟩,Bool.and_eq_true_iff.mpr ⟨ha,hb⟩⟩
end PEqualNP.Outside.L_meta_18617_aux

open PEqualNP.Outside.L_meta_18617_aux in
theorem PEqualNP.Outside.L_meta_18617 : (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (15 : ℕ) ∧ (27 : ℕ) ≤ x1.output ∧ x1.output < (27 : ℕ) + x1.size ∧ PEqualNP.TopForm.IsAO2 (27 : ℕ) x1 ∧ (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧ ∀ (x2 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x2 ++ [x2 (1 : Fin (26 : ℕ)) || x2 (2 : Fin (26 : ℕ))]) = Bool.true ↔ ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x3 ∈ [(1 : Fin (13 : ℕ)), (2 : Fin (13 : ℕ)), (4 : Fin (13 : ℕ)), (10 : Fin (13 : ℕ))] ∧ x4 ≠ (1 : Fin (13 : ℕ)) ∧ (x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ))) ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true) := build
