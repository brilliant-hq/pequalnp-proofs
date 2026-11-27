import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32049_aux


open PEqualNP.CircuitLowerBounds

def step (wires : List Bool) (gate : Gate) : List Bool :=
  wires ++ [gate.op.eval (gate.inputs.map fun j => wires.getD j false)]

theorem head_preserved (gates : List Gate) (bit : Bool) (rest : List Bool) :
    (gates.foldl step (bit :: rest)).getD 0 false = bit := by
  induction gates generalizing rest with
  | nil => rfl
  | cons gate gates ih =>
    exact ih (rest ++ [gate.op.eval (gate.inputs.map fun j => (bit :: rest).getD j false)])

theorem same_tail (fixed : List Bool) (W : Nat) (hWt : ∀ (bit : Bool) (extra : List Bool), (bit :: (fixed ++ extra)).getD W false = true) (gates : List Gate)
    (hread : ∀ gate ∈ gates, 0 ∉ gate.inputs ∨ (gate.op = GateOp.or ∧ W ∈ gate.inputs)) (extra : List Bool) :
    ∃ result, gates.foldl step (false :: (fixed ++ extra)) = false :: result ∧
      gates.foldl step (true :: (fixed ++ extra)) = true :: result := by
  induction gates generalizing extra with
  | nil => exact ⟨fixed ++ extra, rfl, rfl⟩
  | cons gate gates ih =>
    have hval : gate.op.eval (gate.inputs.map fun j => (false :: (fixed ++ extra)).getD j false) =
        gate.op.eval (gate.inputs.map fun j => (true :: (fixed ++ extra)).getD j false) := by
      rcases hread gate (by simp) with h0 | ⟨hop, hw⟩
      · congr 1
        apply List.map_congr_left
        intro j hj
        cases j with
        | zero => exact (h0 hj).elim
        | succ j => rfl
      · rw [hop]
        have h1 : ∀ bit : Bool, GateOp.or.eval (gate.inputs.map fun j => (bit :: (fixed ++ extra)).getD j false) = true :=
          fun bit => List.any_eq_true.mpr ⟨true, List.mem_map.mpr ⟨W, hw, hWt bit _⟩, rfl⟩
        rw [h1 false, h1 true]
    obtain ⟨result, hlo, hhi⟩ := ih (fun g hg => hread g (by simp [hg]))
      (extra ++ [gate.op.eval (gate.inputs.map fun j => (false :: (fixed ++ extra)).getD j false)])
    refine ⟨result, ?_, ?_⟩
    · rw [List.foldl_cons]
      have hstep : step (false :: (fixed ++ extra)) gate = false :: (fixed ++ (extra ++
          [gate.op.eval (gate.inputs.map fun j => (false :: (fixed ++ extra)).getD j false)])) := by
        simp only [step, List.cons_append, List.append_assoc]
      rw [hstep]
      exact hlo
    · rw [List.foldl_cons]
      have hstep : step (true :: (fixed ++ extra)) gate = true :: (fixed ++ (extra ++
          [gate.op.eval (gate.inputs.map fun j => (false :: (fixed ++ extra)).getD j false)])) := by
        simp only [step, List.cons_append, List.append_assoc, hval]
      rw [hstep]
      exact hhi


theorem key (fixed : List Bool) (W : Nat) (hWt : ∀ (bit : Bool) (extra : List Bool), (bit :: (fixed ++ extra)).getD W false = true) (gates : List Gate) (out : Nat)
    (hread : ∀ gate ∈ gates, 0 ∉ gate.inputs ∨ (gate.op = GateOp.or ∧ W ∈ gate.inputs))
    (hz : (gates.foldl step [true, false, false, false, false, false, false]).getD out false = false)
    (hlo : (gates.foldl step (false :: (fixed ++ []))).getD out false = false)
    (hhi : (gates.foldl step (true :: (fixed ++ []))).getD out false = true) : False := by
  cases out with
  | zero =>
    rw [head_preserved] at hz
    contradiction
  | succ out =>
    obtain ⟨result, hfalse, htrue⟩ := same_tail fixed W hWt gates hread []
    rw [hfalse] at hlo
    rw [htrue] at hhi
    change result.getD out false = false at hlo
    change result.getD out false = true at hhi
    rw [hlo] at hhi
    contradiction

theorem prefix_pres (gates : List Gate) (w : List Bool) (j : Nat) (hj : j < w.length) :
    (gates.foldl step w).getD j false = w.getD j false := by
  induction gates generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    · unfold step
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
    · simp [step]; omega

end PEqualNP.Outside.L_meta_32049_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_32049_aux in
theorem PEqualNP.Outside.L_meta_32049 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length) (h : ℕ),
  PEqualNP.MetaComplexity.FanInTwo C → C.size = 10 →
  (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
    (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) →
  0 ∈ (C.gates.get i).inputs → (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) →
  (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or →
  (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and → i.val < k.val →
  7 + i.val ∈ (C.gates.get k).inputs → h ∈ (C.gates.get i).inputs → h ≠ 0 → h < 7 + i.val →
  (∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧
    (C.wires (List.ofFn x)).getD h false = true) →
  7 ≤ h := by
  rintro ⟨gates, out⟩ i k h _ _ correct _ hUnique hOp _ _ _ hReadW hne hlt ⟨x, _, hx1, hx6, hxh⟩
  by_contra hcon
  have h7 : h < 7 := by omega
  have hread : ∀ W : Nat, W ∈ (gates.get i).inputs → ∀ gate ∈ gates, 0 ∉ gate.inputs ∨ (gate.op = GateOp.or ∧ W ∈ gate.inputs) := by
    intro W hW g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    by_cases h0 : 0 ∈ gates[j].inputs
    · have e : (⟨j, hj⟩ : Fin gates.length) = i := hUnique ⟨j, hj⟩ h0
      subst e
      exact Or.inr ⟨hOp, hW⟩
    · exact Or.inl h0
  change (gates.foldl step (List.ofFn x)).getD h false = true at hxh
  interval_cases h
  · omega
  · rw [prefix_pres gates _ 1 (by simp)] at hxh
    simp [hx1] at hxh
  · have hz := correct (fun j => decide (j = 0))
    have hlo := correct (fun j : Fin 7 => (false :: [false, true, false, false, false, true]).getD j.val false)
    have hhi := correct (fun j : Fin 7 => (true :: [false, true, false, false, false, true]).getD j.val false)
    change (gates.foldl step [true, false, false, false, false, false, false]).getD out false = false at hz
    change (gates.foldl step (false :: ([false, true, false, false, false, true] ++ []))).getD out false = false at hlo
    change (gates.foldl step (true :: ([false, true, false, false, false, true] ++ []))).getD out false = true at hhi
    exact key [false, true, false, false, false, true] 2 (fun _ _ => rfl) gates out (hread 2 hReadW) hz hlo hhi
  · have hz := correct (fun j => decide (j = 0))
    have hlo := correct (fun j : Fin 7 => (false :: [true, false, true, false, false, false]).getD j.val false)
    have hhi := correct (fun j : Fin 7 => (true :: [true, false, true, false, false, false]).getD j.val false)
    change (gates.foldl step [true, false, false, false, false, false, false]).getD out false = false at hz
    change (gates.foldl step (false :: ([true, false, true, false, false, false] ++ []))).getD out false = false at hlo
    change (gates.foldl step (true :: ([true, false, true, false, false, false] ++ []))).getD out false = true at hhi
    exact key [true, false, true, false, false, false] 3 (fun _ _ => rfl) gates out (hread 3 hReadW) hz hlo hhi
  · have hz := correct (fun j => decide (j = 0))
    have hlo := correct (fun j : Fin 7 => (false :: [true, false, false, true, false, false]).getD j.val false)
    have hhi := correct (fun j : Fin 7 => (true :: [true, false, false, true, false, false]).getD j.val false)
    change (gates.foldl step [true, false, false, false, false, false, false]).getD out false = false at hz
    change (gates.foldl step (false :: ([true, false, false, true, false, false] ++ []))).getD out false = false at hlo
    change (gates.foldl step (true :: ([true, false, false, true, false, false] ++ []))).getD out false = true at hhi
    exact key [true, false, false, true, false, false] 4 (fun _ _ => rfl) gates out (hread 4 hReadW) hz hlo hhi
  · have hz := correct (fun j => decide (j = 0))
    have hlo := correct (fun j : Fin 7 => (false :: [true, false, false, false, true, false]).getD j.val false)
    have hhi := correct (fun j : Fin 7 => (true :: [true, false, false, false, true, false]).getD j.val false)
    change (gates.foldl step [true, false, false, false, false, false, false]).getD out false = false at hz
    change (gates.foldl step (false :: ([true, false, false, false, true, false] ++ []))).getD out false = false at hlo
    change (gates.foldl step (true :: ([true, false, false, false, true, false] ++ []))).getD out false = true at hhi
    exact key [true, false, false, false, true, false] 5 (fun _ _ => rfl) gates out (hread 5 hReadW) hz hlo hhi
  · rw [prefix_pres gates _ 6 (by simp)] at hxh
    simp [hx6] at hxh
