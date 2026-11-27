import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29884_aux

open PEqualNP.CircuitLowerBounds

theorem fold_head (gs : List Gate) : ∀ (h : Bool) (t : List Bool), ∃ t' : List Bool,
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (h :: t)
      = h :: t' := by
  induction gs with
  | nil => intro h t; exact ⟨t, rfl⟩
  | cons g gs ih =>
    intro h t
    obtain ⟨t', ht'⟩ := ih h (t ++ [g.op.eval (g.inputs.map fun i => (h :: t).getD i false)])
    exact ⟨t', ht'⟩

theorem fold_tail (gs : List Gate)
    (hP : ∀ g ∈ gs, 0 ∈ g.inputs → g.op = GateOp.or ∧ 3 ∈ g.inputs) :
    ∀ (h1 h2 : Bool) (t : List Bool), t.getD 2 false = true → ∃ t' : List Bool,
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (h1 :: t)
        = h1 :: t' ∧
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (h2 :: t)
        = h2 :: t' := by
  induction gs with
  | nil => intro h1 h2 t _; exact ⟨t, rfl, rfl⟩
  | cons g gs ih =>
    intro h1 h2 t ht
    have hPg := hP g (List.mem_cons_self)
    have hv : g.op.eval (g.inputs.map fun i => (h1 :: t).getD i false)
        = g.op.eval (g.inputs.map fun i => (h2 :: t).getD i false) := by
      by_cases h0 : 0 ∈ g.inputs
      · obtain ⟨hop, h3⟩ := hPg h0
        rw [hop]
        have e1 : (g.inputs.map fun i => (h1 :: t).getD i false).any id = true := by
          rw [List.any_eq_true]
          exact ⟨true, List.mem_map.2 ⟨3, h3, ht⟩, rfl⟩
        have e2 : (g.inputs.map fun i => (h2 :: t).getD i false).any id = true := by
          rw [List.any_eq_true]
          exact ⟨true, List.mem_map.2 ⟨3, h3, ht⟩, rfl⟩
        show (g.inputs.map fun i => (h1 :: t).getD i false).any id
          = (g.inputs.map fun i => (h2 :: t).getD i false).any id
        rw [e1, e2]
      · have hm : (g.inputs.map fun i => (h1 :: t).getD i false)
            = (g.inputs.map fun i => (h2 :: t).getD i false) := by
          apply List.map_congr_left
          intro i hi
          cases i with
          | zero => exact absurd hi h0
          | succ n => rfl
        rw [hm]
    have ht2 : (t ++ [g.op.eval (g.inputs.map fun i => (h1 :: t).getD i false)]).getD 2 false
        = true := by
      have hlen : 2 < t.length := by
        by_contra hc
        rw [List.getD_eq_default _ _ (by omega)] at ht
        exact Bool.false_ne_true ht
      rw [List.getD_append _ _ _ _ hlen]
      exact ht
    obtain ⟨t', a1, a2⟩ := ih (fun g' hg' => hP g' (List.mem_cons_of_mem _ hg')) h1 h2
      (t ++ [g.op.eval (g.inputs.map fun i => (h1 :: t).getD i false)]) ht2
    refine ⟨t', a1, ?_⟩
    have a2' : gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (h2 :: (t ++ [g.op.eval (g.inputs.map fun i => (h2 :: t).getD i false)])) = h2 :: t' := by
      rw [← hv]; exact a2
    exact a2'

end PEqualNP.Outside.L_meta_29884_aux

theorem PEqualNP.Outside.L_meta_29884 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 7 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 3 ∈ (C.gates.get i).inputs ∧ 3 ≠ 0 ∧ 3 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 3 false = true)) := by
  rintro ⟨C, i, k, _, _, _, hf, _, honly, hor, _, _, _, h3i, _⟩
  have hP : ∀ g ∈ C.gates, 0 ∈ g.inputs →
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 3 ∈ g.inputs := by
    intro g hg h0
    obtain ⟨j, rfl⟩ := List.mem_iff_get.1 hg
    have hj := honly j h0
    rw [hj]
    exact ⟨hor, h3i⟩
  by_cases ho : C.output = 0
  ·
    obtain ⟨t', ht'⟩ := PEqualNP.Outside.L_meta_29884_aux.fold_head C.gates true
      [false, false, false, false, false, false]
    have hc := hf (fun j => decide (j = 0))
    have hl : List.ofFn (fun j : Fin 7 => decide (j = 0))
        = [true, false, false, false, false, false, false] := by decide
    have hw : C.wires [true, false, false, false, false, false, false] = true :: t' := ht'
    have he : C.eval [true, false, false, false, false, false, false] = true := by
      show (C.wires [true, false, false, false, false, false, false]).getD C.output false = true
      rw [hw, ho]
      rfl
    rw [hl, he] at hc
    revert hc
    decide
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero ho
    obtain ⟨t', a1, a2⟩ := PEqualNP.Outside.L_meta_29884_aux.fold_tail C.gates hP false true
      [true, false, true, false, false, false] rfl
    have hca := hf (fun j => decide (j = 1 ∨ j = 3))
    have hcb := hf (fun j => decide (j = 0 ∨ j = 1 ∨ j = 3))
    have hla : List.ofFn (fun j : Fin 7 => decide (j = 1 ∨ j = 3))
        = [false, true, false, true, false, false, false] := by decide
    have hlb : List.ofFn (fun j : Fin 7 => decide (j = 0 ∨ j = 1 ∨ j = 3))
        = [true, true, false, true, false, false, false] := by decide
    have hwa : C.wires [false, true, false, true, false, false, false] = false :: t' := a1
    have hwb : C.wires [true, true, false, true, false, false, false] = true :: t' := a2
    have hea : C.eval [false, true, false, true, false, false, false] = t'.getD n false := by
      show (C.wires [false, true, false, true, false, false, false]).getD C.output false = _
      rw [hwa, hn]
      rfl
    have heb : C.eval [true, true, false, true, false, false, false] = t'.getD n false := by
      show (C.wires [true, true, false, true, false, false, false]).getD C.output false = _
      rw [hwb, hn]
      rfl
    rw [hla, hea] at hca
    rw [hlb, heb, hca] at hcb
    revert hcb
    decide
