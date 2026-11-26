import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18812

open PEqualNP.CircuitLowerBounds

def val (W : List Bool) (g : Gate) (acc : List Bool) : Bool :=
  match g.inputs with
  | [a, b] =>
    match g.op with
    | GateOp.and => ((W.getD a false && acc.getD b false) || (acc.getD a false && W.getD b false))
    | _ => (acc.getD a false || acc.getD b false)
  | _ => false

def F (W : List Bool) (acc : List Bool) (g : Gate) : List Bool := acc ++ [val W g acc]

theorem F_ext (W : List Bool) : ∀ (gs : List Gate) (w : List Bool), ∃ r, gs.foldl (F W) w = w ++ r := by
  intro gs
  induction gs with
  | nil => intro w; exact ⟨[], by simp⟩
  | cons g gs ih =>
    intro w
    obtain ⟨r, hr⟩ := ih (F W w g)
    exact ⟨val W g w :: r, by rw [List.foldl_cons, hr]; simp [F]⟩

theorem getD_pre (L A : List Bool) (i : ℕ) (h : i < L.length) : (L ++ A).getD i false = L.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem len_fold (W : List Bool) : ∀ (gs : List Gate) (w : List Bool), (gs.foldl (F W) w).length = w.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro w; simp
  | cons g gs ih => intro w; rw [List.foldl_cons, ih]; simp [F]; omega

theorem at_gate (W : List Bool) (gs : List Gate) (L : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
    let V := (gs.take j).foldl (F W) L
    V.length = L.length + j ∧
    (∀ i < L.length + j, (gs.foldl (F W) L).getD i false = V.getD i false) ∧
    (gs.foldl (F W) L).getD (L.length + j) false = val W g V := by
  intro V
  have hjl : j < gs.length := by
    rcases Nat.lt_or_ge j gs.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hj; cases hj
  have hd : gs.drop j = g :: gs.drop (j + 1) := by
    rw [List.drop_eq_getElem_cons hjl]
    rw [List.getElem?_eq_getElem hjl] at hj
    cases hj; rfl
  have hsplit : gs.foldl (F W) L = (gs.drop (j + 1)).foldl (F W) (F W V g) := by
    conv_lhs => rw [← List.take_append_drop j gs]
    rw [List.foldl_append, hd, List.foldl_cons]
  have hVl : V.length = L.length + j := by
    simp only [V]; rw [len_fold, List.length_take]; omega
  obtain ⟨r, hr⟩ := F_ext W (gs.drop (j + 1)) (F W V g)
  refine ⟨hVl, ?_, ?_⟩
  · intro i hi
    rw [hsplit, hr, getD_pre _ _ i (by simp [F]; omega)]
    simp only [F]
    exact getD_pre _ _ i (by omega)
  · rw [hsplit, hr, getD_pre _ _ _ (by simp [F]; omega)]
    simp only [F]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    simp [hVl]

end PEqualNP.Outside.L_meta_18812

open PEqualNP.Outside.L_meta_18812 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_18812 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : List Bool), PEqualNP.TopForm.IsAO2 x1 x2 → ∃ (x6 : ℕ → Bool), (∀ x7 < x1, x6 x7 = Decidable.decide (x7 = x3)) ∧ ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) (x9 x10 : ℕ), x2.gates[x7]? = Option.some x8 → x8.inputs = [x9, x10] → (x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → x6 (x1 + x7) = ((x2.wires x4).getD x9 Bool.false && x6 x10 || x6 x9 && (x2.wires x4).getD x10 Bool.false)) ∧ (x8.op = PEqualNP.CircuitLowerBounds.GateOp.or → x6 (x1 + x7) = (x6 x9 || x6 x10)) := by
  intro n C t x hC
  let W := C.wires x
  let L : List Bool := (List.range n).map fun i => decide (i = t)
  have hLl : L.length = n := by simp [L]
  let V := C.gates.foldl (F W) L
  refine ⟨fun w => V.getD w false, ?_, ?_⟩
  · intro i hi
    obtain ⟨r, hr⟩ := F_ext W C.gates L
    show V.getD i false = _
    simp only [V]
    rw [hr, getD_pre _ _ i (by omega)]
    simp [L, List.getD_eq_getElem?_getD, hi]
  · intro j g a b hg hin
    obtain ⟨hVl, hpre, hval⟩ := at_gate W C.gates L j g hg
    have hjl : j < C.gates.length := by
      rcases Nat.lt_or_ge j C.gates.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hg; cases hg
    have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C j = g := by
      simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hg, Option.getD_some]
    have ha : a < n + j := hC.2.1 j hjl a (by rw [hga, hin]; simp)
    have hb : b < n + j := hC.2.1 j hjl b (by rw [hga, hin]; simp)
    have e : V.getD (n + j) false = val W g ((C.gates.take j).foldl (F W) L) := by
      rw [← hLl]; exact hval
    have ea := hpre a (by omega)
    have eb := hpre b (by omega)
    refine ⟨fun hop => ?_, fun hop => ?_⟩
    · show V.getD (n + j) false = _
      rw [e]
      simp only [val, hin, hop]
      change _ = ((W.getD a false && V.getD b false) || (V.getD a false && W.getD b false))
      rw [ea, eb]
    · show V.getD (n + j) false = _
      rw [e]
      simp only [val, hin, hop]
      change _ = (V.getD a false || V.getD b false)
      rw [ea, eb]
