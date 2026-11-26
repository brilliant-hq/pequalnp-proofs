import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18917_aux

open PEqualNP.CircuitLowerBounds

theorem len (h : List Bool → Gate → Bool) (gs : List Gate) : ∀ a : List Bool,
    (gs.foldl (fun acc g => acc ++ [h acc g]) a).length = a.length + gs.length := by
  induction gs with
  | nil => intro a; simp
  | cons g gs ih => intro a; simp only [List.foldl_cons]; rw [ih]; simp; omega

theorem pre (h : List Bool → Gate → Bool) (gs : List Gate) : ∀ a : List Bool, ∀ i < a.length,
    (gs.foldl (fun acc g => acc ++ [h acc g]) a).getD i false = a.getD i false := by
  induction gs with
  | nil => intro a i hi; simp
  | cons g gs ih =>
    intro a i hi
    simp only [List.foldl_cons]
    rw [ih _ i (by simp; omega), List.getD_append _ _ _ _ hi]

theorem at_ (h : List Bool → Gate → Bool) (gs : List Gate) (a : List Bool) (m : ℕ)
    (hm : m < gs.length) : ∃ P : List Bool, P.length = a.length + m ∧
      (∀ i < P.length, (gs.foldl (fun acc g => acc ++ [h acc g]) a).getD i false = P.getD i false) ∧
      (gs.foldl (fun acc g => acc ++ [h acc g]) a).getD (a.length + m) false = h P gs[m] := by
  refine ⟨(gs.take m).foldl (fun acc g => acc ++ [h acc g]) a, ?_, ?_, ?_⟩
  · rw [len]; simp; omega
  · intro i hi
    conv_lhs => rw [← List.take_append_drop m gs, List.foldl_append]
    exact pre h _ _ i hi
  · conv_lhs => rw [← List.take_append_drop m gs, List.foldl_append, List.drop_eq_getElem_cons hm, List.foldl_cons]
    have hl : ((gs.take m).foldl (fun acc g => acc ++ [h acc g]) a).length = a.length + m := by
      rw [len]; simp; omega
    rw [pre h _ _ _ (by simp [hl])]
    rw [← hl, List.getD_append_right _ _ _ _ (le_refl _)]
    simp

end PEqualNP.Outside.L_meta_18917_aux

open PEqualNP.Outside.L_meta_18917_aux in
theorem PEqualNP.Outside.L_meta_18917 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 x5 x6 : ℕ) (x7 : Fin x1 → Bool),   PEqualNP.TopForm.IsAO2 x1 x2 →     x2.output = x1 + x3 →       x3 + (1 : ℕ) = x2.size →         x2.gates[x3]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x4, x5] : PEqualNP.CircuitLowerBounds.Gate } →           have x12 : ℕ → Bool := fun (x12 : ℕ) => (x2.wires (List.ofFn x7)).getD x12 Bool.false;           x12 x4 = Bool.false → x12 x5 = Bool.false → ∃ (x15 : ℕ → Bool), (∀ x16 < x1, x15 x16 = Decidable.decide (x16 = x6)) ∧ (∀ (x16 : ℕ) (x17 : PEqualNP.CircuitLowerBounds.Gate) (x18 x19 : ℕ), x2.gates[x16]? = Option.some x17 → x17.inputs = [x18, x19] → (x17.op = PEqualNP.CircuitLowerBounds.GateOp.and → x15 (x1 + x16) = (x12 x18 && x15 x19 || x15 x18 && x12 x19)) ∧ (x17.op = PEqualNP.CircuitLowerBounds.GateOp.or → x15 (x1 + x16) = (x15 x18 || x15 x19))) ∧ x15 x2.output = Bool.false := by
  intro n C k a b j x hC hout hsize hgk
  dsimp only
  intro ha hb
  let w : ℕ → Bool := fun i => (C.wires (List.ofFn x)).getD i false
  let h : List Bool → PEqualNP.CircuitLowerBounds.Gate → Bool := fun acc g =>
    match g.op with
    | PEqualNP.CircuitLowerBounds.GateOp.and =>
      (w (g.inputs.getD 0 0) && acc.getD (g.inputs.getD 1 0) false ||
        acc.getD (g.inputs.getD 0 0) false && w (g.inputs.getD 1 0))
    | _ => (acc.getD (g.inputs.getD 0 0) false || acc.getD (g.inputs.getD 1 0) false)
  let I : List Bool := List.ofFn (fun i : Fin n => decide (i.val = j))
  let D := C.gates.foldl (fun acc g => acc ++ [h acc g]) I
  have hI : I.length = n := by simp [I]
  refine ⟨fun i => D.getD i false, ?_, ?_, ?_⟩
  · intro i hi
    show D.getD i false = _
    rw [pre h _ _ i (by rw [hI]; exact hi)]
    simp [I, List.getD_eq_getElem?_getD, hi]
  · intro m g p q hg hin
    have hm : m < C.gates.length := by
      rcases Nat.lt_or_ge m C.gates.length with h1 | h1
      · exact h1
      · rw [List.getElem?_eq_none h1] at hg; simp at hg
    have hgm : C.gates[m] = g := by rw [List.getElem?_eq_getElem hm] at hg; simpa using hg
    obtain ⟨P, hPl, hPe, hPv⟩ := at_ h C.gates I m hm
    rw [hI] at hPl hPv
    have hrb := hC.2.1 m hm
    have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C m = g := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hg]
    rw [hga, hin] at hrb
    have hp : p < n + m := hrb p (by simp)
    have hq : q < n + m := hrb q (by simp)
    have ep : D.getD p false = P.getD p false := hPe p (by omega)
    have eq_ : D.getD q false = P.getD q false := hPe q (by omega)
    show (_ → D.getD (n + m) false = _) ∧ (_ → D.getD (n + m) false = _)
    rw [hPv, hgm]
    beta_reduce
    rw [ep, eq_]
    constructor
    · intro hop; simp [h, w, hop, hin]
    · intro hop; simp [h, w, hop, hin]
  · show D.getD C.output false = false
    have hk : k < C.gates.length := by
      have : C.size = C.gates.length := rfl
      omega
    obtain ⟨P, hPl, hPe, hPv⟩ := at_ h C.gates I k hk
    rw [hI] at hPv
    have hgk' : C.gates[k] = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [a, b] } := by rw [List.getElem?_eq_getElem hk] at hgk; exact Option.some.inj hgk
    rw [hout, hPv, hgk']
    simp only [h, w, List.getD_cons_zero, List.getD_cons_succ]
    rw [ha, hb]
    simp
