import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18812_aux

open PEqualNP.CircuitLowerBounds

def val (W : List Bool) (L : List Bool) (g : Gate) : Bool :=
  match g.op, g.inputs with
  | GateOp.and, [a, b] => (W.getD a false && L.getD b false || L.getD a false && W.getD b false)
  | GateOp.or, [a, b] => (L.getD a false || L.getD b false)
  | _, _ => false

def F (W : List Bool) (gs : List Gate) (L : List Bool) : List Bool :=
  gs.foldl (fun L g => L ++ [val W L g]) L

theorem F_len (W : List Bool) : ∀ (gs : List Gate) (L : List Bool), (F W gs L).length = L.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro L; simp [F]
  | cons g t ih =>
    intro L
    have := ih (L ++ [val W L g])
    simp only [F, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem F_pre (W : List Bool) : ∀ (gs : List Gate) (L : List Bool) (i : ℕ), i < L.length → (F W gs L).getD i false = L.getD i false := by
  intro gs
  induction gs with
  | nil => intro L i h; rfl
  | cons g t ih =>
    intro L i h
    have := ih (L ++ [val W L g]) i (by simp; omega)
    simp only [F, List.foldl_cons] at this ⊢
    rw [this, List.getD_append _ _ _ _ h]

theorem F_split (W : List Bool) (gs : List Gate) (L : List Bool) (k : ℕ) (g : Gate) (hk : gs[k]? = some g) :
    F W gs L = F W (gs.drop (k+1)) (F W (gs.take k) L ++ [val W (F W (gs.take k) L) g]) := by
  have hl : k < gs.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hk; cases hk
  have e : gs = gs.take k ++ g :: gs.drop (k+1) := by
    have h1 := List.take_append_drop k gs
    have h2 : gs.drop k = g :: gs.drop (k+1) := by
      rw [List.drop_eq_getElem_cons hl]
      rw [List.getElem?_eq_getElem hl] at hk
      cases hk; rfl
    rw [h2] at h1; exact h1.symm
  conv_lhs => rw [e]
  simp [F, List.foldl_append]

end PEqualNP.Outside.L_meta_18812_aux

open PEqualNP.Outside.L_meta_18812_aux in
theorem PEqualNP.Outside.L_meta_18812 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : List Bool), PEqualNP.TopForm.IsAO2 x1 x2 → ∃ (x6 : ℕ → Bool), (∀ x7 < x1, x6 x7 = Decidable.decide (x7 = x3)) ∧ ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) (x9 x10 : ℕ), x2.gates[x7]? = Option.some x8 → x8.inputs = [x9, x10] → (x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → x6 (x1 + x7) = ((x2.wires x4).getD x9 Bool.false && x6 x10 || x6 x9 && (x2.wires x4).getD x10 Bool.false)) ∧ (x8.op = PEqualNP.CircuitLowerBounds.GateOp.or → x6 (x1 + x7) = (x6 x9 || x6 x10)) := by
  intro n C v x hC
  obtain ⟨_, hR, _⟩ := hC
  let W := C.wires x
  let L0 : List Bool := List.ofFn (fun i : Fin n => decide (i.val = v))
  refine ⟨fun i => (F W C.gates L0).getD i false, ?_, ?_⟩
  · intro i hi
    show (F W C.gates L0).getD i false = _
    rw [F_pre W C.gates L0 i (by simp [L0]; exact hi)]
    simp [L0, List.getD_eq_getElem?_getD, hi]
  · intro k g a b hk hin
    have hl : k < C.gates.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hk; cases hk
    have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C k = g := by simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hk]
    have ha : a < n + k := hR k hl a (by rw [hga, hin]; simp)
    have hb : b < n + k := hR k hl b (by rw [hga, hin]; simp)
    have hs := F_split W C.gates L0 k g hk
    have hP : (F W (C.gates.take k) L0).length = n + k := by
      rw [F_len]; simp [L0]; omega
    have key : ∀ i < n + k, (F W C.gates L0).getD i false = (F W (C.gates.take k) L0).getD i false := by
      intro i hi
      rw [hs, F_pre W _ _ i (by simp; omega), List.getD_append _ _ _ _ (by omega)]
    have kv : (F W C.gates L0).getD (n + k) false = val W (F W (C.gates.take k) L0) g := by
      rw [hs, F_pre W _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by omega)]
      simp [hP]
    simp only []
    rw [kv, key a ha, key b hb]
    constructor
    · intro hop; simp [val, hop, hin, W]
    · intro hop; simp [val, hop, hin]
