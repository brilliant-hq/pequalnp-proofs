import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18709_aux

open PEqualNP.CircuitLowerBounds

def F (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem len (gs : List Gate) : ∀ w : List Bool, (gs.foldl F w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih => intro w; simp only [List.foldl_cons, ih, F]; simp; omega

theorem keep (gs : List Gate) : ∀ w : List Bool, ∀ i, i < w.length →
    (gs.foldl F w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i h; simp
  | cons g gs ih =>
    intro w i h
    simp only [List.foldl_cons]
    rw [ih _ i (by simp [F]; omega)]
    simp only [F]
    rw [List.getD_append _ _ _ _ h]

theorem mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, a.length = b.length → (∀ i, a.getD i false = true → b.getD i false = true) →
      ∀ i, (gs.foldl F a).getD i false = true → (gs.foldl F b).getD i false = true := by
  induction gs with
  | nil => intro a b _ h; exact h
  | cons g gs ih =>
    intro a b hl hv
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hg g' (by simp [hg']))
    · simp [F, hl]
    · intro i hi
      have hev : g.op.eval (g.inputs.map fun i => a.getD i false) = true →
          g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
        rcases hg g (by simp) with h | h <;> rw [h] <;> simp [GateOp.eval]
        · intro H j hj; exact hv _ (H j hj)
        · intro j hj H; exact ⟨j, hj, hv _ H⟩
      simp only [F] at hi ⊢
      rcases lt_trichotomy i a.length with h1 | h1 | h1
      · rw [List.getD_append _ _ _ _ h1] at hi
        rw [List.getD_append _ _ _ _ (hl ▸ h1)]
        exact hv _ hi
      · subst h1
        rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
        rw [hl, List.getD_append_right _ _ _ _ (le_refl _)]
        simp at hi ⊢
        exact hev hi
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        simp at hi

theorem at_gate (gs : List Gate) (k : ℕ) (g : Gate) (hk : gs[k]? = some g) (x : List Bool)
    (hi : ∀ j ∈ g.inputs, j < x.length + k) :
    (gs.foldl F x).getD (x.length + k) false =
      g.op.eval (g.inputs.map fun j => (gs.foldl F x).getD j false) := by
  obtain ⟨hk1, hk2⟩ := List.getElem?_eq_some_iff.mp hk
  have hs : gs = gs.take k ++ g :: gs.drop (k + 1) := by
    rw [← hk2, List.getElem_cons_drop, List.take_append_drop]
  have hl : ((gs.take k).foldl F x).length = x.length + k := by
    rw [len]; simp; omega
  rw [hs, List.foldl_append, List.foldl_cons]
  rw [keep _ _ _ (by simp [F, hl])]
  have hm : g.inputs.map (fun j => (List.foldl F (F (List.foldl F x (List.take k gs)) g)
      (List.drop (k + 1) gs)).getD j false) =
      g.inputs.map (fun j => (List.foldl F x (List.take k gs)).getD j false) := by
    apply List.map_congr_left
    intro j hj
    have := hi j hj
    rw [keep _ _ _ (by simp [F]; omega)]
    simp only [F]
    rw [List.getD_append _ _ _ _ (by omega)]
  rw [hm]
  simp only [F]
  rw [← hl, List.getD_append_right _ _ _ _ le_rfl]
  simp

end PEqualNP.Outside.L_meta_18709_aux

open PEqualNP.Outside.L_meta_18709_aux in
theorem PEqualNP.Outside.L_meta_18709 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 x5 : ℕ), PEqualNP.TopForm.IsAO2 x1 x2 → x2.output = x1 + x3 → x2.gates[x3]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x4, x5] : PEqualNP.CircuitLowerBounds.Gate } → ∀ (x9 x10 : Fin x1), (x2.wires (List.ofFn fun (x11 : Fin x1) => Decidable.decide (x11 = x9))).getD x4 Bool.false = Bool.true → (x2.wires (List.ofFn fun (x12 : Fin x1) => Decidable.decide (x12 = x10))).getD x5 Bool.false = Bool.true → x2.eval (List.ofFn fun (x13 : Fin x1) => Decidable.decide (x13 = x9 ∨ x13 = x10)) = Bool.true := by
  intro n C k a b hC hout hk i j ha hb
  obtain ⟨h1, h2, _⟩ := hC
  have hg : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or := h1
  have hk1 : k < C.gates.length := (List.getElem?_eq_some_iff.mp hk).1
  have hin : ∀ q ∈ [a, b], q < n + k := by
    intro q hq
    have := h2 k hk1 q
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hk, Option.getD_some] at this
    exact this hq
  have hw : ∀ (y z : Fin n → Bool), (∀ t, y t = true → z t = true) → ∀ q,
      (C.wires (List.ofFn y)).getD q false = true → (C.wires (List.ofFn z)).getD q false = true := by
    intro y z hyz
    apply mono C.gates hg
    · simp
    · intro q hq
      by_cases h : q < n
      · rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; omega)] at hq ⊢
        simp only [List.getElem_ofFn] at hq ⊢
        exact hyz _ hq
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hq
        simp at hq
  have ha' := hw _ (fun t : Fin n => decide (t = i ∨ t = j)) (by intro t; simp; intro h; exact Or.inl h) a ha
  have hb' := hw _ (fun t : Fin n => decide (t = i ∨ t = j)) (by intro t; simp; intro h; exact Or.inr h) b hb
  unfold PEqualNP.CircuitLowerBounds.Circuit.eval
  rw [hout]
  have := at_gate C.gates k _ hk (List.ofFn fun t : Fin n => decide (t = i ∨ t = j)) (by simpa using hin)
  simp only [List.length_ofFn] at this
  unfold PEqualNP.CircuitLowerBounds.Circuit.wires at ha' hb' ⊢
  rw [show (fun w (g : PEqualNP.CircuitLowerBounds.Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = F from rfl] at ha' hb' ⊢
  rw [this]
  simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil, ha', hb']
  rfl
