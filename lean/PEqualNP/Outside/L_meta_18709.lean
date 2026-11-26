import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18709

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem ev_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (U V : List Bool)
    (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    g.op.eval (g.inputs.map fun i => U.getD i false) = true →
      g.op.eval (g.inputs.map fun i => V.getD i false) = true := by
  rcases hg with h1 | h1 <;> rw [h1] <;> simp only [GateOp.eval, List.all_eq_true, List.any_eq_true,
    List.mem_map, id_eq]
  · intro hu x ⟨i, hi, hx⟩
    subst hx
    exact h i (hu _ ⟨i, hi, rfl⟩)
  · rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨_, ⟨i, hi, rfl⟩, h i hx⟩

theorem key : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    ∀ U V : List Bool, U.length = V.length → (∀ i, U.getD i false = true → V.getD i false = true) →
    ∀ i, (gs.foldl stp U).getD i false = true → (gs.foldl stp V).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro _ U V _ h i; exact h i
  | cons g gs ih =>
    intro hgs U V hl h i
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [stp, hl]
    · intro k hk
      unfold stp at hk ⊢
      rcases Nat.lt_trichotomy k U.length with hlt | heq | hgt
      · rw [List.getD_append _ _ _ _ hlt] at hk
        rw [List.getD_append _ _ _ _ (hl ▸ hlt)]
        exact h k hk
      · subst heq
        rw [List.getD_append_right _ _ _ _ (le_refl _)] at hk
        rw [hl, List.getD_append_right _ _ _ _ (le_refl _)]
        simp only [Nat.sub_self, List.getD_cons_zero] at hk ⊢
        exact ev_mono g (hgs g (List.mem_cons_self ..)) U V h hk
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hk
        exact absurd hk (by simp)

theorem stp_ext : ∀ (gs : List Gate) (w : List Bool), ∃ r, gs.foldl stp w = w ++ r := by
  intro gs
  induction gs with
  | nil => intro w; exact ⟨[], by simp⟩
  | cons g gs ih =>
    intro w
    obtain ⟨r, hr⟩ := ih (stp w g)
    exact ⟨(g.op.eval (g.inputs.map fun i => w.getD i false)) :: r, by rw [List.foldl_cons, hr]; simp [stp]⟩

theorem getD_pre (L A : List Bool) (i : ℕ) (h : i < L.length) : (L ++ A).getD i false = L.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem len_fold : ∀ (gs : List Gate) (w : List Bool), (gs.foldl stp w).length = w.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro w; simp
  | cons g gs ih => intro w; rw [List.foldl_cons, ih]; simp [stp]; omega

theorem at_gate (gs : List Gate) (L : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
    let W := (gs.take j).foldl stp L
    W.length = L.length + j ∧
    (∀ i < L.length + j, (gs.foldl stp L).getD i false = W.getD i false) ∧
    (gs.foldl stp L).getD (L.length + j) false = g.op.eval (g.inputs.map fun i => W.getD i false) := by
  intro W
  have hjl : j < gs.length := by
    rcases Nat.lt_or_ge j gs.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hj; cases hj
  have hd : gs.drop j = g :: gs.drop (j + 1) := by
    rw [List.drop_eq_getElem_cons hjl]
    rw [List.getElem?_eq_getElem hjl] at hj
    cases hj; rfl
  have hsplit : gs.foldl stp L = (gs.drop (j + 1)).foldl stp (stp W g) := by
    conv_lhs => rw [← List.take_append_drop j gs]
    rw [List.foldl_append, hd, List.foldl_cons]
  have hWl : W.length = L.length + j := by
    simp only [W]; rw [len_fold, List.length_take]; omega
  obtain ⟨r, hr⟩ := stp_ext (gs.drop (j + 1)) (stp W g)
  refine ⟨hWl, ?_, ?_⟩
  · intro i hi
    rw [hsplit, hr, getD_pre _ _ i (by simp [stp]; omega)]
    simp only [stp]
    exact getD_pre _ _ i (by omega)
  · rw [hsplit, hr, getD_pre _ _ _ (by simp [stp]; omega)]
    simp only [stp]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    simp [hWl]

end PEqualNP.Outside.L_meta_18709

open PEqualNP.Outside.L_meta_18709 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_18709 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 x5 : ℕ), PEqualNP.TopForm.IsAO2 x1 x2 → x2.output = x1 + x3 → x2.gates[x3]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x4, x5] : PEqualNP.CircuitLowerBounds.Gate } → ∀ (x9 x10 : Fin x1), (x2.wires (List.ofFn fun (x11 : Fin x1) => Decidable.decide (x11 = x9))).getD x4 Bool.false = Bool.true → (x2.wires (List.ofFn fun (x12 : Fin x1) => Decidable.decide (x12 = x10))).getD x5 Bool.false = Bool.true → x2.eval (List.ofFn fun (x13 : Fin x1) => Decidable.decide (x13 = x9 ∨ x13 = x10)) = Bool.true := by
  intro n C j a b hC hout hg u v hu hv
  have hgs : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := hC.1
  let P : List Bool := List.ofFn fun i : Fin n => decide (i = u ∨ i = v)
  have hmono : ∀ (w : Fin n), (w = u ∨ w = v) → (∀ i, (List.ofFn fun k : Fin n => decide (k = w)).getD i false = true → P.getD i false = true) := by
    intro w hw i hi
    by_cases h : i < n
    · have e1 : (List.ofFn fun k : Fin n => decide (k = w)).getD i false = decide ((⟨i, h⟩ : Fin n) = w) := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h]; rfl
      have e2 : P.getD i false = decide ((⟨i, h⟩ : Fin n) = u ∨ (⟨i, h⟩ : Fin n) = v) := by
        simp only [P, List.getD_eq_getElem?_getD, List.getElem?_ofFn, h]; rfl
      rw [e1] at hi; rw [e2]
      simp only [decide_eq_true_eq] at hi ⊢
      rcases hw with rfl | rfl
      · exact Or.inl hi
      · exact Or.inr hi
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; exact absurd hi (by simp)
  have hu' : (C.wires P).getD a false = true :=
    key C.gates hgs _ P (by simp [P]) (hmono u (Or.inl rfl)) a hu
  have hv' : (C.wires P).getD b false = true :=
    key C.gates hgs _ P (by simp [P]) (hmono v (Or.inr rfl)) b hv
  obtain ⟨hWl, hpre, hval⟩ := at_gate C.gates P j _ hg
  have hjl : j < C.gates.length := by
    rcases Nat.lt_or_ge j C.gates.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hg; cases hg
  have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C j = ⟨GateOp.and, [a, b]⟩ := by
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hg, Option.getD_some]
  have ha : a < n + j := hC.2.1 j hjl a (by rw [hga]; simp)
  have hb : b < n + j := hC.2.1 j hjl b (by rw [hga]; simp)
  have hPl : P.length = n := by simp [P]
  show (C.wires P).getD C.output false = true
  have e : (C.wires P).getD C.output false = (C.gates.foldl stp P).getD (P.length + j) false := by
    rw [hout, hPl]; rfl
  rw [e, hval]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true]
  rw [← hpre a (by omega), ← hpre b (by omega)]
  change ((C.wires P).getD a false && (C.wires P).getD b false) = true
  rw [hu', hv']; rfl
