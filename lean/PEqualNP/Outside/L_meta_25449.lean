import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25449

-- stp, getD_snoc, getD_ge, mg and sim copied from our parked L-meta-25307 proof.

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

def mg (s : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map s⟩

theorem sim (s : ℕ → ℕ) (N L : ℕ) (gs : List Gate) : ∀ W Y : List Bool,
    W.length = Y.length + L → N ≤ Y.length → (∀ i, N ≤ i → s i = i + L) →
    (∀ i, i < N → s i < W.length ∨ W.length + gs.length ≤ s i) →
    (∀ i, W.getD (s i) false = Y.getD i false) →
    ∀ i, ((gs.map (mg s)).foldl stp W).getD (s i) false = (gs.foldl stp Y).getD i false := by
  induction gs with
  | nil => intro W Y _ _ _ _ h5; simpa using h5
  | cons g gs ih =>
    intro W Y h1 h2 h3 h4 h5
    simp only [List.map_cons, List.foldl_cons]
    have eW : (stp W (mg s g)).length = W.length + 1 := by simp [stp]
    have eY : (stp Y g).length = Y.length + 1 := by simp [stp]
    apply ih
    · rw [eW, eY]; omega
    · rw [eY]; omega
    · exact h3
    · intro i hi
      have := h4 i hi
      simp only [List.length_cons] at this
      rw [eW]; omega
    · intro i
      simp only [stp]
      rw [getD_snoc, getD_snoc]
      by_cases hi : i < N
      · rcases h4 i hi with h | h
        · rw [if_pos h, if_pos (by omega : i < Y.length)]; exact h5 i
        · simp only [List.length_cons] at h
          have e1 := h5 i
          rw [getD_ge W (s i) (by omega)] at e1
          rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
          exact e1
      · have hs := h3 i (by omega)
        rcases lt_trichotomy i Y.length with h | h | h
        · rw [if_pos (by omega), if_pos h]; exact h5 i
        · rw [hs, if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos h]
          simp only [mg, List.map_map, Function.comp_def]
          congr 1
          apply List.map_congr_left
          intro j _
          exact h5 j
        · rw [hs, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem ofn_get (n : ℕ) (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp

end PEqualNP.Outside.L_meta_25449

open PEqualNP.Outside.L_meta_25449 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_25449 : ∀ (N N' : ℕ) (f : Fin N → Fin N') (C C' : PEqualNP.CircuitLowerBounds.Circuit) (ρ : ℕ → ℕ), Function.Injective f → ρ = (fun w => if h : w < N then (f ⟨w, h⟩).val else w - N + N') → C' = ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map ρ⟩), ρ C.output⟩ → (∀ x : Fin N' → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn (fun i => x (f i)))) ∧ C'.size = C.size ∧ (PEqualNP.MetaComplexity.FanInTwo C ↔ PEqualNP.MetaComplexity.FanInTwo C') ∧ (PEqualNP.MetaComplexity.Monotone2 C ↔ PEqualNP.MetaComplexity.Monotone2 C') ∧ (PEqualNP.MetaComplexity.NestedCover.ReadsBack N C → PEqualNP.MetaComplexity.NestedCover.ReadsBack N' C') ∧ (∀ (G : Finset ℕ) (i : Fin N), PEqualNP.MetaComplexity.NestedCover.readsIn C' G (f i).val = PEqualNP.MetaComplexity.NestedCover.readsIn C G i.val) ∧ (∀ (G : Finset ℕ) (i : Fin N'), (∀ i0 : Fin N, f i0 ≠ i) → PEqualNP.MetaComplexity.NestedCover.readsIn C' G i.val = 0) ∧ (∀ (G : Finset ℕ) (j : ℕ), PEqualNP.MetaComplexity.NestedCover.readsIn C' G (N' + j) = PEqualNP.MetaComplexity.NestedCover.readsIn C G (N + j)) := by
  intro N N' f C C' ρ hf hρ hC'
  have hNN : N ≤ N' := by simpa using Fintype.card_le_of_injective f hf
  have r1 : ∀ w (h : w < N), ρ w = (f ⟨w, h⟩).val := by intro w h; rw [hρ]; simp [h]
  have r2 : ∀ w, N ≤ w → ρ w = w - N + N' := by
    intro w h; rw [hρ]; simp [show ¬ w < N by omega]
  have rinj : Function.Injective ρ := by
    intro a b hab
    by_cases ha : a < N <;> by_cases hb : b < N
    · rw [r1 a ha, r1 b hb] at hab
      have := hf (Fin.ext hab)
      simpa using this
    · rw [r1 a ha, r2 b (by omega)] at hab; have := (f ⟨a, ha⟩).isLt; omega
    · rw [r2 a (by omega), r1 b hb] at hab; have := (f ⟨b, hb⟩).isLt; omega
    · rw [r2 a (by omega), r2 b (by omega)] at hab; omega
  have hg : C'.gates = C.gates.map (mg ρ) := by rw [hC']; rfl
  have ho : C'.output = ρ C.output := by rw [hC']
  have hgat : ∀ j, PEqualNP.MetaComplexity.NestedCover.gateAt C' j =
      mg ρ (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
    intro j
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [hg, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases C.gates[j]? <;> rfl
  have hfi : ∀ i : Fin N, (f i).val = ρ i.val := by
    intro i; rw [r1 i.val i.isLt]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    unfold Circuit.eval Circuit.wires
    rw [hg, ho]
    change ((C.gates.map (mg ρ)).foldl stp _).getD _ _ = (C.gates.foldl stp _).getD _ _
    refine sim ρ N (N' - N) C.gates _ _ (by simp; omega) (by simp) (fun i hi => by rw [r2 i hi]; omega)
      (fun i hi => Or.inl (by rw [r1 i hi]; simp)) (fun i => ?_) C.output
    by_cases hi : i < N
    · rw [r1 i hi, ofn_get _ _ _ (f ⟨i, hi⟩).isLt, ofn_get _ _ _ hi]
    · rw [r2 i (by omega), getD_ge _ _ (by simp <;> omega), getD_ge _ _ (by simp <;> omega)]
  · unfold Circuit.size; rw [hg, List.length_map]
  · unfold PEqualNP.MetaComplexity.FanInTwo; rw [hg]; simp [mg]
  · unfold PEqualNP.MetaComplexity.Monotone2; rw [hg]; simp [mg]
  · intro h
    unfold PEqualNP.MetaComplexity.NestedCover.ReadsBack at h ⊢
    intro j hj i hi
    rw [hg, List.length_map] at hj
    rw [hgat] at hi
    simp only [mg, List.mem_map] at hi
    obtain ⟨w, hw, rfl⟩ := hi
    have := h j hj w hw
    by_cases hwN : w < N
    · rw [r1 w hwN]; have := (f ⟨w, hwN⟩).isLt; omega
    · rw [r2 w (by omega)]; omega
  · intro G i
    unfold PEqualNP.MetaComplexity.NestedCover.readsIn
    apply Finset.sum_congr rfl
    intro j _
    rw [hgat, hfi]
    exact List.count_map_of_injective _ _ rinj _
  · intro G i hi
    unfold PEqualNP.MetaComplexity.NestedCover.readsIn
    apply Finset.sum_eq_zero
    intro j _
    rw [hgat]
    apply List.count_eq_zero.2
    simp only [mg, List.mem_map, not_exists, not_and]
    intro w _ hw
    by_cases hwN : w < N
    · rw [r1 w hwN] at hw; exact hi ⟨w, hwN⟩ (Fin.ext hw)
    · rw [r2 w (by omega)] at hw; have := i.isLt; omega
  · intro G j
    unfold PEqualNP.MetaComplexity.NestedCover.readsIn
    apply Finset.sum_congr rfl
    intro k _
    rw [hgat, show N' + j = ρ (N + j) by rw [r2 _ (by omega)]; omega]
    exact List.count_map_of_injective _ _ rinj _
