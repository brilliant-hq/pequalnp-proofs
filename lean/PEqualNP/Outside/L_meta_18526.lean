import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18526_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def advance (g : Gate) (w : List Bool) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem getD_missing {x : List Bool} {i : ℕ} (h : x.length ≤ i) :
    x.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

private theorem getD_advance_lt (g : Gate) (x : List Bool) (i : ℕ) (h : i < x.length) :
    (advance g x).getD i false = x.getD i false := by
  simp [advance, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem getD_advance_eq (g : Gate) (x : List Bool) :
    (advance g x).getD x.length false = g.op.eval (g.inputs.map fun i => x.getD i false) := by
  simp [advance, List.getD_eq_getElem?_getD]

private theorem advance_len (g : Gate) (x : List Bool) :
    (advance g x).length = x.length + 1 := by simp [advance]

private def renameWire (n m : ℕ) (σ : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i < n then σ i else m + (i - n)

private def renGate (n m : ℕ) (σ : ℕ → ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (renameWire n m σ)⟩

private def foldW (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => advance g w) x

private theorem foldW_append (g : Gate) (gs : List Gate) (x : List Bool) :
    foldW (gs ++ [g]) x = advance g (foldW gs x) := by simp [foldW]

private theorem foldW_len (gs : List Gate) (x : List Bool) :
    (foldW gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [foldW]
  | append_singleton gs g ih =>
    rw [foldW_append, advance_len, ih]
    simp
    omega

private theorem rename_values (gs : List Gate) (x y : List Bool) (σ : ℕ → ℕ)
    (hσ : ∀ i < x.length, σ i < y.length ∨ y.length + gs.length ≤ σ i)
    (h : ∀ i < x.length, x.getD i false = y.getD (σ i) false) :
    ∀ i, (foldW gs x).getD i false =
      (foldW (gs.map (renGate x.length y.length σ)) y).getD
        (renameWire x.length y.length σ i) false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i
    change x.getD i false = y.getD (renameWire x.length y.length σ i) false
    by_cases hi : i < x.length
    · simpa only [renameWire, ite_eq_left hi] using h i hi
    · rw [renameWire, ite_eq_right hi, getD_missing (by omega : x.length ≤ i),
        getD_missing (Nat.le_add_right ..)]
  | append_singleton gs g ih =>
    let gx := foldW gs x
    let gy := foldW (gs.map (renGate x.length y.length σ)) y
    let k := x.length + gs.length
    let l := y.length + gs.length
    let r := renameWire x.length y.length σ
    have hgx : gx.length = k := foldW_len _ _
    have hgy : gy.length = l := by simp [gy, l, foldW_len]
    have hσ' (i : ℕ) (hi : i < x.length) : σ i < y.length ∨ y.length + gs.length ≤ σ i := by
      rcases hσ i hi with h | h
      · exact Or.inl h
      · exact Or.inr (by simp at h; omega)
    have H : ∀ i, gx.getD i false = gy.getD (r i) false := ih hσ'
    have hgate : g.op.eval (g.inputs.map (fun i => gx.getD i false)) =
        (renGate x.length y.length σ g).op.eval
          ((renGate x.length y.length σ g).inputs.map (fun i => gy.getD i false)) := by
      simp only [renGate, List.map_map, Function.comp_def]
      congr 1
      exact List.map_congr_left (fun i _ => H i)
    intro i
    rw [foldW_append, List.map_append, List.map_singleton, foldW_append]
    change (advance g gx).getD i false =
      (advance (renGate x.length y.length σ g) gy).getD (r i) false
    by_cases hix : i < x.length
    · have hr : r i = σ i := by simp [r, renameWire, hix]
      rw [getD_advance_lt _ _ _ (by omega)]
      rcases hσ i hix with hlo | hhi
      · rw [getD_advance_lt _ _ _ (by omega)]
        exact H i
      · have hh : (advance (renGate x.length y.length σ g) gy).length ≤ r i := by
          rw [advance_len]
          simp at hhi
          omega
        rw [getD_missing hh, H i, getD_missing (Nat.le_trans (by rw [advance_len]; omega) hh : gy.length ≤ r i)]
    · have hr : r i = y.length + (i - x.length) := by simp [r, renameWire, hix]
      rcases lt_trichotomy i k with hk | hk | hk
      · rw [getD_advance_lt _ _ _ (by omega), getD_advance_lt _ _ _ (by omega)]
        exact H i
      · have hrk : r i = gy.length := by omega
        have hik : i = gx.length := by omega
        rw [hik, getD_advance_eq]
        have hrel : r gx.length = gy.length := by rw [← hik, hrk]
        rw [hrel, getD_advance_eq]
        exact hgate
      · rw [getD_missing (by rw [advance_len]; omega), getD_missing (by rw [advance_len]; omega)]

private theorem renamed_fan (gs : List Gate) (n m : ℕ) (σ : ℕ → ℕ) (o : ℕ)
    (h : FanInTwo ⟨gs, o⟩) : FanInTwo ⟨gs.map (renGate n m σ), renameWire n m σ o⟩ := by
  intro g hg
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
  simpa [renGate] using h q hq

private theorem ofFn_getD {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD i.val false = f i := by
  simp [List.getD_eq_getElem?_getD, i.isLt]


private theorem reindex : ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size = x3.size ∧ ∀ (x6 : Fin x1 → Bool), x5.eval (List.ofFn x6) = x3.eval (List.ofFn (x6 ∘ x2)) := by
  intro n f C hC
  let σ (i : ℕ) : ℕ := if h : i < n then (f ⟨i,h⟩).val else i
  let D : Circuit := ⟨C.gates.map (renGate n n σ), renameWire n n σ C.output⟩
  refine ⟨D,renamed_fan _ _ _ _ _ hC,by simp [D,Circuit.size],?_⟩
  intro x
  let y := List.ofFn (x ∘ f)
  let z := List.ofFn x
  have hy : y.length = n := by simp [y]
  have hz : z.length = n := by simp [z]
  have hr (i : ℕ) (hi : i < y.length) : σ i < z.length ∨ z.length + C.gates.length ≤ σ i := by
    have h : i < n := hy ▸ hi
    exact Or.inl (by simpa [σ, hz, h] using (f ⟨i,h⟩).isLt)
  have hv (i : ℕ) (hi : i < y.length) : y.getD i false = z.getD (σ i) false := by
    have h : i < n := hy ▸ hi
    change (List.ofFn (x ∘ f)).getD i false = (List.ofFn x).getD (σ i) false
    rw [show σ i = (f ⟨i,h⟩).val from dif_pos h, ofFn_getD x (f ⟨i,h⟩)]
    exact ofFn_getD (x ∘ f) ⟨i,h⟩
  have he := rename_values C.gates y z σ hr hv C.output
  rw [hy,hz] at he
  exact he.symm

end PEqualNP.Outside.L_meta_18526_aux

theorem PEqualNP.Outside.L_meta_18526 : ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size = x3.size ∧ ∀ (x6 : Fin x1 → Bool), x5.eval (List.ofFn x6) = x3.eval (List.ofFn (x6 ∘ x2)) := PEqualNP.Outside.L_meta_18526_aux.reindex
