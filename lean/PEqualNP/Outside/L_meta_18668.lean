import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18668

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem step_getD (w : List Bool) (g : Gate) (i : ℕ) : (step w g).getD i false =
    if i < w.length then w.getD i false
    else if i = w.length then g.op.eval (g.inputs.map fun i => w.getD i false) else false := by
  unfold step
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · rw [List.getD_append_right _ _ _ _ (by omega), h2]
    simp
  · exact List.getD_eq_default _ _ (by simp; omega)

theorem eval_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (f f' : ℕ → Bool)
    (h : ∀ i, f i = true → f' i = true) (hv : g.op.eval (g.inputs.map f) = true) :
    g.op.eval (g.inputs.map f') = true := by
  rcases hop with h1 | h1
  · rw [h1] at hv ⊢
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at hv ⊢
    rintro b ⟨a, ha, rfl⟩
    exact h a (hv (f a) ⟨a, ha, rfl⟩)
  · rw [h1] at hv ⊢
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at hv ⊢
    obtain ⟨b, ⟨a, ha, rfl⟩, hb⟩ := hv
    exact ⟨f' a, ⟨a, ha, rfl⟩, h a hb⟩

theorem mono_run (gs : List Gate) : ∀ (w w' : List Bool),
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) → w.length = w'.length →
    (∀ i, w.getD i false = true → w'.getD i false = true) →
    ∀ i, (gs.foldl step w).getD i false = true → (gs.foldl step w').getD i false = true := by
  induction gs with
  | nil => intro w w' _ _ h i; simpa using h i
  | cons g gs ih =>
    intro w w' hall hl h
    simp only [List.foldl_cons]
    apply ih (step w g) (step w' g) (fun g' hg' => hall g' (List.mem_cons_of_mem _ hg'))
      (by simp [step, hl])
    intro i
    rw [step_getD, step_getD, hl]
    split_ifs with h1 h2
    · exact h i
    · exact eval_mono g (hall g List.mem_cons_self) _ _ h
    · exact id

end PEqualNP.Outside.L_meta_18668

open PEqualNP.Outside.L_meta_18668

theorem PEqualNP.Outside.L_meta_18668 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → ∀ (x3 x4 : Fin (24 : ℕ) → Bool), (∀ (x5 : Fin (24 : ℕ)), x3 x5 = Bool.true → x4 x5 = Bool.true) → ∀ (x6 : ℕ), (x1.wires (List.ofFn x3)).getD x6 Bool.false = Bool.true → (x1.wires (List.ofFn x4)).getD x6 Bool.false = Bool.true := by
  intro C hm x y le k
  apply mono_run C.gates _ _ (fun g hg => (hm g hg).1) (by simp) ?_ k
  intro i hi
  by_cases h : i < 24
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn] at hi ⊢
    exact le _ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    cases hi
