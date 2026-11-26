import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25449_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def rho (N N' : ℕ) (f : Fin N → Fin N') (w : ℕ) : ℕ :=
  if h : w < N then (f ⟨w, h⟩).val else w - N + N'

theorem rho_lt {N N' : ℕ} (f : Fin N → Fin N') (i : Fin N) : rho N N' f i.val = (f i).val := by
  simp [rho, i.isLt]

theorem rho_ge {N N' : ℕ} (f : Fin N → Fin N') (j : ℕ) : rho N N' f (N + j) = N' + j := by
  simp [rho]; omega

theorem rho_inj {N N' : ℕ} (f : Fin N → Fin N') (hf : Function.Injective f) :
    Function.Injective (rho N N' f) := by
  intro a b hab
  unfold rho at hab
  split_ifs at hab with ha hb hb
  · have h1 := hf (Fin.ext hab)
    exact congrArg Fin.val h1
  · have := (f ⟨a, ha⟩).isLt; omega
  · have := (f ⟨b, hb⟩).isLt; omega
  · omega

def ren (N N' : ℕ) (f : Fin N → Fin N') (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (rho N N' f)⟩

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Inv (N N' : ℕ) (f : Fin N → Fin N') (k : ℕ) (w w' : List Bool) : Prop :=
  w.length = N + k ∧ w'.length = N' + k ∧ ∀ i, w'.getD (rho N N' f i) false = w.getD i false

theorem inv_step {N N' : ℕ} (f : Fin N → Fin N') (k : ℕ) (w w' : List Bool) (g : Gate)
    (h : Inv N N' f k w w') : Inv N N' f (k + 1) (stepW w g) (stepW w' (ren N N' f g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (ren N N' f g).op.eval ((ren N N' f g).inputs.map fun i => w'.getD i false)
      = g.op.eval (g.inputs.map fun i => w.getD i false) := by
    simp only [ren, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact h3 i
  refine ⟨by simp [stepW, h1]; omega, by simp [stepW, h2]; omega, ?_⟩
  intro i
  unfold stepW
  rw [hv]
  have h3i := h3 i
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append] at h3i ⊢
  by_cases hi : i < N
  · have hr : rho N N' f i < w'.length := by
      have := (f ⟨i, hi⟩).isLt
      simp only [rho, hi, ↓reduceDIte]; omega
    have hi' : i < w.length := by omega
    simp only [hr, hi', ↓reduceIte]
    exact h3i
  · have hre : rho N N' f i = i - N + N' := by simp [rho, hi]
    rw [hre] at h3i ⊢
    by_cases hik : i < N + k
    · have hr : i - N + N' < w'.length := by omega
      have hi' : i < w.length := by omega
      simp only [hr, hi', ↓reduceIte]
      exact h3i
    · have hr : ¬ (i - N + N' < w'.length) := by omega
      have hi' : ¬ (i < w.length) := by omega
      simp only [hr, hi', ↓reduceIte]
      have e : i - N + N' - w'.length = i - w.length := by omega
      rw [e]

theorem inv_fold {N N' : ℕ} (f : Fin N → Fin N') (gs : List Gate) :
    ∀ (k : ℕ) (w w' : List Bool), Inv N N' f k w w' →
      Inv N N' f (k + gs.length) (gs.foldl stepW w) ((gs.map (ren N N' f)).foldl stepW w') := by
  induction gs with
  | nil => intro k w w' h; simpa using h
  | cons g gs ih =>
    intro k w w' h
    have h' := ih (k + 1) _ _ (inv_step f k w w' g h)
    simp only [List.foldl_cons, List.map_cons, List.length_cons]
    have e : k + (gs.length + 1) = k + 1 + gs.length := by omega
    rw [e]
    exact h'

theorem inv_start {N N' : ℕ} (f : Fin N → Fin N') (x : Fin N' → Bool) :
    Inv N N' f 0 (List.ofFn fun i => x (f i)) (List.ofFn x) := by
  refine ⟨by simp, by simp, ?_⟩
  intro i
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases hi : i < N
  · have hr : rho N N' f i = (f ⟨i, hi⟩).val := by simp [rho, hi]
    have hlt := (f ⟨i, hi⟩).isLt
    rw [hr]
    simp [hi, hlt]
  · have hr : rho N N' f i = i - N + N' := by simp [rho, hi]
    have hlt : ¬ (i - N + N' < N') := by omega
    rw [hr]
    simp [hi, hlt]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

theorem gateAt_ren {N N' : ℕ} (f : Fin N → Fin N') (C : Circuit) (o : ℕ) (j : ℕ) :
    gateAt ⟨C.gates.map (ren N N' f), o⟩ j = ren N N' f (gateAt C j) := by
  unfold gateAt
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases C.gates[j]? <;> simp [ren]

theorem main (N N' : ℕ) (f : Fin N → Fin N') (C : Circuit) (hf : Function.Injective f) :
    (∀ x : Fin N' → Bool,
        (⟨C.gates.map (ren N N' f), rho N N' f C.output⟩ : Circuit).eval (List.ofFn x)
          = C.eval (List.ofFn (fun i => x (f i)))) ∧
    (⟨C.gates.map (ren N N' f), rho N N' f C.output⟩ : Circuit).size = C.size ∧
    (FanInTwo C ↔ FanInTwo ⟨C.gates.map (ren N N' f), rho N N' f C.output⟩) ∧
    (Monotone2 C ↔ Monotone2 ⟨C.gates.map (ren N N' f), rho N N' f C.output⟩) ∧
    (ReadsBack N C → ReadsBack N' ⟨C.gates.map (ren N N' f), rho N N' f C.output⟩) ∧
    (∀ (G : Finset ℕ) (i : Fin N),
        readsIn ⟨C.gates.map (ren N N' f), rho N N' f C.output⟩ G (f i).val = readsIn C G i.val) ∧
    (∀ (G : Finset ℕ) (i : Fin N'), (∀ i0 : Fin N, f i0 ≠ i) →
        readsIn ⟨C.gates.map (ren N N' f), rho N N' f C.output⟩ G i.val = 0) ∧
    (∀ (G : Finset ℕ) (j : ℕ),
        readsIn ⟨C.gates.map (ren N N' f), rho N N' f C.output⟩ G (N' + j)
          = readsIn C G (N + j)) := by
  have hinj := rho_inj f hf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    have h := inv_fold f C.gates 0 _ _ (inv_start f x)
    unfold Circuit.eval
    rw [wires_eq, wires_eq]
    exact h.2.2 C.output
  · simp [Circuit.size]
  · simp [FanInTwo, ren]
  · simp [Monotone2, ren]
  · intro h j hj i hi
    rw [gateAt_ren] at hi
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hi
    have hj' : j < C.gates.length := by simpa using hj
    have hlt := h j hj' w hw
    unfold rho
    split_ifs with hwN
    · have := (f ⟨w, hwN⟩).isLt; omega
    · omega
  · intro G i
    unfold readsIn
    apply Finset.sum_congr rfl
    intro j _
    rw [gateAt_ren, ← rho_lt f i]
    exact List.count_map_of_injective _ _ hinj _
  · intro G i hi
    unfold readsIn
    apply Finset.sum_eq_zero
    intro j _
    rw [gateAt_ren]
    apply List.count_eq_zero.2
    intro hmem
    obtain ⟨w, _, hw⟩ := List.mem_map.1 hmem
    unfold rho at hw
    split_ifs at hw with hwN
    · exact hi ⟨w, hwN⟩ (Fin.ext hw)
    · have := i.isLt; omega
  · intro G j
    unfold readsIn
    apply Finset.sum_congr rfl
    intro k _
    rw [gateAt_ren, ← rho_ge f j]
    exact List.count_map_of_injective _ _ hinj _

end PEqualNP.Outside.L_meta_25449_aux

theorem PEqualNP.Outside.L_meta_25449 : (∀ (N N' : ℕ) (f : Fin N → Fin N') (C C' : PEqualNP.CircuitLowerBounds.Circuit) (ρ : ℕ → ℕ), Function.Injective f → ρ = (fun w => if h : w < N then (f ⟨w, h⟩).val else w - N + N') → C' = ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map ρ⟩), ρ C.output⟩ → (∀ x : Fin N' → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn (fun i => x (f i)))) ∧ C'.size = C.size ∧ (PEqualNP.MetaComplexity.FanInTwo C ↔ PEqualNP.MetaComplexity.FanInTwo C') ∧ (PEqualNP.MetaComplexity.Monotone2 C ↔ PEqualNP.MetaComplexity.Monotone2 C') ∧ (PEqualNP.MetaComplexity.NestedCover.ReadsBack N C → PEqualNP.MetaComplexity.NestedCover.ReadsBack N' C') ∧ (∀ (G : Finset ℕ) (i : Fin N), PEqualNP.MetaComplexity.NestedCover.readsIn C' G (f i).val = PEqualNP.MetaComplexity.NestedCover.readsIn C G i.val) ∧ (∀ (G : Finset ℕ) (i : Fin N'), (∀ i0 : Fin N, f i0 ≠ i) → PEqualNP.MetaComplexity.NestedCover.readsIn C' G i.val = 0) ∧ (∀ (G : Finset ℕ) (j : ℕ), PEqualNP.MetaComplexity.NestedCover.readsIn C' G (N' + j) = PEqualNP.MetaComplexity.NestedCover.readsIn C G (N + j))) := by
  intro N N' f C C' ρ hf hρ hC'
  have hρ' : ρ = PEqualNP.Outside.L_meta_25449_aux.rho N N' f := hρ
  subst hρ'
  subst hC'
  exact PEqualNP.Outside.L_meta_25449_aux.main N N' f C hf
