import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25449_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem getD_ge (W : List Bool) (i : ℕ) (h : W.length ≤ i) : W.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

def rl (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

theorem copy (f : ℕ → ℕ) (n0 B : ℕ) (h2 : ∀ k, n0 ≤ k → f k = B + (k - n0)) :
    ∀ (gs : List Gate) (S W : List Bool), n0 ≤ S.length → W.length + n0 = S.length + B →
    (∀ k < n0, f k < B ∨ W.length + gs.length ≤ f k) →
    (∀ k, W.getD (f k) false = S.getD k false) →
    ∀ k, ((gs.map (rl f)).foldl stp W).getD (f k) false = (gs.foldl stp S).getD k false
  | [], S, W, _, _, _, hI => by simpa using hI
  | g :: gs, S, W, hS, hL, h1, hI => by
    have hv : g.op.eval ((g.inputs.map f).map fun i => W.getD i false) =
        g.op.eval (g.inputs.map fun i => S.getD i false) := by
      rw [List.map_map]; congr 1; exact List.map_congr_left (fun i _ => hI i)
    have e1 : stp W (rl f g) = W ++ [g.op.eval (g.inputs.map fun i => S.getD i false)] := by
      show W ++ [g.op.eval ((g.inputs.map f).map fun i => W.getD i false)] = _
      rw [hv]
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, e1]
    apply copy f n0 B h2 gs
    · simp [stp]; omega
    · simp [stp]; omega
    · intro k hk
      rcases h1 k hk with h | h
      · exact Or.inl h
      · right; simp at h ⊢; omega
    · intro k
      rw [stp, getD_snoc, getD_snoc]
      rcases lt_trichotomy k S.length with hk | hk | hk
      · have hne : f k ≠ W.length := by
          by_cases hk0 : k < n0
          · rcases h1 k hk0 with h | h <;> (try simp only [List.length_cons] at h) <;> omega
          · rw [h2 k (by omega)]; omega
        rw [ite_eq_left hk, ← hI k]
        by_cases ha : f k < W.length
        · rw [ite_eq_left ha]
        · rw [ite_eq_right ha, ite_eq_right hne, getD_ge _ _ (by omega)]
      · subst hk
        have : f S.length = W.length := by rw [h2 _ hS]; omega
        rw [this]; simp
      · rw [h2 k (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega)]


def shift {N N' : ℕ} (f : Fin N → Fin N') (w : ℕ) : ℕ :=
  if h : w < N then (f ⟨w, h⟩).val else w - N + N'

theorem shift_input {N N' : ℕ} (f : Fin N → Fin N') (i : Fin N) :
    shift f i.val = (f i).val := by simp [shift, i.isLt]

theorem shift_gate {N N' : ℕ} (f : Fin N → Fin N') (j : ℕ) :
    shift f (N + j) = N' + j := by simp [shift, Nat.add_comm]

theorem shift_injective {N N' : ℕ} {f : Fin N → Fin N'} (hf : Function.Injective f) :
    Function.Injective (shift f) := by
  intro i j e
  by_cases hi : i < N <;> by_cases hj : j < N
  · simp only [shift, dite_eq_left hi, dite_eq_left hj] at e
    exact congrArg Fin.val (hf (Fin.ext e))
  · simp only [shift, dite_eq_left hi, dite_eq_right hj] at e
    have := (f ⟨i,hi⟩).isLt
    omega
  · simp only [shift, dite_eq_right hi, dite_eq_left hj] at e
    have := (f ⟨j,hj⟩).isLt
    omega
  · simp only [shift, dite_eq_right hi, dite_eq_right hj] at e
    omega

def rename (C : Circuit) (r : ℕ → ℕ) : Circuit := ⟨C.gates.map (rl r), r C.output⟩

theorem rename_shape (C : Circuit) (r : ℕ → ℕ) (P : GateOp → ℕ → Prop) :
    (∀ g ∈ C.gates, P g.op g.inputs.length) ↔
    (∀ g ∈ (rename C r).gates, P g.op g.inputs.length) := by
  constructor
  · intro h g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    simpa [rl] using h a ha
  · intro h g hg
    have hg' : rl r g ∈ (rename C r).gates := List.mem_map.mpr ⟨g,hg,rfl⟩
    simpa [rl] using h _ hg'

theorem rename_gateAt (C : Circuit) (r : ℕ → ℕ) (j : ℕ) :
    gateAt (rename C r) j = rl r (gateAt C j) := by
  by_cases h : j < C.gates.length
  · have hm : j < (rename C r).gates.length := by simpa [rename] using h
    rw [gateAt, gateAt, List.getD_eq_getElem _ _ hm, List.getD_eq_getElem _ _ h]
    simp [rename]
  · have hm : (rename C r).gates.length ≤ j := by simpa [rename] using Nat.le_of_not_gt h
    rw [gateAt, gateAt, List.getD_eq_default _ _ hm, List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    rfl

theorem rename_reads {C : Circuit} {r : ℕ → ℕ} (hr : Function.Injective r)
    (G : Finset ℕ) (w : ℕ) : readsIn (rename C r) G (r w) = readsIn C G w := by
  unfold readsIn
  apply Finset.sum_congr rfl
  intro j _
  rw [rename_gateAt]
  exact List.count_map_of_injective _ _ hr _

theorem rename_misses {C : Circuit} {r : ℕ → ℕ} (G : Finset ℕ)
    {w : ℕ} (h : ∀ i, r i ≠ w) : readsIn (rename C r) G w = 0 := by
  unfold readsIn
  apply Finset.sum_eq_zero
  intro j _
  rw [rename_gateAt]
  apply List.count_eq_zero.mpr
  intro hm
  obtain ⟨i,_,he⟩ := List.mem_map.mp hm
  exact h i he

theorem rename_back {N N' : ℕ} (f : Fin N → Fin N') (C : Circuit)
    (h : ReadsBack N C) : ReadsBack N' (rename C (shift f)) := by
  intro j hj w hw
  have hlen : j < C.gates.length := by simpa [rename] using hj
  rw [rename_gateAt] at hw
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
  have hlt := h j hlen i hi
  by_cases hin : i < N
  · have hi' := (f ⟨i,hin⟩).isLt
    simp only [shift,dite_eq_left hin]
    omega
  · simp only [shift,dite_eq_right hin]
    omega

theorem rename_eval {N N' : ℕ} (f : Fin N → Fin N') (C : Circuit) (x : Fin N' → Bool) :
    (rename C (shift f)).eval (List.ofFn x) = C.eval (List.ofFn fun i => x (f i)) := by
  change ((C.gates.map (rl (shift f))).foldl stp (List.ofFn x)).getD (shift f C.output) false =
    (C.gates.foldl stp (List.ofFn fun i => x (f i))).getD C.output false
  refine copy (shift f) N N' (fun i hi => by simp [shift, dite_eq_right (Nat.not_lt_of_ge hi), Nat.add_comm])
    C.gates _ _ (by simp) (by simp [Nat.add_comm]) ?_ ?_ C.output
  · intro i hi
    exact Or.inl (by simp [shift,hi])
  · intro i
    by_cases hi : i < N
    · have hj := (f ⟨i,hi⟩).isLt
      simp only [shift, dite_eq_left hi, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hj,
        Option.getD_some]
    · have hshift : N' ≤ shift f i := by simp [shift,hi]
      rw [getD_ge _ _ (by simpa using hshift), getD_ge _ _ (by simpa using Nat.le_of_not_gt hi)]

end PEqualNP.Outside.L_meta_25449_aux

open PEqualNP.Outside.L_meta_25449_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.L_meta_25449 : ∀ (N N' : ℕ) (f : Fin N → Fin N') (C C' : PEqualNP.CircuitLowerBounds.Circuit) (ρ : ℕ → ℕ), Function.Injective f → ρ = (fun w => if h : w < N then (f ⟨w, h⟩).val else w - N + N') → C' = ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map ρ⟩), ρ C.output⟩ → (∀ x : Fin N' → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn (fun i => x (f i)))) ∧ C'.size = C.size ∧ (PEqualNP.MetaComplexity.FanInTwo C ↔ PEqualNP.MetaComplexity.FanInTwo C') ∧ (PEqualNP.MetaComplexity.Monotone2 C ↔ PEqualNP.MetaComplexity.Monotone2 C') ∧ (PEqualNP.MetaComplexity.NestedCover.ReadsBack N C → PEqualNP.MetaComplexity.NestedCover.ReadsBack N' C') ∧ (∀ (G : Finset ℕ) (i : Fin N), PEqualNP.MetaComplexity.NestedCover.readsIn C' G (f i).val = PEqualNP.MetaComplexity.NestedCover.readsIn C G i.val) ∧ (∀ (G : Finset ℕ) (i : Fin N'), (∀ i0 : Fin N, f i0 ≠ i) → PEqualNP.MetaComplexity.NestedCover.readsIn C' G i.val = 0) ∧ (∀ (G : Finset ℕ) (j : ℕ), PEqualNP.MetaComplexity.NestedCover.readsIn C' G (N' + j) = PEqualNP.MetaComplexity.NestedCover.readsIn C G (N + j)) := by
  rintro N N' f C C' r hf rfl rfl
  change _ ∧ (rename C (shift f)).size = C.size ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  refine ⟨rename_eval f C, by simp [rename,Circuit.size], ?_, ?_,
    rename_back f C, ?_, ?_, ?_⟩
  · exact rename_shape C (shift f) (fun op k => op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ k ≤ 2)
  · exact rename_shape C (shift f) (fun op k => op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ k ≤ 2)
  · intro G i
    change readsIn (rename C (shift f)) G (f i).val = readsIn C G i.val
    simpa only [shift_input] using rename_reads (C := C) (shift_injective hf) G i.val
  · intro G i hi
    change readsIn (rename C (shift f)) G i.val = 0
    apply rename_misses G
    intro w hw
    change shift f w = i.val at hw
    by_cases ht : w < N
    · exact hi ⟨w,ht⟩ (Fin.ext (by simpa [shift,ht] using hw))
    · have hlarge : N' ≤ shift f w := by simp [shift,ht]
      have hsmall := i.isLt
      omega
  · intro G j
    change readsIn (rename C (shift f)) G (N' + j) = readsIn C G (N + j)
    simpa only [shift_gate] using rename_reads (C := C) (shift_injective hf) G (N + j)
