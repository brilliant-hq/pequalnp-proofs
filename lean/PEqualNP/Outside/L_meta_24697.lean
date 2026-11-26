import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24697_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Represents PEqualNP.MetaComplexity.NestedCover

def permWire {n m : ℕ} (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (i : ℕ) : ℕ :=
  if h : i < n then (π ⟨i, h⟩).val
  else if h : i - n < m then n + (ρ ⟨i - n, h⟩).val else i

theorem perm_row {n m : ℕ} (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (u : Fin n) :
    permWire π ρ u.val = (π u).val := by
  simp [permWire, u.isLt]

theorem perm_col {n m : ℕ} (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (v : Fin m) :
    permWire π ρ (n + v.val) = n + (ρ v).val := by
  simp [permWire, show ¬ n + v.val < n by omega, v.isLt]

theorem perm_upper {n m i : ℕ} (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m))
    (hi : n + m ≤ i) : permWire π ρ i = i := by
  simp [permWire, show ¬i < n by omega, show ¬i - n < m by omega]

theorem perm_lt {n m i l : ℕ} (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m))
    (hl : n + m ≤ l) : permWire π ρ i < l ↔ i < l := by
  by_cases hi : i < n
  · have hp := (π ⟨i, hi⟩).isLt
    rw [permWire, dite_eq_left hi]
    omega
  · by_cases hc : i - n < m
    · have hp := (ρ ⟨i - n, hc⟩).isLt
      rw [permWire, dite_eq_right hi, dite_eq_left hc]
      omega
    · have he : n + m ≤ i := by omega
      rw [perm_upper π ρ he]

theorem perm_inverse {n m : ℕ} (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m))
    (i : ℕ) : permWire π ρ (permWire π.symm ρ.symm i) = i := by
  by_cases hr : i < n
  · let u : Fin n := ⟨i, hr⟩
    change permWire π ρ (permWire π.symm ρ.symm u.val) = u.val
    rw [perm_row, perm_row, Equiv.apply_symm_apply]
  · by_cases hc : i < n + m
    · let v : Fin m := ⟨i - n, by omega⟩
      have hv : n + v.val = i := by dsimp [v]; omega
      rw [← hv, perm_col, perm_col, Equiv.apply_symm_apply]
    · have hp : n + m ≤ i := by omega
      rw [perm_upper π.symm ρ.symm hp, perm_upper π ρ hp]

theorem perm_injective {n m : ℕ} (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) :
    Function.Injective (permWire π ρ) := by
  have h : Function.LeftInverse (permWire π.symm ρ.symm) (permWire π ρ) := by
    intro i
    simpa only [Equiv.symm_symm] using perm_inverse π.symm ρ.symm i
  exact h.injective

theorem each_value {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  have hu := u.isLt
  have hv := v.isLt
  apply Bool.eq_iff_iff.2
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs <;> simp [Fin.ext_iff] <;> omega

theorem initial {n m : ℕ} (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m))
    (u : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach u v).getD i false = (oneEach (π u) (ρ v)).getD (permWire π ρ i) false := by
  rw [each_value, each_value, ← perm_row π ρ u, ← perm_col π ρ v]
  simp only [(perm_injective π ρ).eq_iff]

def renameGate (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

def rename (f : ℕ → ℕ) (C : Circuit) : Circuit := ⟨C.gates.map (renameGate f), f C.output⟩

theorem size_eq (f : ℕ → ℕ) (C : Circuit) : (rename f C).size = C.size := by
  simp [rename, Circuit.size]

theorem preserve {P : GateOp → ℕ → Prop} {f : ℕ → ℕ} {C : Circuit}
    (h : ∀ g ∈ C.gates, P g.op g.inputs.length) :
    ∀ g ∈ (rename f C).gates, P g.op g.inputs.length := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
  simpa [renameGate] using h a ha

theorem gateAt_eq {f : ℕ → ℕ} {j : ℕ} {C : Circuit} (hj : j < C.gates.length) :
    gateAt (rename f C) j = renameGate f (gateAt C j) := by
  have hm : j < (rename f C).gates.length := by simpa [rename] using hj
  rw [gateAt, gateAt, List.getD_eq_getElem _ _ hm, List.getD_eq_getElem _ _ hj]
  simp [rename]

theorem reads_eq {f : ℕ → ℕ} {C : Circuit} {i : ℕ} (hinj : Function.Injective f) :
    readsIn (rename f C) (Finset.range (rename f C).size) (f i) =
      readsIn C (Finset.range C.size) i := by
  simp only [readsIn, size_eq]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < C.gates.length := Finset.mem_range.mp hj
  rw [gateAt_eq hj']
  exact List.count_map_of_injective _ _ hinj _

def appendGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem append_read {n m : ℕ} (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m))
    {w z : List Bool} (hw : n + m ≤ w.length) (hlen : z.length = w.length)
    (he : ∀ i, w.getD i false = z.getD (permWire π ρ i) false) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = (z ++ [b]).getD (permWire π ρ i) false := by
  by_cases hi : i < w.length
  · have hj : permWire π ρ i < z.length := by rw [hlen]; exact (perm_lt π ρ hw).mpr hi
    rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hj]
    exact he i
  · rw [perm_upper π ρ (by omega)]
    by_cases hh : i = w.length
    · have hz : i = z.length := by omega
      conv_lhs => rw [hh]
      conv_rhs => rw [hz]
      simp
    · have hw' : (w ++ [b]).length ≤ i := by simp; omega
      have hz' : (z ++ [b]).length ≤ i := by simp; omega
      rw [List.getD_eq_default _ _ hw', List.getD_eq_default _ _ hz']

theorem fold_related {n m : ℕ} (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m))
    (gs : List Gate) {w z : List Bool} (hw : n + m ≤ w.length)
    (hlen : z.length = w.length)
    (he : ∀ i, w.getD i false = z.getD (permWire π ρ i) false) :
    ∀ i, ((gs.map (renameGate (permWire π.symm ρ.symm))).foldl appendGate w).getD i false =
      (gs.foldl appendGate z).getD (permWire π ρ i) false := by
  induction gs generalizing w z with
  | nil => exact he
  | cons g gs ih =>
    have hvalues : (renameGate (permWire π.symm ρ.symm) g).inputs.map
        (fun i => w.getD i false) = g.inputs.map (fun i => z.getD i false) := by
      change (g.inputs.map (permWire π.symm ρ.symm)).map _ = _
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      simpa only [Function.comp_apply, perm_inverse] using he (permWire π.symm ρ.symm i)
    have hrel : ∀ i, (appendGate w (renameGate (permWire π.symm ρ.symm) g)).getD i false =
        (appendGate z g).getD (permWire π ρ i) false := by
      intro i
      unfold appendGate
      rw [hvalues]
      exact append_read π ρ hw hlen he _ _
    simp only [List.map_cons, List.foldl_cons]
    apply ih _ _ hrel
    · simp [appendGate]
      omega
    · simp [appendGate, hlen]

def uses (C : Circuit) (i : ℕ) : Prop :=
  (∃ g ∈ C.gates, i ∈ g.inputs) ∨ C.output = i

theorem uses_lift {f h : ℕ → ℕ} {i : ℕ} {C : Circuit}
    (hinv : Function.LeftInverse h f) (hi : uses (rename f C) i) : uses C (h i) := by
  rcases hi with ⟨g, hg, hi⟩ | he
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    obtain ⟨w, hw, e⟩ := List.mem_map.mp hi
    exact Or.inl ⟨a, ha, by rw [← e, hinv w]; exact hw⟩
  · exact Or.inr (by rw [← he]; exact (hinv C.output).symm)

end PEqualNP.Outside.L_meta_24697_aux

open PEqualNP.Outside.L_meta_24697_aux PEqualNP.CircuitLowerBounds PEqualNP.Represents PEqualNP.MetaComplexity.NestedCover in

theorem PEqualNP.Outside.L_meta_24697 : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.Represents.Represents A C → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, C2.size = C.size ∧ (PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.FanInTwo C2) ∧ (PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.Monotone2 C2) ∧ (((∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C ∧ 0 < C.size ∧ C.output + 1 = (n + m) + C.size ∧ (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) ((n + m) + j) = 0 ↔ j + 1 = C.size)) ∨ (C.size = 0 ∧ C.output < (n + m))) → ((∀ g ∈ C2.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C2 ∧ 0 < C2.size ∧ C2.output + 1 = (n + m) + C2.size ∧ (∀ j < C2.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C2 (Finset.range C2.size) ((n + m) + j) = 0 ↔ j + 1 = C2.size)) ∨ (C2.size = 0 ∧ C2.output < (n + m)))) ∧ PEqualNP.Represents.Represents (fun u v => A (π u) (ρ v)) C2 ∧ (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) → ((∃ g ∈ C.gates, (π u).val ∈ g.inputs) ∨ C.output = (π u).val)) ∧ (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) → ((∃ g ∈ C.gates, (n + (ρ v).val) ∈ g.inputs) ∨ C.output = (n + (ρ v).val))) := by
  intro n m A π ρ C hrep
  let f := permWire π.symm ρ.symm
  let D := rename f C
  have hs : D.size = C.size := size_eq f C
  have hback (h : ReadsBack (n + m) C) : ReadsBack (n + m) D := by
    intro j hj i hi
    have hj' : j < C.gates.length := by simpa [D, rename] using hj
    rw [show D = rename f C from rfl, gateAt_eq hj'] at hi
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hi
    exact (perm_lt π.symm ρ.symm (Nat.le_add_right _ _)).mpr (h j hj' w hw)
  refine ⟨D, hs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact preserve (f := f)
      (P := fun op len => op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ len ≤ 2) h
  · intro h
    exact preserve (f := f)
      (P := fun op len => op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ len ≤ 2) h
  · intro h
    rcases h with ⟨hops, hreads, hp, hl, hcount⟩ | ⟨hz, hout⟩
    · have ho : n + m ≤ C.output := by omega
      have hshape := preserve (f := f)
        (P := fun op len => ((op = GateOp.and ∨ op = GateOp.or) ∧ len = 2) ∨
          (op = GateOp.not ∧ len = 1)) hops
      refine Or.inl ⟨hshape, hback hreads, by simpa [hs] using hp, ?_, ?_⟩
      · change f C.output + 1 = n + m + D.size
        rw [hs, show f C.output = C.output from perm_upper π.symm ρ.symm ho]
        exact hl
      · intro j hj
        have he : f (n + m + j) = n + m + j :=
          perm_upper π.symm ρ.symm (Nat.le_add_right _ _)
        have ht : readsIn (rename f C) (Finset.range (rename f C).size) (f (n + m + j)) =
            readsIn C (Finset.range C.size) (n + m + j) :=
          reads_eq (perm_injective π.symm ρ.symm)
        rw [he] at ht
        change readsIn (rename f C) (Finset.range (rename f C).size) (n + m + j) = 0 ↔ _
        rw [ht, size_eq]
        exact hcount j (by simpa [hs] using hj)
    · refine Or.inr ⟨by simpa [hs] using hz, ?_⟩
      exact (perm_lt π.symm ρ.symm le_rfl).mpr hout
  · intro u v
    change D.eval (oneEach u v) = A (π u) (ρ v)
    rw [← hrep (π u) (ρ v)]
    have hw : n + m ≤ (oneEach u v).length := by simp [oneEach]
    have hl : (oneEach (π u) (ρ v)).length = (oneEach u v).length := by simp [oneEach]
    have h := fold_related π ρ C.gates hw hl (initial π ρ u v) (f C.output)
    change _ = ((C.gates.foldl appendGate (oneEach (π u) (ρ v))).getD
      (permWire π ρ (permWire π.symm ρ.symm C.output)) false) at h
    rw [perm_inverse] at h
    exact h
  · intro u hu
    have h := uses_lift (C := C) (perm_inverse π ρ) hu
    simpa only [uses, perm_row π ρ u] using h
  · intro v hv
    have h := uses_lift (C := C) (perm_inverse π ρ) hv
    simpa only [uses, perm_col π ρ v] using h
