import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24697_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

def rwWire (n m : ℕ) (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (i : ℕ) : ℕ :=
  if h1 : i < n then (π.symm ⟨i, h1⟩).val
  else if h2 : i < n + m then n + (ρ.symm ⟨i - n, by omega⟩).val
  else i

def rwGate (n m : ℕ) (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (rwWire n m π ρ)⟩

def rwCircuit (n m : ℕ) (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (C : Circuit) : Circuit :=
  ⟨C.gates.map (rwGate n m π ρ), rwWire n m π ρ C.output⟩

theorem rwWire_lt_nm {n m : ℕ} (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m))
    {i : ℕ} (hi : i < n + m) : rwWire n m π ρ i < n + m := by
  unfold rwWire
  split_ifs with h1
  · have := (π.symm ⟨i, h1⟩).2
    omega
  · have := (ρ.symm ⟨i - n, by omega⟩).2
    omega

theorem rwWire_ge_nm {n m : ℕ} (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m))
    {i : ℕ} (hi : n + m ≤ i) : rwWire n m π ρ i = i := by
  unfold rwWire
  rw [dif_neg (by omega), dif_neg (by omega)]

theorem rwWire_eq_gate {n m : ℕ} (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m))
    {k w : ℕ} (hw : n + m ≤ w) : rwWire n m π ρ k = w ↔ k = w := by
  constructor
  · intro h
    by_cases hk : k < n + m
    · have hlt := rwWire_lt_nm π ρ hk
      omega
    · have hge : rwWire n m π ρ k = k := rwWire_ge_nm π ρ (by omega)
      omega
  · intro h
    subst h
    exact rwWire_ge_nm π ρ hw

theorem rwWire_eq_left {n m : ℕ} (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m))
    {k : ℕ} {u : Fin n} (h : rwWire n m π ρ k = u.val) : k = (π u).val := by
  unfold rwWire at h
  split_ifs at h with h1 h2
  · have he : π.symm ⟨k, h1⟩ = u := Fin.ext h
    have he2 : (⟨k, h1⟩ : Fin n) = π u := (Equiv.symm_apply_eq π).mp he
    exact congrArg Fin.val he2
  · omega
  · have := u.2
    omega

theorem rwWire_eq_right {n m : ℕ} (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m))
    {k : ℕ} {v : Fin m} (h : rwWire n m π ρ k = n + v.val) : k = n + (ρ v).val := by
  unfold rwWire at h
  split_ifs at h with h1 h2
  · have := (π.symm ⟨k, h1⟩).2
    omega
  · have he : ρ.symm ⟨k - n, by omega⟩ = v := Fin.ext (by omega)
    have he2 : (⟨k - n, by omega⟩ : Fin m) = ρ v := (Equiv.symm_apply_eq ρ).mp he
    have hv := congrArg Fin.val he2
    dsimp only at hv
    omega
  · have := v.2
    omega

theorem list_count_map_rw {n m : ℕ} (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m))
    (xs : List ℕ) {w : ℕ} (hw : n + m ≤ w) :
    (xs.map (rwWire n m π ρ)).count w = xs.count w := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.count_cons, ih, beq_iff_eq, rwWire_eq_gate π ρ hw]

theorem gateAt_rwCircuit {n m : ℕ} (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m))
    (C : Circuit) {j : ℕ} (hj : j < C.gates.length) :
    gateAt (rwCircuit n m π ρ C) j = rwGate n m π ρ (gateAt C j) := by
  unfold gateAt rwCircuit
  rw [List.getD_eq_getElem _ _ (by simp [hj]), List.getD_eq_getElem _ _ hj]
  simp

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem oneEach_len {n m : ℕ} (u : Fin n) (v : Fin m) :
    (oneEach u v).length = n + m := by
  simp [oneEach]

theorem oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (k : ℕ) :
    (oneEach u v).getD k false =
      if hk1 : k < n then decide (⟨k, hk1⟩ = u)
      else if hk2 : k < n + m then decide (⟨k - n, by omega⟩ = v)
      else false := by
  unfold oneEach
  by_cases h1 : k < n
  · rw [dif_pos h1, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [h1]),
      List.getElem?_ofFn, dif_pos h1]
    simp [Fin.ext_iff]
  · rw [dif_neg h1]
    by_cases h2 : k < n + m
    · rw [dif_pos h2, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega),
        List.length_ofFn, List.getElem?_ofFn, dif_pos (by omega)]
      simp [Fin.ext_iff]
    · rw [dif_neg h2, List.getD_eq_default _ _ (by simp; omega)]

theorem oneEach_rwWire {n m : ℕ} (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m))
    (u : Fin n) (v : Fin m) (k : ℕ) :
    (oneEach u v).getD (rwWire n m π ρ k) false = (oneEach (π u) (ρ v)).getD k false := by
  rw [oneEach_getD, oneEach_getD]
  unfold rwWire
  by_cases h1 : k < n
  · have hlt1 : (π.symm ⟨k, h1⟩).val < n := (π.symm ⟨k, h1⟩).2
    simp only [h1, ↓reduceDIte, hlt1]
    simp [Fin.ext_iff, Equiv.symm_apply_eq]
  · by_cases h2 : k < n + m
    · have hlt2 : n + (ρ.symm ⟨k - n, by omega⟩).val < n + m := by
        have := (ρ.symm ⟨k - n, by omega⟩).2; omega
      have hge2 : ¬ (n + (ρ.symm ⟨k - n, by omega⟩).val < n) := by omega
      simp only [h1, ↓reduceDIte, h2, hge2, hlt2]
      simp [Fin.ext_iff, Equiv.symm_apply_eq]
    · simp only [h1, ↓reduceDIte, h2]

theorem getD_snoc_rw {n m : ℕ} (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m))
    (wx wy : List Bool) (hl : wx.length = wy.length) (hnm : n + m ≤ wx.length)
    (heq : ∀ k, wy.getD (rwWire n m π ρ k) false = wx.getD k false) (b : Bool) (k : ℕ) :
    (wy ++ [b]).getD (rwWire n m π ρ k) false = (wx ++ [b]).getD k false := by
  by_cases hk : k < wx.length
  · have hkrw : rwWire n m π ρ k < wy.length := by
      by_cases hlt : k < n + m
      · have := rwWire_lt_nm π ρ hlt; omega
      · rw [rwWire_ge_nm π ρ (by omega)]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hkrw,
      List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
    exact heq k
  · have hrw : rwWire n m π ρ k = k := rwWire_ge_nm π ρ (by omega)
    rw [hrw]
    by_cases hke : k = wx.length
    · subst hke
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
        List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
      simp [hl]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem foldl_rw {n m : ℕ} (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (gs : List Gate) :
    ∀ wx wy : List Bool, wx.length = wy.length → n + m ≤ wx.length →
      (∀ k, wy.getD (rwWire n m π ρ k) false = wx.getD k false) →
      ∀ k, ((gs.map (rwGate n m π ρ)).foldl stepW wy).getD (rwWire n m π ρ k) false =
        (gs.foldl stepW wx).getD k false := by
  induction gs with
  | nil => intro wx wy _ _ heq k; exact heq k
  | cons g gs ih =>
    intro wx wy hl hnm heq k
    simp only [List.map_cons, List.foldl_cons]
    have hmap : (rwGate n m π ρ g).op.eval ((rwGate n m π ρ g).inputs.map fun i => wy.getD i false) =
        g.op.eval (g.inputs.map fun i => wx.getD i false) := by
      simp only [rwGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact heq i
    apply ih (stepW wx g) (stepW wy (rwGate n m π ρ g))
    · simp [stepW, hl]
    · simp [stepW]; omega
    · intro j
      unfold stepW
      rw [hmap]
      exact getD_snoc_rw π ρ wx wy hl hnm heq _ j

theorem main (n m : ℕ) (A : Fin n → Fin m → Bool) (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m))
    (C : Circuit) (hR : Represents A C) :
    ∃ C2 : Circuit,
      C2.size = C.size ∧
      (FanInTwo C → FanInTwo C2) ∧
      (Monotone2 C → Monotone2 C2) ∧
      (((∀ g ∈ C.gates, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
          (g.op = GateOp.not ∧ g.inputs.length = 1)) ∧
        ReadsBack (n + m) C ∧ 0 < C.size ∧ C.output + 1 = (n + m) + C.size ∧
        (∀ j < C.size, readsIn C (Finset.range C.size) ((n + m) + j) = 0 ↔ j + 1 = C.size) ∨
        (C.size = 0 ∧ C.output < n + m)) →
       ((∀ g ∈ C2.gates, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
          (g.op = GateOp.not ∧ g.inputs.length = 1)) ∧
        ReadsBack (n + m) C2 ∧ 0 < C2.size ∧ C2.output + 1 = (n + m) + C2.size ∧
        (∀ j < C2.size, readsIn C2 (Finset.range C2.size) ((n + m) + j) = 0 ↔ j + 1 = C2.size) ∨
        (C2.size = 0 ∧ C2.output < n + m))) ∧
      Represents (fun u v => A (π u) (ρ v)) C2 ∧
      (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) →
        ((∃ g ∈ C.gates, (π u).val ∈ g.inputs) ∨ C.output = (π u).val)) ∧
      (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) →
        ((∃ g ∈ C.gates, (n + (ρ v).val) ∈ g.inputs) ∨ C.output = (n + (ρ v).val))) := by
  let C2 := rwCircuit n m π ρ C
  refine ⟨C2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [C2, rwCircuit, Circuit.size]
  · intro hF g' hg'
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
    have h := hF g hg
    simpa [rwGate] using h
  · intro hM g' hg'
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
    have h := hM g hg
    simpa [rwGate] using h
  · intro hred
    rcases hred with ⟨hgC, hrb, hpos, hout, hreads⟩ | ⟨hsz0, hout⟩
    · left
      have hsz : C2.size = C.size := by simp [C2, rwCircuit, Circuit.size]
      have hglen : C2.gates.length = C.gates.length := hsz
      refine ⟨?_, ?_, by omega, ?_, ?_⟩
      · intro g' hg'
        obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
        simpa [rwGate] using hgC g hg
      · intro j hj i hi
        have hj' : j < C.gates.length := by omega
        rw [gateAt_rwCircuit π ρ C hj'] at hi
        simp only [rwGate, List.mem_map] at hi
        obtain ⟨k, hk, rfl⟩ := hi
        have hklt := hrb j hj' k hk
        by_cases hknm : k < n + m
        · have := rwWire_lt_nm π ρ hknm
          omega
        · rw [rwWire_ge_nm π ρ (by omega)]
          exact hklt
      · have hge : n + m ≤ C.output := by simp only [Circuit.size] at hpos hout; omega
        change rwWire n m π ρ C.output + 1 = (n + m) + C2.size
        rw [rwWire_ge_nm π ρ hge, hout, hsz]
      · intro j hj
        have hj' : j < C.size := by omega
        have hrc : readsIn C2 (Finset.range C2.size) ((n + m) + j) =
            readsIn C (Finset.range C.size) ((n + m) + j) := by
          unfold readsIn
          rw [hsz]
          refine Finset.sum_congr rfl fun k hk => ?_
          have hk' : k < C.gates.length := Finset.mem_range.mp hk
          rw [gateAt_rwCircuit π ρ C hk']
          exact list_count_map_rw π ρ (gateAt C k).inputs (by omega)
        rw [hrc, hsz]
        exact hreads j hj'
    · right
      refine ⟨by simpa [C2, rwCircuit, Circuit.size] using hsz0, ?_⟩
      exact rwWire_lt_nm π ρ hout
  · intro u v
    have hev := foldl_rw π ρ C.gates (oneEach (π u) (ρ v)) (oneEach u v)
      (by simp [oneEach_len]) (by simp [oneEach_len]) (oneEach_rwWire π ρ u v) C.output
    change ((C.gates.map (rwGate n m π ρ)).foldl stepW (oneEach u v)).getD (rwWire n m π ρ C.output) false = A (π u) (ρ v)
    rw [hev]
    exact hR (π u) (ρ v)
  · intro u hu
    rcases hu with ⟨g', hg', huin⟩ | hout
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
      simp only [rwGate, List.mem_map] at huin
      obtain ⟨k, hk, hku⟩ := huin
      left
      exact ⟨g, hg, (rwWire_eq_left π ρ hku) ▸ hk⟩
    · right
      exact rwWire_eq_left π ρ hout
  · intro v hv
    rcases hv with ⟨g', hg', hvin⟩ | hout
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
      simp only [rwGate, List.mem_map] at hvin
      obtain ⟨k, hk, hkv⟩ := hvin
      left
      exact ⟨g, hg, (rwWire_eq_right π ρ hkv) ▸ hk⟩
    · right
      exact rwWire_eq_right π ρ hout

end PEqualNP.Outside.L_meta_24697_aux

theorem PEqualNP.Outside.L_meta_24697 : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.Represents.Represents A C → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, C2.size = C.size ∧ (PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.FanInTwo C2) ∧ (PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.Monotone2 C2) ∧ (((∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C ∧ 0 < C.size ∧ C.output + 1 = (n + m) + C.size ∧ (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) ((n + m) + j) = 0 ↔ j + 1 = C.size)) ∨ (C.size = 0 ∧ C.output < (n + m))) → ((∀ g ∈ C2.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C2 ∧ 0 < C2.size ∧ C2.output + 1 = (n + m) + C2.size ∧ (∀ j < C2.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C2 (Finset.range C2.size) ((n + m) + j) = 0 ↔ j + 1 = C2.size)) ∨ (C2.size = 0 ∧ C2.output < (n + m)))) ∧ PEqualNP.Represents.Represents (fun u v => A (π u) (ρ v)) C2 ∧ (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) → ((∃ g ∈ C.gates, (π u).val ∈ g.inputs) ∨ C.output = (π u).val)) ∧ (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) → ((∃ g ∈ C.gates, (n + (ρ v).val) ∈ g.inputs) ∨ C.output = (n + (ρ v).val))) :=
  fun n m A π ρ C hR => PEqualNP.Outside.L_meta_24697_aux.main n m A π ρ C hR
