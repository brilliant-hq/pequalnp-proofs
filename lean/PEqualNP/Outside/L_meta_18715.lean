import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18715

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepW x := rfl

theorem foldl_getD_lt (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (gs.foldl stepW w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (stepW w g) (by simp [stepW]; omega)]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepW w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun t =>
        if t < w.length + j then (gs.foldl stepW w).getD t false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      rw [Nat.add_zero, foldl_getD_lt gs (stepW w g) w.length (by simp [stepW])]
      simp only [List.getElem_cons_zero]
      have h0 : (stepW w g).getD w.length false =
          g.op.eval (g.inputs.map fun t => w.getD t false) := by
        simp [stepW, List.getD_eq_getElem?_getD]
      rw [h0]
      congr 1
      apply List.map_congr_left
      intro t _
      by_cases ht : t < w.length
      · rw [ite_eq_left ht, foldl_getD_lt gs (stepW w g) t (by simp [stepW]; omega)]
        simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left ht]
      · rw [ite_eq_right ht, List.getD_eq_default w false (by omega)]
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepW w g) j hj'
      have hl : (stepW w g).length = w.length + 1 := by simp [stepW]
      rw [hl] at key
      simp only [List.getElem_cons_succ]
      rw [show w.length + (j + 1) = w.length + 1 + j by omega]
      exact key

theorem gateAt_eq_getElem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

theorem gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [gateAt_eq_getElem hj]
  exact List.getElem_mem hj

theorem wireValue_input (C : Circuit) (n : ℕ) (x : Fin n → Bool) {w : ℕ} (hw : w < n) :
    PEqualNP.BlindGate.wireValue C n x w = (List.ofFn x).getD w false := by
  unfold PEqualNP.BlindGate.wireValue
  rw [wires_eq_foldl]
  exact foldl_getD_lt C.gates (List.ofFn x) w (by simp [hw])

theorem wireValue_gate {C : Circuit} {n : ℕ} (hRB : ReadsBack n C)
    (x : Fin n → Bool) {j : ℕ} (hj : j < C.gates.length) :
    PEqualNP.BlindGate.wireValue C n x (n + j) =
      (gateAt C j).op.eval ((gateAt C j).inputs.map (PEqualNP.BlindGate.wireValue C n x)) := by
  unfold PEqualNP.BlindGate.wireValue
  rw [wires_eq_foldl]
  have hx : (List.ofFn x).length = n := List.length_ofFn
  have key := foldl_getD_gate C.gates (List.ofFn x) j hj
  rw [hx] at key
  rw [key, gateAt_eq_getElem hj]
  congr 1
  apply List.map_congr_left
  intro t ht
  have hlt : t < n + j := by
    have h1 := hRB j hj t
    rw [gateAt_eq_getElem hj] at h1
    exact h1 ht
  exact ite_eq_left hlt

def shiftW (i w : ℕ) : ℕ := if w < 26 + i then w else w - 1

def unshiftW (i w : ℕ) : ℕ := if w < 26 + i then w else w + 1

def origG (i j : ℕ) : ℕ := if j < i then j else j + 1

theorem unshiftW_shiftW (i w : ℕ) (_hne : w ≠ 26 + i) :
    unshiftW i (shiftW i w) = w := by
  unfold unshiftW shiftW
  split_ifs <;> omega

theorem shiftW_inj (i w1 w2 : ℕ) (_h1 : w1 ≠ 26 + i) (_h2 : w2 ≠ 26 + i)
    (heq : shiftW i w1 = shiftW i w2) : w1 = w2 := by
  unfold shiftW at heq
  split_ifs at heq <;> omega

theorem shiftW_lt (i j w : ℕ) (hw : w < 26 + origG i j) (_hne : w ≠ 26 + i) :
    shiftW i w < 26 + j := by
  unfold shiftW origG at *
  split_ifs at * <;> omega

theorem shiftW_lt_top (i w : ℕ) (hi : i < 64) (hw : w < 26 + 64) (_hne : w ≠ 26 + i) :
    shiftW i w < 26 + 63 := by
  unfold shiftW
  split_ifs <;> omega

theorem unshiftW_gate (i j : ℕ) :
    unshiftW i (26 + j) = 26 + origG i j := by
  unfold unshiftW origG
  split_ifs <;> omega

def trimCircuit (m : ℕ) (C : Circuit) (i : ℕ) : Circuit :=
  ⟨(List.range m).map fun j =>
    let g := gateAt C (origG i j)
    ⟨g.op, g.inputs.map (shiftW i)⟩, 0⟩

theorem trimCircuit_len (m : ℕ) (C : Circuit) (i : ℕ) :
    (trimCircuit m C i).gates.length = m := by
  simp [trimCircuit]

theorem gateAt_trim (m : ℕ) (C : Circuit) (i j : ℕ) (hj : j < m) :
    gateAt (trimCircuit m C i) j =
      ⟨(gateAt C (origG i j)).op, (gateAt C (origG i j)).inputs.map (shiftW i)⟩ := by
  rw [gateAt_eq_getElem (by rw [trimCircuit_len]; exact hj)]
  simp [trimCircuit]

theorem wireValue_trim (m : ℕ) (C : Circuit) (i : ℕ)
    (hRB : ReadsBack 26 C)
    (hRB' : ReadsBack 26 (trimCircuit m C i))
    (horig_lt : ∀ j < m, origG i j < C.gates.length)
    (hnoti : ∀ j < m, 26 + i ∉ (gateAt C (origG i j)).inputs)
    (x : Fin 26 → Bool) (w : ℕ) (hw : w < 26 + m) :
    PEqualNP.BlindGate.wireValue (trimCircuit m C i) 26 x w =
      PEqualNP.BlindGate.wireValue C 26 x (unshiftW i w) := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases h26 : w < 26
    · have hun : unshiftW i w = w := by unfold unshiftW; exact ite_eq_left (by omega)
      rw [hun, wireValue_input (trimCircuit m C i) 26 x h26, wireValue_input C 26 x h26]
    · obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
      have hjm : j < m := by omega
      rw [unshiftW_gate i j]
      rw [wireValue_gate hRB' x (j := j) (by rw [trimCircuit_len]; exact hjm)]
      rw [wireValue_gate hRB x (j := origG i j) (horig_lt j hjm)]
      rw [gateAt_trim m C i j hjm]
      simp only [List.map_map]
      congr 1
      apply List.map_congr_left
      intro t ht
      simp only [Function.comp_apply]
      have ht_lt := hRB (origG i j) (horig_lt j hjm) t ht
      have ht_ne : t ≠ 26 + i := fun h => hnoti j hjm (h ▸ ht)
      have hst_lt : shiftW i t < 26 + j := shiftW_lt i j t ht_lt ht_ne
      rw [ih (shiftW i t) hst_lt (by omega), unshiftW_shiftW i t ht_ne]

theorem main
    (C : Circuit) (a b : ℕ)
    (hsz : C.size = 65)
    (hAO : IsAO2 26 C)
    (hnodup : ∀ g ∈ C.gates, g.inputs.Nodup)
    (hg64 : C.gates[64]? = some ⟨.and, [a, b]⟩)
    (hdead : ∃ i < 64, ∀ j < 65, i < j → 26 + i ∉ (gateAt C j).inputs) :
    ∃ (D : Circuit) (u v : ℕ),
      D.size ≤ 63 ∧ IsAO2 26 D ∧
      (∀ g ∈ D.gates, g.inputs.Nodup) ∧ u ≠ v ∧ u < 26 + D.size ∧ v < 26 + D.size ∧
      ∀ x : Fin 26 → Bool,
        PEqualNP.BlindGate.wireValue D 26 x u = PEqualNP.BlindGate.wireValue C 26 x a ∧
        PEqualNP.BlindGate.wireValue D 26 x v = PEqualNP.BlindGate.wireValue C 26 x b := by
  obtain ⟨i, hi64, hunused⟩ := hdead
  have hlen : C.gates.length = 65 := hsz
  have hga64 : gateAt C 64 = ⟨.and, [a, b]⟩ := by
    simp [gateAt, List.getD_eq_getElem?_getD, hg64]
  have hmem64 : (⟨.and, [a, b]⟩ : Gate) ∈ C.gates := List.mem_iff_getElem?.2 ⟨64, hg64⟩
  have hab_ne : a ≠ b := by
    have hnd := hnodup _ hmem64
    simpa using hnd
  have ha_lt : a < 26 + 64 := by
    have h1 := hAO.2.1 64 (by omega) a
    rw [hga64] at h1
    exact h1 (by simp)
  have hb_lt : b < 26 + 64 := by
    have h1 := hAO.2.1 64 (by omega) b
    rw [hga64] at h1
    exact h1 (by simp)
  have hab_noti : 26 + i ∉ ([a, b] : List ℕ) := by
    have h1 := hunused 64 (by omega) hi64
    rwa [hga64] at h1
  have ha_ne : a ≠ 26 + i := fun h => hab_noti (by simp [h])
  have hb_ne : b ≠ 26 + i := fun h => hab_noti (by simp [h])
  have hnoti_orig : ∀ j < 63, 26 + i ∉ (gateAt C (origG i j)).inputs := by
    intro j hj hmem
    by_cases hji : j < i
    · have hor : origG i j = j := by simp [origG, hji]
      rw [hor] at hmem
      have hlt := hAO.2.1 j (by omega) (26 + i) hmem
      omega
    · have hor : origG i j = j + 1 := by simp [origG, hji]
      rw [hor] at hmem
      exact hunused (j + 1) (by omega) (by omega) hmem
  have horig_lt : ∀ j < 63, origG i j < C.gates.length := by
    intro j hj
    unfold origG
    split_ifs <;> omega
  have hDsz : (trimCircuit 63 C i).size = 63 := trimCircuit_len 63 C i
  have hDAO : IsAO2 26 (trimCircuit 63 C i) := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simp only [trimCircuit, List.mem_map, List.mem_range] at hg
      obtain ⟨j, hj, rfl⟩ := hg
      exact hAO.1 (gateAt C (origG i j)) (gateAt_mem (horig_lt j hj))
    · intro j hj w hw
      rw [trimCircuit_len] at hj
      rw [gateAt_trim 63 C i j hj] at hw
      simp only [List.mem_map] at hw
      obtain ⟨t, ht, rfl⟩ := hw
      have ht_lt := hAO.2.1 (origG i j) (horig_lt j hj) t ht
      have ht_ne : t ≠ 26 + i := fun h => hnoti_orig j hj (h ▸ ht)
      exact shiftW_lt i j t ht_lt ht_ne
    · intro g hg
      simp only [trimCircuit, List.mem_map, List.mem_range] at hg
      obtain ⟨j, hj, rfl⟩ := hg
      simpa using hAO.2.2 (gateAt C (origG i j)) (gateAt_mem (horig_lt j hj))
  have hDnd : ∀ g ∈ (trimCircuit 63 C i).gates, g.inputs.Nodup := by
    intro g hg
    simp only [trimCircuit, List.mem_map, List.mem_range] at hg
    obtain ⟨j, hj, rfl⟩ := hg
    have hnd := hnodup (gateAt C (origG i j)) (gateAt_mem (horig_lt j hj))
    refine List.Nodup.map_on ?_ hnd
    intro x hx y hy hxy
    have hx' : x ≠ 26 + i := fun h => hnoti_orig j hj (h ▸ hx)
    have hy' : y ≠ 26 + i := fun h => hnoti_orig j hj (h ▸ hy)
    exact shiftW_inj i x y hx' hy' hxy
  refine ⟨trimCircuit 63 C i, shiftW i a, shiftW i b, by omega, hDAO, hDnd,
    fun h => hab_ne (shiftW_inj i a b ha_ne hb_ne h),
    by rw [hDsz]; exact shiftW_lt_top i a hi64 ha_lt ha_ne,
    by rw [hDsz]; exact shiftW_lt_top i b hi64 hb_lt hb_ne, ?_⟩
  intro x
  constructor
  · rw [wireValue_trim 63 C i hAO.2.1 hDAO.2.1 horig_lt hnoti_orig x (shiftW i a)
      (shiftW_lt_top i a hi64 ha_lt ha_ne), unshiftW_shiftW i a ha_ne]
  · rw [wireValue_trim 63 C i hAO.2.1 hDAO.2.1 horig_lt hnoti_orig x (shiftW i b)
      (shiftW_lt_top i b hi64 hb_lt hb_ne), unshiftW_shiftW i b hb_ne]

end PEqualNP.Outside.L_meta_18715

theorem PEqualNP.Outside.L_meta_18715 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ), x1.size = (65 : ℕ) → PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ x6 ∈ x1.gates, x6.inputs.Nodup) → x1.gates[(64 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x2, x3] : PEqualNP.CircuitLowerBounds.Gate } → (∃ x8 < (64 : ℕ), ∀ x9 < (65 : ℕ), x8 < x9 → (26 : ℕ) + x8 ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x9).inputs) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : ℕ) (x11 : ℕ), x9.size ≤ (63 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x9 ∧ (∀ x12 ∈ x9.gates, x12.inputs.Nodup) ∧ x10 ≠ x11 ∧ x10 < (26 : ℕ) + x9.size ∧ x11 < (26 : ℕ) + x9.size ∧ ∀ (x12 : Fin (26 : ℕ) → Bool), PEqualNP.BlindGate.wireValue x9 (26 : ℕ) x12 x10 = PEqualNP.BlindGate.wireValue x1 (26 : ℕ) x12 x2 ∧ PEqualNP.BlindGate.wireValue x9 (26 : ℕ) x12 x11 = PEqualNP.BlindGate.wireValue x1 (26 : ℕ) x12 x3 :=
  PEqualNP.Outside.L_meta_18715.main
