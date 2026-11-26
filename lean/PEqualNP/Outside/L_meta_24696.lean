import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24696_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Represents PEqualNP.MetaComplexity.NestedCover

def liftWire (d i : ℕ) : ℕ := if i < d then i else i + 1

def lowerWire (d i : ℕ) : ℕ := if i < d then i else i - 1

theorem lift_lower {d i : ℕ} (hi : i ≠ d) : liftWire d (lowerWire d i) = i := by
  unfold liftWire lowerWire
  split_ifs <;> omega

theorem lift_injective (d : ℕ) : Function.Injective (liftWire d) := by
  intro i j h
  unfold liftWire at h
  split_ifs at h <;> omega

theorem lift_lt {d w i : ℕ} (h : d ≤ w) : liftWire d i < w + 1 ↔ i < w := by
  unfold liftWire
  split_ifs <;> omega

theorem lower_lt {d w i : ℕ} (h : d ≤ w) (hi : i ≠ d) :
    lowerWire d i < w ↔ i < w + 1 := by
  rw [← lift_lt h, lift_lower hi]

theorem lift_column {n m : ℕ} (k : Fin (m + 1)) (j : Fin m) :
    liftWire (n + k.val) (n + j.val) = n + (k.succAbove j).val := by
  unfold liftWire
  by_cases h : j.val < k.val
  · rw [Fin.succAbove_of_castSucc_lt k j h, ite_eq_left (by omega)]
    rfl
  · rw [Fin.succAbove_of_le_castSucc k j (show k.val ≤ j.val by omega), ite_eq_right (by omega)]
    simp [Nat.add_assoc]

theorem each_value {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  have hu := u.isLt
  have hv := v.isLt
  apply Bool.eq_iff_iff.2
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs <;> simp [Fin.ext_iff] <;> omega

theorem initial {n m : ℕ} (k : Fin (m + 1)) (u : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach u v).getD i false =
      (oneEach u (k.succAbove v)).getD (liftWire (n + k.val) i) false := by
  have hu : liftWire (n + k.val) u.val = u.val := by
    have h := u.isLt
    simp [liftWire, show u.val < n + k.val by omega]
  rw [each_value, each_value]
  conv_rhs => rw [← hu, ← lift_column k v]
  simp only [(lift_injective _).eq_iff]

def renameGate (d : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (lowerWire d)⟩

def withoutColumn (d : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (renameGate d), lowerWire d C.output⟩

theorem size_eq (d : ℕ) (C : Circuit) : (withoutColumn d C).size = C.size := by
  simp [withoutColumn, Circuit.size]

theorem gateAt_eq {d j : ℕ} {C : Circuit} (hj : j < C.gates.length) :
    gateAt (withoutColumn d C) j = renameGate d (gateAt C j) := by
  have hm : j < (withoutColumn d C).gates.length := by simpa [withoutColumn] using hj
  rw [gateAt, gateAt, List.getD_eq_getElem _ _ hm, List.getD_eq_getElem _ _ hj]
  simp [withoutColumn]

theorem reads_eq {d n j : ℕ} {C : Circuit}
    (h : d ≤ n) (hskip : ∀ g ∈ C.gates, d ∉ g.inputs) :
    readsIn (withoutColumn d C) (Finset.range (withoutColumn d C).size) (n + j) =
      readsIn C (Finset.range C.size) (n + 1 + j) := by
  simp only [readsIn, size_eq]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < C.gates.length := Finset.mem_range.mp hi
  rw [gateAt_eq hi']
  have hm : gateAt C i ∈ C.gates := by
    rw [gateAt, List.getD_eq_getElem _ _ hi']
    exact List.getElem_mem hi'
  have hmap : ((renameGate d (gateAt C i)).inputs.map (liftWire d)) = (gateAt C i).inputs := by
    change ((gateAt C i).inputs.map (lowerWire d)).map (liftWire d) = _
    rw [List.map_map]
    calc
      _ = (gateAt C i).inputs.map id := by
        apply List.map_congr_left
        intro w hw
        exact lift_lower (fun he => hskip _ hm (he ▸ hw))
      _ = _ := List.map_id _
  have he : liftWire d (n + j) = n + 1 + j := by
    simp [liftWire, show ¬ n + j < d by omega]
    omega
  rw [← he, ← hmap]
  exact (List.count_map_of_injective _ _ (lift_injective d) _).symm

def appendGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem append_read {d : ℕ} {w z : List Bool} (hd : d ≤ w.length)
    (hlen : z.length = w.length + 1)
    (he : ∀ i, w.getD i false = z.getD (liftWire d i) false)
    (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = (z ++ [b]).getD (liftWire d i) false := by
  by_cases hi : i < w.length
  · have hj : liftWire d i < z.length := by rw [hlen]; exact (lift_lt hd).mpr hi
    rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hj]
    exact he i
  · have heq : liftWire d i = i + 1 := by simp [liftWire, show ¬ i < d by omega]
    rw [heq]
    by_cases hh : i = w.length
    · have hh' : i + 1 = z.length := by omega
      rw [hh', hh]
      simp
    · have hw : (w ++ [b]).length ≤ i := by simp; omega
      have hz : (z ++ [b]).length ≤ i + 1 := by simp; omega
      rw [List.getD_eq_default _ _ hw, List.getD_eq_default _ _ hz]

theorem fold_related (d : ℕ) (gs : List Gate)
    (hskip : ∀ g ∈ gs, d ∉ g.inputs) {w z : List Bool}
    (hd : d ≤ w.length) (hlen : z.length = w.length + 1)
    (he : ∀ i, w.getD i false = z.getD (liftWire d i) false) :
    ∀ i, ((gs.map (renameGate d)).foldl appendGate w).getD i false =
      (gs.foldl appendGate z).getD (liftWire d i) false := by
  induction gs generalizing w z with
  | nil => exact he
  | cons g gs ih =>
    have hvalues : (renameGate d g).inputs.map (fun i => w.getD i false) =
        g.inputs.map (fun i => z.getD i false) := by
      change (g.inputs.map (lowerWire d)).map _ = _
      rw [List.map_map]
      apply List.map_congr_left
      intro i hi
      have hn : i ≠ d := fun e => hskip g (by simp) (e ▸ hi)
      simpa only [Function.comp_apply, lift_lower hn] using he (lowerWire d i)
    have hrel : ∀ i, (appendGate w (renameGate d g)).getD i false =
        (appendGate z g).getD (liftWire d i) false := by
      intro i
      unfold appendGate
      rw [hvalues]
      exact append_read hd hlen he _ _
    simp only [List.map_cons, List.foldl_cons]
    apply ih (fun a ha => hskip a (List.mem_cons_of_mem _ ha)) _ _ hrel
    · simp [appendGate]
      omega
    · simp [appendGate, hlen, Nat.add_assoc]

def uses (C : Circuit) (i : ℕ) : Prop :=
  (∃ g ∈ C.gates, i ∈ g.inputs) ∨ C.output = i

theorem uses_lift {d i : ℕ} {C : Circuit}
    (hskip : ∀ g ∈ C.gates, d ∉ g.inputs) (hout : C.output ≠ d)
    (hi : uses (withoutColumn d C) i) : uses C (liftWire d i) := by
  rcases hi with ⟨g, hg, hi⟩ | he
  · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
    obtain ⟨w, hw, e⟩ := List.mem_map.mp hi
    have hn : w ≠ d := fun e => hskip f hf (e ▸ hw)
    exact Or.inl ⟨f, hf, by rw [← e, lift_lower hn]; exact hw⟩
  · exact Or.inr (by rw [← he]; exact (lift_lower hout).symm)

end PEqualNP.Outside.L_meta_24696_aux

open PEqualNP.Outside.L_meta_24696_aux PEqualNP.CircuitLowerBounds PEqualNP.Represents PEqualNP.MetaComplexity.NestedCover in

theorem PEqualNP.Outside.L_meta_24696 : ∀ (n m : ℕ) (A : Fin n → Fin (m + 1) → Bool) (k : Fin (m + 1)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → ((∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + (m + 1)) C ∧ 0 < C.size ∧ C.output + 1 = (n + (m + 1)) + C.size ∧ (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) ((n + (m + 1)) + j) = 0 ↔ j + 1 = C.size)) ∨ (C.size = 0 ∧ C.output < (n + (m + 1)))) → (∀ g ∈ C.gates, n + k.val ∉ g.inputs) → C.output ≠ n + k.val → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin m) => A u (k.succAbove v)) C2 ∧ ((∀ g ∈ C2.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C2 ∧ 0 < C2.size ∧ C2.output + 1 = (n + m) + C2.size ∧ (∀ j < C2.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C2 (Finset.range C2.size) ((n + m) + j) = 0 ↔ j + 1 = C2.size)) ∨ (C2.size = 0 ∧ C2.output < (n + m))) ∧ C2.size = C.size ∧ (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) → ((∃ g ∈ C.gates, u.val ∈ g.inputs) ∨ C.output = u.val)) ∧ (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) → ((∃ g ∈ C.gates, (n + (k.succAbove v).val) ∈ g.inputs) ∨ C.output = (n + (k.succAbove v).val))) := by
  intro n m A k C hfan hrep hred hskip hout
  let d := n + k.val
  have hd : d ≤ n + m := by have hk := k.isLt; dsimp [d]; omega
  have hh (g : Gate) :
      (renameGate d g).op = g.op ∧ (renameGate d g).inputs.length = g.inputs.length := by
    simp [renameGate]
  refine ⟨withoutColumn d C, ?_, ?_, ?_, size_eq d C, ?_, ?_⟩
  · intro g hg
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
    have e := hh f
    rw [e.1, e.2]
    exact hfan f hf
  · intro u v
    change (withoutColumn d C).eval (oneEach u v) = A u (k.succAbove v)
    rw [← hrep u (k.succAbove v)]
    have hlength : (oneEach u (k.succAbove v)).length = (oneEach u v).length + 1 := by
      simp [oneEach, Nat.add_assoc]
    have hsize : d ≤ (oneEach u v).length := by simpa [oneEach] using hd
    have h :=
      fold_related d C.gates hskip hsize hlength (initial k u v) (lowerWire d C.output)
    rw [lift_lower hout] at h
    exact h
  · rcases hred with ⟨hops, hback, hpos, hlast, hread⟩ | ⟨hzero, hb⟩
    · refine Or.inl ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro g hg
        obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
        have e := hh f
        rw [e.1, e.2]
        exact hops f hf
      · intro j hj i hi
        have hj' : j < C.gates.length := by simpa [withoutColumn] using hj
        rw [gateAt_eq hj'] at hi
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hi
        have hmem : gateAt C j ∈ C.gates := by
          rw [gateAt, List.getD_eq_getElem _ _ hj']
          exact List.getElem_mem hj'
        have hne : w ≠ d := by
          intro e
          apply hskip _ hmem
          change d ∈ (gateAt C j).inputs
          simpa only [e] using hw
        have hold := hback j hj' w hw
        apply (lower_lt (show d ≤ n + m + j by omega) hne).mpr
        omega
      · simpa [size_eq] using hpos
      · rw [size_eq]
        have hc : ¬ C.output < d := by omega
        change lowerWire d C.output + 1 = _
        simp only [lowerWire, ite_eq_right hc]
        omega
      · intro j hj
        rw [reads_eq hd hskip, size_eq]
        simpa only [Nat.add_assoc] using hread j (by simpa [size_eq] using hj)
    · refine Or.inr ⟨by simpa [size_eq] using hzero, ?_⟩
      change lowerWire d C.output < n + m
      apply (lower_lt hd hout).mpr
      omega
  · intro u hu
    have h := uses_lift hskip hout hu
    simpa [uses, d, liftWire, show u.val < n + k.val by have := u.isLt; omega] using h
  · intro v hv
    have h := uses_lift hskip hout hv
    simpa only [uses, d, lift_column k v] using h
