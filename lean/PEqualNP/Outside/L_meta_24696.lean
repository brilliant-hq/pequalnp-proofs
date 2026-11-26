import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24696_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

private def lower (d i : ℕ) : ℕ := if i < d then i else i - 1

private def liftWire (d i : ℕ) : ℕ := if i < d then i else i + 1

private theorem lift_lower {d i : ℕ} (hi : i ≠ d) : liftWire d (lower d i) = i := by
  unfold liftWire lower
  split <;> (try split) <;> omega

private theorem lift_inj {d x y : ℕ} : liftWire d x = liftWire d y ↔ x = y := by
  unfold liftWire
  split <;> (try split) <;> omega

private theorem lift_col {m : ℕ} (n : ℕ) (k : Fin (m+1)) (v : Fin m) :
    liftWire (n+k.val) (n+v.val) = n+(k.succAbove v).val := by
  by_cases h : v.castSucc < k
  · rw [Fin.succAbove_of_castSucc_lt _ _ h]
    have hv : v.val < k.val := h
    simp [liftWire, Fin.val_castSucc, hv]
  · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt h)]
    have hv : ¬v.val < k.val := h
    simp [liftWire, hv, Nat.add_assoc]

private def renGate (d : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (lower d)⟩

private def ren (d : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (renGate d), lower d C.output⟩

private theorem oneAt {n m : ℕ} (u : Fin n) (v : Fin m) (j : ℕ) :
    (oneEach u v).getD j false = decide (j = u.val ∨ j = n+v.val) := by
  by_cases hj : j < n
  · rw [oneEach, List.getD_append _ _ _ _ (by simpa using hj),
      List.getD_eq_getElem _ _ (by simpa using hj)]
    simp [Fin.ext_iff, show j ≠ n+v.val by omega]
  · by_cases h2 : j < n+m
    · rw [oneEach, List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_ofFn]
      rw [List.getD_eq_getElem _ _ (by simp; omega)]
      have hu := u.isLt
      simp [Fin.ext_iff, show j ≠ u.val by omega, show (j-n = v.val) ↔ j = n+v.val by omega]
    · rw [List.getD_eq_default _ _ (by simp [oneEach]; omega)]
      have hu := u.isLt
      have hv := v.isLt
      simp [show j ≠ u.val by omega, show j ≠ n+v.val by omega]

private def EvalAgrees (d : ℕ) (small big : List Bool) : Prop :=
  big.length = small.length+1 ∧ d ≤ small.length ∧
    ∀ i, (small.getD i false) = big.getD (liftWire d i) false

private theorem start_agrees {n m : ℕ} (u : Fin n) (k : Fin (m+1)) (v : Fin m) :
    EvalAgrees (n+k.val) (oneEach u v) (oneEach u (k.succAbove v)) := by
  refine ⟨by simp [oneEach, Nat.add_assoc], by simp [oneEach]; omega, ?_⟩
  intro j
  rw [oneAt, oneAt, ← lift_col]
  have hu : liftWire (n+k.val) u.val = u.val := by
    have := u.isLt
    simp [liftWire, show u.val < n+k.val by omega]
  congr 1
  rw [← hu, lift_inj, lift_inj, hu]

private theorem append_agrees {d : ℕ} {small big : List Bool} (h : EvalAgrees d small big)
    (b : Bool) : EvalAgrees d (small ++ [b]) (big ++ [b]) := by
  obtain ⟨hl,hd,ha⟩ := h
  refine ⟨by simp; omega, by simp; omega, ?_⟩
  intro i
  by_cases hi : i < small.length
  · have h' : liftWire d i < big.length := by unfold liftWire; split <;> omega
    rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ h']
    exact ha i
  · have h' : big.length ≤ liftWire d i := by unfold liftWire; split <;> omega
    rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ h']
    congr 1
    unfold liftWire
    split <;> omega

private def runGates (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun s g => s ++ [g.op.eval (g.inputs.map fun i => s.getD i false)]) w

private theorem run_agrees (d : ℕ) (gs : List Gate) (small big : List Bool)
    (avoid : ∀ g ∈ gs, d ∉ g.inputs) (h : EvalAgrees d small big) :
    EvalAgrees d (runGates (gs.map (renGate d)) small) (runGates gs big) := by
  induction gs generalizing small big with
  | nil => exact h
  | cons g gs ih =>
    have hargs : (g.inputs.map (lower d)).map (fun i => small.getD i false) =
        g.inputs.map (fun i => big.getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro w hw
      change small.getD (lower d w) false = big.getD w false
      have hn : w ≠ d := fun eq => avoid g List.mem_cons_self (by simpa [← eq] using hw)
      rw [h.2.2, lift_lower hn]
    simp only [List.map_cons, runGates, List.foldl_cons, renGate] at ⊢
    rw [hargs]
    exact ih _ _ (fun g hg => avoid g (List.mem_cons_of_mem _ hg)) (append_agrees h _)

private theorem ren_rep {n m : ℕ} (A : Fin n → Fin (m+1) → Bool) (k : Fin (m+1))
    (C : Circuit) (rep : Represents A C) (hg : ∀ g ∈ C.gates, n+k.val ∉ g.inputs)
    (ho : C.output ≠ n+k.val) :
    Represents (fun u v => A u (k.succAbove v)) (ren (n+k.val) C) := by
  intro u v
  change _ = A u (k.succAbove v)
  rw [← rep u (k.succAbove v)]
  have h := run_agrees (n+k.val) C.gates _ _ hg (start_agrees u k v)
  exact (h.2.2 (lower (n+k.val) C.output)).trans (by rw [lift_lower ho]; rfl)


private theorem gate_eq (d : ℕ) (C : Circuit) (j : ℕ) :
    gateAt (ren d C) j = renGate d (gateAt C j) := by
  exact List.getD_map C.gates ⟨.or, []⟩ (renGate d)

private theorem ren_fan (d : ℕ) (C : Circuit) (hf : FanInTwo C) : FanInTwo (ren d C) := by
  intro g hg
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
  simpa [renGate] using hf a ha

private theorem ren_back (d t : ℕ) (hd : d ≤ t) (C : Circuit)
    (hb : ReadsBack (t+1) C) (unused : ∀ g ∈ C.gates, d ∉ g.inputs) :
    ReadsBack t (ren d C) := by
  intro j hj i hi
  have hlen : j < C.gates.length := by simpa [ren] using hj
  rw [gate_eq] at hi
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hi
  have hwlt := hb j hlen w hw
  have hm : gateAt C j ∈ C.gates := by
    rw [gateAt, List.getD_eq_getElem _ _ hlen]
    exact List.getElem_mem _
  have hne : w ≠ d := fun e => unused _ hm (by simpa [← e] using hw)
  unfold lower
  split <;> omega

private theorem count_shift (d w : ℕ) (l : List ℕ) (hu : d ∉ l) :
    (l.map (lower d)).count w = l.count (liftWire d w) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha : a ≠ d := by intro e; subst a; exact hu List.mem_cons_self
    have hl : d ∉ l := fun h => hu (List.mem_cons_of_mem _ h)
    have he : lower d a = w ↔ a = liftWire d w := by
      rw [← lift_inj (d := d), lift_lower ha]
    simp [List.count_cons, ih hl, he]

private theorem ren_reads (d : ℕ) (C : Circuit) (hu : ∀ g ∈ C.gates, d ∉ g.inputs)
    (w : ℕ) : readsIn (ren d C) (Finset.range C.size) w =
        readsIn C (Finset.range C.size) (liftWire d w) := by
  unfold readsIn
  apply Finset.sum_congr rfl
  intro j hj
  rw [gate_eq]
  apply count_shift
  apply hu
  rw [gateAt, List.getD_eq_getElem _ _ (Finset.mem_range.mp hj : j < C.gates.length)]
  exact List.getElem_mem _

private theorem ren_used (d : ℕ) (C : Circuit) (hu : ∀ g ∈ C.gates, d ∉ g.inputs)
    (ho : C.output ≠ d) (i : ℕ) :
    ((∃ g ∈ (ren d C).gates, i ∈ g.inputs) ∨ (ren d C).output = i) →
      ((∃ g ∈ C.gates, liftWire d i ∈ g.inputs) ∨ C.output = liftWire d i) := by
  rintro (⟨g,hg,hi⟩ | h)
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hi
    have hn : w ≠ d := fun e => hu a ha (by simpa [← e] using hw)
    exact Or.inl ⟨a,ha,by rwa [lift_lower hn]⟩
  · change lower d C.output = i at h
    exact Or.inr (by rw [← h, lift_lower ho])

end PEqualNP.Outside.L_meta_24696_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open PEqualNP.Outside.L_meta_24696_aux


theorem PEqualNP.Outside.L_meta_24696 : (∀ (n m : ℕ) (A : Fin n → Fin (m + 1) → Bool) (k : Fin (m + 1)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → ((∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + (m + 1)) C ∧ 0 < C.size ∧ C.output + 1 = (n + (m + 1)) + C.size ∧ (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) ((n + (m + 1)) + j) = 0 ↔ j + 1 = C.size)) ∨ (C.size = 0 ∧ C.output < (n + (m + 1)))) → (∀ g ∈ C.gates, n + k.val ∉ g.inputs) → C.output ≠ n + k.val → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin m) => A u (k.succAbove v)) C2 ∧ ((∀ g ∈ C2.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C2 ∧ 0 < C2.size ∧ C2.output + 1 = (n + m) + C2.size ∧ (∀ j < C2.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C2 (Finset.range C2.size) ((n + m) + j) = 0 ↔ j + 1 = C2.size)) ∨ (C2.size = 0 ∧ C2.output < (n + m))) ∧ C2.size = C.size ∧ (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) → ((∃ g ∈ C.gates, u.val ∈ g.inputs) ∨ C.output = u.val)) ∧ (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) → ((∃ g ∈ C.gates, (n + (k.succAbove v).val) ∈ g.inputs) ∨ C.output = (n + (k.succAbove v).val)))) := by
  intro n m A k C hf rep hshape hu ho
  let d := n + k.val
  have hd : d ≤ n+m := by dsimp [d]; omega
  have sz : (ren d C).size = C.size := by simp [ren, Circuit.size]
  refine ⟨ren d C, ren_fan d C hf, ren_rep A k C rep hu ho, ?_, sz, ?_, ?_⟩
  · rcases hshape with ⟨forms,back,pos,last,reads⟩ | ⟨hz,ho'⟩
    · left
      refine ⟨?_, ?_, sz.symm ▸ pos, ?_, ?_⟩
      · intro g hg
        obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
        simpa [renGate] using forms a ha
      · apply ren_back d (n+m) hd C _ hu
        simpa [Nat.add_assoc] using back
      · rw [sz]
        change lower d C.output + 1 = _
        unfold lower
        split <;> omega
      · intro j hj
        rw [sz] at hj ⊢
        rw [ren_reads d C hu]
        have e : liftWire d (n+m+j) = n+(m+1)+j := by
          unfold liftWire
          split <;> omega
        rw [e]
        exact reads j hj
    · right
      refine ⟨sz.trans hz, ?_⟩
      change lower d C.output < n+m
      unfold lower
      split <;> omega
  · intro u h
    have hr := ren_used d C hu ho u.val h
    have e : liftWire d u.val = u.val := by
      have := u.isLt
      simp [liftWire, d, show u.val < n+k.val by omega]
    rwa [e] at hr
  · intro v h
    have hr := ren_used d C hu ho (n+v.val) h
    simpa [d, lift_col] using hr
