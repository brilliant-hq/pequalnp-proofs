import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18543

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem prefixRead (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) : (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

private theorem stepLength (w : List Bool) (g : Gate) :
    (step w g).length = w.length+1 := by simp [step]

private theorem gateRead (gs : List Gate) (w : List Bool) (i : ℕ) (g : Gate)
    (hg : gs[i]? = some g) (h : ∀ k ∈ g.inputs, k < w.length+i) :
    let W := gs.foldl step w
    W.getD (w.length+i) false = g.op.eval (g.inputs.map fun k => W.getD k false) := by
  induction gs generalizing w i with
  | nil => simp at hg
  | cons q qs ih =>
    cases i with
    | zero =>
      simp at hg
      subst q
      simp only [List.foldl_cons, Nat.add_zero] at h ⊢
      rw [prefixRead _ _ _ (by rw [stepLength]; omega)]
      have hx : (step w g).getD w.length false =
          g.op.eval (g.inputs.map fun k => w.getD k false) := by simp [step]
      rw [hx]
      congr 1
      apply List.map_congr_left
      intro k hk
      rw [prefixRead _ _ _ (by rw [stepLength]; specialize h k hk; omega)]
      exact (List.getD_append _ _ _ _ (h k hk)).symm
    | succ i =>
      have H : (step w q).length+i = w.length+(i+1) := by rw [stepLength]; omega
      simpa only [H, List.foldl_cons] using
        ih (step w q) i (by simpa using hg) (fun k hk => by simpa [H] using h k hk)
private def wires {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

private theorem wiresLen {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (wires gs x).length = n+gs.length := by
  have len (w : List Bool) (ls : List Gate) : (ls.foldl step w).length = w.length + ls.length := by
    induction ls generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih, stepLength]
      simp
      omega
  simp [wires, len]



private def extra (m o : ℕ) (r : Fin 13 → ℕ) : List Gate := [
  ⟨.or, [0, 1]⟩,
  ⟨.or, [3, 9]⟩,
  ⟨.or, [m, m + 1]⟩,
  ⟨.and, [0, r 0]⟩,
  ⟨.and, [1, r 1]⟩,
  ⟨.and, [3, r 3]⟩,
  ⟨.and, [9, r 9]⟩,
  ⟨.or, [m + 3, m + 4]⟩,
  ⟨.or, [m + 5, m + 6]⟩,
  ⟨.or, [m + 7, m + 8]⟩,
  ⟨.or, [o, m + 2]⟩,
  ⟨.or, [o, m + 9]⟩,
  ⟨.or, [m + 11, 13]⟩,
  ⟨.and, [m + 10, m + 12]⟩]

private theorem lineZero (v : Fin 13) :
    v ∈ PEqualNP.HeptadCover.singerLines3 0 ↔ v = 0 ∨ v = 1 ∨ v = 3 ∨ v = 9 := by
  revert v
  decide +kernel

set_option maxHeartbeats 1500000 in
theorem pack (C : Circuit) (r : Fin 13 → ℕ) (legal : IsAO2 26 C)
    (nodup : ∀ g ∈ C.gates, g.inputs.Nodup) (hout : C.output < 26 + C.size)
    (hr : ∀ p ∈ PEqualNP.HeptadCover.singerLines3 0, r p < 26 + C.size ∧ r p ≠ p.val) :
    ∃ D : Circuit, ∃ i a b : ℕ,
      D.size ≤ C.size + 14 ∧ IsAO2 26 D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
      D.output = 26 + i ∧ D.gates[i]? = some ⟨.and, [a, b]⟩ ∧
      ∀ x : Fin 26 → Bool,
        PEqualNP.BlindGate.wireValue D 26 x a =
          (C.eval (List.ofFn x) || decide (∃ p ∈ PEqualNP.HeptadCover.singerLines3 0,
            x (Fin.castAdd 13 p) = true)) ∧
        PEqualNP.BlindGate.wireValue D 26 x b =
          (C.eval (List.ofFn x) || decide (∃ p ∈ PEqualNP.HeptadCover.singerLines3 0,
            x (Fin.castAdd 13 p) = true ∧ PEqualNP.BlindGate.wireValue C 26 x (r p) = true) || x 13) := by
  let m := 26 + C.size
  let S := extra m C.output r
  let D : Circuit := ⟨C.gates ++ S, m + 13⟩
  have hlen : S.length = 14 := rfl
  have r0 := hr 0 ((lineZero 0).mpr (by simp))
  have r1 := hr 1 ((lineZero 1).mpr (by simp))
  have r3 := hr 3 ((lineZero 3).mpr (by simp))
  have r9 := hr 9 ((lineZero 9).mpr (by simp))
  have spec (k : Fin 14) :
      let g := S.getD k.val ⟨.or, []⟩
      (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ g.inputs.Nodup ∧
        ∀ j ∈ g.inputs, j < m + k.val := by
    have hm : 26 ≤ m := by dsimp [m]; omega
    change C.output < m at hout
    change r 0 < m ∧ r 0 ≠ 0 at r0
    change r 1 < m ∧ r 1 ≠ 1 at r1
    change r 3 < m ∧ r 3 ≠ 3 at r3
    change r 9 < m ∧ r 9 ≠ 9 at r9
    fin_cases k <;> simp [S, extra, Ne.symm r0.2, Ne.symm r1.2, Ne.symm r3.2, Ne.symm r9.2] <;> omega
  have atGate (k : ℕ) (hk : k < 14) :
      D.gates[C.gates.length + k]? = some (S.getD k ⟨.or, []⟩) := by
    have hsk : k < S.length := by omega
    change (C.gates ++ S)[C.gates.length + k]? = _
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, List.getElem?_eq_getElem hsk,
      List.getD_eq_getElem _ _ hsk]
  have dreads : ReadsBack 26 D := by
    intro j hj i hi
    by_cases he : j < C.gates.length
    · apply legal.2.1 j he i
      simpa [gateAt, D, List.getElem?_append_left he] using hi
    · let k := j - C.gates.length
      have eq : C.gates.length + k = j := by dsimp [k]; omega
      have hk : k < 14 := by
        change j < (C.gates ++ S).length at hj
        rw [List.length_append, hlen] at hj
        omega
      have hg := atGate k hk
      rw [eq] at hg
      have hs := (spec ⟨k, hk⟩).2.2.2 i (by simpa [gateAt, hg] using hi)
      change i < m + k at hs
      dsimp [m, Circuit.size] at hs
      omega
  have memData (g : Gate) (hg : g ∈ D.gates) :
      (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ g.inputs.Nodup := by
    rcases List.mem_append.mp hg with h | h
    · exact ⟨legal.1 g h, legal.2.2 g h, nodup g h⟩
    · obtain ⟨k, hk⟩ := List.mem_iff_get.mp h
      have hki : k.val < 14 := by simpa only [hlen] using k.isLt
      have hs := spec ⟨k.val, hki⟩
      have e : S.getD k.val ⟨.or, []⟩ = g := by
        rw [List.getD_eq_getElem _ _ k.isLt]
        exact hk
      have hspec : ((S.getD k.val ⟨.or, []⟩).op = .and ∨
          (S.getD k.val ⟨.or, []⟩).op = .or) ∧
          (S.getD k.val ⟨.or, []⟩).inputs.length = 2 ∧
          (S.getD k.val ⟨.or, []⟩).inputs.Nodup := ⟨hs.1, hs.2.1, hs.2.2.1⟩
      simpa only [e] using hspec
  refine ⟨D, C.size + 13, m + 10, m + 12, ?_, ⟨fun g hg => (memData g hg).1, dreads,
    fun g hg => (memData g hg).2.1⟩, fun g hg => (memData g hg).2.2, by dsimp [D, m]; omega,
    ?_, ?_⟩
  · simp [D, Circuit.size, hlen]
  · exact atGate 13 (by omega)
  · intro x
    let W (i : ℕ) := (wires D.gates x).getD i false
    let W₀ (i : ℕ) := (wires C.gates x).getD i false
    have old (i : ℕ) (hi : i < m) : W i = W₀ i := by
      change ((C.gates ++ S).foldl step (List.ofFn x)).getD i false =
        (C.gates.foldl step (List.ofFn x)).getD i false
      rw [List.foldl_append]
      apply prefixRead
      change i < (wires C.gates x).length
      rw [wiresLen]
      exact hi
    have primary (i : Fin 26) : W i = x i := by
      change (D.gates.foldl step (List.ofFn x)).getD i.val false = x i
      rw [prefixRead _ _ _ (by simpa only [List.length_ofFn] using i.isLt),
        List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt)]
      simp only [List.getElem_ofFn, Fin.eta]
    have evalGate (k : ℕ) (hk : k < 14) :
        W (m + k) = (S.getD k ⟨.or, []⟩).op.eval ((S.getD k ⟨.or, []⟩).inputs.map W) := by
      let j := C.gates.length + k
      have gj := atGate k hk
      have q := (spec ⟨k, hk⟩).2.2.2
      have z := gateRead D.gates (List.ofFn x) j _ gj
      have read : ∀ i ∈ (S.getD k ⟨.or, []⟩).inputs, i < (List.ofFn x).length + j := by
        intro i hi
        simpa only [List.length_ofFn, j, m, Circuit.size, ← Nat.add_assoc] using q i hi
      have v := z read
      change W ((List.ofFn x).length + j) =
        (S.getD k ⟨.or, []⟩).op.eval ((S.getD k ⟨.or, []⟩).inputs.map W) at v
      simpa only [List.length_ofFn, j, m, Circuit.size, ← Nat.add_assoc] using v
    have v0 : W (m + 0) = (W (0) || W (1)) := by
      simpa [S, extra, GateOp.eval] using evalGate 0 (by omega)
    have v1 : W (m + 1) = (W (3) || W (9)) := by
      simpa [S, extra, GateOp.eval] using evalGate 1 (by omega)
    have v2 : W (m + 2) = (W (m) || W (m + 1)) := by
      simpa [S, extra, GateOp.eval] using evalGate 2 (by omega)
    have v3 : W (m + 3) = (W (0) && W (r 0)) := by
      simpa [S, extra, GateOp.eval] using evalGate 3 (by omega)
    have v4 : W (m + 4) = (W (1) && W (r 1)) := by
      simpa [S, extra, GateOp.eval] using evalGate 4 (by omega)
    have v5 : W (m + 5) = (W (3) && W (r 3)) := by
      simpa [S, extra, GateOp.eval] using evalGate 5 (by omega)
    have v6 : W (m + 6) = (W (9) && W (r 9)) := by
      simpa [S, extra, GateOp.eval] using evalGate 6 (by omega)
    have v7 : W (m + 7) = (W (m + 3) || W (m + 4)) := by
      simpa [S, extra, GateOp.eval] using evalGate 7 (by omega)
    have v8 : W (m + 8) = (W (m + 5) || W (m + 6)) := by
      simpa [S, extra, GateOp.eval] using evalGate 8 (by omega)
    have v9 : W (m + 9) = (W (m + 7) || W (m + 8)) := by
      simpa [S, extra, GateOp.eval] using evalGate 9 (by omega)
    have v10 : W (m + 10) = (W (C.output) || W (m + 2)) := by
      simpa [S, extra, GateOp.eval] using evalGate 10 (by omega)
    have v11 : W (m + 11) = (W (C.output) || W (m + 9)) := by
      simpa [S, extra, GateOp.eval] using evalGate 11 (by omega)
    have v12 : W (m + 12) = (W (m + 11) || W (13)) := by
      simpa [S, extra, GateOp.eval] using evalGate 12 (by omega)

    have p0 : W 0 = x 0 := primary 0
    have p1 : W 1 = x 1 := primary 1
    have p3 : W 3 = x 3 := primary 3
    have p9 : W 9 = x 9 := primary 9
    have p13 : W 13 = x 13 := primary 13
    have expand (P : Fin 13 → Prop) :
        (∃ p ∈ PEqualNP.HeptadCover.singerLines3 0, P p) ↔ P 0 ∨ P 1 ∨ P 3 ∨ P 9 := by
      constructor
      · rintro ⟨p, hp, hP⟩
        rcases (lineZero p).mp hp with rfl | rfl | rfl | rfl <;> tauto
      · rintro (h | h | h | h)
        · exact ⟨0, (lineZero 0).mpr (by simp), h⟩
        · exact ⟨1, (lineZero 1).mpr (by simp), h⟩
        · exact ⟨3, (lineZero 3).mpr (by simp), h⟩
        · exact ⟨9, (lineZero 9).mpr (by simp), h⟩
    have one : decide (∃ p ∈ PEqualNP.HeptadCover.singerLines3 0,
        x (Fin.castAdd 13 p) = true) = (x 0 || x 1 || x 3 || x 9) := by
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, Bool.or_eq_true]
      rw [expand]
      change (x 0 = true ∨ x 1 = true ∨ x 3 = true ∨ x 9 = true) ↔ _
      tauto
    have two : decide (∃ p ∈ PEqualNP.HeptadCover.singerLines3 0,
        x (Fin.castAdd 13 p) = true ∧ PEqualNP.BlindGate.wireValue C 26 x (r p) = true) =
        ((x 0 && W₀ (r 0)) || (x 1 && W₀ (r 1)) || (x 3 && W₀ (r 3)) || (x 9 && W₀ (r 9))) := by
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.and_eq_true]
      rw [expand]
      change ((x 0 = true ∧ W₀ (r 0) = true) ∨ (x 1 = true ∧ W₀ (r 1) = true) ∨
        (x 3 = true ∧ W₀ (r 3) = true) ∨ (x 9 = true ∧ W₀ (r 9) = true)) ↔ _
      tauto
    change W (m + 10) = (W₀ C.output || _) ∧ W (m + 12) = (W₀ C.output || _ || x 13)
    constructor
    · rw [v10, v2, show W m = W (m + 0) from rfl, v0, v1, p0, p1, p3, p9, old _ hout, one]
      ac_rfl
    · rw [v12, v11, v9, v7, v8, v3, v4, v5, v6, p0, p1, p3, p9, p13,
        old _ hout, old _ r0.1, old _ r1.1, old _ r3.1, old _ r9.1, two]
      ac_rfl

end PEqualNP.Outside.L_meta_18543

theorem PEqualNP.Outside.L_meta_18543 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (13 : ℕ) → ℕ),   PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →     (∀ x4 ∈ x1.gates, x4.inputs.Nodup) →       x1.output < (26 : ℕ) + x1.size →         (∀ x6 ∈ PEqualNP.HeptadCover.singerLines3 (0 : Fin (13 : ℕ)), x2 x6 < (26 : ℕ) + x1.size ∧ x2 x6 ≠ ↑x6) →           ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : ℕ) (x9 : ℕ) (x10 : ℕ),             x7.size ≤ x1.size + (14 : ℕ) ∧               PEqualNP.TopForm.IsAO2 (26 : ℕ) x7 ∧                 (∀ x11 ∈ x7.gates, x11.inputs.Nodup) ∧                   x7.output = (26 : ℕ) + x8 ∧                     x7.gates[x8]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x9, x10] : PEqualNP.CircuitLowerBounds.Gate } ∧                       ∀ (x11 : Fin (26 : ℕ) → Bool),                         have x12 : Bool := Decidable.decide (∃ x12 ∈ PEqualNP.HeptadCover.singerLines3 (0 : Fin (13 : ℕ)), x11 (Fin.castAdd (13 : ℕ) x12) = Bool.true);                         have x13 : Bool := Decidable.decide (∃ x13 ∈ PEqualNP.HeptadCover.singerLines3 (0 : Fin (13 : ℕ)), x11 (Fin.castAdd (13 : ℕ) x13) = Bool.true ∧ PEqualNP.BlindGate.wireValue x1 (26 : ℕ) x11 (x2 x13) = Bool.true);                         have x14 : Bool := x1.eval (List.ofFn x11);                         PEqualNP.BlindGate.wireValue x7 (26 : ℕ) x11 x9 = (x14 || x12) ∧ PEqualNP.BlindGate.wireValue x7 (26 : ℕ) x11 x10 = (x14 || x13 || x11 (13 : Fin (26 : ℕ))) := PEqualNP.Outside.L_meta_18543.pack
