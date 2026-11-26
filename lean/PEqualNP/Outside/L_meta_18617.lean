import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18617

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

private def C : Circuit := ⟨[
  ⟨.or, [13, 18]⟩,
  ⟨.or, [27, 24]⟩,
  ⟨.and, [1, 28]⟩,
  ⟨.or, [15, 19]⟩,
  ⟨.or, [30, 25]⟩,
  ⟨.and, [2, 31]⟩,
  ⟨.or, [16, 17]⟩,
  ⟨.or, [33, 21]⟩,
  ⟨.and, [4, 34]⟩,
  ⟨.or, [20, 22]⟩,
  ⟨.or, [36, 23]⟩,
  ⟨.and, [10, 37]⟩,
  ⟨.or, [29, 32]⟩,
  ⟨.or, [35, 38]⟩,
  ⟨.or, [39, 40]⟩], 41⟩

private def edge (i j : Fin 13) : Prop :=
  i ∈ ([1, 2, 4, 10] : List (Fin 13)) ∧ j ≠ 1 ∧
    (i = j ∨ i = j + 1 ∨ i = j + 3 ∨ i = j + 9)

private instance (i j : Fin 13) : Decidable (edge i j) := by
  unfold edge
  infer_instance

private theorem table : ∀ i j : Fin 13, edge i j ↔
      (i = 1 ∧ (j = 0 ∨ j = 5 ∨ j = 11)) ∨
      (i = 2 ∧ (j = 2 ∨ j = 6 ∨ j = 12)) ∨
      (i = 4 ∧ (j = 3 ∨ j = 4 ∨ j = 8)) ∨
      (i = 10 ∧ (j = 7 ∨ j = 9 ∨ j = 10)) := by
  decide +kernel

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

set_option maxHeartbeats 1300000 in
private theorem correct (x : Fin 26 → Bool) :
    C.eval (List.ofFn x ++ [x 1 || x 2]) = true ↔
      ∃ i j : Fin 13, edge i j ∧ x (Fin.castAdd 13 i) = true ∧ x (Fin.natAdd 13 j) = true := by
  let bank := List.ofFn x ++ [x 1 || x 2]
  let W (idx : ℕ) := (C.gates.foldl step bank).getD idx false
  have hlen : bank.length = 27 := by simp [bank]
  have orig (k : Fin 26) : W k.val = x k := by
    change (C.gates.foldl step bank).getD k.val false = _
    rw [prefixRead _ _ _ (by rw [hlen]; have := k.isLt; omega)]
    change (List.ofFn x ++ [x 1 || x 2]).getD k.val false = _
    rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using k.isLt),
      List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using k.isLt)]
    simp only [List.getElem_ofFn, Fin.eta]
  have readGate (k : ℕ) (g : Gate) (hg : C.gates[k]? = some g)
      (hb : ∀ i ∈ g.inputs, i < 27 + k) :
      W (27 + k) = g.op.eval (g.inputs.map W) := by
    have r := gateRead C.gates bank k g hg
    have out := r (fun i hi => by rw [hlen]; exact hb i hi)
    change W (bank.length + k) = g.op.eval (g.inputs.map W) at out
    simpa only [hlen] using out
  have v0 : W 27 = (W 13 || W 18) := by
    simpa [GateOp.eval] using readGate 0 ⟨.or, [13, 18]⟩ rfl (by decide)
  have v1 : W 28 = (W 27 || W 24) := by
    simpa [GateOp.eval] using readGate 1 ⟨.or, [27, 24]⟩ rfl (by decide)
  have v2 : W 29 = (W 1 && W 28) := by
    simpa [GateOp.eval] using readGate 2 ⟨.and, [1, 28]⟩ rfl (by decide)
  have v3 : W 30 = (W 15 || W 19) := by
    simpa [GateOp.eval] using readGate 3 ⟨.or, [15, 19]⟩ rfl (by decide)
  have v4 : W 31 = (W 30 || W 25) := by
    simpa [GateOp.eval] using readGate 4 ⟨.or, [30, 25]⟩ rfl (by decide)
  have v5 : W 32 = (W 2 && W 31) := by
    simpa [GateOp.eval] using readGate 5 ⟨.and, [2, 31]⟩ rfl (by decide)
  have v6 : W 33 = (W 16 || W 17) := by
    simpa [GateOp.eval] using readGate 6 ⟨.or, [16, 17]⟩ rfl (by decide)
  have v7 : W 34 = (W 33 || W 21) := by
    simpa [GateOp.eval] using readGate 7 ⟨.or, [33, 21]⟩ rfl (by decide)
  have v8 : W 35 = (W 4 && W 34) := by
    simpa [GateOp.eval] using readGate 8 ⟨.and, [4, 34]⟩ rfl (by decide)
  have v9 : W 36 = (W 20 || W 22) := by
    simpa [GateOp.eval] using readGate 9 ⟨.or, [20, 22]⟩ rfl (by decide)
  have v10 : W 37 = (W 36 || W 23) := by
    simpa [GateOp.eval] using readGate 10 ⟨.or, [36, 23]⟩ rfl (by decide)
  have v11 : W 38 = (W 10 && W 37) := by
    simpa [GateOp.eval] using readGate 11 ⟨.and, [10, 37]⟩ rfl (by decide)
  have v12 : W 39 = (W 29 || W 32) := by
    simpa [GateOp.eval] using readGate 12 ⟨.or, [29, 32]⟩ rfl (by decide)
  have v13 : W 40 = (W 35 || W 38) := by
    simpa [GateOp.eval] using readGate 13 ⟨.or, [35, 38]⟩ rfl (by decide)
  have v14 : W 41 = (W 39 || W 40) := by
    simpa [GateOp.eval] using readGate 14 ⟨.or, [39, 40]⟩ rfl (by decide)
  have x1 : W 1 = x 1 := orig 1
  have x2 : W 2 = x 2 := orig 2
  have x4 : W 4 = x 4 := orig 4
  have x10 : W 10 = x 10 := orig 10
  have x13 : W 13 = x 13 := orig 13
  have x15 : W 15 = x 15 := orig 15
  have x16 : W 16 = x 16 := orig 16
  have x17 : W 17 = x 17 := orig 17
  have x18 : W 18 = x 18 := orig 18
  have x19 : W 19 = x 19 := orig 19
  have x20 : W 20 = x 20 := orig 20
  have x21 : W 21 = x 21 := orig 21
  have x22 : W 22 = x 22 := orig 22
  have x23 : W 23 = x 23 := orig 23
  have x24 : W 24 = x 24 := orig 24
  have x25 : W 25 = x 25 := orig 25
  change W 41 = true ↔ _
  rw [v14,v13,v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1,v0, x1, x2, x4, x10, x13, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25]
  simp only [Bool.and_eq_true, Bool.or_eq_true]
  constructor
  · rintro ((⟨hi,hj⟩ | ⟨hi,hj⟩) | (⟨hi,hj⟩ | ⟨hi,hj⟩))
    · rcases hj with (ha | hb) | hc
      · exact ⟨1, 0, (table 1 0).mpr (by decide), hi, ha⟩
      · exact ⟨1, 5, (table 1 5).mpr (by decide), hi, hb⟩
      · exact ⟨1, 11, (table 1 11).mpr (by decide), hi, hc⟩
    · rcases hj with (ha | hb) | hc
      · exact ⟨2, 2, (table 2 2).mpr (by decide), hi, ha⟩
      · exact ⟨2, 6, (table 2 6).mpr (by decide), hi, hb⟩
      · exact ⟨2, 12, (table 2 12).mpr (by decide), hi, hc⟩
    · rcases hj with (ha | hb) | hc
      · exact ⟨4, 3, (table 4 3).mpr (by decide), hi, ha⟩
      · exact ⟨4, 4, (table 4 4).mpr (by decide), hi, hb⟩
      · exact ⟨4, 8, (table 4 8).mpr (by decide), hi, hc⟩
    · rcases hj with (ha | hb) | hc
      · exact ⟨10, 7, (table 10 7).mpr (by decide), hi, ha⟩
      · exact ⟨10, 9, (table 10 9).mpr (by decide), hi, hb⟩
      · exact ⟨10, 10, (table 10 10).mpr (by decide), hi, hc⟩
  · rintro ⟨i, j, he, hi, hj⟩
    rw [table] at he
    rcases he with h | h | h | h
    · rcases h with ⟨rfl, rfl | rfl | rfl⟩
      · exact Or.inl (Or.inl ⟨hi, Or.inl (Or.inl hj)⟩)
      · exact Or.inl (Or.inl ⟨hi, Or.inl (Or.inr hj)⟩)
      · exact Or.inl (Or.inl ⟨hi, Or.inr hj⟩)
    · rcases h with ⟨rfl, rfl | rfl | rfl⟩
      · exact Or.inl (Or.inr ⟨hi, Or.inl (Or.inl hj)⟩)
      · exact Or.inl (Or.inr ⟨hi, Or.inl (Or.inr hj)⟩)
      · exact Or.inl (Or.inr ⟨hi, Or.inr hj⟩)
    · rcases h with ⟨rfl, rfl | rfl | rfl⟩
      · exact Or.inr (Or.inl ⟨hi, Or.inl (Or.inl hj)⟩)
      · exact Or.inr (Or.inl ⟨hi, Or.inl (Or.inr hj)⟩)
      · exact Or.inr (Or.inl ⟨hi, Or.inr hj⟩)
    · rcases h with ⟨rfl, rfl | rfl | rfl⟩
      · exact Or.inr (Or.inr ⟨hi, Or.inl (Or.inl hj)⟩)
      · exact Or.inr (Or.inr ⟨hi, Or.inl (Or.inr hj)⟩)
      · exact Or.inr (Or.inr ⟨hi, Or.inr hj⟩)

end PEqualNP.Outside.L_meta_18617

open PEqualNP.Outside.L_meta_18617 in
theorem PEqualNP.Outside.L_meta_18617 : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (15 : ℕ) ∧ (27 : ℕ) ≤ x1.output ∧ x1.output < (27 : ℕ) + x1.size ∧ PEqualNP.TopForm.IsAO2 (27 : ℕ) x1 ∧ (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧ ∀ (x2 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x2 ++ [x2 (1 : Fin (26 : ℕ)) || x2 (2 : Fin (26 : ℕ))]) = Bool.true ↔ ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x3 ∈ [(1 : Fin (13 : ℕ)), (2 : Fin (13 : ℕ)), (4 : Fin (13 : ℕ)), (10 : Fin (13 : ℕ))] ∧ x4 ≠ (1 : Fin (13 : ℕ)) ∧ (x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ))) ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true := by
  refine ⟨C, by decide, by decide, by decide, by decide, by decide, fun x => ?_⟩
  simpa only [edge, and_assoc] using correct x
