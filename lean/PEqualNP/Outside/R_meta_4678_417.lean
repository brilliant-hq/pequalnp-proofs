import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4678_417
    (hShort :
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let P := fun (p l : Fin 13) =>
        List.ofFn (fun u : Fin 13 => decide (u = p)) ++
        List.ofFn (fun v : Fin 13 => decide (v = l))
      let N := fun (Q : Finset (Fin 13)) =>
        List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
        List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ D))
      let good := fun (Q : Finset (Fin 13)) =>
        Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter (fun u => u - k ∈ D)).card ≤ 2
      let fits := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (s : List ℕ) =>
        let extend := fun (x : List Bool) => x ++ [s.any (fun i => x.getD i false)]
        (∀ p l : Fin 13, p - l ∈ D → C.eval (extend (P p l)) = true) ∧
        (∀ Q, good Q → C.eval (extend (N Q)) = false)
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (s : List ℕ),
        s ∈ ([[], [0], [13]] : List (List ℕ)) →
        PEqualNP.MetaComplexity.Monotone2 C →
        (∀ i : Fin C.gates.length, ∀ w ∈ (C.gates.get i).inputs, w < 27 + i.val) → fits C s →
        27 ≤ C.output → C.output < 27 + C.size → 63 ≤ C.size)
    (hPair :
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let P := fun (p l : Fin 13) =>
        List.ofFn (fun u : Fin 13 => decide (u = p)) ++
        List.ofFn (fun v : Fin 13 => decide (v = l))
      let N := fun (Q : Finset (Fin 13)) =>
        List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
        List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ D))
      let good := fun (Q : Finset (Fin 13)) =>
        Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter (fun u => u - k ∈ D)).card ≤ 2
      let fits := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (s : List ℕ) =>
        let extend := fun (x : List Bool) => x ++ [s.any (fun i => x.getD i false)]
        (∀ p l : Fin 13, p - l ∈ D → C.eval (extend (P p l)) = true) ∧
        (∀ Q, good Q → C.eval (extend (N Q)) = false)
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (s : List ℕ),
        s ∈ ([[0, 1], [0, 2], [0, 13], [0, 14], [0, 15], [0, 17], [0, 20], [13, 14], [13, 15]] : List (List ℕ)) →
        PEqualNP.MetaComplexity.Monotone2 C →
        (∀ i : Fin C.gates.length, ∀ w ∈ (C.gates.get i).inputs, w < 27 + i.val) → fits C s →
        27 ≤ C.output → C.output < 27 + C.size → 63 ≤ C.size) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : (List Bool → Bool) → Prop := fun (x2 : List Bool → Bool) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2 ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2 ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → List ℕ → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : List ℕ) => x2 fun (x5 : List Bool) => x3.eval (x5 ++ [x4.any fun (x6 : ℕ) => x5.getD x6 Bool.false]); have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x5 : Fin x4.gates.length), ∀ x6 ∈ (x4.gates.get x5).inputs, x6 < (27 : ℕ) + ↑x5; have x5 : List (List ℕ) := [[], [(0 : ℕ)], [(13 : ℕ)], [(0 : ℕ), (1 : ℕ)], [(0 : ℕ), (2 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)], [(0 : ℕ), (15 : ℕ)], [(0 : ℕ), (17 : ℕ)], [(0 : ℕ), (20 : ℕ)], [(13 : ℕ), (14 : ℕ)], [(13 : ℕ), (15 : ℕ)]]; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), ∀ x7 ∈ x5, PEqualNP.MetaComplexity.Monotone2 x6 → x4 x6 → x3 x6 x7 → (63 : ℕ) ≤ x6.size := by
  intro x1 x2 x3 x4 x5 C s hs hm hb hfit
  have key : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool), ∃ t : List Bool,
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = w ++ t ∧
        t.length = gs.length := by
    intro gs
    induction gs with
    | nil => intro w; exact ⟨[], by simp, rfl⟩
    | cons g gs ih =>
      intro w
      obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, ?_⟩
      · rw [List.foldl_cons, ht]; simp
      · simp [hl]
  have evalEq : ∀ y : List Bool, C.eval y =
      (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) y).getD C.output false :=
    fun y => rfl
  have inc : ∀ p l : Fin 13, p - l ∈ x1 →
      C.eval ((List.ofFn fun u : Fin 13 => decide (u = p)) ++ (List.ofFn fun v : Fin 13 => decide (v = l)) ++
        [s.any fun i => ((List.ofFn fun u : Fin 13 => decide (u = p)) ++
          (List.ofFn fun v : Fin 13 => decide (v = l))).getD i false]) = true :=
    fun p l h => hfit.1 p l h
  have low : ∀ s ∈ x5, ∀ i < 27, ∃ p l : Fin 13, p - l ∈ x1 ∧
      ((List.ofFn fun u : Fin 13 => decide (u = p)) ++ (List.ofFn fun v : Fin 13 => decide (v = l)) ++
        [s.any fun i => ((List.ofFn fun u : Fin 13 => decide (u = p)) ++
          (List.ofFn fun v : Fin 13 => decide (v = l))).getD i false]).getD i false = false := by
    decide +kernel
  have hlo : 27 ≤ C.output := by
    by_contra hcon
    obtain ⟨p, l, hpl, hfalse⟩ := low s hs C.output (by omega)
    have h := inc p l hpl
    obtain ⟨t, ht, -⟩ := key C.gates ((List.ofFn fun u : Fin 13 => decide (u = p)) ++
      (List.ofFn fun v : Fin 13 => decide (v = l)) ++
        [s.any fun i => ((List.ofFn fun u : Fin 13 => decide (u = p)) ++
          (List.ofFn fun v : Fin 13 => decide (v = l))).getD i false])
    rw [evalEq, ht, List.getD_append _ _ _ _ (by simp; omega), hfalse] at h
    exact Bool.false_ne_true h
  have hhi : C.output < 27 + C.size := by
    by_contra hcon
    have h := inc 0 0 (by decide)
    obtain ⟨t, ht, hl⟩ := key C.gates ((List.ofFn fun u : Fin 13 => decide (u = 0)) ++
      (List.ofFn fun v : Fin 13 => decide (v = 0)) ++
        [s.any fun i => ((List.ofFn fun u : Fin 13 => decide (u = 0)) ++
          (List.ofFn fun v : Fin 13 => decide (v = 0))).getD i false])
    have hsz : C.size = C.gates.length := rfl
    rw [evalEq, ht, List.getD_eq_default _ _ (by simp; omega)] at h
    exact Bool.false_ne_true h
  have hcase : s ∈ ([[], [0], [13]] : List (List ℕ)) ∨
      s ∈ ([[0, 1], [0, 2], [0, 13], [0, 14], [0, 15], [0, 17], [0, 20], [13, 14], [13, 15]] : List (List ℕ)) := by
    have hs' : s ∈ ([[], [0], [13], [0, 1], [0, 2], [0, 13], [0, 14], [0, 15], [0, 17],
        [0, 20], [13, 14], [13, 15]] : List (List ℕ)) := hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs' ⊢
    rcases hs' with h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h]
  rcases hcase with h | h
  · exact hShort C s h hm hb ⟨hfit.1, fun Q hQ => hfit.2 Q hQ.1 hQ.2⟩ hlo hhi
  · exact hPair C s h hm hb ⟨hfit.1, fun Q hQ => hfit.2 Q hQ.1 hQ.2⟩ hlo hhi
