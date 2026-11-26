import PEqualNP.Defs

set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_8321_1
    (hmono : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 C →
      ∀ x y : Fin 42 → Bool, (∀ i, x i = true → y i = true) →
      ∀ w : ℕ, (C.wires (List.ofFn x)).getD w false = true →
        (C.wires (List.ofFn y)).getD w false = true)
    (hboundary :
      let E := fun (p l : Fin 42) =>
        p.val < 21 ∧ 21 ≤ l.val ∧ (l.val + 21 - p.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)
      let computes := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
        ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ p l, E p l ∧ x p = true ∧ x l = true
      let cost := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
        C.gates.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.casesOn g.op
          false true false (fun _ => false) false)
      ∀ C, PEqualNP.MetaComplexity.Monotone2 C → computes C →
        ∃ D, PEqualNP.MetaComplexity.Monotone2 D ∧ computes D ∧ cost D ≤ cost C ∧
          ∀ A : Finset (Fin 42), (∀ p ∈ A, p.val < 21) →
            let L := fun l : Fin 42 => 21 ≤ l.val ∧ ∀ p ∈ A, ¬ E p l
            (∀ p : Fin 42, p.val < 21 → p ∉ A → ∃ l, L l ∧ E p l) →
            ∀ y : Fin 42 → Bool, (∀ i, y i = true ↔ i ∈ A ∨ L i) →
            ∀ j g, D.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
              (D.wires (List.ofFn y)).getD (42+j) false = false) :
    (have x1 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x2 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (42 : ℕ)) (x4 : Fin (42 : ℕ)), (↑x3 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x4 ∧ (↑x4 + (21 : ℕ) - ↑x3) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → x4.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x7 : Fin (42 : ℕ) → Bool), (x2.wires (List.ofFn x7)).getD ((42 : ℕ) + x3) Bool.false = Bool.true → x2.eval (List.ofFn x7) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.casesOn x4.op Bool.false Bool.true Bool.false (fun (x5 : ℕ) => Bool.false) Bool.false) x3.gates; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → x1 x4 → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 ∧ x1 x7 ∧ x2 x7 ∧ x3 x7 ≤ x3 x4) := by
  classical
  let E := fun (p l : Fin 42) =>
    p.val < 21 ∧ 21 ≤ l.val ∧ (l.val + 21 - p.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)
  dsimp only
  intro C hC hF
  obtain ⟨D, hD, hG, hcost, hrows⟩ := hboundary C hC hF
  refine ⟨D, hD, hG, ?_, hcost⟩
  intro j g hj hg x hw
  by_contra hneg
  have hnone : ¬ ∃ p l, E p l ∧ x p = true ∧ x l = true := fun e => hneg ((hG x).2 e)
  let lines := fun l : Fin 42 => 21 ≤ l.val ∧ ∀ p : Fin 42, p.val < 21 → x p = true → ¬ E p l
  let A := Finset.univ.filter fun p : Fin 42 => p.val < 21 ∧ ∀ l, lines l → ¬ E p l
  have hA (p : Fin 42) : p ∈ A ↔ p.val < 21 ∧ ∀ l, lines l → ¬ E p l := by
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
  have hcontains (p : Fin 42) (hp : p.val < 21) (hx : x p = true) : p ∈ A :=
    (hA p).2 ⟨hp, fun _ h => h.2 p hp hx⟩
  let closedLines := fun l : Fin 42 => 21 ≤ l.val ∧ ∀ p ∈ A, ¬ E p l
  have hsame (l : Fin 42) : lines l ↔ closedLines l := by
    constructor
    · intro hl
      exact ⟨hl.1, fun p hp => ((hA p).1 hp).2 l hl⟩
    · intro hl
      exact ⟨hl.1, fun p hp hx => hl.2 p (hcontains p hp hx)⟩
  have hclosed (p : Fin 42) (hp : p.val < 21) (hna : p ∉ A) :
      ∃ l, closedLines l ∧ E p l := by
    by_contra hmissing
    apply hna
    apply (hA p).2
    exact ⟨hp, fun l hl he => hmissing ⟨l, (hsame l).1 hl, he⟩⟩
  let y := fun i : Fin 42 => decide (i ∈ A ∨ closedLines i)
  have hbits (i : Fin 42) : y i = true ↔ i ∈ A ∨ closedLines i := decide_eq_true_iff
  have hdom (i : Fin 42) (hi : x i = true) : y i = true := by
    apply (hbits i).2
    by_cases hp : i.val < 21
    · exact Or.inl (hcontains i hp hi)
    · exact Or.inr ((hsame i).1 ⟨Nat.le_of_not_gt hp, fun p _ hx he => hnone ⟨p,i,he,hx,hi⟩⟩)
  have hz := hrows A (fun p hp => ((hA p).1 hp).1) hclosed y hbits j g hj hg
  have ho := hmono D hD x y hdom (42+j) hw
  exact Bool.noConfusion (hz.symm.trans ho)

