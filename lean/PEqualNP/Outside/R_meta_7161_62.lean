import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_7161_62
    (affine :
      let e := fun (p l : Fin 13) => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List Nat)
      let u := fun (d : Fin 4) => ([0,1,3,9] : List (Fin 13)).getD d.val 0
      let input := fun (s t : Finset (Fin 13)) => List.ofFn fun i : Fin 26 =>
        if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
      ∃ (B : Circuit) (r : Fin 4 → Nat), Monotone2 B ∧ B.size ≤ 51 ∧
        B.output < 26 + B.size ∧ (∀ d, r d < 26 + B.size) ∧
        (∀ p l : Fin 13, p.val ∉ ([0,1,3,9] : List Nat) → e p l → B.eval (input {p} {l}) = true) ∧
        (∀ d l, l ≠ 0 → e (u d) l → (B.wires (input {u d} {l})).getD (r d) false = true) ∧
        ∀ s t, (∀ p ∈ s, ∀ l ∈ t, ¬e p l) →
          B.eval (input s t) = false ∧ ∀ d, u d ∈ s → (B.wires (input s t)).getD (r d) false = false)
    (extend :
      let u := fun (d : Fin 4) => ([0,1,3,9] : List (Fin 13)).getD d.val 0
      ∀ (B : Circuit) (r : Fin 4 → Nat), Monotone2 B → B.output < 26 + B.size →
        (∀ d, r d < 26 + B.size) → ∃ (Q : Circuit) (w : Nat),
        Monotone2 Q ∧ Q.size ≤ B.size + 11 ∧ B.output < w ∧ ∀ z : Fin 26 → Bool,
          (Q.wires (List.ofFn z)).getD B.output false = B.eval (List.ofFn z) ∧
          (Q.wires (List.ofFn z)).getD w false = (List.finRange 4).any (fun d =>
            z (Fin.castAdd 13 (u d)) && (z 13 || (B.wires (List.ofFn z)).getD (r d) false)))
    : (let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x2 : Finset (Fin (13 : ℕ))) => {x3 : Fin (13 : ℕ) | ∀ x4 ∈ x2, ¬x1 x4 x3}; have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x3 x4 : Finset (Fin (13 : ℕ))) => List.ofFn fun (x5 : Fin (26 : ℕ)) => if ↑x5 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x3) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x4); ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) (x6 : ℕ) (x7 : Bool),   PEqualNP.MetaComplexity.Monotone2 x4 ∧     x4.size ≤ (62 : ℕ) ∧       x5 < x6 ∧         have x8 : ℕ → Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x8 : ℕ) (x9 x10 : Finset (Fin (13 : ℕ))) => (x4.wires (x3 x9 x10)).getD x8 Bool.false;         have x9 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x9 x10 : Finset (Fin (13 : ℕ))) => (if x7 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or).eval [x8 x5 x9 x10, x8 x6 x9 x10];         (∀ (x10 x11 : Fin (13 : ℕ)), x1 x10 x11 → x9 {x10} {x11} = Bool.true) ∧ ∀ (x10 : Finset (Fin (13 : ℕ))), x10.card ≤ (3 : ℕ) → x9 x10 (x2 x10) = Bool.false ∧ x9 (x2 x10) x10 = Bool.false) := by
  obtain ⟨B, r, hB, sizeB, outB, bounded, affinePos, classPos, excluded⟩ := affine
  obtain ⟨Q, w, hQ, sizeQ, ordered, extendRun⟩ := extend B r hB outB bounded
  let ds : List Nat := [0,1,3,9]
  let e (p l : Fin 13) := (p.val + l.val) % 13 ∈ ds
  let u (d : Fin 4) := ([0,1,3,9] : List (Fin 13)).getD d.val 0
  let bit (s t : Finset (Fin 13)) (i : Fin 26) :=
    if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
  let input (s t : Finset (Fin 13)) := List.ofFn (bit s t)
  let off (s : Finset (Fin 13)) := Finset.univ.filter fun l => ∀ p ∈ s, ¬e p l
  let read (s t : Finset (Fin 13)) := GateOp.or.eval
    [(Q.wires (input s t)).getD B.output false, (Q.wires (input s t)).getD w false]
  have infPoint : ∀ p : Fin 13, p.val ∈ ds ↔ ∃ d : Fin 4, u d = p := by decide
  have lineZero : ∀ d : Fin 4, e (u d) 0 := by decide
  have onLeft (s t : Finset (Fin 13)) (p : Fin 13) :
      bit s t (Fin.castAdd 13 p) = decide (p ∈ s) := by simp [bit]
  have onRight (s t : Finset (Fin 13)) : bit s t 13 = decide ((0 : Fin 13) ∈ t) := rfl
  have staged (s t : Finset (Fin 13)) :
      read s t = (B.eval (input s t) || (List.finRange 4).any (fun d =>
        bit s t (Fin.castAdd 13 (u d)) && (bit s t 13 || (B.wires (input s t)).getD (r d) false))) := by
    obtain ⟨oldVal, newVal⟩ := extendRun (bit s t)
    have evalOr (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by cases a <;> cases b <;> decide
    unfold read
    rw [evalOr]
    exact congrArg₂ Bool.or oldVal newVal
  have zero (s t : Finset (Fin 13)) (hn : ∀ p ∈ s, ∀ l ∈ t, ¬e p l) : read s t = false := by
    obtain ⟨af, cls⟩ := excluded s t hn
    change B.eval (input s t) = false at af
    change ∀ d, u d ∈ s → (B.wires (input s t)).getD (r d) false = false at cls
    rw [staged, af, Bool.false_or]
    apply Bool.eq_false_iff.mpr
    intro ht
    obtain ⟨d, _, hd⟩ := List.any_eq_true.mp ht
    rw [Bool.and_eq_true, onLeft, decide_eq_true_eq, Bool.or_eq_true, onRight, decide_eq_true_eq] at hd
    rcases hd with ⟨hp, hz | hc⟩
    · exact hn (u d) hp 0 hz (lineZero d)
    · rw [cls d hp] at hc
      contradiction
  refine ⟨Q, B.output, w, false, hQ, by omega, ordered, ?_⟩
  change (∀ p l, e p l → read {p} {l} = true) ∧
    ∀ s : Finset (Fin 13), s.card ≤ 3 → read s (off s) = false ∧ read (off s) s = false
  constructor
  · intro p l hpl
    rw [staged, Bool.or_eq_true]
    by_cases hi : p.val ∈ ds
    · obtain ⟨d, rfl⟩ := (infPoint p).mp hi
      right
      apply List.any_eq_true.mpr
      refine ⟨d, List.mem_finRange _, ?_⟩
      rw [Bool.and_eq_true, onLeft, decide_eq_true_eq, Bool.or_eq_true, onRight, decide_eq_true_eq]
      refine ⟨Finset.mem_singleton_self _, ?_⟩
      by_cases hz : l = 0
      · exact Or.inl (hz ▸ Finset.mem_singleton_self _)
      · exact Or.inr (classPos d l hz hpl)
    · exact Or.inl (affinePos p l hi hpl)
  · intro s _
    constructor
    · exact zero s (off s) fun p hp l hl he => (Finset.mem_filter.mp hl).2 p hp he
    · exact zero (off s) s fun p hp l hl he =>
        (Finset.mem_filter.mp hp).2 l hl (by simpa [e, Nat.add_comm] using he)
