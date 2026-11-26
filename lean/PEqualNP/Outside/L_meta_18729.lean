import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18729_aux

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

def lineGates (base : ℕ) (l p0 p1 p2 p3 : ℕ) : List Gate :=
  [ ⟨GateOp.or, [p0, p1]⟩,
    ⟨GateOp.or, [p2, p3]⟩,
    ⟨GateOp.or, [base, base + 1]⟩,
    ⟨GateOp.and, [13 + l, base + 2]⟩ ]

def gates29 : List Gate :=
  lineGates 27 2 2 3 5 11 ++
  lineGates 31 3 3 4 6 12 ++
  lineGates 35 6 6 7 9 2 ++
  lineGates 39 7 7 8 10 3 ++
  lineGates 43 8 8 9 11 4 ++
  lineGates 47 9 9 10 12 5 ++
  [ ⟨GateOp.or, [30, 34]⟩,
    ⟨GateOp.or, [38, 42]⟩,
    ⟨GateOp.or, [46, 50]⟩,
    ⟨GateOp.or, [51, 52]⟩,
    ⟨GateOp.or, [53, 54]⟩ ]

def circ29 : Circuit := ⟨gates29, 55⟩

theorem circ29_size : circ29.size ≤ 29 := by decide
theorem circ29_out_lo : 27 ≤ circ29.output := by decide
theorem circ29_out_hi : circ29.output < 27 + circ29.size := by decide
theorem circ29_ao2 : IsAO2 27 circ29 := by decide +kernel
theorem circ29_nodup : ∀ g ∈ circ29.gates, g.inputs.Nodup := by decide +kernel

theorem circ29_eval (x : Fin 26 → Bool) :
    circ29.eval (List.ofFn x ++ [x 0 || x 1]) =
      (((x 21 && ((x 8 || x 9) || (x 11 || x 4))) ||
        (x 22 && ((x 9 || x 10) || (x 12 || x 5)))) ||
       (((x 15 && ((x 2 || x 3) || (x 5 || x 11))) ||
         (x 16 && ((x 3 || x 4) || (x 6 || x 12)))) ||
        ((x 19 && ((x 6 || x 7) || (x 9 || x 2))) ||
         (x 20 && ((x 7 || x 8) || (x 10 || x 3)))))) := by
  simp only [circ29, gates29, lineGates, Circuit.eval, Circuit.wires, GateOp.eval,
    List.cons_append, List.nil_append, List.foldl_cons, List.foldl_nil,
    List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil,
    Bool.or_false, Bool.and_true, List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, List.getD_cons_zero, List.getD_cons_succ, id_eq]
  rfl

theorem circ29_pos :
    ∀ p l : Fin 13, l ∈ ([2, 3, 6, 7, 8, 9] : List (Fin 13)) →
      (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) →
      circ29.eval (List.ofFn (fun i : Fin 26 => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) ++
        [decide ((0 : Fin 26) = Fin.castAdd 13 p ∨ (0 : Fin 26) = Fin.natAdd 13 l) ||
         decide ((1 : Fin 26) = Fin.castAdd 13 p ∨ (1 : Fin 26) = Fin.natAdd 13 l)]) = true := by
  decide +kernel

theorem circ29_sound (x : Fin 26 → Bool)
    (h : circ29.eval (List.ofFn x ++ [x 0 || x 1]) = true) :
    ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
  rw [circ29_eval] at h
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ((⟨hl, (hp | hp) | (hp | hp)⟩ | ⟨hl, (hp | hp) | (hp | hp)⟩) |
                 ((⟨hl, (hp | hp) | (hp | hp)⟩ | ⟨hl, (hp | hp) | (hp | hp)⟩) |
                  (⟨hl, (hp | hp) | (hp | hp)⟩ | ⟨hl, (hp | hp) | (hp | hp)⟩)))
  · exact ⟨8, 8, by decide, hp, hl⟩
  · exact ⟨9, 8, by decide, hp, hl⟩
  · exact ⟨11, 8, by decide, hp, hl⟩
  · exact ⟨4, 8, by decide, hp, hl⟩
  · exact ⟨9, 9, by decide, hp, hl⟩
  · exact ⟨10, 9, by decide, hp, hl⟩
  · exact ⟨12, 9, by decide, hp, hl⟩
  · exact ⟨5, 9, by decide, hp, hl⟩
  · exact ⟨2, 2, by decide, hp, hl⟩
  · exact ⟨3, 2, by decide, hp, hl⟩
  · exact ⟨5, 2, by decide, hp, hl⟩
  · exact ⟨11, 2, by decide, hp, hl⟩
  · exact ⟨3, 3, by decide, hp, hl⟩
  · exact ⟨4, 3, by decide, hp, hl⟩
  · exact ⟨6, 3, by decide, hp, hl⟩
  · exact ⟨12, 3, by decide, hp, hl⟩
  · exact ⟨6, 6, by decide, hp, hl⟩
  · exact ⟨7, 6, by decide, hp, hl⟩
  · exact ⟨9, 6, by decide, hp, hl⟩
  · exact ⟨2, 6, by decide, hp, hl⟩
  · exact ⟨7, 7, by decide, hp, hl⟩
  · exact ⟨8, 7, by decide, hp, hl⟩
  · exact ⟨10, 7, by decide, hp, hl⟩
  · exact ⟨3, 7, by decide, hp, hl⟩

theorem main_proof :
    (let inc (p l : Fin 13) := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      let row (p l : Fin 13) : Fin 26 → Bool := fun i =>
        decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
      let input (x : Fin 26 → Bool) := List.ofFn x ++ [x 0 || x 1]
      ∃ D : Circuit, D.size ≤ 29 ∧ 27 ≤ D.output ∧ D.output < 27 + D.size ∧
        IsAO2 27 D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
        (∀ p l : Fin 13, l ∈ ([2, 3, 6, 7, 8, 9] : List (Fin 13)) → inc p l →
          D.eval (input (row p l)) = true) ∧
        ∀ x : Fin 26 → Bool, D.eval (input x) = true →
          ∃ p l : Fin 13, inc p l ∧
            x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) :=
  ⟨circ29, circ29_size, circ29_out_lo, circ29_out_hi, circ29_ao2, circ29_nodup, circ29_pos, circ29_sound⟩

end PEqualNP.Outside.L_meta_18729_aux

theorem PEqualNP.Outside.L_meta_18729 : (have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (26 : ℕ) → Bool := fun (x2 x3 : Fin (13 : ℕ)) (x4 : Fin (26 : ℕ)) => Decidable.decide (x4 = Fin.castAdd (13 : ℕ) x2 ∨ x4 = Fin.natAdd (13 : ℕ) x3); have x3 : (Fin (26 : ℕ) → Bool) → List Bool := fun (x3 : Fin (26 : ℕ) → Bool) => List.ofFn x3 ++ [x3 (0 : Fin (26 : ℕ)) || x3 (1 : Fin (26 : ℕ))]; ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x4.size ≤ (29 : ℕ) ∧ (27 : ℕ) ≤ x4.output ∧ x4.output < (27 : ℕ) + x4.size ∧ PEqualNP.TopForm.IsAO2 (27 : ℕ) x4 ∧ (∀ x5 ∈ x4.gates, x5.inputs.Nodup) ∧ (∀ (x5 x6 : Fin (13 : ℕ)), x6 ∈ [(2 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (6 : Fin (13 : ℕ)), (7 : Fin (13 : ℕ)), (8 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))] → x1 x5 x6 → x4.eval (x3 (x2 x5 x6)) = Bool.true) ∧ ∀ (x5 : Fin (26 : ℕ) → Bool), x4.eval (x3 x5) = Bool.true → ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), x1 x7 x8 ∧ x5 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x8) = Bool.true)  := by
  exact PEqualNP.Outside.L_meta_18729_aux.main_proof
