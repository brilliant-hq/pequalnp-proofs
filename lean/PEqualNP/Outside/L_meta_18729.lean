import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
set_option maxHeartbeats 7000000 in
theorem PEqualNP.Outside.L_meta_18729 : (have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (26 : ℕ) → Bool := fun (x2 x3 : Fin (13 : ℕ)) (x4 : Fin (26 : ℕ)) => Decidable.decide (x4 = Fin.castAdd (13 : ℕ) x2 ∨ x4 = Fin.natAdd (13 : ℕ) x3); have x3 : (Fin (26 : ℕ) → Bool) → List Bool := fun (x3 : Fin (26 : ℕ) → Bool) => List.ofFn x3 ++ [x3 (0 : Fin (26 : ℕ)) || x3 (1 : Fin (26 : ℕ))]; ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x4.size ≤ (29 : ℕ) ∧ (27 : ℕ) ≤ x4.output ∧ x4.output < (27 : ℕ) + x4.size ∧ PEqualNP.TopForm.IsAO2 (27 : ℕ) x4 ∧ (∀ x5 ∈ x4.gates, x5.inputs.Nodup) ∧ (∀ (x5 x6 : Fin (13 : ℕ)), x6 ∈ [(2 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (6 : Fin (13 : ℕ)), (7 : Fin (13 : ℕ)), (8 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))] → x1 x5 x6 → x4.eval (x3 (x2 x5 x6)) = Bool.true) ∧ ∀ (x5 : Fin (26 : ℕ) → Bool), x4.eval (x3 x5) = Bool.true → ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), x1 x7 x8 ∧ x5 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x8) = Bool.true) := by
  dsimp only
  let C : Circuit := ⟨[⟨.or,[2,3]⟩, ⟨.or,[5,11]⟩, ⟨.or,[27,28]⟩, ⟨.and,[15,29]⟩, ⟨.or,[3,4]⟩, ⟨.or,[6,12]⟩, ⟨.or,[31,32]⟩, ⟨.and,[16,33]⟩, ⟨.or,[6,7]⟩, ⟨.or,[9,2]⟩, ⟨.or,[35,36]⟩, ⟨.and,[19,37]⟩, ⟨.or,[7,8]⟩, ⟨.or,[10,3]⟩, ⟨.or,[39,40]⟩, ⟨.and,[20,41]⟩, ⟨.or,[8,9]⟩, ⟨.or,[11,4]⟩, ⟨.or,[43,44]⟩, ⟨.and,[21,45]⟩, ⟨.or,[9,10]⟩, ⟨.or,[12,5]⟩, ⟨.or,[47,48]⟩, ⟨.and,[22,49]⟩, ⟨.or,[30,34]⟩, ⟨.or,[51,38]⟩, ⟨.or,[52,42]⟩, ⟨.or,[53,46]⟩, ⟨.or,[54,50]⟩],55⟩
  refine ⟨C, by decide, by decide, by decide, by decide, by decide, by decide +kernel, ?_⟩
  intro x hx
  simp [C, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
    Bool.or_eq_true, Bool.and_eq_true] at hx
  rcases hx with (((((h2 | h3) | h6) | h7) | h8) | h9)
  · rcases h2 with ⟨hl, (hp | hp) | (hp | hp)⟩
    · exact ⟨2, 2, by decide, hp, hl⟩
    · exact ⟨3, 2, by decide, hp, hl⟩
    · exact ⟨5, 2, by decide, hp, hl⟩
    · exact ⟨11, 2, by decide, hp, hl⟩
  · rcases h3 with ⟨hl, (hp | hp) | (hp | hp)⟩
    · exact ⟨3, 3, by decide, hp, hl⟩
    · exact ⟨4, 3, by decide, hp, hl⟩
    · exact ⟨6, 3, by decide, hp, hl⟩
    · exact ⟨12, 3, by decide, hp, hl⟩
  · rcases h6 with ⟨hl, (hp | hp) | (hp | hp)⟩
    · exact ⟨6, 6, by decide, hp, hl⟩
    · exact ⟨7, 6, by decide, hp, hl⟩
    · exact ⟨9, 6, by decide, hp, hl⟩
    · exact ⟨2, 6, by decide, hp, hl⟩
  · rcases h7 with ⟨hl, (hp | hp) | (hp | hp)⟩
    · exact ⟨7, 7, by decide, hp, hl⟩
    · exact ⟨8, 7, by decide, hp, hl⟩
    · exact ⟨10, 7, by decide, hp, hl⟩
    · exact ⟨3, 7, by decide, hp, hl⟩
  · rcases h8 with ⟨hl, (hp | hp) | (hp | hp)⟩
    · exact ⟨8, 8, by decide, hp, hl⟩
    · exact ⟨9, 8, by decide, hp, hl⟩
    · exact ⟨11, 8, by decide, hp, hl⟩
    · exact ⟨4, 8, by decide, hp, hl⟩
  · rcases h9 with ⟨hl, (hp | hp) | (hp | hp)⟩
    · exact ⟨9, 9, by decide, hp, hl⟩
    · exact ⟨10, 9, by decide, hp, hl⟩
    · exact ⟨12, 9, by decide, hp, hl⟩
    · exact ⟨5, 9, by decide, hp, hl⟩
