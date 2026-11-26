import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21436_aux

open PEqualNP.CircuitLowerBounds

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem len (gs : List Gate) : ∀ w : List Bool, (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih => intro w; rw [List.foldl_cons, ih]; simp [stepW]; omega

theorem fold_getD_lt (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons, ih (stepW w g) i (by simp [stepW]; omega)]
    simp [stepW, List.getD, List.getElem?_append_left hi]

theorem fold_getD_gate (gs : List Gate) : ∀ (w : List Bool) (j : ℕ) (hj : j < gs.length),
    (∀ i ∈ (gs[j]).inputs, i < w.length + j) →
    (gs.foldl stepW w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (gs.foldl stepW w).getD i false) := by
  induction gs with
  | nil => intro w j hj; simp at hj
  | cons g gs ih =>
    intro w j hj hr
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero, List.foldl_cons, Nat.add_zero] at hr ⊢
      rw [fold_getD_lt gs (stepW w g) w.length (by simp [stepW])]
      have hm : (g.inputs.map fun i => (gs.foldl stepW (stepW w g)).getD i false) =
          g.inputs.map fun i => w.getD i false := by
        apply List.map_congr_left
        intro i hi
        rw [fold_getD_lt gs (stepW w g) i (by simp [stepW]; have := hr i hi; omega)]
        simp [stepW, List.getD, List.getElem?_append_left (hr i hi)]
      rw [hm]
      simp [stepW, List.getD]
    | succ j =>
      simp only [List.getElem_cons_succ, List.foldl_cons] at hr ⊢
      have hl : w.length + (j + 1) = (stepW w g).length + j := by simp [stepW]; omega
      rw [hl]
      exact ih (stepW w g) j (by simp at hj; omega) (fun i hi => by rw [← hl]; exact hr i hi)

open PEqualNP.MetaComplexity.NestedCover in
theorem core (m : ℕ) (C : Circuit) (S Rg : Finset ℕ) (tj : ℕ) (hRB : ReadsBack m C)
    (hrd : ∀ j < C.size, ∀ w ∈ (gateAt C j).inputs,
      (w ∈ S ∨ (m ≤ w ∧ w - m ∈ Rg ∧ w ≠ m + tj)) → j ∈ Rg)
    (x y : Fin m → Bool) (hxy : ∀ i : Fin m, (i : ℕ) ∉ S → x i = y i)
    (ht : (C.wires (List.ofFn x)).getD (m + tj) false = (C.wires (List.ofFn y)).getD (m + tj) false) :
    ∀ w, ¬ (w ∈ S ∨ (m ≤ w ∧ w - m ∈ Rg ∧ w ≠ m + tj)) →
      (C.wires (List.ofFn x)).getD w false = (C.wires (List.ofFn y)).getD w false := by
  have hW : ∀ z : Fin m → Bool, C.wires (List.ofFn z) = C.gates.foldl stepW (List.ofFn z) :=
    fun _ => rfl
  rw [hW, hW] at ht ⊢
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h1 : w < m
    · rw [fold_getD_lt _ _ _ (by simpa using h1), fold_getD_lt _ _ _ (by simpa using h1)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h1, dite_true, Option.getD_some]
      exact hxy ⟨w, h1⟩ fun h => hw (Or.inl h)
    · by_cases h2 : w = m + tj
      · rw [h2]; exact ht
      · by_cases h3 : w - m < C.gates.length
        · have hnR : w - m ∉ Rg := fun h => hw (Or.inr ⟨by omega, h, h2⟩)
          have hga : gateAt C (w - m) = C.gates[w - m] := by
            simp [gateAt, List.getD_eq_getElem?_getD, h3]
          have hr := hRB (w - m) h3
          rw [hga] at hr
          have kx := fold_getD_gate C.gates (List.ofFn x) (w - m) h3
            (by rw [List.length_ofFn]; exact hr)
          have ky := fold_getD_gate C.gates (List.ofFn y) (w - m) h3
            (by rw [List.length_ofFn]; exact hr)
          rw [List.length_ofFn, show m + (w - m) = w by omega] at kx ky
          rw [kx, ky]
          congr 1
          refine List.map_congr_left fun i hi => ih i (by have := hr i hi; omega) fun hb => ?_
          exact hnR (hrd (w - m) h3 i (by rw [hga]; exact hi) hb)
        · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_eq_none (by rw [len, List.length_ofFn]; omega),
            List.getElem?_eq_none (by rw [len, List.length_ofFn]; omega)]

end PEqualNP.Outside.L_meta_21436_aux

open PEqualNP.Outside.L_meta_21436_aux in
theorem PEqualNP.Outside.L_meta_21436 : ∀ (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (S Rg : Finset ℕ) (tj : ℕ),
  PEqualNP.MetaComplexity.NestedCover.ReadsBack m C → tj ∈ Rg → (∀ j ∈ Rg, j < C.size) →
  (∀ j < C.size, ∀ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
    (w ∈ S ∨ (m ≤ w ∧ w - m ∈ Rg ∧ w ≠ m + tj)) → j ∈ Rg) →
  C.output ∉ S → (∀ j ∈ Rg, j ≠ tj → C.output ≠ m + j) →
  ∃ G : Bool → (Fin m → Bool) → Bool,
    (∀ (c : Bool) (x y : Fin m → Bool), (∀ i : Fin m, (i : ℕ) ∉ S → x i = y i) → G c x = G c y) ∧
    ∀ x : Fin m → Bool,
      C.eval (List.ofFn x) = G ((C.wires (List.ofFn x)).getD (m + tj) false) x := by
  intro m C S Rg tj hRB _ _ hrd hoS hoR
  classical
  let P : Bool → (Fin m → Bool) → (Fin m → Bool) → Prop := fun c x z =>
    (∀ i : Fin m, (i : ℕ) ∉ S → x i = z i) ∧ (C.wires (List.ofFn z)).getD (m + tj) false = c
  refine ⟨fun c x => if h : ∃ z, P c x z then C.eval (List.ofFn h.choose) else false, ?_, ?_⟩
  · intro c x y hxy
    have e : P c x = P c y := by
      funext z
      refine propext ⟨fun h => ⟨fun i hi => (hxy i hi).symm.trans (h.1 i hi), h.2⟩,
        fun h => ⟨fun i hi => (hxy i hi).trans (h.1 i hi), h.2⟩⟩
    simp only [e]
  · intro x
    have hex : ∃ z, P ((C.wires (List.ofFn x)).getD (m + tj) false) x z := ⟨x, fun _ _ => rfl, rfl⟩
    show _ = dite _ _ _
    rw [dif_pos hex]
    have hc := hex.choose_spec
    refine core m C S Rg tj hRB hrd x _ hc.1 hc.2.symm C.output fun hb => ?_
    rcases hb with hb | ⟨h1, h2, h3⟩
    · exact hoS hb
    · exact hoR (C.output - m) h2 (fun e => h3 (by omega)) (by omega)
