import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18430_aux

open PEqualNP.CircuitLowerBounds PEqualNP.BlindGate

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem step_getD_lt (w : List Bool) (g : Gate) {k : ℕ} (hk : k < w.length) :
    (step w g).getD k false = w.getD k false := by
  simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem step_getD_self (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
    Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

theorem step_getD_gt (w : List Bool) (g : Gate) {k : ℕ} (hk : w.length < k) :
    (step w g).getD k false = false := by
  have hle : (step w g).length ≤ k := by simp [step]; omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle, Option.getD_none]

theorem foldl_mono_no2 (gs : List Gate)
    (hao : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hno2 : ∀ g ∈ gs, (2 : ℕ) ∉ g.inputs)
    (W1 W2 : List Bool)
    (hlen : W1.length = W2.length)
    (hmono : ∀ k, k ≠ 2 → W1.getD k false = true → W2.getD k false = true) :
    ∀ k, k ≠ 2 → (gs.foldl step W1).getD k false = true →
      (gs.foldl step W2).getD k false = true := by
  induction gs generalizing W1 W2 with
  | nil => exact hmono
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hao g (List.mem_cons_self ..)
    have hgn : (2 : ℕ) ∉ g.inputs := hno2 g (List.mem_cons_self ..)
    apply ih (fun g' hg' => hao g' (List.mem_cons_of_mem _ hg'))
      (fun g' hg' => hno2 g' (List.mem_cons_of_mem _ hg'))
      (step W1 g) (step W2 g) (by simp [step, hlen])
    intro k hk2 hk
    rcases lt_trichotomy k W1.length with hlt | rfl | hgt
    · rw [step_getD_lt W1 g hlt] at hk
      rw [step_getD_lt W2 g (by rw [← hlen]; exact hlt)]
      exact hmono k hk2 hk
    · rw [step_getD_self W1 g] at hk
      rw [hlen, step_getD_self W2 g]
      rcases hg with hand | hor
      · rw [hand] at hk ⊢
        simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hk ⊢
        rintro _ ⟨j, hj, rfl⟩
        have hj2 : j ≠ 2 := fun h => hgn (h ▸ hj)
        exact hmono j hj2 (hk _ ⟨j, hj, rfl⟩)
      · rw [hor] at hk ⊢
        simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hk ⊢
        obtain ⟨_, ⟨j, hj, rfl⟩, h1⟩ := hk
        have hj2 : j ≠ 2 := fun h => hgn (h ▸ hj)
        exact ⟨true, ⟨j, hj, hmono j hj2 h1⟩, rfl⟩
    · rw [step_getD_gt W1 g hgt] at hk
      cases hk

theorem main :
    ∀ (x1 : Circuit), PEqualNP.TopForm.IsAO2 14 x1 →
      (∀ x3 ∈ x1.gates, (2 : ℕ) ∉ x3.inputs) →
      ∀ (x4 : ℕ), x4 ≠ 2 →
      ∀ (x6 x7 : Fin 14 → Bool),
        (∀ (x8 : Fin 14), x8 ≠ (2 : Fin 14) → x6 x8 = true → x7 x8 = true) →
        wireValue x1 14 x6 x4 = true →
        wireValue x1 14 x7 x4 = true := by
  intro C hAO hNo2 w hw x y hle hx
  apply foldl_mono_no2 C.gates hAO.1 hNo2 (List.ofFn x) (List.ofFn y) (by simp)
  · intro k hk2 hk
    by_cases hlt : k < 14
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte,
        Option.getD_some] at hk ⊢
      exact hle ⟨k, hlt⟩ (fun h => hk2 (congrArg Fin.val h)) hk
    · exfalso
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hk
      simp at hk
  · exact hw
  · exact hx

end PEqualNP.Outside.L_meta_18430_aux

theorem PEqualNP.Outside.L_meta_18430 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x3 ∈ x1.gates, (2 : ℕ) ∉ x3.inputs) → ∀ (x4 : ℕ), x4 ≠ (2 : ℕ) → ∀ (x6 x7 : Fin (14 : ℕ) → Bool), (∀ (x8 : Fin (14 : ℕ)), x8 ≠ (2 : Fin (14 : ℕ)) → x6 x8 = Bool.true → x7 x8 = Bool.true) → PEqualNP.BlindGate.wireValue x1 (14 : ℕ) x6 x4 = Bool.true → PEqualNP.BlindGate.wireValue x1 (14 : ℕ) x7 x4 = Bool.true) :=
  PEqualNP.Outside.L_meta_18430_aux.main
