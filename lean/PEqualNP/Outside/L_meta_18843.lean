import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_18843 : ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj], (∀ (x3 x4 : Fin (26 : ℕ)), x1.Adj x3 x4 ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ (x3 = Fin.castAdd (13 : ℕ) x5 ∧ x4 = Fin.natAdd (13 : ℕ) x6 ∨ x4 = Fin.castAdd (13 : ℕ) x5 ∧ x3 = Fin.natAdd (13 : ℕ) x6)) → ∀ (x4 : Finset (Fin (26 : ℕ))), (∀ (x5 x6 : Fin (26 : ℕ)), x1.Adj x5 x6 → x5 ∈ x4 ∨ x6 ∈ x4) → (∃ (x6 : Fin (13 : ℕ)), Fin.castAdd (13 : ℕ) x6 ∈ x4) → (∃ (x7 : Fin (13 : ℕ)), Fin.natAdd (13 : ℕ) x7 ∈ x4) → (14 : ℕ) ≤ x4.card := by
  classical
  intro G _ hAdj S hcover hleft hright
  let left : Fin 13 → Fin 26 := Fin.castAdd 13
  let right : Fin 13 → Fin 26 := Fin.natAdd 13
  have edge (i j : Fin 13) (h : i = j ∨ i = j + 1) : G.Adj (left i) (right j) :=
    (hAdj _ _).mpr ⟨i, j, h.imp_right Or.inl, Or.inl ⟨rfl, rfl⟩⟩
  have hits (i : Fin 13) : left i ∈ S ∨ right i ∈ S := hcover _ _ (edge i i (Or.inl rfl))
  let pick (i : Fin 13) : Fin 26 := if left i ∈ S then left i else right i
  have pick_mem (i : Fin 13) : pick i ∈ S := by
    by_cases h : left i ∈ S
    · simp [pick, h]
    · simpa [pick, h] using (hits i).resolve_left h
  have pick_index (i : Fin 13) : (pick i).val % 13 = i.val := by
    have bound := i.isLt
    by_cases h : left i ∈ S
    · simp [pick, h, left, Nat.mod_eq_of_lt bound]
    · simp [pick, h, right, Nat.mod_eq_of_lt bound]
  have inj : Function.Injective pick := by
    intro a b h
    apply Fin.ext
    rw [← pick_index a, ← pick_index b, h]
  let chosen := Finset.univ.image pick
  have inc : chosen ⊆ S := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact pick_mem i
  have count : chosen.card = 13 := by
    simp [chosen, Finset.card_image_of_injective _ inj]
  by_contra! small
  have equal : chosen = S := Finset.eq_of_subset_of_card_le inc (by omega)
  have excludes (i : Fin 13) (li : left i ∈ S) : right i ∉ S := by
    intro ri
    rw [← equal] at ri
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp ri
    have idx := pick_index j
    rw [hj] at idx
    have bound := i.isLt
    have same : j = i := Fin.ext (by
      simpa [right, Nat.mod_eq_of_lt bound] using idx.symm)
    subst j
    simp [pick, li] at hj
    have hv := congrArg Fin.val hj
    change i.val = 13 + i.val at hv
    omega
  obtain ⟨start, hs⟩ := hleft
  have step (i : Fin 13) (hi : left i ∈ S) : left (i + 1) ∈ S :=
    (hcover _ _ (edge (i+1) i (Or.inr rfl))).resolve_right (excludes i hi)
  have all (k : ℕ) : left (start + Fin.ofNat 13 k) ∈ S := by
    induction k with
    | zero => simpa using hs
    | succ k ih =>
      have next : Fin.ofNat 13 (k+1) = Fin.ofNat 13 k + 1 := by
        apply Fin.ext
        change (k+1) % 13 = (k % 13 + 1) % 13
        omega
      rw [next, ← add_assoc]
      exact step _ ih
  obtain ⟨finish, hf⟩ := hright
  have cast_back : Fin.ofNat 13 (finish - start).val = finish - start := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt (finish - start).isLt
  have hfLeft := all (finish - start).val
  rw [cast_back, add_comm start, sub_add_cancel] at hfLeft
  exact excludes finish hfLeft hf
