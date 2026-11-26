import PEqualNP.Defs

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_meta_18860 : ∀ (x1 : Set (Set (Fin (26 : ℕ) → Bool))) (x2 : Finset (Set (Fin (26 : ℕ) → Bool))), (∀ x3 ∈ x2, x3 ∉ x1) → ∃ (x4 : List (Set (Fin (26 : ℕ) → Bool))), x4.Nodup ∧ x4.toFinset ⊆ x2 ∧ (∀ (x5 : ℕ) (x6 : Set (Fin (26 : ℕ) → Bool)), x4[x5]? = Option.some x6 → ∃ x8 ∈ x1 ∪ ↑(List.take x5 x4).toFinset, ∃ x9 ∈ x1 ∪ ↑(List.take x5 x4).toFinset, x6 = x8 ∩ x9 ∨ x6 = x8 ∪ x9) ∧ ∀ x5 ∈ x1 ∪ ↑x4.toFinset, ∀ x7 ∈ x1 ∪ ↑x4.toFinset, ∀ x9 ∈ x2, x9 = x5 ∩ x7 ∨ x9 = x5 ∪ x7 → x9 ∈ x1 ∪ ↑x4.toFinset := by
  classical
  intro B S
  induction S using Finset.strongInductionOn generalizing B with
  | _ S ih =>
    intro outside
    by_cases next : ∃ A ∈ S, ∃ U ∈ B, ∃ V ∈ B, A = U ∩ V ∨ A = U ∪ V
    · obtain ⟨A, aS, U, uB, V, vB, operation⟩ := next
      let B' : Set (Set (Fin 26 → Bool)) := B ∪ {A}
      have small : S.erase A ⊂ S := Finset.erase_ssubset aS
      have away : ∀ Z ∈ S.erase A, Z ∉ B' := by
        intro Z hz hB
        obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hz
        rcases hB with h | h
        · exact outside Z mem h
        · exact ne (Set.mem_singleton_iff.mp h)
      obtain ⟨L, nd, sub, steps, closed⟩ := ih (S.erase A) small B' away
      have lift (K : List (Set (Fin 26 → Bool))) :
          B ∪ (↑(A :: K).toFinset : Set (Set (Fin 26 → Bool))) =
          B' ∪ (↑K.toFinset : Set (Set (Fin 26 → Bool))) := by
        ext Z
        simp only [B', List.toFinset_cons, Finset.coe_insert, Set.mem_union,
          Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      refine ⟨A :: L, ?_, ?_, ?_, ?_⟩
      · apply List.nodup_cons.mpr
        refine ⟨?_, nd⟩
        intro mem
        exact (Finset.mem_erase.mp (sub (List.mem_toFinset.mpr mem))).1 rfl
      · intro Z hz
        rcases List.mem_cons.mp (List.mem_toFinset.mp hz) with rfl | h
        · exact aS
        · exact Finset.mem_of_mem_erase (sub (List.mem_toFinset.mpr h))
      · intro i Z hz
        cases i with
        | zero =>
          have eq : A = Z := Option.some.inj (by simpa using hz)
          subst Z
          exact ⟨U, Or.inl uB, V, Or.inl vB, operation⟩
        | succ i =>
          have get : L[i]? = some Z := by simpa using hz
          obtain ⟨X,hX,Y,hY,hXY⟩ := steps i Z get
          simp only [List.take_succ_cons, lift]
          exact ⟨X,hX,Y,hY,hXY⟩
      · rw [lift]
        intro X hX Y hY Z hz hZ
        by_cases eq : Z = A
        · subst Z
          exact Or.inl (Or.inr (Set.mem_singleton A))
        · exact closed X hX Y hY Z (Finset.mem_erase.mpr ⟨eq,hz⟩) hZ
    · refine ⟨[], by simp, by simp, ?_, ?_⟩
      · intro i Z hz
        simp at hz
      · simp only [List.toFinset_nil, Finset.coe_empty, Set.union_empty]
        intro X hX Y hY Z hz hZ
        exact False.elim (next ⟨Z,hz,X,hX,Y,hY,hZ⟩)
