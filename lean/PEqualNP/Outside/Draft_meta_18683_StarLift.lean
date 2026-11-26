import PEqualNP.Defs
theorem PEqualNP.Outside.Draft_meta_18683_StarLift : ∀ (z : Nat → Nat) (a : Nat) (p : Fin 28), (∀ j : Fin 18, ∃ i h : Fin (10 + j.val), z (10 + j.val) = (z i.val ||| z h.val) ∨ z (10 + j.val) = (z i.val &&& z h.val)) →
    ∃ w : Nat → Nat, w 0 = a ∧ (∀ i : Fin 10, w (i.val + 1) = z i.val) ∧
      w 31 = (z p.val ||| (a &&& (z 8 ||| z 9))) ∧ (∀ j : Fin 21, ∃ i h : Fin (11 + j.val), w (11 + j.val) = (w i.val ||| w h.val) ∨ w (11 + j.val) = (w i.val &&& w h.val)) := by
  intro z a p hrec
  let w : Nat → Nat := fun i =>
    if i = 0 then a else if i < 29 then z (i-1)
    else if i = 29 then z 8 ||| z 9
    else if i = 30 then a &&& (z 8 ||| z 9)
    else z p.val ||| (a &&& (z 8 ||| z 9))
  have shift (i : Nat) (h : i < 28) : w (i+1) = z i := by
    have hs : i+1 < 29 := by omega
    simp [w, hs]
  refine ⟨w, by simp [w], (fun i => shift i.val (by omega)), by simp [w], ?_⟩
  intro j
  by_cases hj : j.val < 18
  · obtain ⟨i,h,hi⟩ := hrec ⟨j.val,hj⟩
    have hiwire : i.val < 10+j.val := i.isLt
    have hhwire : h.val < 10+j.val := h.isLt
    refine ⟨⟨i.val+1, by omega⟩, ⟨h.val+1, by omega⟩, ?_⟩
    change w (11+j.val) = (w (i.val+1) ||| w (h.val+1)) ∨ w (11+j.val) = (w (i.val+1) &&& w (h.val+1))
    have hs : 11+j.val = (10+j.val)+1 := by omega
    rw [hs, shift _ (by omega), shift _ (by omega), shift _ (by omega)]
    exact hi
  · have casesj : j.val = 18 ∨ j.val = 19 ∨ j.val = 20 := by omega
    rcases casesj with h | h | h
    · refine ⟨⟨9,by omega⟩, ⟨10,by omega⟩, Or.inl ?_⟩
      simp [h, w]
    · refine ⟨⟨0,by omega⟩, ⟨29,by omega⟩, Or.inr ?_⟩
      simp [h, w]
    · refine ⟨⟨p.val+1,by omega⟩, ⟨30,by omega⟩, Or.inl ?_⟩
      change w (11+j.val) = (w (p.val+1) ||| w 30)
      rw [shift p.val p.isLt]
      simp [h, w]
