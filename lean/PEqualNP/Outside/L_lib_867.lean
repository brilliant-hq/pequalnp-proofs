import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_867 : (∀ (k l : Nat) (hl : 0 < l), 5 ≤ l →
  ∀ (name : Fin l → Fin k), Function.Injective name →
  ∀ p : Equiv.Perm (Fin k), Function.Involutive p →
  let shift := fun (i : Fin l) (d : Nat) => (⟨(i.val+d) % l, Nat.mod_lt _ hl⟩ : Fin l)
  let edge := fun i j : Fin l => p (name i) = name j
  let near := Finset.univ.filter (fun i : Fin l => edge i (shift i 1))
  let skip := Finset.univ.filter (fun i : Fin l => edge i (shift i 2))
  let miss := Finset.univ.filter (fun i : Fin l =>
    ¬ (edge i (shift i 1) ∨ edge i (shift i 2) ∨ edge (shift i 1) (shift i 2)))
  let off := Finset.univ.filter (fun i : Fin l =>
    ¬ edge i (shift i 1) ∧ ¬ edge (shift i (l-1)) i)
  miss.card + 2*near.card + skip.card = l ∧
    miss.card + skip.card = off.card ∧
    (miss.card = 0 ↔ l % 2 = 0 ∧
      ∃ b : Fin 2, ∀ i : Fin l, edge i (shift i 1) ↔ i.val % 2 = b.val)) := by
  intro k l hl h5 name hinj p hp
  haveI : NeZero l := ⟨by omega⟩
  let ρ : Equiv.Perm (Fin l) := Equiv.addRight (1 : Fin l)
  have hρeq : ∀ i : Fin l, ρ i = i + 1 := by
    intro i; rfl
  have hρ2eq : ∀ i : Fin l, ρ (ρ i) = i + (2 : Fin l) := by
    intro i
    simp [ρ, Equiv.coe_addRight, add_assoc]
    apply Fin.ext
    simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 2 < l)]
  have h1 : ∀ i : Fin l, (⟨(i.val+1) % l, Nat.mod_lt _ hl⟩ : Fin l) = ρ i := by
    intro i
    ext
    simp [ρ, Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < l)]
  have h2 : ∀ i : Fin l, (⟨(i.val+2) % l, Nat.mod_lt _ hl⟩ : Fin l) = ρ (ρ i) := by
    intro i
    rw [hρ2eq]
    ext
    simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 2 < l)]
  have hm : ∀ i : Fin l, (⟨(i.val+(l-1)) % l, Nat.mod_lt _ hl⟩ : Fin l) = ρ.symm i := by
    intro i
    have h : ρ.symm i = i - 1 := by
      show i + (-1) = i - 1
      rw [sub_eq_add_neg]
    rw [h]
    ext
    simp only [Fin.val_sub, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < l)]
    rw [Nat.add_comm (i.val) (l-1)]
  dsimp only
  simp only [h1, h2, hm]
  let N : Fin l → Prop := fun i => p (name i) = name (ρ i)
  let S : Fin l → Prop := fun i => p (name i) = name (ρ (ρ i))
  let M : Fin l → Prop := fun i => ¬ (N i ∨ S i ∨ N (ρ i))
  let O : Fin l → Prop := fun i => ¬ N i ∧ ¬ (p (name (ρ.symm i)) = name i)
  change (Finset.univ.filter M).card + 2*(Finset.univ.filter N).card + (Finset.univ.filter S).card = l ∧
    (Finset.univ.filter M).card + (Finset.univ.filter S).card = (Finset.univ.filter O).card ∧
    ((Finset.univ.filter M).card = 0 ↔ l % 2 = 0 ∧
      ∃ b : Fin 2, ∀ i : Fin l, N i ↔ i.val % 2 = b.val)

  have h10 : (1 : Fin l) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < l)] at this
  have h20 : (2 : Fin l) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 2 < l)] at this
  have hρne : ∀ i : Fin l, ρ i ≠ i := by
    intro i h
    have h' : i + 1 = i + 0 := by simpa [hρeq] using h
    exact h10 (add_left_cancel h')
  have hρ2ne : ∀ i : Fin l, ρ (ρ i) ≠ i := by
    intro i h
    have h' : i + 2 = i + 0 := by simpa [hρ2eq] using h
    exact h20 (add_left_cancel h')

  have hNinv : ∀ i, N i → name i = p (name (ρ i)) := by
    intro i h
    have := congrArg p h
    rw [hp (name i)] at this
    exact this

  have hNS : ∀ i, ¬ (N i ∧ S i) := by
    intro i h
    obtain ⟨hN, hS⟩ := h
    have hname : name (ρ i) = name (ρ (ρ i)) := by rw [← hN, hS]
    have hi : i = ρ i := ρ.injective (hinj hname)
    exact hρne i hi.symm
  have hNN : ∀ i, ¬ (N i ∧ N (ρ i)) := by
    intro i h
    obtain ⟨hN, hN1⟩ := h
    have hp2 : name (ρ i) = p (name (ρ (ρ i))) := by
      have := congrArg p hN1
      rw [hp (name (ρ i))] at this
      exact this
    have hcomm : p (name i) = p (name (ρ (ρ i))) := by rw [hN, hp2]
    have hname : name i = name (ρ (ρ i)) := p.injective hcomm
    have hi : i = ρ (ρ i) := hinj hname
    exact hρ2ne i hi.symm
  have hSN : ∀ i, ¬ (S i ∧ N (ρ i)) := by
    intro i h
    obtain ⟨hS, hN1⟩ := h
    have hcomm : p (name i) = p (name (ρ i)) := by rw [hS, hN1]
    have hname : name i = name (ρ i) := p.injective hcomm
    have hi : i = ρ i := hinj hname
    exact hρne i hi.symm
  have htriple : ∀ i, ¬ (N i ∧ S i) ∧ ¬ (N i ∧ N (ρ i)) ∧ ¬ (S i ∧ N (ρ i)) :=
    fun i => ⟨hNS i, hNN i, hSN i⟩

  have hpt : ∀ i : Fin l,
      (if M i then 1 else 0) + (if N i then 1 else 0) +
        (if S i then 1 else 0) + (if N (ρ i) then 1 else 0) = 1 := by
    intro i
    by_cases hN : N i
    · have hS : ¬ S i := fun h => (htriple i).1 ⟨hN, h⟩
      have hN1 : ¬ N (ρ i) := fun h => (htriple i).2.1 ⟨hN, h⟩
      have hM : ¬ M i := by simp [M, hN]
      simp [hN, hS, hN1, hM]
    · by_cases hS : S i
      · have hN1 : ¬ N (ρ i) := fun h => (htriple i).2.2 ⟨hS, h⟩
        have hM : ¬ M i := by simp [M, hS]
        simp [hN, hS, hN1, hM]
      · by_cases hN1 : N (ρ i)
        · have hM : ¬ M i := by simp [M, hN1]
          simp [hN, hS, hN1, hM]
        · have hM : M i := by simp [M, hN, hS, hN1]
          simp [hN, hS, hN1, hM]
  have hsum : (∑ i : Fin l, ((if M i then 1 else 0) + (if N i then 1 else 0) +
        (if S i then 1 else 0) + (if N (ρ i) then 1 else 0))) = ∑ i : Fin l, (1 : Nat) := by
    apply Finset.sum_congr rfl
    intro i _
    exact hpt i
  have hMc : (Finset.univ.filter M).card = ∑ i : Fin l, (if M i then 1 else 0) :=
    (Finset.sum_boole M Finset.univ).symm
  have hNc : (Finset.univ.filter N).card = ∑ i : Fin l, (if N i then 1 else 0) :=
    (Finset.sum_boole N Finset.univ).symm
  have hSc : (Finset.univ.filter S).card = ∑ i : Fin l, (if S i then 1 else 0) :=
    (Finset.sum_boole S Finset.univ).symm
  have hOc : (Finset.univ.filter O).card = ∑ i : Fin l, (if O i then 1 else 0) :=
    (Finset.sum_boole O Finset.univ).symm
  have hshift1 : (∑ i : Fin l, (if N (ρ i) then 1 else 0)) =
      ∑ i : Fin l, (if N i then 1 else 0) :=
    Equiv.sum_comp ρ (fun i : Fin l => if N i then 1 else 0)
  have hclaim1 : (Finset.univ.filter M).card + 2*(Finset.univ.filter N).card +
      (Finset.univ.filter S).card = l := by
    have h := hsum
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at h
    rw [hshift1, ← hMc, ← hNc, ← hSc] at h
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h
    omega

  have hOtriple : ∀ i, ¬ (N i ∧ N (ρ.symm i)) := by
    intro i h
    exact hNN (ρ.symm i) ⟨h.2, by simpa using h.1⟩
  have hOiff : ∀ i, O i ↔ ¬ N i ∧ ¬ N (ρ.symm i) := by
    intro i
    simp [O, N, Equiv.apply_symm_apply]
  have hOpt : ∀ i : Fin l,
      (if O i then 1 else 0) + (if N i then 1 else 0) + (if N (ρ.symm i) then 1 else 0) = 1 := by
    intro i
    by_cases hN : N i
    · have hNs : ¬ N (ρ.symm i) := fun h => hOtriple i ⟨hN, h⟩
      have hO' : ¬ O i := by
        rw [hOiff]
        intro h
        exact h.1 hN
      simp [hN, hNs, hO']
    · by_cases hNs : N (ρ.symm i)
      · have hO' : ¬ O i := by
          rw [hOiff]
          intro h
          exact h.2 hNs
        simp [hN, hNs, hO']
      · have hO' : O i := by rw [hOiff]; exact ⟨hN, hNs⟩
        simp [hN, hNs, hO']
  have hsumO : (∑ i : Fin l, ((if O i then 1 else 0) + (if N i then 1 else 0) +
        (if N (ρ.symm i) then 1 else 0))) = ∑ i : Fin l, (1 : Nat) := by
    apply Finset.sum_congr rfl
    intro i _
    exact hOpt i
  have hshiftm : (∑ i : Fin l, (if N (ρ.symm i) then 1 else 0)) =
      ∑ i : Fin l, (if N i then 1 else 0) :=
    Equiv.sum_comp ρ.symm (fun i : Fin l => if N i then 1 else 0)
  have hOff : (Finset.univ.filter O).card + 2*(Finset.univ.filter N).card = l := by
    have h := hsumO
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h
    rw [hshiftm, ← hOc, ← hNc] at h
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h
    omega
  have hclaim2 : (Finset.univ.filter M).card + (Finset.univ.filter S).card =
      (Finset.univ.filter O).card := by omega

  refine ⟨hclaim1, hclaim2, ?_⟩
  constructor
  · intro hm
    have hMfalse : ∀ i, ¬ M i := by
      intro i hi
      have hmem : i ∈ Finset.univ.filter M := by simp [hi]
      have hpos : 0 < (Finset.univ.filter M).card := Finset.card_pos.mpr ⟨i, hmem⟩
      have hm' : (Finset.univ.filter M).card = 0 := hm
      omega
    have h30 : (3 : Fin l) ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      simp [Nat.mod_eq_of_lt (by omega : 3 < l)] at this
    have h40 : (4 : Fin l) ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      simp [Nat.mod_eq_of_lt (by omega : 4 < l)] at this
    have h12 : (1 : Fin l) + 2 = 3 := by
      ext
      simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < l),
        Nat.mod_eq_of_lt (by omega : 2 < l), Nat.mod_eq_of_lt (by omega : 3 < l)]
    have h21 : (2 : Fin l) + 1 = 3 := by
      ext
      simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 2 < l),
        Nat.mod_eq_of_lt (by omega : 3 < l)]
    have h22 : (2 : Fin l) + 2 = 4 := by
      ext
      simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 2 < l),
        Nat.mod_eq_of_lt (by omega : 4 < l)]
    have hE1 : ∀ j, ¬ (S j ∧ N (ρ (ρ j))) := by
      intro j h
      obtain ⟨hS, hN2⟩ := h
      have hN2p : name (ρ (ρ j)) = p (name (ρ (ρ (ρ j)))) := by
        have := congrArg p hN2
        rw [hp (name (ρ (ρ j)))] at this
        exact this
      have hcomm : p (name j) = p (name (ρ (ρ (ρ j)))) := by rw [hS, hN2p]
      have hname : name j = name (ρ (ρ (ρ j))) := p.injective hcomm
      have hj : j = ρ (ρ (ρ j)) := hinj hname
      have hρ3 : ρ (ρ (ρ j)) = j + 3 := by
        calc ρ (ρ (ρ j)) = ρ (ρ j) + 1 := hρeq (ρ (ρ j))
          _ = (j + 2) + 1 := by rw [hρ2eq j]
          _ = j + (2 + 1) := add_assoc _ _ _
          _ = j + 3 := by rw [h21]
      rw [hρ3] at hj
      have h3 : (3 : Fin l) = 0 := by
        have h' : j + 3 = j + 0 := by simpa using hj.symm
        exact add_left_cancel h'
      exact h30 h3
    have hE2 : ∀ j, ¬ (N (ρ.symm j) ∧ S j) := by
      intro j h
      obtain ⟨hN, hS⟩ := h
      have hN' : p (name (ρ.symm j)) = name j := by
        simpa [N, Equiv.apply_symm_apply] using hN
      have hSp : name j = p (name (ρ (ρ j))) := by
        have := congrArg p hS
        rw [hp (name j)] at this
        exact this
      have hcomm : p (name (ρ.symm j)) = p (name (ρ (ρ j))) := by rw [hN', hSp]
      have hname : name (ρ.symm j) = name (ρ (ρ j)) := p.injective hcomm
      have hj : ρ.symm j = ρ (ρ j) := hinj hname
      have hjeq : j = j + 3 := by
        have h1 : ρ.symm j = j - 1 := by
          show j + (-1) = j - 1
          rw [sub_eq_add_neg]
        have h2 : ρ (ρ j) = j + 2 := hρ2eq j
        rw [h1, h2] at hj
        have h := congrArg (fun x : Fin l => x + 1) hj
        rw [sub_add_cancel] at h
        rw [add_assoc, h21] at h
        exact h
      have h3 : (3 : Fin l) = 0 := by
        have h' : j + 3 = j + 0 := by simpa using hjeq.symm
        exact add_left_cancel h'
      exact h30 h3
    have hE3 : ∀ j, ¬ (S j ∧ S (ρ (ρ j))) := by
      intro j h
      obtain ⟨hS, hS2⟩ := h
      have hS2p : name (ρ (ρ j)) = p (name (ρ (ρ (ρ (ρ j))))) := by
        have := congrArg p hS2
        rw [hp (name (ρ (ρ j)))] at this
        exact this
      have hcomm : p (name j) = p (name (ρ (ρ (ρ (ρ j))))) := by rw [hS, hS2p]
      have hname : name j = name (ρ (ρ (ρ (ρ j)))) := p.injective hcomm
      have hj : j = ρ (ρ (ρ (ρ j))) := hinj hname
      have hρ4 : ρ (ρ (ρ (ρ j))) = j + 4 := by
        calc ρ (ρ (ρ (ρ j))) = ρ (ρ j) + 2 := hρ2eq (ρ (ρ j))
          _ = (j + 2) + 2 := by rw [hρ2eq j]
          _ = j + (2 + 2) := add_assoc _ _ _
          _ = j + 4 := by rw [h22]
      rw [hρ4] at hj
      have h4 : (4 : Fin l) = 0 := by
        have h' : j + 4 = j + 0 := by simpa using hj.symm
        exact add_left_cancel h'
      exact h40 h4
    have hcover : ∀ v, N v ∨ N (ρ.symm v) := by
      intro v
      by_contra hv
      push_neg at hv
      have hv0 : ¬ N v := hv.1
      have hv1 : ¬ N (ρ.symm v) := hv.2
      have hS1 : S (ρ.symm v) := by
        by_contra hS
        exact hMfalse (ρ.symm v) (by
          simp [M, hv1, hS, hv0, Equiv.apply_symm_apply])
      have hNv1 : ¬ N (ρ v) := by
        intro hN
        exact hE1 (ρ.symm v) ⟨hS1, by simpa [Equiv.apply_symm_apply] using hN⟩
      have hSv : S v := by
        by_contra hS
        exact hMfalse v (by simp [M, hv0, hS, hNv1])
      have hNvm2 : ¬ N (ρ.symm (ρ.symm v)) := by
        intro hN
        exact hE2 (ρ.symm v) ⟨hN, hS1⟩
      have hSvm2 : S (ρ.symm (ρ.symm v)) := by
        by_contra hS
        exact hMfalse (ρ.symm (ρ.symm v)) (by
          simp [M, hNvm2, hS, hv1, Equiv.apply_symm_apply])
      exact hE3 (ρ.symm (ρ.symm v)) ⟨hSvm2, by simpa [Equiv.apply_symm_apply] using hSv⟩
    have hnear : ∀ i, N i ∨ N (ρ i) := by
      intro i
      rcases hcover (ρ i) with h | h
      · exact Or.inr h
      · exact Or.inl (by simpa using h)
    have halt : ∀ i, N (ρ i) ↔ ¬ N i := by
      intro i
      constructor
      · intro h hi
        exact hNN i ⟨hi, h⟩
      · intro hi
        exact (hnear i).resolve_left hi

    have h2near : 2 * (Finset.univ.filter N).card = l := by
      have hpt : ∀ v : Fin l,
          (if N v then 1 else 0) + (if N (ρ.symm v) then 1 else 0) = 1 := by
        intro v
        by_cases hN : N v
        · have hNs : ¬ N (ρ.symm v) := fun h => hOtriple v ⟨hN, h⟩
          simp [hN, hNs]
        · have hNs : N (ρ.symm v) := (hcover v).resolve_left hN
          simp [hN, hNs]
      have hsum2 : (∑ v : Fin l, ((if N v then 1 else 0) +
          (if N (ρ.symm v) then 1 else 0))) = ∑ v : Fin l, (1 : Nat) := by
        apply Finset.sum_congr rfl
        intro v _
        exact hpt v
      rw [Finset.sum_add_distrib] at hsum2
      rw [hshiftm, ← hNc] at hsum2
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
        mul_one] at hsum2
      omega
    have hl2 : l % 2 = 0 := by omega
    refine ⟨hl2, ?_⟩
    have hparity : ∀ n (hn : n < l),
        N (⟨n, hn⟩ : Fin l) ↔ (n % 2 = 0 ↔ N 0) := by
      intro n
      induction n with
      | zero =>
        intro hn
        simp
      | succ n ih =>
        intro hn
        have hn' : n < l := by omega
        have hρn : (⟨n+1, hn⟩ : Fin l) = ρ (⟨n, hn'⟩ : Fin l) := by
          ext
          simp [ρ, Equiv.coe_addRight, Fin.val_add, Nat.mod_eq_of_lt hn]
        rw [hρn, halt, ih hn']
        have hR : ((n + 1) % 2 = 0) ↔ ¬ (n % 2 = 0) := by omega
        rw [hR]
        tauto
    by_cases h0 : N 0
    · refine ⟨0, ?_⟩
      intro i
      have hi := hparity i.val i.isLt
      have hii : (⟨i.val, i.isLt⟩ : Fin l) = i := rfl
      rw [hii] at hi
      simpa [h0] using hi
    · refine ⟨1, ?_⟩
      intro i
      have hi := hparity i.val i.isLt
      have hii : (⟨i.val, i.isLt⟩ : Fin l) = i := rfl
      rw [hii] at hi
      rw [hi]
      constructor
      · intro h
        by_contra h1
        have hz : i.val % 2 = 0 := by omega
        exact h0 (h.mp hz)
      · intro h1
        constructor
        · intro hz
          omega
        · intro hN0
          exact absurd hN0 h0
  · rintro ⟨hl2, b, hb⟩
    have hbval : b.val = 0 ∨ b.val = 1 := by omega
    have hNi_all : ∀ i, N i ∨ N (ρ i) := by
      intro i
      by_cases h : i.val % 2 = b.val
      · exact Or.inl ((hb i).mpr h)
      · right
        apply (hb (ρ i)).mpr
        have hρval : (ρ i).val = (i.val + 1) % l := by
          simp [ρ, Equiv.coe_addRight, Fin.val_add]
        rw [hρval]
        have hmod : ((i.val + 1) % l) % 2 = (i.val + 1) % 2 :=
          Nat.mod_mod_of_dvd _ (by omega : 2 ∣ l)
        rw [hmod]
        omega
    have hempty : Finset.univ.filter M = ∅ := by
      apply Finset.filter_false_of_mem
      intro i _
      intro hM
      exact hM ((hNi_all i).elim (fun h => Or.inl h) (fun h => Or.inr (Or.inr h)))
    change (Finset.univ.filter M).card = 0
    rw [hempty]
    simp
