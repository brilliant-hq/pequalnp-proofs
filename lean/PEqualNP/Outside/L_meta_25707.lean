import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25707_aux

private theorem hall_perm_of_const_sums {n b : ℕ} (hb : 0 < b)
    (M : Fin n → Fin n → ℕ)
    (hrow : ∀ i : Fin n, ∑ j : Fin n, M i j = b)
    (hcol : ∀ j : Fin n, ∑ i : Fin n, M i j = b) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin n, 0 < M i (σ i) := by
  let t : Fin n → Finset (Fin n) := fun i => Finset.univ.filter (fun j => 0 < M i j)
  have hhall : ∀ s : Finset (Fin n), s.card ≤ (s.biUnion t).card := by
    intro s
    have h1 : s.card * b = ∑ i ∈ s, ∑ j ∈ s.biUnion t, M i j := by
      calc s.card * b = ∑ _i ∈ s, b := by rw [Finset.sum_const, smul_eq_mul]
        _ = ∑ i ∈ s, ∑ j : Fin n, M i j := Finset.sum_congr rfl fun i _ => (hrow i).symm
        _ = ∑ i ∈ s, ∑ j ∈ s.biUnion t, M i j := by
          refine Finset.sum_congr rfl fun i hi => ?_
          symm
          refine Finset.sum_subset (Finset.subset_univ _) fun j _ hnot => ?_
          by_contra hnz
          apply hnot
          exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.pos_of_ne_zero hnz⟩⟩
    have h2 : ∑ i ∈ s, ∑ j ∈ s.biUnion t, M i j ≤ (s.biUnion t).card * b := by
      calc ∑ i ∈ s, ∑ j ∈ s.biUnion t, M i j
          = ∑ j ∈ s.biUnion t, ∑ i ∈ s, M i j := Finset.sum_comm
        _ ≤ ∑ j ∈ s.biUnion t, ∑ i : Fin n, M i j :=
            Finset.sum_le_sum fun j _ => Finset.sum_le_sum_of_subset (Finset.subset_univ _)
        _ = ∑ _j ∈ s.biUnion t, b := Finset.sum_congr rfl fun j _ => hcol j
        _ = (s.biUnion t).card * b := by rw [Finset.sum_const, smul_eq_mul]
    exact Nat.le_of_mul_le_mul_right (h1.trans_le h2) hb
  rcases (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hhall with ⟨f, hinj, hmem⟩
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), fun i => ?_⟩
  exact (Finset.mem_filter.mp (hmem i)).2

private def suppCard {n : ℕ} (M : Fin n → Fin n → ℕ) : ℕ :=
  (Finset.univ.filter (fun p : Fin n × Fin n => 0 < M p.1 p.2)).card

private theorem birkhoff_peel {n : ℕ} (hn : 0 < n) :
    ∀ k : ℕ, ∀ (b : ℕ) (M : Fin n → Fin n → ℕ),
      suppCard M ≤ k →
      (∀ i : Fin n, ∑ j : Fin n, M i j = b) →
      (∀ j : Fin n, ∑ i : Fin n, M i j = b) →
      ∃ L : List (Equiv.Perm (Fin n) × ℕ),
        (∀ p ∈ L, 0 < p.2) ∧
        (∀ i j : Fin n, M i j = (L.map (fun p => if j = p.1 i then p.2 else 0)).sum) ∧
        (∀ idx : Fin L.length, ∃ i0 : Fin n, ∀ idx2 : Fin L.length,
          idx.val < idx2.val → (L.get idx2).1 i0 ≠ (L.get idx).1 i0) := by
  intro k
  induction k with
  | zero =>
    intro b M hsupp hrow _
    have hzero : ∀ i j : Fin n, M i j = 0 := by
      intro i j
      by_contra hnz
      have hmem : (i, j) ∈ Finset.univ.filter (fun p : Fin n × Fin n => 0 < M p.1 p.2) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.pos_of_ne_zero hnz⟩
      have hpos : 0 < suppCard M := Finset.card_pos.mpr ⟨(i, j), hmem⟩
      omega
    exact ⟨[], by simp, fun i j => by simp [hzero i j], fun idx => by exact absurd idx.isLt (by simp)⟩
  | succ k ih =>
    intro b M hsupp hrow hcol
    by_cases hb : b = 0
    · subst hb
      have hzero : ∀ i j : Fin n, M i j = 0 := by
        intro i j
        have h1 := hrow i
        have hle : M i j ≤ ∑ j' : Fin n, M i j' :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
        omega
      exact ⟨[], by simp, fun i j => by simp [hzero i j], fun idx => by exact absurd idx.isLt (by simp)⟩
    · have hbpos : 0 < b := Nat.pos_of_ne_zero hb
      rcases hall_perm_of_const_sums hbpos M hrow hcol with ⟨σ, hσ⟩
      have hne : (Finset.univ.image (fun i : Fin n => M i (σ i))).Nonempty :=
        ⟨M ⟨0, hn⟩ (σ ⟨0, hn⟩), Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩⟩
      let h : ℕ := (Finset.univ.image (fun i : Fin n => M i (σ i))).min' hne
      have hmin_mem : h ∈ Finset.univ.image (fun i : Fin n => M i (σ i)) := Finset.min'_mem _ hne
      rcases Finset.mem_image.mp hmin_mem with ⟨i0, _, hi0⟩
      have hle : ∀ i : Fin n, h ≤ M i (σ i) := fun i =>
        Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      have hhpos : 0 < h := by rw [← hi0]; exact hσ i0
      let M' : Fin n → Fin n → ℕ := fun i j => if j = σ i then M i j - h else M i j
      have hrow' : ∀ i : Fin n, ∑ j : Fin n, M' i j = b - h := by
        intro i
        have hadd : (∑ j : Fin n, M' i j) + h = ∑ j : Fin n, M i j := by
          have hsplit1 := Finset.add_sum_erase Finset.univ (fun j => M' i j) (Finset.mem_univ (σ i))
          have hsplit2 := Finset.add_sum_erase Finset.univ (fun j => M i j) (Finset.mem_univ (σ i))
          have herase : ∑ j ∈ Finset.univ.erase (σ i), M' i j = ∑ j ∈ Finset.univ.erase (σ i), M i j := by
            refine Finset.sum_congr rfl fun j hj => ?_
            have hne' : j ≠ σ i := (Finset.mem_erase.mp hj).1
            simp only [M', hne', ↓reduceIte]
          have hdiag : M' i (σ i) + h = M i (σ i) := by
            simp only [M', ↓reduceIte]
            exact Nat.sub_add_cancel (hle i)
          rw [← hsplit1, ← hsplit2, herase]
          omega
        rw [hrow i] at hadd
        omega
      have hcol' : ∀ j : Fin n, ∑ i : Fin n, M' i j = b - h := by
        intro j
        have hadd : (∑ i : Fin n, M' i j) + h = ∑ i : Fin n, M i j := by
          have hsplit1 := Finset.add_sum_erase Finset.univ (fun i => M' i j) (Finset.mem_univ (σ.symm j))
          have hsplit2 := Finset.add_sum_erase Finset.univ (fun i => M i j) (Finset.mem_univ (σ.symm j))
          have herase : ∑ i ∈ Finset.univ.erase (σ.symm j), M' i j =
              ∑ i ∈ Finset.univ.erase (σ.symm j), M i j := by
            refine Finset.sum_congr rfl fun i hi => ?_
            have hne' : j ≠ σ i := fun heq => (Finset.mem_erase.mp hi).1 (by rw [heq, Equiv.symm_apply_apply])
            simp only [M', hne', ↓reduceIte]
          have hdiag : M' (σ.symm j) j + h = M (σ.symm j) j := by
            simp only [M', Equiv.apply_symm_apply, ↓reduceIte]
            have hle' := hle (σ.symm j)
            rw [Equiv.apply_symm_apply] at hle'
            exact Nat.sub_add_cancel hle'
          rw [← hsplit1, ← hsplit2, herase]
          omega
        rw [hcol j] at hadd
        omega
      have hsupp_lt : suppCard M' < suppCard M := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨?_, ?_⟩
        · intro ⟨i, j⟩ hm
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
          dsimp only [M'] at hm
          split_ifs at hm <;> omega
        · intro heq
          have hmemM : (i0, σ i0) ∈ Finset.univ.filter (fun p : Fin n × Fin n => 0 < M p.1 p.2) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ i0⟩
          rw [← heq, Finset.mem_filter] at hmemM
          have h0 : M' i0 (σ i0) = 0 := by simp [M', hi0]
          have hpos := hmemM.2
          dsimp only at hpos
          omega
      rcases ih (b - h) M' (by omega) hrow' hcol' with ⟨L', hpos', hsum', hpiv'⟩
      refine ⟨(σ, h) :: L', ?_, ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact hhpos
        · exact hpos' p hp'
      · intro i j
        simp only [List.map_cons, List.sum_cons]
        rw [← hsum' i j]
        dsimp only [M']
        split_ifs with heq
        · subst heq; exact (Nat.add_sub_of_le (hle i)).symm
        · omega
      · intro idx
        cases hidx : idx.val with
        | zero =>
          refine ⟨i0, fun idx2 hlt => ?_⟩
          have hidx2_pos : 0 < idx2.val := by omega
          let idx2' : Fin L'.length := ⟨idx2.val - 1, by have := idx2.isLt; simp at this; omega⟩
          have hget2 : ((σ, h) :: L').get idx2 = L'.get idx2' := by
            have h1 : idx2 = idx2'.succ := Fin.ext (by dsimp [idx2']; omega)
            rw [h1]; rfl
          have hget0 : ((σ, h) :: L').get idx = (σ, h) := by
            have h1 : idx = ⟨0, by simp⟩ := Fin.ext hidx
            rw [h1]; rfl
          rw [hget2, hget0]
          intro hbad
          have hM0 : M' i0 (σ i0) = 0 := by simp [M', hi0]
          rw [hsum' i0 (σ i0)] at hM0
          have hmem_l : L'.get idx2' ∈ L' := List.get_mem _ _
          have hpos_l : 0 < (L'.get idx2').2 := hpos' _ hmem_l
          have hmem_map : (L'.get idx2').2 ∈ L'.map (fun p => if σ i0 = p.1 i0 then p.2 else 0) := by
            refine List.mem_map.mpr ⟨L'.get idx2', hmem_l, ?_⟩
            dsimp only at hbad
            simp only [hbad, ↓reduceIte]
          have hle_sum : (L'.get idx2').2 ≤ (L'.map (fun p => if σ i0 = p.1 i0 then p.2 else 0)).sum :=
            List.le_sum_of_mem hmem_map
          omega
        | succ m =>
          let idx' : Fin L'.length := ⟨m, by have := idx.isLt; simp at this; omega⟩
          rcases hpiv' idx' with ⟨i1, hi1⟩
          refine ⟨i1, fun idx2 hlt => ?_⟩
          let idx2' : Fin L'.length := ⟨idx2.val - 1, by have := idx2.isLt; simp at this; omega⟩
          have hget1 : ((σ, h) :: L').get idx = L'.get idx' := by
            have h1 : idx = idx'.succ := Fin.ext (by dsimp [idx']; omega)
            rw [h1]; rfl
          have hget2 : ((σ, h) :: L').get idx2 = L'.get idx2' := by
            have h1 : idx2 = idx2'.succ := Fin.ext (by dsimp [idx2']; omega)
            rw [h1]; rfl
          rw [hget1, hget2]
          exact hi1 idx2' (by dsimp [idx', idx2']; omega)

private def projMap (n : ℕ) (hn : 0 < n) :
    ((Fin n × Fin n) → ℚ) →ₗ[ℚ] ((Fin (n - 1) × Fin (n - 1) → ℚ) × ℚ) where
  toFun := fun A =>
    (fun p => A (⟨p.1.val, by have := p.1.isLt; omega⟩, ⟨p.2.val, by have := p.2.isLt; omega⟩),
     ∑ j : Fin n, A (⟨0, hn⟩, j))
  map_add' := fun A B => by
    ext p
    · rfl
    · simp [Finset.sum_add_distrib]
  map_smul' := fun r A => by
    ext p
    · rfl
    · simp [Finset.mul_sum]

private theorem birkhoff_len_le {n : ℕ} (hn : 0 < n) (L : List (Equiv.Perm (Fin n) × ℕ))
    (hpiv : ∀ idx : Fin L.length, ∃ i0 : Fin n, ∀ idx2 : Fin L.length,
      idx.val < idx2.val → (L.get idx2).1 i0 ≠ (L.get idx).1 i0) :
    L.length ≤ (n - 1) ^ 2 + 1 := by
  let P : Fin L.length → (Fin n × Fin n → ℚ) :=
    fun k p => if p.2 = (L.get k).1 p.1 then 1 else 0
  have hP_row : ∀ (k : Fin L.length) (i : Fin n), ∑ j : Fin n, P k (i, j) = 1 := by
    intro k i
    simp [P]
  have hP_col : ∀ (k : Fin L.length) (j : Fin n), ∑ i : Fin n, P k (i, j) = 1 := by
    intro k j
    have heq : ∀ i : Fin n, P k (i, j) = if i = (L.get k).1.symm j then 1 else 0 := by
      intro i
      dsimp only [P]
      by_cases h : i = (L.get k).1.symm j
      · subst h; simp only [Equiv.apply_symm_apply, ↓reduceIte]
      · have h2 : j ≠ (L.get k).1 i := fun he => h (by rw [he, Equiv.symm_apply_apply])
        simp only [h, h2, ↓reduceIte]
    simp only [heq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hli : LinearIndependent ℚ (fun k : Fin L.length => projMap n hn (P k)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hsum
    let A : Fin n × Fin n → ℚ := ∑ k : Fin L.length, c k • P k
    have hproj0 : projMap n hn A = 0 := by
      dsimp only [A]
      rw [map_sum]
      simpa only [map_smul] using hsum
    have hA_row : ∀ i : Fin n, ∑ j : Fin n, A (i, j) = ∑ k : Fin L.length, c k := by
      intro i
      dsimp only [A]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.mul_sum, hP_row k i, mul_one]
    have hA_col : ∀ j : Fin n, ∑ i : Fin n, A (i, j) = ∑ k : Fin L.length, c k := by
      intro j
      dsimp only [A]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.mul_sum, hP_col k j, mul_one]
    have hsumc : ∑ k : Fin L.length, c k = 0 := by
      have h2 := congrArg Prod.snd hproj0
      change ∑ j : Fin n, A (⟨0, hn⟩, j) = 0 at h2
      rw [hA_row ⟨0, hn⟩] at h2
      exact h2
    have hA_sub : ∀ (i j : Fin n), i.val < n - 1 → j.val < n - 1 → A (i, j) = 0 := by
      intro i j hi hj
      have h1 := congrFun (congrArg Prod.fst hproj0) (⟨i.val, hi⟩, ⟨j.val, hj⟩)
      dsimp only [projMap] at h1
      exact h1
    have hA_last_col : ∀ i : Fin n, i.val < n - 1 → A (i, ⟨n - 1, by omega⟩) = 0 := by
      intro i hi
      have hr := hA_row i
      rw [hsumc] at hr
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (⟨n - 1, by omega⟩ : Fin n))] at hr
      have hrest : ∑ j ∈ Finset.univ.erase (⟨n - 1, by omega⟩ : Fin n), A (i, j) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        have hne : j ≠ ⟨n - 1, by omega⟩ := (Finset.mem_erase.mp hj).1
        have hjlt : j.val < n - 1 := by
          have := j.isLt
          have hnv : j.val ≠ n - 1 := fun heq => hne (Fin.ext heq)
          omega
        exact hA_sub i j hi hjlt
      rw [hrest, add_zero] at hr
      exact hr
    have hA_last_row : ∀ j : Fin n, j.val < n - 1 → A (⟨n - 1, by omega⟩, j) = 0 := by
      intro j hj
      have hc := hA_col j
      rw [hsumc] at hc
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (⟨n - 1, by omega⟩ : Fin n))] at hc
      have hrest : ∑ i ∈ Finset.univ.erase (⟨n - 1, by omega⟩ : Fin n), A (i, j) = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        have hne : i ≠ ⟨n - 1, by omega⟩ := (Finset.mem_erase.mp hi).1
        have hilt : i.val < n - 1 := by
          have := i.isLt
          have hnv : i.val ≠ n - 1 := fun heq => hne (Fin.ext heq)
          omega
        exact hA_sub i j hilt hj
      rw [hrest, add_zero] at hc
      exact hc
    have hA_corner : A (⟨n - 1, by omega⟩, ⟨n - 1, by omega⟩) = 0 := by
      have hr := hA_row ⟨n - 1, by omega⟩
      rw [hsumc] at hr
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (⟨n - 1, by omega⟩ : Fin n))] at hr
      have hrest : ∑ j ∈ Finset.univ.erase (⟨n - 1, by omega⟩ : Fin n), A (⟨n - 1, by omega⟩, j) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        have hne : j ≠ ⟨n - 1, by omega⟩ := (Finset.mem_erase.mp hj).1
        have hjlt : j.val < n - 1 := by
          have := j.isLt
          have hnv : j.val ≠ n - 1 := fun heq => hne (Fin.ext heq)
          omega
        exact hA_last_row j hjlt
      rw [hrest, add_zero] at hr
      exact hr
    have hA_zero : ∀ p : Fin n × Fin n, A p = 0 := by
      rintro ⟨i, j⟩
      by_cases hi : i.val < n - 1
      · by_cases hj : j.val < n - 1
        · exact hA_sub i j hi hj
        · have hjEq : j = ⟨n - 1, by omega⟩ := Fin.ext (by dsimp only; have := j.isLt; omega)
          rw [hjEq]; exact hA_last_col i hi
      · have hiEq : i = ⟨n - 1, by omega⟩ := Fin.ext (by dsimp only; have := i.isLt; omega)
        rw [hiEq]
        by_cases hj : j.val < n - 1
        · exact hA_last_row j hj
        · have hjEq : j = ⟨n - 1, by omega⟩ := Fin.ext (by dsimp only; have := j.isLt; omega)
          rw [hjEq]; exact hA_corner
    have hstrong : ∀ m : ℕ, ∀ k : Fin L.length, k.val < m → c k = 0 := by
      intro m
      induction m with
      | zero => intro k hk; omega
      | succ m ihm =>
        intro k hk
        by_cases hlt : k.val < m
        · exact ihm k hlt
        · rcases hpiv k with ⟨i0, hi0⟩
          have heval := hA_zero (i0, (L.get k).1 i0)
          dsimp only [A] at heval
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at heval
          rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k)] at heval
          have hrest : ∑ j ∈ Finset.univ.erase k, c j * P j (i0, (L.get k).1 i0) = 0 := by
            refine Finset.sum_eq_zero fun j hj => ?_
            have hne : j ≠ k := (Finset.mem_erase.mp hj).1
            by_cases hjk : j.val < k.val
            · rw [ihm j (by omega), zero_mul]
            · have hgt : k.val < j.val := by
                have hnv : j.val ≠ k.val := fun heq => hne (Fin.ext heq)
                omega
              have hne_val := hi0 j hgt
              have hP0 : P j (i0, (L.get k).1 i0) = 0 := by
                simp only [P, Ne.symm hne_val, ↓reduceIte]
              rw [hP0, mul_zero]
          have hPk : P k (i0, (L.get k).1 i0) = 1 := by simp [P]
          rw [hrest, add_zero, hPk, mul_one] at heval
          exact heval
    intro k
    exact hstrong (k.val + 1) k (Nat.lt_succ_self _)
  have hle := hli.fintype_card_le_finrank
  rw [Fintype.card_fin, Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_self] at hle
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, smul_eq_mul, mul_one, ← sq] at hle
  exact hle

private theorem int_balance_sq {K b : ℕ} (_hK : 0 < K) (L : List ℕ)
    (hlen : L.length ≤ K) (hsum : L.sum = b) :
    K * (b / K) ^ 2 + (2 * (b / K) + 1) * (b % K) ≤ (L.map (fun x => x ^ 2)).sum := by
  let h : Fin K → ℕ := fun t => if ht : t.val < L.length then L.get ⟨t.val, ht⟩ else 0
  have hsum_eq : ∑ t : Fin K, h t = b := by
    rw [← hsum]
    have hsplit : ∑ t : Fin K, h t = ∑ t ∈ Finset.univ.filter (fun t : Fin K => t.val < L.length), h t := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun t _ hnot => ?_
      have hge : ¬(t.val < L.length) := fun hlt => hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
      simp only [h, hge, ↓reduceDIte]
    rw [hsplit]
    have hbij : ∑ t ∈ Finset.univ.filter (fun t : Fin K => t.val < L.length), h t =
        ∑ i : Fin L.length, L.get i := by
      refine Finset.sum_bij (fun t ht => ⟨t.val, (Finset.mem_filter.mp ht).2⟩) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro t1 _ t2 _ heq; exact Fin.ext (congrArg (Fin.val : Fin L.length → ℕ) heq)
      · intro i _
        refine ⟨⟨i.val, i.isLt.trans_le hlen⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩, rfl⟩
      · intro t ht
        have hlt : t.val < L.length := (Finset.mem_filter.mp ht).2
        simp only [h, hlt, ↓reduceDIte]
    rw [hbij, ← List.sum_ofFn]
    congr 1
    exact List.ofFn_get L
  have hsq_eq : ∑ t : Fin K, (h t) ^ 2 = (L.map (fun x => x ^ 2)).sum := by
    have hsplit : ∑ t : Fin K, (h t) ^ 2 =
        ∑ t ∈ Finset.univ.filter (fun t : Fin K => t.val < L.length), (h t) ^ 2 := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun t _ hnot => ?_
      have hge : ¬(t.val < L.length) := fun hlt => hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
      simp only [h, hge, ↓reduceDIte, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    rw [hsplit]
    have hbij : ∑ t ∈ Finset.univ.filter (fun t : Fin K => t.val < L.length), (h t) ^ 2 =
        ∑ i : Fin L.length, (L.get i) ^ 2 := by
      refine Finset.sum_bij (fun t ht => ⟨t.val, (Finset.mem_filter.mp ht).2⟩) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro t1 _ t2 _ heq; exact Fin.ext (congrArg (Fin.val : Fin L.length → ℕ) heq)
      · intro i _
        refine ⟨⟨i.val, i.isLt.trans_le hlen⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩, rfl⟩
      · intro t ht
        have hlt : t.val < L.length := (Finset.mem_filter.mp ht).2
        simp only [h, hlt, ↓reduceDIte]
    rw [hbij, ← List.sum_ofFn]
    congr 1
    apply List.ext_get (by simp)
    intro i hi1 hi2
    simp
  rw [← hsq_eq]
  let d : ℕ := b / K
  let r : ℕ := b % K
  have hb_eq : K * d + r = b := Nat.div_add_mod b K
  have hineqZ : (K : ℤ) * (d : ℤ) ^ 2 + (2 * (d : ℤ) + 1) * (r : ℤ) ≤
      ∑ t : Fin K, ((h t : ℤ) ^ 2) := by
    have hpt : ∀ t : Fin K,
        (2 * (d : ℤ) + 1) * (h t : ℤ) - (d : ℤ) * ((d : ℤ) + 1) ≤ (h t : ℤ) ^ 2 := by
      intro t
      have hprod : 0 ≤ ((h t : ℤ) - (d : ℤ)) * ((h t : ℤ) - ((d : ℤ) + 1)) := by
        by_cases hle : (h t : ℤ) ≤ (d : ℤ)
        · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
        · exact mul_nonneg (by omega) (by omega)
      linarith
    have hsumZ := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin K))) (fun t _ => hpt t)
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hsumZ
    have hsum_cast : (∑ t : Fin K, (h t : ℤ)) = (K : ℤ) * (d : ℤ) + (r : ℤ) := by
      have h1 : (∑ t : Fin K, (h t : ℤ)) = ((∑ t : Fin K, h t : ℕ) : ℤ) := by simp
      rw [h1, hsum_eq, ← hb_eq]
      push_cast; ring
    rw [hsum_cast] at hsumZ
    linarith
  exact_mod_cast hineqZ

private theorem typ_fiber_card {n b : ℕ} (hn : 0 < n) (i : Fin n) :
    (Finset.univ.filter (fun x : Fin (n * b) => (⟨x.val % n, Nat.mod_lt _ hn⟩ : Fin n) = i)).card = b := by
  have hbij : (Finset.univ.filter (fun x : Fin (n * b) =>
      (⟨x.val % n, Nat.mod_lt _ hn⟩ : Fin n) = i)).card = (Finset.univ : Finset (Fin b)).card := by
    refine Finset.card_bij (fun x _ => ⟨x.val / n, (Nat.div_lt_iff_lt_mul hn).mpr (by rw [Nat.mul_comm b n]; exact x.isLt)⟩) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro x1 hx1 x2 hx2 heq
      have hm1 : x1.val % n = i.val := congrArg Fin.val (Finset.mem_filter.mp hx1).2
      have hm2 : x2.val % n = i.val := congrArg Fin.val (Finset.mem_filter.mp hx2).2
      have hd : x1.val / n = x2.val / n := congrArg Fin.val heq
      apply Fin.ext
      have h1 := Nat.div_add_mod x1.val n
      have h2 := Nat.div_add_mod x2.val n
      rw [hd] at h1
      omega
    · intro k _
      have hlt : k.val * n + i.val < n * b := by
        have h1 : (k.val + 1) * n ≤ b * n := Nat.mul_le_mul_right n (by have := k.isLt; omega)
        rw [Nat.add_mul, Nat.one_mul] at h1
        have := i.isLt
        rw [Nat.mul_comm n b]; omega
      refine ⟨⟨k.val * n + i.val, hlt⟩, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.ext ?_⟩
        dsimp only
        rw [Nat.mul_comm k.val n, Nat.mul_add_mod, Nat.mod_eq_of_lt i.isLt]
      · apply Fin.ext
        dsimp only
        rw [Nat.mul_comm k.val n, Nat.mul_add_div hn, Nat.div_eq_of_lt i.isLt, Nat.add_zero]
  rw [hbij, Finset.card_univ, Fintype.card_fin]

private theorem choice_two_coord_card {n h : ℕ} {u v : Fin n} (huv : u ≠ v) (r1 r2 : Fin h) :
    (Finset.univ.filter (fun ρ : Fin n → Fin h => ρ u = r1 ∧ ρ v = r2)).card = h ^ (n - 2) := by
  let S : Finset (Fin n) := {u, v}
  have hScard : S.card = 2 := Finset.card_pair huv
  have hcomp_card : Fintype.card {w : Fin n // w ∉ S} = n - 2 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
    have hmem : Fintype.card {w : Fin n // w ∈ S} = S.card := Fintype.card_coe S
    rw [hmem, hScard]
  have heq : (Finset.univ.filter (fun ρ : Fin n → Fin h => ρ u = r1 ∧ ρ v = r2)).card =
      Fintype.card ({w : Fin n // w ∉ S} → Fin h) := by
    rw [← Finset.card_univ]
    refine Finset.card_bij (fun ρ _ => fun w : {w : Fin n // w ∉ S} => ρ w.1) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro ρ1 hρ1 ρ2 hρ2 hfun
      rcases (Finset.mem_filter.mp hρ1).2 with ⟨h1u, h1v⟩
      rcases (Finset.mem_filter.mp hρ2).2 with ⟨h2u, h2v⟩
      funext w
      by_cases hw : w ∈ S
      · rcases Finset.mem_insert.mp hw with rfl | hmv
        · rw [h1u, h2u]
        · rw [Finset.mem_singleton.mp hmv, h1v, h2v]
      · exact congrFun hfun ⟨w, hw⟩
    · intro f _
      let ρ : Fin n → Fin h := fun w =>
        if hw1 : w = u then r1
        else if hw2 : w = v then r2
        else f ⟨w, fun hm => by
          rcases Finset.mem_insert.mp hm with rfl | hmv
          · exact hw1 rfl
          · exact hw2 (Finset.mem_singleton.mp hmv)⟩
      refine ⟨ρ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩
      · simp [ρ]
      · simp [ρ, Ne.symm huv]
      · funext ⟨w, hw⟩
        have h1 : w ≠ u := fun he => hw (he ▸ Finset.mem_insert_self u {v})
        have h2 : w ≠ v := fun he => hw (he ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self v))
        simp [ρ, h1, h2]
  rw [heq, Fintype.card_fun, Fintype.card_fin, hcomp_card]

private theorem sum_list_get_eq {α : Type*} (L : List α) (f : α → ℕ) :
    (L.map f).sum = ∑ t : Fin L.length, f (L.get t) := by
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_get (by simp)
  intro i hi1 hi2
  simp

end PEqualNP.Outside.L_meta_25707_aux

theorem PEqualNP.Outside.L_meta_25707 :
    ∀ (n b q : ℕ) (hn : 0 < n), 0 < b →
      ∀ (rowCap colCap : Fin q → ℕ),
      let fits := fun (s : ℕ) (G : Fin s → Fin s → Bool) (budget : ℕ) =>
        ∃ (π : Equiv.Perm (Fin s)) (rf cf : Fin s → Bool)
          (R C : Fin q → Finset (Fin s)) (out : Finset (Fin s) → (Fin q → Bool) → Bool),
          (∀ j, (R j).card ≤ rowCap j ∧ (C j).card ≤ colCap j) ∧
          ((Finset.univ : Finset (Fin s × Fin s)).filter (fun z =>
            out {z.1,z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
              Bool.xor (G z.1 (π z.2)) (Bool.xor (rf z.1) (cf (π z.2))))).card ≤ budget
      let typ := fun label : Fin (n*b) => (⟨label.val % n, Nat.mod_lt _ hn⟩ : Fin n)
      let K := (n-1)^2+1
      let d := b/K
      let W := K*d^2 + (2*d+1)*(b%K)
      ∀ (G : Fin n → Fin n → Bool) (E : ℕ),
        fits (n*b) (fun i j => G (typ i) (typ j)) E → fits n G (E/W) := by
  intro n b q hn hb rowCap colCap fits typ K d W G E hfits
  by_cases hn1 : n = 1
  · subst hn1
    refine ⟨Equiv.refl (Fin 1), fun _ => false, fun _ => false, fun _ => ∅, fun _ => ∅,
      fun _ _ => G ⟨0, hn⟩ ⟨0, hn⟩, fun _ => ⟨Nat.zero_le _, Nat.zero_le _⟩, ?_⟩
    have h0 : ((Finset.univ : Finset (Fin 1 × Fin 1)).filter (fun z =>
        G ⟨0, hn⟩ ⟨0, hn⟩ ≠ Bool.xor (G z.1 (Equiv.refl (Fin 1) z.2))
          (Bool.xor false false))).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro ⟨z1, z2⟩ _
      have hz1 : z1 = ⟨0, hn⟩ := Fin.ext (by omega)
      have hz2 : z2 = ⟨0, hn⟩ := Fin.ext (by omega)
      subst hz1; subst hz2
      simp
    rw [h0]
    exact Nat.zero_le _
  · have hn2 : 2 ≤ n := by omega
    rcases hfits with ⟨π, rf, cf, R, C, out, hcaps, hErr⟩
    let ErrBig : Finset (Fin (n * b) × Fin (n * b)) :=
      Finset.univ.filter (fun z =>
        out {z.1, z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
          Bool.xor (G (typ z.1) (typ (π z.2))) (Bool.xor (rf z.1) (cf (π z.2))))
    have hErrCard : ErrBig.card ≤ E := hErr
    let bucket : Fin n → Fin n → Finset (Fin (n * b)) := fun i j =>
      Finset.univ.filter (fun x => typ x = i ∧ typ (π x) = j)
    let M : Fin n → Fin n → ℕ := fun i j => (bucket i j).card
    have hM_row : ∀ i : Fin n, ∑ j : Fin n, M i j = b := by
      intro i
      have hbi : (Finset.univ.biUnion (fun j : Fin n => bucket i j)).card = ∑ j : Fin n, M i j := by
        rw [Finset.card_biUnion]
        intro j1 _ j2 _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro x hx1 hx2
        exact hne ((Finset.mem_filter.mp hx1).2.2.symm.trans (Finset.mem_filter.mp hx2).2.2)
      rw [← hbi]
      have heq : Finset.univ.biUnion (fun j : Fin n => bucket i j) =
          Finset.univ.filter (fun x : Fin (n * b) => typ x = i) := by
        ext x
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, bucket, Finset.mem_filter]
        exact ⟨fun ⟨_, hx, _⟩ => hx, fun hx => ⟨typ (π x), hx, rfl⟩⟩
      rw [heq]
      exact PEqualNP.Outside.L_meta_25707_aux.typ_fiber_card hn i
    have hM_col : ∀ j : Fin n, ∑ i : Fin n, M i j = b := by
      intro j
      have hbi : (Finset.univ.biUnion (fun i : Fin n => bucket i j)).card = ∑ i : Fin n, M i j := by
        rw [Finset.card_biUnion]
        intro i1 _ i2 _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro x hx1 hx2
        exact hne ((Finset.mem_filter.mp hx1).2.1.symm.trans (Finset.mem_filter.mp hx2).2.1)
      rw [← hbi]
      have heq : Finset.univ.biUnion (fun i : Fin n => bucket i j) =
          Finset.univ.filter (fun x : Fin (n * b) => typ (π x) = j) := by
        ext x
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, bucket, Finset.mem_filter]
        exact ⟨fun ⟨_, _, hx⟩ => hx, fun hx => ⟨typ x, rfl, hx⟩⟩
      rw [heq]
      have hbij : (Finset.univ.filter (fun x : Fin (n * b) => typ (π x) = j)).card =
          (Finset.univ.filter (fun y : Fin (n * b) => typ y = j)).card := by
        refine Finset.card_bij (fun x _ => π x) ?_ ?_ ?_
        · intro x hx; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
        · intro x1 _ x2 _ heq'; exact π.injective heq'
        · intro y hy
          exact ⟨π.symm y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            rw [Equiv.apply_symm_apply]; exact (Finset.mem_filter.mp hy).2⟩, Equiv.apply_symm_apply π y⟩
      rw [hbij]
      exact PEqualNP.Outside.L_meta_25707_aux.typ_fiber_card hn j
    rcases PEqualNP.Outside.L_meta_25707_aux.birkhoff_peel hn
        (PEqualNP.Outside.L_meta_25707_aux.suppCard M) b M le_rfl hM_row hM_col with
      ⟨L, hLpos, hLsum, hLpiv⟩
    have hLlen : L.length ≤ K := PEqualNP.Outside.L_meta_25707_aux.birkhoff_len_le hn L hLpiv
    have hLtot : (L.map Prod.snd).sum = b := by
      have hr := hM_row ⟨0, hn⟩
      rw [← hr]
      have h1 : ∑ j : Fin n, M ⟨0, hn⟩ j =
          ∑ j : Fin n, ∑ t : Fin L.length, if j = (L.get t).1 ⟨0, hn⟩ then (L.get t).2 else 0 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hLsum ⟨0, hn⟩ j, PEqualNP.Outside.L_meta_25707_aux.sum_list_get_eq]
      rw [h1, Finset.sum_comm]
      have h2 : ∑ t : Fin L.length, ∑ j : Fin n, (if j = (L.get t).1 ⟨0, hn⟩ then (L.get t).2 else 0) =
          ∑ t : Fin L.length, (L.get t).2 := by
        refine Finset.sum_congr rfl fun t _ => by simp
      rw [h2, PEqualNP.Outside.L_meta_25707_aux.sum_list_get_eq]
    have hKpos : 0 < K := by dsimp only [K]; omega
    have hWle : W ≤ ∑ t : Fin L.length, (L.get t).2 ^ 2 := by
      have hbal := PEqualNP.Outside.L_meta_25707_aux.int_balance_sq hKpos (L.map Prod.snd)
        (by simp [hLlen]) hLtot
      rw [List.map_map] at hbal
      have heq : (L.map ((fun x => x ^ 2) ∘ Prod.snd)).sum = ∑ t : Fin L.length, (L.get t).2 ^ 2 :=
        PEqualNP.Outside.L_meta_25707_aux.sum_list_get_eq L (fun p => p.2 ^ 2)
      rw [heq] at hbal
      exact hbal
    have hWpos : 0 < W := by
      dsimp only [W, d]
      by_cases hd0 : b / K = 0
      · have hmod : 0 < b % K := by
          have h1 := Nat.div_add_mod b K
          rw [hd0, Nat.mul_zero, Nat.zero_add] at h1; omega
        rw [hd0]
        simp only [Nat.mul_zero, Nat.zero_add, Nat.one_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        exact hmod
      · have hpos_d : 0 < b / K := Nat.pos_of_ne_zero hd0
        have h1 : 0 < (b / K) ^ 2 := pow_pos hpos_d 2
        have h2 : 0 < K * (b / K) ^ 2 := Nat.mul_pos hKpos h1
        omega
    let eB : ∀ i j : Fin n, Fin (M i j) ≃ {x : Fin (n * b) // x ∈ bucket i j} :=
      fun i j => (Fintype.equivFinOfCardEq (Fintype.card_coe (bucket i j))).symm
    let off : Fin L.length → Fin n → ℕ := fun t i =>
      ∑ t' ∈ Finset.univ.filter (fun t' : Fin L.length => t'.val < t.val ∧ (L.get t').1 i = (L.get t).1 i),
        (L.get t').2
    have hoff_lt : ∀ (t : Fin L.length) (i : Fin n) (r : Fin (L.get t).2),
        off t i + r.val < M i ((L.get t).1 i) := by
      intro t i r
      rw [hLsum i ((L.get t).1 i), PEqualNP.Outside.L_meta_25707_aux.sum_list_get_eq]
      let Ssub : Finset (Fin L.length) :=
        Finset.univ.filter (fun t' : Fin L.length => t'.val < t.val ∧ (L.get t').1 i = (L.get t).1 i)
      have hnot : t ∉ Ssub := by simp [Ssub]
      have hsub : insert t Ssub ⊆ Finset.univ := Finset.subset_univ _
      have hle_sum : ∑ t' ∈ insert t Ssub, (if (L.get t).1 i = (L.get t').1 i then (L.get t').2 else 0) ≤
          ∑ t' : Fin L.length, (if (L.get t).1 i = (L.get t').1 i then (L.get t').2 else 0) :=
        Finset.sum_le_sum_of_subset hsub
      rw [Finset.sum_insert hnot] at hle_sum
      simp only [↓reduceIte] at hle_sum
      have hSsub_eq : ∑ t' ∈ Ssub, (if (L.get t).1 i = (L.get t').1 i then (L.get t').2 else 0) = off t i := by
        refine Finset.sum_congr rfl fun t' ht' => ?_
        have heq := (Finset.mem_filter.mp ht').2.2
        simp only [heq, ↓reduceIte]
      rw [hSsub_eq] at hle_sum
      have := r.isLt
      omega
    let phys : ∀ (t : Fin L.length), Fin n → Fin (L.get t).2 → Fin (n * b) :=
      fun t i r => (eB i ((L.get t).1 i) ⟨off t i + r.val, hoff_lt t i r⟩).1
    have hphys_mem : ∀ t i r, phys t i r ∈ bucket i ((L.get t).1 i) :=
      fun t i r => (eB i ((L.get t).1 i) ⟨off t i + r.val, hoff_lt t i r⟩).2
    have hphys_typ : ∀ t i r, typ (phys t i r) = i :=
      fun t i r => (Finset.mem_filter.mp (hphys_mem t i r)).2.1
    have hphys_ptyp : ∀ t i r, typ (π (phys t i r)) = (L.get t).1 i :=
      fun t i r => (Finset.mem_filter.mp (hphys_mem t i r)).2.2
    have hphys_inj : ∀ {t1 t2 : Fin L.length} {i1 i2 : Fin n}
        {r1 : Fin (L.get t1).2} {r2 : Fin (L.get t2).2},
        phys t1 i1 r1 = phys t2 i2 r2 → t1 = t2 ∧ i1 = i2 ∧ r1.val = r2.val := by
      intro t1 t2 i1 i2 r1 r2 heq
      have hi : i1 = i2 := by
        have h1 := hphys_typ t1 i1 r1
        have h2 := hphys_typ t2 i2 r2
        rw [heq] at h1; exact h1.symm.trans h2
      subst hi
      have hj : (L.get t1).1 i1 = (L.get t2).1 i1 := by
        have h1 := hphys_ptyp t1 i1 r1
        have h2 := hphys_ptyp t2 i1 r2
        rw [heq] at h1; exact h1.symm.trans h2
      have hidx_eq : off t1 i1 + r1.val = off t2 i1 + r2.val := by
        have hcast : ∀ (j1 j2 : Fin n) (hjEq : j1 = j2) (a1 : Fin (M i1 j1)) (a2 : Fin (M i1 j2)),
            (eB i1 j1 a1).1 = (eB i1 j2 a2).1 → a1.val = a2.val := by
          rintro j1 _ rfl a1 a2 h
          exact congrArg Fin.val ((eB i1 j1).injective (Subtype.ext h))
        exact hcast _ _ hj _ _ heq
      have ht : t1 = t2 := by
        by_contra hne
        have hlt_or : t1.val < t2.val ∨ t2.val < t1.val := by
          have : t1.val ≠ t2.val := fun h => hne (Fin.ext h)
          omega
        have hstep : ∀ (a b' : Fin L.length), a.val < b'.val → (L.get a).1 i1 = (L.get b').1 i1 →
            off a i1 + (L.get a).2 ≤ off b' i1 := by
          intro a b' hab hperm
          let Sa := Finset.univ.filter (fun t' : Fin L.length => t'.val < a.val ∧ (L.get t').1 i1 = (L.get a).1 i1)
          let Sb := Finset.univ.filter (fun t' : Fin L.length => t'.val < b'.val ∧ (L.get t').1 i1 = (L.get b').1 i1)
          have hsub : insert a Sa ⊆ Sb := by
            intro t' ht'
            rcases Finset.mem_insert.mp ht' with rfl | hma
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hperm⟩
            · rcases (Finset.mem_filter.mp hma).2 with ⟨h1, h2⟩
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega, h2.trans hperm⟩
          have hnot : a ∉ Sa := by simp [Sa]
          have hle_s := Finset.sum_le_sum_of_subset (f := fun t' : Fin L.length => (L.get t').2) hsub
          rw [Finset.sum_insert hnot] at hle_s
          dsimp only [Sa, Sb] at hle_s
          dsimp only [off]
          omega
        rcases hlt_or with hlt | hlt
        · have hle1 := hstep t1 t2 hlt hj
          have := r1.isLt; omega
        · have hle2 := hstep t2 t1 hlt hj.symm
          have := r2.isLt; omega
      subst ht
      exact ⟨rfl, rfl, by omega⟩
    let grp : Fin L.length → Finset (Fin (n * b)) := fun t =>
      Finset.univ.image (fun p : Fin n × Fin (L.get t).2 => phys t p.1 p.2)
    let Egrp : Fin L.length → ℕ := fun t =>
      (ErrBig.filter (fun z => z.1 ∈ grp t ∧ z.2 ∈ grp t ∧ typ z.1 ≠ typ z.2)).card
    have hEsum : ∑ t : Fin L.length, Egrp t ≤ E := by
      have hcard_bi : (Finset.univ.biUnion (fun t : Fin L.length =>
          ErrBig.filter (fun z => z.1 ∈ grp t ∧ z.2 ∈ grp t ∧ typ z.1 ≠ typ z.2))).card =
          ∑ t : Fin L.length, Egrp t := by
        rw [Finset.card_biUnion]
        intro t1 _ t2 _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro z hz1 hz2
        have hm1 := (Finset.mem_filter.mp hz1).2.1
        have hm2 := (Finset.mem_filter.mp hz2).2.1
        rcases Finset.mem_image.mp hm1 with ⟨⟨i1, r1⟩, _, he1⟩
        rcases Finset.mem_image.mp hm2 with ⟨⟨i2, r2⟩, _, he2⟩
        exact hne (hphys_inj (he1.trans he2.symm)).1
      rw [← hcard_bi]
      refine (Finset.card_le_card ?_).trans hErrCard
      intro z hz
      rcases Finset.mem_biUnion.mp hz with ⟨t, _, hzt⟩
      exact (Finset.mem_filter.mp hzt).1
    have hex_good : ∃ (t : Fin L.length) (ρ : Fin n → Fin (L.get t).2),
        ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p =>
          p.1 ≠ p.2 ∧ (phys t p.1 (ρ p.1), phys t p.2 (ρ p.2)) ∈ ErrBig)).card ≤ E / W := by
      by_contra hno
      push Not at hno
      let B : ℕ := E / W + 1
      have hgrp_bound : ∀ t : Fin L.length, (L.get t).2 ^ 2 * B ≤ Egrp t := by
        intro t
        let h : ℕ := (L.get t).2
        have hhpos : 0 < h := hLpos (L.get t) (List.get_mem _ _)
        let errρ : (Fin n → Fin h) → Finset (Fin n × Fin n) := fun ρ =>
          Finset.univ.filter (fun p => p.1 ≠ p.2 ∧ (phys t p.1 (ρ p.1), phys t p.2 (ρ p.2)) ∈ ErrBig)
        have hlow : h ^ n * B ≤ ∑ ρ : Fin n → Fin h, (errρ ρ).card := by
          calc h ^ n * B = ∑ _ρ : Fin n → Fin h, B := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, smul_eq_mul]
            _ ≤ ∑ ρ : Fin n → Fin h, (errρ ρ).card :=
                Finset.sum_le_sum fun ρ _ => hno t ρ
        have hdouble : ∑ ρ : Fin n → Fin h, (errρ ρ).card = h ^ (n - 2) * Egrp t := by
          have h1 : ∑ ρ : Fin n → Fin h, (errρ ρ).card =
              ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2),
                (Finset.univ.filter (fun ρ : Fin n → Fin h =>
                  (phys t p.1 (ρ p.1), phys t p.2 (ρ p.2)) ∈ ErrBig)).card := by
            trans (∑ ρ : Fin n → Fin h,
                ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2),
                  if (phys t p.1 (ρ p.1), phys t p.2 (ρ p.2)) ∈ ErrBig then 1 else 0)
            · refine Finset.sum_congr rfl fun ρ _ => ?_
              rw [Finset.sum_boole, Nat.cast_id]
              congr 1
              ext p
              simp only [errρ, Finset.mem_filter, Finset.mem_univ, true_and]
            · rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun p _ => ?_
              rw [Finset.sum_boole, Nat.cast_id]
          rw [h1]
          have hinner : ∀ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2),
              (Finset.univ.filter (fun ρ : Fin n → Fin h =>
                (phys t p.1 (ρ p.1), phys t p.2 (ρ p.2)) ∈ ErrBig)).card =
              h ^ (n - 2) * (Finset.univ.filter (fun r : Fin h × Fin h =>
                (phys t p.1 r.1, phys t p.2 r.2) ∈ ErrBig)).card := by
            intro p hp
            have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
            have hbi : Finset.univ.filter (fun ρ : Fin n → Fin h =>
                (phys t p.1 (ρ p.1), phys t p.2 (ρ p.2)) ∈ ErrBig) =
                (Finset.univ.filter (fun r : Fin h × Fin h =>
                  (phys t p.1 r.1, phys t p.2 r.2) ∈ ErrBig)).biUnion (fun r =>
                  Finset.univ.filter (fun ρ : Fin n → Fin h => ρ p.1 = r.1 ∧ ρ p.2 = r.2)) := by
              ext ρ
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
              constructor
              · intro hmem
                exact ⟨(ρ p.1, ρ p.2), hmem, rfl, rfl⟩
              · rintro ⟨⟨r1, r2⟩, hmem, h1, h2⟩
                rw [h1, h2]; exact hmem
            rw [hbi, Finset.card_biUnion]
            · rw [Finset.sum_congr rfl (fun r _ =>
                PEqualNP.Outside.L_meta_25707_aux.choice_two_coord_card hne r.1 r.2),
                Finset.sum_const, smul_eq_mul, Nat.mul_comm]
            · intro r1 _ r2 _ hrne
              rw [Function.onFun, Finset.disjoint_left]
              intro ρ hρ1 hρ2
              rcases (Finset.mem_filter.mp hρ1).2 with ⟨a1, b1⟩
              rcases (Finset.mem_filter.mp hρ2).2 with ⟨a2, b2⟩
              exact hrne (Prod.ext (a1.symm.trans a2) (b1.symm.trans b2))
          rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]
          congr 1
          have hEbij : ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2),
              (Finset.univ.filter (fun r : Fin h × Fin h =>
                (phys t p.1 r.1, phys t p.2 r.2) ∈ ErrBig)).card = Egrp t := by
            rw [← Finset.card_sigma]
            dsimp only [Egrp]
            refine Finset.card_bij (fun s _ => (phys t s.1.1 s.2.1, phys t s.1.2 s.2.2)) ?_ ?_ ?_
            · intro s hs
              rcases Finset.mem_sigma.mp hs with ⟨hp, hr⟩
              have hne : s.1.1 ≠ s.1.2 := (Finset.mem_filter.mp hp).2
              have hmemE : (phys t s.1.1 s.2.1, phys t s.1.2 s.2.2) ∈ ErrBig := (Finset.mem_filter.mp hr).2
              refine Finset.mem_filter.mpr ⟨hmemE, ?_, ?_, ?_⟩
              · exact Finset.mem_image.mpr ⟨(s.1.1, s.2.1), Finset.mem_univ _, rfl⟩
              · exact Finset.mem_image.mpr ⟨(s.1.2, s.2.2), Finset.mem_univ _, rfl⟩
              · rw [hphys_typ, hphys_typ]; exact hne
            · intro s1 _ s2 _ heq
              have h1 := hphys_inj (congrArg Prod.fst heq)
              have h2 := hphys_inj (congrArg Prod.snd heq)
              exact Sigma.ext (Prod.ext h1.2.1 h2.2.1)
                (heq_of_eq (Prod.ext (Fin.ext h1.2.2) (Fin.ext h2.2.2)))
            · intro z hz
              rcases Finset.mem_filter.mp hz with ⟨hmemE, hz1, hz2, hne⟩
              rcases Finset.mem_image.mp hz1 with ⟨⟨u, r1⟩, _, hu⟩
              rcases Finset.mem_image.mp hz2 with ⟨⟨v, r2⟩, _, hv⟩
              have huv : u ≠ v := by
                rw [← hu, ← hv, hphys_typ, hphys_typ] at hne; exact hne
              refine ⟨⟨(u, v), (r1, r2)⟩, Finset.mem_sigma.mpr ⟨?_, ?_⟩, Prod.ext hu hv⟩
              · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv⟩
              · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [hu, hv]⟩
          exact hEbij
        rw [hdouble] at hlow
        have hpow_split : h ^ n = h ^ (n - 2) * h ^ 2 := by
          rw [← pow_add, Nat.sub_add_cancel hn2]
        rw [hpow_split, Nat.mul_assoc] at hlow
        exact Nat.le_of_mul_le_mul_left hlow (pow_pos hhpos (n - 2))
      have htot_le : W * B ≤ E := by
        calc W * B ≤ (∑ t : Fin L.length, (L.get t).2 ^ 2) * B := Nat.mul_le_mul_right B hWle
          _ = ∑ t : Fin L.length, (L.get t).2 ^ 2 * B := Finset.sum_mul _ _ _
          _ ≤ ∑ t : Fin L.length, Egrp t := Finset.sum_le_sum fun t _ => hgrp_bound t
          _ ≤ E := hEsum
      have hlt : E < W * B := Nat.lt_mul_div_succ E hWpos
      omega
    rcases hex_good with ⟨t, ρ, hgood⟩
    let σ : Equiv.Perm (Fin n) := (L.get t).1
    let rep : Fin n → Fin (n * b) := fun u => phys t u (ρ u)
    have hrep_typ : ∀ u, typ (rep u) = u := fun u => hphys_typ t u (ρ u)
    have hrep_ptyp : ∀ u, typ (π (rep u)) = σ u := fun u => hphys_ptyp t u (ρ u)
    have hrep_inj : Function.Injective rep := fun u1 u2 heq => by
      have h1 := hrep_typ u1
      have h2 := hrep_typ u2
      rw [heq] at h1; exact h1.symm.trans h2
    let rf' : Fin n → Bool := fun u => rf (rep u)
    let cf' : Fin n → Bool := fun w => cf (π (rep (σ.symm w)))
    let R' : Fin q → Finset (Fin n) := fun j => Finset.univ.filter (fun u => rep u ∈ R j)
    let C' : Fin q → Finset (Fin n) := fun j => Finset.univ.filter (fun w => π (rep (σ.symm w)) ∈ C j)
    let out' : Finset (Fin n) → (Fin q → Bool) → Bool := fun S mask =>
      if h1 : S.card = 1 then
        let u := (Finset.card_eq_one.mp h1).choose
        Bool.xor (G u (σ u)) (Bool.xor (rf' u) (cf' (σ u)))
      else
        out (S.image rep) mask
    refine ⟨σ, rf', cf', R', C', out', ?_, ?_⟩
    · intro j
      constructor
      · calc (R' j).card = ((R' j).image rep).card := (Finset.card_image_of_injective _ hrep_inj).symm
          _ ≤ (R j).card := Finset.card_le_card fun x hx => by
              rcases Finset.mem_image.mp hx with ⟨u, hu, rfl⟩
              exact (Finset.mem_filter.mp hu).2
          _ ≤ rowCap j := (hcaps j).1
      · have hcinj : Function.Injective (fun w : Fin n => π (rep (σ.symm w))) :=
          π.injective.comp (hrep_inj.comp σ.symm.injective)
        calc (C' j).card = ((C' j).image (fun w => π (rep (σ.symm w)))).card :=
              (Finset.card_image_of_injective _ hcinj).symm
          _ ≤ (C j).card := Finset.card_le_card fun x hx => by
              rcases Finset.mem_image.mp hx with ⟨w, hw, rfl⟩
              exact (Finset.mem_filter.mp hw).2
          _ ≤ colCap j := (hcaps j).2
    · refine (Finset.card_le_card ?_).trans hgood
      intro ⟨u, v⟩ hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      by_cases huv : u = v
      · subst huv
        have hcard1 : ({u, u} : Finset (Fin n)).card = 1 := by simp
        dsimp only [out'] at hz
        simp only [hcard1, ↓reduceDIte] at hz
        have hch : (Finset.card_eq_one.mp hcard1).choose = u := by
          have hspec := (Finset.card_eq_one.mp hcard1).choose_spec
          have hm : u ∈ ({u, u} : Finset (Fin n)) := Finset.mem_insert_self u _
          rw [hspec, Finset.mem_singleton] at hm
          exact hm.symm
        rw [hch] at hz
        exact absurd rfl hz
      · refine ⟨huv, ?_⟩
        have hcard2 : ({u, v} : Finset (Fin n)).card ≠ 1 := by
          rw [Finset.card_pair huv]; omega
        dsimp only [out'] at hz
        simp only [hcard2, ↓reduceDIte] at hz
        have himg : ({u, v} : Finset (Fin n)).image rep = {rep u, rep v} := by
          ext x; simp
        have hmask : (fun j : Fin q => decide (u ∈ R' j ∨ σ v ∈ C' j)) =
            (fun j : Fin q => decide (rep u ∈ R j ∨ π (rep v) ∈ C j)) := by
          funext j
          simp [R', C', Equiv.symm_apply_apply]
        have hrhs : Bool.xor (G u (σ v)) (Bool.xor (rf' u) (cf' (σ v))) =
            Bool.xor (G (typ (rep u)) (typ (π (rep v)))) (Bool.xor (rf (rep u)) (cf (π (rep v)))) := by
          simp [rf', cf', hrep_typ, hrep_ptyp, Equiv.symm_apply_apply]
        rw [himg, hmask, hrhs] at hz
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
