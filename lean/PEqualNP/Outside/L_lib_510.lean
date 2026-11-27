import Mathlib

namespace PEqualNP.Outside.L_lib_510

def mismatch {n q : Nat} (x y : Fin n → Fin q) := Finset.univ.filter (fun i => x i ≠ y i)

theorem fiber {n q : Nat} (x : Fin n → Fin q) (s : Finset (Fin n)) :
    (Finset.univ.filter (fun y : Fin n → Fin q => mismatch x y = s)).card = (q-1)^s.card := by
  classical
  let choices (i : Fin n) : Finset (Fin q) := if i ∈ s then Finset.univ.erase (x i) else {x i}
  have sides : Finset.univ.filter (fun y : Fin n → Fin q => mismatch x y = s) = Fintype.piFinset choices := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro eq i
      have hi : i ∈ mismatch x y ↔ i ∈ s := eq ▸ Iff.rfl
      simp only [mismatch,Finset.mem_filter,Finset.mem_univ,true_and] at hi
      by_cases h : i ∈ s
      · simpa [choices,h,ne_comm] using (hi.mpr h)
      · have equal : x i = y i := by by_contra ne; exact h (hi.mp ne)
        simpa [choices,h] using equal.symm
    · intro all
      ext i
      have this := all i
      by_cases h : i ∈ s <;> simp_all [choices,mismatch,ne_comm]
  rw [sides,Fintype.card_piFinset]
  have cards (i : Fin n) : (choices i).card = if i ∈ s then q-1 else 1 := by
    by_cases hi : i ∈ s <;> simp [choices,hi,Finset.card_erase_of_mem]
  simp_rw [cards]
  rw [← Finset.prod_filter]
  simp

theorem volume {n q : Nat} (x : Fin n → Fin q) (r : Nat) :
    (Finset.univ.filter (fun y : Fin n → Fin q => (mismatch x y).card ≤ r)).card =
    ((List.range (r+1)).map (fun j => Nat.choose n j * (q-1)^j)).sum := by
  classical
  have shell (j : Nat) :
      (Finset.univ.filter (fun y : Fin n → Fin q => (mismatch x y).card = j)).card =
      Nat.choose n j * (q-1)^j := by
    have sums := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin n → Fin q))
      ((Finset.univ : Finset (Fin n)).powersetCard j) (mismatch x)
    simp only [Finset.mem_powersetCard,Finset.subset_univ,true_and] at sums
    rw [← sums]
    apply (Finset.sum_const_nat (m := (q-1)^j) (fun s hs => ?_)).trans
    · simp
    · rw [fiber,(Finset.mem_powersetCard.mp hs).2]
  have sums := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin n → Fin q))
    (Finset.range (r+1)) (fun y => (mismatch x y).card)
  simp only [Finset.mem_range,Nat.lt_succ_iff] at sums
  rw [← sums]
  simp_rw [shell]
  have seq (f : ℕ → ℕ) (k : ℕ) : (∑ j ∈ Finset.range k, f j) = ((List.range k).map f).sum := by
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, List.range_succ, List.map_append, List.sum_append, ih]; simp
  exact seq _ _

theorem alteration :
  ∀ (q n r t : Nat), 2 ≤ q → r ≤ n →
  let Word := Fin n → Fin q
  let dist := fun (x y : Word) =>
    ((Finset.univ : Finset (Fin n)).filter (fun i => x i ≠ y i)).card
  let A := q^n
  let V := ((List.range (r+1)).map (fun j => Nat.choose n j * (q-1)^j)).sum
  ∃ C : Finset Word, (∀ point : Word, ∃ c ∈ C, dist point c ≤ r) ∧
    C.card * A^t ≤ t*A^t + A*(A-V)^t := by
  classical
  intro q n r t hq _
  dsimp only
  let Word := Fin n → Fin q
  let Centers := Fin t → Word
  have : Nonempty (Fin q) := ⟨⟨0,by omega⟩⟩
  let V := ((List.range (r+1)).map (fun j => Nat.choose n j * (q-1)^j)).sum
  let ball (x : Word) : Finset Word := Finset.univ.filter (fun y => (L_lib_510.mismatch x y).card ≤ r)
  let missed (z : Centers) := Finset.univ.filter (fun x : Word => ∀ j, z j ∉ ball x)
  have hcardW : Fintype.card Word = q^n := by simp [Word]
  have hcardZ : Fintype.card Centers = (q^n)^t := by simp [Centers,hcardW]
  have avoid (x : Word) : (Finset.univ.filter (fun z : Centers => ∀ j, z j ∉ ball x)).card = (q^n-V)^t := by
    have same : Finset.univ.filter (fun z : Centers => ∀ j, z j ∉ ball x) = Fintype.piFinset (fun _ : Fin t => (ball x)ᶜ) := by
      ext z
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · exact fun h => Fintype.mem_piFinset.mpr (fun j => Finset.mem_compl.mpr (h j))
      · exact fun h j => Finset.mem_compl.mp (Fintype.mem_piFinset.mp h j)
    have size : (ball x).card = V := L_lib_510.volume x r
    have rest : (ball x)ᶜ.card = q^n-V := by rw [Finset.card_compl,hcardW,size]
    rw [same,Fintype.card_piFinset]
    simp only [rest,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have count : (∑ z : Centers, (missed z).card) = q^n*(q^n-V)^t := by
    calc
      _ = ∑ x : Word, (Finset.univ.filter (fun z : Centers => ∀ j, z j ∉ ball x)).card := by
        simp only [missed,Finset.card_filter]
        exact Finset.sum_comm
      _ = _ := by simp [avoid,hcardW]
  obtain ⟨z,_,hz⟩ := (Finset.univ : Finset Centers).exists_min_image (fun z => (missed z).card) Finset.univ_nonempty
  have hb : (missed z).card * (q^n)^t ≤ q^n*(q^n-V)^t := by
    have le := Finset.sum_le_sum (s := (Finset.univ : Finset Centers)) (fun i hi => hz i hi)
    rw [count] at le
    simpa [hcardZ,Nat.mul_comm] using le
  let base : Finset Word := Finset.univ.image z
  refine ⟨base ∪ missed z, ?_, ?_⟩
  · intro x
    by_cases covered : ∃ j, z j ∈ ball x
    · obtain ⟨j,hj⟩ := covered
      exact ⟨z j,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩),(Finset.mem_filter.mp hj).2⟩
    · refine ⟨x,Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun j hj => covered ⟨j,hj⟩⟩),?_⟩
      simp
  · have nb : base.card ≤ t := by simpa [base] using (Finset.card_image_le (s := Finset.univ) (f := z))
    have total : (base ∪ missed z).card ≤ t + (missed z).card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_right nb _)
    calc
      _ ≤ (t + (missed z).card) * (q^n)^t := Nat.mul_le_mul_right _ total
      _ ≤ _ := by rw [Nat.add_mul]; exact Nat.add_le_add_left hb _

lemma remainder_bound (n A V t : ℕ) (hA : A = 2 ^ n) (hv : V ≤ A)
    (ht : n*A ≤ t*V) : A*(A-V)^t ≤ A^t := by
  have ha : 0 < A := by rw [hA]; positivity
  have haR : (0:ℝ) < A := by exact_mod_cast ha
  let u : ℝ := V / (A : ℝ)
  have hu : u * A = V := by dsimp [u]; field_simp
  have hbase : ((A-V : ℕ) : ℝ) ≤ (A:ℝ) * Real.exp (-u) := by
    rw [Nat.cast_sub hv]
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-u)) haR.le
    nlinarith
  have htu : (n:ℝ) ≤ (t:ℝ)*u := by
    apply (le_of_mul_le_mul_right _ haR)
    rw [mul_assoc, hu]
    exact_mod_cast ht
  have htwo : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have heA : (A:ℝ) ≤ Real.exp ((t:ℝ)*u) := calc
    (A:ℝ) = (2:ℝ)^n := by exact_mod_cast hA
    _ ≤ (Real.exp 1)^n := pow_le_pow_left₀ (by norm_num) htwo _
    _ = Real.exp (n:ℝ) := by rw [← Real.exp_nat_mul]; simp
    _ ≤ _ := Real.exp_le_exp.mpr htu
  have hdec : (A:ℝ) * (Real.exp (-u))^t ≤ 1 := by
    rw [← Real.exp_nat_mul, mul_neg, Real.exp_neg, ← div_eq_mul_inv]
    exact (div_le_one (Real.exp_pos _)).mpr heA
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg (A-V)) hbase t
  rw [mul_pow] at hp
  have target : (A:ℝ)*((A-V : ℕ):ℝ)^t ≤ (A:ℝ)^t := calc
    _ ≤ (A:ℝ)*((A:ℝ)^t * Real.exp (-u)^t) := mul_le_mul_of_nonneg_left hp haR.le
    _ = ((A:ℝ)*Real.exp (-u)^t) * (A:ℝ)^t := by ring
    _ ≤ 1*(A:ℝ)^t := mul_le_mul_of_nonneg_right hdec (by positivity)
    _ = _ := one_mul _
  exact_mod_cast target

lemma selected_radius (n a : ℕ) :
    ∃ r ≤ n, (a+1)^n ≤ (n+1) * (n.choose r * a^(n-r)) := by
  classical
  let f (i : ℕ) := n.choose i * a^(n-i)
  have hn : (Finset.range (n+1)).Nonempty := ⟨0, by simp⟩
  obtain ⟨r, hr, hmax⟩ := (Finset.range (n+1)).exists_max_image f hn
  refine ⟨r, Nat.le_of_lt_succ (Finset.mem_range.mp hr), ?_⟩
  calc
    _ = ∑ i ∈ Finset.range (n+1), f i := by
      rw [Nat.add_comm a 1, add_pow]
      simp [f, Nat.mul_comm]
    _ ≤ ∑ _i ∈ Finset.range (n+1), f r := Finset.sum_le_sum hmax
    _ = _ := by simp [f]

end PEqualNP.Outside.L_lib_510

open PEqualNP.Outside

theorem PEqualNP.Outside.L_lib_510 :
    ∀ (n a : Nat), 0 < a →
      let Point := Fin n → Bool
      let dist := fun (x y : Point) =>
        ((Finset.univ : Finset (Fin n)).filter (fun i => x i ≠ y i)).card
      ∃ (r : Nat) (C : Finset Point), r ≤ n ∧ (∀ y : Point, ∃ c ∈ C, dist c y ≤ r) ∧
        C.card * a^r * (a+1)^n ≤ (n+2)*(n+1)*(2*a)^n := by
  intro n a _
  dsimp only
  classical
  obtain ⟨r, hr, hmax⟩ := L_lib_510.selected_radius n a
  let A := 2^n
  let V := ((List.range (r+1)).map (fun j => n.choose j * (2-1)^j)).sum
  have hA : 0 < A := by dsimp [A]; positivity
  have hsmall : n.choose r ≤ V := by
    apply List.le_sum_of_mem
    exact List.mem_map.mpr ⟨r, by simp, by simp⟩
  have hV : 0 < V := (Nat.choose_pos hr).trans_le hsmall
  have hVA : V ≤ A := by
    have h := Finset.card_le_univ ((Finset.univ : Finset (Fin n → Fin 2)).filter
      (fun y => (L_lib_510.mismatch (fun _ => 0) y).card ≤ r))
    rw [L_lib_510.volume] at h
    simpa [V,A] using h
  let t := n*A/V+1
  have hmul : n*A ≤ t*V := by
    apply Nat.le_of_lt
    exact (Nat.div_lt_iff_lt_mul hV).mp (Nat.lt_succ_self _)
  have hsize : t*V ≤ n*A+V := by
    dsimp [t]
    rw [Nat.add_mul, one_mul]
    exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
  have rem := L_lib_510.remainder_bound n A V t rfl hVA hmul
  obtain ⟨C, cov, sz⟩ := L_lib_510.alteration 2 n r t (by decide) hr
  change C.card * A^t ≤ t*A^t + A*(A-V)^t at sz
  have cardBound : C.card ≤ t+1 := by
    refine Nat.le_of_mul_le_mul_right ?_ (pow_pos hA t)
    calc
      _ ≤ _ := sz
      _ ≤ t*A^t + A^t := Nat.add_le_add_left rem _
      _ = _ := by ring
  have bound : C.card*n.choose r ≤ (n+2)*A := calc
    _ ≤ (t+1)*V := Nat.mul_le_mul cardBound hsmall
    _ = t*V + V := by ring
    _ ≤ n*A+V+V := Nat.add_le_add_right hsize _
    _ ≤ n*A+A+A := Nat.add_le_add (Nat.add_le_add_left hVA _) hVA
    _ = _ := by ring
  let e : (Fin n → Fin 2) ≃ (Fin n → Bool) := Equiv.piCongrRight (fun _ => finTwoEquiv)
  refine ⟨r, C.map e.toEmbedding, hr, ?_, ?_⟩
  · intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨c, hc, hd⟩ := cov x
    refine ⟨e c, Finset.mem_map.mpr ⟨c, hc, rfl⟩, ?_⟩
    simpa [e, eq_comm] using hd
  · rw [Finset.card_map]
    calc
      _ ≤ C.card*a^r*((n+1)*(n.choose r*a^(n-r))) := Nat.mul_le_mul_left _ hmax
      _ = (C.card*n.choose r)*(n+1)*(a^r*a^(n-r)) := by ring
      _ = (C.card*n.choose r)*(n+1)*a^n := by rw [← pow_add, Nat.add_sub_of_le hr]
      _ ≤ ((n+2)*A)*(n+1)*a^n := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ bound)
      _ = _ := by rw [mul_pow]; dsimp [A]; ring
