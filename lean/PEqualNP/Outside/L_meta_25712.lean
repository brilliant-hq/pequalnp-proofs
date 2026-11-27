import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25712

open Finset

theorem two_choose (s : ℕ) : 2 * s.choose 2 + s = s * s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith [ih]

theorem cast_mul_pred (a : ℕ) : ((a * (a - 1) : ℕ) : ℤ) = (a : ℤ) * a - a := by
  cases a with
  | zero => simp
  | succ a => simp only [Nat.add_sub_cancel]; push_cast; ring

/-- Balanced classes minimize the number of within-class pairs. -/
theorem balance {n : ℕ} {K : Type} [Fintype K] [DecidableEq K] (c : ℕ)
    (hcK : Fintype.card K = c) (hc : 0 < c) (κ : Fin n → K) :
    (c - n % c) * Nat.choose (n / c) 2 + n % c * Nat.choose (n / c + 1) 2 ≤
      (univ.filter (fun z : Fin n × Fin n => z.1 < z.2 ∧ κ z.1 = κ z.2)).card := by
  set s := n / c with hs
  set r := n % c with hr
  have hnr : c * s + r = n := Nat.div_add_mod n c
  have hrc : r ≤ c := (Nat.mod_lt n hc).le
  set m : K → ℕ := fun k => (univ.filter (fun x : Fin n => κ x = k)).card with hm
  have hsum : ∑ k, m k = n := by
    have := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n)))
      (t := (univ : Finset K)) (f := κ) (fun x _ => mem_univ _)
    simpa [m] using this.symm
  set A := univ.filter (fun z : Fin n × Fin n => z.1 < z.2 ∧ κ z.1 = κ z.2) with hA
  set B := univ.filter (fun z : Fin n × Fin n => z.2 < z.1 ∧ κ z.1 = κ z.2) with hB
  set D := univ.filter (fun z : Fin n × Fin n => z.1 ≠ z.2 ∧ κ z.1 = κ z.2) with hD
  have hDAB : D.card = A.card + B.card := by
    rw [← card_union_of_disjoint]
    · congr 1
      ext z
      simp only [hA, hB, hD, mem_filter, mem_univ, true_and, mem_union]
      constructor
      · rintro ⟨h1, h2⟩
        rcases lt_or_gt_of_ne h1 with h | h
        · exact Or.inl ⟨h, h2⟩
        · exact Or.inr ⟨h, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨ne_of_lt h1, h2⟩
        · exact ⟨ne_of_gt h1, h2⟩
    · rw [disjoint_left]
      intro z h1 h2
      simp only [hA, hB, mem_filter, mem_univ, true_and] at h1 h2
      exact lt_asymm h1.1 h2.1
  have hBA : B.card = A.card := by
    apply card_nbij' Prod.swap Prod.swap
    · intro z hz
      simp only [hA, hB, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hz ⊢
      exact ⟨hz.1, hz.2.symm⟩
    · intro z hz
      simp only [hA, hB, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hz ⊢
      exact ⟨hz.1, hz.2.symm⟩
    · intro z _
      simp
    · intro z _
      simp
  have hDsum : D.card = ∑ x : Fin n, (m (κ x) - 1) := by
    rw [hD, card_filter, ← univ_product_univ, sum_product]
    apply sum_congr rfl
    intro x _
    rw [← card_filter]
    have : (univ.filter (fun y : Fin n => x ≠ y ∧ κ x = κ y)) =
        (univ.filter (fun y : Fin n => κ y = κ x)).erase x := by
      ext y
      simp only [mem_filter, mem_univ, true_and, mem_erase]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨Ne.symm h1, h2.symm⟩
      · rintro ⟨h1, h2⟩
        exact ⟨Ne.symm h1, h2.symm⟩
    rw [this, card_erase_of_mem (by simp)]
  have hDk : D.card = ∑ k, m k * (m k - 1) := by
    rw [hDsum]
    refine (sum_fiberwise_of_maps_to' (s := univ) (g := κ) (t := univ) (fun _ _ => mem_univ _)
      (fun k => m k - 1)).symm.trans ?_
    apply sum_congr rfl
    intro k _
    show ∑ i ∈ univ.filter (fun i => κ i = k), (m k - 1) = m k * (m k - 1)
    rw [sum_const, smul_eq_mul]
  have hz : (2 * ((c - r) * Nat.choose s 2 + r * Nat.choose (s + 1) 2) : ℤ) ≤ (D.card : ℤ) := by
    have e1 := two_choose s
    have e2 := two_choose (s + 1)
    have e1' : (2 * (Nat.choose s 2 : ℤ)) = s * s - s := by
      have : ((2 * s.choose 2 + s : ℕ) : ℤ) = ((s * s : ℕ) : ℤ) := by rw [e1]
      push_cast at this
      linarith
    have e2' : (2 * (Nat.choose (s + 1) 2 : ℤ)) = s * s + s := by
      have : ((2 * (s + 1).choose 2 + (s + 1) : ℕ) : ℤ) = (((s + 1) * (s + 1) : ℕ) : ℤ) := by
        rw [e2]
      push_cast at this
      linarith
    have hsumZ : (∑ k, (m k : ℤ)) = n := by exact_mod_cast hsum
    have hnrZ : (c : ℤ) * s + r = n := by exact_mod_cast hnr
    have hcard : (Finset.univ : Finset K).card = c := by rw [card_univ, hcK]
    have key : (∑ k, (2 * (s : ℤ) * m k - s * s - s)) ≤ ∑ k, ((m k : ℤ) * m k - m k) := by
      apply sum_le_sum
      intro k _
      rcases le_or_gt (m k) s with h | h
      · have h' : (m k : ℤ) ≤ s := by exact_mod_cast h
        nlinarith [mul_nonneg (sub_nonneg.2 h') (by linarith : (0 : ℤ) ≤ s - m k + 1)]
      · have h' : (s : ℤ) + 1 ≤ m k := by exact_mod_cast h
        nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ m k - s - 1) (by linarith : (0 : ℤ) ≤ m k - s)]
    have hL : (∑ k, (2 * (s : ℤ) * m k - s * s - s)) = 2 * s * n - c * (s * s + s) := by
      rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum, hsumZ]
      simp only [sum_const, hcard, nsmul_eq_mul]
      ring
    have hDZ : (D.card : ℤ) = ∑ k, ((m k : ℤ) * m k - m k) := by
      rw [hDk]
      push_cast
      apply sum_congr rfl
      intro k _
      exact cast_mul_pred (m k)
    rw [hDZ]
    have goalEq : (2 * (((c : ℤ) - r) * (Nat.choose s 2 : ℤ) + r * (Nat.choose (s + 1) 2 : ℤ))) =
        2 * s * n - c * (s * s + s) := by
      rw [← hnrZ]
      linear_combination ((c : ℤ) - r) * e1' + (r : ℤ) * e2'
    linarith [key, hL, goalEq]
  have : 2 * ((c - r) * Nat.choose s 2 + r * Nat.choose (s + 1) 2) ≤ D.card := by
    exact_mod_cast hz
  omega

theorem count_small {n : ℕ} (T : Finset (Fin n × Fin n)) (e : ℕ) :
    (univ.filter (fun H : Fin n → Fin n → Bool =>
      (T.filter (fun c => H c.1 c.2 = true)).card ≤ e)).card * 2 ^ T.card
      ≤ (∑ j ∈ range (e + 1), Nat.choose T.card j) * 2 ^ (n * n) := by
  classical
  have h1 : (univ.filter (fun H : Fin n → Fin n → Bool =>
      (T.filter (fun c => H c.1 c.2 = true)).card ≤ e)).card ≤
      ((T.powerset.filter (fun s => s.card ≤ e)) ×ˢ Tᶜ.powerset).card := by
    apply card_le_card_of_injOn (fun H => (T.filter (fun c => H c.1 c.2 = true),
      Tᶜ.filter (fun c => H c.1 c.2 = true)))
    · intro H hH
      rw [mem_coe, mem_filter] at hH
      rw [mem_coe, mem_product, mem_filter, mem_powerset, mem_powerset]
      exact ⟨⟨filter_subset _ _, hH.2⟩, filter_subset _ _⟩
    · intro H _ H' _ hHH
      simp only [Prod.mk.injEq] at hHH
      funext x y
      by_cases hxy : (x, y) ∈ T
      · have := congrArg (fun s => (x, y) ∈ s) hHH.1
        simp only [mem_filter, hxy, true_and, eq_iff_iff] at this
        cases hx : H x y <;> cases hx' : H' x y <;> simp_all
      · have := congrArg (fun s => (x, y) ∈ s) hHH.2
        simp only [mem_filter, mem_compl, hxy, not_false_eq_true, true_and, eq_iff_iff] at this
        cases hx : H x y <;> cases hx' : H' x y <;> simp_all
  have h2 : ((T.powerset.filter (fun s => s.card ≤ e))).card ≤
      ∑ j ∈ range (e + 1), Nat.choose T.card j := by
    calc _ ≤ ((range (e + 1)).biUnion (fun j => T.powersetCard j)).card := by
          apply card_le_card
          intro s hs
          simp only [mem_filter, mem_powerset] at hs
          simp only [mem_biUnion, mem_range, mem_powersetCard]
          exact ⟨s.card, by omega, hs.1, rfl⟩
      _ ≤ ∑ j ∈ range (e + 1), (T.powersetCard j).card := card_biUnion_le
      _ = _ := by simp [card_powersetCard]
  have h3 : Tᶜ.card + T.card = n * n := by
    rw [card_compl]
    have := card_le_univ T
    simp only [Fintype.card_prod, Fintype.card_fin] at this ⊢
    omega
  rw [card_product, card_powerset] at h1
  calc _ ≤ ((T.powerset.filter (fun s => s.card ≤ e)).card * 2 ^ Tᶜ.card) * 2 ^ T.card :=
        Nat.mul_le_mul_right _ h1
    _ ≤ ((∑ j ∈ range (e + 1), Nat.choose T.card j) * 2 ^ Tᶜ.card) * 2 ^ T.card := by gcongr
    _ = _ := by rw [mul_assoc, ← pow_add, h3]

def failB {n : ℕ} (G : Fin n → Fin n → Bool) (π : Equiv.Perm (Fin n)) (l : Fin n → Bool)
    (z : Fin n × Fin n) : Bool :=
  xor (xor (G z.1 (π z.2)) (G z.2 (π z.1))) (xor (l z.1) (l z.2))

def phi {n : ℕ} (sel : Finset (Fin n × Fin n)) (π : Equiv.Perm (Fin n)) (l : Fin n → Bool)
    (G : Fin n → Fin n → Bool) : Fin n → Fin n → Bool := fun x y =>
  if (x, π.symm y) ∈ sel then
    xor (xor (G x y) (G (π.symm y) (π x))) (xor (l x) (l (π.symm y)))
  else G x y

theorem xor4 (a b c d : Bool) : xor (xor (xor (xor a b) (xor c d)) b) (xor c d) = a := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem bad_count {n : ℕ} (sel : Finset (Fin n × Fin n)) (hsel : ∀ z ∈ sel, z.1 < z.2)
    (π : Equiv.Perm (Fin n)) (l : Fin n → Bool) (e : ℕ) :
    (univ.filter (fun G : Fin n → Fin n → Bool =>
      (sel.filter (fun z => failB G π l z = true)).card ≤ e)).card * 2 ^ sel.card
      ≤ (∑ j ∈ range (e + 1), Nat.choose sel.card j) * 2 ^ (n * n) := by
  classical
  set T := sel.image (fun z => (z.1, π z.2)) with hTdef
  have hinj : Function.Injective (fun z : Fin n × Fin n => (z.1, π z.2)) := by
    intro a b h
    simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
    exact Prod.ext h.1 h.2
  have hT : T.card = sel.card := card_image_of_injective _ hinj
  have hinv : ∀ G, phi sel π l (phi sel π l G) = G := by
    intro G
    funext x y
    by_cases h : (x, π.symm y) ∈ sel
    · have h2 : (π.symm y, π.symm (π x)) ∉ sel := by
        rw [Equiv.symm_apply_apply]
        intro h'
        exact lt_asymm (hsel _ h) (hsel _ h')
      simp only [phi, h, h2, if_true, if_false]
      exact xor4 _ _ _ _
    · simp only [phi, h, if_false]
  have hval : ∀ G, ∀ z ∈ sel, phi sel π l G z.1 (π z.2) = failB G π l z := by
    intro G z hz
    simp [phi, hz, failB]
  have hle : (univ.filter (fun G : Fin n → Fin n → Bool =>
      (sel.filter (fun z => failB G π l z = true)).card ≤ e)).card ≤
      (univ.filter (fun H : Fin n → Fin n → Bool =>
        (T.filter (fun c => H c.1 c.2 = true)).card ≤ e)).card := by
    apply card_le_card_of_injOn (phi sel π l)
    · intro G hG
      rw [mem_coe, mem_filter] at hG
      rw [mem_coe, mem_filter]
      refine ⟨mem_univ _, ?_⟩
      replace hG := hG.2
      have : (T.filter (fun c => phi sel π l G c.1 c.2 = true)) =
          (sel.filter (fun z => failB G π l z = true)).image (fun z => (z.1, π z.2)) := by
        rw [hTdef, filter_image]
        congr 1
        apply filter_congr
        intro z hz
        rw [hval G z hz]
      rw [this, card_image_of_injective _ hinj]
      exact hG
    · intro G _ G' _ h
      have h' : phi sel π l (phi sel π l G) = phi sel π l (phi sel π l G') := by
        rw [h]
      rwa [hinv, hinv] at h'
  have := count_small T e
  rw [hT] at this
  calc _ ≤ _ := Nat.mul_le_mul_right _ hle
    _ ≤ _ := this

def cls {n q : ℕ} (π : Equiv.Perm (Fin n)) (R C : Fin q → Finset (Fin n)) (x : Fin n) :
    Fin q → Fin 3 :=
  fun j => if x ∈ R j then 0 else if π x ∈ C j then 1 else 2

theorem bits_eq {n q : ℕ} (π : Equiv.Perm (Fin n)) (R C : Fin q → Finset (Fin n)) (a b : Fin n)
    (h : cls π R C a = cls π R C b) :
    (fun j => decide (b ∈ R j ∨ π a ∈ C j)) = (fun j => decide (a ∈ R j ∨ π b ∈ C j)) := by
  funext j
  have hj := congrFun h j
  simp only [cls] at hj
  by_cases ha : a ∈ R j <;> by_cases hb : b ∈ R j <;> by_cases hpa : π a ∈ C j <;>
    by_cases hpb : π b ∈ C j <;> simp_all

theorem xor_fact (A B r1 c1 r2 c2 : Bool)
    (hf : xor (xor A B) (xor (xor r1 c1) (xor r2 c2)) = true) :
    xor A (xor r1 c2) ≠ xor B (xor r2 c1) := by
  revert hf
  cases A <;> cases B <;> cases r1 <;> cases c1 <;> cases r2 <;> cases c2 <;> decide

theorem loss_ge {n q : ℕ} (G : Fin n → Fin n → Bool) (π : Equiv.Perm (Fin n))
    (rowFlip colFlip : Fin n → Bool)
    (R C : Fin q → Finset (Fin n)) (out : Finset (Fin n) → (Fin q → Bool) → Bool)
    (sel : Finset (Fin n × Fin n))
    (hsel : ∀ z ∈ sel, z.1 < z.2 ∧ cls π R C z.1 = cls π R C z.2) :
    (sel.filter (fun z => failB G π (fun x => xor (rowFlip x) (colFlip (π x))) z = true)).card ≤
    ((Finset.univ : Finset (Fin n × Fin n)).filter (fun z =>
      out {z.1,z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
        Bool.xor (G z.1 (π z.2)) (Bool.xor (rowFlip z.1) (colFlip (π z.2))))).card := by
  classical
  apply card_le_card_of_injOn (fun z =>
    if out {z.1,z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
        Bool.xor (G z.1 (π z.2)) (Bool.xor (rowFlip z.1) (colFlip (π z.2))) then z else z.swap)
  · intro z hz
    dsimp only
    rw [mem_coe, mem_filter] at hz
    obtain ⟨hzs, hf⟩ := hz
    obtain ⟨_, hc⟩ := hsel z hzs
    have hv : out {z.2, z.1} (fun j => decide (z.2 ∈ R j ∨ π z.1 ∈ C j)) =
        out {z.1, z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) := by
      rw [Finset.pair_comm, bits_eq π R C z.1 z.2 hc]
    by_cases h : out {z.1,z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
        Bool.xor (G z.1 (π z.2)) (Bool.xor (rowFlip z.1) (colFlip (π z.2)))
    · rw [if_pos h, mem_coe, mem_filter]
      exact ⟨mem_univ _, h⟩
    · rw [if_neg h, mem_coe, mem_filter]
      refine ⟨mem_univ _, ?_⟩
      simp only [Prod.fst_swap, Prod.snd_swap]
      rw [hv]
      push_neg at h
      rw [h]
      simp only [failB] at hf
      exact xor_fact _ _ _ _ _ _ hf
  · intro z hz z' hz' heq
    rw [mem_coe, mem_filter] at hz hz'
    have h1 := (hsel z hz.1).1
    have h2 := (hsel z' hz'.1).1
    simp only at heq
    split_ifs at heq with ha hb hb
    · exact heq
    · rw [heq] at h1
      simp only [Prod.fst_swap, Prod.snd_swap] at h1
      exact (lt_asymm h1 h2).elim
    · rw [← heq] at h2
      simp only [Prod.fst_swap, Prod.snd_swap] at h2
      exact (lt_asymm h1 h2).elim
    · exact Prod.swap_injective heq

end PEqualNP.Outside.L_meta_25712

open PEqualNP.Outside.L_meta_25712 in
theorem PEqualNP.Outside.L_meta_25712 : ∀ (n q e : ℕ),
  let I := Fin n
  let Table := I → I → Bool
  let loss := fun (G : Table) (q : ℕ) (π : Equiv.Perm I) (rowFlip colFlip : I → Bool)
      (R C : Fin q → Finset I) (out : Finset I → (Fin q → Bool) → Bool) =>
    ((Finset.univ : Finset (I × I)).filter (fun z =>
      out {z.1,z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
        Bool.xor (G z.1 (π z.2)) (Bool.xor (rowFlip z.1) (colFlip (π z.2))))).card
  let colors := 3^q
  let small := n/colors
  let rem := n%colors
  let pairs := (colors-rem)*Nat.choose small 2 + rem*Nat.choose (small+1) 2
  n.factorial*(2*colors)^n*(∑ j ∈ Finset.range (e+1), Nat.choose pairs j) < 2^pairs →
    ∃ G : Table, ∀ (π : Equiv.Perm I) (rowFlip colFlip : I → Bool)
      (R C : Fin q → Finset I) (out : Finset I → (Fin q → Bool) → Bool),
      e < loss G q π rowFlip colFlip R C out := by
  intro n q e I Table loss colors small rem pairs hyp
  classical
  by_contra hcon
  push_neg at hcon
  have hbal : ∀ κ : Fin n → (Fin q → Fin 3), pairs ≤
      (Finset.univ.filter (fun z : Fin n × Fin n => z.1 < z.2 ∧ κ z.1 = κ z.2)).card := by
    intro κ
    exact balance (3 ^ q) (by simp) (by positivity) κ
  choose sel hselsub hselcard using fun κ : Fin n → (Fin q → Fin 3) =>
    Finset.exists_subset_card_eq (hbal κ)
  have hselW : ∀ κ, ∀ z ∈ sel κ, z.1 < z.2 ∧ κ z.1 = κ z.2 := by
    intro κ z hz
    have := hselsub κ hz
    simpa using this
  let Bad := fun t : Equiv.Perm (Fin n) × (Fin n → (Fin q → Fin 3)) × (Fin n → Bool) =>
    Finset.univ.filter (fun G : Fin n → Fin n → Bool =>
      ((sel t.2.1).filter (fun z => failB G t.1 t.2.2 z = true)).card ≤ e)
  have hcover : (Finset.univ : Finset (Fin n → Fin n → Bool)) ⊆
      (Finset.univ : Finset (Equiv.Perm (Fin n) × (Fin n → (Fin q → Fin 3)) ×
        (Fin n → Bool))).biUnion Bad := by
    intro G _
    obtain ⟨π, rf, cf, R, C, out, hl⟩ := hcon G
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Bad, Finset.mem_filter]
    refine ⟨(π, cls π R C, fun x => xor (rf x) (cf (π x))), ?_⟩
    exact le_trans (loss_ge G π rf cf R C out (sel (cls π R C)) (hselW _)) hl
  set S := ∑ j ∈ Finset.range (e + 1), Nat.choose pairs j with hS
  have hbad : ∀ t, (Bad t).card * 2 ^ pairs ≤ S * 2 ^ (n * n) := by
    intro t
    have := bad_count (sel t.2.1) (fun z hz => (hselW t.2.1 z hz).1) t.1 t.2.2 e
    rw [hselcard] at this
    exact this
  have hM : Fintype.card (Equiv.Perm (Fin n) × (Fin n → (Fin q → Fin 3)) × (Fin n → Bool)) =
      n.factorial * ((3 ^ q) ^ n * 2 ^ n) := by
    simp [Fintype.card_prod, Fintype.card_perm, Fintype.card_fun]
  have hcard : 2 ^ (n * n) * 2 ^ pairs ≤
      (n.factorial * ((3 ^ q) ^ n * 2 ^ n)) * (S * 2 ^ (n * n)) := by
    calc 2 ^ (n * n) * 2 ^ pairs
        = (Finset.univ : Finset (Fin n → Fin n → Bool)).card * 2 ^ pairs := by
          simp [Finset.card_univ, Fintype.card_fun, pow_mul]
      _ ≤ ((Finset.univ : Finset (Equiv.Perm (Fin n) × (Fin n → (Fin q → Fin 3)) ×
            (Fin n → Bool))).biUnion Bad).card * 2 ^ pairs :=
          Nat.mul_le_mul_right _ (Finset.card_le_card hcover)
      _ ≤ (∑ t, (Bad t).card) * 2 ^ pairs := Nat.mul_le_mul_right _ Finset.card_biUnion_le
      _ = ∑ t, (Bad t).card * 2 ^ pairs := Finset.sum_mul _ _ _
      _ ≤ ∑ _t : Equiv.Perm (Fin n) × (Fin n → (Fin q → Fin 3)) × (Fin n → Bool),
            S * 2 ^ (n * n) := Finset.sum_le_sum (fun t _ => hbad t)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, hM, smul_eq_mul]
  have hyp' : n.factorial * ((3 ^ q) ^ n * 2 ^ n) * S < 2 ^ pairs := by
    have : n.factorial * (2 * colors) ^ n * S < 2 ^ pairs := hyp
    calc n.factorial * ((3 ^ q) ^ n * 2 ^ n) * S = n.factorial * (2 * colors) ^ n * S := by
          simp only [colors, mul_pow]
          ring
      _ < 2 ^ pairs := this
  have hpos : 0 < 2 ^ (n * n) := by positivity
  have := Nat.mul_lt_mul_of_pos_right hyp' hpos
  have h2 : n.factorial * ((3 ^ q) ^ n * 2 ^ n) * (S * 2 ^ (n * n)) =
      n.factorial * ((3 ^ q) ^ n * 2 ^ n) * S * 2 ^ (n * n) := by ring
  linarith
