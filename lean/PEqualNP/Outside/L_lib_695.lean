import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_695

lemma dyadic_max_depth {α : Type*} [DecidableEq α] :
    ∀ (m : ℕ) (S : Finset α) (M d : ℕ) (a : α → ℕ),
      S.card = m →
      (∀ x ∈ S, a x ≤ M) →
      2 ^ M ∣ ∑ x ∈ S, 2 ^ (M - a x + d) →
      ∀ x ∈ S, a x ≤ d + m - 1 := by
  intro m
  induction m with
  | zero =>
    intro S _ _ _ hcard _ _ x hx
    rw [Finset.card_eq_zero.mp hcard] at hx
    exact False.elim (Finset.notMem_empty x hx)
  | succ m ih =>
    intro S M d a hcard hle hdiv x hx
    by_cases hxd : a x ≤ d
    · omega
    · have hne : S.Nonempty := ⟨x, hx⟩
      obtain ⟨y0, hy0, hmax⟩ := Finset.exists_max_image S a hne
      set amax := a y0
      have hamax_gt : d < amax := lt_of_lt_of_le (by omega : d < a x) (hmax x hx)
      have hamax_le : amax ≤ M := hle y0 hy0
      set emin := M - amax + d
      have hemin_lt : emin < M := by omega
      let Top := S.filter (fun y => a y = amax)
      let Rest := S.filter (fun y => ¬ a y = amax)
      have hsplit : ∑ y ∈ S, 2 ^ (M - a y + d) =
          Top.card * 2 ^ emin + ∑ y ∈ Rest, 2 ^ (M - a y + d) := by
        rw [← Finset.sum_filter_add_sum_filter_not S (fun y => a y = amax)]
        congr 1
        have hconst : ∀ y ∈ Top, 2 ^ (M - a y + d) = 2 ^ emin := fun y hy => by
          have ha : a y = amax := (Finset.mem_filter.mp hy).2
          rw [ha]
        rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
      have hdvd_total : 2 ^ (emin + 1) ∣ ∑ y ∈ S, 2 ^ (M - a y + d) :=
        dvd_trans (Nat.pow_dvd_pow 2 (by omega : emin + 1 ≤ M)) hdiv
      have hdvd_rest : 2 ^ (emin + 1) ∣ ∑ y ∈ Rest, 2 ^ (M - a y + d) := by
        refine Finset.dvd_sum fun y hy => ?_
        have hyS : y ∈ S := (Finset.mem_filter.mp hy).1
        have hyne : a y ≠ amax := (Finset.mem_filter.mp hy).2
        have hyle : a y ≤ amax := hmax y hyS
        exact Nat.pow_dvd_pow 2 (by omega : emin + 1 ≤ M - a y + d)
      have hdvd_top : 2 ^ (emin + 1) ∣ Top.card * 2 ^ emin := by
        rw [hsplit] at hdvd_total
        exact (Nat.dvd_add_left hdvd_rest).mp hdvd_total
      have h2_top : 2 ∣ Top.card := by
        rw [pow_succ] at hdvd_top
        have hpos : 0 < 2 ^ emin := by positivity
        rcases hdvd_top with ⟨k, hk⟩
        refine ⟨k, ?_⟩
        have hmul : Top.card * 2 ^ emin = (2 * k) * 2 ^ emin := by linarith
        exact Nat.eq_of_mul_eq_mul_right hpos hmul
      have hy0_top : y0 ∈ Top := Finset.mem_filter.mpr ⟨hy0, rfl⟩
      have htop_pos : 0 < Top.card := Finset.card_pos.mpr ⟨y0, hy0_top⟩
      have htop_ge2 : 2 ≤ Top.card := by
        rcases h2_top with ⟨k, hk⟩
        omega
      have hex_uv : ∃ u ∈ Top, ∃ v ∈ Top, u ≠ v ∧ v ≠ x := by
        by_cases hxT : x ∈ Top
        · have hpos : 0 < (Top.erase x).card := by
            rw [Finset.card_erase_of_mem hxT]; omega
          obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
          rw [Finset.mem_erase] at hv
          exact ⟨x, hxT, v, hv.2, hv.1.symm, hv.1⟩
        · have hpos : 0 < (Top.erase y0).card := by
            rw [Finset.card_erase_of_mem hy0_top]; omega
          obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
          rw [Finset.mem_erase] at hv
          have hvx : v ≠ x := fun h => hxT (h ▸ hv.2)
          exact ⟨y0, hy0_top, v, hv.2, hv.1.symm, hvx⟩
      obtain ⟨u, huT, v, hvT, huv, hvx⟩ := hex_uv
      have huS : u ∈ S := (Finset.mem_filter.mp huT).1
      have hvS : v ∈ S := (Finset.mem_filter.mp hvT).1
      have hau : a u = amax := (Finset.mem_filter.mp huT).2
      have hav : a v = amax := (Finset.mem_filter.mp hvT).2
      let S' := S.erase v
      let a' : α → ℕ := fun y => if y = u then a u - 1 else a y
      have hcard' : S'.card = m := by
        rw [Finset.card_erase_of_mem hvS, hcard]; omega
      have hle' : ∀ y ∈ S', a' y ≤ M := by
        intro y hy
        have hyS : y ∈ S := Finset.mem_of_mem_erase hy
        dsimp only [a']
        split_ifs
        · have := hle y hyS; omega
        · exact hle y hyS
      have hsum_eq : ∑ y ∈ S', 2 ^ (M - a' y + d) = ∑ y ∈ S, 2 ^ (M - a y + d) := by
        have huS' : u ∈ S' := Finset.mem_erase.mpr ⟨huv, huS⟩
        rw [← Finset.add_sum_erase S' (fun y => 2 ^ (M - a' y + d)) huS']
        rw [← Finset.add_sum_erase S (fun y => 2 ^ (M - a y + d)) hvS]
        have huS_v : u ∈ S.erase v := huS'
        rw [← Finset.add_sum_erase (S.erase v) (fun y => 2 ^ (M - a y + d)) huS_v]
        have htail : ∑ y ∈ S'.erase u, 2 ^ (M - a' y + d) =
            ∑ y ∈ (S.erase v).erase u, 2 ^ (M - a y + d) := by
          refine Finset.sum_congr rfl fun y hy => ?_
          have hyu : y ≠ u := (Finset.mem_erase.mp hy).1
          simp [a', hyu]
        rw [htail]
        have hmerge : 2 ^ (M - a' u + d) = 2 ^ (M - a v + d) + 2 ^ (M - a u + d) := by
          simp only [a', ↓reduceIte, hau, hav]
          have hexp : M - (amax - 1) + d = (M - amax + d) + 1 := by omega
          rw [hexp, pow_succ]; ring
        linarith
      have hdiv' : 2 ^ M ∣ ∑ y ∈ S', 2 ^ (M - a' y + d) := by rw [hsum_eq]; exact hdiv
      have hxS' : x ∈ S' := Finset.mem_erase.mpr ⟨hvx.symm, hx⟩
      have hih := ih S' M d a' hcard' hle' hdiv' x hxS'
      have hm_pos : 1 ≤ m := by
        have h2 : 2 ≤ S.card := by
          calc 2 ≤ Top.card := htop_ge2
            _ ≤ S.card := Finset.card_le_card (Finset.filter_subset _ _)
        omega
      dsimp only [a'] at hih
      by_cases hxu : x = u
      · have hax : a x = a u := congrArg a hxu
        rw [if_pos hxu] at hih; omega
      · rw [if_neg hxu] at hih; omega

lemma sum_partition_012 {α : Type*} [Fintype α] [DecidableEq α]
    (ch : α → ℕ) (hch : ∀ t, ch t ≤ 2) (g : α → ℕ) (hg0 : ∀ t, ch t = 0 → g t = 0) :
    ∑ t : α, g t =
      ∑ t ∈ Finset.univ.filter (fun u : α => ch u = 1), g t +
      ∑ t ∈ Finset.univ.filter (fun u : α => ch u = 2), g t := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun u : α => ch u = 2)]
  rw [Nat.add_comm]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter (fun u : α => ¬ ch u = 2))
      (fun u : α => ch u = 1)]
  have h1 : (Finset.univ.filter (fun u : α => ¬ ch u = 2)).filter (fun u : α => ch u = 1) =
      Finset.univ.filter (fun u : α => ch u = 1) := by
    ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨by omega, h⟩
  have h0 : ∑ u ∈ (Finset.univ.filter (fun u : α => ¬ ch u = 2)).filter (fun u : α => ¬ ch u = 1),
      g u = 0 := by
    refine Finset.sum_eq_zero fun u hu => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    have hle := hch u
    exact hg0 u (by omega)
  rw [h1, h0, Nat.add_zero]

lemma prod_pow_012 {α : Type*} [Fintype α] [DecidableEq α]
    (ch : α → ℕ) (hch : ∀ t, ch t ≤ 2) (g : α → ℕ) (hg0 : ∀ t, ch t = 0 → g t = 0) :
    ∏ t : α, (ch t) ^ (g t) = 2 ^ (∑ t ∈ Finset.univ.filter (fun u : α => ch u = 2), g t) := by
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun u : α => ch u = 2)]
  have h2 : ∏ t ∈ Finset.univ.filter (fun u : α => ch u = 2), (ch t) ^ (g t) =
      2 ^ (∑ t ∈ Finset.univ.filter (fun u : α => ch u = 2), g t) := by
    have hcongr : ∀ t ∈ Finset.univ.filter (fun u : α => ch u = 2),
        (ch t) ^ (g t) = 2 ^ (g t) := fun t ht => by
      rw [(Finset.mem_filter.mp ht).2]
    rw [Finset.prod_congr rfl hcongr, Finset.prod_pow_eq_pow_sum]
  have hnot2 : ∏ t ∈ Finset.univ.filter (fun u : α => ¬ ch u = 2), (ch t) ^ (g t) = 1 := by
    refine Finset.prod_eq_one fun t ht => ?_
    have hne2 : ch t ≠ 2 := (Finset.mem_filter.mp ht).2
    have hle := hch t
    have h01 : ch t = 0 ∨ ch t = 1 := by omega
    rcases h01 with h0 | h1
    · rw [hg0 t h0, pow_zero]
    · rw [h1, one_pow]
  rw [h2, hnot2, mul_one]

end PEqualNP.Outside.L_lib_695

open PEqualNP.Outside.L_lib_695 in
theorem PEqualNP.Outside.L_lib_695 : let W := fun k : ℕ => Fin k → Bool
let Lit := fun k : ℕ => Fin k × Bool
let F := fun k : ℕ => Finset (Lit k × Lit k)
∀ c d : ℕ,
  let T := Finset (Lit c × Bool)
  let choices := fun (t : T) (w : W c) =>
    (Finset.univ.filter (fun b : Bool => ∀ edge ∈ t,
      w edge.1.1 ≠ edge.1.2 ∨ b ≠ edge.2)).card
  let width := fun h : T → ℕ => c + ∑ t, h t
  let fiber := fun (D : F c) (h : T → ℕ) (w : W c) =>
    if ∀ e ∈ D, w e.1.1 ≠ e.1.2 ∨ w e.2.1 ≠ e.2.2 then
      ∏ t, (choices t w) ^ (h t)
    else 0
  let score := fun (D : F c) (h : T → ℕ) => ∑ w, fiber D h w
  ∀ (D : F c) (h : T → ℕ), 2 ^ (width h) ∣ score D h * 2 ^ d →
    let B := d + 2 ^ c
    let cropped := fun t : T => min (h t) B
    let live := (Finset.univ.filter (fun w : W c => 0 < fiber D h w)).card
    (∀ w : W c, 0 < fiber D h w →
      c + ∑ t ∈ (Finset.univ.filter (fun u : T => choices u w = 1)), h t ≤ d + live - 1) ∧
    ∀ w : W c, fiber D cropped w * 2 ^ (width h) = fiber D h w * 2 ^ (width cropped) := by
  intro W Lit F c d T choices width fiber score D h hdiv B cropped live
  have hch_le : ∀ (t : T) (w : W c), choices t w ≤ 2 := fun t w => by
    calc choices t w ≤ (Finset.univ : Finset Bool).card := Finset.card_le_univ _
      _ = 2 := by decide
  have hlive_prop : ∀ w : W c, 0 < fiber D h w →
      (∀ e ∈ D, w e.1.1 ≠ e.1.2 ∨ w e.2.1 ≠ e.2.2) ∧
      (∀ t : T, choices t w = 0 → h t = 0) := by
    intro w hw
    have hD : ∀ e ∈ D, w e.1.1 ≠ e.1.2 ∨ w e.2.1 ≠ e.2.2 := by
      by_contra hnot
      simp only [fiber, if_neg hnot] at hw
      exact Nat.lt_irrefl 0 hw
    refine ⟨hD, fun t ht => ?_⟩
    simp only [fiber, if_pos hD] at hw
    by_contra hne0
    have h0 : (choices t w) ^ (h t) = 0 := by rw [ht]; exact zero_pow hne0
    have hprod0 : ∏ u : T, (choices u w) ^ (h u) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ t) h0
    omega
  let a : W c → ℕ := fun w =>
    c + ∑ t ∈ Finset.univ.filter (fun u : T => choices u w = 1), h t
  have hfiber_pow : ∀ w : W c, 0 < fiber D h w →
      a w ≤ width h ∧ fiber D h w = 2 ^ (width h - a w) := by
    intro w hw
    obtain ⟨hD, hg0⟩ := hlive_prop w hw
    have hsum := sum_partition_012 (fun t => choices t w) (fun t => hch_le t w) h hg0
    have hprod := prod_pow_012 (fun t => choices t w) (fun t => hch_le t w) h hg0
    have hw_eq : width h = a w + ∑ t ∈ Finset.univ.filter (fun u : T => choices u w = 2), h t := by
      dsimp only [width, a]; rw [hsum]; omega
    refine ⟨by omega, ?_⟩
    simp only [fiber, if_pos hD, hprod]
    congr 1; omega
  let L := Finset.univ.filter (fun w : W c => 0 < fiber D h w)
  have hclaim1 : ∀ w : W c, 0 < fiber D h w → a w ≤ d + live - 1 := by
    have hsum_L : score D h * 2 ^ d = ∑ w ∈ L, 2 ^ (width h - a w + d) := by
      have hsc : score D h = ∑ w ∈ L, fiber D h w := by
        dsimp only [score, L]
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun w : W c => 0 < fiber D h w)]
        have hzero : ∑ w ∈ Finset.univ.filter (fun w : W c => ¬ 0 < fiber D h w), fiber D h w = 0 := by
          refine Finset.sum_eq_zero fun w hw => ?_
          have hnot : ¬ 0 < fiber D h w := (Finset.mem_filter.mp hw).2
          omega
        rw [hzero, Nat.add_zero]
      rw [hsc, Finset.sum_mul]
      refine Finset.sum_congr rfl fun w hw => ?_
      have hwpos : 0 < fiber D h w := (Finset.mem_filter.mp hw).2
      rw [(hfiber_pow w hwpos).2, ← pow_add]
    have hdiv_L : 2 ^ (width h) ∣ ∑ w ∈ L, 2 ^ (width h - a w + d) := by
      rw [← hsum_L]; exact hdiv
    have hle_L : ∀ w ∈ L, a w ≤ width h := fun w hw =>
      (hfiber_pow w (Finset.mem_filter.mp hw).2).1
    have hbound := dyadic_max_depth live L (width h) d a rfl hle_L hdiv_L
    intro w hw
    exact hbound w (Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩)
  refine ⟨hclaim1, fun w => ?_⟩
  by_cases hw : 0 < fiber D h w
  · obtain ⟨hD, hg0⟩ := hlive_prop w hw
    have ha_le : a w ≤ B := by
      have h1 := hclaim1 w hw
      have hlive_le : live ≤ 2 ^ c := by
        calc live ≤ (Finset.univ : Finset (W c)).card := Finset.card_le_univ _
          _ = 2 ^ c := by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      dsimp only [B]; omega
    have hcr0 : ∀ t : T, choices t w = 0 → cropped t = 0 := fun t ht => by
      dsimp only [cropped]; rw [hg0 t ht]; simp
    have hcr1 : ∀ t ∈ Finset.univ.filter (fun u : T => choices u w = 1), cropped t = h t := by
      intro t ht
      have htle : h t ≤ a w := by
        have hle1 : h t ≤ ∑ u ∈ Finset.univ.filter (fun u : T => choices u w = 1), h u :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) ht
        dsimp only [a]; omega
      dsimp only [cropped]; exact Nat.min_eq_left (le_trans htle ha_le)
    have hsum_h := sum_partition_012 (fun t => choices t w) (fun t => hch_le t w) h hg0
    have hsum_cr := sum_partition_012 (fun t => choices t w) (fun t => hch_le t w) cropped hcr0
    have hprod_h := prod_pow_012 (fun t => choices t w) (fun t => hch_le t w) h hg0
    have hprod_cr := prod_pow_012 (fun t => choices t w) (fun t => hch_le t w) cropped hcr0
    have hS1_eq : ∑ t ∈ Finset.univ.filter (fun u : T => choices u w = 1), cropped t =
        ∑ t ∈ Finset.univ.filter (fun u : T => choices u w = 1), h t :=
      Finset.sum_congr rfl hcr1
    simp only [fiber, if_pos hD, hprod_h, hprod_cr, width, hsum_h, hsum_cr, hS1_eq]
    rw [← pow_add, ← pow_add]
    congr 1; ring
  · have hfh0 : fiber D h w = 0 := by omega
    have hfcr0 : fiber D cropped w = 0 := by
      by_cases hD : ∀ e ∈ D, w e.1.1 ≠ e.1.2 ∨ w e.2.1 ≠ e.2.2
      · simp only [fiber, if_pos hD] at hfh0 ⊢
        obtain ⟨t, _, ht0⟩ := Finset.prod_eq_zero_iff.mp hfh0
        have hcht0 : choices t w = 0 := by
          by_contra hne
          exact pow_ne_zero (h t) hne ht0
        have hht_ne0 : h t ≠ 0 := by
          intro h0; rw [h0, pow_zero] at ht0; omega
        have hB_pos : 1 ≤ B := by
          have : 1 ≤ 2 ^ c := Nat.one_le_pow c 2 (by omega)
          dsimp only [B]; omega
        have hcr_ne0 : cropped t ≠ 0 := by
          dsimp only [cropped]; omega
        refine Finset.prod_eq_zero (Finset.mem_univ t) ?_
        rw [hcht0]; exact zero_pow hcr_ne0
      · simp only [fiber, if_neg hD]
    rw [hfh0, hfcr0, zero_mul, zero_mul]
