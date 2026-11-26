import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18637_aux

private def codes : List ℕ :=
  [7405575, 23330829, 5799955, 22282261, 21757977, 21233693, 3735587, 19988517, 3211303,
   19415081, 7372867, 24117317, 7340103, 23085129, 23068749, 22052945, 5275731, 22020181,
   19939425, 19923045, 18890857, 6389891, 6619269, 6357127, 6570121, 6553741, 6324419,
   6308041, 21512457, 21528849, 4751635, 21496089, 17318185, 20988233, 21004625, 17891877]

private def D : Finset (Fin 13) := {0, 1, 3, 9}

private def inD (z : Fin 13) : Bool :=
  z == 0 || z == 1 || z == 3 || z == 9

private lemma inD_iff (z : Fin 13) : inD z = true ↔ z ∈ D := by
  revert z
  decide

private def isArc (xs : List (Fin 13)) : Bool :=
  (List.finRange 13).all fun x5 => decide ((xs.countP fun x6 => inD (x6 - x5)) ≤ 2)

private def lowMask (xs : List (Fin 13)) (t : Fin 13) : ℕ :=
  xs.foldl (fun acc x => acc + 2 ^ (x - t).val) 0

private def matchesCode (xs : List (Fin 13)) (c : ℕ) (t : Fin 13) : Bool :=
  (List.finRange 13).all fun x8 =>
    (c.testBit (x8 - t).val == decide (x8 ∈ xs)) &&
    (c.testBit (13 + (x8 - t).val) == xs.all fun x9 => !inD (x9 - x8))

private def hasMatch (xs : List (Fin 13)) : Bool :=
  (List.finRange 13).any fun t =>
    let lm := lowMask xs t
    codes.any fun c => (c % 8192 == lm) && matchesCode xs c t

private lemma check3 :
    ∀ a b : Fin 13, 0 < a → a < b → isArc [0, a, b] = true → hasMatch [0, a, b] = true := by
  decide +kernel

private lemma check4 :
    ∀ a b c : Fin 13, 0 < a → a < b → b < c → isArc [0, a, b, c] = true →
      hasMatch [0, a, b, c] = true := by
  decide +kernel

private lemma exists_of_hasMatch {xs : List (Fin 13)} (h : hasMatch xs = true) :
    ∃ c ∈ codes, ∃ t : Fin 13, matchesCode xs c t = true := by
  unfold hasMatch at h
  rw [List.any_eq_true] at h
  obtain ⟨t, _, ht⟩ := h
  rw [List.any_eq_true] at ht
  obtain ⟨c, hc_mem, hc⟩ := ht
  exact ⟨c, hc_mem, t, (Bool.and_eq_true _ _ |>.mp hc).2⟩

private lemma matchesCode_spec {xs : List (Fin 13)} {c : ℕ} {t : Fin 13}
    (hm : matchesCode xs c t = true) (x8 : Fin 13) :
    c.testBit (x8 - t).val = decide (x8 ∈ xs) ∧
    c.testBit (13 + (x8 - t).val) = xs.all (fun x9 => !inD (x9 - x8)) := by
  unfold matchesCode at hm
  rw [List.all_eq_true] at hm
  have h8 := hm x8 (List.mem_finRange x8)
  obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp h8
  exact ⟨beq_iff_eq.mp h1, beq_iff_eq.mp h2⟩

private lemma isArc_of_finset {S : Finset (Fin 13)} {xs : List (Fin 13)}
    (hnd : xs.Nodup) (hmem : ∀ y, y ∈ xs ↔ y ∈ S)
    (harc : ∀ x5 : Fin 13, {y ∈ S | y - x5 ∈ D}.card ≤ 2) :
    isArc xs = true := by
  unfold isArc
  rw [List.all_eq_true]
  intro x5 _
  rw [decide_eq_true_eq, List.countP_eq_length_filter]
  have hfilt_nd : (xs.filter fun x6 => inD (x6 - x5)).Nodup := hnd.filter _
  have hcard_eq : (xs.filter fun x6 => inD (x6 - x5)).length =
      (xs.filter fun x6 => inD (x6 - x5)).toFinset.card :=
    (List.toFinset_card_of_nodup hfilt_nd).symm
  rw [hcard_eq]
  have hset_eq : (xs.filter fun x6 => inD (x6 - x5)).toFinset = {y ∈ S | y - x5 ∈ D} := by
    ext y
    simp only [List.mem_toFinset, List.mem_filter, Finset.mem_filter, hmem, inD_iff]
  rw [hset_eq]
  exact harc x5

private lemma finRange_pairwise_lt : (List.finRange 13).Pairwise (· < ·) := by
  decide

private lemma main_proof :
    ∀ (x3 : Finset (Fin 13)), x3.card = 3 ∨ x3.card = 4 →
      (∀ (x5 : Fin 13), {x6 ∈ x3 | x6 - x5 ∈ D}.card ≤ 2) →
      ∃ x6 ∈ codes, ∃ (x7 : Fin 13),
        (∀ (x8 : Fin 13), x6.testBit ↑(x8 - x7) = Decidable.decide (x8 ∈ x3)) ∧
        ∀ (x8 : Fin 13), x6.testBit (13 + ↑(x8 - x7)) = Decidable.decide (∀ x9 ∈ x3, x9 - x8 ∉ D) := by
  intro x3 hcard harc
  have hne : x3.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨s, hs⟩ := hne
  have hinj : Function.Injective (fun z : Fin 13 => z - s) := fun a b h => by
    have h' := congrArg (· + s) h
    simpa [sub_add_cancel] using h'
  let S : Finset (Fin 13) := x3.image (· - s)
  have hS_mem : ∀ y : Fin 13, y ∈ S ↔ y + s ∈ x3 := by
    intro y
    simp only [S, Finset.mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [sub_add_cancel] using hz
    · intro h
      exact ⟨y + s, h, add_sub_cancel_right y s⟩
  have h0S : (0 : Fin 13) ∈ S := (hS_mem 0).mpr (by simpa using hs)
  have hS_card : S.card = x3.card := Finset.card_image_of_injective x3 hinj
  have hS_arc : ∀ x5 : Fin 13, {y ∈ S | y - x5 ∈ D}.card ≤ 2 := by
    intro x5
    have hset : {y ∈ S | y - x5 ∈ D} = ({z ∈ x3 | z - (x5 + s) ∈ D}).image (· - s) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_image, hS_mem]
      constructor
      · rintro ⟨hy1, hy2⟩
        refine ⟨y + s, ⟨hy1, ?_⟩, add_sub_cancel_right y s⟩
        have heq : (y + s) - (x5 + s) = y - x5 := by abel
        rw [heq]
        exact hy2
      · rintro ⟨z, ⟨hz1, hz2⟩, rfl⟩
        refine ⟨by simpa [sub_add_cancel] using hz1, ?_⟩
        have heq : (z - s) - x5 = z - (x5 + s) := by abel
        rw [heq]
        exact hz2
    rw [hset, Finset.card_image_of_injective _ hinj]
    exact harc (x5 + s)
  let xs : List (Fin 13) := (List.finRange 13).filter (fun y => decide (y ∈ S))
  have hxs_nd : xs.Nodup := (List.nodup_finRange 13).filter _
  have hxs_pw : xs.Pairwise (· < ·) := finRange_pairwise_lt.filter _
  have hxs_mem : ∀ y, y ∈ xs ↔ y ∈ S := by
    intro y
    simp only [xs, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  have hxs_len : xs.length = S.card := by
    have hto : xs.toFinset = S := by
      ext y
      simp only [List.mem_toFinset, hxs_mem]
    rw [← hto, List.toFinset_card_of_nodup hxs_nd]
  have hxs_arc : isArc xs = true := isArc_of_finset hxs_nd hxs_mem hS_arc
  have hmatch : hasMatch xs = true := by
    rcases hcard with hc3 | hc4
    · have hlen3 : xs.length = 3 := by omega
      have hex3 : ∃ u a b, xs = [u, a, b] := by
        rcases xs with _ | ⟨u, _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩⟩ <;> simp_all
      rcases hex3 with ⟨u, a, b, hxs_eq⟩
      rw [hxs_eq] at hxs_pw hxs_arc
      have h0_in : (0 : Fin 13) ∈ [u, a, b] := by rw [← hxs_eq]; exact (hxs_mem 0).mpr h0S
      simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hxs_pw
      have hua : u < a := hxs_pw.1.1
      have hab : a < b := hxs_pw.2.1
      have hu0 : u = 0 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h0_in
        rcases h0_in with h | h | h
        · exact h.symm
        · exfalso; exact not_lt_of_ge (Fin.zero_le u) (h ▸ hua)
        · exfalso; exact not_lt_of_ge (Fin.zero_le u) (h ▸ lt_trans hua hab)
      subst hu0
      rw [hxs_eq]
      exact check3 a b hua hab hxs_arc
    · have hlen4 : xs.length = 4 := by omega
      have hex4 : ∃ u a b d, xs = [u, a, b, d] := by
        rcases xs with _ | ⟨u, _ | ⟨a, _ | ⟨b, _ | ⟨d, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp_all
      rcases hex4 with ⟨u, a, b, d, hxs_eq⟩
      rw [hxs_eq] at hxs_pw hxs_arc
      have h0_in : (0 : Fin 13) ∈ [u, a, b, d] := by rw [← hxs_eq]; exact (hxs_mem 0).mpr h0S
      simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hxs_pw
      have hua : u < a := hxs_pw.1.1
      have hab : a < b := hxs_pw.2.1.1
      have hbd : b < d := hxs_pw.2.2.1
      have hu0 : u = 0 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h0_in
        rcases h0_in with h | h | h | h
        · exact h.symm
        · exfalso; exact not_lt_of_ge (Fin.zero_le u) (h ▸ hua)
        · exfalso; exact not_lt_of_ge (Fin.zero_le u) (h ▸ lt_trans hua hab)
        · exfalso; exact not_lt_of_ge (Fin.zero_le u) (h ▸ lt_trans (lt_trans hua hab) hbd)
      subst hu0
      rw [hxs_eq]
      exact check4 a b d hua hab hbd hxs_arc
  obtain ⟨c, hc_mem, t, hm⟩ := exists_of_hasMatch hmatch
  refine ⟨c, hc_mem, t + s, ?_, ?_⟩
  · intro x8
    have hsp := (matchesCode_spec hm (x8 - s)).1
    have hsub : (x8 - s) - t = x8 - (t + s) := by abel
    rw [hsub] at hsp
    rw [hsp]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, hxs_mem, hS_mem, sub_add_cancel]
  · intro x8
    have hsp := (matchesCode_spec hm (x8 - s)).2
    have hsub : (x8 - s) - t = x8 - (t + s) := by abel
    rw [hsub] at hsp
    rw [hsp]
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, Bool.not_eq_true', decide_eq_true_eq]
    constructor
    · intro hall x9 hx9
      have h9S : x9 - s ∈ xs := (hxs_mem _).mpr ((hS_mem _).mpr (by simpa [sub_add_cancel] using hx9))
      have hnot := hall (x9 - s) h9S
      have hdiff : (x9 - s) - (x8 - s) = x9 - x8 := by abel
      rw [hdiff] at hnot
      intro hmemD
      have ht := (inD_iff (x9 - x8)).mpr hmemD
      rw [ht] at hnot
      exact Bool.noConfusion hnot
    · intro hall x9 hx9
      have hx9' : x9 + s ∈ x3 := (hS_mem x9).mp ((hxs_mem x9).mp hx9)
      have hnotD := hall (x9 + s) hx9'
      have hdiff : x9 - (x8 - s) = (x9 + s) - x8 := by abel
      rw [hdiff]
      exact Bool.eq_false_iff.mpr (fun ht => hnotD ((inD_iff _).mp ht))

end PEqualNP.Outside.L_meta_18637_aux

theorem PEqualNP.Outside.L_meta_18637 : (have x1 : List ℕ :=   have x1 : List ℕ :=     have x1 : List ℕ :=       have x1 : List ℕ := [(21496089 : ℕ), (17318185 : ℕ), (20988233 : ℕ), (21004625 : ℕ), (17891877 : ℕ)];       (6308041 : ℕ) :: (21512457 : ℕ) :: (21528849 : ℕ) :: (4751635 : ℕ) :: x1;     have x2 : List ℕ := (6619269 : ℕ) :: (6357127 : ℕ) :: (6570121 : ℕ) :: (6553741 : ℕ) :: (6324419 : ℕ) :: x1;     (19939425 : ℕ) :: (19923045 : ℕ) :: (18890857 : ℕ) :: (6389891 : ℕ) :: x2;   have x2 : List ℕ :=     have x2 : List ℕ := (23085129 : ℕ) :: (23068749 : ℕ) :: (22052945 : ℕ) :: (5275731 : ℕ) :: (22020181 : ℕ) :: x1;     (19415081 : ℕ) :: (7372867 : ℕ) :: (24117317 : ℕ) :: (7340103 : ℕ) :: x2;   have x3 : List ℕ := (21757977 : ℕ) :: (21233693 : ℕ) :: (3735587 : ℕ) :: (19988517 : ℕ) :: (3211303 : ℕ) :: x2;   (7405575 : ℕ) :: (23330829 : ℕ) :: (5799955 : ℕ) :: (22282261 : ℕ) :: x3; have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (3 : ℕ) ∨ x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x2}.card ≤ (2 : ℕ)) → ∃ x6 ∈ x1, ∃ (x7 : Fin (13 : ℕ)), (∀ (x8 : Fin (13 : ℕ)), x6.testBit ↑(x8 - x7) = Decidable.decide (x8 ∈ x3)) ∧ ∀ (x8 : Fin (13 : ℕ)), x6.testBit ((13 : ℕ) + ↑(x8 - x7)) = Decidable.decide (∀ x9 ∈ x3, x9 - x8 ∉ x2)) :=
  PEqualNP.Outside.L_meta_18637_aux.main_proof
