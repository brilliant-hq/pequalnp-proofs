import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25701

open Finset

theorem count_pat (k : ℕ) (w : ℕ → Bool) (C : Finset ℕ) (hC : ∀ s ∈ C, s < k) :
    (univ.filter (fun i : Fin (2 ^ k) => ∀ s ∈ C, i.val.testBit s = w s)).card * 2 ^ C.card
      ≤ 2 ^ k := by
  induction C using Finset.induction_on with
  | empty => simp
  | insert s C hs ih =>
    have hsk : s < k := hC s (mem_insert_self s C)
    have ih' := ih (fun t ht => hC t (mem_insert_of_mem ht))
    set A := univ.filter (fun i : Fin (2 ^ k) => ∀ t ∈ C, i.val.testBit t = w t) with hA
    have hA' : univ.filter (fun i : Fin (2 ^ k) => ∀ t ∈ insert s C, i.val.testBit t = w t)
        = A.filter (fun i => i.val.testBit s = w s) := by
      ext i
      simp only [hA, mem_filter, mem_univ, true_and, forall_mem_insert]
      tauto
    have hsplit := card_filter_add_card_filter_not (s := A)
      (fun i : Fin (2 ^ k) => i.val.testBit s = w s)
    have hlt : 2 ^ s < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) hsk
    have hle : (A.filter (fun i => i.val.testBit s = w s)).card
        ≤ (A.filter (fun i => ¬ i.val.testBit s = w s)).card := by
      refine card_le_card_of_injOn
        (fun i : Fin (2 ^ k) => (⟨i.val ^^^ 2 ^ s, Nat.xor_lt_two_pow i.isLt hlt⟩ : Fin (2 ^ k)))
        ?_ ?_
      · intro i hi
        simp only [coe_filter, Set.mem_setOf_eq, hA, mem_filter, mem_univ, true_and] at hi ⊢
        refine ⟨fun t ht => ?_, ?_⟩
        · have hts : s ≠ t := fun h => hs (h ▸ ht)
          simp [Nat.testBit_xor, hi.1 t ht, hts]
        · simp [Nat.testBit_xor, hi.2]
      · intro i _ j _ hij
        simp only [Fin.mk.injEq] at hij
        apply Fin.ext
        have h2 := congrArg (· ^^^ 2 ^ s) hij
        simpa [Nat.xor_assoc] using h2
    rw [hA', card_insert_of_notMem hs, pow_succ]
    calc (A.filter (fun i => i.val.testBit s = w s)).card * (2 ^ C.card * 2)
        = ((A.filter (fun i => i.val.testBit s = w s)).card * 2) * 2 ^ C.card := by ring
      _ ≤ A.card * 2 ^ C.card := by gcongr; omega
      _ ≤ 2 ^ k := ih'

theorem two_mul_le_two_pow (d : ℕ) : 2 * d ≤ 2 ^ d := by
  induction d with
  | zero => simp
  | succ n ih =>
    rcases Nat.lt_or_ge n 1 with h | h
    · interval_cases n; norm_num
    · rw [pow_succ]; omega

theorem bool_same : ∀ x y li lj : Bool, xor (xor x y) (xor x y) = xor li lj → li = lj := by
  decide

theorem bool_pat : ∀ x1 y x2 z w1 w2 li lj lr : Bool,
    xor (xor x1 y) (xor x2 z) = xor li lj → xor (xor w1 y) (xor w2 z) = xor lr lj → li = lr →
    xor x2 w2 = xor x1 w1 := by
  decide

theorem bool_split : ∀ x y b : Bool, xor x y = b → x = xor y b := by
  decide

theorem upper (k a : ℕ) (ha : 2 ≤ a) (hak : 2 ^ a ≤ k) (π : Equiv.Perm (Fin (2 ^ k)))
    (K L : Finset (Fin (2 ^ k)))
    (H : ∀ i ∈ K, ∀ j ∈ K,
      xor (xor ((i.val).testBit ((π i).val % 2 ^ a)) ((j.val).testBit ((π j).val % 2 ^ a)))
        (xor ((i.val).testBit ((π j).val % 2 ^ a)) ((j.val).testBit ((π i).val % 2 ^ a))) =
        xor (decide (i ∈ L)) (decide (j ∈ L))) :
    K.card ≤ (a + 1) * 2 ^ (k - a) := by
  classical
  set c : Fin (2 ^ k) → ℕ := fun i => (π i).val % 2 ^ a with hc
  set C := K.image c with hCdef
  have hpa : 0 < 2 ^ a := by positivity
  have hcl : ∀ i, c i < 2 ^ a := fun i => Nat.mod_lt _ hpa
  have hCk : ∀ s ∈ C, s < k := by
    intro s hs
    obtain ⟨j, -, rfl⟩ := mem_image.1 hs
    exact lt_of_lt_of_le (hcl j) hak
  have hak' : a ≤ k := le_trans (Nat.lt_two_pow_self).le hak
  have hhk : C.card ≤ k := by
    calc C.card ≤ (range k).card := card_le_card (fun s hs => mem_range.2 (hCk s hs))
      _ = k := card_range k
  have hsame : ∀ i ∈ K, ∀ j ∈ K, c i = c j → (decide (i ∈ L) = decide (j ∈ L)) := by
    intro i hi j hj hij
    have h := H i hi j hj
    have e : (π j).val % 2 ^ a = (π i).val % 2 ^ a := hij.symm
    rw [e] at h
    exact bool_same _ _ _ _ h
  have hpat : ∀ i ∈ K, ∀ r ∈ K, c i = c r → ∀ s ∈ C,
      xor ((i.val).testBit s) ((r.val).testBit s)
        = xor ((i.val).testBit (c i)) ((r.val).testBit (c i)) := by
    intro i hi r hr hir s hs
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hs
    have h1 := H i hi j hj
    have h2 := H r hr j hj
    have e : (π r).val % 2 ^ a = (π i).val % 2 ^ a := hir.symm
    rw [e] at h2
    exact bool_pat _ _ _ _ _ _ _ _ _ h1 h2 (hsame i hi r hr hir)
  have B1 : K.card ≤ 2 ^ (k - a) * C.card := by
    apply card_le_mul_card_image K (2 ^ (k - a))
    intro t _
    calc (K.filter (fun i => c i = t)).card ≤ (range (2 ^ (k - a))).card := by
          refine card_le_card_of_injOn (fun i => (π i).val / 2 ^ a) ?_ ?_
          · intro i _
            simp only [coe_range, Set.mem_Iio]
            apply Nat.div_lt_of_lt_mul
            rw [← pow_add, Nat.add_sub_cancel' hak']
            exact (π i).isLt
          · intro i hi j hj hij
            simp only [coe_filter, Set.mem_setOf_eq] at hi hj
            have hv : (π i).val = (π j).val := by
              have h1 := Nat.div_add_mod (π i).val (2 ^ a)
              have h2 := Nat.div_add_mod (π j).val (2 ^ a)
              have hm : (π i).val % 2 ^ a = (π j).val % 2 ^ a := hi.2.trans hj.2.symm
              simp only at hij
              rw [← h1, ← h2, hij, hm]
            exact π.injective (Fin.ext hv)
      _ = 2 ^ (k - a) := card_range _
  have B2 : K.card ≤ (2 * 2 ^ (k - C.card)) * C.card := by
    apply card_le_mul_card_image K (2 * 2 ^ (k - C.card))
    intro t ht
    obtain ⟨r, hr, hrt⟩ := mem_image.1 ht
    have hfib : ∀ w : ℕ → Bool,
        (univ.filter (fun i : Fin (2 ^ k) => ∀ s ∈ C, i.val.testBit s = w s)).card
          ≤ 2 ^ (k - C.card) := by
      intro w
      have h := count_pat k w C hCk
      have e : 2 ^ k = 2 ^ (k - C.card) * 2 ^ C.card := by
        rw [← pow_add, Nat.sub_add_cancel hhk]
      exact Nat.le_of_mul_le_mul_right (h.trans e.le) (by positivity)
    have hsub : K.filter (fun i => c i = t) ⊆
        univ.filter (fun i : Fin (2 ^ k) => ∀ s ∈ C, i.val.testBit s = (r.val).testBit s) ∪
        univ.filter (fun i : Fin (2 ^ k) => ∀ s ∈ C, i.val.testBit s = !(r.val).testBit s) := by
      intro i hi
      simp only [mem_filter] at hi
      have hir : c i = c r := hi.2.trans hrt.symm
      have hp := hpat i hi.1 r hr hir
      simp only [mem_union, mem_filter, mem_univ, true_and]
      cases hb : xor ((i.val).testBit (c i)) ((r.val).testBit (c i))
      · left
        intro s hs
        have := bool_split _ _ _ ((hp s hs).trans hb)
        simpa using this
      · right
        intro s hs
        have := bool_split _ _ _ ((hp s hs).trans hb)
        simpa using this
    calc (K.filter (fun i => c i = t)).card
        ≤ (univ.filter (fun i : Fin (2 ^ k) => ∀ s ∈ C, i.val.testBit s = (r.val).testBit s) ∪
          univ.filter (fun i : Fin (2 ^ k) => ∀ s ∈ C, i.val.testBit s = !(r.val).testBit s)).card :=
          card_le_card hsub
      _ ≤ _ := card_union_le _ _
      _ ≤ 2 ^ (k - C.card) + 2 ^ (k - C.card) := add_le_add (hfib _) (hfib _)
      _ = 2 * 2 ^ (k - C.card) := by ring
  rcases Nat.lt_or_ge C.card (a + 2) with hh | hh
  · calc K.card ≤ 2 ^ (k - a) * C.card := B1
      _ ≤ 2 ^ (k - a) * (a + 1) := by gcongr; omega
      _ = (a + 1) * 2 ^ (k - a) := by ring
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show a ≤ C.card by omega)
    have hd2 : 2 ≤ d := by omega
    have e : 2 ^ (k - a) = 2 ^ (k - C.card) * 2 ^ d := by
      rw [← pow_add]; congr 1; omega
    have hdd := two_mul_le_two_pow d
    have hX : 2 * C.card ≤ (a + 1) * 2 ^ d := by
      rw [hd]
      have h1 : a * (2 * d) ≤ a * 2 ^ d := Nat.mul_le_mul_left a hdd
      have h2 : a * 1 ≤ a * d := Nat.mul_le_mul_left a (by omega)
      nlinarith
    calc K.card ≤ (2 * 2 ^ (k - C.card)) * C.card := B2
      _ = 2 ^ (k - C.card) * (2 * C.card) := by ring
      _ ≤ 2 ^ (k - C.card) * ((a + 1) * 2 ^ d) := by gcongr
      _ = (a + 1) * 2 ^ (k - a) := by rw [e]; ring

theorem vbit (a t : ℕ) (b : Bool) (s : ℕ) (hs : s < a + 1) :
    (if b then 2 ^ t ^^^ (2 ^ (a + 1) - 1) else 2 ^ t).testBit s = xor (decide (t = s)) b := by
  cases b
  · simp [Nat.testBit_two_pow]
  · simp [Nat.testBit_xor, Nat.testBit_two_pow, hs]

theorem vlt (a t : ℕ) (b : Bool) (ht : t < a + 1) :
    (if b then 2 ^ t ^^^ (2 ^ (a + 1) - 1) else 2 ^ t) < 2 ^ (a + 1) := by
  have h1 : 2 ^ t < 2 ^ (a + 1) := Nat.pow_lt_pow_right (by norm_num) ht
  cases b
  · simpa using h1
  · simp only [if_true]
    exact Nat.xor_lt_two_pow h1 (Nat.sub_lt (by positivity) (by norm_num))

theorem bool_cond : ∀ b b' e : Bool,
    xor (xor (xor true b) (xor true b')) (xor (xor e b) (xor e b')) = false := by
  decide

theorem lower (k a u m : ℕ) (ha : 2 ≤ a) (hak : 2 ^ a ≤ k) (hm : m ≤ (a + 1) * 2 ^ (k - a)) :
    ∃ (π : Equiv.Perm (Fin (2 ^ k))) (K L : Finset (Fin (2 ^ k))),
      m ≤ K.card ∧ L ⊆ K ∧ L.card ≤ u ∧
      ∀ i ∈ K, ∀ j ∈ K,
        xor (xor ((i.val).testBit ((π i).val % 2 ^ a)) ((j.val).testBit ((π j).val % 2 ^ a)))
          (xor ((i.val).testBit ((π j).val % 2 ^ a)) ((j.val).testBit ((π i).val % 2 ^ a))) =
          xor (decide (i ∈ L)) (decide (j ∈ L)) := by
  classical
  have hA1 : a + 1 ≤ 2 ^ a := by have := two_mul_le_two_pow a; omega
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le (show a + 1 ≤ k by omega)
  have hka : k - a = n + 1 := by omega
  have hpa : 0 < 2 ^ a := by positivity
  let v : ℕ → Bool → ℕ := fun t b => if b then 2 ^ t ^^^ (2 ^ (a + 1) - 1) else 2 ^ t
  have hv : ∀ x : Fin (a + 1) × Bool × Fin (2 ^ n), v x.1.val x.2.1 < 2 ^ (a + 1) :=
    fun x => vlt a x.1.val x.2.1 x.1.isLt
  have hψlt : ∀ x : Fin (a + 1) × Bool × Fin (2 ^ n),
      2 ^ (a + 1) * x.2.2.val + v x.1.val x.2.1 < 2 ^ k := by
    intro x
    have h1 : x.2.2.val + 1 ≤ 2 ^ n := x.2.2.isLt
    calc 2 ^ (a + 1) * x.2.2.val + v x.1.val x.2.1 < 2 ^ (a + 1) * x.2.2.val + 2 ^ (a + 1) := by
          have := hv x; omega
      _ = 2 ^ (a + 1) * (x.2.2.val + 1) := by ring
      _ ≤ 2 ^ (a + 1) * 2 ^ n := Nat.mul_le_mul_left _ h1
      _ = 2 ^ k := by rw [← pow_add, hn]
  let ψ : Fin (a + 1) × Bool × Fin (2 ^ n) → Fin (2 ^ k) := fun x =>
    ⟨2 ^ (a + 1) * x.2.2.val + v x.1.val x.2.1, hψlt x⟩
  have hφlt : ∀ x : Fin (a + 1) × Bool × Fin (2 ^ n),
      (2 * x.2.2.val + (if x.2.1 then 1 else 0)) * 2 ^ a + x.1.val < 2 ^ k := by
    intro x
    have h1 : x.2.2.val + 1 ≤ 2 ^ n := x.2.2.isLt
    have h2 : (if x.2.1 then 1 else 0) ≤ 1 := by split <;> omega
    have h3 : x.1.val < 2 ^ a := lt_of_lt_of_le x.1.isLt hA1
    calc (2 * x.2.2.val + (if x.2.1 then 1 else 0)) * 2 ^ a + x.1.val
        < (2 * x.2.2.val + (if x.2.1 then 1 else 0)) * 2 ^ a + 2 ^ a := by omega
      _ = (2 * x.2.2.val + (if x.2.1 then 1 else 0) + 1) * 2 ^ a := by ring
      _ ≤ (2 * 2 ^ n) * 2 ^ a := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ k := by rw [hn, pow_add, pow_succ]; ring
  let φ : Fin (a + 1) × Bool × Fin (2 ^ n) → Fin (2 ^ k) := fun x =>
    ⟨(2 * x.2.2.val + (if x.2.1 then 1 else 0)) * 2 ^ a + x.1.val, hφlt x⟩
  have hφmod : ∀ x, (φ x).val % 2 ^ a = x.1.val := by
    intro x
    show ((2 * x.2.2.val + (if x.2.1 then 1 else 0)) * 2 ^ a + x.1.val) % 2 ^ a = x.1.val
    rw [Nat.mul_add_mod', Nat.mod_eq_of_lt (lt_of_lt_of_le x.1.isLt hA1)]
  have hφinj : Function.Injective φ := by
    rintro ⟨t, b, q⟩ ⟨t', b', q'⟩ h
    have hm1 := hφmod (t, b, q)
    have hm2 := hφmod (t', b', q')
    rw [h] at hm1
    have htt : t = t' := Fin.ext (hm1.symm.trans hm2)
    subst htt
    have h' : (2 * q.val + (if b then 1 else 0)) * 2 ^ a + t.val
        = (2 * q'.val + (if b' then 1 else 0)) * 2 ^ a + t.val := congrArg Fin.val h
    have h'' : 2 * q.val + (if b then 1 else 0) = 2 * q'.val + (if b' then 1 else 0) :=
      Nat.eq_of_mul_eq_mul_right hpa (by omega)
    have hqq : q = q' := by
      apply Fin.ext
      cases b <;> cases b' <;> simp at h'' <;> omega
    subst hqq
    have hbb : b = b' := by
      cases b <;> cases b' <;> simp at h'' <;> rfl
    rw [hbb]
  have hψbit : ∀ x : Fin (a + 1) × Bool × Fin (2 ^ n), ∀ s, s < a + 1 →
      (ψ x).val.testBit s = xor (decide (x.1.val = s)) x.2.1 := by
    intro x s hs
    show (2 ^ (a + 1) * x.2.2.val + v x.1.val x.2.1).testBit s = _
    rw [Nat.testBit_two_pow_mul_add _ (hv x), if_pos hs]
    exact vbit a x.1.val x.2.1 s hs
  have hψinj : Function.Injective ψ := by
    rintro ⟨t, b, q⟩ ⟨t', b', q'⟩ h
    have hb : ∀ s, s < a + 1 → xor (decide (t.val = s)) b = xor (decide (t'.val = s)) b' := by
      intro s hs
      have e1 := hψbit (t, b, q) s hs
      have e2 := hψbit (t', b', q') s hs
      rw [h] at e1
      exact e1.symm.trans e2
    have htb : t = t' ∧ b = b' := by
      by_cases htt : t = t'
      · subst htt
        refine ⟨rfl, ?_⟩
        have := hb t.val t.isLt
        cases b <;> cases b' <;> simp_all
      · exfalso
        have htt' : t.val ≠ t'.val := fun e => htt (Fin.ext e)
        have e1 := hb t.val t.isLt
        obtain ⟨s0, hs0, h0, h0'⟩ : ∃ s0, s0 < a + 1 ∧ t.val ≠ s0 ∧ t'.val ≠ s0 := by
          rcases (show (t.val ≠ 0 ∧ t'.val ≠ 0) ∨ (t.val ≠ 1 ∧ t'.val ≠ 1) ∨
              (t.val ≠ 2 ∧ t'.val ≠ 2) by omega) with h | h | h
          · exact ⟨0, by omega, h.1, h.2⟩
          · exact ⟨1, by omega, h.1, h.2⟩
          · exact ⟨2, by omega, h.1, h.2⟩
        have e2 := hb s0 hs0
        simp only [h0, h0', decide_true, decide_false] at e1 e2
        cases b <;> cases b' <;> simp_all
    obtain ⟨rfl, rfl⟩ := htb
    have hval : 2 ^ (a + 1) * q.val + v t.val b = 2 ^ (a + 1) * q'.val + v t.val b :=
      congrArg Fin.val h
    have : q.val = q'.val := by
      have := Nat.eq_of_mul_eq_mul_left (show 0 < 2 ^ (a + 1) by positivity) (by omega : 2 ^ (a + 1) * q.val = 2 ^ (a + 1) * q'.val)
      exact this
    rw [Fin.ext this]
  let e : {x // x ∈ Set.range ψ} ≃ {x // x ∈ Set.range φ} :=
    (Equiv.ofInjective ψ hψinj).symm.trans (Equiv.ofInjective φ hφinj)
  let π : Equiv.Perm (Fin (2 ^ k)) := e.extendSubtype
  have hπ : ∀ x, π (ψ x) = φ x := by
    intro x
    show e.extendSubtype (ψ x) = φ x
    rw [Equiv.extendSubtype_apply_of_mem e (ψ x) ⟨x, rfl⟩]
    show φ ((Equiv.ofInjective ψ hψinj).symm ⟨ψ x, ⟨x, rfl⟩⟩) = φ x
    rw [Equiv.ofInjective_symm_apply]
  refine ⟨π, univ.image ψ, ∅, ?_, empty_subset _, by simp, ?_⟩
  · rw [card_image_of_injective _ hψinj, card_univ]
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    calc m ≤ (a + 1) * 2 ^ (k - a) := hm
      _ = (a + 1) * (2 * 2 ^ n) := by rw [hka, pow_succ]; ring
  · intro i hi j hj
    obtain ⟨x, -, rfl⟩ := mem_image.1 hi
    obtain ⟨y, -, rfl⟩ := mem_image.1 hj
    rw [hπ x, hπ y, hφmod x, hφmod y,
      hψbit x _ x.1.isLt, hψbit y _ y.1.isLt, hψbit x _ y.1.isLt, hψbit y _ x.1.isLt]
    have hsym : decide (y.1.val = x.1.val) = decide (x.1.val = y.1.val) := by
      simp [eq_comm]
    rw [hsym]
    simp only [decide_true, notMem_empty, decide_false]
    exact bool_cond _ _ _

end PEqualNP.Outside.L_meta_25701

theorem PEqualNP.Outside.L_meta_25701 : (∀ (k a u m : ℕ), 2 ≤ a → 2^a ≤ k →
  let N := 2^k
  let F := fun (x y : Fin N) => x.val.testBit (y.val % 2^a)
  ((∃ (π : Equiv.Perm (Fin N)) (K L : Finset (Fin N)),
    m ≤ K.card ∧ L ⊆ K ∧ L.card ≤ u ∧
    ∀ i ∈ K, ∀ j ∈ K,
      xor (xor (F i (π i)) (F j (π j))) (xor (F i (π j)) (F j (π i))) =
        xor (decide (i ∈ L)) (decide (j ∈ L))) ↔
    m ≤ (a+1)*2^(k-a))) := by
  intro k a u m ha hak
  dsimp only
  constructor
  · rintro ⟨π, K, L, hmK, -, -, H⟩
    exact hmK.trans (PEqualNP.Outside.L_meta_25701.upper k a ha hak π K L H)
  · intro hm
    exact PEqualNP.Outside.L_meta_25701.lower k a u m ha hak hm
