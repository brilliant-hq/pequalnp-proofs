import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38164

open Finset

def chiF (b : ℕ → Bool) (j : ℕ) : Bool := xor (b j) (!(b (j+1)) && b (j+2))

def mixN (d x i : ℕ) : Bool := xor (x.testBit i) (xor (x.testBit (i+d)) (x.testBit (i+2*d)))

def firstF (h u : ℕ) : Finset ℕ := (range h).filter (fun j => chiF (fun i => u.testBit i) j)

def T (h d : ℕ) (pick : Finset ℕ → ℕ) (mask : Finset ℕ → Finset ℕ) (u : ℕ) :
    Finset ℕ × Finset ℕ :=
  (firstF h u, (mask (firstF h u)).filter
    (fun j => chiF (fun i => xor (u.testBit i) (mixN d (pick (firstF h u)) i)) j))

def enc (k : ℕ) (p : ℕ × ℕ) : ℕ := 2^(k+2) * p.1 + p.2

def chiB (a b c : Bool) : Bool := xor a (!b && c)

theorem chi_at (b : ℕ → Bool) (j : ℕ) : chiF b j = chiB (b j) (b (j+1)) (b (j+2)) := rfl
theorem chi_k0 (b : ℕ → Bool) (k : ℕ) : chiF b k = chiB (b k) (b (k+1)) (b (k+2)) := rfl
theorem chi_k1 (b : ℕ → Bool) (k : ℕ) : chiF b (k+1) = chiB (b (k+1)) (b (k+2)) (b (k+3)) := rfl
theorem chi_k2 (b : ℕ → Bool) (k : ℕ) : chiF b (k+2) = chiB (b (k+2)) (b (k+3)) (b (k+4)) := rfl
theorem chi_k3 (b : ℕ → Bool) (k : ℕ) : chiF b (k+3) = chiB (b (k+3)) (b (k+4)) (b (k+5)) := rfl

theorem chiB_true (x y : Bool) : chiB x true y = x := by cases x <;> cases y <;> rfl

/-! Bits of the split encoding `2^(k+2) * q + L`. -/

theorem encB (k q L i : ℕ) (hL : L < 2^(k+2)) :
    (enc k (q, L)).testBit i = if i < k+2 then L.testBit i else q.testBit (i-(k+2)) := by
  unfold enc; exact Nat.testBit_two_pow_mul_add q hL i

theorem encLo (k q L i : ℕ) (hL : L < 2^(k+2)) (hi : i < k+2) :
    (enc k (q, L)).testBit i = L.testBit i := by
  rw [encB k q L i hL, if_pos hi]

theorem encHi (k q L r : ℕ) (hL : L < 2^(k+2)) :
    (enc k (q, L)).testBit (k+2+r) = q.testBit r := by
  rw [encB k q L _ hL, if_neg (by omega)]; congr 1; omega

theorem e0 (k q L : ℕ) (hL : L < 2^(k+2)) : (enc k (q, L)).testBit k = L.testBit k :=
  encLo k q L k hL (by omega)
theorem e1 (k q L : ℕ) (hL : L < 2^(k+2)) : (enc k (q, L)).testBit (k+1) = L.testBit (k+1) :=
  encLo k q L (k+1) hL (by omega)
theorem e2 (k q L : ℕ) (hL : L < 2^(k+2)) : (enc k (q, L)).testBit (k+2) = q.testBit 0 :=
  encHi k q L 0 hL
theorem e3 (k q L : ℕ) (hL : L < 2^(k+2)) : (enc k (q, L)).testBit (k+3) = q.testBit 1 :=
  encHi k q L 1 hL
theorem e4 (k q L : ℕ) (hL : L < 2^(k+2)) : (enc k (q, L)).testBit (k+4) = q.testBit 2 :=
  encHi k q L 2 hL
theorem e5 (k q L : ℕ) (hL : L < 2^(k+2)) : (enc k (q, L)).testBit (k+5) = q.testBit 3 :=
  encHi k q L 3 hL

theorem strips_eq (k : ℕ) :
    range (2^(k+4+2)) = (range 16 ×ˢ range (2^(k+2))).image (enc k) := by
  have hM : 2^(k+4+2) = 2^(k+2) * 16 := by
    rw [show k+4+2 = (k+2)+4 by omega, pow_add]; norm_num
  have hpos : 0 < 2^(k+2) := by positivity
  ext u
  simp only [mem_range, mem_image, mem_product, Prod.exists, enc]
  constructor
  · intro hu
    refine ⟨u / 2^(k+2), u % 2^(k+2), ⟨?_, Nat.mod_lt _ hpos⟩, Nat.div_add_mod u _⟩
    rw [Nat.div_lt_iff_lt_mul hpos]; rw [hM] at hu; linarith
  · rintro ⟨q, L, ⟨hq, hL⟩, rfl⟩
    have h1 : 2^(k+2) * (q+1) ≤ 2^(k+2) * 16 := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_succ] at h1
    rw [hM]; omega

theorem low_eq (k L L' : ℕ) (hL : L < 2^(k+2)) (hL' : L' < 2^(k+2))
    (h : ∀ i < k+2, L.testBit i = L'.testBit i) : L = L' := by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases hi : i < k+2
  · exact h i hi
  · have hp : 2^(k+2) ≤ 2^i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hL hp),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hL' hp)]

theorem nib_eq (q q' : ℕ) (hq : q < 16) (hq' : q' < 16)
    (h : ∀ r < 4, q.testBit r = q'.testBit r) : q = q' := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 4
  · exact h r hr
  · have hp : 16 ≤ 2^r := by
      calc (16 : ℕ) = 2^4 := by norm_num
        _ ≤ 2^r := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

theorem bits15 : ∀ r < 4, (15 : ℕ).testBit r = true := by decide

theorem bxc : ∀ x c c' : Bool, xor c x = xor c' x → c = c' := by decide

/-- Two strips that agree on all replies below `N` and on bits `N`, `N+1` agree below `N+2`. -/
theorem back (b b' : ℕ → Bool) (N : ℕ) (hc : ∀ j < N, chiF b j = chiF b' j)
    (h0 : b N = b' N) (h1 : b (N+1) = b' (N+1)) : ∀ p ≤ N+1, b p = b' p := by
  have key : ∀ t p, p + t = N → b p = b' p ∧ b (p+1) = b' (p+1) := by
    intro t
    induction t with
    | zero => intro p hp; subst hp; exact ⟨h0, h1⟩
    | succ t ih =>
      intro p hp
      obtain ⟨ha, hb⟩ := ih (p+1) (by omega)
      have hcp := hc p (by omega)
      unfold chiF at hcp
      rw [ha, hb] at hcp
      exact ⟨bxc _ _ _ hcp, ha⟩
  intro p hp
  rcases Nat.lt_or_ge p (N+1) with h | h
  · exact (key (N-p) p (by omega)).1
  · rw [show p = N+1 by omega]; exact h1

/-! Witness numbers with a prescribed mixed window. -/

def gw (P : ℕ → Bool) (e top i : ℕ) : Bool :=
  if hi : i < top then xor (P i) (xor (gw P e top (i+(e+1))) (gw P e top (i+2*(e+1))))
  else false
termination_by top - i
decreasing_by all_goals omega

theorem gw_ge (P : ℕ → Bool) (e top i : ℕ) (h : top ≤ i) : gw P e top i = false := by
  rw [gw, dif_neg (by omega)]

theorem gw_lt (P : ℕ → Bool) (e top i : ℕ) (h : i < top) :
    gw P e top i = xor (P i) (xor (gw P e top (i+(e+1))) (gw P e top (i+2*(e+1)))) := by
  rw [gw, dif_pos h]

def nb (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n+1 => 2^n * (if f n then 1 else 0) + nb f n

theorem nb_lt (f : ℕ → Bool) (n : ℕ) : nb f n < 2^n := by
  induction n with
  | zero => simp [nb]
  | succ n ih =>
    rw [nb, pow_succ]
    split_ifs <;> omega

theorem tb1 (j : ℕ) : (1 : ℕ).testBit j = decide (j = 0) := by
  cases j with
  | zero => rfl
  | succ j => rw [Nat.testBit_succ]; simp

theorem nb_bit (f : ℕ → Bool) (n i : ℕ) : (nb f n).testBit i = (decide (i < n) && f i) := by
  induction n with
  | zero => simp [nb]
  | succ n ih =>
    rw [nb, Nat.testBit_two_pow_mul_add _ (nb_lt f n)]
    by_cases h1 : i < n
    · rw [if_pos h1, ih]; simp [h1, show i < n+1 by omega]
    · rw [if_neg h1]
      by_cases hin : i = n
      · subst hin; cases h2 : f i <;> simp [h2]
      · have : i - n ≠ 0 := by omega
        cases h2 : f n <;> simp [h2, tb1, this, show ¬ i < n+1 by omega]

theorem bxx : ∀ p a : Bool, xor (xor p a) a = p := by decide

theorem witness (P : ℕ → Bool) (e top : ℕ) :
    nb (gw P e top) top < 2^top ∧ ∀ i < top, mixN (e+1) (nb (gw P e top) top) i = P i := by
  have tbx : ∀ i, (nb (gw P e top) top).testBit i = gw P e top i := by
    intro i; rw [nb_bit]
    by_cases h : i < top
    · simp [h]
    · simp [h, gw_ge P e top i (by omega)]
  refine ⟨nb_lt _ _, ?_⟩
  intro i hi
  unfold mixN
  rw [tbx, tbx, tbx, gw_lt P e top i hi]
  exact bxx _ _

/-! Finite facts on the last six positions. -/

def qv : Fin 4 → ℕ
  | 0 => 3
  | 1 => 7
  | 2 => 9
  | 3 => 15

theorem qv_mem : ∀ i : Fin 4, qv i ∈ ({3, 7, 9, 15} : Finset ℕ) := by decide

theorem qv_inj : ∀ i j : Fin 4, qv i = qv j → i = j := by decide

theorem Q4_cover : ∀ q ∈ ({3, 7, 9, 15} : Finset ℕ), ∃ i : Fin 4, qv i = q := by decide

theorem Q4_facts : ∀ q ∈ ({3, 7, 9, 15} : Finset ℕ), q.testBit 0 = true ∧
    chiB (q.testBit 0) (q.testBit 1) (q.testBit 2) = true ∧
    chiB (q.testBit 1) (q.testBit 2) (q.testBit 3) = true := by decide

theorem coll : ∀ (l1 m1 m2 m3 m4 m5 f1 f2 : Bool), (f1 && f2) = false → ∃ i j : Fin 4, i ≠ j ∧
    (f1 = true →
      chiB (xor l1 m1) (xor ((qv i).testBit 0) m2) (xor ((qv i).testBit 1) m3) =
      chiB (xor l1 m1) (xor ((qv j).testBit 0) m2) (xor ((qv j).testBit 1) m3)) ∧
    (f2 = true →
      chiB (xor ((qv i).testBit 0) m2) (xor ((qv i).testBit 1) m3) (xor ((qv i).testBit 2) m4) =
      chiB (xor ((qv j).testBit 0) m2) (xor ((qv j).testBit 1) m3) (xor ((qv j).testBit 2) m4)) ∧
    chiB (xor ((qv i).testBit 1) m3) (xor ((qv i).testBit 2) m4) (xor ((qv i).testBit 3) m5) =
      chiB (xor ((qv j).testBit 1) m3) (xor ((qv j).testBit 2) m4) (xor ((qv j).testBit 3) m5) := by
  decide

theorem injF : ∀ l0 l1 b2 b3 b4 b5 l0' l1' b2' b3' b4' b5' : Bool,
    chiB l0 l1 b2 = chiB l0' l1' b2' → chiB l1 b2 b3 = chiB l1' b2' b3' →
    chiB b2 b3 b4 = chiB b2' b3' b4' → chiB b3 b4 b5 = chiB b3' b4' b5' →
    chiB (xor l0 false) (xor l1 (!chiB b3 b4 b5)) (xor b2 (chiB b3 b4 b5)) =
      chiB (xor l0' false) (xor l1' (!chiB b3 b4 b5)) (xor b2' (chiB b3 b4 b5)) →
    chiB (xor b2 (chiB b3 b4 b5)) (xor b3 (chiB b3 b4 b5)) (xor b4 true) =
      chiB (xor b2' (chiB b3 b4 b5)) (xor b3' (chiB b3 b4 b5)) (xor b4' true) →
    chiB (xor b3 (chiB b3 b4 b5)) (xor b4 true) (xor b5 false) =
      chiB (xor b3' (chiB b3 b4 b5)) (xor b4' true) (xor b5' false) →
    (b2 && b3 && b4 && b5) = false → (b2' && b3' && b4' && b5') = false →
    b2 = b2' ∧ b3 = b3' ∧ b4 = b4' ∧ b5 = b5' := by
  decide

/-! The ceiling. -/

theorem first_Q4 (k L q : ℕ) (hL : L < 2^(k+2)) (hq : q ∈ ({3, 7, 9, 15} : Finset ℕ)) :
    firstF (k+4) (enc k (q, L)) = firstF (k+4) (enc k (3, L)) := by
  obtain ⟨f0, f2, f3⟩ := Q4_facts q hq
  obtain ⟨g0, g2, g3⟩ := Q4_facts 3 (by decide)
  unfold firstF
  apply filter_congr
  intro j hj
  rw [mem_range] at hj
  suffices H : chiF (fun i => (enc k (q, L)).testBit i) j =
      chiF (fun i => (enc k (3, L)).testBit i) j by rw [H]
  rcases Nat.lt_or_ge j k with h | h
  · simp only [chi_at]
    rw [encLo k q L j hL (by omega), encLo k q L (j+1) hL (by omega),
      encLo k q L (j+2) hL (by omega), encLo k 3 L j hL (by omega),
      encLo k 3 L (j+1) hL (by omega), encLo k 3 L (j+2) hL (by omega)]
  · obtain h' | h' | h' | h' : j = k ∨ j = k+1 ∨ j = k+2 ∨ j = k+3 := by omega
    · subst h'; simp only [chi_k0]; rw [e0 _ _ _ hL, e1 _ _ _ hL, e2 _ _ _ hL, e0 _ _ _ hL,
        e1 _ _ _ hL, e2 _ _ _ hL, f0, g0]
    · subst h'; simp only [chi_k1]; rw [e1 _ _ _ hL, e2 _ _ _ hL, e3 _ _ _ hL, e1 _ _ _ hL,
        e2 _ _ _ hL, e3 _ _ _ hL, f0, g0, chiB_true, chiB_true]
    · subst h'; simp only [chi_k2]; rw [e2 _ _ _ hL, e3 _ _ _ hL, e4 _ _ _ hL, e2 _ _ _ hL,
        e3 _ _ _ hL, e4 _ _ _ hL, f2, g2]
    · subst h'; simp only [chi_k3]; rw [e3 _ _ _ hL, e4 _ _ _ hL, e5 _ _ _ hL, e3 _ _ _ hL,
        e4 _ _ _ hL, e5 _ _ _ hL, f3, g3]

theorem perL (k d L : ℕ) (hL : L < 2^(k+2)) (pick : Finset ℕ → ℕ) (mask : Finset ℕ → Finset ℕ)
    (hS : mask (firstF (k+4) (enc k (3, L))) ⊆ range (k+4))
    (hmiss : k+1 ∉ mask (firstF (k+4) (enc k (3, L))) ∨
      k+2 ∉ mask (firstF (k+4) (enc k (3, L)))) :
    (({3, 7, 9, 15} : Finset ℕ).image (fun q => T (k+4) d pick mask (enc k (q, L)))).card ≤ 3 := by
  set Z := firstF (k+4) (enc k (3, L)) with hZdef
  set m : ℕ → Bool := fun i => mixN d (pick Z) i with hm
  have hf : (decide (k+1 ∈ mask Z) && decide (k+2 ∈ mask Z)) = false := by
    rcases hmiss with h | h <;> simp [h]
  obtain ⟨i, j, hij, c1, c2, c3⟩ := coll (L.testBit (k+1)) (m (k+1)) (m (k+2)) (m (k+3))
    (m (k+4)) (m (k+5)) _ _ hf
  have hTe : T (k+4) d pick mask (enc k (qv i, L)) = T (k+4) d pick mask (enc k (qv j, L)) := by
    unfold T
    rw [first_Q4 k L _ hL (qv_mem i), first_Q4 k L _ hL (qv_mem j)]
    congr 1
    apply filter_congr
    intro p hp
    have hp4 : p < k+4 := mem_range.mp (hS hp)
    suffices H : chiF (fun t => xor ((enc k (qv i, L)).testBit t) (m t)) p =
        chiF (fun t => xor ((enc k (qv j, L)).testBit t) (m t)) p by
      simp only [hm] at H; rw [H]
    rcases Nat.lt_or_ge p k with h | h
    · simp only [chi_at]
      rw [encLo k _ L p hL (by omega), encLo k _ L (p+1) hL (by omega),
        encLo k _ L (p+2) hL (by omega), encLo k _ L p hL (by omega),
        encLo k _ L (p+1) hL (by omega), encLo k _ L (p+2) hL (by omega)]
    · obtain h' | h' | h' | h' : p = k ∨ p = k+1 ∨ p = k+2 ∨ p = k+3 := by omega
      · subst h'; simp only [chi_k0]
        rw [e0 _ _ _ hL, e1 _ _ _ hL, e2 _ _ _ hL, e0 _ _ _ hL, e1 _ _ _ hL, e2 _ _ _ hL,
          (Q4_facts _ (qv_mem i)).1, (Q4_facts _ (qv_mem j)).1]
      · subst h'; simp only [chi_k1]
        rw [e1 _ _ _ hL, e2 _ _ _ hL, e3 _ _ _ hL, e1 _ _ _ hL, e2 _ _ _ hL, e3 _ _ _ hL]
        exact c1 (decide_eq_true hp)
      · subst h'; simp only [chi_k2]
        rw [e2 _ _ _ hL, e3 _ _ _ hL, e4 _ _ _ hL, e2 _ _ _ hL, e3 _ _ _ hL, e4 _ _ _ hL]
        exact c2 (decide_eq_true hp)
      · subst h'; simp only [chi_k3]
        rw [e3 _ _ _ hL, e4 _ _ _ hL, e5 _ _ _ hL, e3 _ _ _ hL, e4 _ _ _ hL, e5 _ _ _ hL]
        exact c3
  have hne : (({3, 7, 9, 15} : Finset ℕ).image
      (fun q => T (k+4) d pick mask (enc k (q, L)))).card ≠ ({3, 7, 9, 15} : Finset ℕ).card := by
    intro hc
    have hinj := Finset.card_image_iff.mp hc
    exact hij (qv_inj i j (hinj (qv_mem i) (qv_mem j) hTe))
  have hle := card_image_le (s := ({3, 7, 9, 15} : Finset ℕ))
    (f := fun q => T (k+4) d pick mask (enc k (q, L)))
  have h4 : ({3, 7, 9, 15} : Finset ℕ).card = 4 := by decide
  omega

theorem upperX (k d : ℕ) (pick : Finset ℕ → ℕ) (mask : Finset ℕ → Finset ℕ)
    (hyp : ∀ z ∈ (range (2^(k+4+2))).image (firstF (k+4)),
      pick z < 2^(k+4+2+2*d) ∧ mask z ⊆ range (k+4) ∧ (k+4-3 ∉ mask z ∨ k+4-2 ∉ mask z)) :
    ((range (2^(k+4+2))).image (T (k+4) d pick mask)).card ≤ 15 * 2^(k+4-2) := by
  rw [show k+4-2 = k+2 by omega]
  have hmem : ∀ q < 16, ∀ L < 2^(k+2), enc k (q, L) ∈ range (2^(k+4+2)) := by
    intro q hq L hL
    rw [strips_eq]; exact mem_image.mpr ⟨(q, L), by simp [hq, hL], rfl⟩
  rw [strips_eq, image_image]
  set F := T (k+4) d pick mask ∘ enc k with hF
  set M := 2^(k+2) with hMdef
  set Q4 : Finset ℕ := {3, 7, 9, 15} with hQ4
  have hsplit : range 16 ×ˢ range M =
      (Q4 ×ˢ range M) ∪ (((range 16).filter (fun q => q ∉ Q4)) ×ˢ range M) := by
    ext ⟨q, L⟩
    simp only [hQ4, mem_union, mem_product, mem_range, mem_filter, mem_insert, mem_singleton]
    omega
  rw [hsplit, image_union]
  refine (card_union_le _ _).trans ?_
  have h12 : ((range 16).filter (fun q => q ∉ Q4)).card = 12 := by rw [hQ4]; decide
  have hB : ((((range 16).filter (fun q => q ∉ Q4)) ×ˢ range M).image F).card ≤ 12 * M := by
    refine card_image_le.trans ?_
    rw [card_product, h12, card_range]
  have hA : ((Q4 ×ˢ range M).image F).card ≤ 3 * M := by
    have hsub : (Q4 ×ˢ range M).image F ⊆
        (range M).biUnion (fun L => Q4.image (fun q => T (k+4) d pick mask (enc k (q, L)))) := by
      intro w hw
      simp only [mem_image, mem_product, Prod.exists] at hw
      obtain ⟨q, L, ⟨hq, hL⟩, rfl⟩ := hw
      exact mem_biUnion.mpr ⟨L, hL, mem_image.mpr ⟨q, hq, rfl⟩⟩
    refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
    have := Finset.sum_le_card_nsmul (range M)
      (fun L => (Q4.image (fun q => T (k+4) d pick mask (enc k (q, L)))).card) 3 (by
        intro L hL
        rw [mem_range] at hL
        have h3 := hyp (firstF (k+4) (enc k (3, L)))
          (mem_image.mpr ⟨_, hmem 3 (by norm_num) L hL, rfl⟩)
        obtain ⟨_, hS, hmiss⟩ := h3
        rw [show k+4-3 = k+1 by omega, show k+4-2 = k+2 by omega] at hmiss
        exact perL k d L hL pick mask hS hmiss)
    rw [card_range, smul_eq_mul] at this
    linarith
  linarith

/-! The matching construction. -/

theorem lowerX (k d : ℕ) (hd : 0 < d) : ∃ x y : ℕ, x < 2^(k+4+2+2*d) ∧ y < 2^(k+4+2+2*d) ∧
    ((range (2^(k+4+2))).image (T (k+4) d (fun z => if k+4-1 ∈ z then y else x)
      (fun _ => {k+4-4, k+4-2, k+4-1}))).card = 15 * 2^(k+4-2) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e+1 := ⟨d-1, by omega⟩
  set P0 : ℕ → Bool := fun i => decide (i = k+1 ∨ i = k+4) with hP0
  set P1 : ℕ → Bool := fun i => decide (k+2 ≤ i ∧ i ≤ k+4) with hP1
  obtain ⟨hx, mx⟩ := witness P0 e (k+6)
  obtain ⟨hy, my⟩ := witness P1 e (k+6)
  set x := nb (gw P0 e (k+6)) (k+6)
  set y := nb (gw P1 e (k+6)) (k+6)
  have hlim : 2^(k+6) ≤ 2^(k+4+2+2*(e+1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨x, y, lt_of_lt_of_le hx hlim, lt_of_lt_of_le hy hlim, ?_⟩
  refine le_antisymm (upperX k (e+1) _ _ ?_) ?_
  · intro z _
    refine ⟨?_, ?_, Or.inl ?_⟩
    · split_ifs
      · exact lt_of_lt_of_le hy hlim
      · exact lt_of_lt_of_le hx hlim
    · intro p hp; simp only [mem_insert, mem_singleton] at hp; rw [mem_range]; omega
    · simp only [mem_insert, mem_singleton]; omega
  simp only [show k+4-1 = k+3 by omega, show k+4-4 = k by omega, show k+4-2 = k+2 by omega]
  set G := T (k+4) (e+1) (fun z => if k+3 ∈ z then y else x) (fun _ => {k, k+2, k+3})
    with hG
  set M := 2^(k+2) with hMdef
  set D := ((range 16).erase 15) ×ˢ range M with hD
  have hsub : D.image (G ∘ enc k) ⊆ (range (2^(k+4+2))).image G := by
    rw [strips_eq, image_image]
    exact image_subset_image (product_subset_product (erase_subset _ _) (Subset.refl _))
  have hcardD : D.card = 15 * M := by
    rw [hD, card_product, card_erase_of_mem (by simp), card_range, card_range]
  rw [← hcardD]
  refine le_trans (le_of_eq ?_) (card_le_card hsub)
  symm
  apply card_image_of_injOn
  rintro ⟨q, L⟩ hp ⟨q', L'⟩ hp' heq
  simp only [hD, coe_product, Set.mem_prod, coe_erase, coe_range, Set.mem_diff,
    Set.mem_Iio, Set.mem_singleton_iff] at hp hp'
  obtain ⟨⟨hq, hq15⟩, hL⟩ := hp
  obtain ⟨⟨hq', hq15'⟩, hL'⟩ := hp'
  simp only [Function.comp, hG, T] at heq
  have hz := congrArg Prod.fst heq
  have hr := congrArg Prod.snd heq
  simp only at hz hr
  rw [← hz] at hr
  set Z := firstF (k+4) (enc k (q, L)) with hZ
  have hc : ∀ j < k+4, chiF (fun i => (enc k (q, L)).testBit i) j =
      chiF (fun i => (enc k (q', L')).testBit i) j := by
    intro j hj
    have := congrArg (j ∈ ·) hz
    simp only [hZ, firstF, mem_filter, mem_range, hj, true_and] at this
    exact Bool.eq_iff_iff.mpr (Iff.of_eq this)
  set m : ℕ → Bool := fun i => mixN (e+1) (if k+3 ∈ Z then y else x) i with hm
  have hrd : ∀ p ∈ ({k, k+2, k+3} : Finset ℕ),
      chiF (fun t => xor ((enc k (q, L)).testBit t) (m t)) p =
      chiF (fun t => xor ((enc k (q', L')).testBit t) (m t)) p := by
    intro p hp
    have := congrArg (p ∈ ·) hr
    simp only [mem_filter, hp, true_and] at this
    exact Bool.eq_iff_iff.mpr (Iff.of_eq this)
  -- the shared reply bit at k+3 decides the mixed window
  set c3 := chiB (q.testBit 1) (q.testBit 2) (q.testBit 3) with hc3
  have hk3 : chiF (fun i => (enc k (q, L)).testBit i) (k+3) = c3 := by
    simp only [chi_k3]; rw [e3 _ _ _ hL, e4 _ _ _ hL, e5 _ _ _ hL]
  have hmv : m k = false ∧ m (k+1) = !c3 ∧ m (k+2) = c3 ∧ m (k+3) = c3 ∧
      m (k+4) = true ∧ m (k+5) = false := by
    have hmem : (k+3 ∈ Z) ↔ c3 = true := by
      rw [hZ, firstF, mem_filter, mem_range, hk3]; simp
    by_cases hc : c3 = true
    · have : k+3 ∈ Z := hmem.mpr hc
      simp only [hm, if_pos this]
      rw [my k (by omega), my (k+1) (by omega), my (k+2) (by omega), my (k+3) (by omega),
        my (k+4) (by omega), my (k+5) (by omega), hc]
      simp [hP1]
    · have : k+3 ∉ Z := fun h => hc (hmem.mp h)
      simp only [hm, if_neg this]
      rw [mx k (by omega), mx (k+1) (by omega), mx (k+2) (by omega), mx (k+3) (by omega),
        mx (k+4) (by omega), mx (k+5) (by omega)]
      simp only [Bool.not_eq_true] at hc
      rw [hc]
      simp [hP0]
  obtain ⟨m0, m1, m2, m3, m4, m5⟩ := hmv
  have r0 := hrd k (by simp)
  have r2 := hrd (k+2) (by simp)
  have r3 := hrd (k+3) (by simp)
  simp only [chi_k0] at r0
  simp only [chi_k2] at r2
  simp only [chi_k3] at r3
  rw [e0 _ _ _ hL, e1 _ _ _ hL, e2 _ _ _ hL, e0 _ _ _ hL', e1 _ _ _ hL', e2 _ _ _ hL',
    m0, m1, m2] at r0
  rw [e2 _ _ _ hL, e3 _ _ _ hL, e4 _ _ _ hL, e2 _ _ _ hL', e3 _ _ _ hL', e4 _ _ _ hL',
    m2, m3, m4] at r2
  rw [e3 _ _ _ hL, e4 _ _ _ hL, e5 _ _ _ hL, e3 _ _ _ hL', e4 _ _ _ hL', e5 _ _ _ hL',
    m3, m4, m5] at r3
  have c0 := hc k (by omega)
  have c1 := hc (k+1) (by omega)
  have c2 := hc (k+2) (by omega)
  have c3' := hc (k+3) (by omega)
  simp only [chi_k0] at c0
  simp only [chi_k1] at c1
  simp only [chi_k2] at c2
  simp only [chi_k3] at c3'
  rw [e0 _ _ _ hL, e1 _ _ _ hL, e2 _ _ _ hL, e0 _ _ _ hL', e1 _ _ _ hL', e2 _ _ _ hL'] at c0
  rw [e1 _ _ _ hL, e2 _ _ _ hL, e3 _ _ _ hL, e1 _ _ _ hL', e2 _ _ _ hL', e3 _ _ _ hL'] at c1
  rw [e2 _ _ _ hL, e3 _ _ _ hL, e4 _ _ _ hL, e2 _ _ _ hL', e3 _ _ _ hL', e4 _ _ _ hL'] at c2
  rw [e3 _ _ _ hL, e4 _ _ _ hL, e5 _ _ _ hL, e3 _ _ _ hL', e4 _ _ _ hL', e5 _ _ _ hL'] at c3'
  have n15 : ∀ v : ℕ, v < 16 → v ≠ 15 →
      (v.testBit 0 && v.testBit 1 && v.testBit 2 && v.testBit 3) = false := by
    intro v hv hv15
    by_contra hcon
    simp only [Bool.not_eq_false, Bool.and_eq_true] at hcon
    obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := hcon
    apply hv15
    apply nib_eq v 15 hv (by norm_num)
    intro r hr
    rw [bits15 r hr]
    interval_cases r <;> assumption
  obtain ⟨b2, b3, b4, b5⟩ := injF _ _ _ _ _ _ _ _ _ _ _ _ c0 c1 c2 c3' r0 r2 r3
    (n15 q hq hq15) (n15 q' hq' hq15')
  have hqq : q = q' := by
    apply nib_eq q q' hq hq'
    intro r hr
    interval_cases r <;> assumption
  subst hqq
  have hLL : L = L' := by
    apply low_eq k L L' hL hL'
    intro i hi
    have hb := back (fun i => (enc k (q, L)).testBit i) (fun i => (enc k (q, L')).testBit i)
      (k+2) (fun j hj => hc j (by omega))
      (by rw [e2 _ _ _ hL, e2 _ _ _ hL'])
      (by rw [e3 _ _ _ hL, e3 _ _ _ hL']) i (by omega)
    rw [encLo k q L i hL hi, encLo k q L' i hL' hi] at hb
    exact hb
  rw [hLL]

end PEqualNP.Outside.L_meta_38164

open PEqualNP.Outside.L_meta_38164 in
theorem PEqualNP.Outside.L_meta_38164 : ∀ (h d : Nat), 4 ≤ h → 0 < d →
  let strips := Finset.range (2^(h+2))
  let limit := 2^(h+2+2*d)
  let mix := fun (x i : Nat) =>
    xor (x.testBit i) (xor (x.testBit (i+d)) (x.testBit (i+2*d)))
  let chi := fun (bits : Nat → Bool) (j : Nat) =>
    xor (bits j) (!(bits (j+1)) && bits (j+2))
  let first := fun u : Nat =>
    (Finset.range h).filter (fun j => chi (fun i => u.testBit i) j)
  let count := fun (pick : Finset Nat → Nat) (mask : Finset Nat → Finset Nat) =>
    (strips.image (fun u =>
      let z := first u
      let bits := fun i : Nat => xor (u.testBit i) (mix (pick z) i)
      (z, (mask z).filter (fun j => chi bits j)))).card
  (∃ x y : Nat, x < limit ∧ y < limit ∧
    count (fun z => if h-1 ∈ z then y else x)
      (fun _ => {h-4,h-2,h-1}) = 15 * 2^(h-2)) ∧
  ∀ (pick : Finset Nat → Nat) (mask : Finset Nat → Finset Nat),
    (∀ z ∈ strips.image first, pick z < limit ∧ mask z ⊆ Finset.range h ∧
      (h-3 ∉ mask z ∨ h-2 ∉ mask z)) →
    count pick mask ≤ 15 * 2^(h-2) := by
  intro h d hh hd strips limit mix chi first count
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 4 := ⟨h - 4, by omega⟩
  exact ⟨lowerX k d hd, fun pick mask hyp => upperX k d pick mask hyp⟩
