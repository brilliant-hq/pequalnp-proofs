import PEqualNP.Defs

-- L-meta-38164. The image comparison cimg and the shape of the flip induction fwd are adapted from our
-- merged L_meta_33621; the bit view of the mixed shift follows L_meta_25883. Both are in this
-- repository; this file imports only PEqualNP.Defs.

namespace PEqualNP.Outside.L_meta_38164_aux

def chi (b : ℕ → Bool) (j : ℕ) : Bool := xor (b j) (!(b (j+1)) && b (j+2))

def mixb (d x i : ℕ) : Bool := xor (x.testBit i) (xor (x.testBit (i+d)) (x.testBit (i+2*d)))

def frs (h u : ℕ) : Finset ℕ := (Finset.range h).filter (fun j => chi (fun i => u.testBit i) j)

def rv (d p u j : ℕ) : Bool := chi (fun i => xor (u.testBit i) (mixb d p i)) j

def rd (d p u : ℕ) (M : Finset ℕ) : Finset ℕ := M.filter (fun j => rv d p u j)

def tr (h d : ℕ) (pick : Finset ℕ → ℕ) (mask : Finset ℕ → Finset ℕ) (u : ℕ) :
    Finset ℕ × Finset ℕ :=
  (frs h u, rd d (pick (frs h u)) u (mask (frs h u)))

def tl (h u : ℕ) : Bool × Bool := (u.testBit h, u.testBit (h+1))

def rr (a b c x y w : Bool) : Bool := xor (xor a x) (!(xor b y) && xor c w)

def mg (b s t : Bool) : Bool × Bool := (s && !(b && t), t)

def Phi (Z1 M1 M2 M3 M4 M5 A1 A2 A3 s t : Bool) : Bool × Bool × Bool :=
  (A1 && rr Z1 true (xor true (!s && t)) M1 M2 M3,
   A2 && rr true (xor true (!s && t)) s M2 M3 M4,
   A3 && rr (xor true (!s && t)) s t M3 M4 M5)

def code (d p : ℕ) (M : Finset ℕ) (n u : ℕ) : Bool × Bool × Bool :=
  (decide (n+1 ∈ M) && rv d p u (n+1), decide (n+2 ∈ M) && rv d p u (n+2),
   decide (n+3 ∈ M) && rv d p u (n+3))

def tx (n i : ℕ) : Bool := if i = n+1 then true else if i = n+4 then true else false

def ty (n i : ℕ) : Bool :=
  if i = n+2 then true else if i = n+3 then true else if i = n+4 then true else false

-- Boolean facts

theorem xsolve {a X Z : Bool} (h : xor a X = Z) : a = xor Z X := by
  subst h
  revert a X
  decide

theorem xcancel {m e L : Bool} (h : xor m L = xor e L) : m = e := by
  revert h
  revert m e L
  decide

set_option maxHeartbeats 2000000 in
theorem coreU : ∀ Z1 M1 M2 M3 M4 M5 A1 A2 A3 : Bool, (A1 && A2) = false →
    (Phi Z1 M1 M2 M3 M4 M5 A1 A2 A3 false false = Phi Z1 M1 M2 M3 M4 M5 A1 A2 A3 true false ∨
     Phi Z1 M1 M2 M3 M4 M5 A1 A2 A3 false false = Phi Z1 M1 M2 M3 M4 M5 A1 A2 A3 false true ∨
     Phi Z1 M1 M2 M3 M4 M5 A1 A2 A3 false false = Phi Z1 M1 M2 M3 M4 M5 A1 A2 A3 true true ∨
     Phi Z1 M1 M2 M3 M4 M5 A1 A2 A3 true false = Phi Z1 M1 M2 M3 M4 M5 A1 A2 A3 false true ∨
     Phi Z1 M1 M2 M3 M4 M5 A1 A2 A3 true false = Phi Z1 M1 M2 M3 M4 M5 A1 A2 A3 true true ∨
     Phi Z1 M1 M2 M3 M4 M5 A1 A2 A3 false true = Phi Z1 M1 M2 M3 M4 M5 A1 A2 A3 true true) := by
  decide

set_option maxHeartbeats 2000000 in
theorem coreLx : ∀ Z0 Z1 Z2 s t s' t' : Bool,
    ∀ a3, a3 = xor false (!s && t) → ∀ a2, a2 = xor Z2 (!a3 && s) →
    ∀ a1, a1 = xor Z1 (!a2 && a3) → ∀ a0, a0 = xor Z0 (!a1 && a2) →
    ∀ b3, b3 = xor false (!s' && t') → ∀ b2, b2 = xor Z2 (!b3 && s') →
    ∀ b1, b1 = xor Z1 (!b2 && b3) → ∀ b0, b0 = xor Z0 (!b1 && b2) →
    rr a0 a1 a2 false true false = rr b0 b1 b2 false true false →
    rr a2 a3 s false false true = rr b2 b3 s' false false true →
    rr a3 s t false true false = rr b3 s' t' false true false →
    s = s' ∧ t = t' := by
  intro Z0 Z1 Z2 s t s' t' a3 h3 a2 h2 a1 h1 a0 h0 b3 g3 b2 g2 b1 g1 b0 g0
  subst h0 h1 h2 h3 g0 g1 g2 g3
  revert Z0 Z1 Z2 s t s' t'
  decide

set_option maxHeartbeats 2000000 in
theorem coreLy : ∀ Z0 Z1 Z2 s t s' t' : Bool,
    ∀ a3, a3 = xor true (!s && t) → ∀ a2, a2 = xor Z2 (!a3 && s) →
    ∀ a1, a1 = xor Z1 (!a2 && a3) → ∀ a0, a0 = xor Z0 (!a1 && a2) →
    ∀ b3, b3 = xor true (!s' && t') → ∀ b2, b2 = xor Z2 (!b3 && s') →
    ∀ b1, b1 = xor Z1 (!b2 && b3) → ∀ b0, b0 = xor Z0 (!b1 && b2) →
    rr a0 a1 a2 false false true = rr b0 b1 b2 false false true →
    rr a2 a3 s true true true = rr b2 b3 s' true true true →
    rr a3 s t true true false = rr b3 s' t' true true false →
    mg Z2 s t = mg Z2 s' t' := by
  intro Z0 Z1 Z2 s t s' t' a3 h3 a2 h2 a1 h1 a0 h0 b3 g3 b2 g2 b1 g1 b0 g0
  subst h0 h1 h2 h3 g0 g1 g2 g3
  revert Z0 Z1 Z2 s t s' t'
  decide

theorem mgcard : ∀ b : Bool,
    ((Finset.univ : Finset (Bool × Bool)).image (fun q => mg b q.1 q.2)).card =
      if b = true then 3 else 4 := by
  decide

theorem txv (n : ℕ) : tx n n = false ∧ tx n (n+1) = true ∧ tx n (n+2) = false ∧
    tx n (n+3) = false ∧ tx n (n+4) = true ∧ tx n (n+5) = false := by
  unfold tx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> split_ifs <;> first | rfl | omega

theorem tyv (n : ℕ) : ty n n = false ∧ ty n (n+1) = false ∧ ty n (n+2) = true ∧
    ty n (n+3) = true ∧ ty n (n+4) = true ∧ ty n (n+5) = false := by
  unfold ty
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> split_ifs <;> first | rfl | omega

-- Finset helpers

theorem cimg {α β : Type} [DecidableEq α] [DecidableEq β] (s : Finset ℕ) (f : ℕ → α) (g : ℕ → β)
    (h : ∀ u ∈ s, ∀ v ∈ s, g u = g v → f u = f v) : (s.image f).card ≤ (s.image g).card := by
  have e1 : (s.image (fun u => (g u, f u))).image Prod.snd = s.image f := Finset.image_image
  have e2 : (s.image (fun u => (g u, f u))).image Prod.fst = s.image g := Finset.image_image
  have inj : Set.InjOn Prod.fst ((s.image (fun u => (g u, f u)) : Finset (β × α)) : Set (β × α)) := by
    intro p hp q hq hpq
    rw [Finset.coe_image] at hp hq
    obtain ⟨u, hu, rfl⟩ := hp
    obtain ⟨v, hv, rfl⟩ := hq
    have h1 : g u = g v := hpq
    exact Prod.ext h1 (h u hu v hv h1)
  rw [← e1, ← e2, Finset.card_image_of_injOn inj]
  exact Finset.card_image_le

theorem card3 {β : Type} [DecidableEq β] (Φ : Bool × Bool → β) (a b : Bool × Bool) (hab : a ≠ b)
    (he : Φ a = Φ b) : ((Finset.univ : Finset (Bool × Bool)).image Φ).card ≤ 3 := by
  have sub : (Finset.univ : Finset (Bool × Bool)).image Φ ⊆
      ((Finset.univ : Finset (Bool × Bool)).erase a).image Φ := by
    intro c hc
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hc
    by_cases hea : e = a
    · rw [hea, he]
      exact Finset.mem_image_of_mem Φ (Finset.mem_erase.mpr ⟨fun hba => hab hba.symm, Finset.mem_univ b⟩)
    · exact Finset.mem_image_of_mem Φ (Finset.mem_erase.mpr ⟨hea, Finset.mem_univ e⟩)
  calc ((Finset.univ : Finset (Bool × Bool)).image Φ).card
      ≤ (((Finset.univ : Finset (Bool × Bool)).erase a).image Φ).card := Finset.card_le_card sub
    _ ≤ ((Finset.univ : Finset (Bool × Bool)).erase a).card := Finset.card_image_le
    _ = 3 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_prod,
          Fintype.card_bool]

theorem coreU' (Z1 M1 M2 M3 M4 M5 A1 A2 A3 : Bool) (hA : (A1 && A2) = false) :
    ((Finset.univ : Finset (Bool × Bool)).image
      (fun q => Phi Z1 M1 M2 M3 M4 M5 A1 A2 A3 q.1 q.2)).card ≤ 3 := by
  rcases coreU Z1 M1 M2 M3 M4 M5 A1 A2 A3 hA with e | e | e | e | e | e
  · exact card3 (fun q => Phi Z1 M1 M2 M3 M4 M5 A1 A2 A3 q.1 q.2) (false, false) (true, false)
      (by decide) e
  · exact card3 (fun q => Phi Z1 M1 M2 M3 M4 M5 A1 A2 A3 q.1 q.2) (false, false) (false, true)
      (by decide) e
  · exact card3 (fun q => Phi Z1 M1 M2 M3 M4 M5 A1 A2 A3 q.1 q.2) (false, false) (true, true)
      (by decide) e
  · exact card3 (fun q => Phi Z1 M1 M2 M3 M4 M5 A1 A2 A3 q.1 q.2) (true, false) (false, true)
      (by decide) e
  · exact card3 (fun q => Phi Z1 M1 M2 M3 M4 M5 A1 A2 A3 q.1 q.2) (true, false) (true, true)
      (by decide) e
  · exact card3 (fun q => Phi Z1 M1 M2 M3 M4 M5 A1 A2 A3 q.1 q.2) (false, true) (true, true)
      (by decide) e

theorem sumIns {s : Finset ℕ} {a : ℕ} (ha : a ∉ s) (f : Finset ℕ → ℕ) :
    Finset.sum (insert a s).powerset f = Finset.sum s.powerset (fun t => f t + f (insert a t)) := by
  rw [Finset.sum_powerset_insert ha, Finset.sum_add_distrib]

theorem sum15 (n : ℕ) :
    Finset.sum (Finset.range (n+4)).powerset (fun z => if n+2 ∈ z ∧ n+3 ∈ z then 3 else 4) =
      15 * 2^(n+2) := by
  have e : Finset.range (n+4) = insert (n+3) (insert (n+2) (Finset.range (n+2))) := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_range]
    omega
  have h3 : n + 3 ∉ insert (n+2) (Finset.range (n+2)) := by
    intro hm
    rw [Finset.mem_insert, Finset.mem_range] at hm
    omega
  have h2 : n + 2 ∉ Finset.range (n+2) := by
    intro hm
    rw [Finset.mem_range] at hm
    omega
  rw [e, sumIns h3, sumIns h2]
  calc Finset.sum (Finset.range (n+2)).powerset _
      = Finset.sum (Finset.range (n+2)).powerset (fun _ => 15) := by
        apply Finset.sum_congr rfl
        intro t ht
        have hs := Finset.mem_powerset.mp ht
        have n2 : n + 2 ∉ t := fun hm => by have := Finset.mem_range.mp (hs hm); omega
        have n3 : n + 3 ∉ t := fun hm => by have := Finset.mem_range.mp (hs hm); omega
        simp [Finset.mem_insert, n2, n3]
    _ = 15 * 2^(n+2) := by
        rw [Finset.sum_const, Finset.card_powerset, Finset.card_range, smul_eq_mul]
        ring

-- bits of a name and its first reply

theorem chiAt (u j a b : ℕ) (ha : a = j+1) (hb : b = j+2) :
    chi (fun i => u.testBit i) j = xor (u.testBit j) (!(u.testBit a) && u.testBit b) := by
  subst ha hb
  rfl

theorem rvAt (d p u j a b : ℕ) (ha : a = j+1) (hb : b = j+2) :
    rv d p u j = rr (u.testBit j) (u.testBit a) (u.testBit b) (mixb d p j) (mixb d p a)
      (mixb d p b) := by
  subst ha hb
  rfl

theorem chiU {h u j : ℕ} (hj : j < h) :
    chi (fun i => u.testBit i) j = decide (j ∈ frs h u) := by
  simp [frs, hj]

theorem bitEq {h u j a b : ℕ} {z : Finset ℕ} (hz : frs h u = z) (hj : j < h) (ha : a = j+1)
    (hb : b = j+2) : u.testBit j = xor (decide (j ∈ z)) (!(u.testBit a) && u.testBit b) := by
  have e := chiU (u := u) hj
  rw [chiAt u j a b ha hb, hz] at e
  exact xsolve e

theorem step {u v j : ℕ} (hc : chi (fun i => u.testBit i) j = chi (fun i => v.testBit i) j)
    (h1 : u.testBit (j+1) = v.testBit (j+1)) (h2 : u.testBit (j+2) = v.testBit (j+2)) :
    u.testBit j = v.testBit j := by
  rw [chiAt u j (j+1) (j+2) rfl rfl, chiAt v j (j+1) (j+2) rfl rfl, h1, h2] at hc
  exact xcancel hc

theorem down (u v : ℕ) (n : ℕ)
    (hc : ∀ j < n, chi (fun i => u.testBit i) j = chi (fun i => v.testBit i) j)
    (h0 : u.testBit n = v.testBit n) (h1 : u.testBit (n+1) = v.testBit (n+1)) :
    ∀ j ≤ n+1, u.testBit j = v.testBit j := by
  induction n with
  | zero =>
    intro j hj
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · exact h0
    · exact h1
  | succ n ih =>
    have hn : u.testBit n = v.testBit n := step (hc n (by omega)) h0 h1
    intro j hj
    rcases (show j ≤ n + 1 ∨ j = n + 1 + 1 by omega) with hj' | rfl
    · exact ih (fun j hj => hc j (by omega)) hn h0 j hj'
    · exact h1

theorem tailInj {h u v : ℕ} (hu : u < 2^(h+2)) (hv : v < 2^(h+2)) (hf : frs h u = frs h v)
    (ht : tl h u = tl h v) : u = v := by
  have hc : ∀ j < h, chi (fun i => u.testBit i) j = chi (fun i => v.testBit i) j := by
    intro j hj
    rw [chiU hj, chiU hj, hf]
  have h0 : u.testBit h = v.testBit h := congrArg Prod.fst ht
  have h1 : u.testBit (h+1) = v.testBit (h+1) := congrArg Prod.snd ht
  have hd := down u v h hc h0 h1
  apply Nat.eq_of_testBit_eq
  intro j
  rcases Nat.lt_or_ge (h+1) j with hj | hj
  · have hp : 2^(h+2) ≤ 2^j := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hu hp), Nat.testBit_lt_two_pow (lt_of_lt_of_le hv hp)]
  · exact hd j hj

theorem surj (h : ℕ) : (Finset.range (2^(h+2))).image (fun u => (frs h u, tl h u)) =
    (Finset.range h).powerset ×ˢ (Finset.univ : Finset (Bool × Bool)) := by
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr
      ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), Finset.mem_univ _⟩
  · have inj : Set.InjOn (fun u => (frs h u, tl h u))
        ((Finset.range (2^(h+2)) : Finset ℕ) : Set ℕ) := by
      intro u hu v hv he
      exact tailInj (Finset.mem_range.mp (Finset.mem_coe.mp hu))
        (Finset.mem_range.mp (Finset.mem_coe.mp hv)) (congrArg Prod.fst he) (congrArg Prod.snd he)
    rw [Finset.card_image_of_injOn inj, Finset.card_product, Finset.card_powerset, Finset.card_range,
      Finset.card_range, Finset.card_univ, Fintype.card_prod, Fintype.card_bool]
    exact le_of_eq (by ring)

theorem fibSurj {h : ℕ} {z : Finset ℕ} (hz : z ∈ (Finset.range h).powerset) :
    ((Finset.range (2^(h+2))).filter (fun u => frs h u = z)).image (tl h) = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro τ
  have hm : (z, τ) ∈ (Finset.range (2^(h+2))).image (fun u => (frs h u, tl h u)) := by
    rw [surj h]
    exact Finset.mem_product.mpr ⟨hz, Finset.mem_univ _⟩
  obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hm
  exact Finset.mem_image.mpr
    ⟨u, Finset.mem_filter.mpr ⟨hu, congrArg Prod.fst he⟩, congrArg Prod.snd he⟩

theorem decomp (h d : ℕ) (pick : Finset ℕ → ℕ) (mask : Finset ℕ → Finset ℕ) :
    ((Finset.range (2^(h+2))).image (tr h d pick mask)).card =
      Finset.sum (Finset.range h).powerset (fun z =>
        (((Finset.range (2^(h+2))).filter (fun u => frs h u = z)).image (tr h d pick mask)).card) := by
  have H : Set.MapsTo Prod.fst
      (↑((Finset.range (2^(h+2))).image (tr h d pick mask)) : Set (Finset ℕ × Finset ℕ))
      (↑((Finset.range h).powerset) : Set (Finset ℕ)) := by
    intro p hp
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hp)
    exact Finset.mem_coe.mpr (Finset.mem_powerset.mpr (Finset.filter_subset _ _))
  rw [Finset.card_eq_sum_card_fiberwise H]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.filter_image] <;> rfl

theorem rdEq {d p u v : ℕ} {M : Finset ℕ} (h : rd d p u M = rd d p v M) {j : ℕ} (hj : j ∈ M) :
    rv d p u j = rv d p v j := by
  have e := Finset.ext_iff.mp h j
  simp only [rd, Finset.mem_filter] at e
  exact Bool.eq_iff_iff.mpr ⟨fun h1 => (e.mp ⟨hj, h1⟩).2, fun h1 => (e.mpr ⟨hj, h1⟩).2⟩

-- the upper bound for one first reply

theorem up4 (h d : ℕ) (pick : Finset ℕ → ℕ) (mask : Finset ℕ → Finset ℕ) (z : Finset ℕ) :
    (((Finset.range (2^(h+2))).filter (fun u => frs h u = z)).image (tr h d pick mask)).card ≤ 4 := by
  calc _ ≤ (((Finset.range (2^(h+2))).filter (fun u => frs h u = z)).image (tl h)).card := by
        apply cimg
        intro u hu v hv he
        have hu' := Finset.mem_filter.mp hu
        have hv' := Finset.mem_filter.mp hv
        rw [tailInj (Finset.mem_range.mp hu'.1) (Finset.mem_range.mp hv'.1) (hu'.2.trans hv'.2.symm) he]
    _ ≤ (Finset.univ : Finset (Bool × Bool)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = 4 := by rw [Finset.card_univ, Fintype.card_prod, Fintype.card_bool]

theorem bits11 {n u : ℕ} {z : Finset ℕ} (hfu : frs (n+4) u = z) (hz2 : n + 2 ∈ z) (hz3 : n + 3 ∈ z) :
    u.testBit (n+1) = decide (n+1 ∈ z) ∧ u.testBit (n+2) = true ∧
      u.testBit (n+3) = xor true (!(u.testBit (n+4)) && u.testBit (n+5)) := by
  have b3 := bitEq hfu (show n+3 < n+4 by omega) (show n+4 = n+3+1 by omega)
    (show n+5 = n+3+2 by omega)
  have b2 := bitEq hfu (show n+2 < n+4 by omega) (show n+3 = n+2+1 by omega)
    (show n+4 = n+2+2 by omega)
  have b1 := bitEq hfu (show n+1 < n+4 by omega) (show n+2 = n+1+1 by omega)
    (show n+3 = n+1+2 by omega)
  rw [decide_eq_true hz3] at b3
  rw [decide_eq_true hz2] at b2
  have b2' : u.testBit (n+2) = true := by
    rw [b2, b3]
    generalize u.testBit (n+4) = s
    generalize u.testBit (n+5) = t
    revert s t
    decide
  refine ⟨?_, b2', b3⟩
  rw [b1, b2']
  generalize decide (n+1 ∈ z) = c
  generalize u.testBit (n+3) = w
  revert c w
  decide

theorem up3 (n d : ℕ) (pick : Finset ℕ → ℕ) (mask : Finset ℕ → Finset ℕ) (z : Finset ℕ)
    (hz2 : n + 2 ∈ z) (hz3 : n + 3 ∈ z) (hm : mask z ⊆ Finset.range (n+4))
    (hA : n + 1 ∉ mask z ∨ n + 2 ∉ mask z) :
    (((Finset.range (2^(n+4+2))).filter (fun u => frs (n+4) u = z)).image
      (tr (n+4) d pick mask)).card ≤ 3 := by
  have common : ∀ u ∈ (Finset.range (2^(n+4+2))).filter (fun u => frs (n+4) u = z),
      ∀ v ∈ (Finset.range (2^(n+4+2))).filter (fun u => frs (n+4) u = z),
      ∀ j ≤ n+2, u.testBit j = v.testBit j := by
    intro u hu v hv
    have hfu := (Finset.mem_filter.mp hu).2
    have hfv := (Finset.mem_filter.mp hv).2
    obtain ⟨u1, u2, -⟩ := bits11 hfu hz2 hz3
    obtain ⟨v1, v2, -⟩ := bits11 hfv hz2 hz3
    have hc : ∀ j < n+1, chi (fun i => u.testBit i) j = chi (fun i => v.testBit i) j := by
      intro j hj
      rw [chiU (h := n+4) (show j < n+4 by omega), chiU (h := n+4) (show j < n+4 by omega), hfu, hfv]
    exact down u v (n+1) hc (u1.trans v1.symm) (u2.trans v2.symm)
  have claim2 : ∀ u ∈ (Finset.range (2^(n+4+2))).filter (fun u => frs (n+4) u = z),
      ∀ v ∈ (Finset.range (2^(n+4+2))).filter (fun u => frs (n+4) u = z),
      code d (pick z) (mask z) n u = code d (pick z) (mask z) n v →
      tr (n+4) d pick mask u = tr (n+4) d pick mask v := by
    intro u hu v hv he
    have hfu := (Finset.mem_filter.mp hu).2
    have hfv := (Finset.mem_filter.mp hv).2
    have hcm := common u hu v hv
    have key : ∀ j ∈ mask z, rv d (pick z) u j = rv d (pick z) v j := by
      intro j hj
      have hj4 : j < n + 4 := Finset.mem_range.mp (hm hj)
      rcases (show j ≤ n ∨ j = n+1 ∨ j = n+2 ∨ j = n+3 by omega) with hj' | rfl | rfl | rfl
      · rw [rvAt d (pick z) u j (j+1) (j+2) rfl rfl, rvAt d (pick z) v j (j+1) (j+2) rfl rfl,
          hcm j (by omega), hcm (j+1) (by omega), hcm (j+2) (by omega)]
      · have e1 : (decide (n+1 ∈ mask z) && rv d (pick z) u (n+1)) =
            (decide (n+1 ∈ mask z) && rv d (pick z) v (n+1)) := congrArg Prod.fst he
        rw [decide_eq_true hj, Bool.true_and, Bool.true_and] at e1
        exact e1
      · have e1 : (decide (n+2 ∈ mask z) && rv d (pick z) u (n+2)) =
            (decide (n+2 ∈ mask z) && rv d (pick z) v (n+2)) := congrArg (fun c => c.2.1) he
        rw [decide_eq_true hj, Bool.true_and, Bool.true_and] at e1
        exact e1
      · have e1 : (decide (n+3 ∈ mask z) && rv d (pick z) u (n+3)) =
            (decide (n+3 ∈ mask z) && rv d (pick z) v (n+3)) := congrArg (fun c => c.2.2) he
        rw [decide_eq_true hj, Bool.true_and, Bool.true_and] at e1
        exact e1
    unfold tr
    rw [hfu, hfv]
    refine Prod.ext rfl ?_
    show rd d (pick z) u (mask z) = rd d (pick z) v (mask z)
    unfold rd
    apply Finset.filter_congr
    intro j hj
    rw [key j hj]
  have claim1 : ∀ u ∈ (Finset.range (2^(n+4+2))).filter (fun u => frs (n+4) u = z),
      code d (pick z) (mask z) n u =
      Phi (decide (n+1 ∈ z)) (mixb d (pick z) (n+1)) (mixb d (pick z) (n+2))
        (mixb d (pick z) (n+3)) (mixb d (pick z) (n+4)) (mixb d (pick z) (n+5))
        (decide (n+1 ∈ mask z)) (decide (n+2 ∈ mask z)) (decide (n+3 ∈ mask z))
        (u.testBit (n+4)) (u.testBit (n+5)) := by
    intro u hu
    obtain ⟨b1, b2, b3⟩ := bits11 (Finset.mem_filter.mp hu).2 hz2 hz3
    unfold code Phi
    rw [rvAt d (pick z) u (n+1) (n+2) (n+3) rfl rfl, rvAt d (pick z) u (n+2) (n+3) (n+4) rfl rfl,
      rvAt d (pick z) u (n+3) (n+4) (n+5) rfl rfl, b1, b2, b3]
  have hA' : (decide (n+1 ∈ mask z) && decide (n+2 ∈ mask z)) = false := by
    rcases hA with h1 | h1 <;> simp [h1]
  calc _ ≤ (((Finset.range (2^(n+4+2))).filter (fun u => frs (n+4) u = z)).image
          (code d (pick z) (mask z) n)).card :=
        cimg _ (tr (n+4) d pick mask) (code d (pick z) (mask z) n) claim2
    _ ≤ ((Finset.univ : Finset (Bool × Bool)).image (fun q => Phi (decide (n+1 ∈ z))
          (mixb d (pick z) (n+1)) (mixb d (pick z) (n+2)) (mixb d (pick z) (n+3))
          (mixb d (pick z) (n+4)) (mixb d (pick z) (n+5)) (decide (n+1 ∈ mask z))
          (decide (n+2 ∈ mask z)) (decide (n+3 ∈ mask z)) q.1 q.2)).card := by
        apply Finset.card_le_card
        intro c hc
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hc
        rw [claim1 u hu]
        exact Finset.mem_image.mpr ⟨(u.testBit (n+4), u.testBit (n+5)), Finset.mem_univ _, rfl⟩
    _ ≤ 3 := coreU' _ _ _ _ _ _ _ _ _ hA'

-- realizing a mixed shift: flip raw taps from the top down

theorem flipBit (x i j : ℕ) : (x ^^^ 2^i).testBit j = xor (x.testBit j) (decide (i = j)) := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow]

theorem mixFlip (d x q i : ℕ) : mixb d (x ^^^ 2^q) i =
    xor (mixb d x i) (xor (decide (q = i)) (xor (decide (q = i+d)) (decide (q = i+2*d)))) := by
  unfold mixb
  rw [flipBit, flipBit, flipBit]
  generalize x.testBit i = a
  generalize x.testBit (i+d) = b
  generalize x.testBit (i+2*d) = c
  generalize decide (q = i) = e1
  generalize decide (q = i+d) = e2
  generalize decide (q = i+2*d) = e3
  revert a b c e1 e2 e3
  decide

theorem fwd (d H : ℕ) (hd : 0 < d) (τ : ℕ → Bool) :
    ∀ m, m ≤ H → ∃ x < 2^H, ∀ i, H - m ≤ i → i < H → mixb d x i = τ i := by
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨0, by positivity, fun i h1 h2 => absurd h2 (by omega)⟩
  | succ m ih =>
    intro hm
    obtain ⟨x, hx, hxt⟩ := ih (by omega)
    by_cases hb : mixb d x (H - (m+1)) = τ (H - (m+1))
    · refine ⟨x, hx, fun i h1 h2 => ?_⟩
      rcases (show i = H - (m+1) ∨ H - m ≤ i by omega) with rfl | h3
      · exact hb
      · exact hxt i h3 h2
    · refine ⟨x ^^^ 2^(H - (m+1)),
        Nat.xor_lt_two_pow hx (Nat.pow_lt_pow_right (by norm_num) (by omega)), fun i h1 h2 => ?_⟩
      rw [mixFlip]
      rcases (show i = H - (m+1) ∨ H - m ≤ i by omega) with rfl | h3
      · rw [decide_eq_true (show H - (m+1) = H - (m+1) from rfl),
          decide_eq_false (show H - (m+1) ≠ H - (m+1) + d by omega),
          decide_eq_false (show H - (m+1) ≠ H - (m+1) + 2*d by omega)]
        revert hb
        generalize mixb d x (H - (m+1)) = a
        generalize τ (H - (m+1)) = b
        revert a b
        decide
      · rw [decide_eq_false (show H - (m+1) ≠ i by omega),
          decide_eq_false (show H - (m+1) ≠ i + d by omega),
          decide_eq_false (show H - (m+1) ≠ i + 2*d by omega), hxt i h3 h2]
        generalize τ i = c
        revert c
        decide

-- the construction for one first reply

theorem low (n d x y : ℕ) (hx : ∀ i < n+4+2, mixb d x i = tx n i)
    (hy : ∀ i < n+4+2, mixb d y i = ty n i) (z : Finset ℕ) (hz : z ∈ (Finset.range (n+4)).powerset) :
    (if n+2 ∈ z ∧ n+3 ∈ z then 3 else 4) ≤
    (((Finset.range (2^(n+4+2))).filter (fun u => frs (n+4) u = z)).image
      (tr (n+4) d (fun z => if n+3 ∈ z then y else x) (fun _ => {n, n+2, n+3}))).card := by
  obtain ⟨x0, x1, x2, x3, x4, x5⟩ := txv n
  obtain ⟨y0, y1, y2, y3, y4, y5⟩ := tyv n
  have hb : (if n+2 ∈ z ∧ n+3 ∈ z then 3 else 4) =
      ((Finset.univ : Finset (Bool × Bool)).image
        (fun q => mg (decide (n+2 ∈ z) && decide (n+3 ∈ z)) q.1 q.2)).card := by
    rw [mgcard]
    by_cases h2 : n + 2 ∈ z <;> by_cases h3 : n + 3 ∈ z <;> simp [h2, h3]
  rw [hb]
  calc ((Finset.univ : Finset (Bool × Bool)).image
        (fun q => mg (decide (n+2 ∈ z) && decide (n+3 ∈ z)) q.1 q.2)).card
      = (((Finset.range (2^(n+4+2))).filter (fun u => frs (n+4) u = z)).image
          (fun u => mg (decide (n+2 ∈ z) && decide (n+3 ∈ z)) (u.testBit (n+4))
            (u.testBit (n+5)))).card := by
        rw [← fibSurj hz, Finset.image_image] <;> rfl
    _ ≤ _ := by
        apply cimg
        intro u hu v hv he
        have hfu := (Finset.mem_filter.mp hu).2
        have hfv := (Finset.mem_filter.mp hv).2
        have hrd : rd d (if n+3 ∈ z then y else x) u {n, n+2, n+3} =
            rd d (if n+3 ∈ z then y else x) v {n, n+2, n+3} := by
          have e2 := congrArg Prod.snd he
          simp only [tr, hfu, hfv] at e2
          exact e2
        have r0 := rdEq hrd (show n ∈ ({n, n+2, n+3} : Finset ℕ) by simp)
        have r2 := rdEq hrd (show n+2 ∈ ({n, n+2, n+3} : Finset ℕ) by simp)
        have r3 := rdEq hrd (show n+3 ∈ ({n, n+2, n+3} : Finset ℕ) by simp)
        rw [rvAt _ _ u n (n+1) (n+2) rfl rfl, rvAt _ _ v n (n+1) (n+2) rfl rfl] at r0
        rw [rvAt _ _ u (n+2) (n+3) (n+4) rfl rfl, rvAt _ _ v (n+2) (n+3) (n+4) rfl rfl] at r2
        rw [rvAt _ _ u (n+3) (n+4) (n+5) rfl rfl, rvAt _ _ v (n+3) (n+4) (n+5) rfl rfl] at r3
        have u3 := bitEq hfu (show n+3 < n+4 by omega) (show n+4 = n+3+1 by omega)
          (show n+5 = n+3+2 by omega)
        have u2 := bitEq hfu (show n+2 < n+4 by omega) (show n+3 = n+2+1 by omega)
          (show n+4 = n+2+2 by omega)
        have u1 := bitEq hfu (show n+1 < n+4 by omega) (show n+2 = n+1+1 by omega)
          (show n+3 = n+1+2 by omega)
        have u0 := bitEq hfu (show n < n+4 by omega) (show n+1 = n+1 by omega)
          (show n+2 = n+2 by omega)
        have v3 := bitEq hfv (show n+3 < n+4 by omega) (show n+4 = n+3+1 by omega)
          (show n+5 = n+3+2 by omega)
        have v2 := bitEq hfv (show n+2 < n+4 by omega) (show n+3 = n+2+1 by omega)
          (show n+4 = n+2+2 by omega)
        have v1 := bitEq hfv (show n+1 < n+4 by omega) (show n+2 = n+1+1 by omega)
          (show n+3 = n+1+2 by omega)
        have v0 := bitEq hfv (show n < n+4 by omega) (show n+1 = n+1 by omega)
          (show n+2 = n+2 by omega)
        show mg (decide (n+2 ∈ z) && decide (n+3 ∈ z)) (u.testBit (n+4)) (u.testBit (n+5)) =
          mg (decide (n+2 ∈ z) && decide (n+3 ∈ z)) (v.testBit (n+4)) (v.testBit (n+5))
        by_cases h3 : n + 3 ∈ z
        · rw [if_pos h3] at r0 r2 r3
          rw [decide_eq_true h3] at u3 v3 ⊢
          rw [Bool.and_true]
          rw [hy n (by omega), y0, hy (n+1) (by omega), y1, hy (n+2) (by omega), y2] at r0
          rw [hy (n+2) (by omega), y2, hy (n+3) (by omega), y3, hy (n+4) (by omega), y4] at r2
          rw [hy (n+3) (by omega), y3, hy (n+4) (by omega), y4, hy (n+5) (by omega), y5] at r3
          exact coreLy _ _ _ _ _ _ _ _ u3 _ u2 _ u1 _ u0 _ v3 _ v2 _ v1 _ v0 r0 r2 r3
        · rw [if_neg h3] at r0 r2 r3
          rw [decide_eq_false h3] at u3 v3 ⊢
          rw [Bool.and_false]
          rw [hx n (by omega), x0, hx (n+1) (by omega), x1, hx (n+2) (by omega), x2] at r0
          rw [hx (n+2) (by omega), x2, hx (n+3) (by omega), x3, hx (n+4) (by omega), x4] at r2
          rw [hx (n+3) (by omega), x3, hx (n+4) (by omega), x4, hx (n+5) (by omega), x5] at r3
          obtain ⟨e1, e2⟩ := coreLx _ _ _ _ _ _ _ _ u3 _ u2 _ u1 _ u0 _ v3 _ v2 _ v1 _ v0 r0 r2 r3
          rw [e1, e2]

-- assembly

theorem main (h d : ℕ) (hh : 4 ≤ h) (hd : 0 < d) :
    (∃ x y : ℕ, x < 2^(h+2+2*d) ∧ y < 2^(h+2+2*d) ∧
      ((Finset.range (2^(h+2))).image (tr h d (fun z => if h-1 ∈ z then y else x)
        (fun _ => {h-4, h-2, h-1}))).card = 15 * 2^(h-2)) ∧
    ∀ (pick : Finset ℕ → ℕ) (mask : Finset ℕ → Finset ℕ),
      (∀ z ∈ (Finset.range (2^(h+2))).image (frs h), pick z < 2^(h+2+2*d) ∧
        mask z ⊆ Finset.range h ∧ (h-3 ∉ mask z ∨ h-2 ∉ mask z)) →
      ((Finset.range (2^(h+2))).image (tr h d pick mask)).card ≤ 15 * 2^(h-2) := by
  obtain ⟨n, rfl⟩ : ∃ n, h = n + 4 := ⟨h - 4, by omega⟩
  rw [show n + 4 - 1 = n + 3 by omega, show n + 4 - 2 = n + 2 by omega,
    show n + 4 - 3 = n + 1 by omega, show n + 4 - 4 = n by omega]
  have upper : ∀ (pick : Finset ℕ → ℕ) (mask : Finset ℕ → Finset ℕ),
      (∀ z ∈ (Finset.range (2^(n+4+2))).image (frs (n+4)), mask z ⊆ Finset.range (n+4) ∧
        (n+1 ∉ mask z ∨ n+2 ∉ mask z)) →
      ((Finset.range (2^(n+4+2))).image (tr (n+4) d pick mask)).card ≤ 15 * 2^(n+2) := by
    intro pick mask hpm
    rw [decomp, ← sum15 n]
    apply Finset.sum_le_sum
    intro z _
    by_cases h11 : n + 2 ∈ z ∧ n + 3 ∈ z
    · rw [if_pos h11]
      by_cases hne : ((Finset.range (2^(n+4+2))).filter (fun u => frs (n+4) u = z)).Nonempty
      · obtain ⟨u, hu⟩ := hne
        have hu' := Finset.mem_filter.mp hu
        obtain ⟨hm, hA⟩ := hpm z (Finset.mem_image.mpr ⟨u, hu'.1, hu'.2⟩)
        exact up3 n d pick mask z h11.1 h11.2 hm hA
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
        simp
    · rw [if_neg h11]
      exact up4 (n+4) d pick mask z
  refine ⟨?_, fun pick mask hpm => upper pick mask (fun z hz => ⟨(hpm z hz).2.1, (hpm z hz).2.2⟩)⟩
  obtain ⟨x, hx, hxt⟩ := fwd d (n+4+2) hd (tx n) (n+4+2) le_rfl
  obtain ⟨y, hy, hyt⟩ := fwd d (n+4+2) hd (ty n) (n+4+2) le_rfl
  have hlim : 2^(n+4+2) ≤ 2^(n+4+2+2*d) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨x, y, lt_of_lt_of_le hx hlim, lt_of_lt_of_le hy hlim, le_antisymm ?_ ?_⟩
  · apply upper
    intro z _
    refine ⟨?_, Or.inl ?_⟩
    · intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rw [Finset.mem_range]
      omega
    · intro hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      omega
  · rw [decomp, ← sum15 n]
    apply Finset.sum_le_sum
    intro z hz
    exact low n d x y (fun i hi => hxt i (by omega) hi) (fun i hi => hyt i (by omega) hi) z hz

end PEqualNP.Outside.L_meta_38164_aux

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
  intro h d hh hd
  exact PEqualNP.Outside.L_meta_38164_aux.main h d hh hd
