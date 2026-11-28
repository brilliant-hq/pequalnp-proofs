import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39006

def num (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | N + 1 => num f N + (if f N then 2 ^ N else 0)

theorem num_lt (f : ℕ → Bool) (N : ℕ) : num f N < 2 ^ N := by
  induction N with
  | zero => simp [num]
  | succ N ih => simp only [num, pow_succ]; split <;> omega

theorem num_testBit (f : ℕ → Bool) (N i : ℕ) :
    (num f N).testBit i = (decide (i < N) && f i) := by
  induction N generalizing i with
  | zero => simp [num]
  | succ N ih =>
    simp only [num]
    have hl := num_lt f N
    by_cases hfN : f N
    · simp only [hfN, if_true]
      rw [Nat.add_comm]
      rcases lt_trichotomy i N with h | h | h
      · rw [Nat.testBit_two_pow_add_gt h, ih]; simp [h, show i < N + 1 by omega]
      · subst h; rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hl]; simp [hfN]
      · rw [Nat.testBit_lt_two_pow]
        · simp; omega
        · calc 2 ^ N + num f N < 2 ^ N + 2 ^ N := by omega
            _ = 2 ^ (N + 1) := by rw [pow_succ]; ring
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) h
    · simp only [hfN, Bool.false_eq_true, if_false, Nat.add_zero, ih]
      by_cases h : i = N
      · subst h; simp [hfN]
      · by_cases h2 : i < N
        · simp [h2, show i < N + 1 by omega]
        · simp [h2, show ¬ i < N + 1 by omega]

def chiB (bits : ℕ → Bool) (j : ℕ) : Bool := xor (bits j) (!(bits (j+1)) && bits (j+2))

def stpS (zs : ℕ → Bool) (a b : Bool) : ℕ → Bool × Bool
  | 0 => (a, b)
  | m + 1 => match stpS zs a b m with
    | (p, q) => (xor (zs m) (!p && q), p)

def W (zs : ℕ → Bool) (a b : Bool) : ℕ → Bool
  | 0 => b
  | m + 1 => (stpS zs a b m).1

theorem stpS_snd (zs : ℕ → Bool) (a b : Bool) (m : ℕ) : (stpS zs a b m).2 = W zs a b m := by
  cases m <;> rfl

theorem stpS_succ (zs : ℕ → Bool) (a b : Bool) (m : ℕ) :
    stpS zs a b (m + 1) = (xor (zs m) (!(stpS zs a b m).1 && (stpS zs a b m).2),
      (stpS zs a b m).1) := by
  show (match stpS zs a b m with | (p, q) => (xor (zs m) (!p && q), p)) = _
  rcases stpS zs a b m with ⟨p, q⟩
  rfl

theorem W_succ_succ (zs : ℕ → Bool) (a b : Bool) (m : ℕ) :
    W zs a b (m + 2) = xor (zs m) (!(W zs a b (m + 1)) && W zs a b m) := by
  show (stpS zs a b (m+1)).1 = _
  rw [stpS_succ]
  simp only [W, stpS_snd]

def fiberS (h : ℕ) (z : Fin h → Bool) : Set ℕ :=
  {u | u < 2^(h+2) ∧ ∀ j : Fin h, chiB (fun i => u.testBit i) j = z j}

def zsOf (h : ℕ) (z : Fin h → Bool) (m : ℕ) : Bool := if hm : m < h then z ⟨h - 1 - m, by omega⟩ else false

theorem fiber_bits {h : ℕ} {z : Fin h → Bool} {u : ℕ} (hu : u ∈ fiberS h z) :
    ∀ m, m ≤ h + 1 → u.testBit (h + 1 - m) = W (zsOf h z) (u.testBit h) (u.testBit (h+1)) m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    match m, ih, hm with
    | 0, _, _ => simp [W]
    | 1, _, _ => simp [W, stpS]
    | m + 2, ih, hm =>
      rw [W_succ_succ, ← ih (m+1) (by omega) (by omega), ← ih m (by omega) (by omega)]
      have hc := hu.2 ⟨h - 1 - m, by omega⟩
      simp only [chiB] at hc
      have e1 : h - 1 - m + 1 = h + 1 - (m + 1) := by omega
      have e2 : h - 1 - m + 2 = h + 1 - m := by omega
      have e0 : h + 1 - (m + 2) = h - 1 - m := by omega
      rw [e1, e2] at hc
      have hz : zsOf h z m = z ⟨h - 1 - m, by omega⟩ := by simp [zsOf, show m < h by omega]
      rw [e0, hz, ← hc]
      simp [Bool.xor_assoc]

def tapD (k start x j back : ℕ) : Bool := x.testBit ((start+j+k-back) % k)

def pulseD (k start : ℕ) (col : Bool) (x j : ℕ) : Bool :=
  if col then xor (tapD k start x j 1) (xor (tapD k start x j 3) (tapD k start x j 5))
  else xor (tapD k start x j 0) (xor (tapD k start x j 1) (tapD k start x j 2))

def tailD (h k start : ℕ) (col : Bool) (x len u : ℕ) : Finset ℕ :=
  (Finset.range len).filter (fun j =>
    chiB (fun i => xor (u.testBit i) (pulseD k start col x i)) (h-len+j))

def okD (h k start x : ℕ) (r c : Fin h → Bool) : Prop :=
  Set.InjOn (tailD h k start false x 5) (fiberS h r) ∧
    Set.InjOn (tailD h k start true x 4) (fiberS h c)

def PA (col : Bool) (kw : ℕ → Bool) (m : ℕ) : Bool :=
  if col then xor (kw (9-m)) (xor (kw (7-m)) (kw (5-m)))
  else xor (kw (10-m)) (xor (kw (9-m)) (kw (8-m)))

def yK (h k start x idx : ℕ) : Bool := x.testBit ((start+h+idx+k-9) % k)

theorem pulse_bridge (h k start x : ℕ) (hk : 11 ≤ k) (col : Bool) (m : ℕ) (hm : m ≤ h+1)
    (hc : col = true → m ≤ 5) (h6 : m ≤ 6) :
    pulseD k start col x (h+1-m) = PA col (yK h k start x) m := by
  cases col
  · simp only [pulseD, PA, tapD, yK, Bool.false_eq_true, ↓reduceIte]
    have e0 : start + (h+1-m) + k - 0 = start+h+(10-m)+k-9 := by omega
    have e1 : start + (h+1-m) + k - 1 = start+h+(9-m)+k-9 := by omega
    have e2 : start + (h+1-m) + k - 2 = start+h+(8-m)+k-9 := by omega
    rw [e0, e1, e2]
  · have hm5 := hc rfl
    simp only [pulseD, PA, tapD, yK, ↓reduceIte]
    have e1 : start + (h+1-m) + k - 1 = start+h+(9-m)+k-9 := by omega
    have e3 : start + (h+1-m) + k - 3 = start+h+(7-m)+k-9 := by omega
    have e5 : start + (h+1-m) + k - 5 = start+h+(5-m)+k-9 := by omega
    rw [e1, e3, e5]

def Vb (pa zs : ℕ → Bool) (a b : Bool) (m : ℕ) : Bool := xor (W zs a b m) (pa m)

def tv (pa zs : ℕ → Bool) (a b : Bool) (len j : ℕ) : Bool :=
  xor (Vb pa zs a b (len+1-j)) (!(Vb pa zs a b (len-j)) && Vb pa zs a b (len-j-1))

theorem chi_bridge (h k start x : ℕ) (hk : 11 ≤ k) (col : Bool) (len : ℕ) (hl5 : len ≤ 5)
    (hlh : len ≤ h) (hlc : col = true → len ≤ 4) (z : Fin h → Bool) (u : ℕ)
    (hu : u ∈ fiberS h z) (j : ℕ) (hj : j < len) :
    chiB (fun i => xor (u.testBit i) (pulseD k start col x i)) (h-len+j)
      = tv (PA col (yK h k start x)) (zsOf h z) (u.testBit h) (u.testBit (h+1)) len j := by
  have g : ∀ m, m ≤ len+1 → xor (u.testBit (h+1-m)) (pulseD k start col x (h+1-m))
      = Vb (PA col (yK h k start x)) (zsOf h z) (u.testBit h) (u.testBit (h+1)) m := by
    intro m hm
    rw [fiber_bits hu m (by omega), pulse_bridge h k start x hk col m (by omega)
      (fun hc => by have := hlc hc; omega) (by omega)]
    rfl
  have h0 : xor (u.testBit (h-len+j)) (pulseD k start col x (h-len+j))
      = Vb (PA col (yK h k start x)) (zsOf h z) (u.testBit h) (u.testBit (h+1)) (len+1-j) := by
    have := g (len+1-j) (by omega)
    rwa [show h+1-(len+1-j) = h-len+j by omega] at this
  have h1 : xor (u.testBit (h-len+j+1)) (pulseD k start col x (h-len+j+1))
      = Vb (PA col (yK h k start x)) (zsOf h z) (u.testBit h) (u.testBit (h+1)) (len-j) := by
    have := g (len-j) (by omega)
    rwa [show h+1-(len-j) = h-len+j+1 by omega] at this
  have h2 : xor (u.testBit (h-len+j+2)) (pulseD k start col x (h-len+j+2))
      = Vb (PA col (yK h k start x)) (zsOf h z) (u.testBit h) (u.testBit (h+1)) (len-j-1) := by
    have := g (len-j-1) (by omega)
    rwa [show h+1-(len-j-1) = h-len+j+2 by omega] at this
  simp only [chiB, tv, h0, h1, h2]

theorem mem_tailD_iff (h k start x : ℕ) (hk : 11 ≤ k) (col : Bool) (len : ℕ) (hl5 : len ≤ 5)
    (hlh : len ≤ h) (hlc : col = true → len ≤ 4) (z : Fin h → Bool) (u : ℕ)
    (hu : u ∈ fiberS h z) (j : ℕ) :
    j ∈ tailD h k start col x len u ↔ j < len ∧
      tv (PA col (yK h k start x)) (zsOf h z) (u.testBit h) (u.testBit (h+1)) len j = true := by
  unfold tailD
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hj, hc⟩
    refine ⟨hj, ?_⟩
    rw [← chi_bridge h k start x hk col len hl5 hlh hlc z u hu j hj]; exact hc
  · rintro ⟨hj, hc⟩
    refine ⟨hj, ?_⟩
    rw [chi_bridge h k start x hk col len hl5 hlh hlc z u hu j hj]; exact hc

theorem tailD_eq_iff (h k start x : ℕ) (hk : 11 ≤ k) (col : Bool) (len : ℕ) (hl5 : len ≤ 5)
    (hlh : len ≤ h) (hlc : col = true → len ≤ 4) (z : Fin h → Bool) (u u' : ℕ)
    (hu : u ∈ fiberS h z) (hu' : u' ∈ fiberS h z) :
    tailD h k start col x len u = tailD h k start col x len u' ↔ ∀ j < len,
      tv (PA col (yK h k start x)) (zsOf h z) (u.testBit h) (u.testBit (h+1)) len j
      = tv (PA col (yK h k start x)) (zsOf h z) (u'.testBit h) (u'.testBit (h+1)) len j := by
  constructor
  · intro heq j hj
    have h1 := mem_tailD_iff h k start x hk col len hl5 hlh hlc z u hu j
    have h2 := mem_tailD_iff h k start x hk col len hl5 hlh hlc z u' hu' j
    rw [heq] at h1
    have h3 := h1.symm.trans h2
    simp only [hj, true_and] at h3
    cases hA : tv (PA col (yK h k start x)) (zsOf h z) (u.testBit h) (u.testBit (h+1)) len j <;>
      cases hB : tv (PA col (yK h k start x)) (zsOf h z) (u'.testBit h) (u'.testBit (h+1)) len j <;>
      simp_all
  · intro H
    ext j
    rw [mem_tailD_iff h k start x hk col len hl5 hlh hlc z u hu j,
      mem_tailD_iff h k start x hk col len hl5 hlh hlc z u' hu' j]
    constructor
    · rintro ⟨hj, hc⟩; exact ⟨hj, by rw [← H j hj]; exact hc⟩
    · rintro ⟨hj, hc⟩; exact ⟨hj, by rw [H j hj]; exact hc⟩

theorem fiber_ext {h : ℕ} {z : Fin h → Bool} {u u' : ℕ} (hu : u ∈ fiberS h z)
    (hu' : u' ∈ fiberS h z) (ha : u.testBit h = u'.testBit h)
    (hb : u.testBit (h+1) = u'.testBit (h+1)) : u = u' := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i ≤ h + 1
  · have e : i = h + 1 - (h + 1 - i) := by omega
    have h1 := fiber_bits hu (h+1-i) (by omega)
    have h2 := fiber_bits hu' (h+1-i) (by omega)
    rw [← e] at h1 h2
    rw [h1, h2, ha, hb]
  · rw [Nat.testBit_lt_two_pow, Nat.testBit_lt_two_pow]
    · calc u' < 2 ^ (h+2) := hu'.1
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    · calc u < 2 ^ (h+2) := hu.1
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem exists_fiber (h : ℕ) (z : Fin h → Bool) (a b : Bool) :
    ∃ u ∈ fiberS h z, u.testBit h = a ∧ u.testBit (h+1) = b := by
  set u := num (fun i => W (zsOf h z) a b (h+1-i)) (h+2) with hu
  have hbit : ∀ i, i ≤ h + 1 → u.testBit i = W (zsOf h z) a b (h+1-i) := by
    intro i hi
    rw [hu, num_testBit]
    simp [show i < h + 2 by omega]
  refine ⟨u, ⟨num_lt _ _, ?_⟩, ?_, ?_⟩
  · intro j
    have hj := j.2
    have hm : h - 1 - j.val + 2 = h + 1 - j.val := by omega
    have hm1 : h - 1 - j.val + 1 = h + 1 - (j.val + 1) := by omega
    have hm0 : h - 1 - j.val = h + 1 - (j.val + 2) := by omega
    have hw := W_succ_succ (zsOf h z) a b (h - 1 - j.val)
    rw [hm, hm1] at hw
    have hz : zsOf h z (h - 1 - j.val) = z j := by
      simp only [zsOf, show h - 1 - j.val < h by omega, dite_true]
      congr 1; apply Fin.ext; simp; omega
    rw [hz] at hw
    simp only [chiB]
    rw [hbit j.val (by omega), hbit (j.val+1) (by omega), hbit (j.val+2) (by omega), hw, ← hm0]
    simp [Bool.xor_assoc]
  · rw [hbit h (by omega)]; simp [W, stpS]
  · rw [hbit (h+1) (by omega)]; simp [W]

def zsP (top p m : ℕ) : Bool := p.testBit (top - m)

def tn (pa zs : ℕ → Bool) (a b : Bool) (len : ℕ) : ℕ := num (fun j => tv pa zs a b len j) len

def dist4 (f : Bool → Bool → ℕ) : Bool :=
  f false false != f false true && f false false != f true false &&
  f false false != f true true && f false true != f true false &&
  f false true != f true true && f true false != f true true

def PhiG (len pv p : ℕ) : Bool :=
  dist4 fun a b => tn (fun m => pv.testBit m) (zsP (len-1) p) a b len

def PhiR (pv p : ℕ) : Bool := dist4 fun a b => tn (fun m => pv.testBit m) (zsP 4 p) a b 5
def PhiC (pv q : ℕ) : Bool := dist4 fun a b => tn (fun m => pv.testBit m) (zsP 3 q) a b 4

theorem PhiR_eq (pv p : ℕ) : PhiR pv p = PhiG 5 pv p := rfl
theorem PhiC_eq (pv p : ℕ) : PhiC pv p = PhiG 4 pv p := rfl

def tbl (r1 r3 c1 c2 : Bool) : Fin 3 :=
  if r1 then (if c1 then 0 else if c2 then 1 else 0)
  else if r3 then (if c1 then 0 else if c2 then 2 else 0)
  else (if c1 then 2 else 1)

def keyY : Fin 3 → ℕ := ![144, 152, 194]

def rowPV (y : ℕ) : ℕ := num (PA false fun i => y.testBit i) 7
def colPV (y : ℕ) : ℕ := num (PA true fun i => y.testBit i) 6

theorem dist4_spec (f : Bool → Bool → ℕ) :
    dist4 f = true ↔ ∀ a b a' b' : Bool, f a b = f a' b' → a = a' ∧ b = b' := by
  constructor
  · intro h a b a' b' hf
    unfold dist4 at h
    cases a <;> cases b <;> cases a' <;> cases b' <;> simp_all
  · intro H
    unfold dist4
    have h1 := H false false false true
    have h2 := H false false true false
    have h3 := H false false true true
    have h4 := H false true true false
    have h5 := H false true true true
    have h6 := H true false true true
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> intro he
    · simpa using h1 he
    · simpa using h2 he
    · simpa using h3 he
    · simpa using h4 he
    · simpa using h5 he
    · simpa using h6 he

theorem num_eq_iff (f g : ℕ → Bool) (N : ℕ) :
    num f N = num g N ↔ ∀ j < N, f j = g j := by
  constructor
  · intro h j hj
    have := congrArg (fun u => u.testBit j) h
    simpa [num_testBit, hj] using this
  · intro H
    apply Nat.eq_of_testBit_eq
    intro i
    rw [num_testBit, num_testBit]
    by_cases hi : i < N
    · simp [hi, H i hi]
    · simp [hi]

theorem W_congr (zs zs' : ℕ → Bool) (a b : Bool) :
    ∀ m, (∀ m', m' + 2 ≤ m → zs m' = zs' m') → W zs a b m = W zs' a b m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro H
    match m, ih, H with
    | 0, _, _ => rfl
    | 1, _, _ => rfl
    | m + 2, ih, H =>
      rw [W_succ_succ, W_succ_succ, ih (m+1) (by omega) (fun m' hm' => H m' (by omega)),
        ih m (by omega) (fun m' hm' => H m' (by omega)), H m (by omega)]

theorem tv_zs_congr (pa zs zs' : ℕ → Bool) (a b : Bool) (len j : ℕ)
    (H : ∀ m < len, zs m = zs' m) : tv pa zs a b len j = tv pa zs' a b len j := by
  have hW : ∀ m, m ≤ len + 1 → W zs a b m = W zs' a b m := fun m hm =>
    W_congr zs zs' a b m (fun m' hm' => H m' (by omega))
  simp only [tv, Vb]
  rw [hW (len+1-j) (by omega), hW (len-j) (by omega), hW (len-j-1) (by omega)]

theorem tv_pa_congr (pa pa' zs : ℕ → Bool) (a b : Bool) (len j : ℕ)
    (H : ∀ m ≤ len + 1, pa m = pa' m) : tv pa zs a b len j = tv pa' zs a b len j := by
  simp only [tv, Vb]
  rw [H (len+1-j) (by omega), H (len-j) (by omega), H (len-j-1) (by omega)]

def pOf (L h : ℕ) (z : Fin h → Bool) : ℕ :=
  num (fun i => if hi : h - L + i < h then z ⟨h - L + i, hi⟩ else false) L

theorem zs_pOf (L h : ℕ) (hL : L ≤ h) (z : Fin h → Bool) :
    ∀ m < L, zsOf h z m = zsP (L-1) (pOf L h z) m := by
  intro m hm
  simp only [zsP, pOf, num_testBit]
  have h1 : L - 1 - m < L := by omega
  have h2 : h - L + (L - 1 - m) < h := by omega
  have h3 : m < h := by omega
  simp only [zsOf, h1, h2, h3, decide_true, Bool.true_and, dite_true]
  congr 1
  apply Fin.ext
  simp only
  omega

theorem exists_z_pOf (L h : ℕ) (hL : L ≤ h) (p : ℕ) (hp : p < 2 ^ L) :
    ∃ z : Fin h → Bool, pOf L h z = p := by
  refine ⟨fun i => p.testBit (i.val + L - h), ?_⟩
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [pOf, num_testBit]
  by_cases hi : i < L
  · have h2 : h - L + i < h := by omega
    simp only [hi, h2, decide_true, Bool.true_and, dite_true]
    congr 1
    omega
  · simp only [hi, decide_false, Bool.false_and]
    symm
    apply Nat.testBit_lt_two_pow
    calc p < 2 ^ L := hp
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)

def pvOf (h k start : ℕ) (col : Bool) (x L : ℕ) : ℕ := num (PA col (yK h k start x)) (L + 2)

theorem tv_conv (h k start : ℕ) (col : Bool) (x L : ℕ) (hL : L ≤ h) (z : Fin h → Bool)
    (a b : Bool) (j : ℕ) :
    tv (PA col (yK h k start x)) (zsOf h z) a b L j =
      tv (fun m => (pvOf h k start col x L).testBit m) (zsP (L-1) (pOf L h z)) a b L j := by
  rw [tv_zs_congr _ (zsOf h z) (zsP (L-1) (pOf L h z)) a b L j (zs_pOf L h hL z)]
  apply tv_pa_congr
  intro m hm
  simp [pvOf, num_testBit, show m < L + 2 by omega]

theorem injOn_of_phi (h k start : ℕ) (hk : 11 ≤ k) (col : Bool) (L : ℕ) (hl5 : L ≤ 5)
    (hlh : L ≤ h) (hlc : col = true → L ≤ 4) (x : ℕ) (z : Fin h → Bool)
    (hphi : PhiG L (pvOf h k start col x L) (pOf L h z) = true) :
    Set.InjOn (tailD h k start col x L) (fiberS h z) := by
  intro u hu u' hu' heq
  rw [tailD_eq_iff h k start x hk col L hl5 hlh hlc z u u' hu hu'] at heq
  unfold PhiG at hphi
  rw [dist4_spec] at hphi
  have := hphi (u.testBit h) (u.testBit (h+1)) (u'.testBit h) (u'.testBit (h+1)) (by
    unfold tn
    rw [num_eq_iff]
    intro j hj
    rw [← tv_conv h k start col x L hlh z, ← tv_conv h k start col x L hlh z]
    exact heq j hj)
  exact fiber_ext hu hu' this.1 this.2

theorem not_injOn_of_phi (h k start : ℕ) (hk : 11 ≤ k) (col : Bool) (L : ℕ) (hl5 : L ≤ 5)
    (hlh : L ≤ h) (hlc : col = true → L ≤ 4) (x p : ℕ) (hp : p < 2 ^ L)
    (hphi : PhiG L (pvOf h k start col x L) p = false) :
    ∃ z : Fin h → Bool, ¬ Set.InjOn (tailD h k start col x L) (fiberS h z) := by
  obtain ⟨z, hz⟩ := exists_z_pOf L h hlh p hp
  refine ⟨z, ?_⟩
  intro hinj
  rw [← hz] at hphi
  unfold PhiG at hphi
  have hn : ¬ (∀ a b a' b' : Bool, (fun a b => tn (fun m => (pvOf h k start col x L).testBit m)
      (zsP (L-1) (pOf L h z)) a b L) a b = (fun a b => tn (fun m => (pvOf h k start col x L).testBit m)
      (zsP (L-1) (pOf L h z)) a b L) a' b' → a = a' ∧ b = b') := by
    rw [← dist4_spec]; simp [hphi]
  simp only [not_forall] at hn
  obtain ⟨a, b, a', b', heq, hne⟩ := hn
  have hne' : ¬ (a = a' ∧ b = b') := hne
  simp only [tn] at heq
  rw [num_eq_iff] at heq
  obtain ⟨u, hu, hua, hub⟩ := exists_fiber h z a b
  obtain ⟨u', hu', hua', hub'⟩ := exists_fiber h z a' b'
  have h1 : tailD h k start col x L u = tailD h k start col x L u' := by
    rw [tailD_eq_iff h k start x hk col L hl5 hlh hlc z u u' hu hu', hua, hub, hua', hub']
    intro j hj
    rw [tv_conv h k start col x L hlh z, tv_conv h k start col x L hlh z]
    exact heq j hj
  have := hinj hu hu' h1
  subst this
  apply hne'
  rw [← hua, ← hua', ← hub, ← hub']
  exact ⟨rfl, rfl⟩

theorem fin_tableB : ((List.range 32).all fun p => (List.range 16).all fun q =>
    PhiR (rowPV (keyY (tbl (p.testBit 4) (p.testBit 2) (q.testBit 3) (q.testBit 2)))) p &&
    PhiC (colPV (keyY (tbl (p.testBit 4) (p.testBit 2) (q.testBit 3) (q.testBit 2)))) q) = true := by
  decide +kernel

theorem fin_rejRB : ((List.range 128).all fun v => (List.range 32).any fun p => !PhiR v p) = true := by
  decide +kernel

theorem fin_rejCB : ((List.range 64).all fun v => (List.range 16).any fun q => !PhiC v q) = true := by
  decide +kernel

theorem fin_table_spec : ∀ p < 32, ∀ q < 16,
    PhiR (rowPV (keyY (tbl (p.testBit 4) (p.testBit 2) (q.testBit 3) (q.testBit 2)))) p = true ∧
    PhiC (colPV (keyY (tbl (p.testBit 4) (p.testBit 2) (q.testBit 3) (q.testBit 2)))) q = true := by
  intro p hp q hq
  have h1 := List.all_eq_true.1 fin_tableB p (List.mem_range.2 hp)
  have h2 := List.all_eq_true.1 h1 q (List.mem_range.2 hq)
  exact Bool.and_eq_true_iff.1 h2

theorem row_rej (h k start : ℕ) (hk : 11 ≤ k) (h5 : 5 ≤ h) (x : ℕ) :
    ∃ z : Fin h → Bool, ¬ Set.InjOn (tailD h k start false x 5) (fiberS h z) := by
  have hv : pvOf h k start false x 5 < 128 := num_lt _ _
  have h1 := List.any_eq_true.1 (List.all_eq_true.1 fin_rejRB _ (List.mem_range.2 hv))
  obtain ⟨p, hp, hp2⟩ := h1
  have hp3 := List.mem_range.1 hp
  have hf : PhiR (pvOf h k start false x 5) p = false := by simpa using hp2
  exact not_injOn_of_phi h k start hk false 5 (by norm_num) h5 (by simp) x p (by omega) hf

theorem col_rej (h k start : ℕ) (hk : 11 ≤ k) (h5 : 5 ≤ h) (x : ℕ) :
    ∃ z : Fin h → Bool, ¬ Set.InjOn (tailD h k start true x 4) (fiberS h z) := by
  have hv : pvOf h k start true x 4 < 64 := num_lt _ _
  have h1 := List.any_eq_true.1 (List.all_eq_true.1 fin_rejCB _ (List.mem_range.2 hv))
  obtain ⟨p, hp, hp2⟩ := h1
  have hp3 := List.mem_range.1 hp
  have hf : PhiC (pvOf h k start true x 4) p = false := by simpa using hp2
  exact not_injOn_of_phi h k start hk true 4 (by norm_num) (by omega) (fun _ => le_rfl) x p
    (by omega) hf

theorem exists_key (h k start : ℕ) (hk : 11 ≤ k) (y : ℕ) :
    ∃ x : ℕ, x < 2 ^ k ∧ ∀ idx < 11, yK h k start x idx = y.testBit idx := by
  set pos : ℕ → ℕ := fun idx => (start + h + idx + k - 9) % k with hpos
  have hinj : ∀ i j, i < 11 → j < 11 → pos i = pos j → i = j := by
    intro i j hi hj hij
    have e1 : start + h + i + k - 9 = (start + h + k - 9) + i := by omega
    have e2 : start + h + j + k - 9 = (start + h + k - 9) + j := by omega
    simp only [hpos, e1, e2] at hij
    have : i ≡ j [MOD k] := Nat.ModEq.add_left_cancel' _ hij
    exact Nat.ModEq.eq_of_lt_of_lt this (by omega) (by omega)
  refine ⟨num (fun m => (List.range 11).any (fun idx => y.testBit idx && decide (pos idx = m))) k,
    num_lt _ _, ?_⟩
  intro idx hidx
  have hk0 : 0 < k := by omega
  simp only [yK]
  show (num _ k).testBit (pos idx) = _
  rw [num_testBit]
  have hlt : pos idx < k := Nat.mod_lt _ hk0
  simp only [hlt, decide_true, Bool.true_and]
  cases hy : y.testBit idx
  · rw [Bool.eq_false_iff]
    intro hc
    rw [List.any_eq_true] at hc
    obtain ⟨i, hi, hc⟩ := hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    have := hinj i idx (List.mem_range.1 hi) hidx hc.2
    subst this
    simp [hy] at hc
  · rw [List.any_eq_true]
    exact ⟨idx, List.mem_range.2 hidx, by simp [hy]⟩

theorem pOf_testBit (L h : ℕ) (hL : L ≤ h) (z : Fin h → Bool) (i : ℕ) (hi : i < L) :
    (pOf L h z).testBit i = z ⟨h - L + i, by omega⟩ := by
  simp only [pOf, num_testBit, hi, decide_true, Bool.true_and]
  simp [show h - L + i < h by omega]

theorem key_good (h k start : ℕ) (hk : 11 ≤ k) (h5 : 5 ≤ h) (i : Fin 3) (x : ℕ)
    (hx : ∀ idx < 11, yK h k start x idx = (keyY i).testBit idx) (r c : Fin h → Bool)
    (hi : tbl (r ⟨h-1, by omega⟩) (r ⟨h-3, by omega⟩) (c ⟨h-1, by omega⟩) (c ⟨h-2, by omega⟩) = i) :
    okD h k start x r c := by
  have hp : pOf 5 h r < 32 := lt_of_lt_of_eq (num_lt _ 5) (by norm_num)
  have hq : pOf 4 h c < 16 := lt_of_lt_of_eq (num_lt _ 4) (by norm_num)
  have hspec := fin_table_spec _ hp _ hq
  have tb1 : (pOf 5 h r).testBit 4 = r ⟨h-1, by omega⟩ := by
    rw [pOf_testBit 5 h (by omega) r 4 (by norm_num)]; congr 1; ext; simp; omega
  have tb2 : (pOf 5 h r).testBit 2 = r ⟨h-3, by omega⟩ := by
    rw [pOf_testBit 5 h (by omega) r 2 (by norm_num)]; congr 1; ext; simp; omega
  have tb3 : (pOf 4 h c).testBit 3 = c ⟨h-1, by omega⟩ := by
    rw [pOf_testBit 4 h (by omega) c 3 (by norm_num)]; congr 1; ext; simp; omega
  have tb4 : (pOf 4 h c).testBit 2 = c ⟨h-2, by omega⟩ := by
    rw [pOf_testBit 4 h (by omega) c 2 (by norm_num)]; congr 1; ext; simp; omega
  rw [tb1, tb2, tb3, tb4, hi] at hspec
  have eR : pvOf h k start false x 5 = rowPV (keyY i) := by
    have : PA false (yK h k start x) = PA false (fun idx => (keyY i).testBit idx) := by
      funext m
      simp only [PA, Bool.false_eq_true, ↓reduceIte]
      rw [hx (10-m) (by omega), hx (9-m) (by omega), hx (8-m) (by omega)]
    unfold pvOf rowPV
    rw [this]
  have eC : pvOf h k start true x 4 = colPV (keyY i) := by
    have : PA true (yK h k start x) = PA true (fun idx => (keyY i).testBit idx) := by
      funext m
      simp only [PA, ↓reduceIte]
      rw [hx (9-m) (by omega), hx (7-m) (by omega), hx (5-m) (by omega)]
    unfold pvOf colPV
    rw [this]
  refine ⟨injOn_of_phi h k start hk false 5 (by norm_num) h5 (by simp) x r ?_,
    injOn_of_phi h k start hk true 4 (by norm_num) (by omega) (fun _ => le_rfl) x c ?_⟩
  · rw [eR, ← PhiR_eq]; exact hspec.1
  · rw [eC, ← PhiC_eq]; exact hspec.2

def toVec {h : ℕ} (w : Fin h → Bool) : Fin h → ZMod 2 := fun i => if w i then 1 else 0

def patOf {n h : ℕ} (r : Fin n → Fin h → ZMod 2) (j : Fin n) : Fin h → Bool :=
  fun i => decide (r j i ≠ 0)

def distD {m : ℕ} (x y : Fin m → ZMod 2) : ℕ := (Finset.univ.filter (fun i => x i ≠ y i)).card

theorem patOf_toVec {n h : ℕ} (f : Fin n → Fin h → Bool) (j : Fin n) :
    patOf (fun j => toVec (f j)) j = f j := by
  funext i
  cases hf : f j i <;> simp [patOf, toVec, hf]

def pick {h : ℕ} (w cw : Fin 3 → Fin h → Bool) (α β : ZMod 2) :
    (Fin h → Bool) × (Fin h → Bool) × (Fin h → Bool) :=
  if α = 0 then (if β = 0 then (w 0, w 0, cw 0) else (w 0, w 2, cw 1))
  else (if β = 0 then (w 0, w 1, cw 2) else (w 1, w 2, cw 0))

theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by revert x; decide

theorem zmod2_sub (x y : ZMod 2) : x - y = x + y := by revert x y; decide

theorem pick_sub {h : ℕ} (w cw : Fin 3 → Fin h → Bool) (α β : ZMod 2) (i : Fin h) :
    toVec (pick w cw α β).1 i - toVec (pick w cw α β).2.1 i =
      α * (toVec (w 0) i + toVec (w 1) i) + β * (toVec (w 0) i + toVec (w 2) i) := by
  rcases zmod2_cases α with rfl | rfl <;> rcases zmod2_cases β with rfl | rfl <;>
    simp [pick, zmod2_sub] <;>
    exact (by decide : ∀ a b c : ZMod 2, b + c = a + b + (a + c)) _ _ _

def iotaM {n h : ℕ} (w : Fin 3 → Fin h → Bool) :
    (Fin (2*n) → ZMod 2) →ₗ[ZMod 2] (Fin n → Fin h → ZMod 2) where
  toFun u j i := u ⟨2*j.val, by have := j.2; omega⟩ * (toVec (w 0) i + toVec (w 1) i) +
    u ⟨2*j.val+1, by have := j.2; omega⟩ * (toVec (w 0) i + toVec (w 2) i)
  map_add' u v := by funext j i; simp only [Pi.add_apply]; ring
  map_smul' c u := by funext j i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem contra3 {h : ℕ} (gL gR : Fin 3 → (Fin h → Bool) → Prop) (w cw : Fin 3 → Fin h → Bool)
    (hw : ∀ i, ¬ gL i (w i)) (hcw : ∀ i, ¬ gR i (cw i)) (i0 a b c : Fin 3)
    (hcov : ∀ i : Fin 3, i = a ∨ i = b ∨ i = c) (g1 : gL i0 (w a)) (g2 : gL i0 (w b))
    (g3 : gR i0 (cw c)) : False := by
  rcases hcov i0 with h0 | h0 | h0 <;> subst h0
  · exact hw _ g1
  · exact hw _ g2
  · exact hcw _ g3

theorem plane_code {n h a b e : ℕ}
    (L : (Fin n → Fin h → ZMod 2) →ₗ[ZMod 2] (Fin a → ZMod 2))
    (Rm : (Fin n → Fin h → ZMod 2) →ₗ[ZMod 2] (Fin b → ZMod 2))
    (out : (Fin a → ZMod 2) → (Fin b → ZMod 2) → Fin n → Fin 3)
    (gL gR : Fin 3 → (Fin h → Bool) → Prop) (w cw : Fin 3 → Fin h → Bool)
    (hw : ∀ i, ¬ gL i (w i)) (hcw : ∀ i, ¬ gR i (cw i))
    (H : ∀ (r c : Fin n → Fin h → ZMod 2) (s : Fin a → ZMod 2) (t : Fin b → ZMod 2),
      distD (L r) s + distD (Rm c) t ≤ e →
        ∀ j, gL (out s t j) (patOf r j) ∧ gR (out s t j) (patOf c j)) :
    ∃ E : (Fin (2*n) → ZMod 2) →ₗ[ZMod 2] (Fin a → ZMod 2),
      ∀ u v, u ≠ v → 2*e < distD (E u) (E v) := by
  refine ⟨L ∘ₗ iotaM w, ?_⟩
  intro u v huv
  by_contra hle
  have hle' : distD ((L ∘ₗ iotaM w) u) ((L ∘ₗ iotaM w) v) ≤ 2 * e := not_lt.1 hle
  have hd : u - v ≠ 0 := sub_ne_zero.2 huv
  obtain ⟨j0, hj0⟩ : ∃ j0 : Fin n, (u - v) ⟨2*j0.val, by have := j0.2; omega⟩ ≠ 0 ∨
      (u - v) ⟨2*j0.val+1, by have := j0.2; omega⟩ ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_or, not_not] at hcon
    apply hd
    funext l
    have hl := l.2
    obtain ⟨hh0, hh1⟩ := hcon ⟨l.val/2, by omega⟩
    by_cases hpar : l.val % 2 = 0
    · have : l = ⟨2*(l.val/2), by omega⟩ := Fin.ext (by simp only; omega)
      rw [this]; exact hh0
    · have : l = ⟨2*(l.val/2)+1, by omega⟩ := Fin.ext (by simp only; omega)
      rw [this]; exact hh1
  let P : Fin n → (Fin h → Bool) × (Fin h → Bool) × (Fin h → Bool) := fun j =>
    pick w cw ((u - v) ⟨2*j.val, by have := j.2; omega⟩)
      ((u - v) ⟨2*j.val+1, by have := j.2; omega⟩)
  let r : Fin n → Fin h → ZMod 2 := fun j => toVec (P j).1
  let r' : Fin n → Fin h → ZMod 2 := fun j => toVec (P j).2.1
  let c : Fin n → Fin h → ZMod 2 := fun j => toVec (P j).2.2
  have hrr : r - r' = iotaM w (u - v) := by
    funext j i
    exact pick_sub w cw _ _ i
  have hE : (L ∘ₗ iotaM w) u - (L ∘ₗ iotaM w) v = L r - L r' := by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← map_sub, ← map_sub, ← hrr, map_sub]
  have hpt : ∀ i, (L r i ≠ L r' i) ↔ ((L ∘ₗ iotaM w) u i ≠ (L ∘ₗ iotaM w) v i) := by
    intro i
    have := congrFun hE i
    simp only [Pi.sub_apply] at this
    rw [← sub_ne_zero, ← sub_ne_zero (a := (L ∘ₗ iotaM w) u i), this]
  set D := Finset.univ.filter (fun i => L r i ≠ L r' i) with hD
  have hDc : D.card ≤ 2 * e := by
    have : D = Finset.univ.filter (fun i => (L ∘ₗ iotaM w) u i ≠ (L ∘ₗ iotaM w) v i) :=
      Finset.filter_congr (fun i _ => hpt i)
    rw [this]; exact hle'
  obtain ⟨D1, hD1, hD1c⟩ := Finset.exists_subset_card_eq (s := D) (n := min e D.card)
    (min_le_right _ _)
  let s : Fin a → ZMod 2 := fun i => if i ∈ D1 then L r' i else L r i
  have hs1 : distD (L r) s ≤ e := by
    unfold distD
    calc (Finset.univ.filter (fun i => L r i ≠ s i)).card ≤ D1.card := by
          apply Finset.card_le_card
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          by_contra hn
          exact hi (by simp [s, hn])
      _ ≤ e := by rw [hD1c]; exact min_le_left _ _
  have hs2 : distD (L r') s ≤ e := by
    unfold distD
    calc (Finset.univ.filter (fun i => L r' i ≠ s i)).card ≤ (D \ D1).card := by
          apply Finset.card_le_card
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          have hn : i ∉ D1 := fun hm => hi (by simp [s, hm])
          have hne : L r i ≠ L r' i := by
            intro heq; apply hi; simp [s, hn, heq]
          exact Finset.mem_sdiff.2 ⟨by simp [hD, hne], hn⟩
      _ ≤ e := by
          rw [Finset.card_sdiff_of_subset hD1, hD1c]; omega
  have hz : distD (Rm c) (Rm c) = 0 := by simp [distD]
  have H1 := H r c s (Rm c) (by omega)
  have H2 := H r' c s (Rm c) (by omega)
  have g1 := H1 j0
  have g2 := H2 j0
  have e1 : patOf r j0 = (P j0).1 := patOf_toVec (fun j => (P j).1) j0
  have e2 : patOf r' j0 = (P j0).2.1 := patOf_toVec (fun j => (P j).2.1) j0
  have e3 : patOf c j0 = (P j0).2.2 := patOf_toVec (fun j => (P j).2.2) j0
  rw [e1, e3] at g1
  rw [e2] at g2
  generalize out s (Rm c) j0 = i0 at g1 g2
  simp only [P, pick] at g1 g2
  rcases zmod2_cases ((u - v) ⟨2*j0.val, by have := j0.2; omega⟩) with ha | ha <;>
    rcases zmod2_cases ((u - v) ⟨2*j0.val+1, by have := j0.2; omega⟩) with hb | hb
  · rcases hj0 with hj | hj <;> contradiction
  · rw [ha, hb] at g1 g2
    simp at g1 g2
    exact contra3 gL gR w cw hw hcw i0 0 2 1 (by decide) g1.1 g2.1 g1.2
  · rw [ha, hb] at g1 g2
    simp at g1 g2
    exact contra3 gL gR w cw hw hcw i0 0 1 2 (by decide) g1.1 g2.1 g1.2
  · rw [ha, hb] at g1 g2
    simp at g1 g2
    exact contra3 gL gR w cw hw hcw i0 1 2 0 (by decide) g1.1 g2.1 g1.2

theorem distD_comm {m : ℕ} (x y : Fin m → ZMod 2) : distD x y = distD y x := by
  unfold distD
  congr 1
  apply Finset.filter_congr
  intro i _
  exact ne_comm

theorem distD_tri {m : ℕ} (x y z : Fin m → ZMod 2) : distD x z ≤ distD x y + distD y z := by
  unfold distD
  calc (Finset.univ.filter (fun i => x i ≠ z i)).card
      ≤ (Finset.univ.filter (fun i => x i ≠ y i) ∪ Finset.univ.filter (fun i => y i ≠ z i)).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hi ⊢
        by_cases hxy : x i = y i
        · right; rw [← hxy]; exact hi
        · left; exact hxy
    _ ≤ _ := Finset.card_union_le _ _

noncomputable def decF {n m : ℕ} (E : (Fin (2*n) → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)) (e : ℕ)
    (s : Fin m → ZMod 2) : Fin (2*n) → ZMod 2 :=
  if hx : ∃ u, distD (E u) s ≤ e then Classical.choose hx else 0

theorem decF_eq {n m : ℕ} (E : (Fin (2*n) → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)) (e : ℕ)
    (hE : ∀ u v, u ≠ v → 2*e < distD (E u) (E v)) (s : Fin m → ZMod 2) (u : Fin (2*n) → ZMod 2)
    (hu : distD (E u) s ≤ e) : decF E e s = u := by
  have hx : ∃ u, distD (E u) s ≤ e := ⟨u, hu⟩
  unfold decF
  rw [dif_pos hx]
  have h1 := Classical.choose_spec hx
  by_contra hne
  have h2 := hE _ _ hne
  have h3 := distD_tri (E (Classical.choose hx)) s (E u)
  have h4 := distD_comm s (E u)
  omega

def rhoM {n h : ℕ} (i1 i2 : ℕ) (h1 : i1 < h) (h2 : i2 < h) :
    (Fin n → Fin h → ZMod 2) →ₗ[ZMod 2] (Fin (2*n) → ZMod 2) where
  toFun r l := if l.val % 2 = 0 then r ⟨l.val / 2, by have := l.2; omega⟩ ⟨i1, h1⟩
    else r ⟨l.val / 2, by have := l.2; omega⟩ ⟨i2, h2⟩
  map_add' r r' := by funext l; simp only [Pi.add_apply]; split_ifs <;> rfl
  map_smul' c r := by funext l; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> rfl

theorem rhoM_even {n h : ℕ} (i1 i2 : ℕ) (h1 : i1 < h) (h2 : i2 < h)
    (r : Fin n → Fin h → ZMod 2) (j : Fin n) :
    rhoM i1 i2 h1 h2 r ⟨2*j.val, by have := j.2; omega⟩ = r j ⟨i1, h1⟩ := by
  simp only [rhoM, LinearMap.coe_mk, AddHom.coe_mk]
  rw [if_pos (by simp)]
  congr 2
  omega

theorem rhoM_odd {n h : ℕ} (i1 i2 : ℕ) (h1 : i1 < h) (h2 : i2 < h)
    (r : Fin n → Fin h → ZMod 2) (j : Fin n) :
    rhoM i1 i2 h1 h2 r ⟨2*j.val+1, by have := j.2; omega⟩ = r j ⟨i2, h2⟩ := by
  simp only [rhoM, LinearMap.coe_mk, AddHom.coe_mk]
  rw [if_neg (by simp [Nat.add_mod])]
  congr 2
  omega

theorem keyY_inj : ∀ i i' : Fin 3, keyY i = keyY i' → i = i' := by decide

theorem keyY_lt : ∀ i : Fin 3, keyY i < 2 ^ 11 := by decide

theorem main_iff (h k start n a b e : ℕ) (h5 : 5 ≤ h) (hk : h + 6 ≤ k) :
    ((∃ (menu : Fin 3 → Fin (2^k)) (L : (Fin n → Fin h → ZMod 2) →ₗ[ZMod 2] (Fin a → ZMod 2))
       (R : (Fin n → Fin h → ZMod 2) →ₗ[ZMod 2] (Fin b → ZMod 2))
       (out : (Fin a → ZMod 2) → (Fin b → ZMod 2) → Fin n → Fin 3),
      Function.Injective menu ∧ ∀ (r c : Fin n → Fin h → ZMod 2) (s : Fin a → ZMod 2)
        (t : Fin b → ZMod 2), distD (L r) s + distD (R c) t ≤ e →
        ∀ j, okD h k start (menu (out s t j)).val (patOf r j) (patOf c j)) ↔
     ((∃ E : (Fin (2*n) → ZMod 2) →ₗ[ZMod 2] (Fin a → ZMod 2),
        ∀ u v, u ≠ v → 2*e < distD (E u) (E v)) ∧
      (∃ E : (Fin (2*n) → ZMod 2) →ₗ[ZMod 2] (Fin b → ZMod 2),
        ∀ u v, u ≠ v → 2*e < distD (E u) (E v)))) := by
  have hk' : 11 ≤ k := by omega
  constructor
  · rintro ⟨menu, L, R, out, -, H⟩
    choose w hw using fun i : Fin 3 => row_rej h k start hk' h5 (menu i).val
    choose cw hcw using fun i : Fin 3 => col_rej h k start hk' h5 (menu i).val
    refine ⟨plane_code L R out
      (fun i z => Set.InjOn (tailD h k start false (menu i).val 5) (fiberS h z))
      (fun i z => Set.InjOn (tailD h k start true (menu i).val 4) (fiberS h z)) w cw hw hcw
      (fun r c s t hd j => H r c s t hd j), ?_⟩
    exact plane_code R L (fun t s j => out s t j)
      (fun i z => Set.InjOn (tailD h k start true (menu i).val 4) (fiberS h z))
      (fun i z => Set.InjOn (tailD h k start false (menu i).val 5) (fiberS h z)) cw w hcw hw
      (fun c r t s hd j => And.symm (H r c s t (by omega) j))
  · rintro ⟨⟨Ea, hEa⟩, ⟨Eb, hEb⟩⟩
    have hx : ∀ i : Fin 3, ∃ x : ℕ, x < 2 ^ k ∧
        ∀ idx < 11, yK h k start x idx = (keyY i).testBit idx :=
      fun i => exists_key h k start hk' (keyY i)
    choose xK hxlt hxK using hx
    refine ⟨fun i => ⟨xK i, hxlt i⟩,
      Ea ∘ₗ rhoM (h-1) (h-3) (by omega) (by omega),
      Eb ∘ₗ rhoM (h-1) (h-2) (by omega) (by omega),
      fun s t j => tbl (decide (decF Ea e s ⟨2*j.val, by have := j.2; omega⟩ ≠ 0))
        (decide (decF Ea e s ⟨2*j.val+1, by have := j.2; omega⟩ ≠ 0))
        (decide (decF Eb e t ⟨2*j.val, by have := j.2; omega⟩ ≠ 0))
        (decide (decF Eb e t ⟨2*j.val+1, by have := j.2; omega⟩ ≠ 0)), ?_, ?_⟩
    · intro i i' hii'
      have hx1 : xK i = xK i' := congrArg Fin.val hii'
      apply keyY_inj
      apply Nat.eq_of_testBit_eq
      intro idx
      by_cases hidx : idx < 11
      · rw [← hxK i idx hidx, ← hxK i' idx hidx, hx1]
      · rw [Nat.testBit_lt_two_pow, Nat.testBit_lt_two_pow]
        · exact lt_of_lt_of_le (keyY_lt i') (Nat.pow_le_pow_right (by norm_num) (by omega))
        · exact lt_of_lt_of_le (keyY_lt i) (Nat.pow_le_pow_right (by norm_num) (by omega))
    · intro r c s t hd j
      have hA : decF Ea e s = rhoM (h-1) (h-3) (by omega) (by omega) r := by
        apply decF_eq Ea e hEa
        have := hd
        simp only [LinearMap.comp_apply] at this
        omega
      have hB : decF Eb e t = rhoM (h-1) (h-2) (by omega) (by omega) c := by
        apply decF_eq Eb e hEb
        have := hd
        simp only [LinearMap.comp_apply] at this
        omega
      refine key_good h k start hk' h5 _ (xK _) (hxK _) _ _ ?_
      show tbl (decide (r j ⟨h-1, by omega⟩ ≠ 0)) (decide (r j ⟨h-3, by omega⟩ ≠ 0))
        (decide (c j ⟨h-1, by omega⟩ ≠ 0)) (decide (c j ⟨h-2, by omega⟩ ≠ 0)) = tbl _ _ _ _
      rw [hA, hB, rhoM_even, rhoM_odd, rhoM_even, rhoM_odd]

end PEqualNP.Outside.L_meta_39006

theorem PEqualNP.Outside.L_meta_39006 : (∀ (h k start n a b e : Nat), 5 ≤ h → h+6 ≤ k →
  let tap := fun (x j back : Nat) => x.testBit ((start+j+k-back) % k)
  let pulse := fun (col : Bool) (x j : Nat) =>
    if col then xor (tap x j 1) (xor (tap x j 3) (tap x j 5))
    else xor (tap x j 0) (xor (tap x j 1) (tap x j 2))
  let chi := fun (bits : Nat → Bool) (j : Nat) =>
    xor (bits j) (!(bits (j+1)) && bits (j+2))
  let fiber := fun (z : Fin h → Bool) =>
    {u : Nat | u < 2^(h+2) ∧ ∀ j : Fin h, chi (fun i => u.testBit i) j = z j}
  let tail := fun (col : Bool) (x len u : Nat) =>
    (Finset.range len).filter (fun j =>
      chi (fun i => xor (u.testBit i) (pulse col x i)) (h-len+j))
  let ok := fun (x : Nat) (r c : Fin h → Bool) =>
    Set.InjOn (tail false x 5) (fiber r) ∧ Set.InjOn (tail true x 4) (fiber c)
  let F := ZMod 2
  let V := Fin n → Fin h → F
  let dist := fun {m : Nat} (x y : Fin m → F) =>
    (Finset.univ.filter (fun i => x i ≠ y i)).card
  let code := fun (m : Nat) =>
    ∃ E : (Fin (2*n) → F) →ₗ[F] (Fin m → F),
      ∀ u v, u ≠ v → 2*e < dist (E u) (E v)
  (∃ (menu : Fin 3 → Fin (2^k)) (L : V →ₗ[F] (Fin a → F))
     (R : V →ₗ[F] (Fin b → F)) (out : (Fin a → F) → (Fin b → F) → Fin n → Fin 3),
    Function.Injective menu ∧ ∀ (r c : V) (s : Fin a → F) (t : Fin b → F),
      dist (L r) s + dist (R c) t ≤ e →
      ∀ j, ok (menu (out s t j)).val (fun i => decide (r j i ≠ 0))
        (fun i => decide (c j i ≠ 0))) ↔ code a ∧ code b) := by
  intro h k start n a b e h5 hk
  exact PEqualNP.Outside.L_meta_39006.main_iff h k start n a b e h5 hk
