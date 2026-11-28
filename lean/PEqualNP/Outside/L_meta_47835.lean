import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47835

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def fullMask : Nat := 0xffffffffffffffff

abbrev Masked (mask w : Nat) : Prop := w &&& mask = w

def bsel {α : Type} (c : Bool) (t f : α) : α := Bool.rec f t c

theorem bsel_true {α : Type} (t f : α) : bsel true t f = t := rfl
theorem bsel_false {α : Type} (t f : α) : bsel false t f = f := rfl

theorem beq_false_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem ne_of_beq_false {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := by
  intro e; subst e; rw [Nat.beq_refl] at h; exact Bool.noConfusion h

theorem masked_zero (mask : Nat) : Masked mask 0 := by
  unfold Masked; simp

theorem masked_self (mask : Nat) : Masked mask mask := by
  unfold Masked; simp

theorem masked_land_right (mask w : Nat) : Masked mask (w &&& mask) := by
  unfold Masked; apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and]

theorem masked_xor {mask a b : Nat} (ha : Masked mask a) (hb : Masked mask b) :
    Masked mask (a ^^^ b) := by
  unfold Masked at ha hb ⊢
  apply Nat.eq_of_testBit_eq; intro i
  have ea := congrArg (fun x => x.testBit i) ha
  have eb := congrArg (fun x => x.testBit i) hb
  simp only [Nat.testBit_and, Nat.testBit_xor] at ea eb ⊢
  cases hm : mask.testBit i <;> simp_all

theorem xor_cancel_left (mask v : Nat) : mask ^^^ (mask ^^^ v) = v := by
  apply Nat.eq_of_testBit_eq; intro i; simp

theorem masked_sub_and {mask cut w : Nat} (sub : mask &&& cut = cut) :
    (w &&& mask) &&& cut = w &&& cut := by
  apply Nat.eq_of_testBit_eq; intro i
  have es := congrArg (fun x => x.testBit i) sub
  simp only [Nat.testBit_and] at es ⊢
  cases hc : cut.testBit i <;> simp_all

theorem masked_sub_xor {mask cut w : Nat} (sub : mask &&& cut = cut) :
    (mask ^^^ w) &&& cut = cut ^^^ (w &&& cut) := by
  apply Nat.eq_of_testBit_eq; intro i
  have es := congrArg (fun x => x.testBit i) sub
  simp only [Nat.testBit_and, Nat.testBit_xor] at es ⊢
  cases hc : cut.testBit i <;> simp_all

def canon (mask w : Nat) : Nat :=
  let v := w &&& mask
  bsel (Nat.beq v 0 || Nat.beq v mask) 0
    (let iv := mask ^^^ v; bsel (Nat.blt v iv) v iv)

theorem canon_zero (mask : Nat) : canon mask 0 = 0 := by
  unfold canon; simp [bsel]

theorem canon_self (mask : Nat) : canon mask mask = 0 := by
  unfold canon; simp [bsel]

theorem canon_land (mask w : Nat) : canon mask (w &&& mask) = canon mask w := by
  unfold canon; dsimp only; rw [masked_land_right mask w]

theorem canon_cases (mask w : Nat) :
    (canon mask w = 0 ∧ (w &&& mask = 0 ∨ w &&& mask = mask)) ∨
    (canon mask w ≠ 0 ∧ (canon mask w = w &&& mask ∨ canon mask w = mask ^^^ (w &&& mask))) := by
  unfold canon; dsimp only
  set v := w &&& mask
  by_cases hv0 : v = 0
  · left; rw [hv0]; simp [bsel]
  · by_cases hvm : v = mask
    · left; rw [hvm]; simp [bsel]
    · right
      rw [beq_false_ne hv0, beq_false_ne hvm]
      simp only [Bool.or_false, bsel_false]
      cases hlt : Nat.blt v (mask ^^^ v)
      · rw [bsel_false]
        refine ⟨?_, Or.inr rfl⟩
        intro hz
        have e := congrArg (fun x => mask ^^^ x) hz
        rw [xor_cancel_left] at e
        exact hvm (by simpa using e)
      · rw [bsel_true]; exact ⟨hv0, Or.inl rfl⟩

theorem canon_masked (mask w : Nat) : Masked mask (canon mask w) := by
  rcases canon_cases mask w with ⟨h0, _⟩ | ⟨_, h1 | h2⟩
  · rw [h0]; exact masked_zero mask
  · rw [h1]; exact masked_land_right mask w
  · rw [h2]; exact masked_xor (masked_self mask) (masked_land_right mask w)

theorem canon_xor_mask (mask w : Nat) : canon mask (mask ^^^ w) = canon mask w := by
  have hsub : (mask ^^^ w) &&& mask = mask ^^^ (w &&& mask) := masked_sub_xor (masked_self mask)
  unfold canon; dsimp only
  rw [hsub]
  generalize hv : w &&& mask = v
  set iv := mask ^^^ v
  have hiv : mask ^^^ iv = v := xor_cancel_left mask v
  rw [hiv]
  by_cases hv0 : v = 0
  · have hivm : iv = mask := by simp [iv, hv0]
    rw [hv0, hivm]; simp [bsel]
  · by_cases hvm : v = mask
    · have hiv0 : iv = 0 := by simp [iv, hvm]
      rw [hvm, hiv0]; simp [bsel]
    · have hiv0 : iv ≠ 0 := by
        intro h; apply hvm
        have e := congrArg (fun x => mask ^^^ x) h
        rw [hiv] at e; simpa using e
      have hivm : iv ≠ mask := by
        intro h; apply hv0
        have e := congrArg (fun x => mask ^^^ x) h
        rw [hiv] at e; simpa using e
      rw [beq_false_ne hv0, beq_false_ne hvm, beq_false_ne hiv0, beq_false_ne hivm]
      simp only [Bool.or_false, bsel_false]
      have hne : v ≠ iv := by
        intro h
        have hm0 : mask = 0 := by
          apply Nat.eq_of_testBit_eq; intro i
          have ei := congrArg (fun x => x.testBit i) h
          simp only [iv, Nat.testBit_xor] at ei
          cases hv' : v.testBit i <;> cases hm' : mask.testBit i <;> simp_all
        have : v = 0 := by rw [← hv, hm0]; simp
        exact hv0 this
      by_cases hlt : v < iv
      · have h1 : Nat.blt v iv = true := Nat.blt_eq.mpr hlt
        have h2 : Nat.blt iv v = false := by cases h : Nat.blt iv v; rfl; have := Nat.blt_eq.mp h; omega
        rw [h1, h2, bsel_true, bsel_false]
      · have hgt : iv < v := by omega
        have h1 : Nat.blt v iv = false := by cases h : Nat.blt v iv; rfl; have := Nat.blt_eq.mp h; omega
        have h2 : Nat.blt iv v = true := Nat.blt_eq.mpr hgt
        rw [h1, h2, bsel_false, bsel_true]

theorem canon_idem (mask w : Nat) : canon mask (canon mask w) = canon mask w := by
  rcases canon_cases mask w with ⟨h0, _⟩ | ⟨_, h1 | h2⟩
  · rw [h0, canon_zero]
  · calc canon mask (canon mask w) = canon mask (w &&& mask) := by rw [h1]
      _ = canon mask w := canon_land mask w
  · calc canon mask (canon mask w) = canon mask (mask ^^^ (w &&& mask)) := by rw [h2]
      _ = canon mask (w &&& mask) := canon_xor_mask mask (w &&& mask)
      _ = canon mask w := canon_land mask w

theorem canon_submask {mask cut w : Nat} (sub : mask &&& cut = cut) (hc : canon mask w ≠ 0) :
    canon cut (canon mask w) = canon cut w := by
  rcases canon_cases mask w with ⟨h0, _⟩ | ⟨_, h1 | h2⟩
  · exact absurd h0 hc
  · rw [h1, ← canon_land cut (w &&& mask), masked_sub_and sub, canon_land]
  · rw [h2, ← canon_land cut (mask ^^^ (w &&& mask)), masked_sub_xor sub, masked_sub_and sub]
    rw [← masked_sub_xor (masked_self cut), canon_land, canon_xor_mask]

theorem canon_submask_zero {mask cut w : Nat} (sub : mask &&& cut = cut) (hc : canon mask w = 0) :
    canon cut w = 0 := by
  rcases canon_cases mask w with ⟨_, h0 | hm⟩ | ⟨hne, _⟩
  · rw [← canon_land cut w, ← masked_sub_and sub, h0]; simp [canon_zero]
  · rw [← canon_land cut w, ← masked_sub_and sub, hm, sub, canon_self]
  · exact absurd hc hne

theorem canon_testBit_eq {mask w p n : Nat} (hp : mask.testBit p = true) (hn : mask.testBit n = true) :
    ((canon mask w).testBit p = (canon mask w).testBit n) ↔ (w.testBit p = w.testBit n) := by
  rcases canon_cases mask w with ⟨h0, h1 | h2⟩ | ⟨_, h1 | h2⟩
  · rw [h0]
    have e1 := congrArg (fun x => x.testBit p) h1
    have e2 := congrArg (fun x => x.testBit n) h1
    simp [Nat.testBit_and, hp, hn] at e1 e2 ⊢; simp [e1, e2]
  · rw [h0]
    have e1 := congrArg (fun x => x.testBit p) h2
    have e2 := congrArg (fun x => x.testBit n) h2
    simp [Nat.testBit_and, hp, hn] at e1 e2 ⊢; simp [e1, e2]
  · rw [h1]; simp [Nat.testBit_and, hp, hn]
  · rw [h2]; simp [Nat.testBit_xor, Nat.testBit_and, hp, hn]

def binOp (mask op a b : Nat) : Nat :=
  bsel (Nat.beq op 0) (canon mask (a &&& b))
    (bsel (Nat.beq op 1) (canon mask (a ||| b))
      (bsel (Nat.beq op 2) (canon mask (a &&& (mask ^^^ b)))
        (canon mask ((mask ^^^ a) &&& b))))

theorem binOp_canon (mask op a b : Nat) : canon mask (binOp mask op a b) = binOp mask op a b := by
  unfold binOp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false] <;> exact canon_idem mask _

theorem binOp_comm (mask op a b : Nat) (hop : op < 4) :
    ∃ op' < 4, binOp mask op a b = binOp mask op' b a := by
  have hland : a &&& b = b &&& a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  have hlor : a ||| b = b ||| a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_or, Bool.or_comm]
  have h23 : a &&& (mask ^^^ b) = (mask ^^^ b) &&& a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  have h32 : (mask ^^^ a) &&& b = b &&& (mask ^^^ a) := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  rcases (show op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 by omega) with rfl | rfl | rfl | rfl
  · exact ⟨0, by omega, by change canon mask (a &&& b) = canon mask (b &&& a); rw [hland]⟩
  · exact ⟨1, by omega, by change canon mask (a ||| b) = canon mask (b ||| a); rw [hlor]⟩
  · exact ⟨3, by omega, by change canon mask (a &&& (mask ^^^ b)) = canon mask ((mask ^^^ b) &&& a); rw [h23]⟩
  · exact ⟨2, by omega, by change canon mask ((mask ^^^ a) &&& b) = canon mask (b &&& (mask ^^^ a)); rw [h32]⟩

theorem binOp_zero_left (mask op b : Nat) : binOp mask op 0 b = 0 ∨ binOp mask op 0 b = canon mask b := by
  unfold binOp
  have hmb : (mask ^^^ 0) &&& b = b &&& mask := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · right; rw [hmb, canon_land]
  · left; simp [canon_zero]
  · right; simp
  · right; simp
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]

theorem binOp_zero_right (mask op a : Nat) : binOp mask op a 0 = 0 ∨ binOp mask op a 0 = canon mask a := by
  unfold binOp
  have hma : a &&& (mask ^^^ 0) = a &&& mask := by simp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · left; simp [canon_zero]
  · right; rw [hma, canon_land]
  · right; simp
  · right; simp
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]

theorem binOp_self (mask op a : Nat) : binOp mask op a a = 0 ∨ binOp mask op a a = canon mask a := by
  have h2 : canon mask (a &&& (mask ^^^ a)) = 0 := by
    rw [← canon_land]
    have : (a &&& (mask ^^^ a)) &&& mask = 0 := by
      apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
      cases a.testBit i <;> cases mask.testBit i <;> rfl
    rw [this, canon_zero]
  have h3 : canon mask ((mask ^^^ a) &&& a) = 0 := by
    rw [← canon_land]
    have : ((mask ^^^ a) &&& a) &&& mask = 0 := by
      apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
      cases a.testBit i <;> cases mask.testBit i <;> rfl
    rw [this, canon_zero]
  unfold binOp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · left; exact h3
  · left; exact h2
  · right; simp
  · right; simp
  · right; simp
  · right; simp
  · right; simp
  · right; simp

theorem deMorgan_or_mask {mask a b : Nat} (ha : Masked mask a) (hb : Masked mask b) :
    mask ^^^ (a &&& b) = (mask ^^^ a) ||| (mask ^^^ b) := by
  unfold Masked at ha hb
  apply Nat.eq_of_testBit_eq; intro i
  have ea := congrArg (fun x => x.testBit i) ha
  have eb := congrArg (fun x => x.testBit i) hb
  simp only [Nat.testBit_and] at ea eb
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor]
  cases hm : mask.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all

theorem canon_and_in_binOp (mask x y : Nat) :
    canon mask (x &&& y) = 0 ∨
    canon mask (x &&& y) = canon mask x ∨
    canon mask (x &&& y) = canon mask y ∨
    ∃ op < 4, canon mask (x &&& y) = binOp mask op (canon mask x) (canon mask y) := by
  have hxy : canon mask (x &&& y) = canon mask ((x &&& mask) &&& (y &&& mask)) := by
    rw [← canon_land mask (x &&& y), ← canon_land mask ((x &&& mask) &&& (y &&& mask))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and]
    cases x.testBit i <;> cases y.testBit i <;> cases mask.testBit i <;> rfl
  rw [hxy]
  have hvxm : Masked mask (x &&& mask) := masked_land_right mask x
  have hvym : Masked mask (y &&& mask) := masked_land_right mask y
  rcases canon_cases mask x with ⟨hx0, hx1 | hx2⟩ | ⟨_, hx1 | hx2⟩
  · left; rw [hx1]; simp [canon_zero]
  · right; right; left; rw [hx2]
    have : mask &&& (y &&& mask) = y &&& mask := by
      apply Nat.eq_of_testBit_eq; intro i
      have e := congrArg (fun t => t.testBit i) hvym
      simp only [Nat.testBit_and] at e ⊢; rw [Bool.and_comm]; exact e
    rw [this, canon_land]
  · rcases canon_cases mask y with ⟨hy0, hy1 | hy2⟩ | ⟨_, hy1 | hy2⟩
    · left; rw [hy1]; simp [canon_zero]
    · right; left; rw [hy2, hvxm, canon_land]
    · right; right; right; refine ⟨0, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x &&& canon mask y)
      rw [hx1, hy1]
    · right; right; right; refine ⟨2, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x &&& (mask ^^^ canon mask y))
      rw [hx1, hy2, xor_cancel_left]
  · rcases canon_cases mask y with ⟨hy0, hy1 | hy2⟩ | ⟨_, hy1 | hy2⟩
    · left; rw [hy1]; simp [canon_zero]
    · right; left; rw [hy2, hvxm, canon_land]
    · right; right; right; refine ⟨3, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask ((mask ^^^ canon mask x) &&& canon mask y)
      rw [hx2, hy1, xor_cancel_left]
    · right; right; right; refine ⟨1, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x ||| canon mask y)
      rw [hx2, hy2, ← deMorgan_or_mask hvxm hvym, canon_xor_mask]

theorem canon_or_in_binOp (mask x y : Nat) :
    canon mask (x ||| y) = 0 ∨
    canon mask (x ||| y) = canon mask x ∨
    canon mask (x ||| y) = canon mask y ∨
    ∃ op < 4, canon mask (x ||| y) = binOp mask op (canon mask x) (canon mask y) := by
  have hxy : canon mask (x ||| y) = canon mask ((mask ^^^ x) &&& (mask ^^^ y)) := by
    rw [← canon_xor_mask mask (x ||| y), ← canon_land mask (mask ^^^ (x ||| y))]
    rw [← canon_land mask ((mask ^^^ x) &&& (mask ^^^ y))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor]
    cases mask.testBit i <;> cases x.testBit i <;> cases y.testBit i <;> rfl
  rw [hxy]
  have h := canon_and_in_binOp mask (mask ^^^ x) (mask ^^^ y)
  rwa [canon_xor_mask, canon_xor_mask] at h

theorem canon_sub_binOp {mask cut op a b : Nat} (sub : mask &&& cut = cut) :
    canon cut (binOp mask op a b) = 0 ∨
    canon cut (binOp mask op a b) = canon cut a ∨
    canon cut (binOp mask op a b) = canon cut b ∨
    ∃ op' < 4, canon cut (binOp mask op a b) = binOp cut op' (canon cut a) (canon cut b) := by
  have go (u : Nat) : canon cut (canon mask u) = canon cut u := by
    by_cases h : canon mask u = 0
    · rw [h, canon_zero, (canon_submask_zero sub h).symm]
    · exact canon_submask sub h
  have hmx1 : canon cut ((mask ^^^ a) &&& b) = canon cut ((cut ^^^ a) &&& b) := by
    rw [← canon_land cut ((mask ^^^ a) &&& b), ← canon_land cut ((cut ^^^ a) &&& b)]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    have es := congrArg (fun t => t.testBit i) sub
    simp only [Nat.testBit_and] at es
    simp only [Nat.testBit_and, Nat.testBit_xor]
    cases hc : cut.testBit i
    · simp
    · simp only [hc, Bool.and_true] at es ⊢; rw [es]
  have hmx2 : canon cut (a &&& (mask ^^^ b)) = canon cut (a &&& (cut ^^^ b)) := by
    rw [← canon_land cut (a &&& (mask ^^^ b)), ← canon_land cut (a &&& (cut ^^^ b))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    have es := congrArg (fun t => t.testBit i) sub
    simp only [Nat.testBit_and] at es
    simp only [Nat.testBit_and, Nat.testBit_xor]
    cases hc : cut.testBit i
    · simp
    · simp only [hc, Bool.and_true] at es ⊢; rw [es]
  have hsub_case1 : canon cut ((cut ^^^ a) &&& b) = 0 ∨ canon cut ((cut ^^^ a) &&& b) = canon cut a ∨
      canon cut ((cut ^^^ a) &&& b) = canon cut b ∨
      ∃ op' < 4, canon cut ((cut ^^^ a) &&& b) = binOp cut op' (canon cut a) (canon cut b) := by
    have h := canon_and_in_binOp cut (cut ^^^ a) b
    rwa [canon_xor_mask] at h
  have hsub_case2 : canon cut (a &&& (cut ^^^ b)) = 0 ∨ canon cut (a &&& (cut ^^^ b)) = canon cut a ∨
      canon cut (a &&& (cut ^^^ b)) = canon cut b ∨
      ∃ op' < 4, canon cut (a &&& (cut ^^^ b)) = binOp cut op' (canon cut a) (canon cut b) := by
    have h := canon_and_in_binOp cut a (cut ^^^ b)
    rwa [canon_xor_mask] at h
  have hbin_eq : binOp mask op a b = canon mask (a &&& b) ∨ binOp mask op a b = canon mask (a ||| b) ∨
      binOp mask op a b = canon mask (a &&& (mask ^^^ b)) ∨ binOp mask op a b = canon mask ((mask ^^^ a) &&& b) := by
    unfold binOp
    cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp [bsel]
  rcases hbin_eq with h | h | h | h <;> rw [h, go]
  · exact canon_and_in_binOp cut a b
  · exact canon_or_in_binOp cut a b
  · rw [hmx2]; exact hsub_case2
  · rw [hmx1]; exact hsub_case1

def Avail (bank : List Nat) (w : Nat) : Prop := w = 0 ∨ w ∈ bank

def GateBin (mask : Nat) (bank : List Nat) (v : Nat) : Prop :=
  ∃ a b op, op < 4 ∧ Avail bank a ∧ Avail bank b ∧ v = binOp mask op a b

def BuildsBin (mask : Nat) (bank : List Nat) : List Nat → Prop
  | [] => True
  | v :: vs => GateBin mask bank v ∧ BuildsBin mask (v :: bank) vs

def LowerBin (mask : Nat) (stock : List Nat) (goal m : Nat) : Prop :=
  ∀ vs, BuildsBin mask stock vs → Avail (vs ++ stock) goal → m ≤ vs.length

theorem avail_weaken {b1 b2 : List Nat} (sub : ∀ w ∈ b1, w ∈ b2) {w : Nat} (h : Avail b1 w) :
    Avail b2 w := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (sub w h)

theorem gate_weaken {mask : Nat} {b1 b2 : List Nat} (sub : ∀ w ∈ b1, w ∈ b2) {v : Nat}
    (h : GateBin mask b1 v) : GateBin mask b2 v := by
  obtain ⟨a, b, op, hop, ha, hb, hv⟩ := h
  exact ⟨a, b, op, hop, avail_weaken sub ha, avail_weaken sub hb, hv⟩

theorem builds_weaken {mask : Nat} {b1 b2 vs : List Nat} (sub : ∀ w ∈ b1, w ∈ b2)
    (h : BuildsBin mask b1 vs) : BuildsBin mask b2 vs := by
  induction vs generalizing b1 b2 with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨gate_weaken sub h.1, ih ?_ h.2⟩
    intro w hw; rcases List.mem_cons.mp hw with rfl | hw
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (sub w hw)

theorem builds_append {mask : Nat} {roots first second : List Nat}
    (h1 : BuildsBin mask roots first) (h2 : BuildsBin mask (first ++ roots) second) :
    BuildsBin mask roots (first ++ second) := by
  induction first generalizing roots with
  | nil => exact h2
  | cons v vs ih =>
    refine ⟨h1.1, ih h1.2 ?_⟩
    exact builds_weaken (fun w hw => by simp only [List.mem_append, List.mem_cons] at hw ⊢; tauto) h2

def dropIf (drop : Bool) (x : Nat) (S : Finset Nat) : Finset Nat :=
  if drop then S.erase x else S

theorem dropIf_subset (drop : Bool) (x : Nat) (S : Finset Nat) : dropIf drop x S ⊆ S := by
  unfold dropIf; split; exact Finset.erase_subset _ _; exact Finset.Subset.refl _

theorem dropIf_card_le (drop : Bool) (x : Nat) (S : Finset Nat) :
    S.card ≤ (dropIf drop x S).card + 1 := by
  unfold dropIf; split
  · by_cases hx : x ∈ S
    · have := Finset.card_erase_add_one hx; omega
    · rw [Finset.erase_eq_of_notMem hx]; omega
  · omega

inductive LiveBin (mask goal : Nat) : Nat → Finset Nat → Prop
  | done : LiveBin mask goal 0 {goal}
  | step {k : Nat} {S : Finset Nat} {a b op : Nat}
      (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hop : op < 4)
      (hz : binOp mask op a b ≠ 0) (hf : binOp mask op a b ∉ S)
      (keepA keepB : Bool) :
      LiveBin mask goal k (insert (binOp mask op a b) (dropIf (!keepA) a (dropIf (!keepB) b S))) →
      LiveBin mask goal (k + 1) S

theorem liveBin_zero_not_mem {mask goal k : Nat} {S : Finset Nat} (hg : goal ≠ 0)
    (h : LiveBin mask goal k S) : 0 ∉ S := by
  induction h with
  | done => simp [hg.symm]
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    intro h0; apply ih
    apply Finset.mem_insert_of_mem
    unfold dropIf
    split
    · apply Finset.mem_erase.mpr; refine ⟨ha0.symm, ?_⟩
      split
      · exact Finset.mem_erase.mpr ⟨hb0.symm, h0⟩
      · exact h0
    · split
      · exact Finset.mem_erase.mpr ⟨hb0.symm, h0⟩
      · exact h0

theorem liveBin_card_le {mask goal k : Nat} {S : Finset Nat} (h : LiveBin mask goal k S) :
    S.card ≤ k + 1 := by
  induction h with
  | done => simp
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    set z := binOp mask op a b
    have h1 := dropIf_card_le (!keepB) b S
    have h2 := dropIf_card_le (!keepA) a (dropIf (!keepB) b S)
    have hz' : z ∉ dropIf (!keepA) a (dropIf (!keepB) b S) := fun hm =>
      hf (dropIf_subset _ _ _ (dropIf_subset _ _ _ hm))
    have h3 : (insert z (dropIf (!keepA) a (dropIf (!keepB) b S))).card =
        (dropIf (!keepA) a (dropIf (!keepB) b S)).card + 1 := Finset.card_insert_of_notMem hz'
    omega

theorem extractLiveBin_aux {mask goal : Nat} (hg : goal ≠ 0) :
    ∀ (vs bank : List Nat) (k : Nat) (L : Finset Nat),
      BuildsBin mask bank vs → (∀ w ∈ bank, canon mask w = w) →
      L ⊆ (vs ++ bank).toFinset → LiveBin mask goal k L →
      ∃ k' S, k' ≤ k + vs.length ∧ S ⊆ bank.toFinset ∧ LiveBin mask goal k' S
  | [], bank, k, L, _, _, hsub, hlive => ⟨k, L, by simp, hsub, hlive⟩
  | v :: vs, bank, k, L, hbuild, hcb, hsub, hlive => by
    have hcv : canon mask v = v := by
      obtain ⟨a, b, op, _, _, _, rfl⟩ := hbuild.1; exact binOp_canon mask op a b
    have hcb' : ∀ w ∈ v :: bank, canon mask w = w := by
      intro w hw; rcases List.mem_cons.mp hw with rfl | hw; exact hcv; exact hcb w hw
    have hsub' : L ⊆ (vs ++ (v :: bank)).toFinset := by
      intro w hw
      have := hsub hw
      simp only [List.toFinset_append, List.toFinset_cons, Finset.mem_union, Finset.mem_insert] at this ⊢
      tauto
    obtain ⟨k1, L1, hk1, hL1sub, hlive1⟩ := extractLiveBin_aux hg vs (v :: bank) k L hbuild.2 hcb' hsub' hlive
    by_cases hv : v ∈ L1 ∧ v ∉ bank
    · obtain ⟨hvL, hvb⟩ := hv
      have hv0 : v ≠ 0 := fun h0 => liveBin_zero_not_mem hg hlive1 (h0 ▸ hvL)
      obtain ⟨a, b, op, hop, haA, hbA, hvEq⟩ := hbuild.1
      have ha0 : a ≠ 0 := by
        intro h0; subst h0
        rcases binOp_zero_left mask op b with h | h
        · exact hv0 (hvEq.trans h)
        · rcases hbA with rfl | hbM
          · rw [canon_zero] at h; exact hv0 (hvEq.trans h)
          · rw [hcb b hbM] at h; exact hvb ((hvEq.trans h) ▸ hbM)
      have hb0 : b ≠ 0 := by
        intro h0; subst h0
        rcases binOp_zero_right mask op a with h | h
        · exact hv0 (hvEq.trans h)
        · rcases haA with rfl | haM
          · rw [canon_zero] at h; exact hv0 (hvEq.trans h)
          · rw [hcb a haM] at h; exact hvb ((hvEq.trans h) ▸ haM)
      have haM : a ∈ bank := haA.resolve_left ha0
      have hbM : b ∈ bank := hbA.resolve_left hb0
      have hab : a ≠ b := by
        intro h; subst h
        rcases binOp_self mask op a with h0 | ha'
        · exact hv0 (hvEq.trans h0)
        · rw [hcb a haM] at ha'; exact hvb ((hvEq.trans ha') ▸ haM)
      set R := L1.erase v
      set S := insert a (insert b R)
      have hSsub : S ⊆ bank.toFinset := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact List.mem_toFinset.mpr haM
        · rcases Finset.mem_insert.mp hw with rfl | hw
          · exact List.mem_toFinset.mpr hbM
          · have h1 := hL1sub (Finset.mem_of_mem_erase hw)
            simp only [List.toFinset_cons, Finset.mem_insert] at h1
            exact h1.resolve_left (Finset.ne_of_mem_erase hw)
      have hvNotS : v ∉ S := by
        intro hm
        rcases Finset.mem_insert.mp hm with rfl | hm
        · exact hvb haM
        · rcases Finset.mem_insert.mp hm with rfl | hm
          · exact hvb hbM
          · exact (Finset.notMem_erase v L1) hm
      have hL1eq : insert v (dropIf (!(decide (a ∈ R))) a (dropIf (!(decide (b ∈ R))) b S)) = L1 := by
        ext w
        by_cases haR : a ∈ R <;> by_cases hbR : b ∈ R
        · simp only [haR, hbR, decide_true, Bool.not_true, Bool.false_eq_true, dropIf, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | rfl | rfl | ⟨_, hw⟩); exact hvL; exact (Finset.mem_erase.mp haR).2; exact (Finset.mem_erase.mp hbR).2; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h; exact Or.inr (Or.inr (Or.inr ⟨h, hw⟩))
        · simp only [haR, hbR, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, dropIf, ite_true, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwb, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact (Finset.mem_erase.mp haR).2; exact absurd rfl hwb; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            intro hwb; subst hwb; exact hbR (Finset.mem_erase.mpr ⟨h, hw⟩)
        · simp only [haR, hbR, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, dropIf, ite_true, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwa, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact absurd rfl hwa; exact (Finset.mem_erase.mp hbR).2; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            intro hwa; subst hwa; exact haR (Finset.mem_erase.mpr ⟨h, hw⟩)
        · simp only [haR, hbR, decide_false, Bool.not_false, dropIf, ite_true, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwa, hwb, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact absurd rfl hwa; exact absurd rfl hwb; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, ?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            · intro hwa; subst hwa; exact haR (Finset.mem_erase.mpr ⟨h, hw⟩)
            · intro hwb; subst hwb; exact hbR (Finset.mem_erase.mpr ⟨h, hw⟩)
      refine ⟨k1 + 1, S, by simp only [List.length_cons]; omega, hSsub, ?_⟩
      apply LiveBin.step (a := a) (b := b) (op := op)
        (Finset.mem_insert_self a _) (Finset.mem_insert_of_mem (Finset.mem_insert_self b _))
        hab ha0 hb0 hop (hvEq ▸ hv0) (hvEq ▸ hvNotS) (decide (a ∈ R)) (decide (b ∈ R))
      rw [← hvEq, hL1eq]; exact hlive1
    · refine ⟨k1, L1, by simp only [List.length_cons]; omega, ?_, hlive1⟩
      intro w hw
      have h1 := hL1sub hw
      simp only [List.toFinset_cons, Finset.mem_insert] at h1
      rcases h1 with rfl | h1
      · have hvb : w ∈ bank := by by_contra hnb; exact hv ⟨hw, hnb⟩
        exact List.mem_toFinset.mpr hvb
      · exact h1

theorem extractLiveBin {mask goal : Nat} {stock vs : List Nat}
    (hg : goal ≠ 0) (hcs : ∀ w ∈ stock, canon mask w = w)
    (hbuild : BuildsBin mask stock vs) (hhit : Avail (vs ++ stock) goal) :
    ∃ k S, k ≤ vs.length ∧ S ⊆ stock.toFinset ∧ LiveBin mask goal k S := by
  have hmem : goal ∈ vs ++ stock := hhit.resolve_left hg
  have hsub : ({goal} : Finset Nat) ⊆ (vs ++ stock).toFinset := by
    intro w hw; rw [Finset.mem_singleton.mp hw]; exact List.mem_toFinset.mpr hmem
  obtain ⟨k, S, hk, hS, hL⟩ := extractLiveBin_aux hg vs stock 0 {goal} hbuild hcs hsub LiveBin.done
  exact ⟨k, S, by omega, hS, hL⟩

theorem liveBin_agrees {mask goal k p n : Nat} {S : Finset Nat}
    (hp : mask.testBit p = true) (hn : mask.testBit n = true)
    (h : LiveBin mask goal k S) (hag : ∀ w ∈ S, w.testBit p = w.testBit n) :
    goal.testBit p = goal.testBit n := by
  induction h with
  | done => exact hag goal (Finset.mem_singleton_self goal)
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    apply ih; intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · have ea := hag a ha
      have eb := hag b hb
      unfold binOp
      cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
      all_goals rw [canon_testBit_eq hp hn]
      all_goals simp [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, hp, hn, ea, eb]
    · exact hag w (dropIf_subset _ _ _ (dropIf_subset _ _ _ hw))

def forceW {α : Type} (w : Nat) (k : Nat → α) : α :=
  Nat.rec (k 0) (fun m _ => k (m + 1)) w

theorem forceW_eq {α : Type} (w : Nat) (k : Nat → α) : forceW w k = k w := by
  cases w <;> rfl

def forceWs (ws : List Nat) (k : List Nat → Bool) : Bool :=
  (List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun w _ next k => forceW w (fun v => next (fun rest => k (v :: rest)))) ws) k

theorem forceWs_eq (ws : List Nat) (k : List Nat → Bool) : forceWs ws k = k ws := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih =>
    change forceW w (fun v => forceWs ws (fun rest => k (v :: rest))) = _
    rw [forceW_eq, ih]

def dagPart (ws : List Nat) : Nat → Nat → Bool :=
  List.rec
    (fun p n => Nat.beq p 0 || Nat.beq n 0)
    (fun w _ rest p n =>
      (Nat.beq p 0 || Nat.beq n 0) ||
        forceW (p &&& w) (fun up =>
          forceW (n &&& w) (fun down =>
            rest up down &&
              forceW (p ^^^ up) (fun offP =>
                forceW (n ^^^ down) (rest offP))))) ws

theorem offBits {v w i : Nat} (h : (v ^^^ (v &&& w)).testBit i = true) :
    v.testBit i = true ∧ w.testBit i = false := by
  rw [Nat.testBit_xor, Nat.testBit_and] at h
  cases hv : v.testBit i <;> cases hw : w.testBit i <;> simp [hv, hw] at h ⊢

theorem dagPart_sound {ws : List Nat} {pos neg : Nat} (fail : dagPart ws pos neg = false) :
    ∃ p n, pos.testBit p = true ∧ neg.testBit n = true ∧ ∀ w ∈ ws, w.testBit p = w.testBit n := by
  have nonempty {w : Nat} (hn : w ≠ 0) : ∃ j, w.testBit j = true := by
    by_contra! all; apply hn; apply Nat.eq_of_testBit_eq; intro i; simp [all i]
  induction ws generalizing pos neg with
  | nil =>
    change (Nat.beq pos 0 || Nat.beq neg 0) = false at fail
    simp only [Bool.or_eq_false_iff] at fail
    obtain ⟨p, hp⟩ := nonempty (ne_of_beq_false fail.1)
    obtain ⟨n, hn⟩ := nonempty (ne_of_beq_false fail.2)
    exact ⟨p, n, hp, hn, by simp⟩
  | cons w ws ih =>
    change ((Nat.beq pos 0 || Nat.beq neg 0) ||
      forceW (pos &&& w) (fun up =>
        forceW (neg &&& w) (fun down =>
          dagPart ws up down &&
            forceW (pos ^^^ up) (fun offP =>
              forceW (neg ^^^ down) (dagPart ws offP))))) = false at fail
    simp only [forceW_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at fail
    rcases fail.2 with on | off
    · obtain ⟨p, n, hp, hn, ag⟩ := ih on
      rw [Nat.testBit_and, Bool.and_eq_true] at hp hn
      refine ⟨p, n, hp.1, hn.1, fun a ha => ?_⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · rw [hp.2, hn.2]
      · exact ag a ha
    · obtain ⟨p, n, hp, hn, ag⟩ := ih off
      have hp' := offBits hp
      have hn' := offBits hn
      refine ⟨p, n, hp'.1, hn'.1, fun a ha => ?_⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · rw [hp'.2, hn'.2]
      · exact ag a ha

theorem dagPart_live {mask goal k : Nat} {ws : List Nat}
    (hgm : Masked mask goal) (hlive : LiveBin mask goal k ws.toFinset) :
    dagPart ws goal (mask ^^^ goal) = true := by
  by_contra hf
  have hfalse : dagPart ws goal (mask ^^^ goal) = false := by
    cases h : dagPart ws goal (mask ^^^ goal) <;> simp_all
  obtain ⟨p, n, hp, hn, ag⟩ := dagPart_sound hfalse
  have hpm : mask.testBit p = true := by
    have e := congrArg (fun x => x.testBit p) hgm
    simp only [Nat.testBit_and, hp, Bool.true_and] at e; exact e
  have hnm : mask.testBit n = true ∧ goal.testBit n = false := by
    rw [Nat.testBit_xor] at hn
    have imp : goal.testBit n = true → mask.testBit n = true := by
      intro hg
      have e := congrArg (fun x => x.testBit n) hgm
      simp only [Nat.testBit_and, hg, Bool.true_and] at e; exact e
    cases hm : mask.testBit n <;> cases hg : goal.testBit n <;> simp_all
  have eq := liveBin_agrees hpm hnm.1 hlive (fun w hw => ag w (List.mem_toFinset.mp hw))
  rw [hp, hnm.2] at eq; exact Bool.noConfusion eq

def flatSet (cut : Nat) (S : Finset Nat) : Finset Nat :=
  S.filter (fun w => Nat.beq (canon cut w) 0)

theorem flatSet_insert_notMem {cut w : Nat} {S : Finset Nat} (hw : w ∉ S) :
    (flatSet cut (insert w S)).card =
      if canon cut w = 0 then (flatSet cut S).card + 1 else (flatSet cut S).card := by
  unfold flatSet
  rw [Finset.filter_insert]
  by_cases hc : canon cut w = 0
  · simp only [hc, Nat.beq_refl, ite_true]
    exact Finset.card_insert_of_notMem (fun h => hw (Finset.mem_filter.mp h).1)
  · simp only [beq_false_ne hc, Bool.false_eq_true, ite_false, hc]

theorem flatSet_erase {cut w : Nat} {S : Finset Nat} :
    (flatSet cut S).card ≤ (flatSet cut (S.erase w)).card + (if canon cut w = 0 then 1 else 0) := by
  unfold flatSet
  rw [Finset.filter_erase]
  by_cases hm : w ∈ S.filter (fun x => Nat.beq (canon cut x) 0)
  · have hcw : canon cut w = 0 := Nat.eq_of_beq_eq_true (Finset.mem_filter.mp hm).2
    have hcard := Finset.card_erase_add_one hm
    simp only [hcw, ite_true]; omega
  · rw [Finset.erase_eq_of_notMem hm]; omega

theorem maskedBuildBin {mask cut goal k : Nat} {S : Finset Nat}
    (sub : mask &&& cut = cut) (hgnf : canon cut goal ≠ 0)
    (h : LiveBin mask goal k S) :
    ∀ (bank : List Nat), (∀ w ∈ S, Avail bank (canon cut w)) →
      ∃ vs, vs.length + (flatSet cut S).card ≤ k ∧ BuildsBin cut bank vs ∧
        Avail (vs ++ bank) (canon cut goal) := by
  induction h with
  | done =>
    intro bank hsup
    have hfl : (flatSet cut {goal}).card = 0 := by
      unfold flatSet
      simp [hgnf]
    exact ⟨[], by simp [hfl], trivial, hsup goal (Finset.mem_singleton_self goal)⟩
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB tail ih =>
    intro bank hsup
    set z := binOp mask op a b
    set S1 := dropIf (!keepB) b S
    set S2 := dropIf (!keepA) a S1
    set S' := insert z S2
    have hS2sub : S2 ⊆ S := Finset.Subset.trans (dropIf_subset _ _ _) (dropIf_subset _ _ _)
    have hzNotS2 : z ∉ S2 := fun hm => hf (hS2sub hm)
    have hfl1 : (flatSet cut S).card ≤ (flatSet cut S1).card + (if canon cut b = 0 then 1 else 0) := by
      unfold S1 dropIf; split; exact flatSet_erase; omega
    have hfl2 : (flatSet cut S1).card ≤ (flatSet cut S2).card + (if canon cut a = 0 then 1 else 0) := by
      unfold S2 dropIf; split; exact flatSet_erase; omega
    have hfl3 : (flatSet cut S').card =
        if canon cut z = 0 then (flatSet cut S2).card + 1 else (flatSet cut S2).card :=
      flatSet_insert_notMem hzNotS2
    have hcz : canon cut z = 0 ∨ canon cut z = canon cut a ∨ canon cut z = canon cut b ∨
        ∃ op' < 4, canon cut z = binOp cut op' (canon cut a) (canon cut b) :=
      canon_sub_binOp sub
    by_cases hfa : canon cut a = 0
    · by_cases hfb : canon cut b = 0
      · have hfz : canon cut z = 0 := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact h
          · exact h.trans hfa
          · exact h.trans hfb
          · rw [hfa, hfb] at h
            rcases binOp_zero_left cut op' 0 with h0 | h0
            · exact h.trans h0
            · exact h.trans (h0.trans (canon_zero cut))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact Or.inl hfz
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, hfz, ite_true] at hfl1 hfl2 hfl3
        exact ⟨vs, by omega, hbd, hhit⟩
      · have hfz : canon cut z = 0 ∨ canon cut z = canon cut b := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact Or.inl h
          · exact Or.inl (h.trans hfa)
          · exact Or.inr h
          · rw [hfa] at h
            rcases binOp_zero_left cut op' (canon cut b) with h0 | h0
            · exact Or.inl (h.trans h0)
            · exact Or.inr (h.trans (h0.trans (canon_idem cut b)))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · rcases hfz with h0 | hb'
            · exact Or.inl h0
            · rw [hb']; exact hsup b hb
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, ite_true, ite_false] at hfl1 hfl2
        have : (flatSet cut S2).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        exact ⟨vs, by omega, hbd, hhit⟩
    · by_cases hfb : canon cut b = 0
      · have hfz : canon cut z = 0 ∨ canon cut z = canon cut a := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact Or.inl h
          · exact Or.inr h
          · exact Or.inl (h.trans hfb)
          · rw [hfb] at h
            rcases binOp_zero_right cut op' (canon cut a) with h0 | h0
            · exact Or.inl (h.trans h0)
            · exact Or.inr (h.trans (h0.trans (canon_idem cut a)))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · rcases hfz with h0 | ha'
            · exact Or.inl h0
            · rw [ha']; exact hsup a ha
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, ite_true, ite_false] at hfl1 hfl2
        have : (flatSet cut S2).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        exact ⟨vs, by omega, hbd, hhit⟩
      · simp only [hfa, hfb, ite_false] at hfl1 hfl2
        have hfl_le : (flatSet cut S).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        rcases hcz with h0 | ha' | hb' | ⟨op', hop', hbin⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · exact Or.inl h0
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · rw [ha']; exact hsup a ha
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · rw [hb']; exact hsup b hb
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · set cz := canon cut z
          have hgate : GateBin cut bank cz := ⟨canon cut a, canon cut b, op', hop', hsup a ha, hsup b hb, hbin⟩
          have hsup' : ∀ w ∈ S', Avail (cz :: bank) (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · exact Or.inr List.mem_cons_self
            · exact avail_weaken (fun u hu => List.mem_cons_of_mem _ hu) (hsup w (hS2sub hw))
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih (cz :: bank) hsup'
          refine ⟨cz :: vs, by simp only [List.length_cons]; omega, ⟨hgate, hbd⟩, ?_⟩
          exact avail_weaken (fun u hu => by simp only [List.mem_append, List.mem_cons] at hu ⊢; tauto) hhit

def flatCount (cut : Nat) (ws : List Nat) : Nat :=
  List.rec 0 (fun w _ cnt => bsel (Nat.beq (canon cut w) 0) (cnt + 1) cnt) ws

theorem flatCount_card (cut : Nat) {ws : List Nat} (nd : ws.Nodup) :
    flatCount cut ws = (flatSet cut ws.toFinset).card := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hnd := List.nodup_cons.mp nd
    have fresh : w ∉ ws.toFinset := by simpa using hnd.1
    change bsel (Nat.beq (canon cut w) 0) (flatCount cut ws + 1) (flatCount cut ws) = _
    rw [List.toFinset_cons, flatSet_insert_notMem fresh, ih hnd.2]
    by_cases hc : canon cut w = 0
    · simp [hc, bsel]
    · rw [beq_false_ne hc, bsel_false]; simp [hc]

def availB (bank : List Nat) (w : Nat) : Bool :=
  Nat.beq w 0 || bank.contains w

theorem availB_spec {bank : List Nat} {w : Nat} : availB bank w = true ↔ Avail bank w := by
  unfold availB Avail; simp [Nat.beq_eq]

def recipeGateBin (cut : Nat) (bank : List Nat) (vc ac bc : Nat) : Bool :=
  availB bank ac && availB bank bc &&
    (Nat.beq vc (binOp cut 0 ac bc) || Nat.beq vc (binOp cut 1 ac bc) ||
     Nat.beq vc (binOp cut 2 ac bc) || Nat.beq vc (binOp cut 3 ac bc))

theorem recipeGateBin_spec {cut : Nat} {bank : List Nat} {vc ac bc : Nat}
    (h : recipeGateBin cut bank vc ac bc = true) : GateBin cut bank vc := by
  unfold recipeGateBin at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, availB_spec] at h
  obtain ⟨⟨ha, hb⟩, ((h0 | h1) | h2) | h3⟩ := h
  · exact ⟨ac, bc, 0, by omega, ha, hb, h0⟩
  · exact ⟨ac, bc, 1, by omega, ha, hb, h1⟩
  · exact ⟨ac, bc, 2, by omega, ha, hb, h2⟩
  · exact ⟨ac, bc, 3, by omega, ha, hb, h3⟩

def addUniq (w : Nat) (l : List Nat) : List Nat :=
  if l.contains w then l else w :: l

def recipeStart (cut : Nat) (stock ws : List Nat) : List Nat :=
  List.rec [] (fun w _ acc =>
    let v := canon cut w
    if availB stock v then acc else addUniq v acc) ws

def recipeClose (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun (w, a, b) _ next acc =>
      let v := canon cut w
      if acc.contains v then
        let va := canon cut a
        let vb := canon cut b
        let acc1 := if availB stock va then acc else addUniq va acc
        let acc2 := if availB stock vb then acc1 else addUniq vb acc1
        next acc2
      else next acc) hist needed

def replayRec (cut : Nat) (needed : List Nat) (hist : List (Nat × Nat × Nat)) (bank : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun _ => [])
    (fun (w, a, b) _ next bank =>
      let v := canon cut w
      if needed.contains v && !(availB bank v) && recipeGateBin cut bank v (canon cut a) (canon cut b) then
        v :: next (v :: bank)
      else next bank) hist bank

theorem replayRec_builds (cut : Nat) (needed : List Nat) (hist : List (Nat × Nat × Nat)) (bank : List Nat) :
    BuildsBin cut bank (replayRec cut needed hist bank) := by
  induction hist generalizing bank with
  | nil => trivial
  | cons rec hist ih =>
    obtain ⟨w, a, b⟩ := rec
    change BuildsBin cut bank
      (if needed.contains (canon cut w) && !(availB bank (canon cut w)) &&
          recipeGateBin cut bank (canon cut w) (canon cut a) (canon cut b) then
        canon cut w :: replayRec cut needed hist (canon cut w :: bank)
      else replayRec cut needed hist bank)
    split
    · rename_i hyes
      exact ⟨recipeGateBin_spec (Bool.and_eq_true_iff.mp hyes).2, ih _⟩
    · exact ih _

def boundCloses (target : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat))
    (bound : Nat × List Nat × Nat × Nat) : Bool :=
  let (cut, stock, lower, goal) := bound
  let (fuel, ws, hist) := state
  Nat.beq (canon cut target) goal && !(Nat.beq goal 0) &&
    forceW (fuel - flatCount cut ws) (fun rem =>
      if Nat.blt rem lower then
        forceWs (recipeStart cut stock ws) (fun start =>
          if Nat.blt (start.length + rem) lower then
            forceWs (recipeClose cut stock hist start) (fun needed =>
              if Nat.blt (needed.length + rem) lower then
                forceWs (replayRec cut needed hist.reverse stock) (fun replay =>
                  Nat.blt (replay.length + rem) lower &&
                    ws.all (fun w => availB (replay ++ stock) (canon cut w)))
              else false)
          else false)
      else false)

def knownCloses (target : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  List.rec false (fun b _ rest => boundCloses target state b || rest) bounds

def KnownBin (bounds : List (Nat × List Nat × Nat × Nat)) : Prop :=
  ∀ b ∈ bounds, LowerBin b.1 b.2.1 b.2.2.2 b.2.2.1

theorem boundCloses_sound {mask goal : Nat} {state : Nat × List Nat × List (Nat × Nat × Nat)}
    {bound : Nat × List Nat × Nat × Nat}
    (hlow : LowerBin bound.1 bound.2.1 bound.2.2.2 bound.2.2.1)
    (sub : mask &&& bound.1 = bound.1)
    (nd : state.2.1.Nodup) {k : Nat} (hk : k ≤ state.1)
    (hlive : LiveBin mask goal k state.2.1.toFinset) :
    boundCloses goal state bound = false := by
  obtain ⟨fuel, ws, hist⟩ := state
  obtain ⟨cut, stock, lower, bgoal⟩ := bound
  dsimp only at hlow sub nd hk hlive
  apply Bool.eq_false_iff.mpr
  intro hc
  unfold boundCloses at hc
  simp only [forceW_eq, forceWs_eq, Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hc
  obtain ⟨⟨hgeq, hgnz⟩, scan⟩ := hc
  have hgnz' : bgoal ≠ 0 := ne_of_beq_false hgnz
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  simp only [Bool.and_eq_true, Nat.blt_eq] at scan
  obtain ⟨hlen, hsrc⟩ := scan
  set replay := replayRec cut (recipeClose cut stock hist (recipeStart cut stock ws)) hist.reverse stock
  have hgnf : canon cut goal ≠ 0 := hgeq.symm ▸ hgnz'
  have hsup : ∀ w ∈ ws.toFinset, Avail (replay ++ stock) (canon cut w) := by
    intro w hw
    exact availB_spec.mp (List.all_eq_true.mp hsrc w (List.mem_toFinset.mp hw))
  obtain ⟨ys, hylen, hybd, hyhit⟩ := maskedBuildBin sub hgnf hlive (replay ++ stock) hsup
  rw [← flatCount_card cut nd] at hylen
  have hboth := builds_append (replayRec_builds cut _ hist.reverse stock) hybd
  have hfinal : Avail ((replay ++ ys) ++ stock) bgoal := by
    rw [← hgeq]
    exact avail_weaken (fun u hu => by simp only [List.mem_append] at hu ⊢; tauto) hyhit
  have heno := hlow (replay ++ ys) hboth hfinal
  simp only [List.length_append] at heno
  omega

theorem knownCloses_sound {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    {state : Nat × List Nat × List (Nat × Nat × Nat)}
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (nd : state.2.1.Nodup) {k : Nat} (hk : k ≤ state.1)
    (hlive : LiveBin mask goal k state.2.1.toFinset) :
    knownCloses goal bounds state = false := by
  induction bounds with
  | nil => rfl
  | cons b bs ih =>
    change (boundCloses goal state b || knownCloses goal bs state) = false
    rw [boundCloses_sound (hknown b List.mem_cons_self) (hsub b List.mem_cons_self) nd hk hlive]
    exact ih (fun x hx => hknown x (List.mem_cons_of_mem _ hx)) (fun x hx => hsub x (List.mem_cons_of_mem _ hx))

def insertSorted (x : Nat) (l : List Nat) : List Nat :=
  List.rec [x] (fun y ys ih => bsel (Nat.ble x y) (x :: y :: ys) (y :: ih)) l

theorem insertSorted_mem {x w : Nat} {l : List Nat} :
    w ∈ insertSorted x l ↔ w = x ∨ w ∈ l := by
  induction l with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    change w ∈ bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys) ↔ _
    cases Nat.ble x y
    · rw [bsel_false]; simp only [List.mem_cons, ih]; tauto
    · rw [bsel_true]; simp only [List.mem_cons]

theorem insertSorted_nodup {x : Nat} {l : List Nat} (hx : x ∉ l) (nd : l.Nodup) :
    (insertSorted x l).Nodup := by
  induction l with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    have hnd := List.nodup_cons.mp nd
    have hxy : x ≠ y := fun h => hx (h ▸ List.mem_cons_self)
    have hxs : x ∉ ys := fun h => hx (List.mem_cons_of_mem _ h)
    change (bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys)).Nodup
    cases Nat.ble x y
    · rw [bsel_false]
      apply List.nodup_cons.mpr
      refine ⟨fun hm => ?_, ih hxs hnd.2⟩
      rcases insertSorted_mem.mp hm with h | h
      · exact hxy h.symm
      · exact hnd.1 h
    · rw [bsel_true]; exact List.nodup_cons.mpr ⟨hx, nd⟩

def dropVal (drop : Bool) (x : Nat) (l : List Nat) : List Nat :=
  bsel drop (List.rec [] (fun y _ ih => bsel (Nat.beq y x) ih (y :: ih)) l) l

theorem dropVal_mem {drop : Bool} {x w : Nat} {l : List Nat} :
    w ∈ dropVal drop x l ↔ w ∈ l ∧ (drop = true → w ≠ x) := by
  cases drop
  · simp [dropVal, bsel]
  · induction l with
    | nil => simp [dropVal, bsel]
    | cons y ys ih =>
      change w ∈ bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys) ↔ _
      cases hb : Nat.beq y x
      · rw [bsel_false]
        have hne : y ≠ x := ne_of_beq_false hb
        simp only [List.mem_cons, ih, true_implies]
        constructor
        · rintro (rfl | ⟨hw, hwx⟩); exact ⟨Or.inl rfl, hne⟩; exact ⟨Or.inr hw, hwx⟩
        · rintro ⟨rfl | hw, hwx⟩; exact Or.inl rfl; exact Or.inr ⟨hw, hwx⟩
      · rw [bsel_true]
        have heq : y = x := Nat.eq_of_beq_eq_true hb
        subst heq
        simp only [List.mem_cons, ih, true_implies]
        constructor
        · rintro ⟨hw, hwx⟩; exact ⟨Or.inr hw, hwx⟩
        · rintro ⟨rfl | hw, hwx⟩; exact absurd rfl hwx; exact ⟨hw, hwx⟩

theorem dropVal_nodup {drop : Bool} {x : Nat} {l : List Nat} (nd : l.Nodup) :
    (dropVal drop x l).Nodup := by
  cases drop
  · exact nd
  · induction l with
    | nil => simp [dropVal, bsel]
    | cons y ys ih =>
      have hnd := List.nodup_cons.mp nd
      change (bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys)).Nodup
      cases Nat.beq y x
      · rw [bsel_false]
        exact List.nodup_cons.mpr ⟨fun hm => hnd.1 (dropVal_mem.mp hm).1, ih hnd.2⟩
      · rw [bsel_true]; exact ih hnd.2

theorem dropVal_toFinset (drop : Bool) (x : Nat) (l : List Nat) :
    (dropVal drop x l).toFinset = dropIf drop x l.toFinset := by
  ext w; simp only [List.mem_toFinset, dropVal_mem, dropIf]
  cases drop <;> simp [Finset.mem_erase, and_comm]

def subsetWords (stock : List Nat) (bits : Nat) : List Nat :=
  (List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun w _ ih b =>
      let rest := ih (b >>> 1)
      bsel (Nat.beq (b &&& 1) 1) (insertSorted w rest) rest) stock) bits

theorem subsetWords_subset (stock : List Nat) (bits : Nat) :
    ∀ w ∈ subsetWords stock bits, w ∈ stock := by
  induction stock generalizing bits with
  | nil => intro w hw; simp [subsetWords] at hw
  | cons x xs ih =>
    intro w hw
    change w ∈ bsel (Nat.beq (bits &&& 1) 1)
      (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1)) at hw
    cases hb : Nat.beq (bits &&& 1) 1
    · rw [hb, bsel_false] at hw; exact List.mem_cons_of_mem _ (ih _ w hw)
    · rw [hb, bsel_true] at hw
      rcases insertSorted_mem.mp hw with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih _ w hm)

theorem subsetWords_nodup {stock : List Nat} (nd : stock.Nodup) (bits : Nat) :
    (subsetWords stock bits).Nodup := by
  induction stock generalizing bits with
  | nil => simp [subsetWords]
  | cons x xs ih =>
    have hnd := List.nodup_cons.mp nd
    change (bsel (Nat.beq (bits &&& 1) 1)
      (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1))).Nodup
    cases Nat.beq (bits &&& 1) 1
    · rw [bsel_false]; exact ih hnd.2 _
    · rw [bsel_true]; exact insertSorted_nodup (fun hm => hnd.1 (subsetWords_subset xs _ x hm)) (ih hnd.2 _)

theorem exists_subsetToken (stock : List Nat) (S : Finset Nat) :
    ∃ bits < 2 ^ stock.length, (subsetWords stock bits).toFinset = S ∩ stock.toFinset := by
  induction stock with
  | nil => exact ⟨0, by simp, by simp [subsetWords]⟩
  | cons x xs ih =>
    obtain ⟨b, hb, heq⟩ := ih
    by_cases hx : x ∈ S
    · refine ⟨2 * b + 1, by simp only [List.length_cons, Nat.pow_succ]; omega, ?_⟩
      have hdiv : (2 * b + 1) >>> 1 = b := by change (2 * b + 1) / 2 = b; omega
      have hmod : ((2 * b + 1) &&& 1) = 1 := by rw [Nat.and_one_is_mod]; omega
      change (bsel (Nat.beq ((2 * b + 1) &&& 1) 1)
        (insertSorted x (subsetWords xs ((2 * b + 1) >>> 1)))
        (subsetWords xs ((2 * b + 1) >>> 1))).toFinset = _
      rw [hdiv, hmod, Nat.beq_refl, bsel_true]
      ext w; simp only [List.mem_toFinset, insertSorted_mem, Finset.mem_inter, List.toFinset_cons, Finset.mem_insert]
      have hw : w ∈ subsetWords xs b ↔ w ∈ S ∧ w ∈ xs := by
        have e := congrArg (fun t => w ∈ t) heq; simpa [List.mem_toFinset] using e
      rw [hw]; constructor
      · rintro (rfl | ⟨hs, hxs⟩); exact ⟨hx, Or.inl rfl⟩; exact ⟨hs, Or.inr hxs⟩
      · rintro ⟨hs, rfl | hxs⟩; exact Or.inl rfl; exact Or.inr ⟨hs, hxs⟩
    · refine ⟨2 * b, by simp only [List.length_cons, Nat.pow_succ]; omega, ?_⟩
      have hdiv : (2 * b) >>> 1 = b := by change (2 * b) / 2 = b; omega
      have hmod : ((2 * b) &&& 1) = 0 := by rw [Nat.and_one_is_mod]; omega
      change (bsel (Nat.beq ((2 * b) &&& 1) 1)
        (insertSorted x (subsetWords xs ((2 * b) >>> 1)))
        (subsetWords xs ((2 * b) >>> 1))).toFinset = _
      rw [hdiv, hmod]
      change (subsetWords xs b).toFinset = _
      ext w; simp only [List.mem_toFinset, Finset.mem_inter, List.toFinset_cons, Finset.mem_insert]
      have hw : w ∈ subsetWords xs b ↔ w ∈ S ∧ w ∈ xs := by
        have e := congrArg (fun t => w ∈ t) heq; simpa [List.mem_toFinset] using e
      rw [hw]; constructor
      · rintro ⟨hs, hxs⟩; exact ⟨hs, Or.inr hxs⟩
      · rintro ⟨hs, rfl | hxs⟩; exact absurd hs hx; exact ⟨hs, hxs⟩

def rootState (stock : List Nat) (fuel token : Nat) : Nat × List Nat × List (Nat × Nat × Nat) :=
  (fuel, subsetWords stock token, [])

def makeToken (a b op keep : Nat) : Nat := ((a * 16 + b) * 4 + op) * 4 + keep

def childState (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  let (fuel, ws, hist) := state
  let keep := token &&& 3
  let op := (token >>> 2) &&& 3
  let b := (token >>> 4) &&& 15
  let a := token >>> 8
  if Nat.beq fuel 0 || !(Nat.blt a b) || !(Nat.blt b ws.length) then none
  else
    let x := ws.getD a 0
    let y := ws.getD b 0
    let z := binOp mask op x y
    if Nat.beq z 0 || ws.contains z then none
    else
      let keepA := Nat.beq (keep &&& 1) 1
      let keepB := Nat.beq ((keep >>> 1) &&& 1) 1
      let rest := dropVal (!keepA) x (dropVal (!keepB) y ws)
      some (fuel - 1, insertSorted z rest, (z, x, y) :: hist)

theorem childState_wf {mask token : Nat} {st ch : Nat × List Nat × List (Nat × Nat × Nat)}
    (nd : st.2.1.Nodup) (h : childState mask token st = some ch) :
    ch.1 < st.1 ∧ ch.2.1.Nodup := by
  obtain ⟨fuel, ws, hist⟩ := st
  dsimp only at nd
  unfold childState at h; dsimp only at h
  split at h
  · contradiction
  · rename_i hok
    split at h
    · contradiction
    · rename_i hfresh
      have heq := Option.some.inj h
      subst ch
      simp only [Bool.or_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hok hfresh
      have hfpos : fuel ≠ 0 := fun hf => hok (Or.inl (Or.inl hf))
      have hznot : ¬(ws.contains (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0)
          (ws.getD ((token >>> 4) &&& 15) 0)) = true) := fun hm => hfresh (Or.inr hm)
      refine ⟨by dsimp; omega, ?_⟩
      apply insertSorted_nodup
      · intro hm
        have hmem := (dropVal_mem.mp (dropVal_mem.mp hm).1).1
        exact hznot (List.contains_iff_mem.mpr hmem)
      · exact dropVal_nodup (dropVal_nodup nd)

def dagTrace (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
    (fun _ prev j =>
      let (parent, token) := forest j
      if Nat.beq parent 0 then
        if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
      else (prev (parent - 1)).bind (childState mask token)) (fuel + 1)) i

theorem dagTrace_nodup {mask fuel : Nat} {stock : List Nat} {forest : Nat → Nat × Nat}
    (nd : stock.Nodup) {i : Nat} {st : Nat × List Nat × List (Nat × Nat × Nat)}
    (h : dagTrace mask stock fuel forest i = some st) : st.2.1.Nodup := by
  unfold dagTrace at h
  suffices ∀ steps j s,
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) steps) j = some s → s.2.1.Nodup from
    this (fuel + 1) i st h
  intro steps
  induction steps with
  | zero => intro j s h; contradiction
  | succ n ih =>
    intro j s h; dsimp only at h
    split at h
    · split at h
      · have e := Option.some.inj h; subst s; exact subsetWords_nodup nd _
      · contradiction
    · cases hp : (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) n) ((forest j).1 - 1) with
      | none => rw [hp] at h; contradiction
      | some p => rw [hp] at h; exact (childState_wf (ih _ _ hp) h).2

def dagLocal (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  let (fuel, ws, _) := state
  Nat.blt (fuel + 1) ws.length ||
    !(dagPart ws goal (mask ^^^ goal)) ||
    knownCloses goal bounds state

theorem dagLocal_open {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    {state : Nat × List Nat × List (Nat × Nat × Nat)}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (nd : state.2.1.Nodup) {k : Nat} (hk : k ≤ state.1)
    (hlive : LiveBin mask goal k state.2.1.toFinset) :
    dagLocal mask goal bounds state = false := by
  obtain ⟨fuel, ws, hist⟩ := state
  dsimp only at nd hk hlive
  unfold dagLocal
  have hcard : ws.length ≤ fuel + 1 := by
    have := liveBin_card_le hlive
    rw [List.toFinset_card_of_nodup nd] at this; omega
  have h1 : Nat.blt (fuel + 1) ws.length = false := by
    cases h : Nat.blt (fuel + 1) ws.length; rfl; have := Nat.blt_eq.mp h; omega
  have h2 : dagPart ws goal (mask ^^^ goal) = true := dagPart_live hgm hlive
  have h3 : knownCloses goal bounds (fuel, ws, hist) = false :=
    knownCloses_sound hknown hsub nd hk hlive
  simp [h1, h2, h3]

def treeBlock (lo hi : Nat) (f : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ next a b =>
      if Nat.blt a b then
        let m := (a + b) / 2
        if Nat.beq a m then f a else next a m && next m b
      else true) (hi - lo + 1)) lo hi

theorem treeBlock_at {lo hi : Nat} {f : Nat → Bool} (h : treeBlock lo hi f = true) :
    ∀ {i : Nat}, lo ≤ i → i < hi → f i = true := by
  unfold treeBlock at h
  suffices ∀ steps a b, b - a ≤ steps →
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          if Nat.blt x y then
            let m := (x + y) / 2
            if Nat.beq x m then f x else next x m && next m y
          else true) steps) a b = true →
      ∀ i, a ≤ i → i < b → f i = true by
    intro i h1 h2; exact this (hi - lo + 1) lo hi (by omega) h i h1 h2
  intro steps
  induction steps with
  | zero => intro a b hba _ i h1 h2; omega
  | succ s ih =>
    intro a b hba h i h1 h2
    dsimp only at h
    have hab : Nat.blt a b = true := Nat.blt_eq.mpr (by omega)
    simp only [hab, ite_true] at h
    set m := (a + b) / 2
    by_cases ham : a = m
    · have hbm : Nat.beq a m = true := Nat.beq_eq.mpr ham
      simp only [hbm, ite_true] at h
      have hia : i = a := by omega
      subst hia; exact h
    · have hbm : Nat.beq a m = false := beq_false_ne ham
      simp only [hbm, Bool.false_eq_true, ite_false] at h
      rcases Bool.and_eq_true_iff.mp h with ⟨hl, hr⟩
      by_cases him : i < m
      · exact ih a m (by omega) hl i h1 him
      · exact ih m b (by omega) hr i (by omega) h2

theorem block_join {a m b : Nat} {f : Nat → Bool}
    (h1 : ∀ i, a ≤ i → i < m → f i = true)
    (h2 : ∀ i, m ≤ i → i < b → f i = true) :
    ∀ i, a ≤ i → i < b → f i = true := by
  intro i hi1 hi2
  by_cases h : i < m
  · exact h1 i hi1 h
  · exact h2 i (by omega) hi2

def dagRef (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (parent token : Nat)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  match links parent token with
  | none => false
  | some dest =>
    Nat.blt dest count &&
      match states dest with
      | none => false
      | some saved => Nat.beq saved.1 state.1 && (saved.2.1 == state.2.1)

def dagCheckChildren (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  let (fuel, ws, hist) := state
  let n := ws.length
  !(ws.contains goal) &&
    (Nat.beq fuel 0 ||
      (Nat.blt n 17 &&
        treeBlock 0 n (fun a =>
          let x := ws.getD a 0
          treeBlock (a + 1) n (fun b =>
            let y := ws.getD b 0
            treeBlock 0 4 (fun op =>
              forceW (binOp mask op x y) (fun z =>
                Nat.beq z 0 || ws.contains z ||
                  treeBlock 0 4 (fun keep =>
                    let keepA := Nat.beq (keep &&& 1) 1
                    let keepB := Nat.beq ((keep >>> 1) &&& 1) 1
                    let newLen := n - 1 + (if keepA then 1 else 0) + (if keepB then 1 else 0)
                    Nat.blt fuel newLen ||
                      forceWs (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))) (fun ws' =>
                        let ch := (fuel - 1, ws', (z, x, y) :: hist)
                        dagLocal mask goal bounds ch || ref (makeToken a b op keep) ch))))))))

def dagCheckNode (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some st => dagCheckChildren mask goal bounds (dagRef count states links (i + 1)) st

def dagCheckRoots (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (stock : List Nat) (fuel : Nat) : Bool :=
  treeBlock 0 (2 ^ stock.length) (fun token =>
    forceWs (subsetWords stock token) (fun ws =>
      let st := (fuel, ws, [])
      dagLocal mask goal bounds st || ref token st))

theorem getElem_index_lt {l : List Nat} {x : Nat} (hx : x ∈ l) :
    ∃ i < l.length, l.getD i 0 = x := by
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hx
  refine ⟨i, hi, ?_⟩
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, heq]

theorem list_len_child {x y z : Nat} {ws : List Nat} {keepA keepB : Bool}
    (nd : ws.Nodup) (hx : x ∈ ws) (hy : y ∈ ws) (hxy : x ≠ y) (hz : z ∉ ws) :
    (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).length =
      ws.length - 1 + (if keepA then 1 else 0) + (if keepB then 1 else 0) := by
  have nd' : (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).Nodup :=
    insertSorted_nodup (fun hm => hz (dropVal_mem.mp (dropVal_mem.mp hm).1).1) (dropVal_nodup (dropVal_nodup nd))
  have h1 := List.toFinset_card_of_nodup nd'
  have h2 := List.toFinset_card_of_nodup nd
  have hset : (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).toFinset =
      insert z (dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset)) := by
    ext w
    simp only [List.mem_toFinset, insertSorted_mem, Finset.mem_insert, ← dropVal_toFinset]
  rw [hset] at h1
  have hz' : z ∉ dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset) :=
    fun hm => hz (List.mem_toFinset.mp (dropIf_subset _ _ _ (dropIf_subset _ _ _ hm)))
  rw [Finset.card_insert_of_notMem hz'] at h1
  set T := dropIf (!keepB) y ws.toFinset
  have hxb : x ∈ T := by
    unfold T dropIf; split
    · exact Finset.mem_erase.mpr ⟨hxy, List.mem_toFinset.mpr hx⟩
    · exact List.mem_toFinset.mpr hx
  have hcb : T.card = ws.toFinset.card - (if keepB then 0 else 1) := by
    unfold T dropIf; cases keepB
    · have := Finset.card_erase_add_one (List.mem_toFinset.mpr hy); simp; omega
    · simp
  have hca : (dropIf (!keepA) x T).card = T.card - (if keepA then 0 else 1) := by
    unfold dropIf; cases keepA
    · have := Finset.card_erase_add_one hxb; simp only [Bool.not_false, Bool.false_eq_true, ite_true, ite_false]; omega
    · simp
  have hlen2 : 2 ≤ ws.toFinset.card := by
    have hsub : ({x, y} : Finset Nat) ⊆ ws.toFinset := by
      intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
      · exact List.mem_toFinset.mpr hx
      · rw [Finset.mem_singleton.mp hw]; exact List.mem_toFinset.mpr hy
    have hpair : ({x, y} : Finset Nat).card = 2 := Finset.card_pair hxy
    have := Finset.card_le_card hsub; omega
  rw [← h1, hca, hcb, h2]
  cases keepA <;> cases keepB <;> simp <;> omega

theorem dagAllNodes {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {links : Nat → Nat → Option Nat}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1) (snd : stock.Nodup)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNode mask goal bounds count
      (dagTrace mask stock fuel forest) links i = true) :
    ∀ cap i st, i < count → dagTrace mask stock fuel forest i = some st →
      st.1 = cap → ∀ k, k ≤ cap → ¬LiveBin mask goal k st.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i st hi htr hcap k hk hlive
    obtain ⟨rem, ws, hist⟩ := st
    dsimp only at hcap hlive
    have nd : ws.Nodup := dagTrace_nodup snd htr
    have hchk := hnodes i (Nat.zero_le i) hi
    unfold dagCheckNode at hchk
    rw [htr] at hchk
    unfold dagCheckChildren at hchk
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, Nat.beq_eq, Nat.blt_eq] at hchk
    obtain ⟨hnohit, hstep⟩ := hchk
    generalize hS : ws.toFinset = S at hlive
    cases hlive with
    | done =>
      have hgm' : goal ∈ ws := List.mem_toFinset.mp (hS.symm ▸ Finset.mem_singleton_self goal)
      have hc : ws.contains goal = true := List.contains_iff_mem.mpr hgm'
      rw [hc] at hnohit; exact Bool.noConfusion hnohit
    | @step k' _ a0 b0 op0 ha0 hb0 hab0 _ _ hop0 hz0 hf0 keepA0 keepB0 tail0 =>
      rw [← hS] at ha0 hb0 hf0 tail0
      have hrem_pos : rem ≠ 0 := by omega
      rcases hstep with hrem0 | ⟨hn17, hblock⟩
      · exact hrem_pos hrem0
      · have haM : a0 ∈ ws := List.mem_toFinset.mp ha0
        have hbM : b0 ∈ ws := List.mem_toFinset.mp hb0
        obtain ⟨ia0, hia0, hea0⟩ := getElem_index_lt haM
        obtain ⟨ib0, hib0, heb0⟩ := getElem_index_lt hbM
        have hiab_ne : ia0 ≠ ib0 := fun heq => hab0 (hea0.symm.trans (heq ▸ heb0))
        have ⟨a, b, op, keepA, keepB, ha_lt, hab_lt, hb_lt, hop_lt, hax, hby, hzeq, htail⟩ :
            ∃ a b op keepA keepB, a < ws.length ∧ a < b ∧ b < ws.length ∧ op < 4 ∧
              ws.getD a 0 = (if ia0 < ib0 then a0 else b0) ∧
              ws.getD b 0 = (if ia0 < ib0 then b0 else a0) ∧
              binOp mask op (ws.getD a 0) (ws.getD b 0) = binOp mask op0 a0 b0 ∧
              LiveBin mask goal k' (insert (binOp mask op (ws.getD a 0) (ws.getD b 0))
                (dropIf (!keepA) (ws.getD a 0) (dropIf (!keepB) (ws.getD b 0) ws.toFinset))) := by
          by_cases hlt : ia0 < ib0
          · exact ⟨ia0, ib0, op0, keepA0, keepB0, hia0, hlt, hib0, hop0,
              by simp only [hlt, ite_true]; exact hea0,
              by simp only [hlt, ite_true]; exact heb0,
              by rw [hea0, heb0], by rw [hea0, heb0]; exact tail0⟩
          · obtain ⟨op1, hop1, hopEq⟩ := binOp_comm mask op0 a0 b0 hop0
            have hswap : dropIf (!keepB0) b0 (dropIf (!keepA0) a0 ws.toFinset) =
                dropIf (!keepA0) a0 (dropIf (!keepB0) b0 ws.toFinset) := by
              ext w; simp only [dropIf]; cases keepA0 <;> cases keepB0 <;> simp [Finset.mem_erase, and_left_comm]
            exact ⟨ib0, ia0, op1, keepB0, keepA0, hib0, by omega, hia0, hop1,
              by simp only [hlt, ite_false]; exact heb0,
              by simp only [hlt, ite_false]; exact hea0,
              by rw [hea0, heb0, hopEq],
              by rw [hea0, heb0, ← hopEq, hswap]; exact tail0⟩
        set x := ws.getD a 0
        set y := ws.getD b 0
        set z := binOp mask op x y
        set keep := (if keepA then 1 else 0) + (if keepB then 2 else 0)
        have hkeep_lt : keep < 4 := by cases keepA <;> cases keepB <;> simp [keep]
        have hkA : Nat.beq (keep &&& 1) 1 = keepA := by cases keepA <;> cases keepB <;> decide
        have hkB : Nat.beq ((keep >>> 1) &&& 1) 1 = keepB := by cases keepA <;> cases keepB <;> decide
        have hkA' : (keep &&& 1 = 1) ↔ keepA = true := by cases keepA <;> cases keepB <;> decide
        have hkB' : ((keep >>> 1) &&& 1 = 1) ↔ keepB = true := by cases keepA <;> cases keepB <;> decide
        have hA := treeBlock_at hblock (Nat.zero_le a) ha_lt
        have hB := treeBlock_at hA (by omega : a + 1 ≤ b) hb_lt
        have hO := treeBlock_at hB (Nat.zero_le op) hop_lt
        simp only [forceW_eq, Bool.or_eq_true, Nat.beq_eq] at hO
        have hznz : z ≠ 0 := hzeq.symm ▸ hz0
        have hznm : ws.contains z = false := by
          cases h : ws.contains z
          · rfl
          · exact absurd (List.mem_toFinset.mpr (List.contains_iff_mem.mp h)) (hzeq.symm ▸ hf0)
        rcases hO with (hz' | hcm) | hK
        · exact hznz hz'
        · rw [hznm] at hcm; exact Bool.noConfusion hcm
        · have hKe := treeBlock_at hK (Nat.zero_le keep) hkeep_lt
          simp only [hkA, hkB, hkA', hkB', forceWs_eq, Bool.or_eq_true, Nat.blt_eq] at hKe
          set ws' := insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))
          have hxM : x ∈ ws := by simp only [x, hax]; split; exact haM; exact hbM
          have hyM : y ∈ ws := by simp only [y, hby]; split; exact hbM; exact haM
          have hxy : x ≠ y := by simp only [x, y, hax, hby]; split; exact hab0; exact hab0.symm
          have hzNotW : z ∉ ws := fun hm => by
            have := List.contains_iff_mem.mpr hm; rw [hznm] at this; exact Bool.noConfusion this
          have hnd' : ws'.Nodup :=
            insertSorted_nodup (fun hm => hzNotW (dropVal_mem.mp (dropVal_mem.mp hm).1).1) (dropVal_nodup (dropVal_nodup nd))
          have hset' : ws'.toFinset = insert z (dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset)) := by
            ext w; simp only [ws', List.mem_toFinset, insertSorted_mem, Finset.mem_insert, ← dropVal_toFinset]
          have hlive' : LiveBin mask goal k' ws'.toFinset := by rwa [hset']
          have hlen' := list_len_child (z := z) (keepA := keepA) (keepB := keepB) nd hxM hyM hxy hzNotW
          have hcard' : ws'.length ≤ rem := by
            have := liveBin_card_le hlive'
            rw [List.toFinset_card_of_nodup hnd'] at this; omega
          rcases hKe with hwide | hloc | href
          · change ws'.length = _ at hlen'; rw [← hlen'] at hwide; omega
          · have hopen := dagLocal_open (state := (rem - 1, ws', (z, x, y) :: hist)) hgm hknown hsub hnd' (k := k') (by omega) hlive'
            rw [hopen] at hloc; exact Bool.noConfusion hloc
          · unfold dagRef at href
            split at href
            · contradiction
            · rename_i dest _
              simp only [Bool.and_eq_true, Nat.blt_eq] at href
              obtain ⟨hdest, hst⟩ := href
              cases htr2 : dagTrace mask stock fuel forest dest with
              | none => rw [htr2] at hst; contradiction
              | some saved =>
                rw [htr2] at hst
                simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at hst
                obtain ⟨hfEq, hwEq⟩ := hst
                have hbelow : rem - 1 < cap := by omega
                exact ih (rem - 1) hbelow dest saved hdest htr2 hfEq k' (by omega) (hwEq ▸ hlive')

theorem lowerDag {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {links : Nat → Nat → Option Nat}
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hroots : dagCheckRoots mask goal bounds
      (dagRef count (dagTrace mask stock fuel forest) links 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNode mask goal bounds count
      (dagTrace mask stock fuel forest) links i = true) :
    LowerBin mask stock goal (fuel + 1) := by
  intro vs hbuild hhit
  by_contra! hlt
  have hcs' : ∀ w ∈ stock, canon mask w = w := fun w hw =>
    Nat.beq_eq.mp (List.all_eq_true.mp hcs w hw)
  obtain ⟨k, S, hk, hSsub, hlive⟩ := extractLiveBin hgnz hcs' hbuild hhit
  obtain ⟨tok, htok, hteq⟩ := exists_subsetToken stock S
  rw [Finset.inter_eq_left.mpr hSsub] at hteq
  have hchk := treeBlock_at hroots (Nat.zero_le tok) htok
  simp only [forceWs_eq, Bool.or_eq_true] at hchk
  have hnd : (subsetWords stock tok).Nodup := subsetWords_nodup snd tok
  have hlive' : LiveBin mask goal k (subsetWords stock tok).toFinset := by rwa [hteq]
  rcases hchk with hloc | href
  · have hopen := dagLocal_open (state := (fuel, subsetWords stock tok, [])) hgm hknown hsub hnd (k := k) (by omega) hlive'
    rw [hopen] at hloc; exact Bool.noConfusion hloc
  · unfold dagRef at href
    split at href
    · contradiction
    · rename_i dest _
      simp only [Bool.and_eq_true, Nat.blt_eq] at href
      obtain ⟨hdest, hst⟩ := href
      cases htr : dagTrace mask stock fuel forest dest with
      | none => rw [htr] at hst; contradiction
      | some saved =>
        rw [htr] at hst
        simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at hst
        obtain ⟨hfEq, hwEq⟩ := hst
        exact dagAllNodes hgm hknown hsub snd hnodes fuel dest saved hdest htr hfEq k (by omega) (hwEq ▸ hlive')

def unpack (data width idx : Nat) : Nat :=
  (data >>> (idx * width)) &&& ((1 <<< width) - 1)

def unpackForest (data pBits tBits : Nat) : Nat → Nat × Nat := fun i =>
  let w := pBits + tBits
  let code := unpack data w i
  (code >>> tBits, code &&& ((1 <<< tBits) - 1))

def unpackLinks (index data idxW sizeBits tokBits destBits steps : Nat) : Nat → Nat → Option Nat :=
  fun parent tok =>
    let entry := unpack index idxW parent
    let sz := entry &&& ((1 <<< sizeBits) - 1)
    let off := entry >>> sizeBits
    let w := tokBits + destBits
    (Nat.rec (motive := fun _ => Nat → Nat → Option Nat) (fun _ _ => none)
      (fun _ next lo hi =>
        if Nat.blt lo hi then
          let mid := (lo + hi) / 2
          let code := unpack data w mid
          let key := code &&& ((1 <<< tokBits) - 1)
          if Nat.beq tok key then some (code >>> tokBits)
          else if Nat.blt tok key then next lo mid else next (mid + 1) hi
        else none) steps) off (off + sz)

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true

def binaryCost (gs : List Gate) : Nat := (gs.filter isBinary).length

def legal (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def evalBit (k : Nat) (w : Nat) : Bool := w.testBit k

def stepBool (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def actionWord (w : List Nat) (g : Gate) : Nat := match g.op with
  | .not => fullMask ^^^ ((g.inputs.head?.map (fun i => w.getD i 0)).getD 0)
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) fullMask
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

theorem fullMask_eq : fullMask = 2 ^ 64 - 1 := by decide

theorem fullMask_bit {k : Nat} (hk : k < 64) : fullMask.testBit k = true := by
  rw [fullMask_eq, Nat.testBit_two_pow_sub_one]; simp [hk]

theorem readBit (w : List Nat) (i k : Nat) :
    (w.map (evalBit k)).getD i false = evalBit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), evalBit]

theorem actionWord_spec (w : List Nat) (g : Gate) (hg : legal g) {k : Nat} (hk : k < 64) :
    stepBool (w.map (evalBit k)) g = (w ++ [actionWord w g]).map (evalBit k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hcap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hcap
  have hfm := fullMask_bit hk
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at hcap
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [stepBool, List.map_cons, List.map_nil, readBit, List.map_append, actionWord,
      GateOp.eval, List.foldr_cons, List.foldr_nil, List.head?_cons, List.head?_nil,
      List.headD_cons, List.headD_nil, Option.map_some, Option.map_none, Option.getD_some,
      Option.getD_none, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq,
      Bool.and_true, Bool.or_false, evalBit, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor,
      Nat.zero_testBit, hfm, Bool.true_xor]

def rawVars : List Nat :=
  [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

def rootStock : List Nat :=
  [0x5555555555555555, 0x3333333333333333, 0x0f0f0f0f0f0f0f0f,
   0x00ff00ff00ff00ff, 0x0000ffff0000ffff, 0x00000000ffffffff]

theorem rawVars_avail : ∀ u ∈ rawVars, Avail rootStock (canon fullMask u) := by
  intro u hu
  simp only [rawVars, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Or.inr (by decide)

theorem compileBin_aux (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (w bank : List Nat)
    (hw : ∀ u ∈ w, Avail bank (canon fullMask u)) :
    ∃ vs, vs.length ≤ binaryCost gs ∧ BuildsBin fullMask bank vs ∧
      ∀ u ∈ gs.foldl (fun acc g => acc ++ [actionWord acc g]) w, Avail (vs ++ bank) (canon fullMask u) := by
  induction gs generalizing w bank with
  | nil => exact ⟨[], Nat.le_refl _, trivial, by simpa using hw⟩
  | cons g gs ih =>
    have hg0 := hg g List.mem_cons_self
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    set z := actionWord w g
    have hread (i : Nat) : Avail bank (canon fullMask (w.getD i 0)) := by
      by_cases hi : i < w.length
      · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi])
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi), canon_zero]; exact Or.inl rfl
    have hstep : Avail bank (canon fullMask z) ∨ (isBinary g = true ∧ GateBin fullMask bank (canon fullMask z)) := by
      obtain ⟨op, args⟩ := g
      obtain ⟨hop, hcap⟩ := hg0
      change op = .and ∨ op = .or ∨ op = .not at hop
      change args.length ≤ 2 at hcap
      rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at hcap
      · rcases hop with rfl | rfl | rfl
        · left; simp [z, actionWord, canon_self]; exact Or.inl rfl
        · left; simp [z, actionWord, canon_zero]; exact Or.inl rfl
        · left; simp [z, actionWord, canon_self]; exact Or.inl rfl
      · rcases hop with rfl | rfl | rfl
        · left; simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
          rw [canon_land]; exact hread i
        · left; simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.or_zero]
          exact hread i
        · left; simp only [z, actionWord, List.head?_cons, Option.map_some, Option.getD_some]
          rw [canon_xor_mask]; exact hread i
      · rcases hop with rfl | rfl | rfl
        · simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
          have h1 : canon fullMask (w.getD i 0 &&& (w.getD j 0 &&& fullMask)) =
              canon fullMask (w.getD i 0 &&& w.getD j 0) := by
            rw [← canon_land fullMask (w.getD i 0 &&& (w.getD j 0 &&& fullMask))]
            rw [← canon_land fullMask (w.getD i 0 &&& w.getD j 0)]
            congr 1; apply Nat.eq_of_testBit_eq; intro k; simp only [Nat.testBit_and]
            cases (w.getD i 0).testBit k <;> cases (w.getD j 0).testBit k <;> cases fullMask.testBit k <;> rfl
          rw [h1]
          rcases canon_and_in_binOp fullMask (w.getD i 0) (w.getD j 0) with h0 | hi' | hj' | ⟨op', hop', hbin⟩
          · left; exact Or.inl h0
          · left; rw [hi']; exact hread i
          · left; rw [hj']; exact hread j
          · right; exact ⟨rfl, canon fullMask (w.getD i 0), canon fullMask (w.getD j 0), op', hop', hread i, hread j, hbin⟩
        · simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.or_zero]
          rcases canon_or_in_binOp fullMask (w.getD i 0) (w.getD j 0) with h0 | hi' | hj' | ⟨op', hop', hbin⟩
          · left; exact Or.inl h0
          · left; rw [hi']; exact hread i
          · left; rw [hj']; exact hread j
          · right; exact ⟨rfl, canon fullMask (w.getD i 0), canon fullMask (w.getD j 0), op', hop', hread i, hread j, hbin⟩
        · left; simp only [z, actionWord, List.head?_cons, Option.map_some, Option.getD_some]
          rw [canon_xor_mask]; exact hread i
    rcases hstep with hav | ⟨hbin, hgate⟩
    · have hw' : ∀ u ∈ w ++ [z], Avail bank (canon fullMask u) := by
        intro u hu; rcases List.mem_append.mp hu with hu | hu
        · exact hw u hu
        · rw [List.mem_singleton.mp hu]; exact hav
      obtain ⟨vs, hlen, hbd, hall⟩ := ih hgs (w ++ [z]) bank hw'
      have hbc : binaryCost gs ≤ binaryCost (g :: gs) := by
        unfold binaryCost; simp only [List.filter]; cases isBinary g <;> simp
      exact ⟨vs, Nat.le_trans hlen hbc, hbd, hall⟩
    · set cz := canon fullMask z
      have hw' : ∀ u ∈ w ++ [z], Avail (cz :: bank) (canon fullMask u) := by
        intro u hu; rcases List.mem_append.mp hu with hu | hu
        · exact avail_weaken (fun a ha => List.mem_cons_of_mem _ ha) (hw u hu)
        · rw [List.mem_singleton.mp hu]; exact Or.inr List.mem_cons_self
      obtain ⟨vs, hlen, hbd, hall⟩ := ih hgs (w ++ [z]) (cz :: bank) hw'
      have hbc : binaryCost (g :: gs) = binaryCost gs + 1 := by
        unfold binaryCost; simp [hbin]
      refine ⟨cz :: vs, by simp only [List.length_cons, hbc]; omega, ⟨hgate, hbd⟩, ?_⟩
      intro u hu
      exact avail_weaken (fun a ha => by simp only [List.mem_append, List.mem_cons] at ha ⊢; tauto) (hall u hu)

theorem foldl_evalBit (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (w : List Nat) {k : Nat} (hk : k < 64) :
    gs.foldl stepBool (w.map (evalBit k)) =
      (gs.foldl (fun acc g => acc ++ [actionWord acc g]) w).map (evalBit k) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [actionWord_spec w g (hg g List.mem_cons_self) hk]
    exact ih (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (w ++ [actionWord w g])

theorem rawVars_ofFn (x : Fin 6 → Bool) :
    List.ofFn x = rawVars.map (evalBit (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) := by
  have hx : ∀ (b0 b1 b2 b3 b4 b5 : Bool),
      [b0, b1, b2, b3, b4, b5] =
      rawVars.map (evalBit ((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
        (if b3 then 8 else 0) + (if b4 then 16 else 0) + (if b5 then 32 else 0))) := by
    decide +kernel
  have hsum : (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) =
      (if x 0 then 1 else 0) + (if x 1 then 2 else 0) + (if x 2 then 4 else 0) +
      (if x 3 then 8 else 0) + (if x 4 then 16 else 0) + (if x 5 then 32 else 0) := by
    simp [Fin.sum_univ_six]
  rw [hsum, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  exact hx (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

theorem sum_bits_6 (n : Nat) (hn : n < 64) :
    (∑ i : Fin 6, if n.testBit i.val then 2 ^ (i : Nat) else 0) = n := by
  simp only [Fin.sum_univ_six, Fin.val_zero, Fin.val_one, Fin.val_two]
  change (if n.testBit 0 then 1 else 0) + (if n.testBit 1 then 2 else 0) +
    (if n.testBit 2 then 4 else 0) + (if n.testBit 3 then 8 else 0) +
    (if n.testBit 4 then 16 else 0) + (if n.testBit 5 then 32 else 0) = n
  revert n; decide +kernel

theorem table2_from_lowerBin (target m : Nat)
    (hlow : LowerBin fullMask rootStock (canon fullMask target) (m - 1))
    (wg : List Gate) (wout : Nat) (hsz : wg.length = m)
    (hmono : Monotone2 ⟨wg, wout⟩)
    (heval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, wout⟩ (List.ofFn x) =
      Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) :
    ∀ s : Nat, HasCircuitSize 6 (fun x : Fin 6 → Bool =>
      Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) s →
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool,
      C.eval (List.ofFn x) = Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) := by
  intro s ⟨C, hfan, hsize, hC⟩
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, hgm, hgop⟩ := hasNot
    have hshort : binaryCost C.gates < C.gates.length :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr ⟨g, hgm, by simp [isBinary, hgop]⟩
    have hleg : ∀ g ∈ C.gates, legal g := by
      intro g hg
      obtain ⟨hop, hlen⟩ := hfan g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      exact ⟨hop, hlen⟩
    obtain ⟨vs, hvlen, hvbd, hvhit⟩ := compileBin_aux C.gates hleg rawVars rootStock rawVars_avail
    set finalW := C.gates.foldl (fun acc g => acc ++ [actionWord acc g]) rawVars
    have hout_eq : finalW.getD C.output 0 &&& fullMask = target &&& fullMask := by
      apply Nat.eq_of_testBit_eq; intro k
      by_cases hk : k < 64
      · have hfm := fullMask_bit hk
        simp only [Nat.testBit_and, hfm, Bool.and_true]
        let x : Fin 6 → Bool := fun i => k.testBit i.val
        have hxidx : (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) = k := sum_bits_6 k hk
        have h1 := hC x
        dsimp only at h1
        rw [hxidx, rawVars_ofFn x, hxidx] at h1
        change (C.gates.foldl stepBool (rawVars.map (evalBit k))).getD C.output false = target.testBit k at h1
        rw [foldl_evalBit C.gates hleg rawVars hk, readBit] at h1
        exact h1
      · have hfm0 : fullMask.testBit k = false := by
          rw [fullMask_eq, Nat.testBit_two_pow_sub_one]; simp [hk]
        simp [Nat.testBit_and, hfm0]
    have hout_avail : Avail (vs ++ rootStock) (canon fullMask target) := by
      rw [← canon_land fullMask target, ← hout_eq, canon_land]
      by_cases hi : C.output < finalW.length
      · exact hvhit _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi])
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi), canon_zero]; exact Or.inl rfl
    have hge := hlow vs hvbd hout_avail
    have hcsz : C.size = C.gates.length := rfl
    have hwsz : (⟨wg, wout⟩ : Circuit).size = m := hsz
    exact ⟨⟨wg, wout⟩, hmono, by omega, heval⟩
  · refine ⟨C, ?_, hsize, hC⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim

def memN (z : Nat) (l : List Nat) : Bool :=
  List.rec false (fun w _ ih => Bool.rec ih true (Nat.beq z w)) l

theorem memN_eq (z : Nat) (l : List Nat) : memN z l = l.contains z := by
  apply Bool.eq_iff_iff.mpr
  rw [List.contains_iff_mem]
  induction l with
  | nil => simp [memN]
  | cons w ws ih =>
    change Bool.rec (memN z ws) true (Nat.beq z w) = true ↔ z ∈ w :: ws
    cases h : Nat.beq z w
    · have hne : z ≠ w := ne_of_beq_false h
      simp [ih, hne]
    · have heq : z = w := Nat.eq_of_beq_eq_true h
      simp [heq]

def allN (p : Nat → Bool) (l : List Nat) : Bool :=
  List.rec true (fun w _ ih => Bool.rec false ih (p w)) l

theorem allN_eq (p : Nat → Bool) (l : List Nat) : allN p l = l.all p := by
  induction l with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec false (allN p ws) (p w) = (p w && ws.all p)
    rw [ih]; cases p w <;> rfl

def lenN (l : List Nat) : Nat :=
  List.rec 0 (fun _ _ ih => Nat.add ih 1) l

theorem lenN_eq (l : List Nat) : lenN l = l.length := by
  induction l with
  | nil => rfl
  | cons _ ws ih => change Nat.add (lenN ws) 1 = ws.length + 1; rw [ih]

def appN (l r : List Nat) : List Nat :=
  List.rec r (fun w _ ih => w :: ih) l

theorem appN_eq (l r : List Nat) : appN l r = l ++ r := by
  induction l with
  | nil => rfl
  | cons w ws ih => change w :: appN ws r = w :: (ws ++ r); rw [ih]

def revAccN {α : Type} (l acc : List α) : List α :=
  (List.rec (motive := fun _ => List α → List α) (fun a => a) (fun w _ ih a => ih (w :: a)) l) acc

theorem revAccN_eq {α : Type} (l acc : List α) : revAccN l acc = l.reverse ++ acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons w ws ih =>
    change revAccN ws (w :: acc) = (w :: ws).reverse ++ acc
    rw [ih, List.reverse_cons, List.append_assoc]; rfl

def getDN (l : List Nat) (i : Nat) : Nat :=
  (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun w _ ih k => Nat.rec w (fun m _ => ih m) k) l) i

theorem getDN_eq (l : List Nat) (i : Nat) : getDN l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons w ws ih =>
    cases i with
    | zero => rfl
    | succ m => change getDN ws m = (w :: ws).getD (m + 1) 0; rw [ih]; rfl

def eqListN (l1 : List Nat) : List Nat → Bool :=
  List.rec
    (fun l2 => List.rec true (fun _ _ _ => false) l2)
    (fun x _ ih l2 => List.rec false (fun y ys _ => Bool.rec false (ih ys) (Nat.beq x y)) l2) l1

theorem eqListN_eq (l1 l2 : List Nat) : eqListN l1 l2 = (l1 == l2) := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> rfl
  | cons x xs ih =>
    cases l2 with
    | nil => rfl
    | cons y ys =>
      change Bool.rec false (eqListN xs ys) (Nat.beq x y) = ((x :: xs) == (y :: ys))
      rw [ih]
      by_cases h : x = y
      · subst h; simp [Nat.beq_refl]
      · have h1 : Nat.beq x y = false := beq_false_ne h
        have h2 : (x == y) = false := beq_false_of_ne h
        simp [h1, h2]

def canonF (mask w : Nat) : Nat :=
  let v := Nat.land w mask
  Bool.rec
    (Bool.rec
      (let iv := Nat.xor mask v
       Bool.rec iv v (Nat.blt v iv))
      0 (Nat.beq v mask))
    0 (Nat.beq v 0)

theorem canonF_eq (mask w : Nat) : canonF mask w = canon mask w := by
  unfold canonF canon bsel; dsimp only
  change (Bool.rec (Bool.rec (Bool.rec (mask ^^^ (w &&& mask)) (w &&& mask) ((w &&& mask).blt (mask ^^^ (w &&& mask)))) 0 ((w &&& mask).beq mask)) 0 ((w &&& mask).beq 0) : Nat) = _
  cases Nat.beq (w &&& mask) 0 <;> cases Nat.beq (w &&& mask) mask <;> rfl

def binOpF (mask op a b : Nat) : Nat :=
  Bool.rec
    (Bool.rec
      (Bool.rec (canonF mask (Nat.land (Nat.xor mask a) b))
        (canonF mask (Nat.land a (Nat.xor mask b))) (Nat.beq op 2))
      (canonF mask (Nat.lor a b)) (Nat.beq op 1))
    (canonF mask (Nat.land a b)) (Nat.beq op 0)

theorem binOpF_eq (mask op a b : Nat) : binOpF mask op a b = binOp mask op a b := by
  unfold binOpF binOp bsel
  simp only [canonF_eq]
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> rfl

def dagPartF (ws : List Nat) : Nat → Nat → Bool :=
  List.rec
    (fun p n => Bool.rec (Nat.beq n 0) true (Nat.beq p 0))
    (fun w _ rest p n =>
      Bool.rec
        (Bool.rec
          (forceW (Nat.land p w) (fun up =>
            forceW (Nat.land n w) (fun down =>
              Bool.rec false
                (forceW (Nat.xor p up) (fun offP =>
                  forceW (Nat.xor n down) (rest offP)))
                (rest up down))))
          true (Nat.beq n 0))
        true (Nat.beq p 0)) ws

theorem dagPartF_eq (ws : List Nat) (p n : Nat) : dagPartF ws p n = dagPart ws p n := by
  induction ws generalizing p n with
  | nil =>
    change Bool.rec (Nat.beq n 0) true (Nat.beq p 0) = (Nat.beq p 0 || Nat.beq n 0)
    cases Nat.beq p 0 <;> rfl
  | cons w ws ih =>
    change Bool.rec (Bool.rec (forceW (Nat.land p w) (fun up =>
      forceW (Nat.land n w) (fun down =>
        Bool.rec false (forceW (Nat.xor p up) (fun offP => forceW (Nat.xor n down) (dagPartF ws offP)))
          (dagPartF ws up down)))) true (Nat.beq n 0)) true (Nat.beq p 0) =
      ((Nat.beq p 0 || Nat.beq n 0) || forceW (p &&& w) (fun up =>
        forceW (n &&& w) (fun down => dagPart ws up down &&
          forceW (p ^^^ up) (fun offP => forceW (n ^^^ down) (dagPart ws offP)))))
    simp only [forceW_eq]
    cases Nat.beq p 0
    · cases Nat.beq n 0
      · change Bool.rec false (dagPartF ws _ _) (dagPartF ws _ _) = (dagPart ws _ _ && dagPart ws _ _)
        rw [ih, ih]; cases dagPart ws (p &&& w) (n &&& w) <;> rfl
      · rfl
    · rfl

def flatCountF (cut : Nat) (ws : List Nat) : Nat :=
  List.rec 0 (fun w _ cnt =>
    let v := Nat.land w cut
    Bool.rec (Bool.rec cnt (Nat.add cnt 1) (Nat.beq v cut)) (Nat.add cnt 1) (Nat.beq v 0)) ws

theorem flatCountF_eq (cut : Nat) (ws : List Nat) : flatCountF cut ws = flatCount cut ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (Bool.rec (flatCountF cut ws) (Nat.add (flatCountF cut ws) 1) (Nat.beq (Nat.land w cut) cut))
      (Nat.add (flatCountF cut ws) 1) (Nat.beq (Nat.land w cut) 0) =
      bsel (Nat.beq (canon cut w) 0) (flatCount cut ws + 1) (flatCount cut ws)
    rw [ih]
    rcases canon_cases cut w with ⟨h0, h1 | h2⟩ | ⟨hne, _⟩
    · have hb : Nat.beq (Nat.land w cut) 0 = true := Nat.beq_eq.mpr h1
      rw [h0, hb, Nat.beq_refl]; rfl
    · have hb : Nat.beq (Nat.land w cut) cut = true := Nat.beq_eq.mpr h2
      rw [h0, hb, Nat.beq_refl]; cases Nat.beq (Nat.land w cut) 0 <;> rfl
    · have h1 : Nat.beq (Nat.land w cut) 0 = false := beq_false_ne (fun e => by
        change w &&& cut = 0 at e; exact hne (by unfold canon; dsimp only; rw [e]; simp [bsel]))
      have h2 : Nat.beq (Nat.land w cut) cut = false := beq_false_ne (fun e => by
        change w &&& cut = cut at e; exact hne (by unfold canon; dsimp only; rw [e]; simp [bsel]))
      rw [h1, h2, beq_false_ne hne]; rfl

def availBF (bank : List Nat) (w : Nat) : Bool :=
  Bool.rec (memN w bank) true (Nat.beq w 0)

theorem availBF_eq (bank : List Nat) (w : Nat) : availBF bank w = availB bank w := by
  unfold availBF availB; rw [memN_eq]; cases Nat.beq w 0 <;> rfl

def recipeGateBinF (cut : Nat) (bank : List Nat) (vc ac bc : Nat) : Bool :=
  Bool.rec false
    (Bool.rec false
      (Bool.rec
        (Bool.rec
          (Bool.rec (Nat.beq vc (binOpF cut 3 ac bc)) true (Nat.beq vc (binOpF cut 2 ac bc)))
          true (Nat.beq vc (binOpF cut 1 ac bc)))
        true (Nat.beq vc (binOpF cut 0 ac bc)))
      (availBF bank bc))
    (availBF bank ac)

theorem recipeGateBinF_eq (cut : Nat) (bank : List Nat) (vc ac bc : Nat) :
    recipeGateBinF cut bank vc ac bc = recipeGateBin cut bank vc ac bc := by
  unfold recipeGateBinF recipeGateBin
  simp only [availBF_eq, binOpF_eq]
  cases availB bank ac <;> cases availB bank bc <;>
    cases Nat.beq vc (binOp cut 0 ac bc) <;> cases Nat.beq vc (binOp cut 1 ac bc) <;>
    cases Nat.beq vc (binOp cut 2 ac bc) <;> cases Nat.beq vc (binOp cut 3 ac bc) <;> rfl

def addUniqF (w : Nat) (l : List Nat) : List Nat :=
  Bool.rec (w :: l) l (memN w l)

theorem addUniqF_eq (w : Nat) (l : List Nat) : addUniqF w l = addUniq w l := by
  unfold addUniqF addUniq; rw [memN_eq]; cases l.contains w <;> rfl

def recipeStartF (cut : Nat) (stock ws : List Nat) : List Nat :=
  List.rec [] (fun w _ acc =>
    let v := canonF cut w
    Bool.rec (addUniqF v acc) acc (availBF stock v)) ws

theorem recipeStartF_eq (cut : Nat) (stock ws : List Nat) : recipeStartF cut stock ws = recipeStart cut stock ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (addUniqF (canonF cut w) (recipeStartF cut stock ws)) (recipeStartF cut stock ws) (availBF stock (canonF cut w)) =
      (if availB stock (canon cut w) then recipeStart cut stock ws else addUniq (canon cut w) (recipeStart cut stock ws))
    rw [ih, canonF_eq, availBF_eq, addUniqF_eq]; cases availB stock (canon cut w) <;> rfl

def recipeCloseF (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun (w, a, b) _ next acc =>
      let v := canonF cut w
      Bool.rec (next acc)
        (let va := canonF cut a
         let vb := canonF cut b
         let acc1 := Bool.rec (addUniqF va acc) acc (availBF stock va)
         let acc2 := Bool.rec (addUniqF vb acc1) acc1 (availBF stock vb)
         next acc2)
        (memN v acc)) hist needed

theorem recipeCloseF_eq (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) :
    recipeCloseF cut stock hist needed = recipeClose cut stock hist needed := by
  induction hist generalizing needed with
  | nil => rfl
  | cons rec hist ih =>
    obtain ⟨w, a, b⟩ := rec
    have hL : recipeCloseF cut stock ((w, a, b) :: hist) needed =
        Bool.rec (recipeCloseF cut stock hist needed)
          (let va := canonF cut a; let vb := canonF cut b
           let acc1 := Bool.rec (addUniqF va needed) needed (availBF stock va)
           let acc2 := Bool.rec (addUniqF vb acc1) acc1 (availBF stock vb)
           recipeCloseF cut stock hist acc2)
          (memN (canonF cut w) needed) := rfl
    have hR : recipeClose cut stock ((w, a, b) :: hist) needed =
        (if needed.contains (canon cut w) then
          let va := canon cut a; let vb := canon cut b
          let acc1 := if availB stock va then needed else addUniq va needed
          let acc2 := if availB stock vb then acc1 else addUniq vb acc1
          recipeClose cut stock hist acc2
        else recipeClose cut stock hist needed) := rfl
    rw [hL, hR]; dsimp only
    simp only [canonF_eq, memN_eq, availBF_eq, addUniqF_eq]
    cases needed.contains (canon cut w)
    · exact ih needed
    · dsimp only; rw [ih]
      cases availB stock (canon cut a) <;> cases availB stock (canon cut b) <;> rfl

def replayRecF (cut : Nat) (needed : List Nat) (hist : List (Nat × Nat × Nat)) (bank : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun _ => [])
    (fun (w, a, b) _ next bank =>
      let v := canonF cut w
      Bool.rec (next bank)
        (Bool.rec
          (Bool.rec (next bank) (v :: next (v :: bank))
            (recipeGateBinF cut bank v (canonF cut a) (canonF cut b)))
          (next bank) (availBF bank v))
        (memN v needed)) hist bank

theorem replayRecF_eq (cut : Nat) (needed : List Nat) (hist : List (Nat × Nat × Nat)) (bank : List Nat) :
    replayRecF cut needed hist bank = replayRec cut needed hist bank := by
  induction hist generalizing bank with
  | nil => rfl
  | cons rec hist ih =>
    obtain ⟨w, a, b⟩ := rec
    have hL : replayRecF cut needed ((w, a, b) :: hist) bank =
        let v := canonF cut w
        Bool.rec (replayRecF cut needed hist bank)
          (Bool.rec
            (Bool.rec (replayRecF cut needed hist bank) (v :: replayRecF cut needed hist (v :: bank))
              (recipeGateBinF cut bank v (canonF cut a) (canonF cut b)))
            (replayRecF cut needed hist bank) (availBF bank v))
          (memN v needed) := rfl
    have hR : replayRec cut needed ((w, a, b) :: hist) bank =
        (let v := canon cut w
         if needed.contains v && !(availB bank v) && recipeGateBin cut bank v (canon cut a) (canon cut b) then
           v :: replayRec cut needed hist (v :: bank)
         else replayRec cut needed hist bank) := rfl
    rw [hL, hR]; dsimp only
    simp only [canonF_eq, memN_eq, availBF_eq, recipeGateBinF_eq]
    rw [ih bank, ih (canon cut w :: bank)]
    cases needed.contains (canon cut w) <;> cases availB bank (canon cut w) <;>
      cases recipeGateBin cut bank (canon cut w) (canon cut a) (canon cut b) <;> rfl

def boundClosesF (state : Nat × List Nat × List (Nat × Nat × Nat))
    (bound : Nat × List Nat × Nat × Nat) : Bool :=
  let (cut, stock, lower, _) := bound
  let (fuel, ws, hist) := state
  forceW (Nat.sub fuel (flatCountF cut ws)) (fun rem =>
    Bool.rec false
      (forceWs (recipeStartF cut stock ws) (fun start =>
        Bool.rec false
          (forceWs (recipeCloseF cut stock hist start) (fun needed =>
            Bool.rec false
              (forceWs (replayRecF cut needed (revAccN hist []) stock) (fun replay =>
                Bool.rec false
                  (allN (fun w => availBF (appN replay stock) (canonF cut w)) ws)
                  (Nat.blt (Nat.add (lenN replay) rem) lower)))
              (Nat.blt (Nat.add (lenN needed) rem) lower)))
          (Nat.blt (Nat.add (lenN start) rem) lower)))
      (Nat.blt rem lower))

theorem boundClosesF_eq {target : Nat} {state : Nat × List Nat × List (Nat × Nat × Nat)}
    {bound : Nat × List Nat × Nat × Nat}
    (hg : canon bound.1 target = bound.2.2.2) (hnz : bound.2.2.2 ≠ 0) :
    boundClosesF state bound = boundCloses target state bound := by
  obtain ⟨fuel, ws, hist⟩ := state
  obtain ⟨cut, stock, lower, bgoal⟩ := bound
  dsimp only at hg hnz
  unfold boundClosesF boundCloses
  simp only [forceW_eq, forceWs_eq, flatCountF_eq, recipeStartF_eq, recipeCloseF_eq,
    replayRecF_eq, revAccN_eq, List.append_nil, lenN_eq, allN_eq, appN_eq, availBF_eq, canonF_eq,
    hg, Nat.beq_refl, beq_false_ne hnz, Bool.not_false, Bool.and_true, Bool.true_and]
  cases Nat.blt (fuel - flatCount cut ws) lower
  · rfl
  · cases Nat.blt ((recipeStart cut stock ws).length + (fuel - flatCount cut ws)) lower
    · rfl
    · cases Nat.blt ((recipeClose cut stock hist (recipeStart cut stock ws)).length + (fuel - flatCount cut ws)) lower
      · rfl
      · cases Nat.blt ((replayRec cut (recipeClose cut stock hist (recipeStart cut stock ws)) hist.reverse stock).length + (fuel - flatCount cut ws)) lower <;> rfl

def knownClosesF (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  List.rec false (fun b _ rest => Bool.rec rest true (boundClosesF state b)) bounds

theorem knownClosesF_eq {target : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 target = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    knownClosesF bounds state = knownCloses target bounds state := by
  induction bounds with
  | nil => rfl
  | cons b bs ih =>
    change Bool.rec (knownClosesF bs state) true (boundClosesF state b) =
      (boundCloses target state b || knownCloses target bs state)
    have h0 := hgoals b List.mem_cons_self
    rw [boundClosesF_eq h0.1 h0.2, ih (fun x hx => hgoals x (List.mem_cons_of_mem _ hx))]
    cases boundCloses target state b <;> rfl

def insertSortedF (x : Nat) (l : List Nat) : List Nat :=
  List.rec [x] (fun y ys ih => Bool.rec (y :: ih) (x :: y :: ys) (Nat.ble x y)) l

theorem insertSortedF_eq (x : Nat) (l : List Nat) : insertSortedF x l = insertSorted x l := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    change Bool.rec (y :: insertSortedF x ys) (x :: y :: ys) (Nat.ble x y) =
      bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys)
    rw [ih]; cases Nat.ble x y <;> rfl

def dropValF (drop : Bool) (x : Nat) (l : List Nat) : List Nat :=
  Bool.rec l (List.rec [] (fun y _ ih => Bool.rec (y :: ih) ih (Nat.beq y x)) l) drop

theorem dropValF_eq (drop : Bool) (x : Nat) (l : List Nat) : dropValF drop x l = dropVal drop x l := by
  cases drop
  · rfl
  · induction l with
    | nil => rfl
    | cons y ys ih =>
      change Bool.rec (y :: dropValF true x ys) (dropValF true x ys) (Nat.beq y x) =
        bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys)
      rw [ih]; cases Nat.beq y x <;> rfl

def subsetWordsF (stock : List Nat) (bits : Nat) : List Nat :=
  (List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun w _ ih b =>
      let rest := ih (Nat.shiftRight b 1)
      Bool.rec rest (insertSortedF w rest) (Nat.beq (Nat.land b 1) 1)) stock) bits

theorem subsetWordsF_eq (stock : List Nat) (bits : Nat) : subsetWordsF stock bits = subsetWords stock bits := by
  induction stock generalizing bits with
  | nil => rfl
  | cons x xs ih =>
    change Bool.rec (subsetWordsF xs (Nat.shiftRight bits 1))
      (insertSortedF x (subsetWordsF xs (Nat.shiftRight bits 1))) (Nat.beq (Nat.land bits 1) 1) =
      bsel (Nat.beq (bits &&& 1) 1) (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1))
    rw [ih, insertSortedF_eq]; cases Nat.beq (bits &&& 1) 1 <;> rfl

def childStateF (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  let (fuel, ws, hist) := state
  let keep := Nat.land token 3
  let op := Nat.land (Nat.shiftRight token 2) 3
  let b := Nat.land (Nat.shiftRight token 4) 15
  let a := Nat.shiftRight token 8
  Bool.rec
    (Bool.rec none
      (Bool.rec none
        (let x := getDN ws a
         let y := getDN ws b
         let z := binOpF mask op x y
         Bool.rec
           (Bool.rec
             (let keepA := Nat.beq (Nat.land keep 1) 1
              let keepB := Nat.beq (Nat.land (Nat.shiftRight keep 1) 1) 1
              let rest := dropValF (Bool.rec true false keepA) x (dropValF (Bool.rec true false keepB) y ws)
              some (Nat.sub fuel 1, insertSortedF z rest, (z, x, y) :: hist))
             none (memN z ws))
           none (Nat.beq z 0))
        (Nat.blt b (lenN ws)))
      (Nat.blt a b))
    none (Nat.beq fuel 0)

theorem childStateF_eq (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    childStateF mask token state = childState mask token state := by
  obtain ⟨fuel, ws, hist⟩ := state
  unfold childStateF childState
  simp only [lenN_eq, getDN_eq, binOpF_eq, memN_eq, dropValF_eq, insertSortedF_eq]
  cases Nat.beq fuel 0
  · cases Nat.blt (token >>> 8) ((token >>> 4) &&& 15)
    · rfl
    · cases Nat.blt ((token >>> 4) &&& 15) ws.length
      · rfl
      · cases Nat.beq (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0) (ws.getD ((token >>> 4) &&& 15) 0)) 0
        · cases ws.contains (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0) (ws.getD ((token >>> 4) &&& 15) 0))
          · cases Nat.beq ((token &&& 3) &&& 1) 1 <;> cases Nat.beq (((token &&& 3) >>> 1) &&& 1) 1 <;> rfl
          · rfl
        · rfl
  · rfl

def dagTraceF (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
    (fun _ prev j =>
      let (parent, token) := forest j
      Bool.rec
        (match prev (Nat.sub parent 1) with
         | none => none
         | some st => childStateF mask token st)
        (Bool.rec none (some (fuel, subsetWordsF stock token, []))
          (Nat.blt token (Nat.shiftLeft 1 (lenN stock))))
        (Nat.beq parent 0)) (Nat.add fuel 1)) i

theorem dagTraceF_eq (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    dagTraceF mask stock fuel forest i = dagTrace mask stock fuel forest i := by
  unfold dagTraceF dagTrace
  suffices ∀ steps j,
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          Bool.rec
            (match prev (Nat.sub parent 1) with
             | none => none
             | some st => childStateF mask token st)
            (Bool.rec none (some (fuel, subsetWordsF stock token, []))
              (Nat.blt token (Nat.shiftLeft 1 (lenN stock))))
            (Nat.beq parent 0)) steps) j =
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) steps) j from
    this (fuel + 1) i
  intro steps
  induction steps with
  | zero => intro j; rfl
  | succ n ih =>
    intro j
    dsimp only
    have hpow : Nat.shiftLeft 1 (lenN stock) = 2 ^ stock.length := by
      rw [lenN_eq]; change 1 <<< stock.length = _; rw [Nat.shiftLeft_eq, Nat.one_mul]
    cases Nat.beq (forest j).1 0
    · dsimp only
      rw [ih]
      cases (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          if Nat.beq (forest k).1 0 then
            if Nat.blt (forest k).2 (2 ^ stock.length) then some (rootState stock fuel (forest k).2) else none
          else (prev ((forest k).1 - 1)).bind (childState mask (forest k).2)) n) ((forest j).1 - 1)
      · rfl
      · exact childStateF_eq mask (forest j).2 _
    · dsimp only
      rw [hpow, subsetWordsF_eq]
      cases Nat.blt (forest j).2 (2 ^ stock.length) <;> rfl

def dagLocalF (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  let (fuel, ws, _) := state
  Bool.rec
    (Bool.rec true
      (knownClosesF bounds state)
      (dagPartF ws goal (Nat.xor mask goal)))
    true (Nat.blt (Nat.add fuel 1) (lenN ws))

theorem dagLocalF_eq {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    dagLocalF mask goal bounds state = dagLocal mask goal bounds state := by
  obtain ⟨fuel, ws, hist⟩ := state
  unfold dagLocalF dagLocal; dsimp only
  rw [lenN_eq, dagPartF_eq, knownClosesF_eq hgoals]
  cases Nat.blt (fuel + 1) ws.length <;> cases dagPart ws goal (mask ^^^ goal) <;> rfl

def dagRefF (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (parent token : Nat)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  match links parent token with
  | none => false
  | some dest =>
    Bool.rec false
      (match states dest with
       | none => false
       | some saved => Bool.rec false (eqListN saved.2.1 state.2.1) (Nat.beq saved.1 state.1))
      (Nat.blt dest count)

theorem dagRefF_eq (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (parent token : Nat)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    dagRefF count states links parent token state = dagRef count states links parent token state := by
  unfold dagRefF dagRef
  cases links parent token with
  | none => rfl
  | some dest =>
    dsimp only
    cases Nat.blt dest count
    · rfl
    · dsimp only
      cases states dest with
      | none => rfl
      | some saved =>
        dsimp only
        rw [eqListN_eq]; cases Nat.beq saved.1 state.1 <;> rfl

def treeBlockF (lo hi : Nat) (f : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ next a b =>
      Bool.rec true
        (let m := Nat.shiftRight (Nat.add a b) 1
         Bool.rec (Bool.rec false (next m b) (next a m)) (f a) (Nat.beq a m))
        (Nat.blt a b)) (Nat.add (Nat.sub hi lo) 1)) lo hi

theorem treeBlockF_eq (lo hi : Nat) (f : Nat → Bool) : treeBlockF lo hi f = treeBlock lo hi f := by
  unfold treeBlockF treeBlock
  suffices ∀ steps a b,
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          Bool.rec true
            (let m := Nat.shiftRight (Nat.add x y) 1
             Bool.rec (Bool.rec false (next m y) (next x m)) (f x) (Nat.beq x m))
            (Nat.blt x y)) steps) a b =
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          if Nat.blt x y then
            let m := (x + y) / 2
            if Nat.beq x m then f x else next x m && next m y
          else true) steps) a b from
    this (hi - lo + 1) lo hi
  intro steps
  induction steps with
  | zero => intro a b; rfl
  | succ s ih =>
    intro a b
    dsimp only
    have hdiv : Nat.shiftRight (Nat.add a b) 1 = (a + b) / 2 := by
      change (a + b) >>> 1 = (a + b) / 2; rw [Nat.shiftRight_eq_div_pow]
    rw [hdiv]
    cases Nat.blt a b
    · rfl
    · cases Nat.beq a ((a + b) / 2)
      · rw [ih, ih]
        change Bool.rec false _ _ = (_ && _)
        cases (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true) _ s) a ((a + b) / 2) <;> rfl
      · rfl

def dagCheckChildrenF (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  let (fuel, ws, hist) := state
  let n := lenN ws
  Bool.rec
    (Bool.rec
      (Bool.rec false
        (treeBlockF 0 n (fun a =>
          let x := getDN ws a
          treeBlockF (Nat.add a 1) n (fun b =>
            let y := getDN ws b
            treeBlockF 0 4 (fun op =>
              forceW (binOpF mask op x y) (fun z =>
                Bool.rec
                  (Bool.rec
                    (treeBlockF 0 4 (fun keep =>
                      let keepA := Nat.beq (Nat.land keep 1) 1
                      let keepB := Nat.beq (Nat.land (Nat.shiftRight keep 1) 1) 1
                      let newLen := Nat.add (Nat.add (Nat.sub n 1) (Bool.rec 0 1 keepA)) (Bool.rec 0 1 keepB)
                      Bool.rec
                        (forceWs (insertSortedF z (dropValF (Bool.rec true false keepA) x (dropValF (Bool.rec true false keepB) y ws))) (fun ws' =>
                          let ch := (Nat.sub fuel 1, ws', (z, x, y) :: hist)
                          let tok := Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) op) 2) keep
                          Bool.rec (dagLocalF mask goal bounds ch) true (ref tok ch)))
                        true (Nat.blt fuel newLen)))
                    true (memN z ws))
                  true (Nat.beq z 0))))))
        (Nat.blt n 17))
      true (Nat.beq fuel 0))
    false (memN goal ws)

theorem makeTokenF_eq (a b op keep : Nat) :
    Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) op) 2) keep =
    makeToken a b op keep := by
  unfold makeToken
  change ((((a <<< 4) + b) <<< 2) + op) <<< 2 + keep = _
  simp only [Nat.shiftLeft_eq]

theorem dagCheckChildrenF_eq {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    dagCheckChildrenF mask goal bounds ref state = dagCheckChildren mask goal bounds ref state := by
  obtain ⟨fuel, ws, hist⟩ := state
  unfold dagCheckChildrenF dagCheckChildren; dsimp only
  simp only [lenN_eq, memN_eq, treeBlockF_eq]
  cases ws.contains goal
  · cases Nat.beq fuel 0
    · cases Nat.blt ws.length 17
      · rfl
      · dsimp only
        simp only [Bool.not_false, Bool.true_and, Bool.false_or]
        congr 1; funext a
        simp only [getDN_eq]
        congr 1; funext b
        congr 1; funext op
        simp only [binOpF_eq, forceW_eq]
        cases Nat.beq (binOp mask op (ws.getD a 0) (ws.getD b 0)) 0
        · cases ws.contains (binOp mask op (ws.getD a 0) (ws.getD b 0))
          · dsimp only; simp only [Bool.false_or]
            congr 1; funext keep
            simp only [insertSortedF_eq, dropValF_eq, forceWs_eq, makeTokenF_eq, dagLocalF_eq hgoals]
            cases Nat.beq (keep &&& 1) 1 <;> cases Nat.beq ((keep >>> 1) &&& 1) 1
            all_goals dsimp only
            all_goals simp only [Bool.false_eq_true, ite_true, ite_false, Bool.not_true, Bool.not_false]
            all_goals cases Nat.blt fuel _
            all_goals try rfl
            all_goals cases ref (makeToken a b op keep) _ <;> cases dagLocal mask goal bounds _ <;> rfl
          · rfl
        · rfl
    · rfl
  · rfl

def dagCheckNodeF (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some st => dagCheckChildrenF mask goal bounds (dagRefF count states links (Nat.add i 1)) st

theorem dagCheckNodeF_eq {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (i : Nat) :
    dagCheckNodeF mask goal bounds count states links i = dagCheckNode mask goal bounds count states links i := by
  unfold dagCheckNodeF dagCheckNode
  cases states i with
  | none => rfl
  | some st =>
    have href : dagRefF count states links (Nat.add i 1) = dagRef count states links (i + 1) := by
      funext tok s; exact dagRefF_eq count states links (i + 1) tok s
    rw [href]; exact dagCheckChildrenF_eq hgoals _ st

def dagCheckRootsF (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (stock : List Nat) (fuel : Nat) : Bool :=
  treeBlockF 0 (Nat.shiftLeft 1 (lenN stock)) (fun token =>
    forceWs (subsetWordsF stock token) (fun ws =>
      let st := (fuel, ws, [])
      Bool.rec (dagLocalF mask goal bounds st) true (ref token st)))

theorem dagCheckRootsF_eq {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (stock : List Nat) (fuel : Nat) :
    dagCheckRootsF mask goal bounds ref stock fuel = dagCheckRoots mask goal bounds ref stock fuel := by
  unfold dagCheckRootsF dagCheckRoots
  have hpow : Nat.shiftLeft 1 (lenN stock) = 2 ^ stock.length := by
    rw [lenN_eq]; change 1 <<< stock.length = _; rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [hpow, treeBlockF_eq]
  congr 1; funext tok
  simp only [subsetWordsF_eq, forceWs_eq, dagLocalF_eq hgoals]
  cases ref tok (fuel, subsetWords stock tok, []) <;> cases dagLocal mask goal bounds (fuel, subsetWords stock tok, []) <;> rfl

def unpackF (data width idx : Nat) : Nat :=
  Nat.land (Nat.shiftRight data (Nat.mul idx width)) (Nat.sub (Nat.shiftLeft 1 width) 1)

def unpackForestF (data pBits tBits : Nat) : Nat → Nat × Nat := fun i =>
  let w := Nat.add pBits tBits
  let code := unpackF data w i
  (Nat.shiftRight code tBits, Nat.land code (Nat.sub (Nat.shiftLeft 1 tBits) 1))

def unpackLinksF (index data idxW sizeBits tokBits destBits steps : Nat) : Nat → Nat → Option Nat :=
  fun parent tok =>
    let entry := unpackF index idxW parent
    let sz := Nat.land entry (Nat.sub (Nat.shiftLeft 1 sizeBits) 1)
    let off := Nat.shiftRight entry sizeBits
    let w := Nat.add tokBits destBits
    (Nat.rec (motive := fun _ => Nat → Nat → Option Nat) (fun _ _ => none)
      (fun _ next lo hi =>
        Bool.rec none
          (let mid := Nat.shiftRight (Nat.add lo hi) 1
           let code := unpackF data w mid
           let key := Nat.land code (Nat.sub (Nat.shiftLeft 1 tokBits) 1)
           Bool.rec
             (Bool.rec (next (Nat.add mid 1) hi) (next lo mid) (Nat.blt tok key))
             (some (Nat.shiftRight code tokBits)) (Nat.beq tok key))
          (Nat.blt lo hi)) steps) off (Nat.add off sz)

theorem lowerDagF {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {links : Nat → Nat → Option Nat}
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hroots : dagCheckRootsF mask goal bounds
      (dagRefF count (dagTraceF mask stock fuel forest) links 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeF mask goal bounds count
      (dagTraceF mask stock fuel forest) links i = true) :
    LowerBin mask stock goal (fuel + 1) := by
  have htr : dagTraceF mask stock fuel forest = dagTrace mask stock fuel forest := by
    funext i; exact dagTraceF_eq mask stock fuel forest i
  rw [htr] at hroots hnodes
  have hr : dagCheckRoots mask goal bounds (dagRef count (dagTrace mask stock fuel forest) links 0) stock fuel = true := by
    have href : dagRefF count (dagTrace mask stock fuel forest) links 0 = dagRef count (dagTrace mask stock fuel forest) links 0 := by
      funext t s; exact dagRefF_eq count _ links 0 t s
    rw [href, dagCheckRootsF_eq hgoals] at hroots; exact hroots
  have hn : ∀ i, 0 ≤ i → i < count → dagCheckNode mask goal bounds count (dagTrace mask stock fuel forest) links i = true := by
    intro i h1 h2
    have h := hnodes i h1 h2
    rwa [dagCheckNodeF_eq hgoals] at h
  exact lowerDag hgm hgnz hcs snd hknown hsub hr hn

theorem treeBlockF_at {lo hi : Nat} {f : Nat → Bool} (h : treeBlockF lo hi f = true) :
    ∀ {i : Nat}, lo ≤ i → i < hi → f i = true := by
  rw [treeBlockF_eq] at h; exact treeBlock_at h

def m_0 : Nat := 0x2222000022220000
def s_0 : List Nat := [0x202000002020000, 0x22000000220000, 0x22220000]
def g_0 : Nat := 0x2000002220000
def bds_0 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_0 : KnownBin bds_0 := by intro b hb; simp [bds_0] at hb
theorem sub_0 : ∀ b ∈ bds_0, m_0 &&& b.1 = b.1 := by intro b hb; simp [bds_0] at hb
theorem gl_0 : ∀ b ∈ bds_0, canon b.1 g_0 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_0] at hb
def f_0 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_0 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_0 : dagCheckRootsF m_0 g_0 bds_0 (dagRefF 1 (dagTraceF m_0 s_0 3 f_0) l_0 0) s_0 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_0_0 : treeBlockF 0 1 (dagCheckNodeF m_0 g_0 bds_0 1 (dagTraceF m_0 s_0 3 f_0) l_0) = true := by decide +kernel
theorem nc_0 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_0 g_0 bds_0 1 (dagTraceF m_0 s_0 3 f_0) l_0) i = true := fun _ h1 h2 => treeBlockF_at nb_0_0 h1 h2
theorem lb_0 : LowerBin m_0 s_0 g_0 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_0 sub_0 gl_0 rc_0 nc_0

def m_1 : Nat := 0xa0a00000a0a0000
def s_1 : List Nat := [0x202000002020000, 0xa0000000a0000, 0xa0a0000]
def g_1 : Nat := 0x20000020a0000
def bds_1 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_1 : KnownBin bds_1 := by intro b hb; simp [bds_1] at hb
theorem sub_1 : ∀ b ∈ bds_1, m_1 &&& b.1 = b.1 := by intro b hb; simp [bds_1] at hb
theorem gl_1 : ∀ b ∈ bds_1, canon b.1 g_1 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_1] at hb
def f_1 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_1 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_1 : dagCheckRootsF m_1 g_1 bds_1 (dagRefF 1 (dagTraceF m_1 s_1 3 f_1) l_1 0) s_1 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_1_0 : treeBlockF 0 1 (dagCheckNodeF m_1 g_1 bds_1 1 (dagTraceF m_1 s_1 3 f_1) l_1) = true := by decide +kernel
theorem nc_1 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_1 g_1 bds_1 1 (dagTraceF m_1 s_1 3 f_1) l_1) i = true := fun _ h1 h2 => treeBlockF_at nb_1_0 h1 h2
theorem lb_1 : LowerBin m_1 s_1 g_1 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1 sub_1 gl_1 rc_1 nc_1

def m_2 : Nat := 0x3030000030300000
def s_2 : List Nat := [0x1010000010100000, 0x30000000300000, 0x30300000]
def g_2 : Nat := 0x10000010300000
def bds_2 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_2 : KnownBin bds_2 := by intro b hb; simp [bds_2] at hb
theorem sub_2 : ∀ b ∈ bds_2, m_2 &&& b.1 = b.1 := by intro b hb; simp [bds_2] at hb
theorem gl_2 : ∀ b ∈ bds_2, canon b.1 g_2 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_2] at hb
def f_2 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_2 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_2 : dagCheckRootsF m_2 g_2 bds_2 (dagRefF 1 (dagTraceF m_2 s_2 3 f_2) l_2 0) s_2 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_2_0 : treeBlockF 0 1 (dagCheckNodeF m_2 g_2 bds_2 1 (dagTraceF m_2 s_2 3 f_2) l_2) = true := by decide +kernel
theorem nc_2 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_2 g_2 bds_2 1 (dagTraceF m_2 s_2 3 f_2) l_2) i = true := fun _ h1 h2 => treeBlockF_at nb_2_0 h1 h2
theorem lb_2 : LowerBin m_2 s_2 g_2 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2 sub_2 gl_2 rc_2 nc_2

def m_3 : Nat := 0xaa000000aa0000
def s_3 : List Nat := [0x22000000220000, 0xa0000000a0000, 0xaa0000]
def g_3 : Nat := 0x20000002a0000
def bds_3 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_3 : KnownBin bds_3 := by intro b hb; simp [bds_3] at hb
theorem sub_3 : ∀ b ∈ bds_3, m_3 &&& b.1 = b.1 := by intro b hb; simp [bds_3] at hb
theorem gl_3 : ∀ b ∈ bds_3, canon b.1 g_3 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_3] at hb
def f_3 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_3 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_3 : dagCheckRootsF m_3 g_3 bds_3 (dagRefF 1 (dagTraceF m_3 s_3 3 f_3) l_3 0) s_3 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_3_0 : treeBlockF 0 1 (dagCheckNodeF m_3 g_3 bds_3 1 (dagTraceF m_3 s_3 3 f_3) l_3) = true := by decide +kernel
theorem nc_3 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_3 g_3 bds_3 1 (dagTraceF m_3 s_3 3 f_3) l_3) i = true := fun _ h1 h2 => treeBlockF_at nb_3_0 h1 h2
theorem lb_3 : LowerBin m_3 s_3 g_3 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_3 sub_3 gl_3 rc_3 nc_3

def m_4 : Nat := 0xaa000000aa
def s_4 : List Nat := [0x2200000022, 0xa0000000a, 0xaa]
def g_4 : Nat := 0x20000002a
def bds_4 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_4 : KnownBin bds_4 := by intro b hb; simp [bds_4] at hb
theorem sub_4 : ∀ b ∈ bds_4, m_4 &&& b.1 = b.1 := by intro b hb; simp [bds_4] at hb
theorem gl_4 : ∀ b ∈ bds_4, canon b.1 g_4 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_4] at hb
def f_4 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_4 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_4 : dagCheckRootsF m_4 g_4 bds_4 (dagRefF 1 (dagTraceF m_4 s_4 3 f_4) l_4 0) s_4 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_4_0 : treeBlockF 0 1 (dagCheckNodeF m_4 g_4 bds_4 1 (dagTraceF m_4 s_4 3 f_4) l_4) = true := by decide +kernel
theorem nc_4 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_4 g_4 bds_4 1 (dagTraceF m_4 s_4 3 f_4) l_4) i = true := fun _ h1 h2 => treeBlockF_at nb_4_0 h1 h2
theorem lb_4 : LowerBin m_4 s_4 g_4 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_4 sub_4 gl_4 rc_4 nc_4

def m_5 : Nat := 0x3300000033000000
def s_5 : List Nat := [0x1100000011000000, 0x300000003000000, 0x33000000]
def g_5 : Nat := 0x100000013000000
def bds_5 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_5 : KnownBin bds_5 := by intro b hb; simp [bds_5] at hb
theorem sub_5 : ∀ b ∈ bds_5, m_5 &&& b.1 = b.1 := by intro b hb; simp [bds_5] at hb
theorem gl_5 : ∀ b ∈ bds_5, canon b.1 g_5 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_5] at hb
def f_5 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_5 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_5 : dagCheckRootsF m_5 g_5 bds_5 (dagRefF 1 (dagTraceF m_5 s_5 3 f_5) l_5 0) s_5 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_5_0 : treeBlockF 0 1 (dagCheckNodeF m_5 g_5 bds_5 1 (dagTraceF m_5 s_5 3 f_5) l_5) = true := by decide +kernel
theorem nc_5 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_5 g_5 bds_5 1 (dagTraceF m_5 s_5 3 f_5) l_5) i = true := fun _ h1 h2 => treeBlockF_at nb_5_0 h1 h2
theorem lb_5 : LowerBin m_5 s_5 g_5 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_5 sub_5 gl_5 rc_5 nc_5

def m_6 : Nat := 0x4444444400000000
def s_6 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_6 : Nat := 0x4044400000000
def bds_6 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_6 : KnownBin bds_6 := by intro b hb; simp [bds_6] at hb
theorem sub_6 : ∀ b ∈ bds_6, m_6 &&& b.1 = b.1 := by intro b hb; simp [bds_6] at hb
theorem gl_6 : ∀ b ∈ bds_6, canon b.1 g_6 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_6] at hb
def f_6 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_6 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_6 : dagCheckRootsF m_6 g_6 bds_6 (dagRefF 1 (dagTraceF m_6 s_6 3 f_6) l_6 0) s_6 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_6_0 : treeBlockF 0 1 (dagCheckNodeF m_6 g_6 bds_6 1 (dagTraceF m_6 s_6 3 f_6) l_6) = true := by decide +kernel
theorem nc_6 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_6 g_6 bds_6 1 (dagTraceF m_6 s_6 3 f_6) l_6) i = true := fun _ h1 h2 => treeBlockF_at nb_6_0 h1 h2
theorem lb_6 : LowerBin m_6 s_6 g_6 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_6 sub_6 gl_6 rc_6 nc_6

def m_7 : Nat := 0x44444444
def s_7 : List Nat := [0x4040404, 0x440044, 0x4444]
def g_7 : Nat := 0x40444
def bds_7 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_7 : KnownBin bds_7 := by intro b hb; simp [bds_7] at hb
theorem sub_7 : ∀ b ∈ bds_7, m_7 &&& b.1 = b.1 := by intro b hb; simp [bds_7] at hb
theorem gl_7 : ∀ b ∈ bds_7, canon b.1 g_7 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_7] at hb
def f_7 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_7 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_7 : dagCheckRootsF m_7 g_7 bds_7 (dagRefF 1 (dagTraceF m_7 s_7 3 f_7) l_7 0) s_7 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_7_0 : treeBlockF 0 1 (dagCheckNodeF m_7 g_7 bds_7 1 (dagTraceF m_7 s_7 3 f_7) l_7) = true := by decide +kernel
theorem nc_7 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_7 g_7 bds_7 1 (dagTraceF m_7 s_7 3 f_7) l_7) i = true := fun _ h1 h2 => treeBlockF_at nb_7_0 h1 h2
theorem lb_7 : LowerBin m_7 s_7 g_7 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_7 sub_7 gl_7 rc_7 nc_7

def m_8 : Nat := 0x5050505000000000
def s_8 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_8 : Nat := 0x10105000000000
def bds_8 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_8 : KnownBin bds_8 := by intro b hb; simp [bds_8] at hb
theorem sub_8 : ∀ b ∈ bds_8, m_8 &&& b.1 = b.1 := by intro b hb; simp [bds_8] at hb
theorem gl_8 : ∀ b ∈ bds_8, canon b.1 g_8 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_8] at hb
def f_8 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_8 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_8 : dagCheckRootsF m_8 g_8 bds_8 (dagRefF 1 (dagTraceF m_8 s_8 3 f_8) l_8 0) s_8 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_8_0 : treeBlockF 0 1 (dagCheckNodeF m_8 g_8 bds_8 1 (dagTraceF m_8 s_8 3 f_8) l_8) = true := by decide +kernel
theorem nc_8 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_8 g_8 bds_8 1 (dagTraceF m_8 s_8 3 f_8) l_8) i = true := fun _ h1 h2 => treeBlockF_at nb_8_0 h1 h2
theorem lb_8 : LowerBin m_8 s_8 g_8 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_8 sub_8 gl_8 rc_8 nc_8

def m_9 : Nat := 0x5500550000000000
def s_9 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_9 : Nat := 0x100150000000000
def bds_9 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_9 : KnownBin bds_9 := by intro b hb; simp [bds_9] at hb
theorem sub_9 : ∀ b ∈ bds_9, m_9 &&& b.1 = b.1 := by intro b hb; simp [bds_9] at hb
theorem gl_9 : ∀ b ∈ bds_9, canon b.1 g_9 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_9] at hb
def f_9 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_9 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_9 : dagCheckRootsF m_9 g_9 bds_9 (dagRefF 1 (dagTraceF m_9 s_9 3 f_9) l_9 0) s_9 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_9_0 : treeBlockF 0 1 (dagCheckNodeF m_9 g_9 bds_9 1 (dagTraceF m_9 s_9 3 f_9) l_9) = true := by decide +kernel
theorem nc_9 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_9 g_9 bds_9 1 (dagTraceF m_9 s_9 3 f_9) l_9) i = true := fun _ h1 h2 => treeBlockF_at nb_9_0 h1 h2
theorem lb_9 : LowerBin m_9 s_9 g_9 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_9 sub_9 gl_9 rc_9 nc_9

def m_10 : Nat := 0x3300330000000000
def s_10 : List Nat := [0x1100110000000000, 0x300030000000000, 0x330000000000]
def g_10 : Nat := 0x100130000000000
def bds_10 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_10 : KnownBin bds_10 := by intro b hb; simp [bds_10] at hb
theorem sub_10 : ∀ b ∈ bds_10, m_10 &&& b.1 = b.1 := by intro b hb; simp [bds_10] at hb
theorem gl_10 : ∀ b ∈ bds_10, canon b.1 g_10 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_10] at hb
def f_10 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_10 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_10 : dagCheckRootsF m_10 g_10 bds_10 (dagRefF 1 (dagTraceF m_10 s_10 3 f_10) l_10 0) s_10 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_10_0 : treeBlockF 0 1 (dagCheckNodeF m_10 g_10 bds_10 1 (dagTraceF m_10 s_10 3 f_10) l_10) = true := by decide +kernel
theorem nc_10 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_10 g_10 bds_10 1 (dagTraceF m_10 s_10 3 f_10) l_10) i = true := fun _ h1 h2 => treeBlockF_at nb_10_0 h1 h2
theorem lb_10 : LowerBin m_10 s_10 g_10 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_10 sub_10 gl_10 rc_10 nc_10

def m_11 : Nat := 0xf000f0000000000
def s_11 : List Nat := [0x500050000000000, 0x300030000000000, 0xf0000000000]
def g_11 : Nat := 0x100070000000000
def bds_11 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_11 : KnownBin bds_11 := by intro b hb; simp [bds_11] at hb
theorem sub_11 : ∀ b ∈ bds_11, m_11 &&& b.1 = b.1 := by intro b hb; simp [bds_11] at hb
theorem gl_11 : ∀ b ∈ bds_11, canon b.1 g_11 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_11] at hb
def f_11 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_11 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_11 : dagCheckRootsF m_11 g_11 bds_11 (dagRefF 1 (dagTraceF m_11 s_11 3 f_11) l_11 0) s_11 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_11_0 : treeBlockF 0 1 (dagCheckNodeF m_11 g_11 bds_11 1 (dagTraceF m_11 s_11 3 f_11) l_11) = true := by decide +kernel
theorem nc_11 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_11 g_11 bds_11 1 (dagTraceF m_11 s_11 3 f_11) l_11) i = true := fun _ h1 h2 => treeBlockF_at nb_11_0 h1 h2
theorem lb_11 : LowerBin m_11 s_11 g_11 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_11 sub_11 gl_11 rc_11 nc_11

def m_12 : Nat := 0x5555000000000000
def s_12 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_12 : Nat := 0x115000000000000
def bds_12 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_12 : KnownBin bds_12 := by intro b hb; simp [bds_12] at hb
theorem sub_12 : ∀ b ∈ bds_12, m_12 &&& b.1 = b.1 := by intro b hb; simp [bds_12] at hb
theorem gl_12 : ∀ b ∈ bds_12, canon b.1 g_12 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_12] at hb
def f_12 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_12 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_12 : dagCheckRootsF m_12 g_12 bds_12 (dagRefF 1 (dagTraceF m_12 s_12 3 f_12) l_12 0) s_12 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_12_0 : treeBlockF 0 1 (dagCheckNodeF m_12 g_12 bds_12 1 (dagTraceF m_12 s_12 3 f_12) l_12) = true := by decide +kernel
theorem nc_12 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_12 g_12 bds_12 1 (dagTraceF m_12 s_12 3 f_12) l_12) i = true := fun _ h1 h2 => treeBlockF_at nb_12_0 h1 h2
theorem lb_12 : LowerBin m_12 s_12 g_12 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_12 sub_12 gl_12 rc_12 nc_12

def m_13 : Nat := 0xaaaa0000
def s_13 : List Nat := [0x22220000, 0xa0a0000, 0xaa0000]
def g_13 : Nat := 0x22a0000
def bds_13 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_13 : KnownBin bds_13 := by intro b hb; simp [bds_13] at hb
theorem sub_13 : ∀ b ∈ bds_13, m_13 &&& b.1 = b.1 := by intro b hb; simp [bds_13] at hb
theorem gl_13 : ∀ b ∈ bds_13, canon b.1 g_13 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_13] at hb
def f_13 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_13 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_13 : dagCheckRootsF m_13 g_13 bds_13 (dagRefF 1 (dagTraceF m_13 s_13 3 f_13) l_13 0) s_13 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_13_0 : treeBlockF 0 1 (dagCheckNodeF m_13 g_13 bds_13 1 (dagTraceF m_13 s_13 3 f_13) l_13) = true := by decide +kernel
theorem nc_13 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_13 g_13 bds_13 1 (dagTraceF m_13 s_13 3 f_13) l_13) i = true := fun _ h1 h2 => treeBlockF_at nb_13_0 h1 h2
theorem lb_13 : LowerBin m_13 s_13 g_13 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_13 sub_13 gl_13 rc_13 nc_13

def m_14 : Nat := 0xaaaa
def s_14 : List Nat := [0x2222, 0xa0a, 0xaa]
def g_14 : Nat := 0x22a
def bds_14 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_14 : KnownBin bds_14 := by intro b hb; simp [bds_14] at hb
theorem sub_14 : ∀ b ∈ bds_14, m_14 &&& b.1 = b.1 := by intro b hb; simp [bds_14] at hb
theorem gl_14 : ∀ b ∈ bds_14, canon b.1 g_14 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_14] at hb
def f_14 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_14 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_14 : dagCheckRootsF m_14 g_14 bds_14 (dagRefF 1 (dagTraceF m_14 s_14 3 f_14) l_14 0) s_14 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_14_0 : treeBlockF 0 1 (dagCheckNodeF m_14 g_14 bds_14 1 (dagTraceF m_14 s_14 3 f_14) l_14) = true := by decide +kernel
theorem nc_14 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_14 g_14 bds_14 1 (dagTraceF m_14 s_14 3 f_14) l_14) i = true := fun _ h1 h2 => treeBlockF_at nb_14_0 h1 h2
theorem lb_14 : LowerBin m_14 s_14 g_14 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_14 sub_14 gl_14 rc_14 nc_14

def m_15 : Nat := 0x3333000000000000
def s_15 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_15 : Nat := 0x113000000000000
def bds_15 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_15 : KnownBin bds_15 := by intro b hb; simp [bds_15] at hb
theorem sub_15 : ∀ b ∈ bds_15, m_15 &&& b.1 = b.1 := by intro b hb; simp [bds_15] at hb
theorem gl_15 : ∀ b ∈ bds_15, canon b.1 g_15 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_15] at hb
def f_15 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_15 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsF m_15 g_15 bds_15 (dagRefF 1 (dagTraceF m_15 s_15 3 f_15) l_15 0) s_15 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_15_0 : treeBlockF 0 1 (dagCheckNodeF m_15 g_15 bds_15 1 (dagTraceF m_15 s_15 3 f_15) l_15) = true := by decide +kernel
theorem nc_15 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_15 g_15 bds_15 1 (dagTraceF m_15 s_15 3 f_15) l_15) i = true := fun _ h1 h2 => treeBlockF_at nb_15_0 h1 h2
theorem lb_15 : LowerBin m_15 s_15 g_15 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_15 sub_15 gl_15 rc_15 nc_15

def m_16 : Nat := 0xcccc
def s_16 : List Nat := [0x4444, 0xc0c, 0xcc]
def g_16 : Nat := 0x44c
def bds_16 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_16 : KnownBin bds_16 := by intro b hb; simp [bds_16] at hb
theorem sub_16 : ∀ b ∈ bds_16, m_16 &&& b.1 = b.1 := by intro b hb; simp [bds_16] at hb
theorem gl_16 : ∀ b ∈ bds_16, canon b.1 g_16 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_16] at hb
def f_16 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_16 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsF m_16 g_16 bds_16 (dagRefF 1 (dagTraceF m_16 s_16 3 f_16) l_16 0) s_16 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16_0 : treeBlockF 0 1 (dagCheckNodeF m_16 g_16 bds_16 1 (dagTraceF m_16 s_16 3 f_16) l_16) = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_16 g_16 bds_16 1 (dagTraceF m_16 s_16 3 f_16) l_16) i = true := fun _ h1 h2 => treeBlockF_at nb_16_0 h1 h2
theorem lb_16 : LowerBin m_16 s_16 g_16 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_16 sub_16 gl_16 rc_16 nc_16

def m_17 : Nat := 0xf0f000000000000
def s_17 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_17 : Nat := 0x107000000000000
def bds_17 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_17 : KnownBin bds_17 := by intro b hb; simp [bds_17] at hb
theorem sub_17 : ∀ b ∈ bds_17, m_17 &&& b.1 = b.1 := by intro b hb; simp [bds_17] at hb
theorem gl_17 : ∀ b ∈ bds_17, canon b.1 g_17 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_17] at hb
def f_17 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_17 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsF m_17 g_17 bds_17 (dagRefF 1 (dagTraceF m_17 s_17 3 f_17) l_17 0) s_17 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17_0 : treeBlockF 0 1 (dagCheckNodeF m_17 g_17 bds_17 1 (dagTraceF m_17 s_17 3 f_17) l_17) = true := by decide +kernel
theorem nc_17 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_17 g_17 bds_17 1 (dagTraceF m_17 s_17 3 f_17) l_17) i = true := fun _ h1 h2 => treeBlockF_at nb_17_0 h1 h2
theorem lb_17 : LowerBin m_17 s_17 g_17 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_17 sub_17 gl_17 rc_17 nc_17

def m_18 : Nat := 0xf0f0
def s_18 : List Nat := [0x5050, 0x3030, 0xf0]
def g_18 : Nat := 0x1070
def bds_18 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_18 : KnownBin bds_18 := by intro b hb; simp [bds_18] at hb
theorem sub_18 : ∀ b ∈ bds_18, m_18 &&& b.1 = b.1 := by intro b hb; simp [bds_18] at hb
theorem gl_18 : ∀ b ∈ bds_18, canon b.1 g_18 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_18] at hb
def f_18 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_18 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsF m_18 g_18 bds_18 (dagRefF 1 (dagTraceF m_18 s_18 3 f_18) l_18 0) s_18 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18_0 : treeBlockF 0 1 (dagCheckNodeF m_18 g_18 bds_18 1 (dagTraceF m_18 s_18 3 f_18) l_18) = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_18 g_18 bds_18 1 (dagTraceF m_18 s_18 3 f_18) l_18) i = true := fun _ h1 h2 => treeBlockF_at nb_18_0 h1 h2
theorem lb_18 : LowerBin m_18 s_18 g_18 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_18 sub_18 gl_18 rc_18 nc_18

def m_19 : Nat := 0xff000000000000
def s_19 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_19 : Nat := 0x17000000000000
def bds_19 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_19 : KnownBin bds_19 := by intro b hb; simp [bds_19] at hb
theorem sub_19 : ∀ b ∈ bds_19, m_19 &&& b.1 = b.1 := by intro b hb; simp [bds_19] at hb
theorem gl_19 : ∀ b ∈ bds_19, canon b.1 g_19 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_19] at hb
def f_19 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_19 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsF m_19 g_19 bds_19 (dagRefF 1 (dagTraceF m_19 s_19 3 f_19) l_19 0) s_19 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_0 : treeBlockF 0 1 (dagCheckNodeF m_19 g_19 bds_19 1 (dagTraceF m_19 s_19 3 f_19) l_19) = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_19 g_19 bds_19 1 (dagTraceF m_19 s_19 3 f_19) l_19) i = true := fun _ h1 h2 => treeBlockF_at nb_19_0 h1 h2
theorem lb_19 : LowerBin m_19 s_19 g_19 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_19 sub_19 gl_19 rc_19 nc_19

def m_20 : Nat := 0xff0000000000
def s_20 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_20 : Nat := 0x170000000000
def bds_20 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_20 : KnownBin bds_20 := by intro b hb; simp [bds_20] at hb
theorem sub_20 : ∀ b ∈ bds_20, m_20 &&& b.1 = b.1 := by intro b hb; simp [bds_20] at hb
theorem gl_20 : ∀ b ∈ bds_20, canon b.1 g_20 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_20] at hb
def f_20 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_20 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsF m_20 g_20 bds_20 (dagRefF 1 (dagTraceF m_20 s_20 3 f_20) l_20 0) s_20 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20_0 : treeBlockF 0 1 (dagCheckNodeF m_20 g_20 bds_20 1 (dagTraceF m_20 s_20 3 f_20) l_20) = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_20 g_20 bds_20 1 (dagTraceF m_20 s_20 3 f_20) l_20) i = true := fun _ h1 h2 => treeBlockF_at nb_20_0 h1 h2
theorem lb_20 : LowerBin m_20 s_20 g_20 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_20 sub_20 gl_20 rc_20 nc_20

def m_21 : Nat := 0xff00
def s_21 : List Nat := [0x5500, 0x3300, 0xf00]
def g_21 : Nat := 0x1700
def bds_21 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_21 : KnownBin bds_21 := by intro b hb; simp [bds_21] at hb
theorem sub_21 : ∀ b ∈ bds_21, m_21 &&& b.1 = b.1 := by intro b hb; simp [bds_21] at hb
theorem gl_21 : ∀ b ∈ bds_21, canon b.1 g_21 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_21] at hb
def f_21 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_21 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsF m_21 g_21 bds_21 (dagRefF 1 (dagTraceF m_21 s_21 3 f_21) l_21 0) s_21 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_0 : treeBlockF 0 1 (dagCheckNodeF m_21 g_21 bds_21 1 (dagTraceF m_21 s_21 3 f_21) l_21) = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_21 g_21 bds_21 1 (dagTraceF m_21 s_21 3 f_21) l_21) i = true := fun _ h1 h2 => treeBlockF_at nb_21_0 h1 h2
theorem lb_21 : LowerBin m_21 s_21 g_21 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_21 sub_21 gl_21 rc_21 nc_21

def m_22 : Nat := 0x2222222222222222
def s_22 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_22 : Nat := 0x2020202220222
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_22 : KnownBin bds_22 := by
  intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_22 : ∀ b ∈ bds_22, m_22 &&& b.1 = b.1 := by intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_22 : ∀ b ∈ bds_22, canon b.1 g_22 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_22 : Nat → Nat × Nat := fun _ => (0, 0)
def l_22 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsF m_22 g_22 bds_22 (dagRefF 0 (dagTraceF m_22 s_22 4 f_22) l_22 0) s_22 4 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_22 g_22 bds_22 0 (dagTraceF m_22 s_22 4 f_22) l_22 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_22 : LowerBin m_22 s_22 g_22 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_22 sub_22 gl_22 rc_22 nc_22

def m_23 : Nat := 0x5050505050505050
def s_23 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_23 : Nat := 0x10105010101050
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_23 : KnownBin bds_23 := by
  intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_23 : ∀ b ∈ bds_23, m_23 &&& b.1 = b.1 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_23 : ∀ b ∈ bds_23, canon b.1 g_23 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_23 : Nat → Nat × Nat := fun _ => (0, 0)
def l_23 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsF m_23 g_23 bds_23 (dagRefF 0 (dagTraceF m_23 s_23 4 f_23) l_23 0) s_23 4 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_23 g_23 bds_23 0 (dagTraceF m_23 s_23 4 f_23) l_23 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_23 sub_23 gl_23 rc_23 nc_23

def m_24 : Nat := 0xa0a0a0a0a0a0a0a
def s_24 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_24 : Nat := 0x20202020a020a
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_24 : KnownBin bds_24 := by
  intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_24 : ∀ b ∈ bds_24, m_24 &&& b.1 = b.1 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_24 : ∀ b ∈ bds_24, canon b.1 g_24 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
def l_24 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsF m_24 g_24 bds_24 (dagRefF 0 (dagTraceF m_24 s_24 4 f_24) l_24 0) s_24 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_24 g_24 bds_24 0 (dagTraceF m_24 s_24 4 f_24) l_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_24 sub_24 gl_24 rc_24 nc_24

def m_25 : Nat := 0x3030303030303030
def s_25 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_25 : Nat := 0x10101010301030
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_25 : KnownBin bds_25 := by
  intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_25 : ∀ b ∈ bds_25, m_25 &&& b.1 = b.1 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_25 : ∀ b ∈ bds_25, canon b.1 g_25 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
def l_25 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsF m_25 g_25 bds_25 (dagRefF 0 (dagTraceF m_25 s_25 4 f_25) l_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_25 g_25 bds_25 0 (dagTraceF m_25 s_25 4 f_25) l_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_25 sub_25 gl_25 rc_25 nc_25

def m_26 : Nat := 0x5500550055005500
def s_26 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_26 : Nat := 0x100150011001500
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_26 : KnownBin bds_26 := by
  intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_26 : ∀ b ∈ bds_26, m_26 &&& b.1 = b.1 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_26 : ∀ b ∈ bds_26, canon b.1 g_26 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
def l_26 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsF m_26 g_26 bds_26 (dagRefF 0 (dagTraceF m_26 s_26 4 f_26) l_26 0) s_26 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_26 g_26 bds_26 0 (dagTraceF m_26 s_26 4 f_26) l_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_26 sub_26 gl_26 rc_26 nc_26

def m_27 : Nat := 0x3300330033003300
def s_27 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]
def g_27 : Nat := 0x100130013001300
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_27 : KnownBin bds_27 := by
  intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_27 : ∀ b ∈ bds_27, m_27 &&& b.1 = b.1 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
def l_27 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsF m_27 g_27 bds_27 (dagRefF 0 (dagTraceF m_27 s_27 4 f_27) l_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_27 g_27 bds_27 0 (dagTraceF m_27 s_27 4 f_27) l_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0xf000f000f000f00
def s_28 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_28 : Nat := 0x100070003000700
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
theorem kn_28 : KnownBin bds_28 := by
  intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_11
theorem sub_28 : ∀ b ∈ bds_28, m_28 &&& b.1 = b.1 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_28 : Nat → Nat × Nat := fun _ => (0, 0)
def l_28 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsF m_28 g_28 bds_28 (dagRefF 0 (dagTraceF m_28 s_28 4 f_28) l_28 0) s_28 4 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_28 g_28 bds_28 0 (dagTraceF m_28 s_28 4 f_28) l_28 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_28 sub_28 gl_28 rc_28 nc_28

def m_29 : Nat := 0xaaaa0000aaaa0000
def s_29 : List Nat := [0x2222000022220000, 0xa0a00000a0a0000, 0xaa000000aa0000, 0xaaaa0000]
def g_29 : Nat := 0x20000022a0000
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_1, s_1, 4, g_1), (m_3, s_3, 4, g_3), (m_13, s_13, 4, g_13)]
theorem kn_29 : KnownBin bds_29 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_0
  · exact lb_1
  · exact lb_3
  · exact lb_13
theorem sub_29 : ∀ b ∈ bds_29, m_29 &&& b.1 = b.1 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_29 : ∀ b ∈ bds_29, canon b.1 g_29 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_29 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def l_29 : Nat → Nat → Option Nat := unpackLinksF 0x8e11c1fc3e17c0f81b43516a0d05a0340662cc15c2a1522a41482184027c4f81e13c0780e89d02b05049893024248088910220404801001e21e00b001 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b407c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 11 4 10 6 5
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsF m_29 g_29 bds_29 (dagRefF 43 (dagTraceF m_29 s_29 6 f_29) l_29 0) s_29 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_0 : treeBlockF 0 32 (dagCheckNodeF m_29 g_29 bds_29 43 (dagTraceF m_29 s_29 6 f_29) l_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_1 : treeBlockF 32 43 (dagCheckNodeF m_29 g_29 bds_29 43 (dagTraceF m_29 s_29 6 f_29) l_29) = true := by decide +kernel
theorem nj_29_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_29 g_29 bds_29 43 (dagTraceF m_29 s_29 6 f_29) l_29) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_29_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_29_1 h1 h2)
theorem nc_29 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_29 g_29 bds_29 43 (dagTraceF m_29 s_29 6 f_29) l_29) i = true := nj_29_1
theorem lb_29 : LowerBin m_29 s_29 g_29 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_29 sub_29 gl_29 rc_29 nc_29

def m_30 : Nat := 0x5555000055550000
def s_30 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_30 : Nat := 0x115000011150000
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
theorem kn_30 : KnownBin bds_30 := by
  intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_12
theorem sub_30 : ∀ b ∈ bds_30, m_30 &&& b.1 = b.1 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_30 : Nat → Nat × Nat := fun _ => (0, 0)
def l_30 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsF m_30 g_30 bds_30 (dagRefF 0 (dagTraceF m_30 s_30 4 f_30) l_30 0) s_30 4 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_30 g_30 bds_30 0 (dagTraceF m_30 s_30 4 f_30) l_30 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_30 sub_30 gl_30 rc_30 nc_30

def m_31 : Nat := 0x3333000033330000
def s_31 : List Nat := [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000]
def g_31 : Nat := 0x113000013330000
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_2, s_2, 4, g_2), (m_5, s_5, 4, g_5), (m_15, s_15, 4, g_15)]
theorem kn_31 : KnownBin bds_31 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_0
  · exact lb_2
  · exact lb_5
  · exact lb_15
theorem sub_31 : ∀ b ∈ bds_31, m_31 &&& b.1 = b.1 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_31 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def l_31 : Nat → Nat → Option Nat := unpackLinksF 0x8e11c1fc3f07c2f81b43606c0d45a0b40662cc15c2b0542a8148a18420841009f13e0784f01d12b0540a814128050098921222440809001e21e00b001 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d347d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 11 4 10 6 5
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsF m_31 g_31 bds_31 (dagRefF 43 (dagTraceF m_31 s_31 6 f_31) l_31 0) s_31 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_0 : treeBlockF 0 32 (dagCheckNodeF m_31 g_31 bds_31 43 (dagTraceF m_31 s_31 6 f_31) l_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_1 : treeBlockF 32 43 (dagCheckNodeF m_31 g_31 bds_31 43 (dagTraceF m_31 s_31 6 f_31) l_31) = true := by decide +kernel
theorem nj_31_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_31 g_31 bds_31 43 (dagTraceF m_31 s_31 6 f_31) l_31) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_31_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_31_1 h1 h2)
theorem nc_31 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_31 g_31 bds_31 43 (dagTraceF m_31 s_31 6 f_31) l_31) i = true := nj_31_1
theorem lb_31 : LowerBin m_31 s_31 g_31 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_31 sub_31 gl_31 rc_31 nc_31

def m_32 : Nat := 0xcccc0000cccc
def s_32 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_32 : Nat := 0x4440000044c
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
theorem kn_32 : KnownBin bds_32 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_16
theorem sub_32 : ∀ b ∈ bds_32, m_32 &&& b.1 = b.1 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_32 : ∀ b ∈ bds_32, canon b.1 g_32 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_32 : Nat → Nat × Nat := fun _ => (0, 0)
def l_32 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsF m_32 g_32 bds_32 (dagRefF 0 (dagTraceF m_32 s_32 4 f_32) l_32 0) s_32 4 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_32 g_32 bds_32 0 (dagTraceF m_32 s_32 4 f_32) l_32 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_32 sub_32 gl_32 rc_32 nc_32

def m_33 : Nat := 0xf0f00000f0f00000
def s_33 : List Nat := [0x5050000050500000, 0x3030000030300000, 0xf0000000f00000, 0xf0f00000]
def g_33 : Nat := 0x10000010300000
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_33 : ∀ b ∈ bds_33, m_33 &&& b.1 = b.1 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
def l_33 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsF m_33 g_33 bds_33 (dagRefF 0 (dagTraceF m_33 s_33 4 f_33) l_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_33 g_33 bds_33 0 (dagTraceF m_33 s_33 4 f_33) l_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_33 sub_33 gl_33 rc_33 nc_33

def m_34 : Nat := 0xf0f00000f0f0000
def s_34 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_34 : Nat := 0x1070000030f0000
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_34 : KnownBin bds_34 := by
  intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_34 : ∀ b ∈ bds_34, m_34 &&& b.1 = b.1 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
def l_34 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsF m_34 g_34 bds_34 (dagRefF 0 (dagTraceF m_34 s_34 4 f_34) l_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_34 g_34 bds_34 0 (dagTraceF m_34 s_34 4 f_34) l_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_34 sub_34 gl_34 rc_34 nc_34

def m_35 : Nat := 0xf0f00000f0f0
def s_35 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_35 : Nat := 0x105000001070
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 4, g_18)]
theorem kn_35 : KnownBin bds_35 := by
  intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_18
theorem sub_35 : ∀ b ∈ bds_35, m_35 &&& b.1 = b.1 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
def l_35 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsF m_35 g_35 bds_35 (dagRefF 0 (dagTraceF m_35 s_35 4 f_35) l_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_35 g_35 bds_35 0 (dagTraceF m_35 s_35 4 f_35) l_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_35 sub_35 gl_35 rc_35 nc_35

def m_36 : Nat := 0xff000000ff000000
def s_36 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_36 : Nat := 0x100000013000000
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_36 : KnownBin bds_36 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_36 : ∀ b ∈ bds_36, m_36 &&& b.1 = b.1 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_36 : ∀ b ∈ bds_36, canon b.1 g_36 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
def l_36 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsF m_36 g_36 bds_36 (dagRefF 0 (dagTraceF m_36 s_36 4 f_36) l_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_36 g_36 bds_36 0 (dagTraceF m_36 s_36 4 f_36) l_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_36 sub_36 gl_36 rc_36 nc_36

def m_37 : Nat := 0xff000000ff0000
def s_37 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_37 : Nat := 0x170000003f0000
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_37 : KnownBin bds_37 := by
  intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_37 : ∀ b ∈ bds_37, m_37 &&& b.1 = b.1 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_37 : ∀ b ∈ bds_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
def l_37 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsF m_37 g_37 bds_37 (dagRefF 0 (dagTraceF m_37 s_37 4 f_37) l_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_37 g_37 bds_37 0 (dagTraceF m_37 s_37 4 f_37) l_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_37 sub_37 gl_37 rc_37 nc_37

def m_38 : Nat := 0xff000000ff
def s_38 : List Nat := [0x5500000055, 0x3300000033, 0xf0000000f, 0xff]
def g_38 : Nat := 0x570000007f
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_38 : ∀ b ∈ bds_38, m_38 &&& b.1 = b.1 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
def l_38 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsF m_38 g_38 bds_38 (dagRefF 0 (dagTraceF m_38 s_38 4 f_38) l_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_38 g_38 bds_38 0 (dagTraceF m_38 s_38 4 f_38) l_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_38 sub_38 gl_38 rc_38 nc_38

def m_39 : Nat := 0x5555555500000000
def s_39 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_39 : Nat := 0x115155500000000
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6), (m_8, s_8, 4, g_8), (m_9, s_9, 4, g_9), (m_12, s_12, 4, g_12)]
theorem kn_39 : KnownBin bds_39 := by
  intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_6
  · exact lb_8
  · exact lb_9
  · exact lb_12
theorem sub_39 : ∀ b ∈ bds_39, m_39 &&& b.1 = b.1 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_39 : ∀ b ∈ bds_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_39 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def l_39 : Nat → Nat → Option Nat := unpackLinksF 0x8e11c1fc3f07c2f81b43606c0d45a0b40662cc15c2b0542a8148a18420841009f13e0784f01d12b0540a814128050098921222440809001e21e00b001 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d347d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 11 4 10 6 5
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsF m_39 g_39 bds_39 (dagRefF 43 (dagTraceF m_39 s_39 6 f_39) l_39 0) s_39 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_39_0 : treeBlockF 0 32 (dagCheckNodeF m_39 g_39 bds_39 43 (dagTraceF m_39 s_39 6 f_39) l_39) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_39_1 : treeBlockF 32 43 (dagCheckNodeF m_39 g_39 bds_39 43 (dagTraceF m_39 s_39 6 f_39) l_39) = true := by decide +kernel
theorem nj_39_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_39 g_39 bds_39 43 (dagTraceF m_39 s_39 6 f_39) l_39) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_39_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_39_1 h1 h2)
theorem nc_39 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_39 g_39 bds_39 43 (dagTraceF m_39 s_39 6 f_39) l_39) i = true := nj_39_1
theorem lb_39 : LowerBin m_39 s_39 g_39 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_39 sub_39 gl_39 rc_39 nc_39

def m_40 : Nat := 0xcccccccc00000000
def s_40 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_40 : Nat := 0x4044400000000
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_40 : KnownBin bds_40 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_40 : ∀ b ∈ bds_40, m_40 &&& b.1 = b.1 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
def l_40 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsF m_40 g_40 bds_40 (dagRefF 0 (dagTraceF m_40 s_40 4 f_40) l_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_40 g_40 bds_40 0 (dagTraceF m_40 s_40 4 f_40) l_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_40 sub_40 gl_40 rc_40 nc_40

def m_41 : Nat := 0x3333333300000000
def s_41 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_41 : Nat := 0x113131300000000
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
theorem kn_41 : KnownBin bds_41 := by
  intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_10
theorem sub_41 : ∀ b ∈ bds_41, m_41 &&& b.1 = b.1 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_41 : ∀ b ∈ bds_41, canon b.1 g_41 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
def l_41 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsF m_41 g_41 bds_41 (dagRefF 0 (dagTraceF m_41 s_41 4 f_41) l_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_41 g_41 bds_41 0 (dagTraceF m_41 s_41 4 f_41) l_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_41 sub_41 gl_41 rc_41 nc_41

def m_42 : Nat := 0xcccccccc
def s_42 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_42 : Nat := 0xc044c
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_42 : KnownBin bds_42 := by
  intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
theorem sub_42 : ∀ b ∈ bds_42, m_42 &&& b.1 = b.1 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_42 : ∀ b ∈ bds_42, canon b.1 g_42 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
def l_42 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsF m_42 g_42 bds_42 (dagRefF 0 (dagTraceF m_42 s_42 4 f_42) l_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_42 g_42 bds_42 0 (dagTraceF m_42 s_42 4 f_42) l_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_42 sub_42 gl_42 rc_42 nc_42

def m_43 : Nat := 0xf0f0f0f000000000
def s_43 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_43 : Nat := 0x10105000000000
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_43 : KnownBin bds_43 := by
  intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_43 : ∀ b ∈ bds_43, m_43 &&& b.1 = b.1 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_43 : ∀ b ∈ bds_43, canon b.1 g_43 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
def l_43 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsF m_43 g_43 bds_43 (dagRefF 0 (dagTraceF m_43 s_43 4 f_43) l_43 0) s_43 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_43 g_43 bds_43 0 (dagTraceF m_43 s_43 4 f_43) l_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_43 sub_43 gl_43 rc_43 nc_43

def m_44 : Nat := 0xf0f0f0f00000000
def s_44 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_44 : Nat := 0x107070700000000
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
theorem kn_44 : KnownBin bds_44 := by
  intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_11
theorem sub_44 : ∀ b ∈ bds_44, m_44 &&& b.1 = b.1 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_44 : ∀ b ∈ bds_44, canon b.1 g_44 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
def l_44 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsF m_44 g_44 bds_44 (dagRefF 0 (dagTraceF m_44 s_44 4 f_44) l_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_44 g_44 bds_44 0 (dagTraceF m_44 s_44 4 f_44) l_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_44 sub_44 gl_44 rc_44 nc_44

def m_45 : Nat := 0xf0f0f0f0
def s_45 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_45 : Nat := 0x10301070
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 4, g_18)]
theorem kn_45 : KnownBin bds_45 := by
  intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_18
theorem sub_45 : ∀ b ∈ bds_45, m_45 &&& b.1 = b.1 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_45 : ∀ b ∈ bds_45, canon b.1 g_45 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
def l_45 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsF m_45 g_45 bds_45 (dagRefF 0 (dagTraceF m_45 s_45 4 f_45) l_45 0) s_45 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_45 g_45 bds_45 0 (dagTraceF m_45 s_45 4 f_45) l_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_45 sub_45 gl_45 rc_45 nc_45

def m_46 : Nat := 0xff00ff0000000000
def s_46 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_46 : Nat := 0x100170000000000
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9), (m_10, s_10, 4, g_10), (m_11, s_11, 4, g_11), (m_20, s_20, 4, g_20)]
theorem kn_46 : KnownBin bds_46 := by
  intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_9
  · exact lb_10
  · exact lb_11
  · exact lb_20
theorem sub_46 : ∀ b ∈ bds_46, m_46 &&& b.1 = b.1 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_46 : ∀ b ∈ bds_46, canon b.1 g_46 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_46 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def l_46 : Nat → Nat → Option Nat := unpackLinksF 0x8e11c1fc3e17c0f81b43516a0d05a0340662cc15c2a1522a41482184027c4f81e13c0780e89d02b05049893024248088910220404801001e21e00b001 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b407c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 11 4 10 6 5
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsF m_46 g_46 bds_46 (dagRefF 43 (dagTraceF m_46 s_46 6 f_46) l_46 0) s_46 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_0 : treeBlockF 0 32 (dagCheckNodeF m_46 g_46 bds_46 43 (dagTraceF m_46 s_46 6 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_1 : treeBlockF 32 43 (dagCheckNodeF m_46 g_46 bds_46 43 (dagTraceF m_46 s_46 6 f_46) l_46) = true := by decide +kernel
theorem nj_46_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_46 g_46 bds_46 43 (dagTraceF m_46 s_46 6 f_46) l_46) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_46_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_46_1 h1 h2)
theorem nc_46 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_46 g_46 bds_46 43 (dagTraceF m_46 s_46 6 f_46) l_46) i = true := nj_46_1
theorem lb_46 : LowerBin m_46 s_46 g_46 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_46 sub_46 gl_46 rc_46 nc_46

def m_47 : Nat := 0xff00ff00000000
def s_47 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_47 : Nat := 0x17005700000000
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 4, g_19)]
theorem kn_47 : KnownBin bds_47 := by
  intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_19
theorem sub_47 : ∀ b ∈ bds_47, m_47 &&& b.1 = b.1 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_47 : ∀ b ∈ bds_47, canon b.1 g_47 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_47 : Nat → Nat × Nat := fun _ => (0, 0)
def l_47 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsF m_47 g_47 bds_47 (dagRefF 0 (dagTraceF m_47 s_47 4 f_47) l_47 0) s_47 4 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_47 g_47 bds_47 0 (dagTraceF m_47 s_47 4 f_47) l_47 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_47 : LowerBin m_47 s_47 g_47 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_47 sub_47 gl_47 rc_47 nc_47

def m_48 : Nat := 0xffff000000000000
def s_48 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_48 : Nat := 0x117000000000000
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12), (m_15, s_15, 4, g_15), (m_17, s_17, 4, g_17), (m_19, s_19, 4, g_19)]
theorem kn_48 : KnownBin bds_48 := by
  intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_12
  · exact lb_15
  · exact lb_17
  · exact lb_19
theorem sub_48 : ∀ b ∈ bds_48, m_48 &&& b.1 = b.1 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_48 : ∀ b ∈ bds_48, canon b.1 g_48 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_48 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def l_48 : Nat → Nat → Option Nat := unpackLinksF 0x8e11c1fc3e17c0f81b43516a0d05a0340662cc15c2a1522a41482184027c4f81e13c0780e89d02b05049893024248088910220404801001e21e00b001 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b407c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 11 4 10 6 5
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsF m_48 g_48 bds_48 (dagRefF 43 (dagTraceF m_48 s_48 6 f_48) l_48 0) s_48 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_0 : treeBlockF 0 32 (dagCheckNodeF m_48 g_48 bds_48 43 (dagTraceF m_48 s_48 6 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_1 : treeBlockF 32 43 (dagCheckNodeF m_48 g_48 bds_48 43 (dagTraceF m_48 s_48 6 f_48) l_48) = true := by decide +kernel
theorem nj_48_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_48 g_48 bds_48 43 (dagTraceF m_48 s_48 6 f_48) l_48) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_48_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_48_1 h1 h2)
theorem nc_48 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_48 g_48 bds_48 43 (dagTraceF m_48 s_48 6 f_48) l_48) i = true := nj_48_1
theorem lb_48 : LowerBin m_48 s_48 g_48 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_48 sub_48 gl_48 rc_48 nc_48

def m_49 : Nat := 0xffff00000000
def s_49 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_49 : Nat := 0x175700000000
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_20, s_20, 4, g_20)]
theorem kn_49 : KnownBin bds_49 := by
  intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_20
theorem sub_49 : ∀ b ∈ bds_49, m_49 &&& b.1 = b.1 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_49 : ∀ b ∈ bds_49, canon b.1 g_49 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_49 : Nat → Nat × Nat := fun _ => (0, 0)
def l_49 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsF m_49 g_49 bds_49 (dagRefF 0 (dagTraceF m_49 s_49 4 f_49) l_49 0) s_49 4 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_49 g_49 bds_49 0 (dagTraceF m_49 s_49 4 f_49) l_49 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_49 sub_49 gl_49 rc_49 nc_49

def m_50 : Nat := 0xffff0000
def s_50 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_50 : Nat := 0x133f0000
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
theorem kn_50 : KnownBin bds_50 := by
  intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_13
theorem sub_50 : ∀ b ∈ bds_50, m_50 &&& b.1 = b.1 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_50 : ∀ b ∈ bds_50, canon b.1 g_50 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_50 : Nat → Nat × Nat := fun _ => (0, 0)
def l_50 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsF m_50 g_50 bds_50 (dagRefF 0 (dagTraceF m_50 s_50 4 f_50) l_50 0) s_50 4 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_50 g_50 bds_50 0 (dagTraceF m_50 s_50 4 f_50) l_50 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_50 sub_50 gl_50 rc_50 nc_50

def m_51 : Nat := 0xffff
def s_51 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_51 : Nat := 0x177f
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14), (m_16, s_16, 4, g_16), (m_18, s_18, 4, g_18), (m_21, s_21, 4, g_21)]
theorem kn_51 : KnownBin bds_51 := by
  intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_14
  · exact lb_16
  · exact lb_18
  · exact lb_21
theorem sub_51 : ∀ b ∈ bds_51, m_51 &&& b.1 = b.1 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_51 : ∀ b ∈ bds_51, canon b.1 g_51 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_51 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def l_51 : Nat → Nat → Option Nat := unpackLinksF 0x8e11c1fc3f07c2f81b43606c0d45a0b40662cc15c2b0542a8148a18420841009f13e0784f01d12b0540a814128050098921222440809001e21e00b001 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d347d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 11 4 10 6 5
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsF m_51 g_51 bds_51 (dagRefF 43 (dagTraceF m_51 s_51 6 f_51) l_51 0) s_51 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_0 : treeBlockF 0 32 (dagCheckNodeF m_51 g_51 bds_51 43 (dagTraceF m_51 s_51 6 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_1 : treeBlockF 32 43 (dagCheckNodeF m_51 g_51 bds_51 43 (dagTraceF m_51 s_51 6 f_51) l_51) = true := by decide +kernel
theorem nj_51_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_51 g_51 bds_51 43 (dagTraceF m_51 s_51 6 f_51) l_51) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_51_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_51_1 h1 h2)
theorem nc_51 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_51 g_51 bds_51 43 (dagTraceF m_51 s_51 6 f_51) l_51) i = true := nj_51_1
theorem lb_51 : LowerBin m_51 s_51 g_51 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_51 sub_51 gl_51 rc_51 nc_51

def m_52 : Nat := 0xaaaaaaaaaaaaaaaa
def s_52 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_52 : Nat := 0x20202022a022a
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_29, s_29, 7, g_29)]
theorem kn_52 : KnownBin bds_52 := by
  intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_29
theorem sub_52 : ∀ b ∈ bds_52, m_52 &&& b.1 = b.1 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_52 : ∀ b ∈ bds_52, canon b.1 g_52 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_52 : Nat → Nat × Nat := fun _ => (0, 0)
def l_52 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsF m_52 g_52 bds_52 (dagRefF 0 (dagTraceF m_52 s_52 7 f_52) l_52 0) s_52 7 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_52 g_52 bds_52 0 (dagTraceF m_52 s_52 7 f_52) l_52 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_52 : LowerBin m_52 s_52 g_52 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_52 sub_52 gl_52 rc_52 nc_52

def m_53 : Nat := 0x5555555555555555
def s_53 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_53 : Nat := 0x115155511151555
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_39, s_39, 7, g_39)]
theorem kn_53 : KnownBin bds_53 := by
  intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_39
theorem sub_53 : ∀ b ∈ bds_53, m_53 &&& b.1 = b.1 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_53 : ∀ b ∈ bds_53, canon b.1 g_53 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_53 : Nat → Nat × Nat := fun _ => (0, 0)
def l_53 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsF m_53 g_53 bds_53 (dagRefF 0 (dagTraceF m_53 s_53 7 f_53) l_53 0) s_53 7 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_53 g_53 bds_53 0 (dagTraceF m_53 s_53 7 f_53) l_53 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_53 : LowerBin m_53 s_53 g_53 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_53 sub_53 gl_53 rc_53 nc_53

def m_54 : Nat := 0xcccccccccccccccc
def s_54 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_54 : Nat := 0x40444000c044c
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_32, s_32, 5, g_32), (m_40, s_40, 5, g_40), (m_42, s_42, 5, g_42), (m_6, s_6, 4, g_6)]
theorem kn_54 : KnownBin bds_54 := by
  intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_32
  · exact lb_40
  · exact lb_42
  · exact lb_6
theorem sub_54 : ∀ b ∈ bds_54, m_54 &&& b.1 = b.1 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_54 : ∀ b ∈ bds_54, canon b.1 g_54 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_54 : Nat → Nat × Nat := unpackForestF 0xa3f28efc50e500a378d021304d1112828cc01f 3 11
def l_54 : Nat → Nat → Option Nat := unpackLinksF 0xe1c34e1972243a70a8601 0x1520223088a068c1ca02b4042606d10894523f9476c8dc519801f 7 3 11 4 4
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsF m_54 g_54 bds_54 (dagRefF 11 (dagTraceF m_54 s_54 6 f_54) l_54 0) s_54 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_0 : treeBlockF 0 11 (dagCheckNodeF m_54 g_54 bds_54 11 (dagTraceF m_54 s_54 6 f_54) l_54) = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 11 → (dagCheckNodeF m_54 g_54 bds_54 11 (dagTraceF m_54 s_54 6 f_54) l_54) i = true := fun _ h1 h2 => treeBlockF_at nb_54_0 h1 h2
theorem lb_54 : LowerBin m_54 s_54 g_54 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_54 sub_54 gl_54 rc_54 nc_54

def m_55 : Nat := 0x3333333333333333
def s_55 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_55 : Nat := 0x113131313331333
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_31, s_31, 7, g_31)]
theorem kn_55 : KnownBin bds_55 := by
  intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_31
theorem sub_55 : ∀ b ∈ bds_55, m_55 &&& b.1 = b.1 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_55 : ∀ b ∈ bds_55, canon b.1 g_55 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_55 : Nat → Nat × Nat := fun _ => (0, 0)
def l_55 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsF m_55 g_55 bds_55 (dagRefF 0 (dagTraceF m_55 s_55 7 f_55) l_55 0) s_55 7 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_55 g_55 bds_55 0 (dagTraceF m_55 s_55 7 f_55) l_55 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_55 : LowerBin m_55 s_55 g_55 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_55 sub_55 gl_55 rc_55 nc_55

def m_56 : Nat := 0xf0f0f0f0f0f0f0f0
def s_56 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_56 : Nat := 0x10105010301070
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_23, s_23, 5, g_23), (m_25, s_25, 5, g_25), (m_33, s_33, 5, g_33), (m_35, s_35, 5, g_35), (m_43, s_43, 5, g_43), (m_45, s_45, 5, g_45), (m_2, s_2, 4, g_2), (m_8, s_8, 4, g_8), (m_18, s_18, 4, g_18)]
theorem kn_56 : KnownBin bds_56 := by
  intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_23
  · exact lb_25
  · exact lb_33
  · exact lb_35
  · exact lb_43
  · exact lb_45
  · exact lb_2
  · exact lb_8
  · exact lb_18
theorem sub_56 : ∀ b ∈ bds_56, m_56 &&& b.1 = b.1 := by intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_56 : ∀ b ∈ bds_56, canon b.1 g_56 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_56 : Nat → Nat × Nat := unpackForestF 0x428e6146a0b437da48293da8a2d25d6927340981486ab5e55a92a97954a40a3f322918d7918a06352312f18948c49a61260519904bc9288412304a702508329e21340ca1820f81064001f 6 11
def l_56 : Nat → Nat → Option Nat := unpackLinksF 0xe4390cdb30b1eb1ac2b0ac22988220882206dda1681a0645906419064109401003c4d2340d0340c1288a006401 0xea514d20ae8f624730a353918b9175f692bb417128ac8f92464283e45a83b145c6baab4e41a138975b49c72420c273409986bcbb5235a6ac97954a46a4128af22d4118a09c5249af20d48d69a7a5e39291a93482bc612624a2144bc8246213414a78650e0686f24f6521a88fcb466394e18a1040f81064001f 10 4 11 6 5
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsF m_56 g_56 bds_56 (dagRefF 35 (dagTraceF m_56 s_56 7 f_56) l_56 0) s_56 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_0 : treeBlockF 0 32 (dagCheckNodeF m_56 g_56 bds_56 35 (dagTraceF m_56 s_56 7 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_1 : treeBlockF 32 35 (dagCheckNodeF m_56 g_56 bds_56 35 (dagTraceF m_56 s_56 7 f_56) l_56) = true := by decide +kernel
theorem nj_56_1 : ∀ i, 0 ≤ i → i < 35 → (dagCheckNodeF m_56 g_56 bds_56 35 (dagTraceF m_56 s_56 7 f_56) l_56) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_56_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_56_1 h1 h2)
theorem nc_56 : ∀ i, 0 ≤ i → i < 35 → (dagCheckNodeF m_56 g_56 bds_56 35 (dagTraceF m_56 s_56 7 f_56) l_56) i = true := nj_56_1
theorem lb_56 : LowerBin m_56 s_56 g_56 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_56 sub_56 gl_56 rc_56 nc_56

def m_57 : Nat := 0xf0f0f0f0f0f0f0f
def s_57 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_57 : Nat := 0x1070707030f070f
def bds_57 : List (Nat × List Nat × Nat × Nat) := [(m_24, s_24, 5, g_24), (m_28, s_28, 5, g_28), (m_34, s_34, 5, g_34), (m_44, s_44, 5, g_44)]
theorem kn_57 : KnownBin bds_57 := by
  intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_24
  · exact lb_28
  · exact lb_34
  · exact lb_44
theorem sub_57 : ∀ b ∈ bds_57, m_57 &&& b.1 = b.1 := by intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_57 : ∀ b ∈ bds_57, canon b.1 g_57 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_57 : Nat → Nat × Nat := unpackForestF 0x1f 1 5
def l_57 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x1f 2 1 5 1 2
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsF m_57 g_57 bds_57 (dagRefF 1 (dagTraceF m_57 s_57 6 f_57) l_57 0) s_57 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_0 : treeBlockF 0 1 (dagCheckNodeF m_57 g_57 bds_57 1 (dagTraceF m_57 s_57 6 f_57) l_57) = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_57 g_57 bds_57 1 (dagTraceF m_57 s_57 6 f_57) l_57) i = true := fun _ h1 h2 => treeBlockF_at nb_57_0 h1 h2
theorem lb_57 : LowerBin m_57 s_57 g_57 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_57 sub_57 gl_57 rc_57 nc_57

def m_58 : Nat := 0xff00ff00ff00ff00
def s_58 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_58 : Nat := 0x100170013001700
def bds_58 : List (Nat × List Nat × Nat × Nat) := [(m_46, s_46, 7, g_46)]
theorem kn_58 : KnownBin bds_58 := by
  intro b hb; simp only [bds_58, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_46
theorem sub_58 : ∀ b ∈ bds_58, m_58 &&& b.1 = b.1 := by intro b hb; simp only [bds_58, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_58 : ∀ b ∈ bds_58, canon b.1 g_58 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_58, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_58 : Nat → Nat × Nat := fun _ => (0, 0)
def l_58 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsF m_58 g_58 bds_58 (dagRefF 0 (dagTraceF m_58 s_58 7 f_58) l_58 0) s_58 7 = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_58 g_58 bds_58 0 (dagTraceF m_58 s_58 7 f_58) l_58 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_58 : LowerBin m_58 s_58 g_58 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_58 sub_58 gl_58 rc_58 nc_58

def m_59 : Nat := 0xff00ff00ff00ff
def s_59 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_59 : Nat := 0x170057003f007f
def bds_59 : List (Nat × List Nat × Nat × Nat) := [(m_37, s_37, 5, g_37), (m_38, s_38, 5, g_38), (m_47, s_47, 5, g_47), (m_3, s_3, 4, g_3)]
theorem kn_59 : KnownBin bds_59 := by
  intro b hb; simp only [bds_59, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_37
  · exact lb_38
  · exact lb_47
  · exact lb_3
theorem sub_59 : ∀ b ∈ bds_59, m_59 &&& b.1 = b.1 := by intro b hb; simp only [bds_59, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_59 : ∀ b ∈ bds_59, canon b.1 g_59 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_59, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_59 : Nat → Nat × Nat := unpackForestF 0x63f18ee04c18dcb4458d0a5438d082418cc01f 4 10
def l_59 : Nat → Nat → Option Nat := unpackLinksF 0xe1c3862a5424c882ac601 0x68c204c5910c2458d0e346d112542092a3f98ede3718cc01f 7 3 10 4 4
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsF m_59 g_59 bds_59 (dagRefF 11 (dagTraceF m_59 s_59 6 f_59) l_59 0) s_59 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_0 : treeBlockF 0 11 (dagCheckNodeF m_59 g_59 bds_59 11 (dagTraceF m_59 s_59 6 f_59) l_59) = true := by decide +kernel
theorem nc_59 : ∀ i, 0 ≤ i → i < 11 → (dagCheckNodeF m_59 g_59 bds_59 11 (dagTraceF m_59 s_59 6 f_59) l_59) i = true := fun _ h1 h2 => treeBlockF_at nb_59_0 h1 h2
theorem lb_59 : LowerBin m_59 s_59 g_59 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_59 sub_59 gl_59 rc_59 nc_59

def m_60 : Nat := 0xffff0000ffff0000
def s_60 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_60 : Nat := 0x1170000133f0000
def bds_60 : List (Nat × List Nat × Nat × Nat) := [(m_29, s_29, 7, g_29), (m_31, s_31, 7, g_31), (m_48, s_48, 7, g_48), (m_30, s_30, 5, g_30), (m_33, s_33, 5, g_33), (m_34, s_34, 5, g_34), (m_36, s_36, 5, g_36), (m_37, s_37, 5, g_37), (m_50, s_50, 5, g_50), (m_0, s_0, 4, g_0)]
theorem kn_60 : KnownBin bds_60 := by
  intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_29
  · exact lb_31
  · exact lb_48
  · exact lb_30
  · exact lb_33
  · exact lb_34
  · exact lb_36
  · exact lb_37
  · exact lb_50
  · exact lb_0
theorem sub_60 : ∀ b ∈ bds_60, m_60 &&& b.1 = b.1 := by intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_60 : ∀ b ∈ bds_60, canon b.1 g_60 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_60 : Nat → Nat × Nat := unpackForestF 0x564239ac846b5904e6b209ad64035001697531166b0ca4d61945ac308b53093eae09fd6024cab82775704deaf49e55da44abb2695704ceae01fd5c037a9849d56c912ac9af55a25cab22bd564056a6095d57c59aaf29d5304a6aa1a9555a50aab29155097aaa094d5403da9824f54c90aa6092d4e352aa34a153897aa709ed4e131a9f4795384a6a749054e125a9804f533166a652154c0250014975264e6a541e549935a9306b4c6d4ea149fd4824ca8527751c132a149bd4613ca884895104f2a249a544014a8526750a0fea141bd31b51a818a3505146a0412d31a49a7f2714f6d869f63053db59a7b0ab4c657e9e5acd3195da774894e51869c8b6d3a460a7229d4e405698ca9d3814ea632a34ccd869b630533359a662db4cc5869a536533159a672a14cc55698c2fd32359a630ba00291e8edad52f16da5e2c34bc1b68edabd1db56a5b2b94b04a696092d2c025a3b4b74ac9b294e33529966a5302b4764ee9451a52835ba3b2734951aa934b0525366a4a2734941368ec9bd24128a474b74764d68fa3551f366a3e29b47c5069052651f139a3f26147c4d68ec1bd1e25ba3b06a0028fe8dcb6d1b961a370db41ed5e83d2d51896da330294625868c436d07a57a0f4ad41e9368b536515366a2a2cd45405683c95d1426ca276af41e4a6881b5512014a232c144099a88094d1003da0f24f43c582875abd07925a126d542499a8489ed0c164a1226342c8f284894d0a154a1324142449683c13d08357a0f04a0028ce70e2cd0394aa0728d40e51681ca250414ca0708b386d3e7edaecfda3a9fb46d4044b67ed1a4fd93a9fb26d3f64d67ec9a4fe13c9fb06b386d0e7dda4cfbb459f708b38653e7b11fcfa34c9ec4773d88de7c5264f7b449ef2493d88ce7b01fcf60379c329d3c8d7a7a49a4f23529e66893cc972790af4f20359c327f3c3166785274e193e9df2893b117a762294edb509db4913b057a7609f4ec04d9c326f3acd0a70c9b4e62529cc49539890a744a84e615e9cf29139853a734984e61469c302f389166724a44e234f9c646938c4e2711a1ce21429c302a00252e6f91cce003c9be46b37c0d6559a9cd823f9bb6993608ee6e4264d82379b7479366d126cc944da2349b30493608ce6c01fcd80379566a335c8e26a9b0cd64609aa6933541165592fcd43499564bb34cd1268630cd0a6d9a38c134293a68412cab25399f49d2ac946649b74c936d9926d9324d96665b64c93629924dd32498a6551b4c92609936c13240d65591fcb8c6298e69531cd1a5c6304c63609716dd3149165c5b64c44609716c52e29ba5c536cb8a6c9830d92e2996601364c00249714c52fd1425c52acbe46c97149b2f31825e52a4b892a9772bd2e24a25d2304ba15497124d2e49825c412cab2339688a32d0d3e5aeb04b645096b2692d0d0e5a628cb40159562932bcd86596304af35995e4db2bc986585b64af25995f4a12bc9565582fcabb5995b6c92ae8fe561324ac1289574672ac174004a3c89b5a9514db2a298654436c89b579136ad292936525234a4a4594948929492252412c89a5b93d6dd27adb64f5b649eb6293d4b327a5ba4f4b14a013693d2c127cd924f436c89a5793b6d926d19a4e52249b26a9364cd26c09644d1dc89a3992dad5264db24b6b349826092d6cd25a8e64b42ec89a3791346b246d2648da2c93b449274b92464fa4952449193692302b22656e46a3548d36691a49b234906475a648d23991b4612348d644c1bc8c24c9144b722cd824512bc8a15b91306a0024fe4309d48613690c26b2184d24349e4860358ae6b71ed18a421254842468f68c1209582416284821348f66b3204d823d9374801558f64d91fd1823d93147b16e8f62db1ec5b23e40a47b1628f72c91ec1b62b9abc7936d8f26c31e41b62b92bc5715a8ea6db1dc0d23a9b0c764608ea6ab1d41b62b8abc571568e56b71cd1b2395abc5714d8da8d51c518236a334701348da6d51b4d9a371b646e3548da2cd1b40d62b89fc6ba5e8d70bb1a8d5a355b646a1578ae27d18d1aa340b646806c8c68cd18cdaa336304633668cb0491929823252a4631668c627d18c1362b89bc61a3d8c304b18096a305304601578ae26d16a9aa2d52545e1648b548516a59a2e4a445a94e8b72a916c4c22d4a34570178b327115ed6e2c4b0457b578af4af15c05400499c552458ab4991541161562dc52c618a769314a9b229436c2ab578a18cd14291228422c2ab4f89f49d0aa96a26e30c4dc5989b0db0aa95e261a8c4c23f8554ad1271aa24e33449a6689308b0aa93e245ae44535b88a6af11b182235b044525788a07f1140de1552742aa4287fad30fed7a2152e43f95e8818b3102d3a205a143f93487f02b0aa56e1f4b643e25785529d0f51821d9b343b1668762690ec056154a1c39c608734d90ced5e1c630433a578672af0ce4de19c93c3615686724d0d455a19c92c3413486702f0aa50a179b542f35285e4cd0c49421792f42fb5085f2490bc54a15413c2b45b8566af0acd3e1592142b15b8576a10ac50e1541280092f85128b0a453214422bf2c5b84aad3094d7a1322cc2624284a2690940d5f95adbf2b4e8456cd08a4d21141abf2b4383c6af0788de0f09bc2025683c26d0784d60f49a41e0377e56850651860c9a741c460832685068d260d11f41a2328322d90641b5f952bc1746682e28905c115f9527c1536682a6bd0540d5f951fc1445b7e547d04b16e095a73f2a3d82329cfca56a07230c0e45981e8c103c4d2071a140e06d7e52af02cd460663040b23381627f02c4bdf94ab408c6a8118cd02259a04422bf294f80f6b9004d6e009abc05a5c80b49900496e022304043608022af00c97200897c0112e80207f0040ddf94a73f29427fe8b6ffcd09f949b3fc45b7f869cff0939fe62d3fc14e7e525cfec511fbe293f7a6a7f38a0fde949fbcb33f81507ef2bcfca05df9a2dbf335b7e6686fcc95df9927bf323f7e7682fcc509f940a80092b7e1692fc4d01f8422bcbc5b7ddad2fba979f7412bcbb5b7db49cf2ed69f55a8beb83f7d706efaad41f542e3cbb5679769cf9f1a9f3d353e7a667cf04af2ed0df352e3e4a5b7c94aef920bdf2413bcbb427bfad2f7f149f15a83dfa5e7c18b2f82939f05213dfa4c7bf04af2e96deea353dd2667ba498f74095e5d21bd85697b08a4f6cd41ec0af3d94597b269cf64d09ec0a63d80157972b6f571a9eacb33d594c7ab02af2e50dea22dbd434279725cf4b16de95a13cb92979f8d4f3f149e7db33d035079f6bcf2e0fde622dbcc34e7984b6f3090de60adbcc14379707a00249de4ca2bca14c79308ad3716de3a30bc835978e2d8f1c1b5a6dabbc546678a288f14115a6da7bc426c77f6aeefe8dddfc9bbc225677f26cefe4d5e01263c013477f06ed36d39df51a34db427738c2ee6d39de6303b9b427756b2eea8f9dd5193b996c7730dad3695ddbe333b794476f08ad3693ddb5363b135776b2d8ec495dd891bbb11377674acec44d9d889abb1a4c763268ec40dda6d273afc6075f2d8ebad5dd751a34da427578d4eaf149d65a73ab94c75709ad368ddd322dba634274d696e9a92dd3523ba6a3f74d466e9a0bdd3413ba613c69b46ce8316dd05a13a134b742496e8491dd091fba123374205ee8409dd049e34da3573d472e7a4d5cf41ab84b4b7388b2e744d1ce12739c025709496e6c495c251f398b5a7314b4e62959cc412b84a3372f498e5492dca923b9512f72a05ee5409dc2519391b5a723684e46959c9520391a4e72304ae124bdc6da5b8d94b71b28ee364fdc6c99b8d81f71b02ee124b9c49a5b8924b71248ee248fdc491f38923371205ee2409dc2496b8535a70a684e14959c312038613470a49ce144f5c2417b4da3470729cd36569bde30b821346f769ce044d1bdd2737d3516fa4b2df4925be91f37e3506fa464df44b9bdd1a37c2346f70dad3655dbc9a8b7923f6f227ede449da6cab36ed6a6dd8d4dbb199b8a2d37135a6eb4a0dc4d59b8920b712406e7498dc48c9b8918b7223d6e2460dc44b9b751a36e9666df460dbc8d1b7422b4d94f6db06ad97169b65ae365b5b6d78b0d96d5db523036a3606cb4aeda3181b45b03659576ce6a0d9cd01b2c93b6583f6cb06ed36539b20aa36401469b284d8916db112736214269b27cd8316db05a734d93d6bd8b6d7ad09af4a734d92e6b78b6d6e939ae1a5b5c2326b7468d364b5ad4a235245e6b3288d48d79ab5a7356b426ad47cd5a4f9ab41f3523446ab688d489a9aa5a03543446a44a4d48599a94a835215e69b02ed3916da71abb4e34f69c4aed3893da711bb4e14269b02a00248da491cb4b93c697260d248d5a489cb49a3c693460d244d52e9a9b3ba3f68f698cee8eda30a634614067746ed128f1a2498342b44685250d0c8d1a149233ba3367727ed049319dc9db3fa4c67f480cee4dd9f11833e13c678488cf04f19e49a33c134677266974d459d11ab3a1354ba692ce48e19b5b0b3846066d692cda5259b4a2a5d25f66b6929749759a4983343446628c2cc49b59963033124e662252cc44952e929b2fc5965f49c9749459752632e03e6576a2cb4d0595d2032c3596572ba97491591db7323b6d6476d8c8ed95945b6323b626474dcc8e9899351b323a6064a6c0c945b191c9cb2436064726a9748fd88a3132134a643280c84d1988a303203606226dcc7c915889b631e4606226c4c44d558893731126d6224d8c6a5b18d4b03112656314d8c624a18c49231126262f8a0c449558b63631124d6298c0c52db18a4b63111296274c0c4449588e303123406232a8c440992e919b101386156c2c3d181855a4b0e1486154dac344a185530b0c36c615492c2c94185522a5d15f60e692c22d518449c30723f60f4a8c1c8cd2e8aeb0623060b488bff1858252a2ffb6d607468bfed857fcb6b024605ff29cc04db17fc9f3002605ff26c97454d7da2cafda445fb288becd3d7e49a2fb3435f749abec5392e8a8afa24c5f307cbc4d457c5a4af125d5e247ebd31817a5b62f4a6c5eb6a0bd29717a4942f12335e3682bc68fd792282f21245e3466bc45012e8a2ae4b6e5c96dab92db1725b2aee36c5c96c4bb4d5172536aeba5c5d7488b92985755282e4a555d26d8ba49b17251cae7c605cf4c0b928d5724b72e49625ca472b944d9724b025d13f5968c4b88929715202e22465968c0b84551659b6ae01345966c2b731816f2282de1345b96a0b729b16e4b62cb3555b76c0b2c9b96d4a2acb26c5b38c0b2c9896592aacb16e5962dab5cd416b52aacb16c5aa6d8b54d81658b2ad316c5a6278b4c4d1658b12d24505962aab451b1658a6acec6059d6a8b3a9b1674b62cb13e59b6c0b2c4d965e302cc3405970a8b2c0592e899aca2445718c2ae3165645362b8b555714dcae29b5631acac63495714d8ae29955c5312b8a555858c0b0adb1615b02b8a4e5834d8ae29095c4b72b896257b8b2af69395ed212bd94e57b24cae25815e1b62bc16c57129cae91815d1362ba16c571284ae45515c41325d12f56f288a8d18551a2caa336e5466c4ad11655a1a72b41355466c0accdb1519a72b1c605636d8a8cd09584b62a325554647cabcdb15191eaa316e5462daaacd65559a4aab23e556464aac4b9518b62a31655462c4a8c55553a302a736c54e6c0a9c981518a72a5b6054b2d8a8c5095189b2a312e5470a8a8c0592e895aa23485308c2a611654c1b72a024c5306d2a60d894c1b0a9dc5953b49ca60d814e5b629834e5358c0a6a9b14d5302983425336c0a604b94c5b02981294ba24ea5c5112ee30a5dc594bb6dca52d254a4a2a5db6c527468976d89494b625db555236d8976d39484a228ec6051d6d8a3c9414751a25db4251a4d8a349812ed3728ab4951547ca2a8c9454a2a5da6c5116d8a22d814451a25da6250f2d8976955431b628626c4bb49ca1451141630282b6c5054d8a0c9414151a25da425026c0a044f12ed1b27fb604ff2789768d53f49a2753514ea6929d49793a92ca752524ea4a29ead253d51f2752504f34b89d48f93b9a827725c4ef2489dc9413a91927512e4eb4b89d44b52ed1a25d96e4e74809cc8d12ecb6a703494e047c9c08c93809f2701324bb2d89b7181371a826e2504db468976595360b626c14c4bb2c49ac9013551a25d9554cf8b099edb133db0267a6c4cf2d897653932a3026536c4ca4d89945b12eca126426c4bb27c98cdb12ec9ea6216c4bb25c9809b1305282602344bb25a97c9412f11a25e0544bb02c97448c004239e035a4b44da9689852d0b6a5a1613c06ae780d592a926a552464aa48a9549112b4a22551294ab490954494f012da4fb6e49f6da93edb127db124fa594a36c893e5b5284a224f96149f0dc78095d275b624bc6649b48892e9a925d3324b92949724a7808ecf011ca4656a4936d89195992453024636648c472918575234ae2461513c046e7808d52249a23f3494872b88fcd151f8a6a3f14647e28a8fc5112052223f13e47f6908fc4d8f00ada36b6e46d6da8dadb11b5b123c35446d4da8ec9111b530a39b6c4734d88da8e51c23023826046d46a8da5651b4371e015746b4d88bf1991a51a22fb494674b88bed15194a222f96a45f2cc8c4d1117c9f23024845f26c7804ed1749a22cb5b45a4d88b45b1165ab9e0139449ad48acdb1126b322a1604496cc8929751452e224a5144e6b889c4a11251ca25a4044b2a08928d51249c9e01374474b888696d112302221604434ae7804d510522219c6a43f4d88671990f522219a6a43b6d88669990cd26a1c2644334948669190cd22a19a4443304c7804bd0c4a220f46a42f2d883d1990791f20f23d42b28883c5a90a5b620f16641e29a84c591078a520f14641e28a83c5110789b21015c41e25c83c058f0095a0e34840b8d4834d8102e3320c24440b6d482b181055b6205b6640b694816d2502da4205b4640f498816d0502c9720592940b07c78049d024a21efc6a4072d87bf1990149e1efa364032787be8d50051c1fd35a3fa6ac7f48e4fe9189fd12e3fa25a7f40b8f7d1a1fb95c3f72887be5a8fd5b61ef9663f34687be574fbe2d1f7c563ef06c7be570fb51a1ef94d3eb2887be528f7ca31f42343df28a7be510f95221ef93e3df27a7c4510f7c971f02343df25a78048cf04a89ed25c3da2807b4174f04a29e09253c10a27a6970f4cae9e99253d3080782114f44a29e08253cd2d879a4d0f34301e081f3c94c07921b0f241a1e081b3c74c078205cf14a81e11243c20987840d0f04099e005600107e774914ef49a1dd1493bb498774514c062d9da4613b76927689b0ed0b69da1613016ae75b198ec22c9d84513ad48875a524eb4a2980b4f3ab49c602968e9e309d396d3a72c260295ce91a89d223f3014ac73d1a8e7a331cf26639e29273c514c05279ce35c38f6b671ed5ce62301cc36038f4ae71e4fce55261c793b38f26e7244f0e41221c813438f266602938c05211c056938b288700d78e249a1c0352387488700578e009e9c013638026a702d38e05a11c01343012b66fc910dc2309b826e3704da6f4d24dc1361b82623758c06eadb0dd5b01b824e3734d86e0908dc0ac9b806e3012ae6dc910d8e351b626c3638cc6d4910d8d351b436c3634cc6c6928d8d231b1a4536348860253cd81ae1b013434d6d46bc5b0d35b31ae13434d2d46b49b0d34b31a695d34d29a69a514d551e1a925a3524ac6a48f4d34a21a693d34d26c69a4d4d349a1809433446cc688d78d10b31a425c3442bc68ad38d15a11a21343012766771a8cee2919da6633f6a0676978cf0a719e14233b4986024dcce536197b6633748865ed78cd49a19796a32f2cc664970cbcaf19813432f2a46024acc962d995a6c32b2d864ad5cca12219414432569e64c934c94a71809293188d46449b0c62331902443188bc631148c74b018c26631a6a0634520c612f18c12930124e61f16cc3da1189b603132c061e95cc41a418814830f49e602494c34b61812573022ac60416cc21b618416c3020ae60c090c081598213c30204e604064c042700082f2fb6925fc530beca497e3402fb28a3d516cbdab497b25e2f62525ec4947a9ad97a24e1ea6b45d6d44bb89f97713b2ee26e5dc4ccbada817595c2eb2a03d4d587a9a7171c6a2e34d45c6998b8c949722682e324a3d4d0cb852e16a25b2d44ae5a84bcb751e16a12b2db6d05a849cb649616aa342d72485aa590b54a616a1231ea6845935a4b26291683502c94bc599164b31271662422c94985924a4b24928f525b2c38d4586998b0d261619292c324a3d490cacab49594692bf288565178af49a1594522ba6a0574d20ac8af15914e2b229a569164ad12715a2422b22985645147a8ad9583482a28c2544db8a89b11513612ab49c544d80aa5b615134e2a58c054a9b0a95301513422a38c05445647a8ab9503482948d453cd80a523314e2442946d4533180a65b614a366294694528d24a51a414a3461ea29e5244d09c635147c6028f2d84e31989c628945a3a28b46c4e3140a24a613896a2876c04e2598a162c13895d27129c4e25349c4a614046827128a4fd1409c49e93c35a27a6a04f49709e1ab13c23e2712784ecd409c49a9394502720784e40d09c40b0f514326f2504c51a89b49413145226b4984c49a8989331343502624bc4cc9309892913115e2638a04c45487a89f9301482568b64ba8d09749412b35b25a4684b44a0959a192b24e25724a4ac5087a89e92a2342458d44a48d091629122a5e24f8a048a948934a612296a2452cc494d40914af12396424729848a548914a68f513324348847316c9011a1201342396b647a8d08f49a11cb4323b26c4729388e4a70f513122b8d44571488ad3311a35022b4bc4625388c4a1115a4c22f2784565788b22811624c22b2a43d44bc8763510ec5221d4bc44d1408752910e9662236a043a5788792710f24221e29c43c508874a60f512321b06a3f0d24864a610c1491f846442ad24855190fc1502132783f04cc831a890813e20c4a041ad40834a81062321f808a4145807e01f900b4020668040c090805301022302010d84020f0804160fc0331fd6923fa4f87f4190fc02d1fb2783f007c7e41e0fc0131ea0ac3d716c7ada10fa2321eb2ac3d616c7c5b00f58571eb09e3d91407b5200f60241eb0863d40b8004138f41341e46923cc530791a28f21451248b63b75a4784a20edb5e1db2743b64d876c9a8ee2421db268248d6c764a20e8c611d16b23a25b8744b68ea3591d12d83a2588744370923571cf2883911a8734b60e44661c8294390518720a28e414412469e38c4d06e9b50e216c1ba6cc374d746e91d0dd2361bf25a3748d06e89d0dd1361ba26a3744d0491a18da4611b46da368d846d5a48da16c1244ae35b1986b5a48d6b451ae8b235d1446b4a209224f1a86cc350d786a5a10d413412447e3471a868e290d224e1a32982488dc684a20cd34f19f25833a8d06749a0cd34319b482334538490ad0cb4611966da32cd84490ab8c63511936d83188fc641360c812418c4663184fc630978c61271242ac30d1a861a330c334918668a30c598490a78c235c16a6b62d4d5c601260c024416a4b62f91805f1b60be36016a4ae2d48fc5e5a60b523b16a46e2ec9305d1a20ba12416a4662e31805c5b00b515716e4b82dc9305a8978b5b5016b6802d449c490a70b41341656b62cc5b0595ab8921421632682b2da8565b30acb5e15f2682b2d48575b60ac96615a6882b4970564af09213f14f8b629e938551b60aa26c14f2ae2a0d105412e0a824414f29e2484f85322d8a614e12427427f1a8524b609fc6614728827f1784fe290a226013f2cc282d405052409f95e13f27c2484dc4da2d89b34213a6c02749804d8ab89bb4813749026c53c4909b09945b1338b426453849099092a5b12e6d825c1b04952b89606c1252ae2540904949789403c12524e24a1584941709204e00103e2448e0479a489024011e68a23c92400a2d88a56911b490228d784511d08a2391168b222c5384511c08a2360026b622492042a3088535910a4dc21498842930885b5910b29c214980009ab8842481018d420c98040633080a4a1014922029204052300134f0ff4701dcda83f5300773660fb4b01dcd743b91d0772390ee4701ecda03b91b07713a0f325c1dc4e03b89b0778280ef0481dc0d8009a18745690e88d21d05783a0a70741460024b61cc510385a7871a380e32681c2d0c384a700125a0cf6a21b68fc36d1d86da370db46619ed4033d2e067a500d68c01acdb033d1f8684600d04d81a2d40344ae0681280cf4660049583352206525b0cb6d819495c009270614510c26d41845a8308b306114e0c38d01845180092185f35c0be27017c4d0295ad85d4600ba2d8174580295ab85b23a0b646c16c0d8295a085a15c0a52b614a55c2c62805293f0af49814a4ec2b2340563500a526e1544f0299220541340a62c814c4f0294998012420a28b61449380091f049c5e0938a413c53024db504dc5009b298126d482649e04996a0932cc12c94024caf04a13c0932a40048ec245a4046c5b08f26c11ad08234a700123a0858b610ad602262d042b4208649610c91c215a00012360748bc0e91482052203a36a07e8a00fc9101d1a903e13c0742d40e85981e52803a15e0762c80ec4f01d0a903a13d0024660e4d101ba2d83813606e69c0dc5380091902ed6905d6a40bad28175a103425005d2bc0ca9201951c02e94e0624800c48c0174a302f45905e29c0bc5081749e00115b0516d40a2d28145a10289660564900ac8e0144a7029a400534600a25181449e0011430438bc08714810db50264500436a40865981252802195e04469c088d08110a70221420432780044ec0d62f01ac520356d407d1400d5a901a96603b4a006a5780d9a701b34203629c06c5080d49e00113303346a020d240bda881803e02f2a00209140411f81526c02a2500540a004119813b500270a00449140952e0112310230980441240409900f34901e46403c0f80409500bb4901747e03409005d1980c231017264020140054160080330130580200ac044160080230020ac00716c00dad8062600036ae006d3c0241a001b4300726800cd0400d210021320030ac0040780040b80001f 12 11
def l_60 : Nat → Nat → Option Nat := unpackLinksF 0x2a58154a43a93855240ea402542d5a820f50306a040d4080a7c934f70a9ec0d3d41a7a034f4029e60d3cc0a78074ef069de05390ba72014e20a9c4053841a70814d9229b2053601a698b4d2069a4053480a68054d0029a0053208a64014c4129860d30c0a61034c1069800d3000a5f834bf0297c0d2d0aa5a014b402958452518a498349302922152440a43174840a9060d2042a408147e0e8fc051f02a3e0147c028f60d1dc4a3a85475028ce751942a3281464068ba3d1740a2d0745a028b20d1640a279544e06890351200a22874450288a051101a220143a2a874050d45a1a03434028660d0c81a1883431028600d0c00a17834242e848050786a03314040a804150002a00013f62a7e22cfc409f7853ee067dc04fa069f4013e7067ce04f9c09ef913df027bc0cf6c39ed813db027b40cf6809ed013cf2e79e04f3819e5873cb0279604f2429e3853c70278c0cf1809e2833bb2a77604ed859ceb339c067360ce6c09ca0f3920a7220ce4019c70538e0270464df459bc0b378026ec14dd419ba03368326d004d9c19b10b362026c404d8419af8535f026be04d40f9a80134f0669234d2409a4033470668c0cd1029a2013420a68404d04199f853333266604cb8598ab330e1e61a0cc3409868130d0261a04c30197f9b2ff025fe04bfc097f812fc0e5f60cbec097d032f9065f204be01974212e7065cc0cb98096e932db0a5b40cb64196c032d8025ae0cb5c096a072d3065a604b20b963832c70258c0cb180963012c40a58804af0895e012bb0656c2cad8095a832b40656804ad00959052b20256404aa88955012a61254a0ca901951832a3025440ca880950832a1025400ca58a94b012960252a0ca54094a812930a52604a2c8939b1272064e4049c02938012652e4c614988193005260024ba1c974092d8525b024b604968192b092540a4a804918e923012430e486049081921012382a46e0c8c469188122e0e45c048b809168322d024465488c090f0b21e0243a0c870190d8321b024340c868090d0121a024320c864090c032054e4041c8080901011f9263f2047e018fc011f60a3ec047d418fa811f5023e80c7d008f9051f2023e4047c028f8011ed0e3da047b018f6011ec023d4147a808f3091e6023cc0479028f2011e306394cc72028e4011c70638e0471818e2051c4023860c6f078dd831bb023740c6e418dc031b80236e0c6dc08db031ab2e356046ac08d5031aa02354046a028d10d18a623101461828c205184022f4545d458ba03174022e8045d008ba01173062cc6c59808b283164062c60c58c08b181163022c60458818b1011610629c9c53808a68314d022980c53008a601144222821c50408a08114006280044fc189f8113f022685c4c438980312f0625e044bc08968512d022580c4b008930d1260224c04490289105122022420c4840890031162a22c04454188a81114062280443c587b330f5061e80c3d00879830f3021e214385086f070de021bc04354986a030d4021a60c3442868810d0061a0043382867010cd0619a043340866030cc02194143280864050af6615c0c2b41856810a61e1481428c1851030a00a14004274384e81091321182c23008460108b0610c2c2180843010840a1080420c1841030820210404200283f83073320e6041cc08378906f020dc0c1a4583481069020d20419c283381067020ca14194083203064020c4141880831010533e0a60414c0828070500209e0c1246824810480608e0c114282203044020841410808208303f0a066640cc081903032020620c0c408160b013660260404c08090300145ffc1bff807fc8aff901fe243fc407f880ff101fd633fac07f484fe709fce03f9c07ef12fdd05fba03f5877eb00fd601faa0bf5407e70efce01f9a0bf3407e680fcd01f9613f2817e500fbe31f7a0bef017dd04fba01f7013ee007dc00fb801f6a1bed407d78cfaf01f5c0bea847d500fa905f5203ea407d480fa415f4803e9007d104fa201f4013e7c17cf80f9f01f3e03e7427ce80f9b09f3603e6817c796f8f01f1a13e3017c600f8b05f1603e2c07c484f8025f0003e0007c000f7f05efe03dfc07bf02f771deb4ebd6807ad00f5905e908bd1c17a284f4501e8a03d0837a100f3c19e7023ce0079c00f3801e662bcc8179900f3201e6403cc0279704f2e01e5a0bc88b78f86f1e05e3c03c70278e00f1c01e3803c5c578b80f0f21e1e03c3c078780f0919e1203c1c278380f001ddfe0bbe8577c82ef901de82bbd0077904ef009de003bc0077800eee09ddc03b94977202ee401dc60bb8c077180edc1ddb803b70076d82edb01da83bb50076982ed301da603b4c076884ed101da203b3c276780ecd09d9a03b30176600ec031d7e0baf8175e82eb815d6c13ad8075b00eb601d6813ab4775680eab09d5603aac075484ea805d5003a9c174f12e9e01d3c03a74174e80e9d01d3a03a74074e02e951dcf0eb9dc173b80e7509cc49b984172f84e5e05cac4395807278ee4e05c9c03938072604e4c01c9023918272204e4305c840b904171c12e3705c6a138d0171904e3105c447b884170f84e1f01c3a13874070e80e1d01c341b868070a0ce1401c2803850070a00e0e19c1a0b82c270580e0909c1203824070480e060dc0c03800670000e0001c000380006fd0cdf905bf00b7cc56f902df105bd82b7ac16f484de805bce0b79426ee90ddd01bba0377406ee80ddd01bba0375876dd38db905b72036d836d224da10db420367056ce00d9421b280365006ca00d8f15b1e0363426c680d8d01b1a0362c26c484d8901b120361c26bd98d7a05aea2b5c836b882d7101ade135bc06b780d6f01ad42b5a806b110d6201ac40358806ae8ad5d01ab61356c06ad02d5a01ab40356806ac04d5609aac0355806aa04d4831a900352006a304d4505a802b500069f04d3e01a78134f0069a8ed3405a68034d0069a00d3401a68034d0069a00d3401a564b498569282d2501a4a03494069280d2501a4a03494069280d1c25a2e2b45c068b80d1701a185b430068600d0a09a1403400a68000cfc119f60b3ec067d80cfb019e44b3c8067882cf1019e00b3bc167780ce5299ca03390167200ce4019c60b38c066b98cd7019ae0335c066b80cd7019ae0335c066712cce0199c03338066682ccc059960b32c066580cc02d980032fc165f80cbf0197e032f4265e80cb32994a73290165104ca00994003278264f00c9c099360b26c064d80c9b0193603268164d00c90299200323c164294c850190a03214064280c7e1d8fa0b1f0163d82c7b018f6031ec063d02c7a018f4031e8063c82c79018f2031e0163c00c6c318d60b1ac063502c69058c04b180062e08c5c018b60b16c062d02c5a018b403160262c00c58018ac13158062b00c54098a60b148162318c460188c0310c362180c4301886030f8561e82c3d018702b0e0061c00c38018662b0c8161900c3201864030b846148ac290184e1309c061284c25018480b090061200c240183453068060c82c19018300b058260a82c15018280b028a60500c0a0181403028060500c0a018140300c75f1c0be2057c402f8415ef06bdd057ba02f7015ec86bcb3979212f2015e304bc60178812f0045e000bbf057781aef005dd82bba0576c22ed025d982bb10976202ebc25d588baa0575402e9c35d380ba60574a0ae8445c99cb92057220ae1ca5c380b840d70802e0c15c084b7f096e07adbc15b50ab6a016d20ad9835b300b66016ca0ad8c25b006b513d69e12d3425a212b44016860acfc459f02b3a1167402cdc359694b2d016580aca4359402b280164e0ac9c059380b27016481ac90059200b210d64202c7c2584acb070960e02c1c058302afe215fc02bf4157e80afa0d5f402be4157c80af9015f202bd4457a80af5015e41abc8057900af2015de1abb8157604aec015d60abac057580aeb015ca32b90157086ae0055c002b7c156e84ac17158202af8355f00abd0557a02ae4455c80ab51156a02acc255980ab1095447aa84155080aa10153c1aa78054d86a961552c02a54154906a920151c22a38054508a8a0151402a24154480a870950e02a10353a9ea73094e6029cc05370aa6c094d0229a0053304a5d254ba02970152c08a58014aa1a950152904a52014a402948052882a510149632928152500a4a0149402920252208a3a29474028e4151b06a350546a028d0151a00a310d462028c405160aa2c014560a8ac051580a280d450028a0051304a260144c02898051300a230d41ab282c250580a0b014140a8088501009ff0d3fa127e444fb849f7013ee027d424fa809f5013de327bc04f7029ee013d61a7ac04f5029ea013d4027a804f5009e9053ca2279404f2809e20d3c40278804f1009df0d3bc0a77024ee009db053b60276c04ed809db013aa3275014e8869d0053a00273c14e6849b171362026b444d5849ab013540a6a804d4829a9013520268484d00299f0533c0a67804cf0099e013342266804cc04998013300266004cc009970532e0265c04c88c991013220263c24c78098f0131e0263034c60098b052dee25bc04b588969092d2025a404b480969012d20258c64b180961092c20258404af0695e012ba0a56c24ad80959092b20256014ac00958012b00256004ac009502129e0a53814a68294d0129a0253404a680949112900a52004a304944092841250804a0829257124a02484448f8491d092380a468248c829160d22a0a45014859290a052101241c1483029050520222400147f048fd051f61239d4472068de191b812364346c808d9011a6323481467868cf0119c0a3380465088ca011920a3240464808c8051862a30c0461808c00d180023000460008c001174322e8045c828b80516a1a2d4045a028b401168022c04458008af0515e022bc0457808ae051522a2a40454808a70914e0229c0452848a4051421a280144f8289e0513c02278044f0089e0112c42258044a828950112a02254044a028910d1220224404478487e450fc021f8043e8287c050f8021f0043e0087c010f8021d8643a82875010ea021cc243806870010e0021b824370086d050d6121ac04358086b010d6021ac04320e864010c60a18814310085e110bc02174142e8085b090b602168142d0085a010b20a15c242b80856050ac021502418488137501e2203814068280c0501609ffcc3fd887fa04ff401fe803fd007fa00ff209fe403fc027e840fd001fa003f3047e504fca01f9403f1067e200fc011f8003e6a67cd00f9809f3003e5827cb00f9211f1c23de167ba08f7401ee803dc827b900f7009ee003db047b600f6619ea0b3d2867a500f4809e9003d1827a204f4401e8803d1007a200f4209e8403d00279040f2001e4003c70478d04f1a01e2833c50078808f1001e2003c30478600f0c01e0c33c18078300ee099dc003b78276f00ed819db003b48676900ed009da003b40076608ecc01d9023ac9675900eb009d6003ac0075608ea811d5003aa0075304ea601d4813a80475000e9a19d3403a68074a0ce9401d2803a38674700e7859cf0039d8273b00e7601ce0339a8673500e6809cd003998273300e6409cc803988273004e6001cb823970072e00e5a09cb4038ca871900e3009c60038b8271604e2a09c54038a0271400e2609c4813890071008e2001c4003878270d08e1a01c283385006f650dea09bcc2379806f108de201bc01378006f000ddc11bb80376826ed00dd809bb00375046e904dd009b9c1368ac6d100d9c19b380365866cb00d9409b280364826c900d9009b200364006c800d9001b200364006bd2cd7a01af4035d846bb00d7409ae8035c826b900d7201ae4035a886b500d6611acc0359026b200d6401ac41358026b000d5e09ab81357006ad04d5a01ab0134baa69508d2a01a54034a8069110d2009a3823470068e00d1c01a3803450868a00d1209a2403448068900d0c19a1803430068600d0619a0813400468000cfe099fc033f8067c0cce451961a32c0065800cae0995c032b0264934c8e1191c03220664208c80118e0831c0063800c70018d8231a0463208c56398a813138662604c4a09890130d1461a00c340184883090061200c220984013078260624c0c0181413028060500c0a0180c23008460004bfe097f812ff005fd04bfa017e832f7965ed08bda017b402f5845eb00bd4097a802f4045e704bce0179c02f3805e700bca11758f2eb005d30cba60174c02e9805d00cb9e0973c02e7805cf00b981973002e5825cb00b96016f0f2de005bb04b76016e812dd005b904b72016e012db825b700b6e016dc02d51a5aa00b540169c32d3805a508b4a0169012d2005a304b460168c02d1805a300b440968802d10059f0cb3c0967412ce8059c04b188163002c50458a00b140162022c40058800b0a195fc62bf8057d08afa015f402bd8457b00af6015e032b90c57200ae2095c402b78456f00adc095b802b70056d04ada015b012b21056400ac80159002b10456200ac40157c32af8055e04ab22956402ac8055804ab00155c12ab0255600aaa0955402aa8055308aa60152c82a58054b00a960152c02a48454900a920151c22a18854300a840950802a10054200a840150022a00053f04a7e014f8129f005371ca3ec147c028f8051d08a3a0146832852050a00a12094201283824fc2c9f8013d8627a044f4009e8013d00279824ef109de013bc02748c4e7089cc093980273004e5049ca0138c226c164d7049aa113540269844d2049a0113400266864cd009961132c0265024ca0098c212e0e25b824b50896a012cc2259804b300966012c03257044ac08948412900252004a3049421127c224b904960492c01258024a82495009241924802490048f0c91e0123c02478048f0091e0123032458247c3c8f8011e0423b82476048ea091d012378a46f008dc091b412368046c048d0211a0023382459388b201160122c00457048ae01158122b00456008a81114c122980452048a2090f9321f0043c08876090ec021c064350c86a010d402161242c00856090ac02150242a00852090a4021480428048500109822130042408848010900212004220884401078420f0041c0883801070020e004190c800c900001ff823ff007f818ff001fd823fb007f600fe811fd003f9047f200fe401fc023ee287dc00fb021f6003ec007d410fa801f5003e8087ce08f9c01f2843df187be00f7811ef003db0c7b600f6c01ed023da007b208f6401ec803d8047b000f6001eb043d60079850f3001e5823cb0079600f2421e4803c90078e10f1c01e3023c60078228f0401df063be0077c00ef021de003bc0076e28edc01db023b60076c00ed021d6103ac0075218ea011d4003a60874c00e9801d2043a40074800e9001d20039f1472e40e5c01ca063940072608e3c41c78038e0471420e2801c4823870870e00e1421c2803850070610e0031c00037f046fa10df401be8037b086f600de811bd0037a006e830dd001ba00374006e218dc401b802370006de08d94a1b280363086c600d8811b100362006c208d8401b002360006be08d7421ab0e33e6067c00cf4119e8033c0467800cbcd1978032f0065a10cb011960032c0065800ca8218d9e31b0063018c60018c003180063000c54318a023140060a78c140182023040060608c081181003020060400bd4d17a802f4045e800bcc1179802f3005e600bcc0178062ef045de00bb81176822dd405b610b64216b842d7005a818b308166002ca0859010b200164002c60857e38afc015e842bd0057418ad0615a002b20856400abc31548c2a90055008aa00153822a70054818a900151822a00c53e08a78114e822932852600a4c0149022920052400a402148002900052000a208144002880050e08a1811428227c244f8009ec113d8027b004f6009e4213c80279004f2009d8313a04273044e4089c4113880270044e0009b431368026d004d6109ac013580269084d2009a401338425c2c4b80096c112d8025a044b010960012b82257004ac08958012a82255004a808950012a002520849440928012482249004920091c2123802470048e00910311f8a23f0047e008f4211e8023d00478088f0011d8223a04474008e4111c802390046e108dc01179022f0045e008bc01178022d0845a008b40115842271044c08898011282223084460088c011180221084420088011100021f0443e00878110f0021e0042e387fd80ff801fd083fa007e830fd001ea403d2087a400f3061e6003cc0079800f3001e30c3c40874cf0e9801cf1039c0873410e6021cb043960072810e28a1b73836e006d810db001b504368086d000d9821b20433e9867c00cf0219e0033a0867400ce0219c003380066c10cd801990832e1065c00c988191083220064400c706175642ea005d400ba02173042e40859cb0b380166042cc0059800b204164002bc3057020ae0015c002b80056c10ab88157002ae0055c00ab80155082a80855000aa00154002a41053c30a48c149002900852000a382145082841850410a0801410028008500009f041332c266004cc0099801300c25e084bc00970212a10254004a80095001212424008478208f0011e002381046c108c841190023200458308b00114082280044c10898010f10202704040080800ff081fe003f8107f000fd041fa003f4007d060fa001f2083e4007c800f8041f0003dc1076940ed001d6103ac0074840e8041c4303841070800e1001c0083800070000de081b420368006c820d9001b008360006c000d50c1aa00350106a000d4001a60834c0069800d1081a20031ca063800c60418c003141062800c01417e082f4205d840b908172002dc205b800b70016a102d4005a800b308166002cc0059800b00c150402a00053040a408148002900052000a2081440028800500409f0412e40258104a0409400128002443048800910011e1023c00478008f0011e00228504110081040fe101fc003f8007c0c0f8001f0003d0407a000f4001e8003d00075140da401b4003506068080d000198203186062040c20818400308005b180b60016c002c84059000ae1015c002b02052100a40014800290004f0c09e0013c00278004d0809a001301024080480008e0811c0023020460008a080eca01d8003b00076000e8101d000390406e100dc001b0203408068000cc10160e01460002980001 0x79c0f8908176750aa3ca07c47c0b9de03f2fd06ece8154ee81797d8278aa25f0a24adf8493bc9923ac64b34c28f6b311cd65a35a3546341a5665509ed65139ac926b1e04c62a497c2812b7e024ef2448d9cc2aa5c03dac806a7720bcbe8138f181f11d02f09e4edf1c9bd581292d206f5340947880f88e017aab46956c4a2538a6d62949ac428b222506ad494d551254b109b586116a8812d5635cac029157a4d2b012655e130abd279578912ad0ae55d934aa36b95824feafc9dd5f137aba26709c4adf1093d5c83fab806e59e09c7800f88d017ab6489568572ad12e55ab5eaa946b56657a444a9554935a9e06a3be076ac80ad2da4dab08b34b4d3eabca725604f2ca06f558d72ab12855594894e6bd55ad4aaa92f554a3eaa92535500f44501ad4e025a5969f54c9092a827964837aa36b9546942a7c9c54ea34a9f47953a4812c5af552352a814c954497aa849e8ef93911426b5404c6a7894d4e125a9a8b3502d56961a7d4ca4294929f21850e1289dbdf937ac68b3500d5695da7d40255ac249f56e93a8d5214a414f90b2870924edef89bc4f12dab125755c4a6a9c93d5292570624295213cb201b9d502da9b04f5300947680f889817a7f4d94ee582a541e541d6ca7e2db4ec586428a0ca213da962735284d63e098d3706d4a507b5260d69f5ae548148a8c269212942a4126484150a8b26151c132a309e544814a892695169129d0ae54513ca880294dad7197032541a599072835224fea3c9dd46937a872671504bde4491b2d855a8607f50a0dcee0178ec01f11102f20c546a0812d41451a838a328653e40ca1a5204fa8104a3ae07c4400bd3ec689022814fe4e29f63053ad6da7e6c34f8d66511a8d3a96194227d2024ca9ac3688785da7b0aacb01569e5acd1ca338ff264cae1152881f9da82f8fe4a14ee9129d0ae53a460a768c34ea9b65052747ea42a752db4e653a3e0a153506d1d203b4e40568e1a1c9fa4ea7029c94013ced01fd36c68a6d8c14d25a299d32534a6ca672a14dcd869b1aca52b51a6b2db4d458443caed34159a662aa3a454527c1f0e881ea646b346e8ce4f49fc7b1338a525ef1c48ea022f530b59a926a7508d46a0124d1b233a7a2bf4f0576088acbea155a712a74de5464f09fc7a9338a425ef1a48e9942fd3185d2ea0aacac1152781f9d982f1d003e21205c7380f883817a56270f104829352252d95ca602db4185a6668b2d2f961a552734984d5e1c90d2f06d6520cb4880d628c97bc61233b205e39807c4140bd24244a5b2b94a2522940a4d23945a5a2534b24968f022d2c025a564d94ab19a92d22d0616aa542cd496516900228e581da5302b4a28d2941adb248573ae07f49a58293a354cd466a4c6cd496d39e19213fda40a4b272f0c48692826880845a3e06b4904a291d2db238573ad05f482521e049051fa443262b94829328fc98522c6a6528cd488d9a90ca68e594910128b4845069009cd1f13577f24347896e81cadcc91578a125ef1448e985ad52eb57a5c6ad45cd3695d2dd17241a062b732255df4c9ed2913ba4f2734924de9189ac001318a025f0904a5e2491bbf1216460ae5d20f68f41bd1d8353ac05e38e07c4000bd14128a1e4694725b68e0b0d13929a1d24b46e1b58e82ad080251c503e1fc05e8b494512124a234694660528d0b6d001699822cb4645865f4aac21939a2c2534444968c436b1a06562e0ab43409611c95bde1272c604e38607c3f00bd0295b97b2aec5815c7080f87d017a2d4d92f2952066303f3950a2c6cd4089aa5e133510a35a002d545659a8849ad0a8351c105a1e80946f40ed15015a284d944ed5e5d92b3140572c406e1e40968900a5119609742a944adaa609b34213496be69144499a8851f50196a9732cd08452688494d1003d0f506b4240947000e878815a1e2c143ad5e804ad3be9306260ae5860dc6f80eb11854a1627142849284d1a50c164a164781e0092850aa5099200ef029436da98d1b350d26683c2934324f46f49c87a935a1726342a4a684892b110660ee02d420d5e7ecadcb8957845276f744de8d9abd1734da354b546095e8bd2b51724d9fa2b72e055e1109dc1d9397b926eef84c622096d1492ba2625343e49e87092b639216210ae5840dce3416d08827a0f04a37207c3b40bc43a3f7b846f3c44f8e301f96083706c04f39405677ca250414ca058bb40ad465b932cb71659de29b41852a82ca3505145a0928857c13681c228d001d9c802b4044b46780ece38159e92692d65925acaacfe13ca058bb40ad765a932d0223aa0346d4028d25a8b2cf413da002753fe4da7f89acfe93438807b3f60d46700ece28159db2893ce4f2779a6cfcb499f868b3d0d067949f4ed13648509b3ee1167400acee35c9f44913e28d27d1a64f82309f14993e0d127992e4f79249d16b93ea8fe7cd1dcf92379ee4671084bded493cf683f9ec06e70c0bcae4138338179e62b93d24d279da24f325c9ea6bd3d0d4a794af4ec9469d926c70a0f67901ace701592729b3c51667852749314f48009e0c805e77ca24ee15c9dc6a13b692277a2f4eec529da2bd3b253a7649f4ec04d2b208b398056759a149214f47e09e0c205e7452e4e7a4c9cd4893a254273ca44e69304854bd3a8948e15274e9a4a2b248d3a490a5a0b24e815e9ce29d39851a724a44e3a349c6271395166721a7ce2b439684ab24693e1fd1fbd82379c428541b166819a7cfd3439674ab24493e1f91fbd7a379672ab3ec53e7aca74781429e327f3c04fa0889d4eb9379d526ce0c4c91f4279bf83f2b106e0b809c6640ece58179c302b35cdb2699304e003c96fad935a9b669530cc824199847b3828e66fd1acbfa319660da8f20f66f81acd635c9bb49136e8d263da84ddb4c98e4a136c8c26e4264dba3c9b40493688d26d9a24d1a5c9b5251366092595ae2f986498d4833788fe6e91dcdc2379b24672de5660e895bbd9235f20ab3620fe6c01b9be82f2af04e37007e6b22c4c62409ae47135918269236cd6b619ab693330d0669130ccba3e98b4652c61b4ab826cd50455f10ab350d266251947a1335f00aa8ee0fc6dc0fcc43509a668934697268e304d2c619a46db32cd3a61da14d226d9a249d2fe90a588369bc02d9a104b328d3a67d2747994347509e36c07e5f1a64be2319996d9332db26551b4c9b6096eadd33adba671b6ccdb6c99a6cb330d8a5eda6ccba6e9964c53289825ed20cb7159839252ef44865683686a8655ef0aa5500f66481acb6d6c98c6d9310d8263da54c734697e4ab2da5660e09cbbc93197a2552ea4997b82acc636098a48abda156622302f60559814d93061b2605364c002497e8a12f24a25d0924be46c97a8c12f29525dcaf4ac05d0d00aabd21165d6304ba1549724c12d55ba642314c6c6098b6dd312db261db14bdb4d9864dd30a9b6611364c126597f4c52fa9565ed26cb5159837272ef04c65e0954bb12897324d2ae1b433c32af405537205b2e20965b5a8cb481596c2692d91425b6b04b59349698a32df1465b9a7cb534346e09e6e20fca881bcb40159658d12cb182585344afb649616d92be942599b0cb23594796a32c69b65893095725d9604b32bc954de128a3683e37005d2b6d92565324ac12895c6b32b48fe55d19c79133832256ee648e59e2f4aa3599bd6a735ed466a52fcd3a5d89e4b2fa895668129ccf25199147f2e08ce59ca4c78933831256ee448e5742fcab05d0ce0aabc21151b01f9b782f2a104e36607cdb41794f82793b470eda4824c1a2493a5c9534db2709a64c532ca926193a47325e8d5db0914a886d5dd0cb2400d60c095bb892336b05e53a09c6c80fc9ca4494a4911cf17650db2ca1a6594e49b27092a535234a624594b4891ce54433026c8b84536905b292096399a64731319326d92804da4f9b24a1d6e9476dd28cdb6515b6498b659446c51cad3650d2cca116e9412c527e582394a0c3e12e76a24527a1b4a6032aea0550ca07b22a0d64edb649ca4493a8cd25cd164e13549ba6692e48b238114d9816c9b02592a2b6ba215c6c40fc9936c9304c12675aa4c6b3497b6692e6bd25c8e5da4a93fd15076924525a174a502ac8d0359292b6b9c15c6c00fc92944928279250d1249d2e492a4892a693252d164989f49213691408b246056475243b212091b6882a2972475a648da309218d4bbb19a481b348fa4d36649252891647920c8e23991a46aec448a4612648b3609174b722a95e450adc1712b76f2472a8d6a541abca7b568e469b29096e4f12bbe9a3d9354772688e64b11bc95a3588846324456e390a0c3d92e82d256edc48dd84912e40570c907b2320de44c1a9b102f29304e35807e3809a4822649046ab1865124349e481c659036cb1ce97639caec7194d8ce28b18451237c9ec8893a91026d21e4d64389a1af83d90c06a2ce0762c80ac8356c9024d91fc982419acc84a4a90848d0e88f9d81194761558e227b19a4d56f82ac829349058a120d5824109a4813609002aab741163fa302dc8458d12d91f20523dcb246b93c903add21518a41e30481b599014dd1fe9b23f531472a4d87247cebc8ca3f0b747d96d8fa2d919e5963e0b14759558e529b1c24f63589e4661358f60da51c1956e02a8b281d8b002b1aa4f2304a247a36d8f36c31a84fa3009b47906d5b10ab15e054d6c1f9440378dd2791960d2328a24770348ec8c11b84f23249a477b6d8df6d319ed963b5b0c75b5586f47d1b64fa3209b47506d5a90cab461562e80ac3c12f7ad24e6b20bca181382c0178e68d91ced6e395abad085735807e5080de38a3046e1548e02690f5182375b646e3548576a11c71aa3863346fb6a8de6cd1b659a31ca346393635709a4fa114d401ec6d0358b802b1b097a35c2e93c85559f08b1aadb2359ab46a15759c0ae4ee0d41540bc6896c8d00d919b182324aa4658248ca4c119295234a35467c668ce6d5198d9a1b92736224c86e47d19059a31ca746393e8c609a4fe114d581e93a8358b502b1888f4d5016c618258c14c118496a300abbae92059a0ae6a20b41480bc5ca4c8b726916c9122f0b22cb8548b92904e61122dcaa45b1302720690ced3a2f9352d4a6635049d17a9289fd2345da428ba2cd17053a2d4a32cb06627108d1664e22c4b045935b8b06af15e95e1d91fbd5a3790b6b71ead5e3c52bc7224d87547f0cc8f9ea91bbae2328f02b51d255e3a0ab47214d8d927f1a64fa0009d4629378bf26cd8e4c96542b9a603f27006e0a009c5900ec5a0178ae02b15693227132c4b24d8ac48aff88f9b091ec4396982827504c4e5ea49b3611317a924cffe49564832a2004d8aa08a1460b617012c4725c88d4990e854229da4c46b4187d27d0e64c96442ac544618a64d911893a1f0a74391428a50dab2015616c12c51c668984cd144911fed1e45084585a04b13e9390f027c48a5c8712a112d1a627630c4e45989449d0e050a26c36ac50655880ab0c60961e8a0c4cb5189847f0f24ce0b095a1d03f23504e35607e2463044b46a8958cd128999b051e21c84d89308b0c2096245ae44746088d6c10c4d72241adc47b5788c4af10c56e0ac95c129296c1242b0815e22c1fc4503723304e35407d6082bc419348852b91045322152e44124c8838b3104d3a205a1443d698866bd10857a2009a42c03587f02b0fa5b21f12bbfd12e5770ae45c09e1ea3043cb668782cd0ee4d21581ac3b0158748c10e69b21c63043612486a2490d855a17c0ac3515686802b0d04d21c9abc3825786f2af0dc4de1b493c3592686924aae615c8ac1bc2f02786702f0c4d72180a82b90548624a10c0d4217c92432b6a58a6cc872d7a191a9431a668614bd0bc5495c43321985e8572830aed421722dc2db5785a69f0b290a160adc2b14382a27715316e291abc5034f89e4b513495e25d2b44924f88949d110909fdd1f36023d87e2b70f653a1d4a1c3314282927704e4ea0909cbd39366c0262f4e499ff492ab805743209e4540dc28416c2e82785504a34e07e148a6427b6982847d04c8f5e991ab5da328202cb02853614ca2bff9367a626aff84b9aec96ab686543009b0a21145340ebf681584d26901857202ca6426c5980b49d09890a13eb4c2735e80a2bd0964d21281abf60158394aeff64b95942b8278278476cd03059a1189a4228357eb02b0804d21012b41e82581e2acfec0560f49a421b578374af0848de074abc2093783f26d07c4d55882bc1e03704e04efea05e0e1a840495c80829906a5b20e23041a16c836693010d060d51f41a2325610ab0751860e5a741bb428332d900e53a0c836ab00557ea02b06119a05cb34179447fa25905c115fa40ac0315c759299058d9a0adaf40b1668052bceb04d20a81abf401575324905116e010a73a612455f0ae85a13dd209a41345b82569ce824d15742ba1604f82329c85413e07da840795c81f8c103c4d205234c10c618208b303ad0a048a740e06d5540caaa4155fc40ac0ca418198c1034d4606119c0b93f81625e8500fcd241782501780f8c10291aa04e334091666ba25884e13604422bf781580f6b901897202d26404c608086c100c971d65263f835c80e6b701ad5e0292dc0395780525f0084b9ae8912a685780307f0040dcd1c1782401754a0aed72481ae0983ffc5b7fe684d6e4815242ba1084f6b9468ff2571fe62d21004d7fc8b6ff6d39fe92735ba347f829ca9015d07c27bf9a507f6288fe7141fc12e2a38547f02a0feb149fd1352aa2664274bcfe4949fc4b33f795e5460cc83c179f9ca83f3b417ed8b6fd8d6dfada1bf52577e949efd08fdf98a142845b8496b7090d3a111a1c1db428314af05a93e0a51fc13a3e82447af488d5ad91941115a81b2af02a55a040a7c0094e800284ffa4d9e909abfb92e6b625aa8a15d074279a183f04204e296075fb80bbf281573f260fc4d01cf4903efb697e3692fa2d05f1d34bd323e6bf47af705a5ea49f36313d7a925cf4c4a5d54913a512173c240a8419506c26bf084579d07a1160d5cec983e6b50739240e704c1f7eb4be94527de4bcfa2949cdc983d184d53f05afba095ef5a1beda4e7ae286eb64cd05c279a103f1a603e82c135f601fbeb8377d96a2facd41f542e20a03f735240a7015df35ae39a140733260e64481cc4983e946a7a5698fa29a9f41333d414c730260f4413503816be782572f260f9a971cb8a03969307a04b8e56501ca8a03e335b7cc4b6f9695dedcadbd413e7a5272eb44cdd50993a4931729260a6815cd041fbe502f7c904e34a07df0d263e2b5c7c1470f8ad41f05a03e1c597c249cf82909f1eb4be34527c44bcf80931e6c26bdf8257bd8d4d7cd31ef1333dda4c79a09af74095ed0a63db15c7b2278f6cd41ec9a03da4597b369cf64d09ee2b4bdbc527b52bcf62531e6426bd80157ae8d4d88931eb4b33d614c79809af56055ae49635c23c7a98b6f50d09adc9629905740d09ed724b1ae0963d345b7a5684d6e4b14c02ba0604f710260f41171c3c9838712070d260f40d41c2c903d1c6a7a28a4a7eda9e85b33cfb5e40e6a4e1248102c2f3cec5b79c69cf3696de6921bcc95b798286eae48df822dbee35b7da6b4fa8d59f4da73e73437c8684f7c96dee521bd223e6bc47af5e56dea8a1bd393e6c327af4e4b9e9094bab12374b244e80485c209029785740a09ef3c0fde5c1e84203533a05e34407dcf91a39ea346db2b8f28531b091eb5da3a75546ce948d5cf11a37815d6da2b8dde535e54a2b6313e6c227ad7e4b9aec96a9606540809af261144d00eb510157604a0daa571b50a63c83596d46a2ed64f9d7c992928457918c2ed4939d79213c796c6d329cf1c1b54902ab5081578c8ccde8599e2ca23c50456a002af109b1e109a3c225678004ae08559ad40abc0a4c780268f0ed5dde92bb9aa3c78646ee0655de149bbc193678226aa4415ddfc1b8208276b402ea3a11dde12bbbea346be25ca3815c10013bbcb506d22b8da2531dd8b63bcc607752d8eeed65b45a8bbb23e775464a1e115dee30bbd34e778684ee85b1b40a73b986d50e0aad3e055dc633379966770288ede115a780abb6a6c767268ed65b1d9d2b3b18257022acd66055d91263b193476c6aeed495dcd51e3b4a377012aeed04ddd989b3b293550b0aeec40dc89c13b590177608c0ebe5b141423baf35775d468d884f94102b9128376cf2b8d9c4f1d65a736734275b8d4eb5149bc8b336695e758298eae135a740aba993c753696ea492dd4523ba823f74f466a0411d0141fba702f74d04eeab16dd51a13a613c5010ae80813dd209e3a434b747496e8c91dd151fba22334ff08e8060fdd0c17ba102774a8b6e92d09d049e27f05740209ee76965cfd1cb99a316ed29add84f5cf89ab9092e71925a9f61550001eb9e83572f480e744d1cee2cb9a34273949ce66909bf8aab9413d6ff25ae200f53e416b9c0256fd28ee6c4953c823b5881772f698e68d69ccd2d3992566e929ae4e4f5b9496b8783d3fd05ae62095cbd26392a4c70d498e5c92dcb523b7d9476e827ae584bdb8c96a7684772b05ee5409dac00bb92b4c725480e50d69c9da137fa5a7264ace48939b952137d1566e229ce140f5abc16b918256ae02ae42d2dc80a5b8f94771e27ee3a4cd3b0239fe03f71c03ee3605db912037223d6e4698e32d2dc6125b8ba4771647ee2a8f9c5119b71a324ea08e7f60fdc4c17b8902770d698e1a901c309a38835a70f6849f2969c392b385a4e3fd484e144f5abc969fd04e6ad02ce78d2dcdd25b9aa3e730466e528c9be4a3b7093f72225ee344b9c4496a748473f907ee120bdab00b9fc04d70729c7ec13dc011a36c95c6fd478e084d1bf51e3811346fc480df8d41bb1acb803516ff4b2dfc925bf51f37da326fa25cdf017536c2aa6a8456f8468ddf1a5c1630b81b4e70149cdf28d1b80a737b86d4da0ca9a8155a980ab7ab516f447ede64fdbc8939fa03f22404e07805dbb51a3762346ea468dd6941b9d2637223d6ed8b4dd8d69ba9ab374a416e8480dcc8c9b9518b71a306e225c7e6134fb41eb6f0356d98c0dbe8c1b791a37856a6ef8d4ddd199b851a3701663f20ba7d8135b7422b520156d78aa9a6154fc41eb6d8356d96b8daf161b563036a3606d28c0da2d81b3da83673406a56b87de171b6a2d36c35b6d66aeda695db40abb669274ce0ae7dc135b301fb6583722204e07405db24aa2648576c8028d8d16db15273621424c70ae7c813dae51a36145b6c169cd6e8d13142b9f184f6bf8b6d7cd09af4a72618573e109ed728d1ae5a5b5c2324c008e7c00fdaee2db5d24e6b746897e15cf7c27b58b4c6b5288d62d31acca2354a406b169cd60d09aad2d26da563ed49cd50909abd1f35713e4bd0acd5a0f9aada2354b406a8688d4a9712f02a3529506b48bcd64d79ab1a235526a4da4cc7d8979a9d293531666a42bc976199a8a2db50b576a069ed3e95da7927b4ea3769c284f2516de35abbc4b4f77e69cef8d09dc92bbb724f76149ceb8909b011eb5b23a75646ee968d9d011ab842347062b4dec55dbc4ab36e14f6ca29cd8e509b0c9f36013d6bc25cd6c4b52e82b9ef04f21c06e06809c4c40eb5181769b02ace4db19a528334260698278d2e4c188136306150694478d268c182cb0338a6d6674c2c8a9059411eb4ca3969646ac608c587cb6b051615c7282bb64f5a549cb491355a5262ce0d71a3d243452346446a0d1ed3190d20344a306424a0d108c1a34a63461404ef248d148f1a24983431244ef240d0c8d1a21a2332a5c687250d0a491879ae34114867c268b8c941a09262e294067d260d009319fd202e215067b2609de4919f51833e13c6792489de4819e49a33da446042b8cf44f19e09a320a4169047ed1c8eda2d1bb422335c3282d064fda049db3f137677266b264bd5b895aa192752d24606605886c1333025167546abfa5459d09aac912f56d256a8449d4b09190d02603202cce1161901203392386708c0c389b1364b62644606092c0ccd1b59c5b0b37b49650682ccc98593d1f31fa3261b2dac10585504a6b3714966d28aaa65055b094a9592152a242cd6d258f5192ec93f5c1266a504859a49831e350668688cca9719963030d26c4c42d8a8098181cb02939306678c2cccdb5939a731db426664dacc89398c12130c96d6062c2ad64e549898ac492d663252cc449535c90ab5139216068bb05355a494b304596596a8c98d3997d272eb14f5bf286ace4e4f742710a03465d498cb49416f8a0b2e03e03102cb7a505969a0aea93f5bb2667b60f9961acadd1323da07ccb6d459652031d2336572baba84fd6e099ac812f5242467b20f80b80b316b4c62d462acc4a548c90b28b6c6516d8c9a8d992c9caa613164b6c0c229b1928b63243605fc2c0caadb9951b6b29b6c6526caca0d898b1a6b27a6e64e4c4c989818b120b0816d1a02d21aa5957e8b0af795553827ac924e591c9aaa5131565252a444840b40b32036c63c6c0c86501911a532134662f4aaac84e548098b159294cd242c4a099901b031f24562a2529984858f2302f5155563252a3e4840b00b319a6c6362d8c6a5818cd36319128631248c480918be2831182462d8d8c571818a9b60682645e94a8c525b00a81228f1306274c033c5a147498312154624680c4b18188caa322c626418c0c7edb98f5b631db6263a6aac58d358e53731c26d6374d8c689958c13131725562c49ac1c5b4670b48679655f82c2bd05555889ca8e13158225ac504a589892a6492121206cc440980a40b30f4585b7280c404e187a3026cc546184b0c3852146c9030b3544c44a8a344c18689430c36c4d94d898958185928302c6d61f6c2c3ad2576da0b0da6d6194c2a8293585d24b0aa45589482c0a5857349f2db13258125ca3248946091309354611270a2e48183d2a28b1304cb240c26d258411fb072335b4264a28489831182d9a5060b488c085718252a289a304c82a8c044f144920303a34600288a804d18123030136c4c84d8a80d818013028892060a8c2c10db5819b0b02a6d5cc49cb649096011f2882326052dac06539694a130093e553274bfe4d935c992bfa3e01c048bcc9917f1222fb95c5fb288036091790aa00d0145e34c8afa8f17e49a00c8245f749aaf84b97f62cafd34f5f8686bc4951725272bd23e5f629c7ae138058122fa24c5ee482bce5417cc1f1088265f1692bda8c8f541f2f31505eb4b8bca5417ada82f74605ed6d8bd89b17a92e2f19505e9250bca905796282f21245e7682bcc8fd78d199e983e5f26a2be09757bd1faf42335e2280b624cd58095a871233d207c416099689a62d113157925ca1a489771b62ee36c5da6a8ba68e1430902eab645cf688bb097175d221050345d54a0ba6db1749362e59605d08c0b9e98172d1cabea315ca26cbc0db977db6aef36c5dd6cabb6d89685a6aeca6d3694d253099575930aea25553847aba28e57391aac12315cd2dcb98589724b02d094157725ca16488824132dba6c5b34c0b8a901719252e224657647ca128c9690aaad013e4cd264b32059421182e11544cc260b78d508181a2ddc6454c290b804d0814222deb505ae2b8b7b1416f09a2df4605bb6a0b749b16e4b62d695c59f278b6ed816d4a2ace92e4cb244b671816b9a82d6a5557425ca0e48880c132d5b6c5aa6c0b505b16a0b62d393c5a6268b30051692282cb8145a28d8b411809e5b22cfb5459e4d8b3a5b08041a28313059b6c06a89a1414902cc054598680b3318165c2a2e3c625c38c0b82db4d7db49473655bf6c2b70d556d9372da26c5b24c4b6295568526ab9a3e504464b605b96bcb6ad616c5a92cab4a58968caaad094d59c27ca944e96689b26493220006c0280996580b2c3a5c585498b289115d8a82c6a6c57f2c0b229b13191e2c6b5958c692b0ad055e09f2ba93255e25298c484f3c1f26426c4c84d8ae409161e302c336c5856c0afc58160d362be96019f248aff1655f9272bea4257c29caf6498f34272bcb6c5782d8aed1815d5362ba16c5722a88811a564e30ac94595906aab1e9b963936ac5a6c58a4cab129896212aac224e582484a908f93151eac096e5802c4af45815dca72b994255f274aba4e54c89b26293153224ca92494f30270fd03657104cac8d41544ae2a794c56f288ad4d81568b62b545956969ca9c539530a12b41353cb09caccdb1560b62b24605636d8aae5b1584b62ab16c502248abcdb13fc9a26112c55a6b2ab2d2553da0aac23e557464aac4b9308911e503e4c42d89885b151c0a2a8c605506d8a9ed81539301aa93454c6c0a965b1501b02601204c04689b25b151c2a21846956e8c2adb1655b1b72b5b625676c0acad39589a12b025555f47caba8f54c11aa5fa3255c2dcab65b5554b62aa1655532c4aa4555534a72a514254926ca604d55209725f92d3c809c0240995180b29bb50544690a6ad013f09029e3604fb240a811b13e8902609305404989f24c13e098298b4c5332989ee4c13d89827a92053c8b2a769394d52129993e531272a064c940098a7a1303c709c9e64814e5b62791204f12609e04813b89829bc605364d8a6a9813b498260a3c5336c09804b130496298b604c02588371a550e30aa14595416dca7eda54f9b129eb6153a6c0a70d394d1a129823e4c347aa644f931c9ea9912e530252a024893f890a749203c609ca42901428a027e9245206a0a129413f11a2669504d1298a5c5113ed1a26995c51b4d8a269813e92629534950c47ca108c94a4a2a6813e4cc26498294146936289260527468a4a5b148db628ba6c4f24789c65b1484a228f2505208c0a3edb14593628ea344e22d8a369b14693027d24c518692a2e8f94591928a9454cf27c9964c93051a260a505136d8a24d814451a28796c50d6d8a189b13c91e27096c50a288a0c9414263028436c5074d8a0a8d1380b6281b60502278a00d813fc9e2779204f14809dc8c13f49a27b2504c16b89828f13d9a4a7aa3e4ee4649ac51539c96a6e1253c507c97c0593cd2e2779244f16a09e09713b928275a5c4e74a0800d653f1a8a7db494fa4bc9f29653e12927ba514f44a09e48f93b51927315d4db2aa9aa5153b09727512d3c407c97a05939d202732344e46929a2d0538d1f2712324e127c9c04c93751a26eb504dc4a09bd18136d1a26c96c4d92d89b05313592026aa344bc0287e31a134e2c26936c4d16c09a09b133cb61e184c27a2881a25113363026636c4cb4d89945b13213626336c4c04689885b13052826126c4c046897c9412f51a25e0544088d2a5b1854b22ca95b6e5286d8a4cd89491aaa9134e51c684a329b94513628826250e4aaa1693941121262a3d4bf474a028d93f91aa74a344e82dc9ca5b537cb626d1654d72c49a8555338a72649424c727c98a4f530c9725f92d3c109c3f00d80401325d8164b86b2d22d4d9d9a8b39b4966c4becd4974ea92c9752556614a6cbc94595922b2323f621466c2857d834ae8cc9590ce2aabfc54d7d4a8af09455c827eb2a4cd5c097aa292b52f24e97448cf001f0fb82600f02c8804bd0c095a0d92740824693a8e1245a223593845448896e9b526934a492654b64c29388e52411aa5a96d4642d28aa5952d0b0a3513945326a87c4bd0b895a0c9274062469369112b4a2255a484a46ca9489952c526a4d24a4b048c95e9152b92206614d45c29288c51459ca0a1e12d4ac252954494fd89089801e3dc0a825e07924db6251b6445b2707b4151111222509444a4adc950db929db6a5336c4926ca94ad892912ca5116d42a2d2828595280b086513d4592728864d459498a4f86e3d90a86180b84b40f24eb6c49b48889c910f88a2207a4846929093919923da2a4d26a4994cc91e9151a0a4a2694543725a9304a525c929f51214882b68e455d24db6248a603e56a88ce4e112d2224695c3eb2889295a924ab324836648f6bc91e8e5238aea129594102aa9185451989ca251354862b68de55cf602b2449344872b88ca5112052223fb482be69a910d25219a29c434146e4ca8dc595214a6a3214a48428c906515208a224013e42a2748fc4d8fd89918503e3d60a86120b9159b623c3544744707aa1911c1a223b2444746d88e69b11c6302382603d40a88dd5b91f1b723db6d47a6d88aad951e5b123ba6d43c4d28289951d53095423d4724728de8d4dc918a3715946d0dc7a4150c1c1709581e46b4d88d28d1180a22079344674b87ca5711889e2329444626887ca91103da423024846a8cc8d0d25199a2a24a454642d48c6599124a2a3093e4252748be4d8fa89922e93445b4d88b45b1171ada2cb574566d88a8580f89a2227a4844c6888a2970fad22227b5c3e24b889c4a0fae2822624044b2a08af5a9156b3229b664496bc8a49750dd2ca082554504a289a8e51291aa249394474b888b181110b01e88544464b688695cf402b220a4443f4d887a9110edb61f2a444384c87ca910f382b22046a43e8cc8789a90e93321ca4d43749486c9190d522a1a24441f47c7c68f50b49d21613940d26c7c64c5034932109253cc0cc8660984a40f21894442f2d880a49100c9a2159444296d87c4511098b21f11443c90ac81ed20f80901f02344202b87d65110c23521746642d47c8588f50311a9efa3242a2d485059909ca6a1294a42428c846515088a221093640c26a83e4b8f7c969e406630507c83c0590049820e348400240834d80ffc9020c2444168c082adb0ff898207b5c40f4987fa4c0f80961f012c3fa0208371a90663320bb6a4146cc826d29049a4a08b4841068c81cd050311f1f0a3d40d27c7c84f503497206129404244804484fe4901e306640b07c6060b849c0f2002343f12b8812510ffd1a20396c3f029880a4f100c9e200a384006b47fed58ff91c9fea313f329a7da4f4fa09a9fe12e3fb25a788158fe8171fc15c3f72887eadb0fcd1a1f8c5a3f08ac786158fbc1b1f6a343eb2887d6510fa11a1e10563e54887c08d0f88a21f02344088d480d198f8d1e9efa3a40446c8048d4fe51a1fb16a3f42cc7e4574fb8ae1f614d3ea2947d2518f9ca29f31443e427c7c64f4f84971ef92d3c10cc7b6950f2c149ee25c3db2807b4174f44129ea0453d32a879a4b8f592e1ea95d3d424a7a6100f44a29e796c3ce26879a180f2d301e506c3c906878a080f1d301e20103c52a0788490f0c261e10343dd2a27b2514f60929eb8513d208a7a0094f300f9e401b3c602e78204d2e1ad259b574b26ac95296d2792b974a3d49647692a8e522d1ba4523538d4628fa56d1b0ab86493d45e2768b04e51209ba211351642628644bd07495a051273de246780158c041709201e3bd268776930e89269df24538c2d26da534ef0a49dd14535b2821464b4cb49498b1251342423ec0d87d8131cca5c39849876ed24e61a098683e32b4c86584a0c4d1a18a1343b88c276c9b0e5d271da96d3b42c26544a4c489298604e3b18b2761144c411a1889343284986524a0eca331d22663af48875c524eb4a299392930f24a6c2504ead271b494f35f286738970ce49418ea343a28d2753184e81271d416d3342d2642594e9cb099c12931c24a3e6090e95a89d223f36727e6ba4ccd2c959a012730b07c3e6098e723018d2343372507451a8e86331d026631f29a73e524e78a2997941336252632494e71ae1ccc603986c0636d70e54a41c91343954987224c0e489e1c8a443322b87204d0e6dad9cd3573974ae71456cdd0ab9cb13f3942767264dce3c999a512b33e24e71056cdc8ab9c114c38b2887124d0e09261c3a44335268704d38e05a11c656938a6bc710d48dc5329b89653862bc6b6548e149e99a13a38426c7064d4e009a18505e1f208c3e40d8ddd2e1baa4c37e4886f4d24dd5a098403e3224d86ef180dd9b61bab603734d86e35b8db6349bec6137c4dc6f69b4de536190a653784c46e8938dc9211b89593700dc60e1387c01b0f802636e4886d89b0da9221b436c3204886db1a8dae331ac45d3694d46ce998c7d269b324a36548c6c8914d8d221ac1511ef06c3de098d85ae1aa1443602686bc5b0d4c9a1ae13435a4d86aa8f0d512d1a9a5635247a6604d07b0120f602635f6d46bad98d612e9ad96a3592cc6b0574d5ca69ab1453512886a04f4cbc9d1a793634e26a69a4d07ac230f58363482b868c530d212e1a324c34669c68ad08c18271a5b6634a6bc692598d1caf1a21343050bc67ed70cf11c19fb5033c68067a538cf0a118204e3428d4683148d013319f25e33b498606178ce53619ba443322b866a4d0cc92e1981343386cc66cd78c611a99a16a3332cc662578cbca918c13532c4d86565b0ca52219315c32828864c934cb62d99535732769e64a538c082719126c320488636d70c74b018db5031a2906471a8c863318fc5e31e8a4638998c652f18c24e318252628d80c4cb0188b4831029062d16cc55a118925730f49e61a5b0c25b618416c3060486084f0c312b98595630a0b660e15cc141598182730203277316cecdab9d634f3aa4b474c95ce8d2b1cea4f38e49c71a908dfcad9b795736229e69850cd0c9d99d1370a125a65c4acc909498b92730e24a262484c04270f50361ea04c4c0930bf8a617e340243260436190be5b497fb492e76825a49a4b04b494f94d2fd2925f6514a20a092f93d14d2721164d49089890d0641f607c3ec0b8b85a8137a4c2542805f35a4ba22917c25e2e74a45805a49b8a692994126a25a5ee4a4bd8929261212c76865e8938a6ca794894323727e4524cca68a694814127b2785e24fcbc09d9779372ee2665e4d44bb5a817615c2eb2a05304fca389995f15b2a82ae5c2d709b5261722682522805d11a8b9d3517326628d2a24d8534944a093292d2e52525c6494918908fa84c2190a85c29708603213425c2dd2705b2490a312816ea3c2db6d0516540b609016b9542d92585ae490b611a16b16424a2b85aa530b45ad97025b2df4ae57856ca90ab94514123627e4504ccb789796e12b2da24e5a848c85c2b0fa83e2ce4985a0d70b311c1683502cc68059d164b352716624225d4984bc530901201209402d2ad25a3148b3d2f165a4c25c29a47e504b28949649252130ac4b493096ca611ea4023e28058f1a8b1933162a4c25929a478504b10949619252120cc56c530afca215d95c2b427857a4d0aeda815d3482b468056d164ad52715a24224d2985835a4b023495f45e2bc8a4544994a88b295c95e2882a4570538adca695994c2b228a4985087c8270f903e2a76a0560d20a95a010886426b8d85475b07c4261080542ab49c54a908a8cac9078541f107c552db08382a1068542a78c054c9b0a95301060542a38c05455b8a7e34957c612ae6dc4d4da4ab5b11563612aa6c0550d38a91a115115920b0a83e00f87c01715034829e6c0538910a6a3014cb6c2858b850a504999ae14fc6a29d8cc509174a6db514c36629769452cd24a55a414a3462656825085449909f12813223a26045c4b889c911048661ef07c3de0b89f0a614913427b278521180a3cb613c93c2634b849e9407b82e116a4e2264845188e8a2d1b13f14d27628a4101587b82713a01628929850ed80a162c1010562808d048e5309fa2813981427b6a04f49709f1ad13cb5627847c4021589d9a81390142748a04e60f09c81a148c6a28e8cc51b144a2a2814225d26249c4ac93093921115a3e2254645105a8a18b314215d28329c504534a04a613f9452462844fa4f49dc9e13a9352000cc3d61387ac1f13881626f2504d0d7098ca813692826b4984d0d4099926131c5026e8d44d91489a935134a662674bc4ca9489152693215e2622a448a504980a40ff86425e4684ba4a096d1a12d1281fe0ac4ae4947f42b12fc5b25c6b64b2d0c9612712b1421fc0ac4a88d093d2812923424a2b849f140934a61253502482c848e53094e35128c522504bc49c9489152692616a24b2cc492578918a912294d2434884828d09009a11f23423d2684764d890a2d91fb5b23c6864749388e4a711a35c23147045a5408d1a8118b4022f49c4589088c8a71189421fb0ac45e4f08b62811624c2378d446d1488d533119a5e23049845c5788aca90fd0662264a04465708809e10f93c2268a043c53088da811034022149c44090887ca710f1421f90ac4531a88a229113a5e2254a4448598888af10e94c1f80cc42c54086c1a8ff82d21929842a940860a490604520806240e0c4859a490aa3220a07e40a0cc84c9e10724020d4604204f88349910735020d2a0422d4483d2810623220a2c040ed408102e103b402060484088c0821a0102a601fd2784061b08081e10082c1ff6923fc4f87f4190fd93c1f9078434d2485d1910a1502122664161148241f9000331fc05a3f407c7e0098fa2561ee0823e88c87c5b00f68341ed4803dd1407b0120fb45b1f56843e65587c82d8f80571ef09e3d610cbea2d97ab5b2f36b45d4d58ba5a71713432d368459096cb092195895b2a12ae52653c9c0a193093f25527a2964e42109a9221332382624544bc870918fb8561ea07c3d40b87a09a0f314c1e26d239cd3479da48f2b451c5682314534790a28ab93e14d27427a4d84d09900702600e02c302530784a20b193418149c3b890878ab48ebc651d76ca3c0d78715a90bf95e1672a42c44f477c9d0ef1361dd26a3b64d04c02f00682600d02c2fc5705f0a60ec9441d46b22f8d444b81f0a496c1d7adc39d1a4762308ebb591d62dc3aa5b474cb60a41651d22c42f6538594a10e886e12d09c01609802c0b0e79441cd2d828e51073a350e64661c28ba384d44680b50c916614629a396528728a30e49451c82880140980280b0e31341c42d833c568640ab0df92d15f2680120500240b0e145d1c56d4386d98709ae8e0a3a1c046c37c8d0670b50c796615e27a37a4e86f09b0dd9351ba2680100980200b0b915c1712982a85505549e09d14413b26836ad245c5a089603e1b88c236edb46d9b08da16c17029c2a64f84e49b09584e1372882704d0540ae0a913c1af8b235d1446ca330d8b491b068a31c5986b4a20a793e13626c2de5705b8a60b734e1a96842541386adb30d535e18d2cc2da5786a09a09485e16c2b82d64f0691270b5a4212809c34d1a8696290c616616a2bc34653049c2f0d094419f25833c8d066cae0ce93419b482340d3c671a18cd14e1842b82ba4f0510a20c54691988c232edb4589b48a43651966c230c5385709f0a1936003028326db0645360c81241946a23248fc63d198c713f18d25e31849c4981f0018161412882b64f0612300c546a1898cc28cd34621a48c3b4515e68230c5985649f0a01361846b8302930601220bf46017d6d82f8d80509ae0bca481764682f2d305d5180bb24c1756882b49705d0920b94601716c02de9705b9260b635016b680306d6c609ab8bfa5b17b4ae2f48fc5e11d8bba371734662e055c5b4978b51271682682cc5b059dad8b2b571632682b457057c9a0aeb6c15b6882b4970589b50b0b661606bc2bcd48570b30ac95e13f28c27e4d8544a68aab6c1544d82a4d105452e0a82441578b62ac93854cab8a794f12509c29b16c530a70a496c147288284570511300a13501414902951a8522330a345e1458a4286598500af09f94e13f27c276d804e93009c34813749027b16c4f1a109c95713629e2665704ce2d09a45b13229c25edb04b83609606c12a0482500f04c12d896a5712b2ae2524bc49c9389305612505c3c716c769ad8e83571c769e372d0c6cd2b8d624f1a747e3448dc664ad0ca95718b2ac30a53c5a4a70b214215827e29c4f852c9d09f13713526c2624c84902700102600202c1229204891c090240072460066190471b4883b4d12169223ed143f9a087626911e49218c90428d1f04823a08b46c0e28c81b0b481906400e05c01c07845d1c06025011b49017e90045e2c88b14e0bf2840f88f0472b48884651106ca234d783f9a9075a690cc4bc17a9484651d08c2391154702288d81ed1880682e00d03c1789404492405d2400310c8218980266b608656c00c078060150431ac88594e0ba28405e1500301708856e1078d2223184441ac887a6e0984d221c988435308852600ca49c1729080b82a00582e00b03c2109204193007dc5c0fb682128d3041e35082c660fa8ba1f4d443953506aa6610449420692440924080a460934821408e420d18837a3004f2720824c40b43300502e00a03c1fe8e03f53007da5802b0ac1ecda01d91e05c2500f00681c89683412b07992e02a0ac16e5403bc1205b1500f00501de0903ea2e87f36a0fc6cc1f4d7438935067a660c84a216a94027d248472480824821f28e83e11c87ba380f546c0ea8c4138a48201410f42741e44e03c49b0148660ee06c0100b80200f05a25009e4901028c03b2b4875c690c76a413ad28201a107515e0c62a41d2538260a507414607b2841cc5103911c0719340e569e1c4d0c16d21826a3b03f4661c253835d2686a2410d22501bc8fc3751d86e2370db4661af180359b60691280d26a01a257035230069a6c0d02501bed44369a806ca5c0d84a01aa8fc33d19866a440cb6d819896c3292b84e35807f6a000c0f02d12e04da480c38d00fc8c032228863b6a09a6940fad08318b50629660c429c126528308a303a942005078180d702fc9c05f1340280a804e1502f23005d96c0ba2c004c1501312481f2410b847416e8d82c4a68561450240ac16c0d8018170118540b42b80441902c6280579480aa26815e930258ae056c680ac6a01524c02a0aa05513c0a826815291029cb203c95c0a627817ad6c2e5ab85ab4106b4b60968ec0f51985995b0b22ae1604fc2b89d8559370a526604215801417051c5b0a249c138d40278a604e4500964b81365302649e04b25009427814117827e2904eb6a09a6a40e8d08260b504b9660952bc1265481d09e848b480200c811e4d807c2b00f0560908b611cd081a92d82d24308d29c03a158225a8044c5a08749610c91c22e2d84535808868410ad001fda8040a4407f8a00fc9101e4ae03e13c0794a00ee5901d89e041c5e0828a4100da81f5a903a34a07b2d40f45981e0af03a95207427a0e4d101c09b038c5b06f69c0d296c1652183714e0602780d09701789403314c0652480c491018c9203425005e4800cc9201951c031a400624600c116417ca702f14206cad20d6d481a9a5034b420672bc0c8538184a302e93c0572980ac49014d2202a1240574900ac8e015120029a300150ac0b6da8169a502cb420582cc0aa538148a302893c0140cc08e4f0131a802313c04c8a009297011094024a5004448008ed38119a102294e04428402615813e2f02745204d6d4096d48128b302415e0432780241980e49e01f35003827807d1400ecae01b12c03b4a006c9000e5a701c34203729c06c5080442b020c5e0408a407eda80f5a901e16603a2bc06a4f004033019a350202540381400a0a001393003007c04e0c80c5a88179500262640361800949801626c02428003e4e00ac9400c86002a050050d4009c28012a5c0182a0046130099228122310172a0044124081a480fa3201e07c0305000681200c23101c6920368fc0651980b9320150580260b00441601934902e48a05a8fc0a51981093201d25402c1400501980902b01004601898001ca000325000906800e4d0019a080215600426401d16c035ad805b5700a69e010d0c0152100185611d8b6226d6c425ab88034f0ed6861ce96c3812d0672560c949c18290c29121050a3e0924761188e82111b039a3306d4640b856c140a182113b03426601e1580081700101eac769752e92e98923d1d23fa0e46738452e554a3c8913f8ad2670a84bdf9095bcb12769a24697211cefc1f98002f1e904e24607c0040b80001f 19 6 11 12 7
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsF m_60 g_60 bds_60 (dagRefF 2765 (dagTraceF m_60 s_60 9 f_60) l_60 0) s_60 9 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_0 : treeBlockF 0 32 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_1 : treeBlockF 32 64 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_2 : treeBlockF 64 96 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_3 : treeBlockF 96 128 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_4 : treeBlockF 128 160 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_5 : treeBlockF 160 192 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_6 : treeBlockF 192 224 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_7 : treeBlockF 224 256 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_8 : treeBlockF 256 288 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_9 : treeBlockF 288 320 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_10 : treeBlockF 320 352 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_11 : treeBlockF 352 384 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_12 : treeBlockF 384 416 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_13 : treeBlockF 416 448 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_14 : treeBlockF 448 480 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_15 : treeBlockF 480 512 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_16 : treeBlockF 512 544 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_17 : treeBlockF 544 576 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_18 : treeBlockF 576 608 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_19 : treeBlockF 608 640 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_20 : treeBlockF 640 672 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_21 : treeBlockF 672 704 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_22 : treeBlockF 704 736 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_23 : treeBlockF 736 768 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_24 : treeBlockF 768 800 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_25 : treeBlockF 800 832 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_26 : treeBlockF 832 864 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_27 : treeBlockF 864 896 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_28 : treeBlockF 896 928 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_29 : treeBlockF 928 960 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_30 : treeBlockF 960 992 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_31 : treeBlockF 992 1024 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_32 : treeBlockF 1024 1056 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_33 : treeBlockF 1056 1088 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_34 : treeBlockF 1088 1120 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_35 : treeBlockF 1120 1152 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_36 : treeBlockF 1152 1184 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_37 : treeBlockF 1184 1216 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_38 : treeBlockF 1216 1248 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_39 : treeBlockF 1248 1280 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_40 : treeBlockF 1280 1312 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_41 : treeBlockF 1312 1344 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_42 : treeBlockF 1344 1376 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_43 : treeBlockF 1376 1408 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_44 : treeBlockF 1408 1440 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_45 : treeBlockF 1440 1472 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_46 : treeBlockF 1472 1504 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_47 : treeBlockF 1504 1536 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_48 : treeBlockF 1536 1568 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_49 : treeBlockF 1568 1600 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_50 : treeBlockF 1600 1632 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_51 : treeBlockF 1632 1664 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_52 : treeBlockF 1664 1696 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_53 : treeBlockF 1696 1728 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_54 : treeBlockF 1728 1760 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_55 : treeBlockF 1760 1792 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_56 : treeBlockF 1792 1824 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_57 : treeBlockF 1824 1856 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_58 : treeBlockF 1856 1888 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_59 : treeBlockF 1888 1920 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_60 : treeBlockF 1920 1952 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_61 : treeBlockF 1952 1984 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_62 : treeBlockF 1984 2016 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_63 : treeBlockF 2016 2048 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_64 : treeBlockF 2048 2080 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_65 : treeBlockF 2080 2112 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_66 : treeBlockF 2112 2144 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_67 : treeBlockF 2144 2176 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_68 : treeBlockF 2176 2208 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_69 : treeBlockF 2208 2240 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_70 : treeBlockF 2240 2272 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_71 : treeBlockF 2272 2304 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_72 : treeBlockF 2304 2336 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_73 : treeBlockF 2336 2368 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_74 : treeBlockF 2368 2400 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_75 : treeBlockF 2400 2432 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_76 : treeBlockF 2432 2464 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_77 : treeBlockF 2464 2496 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_78 : treeBlockF 2496 2528 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_79 : treeBlockF 2528 2560 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_80 : treeBlockF 2560 2592 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_81 : treeBlockF 2592 2624 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_82 : treeBlockF 2624 2656 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_83 : treeBlockF 2656 2688 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_84 : treeBlockF 2688 2720 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_85 : treeBlockF 2720 2752 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_86 : treeBlockF 2752 2765 (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) = true := by decide +kernel
theorem nj_60_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_60_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_60_1 h1 h2)
theorem nj_60_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_1 (fun _ h1 h2 => treeBlockF_at nb_60_2 h1 h2)
theorem nj_60_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_2 (fun _ h1 h2 => treeBlockF_at nb_60_3 h1 h2)
theorem nj_60_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_3 (fun _ h1 h2 => treeBlockF_at nb_60_4 h1 h2)
theorem nj_60_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_4 (fun _ h1 h2 => treeBlockF_at nb_60_5 h1 h2)
theorem nj_60_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_5 (fun _ h1 h2 => treeBlockF_at nb_60_6 h1 h2)
theorem nj_60_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_6 (fun _ h1 h2 => treeBlockF_at nb_60_7 h1 h2)
theorem nj_60_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_7 (fun _ h1 h2 => treeBlockF_at nb_60_8 h1 h2)
theorem nj_60_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_8 (fun _ h1 h2 => treeBlockF_at nb_60_9 h1 h2)
theorem nj_60_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_9 (fun _ h1 h2 => treeBlockF_at nb_60_10 h1 h2)
theorem nj_60_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_10 (fun _ h1 h2 => treeBlockF_at nb_60_11 h1 h2)
theorem nj_60_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_11 (fun _ h1 h2 => treeBlockF_at nb_60_12 h1 h2)
theorem nj_60_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_12 (fun _ h1 h2 => treeBlockF_at nb_60_13 h1 h2)
theorem nj_60_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_13 (fun _ h1 h2 => treeBlockF_at nb_60_14 h1 h2)
theorem nj_60_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_14 (fun _ h1 h2 => treeBlockF_at nb_60_15 h1 h2)
theorem nj_60_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_15 (fun _ h1 h2 => treeBlockF_at nb_60_16 h1 h2)
theorem nj_60_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_16 (fun _ h1 h2 => treeBlockF_at nb_60_17 h1 h2)
theorem nj_60_18 : ∀ i, 0 ≤ i → i < 608 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_17 (fun _ h1 h2 => treeBlockF_at nb_60_18 h1 h2)
theorem nj_60_19 : ∀ i, 0 ≤ i → i < 640 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_18 (fun _ h1 h2 => treeBlockF_at nb_60_19 h1 h2)
theorem nj_60_20 : ∀ i, 0 ≤ i → i < 672 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_19 (fun _ h1 h2 => treeBlockF_at nb_60_20 h1 h2)
theorem nj_60_21 : ∀ i, 0 ≤ i → i < 704 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_20 (fun _ h1 h2 => treeBlockF_at nb_60_21 h1 h2)
theorem nj_60_22 : ∀ i, 0 ≤ i → i < 736 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_21 (fun _ h1 h2 => treeBlockF_at nb_60_22 h1 h2)
theorem nj_60_23 : ∀ i, 0 ≤ i → i < 768 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_22 (fun _ h1 h2 => treeBlockF_at nb_60_23 h1 h2)
theorem nj_60_24 : ∀ i, 0 ≤ i → i < 800 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_23 (fun _ h1 h2 => treeBlockF_at nb_60_24 h1 h2)
theorem nj_60_25 : ∀ i, 0 ≤ i → i < 832 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_24 (fun _ h1 h2 => treeBlockF_at nb_60_25 h1 h2)
theorem nj_60_26 : ∀ i, 0 ≤ i → i < 864 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_25 (fun _ h1 h2 => treeBlockF_at nb_60_26 h1 h2)
theorem nj_60_27 : ∀ i, 0 ≤ i → i < 896 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_26 (fun _ h1 h2 => treeBlockF_at nb_60_27 h1 h2)
theorem nj_60_28 : ∀ i, 0 ≤ i → i < 928 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_27 (fun _ h1 h2 => treeBlockF_at nb_60_28 h1 h2)
theorem nj_60_29 : ∀ i, 0 ≤ i → i < 960 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_28 (fun _ h1 h2 => treeBlockF_at nb_60_29 h1 h2)
theorem nj_60_30 : ∀ i, 0 ≤ i → i < 992 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_29 (fun _ h1 h2 => treeBlockF_at nb_60_30 h1 h2)
theorem nj_60_31 : ∀ i, 0 ≤ i → i < 1024 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_30 (fun _ h1 h2 => treeBlockF_at nb_60_31 h1 h2)
theorem nj_60_32 : ∀ i, 0 ≤ i → i < 1056 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_31 (fun _ h1 h2 => treeBlockF_at nb_60_32 h1 h2)
theorem nj_60_33 : ∀ i, 0 ≤ i → i < 1088 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_32 (fun _ h1 h2 => treeBlockF_at nb_60_33 h1 h2)
theorem nj_60_34 : ∀ i, 0 ≤ i → i < 1120 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_33 (fun _ h1 h2 => treeBlockF_at nb_60_34 h1 h2)
theorem nj_60_35 : ∀ i, 0 ≤ i → i < 1152 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_34 (fun _ h1 h2 => treeBlockF_at nb_60_35 h1 h2)
theorem nj_60_36 : ∀ i, 0 ≤ i → i < 1184 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_35 (fun _ h1 h2 => treeBlockF_at nb_60_36 h1 h2)
theorem nj_60_37 : ∀ i, 0 ≤ i → i < 1216 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_36 (fun _ h1 h2 => treeBlockF_at nb_60_37 h1 h2)
theorem nj_60_38 : ∀ i, 0 ≤ i → i < 1248 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_37 (fun _ h1 h2 => treeBlockF_at nb_60_38 h1 h2)
theorem nj_60_39 : ∀ i, 0 ≤ i → i < 1280 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_38 (fun _ h1 h2 => treeBlockF_at nb_60_39 h1 h2)
theorem nj_60_40 : ∀ i, 0 ≤ i → i < 1312 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_39 (fun _ h1 h2 => treeBlockF_at nb_60_40 h1 h2)
theorem nj_60_41 : ∀ i, 0 ≤ i → i < 1344 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_40 (fun _ h1 h2 => treeBlockF_at nb_60_41 h1 h2)
theorem nj_60_42 : ∀ i, 0 ≤ i → i < 1376 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_41 (fun _ h1 h2 => treeBlockF_at nb_60_42 h1 h2)
theorem nj_60_43 : ∀ i, 0 ≤ i → i < 1408 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_42 (fun _ h1 h2 => treeBlockF_at nb_60_43 h1 h2)
theorem nj_60_44 : ∀ i, 0 ≤ i → i < 1440 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_43 (fun _ h1 h2 => treeBlockF_at nb_60_44 h1 h2)
theorem nj_60_45 : ∀ i, 0 ≤ i → i < 1472 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_44 (fun _ h1 h2 => treeBlockF_at nb_60_45 h1 h2)
theorem nj_60_46 : ∀ i, 0 ≤ i → i < 1504 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_45 (fun _ h1 h2 => treeBlockF_at nb_60_46 h1 h2)
theorem nj_60_47 : ∀ i, 0 ≤ i → i < 1536 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_46 (fun _ h1 h2 => treeBlockF_at nb_60_47 h1 h2)
theorem nj_60_48 : ∀ i, 0 ≤ i → i < 1568 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_47 (fun _ h1 h2 => treeBlockF_at nb_60_48 h1 h2)
theorem nj_60_49 : ∀ i, 0 ≤ i → i < 1600 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_48 (fun _ h1 h2 => treeBlockF_at nb_60_49 h1 h2)
theorem nj_60_50 : ∀ i, 0 ≤ i → i < 1632 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_49 (fun _ h1 h2 => treeBlockF_at nb_60_50 h1 h2)
theorem nj_60_51 : ∀ i, 0 ≤ i → i < 1664 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_50 (fun _ h1 h2 => treeBlockF_at nb_60_51 h1 h2)
theorem nj_60_52 : ∀ i, 0 ≤ i → i < 1696 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_51 (fun _ h1 h2 => treeBlockF_at nb_60_52 h1 h2)
theorem nj_60_53 : ∀ i, 0 ≤ i → i < 1728 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_52 (fun _ h1 h2 => treeBlockF_at nb_60_53 h1 h2)
theorem nj_60_54 : ∀ i, 0 ≤ i → i < 1760 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_53 (fun _ h1 h2 => treeBlockF_at nb_60_54 h1 h2)
theorem nj_60_55 : ∀ i, 0 ≤ i → i < 1792 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_54 (fun _ h1 h2 => treeBlockF_at nb_60_55 h1 h2)
theorem nj_60_56 : ∀ i, 0 ≤ i → i < 1824 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_55 (fun _ h1 h2 => treeBlockF_at nb_60_56 h1 h2)
theorem nj_60_57 : ∀ i, 0 ≤ i → i < 1856 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_56 (fun _ h1 h2 => treeBlockF_at nb_60_57 h1 h2)
theorem nj_60_58 : ∀ i, 0 ≤ i → i < 1888 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_57 (fun _ h1 h2 => treeBlockF_at nb_60_58 h1 h2)
theorem nj_60_59 : ∀ i, 0 ≤ i → i < 1920 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_58 (fun _ h1 h2 => treeBlockF_at nb_60_59 h1 h2)
theorem nj_60_60 : ∀ i, 0 ≤ i → i < 1952 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_59 (fun _ h1 h2 => treeBlockF_at nb_60_60 h1 h2)
theorem nj_60_61 : ∀ i, 0 ≤ i → i < 1984 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_60 (fun _ h1 h2 => treeBlockF_at nb_60_61 h1 h2)
theorem nj_60_62 : ∀ i, 0 ≤ i → i < 2016 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_61 (fun _ h1 h2 => treeBlockF_at nb_60_62 h1 h2)
theorem nj_60_63 : ∀ i, 0 ≤ i → i < 2048 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_62 (fun _ h1 h2 => treeBlockF_at nb_60_63 h1 h2)
theorem nj_60_64 : ∀ i, 0 ≤ i → i < 2080 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_63 (fun _ h1 h2 => treeBlockF_at nb_60_64 h1 h2)
theorem nj_60_65 : ∀ i, 0 ≤ i → i < 2112 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_64 (fun _ h1 h2 => treeBlockF_at nb_60_65 h1 h2)
theorem nj_60_66 : ∀ i, 0 ≤ i → i < 2144 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_65 (fun _ h1 h2 => treeBlockF_at nb_60_66 h1 h2)
theorem nj_60_67 : ∀ i, 0 ≤ i → i < 2176 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_66 (fun _ h1 h2 => treeBlockF_at nb_60_67 h1 h2)
theorem nj_60_68 : ∀ i, 0 ≤ i → i < 2208 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_67 (fun _ h1 h2 => treeBlockF_at nb_60_68 h1 h2)
theorem nj_60_69 : ∀ i, 0 ≤ i → i < 2240 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_68 (fun _ h1 h2 => treeBlockF_at nb_60_69 h1 h2)
theorem nj_60_70 : ∀ i, 0 ≤ i → i < 2272 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_69 (fun _ h1 h2 => treeBlockF_at nb_60_70 h1 h2)
theorem nj_60_71 : ∀ i, 0 ≤ i → i < 2304 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_70 (fun _ h1 h2 => treeBlockF_at nb_60_71 h1 h2)
theorem nj_60_72 : ∀ i, 0 ≤ i → i < 2336 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_71 (fun _ h1 h2 => treeBlockF_at nb_60_72 h1 h2)
theorem nj_60_73 : ∀ i, 0 ≤ i → i < 2368 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_72 (fun _ h1 h2 => treeBlockF_at nb_60_73 h1 h2)
theorem nj_60_74 : ∀ i, 0 ≤ i → i < 2400 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_73 (fun _ h1 h2 => treeBlockF_at nb_60_74 h1 h2)
theorem nj_60_75 : ∀ i, 0 ≤ i → i < 2432 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_74 (fun _ h1 h2 => treeBlockF_at nb_60_75 h1 h2)
theorem nj_60_76 : ∀ i, 0 ≤ i → i < 2464 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_75 (fun _ h1 h2 => treeBlockF_at nb_60_76 h1 h2)
theorem nj_60_77 : ∀ i, 0 ≤ i → i < 2496 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_76 (fun _ h1 h2 => treeBlockF_at nb_60_77 h1 h2)
theorem nj_60_78 : ∀ i, 0 ≤ i → i < 2528 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_77 (fun _ h1 h2 => treeBlockF_at nb_60_78 h1 h2)
theorem nj_60_79 : ∀ i, 0 ≤ i → i < 2560 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_78 (fun _ h1 h2 => treeBlockF_at nb_60_79 h1 h2)
theorem nj_60_80 : ∀ i, 0 ≤ i → i < 2592 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_79 (fun _ h1 h2 => treeBlockF_at nb_60_80 h1 h2)
theorem nj_60_81 : ∀ i, 0 ≤ i → i < 2624 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_80 (fun _ h1 h2 => treeBlockF_at nb_60_81 h1 h2)
theorem nj_60_82 : ∀ i, 0 ≤ i → i < 2656 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_81 (fun _ h1 h2 => treeBlockF_at nb_60_82 h1 h2)
theorem nj_60_83 : ∀ i, 0 ≤ i → i < 2688 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_82 (fun _ h1 h2 => treeBlockF_at nb_60_83 h1 h2)
theorem nj_60_84 : ∀ i, 0 ≤ i → i < 2720 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_83 (fun _ h1 h2 => treeBlockF_at nb_60_84 h1 h2)
theorem nj_60_85 : ∀ i, 0 ≤ i → i < 2752 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_84 (fun _ h1 h2 => treeBlockF_at nb_60_85 h1 h2)
theorem nj_60_86 : ∀ i, 0 ≤ i → i < 2765 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := block_join nj_60_85 (fun _ h1 h2 => treeBlockF_at nb_60_86 h1 h2)
theorem nc_60 : ∀ i, 0 ≤ i → i < 2765 → (dagCheckNodeF m_60 g_60 bds_60 2765 (dagTraceF m_60 s_60 9 f_60) l_60) i = true := nj_60_86
theorem lb_60 : LowerBin m_60 s_60 g_60 10 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_60 sub_60 gl_60 rc_60 nc_60

def m_61 : Nat := 0xffff0000ffff
def s_61 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_61 : Nat := 0x17570000177f
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_51, s_51, 7, g_51)]
theorem kn_61 : KnownBin bds_61 := by
  intro b hb; simp only [bds_61, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_51
theorem sub_61 : ∀ b ∈ bds_61, m_61 &&& b.1 = b.1 := by intro b hb; simp only [bds_61, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_61 : ∀ b ∈ bds_61, canon b.1 g_61 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_61, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_61 : Nat → Nat × Nat := fun _ => (0, 0)
def l_61 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsF m_61 g_61 bds_61 (dagRefF 0 (dagTraceF m_61 s_61 7 f_61) l_61 0) s_61 7 = true := by decide +kernel
theorem nc_61 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_61 g_61 bds_61 0 (dagTraceF m_61 s_61 7 f_61) l_61 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_61 : LowerBin m_61 s_61 g_61 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_61 sub_61 gl_61 rc_61 nc_61

def m_62 : Nat := 0xffffffff00000000
def s_62 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_62 : Nat := 0x117175700000000
def bds_62 : List (Nat × List Nat × Nat × Nat) := [(m_39, s_39, 7, g_39), (m_46, s_46, 7, g_46), (m_48, s_48, 7, g_48), (m_40, s_40, 5, g_40), (m_41, s_41, 5, g_41), (m_43, s_43, 5, g_43), (m_44, s_44, 5, g_44), (m_47, s_47, 5, g_47), (m_49, s_49, 5, g_49), (m_6, s_6, 4, g_6)]
theorem kn_62 : KnownBin bds_62 := by
  intro b hb; simp only [bds_62, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_39
  · exact lb_46
  · exact lb_48
  · exact lb_40
  · exact lb_41
  · exact lb_43
  · exact lb_44
  · exact lb_47
  · exact lb_49
  · exact lb_6
theorem sub_62 : ∀ b ∈ bds_62, m_62 &&& b.1 = b.1 := by intro b hb; simp only [bds_62, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_62 : ∀ b ∈ bds_62, canon b.1 g_62 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_62, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_62 : Nat → Nat × Nat := unpackForestF 0x244924c8924591228b224114005a7c7835d90e24b21c0963c11dc7823990947321253642426c782378f046b1fc9364141247f2419036991fc8e6404124802308fe46b1fc1363c09bc781358f249b1f44923c920c7c34c8f24731ec4923d5184792358f229b1e44d63c01bc780350016871da4d63b41ac6c34b8d86931d25b63a436c6c3478d868b1c4d763962e4713498e268b1c4176360a3c6c1458da6bb1bd172369a4c6d3458da2bb1b451636023c6c04500149f17e976350a2c6a0458bf49f17e93a340aec6805d8bf48f17e91a325ad4662588c94bd19295a3241ec5f9278bf24b182d6a3152c460a5e8c14ad1824f630492c5f8278bf04a00290e291af4523528a44bd1709122e092c5c0258a44a71648d62d5224591278b348916409e2912945804d8a426f158d4a2b6304562538a426b1525362a49ac520378a56a514d18229529c5203500147f0c717a27d2244f94589f08b0c714e259a3c4b24789648d12c9162652244b14789748912c11e18e294499558930ab0c6d7e240a2c4804586369f0c6d3a2362f431b4d88a2ab11415618d2fc4294f88528f10a13e21423c31a5e8634a510514a18d23431a3e87f4a90f358a1f6b043cb6287b4c10f29ba1e41ec319278738a70e6d7e1cda7c3a4518734a50c64961c52a43556286fac10d4d8a1b53043526e86a27b0d449618c13c324538646bf0c8d3e19628c3225286304a0028ee0f22f42f93585f06b07914e1689fc2d13785a07f0b40de0f22942b35c85626b0ac0d60f1a9c2992585304b07894e0f11f42845283c47309758a13630425c6e84b08b07853e11e2f423b538474a7078536106b14224608418dd082576104a2c1e04f83d8bd07ad4e0f529c1e04d00146ef9b17a0e5a23e6c528354a906a5560d42abe6b5f82d48d062d720c52241694782e6b905c9120b423be6b5e82b688f9ad4a09d2e41395d8270baf9ad1e0889fc1113782207f0440de085263e6b468188a5032d3e065a1c0c93f81926f0320fe0641bc0c24c7cd68afe0d3a0509ac0a0357f068701e4fe03c9bc0783f80f06efe0d0a0309ac060357f047f00a93e01521c0292f80524f00a0be01413bf823e80027f0004de0001fc000377f047aff3149ff1a83fe2447f96bcff2935fe41abf813f7f18a4fead41fd5223f8b5e7f149afe2535fc49abf803f7cd688f9a979fb0923f60247cd4a4f9a939f3526bf3c527e74bcf9a8f9f95a23e6a3d7e169cfc2939f84a73ef4547df8a8fbc0f5f3493bed35f7da68efb4949f3492beb34e7d649cfac139f4a2a3ea4547d227afa4495f3413be735f7ce68ef9c949f3412800a337c9472f928d5f241abb6b4b76d692f869b5f15363e1a617c30daedad1ddb5a2be03447ba8b2f7cdb1eea2abde3587ba48cf74095db525bb6a497b06daf6b1b1ed51c3d83497b34c0f60d15ec124bd806d76d48eeda915ea9ab3d53547ab6b0f540d5db51fbcf34d79e4baf4c091e792d3cf25679e4aaf3c951e79233cf12679f4b0f3c095db51dbc9c5a7938b2f27161e4e2b3cc35c7938a2f268e5e4ca73ca45479309aeda8dde45263c234578c692f18d05e311f3c613e784688f089b1e112b3c22547874a8f088f9e152c3c202576d466ef2d75e062e3bcb4977968aef2975de528bbe35c779492ef4901de522bb68477776b8edc8fddd52e3b723b7738a0edc8dddbda23b7a6c76f4b8edc8cddb42280094f73b6bce76d49d99ab3b33547676b8ecc155ced2fbaf26d75e4aaebc951d7922baf24475f490ebc095ced29bada4475b04ae7692dd61ae3ac05d73b48eeac095ced1dbaa25e73b472ea28e5d442eb9da3774f8a4e768d5d3494b9d95e74649ae8c905d25a63a3239747460e8c8d5cec1bb9e3527436b0e7897dd012a3a024c73c4a6e7892dcf123b9e15e73b06a0024fdb062f39aa39737078e6a8d5cd41ab60c5372847ee64d31ca11db9804c72846ee5c8f1cada239623472b048e508cdca01fb940376c18a4e46d71c8d1cb91a3572306ad82d4dc722d38e45971c8b0e39159c762838e0556c14bee09585c61a538c346704ac0e2d5a1c1136b8225e7044bae08971c442e38225570fac0e08935c35a738224c70b8c0e08915c1eb038394c707288e08499c15283820256c14a6e048e1be6b13804606f96dcdfcd71be5b137ca6e6fbac0df2989be41ab60a4f6f6688dec8e1bca29b7935e6f346ade4949b0526b783446e5ac4dcadb9bb6b0372b626eb8c0dca9b9ba12e3740246e54c4dca975b9412b60a436e2688dc4911b7a29b702466de6bcdbc979b0520b6db5c6db06ad828fdb612e36c0256c1466dac095b049f3665626d38c0d991b9b312eb662516cf6b8d98925b35203662456c109ed85179b09a9b644546c24bed8a951b15263612536c247ed848cdb04268009376bd4aad7c971af42ab2bc5f6b18dad62d29ac5a335c23d6b1688d62929ac523358a456b1488d64931ac422b2bc536aa8b2d55155ab02f3560526aa4a8d5415595dafb52c6e6a78a4d4a911a9422b2bb4f6a0ac4d44d79a812e35005d65768ed39165a722ab4e0556574bed16d3da662e345b4b68b68ed2cd71a522a34a23468b686d22db1a45ae345a3f68e8c0d1d141a2d1bb4584f68b08ecae97995d2934146e687488d05189a122a34236c6824dcd0411595d27b2ba4e67f4bccae9299deb733bd6267a8c0cf4d619dd3733ba4e6770bacae91d9ca29339c586736b0ce497d95d2332ba4266f268cd88fd9b4a63362376572bccc4d89989ad3313526674c0cc49b99952c33125e663480cc495995c13b2c45f65e688cbc92196229b2c35f65869ecb0d1d9612932c15e65704a0024bd94dacb2a3506530aab8d17d90e36b21b4a643692c86d2193426321b46643494c948f990d24321a46646270c8c4d190ca332234064308ab8d14d719af31e56163c4bcc7c1718f12b31e0255c66a6c70d298e1a331c1466288a2c6d5818a127b1a35c628496c631818c42e31424762f498c56d518ad2631624462b048c5090d8a017b140275c66a4b8cd39876b730ed62622ac0c449718763131036061d4dcc3a98987412ae334b61b48cc331498652f2e334a6138a4c2a0fd8541bb09c50613098b8cd1981ab730356260eac0c1cd5181a313063606064dcc129318241230326260649ac0c095719a1ae33425fd8b4c02d61805a42fea5e5fd4acbfa9317f412ae32535f0adcbe15897e6b02f84625f76c0be09b97ca2f2f94525f24bcbe49497c1262f80255c6496bc75b978eb12f65605e38c4bd4d8178d372f2c5e5e58a4bca979795292f1a4c5e304ab8c90d76a2faf01445da8a6bbc91177628aed3525db6a4bb4055718972e84625d08b4ba1149755b02e836e5d36b0ba0d79745a02e83565c607eb8f17d731a22e62485c78a6b8ed7971d29ae3a4b5c7486b8c0f400493ae12395c246ab844d549da5a93b495bc4dab7c9b16f130ade16d52768ea4ed156e5a22d9c595b76d8b671556d5ac2d9a465b324aa4e92d49d24ad4b6d5ae8d8b5c8e16a5a4ad62605a968ab529256a4b6a93a4752748ab46d5968daa2d23585a326aa4e8fd65da6acba5d59f248b2e96965d2b2cba555974a8b2e9196652c2cb92559704ca4e8ed6322d2c645958c8b0b19159645ae2c645158c472b1d151630a6ac604e52746eb149315f5a2ac2b49585682b0a8f96141f2beb4457d4d8afa9595f52a2c025457d47cafc9615f492a93a335726daaf51b15c9a4ab93455724daae49855d5b62b92495734a0ae491549ca3ab836c56747eadc9b159d1dab646056746ead0d115a1362b425c567466a4e515571ab2ae354563488ab8965585b62ae25555f4a8ab88e55762c2ae23552727ea9516952a2caa545854a8acaacd7152a28aaa25c54a4b2aa51815292aaa7b5454f4b0a94935531aa2a625454a482a9413949c9baa424453b8b2a8c9b14ee2aa9da5d5434a8a769694ed2b29da5553b4a8a7c9514ed2529e45853b48ca4e4bd4e5a42944595376c0a511554a1ad2943595286b0a50d594c52629435152e8b0a5c9514a1a5295c6052b8b0a50d194a09729403e52724e00213d2e1af25c3525206aca40d51485ae2901554b84bea309b54612aa8c25451848aa309114652428c1254b84a6a2a91145492a5c24b5126b8a245752e123a881254b8476a1c9792e11ca85a3950b2ba9708dd4262925c2354fe6ac9fcd514152227f2595036d89fc9554052a27f2394ff8b09fc8d52e0afa7a35c4f44ba9e89453e1ae27c25c4f44729eb1413d52027a2354b828e9da9753b528a7835c4ed4729dc9013b51aa5c1374e48a49d51613912fa73a5c4e74889c894d3911da722374b826a9a71b938522269c624df6a89a69b937522269a624d349a9b491134d25269a464d348a9ab17935629269a444d32dc9704bd302372683484c08c499cd51301b7265c6c4cb488980d89301a52603494c64bc98c949301a42603464c3498980d053009726003e4b824e9724a52e412a5c81f4ba4b09748e12e40ba5c05e00107e7eb1792c91ca5a13c4b246a9644d4fd629a52a3f4af69894a8ed2b4a6252a374ab478950d112a51a2541244a546694a4fd2949b9fac524a06b89408e52811aa501353f56a69331692662ca4cc584998ac935141264aa9faa5f481ac292ad29255a3240d60493ad09029b52052f240a5d4814b891c5712052aa4656048149a914d392052624446048148a90c94120492a41560482298904511204131faa5347f4708ed5891f63023b36e47b6b88ecd891d93723c5604764c48ec4d4fd527a39b444734708df14d1bdaf23823546f4a47ea9351b5a22315624626dc8d5581189b12344604624dc8ca971194922312624624ba8c4494fd521a2fb4445f4888b714d1752322db5e45b4bc7ea905161ae22c1353f547e8aa971154929faa334468b488d16511a2c22345644f4b888c9651363022325544a6a889496111926a23b544474a888c904fd4afa1cd624438c0872db9105ae21cb624394ba8729450f5ae21ca3943b4808728d50e4b71fa94f42f8a685ed790d5aa217a5f4324b88649110bd29a17a4f42f4867ea535095ae212a5d4254a2852d710a52e212a394268a084c9010951a9fa93f4234a881f5b908522207d6241e8c083d16103d3720e25c40f4c481e97903d2ea0bb5e4176a481e97103d2aa0a25c40f4a4823161044a620796e40f2bc7ea4bd035ac1fdd6e40b6907f75890262c1fdb6e406ac080c970fedb11fdb5e4034987f6d64feda91fdb513fe4bc7fc948feda81fe3503fb25c7ea49cfd8129fb01f3f74a07ec05cfd41f0008373f14aa7e4970fc4aa9a145f3e58da7cad28f95a31f623d3e56887ca928f95231f2a453e54887cc930f94a29a14533de8b27bd154f80af1f01523de4a87bc554d09af9ecc6e3db8a47b2910f64a29a134f3d4ac47acd78f512e1ea15d34268e7a1164f422a9e81553424be77ed3cf362e1dfb4b3bf68e794d70f222a1e42343bf68678adb0f15ae1dfa3f3c28c0785140efd1b9df94f3bf28e684978d09291db46e3bb48876d188ee22a1dc36c3b64dc76c514d09279a124e3b34bc684928eaeb71d5d623ae8c075cd60ead371d5a4e3ab2ba68491ce9a291d3c583a76b074c97cd09231a12423a3488731164e85361cc4553984b4730958e612a9cc25439b4a8730928e662c1cc2463422be7131b8e55221c4c623936a87129b8e45221c4a62389494712918e25229c5c5e38b8a4712910e24b71a114f3874a86ef5b8e15221bbd623828c0705160ddd371c025c3774c46ee978ddd2e9bdb5e37b6a46ee970ddd291bb94e3770bc68451cda2311b445a3688a46e4d80da1371b7b5836f6906d0978db1a81b63403684ac6d2578da4a91b424c34226e6cc950d62371ac4623634886b1178d622d1b025c3588ac6b1148d75b01ac26e35b6b06b0978d65a01ac25634224e69f17cd51a41aa24434f8a669ed48d3d2f9a7a4f34f48e684494d349a1a1a3f34b2986868dcd0c1f9a3c583472986860dcd149e1a182734302a6841780041799f35933f6a067c5549862f99746d32e69465cd24cb9a419c14c32e68c65c928cd51f19724832e48c664d00cb8a299793832f26865c11898629930b5e327ac264e978ca4ae193a5632724a4c2d4cc8da5191b4632308c627144c86b0189a4f31f6b862692cc723018e15c31348e634930c59aa18b24c31748862c490c4d2198992f31324e4c2d48985a718456e308ac461b580c352e18446230b6c06109b8c213118412526169660c918c122918225e2616945fd148c009f9801372fe8a05fc530985a3178d6e2f1ac45f3580be5aa178c622f76c05e29b8bd12617a1242f14c45e2934bc492930b432616845d1168bb1ac1763482e84bc5d0958ba1261741252614a65b75b8b6eb11725602db8c45c4d80b6d3716ec5e2dd8a45ba978b752916da4c2db24a4c292cb3ab71675622d7ac059d188b55b016726e2d08bc5a1148b412f1682522ce49859c494985219663482bf8b2594d80afe2a95fb5a2bf6b257ed60afdab161c582c34a857ed28b02301604582bf68c4c257cab63715e3482ad8c4574d50ab5b715bc6c2b748855ad88ab5a5156b492b24bc564948ab5a4156b462ae4b055c8e0ab4b713094f2ab6b05375b8aa5a414dd622a78b0536db8a92b015225c29b6c4536d78a6da914db5129e4bc53c948a6da814e25029b29c4c251ca2631144c5a2898a452cd80a253714a24c2894c4524d60a252f14824c2894b451cd00a252b14624c2894a45125b8a24af13093f2808be50ad20a15221404532806a6500d2ca01a194025e26127a4df1889be2d137c5227b6c04de9b89e1ac13c34826f4bc4ead409d5a0137a562722bc4e45489bd2613813c26f2dc4c24bc98a2f9361442628a64d49109a6289313522620be4c413c995a81310472634a44c40549841700082725f4704b6d649752812db5525b4b200517c9323692c23824c6924ac900931a292624a24c4924989209412612824024c48c4985189341a1260460028a649492090e2c9242602438aa48696890d2c921a582434ac004d7c9053411a36d23f490468d788f52811a3562344744688e48d11c11c35823446c4684d88d41211a0360026a64451b88c52411146222f4b0444db88b51c11136222249444492489daf113b522272bc44492088923111146223068444118009a790556e21f4b041558882a2f10e25820a8ba434960829b710c23820a6c4414d58829a710523a20a47241f17883e29107b4e20f2bc4148e08291b10513620b0484140d8009a59042581fcadc40c9207f2b10fe34e1fc6923f89787f1290fe2511fd69c3fad247f4af0fe25000268e37b5b87e5200fbc541f74b037b5887d52c0dec6e1f34803e31507c5240dec621ee6b83dc9406f62b0f5b5c1eb4a037b1547a5240ef45e1e74903bd148779a70f22481de69a3bc938779210ef2411df29c3bc9006f62a0deb6e1db47037ad886f5af0ec2581bd6ba37ad387522a0ea2481bd69a3a45007462a0dea3a1bd47239517872a290e535e1ca6a43945786f51c0e43401c58a838d150715b00dea361c32803851506f49b0e01401be8a837c0906f41b0013431bb6a83628fc6e52a0d8a3b1b78b03628dc6d5a40d93441b24d83649506c51980125e1a6ac234d184698af0d5b5c1ab6a034c558698a70d3c581a78a034c518009298d0b491a148c3444d0684230b045119c6bc3388d8674920ce0361606a232f1b065db00cb9481972882c0d3c64ab00c936c1922703244d0581a58c756018e2b831c540581a38c15601828c0313140624a00c14541826c03044e060e280c1b501836883044d0581a18c056016029e2fc970580a58bcc601796b82f51405e5a80b01471766802ec5305c92a0b914c1732882e4510580a18b846016027e2dc9305809d8b4c581698a02d51405a5b00b01371666802cc4f0585220b095c1634602c44d0584aa0b01330024a400493854ab70a95621528b22a5144562b00ac15c1526c42ac980548b70a916215229c2a4518009258a7b4914f28c2831485322c0a61541416be2944d0505a98a245e1448a4288d78511a90a21361416822848c4504af00124a12f8a42768fc4ed1d89da3713b46625f1404e23009c45812f4be2655804c92e099c501336982649304bd29897a4c12f480004918472b708e56211c8b223914449eb00943401274a8238d884953008e16e1212982425104849e08e16211c29c23cd40470a308e13d0024862344d8465a48012421128be22ad10455220894531136a22249780091f07cc6e0f98c41f31783e629085c6010b2981f2d884222808414c0f96b420b140414a607cb521034c01f25b84049e07c9620ff4b01f25783f62807c95a0fb4801f25583e4a900123b0f76b01d317c3d4a2074c530f269c1e44d83a5a907645e0ec8a41d8d783b1a90761360e96841d48c83a4af00123a0d88be1c8d203951e0722480d88a61c31743862886c3520db49e1b692c36d2386e24c0db4861b0d40361a406c34000246c16b1b82d63105ac5e0b58a41a1180345a00682440b56c419b1403352205ab5a0ca8a01949102d5a90642600b52dc188570310aa06213c0b52c41829603052405a95e0bf27816a5682e9a005e3400ba4a01749002d4ab05b96c0b727816a5482d49e8012330b36a814b17c2c4a2052c530ae69215c518295af054b5e0ab268152d482a49b052b4e0a66ba14c8f8294af00123209368a126914281aa05013809347e13a95027494049a3b09b2801268dc2649804b3440964d812c95024d1984a23e0932440045782452e04803e07e8a411cd701f9a983f25f087ac010e97021d260444500872500fc94c211af04225207e49a104d701f91f84025c07e4660fc4c0008a303245f0796900f29201e4a40324530772900e91441d4ae03a02e0646a40e31481c52f03234a06f4980c894c1b52603224b06b4980c890c195a78341340656860ccd041952103212000226c092d141252282fb5405f2700928fc1712a02e1280494760b45001251b82c1300556880aa9b01552a024a3305347c09248813da402794504f27a0920d8129a282524804a4740940401241300105e0474b808c0f80a62902235c0296a605297c0f6b001ea5c03d49807d1400f494014a5303a6bc0749480a52681c35c02947e06c9700a5198149300316900625140c49e81485e02a8a405d1400a92901594e02b2840549000a4130010460038be048d20091240121480038a604452007e2881015c01f05c006d480722900e25e00369403493000d2980c24c00349602c93000d2180834f013068020d0c045a0808242003240016d1402d24005a3a00b020006178012290044500044a400a538014a100224000308c0040d80040b80001f 12 11
def l_62 : Nat → Nat → Option Nat := unpackLinksF 0x1174062e60c5c428b78515e462b22c56018ab8314b3228c2c51808a3011460226e7c4c468980312f0625a144b408958512b022540c4a028940111c3222e2c458188a831130a226044442888811100621c14438088683101321f82c38d9871810e3021be24370386e010dc021ac3434c3868850d1021a00c3400868010c8221862c3042860810c006180043000860010b8221662c269984a8b094061260c23468440b08802110041f8a83c0d077060ee041d4283a03074020d454194583203064020c414184183081060060ac54144581c33034120660c0c818190103202064040b458158502b020540c0a80814830251204a040844810030200203e0c064680c81018060282404c1809810120601833fc5b7f706fee01fdc03fb807f48afe901fd203f9c27f284fe501fc80bf9007f182fd82dfb003f6007ea08fd401fa803f3c57e684fcd01f902bf2007e400fc219f820bf0407e002fc001f723bee017dc00fb315f6213ec407d784faf01f5a13eb407d602fac01f464be8817d100fa201f4403e8417cd0ef9a01f3013e6007cb04f9601f2a0be5407ca02f8b25f140be2807c500f8a01f120be0877b2baf6309ec40bd8417ac90f5709eac0bd5027a982f4929e9203d2407a480f4319e8603d0c079f88f3d09e7a03ce0579b04f3505e6613cc8179510f2a01e5403ca807918ef2109e400bc78278e82f1c05e2843c50078a00f1401e1a3bbc5c77688eec05dce2bb9c077380ee701dc42bb80277000ee001dbc13b78076f00edc09dae2bb58176a04ed401da803b5007678aecf01d9e03b3c076780eca15d9013b20076400ec801d9003b20076400ec801d7e4bae8575c82eb901d7203acc675902eb201d620bac407560aeac01d5803a90875200ea401d4803a90075200ea401d364ba6c074d80e9b01d3603a58574a82e9501d2a03a4c274980e9301d1253a20174400e8801d0c13a18074300e8601cf8539bcd7350ae6a01cd40399c373302e6409cc803990072f8ae5e05cb813970072e00e5c01cac33958072a82e5015ca003940072800e4a19c9403928072500e4419c880390c172102e3d15c7a038f4071e80e3719c32f385c270a84e1501c1e33834270602e0c01c1413828070092dfe0dbfc037ec36fd80dfa05bf4037e026fc00def25bda137ac26f580deb01bd01b7a006f382de701bce0377896ed86ddb01bb40b76806ec82dd025b9e0b73816e700dcc09b980373006e582dca05b940372806e482dba3db74036e416dc80db805b70036d826db00db505b6a036d016d1a2da301b440b68806d100da201b440366c76cc06d9801b2e0b65c06cb02d9601b2a0b62ca6c502d8a01b120b62406c402d8705b0e0361816c300d8505af6535ec06bd02d7a01af20b5e406bb84d7701aee035dc06ba06d7011aacd355026a904d5201aa40354806a882d4a1da940352806a482d4901a920352406a402d3f25a7e034fc069e06d3c01a78034e4369c80d3415a68034c0469800d3001a562b4ac069406d2801a482348c169102d2201a420b484069002d191da3203464068c02d1801a3003458268b00d1601a2c0343c767caccf7099ec0b3d8067a04cf4019d4533a0267382ce5099ca03388367100ce0099c00337c166e06cda099b403340a66782ccd099961332c066190cc20598403304166002cc00197e0b2c0f65704cae0195c032a0665400ca70594e0329c065302ca60194813290065104ca20193c23278064e04c9c0193803270064c86c99019300b20d564180c800d900031fc163f80c7e058fc031f8063e82c7d018e6531cc063980c71098e00b1c0063704c68198d003194363280c65018c80b190063182c63018c603184263080c61018ae5315c062b80c55098aa03150162a00c4f1589c0b138062508c490589203114462280c420d8820b104062002c3f0587c0b0f8061e82c3d018780b0c4b61880c3101862030c0161800c300185c130b8061700c2819820c3040060800c0f0580a53014060280c050180a03008360082c01018000affc15ff80bfe057dc82fb025f600bec017d802fa825f500be4197c412f8805ef86bdf017b232f5c25eb80bd40d7a802f3865e682bcc0579802f0c95e084bc00577e0aef815df00bbd0577a02ee835dd00bba0177012ee005dc00bb60976a0aed405d516ba80974e0ae9c05d302ba60174c02e9025d200b9c217360ae6c05cc84b99017300ae6005cc00b960972c02e5805c710b8e0171c02e3805c604b881171002e2005c382b870170c0ae0065bf82b7e056fa0adf405be02b7c016f60adec05bd02b70296e002dc005b800b6e096dc02db805b700b6e016dc02d9885a730b4e0169c02d34159f1eb3e0167c02cf8059e82b3d0167612ce4259c80b351166612ccc059980b300d66002cbc158b32b14096221ac40158800b0e0961c02c0cb58180b030160602be8957d00af8095ee0abd4257a80af5015e41abc8057804af0015e002bbc157588ae9095d202b6ce56d80adb015b40ab68056d00ad70d5ae02b58156b00ad60159852b30056504ac90558632b08156100ac20158012b00055e08abc015760aaec055d80ab80d57002adc155b80ab70156a12ad4055a80aab295540aaa0255400aa80154c12a98055282aa50153c3aa74154d84a9b015301aa60054b04a960152c02a58054b00a911552202a24854402a860950c02a0c354180a810950202a04054080a81014f82a9f0053a10a74014e60a9c4253880a70054dc129b8053682a661d4ca0a990153182a63014c40a988053082a61014c00a954b52a80a55014aa0294c252980a53014a60294c05268ca3561466128c4251880a2b19452128a0151400a260944c02874950d06a1a0142e1a85c050b02a160142812850050592a090940e1281c050380a040d4080280c150180a03013f44a7dc34fb809f6053ec027d414f6129eb053d40a7a804f4049e8013d00279c14f3029e6013ca0a79404eb1e9d6013aa0a75404ea029d4013a41274804e9009d1053a00a6fd14df809be0537c026f804df009be0136e3a6d034da009b305366026c814d9009b10534e5269814d3009a50534a0269014d1829a3013440a68804d0829972932e0265814cb009950532a0264c24c980993013260264034c60898c013180263004c58298b013140a62804c482989013100a5fc94bf8097f012fa125f014be0097b052f6025e424bc809760d2ec025d804b986973012e6025c424b880961412c20258014b00095f052bc0a57804ae8295d012ba0257404ae8095c052b80256c14a69c94d012961252c04a484949012920251c24a3029460128a0a51404a2809420d2840250804a00494001280024bd148ab49130922212444048880911012200a424748480909012100a4200484009080120e0a3f8947f008fe011f61a3ec047d808f80d1f0023cc5479808ef111de023bc04750a8ea011ce1a39c0473808e7011cc0a3980472828e5011c80a3900471828da251b402360246b048d6011ac02350246a008d4011a4123345466028cb05196023281465008c9051843a3080461008c10518202304045f848bf0117e022e0745b828b70116c0a2d8045a048b4011660a2c81459008b105162022c40458808b10115e122bc04501e89e0913c02274144e8089c0513802270044c868990113202264044c808960d12a0a254044a028940112802214f442808850110a02214044280883090fe221a5643384866050cc0219024320085a290b01215c142a84855010a41a1480428048500109e0a13034250484a01080520fc141e8483b09076020cc841902832010620a0c014180082f050407a078240f0081e0103032060040b828170102e02058140b00814090280204824090080e1101c0203024060080b050160202c0405808080cfe6a9fcc03f8067f000fde09fbc03f7027ee00fdc01fb413f6807e328fc601f8c03f0847e004fc001f7823ec0c7d800faa19f5403ea807d404fa801f4c13e9807d300fa211f4403e8807c728f8e01f1c03e2847c500f8809f1003df8a7be04f7c01ee843dc827b900f6a21ed403da807b308f6409ec803d8047b000f5a19eb403d6807aa0cf5401ea803d40479840f2e09e5c03cb0279600f2a09e5013c98279300f2409e4803c88279100f0c59e1803c30078600f0a09e1403c28078308f0601e0c03be8c77d00ef611de423bc8077900eee11ddc03bb8077508ee029dc003b78276f00ed819db003b6007690ced201da013b40076800ed001da003b28676404ec801d8c13b18076300ec211d8403a91e75200ea209d4403a68874d00e9809d2c13a58074710e8c09d1803a28274404e8609d0813a08273c14e7801cec13969c72d00e5a01cb40396027290ce22c1c4403888071004e0c51c1803830070600e0c01c0c33810270200e0209c001380006ff04dde81bb42376806ed00dda01bac2375806e518dc611b8c0370066e000db431b60236c006d50cdaa01b3c6367026cd04d9a01b109361046c104d8009afc135f806be04d7c01aec335d806bb00d7211ae4035c806b708d6c09ad80355966a908d5009aa00353826a700d4e01a9423528069d20d3809a70034d0469a00d3209a64034c8069708d2e01a5c03479068f00d1e01a3c03468468910d1201a2403440268800d0e09a1813430068600d0c01a1803428268500d08099d8e33a8267500ce8099d003390467200ce2099c013380067000ce0019c003370466e00cbe7997c032f0265e00cb61996c032d806580ccb00195c132b8065700cae0195c032a0665304ca60194c03221e64208c80118f8231f0063c08c78018f0031d0463a00c74018e0231c0063800c6a198b483168062c04c56098ac03150262904c52018a013138262700c4c0989803128262500c4809868a30d0061a00c3401860230c0061800c300186003081061000c1e0983c03070260e00c1c0183803060460c00c160982c03028c5ed60bda017b402f6025dd3cbba0177402ee805dc04bb80176822ec045d800ba82174822e9005d104ba20174402e7065b564b66116c032d7825af00b5a116b402d1165a200b440168802cc9259900b2e1165812ca0459400b280164432c88058f08b1e0163c02c70258a10b101162002bd1c57a00af4015e412bc8057900aec195d802ba8257500aea015aca2b58056908ad00958862b08256100ac20157c22af8055b10ab60156812ad0055a00aae1955c02ab0255600aac0155022aa0055400a945152412a38454700a8e0151422a28054404a88014f4729e0253a08a74014dc329b8053508a6a014d4029a8053500a60294c002941052704a4a1149402910652200a401148002900052000a400146c528d8051320a260144422888050f08a1e0143c02868450c04a180143002848650900a120141c227b224f4089e8013cc1279804f2049e4013c80277864ef009de013bc0277804ec0c9d6093ac0275804e9089b479368026c824d9009aa21354026a024d3049a60133c4267024cd049980932c1265024c51498a01310125b1c4b504968092cc1259804b204964012c41258804b004960012bc1257804ae0495c012b41256804ad00944592880251004a200940112800250004a00094001268624c04496089281125002490449200924012402248004900091c1123802470048b0c9160122812411048200902091fc223f8047e048f8111f0023e0047c008f6091ec023d024731c8b6c116c022c84459008ae1115c0222a44450088a010fc621f0243b0c876010ec021b884370086e010d03219044310485e1104dc209804100c8200103c12070240e008161902811fb283f6007ea08fd401f78c3ee047d810fb001f6003e8107d000f9821f2043e3047c210f1da1e2063c40078410f0801e0043c00077a18ef011de003bc0077800ef001da103b30476408ec801d8823957072808e5001c88638f0871e00e3421c68038a0c71400e2411c3843850870808e1001c2003840070800e1001be1037b046f408de801bc8235d706b808d6821ac82355106a610d4421a78434c0c69608d2811a4823480467e48cad4194063280064e08c9c01910a3220063c20c78018e8231d0063028c60018c003160862c00c58018a043140062608c4c0188063100062000c3821868230d0061a00c340182902f4445dc30bb80175082e9045d200b9c2173022e5045ca00b8c2171802e2045c208b840170802e1005c200b840170802db185b600b64216c802d8045aa18b54016a022d2085a400b441168802cf0855720aac0155022aa0055208aa01153042a60054a08a940152802a20c53c20a70214d042990453200a60114a862940452800a4c1148062823850400a04114080280044f0409e0013b82277004ec089b881370026e004dc009b801350826a004d4009a8013500266104ca08994013202260104be08978112f0025d044b418968012d0025a004b400964112b06250184a00093821268224b0849408928012500248084882090c1121802400c480008fc111f0223a10474008e0211b822350846a008cc2119802320445c208b411168022a0c454008a80114822280444820858e10b002160042a08854010906212004240083c31078020e0441c008302105041fb3c3f6007ec00fc061f8003f0007d430fa801f20c3e4007c800f9001f1043e2007ac60f5801ea043ca2878c20f1801e3003c60078810ef081de003bc0077020ed821db003b60076c00ec841d60c3ac0075800e80c1d00039e0873c00e6061cc003980072c10e4061c80038e0871c00e3801c7003881870820e0821be0c37c006bcf0d7801ae04356186ac00d5021aa0034e1869c00d3021a30c3460068810d10019f0c33e0067c00ce0619c003380066040cc00198003282065000c982193003240864800c80418f0431a1063400c58418a042f6785ec00bc84179002ec185d800bb001730c2e6005cc00b980172042e4005b060b60016b042cc2859410b280165002c61058030b00015f042ba1057400ae8015d002ba0057010ac08158002b00054860a900151042a20053830a70014e0029a0852830a50014a0028c2051410a280141102820050010a00014000280004f4309e8013d00276104ec009d0213904272004e0109c001350c26a004d4009984133002487849000900811e0823420468008d001170c22e0045c008b02116002203044000880010e0820a484101081821030020600400308000100001fc103f4107d840fb001f4083e8007d000f70c1ee003d42076120ec001d6083a03074000e7041ce003981073000e6001cc0039410700a0e0001c000374306e800dc041b80036c106d800d1281a0083400068000cf04192303240063840c70018c083084061000c20017e182fc005f020be0017a082f4005e020bc00178002e8205d000b90416a202aca055020a904152002a40053060a60014c002902051820a108142002801050000a00013a18274004d8409b001360026c004c060980013000260004c00094101164822c0045020870c10e002181043000850410a00214004280084040fe281fc003f8007c0c0f8001ec103d8007a040f4001e8003d0007a000ee181d4203a80073080e6001cc00388406e0c0c85018c103180063000c408170602e0005a080b400164102a88055000aa00148302900051040a20014010280004f0409e0013c00268404d0009808120402400048000900012000220804208084001002020000400007c100ec30189401474002980001 0x12f01725c02e7e20bccf813b5e92f65324f221176441a8c30a4d91549322891620d20c5123983a462e7253644ca2b5e12f65224e96c136448229f802f33d04e4b405daec97b289273ef05e67809c9640bc3a2608654c1216d1642d22c811456ba27ac964d5ad896c879258f708a7dc0f4cd81a9f502d90e04ae4a51d9249aa5104733406a4ae05e2762cbf445890b69d13a96642d1cc8514d64c28b1fe4d5ae496b2412590909a66e1163d01a9f682d33304b072901c90a3b5b92d4a108e7d60b49540bc81a48901469200d1241412481b4c647269202092401183231248984b320c935ad924b262459044832048e63fd1ab229268fe09a49e1163c81a9270158a04970ae91d280239f282f33104f1f09223d91a47ab448fa2491f0d30cc01a47b1248f546065e0909340a44b2598fb49a7d4924cdd22c7ca418f74731e88d63cca69279458f226a65c0989300b44fa4b85648ee4651dac497b219279108bb220d7627925c4aa4985548f0709062f11ec86a3b90c4732108de41d1abf5a3172228eed44f63f49bc7e1356b025ec8449d27c23a9203d8f106f1e00d4f901799682724b02f1c85563b89ac6e8558ed06ad5e4bcf8c179248178ea2dae3c59638ca2c7486d49b0cb1b8115ab8979f102f24702f1cad620c918472c5c8e66bae3cd56391a4c71b458304651c417490c2ac6d04589447706c8cd4801fa4c8373de05f1bcd620bd1846f45c8df6ba936d56375a4c6e34582d4651b657490caac6d14589347706a8cdd989fb8e1376aa25f1ad176185a6c7634b8eb6931d0d1e39da2c5e3418d64a31768fa2491dc1a23382c464c82536384a3c7014576527ee364ddaa49799604d8d908f1b011547c1fa4c0373dd05e48405dd90a7b8a94751e09e92411c9000bc56c608a68c0e1c556354a2c6592548b0ab1a811631012b8614560024e912114bac1391f0178d12bae20555d8ca6b851458ca24b1a01752342aa8e84d48708b1860960ad183b113d5ff24ea380f4ba81391e0178cc6b9198961c20aa3839448b48bd19ad69c41ab465a5e8ca4ace0c55a3241e91b8358c104a46c0562e5a7c2a34751809e90a11cba01bc62b5c8c54b09061512082211a8148b28bd18cd69235ab46225e8c34ad1844f48dc9ac609254810ac46805a2e1a7c29b4775e29ee0851d7f49bc6b35d8b769f162d3a149a3c153428d64bb1a693e34927441a4a8cf48f19c919fad213ae94f70328ebf84dda2496c641278c724aa2e13d200239738373bd05b18009e2fc1291981788d472d504bcf701791901723002e45c05e2e9224561458b924b14a1162e012c5a9258b304b16a9122cd2245b2358b424f16409c8b00bc5804d22508b1520d48900ac56a518ad8c115cd4a2b129c48a4b5a30be8b011cf64179118148aa29a44a5162a49a9110168a64a314d18229da9452a53890496f5457db6ca3b5292f8bd6bd178d4a201a73f4b4d8bb4bd16e94e2c529447a4b88e495118926145233f4a4185146d1028d5ea4afb6d14762627b15e4de2ac9ab5212f5a20be8ae11cc441ec540378a406a7b00bc8840bafd9372e606e44005e2852245014587724b13e1161a012c4c93589706b0fe4961c412c4ca4489748913ad1e27123c4da4689a48b13051d7e89bc3f12789608e5ca0de1c01390f0178942ab0ec49624c2ac338258294891225161d492c4804586604b0428d08740bc46c5e818488f5057d6842f90d8177a72bb1165561e892ad005d88a0ab0d80961ee36436c6c88829f10e51d7d893c4304f88508e5c209c8640b90b8178828a4fca8c1e84afacd05f21602efcad108540bc3eb6087f4a90fb5821edb643da6087eac4f4edba1f1b143d26e7a02dd0f20f48341ac3502520c02b0e89821d228c3bc538766bf0ead3e1cd292cc05f51509e5b60de1bdb0438a5486fac10dadb21b530105814870ac4b40dba1b9b143626e86b27a41a4d61a892acb86e20a02d0ca98219628c344538676bf0ccd3e191293cf15f75b29ebe04de28a2f44f4538958a5124d7e23da7c4734e88c69b09ed15f91a1444a5f8844bd10694a20523427a4588047cfc88f5e74afbad14f5ef26ecfc4b61e093c391255960bea2813cb681b9d902d86904f0c60948240bc0b23020702f02a9020512042845c81348109c575e5c9ec301358450bab200f617c1ac26b6c8124a1022942111b640825080f4a10a092607d20c0724085d27f0b84dda8c97c2d83f85a06e7ae0bc8140bbf445c8586b909057615c9ac1f05d85606b08e57615092c1e85d85304afca8f08100bc284527e5478f2c57d63c2f90181784dad8ffc901ff520426c607fb460ff28c213ab142646e7978c4ff08c1e54b742105d20209b0961161262f4243538474a70508cd6342fa8903f3d405f0895b1fdd203fb2408448c0fe88c1fc9183f8a30845ac50871b9642313f82308422ba404536104a2ac606e83f8bd07cd4e0f529c13a337932beeb04fda8097c30c5e85e8a70b314a155a9c27b4e7e669b0a494e145273f524d85147d09e8e609919c10232817462fde8c1e48afc2514f84629ac24515d5c9fb4f92f58b0bf08013e0f02697e84551107e7a60bc7ec0bc0b34c5ee26e5b20dc7e80b8fc017839688fd08f97b49b96c0371f602f06e9520d8aabee1258350aafa00960c49ac170358326b90629120bdae41724481669906691a0c0a3c168471f402e3e405e0ada20f80178294b9050575f6c92c1385d7cf04b04a4fe0909bc1183f82206e3de05e085260f681781e69f03ad0de44a7c0e13f81b26eb1413e0681fc0c8371ec02f03f14a061263c815f5890be3d405c7a00bbff14d78e27b02a4d5fdc26ac383d81406affad71fd9ae40913f81126f0200fe03c1b8f30177fa29afc64f60349abf11257f309afb00f60301abeb82580a49f01290de34a7c0412f80724eb0c13e01817c028271e502f0064fe0089bc0083f80006e3c605dff62e3feb507fc488ffd149fedaf3c73527fa49afc68f5e30af3f09267f209a3c40f5fe41abfb45c7f66a0fea911fde293fa35e5876a4fe6935f611ebf914d1e227afe24d56142f3eb02681669d026d0e039a1405a3f80447cffe8f5e2ca7bfc13f7e024eb0813dfc01fbea8271dd02ef145757a493ac185d2d404e3b805dfb4923f60241da02e3b205df95a20eb8177e88a4fce979e18afabf85f1d602e3aa05df95a20e98177e369cfc4939f84a73ef83d1c706a384055f7e2a3f04547de07a3880d5f48128e08157dc6befb6d1df69292be85f45508e59c0ddf61a73eba4e7d427a38e4d5f58270df8167d48a837c051f562a3e993d1c426afa44946f40b3e835f7cf68ef9c949e10afb6c1475e326f07517a0e22941a35f82c6bd054d49fa5a6bf234a82668f040d1a05da2bf7b447ee4bcfd6949fa9273f4a4d7e647cfc88f5e0cafb6b9475e226ece04b5f7493bec92557c0be8a811cb341b9d202d7d104ef9a0946f00bbdab547874a8f30d61f012c3dfa597b44aaf968e5f291abc00557c906a7440bcb2c13bdf2487b36a8f8a9b1f1936bd2a697994caf88985ef524bd92457c30da8a0195dfc229d002f2c904e146055f01a23de254798488f7cdb1e622c3de3587bf8b2f7b155ec5aabd8a557a5494f76919dec2a9cf82d7ba04aa0813d13823bc3c547b66b0f6d1b1e1db63daa387b34c0f631b9eddb6bccb657b4692f64d15ec524bd806d2c50caef21154081fa260370a202a142055eadac3d6b567ac6a8f50925e851ab3712e1ba0baeec155ea81a84f815791488f0e951e1d2a3d302409e02af31161e7d2c3d434d79668af4e975e952d3d22567a34aaf44951e85233cb2457a024c370175dd02a9cd02d79e04a138055e3d203cc46c7986b8f1c901e30903ca45479c8b4f37165e6a2c3ccc567978a2f2cd39e19a6bcb239790462f168c1e54a733612e1b60baee4155e4c2695f84509a02af22931e3da4bc734178d47cf184f86d026bb884509802a366175dc02a84b81509602af0e951e152c3c834578b688f149b1e252b3c425478647c362175db82abc202509502af02d61e062e3be25877a6a8ef8d71de9203c135d4506aaf00d25dfda2bbf25d39f4b258a955df528bbda4977948aeeed71dd52e3b9c50771460ee2d11dc1363b7a5c77647eee88eddc91bbb723373969af90d2df1da4be13477c168aed4d0590526bdca4b7b8492f5e91deb922b44a417a947ef3a8ede491bbc1a3374c27ccd64b86c026bbc04776d08a9fa0fd1141b9cb82f2be04e124054e581795e82739405e57609dd9dae3b256d7696aced0d51d913095c85d7660aae840d5d041abafa487646daec89b5d8d2abb125476148aec0911cfc229c802d75e04aeb8911cf822bad8257596b8eb0175cf41aba934575248ae90114e3c16bab0257544bce9a5795782fa140477526bcea48e5d442e95805574606ae9f1495702fa1283774d252e78094e240f956817749490e8ed11d25a63a3a3074b49a71e924ac122ba5241748472e8c8d5b589a3a1b587414a8e80931d11a93a125f73f4a6e7c92dcf523b9e15e6d628ced6d79da9a93b2a5f75d4a6eb492dd5d23b1323d755476ea68e5d411bba7235670462e98579b54a336a93655b0be84811c5781eba283773b06a7100bcab0139c302f2aa04ee04d71bc12839b83c71a4c2e02975bbd28b7ea3d738472e6c8d5b9d18b6a05d55507ae6a0d5c01b639924872e468e32d81cc9a638c26072d460e60131cb91e39602472c468e5ad11bad363958246d36d8120051c5d28b99a3f731476e5e8ddca919b9483f72806e7080bcaa01384781508e02adecd71bdd2e3713506e34a0e4cd71bd52eb70a51725472e488d5b242eb9183508d02ae2d5b1c5928b7f46c71d8a0e2b5b5c862d39045971f8b0e3d159bf628b8aa616fc49cddc909b7d2015305d71c0aad8e1344dc228460156fb6d8ddad81c65a538c34670f4bae16955c2493045815716ad0114055ba52e38885c70fac0e10491c35a736284d13208a112055c2e30383924709ac0e10531c1ca2382a5071aac2e2f581c55b6b7d35e6f26b8dd8d49c5536b8a25e7134bae24971c412ab73a5270e49ae18931c2922b831266c40ba262154dfc16b8202508602ae011b1bed303812387008c0dfcd71beeb0380d626ff6dcdfad89b99aeb7e26e6fa4c4dcc945b442e95103d6f906adeed11bd91c0428156f346a108055bd629b7a35e6f24a4a9c17d3ec278418156ed6c0de0d11bad36376d606eb8c0dd2971ba012377d626ee6dcdd8d89b99aeb7526e6e74c4dcc975b402e9bc82d6e504adc6d11b89223702466e18a6dbed79b792f2a585f4fa09e104055b71ae36185d6db06a1020542000ab6ca5c6c20badb00941fc0ab6b02537803e53605db4eb6369c606cf4b0d9ad51b3dae366a406d4ac4da51b955631368a5d6d04a2544935b3924b66245379482a941b8ddc173644546c64a8d8a931b2a2f364b536c74bed8894db0d1fb612337398bce6914dc9e2939135371b4bee0694dbe127b78a4d67e492c24915b9121b6ea416da47edae8cdb54a736a93e5490bed9613db04268970454f307e6ec0bca681383e8156be4b8d775b5aee30b3ea5d6bf4aabc24d97849321105d6bd0aa22e0b598012b5c23d11605acbe095a1d222f01245e024cd64931aeeb6b5dc6d6ba694d72d19adda234324d6b6494d6a919ad122b59a445df26cbbe49938026b5884511405acba0959cd2a33a2446ad0bcd58149abe2cb574556ab4a8ce4919aa82ab2e0256924d8d22971a462f353c5266f2bcd511b9a413735324466e2dcd4a11596c12b47a6c68e498d44d79a39a933695e6a3ac4d1a9b9a852e33616e6a00bacb40959e92a342a4c67d8bad3d165a762ab4345168349ccf29195102eb4e05566604acf71b1a65ac34b3446998b8d2ad01a59ae34ac546846d8d288d1a49b6348b5c68f8c0d1d14199e3634d34f698696d2ed1da4da1b4823f68d46ed1813da2c23a6f03f41d06e4f409d37027a0d8476844d8d0e911a162a34236c6888dcd0d189a0d3733c25667848c9b6135a0822b3202527704ecfe9794f42fb3da6c67b8c0cf4d619f6b733e5626794dccf09799e12733b85d4150aacc40959d22c339b586758a4ce497d4ec2f93a02766f268cda5319b91fb362374d307e8200dc9bc13b2c0156676d8ccad7198daa333a606654b0cc6901511b73353624db6bccd2d69055ab3343526664dccc89799892b2ed12465f688cbc9219822fb2ec5365c6becb6d3d969a3b2ca526582bcbb44d9af22fb584536a96bed48d3da7da3b4da5f68a4bcd12949a0527b4024e67e494cec91d9c52333824266b2bcbb24d97649329d05f4d209e81c11c9b81b88882d66104ecae095951a8328d6d6518c2caad65879a8b12b49611682bf69257b920af093e5e125c81817594c2aae703d0e706a0f80541ec0ab0534c64d098c74d8191ca232523e5cc07a1c80d41e80ab1ca60646268c7098191c9c323134644680ca35b594636b203616376c0c48d65869ac308351650694c9ed25939a4326346608682bf49657b528b25a4a649490c90919914a32ef93e5df25c99e13590c22ae583d0e306a0f00553341fa040376238d0c1f181774a631135860e680c7c171902b0b10c5a60d8a4c7e9798792d31ea566084a4bb853176026a9802d63c04abf2d657b1a8b1d34a63968cc6c9758c92ab1c1465dd27c0ec0558dab031a25862f488c68d718813631946062e480c621718bd2631602462c488c5cd5183136316a4c62b048baa9b01d00a31bc515f8696bd6d0d8d527b19a4b63048ec5490d7709f26504f40508e6ea0fd8a417b1402707302ac4718188eb031036c6224b8c40d81896b73125626218c4c0f14987d3730f26260749abae13500816b0e82561b48c0e40541c40ab0d4526036a6c329794b42f9ba03f07002aa581758581fb0a8376178a4c291414a82fb0984c60f8c0c1f581839aa30626c60c6c0c1493182412308d6e610ac4c1b18981e2d305a6e6084c4c0e93575826a6102d60604a6e60fd8092e300a346026b0c02d201bc0ab01c5a6004bcbfe9597f9262e484d5fd04a0dc0557d5262fcc605f4498bf35817ddb62f92385f76c0be4d417d62f2fa4525f34bcbe49481b40aafdd6e5faac4bf11897d9372f8a4c5c809abe00941b00aaf424c5ec8c0bce9317b2b02f526c5e5478bd4d81795a82f445e5e78a4bcc979795290358155eeadcbdb5897ae312f4a6e5e4498b8e13578c128350155de4a0bbad81780a22ef2445dd8a2bb609576da92f0c5f5df8a6bb8d494a42fa6084f3fb08ebb4055756362e9c5c5d18a8baad8174dac2e8b405d88c4baf16975a292ea36e5306c4ba4d79009ad2e83564c26a4a501b93002f2e6b445cc490b9d17d72e29ae535e5c94a6b9092d71d21b2945f6428a6c82d798eda9b13b5262669cc38d2d861a5309346605686c08d097f129af7a4b5e2486bb24f97649729385f4bf09e7f411d73c1fae303d0d706a6ce0bc18c0aad73545804a8b22d616e52c2dc2595ad4aab888e570d1aabc9555c226aa8e4bd4e093adba485ac6a8b7c9b16fd36acf2695924cab7a9856d924ad5a455bc2daaae5955e0a2aa292f53624e0c40596e5a22daa54591488b6edb16462c2dab585b88b2b6d1556a9aaad525559e494b689195d0aaaa112d5b324aac453d54ca3ac04545af6b0b5f1b1601b62d72385ac4c0b551b96c1b6ac93655ad692b56d156a924ad496d5322caae45155809faa893706102c0c0059691ac2d33565a56a8b429256691a8dd15d56f2aab464d4d301702f01658a488b009516012a2cf92405d02cb231616652c2d0b4d58f68ab409756792d2cea5659c4aab36951669232c7a451b82baada5554f496acc12559704c0b6059621202c8c6c5916b8b0e90163a2a2c29205958b4b2916564e2c2c94565908a2b1ed395fda6ac7a39589462b088c06d8aeab595558d29aa54515630271a502e05902cb14931621a4ac3b4158647c3685355a8a2ac283e05702c3665755a0aa82b01605502cb009515f92c2c4b45584688b069b16092b2c0a5457f47c36257559caaabe92505402caf4d615ea362baa585736a8aeadb15cd282bdb6d5576caaf2d255e1a2abba6d5424d2a649955d930aba24957248aae0db15b9362b646056a460ad4d115a5362b425c56f47eada8ed5ad1bab3a33563488ac2db157d2a2aec585656acac8d50ae52eab12595604aa7209455791caae23534905c6900b81440a2ab46c5566b8a9ed715512e2a946054d4800a0051541aa2a7a5804f028a9ad515312a2ad45a5598b2ab116155e2b2aac512a64baaa69655452a9bfa5154e49aa7a9254a922aa5a4154a09c68c0b81380a2a42445464d8a8695150d2a29f25453c8b084517551e2caa2c554e08a2a889755092d2a0a565404aaa7e9514f52529da4652926ca524992f027297b58539690a6ed801340a25d84e04c028a631b14c526297c5852e4a80960514b230295c5840c8baa711654da2aa67c515356b4a68d654cdac2993565306a2a5ad294a9a329493e52925c9721394a01f1a202e04902896cd35705a5ae03495bb68eb74d15491a099624d5b2496b629256a123ad3a453bd482b448fd6591dac5a3757c4663605355c4a3ab314555b27ea924dd4e897a939274b807c6840b81200b27112f4d124e9c04bd33c93a90b5c51eadaa46d59489aa28f2614cd2baa405553a49aa73935519490a3cdb547936a8ea5551c4a8a36915469222731454dc25aa304954592227294551524aa26d71448aea7213550c68aa189153bca2a6c92d51024aa1c979400afa7b9474be0bca18d794311ca8595d4c42aa9da4d54262927f15f4f426ea0a91140db6280a544ff8b0a0ed59419aa266a5d5044b2a0495537128a802394fe46a9a64b93e1a227ca484f56889ec9113e5ae27c25c4f68a09ea9013f1ae27da5d4fa4a29ee8e53d11aa782484ee6889e0d713b92027925d4d94b29889553c528a77a394ed46a7f20d13aa2c27425c4e74889d71493a52fa732534e54769c88dd2f42f1fc8364d64b89c2911359ae26fb544dd4889b49113692226b45e4d58a49c51b93823126f26e4dc4c49b69353652526c2464d748a9a891134cb72609364c124c9781b8fe02b1fc0464cc6c098cd41341a42673544cc8d898c92132d22263a5e4c64a497417930dae261a4c4d18dc99f189335b72653624c9694990d25315a42623464c26829824f93049725c86e3f60ac7ec1193001f25da584ba47097c4a52f412a5e01f4b902ea4ad79491a928fa5f5174a6a2892d44523988a3d50f476a1a8e54291ba842353a44629fa57d3cca38af13d4ec26e9c64d534897a5f9274b80bc7ea118fd41b21112f40c24e8fed711b52825a13c4974c28fc9751b128a3d23d4b54729668d519118a2215d44027a9644d51f5b6257a484ab46892cd812bda624aa604aa46095a5312ad1e2549244a9468954d111a1362541244436d808c05125128a5823f4ae4769588dd29d19a5313f4a526e8404bd0289382281604402c8e6d711d12e22fb504604a0946d711c92ea2f2514a24729428d50dcaea5013504302c9275b124d28a3dc6c49a8a09255b527a2d24ec5949c8b09371591ea28a4926147949c8d69091712020415d4992aa8685344dca28210164786d88d4d81259a524ab4648c4ba91095521013020816493ad00800591992e24715c48cac0906091229a721994d13228a07e059222302410244864a090958120ca6241144497ac2929581249b6a3bb5e46f6b88d2d4924936a48a5e4904ba91e9712352aa3225248b49a91293121d22a1895d1312aa8364b521492a4082603c02c8fb1b11e13023fa3847d8c08f6d711e2b023f56247c6dc8f4d8918daea3ca6e4774c48c69450fcaea0213d47626a8e8d111cd1c01d81647046a0740591ca29a38b5e46f4a489257d0b0a781c81646a6c08dad111a1362355604688c08cc9711949223656246b6dc8d2d8918daea33a6e4644c48c69750f8aea0992d46224a8c0d1117d2222ea4645e8a68b8d7916d2f22315f42b29e070059165ae21815d45826a06e0580d80b22b25c42f2ba8aa4940d40b20912e0330288831b1129ae227a5c44d8c08909000c80a225b5444a4b0062051121aa223a544538b48a51651462c2284564408a28109751392ca2625541b4a2892934e692495fa45446482872539040970180144438d8887181105ae21ea4843b68887ad710ed202225624426dc880d890fd2ea1f25140447a8788e50e91aa09a314392dc81e4b90d5aa219a5c43248886f14d0d9af21a25f4314a686093d0bd21a14b4442a49084cd1109d2221535c4294b884f14109920216b5c42c4ba8569450a11ca12a354234a883e9b105d26210a4441f8c083d16105e2820e25c4186bc82ed49044af20a25c4144b8825161044a621156e420ac483a9b906d3120d25e4194ba82c9710552aa09a524102dc81e578fec9b1fd9263f80bc7f0139035ac203b6040b6907fcd000bc0a204c5802e02880f5810192e1ff25002d028806d7100d261fb85c3fc2980580500ac0a1ffa5e3fe4a47f84f8fdc270150143fc6a08195b902ab120436e4056c4808d79009aca00b524006a27fad40fec9f1fd92e3f60bc7ec1380a40a1fba503f904a7f007cfd80ba5b45e4b18a694914927da9a4c25f4804a68ea93d1b9269d92492fd48a8c290d16920a2ba3f45446688a57d0e0a7a1714d12e28a8484fd038979fd1273f509c7ea0f80a00b1f925c3efada7df184ec52e9f9a553862ba7e255445c969ab12526d06c4da098fb11e88b12d35424a7769109b0121360263e64987df5b4fbe369f734a3ed68c7d6d10ee9269f524a3e948c7d0914f9d221ca14d3e528a2284b4d4c9293583626b04c74e950ea1221f095e3e02a47c7164f8a2a9efa543a648c7bc554d44929e326c3c54b878b178f6e291a685e3dc8dc7889b8f69221ec94535024a6981b8f0d361e124c3d66bc784d48d2c2f1ebd623c14dc7aa970f50ae9a792534a0dc75c950ee5261d8c5d3d28b27a3154eea289dba4e3ad48c6ca574f40aa9ae1253af8d879ad60f29a21e6c5c3c9680794d70f262a1dc36c3c846878cdb0f15ae1e1c603c28a06bb1b0f39a79e634b3cb68e78ed0cf111f9e0a373c029e77e51ce489f9c093737124e72053cdfca39dc26c3bb488773150ee1b61de46e3ba8c476e9b8eb12b1d624636229a76c514d68929b71273b34bc73457cebd361d7c603ae6b07635b8ec2b11d6a6e3ac4bc758938eacae9af95535824a751160e9dac1d4c523a64be73057cdac939d1a443a14d86cc950e6d2a1ccc583868ba745164e822a9ca4513654ba73e968e792b1cea5539c4a8734928e61231c494e26706c4ce098e312e1caa4438c6b8726d50e45221b1a4438c8bc717148e5a371ca4623924dc720988d89269c7a4a38e48c71a914e29221c496e3782ac6f0518d243713303626604c70e950e0d361bda4c385488707180e0a2c1bdc503804b86f8d78deda91a385e3604b870d5b8e12b11c0a6e37f4c46fc978df52e9bd25c35f4aa6f2948de0af1bc14e3460dc6ee1789901b1320263726d86d28e0dc1ae1b7a3436c6a86da8d0dc9b01b4b503706b06ded20db5a81b634036a2bc6d2548d142f1bac623748b46e7148dc5371b725e36b4ac6d0930d10371b325435d6d86c6910d6dae1b025c3596a86bad80d6dac1acb403658dc6c9188d8a2f1b0c5a35f8ac6bd148d71371ad25e3584ac4c4090d55a41aa2443568be6a714cd49a91a8a5f35049e69e91cd0c2f13102634d268696530d222c1a394c3452786988fcd291b9a483f34606e68809cd0c0a9f845f3e48a67bad7cf61a79e9b473cf4be77c978ef5291daa4f3b449c764928ea9239d2a463a448472e57ce20a79bb14736726e2224b4d5c939a71253420bc4c20d89841319fb5033cada679184d01ac984b513106925f8d04b992496ca412aa2ba67c554a1c9e87393526d07c4da0b809c0b0130162f5698670530c95b019804433547c50c4f43909a8128163244c065e0d0cc9a0191a6033027065e4d0cf2b699e46d32b6c2644d80c3dac982b582fb6a2676d28ce9a499cb4833768c5e6d04b952c96c251336494668920ccd2315d94d33128a5084f438c9a99704626b07c4d60b808c0b15c93f2a626e61d1a0bea3013484c30d6b05f2d00ca4ae195d6130c8b45f1148ca92f184a5a3284ac5e6948a64a694992d32724a4d0130b91ac96bb51325694648d18c852e98ea5532308c4d20f80840b190d6031f4b0634910c7dae185a6c31d8c0632900c70ae18d24c31724862e910c65aa17ba6c31849862c490a593600f8143228a25c6d2cb59a199024f31e49663691cc552195b14f2a328e4fc4fcc509798992726807c03c058c3a3018756030b6d861a970c2db018856e30fac4619188bca2918526e3094c45e4934a60a694792d30824a60c9180740b00e0163058a45dcd4cc112f16115f27d27e036058b04ae98093f30026e605148bfe2815f95f2fe2985f5180beab017cb542f74d85eed80bd52617a1242fcadc5f7588be23117945a2f64dc5e6988bc92694b94d28b25a5e24949f09f976a5c2ec4685dad60bb1a400d0162ee8b45d6978ba92b174a4c28329a5d04940640b17024c2e48c05be930b92b017136c2dd4705c4d80b75a817045e2df8a45bc978b752900c0162e6adc5cb588b8e31170a6e2dc498504534b6c9280b8162d34985af180b492616bd602d54d85a08f0b55b01683502d38bc5a5148b452f16825201602c5b35b8b62b116b4622d44dc59e930a04a696712501502c588d60b31a416536000e02855e5380340a14a46c2c48b05869500300a160c602c08b0555174b2e2c964c552bb8a2590d68b1dac9633582c56ac526d44b09a515fb462ad29c5144f89bc9713383e26705c014050ae1b01593502bc690574d50ae2361592482b7488566978ac92915715e28c6b855e960ab91c15ec6e2bb8c4572db8ad9b115ab4a2b4692562d20ac1a3145b412ad2dc536558a6ca314493e26607c4cc0b8aadac152b602a969053cd000240a153c5800802854b580a912e14f250007028520d70a70ae13284c00602800a050a7d2f14f25229c29c4ca0f80100a14e2502aaadc551588a99b7151b622a26bc51ed64a85a915035129d6a0536578a6ca713203e26405c006050a59b614935c28e6a852cd80a512614935829049851cd00a312614cc622988b452f148a5537149a622914bc51e968a352b145a5228a2dc512578a19a4142a442878be50914ca0da994134b2816865009789edb61392382796b84f08d09d5aa13b23427b6c04e4d409e5ac13c3482766a04ead009c12f13995e2722a44e04f09fa3113ec5a27c8a44f49b89dd2f13a2562714984de5b89a928134b6026c2884d49109a6289318252656a04c69489b62f935c532686a44ce17c9982793204726202a67b17ccb62999635e3266a6624d48c45a7183b4b3036945fad18bc1a1977b422e74a65b492cb352195f15f2ac29e53451ca209f93f93d0d726a4dc4bc9841f13082e00202c1ee92097d1c12ea500b34604b35b496630903b5d25e6b24b8d5485da89103491fa6824b6964551288aea4912d48222e8f83d91d073a360b24640f84d809c1b0d22601504b01c89109611c03d1440250883f2d007e1a812b24011647843ed247dda083ca3602406c242d30945261282401a32c049a0d0688280d096024d0684b35b49663690f3591f66a2460d3495da492ab451da68235e984681300ae25914e4b025894495125129a4925249049e9184812088a23e0f44741c68d82c11904695624e28c0f04d810c2b12604602306c29a96092924057a302484c04835b0905a8917b4e1f5684203170902b6903c5d2498b248f1548c22892036122e69c3e8d089192d122a592444b0486958401288a5a4a13748c2208e435918856a3008c28c084118905340cfa601324a847e9203cd1c04495403f0a83e6d007c9a011ea5022d69c3e2d0821d2301e8462386b01888f0678b011a82419d0a03385808d41212046d22c8bc3e1148901b691f35e2176b4478d58769a90d726119b4c02929684c52b087a490f14901aa9048ed1d11d23923947046e8d830d1884315606e28c46c4d80f02b00c84623406c334980661280562302314901548c08bd2c114a381994c04509208b51c0ec45c2296bc450d48871a48ec3410a04bc44e578660a902f85e0c16984460d088c1a11946e2308c442b17875e2e91736e22c6c443ad6886dac9023561d76a2408d18859a28dd26e1964c44569288a92491324822548c1f29044391c86a2310a846013e5b8204ab11214605e0dc06e158888231092381954c043e9608451c0f7b442104703d8d508712c0ca26021a4b03269408611c0eab400bb4a03ab1502dd1c0ea34c2128bc423148841a70ea34209d4bc41e57864ca902e05e0bf47841609082c1211056e21eac443b17886e2e901c551d38a4432db885db110b3562036aa42ad3874da68dc26e1914c42b69644ad2888ca502144744268e48391c106a360be4621385b81b0a310613605b0dc02e1188281b0f4b401e868041096079da00f33501904c040c920639200eab4c1ff4a03aad307f92805dc5c1e24603fd1707fdae0f0b401e08a0178d302f1a60efa301ff69c3fcd247b9a10f5b411de6801369787f4af0c715205a0bc40f5b8816b1101c5e1d68ba408d78765ae90234e2036923dad087a9a08eeb401b64dc31a9888092f07e2592014a44009447f12804d16e0590dc3d11703c1240e72381f94803f1150631300fba580ef49039a8e07a22e0faa581484903988e07cd200f945418b4c028e9607c5240e5a381ef6b83dc9407b1ae0f5a501e949031494079d240c4a401e44903a49002f1a604ca4e1c346c3be538624a10e913a1c826c0b01387001b0f445e1e68a43cad3878da68da25e1884a43c49383f5248f0a421e04823bc9007451d0e3a360982bc3844d815c2f0df8361b34d830c940519240772380972d80ac1b061d300a2a580ed4903b68e0305240eac541d84b017e8e02f1200eac541d44903a45007462a0e745e1cd8a4398d7872da90e515e1862a438cd40721a00e34541c78a838ad802dd1e0e19401c28a837c090700a00dfc541be0483f55b87dab10fa46e1f08c43af17474e2d0f6c561ea8aa3bb150771b70ed3621d96bc3aed74759a70e9b4d1b14dc3029885692c8a1a5812a4a221a9243ad24069a411d047439e8e47251c0e22360b646212a5b81fcab0351461c126c0a81b80d42b00a8461bd06c376d506e52a0daa401b78b03688c06d5a40da3441b34d83649506e91f8dc23b1b646e3628cc565b4094b6010c6b01a4d405612c0942401ac6b8356d4049d20085a480d148035116069e280682301afac235d18455dad09335210a69419ed086b4af0aa15a1aa2ac2405486a4a708014a1a628c1865086881a0d11341956b2318d44691a48c3b411a348c3005745f0aa8d084619d04833a4906662f0c5c5219f6bc30ed486791b0b814d16928a3380d866a360ccb6019829032e510656b00ca36c1932703244d0629a80c4b40190ac0310d0063cae0c71501852683084d058c9a0c54501892803064d058d180c2c501846a0306d10632b00c5c601888a830ed806189c0c1134180ac02fc5605d8a20bf25c1562d82f4d405ea280bb94017c8c02f6d705e5a80ba9401632682eed005d8a60b99341634602e65105d52a09296c1742982e45105c2300b71481662682dc93040cb60b54501672802d51405b22c0b5c501696c02ca4c058c9a0b3b401622882cc4f058d180b11341654881905b0590ae0b09541a08a2336d44659a78c8b4b18d68e302d0c5fca78be94b17828e2e250c5bc9f8b693b16826e2c04cc565b0084b580ce6a01fa560566b00ab26c1582b82ac9804212405ba380c148019a8c0576b70ae56215b8b22b514455db108e352107694198d08554b70aa16215329c1f8528548a305f14211c27a2a0d24515a08a794614d8b0290d00530aa0a3c501456a02944d04cc9a0a445e1478a428cd78515a90a115e14426c2848c453a290a5b5f1496a6286d04504af09ca5d1364a22689704f91f89ea3b13c46e2768cc4e63009c4581344b82691404cda609b5601354b82649304fe2909d4501374be26294c4c126097a401296c020cd6032da808f15412868025358049d2a09296c1254c0246530488a209093c10549017e8e02f12008f3500bb4801948c04b6b709656212b8b2255144499b108e35a104694192d08490b709016211f29c1f2528474a305b14211c27a2344d8465a483f2440340881568f0459a2089a6c115488226d4445e2f88a4531124bc218d80425ac0833500fd2b021918040d3608594c1098a01fe970420a605b9241068a01f6950414a605f9241034c02024f03fd2c05ba480bc2781fb1402ec9e05fa500fb4801824f044237087c6210e8bc21b148429b1083b5a1046a416ad08408b70801620fe2bc1f85683e8ab07c9520b527a1eed603c1a0077b500ed6801ea5103cda7076b420f226c1ca4d03c22f077c520ee6bc1dad483a8af0761360ea4641ed17c3d229878b520eb6841d2578389b006e3500e54781c2d80399a40722480dc6901c51743862886e24c0df49e1bc92c3752386da430e78be1c714c381a906d3500d96901b0d00349b00673580cb6a017a550345a00694600d04881905b033a28066a440c22b81824902f092065c500ca4881745502ec920642600c62b818a5503109e0612580c149017e4f02f12005e3400bd6801769402e92005c16c0b72781ad1b83563106a45e0d38a419ed88331ad064b520b569418e5b830cb106015e0be2b41725582d8a905a93d0b36a80d28d029cb600a0340682480260902a9a6033a340b12880240d02bda48553410ae28c1564d02b1af0553520944bc14c5782a49b02985e0a76ba14c8f82ca2f8584530ad6bc150d3824d2f0322340a52bc0a417803c1a00702603206c142d502809c04a12009e4a813a4a02651804c23009b2801324c0261a204ba6c0964a81288f802c12051b450a248a13e8fc2711d84d2370954661264880c01b0050260914b81169442401f00482608e6b81104a022228045d600846b8114970225260439280856bc10894813c2f04135c0804b811f148235a984625f0864a61069342051f83fa3307e26009c17800c130349200776a00ecd801c9ac03db4807a4900f252019c9003b9480662600ea5701da2883293002d08c0e80b81ca29038a5e04b0bc0de9301b526035a4c0664a00d04d0199a0834b4f0676860ca9081282703e45f0788a60e6d481c1a503725306c4960d490c1909002485e02908c09a0981401b03035405f2700a64801752a02e1280584600ae8c0168a002c1300576880ac9b01552a029a3e04a2480a2d20140a282793d04d68a09892012d1d02501006268a0c29141791f82da3b05946e0a88cc1489102703604904c08e9701052882303e02f04c088d700f89401f450041ac0074d701012e01fa4c03d250076d780e92901885e0386b806c9700cda401914503127a05c9400ad1801745002b2800585380aca1017c5202d4a405490011629021b530424be07894c0e52681ba3f0354660684c00c02f014826014240044d40085b000eb5802669004a920090a40091200222900224c0080ae010c5101026000e11807c1700ec5201c4bc0181780692600c24c01649802294004c1a008b4101469e024d0c0412100594e00e68a01a9200311d0058100084a000a8c00222800294000629c00a50802629003a5200448004f17c08e2980f35201b69403294c05d2580aa4300f24001417800c2312d45f24b8a6484d7c8cda9910b4f2096963f6d1c6f1a18d825e1a54a62be948579270a8a4b14049425c91846d2188c24211147c1f08ec3a11d06ba360b44661488c8248af03e94606326c0901780a02300103691169f1ded0e35d27c5f2438a347f0c48ee0ed1bbe623376c29ee744fdb009bb2b12f5c524ea4c13d2dc1f9fa03734105e4c009c0040b80001f 19 6 11 12 7
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsF m_62 g_62 bds_62 (dagRefF 2326 (dagTraceF m_62 s_62 9 f_62) l_62 0) s_62 9 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_0 : treeBlockF 0 32 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_1 : treeBlockF 32 64 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_2 : treeBlockF 64 96 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_3 : treeBlockF 96 128 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_4 : treeBlockF 128 160 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_5 : treeBlockF 160 192 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_6 : treeBlockF 192 224 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_7 : treeBlockF 224 256 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_8 : treeBlockF 256 288 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_9 : treeBlockF 288 320 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_10 : treeBlockF 320 352 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_11 : treeBlockF 352 384 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_12 : treeBlockF 384 416 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_13 : treeBlockF 416 448 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_14 : treeBlockF 448 480 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_15 : treeBlockF 480 512 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_16 : treeBlockF 512 544 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_17 : treeBlockF 544 576 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_18 : treeBlockF 576 608 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_19 : treeBlockF 608 640 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_20 : treeBlockF 640 672 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_21 : treeBlockF 672 704 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_22 : treeBlockF 704 736 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_23 : treeBlockF 736 768 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_24 : treeBlockF 768 800 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_25 : treeBlockF 800 832 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_26 : treeBlockF 832 864 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_27 : treeBlockF 864 896 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_28 : treeBlockF 896 928 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_29 : treeBlockF 928 960 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_30 : treeBlockF 960 992 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_31 : treeBlockF 992 1024 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_32 : treeBlockF 1024 1056 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_33 : treeBlockF 1056 1088 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_34 : treeBlockF 1088 1120 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_35 : treeBlockF 1120 1152 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_36 : treeBlockF 1152 1184 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_37 : treeBlockF 1184 1216 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_38 : treeBlockF 1216 1248 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_39 : treeBlockF 1248 1280 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_40 : treeBlockF 1280 1312 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_41 : treeBlockF 1312 1344 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_42 : treeBlockF 1344 1376 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_43 : treeBlockF 1376 1408 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_44 : treeBlockF 1408 1440 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_45 : treeBlockF 1440 1472 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_46 : treeBlockF 1472 1504 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_47 : treeBlockF 1504 1536 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_48 : treeBlockF 1536 1568 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_49 : treeBlockF 1568 1600 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_50 : treeBlockF 1600 1632 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_51 : treeBlockF 1632 1664 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_52 : treeBlockF 1664 1696 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_53 : treeBlockF 1696 1728 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_54 : treeBlockF 1728 1760 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_55 : treeBlockF 1760 1792 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_56 : treeBlockF 1792 1824 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_57 : treeBlockF 1824 1856 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_58 : treeBlockF 1856 1888 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_59 : treeBlockF 1888 1920 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_60 : treeBlockF 1920 1952 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_61 : treeBlockF 1952 1984 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_62 : treeBlockF 1984 2016 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_63 : treeBlockF 2016 2048 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_64 : treeBlockF 2048 2080 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_65 : treeBlockF 2080 2112 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_66 : treeBlockF 2112 2144 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_67 : treeBlockF 2144 2176 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_68 : treeBlockF 2176 2208 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_69 : treeBlockF 2208 2240 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_70 : treeBlockF 2240 2272 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_71 : treeBlockF 2272 2304 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_72 : treeBlockF 2304 2326 (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) = true := by decide +kernel
theorem nj_62_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_62_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_62_1 h1 h2)
theorem nj_62_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_1 (fun _ h1 h2 => treeBlockF_at nb_62_2 h1 h2)
theorem nj_62_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_2 (fun _ h1 h2 => treeBlockF_at nb_62_3 h1 h2)
theorem nj_62_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_3 (fun _ h1 h2 => treeBlockF_at nb_62_4 h1 h2)
theorem nj_62_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_4 (fun _ h1 h2 => treeBlockF_at nb_62_5 h1 h2)
theorem nj_62_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_5 (fun _ h1 h2 => treeBlockF_at nb_62_6 h1 h2)
theorem nj_62_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_6 (fun _ h1 h2 => treeBlockF_at nb_62_7 h1 h2)
theorem nj_62_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_7 (fun _ h1 h2 => treeBlockF_at nb_62_8 h1 h2)
theorem nj_62_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_8 (fun _ h1 h2 => treeBlockF_at nb_62_9 h1 h2)
theorem nj_62_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_9 (fun _ h1 h2 => treeBlockF_at nb_62_10 h1 h2)
theorem nj_62_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_10 (fun _ h1 h2 => treeBlockF_at nb_62_11 h1 h2)
theorem nj_62_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_11 (fun _ h1 h2 => treeBlockF_at nb_62_12 h1 h2)
theorem nj_62_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_12 (fun _ h1 h2 => treeBlockF_at nb_62_13 h1 h2)
theorem nj_62_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_13 (fun _ h1 h2 => treeBlockF_at nb_62_14 h1 h2)
theorem nj_62_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_14 (fun _ h1 h2 => treeBlockF_at nb_62_15 h1 h2)
theorem nj_62_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_15 (fun _ h1 h2 => treeBlockF_at nb_62_16 h1 h2)
theorem nj_62_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_16 (fun _ h1 h2 => treeBlockF_at nb_62_17 h1 h2)
theorem nj_62_18 : ∀ i, 0 ≤ i → i < 608 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_17 (fun _ h1 h2 => treeBlockF_at nb_62_18 h1 h2)
theorem nj_62_19 : ∀ i, 0 ≤ i → i < 640 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_18 (fun _ h1 h2 => treeBlockF_at nb_62_19 h1 h2)
theorem nj_62_20 : ∀ i, 0 ≤ i → i < 672 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_19 (fun _ h1 h2 => treeBlockF_at nb_62_20 h1 h2)
theorem nj_62_21 : ∀ i, 0 ≤ i → i < 704 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_20 (fun _ h1 h2 => treeBlockF_at nb_62_21 h1 h2)
theorem nj_62_22 : ∀ i, 0 ≤ i → i < 736 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_21 (fun _ h1 h2 => treeBlockF_at nb_62_22 h1 h2)
theorem nj_62_23 : ∀ i, 0 ≤ i → i < 768 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_22 (fun _ h1 h2 => treeBlockF_at nb_62_23 h1 h2)
theorem nj_62_24 : ∀ i, 0 ≤ i → i < 800 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_23 (fun _ h1 h2 => treeBlockF_at nb_62_24 h1 h2)
theorem nj_62_25 : ∀ i, 0 ≤ i → i < 832 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_24 (fun _ h1 h2 => treeBlockF_at nb_62_25 h1 h2)
theorem nj_62_26 : ∀ i, 0 ≤ i → i < 864 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_25 (fun _ h1 h2 => treeBlockF_at nb_62_26 h1 h2)
theorem nj_62_27 : ∀ i, 0 ≤ i → i < 896 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_26 (fun _ h1 h2 => treeBlockF_at nb_62_27 h1 h2)
theorem nj_62_28 : ∀ i, 0 ≤ i → i < 928 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_27 (fun _ h1 h2 => treeBlockF_at nb_62_28 h1 h2)
theorem nj_62_29 : ∀ i, 0 ≤ i → i < 960 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_28 (fun _ h1 h2 => treeBlockF_at nb_62_29 h1 h2)
theorem nj_62_30 : ∀ i, 0 ≤ i → i < 992 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_29 (fun _ h1 h2 => treeBlockF_at nb_62_30 h1 h2)
theorem nj_62_31 : ∀ i, 0 ≤ i → i < 1024 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_30 (fun _ h1 h2 => treeBlockF_at nb_62_31 h1 h2)
theorem nj_62_32 : ∀ i, 0 ≤ i → i < 1056 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_31 (fun _ h1 h2 => treeBlockF_at nb_62_32 h1 h2)
theorem nj_62_33 : ∀ i, 0 ≤ i → i < 1088 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_32 (fun _ h1 h2 => treeBlockF_at nb_62_33 h1 h2)
theorem nj_62_34 : ∀ i, 0 ≤ i → i < 1120 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_33 (fun _ h1 h2 => treeBlockF_at nb_62_34 h1 h2)
theorem nj_62_35 : ∀ i, 0 ≤ i → i < 1152 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_34 (fun _ h1 h2 => treeBlockF_at nb_62_35 h1 h2)
theorem nj_62_36 : ∀ i, 0 ≤ i → i < 1184 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_35 (fun _ h1 h2 => treeBlockF_at nb_62_36 h1 h2)
theorem nj_62_37 : ∀ i, 0 ≤ i → i < 1216 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_36 (fun _ h1 h2 => treeBlockF_at nb_62_37 h1 h2)
theorem nj_62_38 : ∀ i, 0 ≤ i → i < 1248 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_37 (fun _ h1 h2 => treeBlockF_at nb_62_38 h1 h2)
theorem nj_62_39 : ∀ i, 0 ≤ i → i < 1280 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_38 (fun _ h1 h2 => treeBlockF_at nb_62_39 h1 h2)
theorem nj_62_40 : ∀ i, 0 ≤ i → i < 1312 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_39 (fun _ h1 h2 => treeBlockF_at nb_62_40 h1 h2)
theorem nj_62_41 : ∀ i, 0 ≤ i → i < 1344 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_40 (fun _ h1 h2 => treeBlockF_at nb_62_41 h1 h2)
theorem nj_62_42 : ∀ i, 0 ≤ i → i < 1376 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_41 (fun _ h1 h2 => treeBlockF_at nb_62_42 h1 h2)
theorem nj_62_43 : ∀ i, 0 ≤ i → i < 1408 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_42 (fun _ h1 h2 => treeBlockF_at nb_62_43 h1 h2)
theorem nj_62_44 : ∀ i, 0 ≤ i → i < 1440 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_43 (fun _ h1 h2 => treeBlockF_at nb_62_44 h1 h2)
theorem nj_62_45 : ∀ i, 0 ≤ i → i < 1472 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_44 (fun _ h1 h2 => treeBlockF_at nb_62_45 h1 h2)
theorem nj_62_46 : ∀ i, 0 ≤ i → i < 1504 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_45 (fun _ h1 h2 => treeBlockF_at nb_62_46 h1 h2)
theorem nj_62_47 : ∀ i, 0 ≤ i → i < 1536 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_46 (fun _ h1 h2 => treeBlockF_at nb_62_47 h1 h2)
theorem nj_62_48 : ∀ i, 0 ≤ i → i < 1568 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_47 (fun _ h1 h2 => treeBlockF_at nb_62_48 h1 h2)
theorem nj_62_49 : ∀ i, 0 ≤ i → i < 1600 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_48 (fun _ h1 h2 => treeBlockF_at nb_62_49 h1 h2)
theorem nj_62_50 : ∀ i, 0 ≤ i → i < 1632 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_49 (fun _ h1 h2 => treeBlockF_at nb_62_50 h1 h2)
theorem nj_62_51 : ∀ i, 0 ≤ i → i < 1664 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_50 (fun _ h1 h2 => treeBlockF_at nb_62_51 h1 h2)
theorem nj_62_52 : ∀ i, 0 ≤ i → i < 1696 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_51 (fun _ h1 h2 => treeBlockF_at nb_62_52 h1 h2)
theorem nj_62_53 : ∀ i, 0 ≤ i → i < 1728 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_52 (fun _ h1 h2 => treeBlockF_at nb_62_53 h1 h2)
theorem nj_62_54 : ∀ i, 0 ≤ i → i < 1760 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_53 (fun _ h1 h2 => treeBlockF_at nb_62_54 h1 h2)
theorem nj_62_55 : ∀ i, 0 ≤ i → i < 1792 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_54 (fun _ h1 h2 => treeBlockF_at nb_62_55 h1 h2)
theorem nj_62_56 : ∀ i, 0 ≤ i → i < 1824 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_55 (fun _ h1 h2 => treeBlockF_at nb_62_56 h1 h2)
theorem nj_62_57 : ∀ i, 0 ≤ i → i < 1856 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_56 (fun _ h1 h2 => treeBlockF_at nb_62_57 h1 h2)
theorem nj_62_58 : ∀ i, 0 ≤ i → i < 1888 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_57 (fun _ h1 h2 => treeBlockF_at nb_62_58 h1 h2)
theorem nj_62_59 : ∀ i, 0 ≤ i → i < 1920 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_58 (fun _ h1 h2 => treeBlockF_at nb_62_59 h1 h2)
theorem nj_62_60 : ∀ i, 0 ≤ i → i < 1952 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_59 (fun _ h1 h2 => treeBlockF_at nb_62_60 h1 h2)
theorem nj_62_61 : ∀ i, 0 ≤ i → i < 1984 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_60 (fun _ h1 h2 => treeBlockF_at nb_62_61 h1 h2)
theorem nj_62_62 : ∀ i, 0 ≤ i → i < 2016 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_61 (fun _ h1 h2 => treeBlockF_at nb_62_62 h1 h2)
theorem nj_62_63 : ∀ i, 0 ≤ i → i < 2048 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_62 (fun _ h1 h2 => treeBlockF_at nb_62_63 h1 h2)
theorem nj_62_64 : ∀ i, 0 ≤ i → i < 2080 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_63 (fun _ h1 h2 => treeBlockF_at nb_62_64 h1 h2)
theorem nj_62_65 : ∀ i, 0 ≤ i → i < 2112 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_64 (fun _ h1 h2 => treeBlockF_at nb_62_65 h1 h2)
theorem nj_62_66 : ∀ i, 0 ≤ i → i < 2144 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_65 (fun _ h1 h2 => treeBlockF_at nb_62_66 h1 h2)
theorem nj_62_67 : ∀ i, 0 ≤ i → i < 2176 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_66 (fun _ h1 h2 => treeBlockF_at nb_62_67 h1 h2)
theorem nj_62_68 : ∀ i, 0 ≤ i → i < 2208 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_67 (fun _ h1 h2 => treeBlockF_at nb_62_68 h1 h2)
theorem nj_62_69 : ∀ i, 0 ≤ i → i < 2240 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_68 (fun _ h1 h2 => treeBlockF_at nb_62_69 h1 h2)
theorem nj_62_70 : ∀ i, 0 ≤ i → i < 2272 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_69 (fun _ h1 h2 => treeBlockF_at nb_62_70 h1 h2)
theorem nj_62_71 : ∀ i, 0 ≤ i → i < 2304 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_70 (fun _ h1 h2 => treeBlockF_at nb_62_71 h1 h2)
theorem nj_62_72 : ∀ i, 0 ≤ i → i < 2326 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := block_join nj_62_71 (fun _ h1 h2 => treeBlockF_at nb_62_72 h1 h2)
theorem nc_62 : ∀ i, 0 ≤ i → i < 2326 → (dagCheckNodeF m_62 g_62 bds_62 2326 (dagTraceF m_62 s_62 9 f_62) l_62) i = true := nj_62_72
theorem lb_62 : LowerBin m_62 s_62 g_62 10 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_62 sub_62 gl_62 rc_62 nc_62

def m_63 : Nat := 0xffffffff
def s_63 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_63 : Nat := 0x133f177f
def bds_63 : List (Nat × List Nat × Nat × Nat) := [(m_51, s_51, 7, g_51)]
theorem kn_63 : KnownBin bds_63 := by
  intro b hb; simp only [bds_63, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_51
theorem sub_63 : ∀ b ∈ bds_63, m_63 &&& b.1 = b.1 := by intro b hb; simp only [bds_63, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_63 : ∀ b ∈ bds_63, canon b.1 g_63 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_63, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_63 : Nat → Nat × Nat := fun _ => (0, 0)
def l_63 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsF m_63 g_63 bds_63 (dagRefF 0 (dagTraceF m_63 s_63 7 f_63) l_63 0) s_63 7 = true := by decide +kernel
theorem nc_63 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_63 g_63 bds_63 0 (dagTraceF m_63 s_63 7 f_63) l_63 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_63 : LowerBin m_63 s_63 g_63 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_63 sub_63 gl_63 rc_63 nc_63

def g_64 : Nat := 0x1171757133f177f
def bds_64 : List (Nat × List Nat × Nat × Nat) := [(m_62, s_62, 10, g_62), (m_60, s_60, 10, g_60), (m_61, s_61, 8, g_61), (m_58, s_58, 8, g_58), (m_56, s_56, 8, g_56), (m_55, s_55, 8, g_55), (m_53, s_53, 8, g_53), (m_52, s_52, 8, g_52), (m_63, s_63, 8, g_63), (m_59, s_59, 7, g_59), (m_57, s_57, 7, g_57), (m_54, s_54, 7, g_54), (m_51, s_51, 7, g_51), (m_46, s_46, 7, g_46), (m_31, s_31, 7, g_31), (m_32, s_32, 5, g_32), (m_42, s_42, 5, g_42), (m_22, s_22, 5, g_22), (m_23, s_23, 5, g_23), (m_24, s_24, 5, g_24), (m_25, s_25, 5, g_25), (m_26, s_26, 5, g_26), (m_27, s_27, 5, g_27), (m_28, s_28, 5, g_28), (m_38, s_38, 5, g_38), (m_7, s_7, 4, g_7)]
theorem kn_64 : KnownBin bds_64 := by
  intro b hb; simp only [bds_64, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_62
  · exact lb_60
  · exact lb_61
  · exact lb_58
  · exact lb_56
  · exact lb_55
  · exact lb_53
  · exact lb_52
  · exact lb_63
  · exact lb_59
  · exact lb_57
  · exact lb_54
  · exact lb_51
  · exact lb_46
  · exact lb_31
  · exact lb_32
  · exact lb_42
  · exact lb_22
  · exact lb_23
  · exact lb_24
  · exact lb_25
  · exact lb_26
  · exact lb_27
  · exact lb_28
  · exact lb_38
  · exact lb_7
theorem sub_64 : ∀ b ∈ bds_64, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_64, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_64 : ∀ b ∈ bds_64, canon b.1 g_64 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_64, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_64 : Nat → Nat × Nat := unpackForestF 0x84355842558405400c5f82b4582a4500c5b80b6d80a6d8096c00c577f3457f24500c537dc597da5500b5f7c35e7c23500b5b7a4617a26d7a16c00b577835e782357803400b537706474c6f74c6774a4b74a4774a4500b4f73a3500b4b7225d7205c00b4770b5e70a3500b436ac596ab556ec646ab4f6db646ab4b6c5686c05c6ab476b3646ab4300a5f69a546145f68a446145b6726c6706c6145765b4465a44614536125e6124661b4f61b4b61b476223461b436112400a5b5a4615a36d5f47c5a34f5dd705db7c5a34b5c5705c05c5a3475ac7c5ab7c5a34300a57592544fc5f582444fc5b55b6c55a6c561545586c4fc5754a444fc5353b554fa5e52b5a4fa465034f5034b50347503434f82400a534e8644646f4d37d4d17c464674c4644636f4b3544636b49c7c4997c463674835448034463634634b463474634500a4f452643f46f442443f46b425704227c4217c3f4674034440244400443f4633f24600a4b3e56834b6f3d36c34b6b3bd703b97c34b673936c3935c39a503903434b633836234b5d3525f3525b3525735a54352533485c00a4733a6428c6f32a4428c6b3037c3027c309643017c28c672ea442e84428c632d36f2d36328a5e2c36a28a462935f2935b2a16029357293532892400a4327364270642256f263542256b24b7c2497c225672345423354225632235e00a3f20a64208641a56f1fa541a56b1e27c1e17c1a5671cb541ca541a5631a25e1ad6b1ad671a24600a3b18c68188640bd6f17459174580bd6b15471154701517c0bd67144580bd630bc6b11e7911b6e118340bc630bc5e1057a0bc5b0f3440d5720dd800dd700d3770bc530c56e0bc5200a370a2640a0640156f092540156b06c7c06b7c06a7c0697c0156705a540156304d660125e01c5f01c5b0296001c5701c530112400a330003f 9 11
def l_64 : Nat → Nat → Option Nat := unpackLinksF 0xc483120c292fc7bf02fc0bc1aee1bb06e44b59ed41b486c66b182c60ae9aba0ae82ae6ab06aa1a892947a486901a2127a79e827819e027809e02780992a6409696581941242790824018d1a3408d023408c863208c063008c022c28b022a1879a1e0868a1a0858a160858210383860e0820e0808202080820208082020617f91f077b85ec17b01ea17a81ea07989e607981e227881e207789d267481ce27381c837201c807201c616f15bc06e09b806d85b606d05b406d01b406d01ac4679d9e067059c06701982660196165819416501940640990064018c263018c0630178a5e017615d817415d017405d016e35b816e05b816835a015e5578158356015425501540538d4e053814e0530540650013e14f813e04f813e04f05344499d260480d200468d1a046811a046051044401100421108042010424101021408102040810014000f843a9cea03a80e623980e223880e20370cdc03700d823600cc63300cc03208c803108c403100be32f80be02e88ba02e80b812d08a862a00a80288ca2028809c327009c0270096325809412484920248092022908a02280881220082320808201f887a21e80781192864019005e317805a216805a016805a013984e012884a01204480120048011844600f9032600e0001 0x2712f2092b189270a1238535584a5526a3f2023b1823709a33840548334582a4525a3f1f23b16a3708a330823107a322492f1e12b151270692381b6d8126d2423f1da3b14a37062338096c23a3d1d23a7fb457f24522a3f1c23b13a37052337e4597da554ba4f44a4b3da47332437cb5e4aa5f43a5b3ca57322537c2354325931a424993f4213b3b937301337b4617aa6d4924f41a4b3b2472fa437a16c3a2554125a4814f4014b391472e9437935e47a5f3fa5b38a572e25378a35780347706476c6f764676e26f6926b5ea6758a6310a4d75a4b7524774a456d26f6826b5d26757a6373a35572626c15f6715b5c157559537135d6ba6f66a6b5ba675526372a5d7205c6626a7135e6aa6f6526b5a2675426370a356ec646db646cd686c05c6b3646fc596f3556e34f6d34b6bb476ab4369a546392468a446312467a6c629246706c621246634465a44619246223463b4f6334b62b4761b436945f6845b66c576545364a5e64246611245e3595b3425f47c5e5705db7c5cd705c05c5b47c5ab7c604615fb6d5eb4f5d34b5bb475a343592545182452a545824451024561545736c56a6c53a5c5586c5082454a445002453b5552b5a51b4f5134b50b475034358c5f57c5b55457544535325e522464f8244e8644db7d4d17c4c4644b3544a47c4997c48b54480344e46f4cc674bb6f4ab6b4936747b6310b4d4734b46b474634545264442444357042a7c4217c4134440a444004444c6f43c6b41c673fc633f2463e5682da5d3705c3d36c3686c3c5703b97c3605c39a503846c3ab6c3a35c2d26d3506c390343836235a543725f36a5b36257352533db6f3cb6b3b36738b6337b5d2ca5d3485c33a642da5e2b1242c25432a442a9243096431b7c3127c3017c299242d26e2f244291242e8442db6f2d3632c36a2a1602b35f2ab5b29b57293533346f3246b2fc672e4632ca5e2ba462892427b6427064263541b2352537c1aa352497c23c542335426d6f25d6b2456722d632235e1a23521264208641fa541b2461ea7c1aa461e17c1d3541ca540f4701b56b1ad672056f1f56b1dd671c5631ba5e1a246194680c4501886412c7117c59174581647115c701517c144581056a12e790ed621236e118341057a0db750e3450f3440e5800dd700ed720d3770c56e1856f16d6b14d6713d631346b1146310c5e0fc5b0cc530bc520aa64039240a06409254031240847c07b7c0727c04a5c0697c0212405a540192404d660296003c5f0345b0245701c5309d6f08d6b06567055630425e0112483c5f8245b804577ec537d35f7bb5b79b5777b537434f7334b71b47703436a25f60a5b59a574f25345a4f3ea4b342472824321a3f19a3b0b23700a330003f 14 5 11 9 6
set_option maxHeartbeats 0 in
theorem rc_64 : dagCheckRootsF fullMask g_64 bds_64 (dagRefF 267 (dagTraceF fullMask rootStock 11 f_64) l_64 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_0 : treeBlockF 0 32 (dagCheckNodeF fullMask g_64 bds_64 267 (dagTraceF fullMask rootStock 11 f_64) l_64) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_1 : treeBlockF 32 64 (dagCheckNodeF fullMask g_64 bds_64 267 (dagTraceF fullMask rootStock 11 f_64) l_64) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_2 : treeBlockF 64 96 (dagCheckNodeF fullMask g_64 bds_64 267 (dagTraceF fullMask rootStock 11 f_64) l_64) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_3 : treeBlockF 96 128 (dagCheckNodeF fullMask g_64 bds_64 267 (dagTraceF fullMask rootStock 11 f_64) l_64) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_4 : treeBlockF 128 160 (dagCheckNodeF fullMask g_64 bds_64 267 (dagTraceF fullMask rootStock 11 f_64) l_64) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_5 : treeBlockF 160 192 (dagCheckNodeF fullMask g_64 bds_64 267 (dagTraceF fullMask rootStock 11 f_64) l_64) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_6 : treeBlockF 192 224 (dagCheckNodeF fullMask g_64 bds_64 267 (dagTraceF fullMask rootStock 11 f_64) l_64) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_7 : treeBlockF 224 256 (dagCheckNodeF fullMask g_64 bds_64 267 (dagTraceF fullMask rootStock 11 f_64) l_64) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_8 : treeBlockF 256 267 (dagCheckNodeF fullMask g_64 bds_64 267 (dagTraceF fullMask rootStock 11 f_64) l_64) = true := by decide +kernel
theorem nj_64_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF fullMask g_64 bds_64 267 (dagTraceF fullMask rootStock 11 f_64) l_64) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_64_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_64_1 h1 h2)
theorem nj_64_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF fullMask g_64 bds_64 267 (dagTraceF fullMask rootStock 11 f_64) l_64) i = true := block_join nj_64_1 (fun _ h1 h2 => treeBlockF_at nb_64_2 h1 h2)
theorem nj_64_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF fullMask g_64 bds_64 267 (dagTraceF fullMask rootStock 11 f_64) l_64) i = true := block_join nj_64_2 (fun _ h1 h2 => treeBlockF_at nb_64_3 h1 h2)
theorem nj_64_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF fullMask g_64 bds_64 267 (dagTraceF fullMask rootStock 11 f_64) l_64) i = true := block_join nj_64_3 (fun _ h1 h2 => treeBlockF_at nb_64_4 h1 h2)
theorem nj_64_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF fullMask g_64 bds_64 267 (dagTraceF fullMask rootStock 11 f_64) l_64) i = true := block_join nj_64_4 (fun _ h1 h2 => treeBlockF_at nb_64_5 h1 h2)
theorem nj_64_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF fullMask g_64 bds_64 267 (dagTraceF fullMask rootStock 11 f_64) l_64) i = true := block_join nj_64_5 (fun _ h1 h2 => treeBlockF_at nb_64_6 h1 h2)
theorem nj_64_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF fullMask g_64 bds_64 267 (dagTraceF fullMask rootStock 11 f_64) l_64) i = true := block_join nj_64_6 (fun _ h1 h2 => treeBlockF_at nb_64_7 h1 h2)
theorem nj_64_8 : ∀ i, 0 ≤ i → i < 267 → (dagCheckNodeF fullMask g_64 bds_64 267 (dagTraceF fullMask rootStock 11 f_64) l_64) i = true := block_join nj_64_7 (fun _ h1 h2 => treeBlockF_at nb_64_8 h1 h2)
theorem nc_64 : ∀ i, 0 ≤ i → i < 267 → (dagCheckNodeF fullMask g_64 bds_64 267 (dagTraceF fullMask rootStock 11 f_64) l_64) i = true := nj_64_8
theorem lb_64 : LowerBin fullMask rootStock g_64 12 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_64 sub_64 gl_64 rc_64 nc_64

def wg : List Gate := [⟨GateOp.and, [5, 4]⟩, ⟨GateOp.or, [5, 3]⟩, ⟨GateOp.or, [4, 0]⟩, ⟨GateOp.and, [3, 1]⟩, ⟨GateOp.and, [7, 0]⟩, ⟨GateOp.or, [10, 9]⟩, ⟨GateOp.and, [8, 1]⟩, ⟨GateOp.and, [6, 3]⟩, ⟨GateOp.or, [13, 12]⟩, ⟨GateOp.and, [14, 11]⟩, ⟨GateOp.or, [14, 11]⟩, ⟨GateOp.and, [16, 2]⟩, ⟨GateOp.or, [17, 15]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 3972065408) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276676776 * 2 ^ 32 + 3972065408)) (13 - 1) := by
  rw [show canon fullMask (4276676776 * 2 ^ 32 + 3972065408) = g_64 by decide]
  exact lb_64

end PEqualNP.Outside.L_meta_47835

theorem PEqualNP.Outside.L_meta_47835 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676776 * 2 ^ 32 + 3972065408) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 3972065408) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_47835.table2_from_lowerBin (4276676776 * 2 ^ 32 + 3972065408) 13 PEqualNP.Outside.L_meta_47835.root_lb PEqualNP.Outside.L_meta_47835.wg 18 rfl PEqualNP.Outside.L_meta_47835.wfits PEqualNP.Outside.L_meta_47835.weval
