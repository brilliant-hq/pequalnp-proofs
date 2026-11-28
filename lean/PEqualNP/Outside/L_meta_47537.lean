import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47537

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

def m_0 : Nat := 0x4400440044004400
def s_0 : List Nat := [0x400040004000400, 0x440000004400, 0x44004400]
def g_0 : Nat := 0x40004004400
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

def m_1 : Nat := 0x222200002222
def s_1 : List Nat := [0x20200000202, 0x2200000022, 0x2222]
def g_1 : Nat := 0x200000222
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

def m_2 : Nat := 0xc0c00000c0c0000
def s_2 : List Nat := [0x404000004040000, 0xc0000000c0000, 0xc0c0000]
def g_2 : Nat := 0x40000040c0000
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

def m_3 : Nat := 0xf0000000f0
def s_3 : List Nat := [0x5000000050, 0x3000000030, 0xf0]
def g_3 : Nat := 0x1000000070
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

def m_4 : Nat := 0x22222222
def s_4 : List Nat := [0x2020202, 0x220022, 0x2222]
def g_4 : Nat := 0x20222
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

def m_5 : Nat := 0xc0c0c0c00000000
def s_5 : List Nat := [0x404040400000000, 0xc000c00000000, 0xc0c00000000]
def g_5 : Nat := 0x4040c00000000
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

def m_6 : Nat := 0xf000f0
def s_6 : List Nat := [0x500050, 0x300030, 0xf0]
def g_6 : Nat := 0x100070
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

def m_7 : Nat := 0xaaaa
def s_7 : List Nat := [0x2222, 0xa0a, 0xaa]
def g_7 : Nat := 0x22a
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

def m_8 : Nat := 0xf0f000000000000
def s_8 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_8 : Nat := 0x107000000000000
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

def m_9 : Nat := 0xff000000000000
def s_9 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_9 : Nat := 0x17000000000000
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

def m_10 : Nat := 0x4444444444444444
def s_10 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_10 : Nat := 0x4040404044444
def bds_10 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_10 : KnownBin bds_10 := by
  intro b hb; simp only [bds_10, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_10 : ∀ b ∈ bds_10, m_10 &&& b.1 = b.1 := by intro b hb; simp only [bds_10, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_10 : ∀ b ∈ bds_10, canon b.1 g_10 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_10, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_10 : Nat → Nat × Nat := fun _ => (0, 0)
def l_10 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_10 : dagCheckRootsF m_10 g_10 bds_10 (dagRefF 0 (dagTraceF m_10 s_10 4 f_10) l_10 0) s_10 4 = true := by decide +kernel
theorem nc_10 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_10 g_10 bds_10 0 (dagTraceF m_10 s_10 4 f_10) l_10 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_10 : LowerBin m_10 s_10 g_10 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_10 sub_10 gl_10 rc_10 nc_10

def m_11 : Nat := 0x2222222222222222
def s_11 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_11 : Nat := 0x2000200020222
def bds_11 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_11 : KnownBin bds_11 := by
  intro b hb; simp only [bds_11, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_11 : ∀ b ∈ bds_11, m_11 &&& b.1 = b.1 := by intro b hb; simp only [bds_11, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_11 : ∀ b ∈ bds_11, canon b.1 g_11 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_11, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_11 : Nat → Nat × Nat := fun _ => (0, 0)
def l_11 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_11 : dagCheckRootsF m_11 g_11 bds_11 (dagRefF 0 (dagTraceF m_11 s_11 4 f_11) l_11 0) s_11 4 = true := by decide +kernel
theorem nc_11 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_11 g_11 bds_11 0 (dagTraceF m_11 s_11 4 f_11) l_11 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_11 : LowerBin m_11 s_11 g_11 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_11 sub_11 gl_11 rc_11 nc_11

def m_12 : Nat := 0xa0a0a0a0a0a0a0a
def s_12 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_12 : Nat := 0x2000a000a020a
def bds_12 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_12 : KnownBin bds_12 := by intro b hb; simp [bds_12] at hb
theorem sub_12 : ∀ b ∈ bds_12, m_12 &&& b.1 = b.1 := by intro b hb; simp [bds_12] at hb
theorem gl_12 : ∀ b ∈ bds_12, canon b.1 g_12 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_12] at hb
def f_12 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
def l_12 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607227207206e26c16c06a16a06a06a06a06a06a06246206206206205a45a05a05625605605225015004e14e04e04e04e04e04e04644604604604603e43e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_12 : dagCheckRootsF m_12 g_12 bds_12 (dagRefF 64 (dagTraceF m_12 s_12 5 f_12) l_12 0) s_12 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_12_0 : treeBlockF 0 32 (dagCheckNodeF m_12 g_12 bds_12 64 (dagTraceF m_12 s_12 5 f_12) l_12) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_12_1 : treeBlockF 32 64 (dagCheckNodeF m_12 g_12 bds_12 64 (dagTraceF m_12 s_12 5 f_12) l_12) = true := by decide +kernel
theorem nj_12_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_12 g_12 bds_12 64 (dagTraceF m_12 s_12 5 f_12) l_12) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_12_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_12_1 h1 h2)
theorem nc_12 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_12 g_12 bds_12 64 (dagTraceF m_12 s_12 5 f_12) l_12) i = true := nj_12_1
theorem lb_12 : LowerBin m_12 s_12 g_12 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_12 sub_12 gl_12 rc_12 nc_12

def m_13 : Nat := 0xc0c0c0c0c0c0c0c
def s_13 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_13 : Nat := 0x4040c040c040c
def bds_13 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_13 : KnownBin bds_13 := by
  intro b hb; simp only [bds_13, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_13 : ∀ b ∈ bds_13, m_13 &&& b.1 = b.1 := by intro b hb; simp only [bds_13, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_13 : ∀ b ∈ bds_13, canon b.1 g_13 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_13, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_13 : Nat → Nat × Nat := fun _ => (0, 0)
def l_13 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_13 : dagCheckRootsF m_13 g_13 bds_13 (dagRefF 0 (dagTraceF m_13 s_13 4 f_13) l_13 0) s_13 4 = true := by decide +kernel
theorem nc_13 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_13 g_13 bds_13 0 (dagTraceF m_13 s_13 4 f_13) l_13 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_13 : LowerBin m_13 s_13 g_13 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_13 sub_13 gl_13 rc_13 nc_13

def m_14 : Nat := 0x5500550055005500
def s_14 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_14 : Nat := 0x1100150015005500
def bds_14 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_14 : KnownBin bds_14 := by
  intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_14 : ∀ b ∈ bds_14, m_14 &&& b.1 = b.1 := by intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_14 : ∀ b ∈ bds_14, canon b.1 g_14 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_14 : Nat → Nat × Nat := fun _ => (0, 0)
def l_14 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_14 : dagCheckRootsF m_14 g_14 bds_14 (dagRefF 0 (dagTraceF m_14 s_14 4 f_14) l_14 0) s_14 4 = true := by decide +kernel
theorem nc_14 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_14 g_14 bds_14 0 (dagTraceF m_14 s_14 4 f_14) l_14 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_14 : LowerBin m_14 s_14 g_14 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_14 sub_14 gl_14 rc_14 nc_14

def m_15 : Nat := 0xaa00aa00aa00aa
def s_15 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_15 : Nat := 0x2000a000a002a
def bds_15 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_15 : KnownBin bds_15 := by intro b hb; simp [bds_15] at hb
theorem sub_15 : ∀ b ∈ bds_15, m_15 &&& b.1 = b.1 := by intro b hb; simp [bds_15] at hb
theorem gl_15 : ∀ b ∈ bds_15, canon b.1 g_15 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_15] at hb
def f_15 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
def l_15 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607227207206e26c16c06a16a06a06a06a06a06a06246206206206205a45a05a05625605605225015004e14e04e04e04e04e04e04644604604604603e43e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsF m_15 g_15 bds_15 (dagRefF 64 (dagTraceF m_15 s_15 5 f_15) l_15 0) s_15 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_15_0 : treeBlockF 0 32 (dagCheckNodeF m_15 g_15 bds_15 64 (dagTraceF m_15 s_15 5 f_15) l_15) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_15_1 : treeBlockF 32 64 (dagCheckNodeF m_15 g_15 bds_15 64 (dagTraceF m_15 s_15 5 f_15) l_15) = true := by decide +kernel
theorem nj_15_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_15 g_15 bds_15 64 (dagTraceF m_15 s_15 5 f_15) l_15) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_15_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_15_1 h1 h2)
theorem nc_15 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_15 g_15 bds_15 64 (dagTraceF m_15 s_15 5 f_15) l_15) i = true := nj_15_1
theorem lb_15 : LowerBin m_15 s_15 g_15 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_15 sub_15 gl_15 rc_15 nc_15

def m_16 : Nat := 0xcc00cc00cc00cc00
def s_16 : List Nat := [0x4400440044004400, 0xc000c000c000c00, 0xcc000000cc00, 0xcc00cc00]
def g_16 : Nat := 0x40004004400
def bds_16 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_16 : KnownBin bds_16 := by
  intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_16 : ∀ b ∈ bds_16, m_16 &&& b.1 = b.1 := by intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_16 : ∀ b ∈ bds_16, canon b.1 g_16 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_16 : Nat → Nat × Nat := fun _ => (0, 0)
def l_16 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsF m_16 g_16 bds_16 (dagRefF 0 (dagTraceF m_16 s_16 4 f_16) l_16 0) s_16 4 = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_16 g_16 bds_16 0 (dagTraceF m_16 s_16 4 f_16) l_16 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_16 : LowerBin m_16 s_16 g_16 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_16 sub_16 gl_16 rc_16 nc_16

def m_17 : Nat := 0xcc00cc00cc00cc
def s_17 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_17 : Nat := 0x4000c000c004c
def bds_17 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_17 : KnownBin bds_17 := by intro b hb; simp [bds_17] at hb
theorem sub_17 : ∀ b ∈ bds_17, m_17 &&& b.1 = b.1 := by intro b hb; simp [bds_17] at hb
theorem gl_17 : ∀ b ∈ bds_17, canon b.1 g_17 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_17] at hb
def f_17 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
def l_17 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607227207206e26c16c06a16a06a06a06a06a06a06246206206206205a45a05a05625605605225015004e14e04e04e04e04e04e04644604604604603e43e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsF m_17 g_17 bds_17 (dagRefF 64 (dagTraceF m_17 s_17 5 f_17) l_17 0) s_17 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17_0 : treeBlockF 0 32 (dagCheckNodeF m_17 g_17 bds_17 64 (dagTraceF m_17 s_17 5 f_17) l_17) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17_1 : treeBlockF 32 64 (dagCheckNodeF m_17 g_17 bds_17 64 (dagTraceF m_17 s_17 5 f_17) l_17) = true := by decide +kernel
theorem nj_17_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_17 g_17 bds_17 64 (dagTraceF m_17 s_17 5 f_17) l_17) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_17_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_17_1 h1 h2)
theorem nc_17 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_17 g_17 bds_17 64 (dagTraceF m_17 s_17 5 f_17) l_17) i = true := nj_17_1
theorem lb_17 : LowerBin m_17 s_17 g_17 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_17 sub_17 gl_17 rc_17 nc_17

def m_18 : Nat := 0xf000f000f000f00
def s_18 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_18 : Nat := 0x100050005000700
def bds_18 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_18 : KnownBin bds_18 := by intro b hb; simp [bds_18] at hb
theorem sub_18 : ∀ b ∈ bds_18, m_18 &&& b.1 = b.1 := by intro b hb; simp [bds_18] at hb
theorem gl_18 : ∀ b ∈ bds_18, canon b.1 g_18 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_18] at hb
def f_18 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_18 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsF m_18 g_18 bds_18 (dagRefF 64 (dagTraceF m_18 s_18 5 f_18) l_18 0) s_18 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18_0 : treeBlockF 0 32 (dagCheckNodeF m_18 g_18 bds_18 64 (dagTraceF m_18 s_18 5 f_18) l_18) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18_1 : treeBlockF 32 64 (dagCheckNodeF m_18 g_18 bds_18 64 (dagTraceF m_18 s_18 5 f_18) l_18) = true := by decide +kernel
theorem nj_18_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_18 g_18 bds_18 64 (dagTraceF m_18 s_18 5 f_18) l_18) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_18_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_18_1 h1 h2)
theorem nc_18 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_18 g_18 bds_18 64 (dagTraceF m_18 s_18 5 f_18) l_18) i = true := nj_18_1
theorem lb_18 : LowerBin m_18 s_18 g_18 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_18 sub_18 gl_18 rc_18 nc_18

def m_19 : Nat := 0xf000f000f000f0
def s_19 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_19 : Nat := 0x10001000100070
def bds_19 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_19 : KnownBin bds_19 := by
  intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_19 : ∀ b ∈ bds_19, m_19 &&& b.1 = b.1 := by intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_19 : ∀ b ∈ bds_19, canon b.1 g_19 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_19 : Nat → Nat × Nat := fun _ => (0, 0)
def l_19 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsF m_19 g_19 bds_19 (dagRefF 0 (dagTraceF m_19 s_19 4 f_19) l_19 0) s_19 4 = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_19 g_19 bds_19 0 (dagTraceF m_19 s_19 4 f_19) l_19 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_19 : LowerBin m_19 s_19 g_19 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_19 sub_19 gl_19 rc_19 nc_19

def m_20 : Nat := 0xaaaa0000aaaa
def s_20 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_20 : Nat := 0xa0000022a
def bds_20 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_20 : KnownBin bds_20 := by
  intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_20 : ∀ b ∈ bds_20, m_20 &&& b.1 = b.1 := by intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_20 : ∀ b ∈ bds_20, canon b.1 g_20 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_20 : Nat → Nat × Nat := fun _ => (0, 0)
def l_20 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsF m_20 g_20 bds_20 (dagRefF 0 (dagTraceF m_20 s_20 4 f_20) l_20 0) s_20 4 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_20 g_20 bds_20 0 (dagTraceF m_20 s_20 4 f_20) l_20 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_20 : LowerBin m_20 s_20 g_20 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_20 sub_20 gl_20 rc_20 nc_20

def m_21 : Nat := 0xcccc0000cccc0000
def s_21 : List Nat := [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000]
def g_21 : Nat := 0x40000040c0000
def bds_21 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_21 : KnownBin bds_21 := by
  intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_21 : ∀ b ∈ bds_21, m_21 &&& b.1 = b.1 := by intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_21 : ∀ b ∈ bds_21, canon b.1 g_21 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_21 : Nat → Nat × Nat := fun _ => (0, 0)
def l_21 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsF m_21 g_21 bds_21 (dagRefF 0 (dagTraceF m_21 s_21 4 f_21) l_21 0) s_21 4 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_21 g_21 bds_21 0 (dagTraceF m_21 s_21 4 f_21) l_21 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_21 : LowerBin m_21 s_21 g_21 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_21 sub_21 gl_21 rc_21 nc_21

def m_22 : Nat := 0x333300003333
def s_22 : List Nat := [0x111100001111, 0x30300000303, 0x3300000033, 0x3333]
def g_22 : Nat := 0x111300001333
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_22 : KnownBin bds_22 := by
  intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_22 : ∀ b ∈ bds_22, m_22 &&& b.1 = b.1 := by intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_22 : ∀ b ∈ bds_22, canon b.1 g_22 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_22 : Nat → Nat × Nat := fun _ => (0, 0)
def l_22 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsF m_22 g_22 bds_22 (dagRefF 0 (dagTraceF m_22 s_22 4 f_22) l_22 0) s_22 4 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_22 g_22 bds_22 0 (dagTraceF m_22 s_22 4 f_22) l_22 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_22 : LowerBin m_22 s_22 g_22 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_22 sub_22 gl_22 rc_22 nc_22

def m_23 : Nat := 0xf0f00000f0f0000
def s_23 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_23 : Nat := 0x1070000050f0000
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_23 : KnownBin bds_23 := by
  intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_23 : ∀ b ∈ bds_23, m_23 &&& b.1 = b.1 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_23 : ∀ b ∈ bds_23, canon b.1 g_23 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_23 : Nat → Nat × Nat := fun _ => (0, 0)
def l_23 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsF m_23 g_23 bds_23 (dagRefF 0 (dagTraceF m_23 s_23 4 f_23) l_23 0) s_23 4 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_23 g_23 bds_23 0 (dagTraceF m_23 s_23 4 f_23) l_23 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_23 sub_23 gl_23 rc_23 nc_23

def m_24 : Nat := 0xf0f00000f0f0
def s_24 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_24 : Nat := 0x101000005070
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_24 : KnownBin bds_24 := by
  intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_24 : ∀ b ∈ bds_24, m_24 &&& b.1 = b.1 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_24 : ∀ b ∈ bds_24, canon b.1 g_24 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
def l_24 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsF m_24 g_24 bds_24 (dagRefF 0 (dagTraceF m_24 s_24 4 f_24) l_24 0) s_24 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_24 g_24 bds_24 0 (dagTraceF m_24 s_24 4 f_24) l_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_24 sub_24 gl_24 rc_24 nc_24

def m_25 : Nat := 0xff000000ff0000
def s_25 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_25 : Nat := 0x170000001f0000
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_25 : KnownBin bds_25 := by
  intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_25 : ∀ b ∈ bds_25, m_25 &&& b.1 = b.1 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_25 : ∀ b ∈ bds_25, canon b.1 g_25 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
def l_25 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsF m_25 g_25 bds_25 (dagRefF 0 (dagTraceF m_25 s_25 4 f_25) l_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_25 g_25 bds_25 0 (dagTraceF m_25 s_25 4 f_25) l_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_25 sub_25 gl_25 rc_25 nc_25

def m_26 : Nat := 0xff000000ff00
def s_26 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_26 : Nat := 0x150000005700
def bds_26 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_26 : KnownBin bds_26 := by intro b hb; simp [bds_26] at hb
theorem sub_26 : ∀ b ∈ bds_26, m_26 &&& b.1 = b.1 := by intro b hb; simp [bds_26] at hb
theorem gl_26 : ∀ b ∈ bds_26, canon b.1 g_26 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_26] at hb
def f_26 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_26 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsF m_26 g_26 bds_26 (dagRefF 64 (dagTraceF m_26 s_26 5 f_26) l_26 0) s_26 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26_0 : treeBlockF 0 32 (dagCheckNodeF m_26 g_26 bds_26 64 (dagTraceF m_26 s_26 5 f_26) l_26) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26_1 : treeBlockF 32 64 (dagCheckNodeF m_26 g_26 bds_26 64 (dagTraceF m_26 s_26 5 f_26) l_26) = true := by decide +kernel
theorem nj_26_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_26 g_26 bds_26 64 (dagTraceF m_26 s_26 5 f_26) l_26) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_26_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_26_1 h1 h2)
theorem nc_26 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_26 g_26 bds_26 64 (dagTraceF m_26 s_26 5 f_26) l_26) i = true := nj_26_1
theorem lb_26 : LowerBin m_26 s_26 g_26 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_26 sub_26 gl_26 rc_26 nc_26

def m_27 : Nat := 0xff000000ff
def s_27 : List Nat := [0x5500000055, 0x3300000033, 0xf0000000f, 0xff]
def g_27 : Nat := 0x1f0000007f
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_27 : KnownBin bds_27 := by
  intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_27 : ∀ b ∈ bds_27, m_27 &&& b.1 = b.1 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
def l_27 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsF m_27 g_27 bds_27 (dagRefF 0 (dagTraceF m_27 s_27 4 f_27) l_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_27 g_27 bds_27 0 (dagTraceF m_27 s_27 4 f_27) l_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0xaaaaaaaa
def s_28 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_28 : Nat := 0xa022a
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_28 : KnownBin bds_28 := by
  intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_28 : ∀ b ∈ bds_28, m_28 &&& b.1 = b.1 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_28 : Nat → Nat × Nat := fun _ => (0, 0)
def l_28 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsF m_28 g_28 bds_28 (dagRefF 0 (dagTraceF m_28 s_28 4 f_28) l_28 0) s_28 4 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_28 g_28 bds_28 0 (dagTraceF m_28 s_28 4 f_28) l_28 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_28 sub_28 gl_28 rc_28 nc_28

def m_29 : Nat := 0xcccccccc00000000
def s_29 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_29 : Nat := 0x4040c00000000
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_29 : KnownBin bds_29 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_29 : ∀ b ∈ bds_29, m_29 &&& b.1 = b.1 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_29 : ∀ b ∈ bds_29, canon b.1 g_29 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_29 : Nat → Nat × Nat := fun _ => (0, 0)
def l_29 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsF m_29 g_29 bds_29 (dagRefF 0 (dagTraceF m_29 s_29 4 f_29) l_29 0) s_29 4 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_29 g_29 bds_29 0 (dagTraceF m_29 s_29 4 f_29) l_29 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_29 sub_29 gl_29 rc_29 nc_29

def m_30 : Nat := 0x33333333
def s_30 : List Nat := [0x11111111, 0x3030303, 0x330033, 0x3333]
def g_30 : Nat := 0x11131333
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_30 : KnownBin bds_30 := by
  intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_30 : ∀ b ∈ bds_30, m_30 &&& b.1 = b.1 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_30 : Nat → Nat × Nat := fun _ => (0, 0)
def l_30 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsF m_30 g_30 bds_30 (dagRefF 0 (dagTraceF m_30 s_30 4 f_30) l_30 0) s_30 4 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_30 g_30 bds_30 0 (dagTraceF m_30 s_30 4 f_30) l_30 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_30 sub_30 gl_30 rc_30 nc_30

def m_31 : Nat := 0xf0f0f0f00000000
def s_31 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_31 : Nat := 0x107050f00000000
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_31 : KnownBin bds_31 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_31 : ∀ b ∈ bds_31, m_31 &&& b.1 = b.1 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
def l_31 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsF m_31 g_31 bds_31 (dagRefF 0 (dagTraceF m_31 s_31 4 f_31) l_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_31 g_31 bds_31 0 (dagTraceF m_31 s_31 4 f_31) l_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_31 sub_31 gl_31 rc_31 nc_31

def m_32 : Nat := 0xf0f0f0f0
def s_32 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_32 : Nat := 0x10105070
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_32 : KnownBin bds_32 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_32 : ∀ b ∈ bds_32, m_32 &&& b.1 = b.1 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_32 : ∀ b ∈ bds_32, canon b.1 g_32 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_32 : Nat → Nat × Nat := fun _ => (0, 0)
def l_32 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsF m_32 g_32 bds_32 (dagRefF 0 (dagTraceF m_32 s_32 4 f_32) l_32 0) s_32 4 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_32 g_32 bds_32 0 (dagTraceF m_32 s_32 4 f_32) l_32 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_32 sub_32 gl_32 rc_32 nc_32

def m_33 : Nat := 0xff00ff00000000
def s_33 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_33 : Nat := 0x17001f00000000
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_33 : ∀ b ∈ bds_33, m_33 &&& b.1 = b.1 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
def l_33 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsF m_33 g_33 bds_33 (dagRefF 0 (dagTraceF m_33 s_33 4 f_33) l_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_33 g_33 bds_33 0 (dagTraceF m_33 s_33 4 f_33) l_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_33 sub_33 gl_33 rc_33 nc_33

def m_34 : Nat := 0xff00ff00
def s_34 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_34 : Nat := 0x15005700
def bds_34 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_34 : KnownBin bds_34 := by intro b hb; simp [bds_34] at hb
theorem sub_34 : ∀ b ∈ bds_34, m_34 &&& b.1 = b.1 := by intro b hb; simp [bds_34] at hb
theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_34] at hb
def f_34 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_34 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsF m_34 g_34 bds_34 (dagRefF 64 (dagTraceF m_34 s_34 5 f_34) l_34 0) s_34 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_0 : treeBlockF 0 32 (dagCheckNodeF m_34 g_34 bds_34 64 (dagTraceF m_34 s_34 5 f_34) l_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_1 : treeBlockF 32 64 (dagCheckNodeF m_34 g_34 bds_34 64 (dagTraceF m_34 s_34 5 f_34) l_34) = true := by decide +kernel
theorem nj_34_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_34 g_34 bds_34 64 (dagTraceF m_34 s_34 5 f_34) l_34) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_34_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_34_1 h1 h2)
theorem nc_34 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_34 g_34 bds_34 64 (dagTraceF m_34 s_34 5 f_34) l_34) i = true := nj_34_1
theorem lb_34 : LowerBin m_34 s_34 g_34 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_34 sub_34 gl_34 rc_34 nc_34

def m_35 : Nat := 0xff00ff
def s_35 : List Nat := [0x550055, 0x330033, 0xf000f, 0xff]
def g_35 : Nat := 0x1f007f
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_35 : KnownBin bds_35 := by
  intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_35 : ∀ b ∈ bds_35, m_35 &&& b.1 = b.1 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
def l_35 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsF m_35 g_35 bds_35 (dagRefF 0 (dagTraceF m_35 s_35 4 f_35) l_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_35 g_35 bds_35 0 (dagTraceF m_35 s_35 4 f_35) l_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_35 sub_35 gl_35 rc_35 nc_35

def m_36 : Nat := 0xffff000000000000
def s_36 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_36 : Nat := 0x1117000000000000
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_36 : KnownBin bds_36 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_36 : ∀ b ∈ bds_36, m_36 &&& b.1 = b.1 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_36 : ∀ b ∈ bds_36, canon b.1 g_36 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
def l_36 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsF m_36 g_36 bds_36 (dagRefF 0 (dagTraceF m_36 s_36 4 f_36) l_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_36 g_36 bds_36 0 (dagTraceF m_36 s_36 4 f_36) l_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_36 sub_36 gl_36 rc_36 nc_36

def m_37 : Nat := 0xffff
def s_37 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_37 : Nat := 0x577f
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_37 : KnownBin bds_37 := by
  intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
theorem sub_37 : ∀ b ∈ bds_37, m_37 &&& b.1 = b.1 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_37 : ∀ b ∈ bds_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
def l_37 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsF m_37 g_37 bds_37 (dagRefF 0 (dagTraceF m_37 s_37 4 f_37) l_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_37 g_37 bds_37 0 (dagTraceF m_37 s_37 4 f_37) l_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_37 sub_37 gl_37 rc_37 nc_37

def m_38 : Nat := 0xaaaaaaaaaaaaaaaa
def s_38 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_38 : Nat := 0x2000a000a022a
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 6, g_12), (m_15, s_15, 6, g_15), (m_11, s_11, 5, g_11), (m_20, s_20, 5, g_20), (m_28, s_28, 5, g_28), (m_1, s_1, 4, g_1), (m_4, s_4, 4, g_4), (m_7, s_7, 4, g_7)]
theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_12
  · exact lb_15
  · exact lb_11
  · exact lb_20
  · exact lb_28
  · exact lb_1
  · exact lb_4
  · exact lb_7
theorem sub_38 : ∀ b ∈ bds_38, m_38 &&& b.1 = b.1 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_38 : Nat → Nat × Nat := unpackForestF 0x38947200b4bdd11df0a4a785053ba239e05367024a381051ba233dd09defa4fb7d033ba139decb66e84cf74077bb83eddc176e80e7750d9ba033005a1ee491b708a3b824e00525edc9174f8b3a7c53da5a56d252769093a7c51d9eb069e93f638a5b1939d8c1ce9e93b5e4d9af24cd78946bc0a34f487a792bd6628eb253b59033a7929d5cb669e48f4f057a9451d48276a40bb4f053a806cd3c1180290f4b695a5949d2c24dab14b418a5a3949d1c24e831434169ba2450d049ce85143410736ab52cfa3067cd82d54bf9e018ce4a4e740b3390936aa5ecd1b6668973344999a23cb552de53143296a19496ccba2865cd43292c19486ccaa28654d43290c16aa57c952e64a543250a18f364c792e63c9331e2518f124c781463c092d54a78625ec312ee189370c47b8612ac3094e184a3152b986126c48946244930c05586029c301461a5730d03186026b5529612973094996a92fc1d1e5aa4af050918095ec0497604173010336a929bf1b45f8d82fc0797e030b5493df0942f82597c020bc51a5e25b2f12c97895cbc4a65e2062f10296a923bb92e5dc932d505f7613cb5415dd4522e60bd7415cb98175cc07ad505370b68b85b05c24f2e12616a827b75285ba482dd0596b134b58365ac192d60b96b04cb58165ac092d504600a33b4d1cd8ad26d149d62a49b2e2c596d62cb4d965a58b2d2a58a8cec946762848b1cae58c48ec50880094fb09a4d8451aa18a35fb5eafc9b542d46b9ac15cc60ae5b05728e2b926950b43ad128d6cd42b44835a239a84a755d146b18a157342ab92755c90aa127d56239a95a0d5493aa548353450a99a854c942a546750818a8c945448cea10280094ba7d1cd26d469d49d49a51a5230528d82944d94c028a513052d172944b94a128a4d1980251e906934824a9f628d1ad7a8d4753eb51a22b0511182886c1441389f5a1d0c8e67e6834224e9f920cff1427f6a13fa509fc944fc8ce7d4a8009439ed1c8024fe782713c1348fda9cec512718a538a3a9c9a84e40c27146d1fb419a924cdcd226a463351459ad18cd41223f4bd34134991a8ccc512658a1323418fd294c49823f2bf2f24997918cbc1263f2bd2e13c8fca9ca8d46598a12a341950aeca84fa5425b2a0198fca94a51423f27f25a5e92d2949c1224b2bd2595292c14c7e4fa472d92393c91c0c47e4ce3f037213419082f4840fa3f0332003c8fc098024ce3b49d1e1258eca10024be382911c14473e29c6c512318a518a3a8c9a84640c23146ce7b428a9a4c5cd222a465151458ad19454121cf4bd1414489228c4c512258a11234273d294444d5cf49d1045073d21c2ed021d4610ba5e86da042e94a1747b0c34085c14b9e90a154c0e795f83da4c1e8ca114610793283c24b9e57a0d278e795380e28c15142036850434080d214065760329d0192d80c0cb9e54a006a10025073ca7bf0d79f86a4fe0487e0af3f0549f8282fc03973ca73e65b1f3298f993c7cc0c39e50df0288f80487652f3b2949d92bcec95d764ae3b2555e72b8f392c79c0c3b2549d929aec93d764973c4551d925aef95c77caa3b2069d9032ec8187682e3b40b1d902ce794273c0dba4d09d5680e92427482f3a4139cf032e803c73c0980248dcd472dfb4972d2737e925c58b0e2b587153638a961c54a8dfa3370d19b7e521c1298e01236fca200213dbc692de04666e28b72d79b906ccdb516ceb0367181b36c0d99386cc1a336d0dae4a2d83506b920b5c8e59b09cd44516ae28350d09a849cd424266c1f34c8e59f682d224e67d20b41141a06a0d025067d19b360b19d050ce23366c1200212d99472c6b5165d2731a9458e8c0c7360639363244a18e4c0c845c6392e31c0a18d46600847629a4b145296f8a2c3b5e61c9d2ded4582ac0c1460609b03040e16f686bf26c5f8942fc0a16f486bd26c5e8942f40a16f466bc2395c1a0aec93970482b8c505c5a82e294171050b82335bcaa00210d6d4720083f5a81c2d40d1276a6b404458e292c64e9646a0b213058c9b24ed05274a6aec50574142bcd015d04893a3355924ab4d2156462ac231558a42ac115272bcaa034541a8aa4111518a0a834149ca929c581270bea4a4952518a92545492929385e51c1624e14d3f6a2a24504fda0a7e1753f07c9f82e4fc0ea4e1493d8a09383f4d92f26c949362529c0484d82f26c1492707c9906c4c81e2640b1270669382f4a9a0a549492a2bc951524a89f2544c92705c9402c49c118020cd2349c9202548c210020bd20090900442b629a3c111198a48c93a469a82344c11926c56b422b529a27141130508a34044c1215a90d0c692883484311921c8c90c290860452b4af214111068a28404441e2820cd08ad2a4820352b4a7205140ad2867cb403fd181f2578fd6807c9523e49e9f4d00f925c569423dcb015a17cf0692782323c0a89e0524f1460780322b42f1dc0b0ad0a6724513ae281c8d08e9680721423902e9c8138e405c7201d2b4291c2d40e12a05684f365af1b2d48d92726e0483642f1b2148d90825684e350361a8130d40786a02c2b4219a2520d10885d15e2e8a9174178ba0ba5d05c2e82a990170c80586401c2e829174134ba07a5d02e3082e184150ba05a5d02c2fc2e174094ba03c5d8542ec12174074ad0845682f2c1a1160948b02bc581522c0a7160508b1680580422b41715c0b0ad046008232a91c1544d08968654233224ae14c4a0a546644954289209448e48929c4f3422792713c9088927c4ab4126d1892a570996804a93e25c2e12a0f89502a44842229a11248c88a2b848240228a711c1708a09c4615c22821114054890640081f2189c10c0d065686413412091f104098654843eb421f5270fa9087d04c32a321d1198f28c47925c3a1321d5190ea4f8752643a1221942e0e40a071466328541b1208d88e46d48036122194270ccd086649c3324219da00cc5086507c0081b17d1c0c44b05f2703002c17c1c0acd0c5c6822e13e159210aed085729c2c15c15ca10ac8c80102e29248148a40a4120028a6272381389c09c0e0026a626038009a1890d044847c2412a00921086d084349c21a4210c950048c83b6821f3400fd1807c4903b4641d93e0ec96804508326841b3400dd1806c490324841914e0c8a10644b402264180280a11985a8c42d25c141320a5190524f829264141220089203f1441f6a20fa4207d1903e5081f2640f84e07c1f004148136820e34004d19034d00132640985e05c1e0261481307c0982d04c0e804108036840834000d2101cd00032840185e02c260061480309c0305c0181600c070030840182d00c0e8040c8010260001f 10 11
def l_38 : Nat → Nat → Option Nat := unpackLinksF 0x73a039c05cd43e6a0735039595cac0e56072b03930bc902e480724038e11c700e3417180b8c01c600e204710038705bdd7dee06f6077b01bd02de806f3077807bc00dde0eee077197b8c0dc01ee0037001b800dac56d6036b01b580dac06d1176785b381d9c06ce036311b180d8816c20b6083b040d8206b9235c81adc2d40bea0034f83a781d1e7e8f034781a3c0d0e4687034381a181d0c0685073b1f9d80cec06721339019c02ce0066e0b321598c1cc606630330859744cb616590b2c819640cb206560f2b019580cac06530f259192c0c96064b0324079200c90064803238391c0c8c0e3e231f018f02c78063c031d058e80c74063a031b878dc0c6e06350b1a818d40c6a06350319078812c400620030e0986c1c2e2617030a8584c2c2606110b039581c0c081e040300877e48bf205f902fc817d83bec05f506fa817d40bea05f406f6117b00bd805e812f38378c4bc605e10af08177c2bba15d32ae9817403ba005cd0ee2917140b8a05c502e1077080b820dc102e0817040b800db822ca496500b20259002c60962c1b140d880ac38361c0afa557a0ebb875dc0aec0d7506b70f5b41ada05671ab3035980ac0355e0aae055682ab0155802a7155341a9a054c06a6015204a8e0d4702a3035180a8a0d4112a0814f83a7c053b0e9d814ec0a7605380e9a874d40a680d3306960f4ac1a4e25260691094841a400d200290014782a3c051c0a8d0544c7a1e250f0287814207a10050802808f3fc29fa14fd027e033c4b9e204ee0e77013ac39d604eb0275813ac09ce24e40e6c9736409ae14d7026a8533489980cc8126401320099004c60a5b9f2d8196c04b40a5a012d009621cab1a55032a0295004a7065285278793c049c0a4e0126c1936049322498124429200c90024705238091c048e024701214990a04820e41012080904048106408120408ee5477023b811dc08e42c700a37831bc08de0467223381194289cbc4e0227011341896144b02248510488800c3c121e010f00878043a0a159f0a8185404280a14010a0084a1c1f1a0f030702838041b060c8504878240411060881038380c440602028301408080c0402020100c17f05bf801fb04fd807ea0bf501fa02fd007d843ec01f504fa417d203e709f380f9817cc03e601f300f9807ba4bdd01ee80f6837b403da01ed00f6417b203d901ec80f3ca79e03cf01e780f3c07942bca01e500f20279003c801e304f1807861bc301e180f0c07801bc001e000f00078003be09df00ef8077813bc01de00ef0077803b90dd3a4e9427480ba401d182e8c0746039b21cd80e642704bb8201bf08df806f4237905bc02dd826ea0b7501b594da036ca1b6501b202d8c16b83b5b05ad80d5466a80b5401a70cd302694134809a304d180678533b059d80ce816740336119a82cd406680b34019982cbc465e032c0d9600ca436520329019480c9836461b23019102c8416343b19058a88c501620230f058702c38061c030c098600c28261013011d7e88bf405fa02f61d7b00bd805de3aed097584bac05d40adf2d6f80b7c05be02da156d00b6805b402d5156a80b4835a402cf0d6780b3c059e02cf016588b20357a5abd015d84aec057212b1215802ab0455802ac015600aa825367a96154908a4805220a8f094390a18150c0284094200a043502027b193d029e024f00277053a849b874dc026c0936009ac14d6026b01319098c04c2126005300097824bc025e012f0097804aa4a5501290694804a4025201290094414a2024729238091c048e02421520048fc147e023f011f808fc047e0237211b808d4243cba1e010f008741436121b010c8484484200a0c1106008300418020a08fd9e7d853e421f200f8827bc23ce41e604f30079023c801e10cf08076c63b409d808ec0075c13aa11ce1ce700734139a01ca0ce110708038209c100e002700038001bf04da166d0036411b200d8826c4036201b100d8026a0835001a608d282694034611a300d102688034401a200d1006649332019900cb06658032c019600cb00654132a019500c59462c0316018b00c580618530c018600c2046100308018208c1005fc32fe017f00bf805f032f8017c00be005f002f8017a08bd005e802ee197700bb805dc02ea116348b08458012c0016000b00058002c0016000af8255c82ae0155089f2e4f0227801322897864b03258012b0495024a4125201251092024900246091f108e844740234191a008c824640230091800890c4402220010d0c86804301218010b04858042422120103187e0e3e821f400f02877043b411da00e718728439011c410e2006e0c36431b200d9006b0635801ac00d600698634031a000cf046702334119a00cd006602320418e08c7006302318018a08c1105d0e2e8017400b8085c002d8215e38ae0456822a4415008a70453802942142209d104e80274013a0098144c002600130009314490221cb10a10850042801f870f8107c003e001f000ea38730839021c800e2086f0837801bc00d0386608328219400c8086208310018800c4005b1c2d8015c40ae0057002a0615000a80054002886138309c004e002700138009c004e0027001380088504208210010410820040042000100007e083f001f800fc006c4834081a000cc106600320419000c8006208310018800c40062002e0c17000b8004a481a2c00b20001 0x36d4a3c4a39dadb069ad4319681b0352c651ed86566912a3c31298e490b7a1658b0a3c282948410e32d23834d9b2a5ce08947020a2904c12aa40da9a8e98d077e27d1c932954968a80877d03229011955246f65b18a2c09f940da5a8e96d0453245bc03e484196ee0b8520449f81d4fca46ea1b3714b3b6253da128e9490787477c2239e0119e168c6c12b347951dfc9def84e77a267299318dc91b76165890a3bc83bdd81cee80cd3e0628f82314409ee491b718a3b824edb922e92d4360691b2a5cd222868f143466a1b5b4ad9d2eed45265a283ad92982c90ed212545083aa0293b010ecf583456a18d250d9629634d36c02b347151d909ccf24c5ba0b2c4051d8c1cad60c71a6b9b0a6cd81266be4a35e05146a6081118688d435b8a3a1b42d68a74f250a0425a28021d640c89c04604471ab96c61cb01c84c3426a1aa451d05a109e48b5309cb5842d481709c088e403a72138d40366db1676c8a7b4451d01a16cc93f6249daea43c2d2157c5668c2a33b943d7095eb04a756247011216e02cb0c14569087aa82bd4414e9e08ce304226813d222868f143496a5a3350d35a567e977324ab5e959a2ca8e98526582831a9316dc2cb0a1474b092a184147418e9052659283a213982898e8e12544083a10393ac18e89143428a1a4c52d1a2868ad373e4bb98a55af0acd1454675283a193982498b6c165840a2b3841d041c9d40c73f8c19f360cdd34636981e92b99e0183282e6740b3348bd8dc5db34aed2a5573b2934414171c2eb1e15739092c1041c9d2a3d04a0c80519bb6ccd92e66a9333447997950cac2865c5432a0a197c50cb9a864c9432b8a195350c9528665143316a18e26cc91286605b32d2c19606cca43064e973262a192850c552e61c9731b6d992364c8d2e6449332125190124c7c1463c0931524987024c4c1461a093152b8f412cc480c6264a3122498715c3209661a0631c4bd8da5dc6926e328f6bb2b344951c609562e4a7162518a12679890b6a165830a38882ac4014e1e0a30c04c63821c292e6129330347983938be4924e89423448183a3c785183d052305090f495c0180c604170070595d25aa512b60857a882a58192e784969560b46104b8081913008ce6542332817d1309c8a04644c2f82417fb68bf9b03c68f2712a118940bdc905fa0f2fc0617d250be4965f0081e2250ed1287851c5ee8d2f62d97a964bd0ae5e6532f203178814bbd2e5dc932e647976038b74122cc5411c2817613c2e8985d4520c80917415c0180c19417007058da15a638ab10e4a85f24d7485e608295ce0b84c0457301e2e80eaca1411b0816f830590202340c2de04172368b8db017a8f2e22797093058c28232102dc0416fa50b78905ba0b0bc0505d8282e89c5b84d2db0d96d064b642e5b0132d70596b024d2a29680d4b3d4bf9c25eccd2de5095f1d4a785a52b28afd7056e932af439539c0a0c604c70825f8312bc0094df649ef0246ec1217102fb6416d8d0aec085358820a300c6ed05f7582bb9414dc009ed50465c8212a40f90a06c5e02e25813b3d20da68e6cc46317922b39a15a293acc485379428b8984dc501e98a9638547a52e59f162ce6b166a6cb312c5969526d281169307bc90592162c60a9359408ac983e0482c9467351328a89158e572c624769349b4124d948ce6926514922b202458a112ac0315eb51b0da4d76d06c228d5913eaac0c554062bc8a56035eaeda956e57abf26d54818ac4a6550062b62b953818a589a54c061e824951814af6b0579182bb6c15d238ad4ae560532ae2795c934a940c544052b66a15b350add28d6a906b447357231ac5a8563141e825159451ac1a155e93aae48554241ab11cd4c8c6a76855524ea9921551142a76a153250aada0d52906a546751928a8919d83146be6a35c343acca755a4faa403150814a18a85369069f4734ba31a14a85085429a6854ea4ea5d21506542822a140950a00a85300a2968b93f9407c4ae4fe5029b8c14d360a653652e982954b93f150a509453cd469c4a349a339f4a0516d469169344b41a412544e8ca0b26413011a2a2951cd7a896a533a52a351d4b45482502312a40828a04ca942592a13fa54a2eb0515182896c13f26499128448901ee4612c150824a05104e1e626141241a191cd008c6816854224ea0121505142816a1402509fc9450ad06834833f233a3e28d18d46876873ea5498d214468ca532850113258421a2e0cc1e0233da39884914ecd02682a13ac5099d3040e8c25a2c12793c9e49c4f04d1e62613314099528410902592a13b1449cda84e40c2758a536a5e991294409061e4813a23a9c51b4be57a582a52914d458209080a44a0432201907408cdcd026e691358489ad18c9c4b9f024537a499b518cd85164d25cf79229a8244ccd02658a134134998a24cb1420848133b51991a0c0e8ca622bb2613e7b899048086624c12b960874984af1766049327a4197d18c38489800a32f0495f820cae9b25c2792cc50966284369025a6a32c341869194ae5765627cf313295496ca80641602329450865203c85024e0912825e93d293c88f64d2bd261527d498c960a5150424181912408bc8932492d8fc95c9209e48e060482600992086120488d0617464bf95290c2f2fc14a4207c8a83204c0e8264a2400793bb539c1a0cd297a634a51da3e87d19c2c8ca612bf2e95e96ca9ca654a5127f2513e91899bb04c97d0a6890332041488e08645037208198fc098240463c24b1ea4e8eca146c902282a11ab5089d304349020b2c0fe94c8e4a4470511e628113140895284369020a2a11b1448cda84640c2358a516a5e891294409061e4811a23a8c51b42457a092a50094d580209000a446042eb01904408c5c9022e691158488ad193f84f9f026517b498b519458515fb27cf79328a82444c902256a114144898a244b1421b48113c51891a143490a152bafd14e7b8a10460862226b104507d5263f25721d49d0da42844a741050a180520e0217540c8200461d4610db40861a043cd021c4bd0d2528651ec2057a072a50014d85c14836085d4032078118553040c5821126108a3081a2ec26d25fd68309232840992f81460f092bd0418193641a4f20a6a10545082120410d020b8a304b4281d2140c5760529cf314281096c060640a02300b50801283ca541fc090ff35e7f5a93cad35fb2bcfd1527e4a0bf00e55f0623f81911408bca971f62d8fa94c7d09e3e6061f1288f80487800c3b6051e92b8f112c77c0c3d2571e8258f3818788aa3b4051e02b8ef95476c2e3b40b006038f7a5e7b9293da579ec2baf595c7a8aabcc549e529af213d78c973c24b47e052220217780d3ba065dc030ec816014088864c003240eaa40755a03acd09d4484bd95274c2f2f4149d209caf84200c0e8064a1d00791bc538c1a145297a234a510a4e87d21c2c90a142bf0715e830a9c04549ff29efb94e7c8a1bb0509790a6ae0431f014884085d7036e881973c09804045c9482e6a3971918a22089c8684e5a4e719212b610910060ad04032a2a382550ca4b8e4c58721ac38e9b1c64b0e2a5470cac3805515908087830340102b01010e0606902070d19aae0c90d044e094c70091b98d25ca492e2233708a437e51155064858226981636ed45bd692dab416f0233580f9a5058d202c6da29374d79b56a4d885e6e41b3460b1ab098d102c6c02e3420b190068d002c67412190051b7ac0db4606d5b03684e1af0b8d504c6a01e3660d19f058ce0246c1a8360d41b14a2d7a416b91cb508c5ab6a0d5c5032014359145aa684d4a4e6a121344905a6472d0231685a1348939a0484d1450685a8340941a5682d1a4167d19b3a0a19c466ddc516e1a8b64d0dad09cd383e67816336091780a0caa416651cb228c5770a0bb050651a132e93991484ba8505d0282e614192250b90506422e2e2100d10b8b884065630328d81934d8c8a6063d2e2e01418e050cc35165928b1a8cd6f080c2b5162da4b06d058a294849323b01904c089848a4c435e60da92a654987274a28520941120e500eb080a8950510282e255185ac0c246060db02e0591502a08314033c98286140ea080c103831c183009b17f250120305f81402c0817c4d8bd92808c182f40a00a040ba2415e11cae48c573684bb24e5c9212e9141736a0b92505c4142eed0575482b823362628b0cd4581686bea435e519ade5514f284829324f8211c60c81e044b6a3940c112d0d01540a0b3c5054cb01d04c1450c09d03c5ac1c2d40d0c7060a9040544a81d2501440a0b4044595a82c84c1678a4b0241564af2a054902282801405989d2c64d89c25c2092252c2f2861493d09a9782e074110444814a0d89703c4b01602c0804026007120070182bc0903f040af3400f8102c11403d2600692006c182540b15f050ae824014102b4d015a690ac14856118a700b8d2044ada4956518aae5215608a9b82e340112a4d01518a0aa034548222a3140e9280a9b51541a09d04c822244a705d4d81f19e0c94e2c0a10603fc182851754c4929d24152d18a9454549292961413f8112845b147058a2450512281fa501456a2a1b413f0992841754107c638325001702c0893f03a9ec503eca018a101380909da5e4e92918a8f539252951214dc2f26c148d60624b01e0f00918a531340d86c85c4cc1e2640b03b2600a0303e82025ed052e4a49695e4b0a92564f92a2640a12d3e4190284f128058b4b53589a0ac294d5c466aa95e53ca92464f9012667c132250970744894d0bea405e51829a7c1493c07e9a83e4c4199720c93005e9482e49c118240892404a92a4e48c2123c9010a0a08eb50424b01f8500ec0c06f04c48424240110c70808404041ca81fa500eb0a08f04446da82344c11d8a48b24143caf20c54902282801404709d2324d89325c1c9223d02f1d4148e209a5b82e04411042480f30d85b03c2d016014080382600d12004018228090370408a3400d81022d140352600c92003c181640b11505089824014102209011069087148439191b80f8d206488b4943d1921a5210c08a6d83e34019210901076a0850444202220f140fd28084c51419a11f8508212447b85d3682719e1090406a81450358a61b2170ff29c7e9423e897034488f109c748422c41701c088ff4607eb403e9a0200d00fe2bc7e1523ec9e9f24b8192447805e3a0291c2134b005c068223dcb01ce180f106078a3039e2e9ead24de6827a2323cca89e4524b42827803239cb61dc0b0eb6a075c503a4a01d2d00ec8a2753423a0a11ce174e609c6384239417014088e403a71350384a818c140dc0906fb5e379a918cd34dd2725913136c2f1b4148d90824681e0d00918c570d70d86b04c3541e1a80b0d22906884430c1617e090ca0b86102c2f00e194170c90586401c30c2e184150bf0b80382c2ec0e178150bb0486815e33ca91164b8332446705e3342e998170cb0aa638523182698a0f4c405c6082d3001617c094050445e81e2e80e8644c004060588402c5a016ed08b64a45a95e2d0a9166538b22840212d2c0210084f0ae0588fc53461a122e94d124868595e414a9206539012867c14222497062488f60be7785e3b4299c6148e009e6c04e34c21972108b805e5782e2b411804088a64a8039242ad1c1505b0a52c85195c280a613c4f0aa2684e05024c201160c09b08049030230101508cc9a064488222989414a8cc9006051a412891c93c8c48f0444c84001c94140d089f49c4f24226021136570992984da3125c17118088996804b85c271a09345709827c4b03e22c1912a054922b84814c2491911c0f88c064482402382e1185706002849b42244ae11e5388d09c458422280a952d0ca72b852154284a713a4f894084448321c8aa00c050844a0402401f91810e4e07b0d8388641bc2e0d413068078430341e82e0ce130790b84234120d1f0fc8c8780b83303e208130ee1706d0983b05c1d42e0c4090806843fa4e1f9210e81706c09c3e8261e8a00ee4c0752403d2311e4970ea488774643b13e1d4990f68cc782643a1221c8140e28cc6d26036a401bd208dc8e4684623612219ca000c0a067680353421a5270d09086628442b43205210f88c8730b8380541ac270ca0f86225818010180160600405d4a02d24018d1c0ae8c0612702f8380bc0805c0802d0202eb411709f0ae4c82c040158200a8080b0570290402d342164a70ae508280402f34316d210ac8c8270202a24814ca404c180520900b0401411c09e4e0250c027038028180604904a4a0232401111808254039280199300bc9203a14011080260380141807050010080253411251f0888c8352642412a0902901e0c8402800e040119a108a938444841e94210c950461481b084202400382007e4903f460203400f892082d043d4641e13e0cc990764b4220a4068320e120034100372481ba300e1a006c490396841aa420d0a70665083225a108520642105c5002b260149200c01405c8c42d25c149220ad190544f82926417a330b099050488268a212b51091210468c822284109320802702c1081f07c05032071200345001c6800d34005c1e03ad041b4640c9320602f02c1481507c02832050168260741048007140041a001cd000b0980405c01c1600c0701168407a42034a10181780a0a40484e014210080b40303a28c53135a9896d0c47484212320e8a10624c8272480f052048210040cb88697b9b43dbd25e9c90ed44676214fa80a5d2451e7c2873d13f8f899c744bdce246df04f66825b1811d6e086b603f49819a440bcac0464401f1900d8aa05c010260001f 17 6 11 10 7
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsF m_38 g_38 bds_38 (dagRefF 906 (dagTraceF m_38 s_38 8 f_38) l_38 0) s_38 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_0 : treeBlockF 0 32 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_1 : treeBlockF 32 64 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_2 : treeBlockF 64 96 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_3 : treeBlockF 96 128 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_4 : treeBlockF 128 160 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_5 : treeBlockF 160 192 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_6 : treeBlockF 192 224 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_7 : treeBlockF 224 256 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_8 : treeBlockF 256 288 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_9 : treeBlockF 288 320 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_10 : treeBlockF 320 352 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_11 : treeBlockF 352 384 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_12 : treeBlockF 384 416 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_13 : treeBlockF 416 448 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_14 : treeBlockF 448 480 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_15 : treeBlockF 480 512 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_16 : treeBlockF 512 544 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_17 : treeBlockF 544 576 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_18 : treeBlockF 576 608 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_19 : treeBlockF 608 640 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_20 : treeBlockF 640 672 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_21 : treeBlockF 672 704 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_22 : treeBlockF 704 736 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_23 : treeBlockF 736 768 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_24 : treeBlockF 768 800 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_25 : treeBlockF 800 832 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_26 : treeBlockF 832 864 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_27 : treeBlockF 864 896 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_28 : treeBlockF 896 906 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
theorem nj_38_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_38_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_38_1 h1 h2)
theorem nj_38_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_1 (fun _ h1 h2 => treeBlockF_at nb_38_2 h1 h2)
theorem nj_38_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_2 (fun _ h1 h2 => treeBlockF_at nb_38_3 h1 h2)
theorem nj_38_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_3 (fun _ h1 h2 => treeBlockF_at nb_38_4 h1 h2)
theorem nj_38_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_4 (fun _ h1 h2 => treeBlockF_at nb_38_5 h1 h2)
theorem nj_38_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_5 (fun _ h1 h2 => treeBlockF_at nb_38_6 h1 h2)
theorem nj_38_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_6 (fun _ h1 h2 => treeBlockF_at nb_38_7 h1 h2)
theorem nj_38_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_7 (fun _ h1 h2 => treeBlockF_at nb_38_8 h1 h2)
theorem nj_38_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_8 (fun _ h1 h2 => treeBlockF_at nb_38_9 h1 h2)
theorem nj_38_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_9 (fun _ h1 h2 => treeBlockF_at nb_38_10 h1 h2)
theorem nj_38_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_10 (fun _ h1 h2 => treeBlockF_at nb_38_11 h1 h2)
theorem nj_38_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_11 (fun _ h1 h2 => treeBlockF_at nb_38_12 h1 h2)
theorem nj_38_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_12 (fun _ h1 h2 => treeBlockF_at nb_38_13 h1 h2)
theorem nj_38_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_13 (fun _ h1 h2 => treeBlockF_at nb_38_14 h1 h2)
theorem nj_38_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_14 (fun _ h1 h2 => treeBlockF_at nb_38_15 h1 h2)
theorem nj_38_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_15 (fun _ h1 h2 => treeBlockF_at nb_38_16 h1 h2)
theorem nj_38_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_16 (fun _ h1 h2 => treeBlockF_at nb_38_17 h1 h2)
theorem nj_38_18 : ∀ i, 0 ≤ i → i < 608 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_17 (fun _ h1 h2 => treeBlockF_at nb_38_18 h1 h2)
theorem nj_38_19 : ∀ i, 0 ≤ i → i < 640 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_18 (fun _ h1 h2 => treeBlockF_at nb_38_19 h1 h2)
theorem nj_38_20 : ∀ i, 0 ≤ i → i < 672 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_19 (fun _ h1 h2 => treeBlockF_at nb_38_20 h1 h2)
theorem nj_38_21 : ∀ i, 0 ≤ i → i < 704 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_20 (fun _ h1 h2 => treeBlockF_at nb_38_21 h1 h2)
theorem nj_38_22 : ∀ i, 0 ≤ i → i < 736 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_21 (fun _ h1 h2 => treeBlockF_at nb_38_22 h1 h2)
theorem nj_38_23 : ∀ i, 0 ≤ i → i < 768 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_22 (fun _ h1 h2 => treeBlockF_at nb_38_23 h1 h2)
theorem nj_38_24 : ∀ i, 0 ≤ i → i < 800 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_23 (fun _ h1 h2 => treeBlockF_at nb_38_24 h1 h2)
theorem nj_38_25 : ∀ i, 0 ≤ i → i < 832 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_24 (fun _ h1 h2 => treeBlockF_at nb_38_25 h1 h2)
theorem nj_38_26 : ∀ i, 0 ≤ i → i < 864 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_25 (fun _ h1 h2 => treeBlockF_at nb_38_26 h1 h2)
theorem nj_38_27 : ∀ i, 0 ≤ i → i < 896 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_26 (fun _ h1 h2 => treeBlockF_at nb_38_27 h1 h2)
theorem nj_38_28 : ∀ i, 0 ≤ i → i < 906 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_27 (fun _ h1 h2 => treeBlockF_at nb_38_28 h1 h2)
theorem nc_38 : ∀ i, 0 ≤ i → i < 906 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := nj_38_28
theorem lb_38 : LowerBin m_38 s_38 g_38 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_38 sub_38 gl_38 rc_38 nc_38

def m_39 : Nat := 0x5555555555555555
def s_39 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_39 : Nat := 0x1115151515155555
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 5, g_10)]
theorem kn_39 : KnownBin bds_39 := by
  intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_10
theorem sub_39 : ∀ b ∈ bds_39, m_39 &&& b.1 = b.1 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_39 : ∀ b ∈ bds_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
def l_39 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsF m_39 g_39 bds_39 (dagRefF 0 (dagTraceF m_39 s_39 5 f_39) l_39 0) s_39 5 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_39 g_39 bds_39 0 (dagTraceF m_39 s_39 5 f_39) l_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_39 sub_39 gl_39 rc_39 nc_39

def m_40 : Nat := 0xcccccccccccccccc
def s_40 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_40 : Nat := 0x4040c040c444c
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 6, g_17), (m_10, s_10, 5, g_10), (m_13, s_13, 5, g_13), (m_16, s_16, 5, g_16), (m_21, s_21, 5, g_21), (m_29, s_29, 5, g_29), (m_0, s_0, 4, g_0), (m_2, s_2, 4, g_2), (m_5, s_5, 4, g_5)]
theorem kn_40 : KnownBin bds_40 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_17
  · exact lb_10
  · exact lb_13
  · exact lb_16
  · exact lb_21
  · exact lb_29
  · exact lb_0
  · exact lb_2
  · exact lb_5
theorem sub_40 : ∀ b ∈ bds_40, m_40 &&& b.1 = b.1 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_40 : Nat → Nat × Nat := unpackForestF 0x25149000b4f92da749c0f64b26b2613d92c1a802d2e454a12295c914a848a172450a000b478f09fc784de4107b1e1358f01fc780de3d27b1e035005a1c724d63906b1924e8d92146c0b63224b19a428cc96c64094014971803c8b49ac5c4f22d06b1224e8ac1245290a2905b1212589c9244a90a2525b1202500521c42d2e2168600a3e87d1e0028ee1d05b0d12586c96c34094014670734e839a1c264fe1326f0983f84c1bc1cd0a1107b0712783c9ec1c09c01464fcb537e5a5c1314a0906afcb4981c9a3f2d0df947cfca327e427c04571f9096fc8477f5a0bfa8f9fd464fc8457ec263f4551f90860094f7d40c3ea055f50280094b7cc1abdcd45ee47cf7b597bd1f3dc1740128ef515e7a89e3d405401286f334d7989b3cc0d5de6a4f1a4c78c923bc96de1498ef25377da53bc5780127eee134759adbb28d1d9268eb353758af3ac4f001276dfc586fe293a08edd1248e82336fe2839b581cd4b8dfa5b722b0390971c98a0e41246fd29b7e901c4296e21436fc2638092dc1248e02436fc200024ddbc468de134671adb744d19c6a6dc1466712f36c1159c2bcd9a4b6cd21b38061b04bcd81526700ab5c4919d496cea43674a733a13da94b8ce84b699a834c9419d08ed025c689a0344901a02a8d003c67421b3a0bd9d046ce01400499b340d59749ccc24265c128024bd9502a009235c5a9ae2d2d908a4c81355c5a4b1c0d171686b8a3e5c5192e257d712a6c40445c4a7b0c97171296b89475fda8afe8f97f464bf94e5fca12e25157d2b8bda545ec0a2e250d786b0bc1545c49fae4951722b8b91545cca22e4051712660084f5b4162da0996d0480084b5ac9aab8d455c47cb3b4959d1f2b8575646c0b216c5709fabb1815d4d8ae96c578ae2bc1015d028ae13300423ab4551524beac12454929aa417952078a995e54ca92a409801086a734d5389aa9c0d93d6a4a5a4c52c1227a96d494989ea53519ac28c1513d2bea1b6050c3627a55d40498a00244f497a7cd293d0bc0083f4ec1a26ad6d382689c0344d5a9a6a179350780083b47a2c23d1492f476980244bd19a3d1412cac09625c4792da4f581274b89445049c1223c94d1e4809194b48ca1a3c5311f4969002447d21a3c5000106e8d93446c1a1d2d6d1906874b53458aa22c150e94be89460448b62241b0e94ae8793443c1a1d28fd0d08c7495e42ca29d217908496842433a416200979004a48015e40ca02005590027c8005e3a4131fc090ea496752433ec221d453cea2967b3503d9281ec170ea28e79b403cd201e2950f1278751433bc121d44bcea246758493ac209d4138e90480083339c9a9b8938dc29e7193438c0a1b850cdd69c6eb42374a71bc050dd2846e125004179b4098010466ba3435c9a190d6cd42686a034321a99a4518c84bc6415e3392a19c5b0c80be65a6c32cae19015cc94686403f0040f98a4d0c50685ab5b3091a1840d0b56a6601542d52f97c5b0b54ae5e1342d51f974118b52bc5b95d2dcaa96a178b504c0081b2c124160910b02885804409e2d956920ab488559442ac2204f14ca6470532342989a14c0d0276b65123828d201448d0276a613b4e26d1c13c9409b4684d93426c1a04ed0c9949049c5224d1d12cd409346c4993624c1b04ed08274be44b492251f11cd208946444946224a29121188908a13a5e219b610c4f0274b641c6020db004e95c7f8a03fb501fcae0fad907d29813a531b22c8f291079088364511b1ac8d8d44752683634e1ca280e44d06c6843615d1b0a70d84f46d6803613509d2904e93c686bc3435209d270cd140274862dc5216da08c28d86106c2db4017d180b65785d6802d95216ca684e9082747e13a33155300ac540550a81395f12d1f0968c84b2b22595112c9f09c8c04b2642584a12c2304e578484a02406c09cab88a5784525c1395210c1a04e4fc3f4c0201400fcaa04e17c3347c19a320ccac8665443327c1c2300cc99066178330a41984a0cc2304e1782f4d817a500bcb604e15c2a2bc151520a82f0540b8270a41413409c1f80205c250680135b0851a0424d0210680135307c1201292c1b2500e13006c9201290c190880494f024a5828d40144a00a05c024a3822d001148007a5403c9e01250c0d0480492f024918141380903c0112401024808104040720203100c0a004178010260001f 10 11
def l_40 : Nat → Nat → Option Nat := unpackLinksF 0x4360219870cc086604300e18010b438502c280214010a00850042802118b080383c141e020c8b0583828141402078b004e802040101fe88ff407fa03f521fa80fd407da43de3def00f7417ba03dc05ec08f6007ae0bd701e790f3c079c0bce01e310edcf76e03b701d790ebc075c0bae01d586eac07501ba50dd280e94074a03a501d280e9407402ba001ce86e7407341b9221c804e38271c038e01c508e28071013850dc106df846fa0b7a0dbb86ddc06ee037701b598dac06d40b6611a7aed3c069e034f01a606d3006921b4805a400d20067e4b37219a06cd00660232a199500ca806540326119300c9806481324019182c8c06421319218c80c6016300318018b04c58062c0312118900c4026200310018782c34261a030d018488c2016100308018304c0456020301018080bfc25fe02ff017f02bf025e842f3057980bbc45de02ec0d7600ba435d202e7097380b9c05ca12e5017202b7865bc02dd056e80b6c25b40ada016c82b6015ae0ad3116980b4c05a602d1096880b38359a0acd016212ae8a57402b8095c00ac8655832ac015582aa4254e12a7015380a8c454602a1094f06a6c352e2293114980a3c451c0a8b0d4406a2005100288014400a2004f8627c013d829ec04ee2277013b809cc44e40a720139009c804e20a6d112b2e95804ac025601298694c04a01a4f05278093c048c4a460123009102488024305218090c04860241091e888d4846a02311118808b444541a2a0115008a8044c22201910008800440021c110e008700434121a010c8286404320215110a80854042612130109808442422020f09039081c040c0a060103008102408020401000880003fc11fe00ff007f413f611fb00fd807dc43ec09f600fb007d023de29ef00f7807bc03da11ed00f6807b013d411e220f08278403ba21dd00ed0676413b201d510ea8075013a801d010e78273c039819cc00e486724038e11c700e380714238a01c404e18270c038211c004e0006e8637401b904dc806e4037009b704db026d4136a01b110d8806c4035e11af00d6066b0035609ab00d5806ac035211a024cb146580328119208c900644131c198e00c700638031c018d04c38c6046302018004c00060002fc117e00bf005f022f8017a08bb085d802ec017210b9005c802de196f00b70259882cc016600b20459002c8016208b10057842bc015b0cad8056812b4015808ac0056002a8215010a4105200290014800a40050c5284094200a082500126e4937009b804dc026e01311898024bc125a1129109288494024a0124049200490023e291f008e064700238011b048d02464121c590914840242002100107048302418020a0905007d943e811f400f51479843c421d438e90474023a001c820e3046e8c37401ba00dd006d0636801b400da006c8236401b200d60c6a0435001a800d400698230d018408c20061002f4517a00bb085d802ec017600bb005a8c2d4016808b40059822cc015640a80c5382298114c00a5045106288014208a1005080284014200a0045000280012c5096004b0024841240092004708238011a088c04460022c1110188800438221c010e0087004380218110c008600430021800f8507c003e001f000f02078003c001e000f00074103a001cc10aaf05404290414410a008500026081300096084b00258012810901048002382114208808430421800fc407e003f001e840f400722039001c020e0007000360816140b00058002c0016000a0404e08231000c40001 0x24f8bd28a488611849c0f4b206a588159309e9644d4b002d27b4e8892749a4d64b06a5781792528490572472a12305c91428414d72164a0f3944855283ce4f2072bcf393e9041e95a0d4ac02ac8b5c8512829c112134a0a703c8f49e95a4d58e0bca703e2ac0b44293a1748509240830afc864fde527b211379009ab2617e3f07ea683d8f81bc780d4aa02ef213d8e89aa980f63906af224e8dd213c6539bd2851b02d2a0129b0074a702aa624e8d1214664b4a824aa584e4702118c068a602d1c24e788a7bb652dcc28edd9438d492a9413d3a0969584746821c64094d603e6201b2940b84804e300791713c7849ec5e4d54907b168358ac123c293a2a484ed14a720a34520b4a204a6181908c08c4e4914949d132428949694449539094938463500f04404a2c49cf014f760a5b8e51db92871412552027a6e12d2608e8c043890129a607cc10365081708009c44d2e216870fa3e814a7be251d8c09eb48472800bc3e8f21d05a4e8252700ac364b49d24a4d81687092c340949a02f0b13f8549bc280fe1306e4c0178441e92a0d49402b0793d2549a92605a1869d0bb43849a140853e1024ec584f8381392405e0a8b1039347a2283be5320a8a4f434d51c1ec120d5e88b10393423c26bfc1145302a4684d7f4228a4054578d8c01448082c114151fb0890115c130921121508a098fd04012c0a28ed25ff682ff23e7f5193101795a0a44504e0c426a8c0f9170646001a1540b3f6131fa2a85c06c0c42e2a80920c6a705b4b821a4c0cd0de568302a3e811193bc4f9b7264c505f56429c0613c8809b0084b80023bf8115f9086a283f454199a2074bf0362a0171280abee061f602afa81445020a880f5f306af785d7c1aca88d45ef47c1895d22caaa860f9130645f01a1200b3e4d45f147cf615d7b82ea840fd110665e81b11c0b8621348908a230150c4af10c5497b0bcac0527b0af3d64f1890beab85311012bd4055e869af39361a01ebcc0d5e4498f1924785263bed284f05af2b527892dbc094dde2bcbb85f58c2b8ce0f4e505eee1347691a3b24d1db6b6ec35375caf3ac4f1ce4b2e5a51744923a48edd0466e75607352e38a171c20a0e492472628382101cbac0e525c72092388171c00a0e294b710a1b82491c2496e02437522c3a7149cf8a0e625b71d29b8c901c3098df8406b80a37a8d1bc268da0186b40a3744d1b3030d60146e0a3362055ab028ba84d6d822b6892db3486af0546c52f2ea579b02a4b905e5742b1c60f9ae248d484969020ae6511a94b8d18406882034ed41a64a0af95c68420346d01a2480d225c684aa3400f0de248d6a4b6b121b56539aa09ed404b69423b3e10d9e05ece8236edadb72d4db74bcda95e5c42fab815ce207ed90186bc0ab380514107acd035505273309094009c880422f00d0860599949c9f84f43821b2e094bb036210176540ab231618e068a84504f8263231495069abc93d6409aaa11618e0684794d608a287a0588d29ac09450f00b063141802a8c40440d80a2fe950312b81a8245ec0a0831b1862b046154620222fa511864b8459540d0121185317c280198145e5acb06d458247cc0a32230af0625758029cbf9425e09f2ec4c8cf03a1f8155f4ae2f8950ce2d81895c5ec0a2f2d60686a0bc1540e41e2e605173288bb2545d4ae2e855172028c9b53649a5b1ed258d686a6b416311f3168c98a2bec495361ca791053585296c21475f8a2af450d7727eb89334f41f2180c8cd03e5c81a0f80b8640596f058b70265b4122c45056527ab593559caead0d2565682b3a3e5909f2c24c83109a448453300e85e055656c0b216c57c0a2be5715e080b1460585362c05b15d028b53515a51f2cc5756327eae1335582e99407c2e02ead1540b4920621715404816134560922a60d0860481894d22ca2856058314bc43252550af2a6549594beaba530a4932ac17955078a9026541a68d04f54f26aa70365312629609149498a3b581a1a809e4f1460a8a236050c36282931400489f34a0e416a9ad494a4b6a4253514afa8455c6727a9f92f4f42f2760d1392689c0344e9ada6ed4d360bc9a83c4b52ca549453004898a3b4bd19a5b5812c4b89215c484a8250091288a0900404aab0252971232b88f95049c1224852d232869002448525a3e90d338b0994524ba2825696d264a692a40488a623c500fe0288e13446c1a2120b0fd0488c834420161f8090fb0288b9544182e22c151040487b014452302265b1120d8810243bc0a2204d10f0688082443423200058ea0288314d42ca2a1292d0848681a543ec22206500f60b8778244192f20a949042bc811564049f200178fe0487d8443b02e1e8500f32807c3503dd281e4500f60b87a3403cd201e4950f12787585c3bc121d8124eb0827ea4b3f1219f453cf92967a9473c0a19dc4bced2467504e469ada30d4d154be88a574391fa185790a0bc8382c3fc131d2090e127a73935385261be490de2486ea343909a1c6050de02870b4e381a11be538dd2846481d0a00a9cc938e529e711433709299007c2702e6d0263611a1ae4d0d52686a034348a308c054ce0ba658550c426912114cf4a86716c0c4ae056050cc4d84496c32cae1928d0d66b669b533452f1a0578cd0be650573201f96a054c62686283430d1a1840d0c02a85c06c0c42e08c090be2d84586c2dc2e1784d0ba08c158162e0ae96e5543129a459450c52f10c948462bc1585e311ad982d4cbf4be5ea572ed1f972578b60bc5a8261ed30166920b2488589442c022132d007a2a03c950261a80f0980644a03424c2b92415a9105c480561442ac220ee980a94705423429c9a14c0d01e0200e820070081469001b0203b2602911c1448d01a02047a5e1d1290a65783d0bc4f25018d2813e8e09d4684e13426c1a0e6940994902ea40259a80c4500612804c4522352f0e2948664823024025d1d12a8d8522bc4a1360f02f1260d8874d0382600fcaa0aa1501802047240239a4080d30566b84345e1c22e920d246868247a3e235191185188b28a45046224228fe550876d828a6c2189e0761b01704040a5005808100940150204246020db00629b07e4a01796c12036026040120400882020628100d407f2b80802003c080e0db07e6c82826c1f4a60741b00e04039b501e9220f21107526839c50174a00e44d0404a82b0541b5a00f7164788a23bb591d9a88e8d38716842ba5d1252a862578702ba3794e170a10dc4f46c26a2085d0c02a8b6940696bc3435216da689e578390bc3345016dae09c9386246c2f94e174a10701386106c2fa30175a00c914863682303401352f0bc5785c2a42d94d0dc2f0504d0430680601002c100ac150562a02ba600c52e0aa1504e2602723014d1f0a48c8512b22815113c9f09a4c8360bc1685213025096118314d824a50118b60901b0462bc2292e0d42f0581484306820254100a0082980314b81f9540e0980708c03d47c1e2320ecac8745443927c1b9320d82f06a14834094198460c5360609402f2d81586c0b4af0585482b0bc1502e0a09a15f16caa8a652b5b285a9940d389a686493422452f910978854b6412571f1298d69486a49e33a4e195218b49085947e2c233150af894578472ae221521089f87c17c320bc170570a42904e0fc080200f8140789204a0d01b2480d92408d1a0444d01a2481083407c120384c01d2500d9240642200e1700502809140044a002cd40154a0081400502e024d00114800825403c9e00c1700403806824028270081081e4960d243060a782e52c1328e071430309781648c0309c0481e01c2480c104050720203100c0a048d6c206a6041240082f4a0d3e4a697223478eda1c6292e234871023e8791dc328ce0d464fc14f7d0a5bda51de9286ee93f7549db7c4dd9b266cb12f65091ae013d6c096ad84754421a780fd340768e8373a0199b60bcd90466381f2d00d84c05c010260001f 17 6 11 10 7
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsF m_40 g_40 bds_40 (dagRefF 594 (dagTraceF m_40 s_40 8 f_40) l_40 0) s_40 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_0 : treeBlockF 0 32 (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_1 : treeBlockF 32 64 (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_2 : treeBlockF 64 96 (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_3 : treeBlockF 96 128 (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_4 : treeBlockF 128 160 (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_5 : treeBlockF 160 192 (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_6 : treeBlockF 192 224 (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_7 : treeBlockF 224 256 (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_8 : treeBlockF 256 288 (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_9 : treeBlockF 288 320 (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_10 : treeBlockF 320 352 (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_11 : treeBlockF 352 384 (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_12 : treeBlockF 384 416 (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_13 : treeBlockF 416 448 (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_14 : treeBlockF 448 480 (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_15 : treeBlockF 480 512 (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_16 : treeBlockF 512 544 (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_17 : treeBlockF 544 576 (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_18 : treeBlockF 576 594 (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) = true := by decide +kernel
theorem nj_40_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_40_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_40_1 h1 h2)
theorem nj_40_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) i = true := block_join nj_40_1 (fun _ h1 h2 => treeBlockF_at nb_40_2 h1 h2)
theorem nj_40_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) i = true := block_join nj_40_2 (fun _ h1 h2 => treeBlockF_at nb_40_3 h1 h2)
theorem nj_40_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) i = true := block_join nj_40_3 (fun _ h1 h2 => treeBlockF_at nb_40_4 h1 h2)
theorem nj_40_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) i = true := block_join nj_40_4 (fun _ h1 h2 => treeBlockF_at nb_40_5 h1 h2)
theorem nj_40_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) i = true := block_join nj_40_5 (fun _ h1 h2 => treeBlockF_at nb_40_6 h1 h2)
theorem nj_40_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) i = true := block_join nj_40_6 (fun _ h1 h2 => treeBlockF_at nb_40_7 h1 h2)
theorem nj_40_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) i = true := block_join nj_40_7 (fun _ h1 h2 => treeBlockF_at nb_40_8 h1 h2)
theorem nj_40_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) i = true := block_join nj_40_8 (fun _ h1 h2 => treeBlockF_at nb_40_9 h1 h2)
theorem nj_40_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) i = true := block_join nj_40_9 (fun _ h1 h2 => treeBlockF_at nb_40_10 h1 h2)
theorem nj_40_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) i = true := block_join nj_40_10 (fun _ h1 h2 => treeBlockF_at nb_40_11 h1 h2)
theorem nj_40_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) i = true := block_join nj_40_11 (fun _ h1 h2 => treeBlockF_at nb_40_12 h1 h2)
theorem nj_40_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) i = true := block_join nj_40_12 (fun _ h1 h2 => treeBlockF_at nb_40_13 h1 h2)
theorem nj_40_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) i = true := block_join nj_40_13 (fun _ h1 h2 => treeBlockF_at nb_40_14 h1 h2)
theorem nj_40_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) i = true := block_join nj_40_14 (fun _ h1 h2 => treeBlockF_at nb_40_15 h1 h2)
theorem nj_40_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) i = true := block_join nj_40_15 (fun _ h1 h2 => treeBlockF_at nb_40_16 h1 h2)
theorem nj_40_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) i = true := block_join nj_40_16 (fun _ h1 h2 => treeBlockF_at nb_40_17 h1 h2)
theorem nj_40_18 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) i = true := block_join nj_40_17 (fun _ h1 h2 => treeBlockF_at nb_40_18 h1 h2)
theorem nc_40 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeF m_40 g_40 bds_40 594 (dagTraceF m_40 s_40 8 f_40) l_40) i = true := nj_40_18
theorem lb_40 : LowerBin m_40 s_40 g_40 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_40 sub_40 gl_40 rc_40 nc_40

def m_41 : Nat := 0x3333333333333333
def s_41 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_41 : Nat := 0x1113111311131333
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 5, g_11)]
theorem kn_41 : KnownBin bds_41 := by
  intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_11
theorem sub_41 : ∀ b ∈ bds_41, m_41 &&& b.1 = b.1 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_41 : ∀ b ∈ bds_41, canon b.1 g_41 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
def l_41 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsF m_41 g_41 bds_41 (dagRefF 0 (dagTraceF m_41 s_41 5 f_41) l_41 0) s_41 5 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_41 g_41 bds_41 0 (dagTraceF m_41 s_41 5 f_41) l_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_41 sub_41 gl_41 rc_41 nc_41

def m_42 : Nat := 0xf0f0f0f0f0f0f0f0
def s_42 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_42 : Nat := 0x1010101010105070
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 5, g_19)]
theorem kn_42 : KnownBin bds_42 := by
  intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_19
theorem sub_42 : ∀ b ∈ bds_42, m_42 &&& b.1 = b.1 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_42 : ∀ b ∈ bds_42, canon b.1 g_42 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
def l_42 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsF m_42 g_42 bds_42 (dagRefF 0 (dagTraceF m_42 s_42 5 f_42) l_42 0) s_42 5 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_42 g_42 bds_42 0 (dagTraceF m_42 s_42 5 f_42) l_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_42 sub_42 gl_42 rc_42 nc_42

def m_43 : Nat := 0xf0f0f0f0f0f0f0f
def s_43 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_43 : Nat := 0x107050f050f070f
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 6, g_12), (m_18, s_18, 6, g_18), (m_13, s_13, 5, g_13), (m_23, s_23, 5, g_23), (m_31, s_31, 5, g_31), (m_2, s_2, 4, g_2), (m_5, s_5, 4, g_5), (m_8, s_8, 4, g_8)]
theorem kn_43 : KnownBin bds_43 := by
  intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_12
  · exact lb_18
  · exact lb_13
  · exact lb_23
  · exact lb_31
  · exact lb_2
  · exact lb_5
  · exact lb_8
theorem sub_43 : ∀ b ∈ bds_43, m_43 &&& b.1 = b.1 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_43 : ∀ b ∈ bds_43, canon b.1 g_43 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_43 : Nat → Nat × Nat := unpackForestF 0x38946a00b4bdd12ff0a557850abba25de05b67025b3810d9ba257dd0afefa9577d0abba15ddedb66e855f740bfbba55ddcaaee8177756d9ba057005a3e34d7f71099b7145dbca66dc1171a6bbb4c6cda5b26d2d53694698d35bd8a366c49b3622d9b1160d88366c41831a6afb035cd66326b24e35d6a9ac934d641c6b4d53590698d353d45a76aa4d355069a8b42d452f6a2577510bb8d345c68afe9c1734b6aba635cd2c2ae34577464d9a3164d18aa68c4d31a2b79fc6ccfdb667ed833f4d99f86ccfc3063455f3d2b99b264cd8a6674553362899b018cdcaa66c0531a2a78d05fcccae660d57316b998155c682ee565b32b0c995854cac1a63416f248d99236cc91b06489b3242d992160c682be441731b2c98d84cc7c2a6361131b0598e054c6c1263414c0148f8c35ec5a2b62cd580147f6ac5bc489ae240d6d58b58736cc38b661c1b2d58af7e45ebf1af5f8d76fc4bd7e15ebf0aedf8573056b97e152c082e604142fc0bd7e05dbf02e5fad72fd2b97e052b562b5f4d3ad56b57bc58bdd365aad5ef26937925ebc8aede4176d56ad74349ba12f5da492ed04974252ba122dd2536e909b74244b552b5aa53ee18ad70b56b8d225c295ae108b6a94db7dae5aa51ed509f6c456b61ab5b4912d84ad6c145b5426dacd72d508e00a37b4c9b00252eb06bf67a45b3c22d60d76cd2d958357ac12fd92d16c908b5825db15b658a5b2c50d958257af9a6d7c93abe2bd5f934afc0a57c54ab048b5c46cae234571182b96815c254ac11bd6017eb36ab59a55acd22d60176b12d958057004a3d5ad7aad4bb46456aad2ed18d5aa68a95336ca99aa54c5b28c4af4fc5aa7e2b53ed5a9f69d50244a7d2b518916998b54cc56a65ab534912994ad46235a5cae52c91e8c0714a14da35a3524d128d28f4734aa39a351c51a8d26b460340049fd131b2892d939b57a152ed0a916852bd39a56a092ed04916732ad3e35a9f1ab4f895a7d2893e1569cc9b4f4d727948f398189d123cea5367526b3a1469cc0a0024ee6e6bd3725d9b8af4dc176578ad35a5d9acaf4aed5a678d933c5499daa4ae95e608b530456981ab4c4912604ad3014e95d1acb097a582bb2c145965a84b48c2592892c12595cab0024de552892946c949364a45b23f6af2835c93d23c7e912494bb24a45928a6c944d6492691f956901ad48c172406ad202569052548291a4128d201448fc9b0024ce3d2bd1da568ecab0024ae386d91c36073e2bb9ed6e3448d1a02573dad4611b2302d91806c73dabc3d17a1e6bd0f35d879ae43cd4a1e4bd14250878af43c576244b9122508782f43c1761e0b90fb5c87cae43c149cf6ace7b4b8652d43295a1904ae7b4a85cae39ed1e0d8b50935c848ae4241720d8ad06b56835a741a53a0d09ae7b4682d28404d16024930123a81d224048da022bd0193480c0a404549cf4ad0013e73cad3f8d61fc4d8fe25473cabbe0d75f0492f823a7c11b3e0579f347af992a7cc933e0511f1288f805d73cab3c8d69ed2b8f23567912b3d4511e42acf213e795253ca919e528cf201473ca53b3159e14a0ecb567652d3b2959d9472ed34476ca03b4911d92ace794673c1fba4d59d268ce925674ca23a4559cf07ae814c73c1b80249dcd06c0084b681afb92915c928ad035d71c36340d5da04bee1b4570ca2b40975bf6d8df96c6fc3634095db869adc24e6e02f3720d1b9028dc05268122b651b1b28d0d94606cda0364951a046ed015f6b5a2b5a955ad48ad015d6ac3634055da78d8d3b6c69cb63404dda16d8d0b68685b0344901a14a8d012700423b3ad799d4babe45666d2eaf8d59968a8cb36c659aa32c1b17c4aec7c5a63e2b31ed598f69cc824463d2b2f8915898b4c4c56625ab314911894acbe23561c2e30c91d7c270c214d5f5233049117d28ebf34a5f9a32fc5197d24abe1340041faf31b1790d8b1b575d52eaea915750bcb19565c92eae4915630acb635a5b1ab2d89596d288b605658c1b2d4d716948eb182c59123aca5356526ab204658c120020ed5e6bcaf25d578aeabc1793f8acada5d56c2f27ed59578d8abc5455daa27e95d508b4a8456541ab2a4911504aca804e4fd1aa991b14c6d8a606c4fcaba90d6148690a403c4fc93a80979402baa0145505a82848c141288a01254fc2b0020dd3d0889d46c4e8b62741b1276ae9c35c4dd23a4e511314ba98a454c8a6a644d531068938564a1ad25c571286ac942564a5252529192928c9404449c1b0020cd250bc9195648c2b0020ad206d8903602b62b95ad6d1c48c8e1252b5ad2311b1182d88c06c2b5aba0d179066bc8335d419ae20cd49064bc87a5c43d2820c579062ba8315c42dae20c549084a0840504182f20c174ad6ac56b4b4052d2029590124a56b4a3fc2e15ad1cf58b47d35c3e8ae1f4170f58ac7ab563d5a71ea534f509c56b463cd281d4d14ea4927523a3bd221d48d8ea0bc758343ac0a1d4148ad4ac72b6c395b01cc900e54a85695738da415a51cad27e6db5636d2d1b6958db4946da4636ca315a4f4d90985693735c1f15a168d36b069a6c34d2a15a15cc56ba62a493151d18a8d8c52bc6523d32895194498c5288641543142e98c910c505a568562e5ad184170b96ac5ca562fca2172158b907c5d24a2e923174518b90285684a2ba2b16c940ae6ac5725a2b92b15c8e4af688581402bd2215c558ad08c008272a8b61541b0896ae5325d2992294c578894ac50b5a285ab142958a127c44a362712e9389149d2884e126224ab1341709948e4494c2412392a5349526a48146245251229189128c48126224a2114d688a6ac4525622ca21145588926c0081f2193610c1b0656ae4125d20922904178652ac3eb5a1f5ab0fa9587d07c329361e12e8f0914792883c0261942b0ec5707548e3284c1b1238e25347126a360461b5250da9186d28c36026194220ccd68666ac3325619ca20cc1586506c0081b185360c25b0610d80dc5717d36036d5c5b4b82d95c16c2e036d1c556ba2aa5d155228aa578550bc0da5613a2d0a49704e8ac273561392689c8d41b48c2135a125ae092570490b821356109a508d1604268c212561089f0840f81b46c1da5d0ed228764d83d2881d9260ec2f036558336b419b560cd2b06c510332ac199460cc1f0364d8284ba142450a09b05c5102824c1405e0a5280544c0292881402606c2b038d681c6ac0e25608ca20385581c28c0f25007c9803c5101c0ac0e03e06c1b00205c190a80aa6c05c2a02a5b0150d80135704cae02491c022480625d0312281a5340d26a060140082b006d68096b801b5600d2b0089280448c0214600c0a0040d8010260001f 10 11
def l_43 : Nat → Nat → Option Nat := unpackLinksF 0x73a039c05cd43e6a0735039595cac0e56072b03930bc902e480724038e11c700e3417180b8c01c600e204710038705bdd7de626f3037885bc40dde16e52b7203b882dc406e2036f09b780dbc06de036e83b740db80ed4236a01b443da206d1036707b380d9c06cb0f6191b0c0d8606c3036085b040d800ebf07581fab04d5806aa0b5501aa02d3c569d074d85a6c0d360697134b81a5c0d2c0e96034b01a541d1a468d034507a280d1406870f4381a1c0d081e7c233c099e00cec1676033a059a8acd20e670b338199c0cc626630331819881cc406620330839648cb206560f2b019580ca61e530329819403c90462493120188c1c4606210b0f078780c3c06142b0a018500c28060f1707818342c1a060d03058582c0c16060b0304078200c1006060b03018180c0c06060301877c52be205f006f8017c00bda1ded02f6817b01bd60de02ef0017800bc005e002ef057780bbc05de02eb1171cfb8a15c502e2037100b860dc302dd916ec0b7215b70adb816d81b6c05b506da816b48b5a05ab0aca2f6500b2415900ac8016400b10458802c30560c3b06058302bc955e40af2057902ba0b5cc1ae6057302b9815cc0ae215623eb1015880ac0155f06ad8954c8aa2155102a8815401a90454802a3054bd7a5e052e06940d4a00a4825220a91014841a3e15152a8a034482a220d1102888143c2a12350902840341c1a0e05060681094080a020d000680013f439fa04fa0e7d013e809f404f70e7a073b479d614eb02709538019bc14de026c0d36009ae0cd312698134819a20cd1026803330499804cb06650331c398e04c702620730439743cba025d012e8097404b12658812c409543ca906538529429345c9a024d01264193204970a4b8124079200490024705234191a048c06450520c78f05c78023b051d028e8046d1e36811a448cc1c6506320319008c804610e2e8917018b8045a0a2c8316408b20459022b07148489c244e0226831340896144b022485104887c1c3e021f010d0a8680434021a010bc585e042d0a16810b408541c2a0215010a028500428021401098284c042602130109808461c114a078503c081e040f02039101c080a1405020281014080a04020e00830040802040101fc12fdc17e623f301f902fc807e013f001f800fc007dc13df3def80f7817bc03de01ef00f6c37b40bda01ec82f6017b003d801ec00f6007a043d001e782f10b7860bc301e084efc277e03be05df00ef8077c03be01dd86ed467680bb305d884ec4076203b101d880ec407600bae09d38ee94274a03a501d202e9007460b9b21cd80e642704bb8201c004df826fc037e01bb10dd806e813710db880dc406ce536701b380d9c06c42b6105b080d8406c2036101af84d40f6a0035001a704d3416922341219f84cfc067c0b3e019b10cd806681334019a00cd0065e2b2f019780cb426580b28119010c257612030805810cc0805fc22fc097e00bec15f212ef297702bb025d60aeb017580ba425c632e3017102b8415c202e0056e08b7005b60ada056d00b5c35ae02d40d6a00b5005a802d10d6706b1c758a12c5015d94ae8157012b801590cac805620aad115680ab015560aab015502a98454c02a5055202a84354202a1014f06a6c35283a94014a00a500528028b254580a2c05083a830540849fc24e85a74013a009cc14e602710938809a874d4026a01350099454ca026501328098054c00260012f0497414ba025c052d0494c74905a480123049102488023d1d1e808e4446c1a35051a028d0046802310d16888b01458022a0914828a404520229011306888443c221e010e828740436121b010c84844841c1a0e010700810a40802040102007fc53fe01fd08fe807f403f419fa00fd007e803f011f800fc007e003ea19f500fa807cc23e601e148ef8477c03be01df00eb9075c03aa11d500ea8075403aa01d20ce88274403a201d100e41271c138621c300e102708038011c000e000700037c11af3cd7806b4235809a810d0106800336299908cc026600330019800cc006600320419000c704638031a098d00c6806340314198904c480620130e098700c38061c030e017f20bf805f812fc017d04b9165c412e2016f08b6845b402d8096c00b6005b002d801690cb18c58812c2095f08af8057c02be015f00af8057812b811551c9f2e4f8027811322898824bc225e012918940249822481124008f0c478023a091d008e0246042300117048b0244c322601130088064400220011000868642832140109048402420020e0903107e0e3e821f400f02877823b421da00e718730239021c410e2006e0c37001b608db006d0235841ac00d5046a0234431a200d1006706338019c00ce006586320319000c7046302318018a08c1105d0e2e8017400ba005a8a2d0115258a90054802a4014828a4005200288214400a2004c9226401320098044c002600130008e284700238011c008e00458622c0116008a0444042200110007f243f801f420fa007d003e021f000ea3875003a801cc20e600720439001c800d6386b0034841a400d2006804340019c10ce006604320417470ba005d002d8416c00b4085a002c8216400b00856082b0013c7088584400210410800801040001c8e0e4006a20320c18820c0106000300016860a440500828001304094104a0025001280088303c201a1000b20001 0x2f948bc4a35c25326a6912f446984a56bdd1b472577862ab5693d9b09aa42177850aace83d5701adf11b3836d984a5ce08b67021b26f2c9359348e52eefc9575248b79a359bcab0c61777d0aa31015dedb64de5715e0c8ad8344852eef09575148b7923518caeeee5555e0ac30816dd5b62bc173874bfc225de012bdf69575048b8ba3dbd91bde28d77f2bfbe15dde8abcda556ac27b351358dc93ef217f760bbba0575742ab380f55a06a8f8271800bed8da30b6c9abb54bbd1a428d33710987e34cdbca6616d1b6b68b3494ddc0a2d144e654262ac84ddb822af40e53c063b034484cae1f41736c8d9b5b64da9aa6d28d3056b97f35cd9e36616d735f6a1b326cd94b66c8583630d9b1060d81ae6ba4d35a069aeb54d59a25dc4d35a6a9aab44bb49a6bf193548a98536cbb1226bc4e35c269ad838d641a6ac4d35506975234ba51a6aed3b54685a9a5ebad1b5d08d3522bb34155aa49ecce4d60a24ba885d5602ab320f55706a79025d24b444e592c12890292484cae69c1734c6b82515c9a5aee9ad56272ada4155a989f4a64c85f0bba585521c0c8300473d2a90a35c1242e6929b3482c9a3954d189a4505721f2b9a246cd0db6684d83414d91395ccf0a86801b33f0c19e95cce89a66e0533a2a9601448109266e552bf28901924cf13257c952024691316cceca6672513380319b014cb83420e191bb08876824cccae1f4173316b82485c565aee64d545f2bb9815541c2b65a1559607c9d8322a80f02c04b220a87e35c128ae65c5b32d0c996054cac1a212171080b994c6cca1b664ed83264d99296cc90b020e173210a19105cc7c1a6380531f0a8dd0443b012638151b908875824c84b2370550ea2688306cc802663c1131d0598d824dc9afedad77686b7b0b57bedaaeb0d4f5068b73a36d3cafe94577452b79f157874aae6a54ebd28b5293fa209dccc4de5126700925cd02fe5e1772a0b7918574142ae3414db708aca83f5e01daac0dd39066748252a40f90a06c5e02e0a013c61af62f15b166ad86564bd6325e0992f88ab86355a90a6cca516bb27b8993565026aaa115b507b89035c322c620db2f74d98796cc383660a542fe0a18185cbf42860ad72132b98105cc0c2e604142fe6b97e95c3e82e61917b0b6bd8535dc252f61057b072bb8315c844aae0854aa327b32135c042f600176ff0b87c855bf0293260f55406b7d34ebe22c5ee9b2eb4a975244ba5225ead26f44bd74244bccaecc6556e427b08135bc82eaa6156db07a7c035bb8925da092ea29b31145b8c96c0e496e909aa9045b68169de096f069377a5ebb1295d6916e84895c145b889ec0c4d69f25b309256c822db20f4ee06ac782d54412c1c5526026971a44b8d2257716ae58ad72356b892b41c5185d09b708451700adbed720e2987a8545401a5b4912da488dac5ab722b5b6d5ad94ac2e94db60a29ea1185b02d6b35c3d42662916f118b586c57bee2b5f2d6af66af78b56b9d2b56e55ee629f7014db78a3c185169e27b2f9356c42bdba13ed709b6a8473d022b1c0f54f06a2d0177fd1b5a64da716c92f1349c5a3586956bc49b682457e89329c136cf08aa68359c5ae59a5b2294c9612547d892578d36ca68b14a46a1c9d4ba4d9fd24a7404db24229500744002aff46cb1db6452972c62d96286c7d4925804d2bf02961b4d9a1a2d8493ab846d6095eaf8a950c4ea5c26cfe1257c8925661345708a7282529c0e87e056b94a92d9449689a572d0262488f9934964925791b2bb8d108c64aea304c6d92b84a8fb9449609a0aa1903b028f8924539aed6ad54e84bb5a255acd22be0498550aca6036ac4b60aa172d16bf6735db31abcdad56cb4bf6425db112bc3a956bd48b5ba37a109d4ae4da3c254fd9277bc9356c17eb20bb580571502aa960dce404e5281d0e80ad280d2ae6bd56a5da8d2ad529169b46b49834aad2ed38956a748b51235a691a5240d2a046909a54a5c14547192a98a95436ca71b254ed529f4894ca34a98b652c0e29106948044955ae51e0d2a048950244a381254916aa38ad51356a85a753e95a8d0690995ca69225349129d8b54e456a6dab53295a972b94b247a50a6d1e5169226b47b54a49a251c4d29069547b46a38a3526d1a9128f46935ab22b554d5aa54af4f245a611ad2a0e28c0690a1449e80c5151b1ec4c9432547ad1a5125b27f2c9411549f89a4f2062770293b0149f4924ea052874baf6255a1922d0a57a7c24d3a0147a8925069767f4ab412457a493428d727d2893e944a01ad4fed5a7e4ad3e1569e9ae4f291de62a93a944794924ec535e628b3a9359dd23ce8519e424d44357a112b3c68da812ad3d9369e00c4e6052716bd3825d8452acd09166346b3795e788934dc174510ab3625d9912acce9161046b3595e780930a00d650261312347709240e8d1da24934c6c846324d1152646c933b54819224c28d1de2c92e15493c983b24926248931244964a24cb16a648ad31b569852b4b055a6029c270357cc9a4b24925a2892d23096da84b25125e4bd2e95d778aacb8515f726b2c1250f81acdb15a6a6ad3325783122cbe8d6572ad271307609334c15c4d08a71027941264aa512506b8f6954952364a69b24f4892916c914b2498552442692835c908aa4945124124927a47924a348049a4b2692513492ca6c845164a26b26a5d9152ac9891649269219449089a48c1724126921a4a9092348251a476b522b569112b480512516af27244920ab47e4da3d2bd1e2568ecab416d51e12891cb6c86db4422d92386c1083448292a3c4591e028917464825b23f25922e4ab0da4a8d5233fc555ee294ef94669016c68094a403a1c8158ca3645cd61fd4d91896c8c03644a172200a10a35c8a0ae448172284a10f8508952e448942206b90f95c1242e45d17a2d6bd1635d8adae422d562a6a514a5e89caf44c575ec274ef13688c2f444176210b824055878291460743802b07c54774aa410d5a1b4b50d25683d22bf05594908aa502d86412c1ed22172b90a35c84cae424172074890ac5a8462b420d5a0f69d032567dcab41c53a0d09a2284576c9a41694207468ee1547689a3e851207488f99448109a4060520a68b04a498211d40c8da052bd011527f0a2be4511eb274ec93668422ba80b44404a5101d0dc0ac004f9fe6b0fea6c7f12a3ea551f4488f99447d51ebb88d5f4254f99267c41e86c0d5d303a1e8157c4a23f4d75e26aafca497e11d3ee8d9f62bcf91447c02e86a155d205a1e02579c0a3da571e6028f51447940a3d4511e7494f3246794a33dcd69ec6acf5a567a4ab3d04f9e4028ee14476d223c2941da288ed940771a23b4911e28acf035677d2d3bc959dd472ec9560d02288411033028e994474ca2348d69d66aca534a755a33a8959d22aca40461081b3a0530420791bc578d9adc66d6a2f6af0eb56871a5c30d2a1668f063468052b3fe569fb2aef795678ca53b0519a00aea384775c1fba20f5cf06e208352800e864054d626ce6836585b228c0d16168cdea556d926b94915a929ae49456a09a9a2099616b8e386c44532378950cd048db34d711a2a22919a529ae19455dc1d28a0d8d404a4201a0c40b1ab1b1c16d888a5c700b637e1b0cc048dd0346e40a37ad355868ade24e6c91b35c5345728ad09256ec2f37014976074a203634c1299209083034180166cd2a28611142068d9b40549221940d141048db46c6d6341f3191b48c0a9b646c92a19c111400682b1640b00a190091a969ad7b456b92ab4a935ad48a2b14669c9b18e098562b8d586c6a6360a3191a86d8d396c0bc22344d502b028150146892006c5102e04814814695b6348da0486c8d1b606852a06a5902d0681401472dafb90d75c66aeaeb557152fb84975be4ae82a556dd22b628ddb02bed615d6a8ab8a8555a626ed01275d01d27e0d92405469027310131020682702cc2134679af33a975934aacca4562d1ab064d19b4bac625565d22b248d58a468c11346411a1f495187050c9c646662a330db18c6c8cbb5463d223128d186270c0934658363005113d6b8bf934641223209117e248ca45a64e2b324d599169cc7a565f49a1f41718a488c52446362d3191598b6acc4a5661c2e30c91d8429abf9456089aafe95182488bf124601a52fed197e28cc1a46604a3afa4959c8accd3566552bb1c9158846ac29385f09a1f81116a058bd46c304b22ec550c0268bc86c5bc322e41516e068b482c59c122cc0516d048b28145dd2e9829557648aba85e5b0132c8050bf048b9a5d5bd2aae4914be04c7e35c5b4222da511706b4b7b565b92b2d81596a6b8b4a472ec2a2ca110ba048b314d2eca2aca4d56748eb20462e4132f0d5d742ac5c1365c42b2d60d968058b1824585af2c0974f94aaac24554d1aabe574512aaaf05e2dc132b8975544aaaba453e11a8a04d55b0bc5a8264e0182a48d0b104877a342bc122b31b0f98c8ac454551b22aed50ee488a8a342cc322881513706057024549222a491141088aac5a5522b2a6d59514ac271355002b2a01394e8d828c64535b607c5114c0d8a5358115aa292d20342a8a403c3289a28249142288a123050da8282511464bca295d2ccaaa88514ce26aa01250bc1aabb1595a6acab2573d122a9e8d54b2ae2694551c93a7e15936060568264e0a627a111386b8610544f2362765b1372889d06c4b4322681512c0689c35c4a82a264111290489ba474c42325009933068990344cca6a545153226a9aa5d4b52aa6891531068958444b8ae2540d12906895a4a4a9232525192f6b496b564b12b250111396ae9b1444c02b24e0d9250bc9215648c2b1e6d50b608890b6c40db41f2d91206c07c3443c92a16e190b50888b4643c5b21a0191164aa81a4a475231be4b51c24a6a85530c25168118800341301646a3622cd60d44d88c96c460362205710b2a07e35c43cae212171104b887a5042dae094571080b884a504202822d179156bc8a35d44dae1f2d55126a488a5e438af21a5750c2b824155428a920e179060ba6083a2cc1b0fe0682502c7bc542c82a1e0d59034b4812563dd229c6514dd25a8092533c2b1eed20ff0b87e35c3ecae1f4170ef4887ec5a3e62b1f0d58f769c772563d8a688a514ce0ac7a84e2c01a1e6940ef468588542bc1a196110ef488650443b01a1d6050f268a78a493c11d1dc8d8e528a7012d110929da178ea0a469845324221800e8ae06c3f01a0900b1ccd50200280f8143992007a490230880f0143a1b61beda0486c873b603952a0784d0220c80e814375ac08ad50e36906d93c0842a0865101c02863044381ab1be968de4ac6ea4a371231b65184324c6285610c9e1b2130d707c6ab58351361a6950cc2a865a44328a21988f4b146a6592a328931900f42306a6301d0b80a990550c648868b5d2ddaa9a0924cf47467236334af192510c70ba110553141685a094bc0286105c2ec0a17e110ba0285f9442f125176918ba28c61b5a305ab180958be0ac5e83e2e40a162510b04885b2502bca2160500b168857a442de2b16ad58b44b459a562c91c95c5582108a8fc57479ada36d69176ae82b56411a5a00d28fe68e7a3463a52b1c855ce228e7093f3689e9b04dc4126a6b05a3482b988158b8094568461f00d036058490a84d03c28d3214e950a24685596c234b213c550992984b9442309a1541b0962684a93422c92150974a34aa53a45298af1284d08a24c49944064ae1244d09d28848934291ad146d58a24ac4e156240a21424f89d2484e94427d2e91a9549e48a4e1262682e13291c922a84a9442449212c5349228a4a93524d251249189128c4ba47250a3120498490b84594422ca211cd688d6ac46256228ab152d5ca54ac5023626cab1305308f288449361282a0ec0f0874d83f96420caa0fc4d0860d8348641e82a0ea13073088340341c81a0e20d0670484225d1fd2a906914820bc38034198130de110170b8370341e4220da0d0806b43fb561f92b0f01586c0883e83e1e4120f25107b4ba34a551e9228f0098762b83aa471b82a0e21106d0483914d1b8a28e24d46f494372461b4a30e691c7008c36026128ae0ce110672883535a1a5ab0d0958660ac42b57204ab0f84d8770ac3a04c1ac220ca0d8634d828a64141220c45b0610d80981017d36090990574a8222340e0b207e55037268128640c02a0480d0120202ea5c1152a09c9105c2b82d85c0d892046090596ba28b551612e8909545748a2b15e0d4930aa1782204c2925c14e2d0a3158506ac27a4d1152289c8d43e2ac1a1260bc2b0420984b6b82515c1242e08d1603d28817044131ad090d584769422b461112b0785584327c168561081f07a4901e0481e9441012e8709543f48a1f1360f0930761781d04c1b1440a42206c510396b41c3560dd2b06a5583428c140560cc1f05c49029048171440a9220544c02b4a0149440c52e84a9543048a179360b4930581782804c11944078220465101f4880f9300812803c510266b412b560912b0445582128c0e8560701f0c115c5e6ae2d3471512b09a9184146c1d1560c89b04e1581b06c0881004cae032150132b80b8540613602c5b0122480a86c0203201e150070680995c0142a01a1100404809247030230060980e02806814038a680a5140d26a0825d0212a81e9140c02803014025ae00a050040280324a015230085180a6b40435601d2b006050146ae0892402c2b0040db88697b9b47c6523e2a8fed446f6914babca3d164fe722772b1378f899c744adce24ee604b67c23af60fd620769f03749819a440acac04e4401f1900d83405c010260001f 17 6 11 10 7
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsF m_43 g_43 bds_43 (dagRefF 906 (dagTraceF m_43 s_43 8 f_43) l_43 0) s_43 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_0 : treeBlockF 0 32 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_1 : treeBlockF 32 64 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_2 : treeBlockF 64 96 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_3 : treeBlockF 96 128 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_4 : treeBlockF 128 160 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_5 : treeBlockF 160 192 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_6 : treeBlockF 192 224 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_7 : treeBlockF 224 256 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_8 : treeBlockF 256 288 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_9 : treeBlockF 288 320 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_10 : treeBlockF 320 352 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_11 : treeBlockF 352 384 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_12 : treeBlockF 384 416 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_13 : treeBlockF 416 448 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_14 : treeBlockF 448 480 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_15 : treeBlockF 480 512 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_16 : treeBlockF 512 544 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_17 : treeBlockF 544 576 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_18 : treeBlockF 576 608 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_19 : treeBlockF 608 640 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_20 : treeBlockF 640 672 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_21 : treeBlockF 672 704 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_22 : treeBlockF 704 736 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_23 : treeBlockF 736 768 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_24 : treeBlockF 768 800 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_25 : treeBlockF 800 832 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_26 : treeBlockF 832 864 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_27 : treeBlockF 864 896 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_28 : treeBlockF 896 906 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
theorem nj_43_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_43_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_43_1 h1 h2)
theorem nj_43_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_1 (fun _ h1 h2 => treeBlockF_at nb_43_2 h1 h2)
theorem nj_43_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_2 (fun _ h1 h2 => treeBlockF_at nb_43_3 h1 h2)
theorem nj_43_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_3 (fun _ h1 h2 => treeBlockF_at nb_43_4 h1 h2)
theorem nj_43_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_4 (fun _ h1 h2 => treeBlockF_at nb_43_5 h1 h2)
theorem nj_43_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_5 (fun _ h1 h2 => treeBlockF_at nb_43_6 h1 h2)
theorem nj_43_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_6 (fun _ h1 h2 => treeBlockF_at nb_43_7 h1 h2)
theorem nj_43_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_7 (fun _ h1 h2 => treeBlockF_at nb_43_8 h1 h2)
theorem nj_43_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_8 (fun _ h1 h2 => treeBlockF_at nb_43_9 h1 h2)
theorem nj_43_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_9 (fun _ h1 h2 => treeBlockF_at nb_43_10 h1 h2)
theorem nj_43_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_10 (fun _ h1 h2 => treeBlockF_at nb_43_11 h1 h2)
theorem nj_43_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_11 (fun _ h1 h2 => treeBlockF_at nb_43_12 h1 h2)
theorem nj_43_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_12 (fun _ h1 h2 => treeBlockF_at nb_43_13 h1 h2)
theorem nj_43_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_13 (fun _ h1 h2 => treeBlockF_at nb_43_14 h1 h2)
theorem nj_43_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_14 (fun _ h1 h2 => treeBlockF_at nb_43_15 h1 h2)
theorem nj_43_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_15 (fun _ h1 h2 => treeBlockF_at nb_43_16 h1 h2)
theorem nj_43_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_16 (fun _ h1 h2 => treeBlockF_at nb_43_17 h1 h2)
theorem nj_43_18 : ∀ i, 0 ≤ i → i < 608 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_17 (fun _ h1 h2 => treeBlockF_at nb_43_18 h1 h2)
theorem nj_43_19 : ∀ i, 0 ≤ i → i < 640 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_18 (fun _ h1 h2 => treeBlockF_at nb_43_19 h1 h2)
theorem nj_43_20 : ∀ i, 0 ≤ i → i < 672 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_19 (fun _ h1 h2 => treeBlockF_at nb_43_20 h1 h2)
theorem nj_43_21 : ∀ i, 0 ≤ i → i < 704 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_20 (fun _ h1 h2 => treeBlockF_at nb_43_21 h1 h2)
theorem nj_43_22 : ∀ i, 0 ≤ i → i < 736 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_21 (fun _ h1 h2 => treeBlockF_at nb_43_22 h1 h2)
theorem nj_43_23 : ∀ i, 0 ≤ i → i < 768 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_22 (fun _ h1 h2 => treeBlockF_at nb_43_23 h1 h2)
theorem nj_43_24 : ∀ i, 0 ≤ i → i < 800 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_23 (fun _ h1 h2 => treeBlockF_at nb_43_24 h1 h2)
theorem nj_43_25 : ∀ i, 0 ≤ i → i < 832 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_24 (fun _ h1 h2 => treeBlockF_at nb_43_25 h1 h2)
theorem nj_43_26 : ∀ i, 0 ≤ i → i < 864 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_25 (fun _ h1 h2 => treeBlockF_at nb_43_26 h1 h2)
theorem nj_43_27 : ∀ i, 0 ≤ i → i < 896 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_26 (fun _ h1 h2 => treeBlockF_at nb_43_27 h1 h2)
theorem nj_43_28 : ∀ i, 0 ≤ i → i < 906 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_27 (fun _ h1 h2 => treeBlockF_at nb_43_28 h1 h2)
theorem nc_43 : ∀ i, 0 ≤ i → i < 906 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := nj_43_28
theorem lb_43 : LowerBin m_43 s_43 g_43 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_43 sub_43 gl_43 rc_43 nc_43

def m_44 : Nat := 0xff00ff00ff00ff00
def s_44 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_44 : Nat := 0x1100150015005700
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 6, g_18), (m_26, s_26, 6, g_26), (m_34, s_34, 6, g_34), (m_14, s_14, 5, g_14), (m_16, s_16, 5, g_16), (m_0, s_0, 4, g_0)]
theorem kn_44 : KnownBin bds_44 := by
  intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_18
  · exact lb_26
  · exact lb_34
  · exact lb_14
  · exact lb_16
  · exact lb_0
theorem sub_44 : ∀ b ∈ bds_44, m_44 &&& b.1 = b.1 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_44 : ∀ b ∈ bds_44, canon b.1 g_44 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_44 : Nat → Nat × Nat := unpackForestF 0x169fe7929f3c14f908e7cc27de6019f209cf920fbc905de4039005a5f8a4a7c5053d4a51ef895f84513be247df02befc2277c08fa94a1dd93eeec0cf52547b425fdc144ed091f6806fb5089da013ea4a87620fbb105dd4851ea817f5c113aa047d501feac2275404fa90a000b47e9894f4c0a790473d092be8491f420afa1047c8238e789f73c06790273cc92fe6491f3206f99027c8138e581f72c0bb90073c882fe4411f2207f91027c8038005a1f1c0678b253c602ee2c1480292f894d9ba24bdd123f0a50785083ba246dd095f0251b81033ba129df4b66fa5537d031ba123dd015ef211b7905dba029dd4366ea15375059ba02300521ea517b7148ba9452dbe366a497f6c293b6049d492f6d4953524a7b2a5dd9522eca4a765053a9252d4895ebf17b5f8a5af95ed7c0cea44a75c2a9ae018d4891ea40af568bdab452d582f6ac0bb52053a9854d4c166a408c01477a8019d3494e9c0bb4d05200a33d2c14e904fb4907da4019004a5e50d4f43471a1938d0c9a650d2f412d99414bca0a3e7a9073d08394146ca09fe6cd4b366959b24acd92366c0a72827d9896ccc4aa6624f33103194133ca00de5a11b2d07d94019ca4366521532909994013004a1dfb17b2528b7ec52c851c6424e3212697eb53bf5a5e3d1b2fd2bf8da49c6c24dfa57b192a97e953c50aee285171427d8a019bf4a95fa4ff0b8bd85c52c2da9616d2b0b4bd85a52c2c14dfa4fb072a98393cc1c0c5fa4cefd03780c5ec062960217b0107d7e819bf82a5fc132fd0260093bbec14df04faf907d7c01900499cb117ef169178a48bcc0c5e2522f12892c45bbadb05d6982eb2d975960bac304b115ee569172a48b94a45ca512e50912c453b85a35c28eae10732c352b662f5bc512d98a56cb5eb65a95b28ead90732c34ab49a95ac8d2d269569246b491eda40a6584a563c5eb3ca258f14acd46963b52b1da558e97ac74a563a3db1c14cb092ac46c162260960afd84142c068b60049960af5769b2bb2995d93caec964b056eb58d95ac60ad5a856a942b50c12c157accae55a992ad2b956954ab4a655a4f2ad0312c153a60af5305769829b4c146a60a2d30512a52894c13da8ca25304b6a029950144a600d530066980314c84ca64225320f2990594c016960a9528d62944b14a048960a7d1c9728e2994713ca3ca651c062582973ec5e9f6294fa57a890313e9529f4a34fa4f67d25b3e81a9f40cd02d3a816853e8189f81e4fc0b27d02d2c14a9e9a44f49225828f3545e9dc1c4d514a756993535a9c1a84e0942702a1380509a9ab4d84f26c259360189a9a74d41065828d3414c9912a4c8532642793212c960a1cb006e5c6a52e34a971294b892a5c0bd2e0469600ccb2132590792c01300491caa4a2550492623394898ca44a64c07d26a329349f49c5124d2652602e00425c3ed4e472712383891c1a43ed2e1f4a721128908144840921f4971f8288fc1243e8ce3d0d90f84b87c23c72906392830f84687c1fc64d4a326951924a8c9234644a61f07d1686c8b42a45a0f22d0590f83387c17c4a94a254951294a894a344a4fa252650f82e88036440152200991002c87c1180210de68bd0e04579a294304e2180710c034799a9bccd2e132510982884c123cc94de6497072548381441c091e64670646c7982fc1292609292f305e81c2a3cc14e020bb010458081f4040b9e60a4f303f7e62f3f3149f96a4fcb4a7e52f3f2949f9252f303e7d42a3ea0f1f5058f303379817bd7179eb8a4f5a527ad253d6579eb2a4f593e7ac993cc0b9e70a8f384c79c163cc08c01076f1254788943c4091da466ef93177c94bb40f9db464ed93e76c993b40b8010668645f74da43a6521d5058e984874c2221916dcd6c0e6a60734b039a1b1cd0c08645771da438e921c7290e384871c2221914dc368ce1a3970c9d218d49bb8bce00446ee29376d79bb6a4dda396ec9d218d29b5498da9286dc2236a0a1b50488625b6c8143640910c4a6d78286bc1221892daa498d51286a8143540910c486d403467da934c0d19f694cfa5e68d2233e9499f494cfa4667c952188c5966a4ce134659a533449196462cb1466589eb2c4b90c2a4c445e64c2231114991268c4352621a531a9118d248c4231620af3105498827ac412e430a530ad81852c08605f60ca8300d1580292c01214302f2f65b17b098bd82c5ec0e21816d758d8bac605d5a82ea981752a0860575cc2e2da5916d0b8b68545b4262da0f16d0588605355918aac179560baab04d558232ac11565242ab04458c222ac0f55605caf84c57c222ac0b556058ad04c568222b40f15604aab84455c122ac0750c0a4a9358549242a45610c09ea615c5302629c1314c078a602c43025a751793a8a49d2314e82f28c0b13a0a49d0464e81ea740b93a05a9fb4e4fda12740b13d0789d0254ec122740750c0949bb484dca421811d238bc9a13848e29264d31236b496b504b52825a5412d0a091b564a41e2520b12903891b4e48ca0a464e5232629223848c90a18119210988e9544742623a0b11d0388604346da02180bd106a48834a4412d220909102bc88152440a5220519100a48804a4301721a1310d058860230041180517d054908294841c1e20a121050880145b3fdb01fe980ff2c07f86c3fc3000515cf96907ca483e4a41f2120f9088014533cd1c1e64e0f5088798383cc1a004d6cf007078034009a99da0e0ed0680134b3a11c1d04e0e807074034009a19c8918e447c7212a009291b9178e10886e4523712f1b8948dc47c6e12a009251b40d0d16a46c034345a51a2978d548868a52345251a2918d1254012323212919c490c84946612432119190518c827c6412d008a9175178c50885d45230c92174948ba4945fa442fc921748c8ba2bc5d1522e89f1744b4022945c03427da916c0d09f6945a12427d291644909f4945624e2bd1a158908ac4745623627d181544809f2bc5323029c9014c5109f2a45223027ca51424e0a12404f94627c968044c89c4c04e1600082f9349409568a4aa492549112c480950440105e240b61200f0900584801c0082d9151b08a8c04536022928114540020ae4405c208b2104170820a84104c2081e1040b0020a633a321fd180ce4c8670bc3385d19c268ce1186708a3b1221dc900ec088670883383e1c8260e41106707a3383c1b8260dc1106706a358441ac1a0ce0b4680883403419c0e8041486369031a5818cac00413c5d2b83004c174260ba0f05d0580104b1262f093148494642c230124990921785507824852124230920f84907a27b4e13da10920f04906a26034124168940d04903a0104a1192408c5200208e17c5e10d1c05f1484169817b5a0f1a80789403c2a01e0500bdab0700f0380581c01c0bda705e9042f47217a310cd1c05e48830470181200bc110041182d098149540a41e0520b029038010430992004c5000207e0db5a06da10369781b4a40da4a06d230365481b2940d85206c250040f8180780c02c00819806d480369401a5200d25006548032940185e030220180f00c0580601c00c290100f0080580401c00c250061180307a0182d00c0e8040c8010260001f 10 11
def l_44 : Nat → Nat → Option Nat := unpackLinksF 0xe609e600e600e546e540e540e486e480e480e3c6e306e300e300e246e240e240e221e220e220e201e165e160e160e0a6e0a0e0a0e081e080e080e061dfc5dfc0dfc0df06df00df00dee1dee0dee0dec1de25dd09dd00dd00dc46dc40dc40dc40dc40dba5dba0dba0dae6dae0dae0dae0dae0da45da40da40d986d980d980d980d980d8e5d76cd760d703d700d6a3d643d640d602d5e1d5e0d5e0d507d4c2d4c0d4c0d3c8d3c0d3a1d3a0d305d2c2d2c0d2c0d1c8d1c0d1a1d1a0d105ceb3cdc7cdc0cce7cce0cca2cca0cca0cbc7cbc0cb82cb80cb80cb80cb80ca88ca42ca40ca40ca40ca40c90ac8e1c8e0c864c822c820c820c820c820c6eac6c1c6c0c644c3b5c3a0c343c340c2e3c283c280c223c220c1c3c163c103c100c100c0e1c007c000bfc2bfa1bfa0bfa0bec7be82be80be80be80be80be80bd88bd80bd61bd60bd60bcc5bc82bc80bc80bb88bb80bb61bb60bac5b873b787b780b6a7b6a0b6a0b681b5a7b543b540b502b500b500b427b420b3e2b3e0b3e0b3e0b3e0b2e8b2a2b2a0b2a0b2a0b2a0b2a0b2a0b2a0b16ab141b140b140b0c4b082b080b080b080b080af4aaf21af20aea4ac15ac00aba3aba0ab43aae3aa07aa00aa00aa00a9e1a9e0a945a921a901a900a8e1a8c1a806a800a800a800a7c2a7c0a6c8a6c0a6c0a6c0a54ca540a540a521a520a520a520a520a36ea360a360a341a340a340a340a1cca1c0a1c0a1a1a1a0a181a180a180a180a180a1809fce9fc09fc09f449f409f219f209e289e019e009e009dc29d449d409d409d409d409d409c679c609c419c409c409c409c409c409b679b609b609b039b009a849a429a409a029a0099c299c099c0998299809980998099809980998098e596f096e096e096e09645960295e195c195c0958294e594c194829480948094429440940293c293a193a093a093a09362936093609303912f9120912090a490a090a090629060904190409040904090408fc48fc08fc08fc08f638f608dec8de08dc18dc08dc08da18d248cc38cc08cc08cc08cc08ca18c818b2b8b208b208ac3871e86e186e086458640864085e385e085e085e085a2854384e38483848084808461838783238320832083018227822081e280c980c080828061806080607f877f427f407f407f407f407f407e487e407e217e207e207d857d427d407d407d407d407d407d407c487c407c217c207c207b857933784778407767776077607741766776037600760075e1750774a374627460742272ea72e072a272a072a071c771c0718271807180718071807088704270407040704070407040704070406f0a6ee16ee06ee06e646e226e206e206e206e206e206e206e206e206cea6cc16cc06cc06c4469b569a06981698068c668c068c0686368606860684167e3678366a766a066a066a06681668065e565c165a165816580656164a664a064a064a064a06462636863606360636061ec61e061e061c161c061c061c061c0600e6000600060005fc25fc05f255f205ee25dc95dc05d825c4a5c405c405c215c205b665b605b225b205ac35aa15a815a425a2159e259e0580f5800580057e157e057a257a057a057a0562c562056205601560055e155e055e055e05583558055805580558053ce53c053c053445340532153205301520851e151e051e051a2512451205120512051205120504750405021502050205020502050204f474f024f004f004ea34ea04e244e014dc24dc04d824d804d804d804d424d404d404d404d404ca54ca04ca04c624a704a604a604a6049c54982496149604922490148654841480247e147e047e047a247a0476247604741474047404702470046a346a04662448f4480448044044400440043c243c043a143a043a043a043a0432443204320432042c342c0428242804280424240cc40c040a140a040a04081400440003fa33fa03fa03f813f613f413f403f403f213f203f203dcb3dc03dc03d6339be38c738c038c038c038a138a0380537e137c137a137a0378136c636c036c036c036c0368235883580358035803542354034a534a0346233493340330231ca31c031c031a131a030e630e030e030e02f6c2f602f602f412f402f402f402f402d8e2d802d422d402ce32cc12ca12c622c412c022c002a2f2a202a202a012a0029c229c029c029c0284c2840284028212820280128002800280027a327a027a027a027a025ee25e025a225a0254325402502250024a324a024a0248124802480230c230022e122c122c022a12262226022412240224022022200202f202020201fa41fa01f811f801f611f601f411e481e211e201e201de21d641d601d601d601d601d601c871c801c611c601c601c601c601c601b871b421b211ae21ae01ae01a831a801a0419e119e019c11982198019801980194219401940194018a518a018a018621860186018221630162016201620158515421540150214e114c11425140113c213a113a013811380138013421340134013211320132012e212831280124212401202102f102010200fa40fa00fa00f620f600f410f400f400f400f400ec40ec00ec00ec00e630e600e220e200e200de20de00de00da20c2c0c200c010c000c000be10b640b600b600b030ae10ac10aa10aa00aa00a810a800a800a800a80092b0920092008c308c008c008c008c008c008c008c008c008c008c008c0084408400840084007e307e007e007e007e0064d029e00330001 0x1b2241dc91ce26507262737b12380420c3a0e5d804685013bd498fa04a6f2242eb831f3c14ba8086f4465e693ebc899212087cc032830117589921048bca07cea032f241720c08bce473e5939bc091f900e5d204682013bbc98f8c4a6ec242e8831f1414b9a087c2289df844f0c95f8248fc0057df02340c09ddc8cbbc27d7613240810f76064ff023dc144ed4227724bfb7246e8023ed80df6804dcf26480922ec81f39a0cbb105c7f822eb822756112eb247d782feb411f5807faa027e2251ef528774547b32a175123ec028f52141cc0467f013ba498f4e4a6e7242e5831e9814b90087a4257d1923e8815f4208cfd02774232e7c9f5ce4c8fc043cf0193e808f384bf9b246e5023e680df3204dc92647d922e5c1f3900cb9605c7d022b9491f280bf93047c901fe4409ee0927a5473d0238c90a4f3a4e7982717212386c24f2a0e790070e30233e0099ee0878e0327a0113d8917180b8f4045c6929e2c149e404f676a9c4a6cd9d246ced3b22293c3141b8c90c3212785082e2821b89205448c3324a591a4ac88a570451aa225ae2031e040c9e2046a325151238dfcb66fc5533a299be81870ca02ac4c2e146316952868a543212b7a08dbc82e3c4112ac07558050ab138ddc366ec15236099ba82ce2125ec892b8748fc2246d18a9e4052ee0263c192be0094ef848e972432505385c25b840c77b057bc029dd011aaa084ef027b7a5db7c98ec44a68c242e0831d6414a940877148b6e931d8494d16485bf063ac02952410edf1b3684c1b445ddb4a4e88506dc243b604992020b7c087686d9b5254da12eece916db263b3129a2090b7a0c765052a2821b692050a8c3628bdb0c52d152961092b602bda2152a1496b780c75f032770119b49450a8e35d2a98714cd700c3765013a261acc5ed62295b28c6492a4fa94ad5c2f49014b5605c770224e80ea520a13a271aa0547f0266a60b3728bdb8452db92fed697b694a7b2252d08a9e3e52ed8263b192bd7894eb648e7c2432305385825b740c75a057aa829d4811a72084ec02675821d400c9d2044ea245a702e3a41169e4a74d052738136e418e960a5b6042dc132d241f36c0cb4a27cda033d200cdae903324719d14cb58985aa903454719c94cce09e6884e34326944130c592a6825b3162918b34ece124e7c906d42450a049cf4209cc046d348152140ce9a9672d2b384959ba46a911ee6c0a5b304272811a949e548933342d999954cc89e662060e426033920b491944054a152950a04acb82365a0f9b30643381d1a40c0ce4a32b0d995054ca4264540f3466a7a134bb451968052f132959f947cf0a36764ff3527d98133a5c9948a14e12096d883338c10e5e06f2c0339401319808da08cb1e2bb8893ea30991c4087040322d811b391964a5171027d4593238010e060645a02366930b31206468e30f2998613cc889c6424d28826165a40c211c61c5331e8d98b960c5e2ee389270c48365122c6c24c86104df0238ba6cc64aa5928cb172bb8b145c549f5104c8de0438a01915008d909028628188c5ec422961ed4b0e69586a5ec312950c8f70b052d802137408cdc4f28649984954c209e60e060dc26024920c122f60714ac74652215279ca560417a430a58083e6c0190920743803024928bfc2a5fc131ef0799345ec9229640d4f1f69763232c74afe3457b182a789952c489fe144fb062673e13290429c2212dae0666d821c140de00066fd026240116b418df60a5ab042d6132be41f3560cafa27cd4833be00cdb6d42df69164a50b41244f0572882a146148bcc0c5ead22f44913a154bc8a45e251272289389449cca24e0512ef6c177260bb4b65d85826f28975860b792459e522dd6b174b48b392c5d09228b2b173948b98a25ca122db69571b46b5d2959892ae24756295dadcaadc20e56b0626c8219840c82c046de2896fc5eb76295b8d7adb6a56aa52b2d255b48ea9629b3d945b641ca900c4d70433001905408dac8d2d76a56ab4ab25255a891ad347b6215dad8aab4e0c6d20524002197c0c828046cf28966a34b422f59d14acc6a565b4ab292f59294ac847b4a94d9e8a2b4a0c6c70522c8219780c826046c56c162260af8b4554582c20a15dc5eaaa2ecf0d36c168b6004990020b48084d6023599549cca2018062be4d95e94caf09e5764b2b98d95c460adda856c942ab2d959150ad430566572aa4d959264ac4ae560552af2995713cab40c4e6512a10314e014a949e5464b2a00314d81468c109aa046a52894d014a8ca2532052a129950144a70265361129a0794c82c0300e55657aaa2bb5494da20a555051aa728b53144a909ed444b5a20626a021a7c0d53c0669d0314c01602c08d2cd62954b149158a1ca252812268289478189b8a24da5128f29936144a492e4d6952912994813ca380c50406275289408189cca25120626e2893f8149b4a24fc0526c2894134ea05a14fe0f27e0580401ca322f51714a8a2bd44152a1ca34d65168627b4292d684189a60868403541819a000c4fa058070233db489e9244d65226728139b449dc1c4ead32736a1392509c4a84e01426e2793692c9b00c4f117a768a53a35a9bdab4d6d3a6469b078499a820c200e5e4062d002134808cd05300803133a54998a64ca4f264258cf940344980064800c09004040985a94c0d2a5f4a52f24a958ad3c650a5d0bd2005283c254b81180303a01928968264b20f2f68bf7845bbaa2bdc914ee06a56c34ab452958c92ac32bf5f95eae8add6855eac2a74b952a4ca7d1a52e7c2953c9479a4a34c650e540b71f05383425bc210d9e062680219880dcb606658026010110300a4ac4a2530992803c934164aa092532632912993490c9c5100c0312823293c9f49a4ca544672883e9301733a5022d2711b04c67018336502492711a84c8d01e4900e247068a283033c984404a22a07867020334984884a2290791402c90c1448409054040cd03033010332500cb260091205ac201000c225059200288fc12016082042a91e86c81024408d3a344931d2418a0a4c72505980446501265ca02c4102366a51ab4a8d1254669196247b191298949099204963078b114c8c03645e1522e0791682c320980d40c22a4a514a4a8a0a544e51a2627d129321a896b2c0c86c0583513c88c36444152210991002c929a9c8cd2e454a720a4b8f919b2a4c8c72451e04b8042547611e3808d1b83f8c41f4580cd550651582f8901743e08c66044ca13231891418175ff07ca50327c8170b6089922646212287022bfc0f949064f882e168113220c1902810d1387f4263f40f2190710c0345141831e501f5270fe04c30c101844c215250f803c7b4164280a2130482a020304983ce4a1ef078c71303009031a0c0bf04108254630a017c4c011240a4040164183d60b20f0510702401c104191b2050c102c5d82924bf490609292f694162c1117a04a052d9038546289917848a050bb0204580c1f28a0ca0205c2a022624a0286101ff8bcff4527f5a93f8d29fb4bcfd25250d1ebf24a5eb2425d8124ac1e286531f70a8fb03c7d4161744c04b060f945e7c6293e0949ef494f715e7b4a93d84f9eb2642592d620190720b04b278f48547a0263ce0b21d8bd0dc5285da9c2cd2e124a708a4b83519b0e4c8b92450585f8202f40c14e010a50003f7e01f3e80cd39064f982f7a8173cc08c48044040147912a3c64a1e0098ee83c76c163c4091e0262ef92976c90810061dd464ee13e76c993c28cdde07ced02e6f5a8382d218a2a0ca1484d42e28a1414a090ea82c75da43ac521310a8ea04874c2225e1112e088968444c0223a2d81d04c0e79607383639a1812c088e024864c2437ed61cb690e5248648ac392521490b0e404871c2237ad29c568ce223968918b3a54990294e193a2dc9130c175770aa8c82e05811380111c18bcdfc526f9af37ad49bc472d0a3166ca931e529bb2745a92255026a701151805c0a8226dc2201a0b1b9498dc12845c1e36c0a1b5048d42302d01034ed01a2480599301f8900280c114058d98286c812016081a646059020695a0342900b12602b9204982a0260c113058d80286bc1200e08009058d6a4c6b09424a15116078d58286a8120fe4c1a80682c1304902234c0d0b02405792068d2215c4c0ad260c71382b09034ed49a5694d225e68929342929a048ccc952630a51564c19f254c005e5ac292901292308c8d83d6709a0fe4c19a248ceb5266da53328c58a294cc14665c9eb2c4b87e244c285d5d42aa220b812044c98446449a31c91058260c69246522f325149906a4c7b4a63118b165798a2a4c493d620970ae4895209a9b84544017022089866c0c29605f8342d2181832a0550205ee2f2d31753569ac1345604a4a2850580242548125cc2a2601100d058bf16c5f4262f80b17b038bcc6c5e2302eed41764c0ba9505a8362e4141730b8b496c5c8b22e2171700a8b784c5b81e2da0b0a8260b28444c0222c00b15c048b183c57c162b609158038538205949094c04963088ad024580262be1115c098ad8445681e01a0b157038ac04455c122d68c4a5244b505e5a42ead013545094b384659822ac81116207ab082e57816aba0b15904a058225580eaa8d6153490a91585402c28811121088a702c4ac2229c1312a08894844540ae2505514f098a683c530162800b1320889f82c2909826011146058958444f4122541114069c9fb424f41e0120b13b038948444ec12295179498a4a423128c9128e179450a4a20464a022a860f54205ca082d4f816278094070449d01d4e1a426e52128090900404c1a22684e132698983504bd2825c5412d0a09583c4a81625207124460510204911c142081358bc99c524c5ad258d592869c8eb4d44ca4a4e505262729293148c90940049210980482c480aa23e1311e0588e81c46da013e4c004060069240249201a520092808cb52461a522e969164848a95e450a92265291228c0212d44429220128042788704c434163b117dd28b6e645771a29b84d49ba694da25b6c529b5c92da9486cf231654a930e5289e244c205f5fc2f2f416d740aeb6053554292a213d4b0969c84a4d823a441191c0868d02f43c1721808c020446f25038924178540c62902205c150280b61210707884a48420a408015106090828440f82207a1103c0881f84440db0204981012c08006c3fc30076110e1290628483f5a41c0960fc490621583eca40b4160fa0907c8443d42201c0f0f74707b138090261e80e0f30686d1302e0181b2900d44605b9402949802c10021078788383c01a0160c0d82605b03035d201a68c0b5280519300d42a02a10020078770383b41a00e0c00a07875a383a89c06815023098748383a01a1bc928e648c72a3e3511919e548c2294599323909513a1748b0aa0f03e050191c2110e28bc7045237d2f1bc948dd47c69a32334a9182528b12646e12a1902688e1141d07c098322a0981b40d0a4260198443601a160480af2406aa442b89815a4c0c027056120365a91aed28d64bc6a25234d251a4918cb2a45f14a2ac981a24a8970bc40052164250641182707a671242a098198490cf4a466a4a32d19178528ca28c6493e294991904b49c0ba450550701f0240c8c508861924301221484c0bf2486345e31229184948c14945f2322f4af178548bb27c519322e8968c61344608a0d83e0441915c8c0b806856a300c42216c0d0ae4605a1242b518144510b224857a342c12715c908ad474562362a8a7150508a427450936258270fe10858074180362a89014e4d0a724054230298a21488c0a2270509202dda916ad28b34a458a4a2ad18152578a52a45194a280a313e4b4950bc3f05215c2505e1182607a4ea60270b01261a07c0c04d2502581012c480908bc3e45d111a6932d149849210a4125c9112a088880a81f8440381e1265b0920784882c2400e11d1b08d8c04636022d281145407d0d8438502202e0f85b0872c84305c2142a108130830784102c1fc980f0110770683fa301d82207e11073078378341c81e0dc0d06c0583481c1dc100ee480782443b0221cc260e41106f098370440381e0d60b068038360441ac1a0d211068068402321f8990fa1787c0ba3d84d150250f41187908a3a8441d01f0e20f4700783683502c190d40b46703a32b481912c0c6560610b0298440b4220c00f0600981d0440e422070110612b81b95417c260bc0f05d0582803c1042209e0f0582602c2300fc220aa0f03a0882834e13da10140f04c0582501c0e4220980d0380882503416e2f0b5148594642b9321582f0a81485308c1b8451481f0a20f44e0782683501c190960b44903a23a48118a406e1202c0801fb4410d1c082d303f6a01f2500f4a80781403a0781c82c0e00e0664c03106019a380c0100628e0302402245e10a29080d683b6ac1bb4e0a5a6840924364821aa390d1188644882f0441684c0281e0585502b0781502c0a40e04e90026280028400391a0148d00e49005240091ad046d08224bc10a520812503e9180547a0f152074a50381481b0940294c0641e0300b00f0880703c034160180700a0780482c0200e02cd48156940a25204d25024548112940805e02c2900e1280608c0283d010168060750a8be8245b3fa2b9f114cf26b677b533b1a59ced0ce34a46da4a3411918e548b92944f13226c2f9281788f0b644857204298cc1486209e2e04b1202508a11c2e08c140430941f8340f81706601032f45a7f8ed2fa868fc7b43e2925ee690f51477a6233d1ca5e4e50efc2777b93395c91c9612e1e086f283b76419a1608c010260001f 16 5 11 10 6
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsF m_44 g_44 bds_44 (dagRefF 978 (dagTraceF m_44 s_44 8 f_44) l_44 0) s_44 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_0 : treeBlockF 0 32 (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_1 : treeBlockF 32 64 (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_2 : treeBlockF 64 96 (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_3 : treeBlockF 96 128 (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_4 : treeBlockF 128 160 (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_5 : treeBlockF 160 192 (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_6 : treeBlockF 192 224 (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_7 : treeBlockF 224 256 (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_8 : treeBlockF 256 288 (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_9 : treeBlockF 288 320 (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_10 : treeBlockF 320 352 (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_11 : treeBlockF 352 384 (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_12 : treeBlockF 384 416 (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_13 : treeBlockF 416 448 (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_14 : treeBlockF 448 480 (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_15 : treeBlockF 480 512 (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_16 : treeBlockF 512 544 (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_17 : treeBlockF 544 576 (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_18 : treeBlockF 576 608 (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_19 : treeBlockF 608 640 (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_20 : treeBlockF 640 672 (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_21 : treeBlockF 672 704 (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_22 : treeBlockF 704 736 (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_23 : treeBlockF 736 768 (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_24 : treeBlockF 768 800 (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_25 : treeBlockF 800 832 (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_26 : treeBlockF 832 864 (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_27 : treeBlockF 864 896 (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_28 : treeBlockF 896 928 (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_29 : treeBlockF 928 960 (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_30 : treeBlockF 960 978 (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
theorem nj_44_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_44_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_44_1 h1 h2)
theorem nj_44_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_1 (fun _ h1 h2 => treeBlockF_at nb_44_2 h1 h2)
theorem nj_44_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_2 (fun _ h1 h2 => treeBlockF_at nb_44_3 h1 h2)
theorem nj_44_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_3 (fun _ h1 h2 => treeBlockF_at nb_44_4 h1 h2)
theorem nj_44_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_4 (fun _ h1 h2 => treeBlockF_at nb_44_5 h1 h2)
theorem nj_44_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_5 (fun _ h1 h2 => treeBlockF_at nb_44_6 h1 h2)
theorem nj_44_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_6 (fun _ h1 h2 => treeBlockF_at nb_44_7 h1 h2)
theorem nj_44_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_7 (fun _ h1 h2 => treeBlockF_at nb_44_8 h1 h2)
theorem nj_44_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_8 (fun _ h1 h2 => treeBlockF_at nb_44_9 h1 h2)
theorem nj_44_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_9 (fun _ h1 h2 => treeBlockF_at nb_44_10 h1 h2)
theorem nj_44_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_10 (fun _ h1 h2 => treeBlockF_at nb_44_11 h1 h2)
theorem nj_44_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_11 (fun _ h1 h2 => treeBlockF_at nb_44_12 h1 h2)
theorem nj_44_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_12 (fun _ h1 h2 => treeBlockF_at nb_44_13 h1 h2)
theorem nj_44_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_13 (fun _ h1 h2 => treeBlockF_at nb_44_14 h1 h2)
theorem nj_44_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_14 (fun _ h1 h2 => treeBlockF_at nb_44_15 h1 h2)
theorem nj_44_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_15 (fun _ h1 h2 => treeBlockF_at nb_44_16 h1 h2)
theorem nj_44_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_16 (fun _ h1 h2 => treeBlockF_at nb_44_17 h1 h2)
theorem nj_44_18 : ∀ i, 0 ≤ i → i < 608 → (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_17 (fun _ h1 h2 => treeBlockF_at nb_44_18 h1 h2)
theorem nj_44_19 : ∀ i, 0 ≤ i → i < 640 → (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_18 (fun _ h1 h2 => treeBlockF_at nb_44_19 h1 h2)
theorem nj_44_20 : ∀ i, 0 ≤ i → i < 672 → (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_19 (fun _ h1 h2 => treeBlockF_at nb_44_20 h1 h2)
theorem nj_44_21 : ∀ i, 0 ≤ i → i < 704 → (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_20 (fun _ h1 h2 => treeBlockF_at nb_44_21 h1 h2)
theorem nj_44_22 : ∀ i, 0 ≤ i → i < 736 → (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_21 (fun _ h1 h2 => treeBlockF_at nb_44_22 h1 h2)
theorem nj_44_23 : ∀ i, 0 ≤ i → i < 768 → (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_22 (fun _ h1 h2 => treeBlockF_at nb_44_23 h1 h2)
theorem nj_44_24 : ∀ i, 0 ≤ i → i < 800 → (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_23 (fun _ h1 h2 => treeBlockF_at nb_44_24 h1 h2)
theorem nj_44_25 : ∀ i, 0 ≤ i → i < 832 → (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_24 (fun _ h1 h2 => treeBlockF_at nb_44_25 h1 h2)
theorem nj_44_26 : ∀ i, 0 ≤ i → i < 864 → (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_25 (fun _ h1 h2 => treeBlockF_at nb_44_26 h1 h2)
theorem nj_44_27 : ∀ i, 0 ≤ i → i < 896 → (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_26 (fun _ h1 h2 => treeBlockF_at nb_44_27 h1 h2)
theorem nj_44_28 : ∀ i, 0 ≤ i → i < 928 → (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_27 (fun _ h1 h2 => treeBlockF_at nb_44_28 h1 h2)
theorem nj_44_29 : ∀ i, 0 ≤ i → i < 960 → (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_28 (fun _ h1 h2 => treeBlockF_at nb_44_29 h1 h2)
theorem nj_44_30 : ∀ i, 0 ≤ i → i < 978 → (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_29 (fun _ h1 h2 => treeBlockF_at nb_44_30 h1 h2)
theorem nc_44 : ∀ i, 0 ≤ i → i < 978 → (dagCheckNodeF m_44 g_44 bds_44 978 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := nj_44_30
theorem lb_44 : LowerBin m_44 s_44 g_44 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_44 sub_44 gl_44 rc_44 nc_44

def m_45 : Nat := 0xff00ff00ff00ff
def s_45 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_45 : Nat := 0x17001f001f007f
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 6, g_15), (m_17, s_17, 6, g_17), (m_19, s_19, 5, g_19), (m_25, s_25, 5, g_25), (m_27, s_27, 5, g_27), (m_33, s_33, 5, g_33), (m_35, s_35, 5, g_35), (m_3, s_3, 4, g_3), (m_6, s_6, 4, g_6), (m_9, s_9, 4, g_9)]
theorem kn_45 : KnownBin bds_45 := by
  intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_15
  · exact lb_17
  · exact lb_19
  · exact lb_25
  · exact lb_27
  · exact lb_33
  · exact lb_35
  · exact lb_3
  · exact lb_6
  · exact lb_9
theorem sub_45 : ∀ b ∈ bds_45, m_45 &&& b.1 = b.1 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_45 : ∀ b ∈ bds_45, canon b.1 g_45 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_45 : Nat → Nat × Nat := unpackForestF 0x9325f9325daab6caaa64aaa54aaa449325ba746ca736ca716ca7160a706ca706093257a625ca3b64a3928a3924a3828a382493253a2058a20549315f9ea6c9e9549e9449e8189f15c9e8149315b9d46c9d36c931579c15c9ba64931539a1589a1549305f9696c96854968449682c9705c968249305b9546c9536c930579405c939649305300b479224600a4b89b5f89b5d8f26c8f1608f06089b578d34e8d25e8d25289b458c1348995b899538a8348985b8985300a4788a5e87b5687a5600a3b7245b7245a84a6c8496084860724577cc5e7cb5e7ca5e7ca5d7c95e80c5c80b5c7c9527f05c7f0507c85e7d45c7d35c7d15c7c852724567ab497aa5e7aa527235679a4e7225a77c5877b6c77b547225775b4975a5e75a4472256749347214b72143730347204b7204300a3770d687095c6d3476f24d6f2356d1466db4a6db466d1360094b6c35d009476ac6c6a96c66b5766a5668a5d68a45669566735a67356669360093b6545a6515a009376426c6045762b5d62b456025660c5a60c5660b56602460092f5f4570092b5e360564575d2465635a5ba5a5ba565634a5a34a5a1465615a58b5a589565614a57b475603c56b4756030009275516c4c45753b5d53b454c1565234f523474c1545045a50456503564c1464eb4b4eb474c1444db474c0184cb474c014009234ad684a85c473474924d492354704647b4a47b46470360084b4435d44c6044c5844b6c441370084742c6c4286c3eb573e95640a5d40a453e8563f35a3f3563e8360083b3b45a3c4603c4583c36c3b1573b05a008373a26c3645738b5d38b453625636c5a36c5636b56362460082f354570082b343602c457332462c35a31a5a31a562c34a30b472c13c2fb472c1302e34a2e0462c05a2cb5a2c8562c04a008272b06c2245729b5d29b45220562834f28347220542645a26456263562204624b4b24b472204423b472202c22b4722024008232116c1e4572035d1e1561ec5a1ec561e1460081f1d06c1a4571c35d1a0561ac5a1ac561a0460081b19457008171806c014571706c013571605c013471535d012561445a0124611b5d123481225c11936011560f45a0fb480fa5c0f156011460e05c0db47011240a35d0a3450a25d0a2450a1360a036010560645a06456063560624d0623506156060560104601b5a04b5c01b5601b4a0345801b4601a5601a4601036008130001f 9 11
def l_45 : Nat → Nat → Option Nat := unpackLinksF 0x8409070a0d0c1a0834106820924120824104820904120824100a201040018001000200040007e10fc01f803ea37cc4f981f303e607cc0f905ed2bda07b40f50dea03d217a02f401e803ca378c4f181e303c6078c0f105dd2bba07740ed0dda03b217602de71bc037426dc6d991b3036416c42d615ac035806b00d395a7034c16980d301a50b4a0659ecb01950b2a064c4c80d8c2318062c2c505852b0626044c0818102fe25fc0bf817c1af805f00bd097a02f405e80bb8d6f42de05bc0b7816a2ad405a42b4816902d205986b3016602cc058c6b181620ac405880b0856102a4f5480a9014e229c05380a5114a029405204a19541127a44f409e8139227204e409c8135226a04d4099892e2a5824b009411280248449009201211a420484090811e1a36346c08d051a022c44580898d13022604406880110021c2438087010c1218042c285810a0a06740c07e98fd01fa03e867d00fa01f023e007c00f801ea33d407a80f311e603c827900f109d473a807500e621cc039807110e201c4038046d94d911b2036026b84d3219e433c06780cb2196032c06580c7218e031c06288c0297c22f805e84bc097042e005a10b4016042c005800ad195a02b405680aa194e329c05304a60144428804f8c9f013e027064e009b0936026824d009a0130226004c0096111e723c044988901120218643008601082210042008401023204040807f10fe01f823f007d08ec71d803a087400e421c8039007010da31b4035886b00d221a4034806710c8318c230886008b6516c02b905700a641482278c4e08963128225004a0090211462204440088010841f8c3f007c10f421e803d007a00f401e803d006a80d401a8035006a00d401a8035005a80b4016802c085800b0015842b00560094c0d2c01c8001 0xac26882a648da447b23482a56aba55a6254ac36caba64ab254aaa44a9c6ca936c82a5ca5a50a896ca8160a786ca7060a625ca5b648d3547ab448226ca5128a4924a4028a3824a1168a2858a20549c1549f0149f15ca126ca0954a01449f8189e8149dc6c9d36c9b9509c15c9ba649a9589a1549906894054970149705c9916c98854980449782c9682495c6c9536c938509405c93964ad25faca5daa25ba6a577c255a32538ca457a235a195f9e15b9c9579b1536392f5f12b5d927549239985f9605b94857930533982f3502b338272a8232081f1c81b19017178137934692246833648e3547623483346782356b1394303980b5c7db5c78c6c8335c9026c8f9608f0608e34e8da5e8d25277a3575a348c1348a8349135f90b5d8eb577c3558cb458823a77237752368b95b8b1536a13b8a05b898534203b1681388a5e8835687a5683d647bc6476a6483b5578a55711594b059814587e45883c587836c85a6c8516084860811507e050809507d8507f85c7d0508145c80b5c7f05c7f85c7f0507e45c7db5c7d15c83c5e8335e82a5e8225d8195e801527e85e7c8527bb497b25e7aa5277a4575a4479a4e78c587836c77b5476b497625e75a44749347303486c5b8645a844577c4567a3567925a77257752567015b7414b739434a05b7284b7204315813715687095c6d9546f1446fa4d6da456f2355a1266e34a6db46703476524659a366e9466d1363c035150116c35d6993a3b837148116b46c6a96c67164689546925d6725568a455892667b5a673566a35769a56582366815666936450551401165c5a6515a44057138116426c6126462a5460a446335d6135562b4561c5a6145660b5663c5762256602465f4575c3685e3605783c568305c24a5d2465914a5c25a5ba565a95a5ab4a5a1465935a5895657b4756b475dc575cb5a5b34a5995a5814a5703c560305516c5096453954501444d8184c8145435d50b5553b4552b4f523475145a50c56503564f34b4eb474db474cb4754c5753156519544f9464e1444d0184c0144b5684a85c478544904449a4d47a45492352e0264834a47b464a3473b1462d93648846470364493513012128101201045c604545844b6c118104635d441374183a110124346c4286c3f064408544125d3f25540a452c8263fb5a3f35642357419562c136400563e8363c95510812100100f8103d4603cc583c36c0f0103dc5a3b9573b05a0e8123a26c3726438a5436a443935d3735538b4537c5a3745636b5639c5738256362463545732368343603093c2f9303224a332462d04a3225a31a562e85a30b472fb472eb4a2e0462d35a2c85633c5732b5a3134a3013c2f1302d85a2c04a2b06c2686429854260442382c228242a35d26b5529b4528b4f283472745a26c56263562534b24b4723b4722b472ac57290562785425846240442302c220242116c1e9642035d1eb551f45a1ec5620c571f9561e1461d06c1a8641c35d1ab551b45a1ac561cc571b8561a0460d810194570d0100e0140d9241806c088640c054080441706c040640b054020341605c0285407044018340f9341535d0f13606836129541445a119560a8561213412b481225c1335d119360603610154103480fa5c10c5a0f1560a0560e05c0db470cb5d08b550c3450ba5d042550b2450a9360a0360945a08c560835607a4d02a4507235069560605604b5c034580535a0435603b4a02b460225601a4617c5716b5715b4714a5613a46111560e9460d12409856058460103692b4791a4b892478723b71a376c94b6b9476613b649375f92f5e92b559274b9234684b438473e03b3a8373582f3482b2b827218231d81f1981b18817008130001f 15 5 11 9 6
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsF m_45 g_45 bds_45 (dagRefF 347 (dagTraceF m_45 s_45 8 f_45) l_45 0) s_45 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_0 : treeBlockF 0 32 (dagCheckNodeF m_45 g_45 bds_45 347 (dagTraceF m_45 s_45 8 f_45) l_45) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_1 : treeBlockF 32 64 (dagCheckNodeF m_45 g_45 bds_45 347 (dagTraceF m_45 s_45 8 f_45) l_45) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_2 : treeBlockF 64 96 (dagCheckNodeF m_45 g_45 bds_45 347 (dagTraceF m_45 s_45 8 f_45) l_45) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_3 : treeBlockF 96 128 (dagCheckNodeF m_45 g_45 bds_45 347 (dagTraceF m_45 s_45 8 f_45) l_45) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_4 : treeBlockF 128 160 (dagCheckNodeF m_45 g_45 bds_45 347 (dagTraceF m_45 s_45 8 f_45) l_45) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_5 : treeBlockF 160 192 (dagCheckNodeF m_45 g_45 bds_45 347 (dagTraceF m_45 s_45 8 f_45) l_45) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_6 : treeBlockF 192 224 (dagCheckNodeF m_45 g_45 bds_45 347 (dagTraceF m_45 s_45 8 f_45) l_45) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_7 : treeBlockF 224 256 (dagCheckNodeF m_45 g_45 bds_45 347 (dagTraceF m_45 s_45 8 f_45) l_45) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_8 : treeBlockF 256 288 (dagCheckNodeF m_45 g_45 bds_45 347 (dagTraceF m_45 s_45 8 f_45) l_45) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_9 : treeBlockF 288 320 (dagCheckNodeF m_45 g_45 bds_45 347 (dagTraceF m_45 s_45 8 f_45) l_45) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_10 : treeBlockF 320 347 (dagCheckNodeF m_45 g_45 bds_45 347 (dagTraceF m_45 s_45 8 f_45) l_45) = true := by decide +kernel
theorem nj_45_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_45 g_45 bds_45 347 (dagTraceF m_45 s_45 8 f_45) l_45) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_45_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_45_1 h1 h2)
theorem nj_45_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_45 g_45 bds_45 347 (dagTraceF m_45 s_45 8 f_45) l_45) i = true := block_join nj_45_1 (fun _ h1 h2 => treeBlockF_at nb_45_2 h1 h2)
theorem nj_45_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_45 g_45 bds_45 347 (dagTraceF m_45 s_45 8 f_45) l_45) i = true := block_join nj_45_2 (fun _ h1 h2 => treeBlockF_at nb_45_3 h1 h2)
theorem nj_45_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_45 g_45 bds_45 347 (dagTraceF m_45 s_45 8 f_45) l_45) i = true := block_join nj_45_3 (fun _ h1 h2 => treeBlockF_at nb_45_4 h1 h2)
theorem nj_45_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_45 g_45 bds_45 347 (dagTraceF m_45 s_45 8 f_45) l_45) i = true := block_join nj_45_4 (fun _ h1 h2 => treeBlockF_at nb_45_5 h1 h2)
theorem nj_45_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_45 g_45 bds_45 347 (dagTraceF m_45 s_45 8 f_45) l_45) i = true := block_join nj_45_5 (fun _ h1 h2 => treeBlockF_at nb_45_6 h1 h2)
theorem nj_45_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_45 g_45 bds_45 347 (dagTraceF m_45 s_45 8 f_45) l_45) i = true := block_join nj_45_6 (fun _ h1 h2 => treeBlockF_at nb_45_7 h1 h2)
theorem nj_45_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_45 g_45 bds_45 347 (dagTraceF m_45 s_45 8 f_45) l_45) i = true := block_join nj_45_7 (fun _ h1 h2 => treeBlockF_at nb_45_8 h1 h2)
theorem nj_45_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_45 g_45 bds_45 347 (dagTraceF m_45 s_45 8 f_45) l_45) i = true := block_join nj_45_8 (fun _ h1 h2 => treeBlockF_at nb_45_9 h1 h2)
theorem nj_45_10 : ∀ i, 0 ≤ i → i < 347 → (dagCheckNodeF m_45 g_45 bds_45 347 (dagTraceF m_45 s_45 8 f_45) l_45) i = true := block_join nj_45_9 (fun _ h1 h2 => treeBlockF_at nb_45_10 h1 h2)
theorem nc_45 : ∀ i, 0 ≤ i → i < 347 → (dagCheckNodeF m_45 g_45 bds_45 347 (dagTraceF m_45 s_45 8 f_45) l_45) i = true := nj_45_10
theorem lb_45 : LowerBin m_45 s_45 g_45 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_45 sub_45 gl_45 rc_45 nc_45

def m_46 : Nat := 0xffff0000ffff0000
def s_46 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_46 : Nat := 0x11170000151f0000
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_21, s_21, 5, g_21), (m_23, s_23, 5, g_23), (m_25, s_25, 5, g_25), (m_36, s_36, 5, g_36)]
theorem kn_46 : KnownBin bds_46 := by
  intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_21
  · exact lb_23
  · exact lb_25
  · exact lb_36
theorem sub_46 : ∀ b ∈ bds_46, m_46 &&& b.1 = b.1 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_46 : ∀ b ∈ bds_46, canon b.1 g_46 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_46 : Nat → Nat × Nat := unpackForestF 0x1f 1 5
def l_46 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x1f 2 1 5 1 2
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsF m_46 g_46 bds_46 (dagRefF 1 (dagTraceF m_46 s_46 6 f_46) l_46 0) s_46 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_0 : treeBlockF 0 1 (dagCheckNodeF m_46 g_46 bds_46 1 (dagTraceF m_46 s_46 6 f_46) l_46) = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_46 g_46 bds_46 1 (dagTraceF m_46 s_46 6 f_46) l_46) i = true := fun _ h1 h2 => treeBlockF_at nb_46_0 h1 h2
theorem lb_46 : LowerBin m_46 s_46 g_46 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_46 sub_46 gl_46 rc_46 nc_46

def m_47 : Nat := 0xffff0000ffff
def s_47 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_47 : Nat := 0x151f0000577f
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_26, s_26, 6, g_26), (m_20, s_20, 5, g_20), (m_22, s_22, 5, g_22), (m_24, s_24, 5, g_24), (m_27, s_27, 5, g_27), (m_37, s_37, 5, g_37), (m_1, s_1, 4, g_1), (m_3, s_3, 4, g_3), (m_7, s_7, 4, g_7)]
theorem kn_47 : KnownBin bds_47 := by
  intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_26
  · exact lb_20
  · exact lb_22
  · exact lb_24
  · exact lb_27
  · exact lb_37
  · exact lb_1
  · exact lb_3
  · exact lb_7
theorem sub_47 : ∀ b ∈ bds_47, m_47 &&& b.1 = b.1 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_47 : ∀ b ∈ bds_47, canon b.1 g_47 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_47 : Nat → Nat × Nat := unpackForestF 0x25048b28144005a7802d2e4d0b31e25d8f02e4940da3c0a31e82f8f415c8c4f23d04f2013490c1248015241049200248f411c7a06e3d02f1e050005a3c648e23246b1b12f8dda046c49e32469191348c81c4640d0016871814400527c5495a2d0731524e8ac274540a40149710b5b885a9c4c0e6216a31085b88429c4413a210a200a4786d264369121b2490d82886c1200290dfe8b50a35d85028c2a0b61504b0a0507fa2b3fcd6e1069b080397f9ad41d161fe6af05c5e82c28bfcd5a088c1043547f92bbfc0fe05298ff03b80c2b3fc0e5fe06f0003c7fca23fc0cc0147efd0297e8143f409001476fb94c7dc208028ddf50a2f8a567c5273e4159f105200a33004a7bd092de848ef60397a11fbd40a5e8466f4146004a53cc0e5e36a2f204e78c2880251de1052eaa437549ebaa4ddda496ed24376825bb410dd526aec02975497bac0f9d50860094674c28ba0d59d10ace80390049fb9c1040126ee62546d22fb6916dc74d8e386c71c3036915dc2688e124470824384111b48a6dfb516fc28b68959b88b4de0506e22b370d69b86acdc0396d12736a159b509cda02900497b64d61958becac5b6b5b035a1b1ad0c0cac576a1a4350911a8090d404465629b4c0e1a349cd204c68c14b2ad699a8bccfb4467c223351499a4b4ce0506692b3340a595684cc3506582b32c139950620092763522b1a511914a8c692f639ac31c0c18d24e0084f628a43141217e69ec393861c1c2fcd0d84290c20485f927b024e181070bf23f5fc202fc8dc01096a7b5c5ed1aa9ed456e47eb723b5dca62dc8dd71688ba2345c52a2e48d171248b72335b89fadc4dd4f6a0b634953d2eacd181666d8b336059da82cc0e14f47eb234457e302be9b15f4a8b035057c1429e8cd5a8c0ad36c56da82b40e14f27eaa46c552302a89b1556a0aa02853c97aa11b1508c0a836053c9380211d4d0689c23f528a02941313846ea392f51c93a701314325ea203050c93a70111380789f12d4fc1827c4953806c9d12f4ec1827449d380689c02400421a6c0e12849e9a0284a121a628f931464942354bc1c25053d2c488960284a097a52d4129690941270041fa4c1191d69a91b5c48c1a23a8fd202809004c4751ba3a0d91d03c0083b45526a349711525e8b350459a022c0c11524e00837441ae2204e11007088034249ada171810b2c08586c42c30124d5c9269e8394a41ca3124d350509a4934540dae124d0d0169a4925a3ee301f6580fb0d87e0343ec3012495cf26a47c05c3c9229e48f4f22a47905e3cc121e4148924ac4924f3b1ae1d84e0ec070760342491f9d0130e90a8740402491b9bc8f4e54986f12f3841e1c4110e10606f12737d1a9bc0f4922884905b369a69b40d8920b46c2542482b99b178cd4ba66a453351e99a514ce4846713d3389699c108cd288490563222e192d30c9498641542481f98c130c34a86194c30c161240ecbc6b85e24c2f5a617a930bd2785e1542481b950d68a86ac5425a2d9a816c140a84ac5424e2a1211644f0a82b4572502b92215c510a82ac5413e2acaa1504c8a825a541252481b14c130994a85194428c1e1325109f2885003427c1a1321909b2884e03426c1a1320d0990584903325c2612a950950584902b24caa12409c010664724e2392611c9100105e1fc5b224b01121b0890c01fc570fdab87ed3c3f68e1fa5a0fd2b07e5687d6a23fa3a1fd1b0fad407d0ba1f9561ec1a87e5383f2961f9431bda68ded146f4b437a561bc2d0e45106f0ac3783d1bc1a87e5086d0581f85b1a8270d40743f0b4341580fc2b8c9178646a2322450fc2b0c45403f09e2b45a17c280ad158566b42b356159268ac914562b42b156158248ac1043f09c2915c148220a40b03f096281400fc2389c1304b2a82584412c1607e10c404b4202561002d08c510400ac2004d10c260800d4410682001d0fc210020ac316841db500ec2406293c376a01bb400dc2806291c312781924d0c9228640f431084008270562d85c4d02c2c01606c0562b82a968292880a94b09ca202a50c246a2123450542b035168210a00d456069ad034d581a2b40d049068208340e41509c0b1420582702c1081503c008230122d822580110d802457010a580850c0d6a2020560162d014140058ac02b5a015ab00a124050820204e0040d8049080102e0001f 10 11
def l_47 : Nat → Nat → Option Nat := unpackLinksF 0x436021b010c84854442a021405098284a0c1f1a0f03074183a041a0e0c05060082e0c17020b0304848220c11020412ff8a7fc03fc09fe00ff007f60bf909fc80fdc27ea13ed21f680fa837d403ea01f386f9c07c81bdf15ee06f6827b403d515e906f4027a003cb15de9cef4077a03bd01de80ef407702bb609db00ed8076c03b601da04ec4375e13af01d780eac475603a909d480ea4074a23a501d280e8c273e239e05cd86e6c071e638c0dc600e2c170e23705db800dc006e0036d0db680da446c6336301b006d7436ba035425a610d2c1696034b01a580d203690034705a380cfc867e033c0d9e00ce4366c1b36019986ccc06660333019980ccc0666032e159700cac365603280d9010c80063c131e018c0cc4866240311058880c40161c130e018700c3416122309018480c2406120305118280c1406022301018080c0016000300018000be085f002f8017810b84f5c202df096f02b7805bc02de016d86b6c05b40ada016c82b5055a802d3056980b48159c22ce016700b38059812cc016600b2c159602c3216180b08158402ba21559eaac055602ab015502aa8055402a8095208a90054802a0115000a80053c129e014f00a702538029c014d04a6805320a91214784a3815103287054302a1805061a81094080a001500027f053d889e814f402712538809bc24dc0a6e0137009b804da0a6911348099c24ce026701338099814c4226105308098404c00a5d0d2e8097014b8025c012d8295c44ae0257012b809503494524a0123089102488023f151f808fc047a123d011e808f01474123a011d008e804720a37091b808dc046c0a34091a008b084580228111400894344a022501108888404400a20011000878243c021e010e0485084280212090900848042012100108008382414220610ff107f413f809fa08fd007e413f009f410f8087c003e001f000f8007ac53d409e904f4027a003be49dc0cee0077003a451d200e708738039421ca00e308718038c01c600e300714138029bf04df806f0337609ba04dd006e8037209ae2cd6826b4035a01ad00d68069c634c09a504d18467c4336219b00cd026680334019904cb8465c032a118b28c5026280314018514c28060c2306018204c1006041302018100c0806040302017b18b9905cc02e6017300b8845b052d8016b04b5025a412c8296400b18258c02c6016300af8856462b2015804ac0056002b001550caa0255002a8015304a98054c02a601500ca800540029e094f00a7804fd027e013b109c844e4026a2134049a004cc126211300498004bc125a112d00930e498024a09250091064880242090378818040c020601000c7e083ec11f600fb007b883d421e220ed10750639c31ca10e500728039401c610e300700638001bc10da106b8635c01ae00d7006b0235801ac00d5046a80354019650cb006484324019200c510628030c218600c30061802fc417e00bc0c5e002f0017608bb005d802ec017600bb005d802ec017408ae3056822b4015a00a9105480298314c00a5045202290014020a0004f8227c013e009e044e822740136109b004d02240a0f2b875103a801d400e220710038801c400da206d0036801b400da006910318c18420c2005f082f8016c40b4085a002b8615c00a6205300298014030a0005000278213c009e004f00278013c009e0046242300118008c00430c1d900e420700838001a860d0106608330018840c4006200300418000c00060003000150c090604800230400c40001 0x25148b2814472c97b6249e1949b07a3d72897b6049cd90624602b0bc1182606e4d0b2448517200fb5c05c2e0410bb4d22c9d05a4c8122544483a9281b42cd305f0990aa4c9189e488082430892081490c124820924426921054084264800900a0990a23d71c97b5a49e4805f2382b91413c7e08e3e0371e8179312ec268f5c625ed612792c2e4921463c0a04402b0ac1182006dc525ad51258dda04704be3624ee192f6a493b8407da802f1d2388e51ac6a8d234268e092f69c93c660e2320691724577caa460511130831683944418a2450a2b09c888428b92b458939ee2b4878438a814c23182086a8ee954846343b85521169b04a4d43820c4c0e50b062eda541a8b00c8151da4a835168434a10da4ea2209c858421a80ec50d6e0f6b313b53895a8c0e8fded294ef146764a244816c690b31185388428a140cc870570fa4c8792243a4921c0510d82483a2a9b60c61605b0a825861aec2e146140a106464825ae418d561169b0803911c18c1d1620c6b10645e82122b141660b0a304c60821aa078d701669899234814244000d1082a10294c100a03d8969d84acc595a598ab26c538c32842593a0ec9b31416a030ac0b01e1000e834d31070a0ff8308001e080521ff2882d85c2d01a43316a138ad0935b83dad41ad5e0a6ad03a577acad3ae559890b6b28574d427a4a12509086830418181fc080ee02073008377f81987e0c4860561d0277f014bf60a1fa0482913a0dc9b02c0e83906cf9a4d7e0a63ee105040624282b0d813b0e165f50a2b084540c208340e416062f525a620ad2be5593429c4c94261c2d3e41581709c0b0427d12b3e6939e92b4c305b5782ba6613d02086f88297a0a2202105ec072248317a814bdc92ded48ef5a3f7a519bd0519000664202b0a8119fe105e60727d8313f8a13c8138fb084f2b5178c289f40ccf9062f08293c810bba92ddc486ed84b768219ee08cf6062ec029120109ea4c9d607c7903278121bbe4f5de26eec93575c97baa10cf10464181b6102cba6145852b4ad1564bca712a509840b4e8856749ab30616d590ae9704f3c021ba00e5ce082e62546f52e374931bc498e4a6c6ed263901b1c70c0e2b4471122386121c2088dd359701a8b02165bf0a2de0506f62d377159ba6b4dcb56490249de105b807276831608ad2a85592c29c771426042d36c159b509c7684272e2fb9516dc68aee0c536f92b36e939900bec005b54c2ba9814d2b09e9104b464239d610db4052d9358685a033ad01af6c0d706c6b4303409019f480cf3506ada4354911a9090d40446981c348131a549ccea4268c14afe085a0688cf844670283431799e8a4cea5a66d2b2541351708acd0293a010b30d418e2bca5952484a522c5197f0b4cb856658271d0109b18bed845b6b22bb4f14da26b4ccb426342fafc16d4f0aea48534a027a3e12d1508e7384365418b229518f6b0c703064d22b245119025ec692762ca41b61418a090238406209c30e0e185290c20486089c3020e17f080c4b4f619a1b0693d8047ebf2372089d1b210869074ac12f54893ac89016a49ab1a415a11eaf68d55d29a4082a59c1c1000e175460bb94c1fc142e891172248ba2345c91a2ead11734a8b8924580142b60e17947ebc23b5d91bae08cd6f27eb713755c97aa249c7e054b63495a1a0ace121676a0b54605a5b62d0d8166070b2344580142c0d41638c0b126c5852a2be0a15b090adb50576302b8db15a070aa828555a82b11b1578c0ab26c550142a51b1518c0a83605f1ae2f4d456d6a0b5a5d5951fabc8cd5927ea992f53c938f80a9480b8a28545002229a0d1442889f93452ca028e171430a8a504c4f81a2904bd4724ea203051497a8649d3f060a012d4f892a760c13c25e9d1275311fa928dd46098a10445041e27a0d9390689c02440e2e02cd21324889b0384c5a202e911340500b34905da0a648f931464978384b5222580a12a6a094b48475a726a93d33486982354b8a7a564bd2824e3d02a49823206079246b891834484a0240130160720d03114c148520850369a0c13a0581d0720d92569a9123f47d1b8f24ec282660792b4781b23a078e6080728404692e1c8100e104070830461a822ed00e00808b03046d26a324bd1524e6e83044dae2244e0b8088888384401a16e0d0b60687c14443a301ee9510d2c08606c11c341721910b0c06a0542d41a186520160805a0344052d1ec95908294839461dc9d0684d8db0b46985632c1e9820d50369a3b13a0cc9b20a135036b84c9382cc2202c0e10169a3a93a1241d1620d8fc0687fc603f8b01fa1b0fb0c069054344221f0170af0a85702433c2219c110f30487cb523dd229ec8f4f52a43a12a3d02f1e4148d808a668441201515a0989529077b5c390aa1dc4e0a9088768383b01a1c6110e2068709443a42a1c0550ea098740402a01a17e0f4c906a6502d2f8129ca930e20887183c3841817e8f4df46a7323d390979c049cde07a6402f3141597809ca50464b01b24c0b9ac590db69a3993a3582a88e0e8da06c6c2543582c1a0550cf28868a423409e95e4d4cf25a670421c80d1ad178d54ba5ca55351229a68f4d228a669441c415194d30c949865c5c320aa0e0520c40901c834318261460d04106862a54310a6084510560b86182c2f4a217ed30be4985e93c29010182d70c04985e1541bc9c0840e0a2060579442dda815c510b60a0208382c89e160940af488571442acaa174d68b96ac5c25a2d52b168938b34842123e0591e962568ad2ac5613e2a8991524b4a824a2602909c109484d0a10a85304c274121401109c0285214427c2a1460f09b048500242801a1425109f0684e0242701a13a5109b06852a54288a213c1901b0b84d0342641602c070970984b2540142e12a0b0932a887b5b429aba12d3d0669a82345409a1a00968fa4ae78a563c1279d68fce746e6e9441e09d8dc4e83126c13133038959b816cd90b46b8573302b18e0fcc20761f83a2ec1b94e0d8980664a02b248139209388f498472441cca00c01705d0982384017ca61165808a0d844860178260da580640a83b95012ca40b617016080291501d8a002c1405a0983a94216427092108742642c03e120190d0554730844023a1fd1b102d447e6a03e85d061a70f60d4572b8298440601602c070562b826044058080e4110722883bb4d1d9a28ea968744ac3114d140a28e6168710ac3803d1bc1a8cc5906d058330551ac2708e1086a03a341581982c0cd1785d6b232b51191228c4540540b02205017c280860d0608b42f456175ad0b8d581669c2234d16d268b4914592b42c15615c248ac1044e0882a15c14c220a40b0160382814005c2e09a1004e0982184c110ae09a5504c0882582c1182208c510430682184c1040e0820d0494b42425611c2d08a1581709c2204d0e41b0840d41a03c2001d2322d91115c876ae4334f215a3908968834ac4115a1f0ab0f4538792963c1431b8a10d816c690b43385718c2b0c213c5509c2884b13c2389410c3f0841e34d0e1a282c8e83946c1e350059a00681403b0901cb500e1a006e140330801a24d0cd228308f43207a1eb420e92786c91c1547a1a93c0c4210441701f098171340842605a5802c0d8120540802603a138292880e05c0680a04e5101b0b80c02c0580e03ed64256a21234508428045168208ac0fb5a079ab03a5681c0920d8410681c82c0c4182840b84e0582105f16c2b8ae1525a0a0a584c50c230ac0c84e0540f016170080980514c048b00221b0090980315c014ae010d640d6a20505002e2d013158086b403b560182480a104138b60845703ca581c50c0c0ac0204e0092149ed3e4e6971db478c5a1c5e93e294971024786921bfa8fdf9476fb2377c119bde53de7294f1147750a339e4fdcd26ed992f65093b1813d7d096a70474dc21a4e0fd1c0768a0372441991a0bc3e056180270501180606c0102e0001f 17 6 11 10 7
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsF m_47 g_47 bds_47 (dagRefF 594 (dagTraceF m_47 s_47 8 f_47) l_47 0) s_47 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_0 : treeBlockF 0 32 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_1 : treeBlockF 32 64 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_2 : treeBlockF 64 96 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_3 : treeBlockF 96 128 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_4 : treeBlockF 128 160 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_5 : treeBlockF 160 192 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_6 : treeBlockF 192 224 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_7 : treeBlockF 224 256 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_8 : treeBlockF 256 288 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_9 : treeBlockF 288 320 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_10 : treeBlockF 320 352 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_11 : treeBlockF 352 384 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_12 : treeBlockF 384 416 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_13 : treeBlockF 416 448 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_14 : treeBlockF 448 480 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_15 : treeBlockF 480 512 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_16 : treeBlockF 512 544 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_17 : treeBlockF 544 576 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_18 : treeBlockF 576 594 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
theorem nj_47_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_47_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_47_1 h1 h2)
theorem nj_47_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_1 (fun _ h1 h2 => treeBlockF_at nb_47_2 h1 h2)
theorem nj_47_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_2 (fun _ h1 h2 => treeBlockF_at nb_47_3 h1 h2)
theorem nj_47_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_3 (fun _ h1 h2 => treeBlockF_at nb_47_4 h1 h2)
theorem nj_47_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_4 (fun _ h1 h2 => treeBlockF_at nb_47_5 h1 h2)
theorem nj_47_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_5 (fun _ h1 h2 => treeBlockF_at nb_47_6 h1 h2)
theorem nj_47_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_6 (fun _ h1 h2 => treeBlockF_at nb_47_7 h1 h2)
theorem nj_47_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_7 (fun _ h1 h2 => treeBlockF_at nb_47_8 h1 h2)
theorem nj_47_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_8 (fun _ h1 h2 => treeBlockF_at nb_47_9 h1 h2)
theorem nj_47_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_9 (fun _ h1 h2 => treeBlockF_at nb_47_10 h1 h2)
theorem nj_47_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_10 (fun _ h1 h2 => treeBlockF_at nb_47_11 h1 h2)
theorem nj_47_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_11 (fun _ h1 h2 => treeBlockF_at nb_47_12 h1 h2)
theorem nj_47_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_12 (fun _ h1 h2 => treeBlockF_at nb_47_13 h1 h2)
theorem nj_47_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_13 (fun _ h1 h2 => treeBlockF_at nb_47_14 h1 h2)
theorem nj_47_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_14 (fun _ h1 h2 => treeBlockF_at nb_47_15 h1 h2)
theorem nj_47_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_15 (fun _ h1 h2 => treeBlockF_at nb_47_16 h1 h2)
theorem nj_47_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_16 (fun _ h1 h2 => treeBlockF_at nb_47_17 h1 h2)
theorem nj_47_18 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_17 (fun _ h1 h2 => treeBlockF_at nb_47_18 h1 h2)
theorem nc_47 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := nj_47_18
theorem lb_47 : LowerBin m_47 s_47 g_47 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_47 sub_47 gl_47 rc_47 nc_47

def m_48 : Nat := 0xffffffff00000000
def s_48 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_48 : Nat := 0x1117151f00000000
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_29, s_29, 5, g_29), (m_31, s_31, 5, g_31), (m_33, s_33, 5, g_33), (m_36, s_36, 5, g_36)]
theorem kn_48 : KnownBin bds_48 := by
  intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_29
  · exact lb_31
  · exact lb_33
  · exact lb_36
theorem sub_48 : ∀ b ∈ bds_48, m_48 &&& b.1 = b.1 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_48 : ∀ b ∈ bds_48, canon b.1 g_48 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_48 : Nat → Nat × Nat := unpackForestF 0x1f 1 5
def l_48 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x1f 2 1 5 1 2
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsF m_48 g_48 bds_48 (dagRefF 1 (dagTraceF m_48 s_48 6 f_48) l_48 0) s_48 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_0 : treeBlockF 0 1 (dagCheckNodeF m_48 g_48 bds_48 1 (dagTraceF m_48 s_48 6 f_48) l_48) = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_48 g_48 bds_48 1 (dagTraceF m_48 s_48 6 f_48) l_48) i = true := fun _ h1 h2 => treeBlockF_at nb_48_0 h1 h2
theorem lb_48 : LowerBin m_48 s_48 g_48 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_48 sub_48 gl_48 rc_48 nc_48

def m_49 : Nat := 0xffffffff
def s_49 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_49 : Nat := 0x151f577f
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_34, s_34, 6, g_34), (m_28, s_28, 5, g_28), (m_30, s_30, 5, g_30), (m_32, s_32, 5, g_32), (m_35, s_35, 5, g_35), (m_37, s_37, 5, g_37), (m_4, s_4, 4, g_4), (m_6, s_6, 4, g_6), (m_7, s_7, 4, g_7)]
theorem kn_49 : KnownBin bds_49 := by
  intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_34
  · exact lb_28
  · exact lb_30
  · exact lb_32
  · exact lb_35
  · exact lb_37
  · exact lb_4
  · exact lb_6
  · exact lb_7
theorem sub_49 : ∀ b ∈ bds_49, m_49 &&& b.1 = b.1 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_49 : ∀ b ∈ bds_49, canon b.1 g_49 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_49 : Nat → Nat × Nat := unpackForestF 0x25048b28144005a7802d2e4d0b31e25d8f02e4940da3c0a31e82f8f415c8c4f23d04f2013490c1248015241049200248f411c7a06e3d02f1e050005a3c648e23246b1b12f8dda046c49e32469191348c81c4640d0016871814400527c5495a2d0731524e8ac274540a40149710b5b885a9c4c0e6216a31085b88429c4413a210a200a4786d264369121b2490d82886c1200290dfe8b50a35d85028c2a0b61504b0a0507fa2b3fcd6e1069b080397f9ad41d161fe6af05c5e82c28bfcd5a088c1043547f92bbfc0fe05298ff03b80c2b3fc0e5fe06f0003c7fca23fc0cc0147efd0297e8143f409001476fb94c7dc208028ddf50a2f8a567c5273e4159f105200a33004a7bd092de848ef60397a11fbd40a5e8466f4146004a53cc0e5e36a2f204e78c2880251de1052eaa437549ebaa4ddda496ed24376825bb410dd526aec02975497bac0f9d50860094674c28ba0d59d10ace80390049fb9c1040126ee62546d22fb6916dc74d8e386c71c3036915dc2688e124470824384111b48a6dfb516fc28b68959b88b4de0506e22b370d69b86acdc0396d12736a159b509cda02900497b64d61958becac5b6b5b035a1b1ad0c0cac576a1a4350911a8090d404465629b4c0e1a349cd204c68c14b2ad699a8bccfb4467c223351499a4b4ce0506692b3340a595684cc3506582b32c139950620092763522b1a511914a8c692f639ac31c0c18d24e0084f628a43141217e69ec393861c1c2fcd0d84290c20485f927b024e181070bf23f5fc202fc8dc01096a7b5c5ed1aa9ed456e47eb723b5dca62dc8dd71688ba2345c52a2e48d171248b72335b89fadc4dd4f6a0b634953d2eacd181666d8b336059da82cc0e14f47eb234457e302be9b15f4a8b035057c1429e8cd5a8c0ad36c56da82b40e14f27eaa46c552302a89b1556a0aa02853c97aa11b1508c0a836053c9380211d4d0689c23f528a02941313846ea392f51c93a701314325ea203050c93a70111380789f12d4fc1827c4953806c9d12f4ec1827449d380689c02400421a6c0e12849e9a0284a121a628f931464942354bc1c25053d2c488960284a097a52d4129690941270041fa4c1191d69a91b5c48c1a23a8fd202809004c4751ba3a0d91d03c0083b45526a349711525e8b350459a022c0c11524e00837441ae2204e11007088034249ada171810b2c08586c42c30124d5c9269e8394a41ca3124d350509a4934540dae124d0d0169a4925a3ee301f6580fb0d87e0343ec3012495cf26a47c05c3c9229e48f4f22a47905e3cc121e4148924ac4924f3b1ae1d84e0ec070760342491f9d0130e90a8740402491b9bc8f4e54986f12f3841e1c4110e10606f12737d1a9bc0f4922884905b369a69b40d8920b46c2542482b99b178cd4ba66a453351e99a514ce4846713d3389699c108cd288490563222e192d30c9498641542481f98c130c34a86194c30c161240ecbc6b85e24c2f5a617a930bd2785e1542481b950d68a86ac5425a2d9a816c140a84ac5424e2a1211644f0a82b4572502b92215c510a82ac5413e2acaa1504c8a825a541252481b14c130994a85194428c1e1325109f2885003427c1a1321909b2884e03426c1a1320d0990584903325c2612a950950584902b24caa12409c010664724e2392611c9100105e1fc5b224b01121b0890c01fc570fdab87ed3c3f68e1fa5a0fd2b07e5687d6a23fa3a1fd1b0fad407d0ba1f9561ec1a87e5383f2961f9431bda68ded146f4b437a561bc2d0e45106f0ac3783d1bc1a87e5086d0581f85b1a8270d40743f0b4341580fc2b8c9178646a2322450fc2b0c45403f09e2b45a17c280ad158566b42b356159268ac914562b42b156158248ac1043f09c2915c148220a40b03f096281400fc2389c1304b2a82584412c1607e10c404b4202561002d08c510400ac2004d10c260800d4410682001d0fc210020ac316841db500ec2406293c376a01bb400dc2806291c312781924d0c9228640f431084008270562d85c4d02c2c01606c0562b82a968292880a94b09ca202a50c246a2123450542b035168210a00d456069ad034d581a2b40d049068208340e41509c0b1420582702c1081503c008230122d822580110d802457010a580850c0d6a2020560162d014140058ac02b5a015ab00a124050820204e0040d8049080102e0001f 10 11
def l_49 : Nat → Nat → Option Nat := unpackLinksF 0x436021b010c84854442a021405098284a0c1f1a0f03074183a041a0e0c05060082e0c17020b0304848220c11020412ff8a7fc03fc09fe00ff007f60bf909fc80fdc27ea13ed21f680fa837d403ea01f386f9c07c81bdf15ee06f6827b403d515e906f4027a003cb15de9cef4077a03bd01de80ef407702bb609db00ed8076c03b601da04ec4375e13af01d780eac475603a909d480ea4074a23a501d280e8c273e239e05cd86e6c071e638c0dc600e2c170e23705db800dc006e0036d0db680da446c6336301b006d7436ba035425a610d2c1696034b01a580d203690034705a380cfc867e033c0d9e00ce4366c1b36019986ccc06660333019980ccc0666032e159700cac365603280d9010c80063c131e018c0cc4866240311058880c40161c130e018700c3416122309018480c2406120305118280c1406022301018080c0016000300018000be085f002f8017810b84f5c202df096f02b7805bc02de016d86b6c05b40ada016c82b5055a802d3056980b48159c22ce016700b38059812cc016600b2c159602c3216180b08158402ba21559eaac055602ab015502aa8055402a8095208a90054802a0115000a80053c129e014f00a702538029c014d04a6805320a91214784a3815103287054302a1805061a81094080a001500027f053d889e814f402712538809bc24dc0a6e0137009b804da0a6911348099c24ce026701338099814c4226105308098404c00a5d0d2e8097014b8025c012d8295c44ae0257012b809503494524a0123089102488023f151f808fc047a123d011e808f01474123a011d008e804720a37091b808dc046c0a34091a008b084580228111400894344a022501108888404400a20011000878243c021e010e0485084280212090900848042012100108008382414220610ff107f413f809fa08fd007e413f009f410f8087c003e001f000f8007ac53d409e904f4027a003be49dc0cee0077003a451d200e708738039421ca00e308718038c01c600e300714138029bf04df806f0337609ba04dd006e8037209ae2cd6826b4035a01ad00d68069c634c09a504d18467c4336219b00cd026680334019904cb8465c032a118b28c5026280314018514c28060c2306018204c1006041302018100c0806040302017b18b9905cc02e6017300b8845b052d8016b04b5025a412c8296400b18258c02c6016300af8856462b2015804ac0056002b001550caa0255002a8015304a98054c02a601500ca800540029e094f00a7804fd027e013b109c844e4026a2134049a004cc126211300498004bc125a112d00930e498024a09250091064880242090378818040c020601000c7e083ec11f600fb007b883d421e220ed10750639c31ca10e500728039401c610e300700638001bc10da106b8635c01ae00d7006b0235801ac00d5046a80354019650cb006484324019200c510628030c218600c30061802fc417e00bc0c5e002f0017608bb005d802ec017600bb005d802ec017408ae3056822b4015a00a9105480298314c00a5045202290014020a0004f8227c013e009e044e822740136109b004d02240a0f2b875103a801d400e220710038801c400da206d0036801b400da006910318c18420c2005f082f8016c40b4085a002b8615c00a6205300298014030a0005000278213c009e004f00278013c009e0046242300118008c00430c1d900e420700838001a860d0106608330018840c4006200300418000c00060003000150c090604800230400c40001 0x25148b2814472c97b6249e1949b07a3d72897b6049cd90624602b0bc1182606e4d0b2448517200fb5c05c2e0410bb4d22c9d05a4c8122544483a9281b42cd305f0990aa4c9189e488082430892081490c124820924426921054084264800900a0990a23d71c97b5a49e4805f2382b91413c7e08e3e0371e8179312ec268f5c625ed612792c2e4921463c0a04402b0ac1182006dc525ad51258dda04704be3624ee192f6a493b8407da802f1d2388e51ac6a8d234268e092f69c93c660e2320691724577caa460511130831683944418a2450a2b09c888428b92b458939ee2b4878438a814c23182086a8ee954846343b85521169b04a4d43820c4c0e50b062eda541a8b00c8151da4a835168434a10da4ea2209c858421a80ec50d6e0f6b313b53895a8c0e8fded294ef146764a244816c690b31185388428a140cc870570fa4c8792243a4921c0510d82483a2a9b60c61605b0a825861aec2e146140a106464825ae418d561169b0803911c18c1d1620c6b10645e82122b141660b0a304c60821aa078d701669899234814244000d1082a10294c100a03d8969d84acc595a598ab26c538c32842593a0ec9b31416a030ac0b01e1000e834d31070a0ff8308001e080521ff2882d85c2d01a43316a138ad0935b83dad41ad5e0a6ad03a577acad3ae559890b6b28574d427a4a12509086830418181fc080ee02073008377f81987e0c4860561d0277f014bf60a1fa0482913a0dc9b02c0e83906cf9a4d7e0a63ee105040624282b0d813b0e165f50a2b084540c208340e416062f525a620ad2be5593429c4c94261c2d3e41581709c0b0427d12b3e6939e92b4c305b5782ba6613d02086f88297a0a2202105ec072248317a814bdc92ded48ef5a3f7a519bd0519000664202b0a8119fe105e60727d8313f8a13c8138fb084f2b5178c289f40ccf9062f08293c810bba92ddc486ed84b768219ee08cf6062ec029120109ea4c9d607c7903278121bbe4f5de26eec93575c97baa10cf10464181b6102cba6145852b4ad1564bca712a509840b4e8856749ab30616d590ae9704f3c021ba00e5ce082e62546f52e374931bc498e4a6c6ed263901b1c70c0e2b4471122386121c2088dd359701a8b02165bf0a2de0506f62d377159ba6b4dcb56490249de105b807276831608ad2a85592c29c771426042d36c159b509c7684272e2fb9516dc68aee0c536f92b36e939900bec005b54c2ba9814d2b09e9104b464239d610db4052d9358685a033ad01af6c0d706c6b4303409019f480cf3506ada4354911a9090d40446981c348131a549ccea4268c14afe085a0688cf844670283431799e8a4cea5a66d2b2541351708acd0293a010b30d418e2bca5952484a522c5197f0b4cb856658271d0109b18bed845b6b22bb4f14da26b4ccb426342fafc16d4f0aea48534a027a3e12d1508e7384365418b229518f6b0c703064d22b245119025ec692762ca41b61418a090238406209c30e0e185290c20486089c3020e17f080c4b4f619a1b0693d8047ebf2372089d1b210869074ac12f54893ac89016a49ab1a415a11eaf68d55d29a4082a59c1c1000e175460bb94c1fc142e891172248ba2345c91a2ead11734a8b8924580142b60e17947ebc23b5d91bae08cd6f27eb713755c97aa249c7e054b63495a1a0ace121676a0b54605a5b62d0d8166070b2344580142c0d41638c0b126c5852a2be0a15b090adb50576302b8db15a070aa828555a82b11b1578c0ab26c550142a51b1518c0a83605f1ae2f4d456d6a0b5a5d5951fabc8cd5927ea992f53c938f80a9480b8a28545002229a0d1442889f93452ca028e171430a8a504c4f81a2904bd4724ea203051497a8649d3f060a012d4f892a760c13c25e9d1275311fa928dd46098a10445041e27a0d9390689c02440e2e02cd21324889b0384c5a202e911340500b34905da0a648f931464978384b5222580a12a6a094b48475a726a93d33486982354b8a7a564bd2824e3d02a49823206079246b891834484a0240130160720d03114c148520850369a0c13a0581d0720d92569a9123f47d1b8f24ec282660792b4781b23a078e6080728404692e1c8100e104070830461a822ed00e00808b03046d26a324bd1524e6e83044dae2244e0b8088888384401a16e0d0b60687c14443a301ee9510d2c08606c11c341721910b0c06a0542d41a186520160805a0344052d1ec95908294839461dc9d0684d8db0b46985632c1e9820d50369a3b13a0cc9b20a135036b84c9382cc2202c0e10169a3a93a1241d1620d8fc0687fc603f8b01fa1b0fb0c069054344221f0170af0a85702433c2219c110f30487cb523dd229ec8f4f52a43a12a3d02f1e4148d808a668441201515a0989529077b5c390aa1dc4e0a9088768383b01a1c6110e2068709443a42a1c0550ea098740402a01a17e0f4c906a6502d2f8129ca930e20887183c3841817e8f4df46a7323d390979c049cde07a6402f3141597809ca50464b01b24c0b9ac590db69a3993a3582a88e0e8da06c6c2543582c1a0550cf28868a423409e95e4d4cf25a670421c80d1ad178d54ba5ca55351229a68f4d228a669441c415194d30c949865c5c320aa0e0520c40901c834318261460d04106862a54310a6084510560b86182c2f4a217ed30be4985e93c29010182d70c04985e1541bc9c0840e0a2060579442dda815c510b60a0208382c89e160940af488571442acaa174d68b96ac5c25a2d52b168938b34842123e0591e962568ad2ac5613e2a8991524b4a824a2602909c109484d0a10a85304c274121401109c0285214427c2a1460f09b048500242801a1425109f0684e0242701a13a5109b06852a54288a213c1901b0b84d0342641602c070970984b2540142e12a0b0932a887b5b429aba12d3d0669a82345409a1a00968fa4ae78a563c1279d68fce746e6e9441e09d8dc4e83126c13133038959b816cd90b46b8573302b18e0fcc20761f83a2ec1b94e0d8980664a02b248139209388f498472441cca00c01705d0982384017ca61165808a0d844860178260da580640a83b95012ca40b617016080291501d8a002c1405a0983a94216427092108742642c03e120190d0554730844023a1fd1b102d447e6a03e85d061a70f60d4572b8298440601602c070562b826044058080e4110722883bb4d1d9a28ea968744ac3114d140a28e6168710ac3803d1bc1a8cc5906d058330551ac2708e1086a03a341581982c0cd1785d6b232b51191228c4540540b02205017c280860d0608b42f456175ad0b8d581669c2234d16d268b4914592b42c15615c248ac1044e0882a15c14c220a40b0160382814005c2e09a1004e0982184c110ae09a5504c0882582c1182208c510430682184c1040e0820d0494b42425611c2d08a1581709c2204d0e41b0840d41a03c2001d2322d91115c876ae4334f215a3908968834ac4115a1f0ab0f4538792963c1431b8a10d816c690b43385718c2b0c213c5509c2884b13c2389410c3f0841e34d0e1a282c8e83946c1e350059a00681403b0901cb500e1a006e140330801a24d0cd228308f43207a1eb420e92786c91c1547a1a93c0c4210441701f098171340842605a5802c0d8120540802603a138292880e05c0680a04e5101b0b80c02c0580e03ed64256a21234508428045168208ac0fb5a079ab03a5681c0920d8410681c82c0c4182840b84e0582105f16c2b8ae1525a0a0a584c50c230ac0c84e0540f016170080980514c048b00221b0090980315c014ae010d640d6a20505002e2d013158086b403b560182480a104138b60845703ca581c50c0c0ac0204e0092149ed3e4e6971db478c5a1c5e93e294971024786921bfa8fdf9476fb2377c119bde53de7294f1147750a339e4fdcd26ed992f65093b1813d7d096a70474dc21a4e0fd1c0768a0372441991a0bc3e056180270501180606c0102e0001f 17 6 11 10 7
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsF m_49 g_49 bds_49 (dagRefF 594 (dagTraceF m_49 s_49 8 f_49) l_49 0) s_49 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_0 : treeBlockF 0 32 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_1 : treeBlockF 32 64 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_2 : treeBlockF 64 96 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_3 : treeBlockF 96 128 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_4 : treeBlockF 128 160 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_5 : treeBlockF 160 192 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_6 : treeBlockF 192 224 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_7 : treeBlockF 224 256 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_8 : treeBlockF 256 288 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_9 : treeBlockF 288 320 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_10 : treeBlockF 320 352 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_11 : treeBlockF 352 384 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_12 : treeBlockF 384 416 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_13 : treeBlockF 416 448 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_14 : treeBlockF 448 480 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_15 : treeBlockF 480 512 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_16 : treeBlockF 512 544 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_17 : treeBlockF 544 576 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_18 : treeBlockF 576 594 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
theorem nj_49_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_49_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_49_1 h1 h2)
theorem nj_49_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_1 (fun _ h1 h2 => treeBlockF_at nb_49_2 h1 h2)
theorem nj_49_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_2 (fun _ h1 h2 => treeBlockF_at nb_49_3 h1 h2)
theorem nj_49_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_3 (fun _ h1 h2 => treeBlockF_at nb_49_4 h1 h2)
theorem nj_49_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_4 (fun _ h1 h2 => treeBlockF_at nb_49_5 h1 h2)
theorem nj_49_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_5 (fun _ h1 h2 => treeBlockF_at nb_49_6 h1 h2)
theorem nj_49_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_6 (fun _ h1 h2 => treeBlockF_at nb_49_7 h1 h2)
theorem nj_49_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_7 (fun _ h1 h2 => treeBlockF_at nb_49_8 h1 h2)
theorem nj_49_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_8 (fun _ h1 h2 => treeBlockF_at nb_49_9 h1 h2)
theorem nj_49_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_9 (fun _ h1 h2 => treeBlockF_at nb_49_10 h1 h2)
theorem nj_49_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_10 (fun _ h1 h2 => treeBlockF_at nb_49_11 h1 h2)
theorem nj_49_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_11 (fun _ h1 h2 => treeBlockF_at nb_49_12 h1 h2)
theorem nj_49_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_12 (fun _ h1 h2 => treeBlockF_at nb_49_13 h1 h2)
theorem nj_49_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_13 (fun _ h1 h2 => treeBlockF_at nb_49_14 h1 h2)
theorem nj_49_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_14 (fun _ h1 h2 => treeBlockF_at nb_49_15 h1 h2)
theorem nj_49_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_15 (fun _ h1 h2 => treeBlockF_at nb_49_16 h1 h2)
theorem nj_49_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_16 (fun _ h1 h2 => treeBlockF_at nb_49_17 h1 h2)
theorem nj_49_18 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_17 (fun _ h1 h2 => treeBlockF_at nb_49_18 h1 h2)
theorem nc_49 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := nj_49_18
theorem lb_49 : LowerBin m_49 s_49 g_49 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_49 sub_49 gl_49 rc_49 nc_49

def g_50 : Nat := 0x1117151f151f577f
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_47, s_47, 9, g_47), (m_45, s_45, 9, g_45), (m_44, s_44, 9, g_44), (m_43, s_43, 9, g_43), (m_40, s_40, 9, g_40), (m_38, s_38, 9, g_38), (m_49, s_49, 9, g_49), (m_48, s_48, 7, g_48), (m_46, s_46, 7, g_46), (m_42, s_42, 6, g_42), (m_41, s_41, 6, g_41), (m_39, s_39, 6, g_39), (m_12, s_12, 6, g_12), (m_10, s_10, 5, g_10), (m_20, s_20, 5, g_20), (m_21, s_21, 5, g_21), (m_22, s_22, 5, g_22), (m_23, s_23, 5, g_23), (m_24, s_24, 5, g_24), (m_28, s_28, 5, g_28), (m_29, s_29, 5, g_29), (m_30, s_30, 5, g_30), (m_31, s_31, 5, g_31), (m_32, s_32, 5, g_32), (m_13, s_13, 5, g_13), (m_36, s_36, 5, g_36), (m_37, s_37, 5, g_37), (m_11, s_11, 5, g_11), (m_8, s_8, 4, g_8), (m_7, s_7, 4, g_7), (m_5, s_5, 4, g_5), (m_4, s_4, 4, g_4), (m_2, s_2, 4, g_2), (m_1, s_1, 4, g_1)]
theorem kn_50 : KnownBin bds_50 := by
  intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_47
  · exact lb_45
  · exact lb_44
  · exact lb_43
  · exact lb_40
  · exact lb_38
  · exact lb_49
  · exact lb_48
  · exact lb_46
  · exact lb_42
  · exact lb_41
  · exact lb_39
  · exact lb_12
  · exact lb_10
  · exact lb_20
  · exact lb_21
  · exact lb_22
  · exact lb_23
  · exact lb_24
  · exact lb_28
  · exact lb_29
  · exact lb_30
  · exact lb_31
  · exact lb_32
  · exact lb_13
  · exact lb_36
  · exact lb_37
  · exact lb_11
  · exact lb_8
  · exact lb_7
  · exact lb_5
  · exact lb_4
  · exact lb_2
  · exact lb_1
theorem sub_50 : ∀ b ∈ bds_50, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_50 : ∀ b ∈ bds_50, canon b.1 g_50 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_50 : Nat → Nat × Nat := unpackForestF 0xabb649936ba713ba7139a998ca7133a703ba7039a788ca70339936399361a5146a5144a2471a2164a2154a214ea2b61a20189916ba147199163a014e991619e8469e8449bc719b8649b8549b84e9c3619b82c9906b9ac71990639984e9906100c5797b7497b5c91b5b91b569615691939949749495c919339385691839920749205c9183300b5b85c6a9035c85b6b8f34d85b6a8e46885b678d56e85b668593b8b96685939899648995c89818859338583b8806685839860648605c8602c8583300b4b849447ec5b7e957833517e9567e94f8135a813567e94e7e81b7f0567f04e7e8190095b7d94573c6b7c81973a6a7b14e7b0187396a7396779b61739667847a781767394f76b6a76b667394e7381b7446b740667404e738190094b6e2726e17f6e17e6e17d7006b700636e17c6e1726ea8c6e0735c5676d1565c16a6ad7f6ad7d6b18c6ad775c1676946d690635c16667966678185c15a6697c6567665576651765c1576356a63566634665c1566228c5f6776157d5f2765fe765fd765f2665c01b5e07e5cd675c8665c8565c019009335b0445245b5a0245225b59024522435205756b515694956933520565204f54b5a54b565204e5202f529565294e5202e0085b5104542c6b4fa644f82442a6b4e87c4d2764d2644d02442a434c02e4296a4a84e4a82c4286a4286748b6148933428664747a470764284f45b6a45b664284e4282f4346b431664314e4282e0084b3d2733d1723d07f401713d07e3d07d3e16b3e1633d07c3d07226d673ba663b82426a6b3a2763a02426a5b390562686a36d7f36d7d3708c36d77268673446d341633497c3414b26866328663282c2685a3187c306763057630076268572dd6a2dd662dc662d949268562c88c29e772bd7d298762a6762a576298662682f2897e2756727166271562682e0083322c7322c7124371243692287e2287c228720156721c660146b1fd7a1fc7a1f8440145b1e46b1e24e0125a1c87e1c87c1bd671ba560124218c6b19a541992418a421894e0115a1707e1707c14d671612414a5a151481495601142130561304e0106a11d7d11c71010670e46d0e3630e3610e34b0e14a0e04a010660c46b0c0660c04e0105a0105708d6a08d6608c6608b6b08b51010560104f04d6704c6a04b6a04b6604b5a04b560104e0307e0307c01d67018660185601042008130003f 9 11
def l_50 : Nat → Nat → Option Nat := unpackLinksF 0x426084450882110422084030802100420083c300b9ff13fe07fc0fe0dfc03f807f00fe01fb0bec57d80f895f103e017c00f801ed1bda07b40f681ed03d8179caf381e22bc407842e93dd203a407404e785cf039c17380e701cc1398072c2e581cb039226f1add09ba037026e00da8db5036626cc0d905b2036406c42d881b1036206b86d701ae035a16b40d681ad0354366a0cd0198133006600ca1194032806500c90992032406480c78d826b0405f0cbe017b0af605ec0bc897712ee05d06ba017402e425c80b9016f1ade05bc0b7816f02d83579caf015e02ba15702ae015c02b425642ac81580a92f5240a40548028e151c0a305403280050009e113c027804e849d0138126e14dc0999133026604cc097152e025634ac09489290252049c4920d240246148c09181201a26d44c0888911021e243c086890d021a04340868109221204240848107120e041c083810419eed3dc07898f101e203bc47780ee09da13b027394e701cc139807300e411c4238807100df19be037c06e88dd01ba036866d00da01b4036806b8cc97190132006400c8018e131826300c60188230c25a3cb4016802c845900b1095852b005584ab015412a805484a33146028c05180a2093c427804f009c1138026844c8499012a425404a80950128123ca47808c19180228445008a011022146428084090802100408c7468e611cc039807300de41b4436806160c2016122c005800b0014ca298053009e413c027804d1098112462480490092011c42380432086010c0208841007e20fc01f043b187600ec01c8839007200dc41b8037006e00dc01b8037005e80bc017802f005830b0016002c005800b00160026304c00980130026004c009801300203040008000f081e003c006c605c00150001 0x8f470abb64a998ca788c8f478a4979a1171aa93baa139a91336f1319e0799a871a883ba8039a70333d031258138f34d25013a5946a5144a2818a2b61a4c71a4164a3954a314ea2018a147172a426f1424184322811a014e9f0469e8449c02c9c3619e4719d8649d0549c84e9b82c9ac716e243411423d042228229984eab36b8eb69a6b63a6361a196b7a969a09639f9616d9339b06b4a0699a063990613c833220139837497b5c2181396156951749495c93856928749205c90c5a9735b8eb5a96b567d15b95939941336c9315085b930399183338831210138e465208138d4749035c8d3658f34d200138e4688d3688d56e8b9668a9648a15c8981888066870648685c8602c90c6a8fb6b8eb6a8db678cb668416b8c13b8b13989133671315a86b8883b8783985833320311f0138194c8494481b5983351500493c03381b5a813567ca5a7f8567f04e8445b7c25a7a95a83957829568214f8094e6c9424f05b3b0438001b7e819128117894d7714c7d9451e821750190d0117c8197b94e7b01878c797814e7736979b613a83378c7a781767736a76b661e0117546b748667404e7d46b7c26a7a96a7a167791667794f7614e671425986b398431d8217581b738190b8116e871620197086b700636697c6ea8c72a727217f7197e7117d6f97c66175639746f17265955631546e0731c0216181b5d819028116d156610196b18c6c57f6bd7d6ad7766575651566081969c6d63c65690634e04b68166678186697c600195f8196667665d76651765f0196456a63d66634664d8491b8116228c602845fa646157d60575606765fd7661e7760a765f2665e07e5dd675d0665c8566dd676c96a6a167689666715a64957629565886b4c85b1b0215e81b5c019010115504c5b044570645a02456866590245535957b5157149569335535a54b56531565294e4c05a5ac5b59a5b58a434b95a4a05a58057560565584f5404e388425382f5202e128221a9224784d4604c510454402e0d022502644f8244e87c1a120198204e2764da6419130488764d0244c02e4b04e4a82c47c794704e46369493614893347c7a470764636a45b66188124446b439664314e50c6b4f26b4ca434b96a181224a06a49867480664684f4504e320424482f4282e0b8224008c401712c82e3e96b3e1633187c41a7341172169224087f3f87e3f07d3d87c310752e8743d072308552e0542c02f2802e028223c2663b824160203aa7615930340762d8643a024390562b82e3708c3857f37d7d36d7731575300562b02e3497c35c6d2ec65351633414b330663282c3187c2a82e2a02e3167630d76300762982e150202f56a2ed662e4662d949148122c88c2a8842a0642bd7d2ad752ae762a5762c6772b076298662897e2856727966271563cd673b26b39a5b141223886a36067338663205a2f8572d0562902f2682e010222488c24b71243691d132178321c932170322047925c73254711c242169422387e2307c0a07422872098540704e0284220d6a2046a21c661ea6a1a96a0d06a090660685c0604c20d7a2047a0f0760504c1f8441ec6b1e24e159420e8661d07e1c87c1a1481c5671ba561915a1a254199241ac6b192421894e0e0661787e1707c15154161241514816d6715a5a14956138561304e1257d11c7110c6d0a46506369103630fb610f34b0e94a0e04a0d46b0c8660c04e0ad6a0a56609c660936b0535908b510756706c6a0636a05b660535a04b560387e0307c02d670206601856225672146b1f45b1da5a1b2421815a141421286a110670d8660b85a0b057080560784f0404e0104298c579135b8534b7e15b7314b5b9335185b4204b26033008130003f 15 5 11 9 6
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsF fullMask g_50 bds_50 (dagRefF 344 (dagTraceF fullMask rootStock 11 f_50) l_50 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_0 : treeBlockF 0 32 (dagCheckNodeF fullMask g_50 bds_50 344 (dagTraceF fullMask rootStock 11 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_1 : treeBlockF 32 64 (dagCheckNodeF fullMask g_50 bds_50 344 (dagTraceF fullMask rootStock 11 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_2 : treeBlockF 64 96 (dagCheckNodeF fullMask g_50 bds_50 344 (dagTraceF fullMask rootStock 11 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_3 : treeBlockF 96 128 (dagCheckNodeF fullMask g_50 bds_50 344 (dagTraceF fullMask rootStock 11 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_4 : treeBlockF 128 160 (dagCheckNodeF fullMask g_50 bds_50 344 (dagTraceF fullMask rootStock 11 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_5 : treeBlockF 160 192 (dagCheckNodeF fullMask g_50 bds_50 344 (dagTraceF fullMask rootStock 11 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_6 : treeBlockF 192 224 (dagCheckNodeF fullMask g_50 bds_50 344 (dagTraceF fullMask rootStock 11 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_7 : treeBlockF 224 256 (dagCheckNodeF fullMask g_50 bds_50 344 (dagTraceF fullMask rootStock 11 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_8 : treeBlockF 256 288 (dagCheckNodeF fullMask g_50 bds_50 344 (dagTraceF fullMask rootStock 11 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_9 : treeBlockF 288 320 (dagCheckNodeF fullMask g_50 bds_50 344 (dagTraceF fullMask rootStock 11 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_10 : treeBlockF 320 344 (dagCheckNodeF fullMask g_50 bds_50 344 (dagTraceF fullMask rootStock 11 f_50) l_50) = true := by decide +kernel
theorem nj_50_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF fullMask g_50 bds_50 344 (dagTraceF fullMask rootStock 11 f_50) l_50) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_50_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_50_1 h1 h2)
theorem nj_50_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF fullMask g_50 bds_50 344 (dagTraceF fullMask rootStock 11 f_50) l_50) i = true := block_join nj_50_1 (fun _ h1 h2 => treeBlockF_at nb_50_2 h1 h2)
theorem nj_50_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF fullMask g_50 bds_50 344 (dagTraceF fullMask rootStock 11 f_50) l_50) i = true := block_join nj_50_2 (fun _ h1 h2 => treeBlockF_at nb_50_3 h1 h2)
theorem nj_50_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF fullMask g_50 bds_50 344 (dagTraceF fullMask rootStock 11 f_50) l_50) i = true := block_join nj_50_3 (fun _ h1 h2 => treeBlockF_at nb_50_4 h1 h2)
theorem nj_50_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF fullMask g_50 bds_50 344 (dagTraceF fullMask rootStock 11 f_50) l_50) i = true := block_join nj_50_4 (fun _ h1 h2 => treeBlockF_at nb_50_5 h1 h2)
theorem nj_50_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF fullMask g_50 bds_50 344 (dagTraceF fullMask rootStock 11 f_50) l_50) i = true := block_join nj_50_5 (fun _ h1 h2 => treeBlockF_at nb_50_6 h1 h2)
theorem nj_50_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF fullMask g_50 bds_50 344 (dagTraceF fullMask rootStock 11 f_50) l_50) i = true := block_join nj_50_6 (fun _ h1 h2 => treeBlockF_at nb_50_7 h1 h2)
theorem nj_50_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF fullMask g_50 bds_50 344 (dagTraceF fullMask rootStock 11 f_50) l_50) i = true := block_join nj_50_7 (fun _ h1 h2 => treeBlockF_at nb_50_8 h1 h2)
theorem nj_50_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF fullMask g_50 bds_50 344 (dagTraceF fullMask rootStock 11 f_50) l_50) i = true := block_join nj_50_8 (fun _ h1 h2 => treeBlockF_at nb_50_9 h1 h2)
theorem nj_50_10 : ∀ i, 0 ≤ i → i < 344 → (dagCheckNodeF fullMask g_50 bds_50 344 (dagTraceF fullMask rootStock 11 f_50) l_50) i = true := block_join nj_50_9 (fun _ h1 h2 => treeBlockF_at nb_50_10 h1 h2)
theorem nc_50 : ∀ i, 0 ≤ i → i < 344 → (dagCheckNodeF fullMask g_50 bds_50 344 (dagTraceF fullMask rootStock 11 f_50) l_50) i = true := nj_50_10
theorem lb_50 : LowerBin fullMask rootStock g_50 12 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_50 sub_50 gl_50 rc_50 nc_50

def wg : List Gate := [⟨GateOp.and, [5, 4]⟩, ⟨GateOp.or, [5, 4]⟩, ⟨GateOp.and, [3, 2]⟩, ⟨GateOp.or, [3, 2]⟩, ⟨GateOp.and, [7, 9]⟩, ⟨GateOp.or, [6, 2]⟩, ⟨GateOp.and, [11, 1]⟩, ⟨GateOp.and, [9, 0]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [8, 1]⟩, ⟨GateOp.and, [15, 0]⟩, ⟨GateOp.or, [10, 16]⟩, ⟨GateOp.and, [17, 14]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4008241888 * 2 ^ 32 + 3940591744) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4008241888 * 2 ^ 32 + 3940591744)) (13 - 1) := by
  rw [show canon fullMask (4008241888 * 2 ^ 32 + 3940591744) = g_50 by decide]
  exact lb_50

end PEqualNP.Outside.L_meta_47537

theorem PEqualNP.Outside.L_meta_47537 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241888 * 2 ^ 32 + 3940591744) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241888 * 2 ^ 32 + 3940591744) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_47537.table2_from_lowerBin (4008241888 * 2 ^ 32 + 3940591744) 13 PEqualNP.Outside.L_meta_47537.root_lb PEqualNP.Outside.L_meta_47537.wg 18 rfl PEqualNP.Outside.L_meta_47537.wfits PEqualNP.Outside.L_meta_47537.weval
