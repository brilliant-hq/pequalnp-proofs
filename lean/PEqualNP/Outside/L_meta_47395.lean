import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47395

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

theorem certBlock {lo hi : Nat} {f : Nat → Bool} (h : treeBlockF lo hi f = true) :
    ∀ i, lo ≤ i → i < hi → f i = true :=
  fun _ hi₁ hi₂ => treeBlockF_at h hi₁ hi₂

theorem joinChecks {lo mid hi : Nat} {f : Nat → Bool}
    (left : ∀ i, lo ≤ i → i < mid → f i = true)
    (right : ∀ i, mid ≤ i → i < hi → f i = true) :
    ∀ i, lo ≤ i → i < hi → f i = true := by
  intro i h₁ h₂
  by_cases hl : i < mid
  · exact left i h₁ hl
  · exact right i (Nat.le_of_not_gt hl) h₂

def selectRows (w : Nat) : List Nat → Nat
  | [] => 0
  | p :: ps => 2 * selectRows w ps + (w.testBit p).toNat

theorem selectRows_testBit (w : Nat) (rows : List Nat) (i : Nat) :
    (selectRows w rows).testBit i = (rows[i]?).any w.testBit := by
  induction rows generalizing i with
  | nil => simp [selectRows]
  | cons p ps ih =>
    cases i with
    | zero =>
      simp only [selectRows, Nat.testBit_zero, List.getElem?_cons_zero, Option.any_some]
      cases w.testBit p
      · change decide ((2 * selectRows w ps + 0) % 2 = 1) = false
        simp
      · change decide ((2 * selectRows w ps + 1) % 2 = 1) = true
        have ht : (2 * selectRows w ps + 1) % 2 = 1 := by omega
        simp [ht]
    | succ i =>
      simp only [selectRows, Nat.testBit_succ, List.getElem?_cons_succ]
      have hd : (2 * selectRows w ps + (w.testBit p).toNat) / 2 = selectRows w ps := by
        cases w.testBit p
        · change (2 * selectRows w ps + 0) / 2 = selectRows w ps
          omega
        · change (2 * selectRows w ps + 1) / 2 = selectRows w ps
          omega
      rw [hd, ih]

theorem selectRows_zero (rows : List Nat) : selectRows 0 rows = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [selectRows_testBit, Nat.zero_testBit]
  cases rows[i]? <;> simp [Nat.zero_testBit]

theorem selectRows_and (rows : List Nat) (x y : Nat) :
    selectRows (x &&& y) rows = selectRows x rows &&& selectRows y rows := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, selectRows_testBit]
  cases rows[i]? <;> simp [Nat.testBit_and]

theorem selectRows_or (rows : List Nat) (x y : Nat) :
    selectRows (x ||| y) rows = selectRows x rows ||| selectRows y rows := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_or, selectRows_testBit]
  cases rows[i]? <;> simp [Nat.testBit_or]

theorem selectRows_xor (rows : List Nat) (x y : Nat) :
    selectRows (x ^^^ y) rows = selectRows x rows ^^^ selectRows y rows := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_xor, selectRows_testBit]
  cases rows[i]? <;> simp [Nat.testBit_xor]

def rowProjection (rows : List Nat) (cut w : Nat) := canon cut (selectRows w rows)

theorem rowProjection_zero (rows : List Nat) (cut : Nat) :
    rowProjection rows cut 0 = 0 := by
  simp [rowProjection, selectRows_zero, canon_zero]

theorem rowProjection_canon {rows : List Nat} {mask cut : Nat}
    (hm : selectRows mask rows = cut) (w : Nat) :
    rowProjection rows cut (canon mask w) = rowProjection rows cut w := by
  have hp : rowProjection rows cut (w &&& mask) = rowProjection rows cut w := by
    simp only [rowProjection, selectRows_and, hm, canon_land]
  rcases canon_cases mask w with ⟨he, h0 | h1⟩ | ⟨_, h0 | h1⟩
  · rw [he, rowProjection_zero, ← hp, h0, rowProjection_zero]
  · rw [he, rowProjection_zero, ← hp, h1]
    simp [rowProjection, hm, canon_self]
  · rw [h0, hp]
  · rw [h1, ← hp]
    simp only [rowProjection, selectRows_xor, hm, canon_xor_mask]

theorem rowProjection_op {rows : List Nat} {mask cut : Nat}
    (hm : selectRows mask rows = cut) (op a b : Nat) :
    rowProjection rows cut (binOp mask op a b) =
      binOp cut op (selectRows a rows) (selectRows b rows) := by
  unfold binOp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;>
    simp only [bsel_true, bsel_false, rowProjection_canon hm] <;>
    simp only [rowProjection, selectRows_and, selectRows_or, selectRows_xor, hm]

theorem rowProjection_avail {rows : List Nat} {mask cut : Nat} {big small : List Nat}
    (hm : selectRows mask rows = cut)
    (sub : ∀ x, Avail big x → Avail small (rowProjection rows cut x)) {y : Nat}
    (gate : GateBin mask big y) : GateBin cut small (rowProjection rows cut y) := by
  obtain ⟨a, b, op, _, ha, hb, rfl⟩ := gate
  have ea := sub a ha
  have eb := sub b hb
  have ca : canon cut (rowProjection rows cut a) = rowProjection rows cut a :=
    canon_idem _ _
  have cb : canon cut (rowProjection rows cut b) = rowProjection rows cut b :=
    canon_idem _ _
  have eq := rowProjection_op hm op a b
  have hs := canon_sub_binOp (op := op) (a := selectRows a rows)
    (b := selectRows b rows) (masked_self cut)
  rw [binOp_canon, ← eq] at hs
  change _ = 0 ∨ _ = rowProjection rows cut a ∨ _ = rowProjection rows cut b ∨ _ at hs
  rcases hs with h | h | h | ⟨op', hop', h⟩
  · exact ⟨0, 0, 0, by decide, Or.inl rfl, Or.inl rfl, by
      rw [h]; simp [binOp, bsel, canon_zero]⟩
  · exact ⟨_, _, 0, by decide, ea, ea, by rw [h]; simpa [binOp, bsel] using ca.symm⟩
  · exact ⟨_, _, 0, by decide, eb, eb, by rw [h]; simpa [binOp, bsel] using cb.symm⟩
  · exact ⟨_, _, op', hop', ea, eb, h⟩

theorem rowProjection_builds {rows : List Nat} {mask cut : Nat} {big small : List Nat}
    (hm : selectRows mask rows = cut)
    (sub : ∀ x, Avail big x → Avail small (rowProjection rows cut x))
    {vs : List Nat} (h : BuildsBin mask big vs) :
    BuildsBin cut small (vs.map (rowProjection rows cut)) := by
  induction vs generalizing big small with
  | nil => trivial
  | cons x xs ih =>
    refine ⟨rowProjection_avail hm sub h.1, ih ?_ h.2⟩
    intro y hy
    rcases hy with hz | hmem
    · exact Or.inl (by rw [hz, rowProjection_zero])
    · rcases List.mem_cons.mp hmem with rfl | hmem
      · exact Or.inr List.mem_cons_self
      · exact avail_weaken (fun z hz => List.mem_cons_of_mem _ hz) (sub y (Or.inr hmem))

theorem lowerByRows {mask cut goal smallGoal n : Nat} {big small : List Nat}
    (rows : List Nat) (hm : selectRows mask rows = cut)
    (hs : ∀ w ∈ big, Avail small (rowProjection rows cut w))
    (hg : rowProjection rows cut goal = smallGoal)
    (cert : LowerBin cut small smallGoal n) : LowerBin mask big goal n := by
  intro vs hv ha
  have sub (w : Nat) (hw : Avail big w) : Avail small (rowProjection rows cut w) := by
    rcases hw with rfl | hw
    · exact Or.inl (rowProjection_zero rows cut)
    · exact hs w hw
  have hv' := rowProjection_builds hm sub hv
  have ha' : Avail (vs.map (rowProjection rows cut) ++ small) smallGoal := by
    rw [← hg]
    rcases ha with rfl | ha
    · exact Or.inl (rowProjection_zero rows cut)
    · rcases List.mem_append.mp ha with ha | ha
      · exact Or.inr (List.mem_append_left _ (List.mem_map_of_mem ha))
      · exact avail_weaken (fun w hw => List.mem_append_right _ hw) (hs _ ha)
  simpa only [List.length_map] using cert _ hv' ha'

def f_12 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_12 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
def m_12 : Nat := 0xaaaa
def s_12 : List Nat := [0x2222, 0xa0a, 0xaa]
def g_12 : Nat := 0x22a
def bds_12 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_12 : KnownBin bds_12 := by
  intro b hb
  simp [bds_12] at hb
theorem sub_12 : ∀ b ∈ bds_12, m_12 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_12] at hb
theorem gl_12 : ∀ b ∈ bds_12, canon b.1 g_12 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_12] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_12 : dagCheckRootsF m_12 g_12 bds_12 (dagRefF 1 (dagTraceF m_12 s_12 3 f_12) l_12 0) s_12 3 = true := by decide +kernel
def node_12 : Nat → Bool := dagCheckNodeF m_12 g_12 bds_12 1 (dagTraceF m_12 s_12 3 f_12) l_12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_12_0 : treeBlockF 0 1 node_12 = true := by decide +kernel
theorem nc_12 : ∀ j, 0 ≤ j → j < 1 → node_12 j = true :=
  (certBlock nb_12_0)
theorem lb_12 : LowerBin m_12 s_12 g_12 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_12 sub_12 gl_12 rc_12 nc_12

def m_32 : Nat := 0xaa00aa
def s_32 : List Nat := [0x220022, 0xa000a, 0xaa]
def g_32 : Nat := 0x2002a
theorem lb_32 : LowerBin m_32 s_32 g_32 4 := by
  refine lowerByRows [0, 1, 0, 3, 0, 5, 0, 7, 0, 17, 0, 19, 0, 21, 0, 23] (by decide +kernel) ?_ (by decide +kernel) lb_12
  intro w hw
  simp only [s_32, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_127 : Nat := 0xff000000
def s_127 : List Nat := [0x55000000, 0x33000000, 0xf000000]
def g_127 : Nat := 0x17000000
theorem lb_127 : LowerBin m_127 s_127 g_127 4 := by
  refine lowerByRows [0, 24, 0, 25, 0, 26, 0, 27, 0, 28, 0, 29, 0, 30, 0, 31] (by decide +kernel) ?_ (by decide +kernel) lb_12
  intro w hw
  simp only [s_127, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_143 : Nat := 0xaa000000aa
def s_143 : List Nat := [0x2200000022, 0xa0000000a, 0xaa]
def g_143 : Nat := 0x20000002a
theorem lb_143 : LowerBin m_143 s_143 g_143 4 := by
  refine lowerByRows [0, 1, 0, 3, 0, 5, 0, 7, 0, 33, 0, 35, 0, 37, 0, 39] (by decide +kernel) ?_ (by decide +kernel) lb_12
  intro w hw
  simp only [s_143, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_248 : Nat := 0xff0000000000
def s_248 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_248 : Nat := 0x170000000000
theorem lb_248 : LowerBin m_248 s_248 g_248 4 := by
  refine lowerByRows [0, 40, 0, 41, 0, 42, 0, 43, 0, 44, 0, 45, 0, 46, 0, 47] (by decide +kernel) ?_ (by decide +kernel) lb_12
  intro w hw
  simp only [s_248, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_354 : Nat := 0xff000000000000
def s_354 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_354 : Nat := 0x17000000000000
theorem lb_354 : LowerBin m_354 s_354 g_354 4 := by
  refine lowerByRows [0, 48, 0, 49, 0, 50, 0, 51, 0, 52, 0, 53, 0, 54, 0, 55] (by decide +kernel) ?_ (by decide +kernel) lb_12
  intro w hw
  simp only [s_354, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_517 : Nat := 0x4040404040404040
def s_517 : List Nat := [0x40004000400040, 0x404000004040, 0x40404040]
def g_517 : Nat := 0x4000404040
theorem lb_517 : LowerBin m_517 s_517 g_517 4 := by
  refine lowerByRows [0, 6, 0, 14, 0, 22, 0, 30, 0, 38, 0, 46, 0, 54, 0, 62] (by decide +kernel) ?_ (by decide +kernel) lb_12
  intro w hw
  simp only [s_517, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_673 : Nat → Nat × Nat := fun _ => (0, 0)
def l_673 : Nat → Nat → Option Nat := fun _ _ => none
def m_673 : Nat := 0xff00ff
def s_673 : List Nat := [0x550055, 0x330033, 0xf000f, 0xff]
def g_673 : Nat := 0x57007f
def bds_673 : List (Nat × List Nat × Nat × Nat) := [(m_32, s_32, 4, g_32)]
theorem kn_673 : KnownBin bds_673 := by
  intro b hb
  simp only [bds_673, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_32
theorem sub_673 : ∀ b ∈ bds_673, m_673 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_673, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_673 : ∀ b ∈ bds_673, canon b.1 g_673 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_673, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_673 : dagCheckRootsF m_673 g_673 bds_673 (dagRefF 0 (dagTraceF m_673 s_673 4 f_673) l_673 0) s_673 4 = true := by decide +kernel
def node_673 : Nat → Bool := dagCheckNodeF m_673 g_673 bds_673 0 (dagTraceF m_673 s_673 4 f_673) l_673
theorem nc_673 : ∀ j, 0 ≤ j → j < 0 → node_673 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_673 : LowerBin m_673 s_673 g_673 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_673 sub_673 gl_673 rc_673 nc_673

def f_691 : Nat → Nat × Nat := fun _ => (0, 0)
def l_691 : Nat → Nat → Option Nat := fun _ _ => none
def m_691 : Nat := 0xaaaaaaaa
def s_691 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_691 : Nat := 0x202022a
def bds_691 : List (Nat × List Nat × Nat × Nat) := [(m_32, s_32, 4, g_32)]
theorem kn_691 : KnownBin bds_691 := by
  intro b hb
  simp only [bds_691, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_32
theorem sub_691 : ∀ b ∈ bds_691, m_691 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_691, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_691 : ∀ b ∈ bds_691, canon b.1 g_691 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_691, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_691 : dagCheckRootsF m_691 g_691 bds_691 (dagRefF 0 (dagTraceF m_691 s_691 4 f_691) l_691 0) s_691 4 = true := by decide +kernel
def node_691 : Nat → Bool := dagCheckNodeF m_691 g_691 bds_691 0 (dagTraceF m_691 s_691 4 f_691) l_691
theorem nc_691 : ∀ j, 0 ≤ j → j < 0 → node_691 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_691 : LowerBin m_691 s_691 g_691 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_691 sub_691 gl_691 rc_691 nc_691

def f_695 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_695 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
def m_695 : Nat := 0xcccccccc
def s_695 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_695 : Nat := 0x444444c
def bds_695 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_695 : KnownBin bds_695 := by
  intro b hb
  simp [bds_695] at hb
theorem sub_695 : ∀ b ∈ bds_695, m_695 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_695] at hb
theorem gl_695 : ∀ b ∈ bds_695, canon b.1 g_695 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_695] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_695 : dagCheckRootsF m_695 g_695 bds_695 (dagRefF 64 (dagTraceF m_695 s_695 5 f_695) l_695 0) s_695 5 = true := by decide +kernel
def node_695 : Nat → Bool := dagCheckNodeF m_695 g_695 bds_695 64 (dagTraceF m_695 s_695 5 f_695) l_695
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_695_0 : treeBlockF 0 32 node_695 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_695_1 : treeBlockF 32 64 node_695 = true := by decide +kernel
theorem nc_695 : ∀ j, 0 ≤ j → j < 64 → node_695 j = true :=
  (joinChecks (certBlock nb_695_0) (certBlock nb_695_1))
theorem lb_695 : LowerBin m_695 s_695 g_695 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_695 sub_695 gl_695 rc_695 nc_695

def f_700 : Nat → Nat × Nat := fun _ => (0, 0)
def l_700 : Nat → Nat → Option Nat := fun _ _ => none
def m_700 : Nat := 0xff00ff00
def s_700 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_700 : Nat := 0x17005700
def bds_700 : List (Nat × List Nat × Nat × Nat) := [(m_127, s_127, 4, g_127)]
theorem kn_700 : KnownBin bds_700 := by
  intro b hb
  simp only [bds_700, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_127
theorem sub_700 : ∀ b ∈ bds_700, m_700 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_700, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_700 : ∀ b ∈ bds_700, canon b.1 g_700 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_700, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_700 : dagCheckRootsF m_700 g_700 bds_700 (dagRefF 0 (dagTraceF m_700 s_700 4 f_700) l_700 0) s_700 4 = true := by decide +kernel
def node_700 : Nat → Bool := dagCheckNodeF m_700 g_700 bds_700 0 (dagTraceF m_700 s_700 4 f_700) l_700
theorem nc_700 : ∀ j, 0 ≤ j → j < 0 → node_700 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_700 : LowerBin m_700 s_700 g_700 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_700 sub_700 gl_700 rc_700 nc_700

def f_702 : Nat → Nat × Nat := fun _ => (0, 0)
def l_702 : Nat → Nat → Option Nat := fun _ _ => none
def m_702 : Nat := 0xff000000ff
def s_702 : List Nat := [0x5500000055, 0x3300000033, 0xf0000000f, 0xff]
def g_702 : Nat := 0x570000007f
def bds_702 : List (Nat × List Nat × Nat × Nat) := [(m_143, s_143, 4, g_143)]
theorem kn_702 : KnownBin bds_702 := by
  intro b hb
  simp only [bds_702, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_143
theorem sub_702 : ∀ b ∈ bds_702, m_702 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_702, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_702 : ∀ b ∈ bds_702, canon b.1 g_702 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_702, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_702 : dagCheckRootsF m_702 g_702 bds_702 (dagRefF 0 (dagTraceF m_702 s_702 4 f_702) l_702 0) s_702 4 = true := by decide +kernel
def node_702 : Nat → Bool := dagCheckNodeF m_702 g_702 bds_702 0 (dagTraceF m_702 s_702 4 f_702) l_702
theorem nc_702 : ∀ j, 0 ≤ j → j < 0 → node_702 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_702 : LowerBin m_702 s_702 g_702 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_702 sub_702 gl_702 rc_702 nc_702

def f_724 : Nat → Nat × Nat := fun _ => (0, 0)
def l_724 : Nat → Nat → Option Nat := fun _ _ => none
def m_724 : Nat := 0xaaaa0000aaaa
def s_724 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_724 : Nat := 0x2020000022a
def bds_724 : List (Nat × List Nat × Nat × Nat) := [(m_143, s_143, 4, g_143)]
theorem kn_724 : KnownBin bds_724 := by
  intro b hb
  simp only [bds_724, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_143
theorem sub_724 : ∀ b ∈ bds_724, m_724 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_724, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_724 : ∀ b ∈ bds_724, canon b.1 g_724 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_724, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_724 : dagCheckRootsF m_724 g_724 bds_724 (dagRefF 0 (dagTraceF m_724 s_724 4 f_724) l_724 0) s_724 4 = true := by decide +kernel
def node_724 : Nat → Bool := dagCheckNodeF m_724 g_724 bds_724 0 (dagTraceF m_724 s_724 4 f_724) l_724
theorem nc_724 : ∀ j, 0 ≤ j → j < 0 → node_724 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_724 : LowerBin m_724 s_724 g_724 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_724 sub_724 gl_724 rc_724 nc_724

def m_729 : Nat := 0xcccc0000cccc
def s_729 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_729 : Nat := 0x4440000444c
theorem lb_729 : LowerBin m_729 s_729 g_729 6 := by
  refine lowerByRows [0, 0, 2, 3, 0, 0, 6, 7, 0, 0, 10, 11, 0, 0, 14, 15, 0, 0, 34, 35, 0, 0, 38, 39, 0, 0, 42, 43, 0, 0, 46, 47] (by decide +kernel) ?_ (by decide +kernel) lb_695
  intro w hw
  simp only [s_729, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_736 : Nat → Nat × Nat := fun _ => (0, 0)
def l_736 : Nat → Nat → Option Nat := fun _ _ => none
def m_736 : Nat := 0xff000000ff00
def s_736 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_736 : Nat := 0x170000005700
def bds_736 : List (Nat × List Nat × Nat × Nat) := [(m_248, s_248, 4, g_248)]
theorem kn_736 : KnownBin bds_736 := by
  intro b hb
  simp only [bds_736, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_248
theorem sub_736 : ∀ b ∈ bds_736, m_736 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_736, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_736 : ∀ b ∈ bds_736, canon b.1 g_736 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_736, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_736 : dagCheckRootsF m_736 g_736 bds_736 (dagRefF 0 (dagTraceF m_736 s_736 4 f_736) l_736 0) s_736 4 = true := by decide +kernel
def node_736 : Nat → Bool := dagCheckNodeF m_736 g_736 bds_736 0 (dagTraceF m_736 s_736 4 f_736) l_736
theorem nc_736 : ∀ j, 0 ≤ j → j < 0 → node_736 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_736 : LowerBin m_736 s_736 g_736 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_736 sub_736 gl_736 rc_736 nc_736

def f_761 : Nat → Nat × Nat := fun _ => (0, 0)
def l_761 : Nat → Nat → Option Nat := fun _ _ => none
def m_761 : Nat := 0xaa00aa00aa00aa
def s_761 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_761 : Nat := 0x200020002002a
def bds_761 : List (Nat × List Nat × Nat × Nat) := [(m_143, s_143, 4, g_143)]
theorem kn_761 : KnownBin bds_761 := by
  intro b hb
  simp only [bds_761, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_143
theorem sub_761 : ∀ b ∈ bds_761, m_761 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_761, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_761 : ∀ b ∈ bds_761, canon b.1 g_761 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_761, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_761 : dagCheckRootsF m_761 g_761 bds_761 (dagRefF 0 (dagTraceF m_761 s_761 4 f_761) l_761 0) s_761 4 = true := by decide +kernel
def node_761 : Nat → Bool := dagCheckNodeF m_761 g_761 bds_761 0 (dagTraceF m_761 s_761 4 f_761) l_761
theorem nc_761 : ∀ j, 0 ≤ j → j < 0 → node_761 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_761 : LowerBin m_761 s_761 g_761 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_761 sub_761 gl_761 rc_761 nc_761

def m_767 : Nat := 0xcc00cc00cc00cc
def s_767 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_767 : Nat := 0x400440044004c
theorem lb_767 : LowerBin m_767 s_767 g_767 6 := by
  refine lowerByRows [0, 0, 2, 3, 0, 0, 6, 7, 0, 0, 18, 19, 0, 0, 22, 23, 0, 0, 34, 35, 0, 0, 38, 39, 0, 0, 50, 51, 0, 0, 54, 55] (by decide +kernel) ?_ (by decide +kernel) lb_695
  intro w hw
  simp only [s_767, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_772 : Nat := 0xf000f000f000f0
def s_772 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_772 : Nat := 0x10005000500070
theorem lb_772 : LowerBin m_772 s_772 g_772 6 := by
  refine lowerByRows [0, 0, 4, 5, 0, 0, 6, 7, 0, 0, 20, 21, 0, 0, 22, 23, 0, 0, 36, 37, 0, 0, 38, 39, 0, 0, 52, 53, 0, 0, 54, 55] (by decide +kernel) ?_ (by decide +kernel) lb_695
  intro w hw
  simp only [s_772, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_776 : Nat → Nat × Nat := fun _ => (0, 0)
def l_776 : Nat → Nat → Option Nat := fun _ _ => none
def m_776 : Nat := 0xff000000ff0000
def s_776 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_776 : Nat := 0x17000000570000
def bds_776 : List (Nat × List Nat × Nat × Nat) := [(m_354, s_354, 4, g_354)]
theorem kn_776 : KnownBin bds_776 := by
  intro b hb
  simp only [bds_776, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_354
theorem sub_776 : ∀ b ∈ bds_776, m_776 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_776, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_776 : ∀ b ∈ bds_776, canon b.1 g_776 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_776, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_776 : dagCheckRootsF m_776 g_776 bds_776 (dagRefF 0 (dagTraceF m_776 s_776 4 f_776) l_776 0) s_776 4 = true := by decide +kernel
def node_776 : Nat → Bool := dagCheckNodeF m_776 g_776 bds_776 0 (dagTraceF m_776 s_776 4 f_776) l_776
theorem nc_776 : ∀ j, 0 ≤ j → j < 0 → node_776 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_776 : LowerBin m_776 s_776 g_776 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_776 sub_776 gl_776 rc_776 nc_776

def f_778 : Nat → Nat × Nat := fun _ => (0, 0)
def l_778 : Nat → Nat → Option Nat := fun _ _ => none
def m_778 : Nat := 0xff00ff00000000
def s_778 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_778 : Nat := 0x17005700000000
def bds_778 : List (Nat × List Nat × Nat × Nat) := [(m_354, s_354, 4, g_354)]
theorem kn_778 : KnownBin bds_778 := by
  intro b hb
  simp only [bds_778, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_354
theorem sub_778 : ∀ b ∈ bds_778, m_778 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_778, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_778 : ∀ b ∈ bds_778, canon b.1 g_778 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_778, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_778 : dagCheckRootsF m_778 g_778 bds_778 (dagRefF 0 (dagTraceF m_778 s_778 4 f_778) l_778 0) s_778 4 = true := by decide +kernel
def node_778 : Nat → Bool := dagCheckNodeF m_778 g_778 bds_778 0 (dagTraceF m_778 s_778 4 f_778) l_778
theorem nc_778 : ∀ j, 0 ≤ j → j < 0 → node_778 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_778 : LowerBin m_778 s_778 g_778 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_778 sub_778 gl_778 rc_778 nc_778

def m_798 : Nat := 0xa0a0a0a0a0a0a0a
def s_798 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_798 : Nat := 0x202020202020a
theorem lb_798 : LowerBin m_798 s_798 g_798 6 := by
  refine lowerByRows [0, 0, 1, 3, 0, 0, 9, 11, 0, 0, 17, 19, 0, 0, 25, 27, 0, 0, 33, 35, 0, 0, 41, 43, 0, 0, 49, 51, 0, 0, 57, 59] (by decide +kernel) ?_ (by decide +kernel) lb_695
  intro w hw
  simp only [s_798, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_832 : Nat := 0x2222222222222222
def s_832 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_832 : Nat := 0x2020202020222
theorem lb_832 : LowerBin m_832 s_832 g_832 6 := by
  refine lowerByRows [0, 0, 1, 5, 0, 0, 9, 13, 0, 0, 17, 21, 0, 0, 25, 29, 0, 0, 33, 37, 0, 0, 41, 45, 0, 0, 49, 53, 0, 0, 57, 61] (by decide +kernel) ?_ (by decide +kernel) lb_695
  intro w hw
  simp only [s_832, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_860 : Nat → Nat × Nat := fun _ => (0, 0)
def l_860 : Nat → Nat → Option Nat := fun _ _ => none
def m_860 : Nat := 0x4444444444444444
def s_860 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_860 : Nat := 0x404044404444444
def bds_860 : List (Nat × List Nat × Nat × Nat) := [(m_517, s_517, 4, g_517)]
theorem kn_860 : KnownBin bds_860 := by
  intro b hb
  simp only [bds_860, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_517
theorem sub_860 : ∀ b ∈ bds_860, m_860 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_860, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_860 : ∀ b ∈ bds_860, canon b.1 g_860 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_860, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_860 : dagCheckRootsF m_860 g_860 bds_860 (dagRefF 0 (dagTraceF m_860 s_860 4 f_860) l_860 0) s_860 4 = true := by decide +kernel
def node_860 : Nat → Bool := dagCheckNodeF m_860 g_860 bds_860 0 (dagTraceF m_860 s_860 4 f_860) l_860
theorem nc_860 : ∀ j, 0 ≤ j → j < 0 → node_860 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_860 : LowerBin m_860 s_860 g_860 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_860 sub_860 gl_860 rc_860 nc_860

def f_924 : Nat → Nat × Nat := fun _ => (0, 0)
def l_924 : Nat → Nat → Option Nat := fun _ _ => none
def m_924 : Nat := 0xc0c0c0c0c0c0c0c0
def s_924 : List Nat := [0x4040404040404040, 0xc000c000c000c0, 0xc0c00000c0c0, 0xc0c0c0c0]
def g_924 : Nat := 0x4000404040
def bds_924 : List (Nat × List Nat × Nat × Nat) := [(m_517, s_517, 4, g_517)]
theorem kn_924 : KnownBin bds_924 := by
  intro b hb
  simp only [bds_924, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_517
theorem sub_924 : ∀ b ∈ bds_924, m_924 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_924, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_924 : ∀ b ∈ bds_924, canon b.1 g_924 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_924, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_924 : dagCheckRootsF m_924 g_924 bds_924 (dagRefF 0 (dagTraceF m_924 s_924 4 f_924) l_924 0) s_924 4 = true := by decide +kernel
def node_924 : Nat → Bool := dagCheckNodeF m_924 g_924 bds_924 0 (dagTraceF m_924 s_924 4 f_924) l_924
theorem nc_924 : ∀ j, 0 ≤ j → j < 0 → node_924 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_924 : LowerBin m_924 s_924 g_924 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_924 sub_924 gl_924 rc_924 nc_924

def f_954 : Nat → Nat × Nat := fun _ => (0, 0)
def l_954 : Nat → Nat → Option Nat := fun _ _ => none
def m_954 : Nat := 0xff000000ff000000
def s_954 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_954 : Nat := 0x1500000017000000
def bds_954 : List (Nat × List Nat × Nat × Nat) := [(m_127, s_127, 4, g_127)]
theorem kn_954 : KnownBin bds_954 := by
  intro b hb
  simp only [bds_954, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_127
theorem sub_954 : ∀ b ∈ bds_954, m_954 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_954, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_954 : ∀ b ∈ bds_954, canon b.1 g_954 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_954, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_954 : dagCheckRootsF m_954 g_954 bds_954 (dagRefF 0 (dagTraceF m_954 s_954 4 f_954) l_954 0) s_954 4 = true := by decide +kernel
def node_954 : Nat → Bool := dagCheckNodeF m_954 g_954 bds_954 0 (dagTraceF m_954 s_954 4 f_954) l_954
theorem nc_954 : ∀ j, 0 ≤ j → j < 0 → node_954 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_954 : LowerBin m_954 s_954 g_954 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_954 sub_954 gl_954 rc_954 nc_954

def f_956 : Nat → Nat × Nat := fun _ => (0, 0)
def l_956 : Nat → Nat → Option Nat := fun _ _ => none
def m_956 : Nat := 0xff00ff0000000000
def s_956 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_956 : Nat := 0x1500170000000000
def bds_956 : List (Nat × List Nat × Nat × Nat) := [(m_248, s_248, 4, g_248)]
theorem kn_956 : KnownBin bds_956 := by
  intro b hb
  simp only [bds_956, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_248
theorem sub_956 : ∀ b ∈ bds_956, m_956 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_956, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_956 : ∀ b ∈ bds_956, canon b.1 g_956 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_956, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_956 : dagCheckRootsF m_956 g_956 bds_956 (dagRefF 0 (dagTraceF m_956 s_956 4 f_956) l_956 0) s_956 4 = true := by decide +kernel
def node_956 : Nat → Bool := dagCheckNodeF m_956 g_956 bds_956 0 (dagTraceF m_956 s_956 4 f_956) l_956
theorem nc_956 : ∀ j, 0 ≤ j → j < 0 → node_956 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_956 : LowerBin m_956 s_956 g_956 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_956 sub_956 gl_956 rc_956 nc_956

def f_958 : Nat → Nat × Nat := fun _ => (0, 0)
def l_958 : Nat → Nat → Option Nat := fun _ _ => none
def m_958 : Nat := 0x5555555555555555
def s_958 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_958 : Nat := 0x1515155515555555
def bds_958 : List (Nat × List Nat × Nat × Nat) := [(m_860, s_860, 5, g_860)]
theorem kn_958 : KnownBin bds_958 := by
  intro b hb
  simp only [bds_958, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_860
theorem sub_958 : ∀ b ∈ bds_958, m_958 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_958, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_958 : ∀ b ∈ bds_958, canon b.1 g_958 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_958, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_958 : dagCheckRootsF m_958 g_958 bds_958 (dagRefF 0 (dagTraceF m_958 s_958 5 f_958) l_958 0) s_958 5 = true := by decide +kernel
def node_958 : Nat → Bool := dagCheckNodeF m_958 g_958 bds_958 0 (dagTraceF m_958 s_958 5 f_958) l_958
theorem nc_958 : ∀ j, 0 ≤ j → j < 0 → node_958 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_958 : LowerBin m_958 s_958 g_958 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_958 sub_958 gl_958 rc_958 nc_958

def f_960 : Nat → Nat × Nat := unpackForestF 0xe19323a2e22343e43221301f 3 9
def l_960 : Nat → Nat → Option Nat := unpackLinksF 0x288a06986121c1 0xe19411a2e42263e432d2382321301f 6 2 9 3 3
def m_960 : Nat := 0xaaaaaaaaaaaaaaaa
def s_960 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_960 : Nat := 0x202020202022a
def bds_960 : List (Nat × List Nat × Nat × Nat) := [(m_724, s_724, 5, g_724), (m_691, s_691, 5, g_691), (m_761, s_761, 5, g_761), (m_798, s_798, 6, g_798), (m_832, s_832, 6, g_832)]
theorem kn_960 : KnownBin bds_960 := by
  intro b hb
  simp only [bds_960, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact lb_724
  · exact lb_691
  · exact lb_761
  · exact lb_798
  · exact lb_832
theorem sub_960 : ∀ b ∈ bds_960, m_960 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_960, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_960 : ∀ b ∈ bds_960, canon b.1 g_960 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_960, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_960 : dagCheckRootsF m_960 g_960 bds_960 (dagRefF 8 (dagTraceF m_960 s_960 7 f_960) l_960 0) s_960 7 = true := by decide +kernel
def node_960 : Nat → Bool := dagCheckNodeF m_960 g_960 bds_960 8 (dagTraceF m_960 s_960 7 f_960) l_960
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_960_0 : treeBlockF 0 8 node_960 = true := by decide +kernel
theorem nc_960 : ∀ j, 0 ≤ j → j < 8 → node_960 j = true :=
  (certBlock nb_960_0)
theorem lb_960 : LowerBin m_960 s_960 g_960 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_960 sub_960 gl_960 rc_960 nc_960

def f_961 : Nat → Nat × Nat := fun _ => (0, 0)
def l_961 : Nat → Nat → Option Nat := fun _ _ => none
def m_961 : Nat := 0x3333333333333333
def s_961 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_961 : Nat := 0x1113131313131333
def bds_961 : List (Nat × List Nat × Nat × Nat) := [(m_832, s_832, 6, g_832)]
theorem kn_961 : KnownBin bds_961 := by
  intro b hb
  simp only [bds_961, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_832
theorem sub_961 : ∀ b ∈ bds_961, m_961 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_961, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_961 : ∀ b ∈ bds_961, canon b.1 g_961 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_961, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_961 : dagCheckRootsF m_961 g_961 bds_961 (dagRefF 0 (dagTraceF m_961 s_961 6 f_961) l_961 0) s_961 6 = true := by decide +kernel
def node_961 : Nat → Bool := dagCheckNodeF m_961 g_961 bds_961 0 (dagTraceF m_961 s_961 6 f_961) l_961
theorem nc_961 : ∀ j, 0 ≤ j → j < 0 → node_961 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_961 : LowerBin m_961 s_961 g_961 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_961 sub_961 gl_961 rc_961 nc_961

def f_962 : Nat → Nat × Nat := unpackForestF 0xa0a92e88929a220a682a49a0a90e8294ba184fa86019a0a52682943a0a12e8383ea0e0ba82849a0a10c00b4fa044a6810299f68e67f93e9fe0667d9399f80fa7e02e9f60e400b4b9f04a67c0299b29467823b9e04ae7a1449e048e7802b9e2112780239b29427693e9da0666c9519ca4ee7292f9d2512729239ca06e730449ca04e6c9509c40fa7102e9b21466d03b9b40be6f0449b408e6d01f9b61126d0139b214000b479aa9266a9499aa1265cb5e9a44a6690299728e6662439984ae661239980ae660239728e26493e9920665c93998650e6192f98648e6181b98604e5c9389800fa6002e9720e65d0439740be5d02397407e5d0139720e000b4396c5065b04195e91a599469660665792996011a5802e95e0a400a4b90917e559489561224245390893e5335c94c9b25324c90892e4224793ed7a4fb5293e90a4f94193e1064224693a9324bb5492e9b24d24492e9324b92892e0a2422439084ae499469260664212991c5b24715c91c5524701890848e4202b91411a4502e9080a64286c90a1724285490a0b24202300290e22c5f902d2a22c5e8fc5823f06088b15e3dc5e8f691622c528f04a63c02988ad6a3ac6c8eada222a5f8ded7637b558de92a379498de12622a5e8cedb233a548d6d7233a4c8ce8f2339288ce0a222a5b8cb17222a578c6972303648c09523024c88a94e2c25e8b09762c2468b09162c23d8b04a62c02988a94a2292b8a517a294528a457a2901988a4a62795489e0622292388a0ae24c5e89314a2485e8920ba2282988c1522302c88a08c00a3b886d721fb428805022004087e91a1745e87917a1e34585cd4a1c9498721261725e86917a1a35286857a1a01985c4a617c5e85ed4a1785e85e0ba170290028ce16134836d2e14a388524d20db43848906122398488c61204183651a0fb4283e92a0fa4683e0a60d93e83811a0e03e8360640094b7c917e0bb4882e121f24537c8d4e092388244e2091347c8d2e0793881e4d1f23437c853e0525c8145b20513c7c852df2147806d7a01b5280690601942806105f2146802531fda547f65b1fd94c7fa511fd93c7f6061f21437c84fdfa3527e8d29fa24a7e8919fa0297c84f9f716c7dc571f71547dc4f1f70187c84cdf201b7d4119f503e7c8065f286c7ca171f28547ca131f201300250dcc45f7c2929cc45e7bcd81ef06073115dedc5e7b6515cc4527aed51eb9387ae4d1cc35b7a68e1e99387a64d1cc353730d2de793e79e065cc25a7991b1e626873057de335d78cd55e324978c529e3049730579df26c77c551df14c782971df13c77c4b1df01873056dde45c73055ddd15c76e991db95476e4f1cc15375e579d795d75e519d794575e4f9d792d75e065cc1527304fdd345e74d149d335274cd29d325e74c949d30297304f9d11547444f1d10187304cdcc01b739179ce452738179ce03e730065cc854732131cc0130024edcb25c724909c9a40726101c91466f3179c735471c8e1c71346f2d6dc61346f2d4dc4c5e712915bca5270c925c30496f2579bfc5e6fed69bfa5e6fe949bf9526fe0a5bc93e6f5179bd2526f4179bd03e6f2064009336ea561bb0406ea5516b45f6ded21b7a486e2061b79486de5116b45b6d2d81b4a606d25b1b49606d21816b4576c6d21b1a486c6521b19446c61216b4536bed19afa3a6be0e56b3526af179ae1446af149abb5e6aed49aba3a6ae0e56b34a6a0d49aa2346a0d29a82466a08f5a80295ac949a2c5e69a511a2c526968d1a2b5268ad29a2a5e68a949a2a3d68a0a56b24a684d81a12605ac57da005067cd159f0495ac5799ca6c6725319c93c6724b16b15b6671b199c60666d4199a506661816b15766257195a64656571959546565319593c6560616b15362c5798b15d62c5358b14662c5158b1446465118b13d6425118b12d63c5318f14462c0698b01962c0618b84c62e1118b83c62e0b18b0165ac54989358624961890485ac53d8625c6185318613c61a531860185ac52d7dc5e5f71497d95e60e0617d9525f65197d93d5f64b57d81a5f60657fb4e5fed097d8185f80f17e02c5f60596b14a5f0d217c2485ac51d7445e5ea0e1744525e6d317435a5dcd41772505dc541770505d0d597513c5d44b1750185d0d39740415ac5197314c5c49517114c5c44f17112c5ac50d6b01b5b4d496d34a5b49496d24a5b41796d0465ac0656b84c5ae0f16b01300248d6a034566d2d689385a20d159b4359e09159a4b5984a16602456690d6492859209159a33584905612395848c5611415844e5611315661195e3425789295e2465784c55e1295660f95a2425688c95a14a5685195a13e56a5115a1325660b80084b4d917d57b4855e921364534d8d4d551385540e1550344d8d2d5383854e0d1363434d894d511285440a1510244d892d4f82853e091362435380a14e0244d88cd3604f52e5714b86c52e0b13604b4d811d4835e520d4948241520505480424d81194704c5105514406c5101314403c5121114402c4d810d3603f502d4940b4a50292940a465024a53603e4f61b13d85c4f61513d83c4f60b1360334d80bd39a524e69293994a4e65193993e4e64c93602e4da1b13685c4da1513684c4da0b13602300210d0745f4d25290745e4ccd813326041d15d31c5e4c6115074524bed512f8384be0d10735b4b64e12d8384b60d10735341cd2d2b2544ac0a12b02441c96d291284a40a12902441c94d0724b49a9512682849a091072334940f92502e41c56923c6c48e5a10705f482d7520b55482925209494821290705e4725b11c8544721311c83c4765711c82c4720710705b46f1710705746a171191644641511902c41c14d1505e454175150464541151503e4540b91501d41c1490703f44317910c52442d4910b4a44297910a524424a50703e43a1510e83c43a0b10703341c0bd09c5e42714909a524269290995e4265490993e4264c90702e41e1510784c41e0b1070230020ed0615c41050904a40412501040463c1179023544084e1020343c0d6d010343c0d4cff2543fc4a0ff0243c096cfe0243c094cfc2543f04a0fc0243c08ccfac5e3ea514f01523e4924f91493c0178f545e3d4d68f525e3d4948f51313d44a4f50523c00f8f0c5e3c2968f0a323c2578f09523c24f8f09323c2148f002e0020ccee0583ba500ee05421f17ceb3483ac520ec02c3ac120eb04421f16ce83603a0980e81603a01b0e806021f15ce5348394920e5148394120e504421f14ce334638c8e4e313a21ed48df45e386110df45237cd78df35237c8e4df13a21ed28dc24c3704a0dd0443700a0dc02421e96cda82836a09087a533640a0d902421e92cd6a4c35a4a0d682835a09087a433560d0d13523520d0d134a344978d3244344948d124a344918d112a21e8c4ccb5233e4d0ccb4a33a490cca31332518cc93d3324b887952317178cb044317148ca134316d48c5b4a320910c81243168c4c595e316548c593d3164b88794a310d80c416021e17cc3150306d14c19493064848785e2fc5b0bf04c2fc0b0bf01c21e16cbc46c2f1180bc3502f0980bc15021e15cbb05c2e0590b805c2e0150b804c2e00f0b802c21e14caca312b2178ac85d2b2134ac8462b2114b41212b2110b30442b20f4ac82e2c4130b10442b20b4ac82c2ba130ae8442ba0f0ac8252b4110ad0242b2074878522aad60aaa482aa5608784f29e570a784c2a2130a783c29e0b08784b27b1789ec5227a8c49e85e2920b09e85227a1189e83d27a0b89e82d284d38a134227a0b0a003c27a0949f02427a0748784a274d209d14821e11c9345e26e4e09345226ad309335a260d40982502605409805024cd589603c2580b09601c24cd389314124c4e49313124e8e09312121e1189204c2405509004c2400b09001c21e10c8f34021e0bc89b52226d2889a5a2269088995e2265488994a226518898522261288782e2201308802c21e08c00823216160862402161500145f20a9208294820e0f08284820a1100145b1fed807fa601fe5807f86c1fe180014571f2d207ca481f25207c8481f2110014531e68e0799381ea110798381e60d00135b1e00e078034004d4c768381da0d00134b1d08e0741381d00e074034004d0c722461c88f87212a0049486e45e1c21106e4521b89786e2521b88f86e12a0049286d0341a2d486c0341a2d2868a5e1aa91068a521a292868a461a24a80123219094867124190928661241908c8641461904f86412d0045485d45e18a1105d4521864905d2521749285fa4417e4905d2321745785d1521744f85d12d0045285c03413ed485b03413ed285a12413e9485912413e9285624e15e8d0562421588e85623613e8c05512013e5785323014e4805314413e5485223013e528509381424804f94613e4b4011321389804e16000417c4d25012ad144aa4912a4884b12012a0880105e1205b04803c1200b04801c00416c4546c115180453601149404515000415c4405c1045904105c1041504104c1040f04102c00414c33a320fe8c0339320ce1783385d0ce134338460ce1143b1220ee4803b0220ce1103383e0e4130390440ce0f43383c0dc130370440ce0d4358440d60d03382d0d0110340340ce074010520c6d2031a580c65600104f0ba5703004c0ba1302e83c0ba0b00104b09317824c520928c82c2300924c82485e0aa0f0248520921182483e0920f427b4e09ed082483c0920d4260340920b4250340920740104a08c9202314800411c17c5e0868e017c52082d3017b5a078d401e2500785401e05005ed581c03c0700b01c01c05ed3817a4105e8e417a310668e0179220608e01812005e0880104605a130149540520f01482c0520700104304c900131400040fc0db5a036d080da5e0369480da4a0369180d9520365280d8520361280103e0300f00c02c0040cc01b52006d2801a52006928019520065280185e0181100603c0180b00601c0061480403c0100b00401c006128018460060f40182d0060740103200204c0001f 11 11
def l_962 : Nat → Nat → Option Nat := unpackLinksF 0x13e829f404fa027b113d049e614f30279813bc89da24ec0a76013b009d044e6126c7736209b104d59a6ac135609a534d282694133e699934cc826641320998f0cc78263c131c198e04c7026343308998404c2025ed32f4197a04bd025e432f2097904bc065bd32de096f04b32659432ca096504b20659012c809630cad26535b29a094d04a68251132880944049da64e83274093a049d024e8126299310498824a1324e192704938249c124e091e4c8f02478122a99140c8a02450122809140485a63ee11f608fb0478aa3c411e208e84c74023a011be98d64c691234811a408cd2c658a328319408ca04631230c718608c20c6102304318018b4645a022c8516408b20458862c4116208ab34548a2a41150189e544f02278113a189d044b9a254512a08940c452a228111408890c448220cd0d3a8661c330217530ba085d042b9a15c10ae084f44278213c1098384b0c258211c908c18450c2282114108a083a5c1c0a0e0107008370c1b820dc106e08313418820b8705c082d0c16820b4105248290414820a4105208290414820a4103cb81c140e020701038081b0c07b2038301c080a24040a02010100808040385fed8ff417fa03fb11f6b8fb407d90bec81f640fae27d22be901f480f9c47ce03e701f288f9407ca03e501f280f80a7c003e001f000f8007b653d629eb00f5237a903d481e948f4a07a503d281e940f36a79b03cd81e6c0f3607924bc901e480f1297804bbe11df00ef807772bb991dcc0ee607720bb59ddac0ed6076913b389d982ecc076603b111d7c6ebe075e0bae85d740eb8175063a801d384e9c074e03a701d342e9a074733a289d140e8a074503a281d102e74a73a039d01ce42e720739039999cc44e6207300b9329c980e4c07250b9281c7cce0ba7021b8101be52df206f9037999bcc0de606eb437581bac0dd606e81b7401ba00dce16e03b6e11b700db806d91b6c05b600da846d30b6905b480da406d20363adb144d8a06c5036281b102d8806c4035f19af80d7636bb035d05ae80d7406b6235b01ad80d6c06b6035b01ad80d6c06ab5b5489aa40d5206a9035481aa40d5206a80b4e31a6c2d36069b034b91a544d2a0695034a81a502d10c6870b4381a0c8ccfc6670333059980ccc0664132f9597c0cbe065f032d9196c0cb22659032c819548caa06550328919440ca206510328819440ca2064753238191c0c8e0647031ea98cd4c6606330319058a52c5206290314818a02c5006232b11058842c4206200b0f85864cc320619030c8185c4c2e060f43078183c0c1e060363018180c0c0416020301018080c0405f472fa017d00be615f302f9817cc0bcec5e702f3817982bcc05e50af2817940bca05e502f28175dcbae05d702e99174c0ba415d202e5217242b9205c902e38970c8b8605c302e18170c0b8605bc3ade016ec2b7605bb02dd816ec0b7605b43ada016d00b6235b102d6916ac4b5605a912d48169c4b4e05a702d2896940b4a05a502d2816940b4a05a02ac8416400b20059002c5956244b1015870ac3816144b00557f0abe895f40afa057b12bd815e44aee25760abb015d80aec057412ba015d00ae235627ab1015880abc455e02af015704ab8055b0aad8156c0ab6055b02ab9155c0aae055702aa0d5500a90c54802a38551c0a8e05460aa1114fc6a7e053f029f814fc0a7c153d0a98354c00a60052d1a87f943c0a18350c0286014208a1005051a82814140a0245000a80013eca9f604fb027d813ec09f604fb0278a93c409e204f10278813c409d094e80274013a009d004e802740139849ba94d44a681134009a004cb2a639131c098e04c60a5f9d2fc097e04bd125c912e4097204b80a589d2c4096204af1257812b4494894a21250852840942049d224d0d268093214980a4b8525c0916c48b024489224091204890244812202904648012400120009000480023f851d548ea0475023a051d008e8046e3236091b008d8046c0236011ac28d6046152308118408c01460023001168c881a43d1a1e810d1286804340217190b8085c0426421301098084c04231a118108c0844141b3a0b9105c082e0417020a0d050082804130a061d020880c2406020208fe947f403fa01fb8cfd827ec03f221f884fc027e003f001f800f9567c623e301f180f8c07c603e209f100f70c7b803d919ec80f6027b003d801ea10f5007a803d401ea00f5007a803d401e4acf1c478e03c701e380f1c078e03c701e304ee9877213b901dc80ed4876623b301d980ecc076603b301d980ec8276403a661d284e94074a03a121c2f0e140708138401c200e0846fa537d01be80df406f2437901bb88ddc06ee037701b990dcc06e2237101b804dc006d4636a01b500d9886cc036601b110d8806c4036201b100d8806c4036201ac28d6006b0035801ac00d6006b0035709ab80d354686a34301a180d0826729339019c80ce406701338019994cc826621330099800cbc26526329019480ca406520327118fa0c7c063e031f0189b0c4c06260312098900c4806240312018238c1006080304018108c0805fa52fd017d88bc925e402f0117328b9805cc02e5097280b7cc5be02dd116e80b6865b212d8096b08b5425a622d301623cb10058802c3096180b04458202c1016080ad5856a02b5015a04ad0056612b3015980acc056032b0015800ac0056002a2715100a88053c429e014e84a7405381294414984a4c05260291114690a34051a028d014680a34050c7286014284a14050a0285014280a1404fc727c113e009f004f23279013a909d024e422720138089c004e002700137089b804dc026e0137009a4a4d2026901338895e04ae0257012b80948a4a0224f09278093444981247292304910448612430121809044482023f111f808f8247c023e011e088f004723239011b888a1e45002280112108900448022211110088424420221011080884043a421d010e808740434321a010c0886004300216110530828041212090104808202408420401008c8040402020008ff847f823fc01fe00fe847f403fa01f160f8807c403dc31d0f0e800740039e11c648e300718038c01c508e280700a37e11be08de846f4037811b630db006d8036c01b600da086b1035801ac00d6006a8435401a528d28068c4334919a00cc08639431c018e00c684634030e618700c38061c02f6c17b00bd805e822f4017a00bd005e802d8e16c00b5085a802ce316608b28458c42c4116010b000545e2a2015100a804540029c214e00a7005380284c14200a1005042282014008a0005000280013d189e804f4027a013d0097b84bc025a212d00950c4a80250212800928c494024a01240892004900230c118008b84458222c011508898844c022411120089004404220010178808040401fa40fd007e043f001f610fb007d043c901e210f10078803bc41d640eb0075803ac01d600eb00721c39001c610e300718038c01c600e3006e1c36841b210d7106b8035c01a830d400681033c219e00ce086608330019800cc006508328019400ca006294314018a00c310618030c018220b18058802c4016200ac2855082a8015020a7085304284a140109e104e842740138109c004e002684134009a004c8426401320097104a0c25001242092004808205e1020081003e901f400fa007b103d801e820f4007a003d001e800ec4076003b001d800e630730038881c400e2006f1037801bc00da206160308018020c00060002f8416c80b6005b002c0c15c20ac1055082a8015400a81054002a0015000a80049582480124008c3046002300118008c0046002300118008c004600230011800844042002100108007e303f001f800fc007e0032680a7800660001 0x8b4d4240b4894cd4a3034a8d28fa2d23da244a5bb921a220a4ef0218b4d62213408e69b251a44760941f0a48814949dba4aa1a4f9bb93277e4b9d812da1806486811760961caa407945b2039444545413494852e5491914aa100f8ef032a0e0b8868224720791501d4545610594048a1b14a04495a94e89a4ba2092687a438ae9064123b9008e61f23183254e8714ba165268514375c505f113b7c04e5c89316e848d58853a1212e83049a0a10d148414d40ed3403940e0c4ed82321404db9931a064a5b81213b40c6810293ae085b9232a004f9b81322120867f81920c044ec93221048a7e83e3ae0ca7e02e20c08a80a399fc4e5b71239f60e4ea82320804e3534a8d292a2e2466da4c67c9296d4484ea0319f00a4e80218d69727a1449e21127b23b9428ddef93b9ea4ae799234ce0ee7902b9e008c81813780929b623277e529d99469dc4f9b5132204086768191fe045e095c9d2512730448fe8ee7593b8084de7512f9d048d3303b3a608e7381b9ca04d1d14a3a44c880922472129170469c60f8e80329c40b87f8224761726f0449b61123f23b7bc4edb49239c00ed480379be0be6e8239b807e6d0139a8d767ba519de9423ea3b9d8546721507ba4edb41239c21466c8504ca0ece78231fc04e6ba498d29063e2399ac525df9417b84e66a84947210532039932d4a2f25e8d2949b39319a64a5b292139c0c6690293960864d2448e293e6824383050e6792b99c48d5804399a0ae660231fa04dfe2526cc8c9da95e77e54a6513e6ca4c87e0219920647d0117fa5125624378e53e6394398c4be6292355e10ce682398806e61813510548e61321f64891805e47214a6083e3960ca6002e1f40894484495690e0b9436c648d2084f97c10e5e82f97808e5d81f97404e6a35e95494e3d2499a28e665a3882c54ded1499904e6611386c448d570534c41265f8399720e0e48231f004e34a498d88e5ec14996e505ec9397204c53004996c1053083940c0c63cb4a71e9099d2327b052a5a1466724c87b8219660647a0118f0d29029422fe4c87b1224c012a588462fc0ca5802e1e808a3bb4a96a919eb14b71a50e591294bc12d0184395e0a47901394cd621eb408d294251a44932d22512548d292256148956122542588b89124ea44950d722db5494e9b25324c878d022da489389024d2385e251099844946d7a513528b6d3a34b4d94290a30a397a8526501416c24852e04993e104e402193a9324d23c9349124e3549369b24ca4c8d28f24c12892e0a1b02406408c00682c7de949eaa4a6588c9ea14a9285199c92e6404b4e3831926064788116424a1902389225b24815c91e551fc14c91c060e31402b24c0060186be8c53d9524ba528b81324b812a458469140b8788222fc078ac81d2b60a0ac9389101b24385c90c1514284c90a0b256c5f95514e1db4295293e52a4b8ae92a5224793c91a4b24382a54de914b71650daf13192a4ae4912991a48d8a92155a14d2d04b40210ce28319180ae4482990808cac0211de04e303588e69b234a50902d2a3b25d8ca955ae9318aa4a5851213880c62602929a0863e46c8d4d8234a608e49723f9608fc1823e45e8f6915ad9318a84a5849213840c6258292980863ab5d8f24a63c0298868f23b46c8eada236a688ba98221a308d694234c5e8bb17639b5d8e4d5638a4a8e0526099416b448637849556104e08218c695235a3c8d6d7236b6c8d89523524c8d28f2341288ce0a232c5c8bc9b2312508c69722eb6c8c4d9230a548c09322f25e8ba9762e2468b69162d23d6b24c62c92960c484e00318b00a4a40216b090181a300120b22ac5e8a914a0a252746929872328a657a099525c44b98192d37e0c6290191dc045759286068e2281547525322781837c5009e9300100622645e897149aba315585490e94a29e4ca2505e55614a2482e1dc0889001e27a0749602827a4e2238544481322302c90517e4045e8fb15e3d4528eed6a3a25f8dc97a3325b8c895e2fa538ae94a1595b82254de894b6ac4c62b12b8a24a6271235f44856985b55214d2c84b37a0c62682b8900a62282327808476013886d72209408801021eb52884d0a1fa4686e4a61902987b17a1e34586c4a618829874526081418721255404186f17a1b35285496971a3286a57a081525c44c8758218680647481186517a18b525a4568909321d448a1805e5501489003285e0b87482287d17a1db5287097a1415b81c54e199295a016d5305385c0a47381384c5521093c8584d21523884a5521114c8524d210a4984e9061323984a8c5df9497864e52b8498481052c0394000c61134284292a102467a05299d931672484de03183e0a4dc82179e928ff9423764c8489224ae12a0e8468380f8dc83212008a15b4b850d0de724a84651a0f13e4aa12cfe84336e0ce0d819814961c524077e54203944830d21fe24880c551df94882e121aaa407de8e1fc14c6724c1aa1306a69020a2387ee531fb13c8264e20913460c4c20813881e4d20615876651200944818971d92548165b20513c712901d9148800501fe9385e29101f84480ed7a03352764d39dfb4d7ec92602a41808509dc1396a44892984980610473011802531fe92c7fa512002547fe5b1ff14c7f84f1df92c7f6061a8a406445000703c7f0d49fbb4a7ec929faa466728f99123d65a4c5fa02936c084728116464f19124c7e45b1f895c7e0551f793c7dc060721300ce480060286a08c9369524a8528411224a6129f58467d40f8db0321200783381d0d2060339287d01b1f385c7cc151f284c4f00f20cc5f82d14e0ab53822d2e07343710909a7a3281a53e0494b75c52a04147804519fd1437f24fdf993e7da4cd8a93254a14d2884b3f610cda0331c6085f601b7d2065f20130cc045dba587945b1df9507c2929a723279a575de1557584f9851321c4085cf8190b6045ee46c7bed81e026077e581e495c7bc181ee45e6988c9ed9457564f9849321c0085cf0190b4045ecb547b04e1eb9346964c1a52407aa8e1d514c74e4f1ea1387a64d183130692901d1a3875253171130798975e813e79e065cb12c79b1b1e62687885a1da16072c4c1e095077f179da45d794d75e4b55790925d3a4178e529a412278c125518411be045dd1547824b1e0a5c7889b1e1954784531e013c77e4b1df018779171da96c772541dd15c7689b1dca64770551db93c68e8c9da95e768575d9946764515d893e60c4c9d812d1bc085d78190a8045a32406085000503c759179d5c52754d49d4b4a750979d3a525c48f98223d61e4c5d30293660846e8115d84f18224c748551d193c7440606e1300924800402873f179cf45268a8c95215241e5282e92273a179518527380f8d98320520782481d07006024928734151cc84c42e0f1f145f7c1179eec577b5149eb35b7a4d4de8b4b79c969a223279657de295e77a56ddd95776c54dd715275a4fdd293e7424cd7d13259c16d508534a012cd88331b6085d001b736065cc013090045cb25c728901c9840714949caa42724519c213e6fa065c835471e8e1c194c71c4d1c093c7184d1c545e712915c013e6f8065c3a49702905c3049540105c245e706d69c125e702949c01525c84c5711213600c5bf82935c085bec5e6f89496695a35e4c8151226f6179500526f40f8d7032052089c8c5e71ad6dc5b53710949c295e6fc4f96585b53c14cd60336f2065bb0406b2d41aeb4868e941a72485ec571bb9586ea55183150614521b88186e6d21b92485e4551b81486de511781445de511789445dc511b6b606d8981b596c6d4581769446d2181ae24869a521adb586ced21a62586cc921849586ca521b21446c6121acb4a6c2d19aaa52694929b023a6865759a9556be0e4b70311b20856f81902c045ae1446bb179adc526b4d79acb526a6949a4a4a6b08e98a14d5f2515ab8392960c46b8215bc0640a8116a88d1aab526a6d29a3a4a6a4919a8a3d6845759a1553540c5a80291000856e819028045a69446968d1a745e699149a5352692d29a425e68e949a323d6265357c1453500c5a28290b20856e019026045a1b606849819e168650581a00506731799445d5ecd359fb4567c1254e84134e0846b011662551789440180619e26c6765319d13c6724b19bc6c66d1819ab506689419496c660541998606625719426c6609919795c65c5519694c6584f1958185e25118f8186340519193c6424b18f018632050d30211aa045919446300519094462e0518f94c63c5118d04c6321118c03c62e0b00601c6525799415d64e5358314a64c519929456485119113d6404b4d28311a80858e81a6380658d81862c05805811628d6189a58620561829446241217314461a061761445d65118694c5d45118825c5d29518794c61c4f186018600061799445fe0617894460e061761445fa051759445f805175144600d397fb425fa0f17e02c0100718545e6131498415e60c549829465d25158213d6064b4d20311a60858101a6020657f0185f6058038115f2d217c2485d2521729405e2d117a8385e6d3178b505e0941779505dc1417613c5d64b1750185ed1797a4525e4d6976b565d2d397134d49c1257404149e0e4fd031346084690115cc530040185ca9517214c5c64f17112c34450068930006480060480101016fb525bcd296ea525b89296515a3f2508881320304896d85e53a1492704a5b41180181d0064a16c04c5ae0f1ba45f6dd16db44576c514daf3526acd29a7a52688929a095f67a5799c15b66455d9515362a5498894f61652d7d14a5ee51d739465c250d6405b53614d2604b3ee10cd08311a00857001b5b20656b0130040456305457e0f16a0345a44e162854580131688345861515c02c59e091669285841515d03c598090060145944a15e84c5720f15a02c5920915fa4958e9056323958a8c55c149588505619395844c51c84947c0e56034257e9295f24657a4c55e1295684852584a3000c4bf02156a510060185749095ca325705295b94656c4f95a1324941284902112004569b4b5a0d0d6724b59690d64233492529608465760f95982e52e560fb1404721414a044560d2157a4851052149854472120d01404f64e14284c2fc0c0cf83033c501561385081314183c5560e1550342900c15403854e0d0679304da4a13c03c1200806702019a4c1521284ee0f13b02c5460a1510240a80815002853e090ce830198080ce1401964c0091202dc100400304e60b14e828538090058205321611704451c1114c95c45a5514c06c52e0b0fa94045a121468405120e099a4407e5114a35e526d4916b4e472d3541a495249053b149522505480424660e4cd8221940494704c5120714484451a5514606c5161314503c5100b11c81c334500b284001c4f142b52508d2941a4a504918bf23e2ca8f5409294e6484b9031192048b303c2ca5313f86c4fc1713e8544f80f13d82c1904c03503001a4a13c2524ee9293b14a4ea5193a13e4e64c84812e0d44b4cc8321060843602c0d44f13886c4e0171378544dc1313682c56317d5745355ad4d54b4b54cd0d52a5354292d4f2435368ccfa1423304c86392253413d4b04b4521294a84751e1194384350c0fd4003e4f40ccac0324f20bd3902e4d808c330224645612286c4721413494a32e4c8631224901751b85544e0f8a68324340b82d8224c91b133b604cc9811d1604721812205c4c9178ca9321884893184544c0f8a60324320b82d0224c2d51300384be0d0ca0303265012e93844a1311103c4b80e12d8342900c0c914043a4e11204c2400c12c2544ae0a12b024186080611304a84a10c03c42a0b1298284a40902a0201824c10792842e0f0148203224c0601203200c05f82049e950c794017c4c0089202961002c8304260b12702849a0900382048e5752583e4940b90601c4911b12396847e1a1178604180c11d85047317917c5d48ad7522355486925112414845250a941482128c702217a0491a8544760711d95c47e5b11f05447a1311e03c4740b11c81c46f1711806c4681411a85c45e5b11a1644661511902c31a4c85e1224601791785d45c119168454580f8a40324560b82a022454074c614028c1000513c44f1791345244ad491234a446979112522408f8a323d4424a5099212a40c45d81225c0f0a314c43e1510f03c43a0b05d1300960c0049284351790cc524309490ba4a42c5790a9524284f9099320524b82592d3160c82f0210720b02593c4221510804c41e0b13545f4d117932c574c51492f35b4b4d4d2cb4b4aa96d28a534a092d26233492568c51321724892305f4801791c05b46c15d188534521491403f4400f90e0332780c90d82f4240b9070230900890615c414901049403ec54905942410118f803e3d00b90335440a4e0f784c4080d0f683c4040d1002543fe4a0f383c3fc090f202c3f8090040143f4950fc9283d8130f303c3c40b0fc0243ed178fa9453d40f8f082e3e6924f6a413e4524f21413e1178f7b5a3dc978f6a523d84c4f59293c4484f50522440c490021010060f445e3ce968f32323ca578f21523c64f8f11323c21481582105204503c5e406d6d00b533fa96cfda533ee8ccfa1523e2178f483e3c00b8ee940380d40e234831a540cb948270170ef0583b8150a405029a120ec02c3b4d20ec948268150eb8483ac1109904426211098044266110ea3603a6980e91603a21b0e806025e110e1a4832c120e135839cd20e6a4832a560e6148298160e5848394110e034a390d18e3a3934a8c4d0152326528e313a16e488c485d2f41548e02e02c088e1844389178e1452382d78e035237e8e4d223133c548c914a37c4e85a9222ae1349d8452360b80a8223741100682c378930dd9282340f0dc828370090d5a30168080d534034a900599300fc4800a03022e0b0db02836a090058203528c059020350d00d22401624c02b9202521500983022c0b0d9828364090038200120b0d824c35e4a0940542320f0d702835a0903f9303560d02c13024e110d48341604805792034c9105713015a4c0c8938158480d5352350d28d3a5e34a948d224a346918ce15231e528559303444a8c185e2dc148a584a24c1188f03d33e4d03f93033a490d035233cd28ce23131a528cd9463344f4cc92e0fc488c405d2f01548a02e024088cb0443284d0c8a440b04c0c812432f178cac52326d48c934a31e8c4c715e31a548c613d3164b82b9222aa1349d0452260b808822312d80c41603021a0b606030c540550202fd178b645d270d34c2b453085248b941306484548122ec1509984401a0b0c096c300130bf82c2fc070be46c2f7180bd3502f2980bc1502da1b0ba8502ec170b616c2ea590ba05c2e6150b904c2e20f0b802c1504c0b4044266110b182c2be090b303c2c40b0af0242b6070538202d0484530122cc110ae8242c6130b10442be130af0442ba0f00682c2b4070ad8442b4090b723114a488b685e2d8174b584d290128b50462d2114b38442ca0f4b202e2c20b4b002c2b8094058222b2074abb582ac920aa9582a6160a3844248110a882c25c110a884c25a110960442a6570959542a4130a803c29e0b0a182c26a110a102c1484c0998442920b09704428009096844286d38a13422800f00482c27c0709604427c090a6c5e299148a5a31146488a505e290148a3846256114a303d28a0b8a202d2820b09f82500e0889e81d276d209d14825612091840266d109b93826ad3099b50264940989502601409703c25a0b09601c24e8c05102024e8e0508202711789b452268d6897b56256d389034d22c524951412524e49413124c484500122481300482c2465509104c2420b09001c23cd004f9300080c006924012490069480125008e352236d288d25a2329088c15e22e5488b14a22a5180212d2281488984a0320840213c2221308802c3b717ceac5b39f15ce4c5338ad48deb4a36e96cda25336292cd62433428c4cc1523145284f12230e17cc105e2fa16cbb8572de14cac0522a813ca704b2781289c84724a1188f84323a0bc8902e21e08c010222189006f2501c49205e15018c5202205c21a160858540a81402d84820e0f084a482105202005420c1208284407c1101e8440781101f844206d80812602025808006c1fe1801d8441c2520628481fad20702581f8920621581f65202d0581f41207c8441ea1100703c1ee8e07b1380481307a0381e60d06d1301700c06ca401a88c05b94014a4c00b0400420f0788381e00d0058301b04c05b0301ae90069a3016a5005193006a1500a8400400f0770381da0d0038300140f075a381d44e01a054046130748381d00d06f24a1cc91872a3e1a88c867952184528599321c84a84e85d1161540f03e0280c8708441c5178704521be9786f2521ba8f869a3219a5486094a1624c86e12a0c81342384503a0f8098321504c06d0341484c0198441b00d05812015e4806aa4415c4c0569301804e0561201b2d486bb4a1ac9786a2521a6928692461965485f14a1564c06892a12e178400520b21281904604e0f4671241504c06612419e94866a4a1968c85e14a1945186493e14a4c86412d138174450550380f80903218a110619241809105213017e4906345e189148612521829285f23217a5785e1521764f8519321744b43184d08c1140d83e0220c8572301700d056a300621105b03415c8c05a12415a8c05114416449057a341609385724215a8e856236154538541421484e85093612c1383f8420b00e8180361544805393414e4805423014c510522301444e05092016ed485ab4a16694858a4a1568c05495e14a5485194a1405184f92d12a1783f0520ae1281784604c0f44ea60138580498680f81804d25012c0804b1201211783e45d088d344cb4513092410a4112e4884a8221101501f84401c0f04996c1240f04882c1200704746c11b18046360116940451500fa1b0438501101703e16c10e5904305c10a1504204c1060f04102c0fe4c03c0440ee0d03fa300ec1101f8440e60f0378340e40f0370340d80b03481c0ee0803b9200f04883b0220e6130390440de1303704401c0f03582c0d0070360440d60d0348440d00d0402320fc4c83e85e0f81743d84d0a81283d0460f21143a8440e80f83883d0e00f0368350160c83502d0ce07432b480c8960319580c21602984405a1103003c0c01301d0440721101c0440c25701b9540be1302f03c0ba0b02803c0821102783c0b04c02c23007e1102a83c0741102834e09ed080503c0980b02501c07211026034070110250340b71782d4520b28c82b9320ac1782a0520a61181b8450a40f82883d09c0f02683500e0c82582d09207423a4808c5201b8480581001fb440868e020b4c07ed401f25007a5401e0500740f01c82c070070199300620c019a3806008018a380604802245e0851482035a076d581bb4e052d341024906c9041aa390688c41912205e0881684c0140f0161540560f01502c05207013a4004c5000284001c8d00523401c92005240048d6811b4204497810a520409280fa4600a8f40f15203a5280e0520361280294c0320f00c02c01e1100703c01a0b00601c0140f00482c0100700b35202ad280a252026928091520225280805e0161480384a00c1180283d0080b40181d21517c8245b1fd15c7c4531e4d6c77b531d8d2c73b431c69486da4a1a08c8639521725284f13213617c4a05e11e16c4485710214c330520c413c2e04b0901282284705c1181404304a0fc0d03e02e0cc01032a08d3e7d34b9b0d1e5c34395c92e41a438888ee16a3383452df194372e4edbc1335aa48d5904b4d610d0683b3be0cc8702300204c0001f 17 5 11 11 6
def m_962 : Nat := 0xcccccccccccccccc
def s_962 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_962 : Nat := 0x40404440444444c
def bds_962 : List (Nat × List Nat × Nat × Nat) := [(m_729, s_729, 6, g_729), (m_695, s_695, 6, g_695), (m_860, s_860, 5, g_860), (m_767, s_767, 6, g_767), (m_924, s_924, 5, g_924)]
theorem kn_962 : KnownBin bds_962 := by
  intro b hb
  simp only [bds_962, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact lb_729
  · exact lb_695
  · exact lb_860
  · exact lb_767
  · exact lb_924
theorem sub_962 : ∀ b ∈ bds_962, m_962 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_962, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_962 : ∀ b ∈ bds_962, canon b.1 g_962 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_962, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_962 : dagCheckRootsF m_962 g_962 bds_962 (dagRefF 1300 (dagTraceF m_962 s_962 8 f_962) l_962 0) s_962 8 = true := by decide +kernel
def node_962 : Nat → Bool := dagCheckNodeF m_962 g_962 bds_962 1300 (dagTraceF m_962 s_962 8 f_962) l_962
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_0 : treeBlockF 0 32 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_1 : treeBlockF 32 64 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_2 : treeBlockF 64 96 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_3 : treeBlockF 96 128 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_4 : treeBlockF 128 160 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_5 : treeBlockF 160 192 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_6 : treeBlockF 192 224 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_7 : treeBlockF 224 256 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_8 : treeBlockF 256 288 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_9 : treeBlockF 288 320 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_10 : treeBlockF 320 352 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_11 : treeBlockF 352 384 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_12 : treeBlockF 384 416 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_13 : treeBlockF 416 448 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_14 : treeBlockF 448 480 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_15 : treeBlockF 480 512 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_16 : treeBlockF 512 544 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_17 : treeBlockF 544 576 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_18 : treeBlockF 576 608 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_19 : treeBlockF 608 640 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_20 : treeBlockF 640 672 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_21 : treeBlockF 672 704 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_22 : treeBlockF 704 736 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_23 : treeBlockF 736 768 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_24 : treeBlockF 768 800 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_25 : treeBlockF 800 832 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_26 : treeBlockF 832 864 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_27 : treeBlockF 864 896 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_28 : treeBlockF 896 928 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_29 : treeBlockF 928 960 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_30 : treeBlockF 960 992 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_31 : treeBlockF 992 1024 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_32 : treeBlockF 1024 1056 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_33 : treeBlockF 1056 1088 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_34 : treeBlockF 1088 1120 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_35 : treeBlockF 1120 1152 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_36 : treeBlockF 1152 1184 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_37 : treeBlockF 1184 1216 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_38 : treeBlockF 1216 1248 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_39 : treeBlockF 1248 1280 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_40 : treeBlockF 1280 1300 node_962 = true := by decide +kernel
theorem nc_962 : ∀ j, 0 ≤ j → j < 1300 → node_962 j = true :=
  (joinChecks (joinChecks (joinChecks (joinChecks (joinChecks (certBlock nb_962_0) (certBlock nb_962_1)) (joinChecks (certBlock nb_962_2) (joinChecks (certBlock nb_962_3) (certBlock nb_962_4)))) (joinChecks (joinChecks (certBlock nb_962_5) (certBlock nb_962_6)) (joinChecks (certBlock nb_962_7) (joinChecks (certBlock nb_962_8) (certBlock nb_962_9))))) (joinChecks (joinChecks (joinChecks (certBlock nb_962_10) (certBlock nb_962_11)) (joinChecks (certBlock nb_962_12) (joinChecks (certBlock nb_962_13) (certBlock nb_962_14)))) (joinChecks (joinChecks (certBlock nb_962_15) (certBlock nb_962_16)) (joinChecks (certBlock nb_962_17) (joinChecks (certBlock nb_962_18) (certBlock nb_962_19)))))) (joinChecks (joinChecks (joinChecks (joinChecks (certBlock nb_962_20) (certBlock nb_962_21)) (joinChecks (certBlock nb_962_22) (joinChecks (certBlock nb_962_23) (certBlock nb_962_24)))) (joinChecks (joinChecks (certBlock nb_962_25) (certBlock nb_962_26)) (joinChecks (certBlock nb_962_27) (joinChecks (certBlock nb_962_28) (certBlock nb_962_29))))) (joinChecks (joinChecks (joinChecks (certBlock nb_962_30) (certBlock nb_962_31)) (joinChecks (certBlock nb_962_32) (joinChecks (certBlock nb_962_33) (certBlock nb_962_34)))) (joinChecks (joinChecks (certBlock nb_962_35) (joinChecks (certBlock nb_962_36) (certBlock nb_962_37))) (joinChecks (certBlock nb_962_38) (joinChecks (certBlock nb_962_39) (certBlock nb_962_40)))))))
theorem lb_962 : LowerBin m_962 s_962 g_962 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_962 sub_962 gl_962 rc_962 nc_962

def f_963 : Nat → Nat × Nat := unpackForestF 0x3a781f 1 10
def l_963 : Nat → Nat → Option Nat := unpackLinksF 0x119 0x3a781f 3 1 10 1 2
def m_963 : Nat := 0xcccccccccccccccc
def s_963 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_963 : Nat := 0x40404440444444c
def bds_963 : List (Nat × List Nat × Nat × Nat) := [(m_729, s_729, 6, g_729), (m_767, s_767, 6, g_767), (m_924, s_924, 5, g_924), (m_695, s_695, 6, g_695), (m_860, s_860, 5, g_860)]
theorem kn_963 : KnownBin bds_963 := by
  intro b hb
  simp only [bds_963, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact lb_729
  · exact lb_767
  · exact lb_924
  · exact lb_695
  · exact lb_860
theorem sub_963 : ∀ b ∈ bds_963, m_963 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_963, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_963 : ∀ b ∈ bds_963, canon b.1 g_963 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_963, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_963 : dagCheckRootsF m_963 g_963 bds_963 (dagRefF 2 (dagTraceF m_963 s_963 7 f_963) l_963 0) s_963 7 = true := by decide +kernel
def node_963 : Nat → Bool := dagCheckNodeF m_963 g_963 bds_963 2 (dagTraceF m_963 s_963 7 f_963) l_963
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_963_0 : treeBlockF 0 2 node_963 = true := by decide +kernel
theorem nc_963 : ∀ j, 0 ≤ j → j < 2 → node_963 j = true :=
  (certBlock nb_963_0)
theorem lb_963 : LowerBin m_963 s_963 g_963 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_963 sub_963 gl_963 rc_963 nc_963

def f_964 : Nat → Nat × Nat := fun _ => (0, 0)
def l_964 : Nat → Nat → Option Nat := fun _ _ => none
def m_964 : Nat := 0xf0f0f0f0f0f0f0f
def s_964 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_964 : Nat := 0x50707070707070f
def bds_964 : List (Nat × List Nat × Nat × Nat) := [(m_798, s_798, 6, g_798)]
theorem kn_964 : KnownBin bds_964 := by
  intro b hb
  simp only [bds_964, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_798
theorem sub_964 : ∀ b ∈ bds_964, m_964 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_964, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_964 : ∀ b ∈ bds_964, canon b.1 g_964 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_964, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_964 : dagCheckRootsF m_964 g_964 bds_964 (dagRefF 0 (dagTraceF m_964 s_964 6 f_964) l_964 0) s_964 6 = true := by decide +kernel
def node_964 : Nat → Bool := dagCheckNodeF m_964 g_964 bds_964 0 (dagTraceF m_964 s_964 6 f_964) l_964
theorem nc_964 : ∀ j, 0 ≤ j → j < 0 → node_964 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_964 : LowerBin m_964 s_964 g_964 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_964 sub_964 gl_964 rc_964 nc_964

def m_965 : Nat := 0xf0f0f0f0f0f0f0f0
def s_965 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_965 : Nat := 0x1010105010505070
theorem lb_965 : LowerBin m_965 s_965 g_965 9 := by
  refine lowerByRows [0, 0, 4, 5, 0, 0, 6, 7, 0, 0, 12, 13, 0, 0, 14, 15, 0, 0, 20, 21, 0, 0, 22, 23, 0, 0, 28, 29, 0, 0, 30, 31, 0, 0, 36, 37, 0, 0, 38, 39, 0, 0, 44, 45, 0, 0, 46, 47, 0, 0, 52, 53, 0, 0, 54, 55, 0, 0, 60, 61, 0, 0, 62, 63] (by decide +kernel) ?_ (by decide +kernel) lb_962
  intro w hw
  simp only [s_965, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_966 : Nat := 0xf0f0f0f0f0f0f0f0
def s_966 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_966 : Nat := 0x1010105010505070
theorem lb_966 : LowerBin m_966 s_966 g_966 8 := by
  refine lowerByRows [0, 0, 4, 5, 0, 0, 6, 7, 0, 0, 12, 13, 0, 0, 14, 15, 0, 0, 20, 21, 0, 0, 22, 23, 0, 0, 28, 29, 0, 0, 30, 31, 0, 0, 36, 37, 0, 0, 38, 39, 0, 0, 44, 45, 0, 0, 46, 47, 0, 0, 52, 53, 0, 0, 54, 55, 0, 0, 60, 61, 0, 0, 62, 63] (by decide +kernel) ?_ (by decide +kernel) lb_963
  intro w hw
  simp only [s_966, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_967 : Nat → Nat × Nat := unpackForestF 0x6849140169f8fa5fc7d2ee751b33a2d99d160ce8366741831f4af8f95fcd93666c5531f2b798c6ccc5366621b3310c18f957cb8ae65c1432d4c98f953c7c2fe525b3290a98f85bc92366489b3242d992160c7c2be42543210b990164c7c29802d1f1d8bd8db55c6da280293ef06bf7835dc4e366265b3132c18986cc4c305e0d5f118bd7834dc39ae61c9b2f068f85b4ec2d2f5e0d16f02bf83a6cc1caa5e056f028d98136cc0836604182f02af7f95cbfc285fc992f02a77805fbe8b65f4152f00b77ac6cbd5b65ea5b2f52c178057bc8a85e4172f12c97805300523ddad52ed4a94ec5fbaeb653b16ee96ad4ec5ab89b65c49b2e22d971160b88365c41829d8af6945eb49af5a497ad22bd6db5cb6d2e5a454ad80b96c050b482f5a6d72d34b96995cb4ca85a414a9d8ad6835cb2ab2594d72ca27165134b281c5940d29d8a763349b19a0d8c97a9d6ad60349b01a0d8097ac048d60244a752b57a122bd0894e94faec2456a972b52895a934ad40c56c532b50294e94bac9ae5649729d28f5814cabd2a53a50eac29156144a7427d54522a42b952044a901a5480b2a509952024a7425d42d72a14b94e847a7c2653c5529d08600a37a6d2ed26d16996bb49a45a522c529152946a94a254a4d1b80253e878af43b57a3cae50ed1e8c6ad4624da1ca3510d2a8868d44256a1c9b00252e8548b39b5da0dae4e6d1e8168b39a5d9fd2e4e691e7c8d93e4609cd1bcf08de7826f3c1279cc2e4e8d1e7448f3a2379cc2800251e712b92bb479b926cdc8d65728d33a3f99d1bcce0fe670773383799c19cae5126369531b4698d234ae4da5c4772e23797017cb80ae5c04f2e02395c9a4b48de570312c23795c0a00250e552a92335f94a364a45b2466af27a5d93c2848c95a4d4bb2315691dad48ed5a474ad2405091cab48c4d801277222358c22d48454a306ad1f4588f9b247cd52304bf1dc608edaa46095e358ad1ab5a8d5ab46cd52354bd1824d8c5ab4629363124d1815a0049bc5c5521b8bf15b6c8acb643715e286bb1405086d2b44b16a256ad0da46889aec444da1b2ad0e45a8722b438d5a1d0a10e15686ca30024ae186b10c2548062fc2cd82018af0a246805ad42117a104b508256805a5414d360a68b0634c8291d41454a014ad0334a8192b40c51a012b50135a8092b40455a01294009277fd2ebdad15fd6baf6a457e22c3f1151f86a8fc2547b51bbec551ed276f9c587cdaa3da4ddf12a8f692b7b9ac3dc951ed24e0084f75e2bbaed5de90b8ebb4775d2dbae95de5048eba4b78c2e3ae91de1048eba3b77c263ae8dddc6acee24d75c233b0d29d868cec25675c1b00212dd548adcb5d74dae372d1dd168adca5d73d2e37291dcc8d8e64606e51bb9091dc828ee41276e4ae388d1dc448ee22376e4a837252db928ee016c6e49db7d181b926ede16c6e495b74d81b924e008476dc2e31ad1db5048c6a4b6cc2e31a91db1048c6a3b6bc2631a8ddaa49ad52356a89cb544d58d08cd0a3f6851bb424fda1276d093768499b424ada124ec684466da5336d199b48ccd92966c92b1a0d992476c92376489db244dd9225ec912b64893b2448d8d068c82376341631c8dd8d0480084362c2a2d8d7d888d8c406c5b1abb0c1516c4bec20245b12db041b16c4aebf2545f9222fc0916c4a6bda545ec122d88ed79098b62375d92eaec5416c2acba25d5b02b2dad696d6acb6a565b494adc1416d0acb60360041dad48d5458b4b4052515ab2c9161646c8b23545152fac3181616a8a2a5756e2b2b6d695b6acae35456d2f28a935588b0ac354514afaac571452b6aa460514abaa057150288a8134514a9a9c57145256a5350529a42949714524ea335651926a8c099450b40083750c2a24117d406d8a006c4822ba7c151204be9e0244812da741b1204ae9b2544d92226c091204a699a444cc1224092d310b8902474b9aea5c541202ac95c5a4adab240519286ba940364802b243169218ac90b564849ca44141210ac9004600415a3ad611d4a87ac5f46db01eb15d1948c7ab5a4562f22a969154ac7ab4a43da6a1ed151169887a3a43c291ea9590c6b0862543d4afa14530f52b6843603d4aba0855104298821343d4a9a04530f52967f3503f9a41fc970f528e7d34a3e92b1f4118f50b47b35a3d92b1ec158f5094008273ccaa18d17cf12d8634573bcaa18cd7ced2d8633573acae18cd1cc64ac73b5d39d2e98c558e18b470c56385ab1c2934e12ac63146369ad1b4d58da6946d3463692b1b4558c626c6a846354221aa0d8d50686305234cae19c958d10b8671563389b19c0d8c60946615c31d2b194170c72ac6394631c2318c0e80103e6205425e2f9841b0978ae6005425daf97c1b0976ae5e05c25da396e918b74885ba362dd1a12e948b546c4ba4a2cd2312e8e8b10b85713a2bc2e15c4a8972ac53b5d29d2e954570a72745415c29c9512e158a08b450456281ab140934a02545005625c23130d68986ac4c34a261a3130958982944c05625c1b00206c954b03ac5f24d300eb15c914b03ab5f23d300ead5c8d4a03ab47228a31144d8754b44315a218ab10c4d8754944095a204ab1025288128c3aa3a1f5250fa8e87d2583a95a1d9250ec8e8792583b15a1dc250ec0b0750b4008171cc2a00517c710d8014571bc2a004d7c6d0d8013571ac2e004d1c6768a33a4519c22004978646ac3224d009230c2d28614ac0123615da28ae9145d4882b93616ca20ae4985804c2c01615c220045784e6ac2724d149220a41104e2bc27a3813ca609c4980228c22b4a1152b092510490882295e1191c08c5304528c0113610c22068d3c412a01a3470fc2206893c3d2a01a2470ec260688dc3924c1a13a0dc0a06a4e83526c1a12a0089202cd741669a0b3450592e82c9341648a15b500ad2202c4d8284a0141440589304ad40254880b036089280445101604c0ba3d07c2002e8d41727a0e04005c9a82e108170800b82a05c0d02c050020ac06c5a04d2e01b1580d6ac06a4d0351a81a4980d04c0104600dad014d70036ac01b4a00da30069580348c0194600c230040d8010260001f 10 11
def l_967 : Nat → Nat → Option Nat := unpackLinksF 0xb224b0eab083afc6afc0afc0afa1afa0af81aea7ae81ae61ae60ae03ae00ae00ae00ade1ad26ad20ad20ace2aca2ac81ac61ac60ac03ac00ac00ac00abe1ab26ab20ab20aae2aaa2a6fea6e0a683a604a4caa463a3a6a3a0a3a0a381a380a361a287a280a223a220a220a1a4a1a0a1a0a0c7a0a1a081a080a023a020a020a020a0019f469f409f409f029ec29ea19e819e809e239e209e209e209e019d469d409d409d029cc2991e990099009884986197e497e097a297a097a097a097a097a097a096a896a09662962295e295e095e09564956095609522952095209520952094a493a893a0938193809380938093809380928892809280928091e591e091e091e091e091e091459121912090c390a19043904090409040902190018f658f608f608f038f008ee18ec18ea18ea08e438e218dc38dc08dc08dc08da18d818ce58ce08ce08c838c808c618c4188dc88c088258820878587808780878087808704860885c28582858085428540854084c484c084c084c08444828e82808204820081a381a08124812080c380c080c080448040804080407fe37fe07fe07fe07f457d507d407c867c807c807bc67bc07bc07bc07bc07bc07bc07aa97aa07aa07aa079e679e079e079e079e079e079e078c978c078a178a07881770c770076e176e076e076457640762175c375c0756375607560756075607541748672ed72e07283728071a771a07181718071047100710070a3708170807080708070616f876f806f806f806f236d6e6d606d416d406d406ca56ca06c816c236c206c206bc36bc06bc06b636b606b606b606b606b416a8668ed68e068e0686468606803680067a367816780678066a7668166806680666166606587658065806580652365206520652064c3630e63006265626061c561c061c061c061c06144614061216120610160a360a060816080606160035f085ec25e825e805e425e215e205e205e015e005de15de05dc15dc05da15da05da05d245d205d205d205ca45aee5ae05a645a605a035a005984598059235920592058a458a058a058a0584358405840584057a557a057a057a057625760574157405702570056e154f054e05426542053c353c0536353605303530052a352a052a052a052a051e651e051e051e051e051e051e051e051e050c950c050c050c050c050c05006500050005000500050005000500050004ee94ee04ec14ec04ea14d2c4d204d014d004d004c654c604c414c404c214c204be24be04be04be04b834b804b804b234b204b014b004ae14a834a804a234a204a204a204a204a204a01494647ad47a047434740466746604641464045c445c045c045634541454045404540452144474440442143c343c043a143a04381438043804380432343204301430042e142c1424442404240424041e3402e40204001400040003f653f603f413f403f213f203ee23ee03ee03ee03e833e803e803e233e203e013e003de13d833d803d803d233d203d203cc33cc03cc03cc03cc03cc03ca13be63a4d3a403a4039c439c039633960390338e138e038e0380737e137e037e037c137c036e736e036c13663366036413640362136203620362035c335c035a135a03581356134e434e034e034e034833480348034803423326e32603241324031e331e031c131c03163316031223085308030802fc62fc02fc02fc02fc02fc02ee72ee02ee02ee02ee02ee02ee02e072e002e002e002e002d652d602d412d402d212d202d202ca42ca02c812c802c612c602c602be42a6c2a602a412a4029e329e029c129c0296329602922292029202920292028852880280428002784278027612760274126a526a026a026a026812680266125a625a025a025a025a025a025a024c724c024c024c024c024c024c024c023e7226c22602222220121a321a02162214120e320e02083208020802004200020001fe11f071f001f001ee11ec11de71de01de01dc11d441d401d401d401d021d001ce11c641b0b1ae11a831a8019a7198119231920184718211785176117411702166516411621156615411521146614411421142013e213e013a213a013a0136212c512a112811280128012421240124012021146112111011100110010c210c010c010820fc60fc00f820f610f220f200ee20ec10e820e610e220e200dc30dc00da10da00d430c480c400c210bc30bc00ba10b430b400b400b020b000b000ac20ac00ac00a820a800a800a420a400a400a210a200a200a010a000a000a000a000908076d0760076007410740074007400740074006480640064006210620062006200620062006200528034f00390001 0x174b45bb51b4304951d04b88255d0922c5a4ae1724ea102b470139e407cc30364a0171c809dbc9930b48963234b792b5d29570e48d732368b094a820a6db4b96aa5ccfa3661edb2de4b99e96ccf0b06761b33a0c19b968cbcaa66e9b3362a946944cb8a86691b2836d999a6ccb4a86641b3310c19795ccb82865a9924248995068c842a6545b3290a8ee844c882864f1b1d36d99326cc94b6648583200a191150c842e64059168289a025fcfd2ee7295ed14ab8e24dc3523e14916c546b9c15fcd4ade6055f2c2a74894ba08a3c824d62a2570a927cac2fe5016f230af8f8537ac25ba411d6706a9f82b468139e007cc1036490171c009e3b17a3f26ab2835ba52addc8d63e26ab2035c71aae36d16542771e9376281dac60dcee03e5f81b2400b8dc04edf6c986354b091a61ed5adf68d74b45b9d1aca64e5890736e35cb59ae62f1b2df6b98726cc58b662a583140d989860c462f41c4951304b74d64c3dae61c9b2c14698634ec2d2f5808d23b26b069255841aa24097082d180154c213660e552882697f950c1636608db27f4d97f150c0c36604183002b97f850bf9324148d2fb0d179054becb65f4151d806979850be2365eedb1cf4d97b16cbd4b05e2142f32a17905cbc4b221e4d3196bf8c35dc49abda2d571069b86b47c29a2d7e8db092bf8315bc04abdfa54e902973f1479449dc744de0924b7e05fbe42dde815ef00a6f504b73823b0e0ed6006e870253b00f97a06c8e02e36013bae345d3152ee6a976a54b41aa5d75b2e0ac964464b11325d2d5ae06ab70458b3e285cedb2e64d97296cb90b05c61b2e20c16e150b58285b6542d50a16c85cb50285b8d72db4b96c05cb4c285b2172d80a16b35cb552e5a8572d32a17045eb3a2edbed7ade4bd6e95eb68a95ae17ad20a56835cb3eb258f192ce6b961a64b349c5984d2cb07165034b21a4d8ed06c64bd60a46b0122588d26c36836125eb0523580912bb2915d158af82457a1103702958144aec2456c050370715b14cae92e572512b82695b818ad40a566d72b24b957940ac0a655e952aa09156948ab0a25521603702955148a7c2254a050370715284caa4ae550112a70695302ca9012544d72a14b94f040a7c2653c552ec8bf7545bba22d5c315ed18ad64c53b15ab57e95a932bf4715b9ecabce054ebc29f5a14bac4a3d5c50df70bef405b72c2bb6c14eab09f5184ba8023d3a10cea03e5d81b2300b8d404e9b4bb4b255a551aab00d4690234cb5da59aad288d90c04a34011a5e2c52d152956a94a254a69a2d309169346ec283b55c1ba7a0ad0b04e330118cd2251a5120746944134a3cae5125528d6ad4624da2522c0c49a8a69544b46a212b46251a918af48357a39a3c6091a0546d45946a1c9b3ce16dc20aec184b55423a760ed0906e3e025a0dab4fa9368548b1492aa0dae4f4172760a13eb4da05a2cfe95a502753fa5c9e42e4ea1427d8d93e4609e0364e81827a46f3c9379e093cecd1e7548f3a23793c9d4504aa846bb41347a012ecfc91e7b46f2713a89c954ee172730a0f304b70423b020ed5306e9c82b41c139d2076712b9321549b8a24c64d25a0312c0149bd26cc89166e46ac00395441a9740666c47f35a379a81fcd20ee6806f338334e015a0c09cb903332b4a991a34c691937052820252e00ccc28ee6046ebf83b5401bcbe0be5e0572e8279701196e0665a46f2c2379c1a3cda51a662893113696c9a2fa12d4f08e9a83b40c1b96c0a6590312b814954aa4a71b2034692916c928b24924d24824d2825d91c9349e1424d4bb25255808934901424b6b5253569252b48e559340525a819951afca2d5e4e4ad00a36930ab48c4d9f50bef205b6fc2bb6814d32076808372d014c708f64446b1312a8fd26c769163947b211528cca544a4a8650231b23c9022c47ed923e6a91aa4c8e2344791823b6a91b24c8d9aa47315a386b51bb568d52f464568fe04a320118cdab4649363124d21c5a905ab47a97e3a4af1a24d8c0ad4484a9f20bef105b6f42bb6414d300567e82718c08c5c5522c6d912a448acb643e5921e2890e9368a5aec384da280a11345a895ab44455a236bb0fb558889b43a142208b50fc56879ab4385597c072598198b62fc5515e274ad12246884ab436519f00bef005b6ec2bb6014d7a096a68472c814c32d6212691072648612a422da2166c106a548452542891a042950635484a2f416d5a114b508256820ad2961146202306238831a641cd360d68b05a3a828a940e52a0327430811821a540e95a0628d0235a80d2b40455a178bf0ac5784dad41ed2a094ad0295a804a53da17dde0b6dc8576b829af012d4908e300117fd2ebf4955f946af993517c093fad75fa6aafc2367b8928bc049fb8b0fd4547e5aa3f0951f62a82e8107d22c3e6d505c020f895416c083ded61ee4a82d0107f9a2bf8915f746efa93b7c89bbe04aded24e2b012520a23ba110fb268ec0347a42e3b215078268f282478c2e3c2091df098eeb5677126bb2914fa04ced34a765a33b09594608cf5c577a9abbd0d1de74b6f325779125bc491de0476ef237514a31f24d87524ced84675c1b3a6d59cd49aeaa454bc153a6d71ca2b8e3150735a6ba2d15cf4acbb83a73d2e392571c52a0e6c6c732303905b1c42c0e5247724a3b9049dc668ee2a477111baec0e92e054e016c2c01437d181bc2d8570286e9b03a8d75d268ee825d73923b968ddc72b8e1950708a5b8251dbf276de9376ec95b7249d750749682a2b40d36e1719e0a8d60446741a3200b18e048d585465c2236a091b30b8d50446581a3441519c088d88246842a35e1319b068d6a4d67922b588d5ab272d51353600f3508fda746ed313f6949db484dda3266d112b684939ae0799f694cf346675233384a59b24a6b01e6651db308dd97276cb13765497b284ad9324ec91233540f3208dd8e46edb3476d125b6491db0476d723735097352119a0088cd0366441a31e0b18d048c5854626361ee4d1880d8b88645c01a30c151840486912c608363009517f488bf0245f12a2de1117b048bc84c5b8132ee975762a0b68265d12eae2954f604cb70505c9ad2e2d59704acb79295b42b19c0798a6bec3b576152fb0696d814aebea535e91daf08dd752ac7a936334972e61596c06caf23d5a91aa580a96549ab0a4557d1ead0149480949582a154092b88f1668b0b2b64591aa2b69315e8d0b1460585aa2b89315c6a8afc56579ad2bad595b4bca512551c2d0a804853020acc58561aa0a2041562b8aa460548ae2a251150268a715c1400809e0414c6a0a5b485292e09c041486aca3a4d518132d3169676acb1a5f5812bab4935572beaa95b54caba9e54d4d256a49275142d2540a84d024a1854505b6256511400d8928644902227c1513c0486592c4e836270951374889b0244d122246151330489885c4881b25ed752e2a0908364b22d256d59280ac94b5d495aaa500d9220a09345a4962b248d59232729085631c0f28517d3f8ae9ea5f4ed2da7295d354a69924b4c123a5a5592a28c6312e49c2b2401191e6b08bb4844d3223a951166d08db604492a22c9291948c7c04a445aa22f179106ac8b25a4552b1fe514fc0b4260124451c222d311369a893454411d21e148fb0947b83a12c090940410d6b08625412008214531086c083154414a62084d1022982381011808200d40ff6907f25c114081f8d28fb4ac7d0463e1ad1ee958f60ac8e45f46a2ba30d69146948725642cafa1256d072ae81953404a59fa51cf90b47a84a110091e6550f12d87216438ca21de550ed2d86f16436c9a1d6570dc2a83395c3849b1b4498d20746582a3a1ae9c8d54e74ba6f2553401d1920a8e58b47245638dab1c4934dc48a70956320151bed68de6ac6eb4a371a31b6958da2ac6784a360231ae110d606c6a8341d80a1a6570d10b869256340ab19e4d8ce06c6615c3282e196958c92ac6414631c231e517cf08ae7735f3b1ab9d4d1ce94ac73156380a31b24d8d40a46684a3181d188150c20d85206428c22180150be0d84e8642681a1781709b0a85d2462e5221708d8b74683e8242d51b160558a90ac4c8362cd2315c558a70ac508462c42e15e170b02745712a15c2e1400d89804c5515c2a0ae158d74a46aa55a5d2752a9524e8a725452c5a2922b146d58a249a4da45284951401589e6b44eb56271a5136d189a4ac4c94a2602b18717cc18ae5fb5f2f5ab976d1cb64a45a24a2c91d15a558a60ac4f84625c1b12a9604202020820221341269804002048a580f80807a080844d047a600f0081049608d4a01d010220a511651884274451360e4080fe968882b4439562089d10c4d87b0b41c0200d81006a0407e4b44215a20cab1045288128c3d05a0d0100f21287f4943f23a1f4960f0168792583b82c1dc250f69287a4743c15a1d81612917c928ae4835f239ab918d1c894b442a4a2011d0f8568750b41981010c0a084490310c839854195220aa510402483886c04832060150110881f8140f89205c1906f0a830a3412c9a0784906d0d8048640b42a00c0d03b0281d1241ac2e00e1500f0880283414c9a0944905204c248161a5a28d09145126c2412619c220561104624832b56191268b85784524c15056010130a0510280883134a1852b0b45784e28c13856038230ba4d05b2482ea44164220b6510580882c8261600b0bed145e48a2e136168930ae110250882792414d220a4110504702794c155ab0a8934512bc271260902b0060984728811044128a2092110474702314c131a5096958482bc229460842b01a118200a82184407c220825401e0880e8540fc220381103d2a00d8440dc1c06c5203b0981b12a0e493030118370281b13a0d49b02e1184269e203470f92787891c3a46e1c13a0d09502c11820028159340941a03c0501d02814124088120360502c6a015a440a528050510266a012a4408d280445101f0800e0400811e83c8d41d27a0d93506821032100180540b81a0c9ae824d543169a183450bd2e8129542e49a16a450a89b04e4982406c108260580a026970148b409456045ab0209340748a07a350389301a0980a6b805b5a025ab010d280768c03256015230085180308c3945f1c22b8dcd7c6c6ae353471992f0c69186046c2b15e134a30884d8332480a856030230040db4169f8f347c6927dde91e9c46f4914fa18a5ce451e562872293b8bc9bc344ae0024ef604f75825b7011d8c086b583b5101ba3e0acf404e6281f2580d8e805c010260001f 16 5 11 10 6
def m_967 : Nat := 0xff00ff00ff00ff
def s_967 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_967 : Nat := 0x1700570057007f
def bds_967 : List (Nat × List Nat × Nat × Nat) := [(m_702, s_702, 5, g_702), (m_776, s_776, 5, g_776), (m_778, s_778, 5, g_778), (m_673, s_673, 5, g_673), (m_767, s_767, 6, g_767), (m_772, s_772, 6, g_772), (m_761, s_761, 5, g_761)]
theorem kn_967 : KnownBin bds_967 := by
  intro b hb
  simp only [bds_967, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_702
  · exact lb_776
  · exact lb_778
  · exact lb_673
  · exact lb_767
  · exact lb_772
  · exact lb_761
theorem sub_967 : ∀ b ∈ bds_967, m_967 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_967, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_967 : ∀ b ∈ bds_967, canon b.1 g_967 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_967, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_967 : dagCheckRootsF m_967 g_967 bds_967 (dagRefF 835 (dagTraceF m_967 s_967 8 f_967) l_967 0) s_967 8 = true := by decide +kernel
def node_967 : Nat → Bool := dagCheckNodeF m_967 g_967 bds_967 835 (dagTraceF m_967 s_967 8 f_967) l_967
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_0 : treeBlockF 0 32 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_1 : treeBlockF 32 64 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_2 : treeBlockF 64 96 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_3 : treeBlockF 96 128 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_4 : treeBlockF 128 160 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_5 : treeBlockF 160 192 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_6 : treeBlockF 192 224 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_7 : treeBlockF 224 256 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_8 : treeBlockF 256 288 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_9 : treeBlockF 288 320 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_10 : treeBlockF 320 352 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_11 : treeBlockF 352 384 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_12 : treeBlockF 384 416 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_13 : treeBlockF 416 448 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_14 : treeBlockF 448 480 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_15 : treeBlockF 480 512 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_16 : treeBlockF 512 544 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_17 : treeBlockF 544 576 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_18 : treeBlockF 576 608 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_19 : treeBlockF 608 640 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_20 : treeBlockF 640 672 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_21 : treeBlockF 672 704 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_22 : treeBlockF 704 736 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_23 : treeBlockF 736 768 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_24 : treeBlockF 768 800 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_25 : treeBlockF 800 832 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_26 : treeBlockF 832 835 node_967 = true := by decide +kernel
theorem nc_967 : ∀ j, 0 ≤ j → j < 835 → node_967 j = true :=
  (joinChecks (joinChecks (joinChecks (joinChecks (certBlock nb_967_0) (joinChecks (certBlock nb_967_1) (certBlock nb_967_2))) (joinChecks (certBlock nb_967_3) (joinChecks (certBlock nb_967_4) (certBlock nb_967_5)))) (joinChecks (joinChecks (certBlock nb_967_6) (joinChecks (certBlock nb_967_7) (certBlock nb_967_8))) (joinChecks (joinChecks (certBlock nb_967_9) (certBlock nb_967_10)) (joinChecks (certBlock nb_967_11) (certBlock nb_967_12))))) (joinChecks (joinChecks (joinChecks (certBlock nb_967_13) (joinChecks (certBlock nb_967_14) (certBlock nb_967_15))) (joinChecks (joinChecks (certBlock nb_967_16) (certBlock nb_967_17)) (joinChecks (certBlock nb_967_18) (certBlock nb_967_19)))) (joinChecks (joinChecks (certBlock nb_967_20) (joinChecks (certBlock nb_967_21) (certBlock nb_967_22))) (joinChecks (joinChecks (certBlock nb_967_23) (certBlock nb_967_24)) (joinChecks (certBlock nb_967_25) (certBlock nb_967_26))))))
theorem lb_967 : LowerBin m_967 s_967 g_967 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_967 sub_967 gl_967 rc_967 nc_967

def f_968 : Nat → Nat × Nat := unpackForestF 0x1f 1 5
def l_968 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x1f 2 1 5 1 2
def m_968 : Nat := 0xff00ff00ff00ff
def s_968 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_968 : Nat := 0x1700570057007f
def bds_968 : List (Nat × List Nat × Nat × Nat) := [(m_776, s_776, 5, g_776), (m_702, s_702, 5, g_702), (m_778, s_778, 5, g_778), (m_673, s_673, 5, g_673), (m_761, s_761, 5, g_761), (m_767, s_767, 6, g_767), (m_772, s_772, 6, g_772)]
theorem kn_968 : KnownBin bds_968 := by
  intro b hb
  simp only [bds_968, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_776
  · exact lb_702
  · exact lb_778
  · exact lb_673
  · exact lb_761
  · exact lb_767
  · exact lb_772
theorem sub_968 : ∀ b ∈ bds_968, m_968 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_968, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_968 : ∀ b ∈ bds_968, canon b.1 g_968 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_968, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_968 : dagCheckRootsF m_968 g_968 bds_968 (dagRefF 1 (dagTraceF m_968 s_968 7 f_968) l_968 0) s_968 7 = true := by decide +kernel
def node_968 : Nat → Bool := dagCheckNodeF m_968 g_968 bds_968 1 (dagTraceF m_968 s_968 7 f_968) l_968
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_968_0 : treeBlockF 0 1 node_968 = true := by decide +kernel
theorem nc_968 : ∀ j, 0 ≤ j → j < 1 → node_968 j = true :=
  (certBlock nb_968_0)
theorem lb_968 : LowerBin m_968 s_968 g_968 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_968 sub_968 gl_968 rc_968 nc_968

def f_969 : Nat → Nat × Nat := unpackForestF 0x3b124f62450169fcb17b962ef2b56e569dca8e7951a80b4bcb69d96d272d2f65a5dcb4b99694b2d28ee34ecb4a1b257364a86595ed64b9ac9432ca96895cd12a1a217344286585ecc4b99894330ae66150cb0a402d1f21ae64250a98ad8cd72a62ad4b5ea96bb52d3aa5a6d4a3aa9473528e2a51b54a35ba69574d1aa51a5ba38b7469524ead0945a124a926d5e8e2bd1a57938af269520eaa89455124aa05154092a41b00b43a66934cd140527cfb5e9f6bb3e95a7d274fa469f47c0292e11af4235d846b908d4a11a8cc236846a12c942112742249924b92494210af47b5c8f6a10854a292e452508a0b914142102f42b5c856a10a57214a8420520148f02d42052e30b567f4b8c2d55852f30a5d6149cc2935852630a466148aea919d51930a446147ce4911851eb7a4c6f488c24a9b0a6361446124cce9319d223392867248c20a988a63114462030c4051841300a434e8b4bc9413a2b2735e4e6b49cd5939a92725e574889c949389d2713652270a44d1381d278284f0489c0d8051f9bc5e4b6886f148ddad24350376ac6ed38dda69ba5e374b46e958dd291ba463747c6e4a8dc931d9283b2486e0a8e00c1c0143704c028ec922f1245a326b864970922b124522f69848d68b1a816250246ac54930912d13b50274a048958911f122390146e449100a2f10344028a43c91009af0e344026a43493009a30c24c0268a26d384da109a3e1347a04d10092f08344024b416d402d28062400b4680495821260423c024a40493809268123e03688048f405198001f 8 11
def l_969 : Nat → Nat → Option Nat := unpackLinksF 0x3c20f007a4ee887a01e70b982e587960debb781de036e5db836e0d89b5c3d703544d503540d3134c0d303444d103440d103440cf133c0cf033c0cf03344c25b080c187003c002fe1bf82fe0bf82fc1bc96f20bc82e66b80ee00b786d64b582d60b392ce0b382c64b182c60b182c60af92be0af82be0af82b64a2da8a0a2066ce9a86681990a62198825e290ba3858e023808b1a26389821e487821c187021c08702144850214083120c083020c08302044810204081020407f11d167385ce0720dc807185c607181c606f15bc06d8daa66a05a806811a0068019e167819e0659196065818e463818e063818e06191860618186061817e454d950154014c25285481518544150854204f893a24d893604d813224c813204b8907441050404008fe13f80fa23e04f613d04f213c04ee13b04ea13988e223880e203788de03780da22cd0b012c00b002c00ac2298ca602888a2028809e227809a226809a0258894124847111c006c21b006821a00642190060218005e117805c117005a116805a013984e013804c113004c013004a1110c440110040210003e10f803e00f041b100b0001 0x19b4ce78bd87177a9ad74b59e36ad86d478da3743453549bda927b122a0a414c472428c725a263354324b81a940211c1423409499d517ba62ef1455c18a5d0d5b89aaf3b4ec169abe934b922ada3de6473ca8d43d18ee2500d8b9b45735ca86a05ccf0a1b8d70c92e6c95cd62a1a617338282f34c2c6885a91371a7643425e47aea8d768ae6c950d20b99a1435d2e6b250d10b99814350ae69950d20b9a21433d2e67250cd2b9985438a2f6145de36bd88d778da771349c76858ad07852f7025ddf4b886964c52aef252dd4a3b6941751e95a35d82bdaa54b402f658520c46992d7321285d234c66b9768d0a11a5c138b5269640e2b41a5da4c084796e4a2d09258828ac0481cd012d24102400c48176d2ae9a325a3998463708e2dd1a58038ab0696a4a2d09257828aa049648e2c51a58138af2695a4a2b09255828aa04987177062d63c56c58ab88d7b0daee134ec169a949247d20aca3dc04757e8e6f91c5ea36bc46b728d01d18db13ab326d5c0eaa41b1925c9f8bcf9174d5a6d3b49a668ab2d06912d51a59954acf89465523512455847c3a8ca05223fa54336b81cd40211c04a4c2d48948d7a8daeca355716a492d28a5a351256944ab429390d25502460f4853e8f9c51e8735c932b920542342e44050336b92c97248ae479508c0b90e141212413a44284692c93a09212423a9846d2c9424d2e492508b0b90c14241ae47b508a0b90a142352e462508b0b91414221ae43b50862b90a542522f39c5d9d6bd38d766dae2db59316ab34d4a65a8cbb50954bcfa97655274a24980484fc9051d1d13236912bd1c54a242f420520c46904d42052e3b2347f4b85a911c094369246a050ca09035202ba3c1c46012931c91e379286c248d20a190120624072494ec9195d1f3aa3272488e0931bd223402863048da531b0a23381862028d4931a5223412867248ca53190a23181862028f8d75c5ad403567e6aaacd386da13ea5e7c4baf6939e926bca4c41494f0919dd22ba24407484e68f9c51eb712a6b24ccc0a9841304b44226b8bc94025a40734c324b8508d0c9222ba442a468a60e1401a290284f048a64e1489a280284f048bf169762b2e35e5b6b4b4d5965a91fb4e0569ab097959292324a454924a918152092a364046aaa4e9509b2883a4e06c669112da217a440846890d40792e0d2341848810920351e19b5c2d488068c00da21e0283904876060e00a1e1283b24872060e00a2645e4a8a492d691dab2334e4569a48d1409a12225e434b4849590529202462448a7e8f8091e9f12a3d24c740a8dc130b230336b864970b5a20aa40284685ed30411816b502c4a054930411814350274a0068f00d1e1ac5e348b463158c2291735a2b6ac48d3811a694a5a264ac4a938192692a3e24472328c85d1889230166984491081a207244166983c91071a206a341a49830930311a0b34e15684209282d230a23e1347a20d103120073500d4a0168d025260423c0368806d10862f0fc521d6bc36d4815a68134a1968c2ed1449a208a5e0f4b4149581d290324e0549a088f8091ef5b4fe469794d1ea1a1d2a4f9e4970691d8121a6a3f36476468dc05198001f 14 5 11 8 6
def m_969 : Nat := 0xff00ff00ff00ff00
def s_969 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_969 : Nat := 0x1500170017005700
def bds_969 : List (Nat × List Nat × Nat × Nat) := [(m_954, s_954, 5, g_954), (m_736, s_736, 5, g_736), (m_956, s_956, 5, g_956), (m_700, s_700, 5, g_700)]
theorem kn_969 : KnownBin bds_969 := by
  intro b hb
  simp only [bds_969, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_954
  · exact lb_736
  · exact lb_956
  · exact lb_700
theorem sub_969 : ∀ b ∈ bds_969, m_969 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_969, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_969 : ∀ b ∈ bds_969, canon b.1 g_969 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_969, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_969 : dagCheckRootsF m_969 g_969 bds_969 (dagRefF 238 (dagTraceF m_969 s_969 7 f_969) l_969 0) s_969 7 = true := by decide +kernel
def node_969 : Nat → Bool := dagCheckNodeF m_969 g_969 bds_969 238 (dagTraceF m_969 s_969 7 f_969) l_969
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_969_0 : treeBlockF 0 32 node_969 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_969_1 : treeBlockF 32 64 node_969 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_969_2 : treeBlockF 64 96 node_969 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_969_3 : treeBlockF 96 128 node_969 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_969_4 : treeBlockF 128 160 node_969 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_969_5 : treeBlockF 160 192 node_969 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_969_6 : treeBlockF 192 224 node_969 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_969_7 : treeBlockF 224 238 node_969 = true := by decide +kernel
theorem nc_969 : ∀ j, 0 ≤ j → j < 238 → node_969 j = true :=
  (joinChecks (joinChecks (joinChecks (certBlock nb_969_0) (certBlock nb_969_1)) (joinChecks (certBlock nb_969_2) (certBlock nb_969_3))) (joinChecks (joinChecks (certBlock nb_969_4) (certBlock nb_969_5)) (joinChecks (certBlock nb_969_6) (certBlock nb_969_7))))
theorem lb_969 : LowerBin m_969 s_969 g_969 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_969 sub_969 gl_969 rc_969 nc_969

def f_970 : Nat → Nat × Nat := unpackForestF 0x3a7874b94b929403a3be387c681d0c327864b56b8ad403239e4c3c88190c31f863b0c6e2d10319801f 5 10
def l_970 : Nat → Nat → Option Nat := unpackLinksF 0x5c2e170b854aa150994c261309844a2110793c1e0e1703443801 0x1397252842387c68bd715a8224c3c8828c05a2574fa6971d1dda1b64f6496991cd21963f247638dc319801f 9 4 10 5 5
def m_970 : Nat := 0xff00ff00ff00ff00
def s_970 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_970 : Nat := 0x1500170017005700
def bds_970 : List (Nat × List Nat × Nat × Nat) := [(m_736, s_736, 5, g_736), (m_700, s_700, 5, g_700), (m_956, s_956, 5, g_956), (m_954, s_954, 5, g_954)]
theorem kn_970 : KnownBin bds_970 := by
  intro b hb
  simp only [bds_970, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_736
  · exact lb_700
  · exact lb_956
  · exact lb_954
theorem sub_970 : ∀ b ∈ bds_970, m_970 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_970, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_970 : ∀ b ∈ bds_970, canon b.1 g_970 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_970, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_970 : dagCheckRootsF m_970 g_970 bds_970 (dagRefF 22 (dagTraceF m_970 s_970 6 f_970) l_970 0) s_970 6 = true := by decide +kernel
def node_970 : Nat → Bool := dagCheckNodeF m_970 g_970 bds_970 22 (dagTraceF m_970 s_970 6 f_970) l_970
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_970_0 : treeBlockF 0 22 node_970 = true := by decide +kernel
theorem nc_970 : ∀ j, 0 ≤ j → j < 22 → node_970 j = true :=
  (certBlock nb_970_0)
theorem lb_970 : LowerBin m_970 s_970 g_970 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_970 sub_970 gl_970 rc_970 nc_970

def m_971 : Nat := 0xffff0000ffff
def s_971 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_971 : Nat := 0x17570000577f
theorem lb_971 : LowerBin m_971 s_971 g_971 9 := by
  refine lowerByRows [0, 1, 2, 3, 4, 5, 6, 7, 16, 16, 16, 16, 16, 16, 16, 16, 8, 9, 10, 11, 12, 13, 14, 15, 16, 16, 16, 16, 16, 16, 16, 16, 32, 33, 34, 35, 36, 37, 38, 39, 16, 16, 16, 16, 16, 16, 16, 16, 40, 41, 42, 43, 44, 45, 46, 47] (by decide +kernel) ?_ (by decide +kernel) lb_967
  intro w hw
  simp only [s_971, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_972 : Nat := 0xffff0000ffff
def s_972 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_972 : Nat := 0x17570000577f
theorem lb_972 : LowerBin m_972 s_972 g_972 8 := by
  refine lowerByRows [0, 1, 2, 3, 4, 5, 6, 7, 16, 16, 16, 16, 16, 16, 16, 16, 8, 9, 10, 11, 12, 13, 14, 15, 16, 16, 16, 16, 16, 16, 16, 16, 32, 33, 34, 35, 36, 37, 38, 39, 16, 16, 16, 16, 16, 16, 16, 16, 40, 41, 42, 43, 44, 45, 46, 47] (by decide +kernel) ?_ (by decide +kernel) lb_968
  intro w hw
  simp only [s_972, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_973 : Nat := 0xffff0000ffff0000
def s_973 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_973 : Nat := 0x1517000017570000
theorem lb_973 : LowerBin m_973 s_973 g_973 8 := by
  refine lowerByRows [0, 0, 0, 0, 0, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 23, 0, 0, 0, 0, 0, 0, 0, 0, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 0, 0, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 55, 0, 0, 0, 0, 0, 0, 0, 0, 56, 57, 58, 59, 60, 61, 62, 63] (by decide +kernel) ?_ (by decide +kernel) lb_969
  intro w hw
  simp only [s_973, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_974 : Nat := 0xffff0000ffff0000
def s_974 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_974 : Nat := 0x1517000017570000
theorem lb_974 : LowerBin m_974 s_974 g_974 7 := by
  refine lowerByRows [0, 0, 0, 0, 0, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 23, 0, 0, 0, 0, 0, 0, 0, 0, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 0, 0, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 55, 0, 0, 0, 0, 0, 0, 0, 0, 56, 57, 58, 59, 60, 61, 62, 63] (by decide +kernel) ?_ (by decide +kernel) lb_970
  intro w hw
  simp only [s_974, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_975 : Nat := 0xffffffff
def s_975 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_975 : Nat := 0x1757577f
theorem lb_975 : LowerBin m_975 s_975 g_975 9 := by
  refine lowerByRows [0, 1, 2, 3, 4, 5, 6, 7, 32, 32, 32, 32, 32, 32, 32, 32, 8, 9, 10, 11, 12, 13, 14, 15, 32, 32, 32, 32, 32, 32, 32, 32, 16, 17, 18, 19, 20, 21, 22, 23, 32, 32, 32, 32, 32, 32, 32, 32, 24, 25, 26, 27, 28, 29, 30, 31] (by decide +kernel) ?_ (by decide +kernel) lb_967
  intro w hw
  simp only [s_975, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_976 : Nat := 0xffffffff
def s_976 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_976 : Nat := 0x1757577f
theorem lb_976 : LowerBin m_976 s_976 g_976 8 := by
  refine lowerByRows [0, 1, 2, 3, 4, 5, 6, 7, 32, 32, 32, 32, 32, 32, 32, 32, 8, 9, 10, 11, 12, 13, 14, 15, 32, 32, 32, 32, 32, 32, 32, 32, 16, 17, 18, 19, 20, 21, 22, 23, 32, 32, 32, 32, 32, 32, 32, 32, 24, 25, 26, 27, 28, 29, 30, 31] (by decide +kernel) ?_ (by decide +kernel) lb_968
  intro w hw
  simp only [s_976, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_977 : Nat := 0xffffffff00000000
def s_977 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_977 : Nat := 0x1517175700000000
theorem lb_977 : LowerBin m_977 s_977 g_977 8 := by
  refine lowerByRows [0, 0, 0, 0, 0, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 0, 0, 0, 0, 0, 0, 0, 0, 40, 41, 42, 43, 44, 45, 46, 47, 0, 0, 0, 0, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 55, 0, 0, 0, 0, 0, 0, 0, 0, 56, 57, 58, 59, 60, 61, 62, 63] (by decide +kernel) ?_ (by decide +kernel) lb_969
  intro w hw
  simp only [s_977, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_978 : Nat := 0xffffffff00000000
def s_978 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_978 : Nat := 0x1517175700000000
theorem lb_978 : LowerBin m_978 s_978 g_978 7 := by
  refine lowerByRows [0, 0, 0, 0, 0, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 0, 0, 0, 0, 0, 0, 0, 0, 40, 41, 42, 43, 44, 45, 46, 47, 0, 0, 0, 0, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 55, 0, 0, 0, 0, 0, 0, 0, 0, 56, 57, 58, 59, 60, 61, 62, 63] (by decide +kernel) ?_ (by decide +kernel) lb_970
  intro w hw
  simp only [s_978, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_1022 : Nat → Nat × Nat := unpackForestF 0x3be35500317fbc26bef05afbc06bebcdbfaf36dee91f7ba246ebc98fb647dee2573b8356ed8dc7b725ceda9c7b6146ebc58fafc7ded2173b4356ebedc7b305ceca95bafa71ec6973b0271ec2573b0171ebe11baf06300315fae455002d7fac25beb056fac05be7b1bf9ec6de7b15fa9d7dea695b9ea63e975f7a816ce9ed9ba5b71e9a9b3a6271e9655b9e963e7d5f7a406ce8ed9b9f371e8a1b3a2266e7c9c7a126ce7e9c7a016ce7e5c79f056e7a18c00b57e6692f9d284e6690f9994be6e61399943e6612f9a084e6610f7dd6be5892f98359e5852f96b59e5a9679604bdf75ab7dd66e4d1b393248e4c52393048df758f7dc66e46d5b7db66e379eb8f958e3e1638de72e3b1bb8e560e369db7da53e1d9eb8bb58e2e16387672e2a5f38a376e1cd878946ee1f5838827ce1e94787176df654f7e67ae14d6385258df99cb8407ce0eddb7e361e0a1f382276df89878146edfb5838027cdfa9477f17cdfa5477e076df614c00b47df29d37c47ddb359f7b264deb5f76cc67dc19ef70576dc11db7867adc09bb73c66dced9b7395bdd606373953dce16f7402cdce14f7026cdc8df372134dc058f70b7cdc20d370063db315f6f570dbad9f6ca56db71c36d567db291800a5bd989bb6995bda654f6985bda614f6626cda0df368134d9858f66b7cd9a0d366063d9315f64a56d9291800a53d8856f62153d8816f62053d8699352c6fd635fb58a7ed785af5e163d781af5e063d629f35be8cd6ee335c57cd6e4d358973d65a335938cd675f359034d621cf52c67d50dbf56c7dd5a51b54163d531f754a71d5211b54063d4a99b5346ad4a91800a4bd4056f50153d4016f50053d3e99340d6fd1b1fb46a7ed305af4c163d301af4c063d1a9f349d8cd26e334a47cd264d346973d1d6334738cd1f1f347034d1a1cf40d67d091bf44d7dd1255b42163d0b5f742a71d0a15b42063d0299b4156ad0295800a3bcfe5d33f47dc5f59f3e164cf75f717c67ccd9ef33576ccd1db3b134cccd8f39e7ace69873316ecd519b35366cd496f37028cd494f3505bcd60f335053ccc5b333a7ccce09333063c5f15f32164cc2df331264cc25f32e567cbe5b32e366cba5732e356c5edaf2d174cb2e3327d77cae57327b56caa9c328467ca092f28247ca00af28023c9e4d317b5bc9a5d32638cc859df2516cc84d9b24270c8759f21a5bc8695f2182bc8608f21134c5ed2f20570c72d9f1e26cc7b1831e246c729af1d26cc728ef17956c6f1c318567c6b18319a66c669731826bc629731825bc5e5180095bc5a4d311363c569871116ec4c96f13253c4c16f13053c445b311a7cc4609311063c1715f1015cc34d5b0da4bc3691f0d82bc3608f0d134c16d6f0c16cc24d9b09a5bc2695f0982bc2608f09134c16d2f0826cc1e8ef05956c1a9730625bc1651800953c0c96f03253c0c16f03053c0a592de46fbe75fb0068cc035f300134be6dceff271be65fafca6bbf298efc86bbf218ef997cbe9a32fa28cbeb5f2fa024be61cede467be29d2f818cbcd5def715cbccd5af6270bcf19ef3a4bbce91ef382bbce08ef3134b78daef215cbbcd5aefa4bbbe91eef82bbbe08eef134b78d8eed97ebb65f2e7b76bb21a2e826fbaedf2e826bba099eea26cba6dd2e8263ba00aee8023b9e4d2de34bb86dbee5c7db9691ae1a63b909fae427cb868eee247db88dc6e2046b8618ede166b7b1aae025cb7a9aedf25cb7a98ede14600252edba5bb6e94edb85bb6e14edb164adb5bed247eb63632d947cb624d2d2373b5e9c6d217eb549aed5263b541aed5063b485f2d2d8cb4aa32d347cb4a092d2073adb59ed1274b42632cbe77b3e5b2cbb66b3a9c2cc567b3096ecc257b300aecc023b2e4d2b6b6bb2a5b2c7b66b2096ec8257b200aec8023b1e4d2b6b63b185fac617cb00ddac5068b029bec437cb029aec0a67b0a9b2c2374b0298ec082bb0208ec0134adad6eba46faf95f6be256ae898ebca7eaf29f2ba24baeb5f6bab71aea15aba063ada59ab756aae29b2b726bade9b2b7263ada5580093bad65b2b2465acad7eb4060acad5eb285baca14eb21649e15beb1174aab1feb0174aab1f6af37daaa5faacb6fab2d9eac86bab218eaa97caaca32ab024aaa1ce78567aa65f2a6565a9b17ea8070a9b15ea685ba9a14ea61649e11bea5164a715fea4164a715f6a3678a8a6329c567a871f69c17ea791be9e467a7f9f29e457a781ae9e063a705f29ca8ca720929c0739e119e9b154a239ee99956a6655288e7aa625f288e76a5e5529657ca5855296058a239ce88d76a5319a88c76a479ea93048a479ca92560a475da8896ea2b5be9067ca2b5ae8ad67a3b1b28de74a361228ad63a2b19a8c356a2ad9a8a85ba2a14e8896ca249f289024a2218e78457a1ed567fc6fa191f6864559fedbe82d7ea131b282d79a0b5ca82d71a0b5c27fb47a015f68047da0015a800469fe18e781669f15aa7e5689f0dbe7cd729f35c27c3679e055a7b4689e35be79c729e71c278d679e31aa7814600248e770749db1f6135679d61927557d84d19e6ae7b9ab5da6ac769ca0d26ab639c60926aa639bf9ea6fa619be5866a86e9ad19a6b3669ac96e6d1289ac94e6b15b9ae4f26b1539aa1b2134579a61926837c9a29926807c99759e6706c996d9a6605c996d5a1336b9921d26438c97d5de6305c97cd5a6227097f19e5fa4b97e91e5f92b97e48e5f03484cd6e5e074976e3258e779721b258b6696e9c25956796496e592579644ae591239620d21334b95e1925627c95a5925607c93b59e5503c94e9125413c94e1124ec6b94a0f2512449464f25104493b16e5006c93a99a4f05c93a95a1326b9361d24d28c9075de4c03c92e91241c7b92a0f2492449264f24904490716e4805c90695a4717090919e46138908dae449389124d24234b90852e421479084fe421339060921325b9021d24028c8d39de3f03c8fa91234c7b8f60f23c2448f24f23c0448d31ae3b06c8d299a3a1708d559e391388d4dae379388de4d23535b8d456e351578d44fe351338d20921324b8ce1d23328c89b9de320748c6a3226d778c21922f27c8be5922f07c89b59e2e06c89a99a2d05c89a95a2c17089d59e2b17089d19e2996c8a65822745789c56e2715789c52e2714789a092132338975c21d36788e9b22446088e91a1d26b88a9b21d23b8825b22146088251a1d16b87e5b21d13b8765b21e46087651a1d12384c15a1c47084f59e1b46086899a1a25c84e9ae1925c84e96e1846085c59a1715c84e5ae1615c84e56e1546085059a1415c84e48e1304600216e12034832d8e1102483298e0fa6183e5860c86e83496e0d25383456e0d1538321b1e245782e17208b5682492e092478244ae091238220d1e235b81e1b204b6681496e052578144ae051238120d1e234b80e0f20224480a4f2020447f316e0105c7f2959ff9387fe4d1fd34b7f452dfd1477f44fdfd1337f2091e225b7ee0f1fa2447ea4f1fa0447d31adf906c7d2999f79387de4d1f535b7d456df51577d44fdf51337d2091e224b7ce191f227c7ca591f207c7af59df106c7ae999f005c7ae959ee96c7ba581ec4577b056dec1577b052dec1477ae091e22337aa9b1e723b7a65b1e713b79e5b1e846079e519e7123788159e625c78a96de515c78a56de446078c599e315c78a48de204600214ddfa5b77e94ddf95b77e54ddf0645f11bdd657e773a31dd57c7720d1d637376ba31db57c76a091d62737649c5d91717581f9d6a6b75a98dd696b75a58dd607c5f119dd5274752231cfd7774e171cfb5674a9c1d046774092dd02477404add012373e0d17c36b73a171cbb5673092dcc2477304adcc12372e0d17c3637281f9ca07c710dd9c91687129bdc837c7129adc4a6771a9b1c637471298dc492b71248dc40345f0d2dc317470a231b75777064f1c10446dd1edc003c6fa911bf13c6fa111b745b6f6171b72566f25c1b7c676ee4e1b7b6b6e84e1ba1346ded2db794b6de51db793f6de4cdb70245f09adb603c6d2911b513c6d2111af45b6ce171af2566c84e1b21346bed2daf94b6be51daf93f6be4cdaf0245f098dae03c6b2911ad13c6b21119fc7b6ae0f1aa2446aa4f1aa04467f1cda887e6a21f19fa7669c4e1a7134680dada59386964d1a0363692da1a016f68e9f1a016b68059da216c6869d1a01636804fda013367e0917c24b67a1b19d2746765b19d07463b5fd9c07466aa319b17466a2318ed776641f99907c63a9d99804465d5e99705c63a959959686565918f46f6505f19417063d19d8f16f64a9f18f16b63c59d9116c6429d18f16363c52d8f14763a0917c233612dbd8cc7d63291984a6362c9f98b27c6128ed8947d624dc58914661258d8797e61e5f18493b6145f98517c6171c18514661248d7c0665f31a98325c5f29ad8225c5f298d8115c5f25ad8015c5f258d7f1445f55e97e4705f45d97d15c5f248d7c04600212d79a5b5e694d7995b5e654d790644595bd7047e5db6317747c5da0d1703735d36317547c5d2091702735cc9c5731715c01f970a6b5c298d7096b5c258d7007c45959d6f2745ba23169e775b61b169b665b29c16a5675a896d6a2575a84ad6a1235a60d11636b5a21b165b6659896d662575984ad661235960d1163635901f96407c578dd96316857a9bd6237c57a9ad5ea675829b16037457a98d5e92b57a48d5e034458d6d5d1745722315167756e4f15b0445451ed5a03c5629115913c5621115146b55e1b15126655a5c151d675564e151b6b5504e154134546d6d5195b54655d5193f5464cd510244589ad5003c53a9114f13c53a1114946b5361b1492665304e14c134526d6d4995b52655d4993f5264cd4902445898d4803c51a9114713c51a11139c7b5160f1442445124f1440444e71cd4287e50a1f139a765044e1411344e8dad3f9384fe4d13a3634fada13a16f4f69f13a16b4e859d3c16c4ee9d13a1634e84fd3a1334e60911625b4e21b1372744de5b1370744a39fd360744d2a31351744d223128e774cc1f93307c4a29d9320544c59e93106c4a29992f9684be5912956f4b85f12e1704a559d2916f4b29f12916b4a459d2b16c4aa9d1291634a456d291574a20911623347b1bd26d7d49a9591ea634949f92527c47a92d2357d48cdc52315647a58d2197e4865f11e94b47c5f91f17c47f5c11f15647a48d1606645b5a91d26c45a9ad1c26c45a98d1b16c45a5ad1a16c45a58d1915445d9e91857045c5d91716c45a48d160560020ed1506c4471951235f44e5811235744856d121534461908bd6f4421d10a47f43e1d10a47d43a0910a273434df50d1714281f90ab6f42ad9d0a96b42a58d0a07c22f59d0907c4175950645f41e5c10645741856d061534161908bc6f412190fbd7f40e190fbd7d40b9e10208c3ef59d010243ee9ccffc7d3fe5c4fb87e3f11bcfc4673f79f0fc4573f05acfc1633ee1f08bc673ea150e867b3e4158f90543a19e8f807c3a19d8f70543d75f0f5a583d6150e86733a15d8f44663a11d8f30243a098cefe7a3c6520efe723c3580efd763be584e806e3a35bcee67c3a35ace8d673b31b0ebe743ae520e8d633a3198ea3563a2d98e895b3a254ce806c22f15ce717439a230da6773965d0e508c3695dce406438a9f0e316438a1f0da5673861b0da266382170da25637e5c0dad6737a5c0dac673745b0dd16036b15cda95b36a55cda94b36a51cda02422e9acd906435e9f0d816435e1f0d156735a1b0d1266356170d12563505b0d416034715cd195b34655cd194b34651cd102422e98cd006c33a9d0cf16c33a1d0c057f3361d0cc28c3325d0cc08c3015dcca87e32a1f0c0276326110c8d7a322170c025631c5a0c71643031bcc597c3165c0c0c673025bcc427c3025acc096730a5b0c227430258cc094b30251cc002422e96cbf06c2f69d0be16c2f61d0af67f2f21d0bb28c2ee5d0bb08c2bd9dcb987e2e61f0af2762e2150b7e7a2de1b0af2662d85a0b61642bf5bcb497c2d25c0afd672be5bcb327c2be5acaf9672c65b0b12742be58caf95b2be55caf02422e92cae3552851bcacc7d2b3154a136f2a55f8ab46c2a55e4a95722a55c4a9570284d1ca6d7d29b1f4a695629a518a11632905f8a417c2931c0a414628452ca197e2865f0a2570286558a113b22e19896d6a27f5a096b6f2795c89e57025ad9c9c16c2731809c14625a5ac9a16c26b1809a14625a58c9915425d9e89857025c5d89716c25a4ec8b8562571a08c56f2511c89447023159c8c46a24b180919662465708c16b2431808f96623e5708c16323a5108cd7a2371c08c9762325708c15b22e1180082322a1b08746521ed7c8926021ed5c87a5b21e94c870640055bc860741ff1fc850741ff1f4840341fedcc82b7d20a9c47f87e200dbc803672009ac802631fe1f0015671fa1f07b5651ef17c7d2701ef15c7ba5b1ee94c7b0640051bc7a0641c55fc790641c55f4786781de230715671da0d0713731d51f4752711c41f871c6f1c719c7367c1c715c71a6b1c698c7107c00519c700541779ec6e8561ba1505de7a1b61f05de761b21506b57c1acd606b0541779cc5dd761a71985dc761a20d05db631959e8672481959c8665601955d8652611761b85e56f18f9f05e56b17959c6246c1859d06124817958c5e46617ed585e36617896c5e2531761b0014571729d05c08c13f9dc5b27416a2304fd771661905837c1629905807c13f59c5706c13ed985605c13ed585527014159c5427014119c52a6c14a9805045714096c5025714092c5024713e0d00136b13a1904d37c1369904d07c11b59c4c06c11ad984b05c11ad5849a6c1269804745711c96c4725711c92c4724711a0d0013631161b0443741129b0440740d75fc43074106e304227410623035d771001f84007c0d6dd83f0440f95e83e05c0d6d583ca680f29903646f0ec9f03b2700d919c3626f0e6df03626b0d899c3826c0dedd0362630d892c362470d60d00135b0d21b0333740ce9b0330740939fc320740c2e30312740c223024e770bc1f82f07c092dd82e0540b59e82d06c092d982ba680ae9902556f0a89f02a27009559c2526f0a2df02526b09499c2726c09add02526309496c252570920d00134b08ed5416c6f0891f42245505adbc1ed7e0831b01ed7907b5c81ed7107b5c016b470715f41c47d0709581c24605a98c19a7e0669f01a47006691816a4b05c9f81727c05f5c01725605a8ec010660315a815568030dbc13d7204f5c00c3670469b0124600469180c26b03e9b01046003e9180c26303a9500ce7a0375c00ca760329b00c23b0041580b4680075bc09c720271c001d670071a80846001c9980725c0069ac064600149980525c00698c042440095e8034700089d80225c00696c0104600204c0003f 11 11
def l_1022 : Nat → Nat → Option Nat := unpackLinksF 0x2d4476947b4a05a502d28167ccb38359b0acd0565a7b2b159582ca836502b28059386c94563c7b1c158e02c6c36322b19058c06c58562c0b150d8a82c5036242b0b3d7d46bdc75e07af0057802bc015c8cade356d12b6055ac2acf3d668ab3415981aca156502b24358e2ac03d5f0aaf8157a1abb155d82ae835702ab8055b86adc156c1ab415569ea7235380a9c054d0aa6815340a98154c02a60152c2a877d428aa1415062a83054182a0454f66a77253a0e9c474dc3a6b1d30aa968f4ae3a503d280294014a00a4d1d268293034923a3f551f828fc147e0a3c1d1e028ec34722a39051c068e0146e1a341d152a8a814540a2a05138e89c144c1a2415120288c34422a21051006880143e1a1f050f0686c7422a9ff94ff827f833f069f804fb867c4d3e019ef0cf7067b813d639eb04f5827ac13d609ea0cf5027a813d219e04cf00278013bc29de04ef0277053a4a9d204e88672cd39609ca0ce21a6e1936c29b604db026d8136c09b12cd8826c4135e29af04d7826b4535059a51cd10e6691334099a04cd02668132a599314c88a63c531e098f04c78263c131079870cc38261c130c19831cc106608130409810cbf0e5d912e8297404ba025c472e2097104b8825b872d069670cb09a55972ac095604ab0255812a2594f14a68a52c5296094b04a58252c128879430ca18250c1284193f1c9f064f8127c093d0c9d0e4c9126029300498024b4725a092d0496824a8724869230c8e9a449722409110c859a42c1214190434818640832021901047f8a3fc11fe08fc1c7e023f011f808fc047d863ec11f608fa0c78a63c411e208ef1472aa39411c818e404718638451c208df146f8237451ac78d6046a8634c51a608d20c690234431a208d1046882344119478c434620230c318228c1046006300117e18bf045f822fc117e08b83c591a2c8116218b10458822c0315c28ae04568629cd14e08a60c5302294314a08a314518228831386890644802238511c088c1446022301118088c04439621c110e088514401620010fe187f043f821fc10fe087a2c3b121d810ea1875043a821d410ea08702c36121b010d618681c340219c30c8385c442e0217010b8085c042b9615450a628520c2902144309c384e04260a1301098084c042602114f088184404220210c30803838441c020dc306a2835041a060d0106618330419820cc1066082c3c131a098104a1825041282094104a08202c0e120701038081a140d02060502e18160c0a86054102818130c098204c101688062c020a010100808011c00820040ffe27ff03ff81ffc0ff837f633fa85fd40fe817f403f985fb4cfc4b7e203f101f880fc407dd2bed89f644fb017d803eb85f506fa807d213e901f480fa407d203e59df282f9407ca03e485f186f7c87be03de85eec4f7607ba0bdd01ee42f7207b903dc81ee40f6477ac33d601eac2f5607ab03d581eac0f4c57a223d101e880f4027a003cf09e742f38179b0bcd81e682f32179903cc81e450f18578a13c501e280f0e378703c381e144f0a078503c281e086ef8677b0bbd81de82ef407790bb999da16ed007670bb381d9c0ecc176603b301d84aeba475d03ad89d6c0eb4175a03ac09d600eb0075803ac01d44eea2075103a789d116e8807430ba181d0c0e84174203a101cf4ae724739039b89cdc0e6c1736039a85cc86e640730139801cc00e60072f0b9781cbc0e507728039401c984e36b71b038c0dc600e300716138b01c504e2807130b8905c442e1a470b138505c204e100708038309c180e0a17002b7f85bf82dfa16fc0b7e01bec2df606f9137c05be00dee16f7037b81bb54dda06ed037589b7d8dbe06db236d81b6c0dae46d60b6b01b542daa06d5036a81b40ada006d0036801b400d9846c6336285b140d8816c4036201b084d7866bc035d85aec0d7606b9135c05ac8cd4cc6a6035285a7ccd3e069e0b4c19a5c2d2c16950b4a81a4c4d260691134881a440d22068e1b4701a380d1c068e034685a340d1a068c0b41a59e54cf206780b3c019dc2cea26750339899cc0ce2266a3b35019a42cce26670333059980cca16650332819940cca065e3b2c199600cae1655132a819502ca806530b298194c0ca6065303261d918cc8c06450b22819102c8426420320859040c80163e131f018f42c7a063c0b1d098e80c702638031b098bcec5e062e0b16098b00c56162913148189c4c4e062513110d8880c4216210310058800c3e161f030f818744c3a061d030e818740c2c761033080183c2c1a260d0306058284c1406081304018184c0636030301058080c0216010300058000c0005fe12ff017f80bfc05fe02fb9d7c4cbe205f00af7097b80bda15eb12f5817a44bd205e712f20d7900bc425e202f0097800bbe15df02ef057780bbc05dc12ee017700bb805dc02ea9d7350b9a05cc0ae6017300b9615c912e4817202b9005c802e3857144b8a05c40ae2017100b8615c112dd996ec0b7415ba02dc856e40b6e25b702db056d80b6a15b502d9896cc0b6415b202d8856c40b5e25a932ceb16740b36259b02cc896640b32059712cb8165c0b2e059702c915634ab1a058c0ac6016300b18058c02c39560c8b0605820ac1016080b04058202be955e48af2057712bb815d44ae4357202b8855c40ae2056f12b7815bc0ade056f02b5155988acc056412b2015884abe355f02af055780abc055c12ae015700ab8055c02ab9554c8aa6055112a88153c4a98354c02a5095280a90254802a4015184a8c054602a3015180a82553b329d814e82a7405390a9c814e40a70153612998d4cc0a6415320298854c40a6015300297094ac6a46852302918148c0a46051e2a8e094684a321519028c054546a2815140289854406a2005100287094380a1c050e02870141ce9fe84ff027f053f049f804fb0a7d813e829f404fa027d013e809e674ed3276813b029d804ec0276013b009ce54e322718138c09c224e1026f8937829ba14dc0a6e0136c29b414da026d01349099a54cd026605328499404c90a638931c098a24c5026189300698004bf0a5f812f8297c04bd0a5e812f4097624bb025d812ec097604b43a57192b8095824ac02550929c694e04a60a5301298094824a40252012900948049f2a4d9126c09322499024b8925069280492124901240491a348d02468122c4916048b02448922409120487124381214490814830a4105208090214800a400120008f084732a39811c448e2046f12360d1b008d4246a02340919468ca046502310d18808c21461022f0d17808bc045c122e0117008b424590a2c0515c28ac1456022a8515028a80454022621114e886244302218110068800440021f090f8087c043e021d8d0ec08760439121c810e4087204380a1a8d0bcc85c142e0216850b40858142c0215850ac0854142a0214850a40850142802128d07cc828b414020a010500828040f2a068902c4814140a020485018680a14050202050046802040101ff88ffc07fe03ff01ff80fe0e7e083f001f784fb447da03ec09f600fac27d603eb01f580fac07c873de31ef00f7427ba03dd01ee80f7407b053d421ea00f5007a423d201e808f3c279c13cd09e680f30279613cb01e580f0d077c53be01de84eec477603ba09dc08ee0076c23b601da08ec4676203b009d800ebc275e03ae09d700eb8075823ac01d600eb0075803a539cf98e7c073a239d01cd88e606730039709cb80e5c072a239501ca80e54072a039029c610e300714238a01c408e14670a038311c180e0446fc337e01bf00df046f8037c01bd08de806f4037811bc00dd846ea137409b984dcc06e4137109b880dc406d2836429b200d8846c4036011ae8cd7406b6235b01ac88d5866ac035601a98cd4c06a4135201a78cd3c069e034d11a680d340696234a09a484d20268e134701a304d14268a0345019ea0cd8e6682334019a00cc466620331019788cbc065e032f01960ccb00658032a119500ca80654032909930cc80c63e131f018f04c78063a131d018e04c700636131b018d04c6806321319018b0cc40c60ab305018204c1006080303098180c0c05fc52fa217d00be045f002f7097b80bd445ea02f5017988bcc05e602f3017980bb0e5c2b2e1017004b8005c002df096f80b7c05b452d6216b00b5045a802d3096980b48259e32cf016688b34059a02cb116580b2c059602ca096500b28058672b8595c00ad4656a02b5015988acc056222b1015804abc255c12aa215408a9c254a22a5015188a8c054602a1115080a802540029b294d04a6425301297094b80a58252c0294114984a4c05241292014900a2144f8c27c013d849e444f20278093b089d804e822740139089bc64de026d1136809ac44d6026a0935009a424d2026901338899c04ce0267013380980e4b08258012b0895804a8225119288093c449e024d1126809340496224b01258092c04960246292018900047c223e011e088e464720237111b808d4446432320119008bc645e022e0917008ac6456022b0114888a404520227111304894244812230911808882442122101108086504247212010808840041c220b1905808244412020711020c81004080201190080800240001fd18fe807f403f621fb00fd807e443f011f708fb047d423ea01f408f9847cc03e601eb40f21c79003c041e000f00077083b611db00ed0476803b401da00ea9475403aa01d500ea8074483a201d100e880740239a31cd00e680734039811c918e198708238401c108e080704037e21bf00df806f8237821bc00de006ec237221b900dc046e0036e11b700da0c6b8c35c01ad08d6806b4035621aa08d5006a4235201a710d380698234c01a410d20068c234601a208d10067c6332618d60c6806302318018c00c58462c0316018628c1106080300218000bf845fc02fa217d00be805ec42f6017b00bd805ec02e8716958b4805a022d0016800b38459c02ce016228af1057802b8215c00ad8456c02b4115718ab8055442aa015500a98854c02a6015300a90454802a4014b38a02c500027a313d009e804ec42760139109c804e0226e11360899104c0425e112d1096804ac4256012b0094884a40250112800919448822421120088f8447c023c111e008e0846c2236011a088d004680220a10460820040c220221010080043f841fc00fc107e003e841ee30f7007a883d401e620f30079043c801e210f10078803bc41de00ef0077803bc01d070e040700037841bc00dc106c8c36401ae20d7006a8835401aa00d310698034c01a600d3006714320c19000c6106300310418230c1005f882fc017a20ba185d002e8016e30b7005b042d8016630b30059802c4416200b10057882b8215a10ac0855842ac015410a90854802a40142809a384d002604130009610498c24c012220910047882306118008c00448c2240110108800428c214010a008310418020c01022080083f841f820fa107d003e041ec20f6007b0039a01b0e0d800682034001a000c8406308318018820c40062003100174a0ba005d002e8017400b24059002c8016400b01055182a8015400aa005408288c12cc094104a0024841240092004710238011c008c1044102200110008610411020801002080003f081f800f0606c6036001a840d4006a00331019040c8006210310017880bc005c102e0016080b00056102b0015040a8004e3021300ab000680001 0xad448d1482322804fbe355d3c8eeda93bac648d7883b44408c86813eea9c7bd26bd3a8e7b9171ef25aeda139ac248fb5071ef01ad7803944008c85813df096f3f15babe48e7685b43c08c84813b6652577849ee05c7b4071eeb1f7ba246ede5c6d814bece1c57604b20e04f4b3495d6127b895cee0d5bb6956edc973b6a71eca1c7b947dededc74934bed851bb20715d012d0e033d22d26d4249ed2173b4356ec415bb305ceca95bb0056ec6973b095cec49c7b0171ed51f7b3b71d1ad2fb2271b4892eaaa33ebe11bbbb6feecdb795365eaad5f92345ee698f7ba5bd188efb5963cfa56ed193baa848faf0639d816d6f83b42608c7f013aa448d088231f804fae455d8492f0214ba9648dde84b41408c7a813ea89c7ad25bd82927a8971eb256f01949a9248fa4871eb016dde04941008c79813dea9af3d96ba8e48e7506b40c08c78813e46d12a212340608c77013c04565dd859e9e5c7a3871ea95f7a9a56e9c5c6ff95be8c1c5dc05b1d804f5d35976e167a816ce9ed9ba6166e9a9b3a6271e881c7a8d7de9cdc75b35be9655ba187176816d00833d6ad66fba59e901b3a3b66e8219ba286ce8899b9f866e849b3a016ce829c79f971e935f7a3371d62d6fa1a71be696e9c233e7c15babc6fead1b795465eab15f91346ea498f7a25bd6092fa5163cf456ef914ba6e48f9e8639d216dd584b3ec08c70813e74a137827ce6e6133a17ce682127087cde69ef90a61e7692f9ca43cf25ef8c961e7052f9b143a6a48e7407be181879a84be6610cfa0231be04f98159e5c16798359e5a16797359e5a96798a4be5e52e99123e5812cf88231b804f94d6da6048cf78231b404e971233da08c6c013e30547858511ae04f90251e14144f6023e3e9478b951a5848f94c6ce3c98794248e2c58793948a5648f84861e4c120f50231aa04f91b56de496f3c15ba5448e7385b3d208c6a013a5248cf40231a604f91b56de296f3b95ba5048e7305b3ce08c69013e389d390158e3e1638ec6ee395838a151e0e14790e7ae3d9cb8da76cea5ef16173e265867207b8461cf830611a004f8c358e225d38b858e2a5f38a376e1e5db8946ee209f388d60e1e94782051e339eb8b672dc6def67b73e26d87871769c41ee10873e06184f2833e16d6385258e021d38407ce0eddb7f876e0a1f382276dfa1db8146ee009f37f17ce035837fa51dfa5478667ae139cb7037bd98dcf83361ccc9ef11273e0698688a33df81db9956be575ab95566e4b58f92466e44d9b6fa6bd9698f8d253cca5af10963e1a54e881239a81ae0c063df614ce782317404f7ca74df11f779455db491ad014b5b812c5b813dec9937ad7dde315b6ea56bde56dd405b16804f7827cddc97376a5cde19eb72961dc418775818dd00b377466ddad9b3196bdd856f751539a41af7485bdce14c59013dcadf372134dc4df370834de79ef79576de31db77a6edcc9b33017bdc658e6787bdc018c57813dbd5c36eb67cbc5aecf13b99a1ad6d03b15a04f6dc70db559f2e16bbda56e6586b74c16c55813def59f7a467dbf15f6e256db291b2d96bbca56ecb14b9941adcf05b5a412c4f013da258767061dac56f6a953da816f6985313804f68b7cda04d36737cd9a0d36ba6eda49b367963d9818c4c813b284ed6803b12e04ef195b73816c4a813d9715f65256d9291aee95bb1c52dcb05b59412c46013d8e56f63153d8a16f6205311404f61a6410e04f5d171d6a1c75c971d681c75f96bd7c58f2c95bd7a1af5e06399016c42813d704d35c57cd75a335cb8cd6e4d359834d675f35ae8cd68e3359034d835fb6027ed769f35b173cb05af5887398e1ac41013d5c5c755871d5d1f756946d541c755c7dd549c754846d5edbf56163b164ef5406358e0ec3f8130fa04f5346acac5af0f96398a1ae0b0630f604f6146fd6119f53a66d4a91b2716bc3258ebf94b97a1ae0806357612c35013d4656f51153d4216f500530d004f4fa640ca04f4b171d221c74a971d201c74d96bd3458f2615bd321af4c06397616c31813d284d34a47cd2d6334ab8cd264d347834d1f1f348d8cd20e3347034d3b1fb4e27ed2e9f349173c965af468739741ac30013d145c743871d155f744956d0c1c743d7dd0c9c742856d171bf44163bb452f4206372612c2e8130b604f4156ac925af0b9639701ae070630b204f4f56fd1959f41a66d0295b2096bc2258ee715b9601ae0406370e16c24013cfe5d33f47dcf115725b4bc6c5195c04b3980cf3e164cf75f73bc56cb0d6f1f95670816ce4833ce85f33895cce05733997ccec4d33a67ace698734061cdc0a33583cce319b38366cc29af37a5bcda94e5706bcd816f3505338e08f3427ccce0933ce7bcf15db3bc76cc0def3ab63ce45bb3496c9561ef330633880cf32164cc499331b7ccc25f32f96cc6851b1e166cba57330567cbcd9b2e356c7659b191567021ad5a85bcb45d32cb8cca84d32b95ccaa9c32a467ca692f292479521ad5984bca20af28023cb15df2b356c6055b2793494c1ed5805bc9a5d32638cc8e4d32516cc909c323d67c8c96f22a579481adbf85bc880af21823c979df24b66c7259b211349421edbe06bc815c31ec60c7c9b31e246c749b31fb67c769af1ca3b93e1ad5703b38408f1bc70c6b1831a266c6697318a5cc6d59f1926bc6096e4e86b6f416ce0023cfb59f3d467ccb15f2db6bc9cd6f20b4bc7055b179469381adb685b54212cd9833c565f316934c5698712061c5296f14253c4e16f1305336208f1227cc4609316363c545bb1296cc4418cd7033c405730f24bc3a91d4f84bc380af0d823c3ed5b06156c344d14e05bc305b30b25bc2a95db585bc280af09823c2ed9b07966c244d1b406bc209b307a3b5340ecd6023c1a9730625b6cc16cd5023c4315f0cb5bc22d2f07156c16519ae85b52212cd0833c1296f04253c0e16f0305333e08f029643380cf01371bee1c700934c035f30168cbfc63300134bfc9c6fb071bf89aefda63be096efd06bbf218e4d05b33408efa824beb5f2fbe8cbeca32fa024c075faffb73bdedaefe97ebf05f2f98739321accb833be29d2f818cbd64d2f715cbd89c2f5c67bd492ef4a4792e1ad4784bbd00aef3823bdf5def6b56b7e55af313492c1ed4605bbc8572f124bbc291d4504bbc00aeef823bc6d5ade956bbc4d14385bbb85faed97cbae9e2ec868ba8992ebb7cba6982ea26cba6dd2ec26fbac9aeeaa67ba498e4a06b80c18ee882bba008eed376b8e5dae79349221ee01873b989c6e3071b991f6e5a46b8a1c6e4a7eb909f2e347db8adc6e2046b9adbee5263b8e8eee18635080ecca02332408ee025cb7c972e0c6ab7e9aedea6391e1ae0086332008f0246fbe519ef2b6bbbad8ee734bb8459ade1469041adfc0634e412cbf833b7496edca53b7016edb8532fa08edb1642f40ced9b71b501c6d9134b651f2d9d8cb5e632d8934b5e9c6d3871b5a9aed6263b4296ed586bb5418e4005b2f008ed3024b4d1f2d458cb4ea32d2824b691fad8373b40daed717eb525f2d20738fe1acba833b449d2d098cb384d2cf96cb3a9c2ce567b3696ecd2578fa1adad85bb320aecc023b419decf366ae059acb9348f81edac06bb2a5b2c9a5bb2495dab05bb220aec8023b28d9ab7166b1e4d1a986bb1a5fac617cb109e2c5068b0a992c437cb08982c2a6cb08dd2c4a6fb0e9aec3267b0698e3d06b7ec18ec102bb0208ec5b76af05dac01348ee1edf9873afa9c6bb871afb5f6be256aec1c6bd27eaf29f2bbd7daecdc6ba856afd1bebda63af092eba0636a012cb90232e008eb8a6cade9b2b956aae09aeb72638ea1adf88632dc08edad6fb4759ecb36bb1cd8ebfb5bae659ab69568d01adf406367c16cae833ad65b2b4060ad2d7eb3b57acc16eb28534e00eeb5465ac85927a9464da12eaf18cac45d2b0174abcdf6ab871ab8dbeadb67a8ad5ead06bab218e3305b4d60eeaba8caac092b0c7fabf1f698475a8919e95455aba5faac17c9e451aaa8738ca1ad3404baa65f2a8070aa317ea7c57a9c16ea685367812ea9565a985927d95667216ea198ca94592a4164a8d9e294c54a8a6329f17ca871f69d071a7f9f2a0c6fa8119e9f457a7a1ae9e0638c616d9b84ba74a329c824a935fea3d7da615d6a2567a5115aa117ea765f27c156a701ce3106b66816e9397ca105729b154a6855a99954a5d9f69897ca5e55284c60a4c5b29757ca4a5f296954a5816294c66a325728c14ca5319a8b95ca499d293048a4958293e7aa4b9ca8457aa475da89861a415e28ec64a419f28e560a3b1b28e674a361228c356a30d5a90d6fa3f5ae8f567a3558e8cc66a2ed9a3006b7cc18e8b05ba2a14e89a7ca240929ae7ba659ea98676a579ce95576a511da82176a445ba8a16c8ba1edf1873a2218e86b7da14d7687b55a061c686c7da1517686455a041c684d7ca131b28557ea115e683d72a0d5c682d70a075f68147da0215a80046a1d1be85b6fa08d1e7f86366212d3283b4c60ee7e5689f55ca7cd709fb5aa7db6f9f0d9e2d86b7c218d3083b9ed1a27a4729e71c19785b9eb5be795679e31aa2c86b7be18d9685bac75beaa567a971be9bc67a2115e7f1669ee55a781468981adeb06363816d2804b9dc1d276c7d9cf1565d34b8fe92e32a3386e11a758649d55f67345698ed6e4ca5b8c48ce250569c21f26e85c9b81727007c9ca0d26f87c9c609270e7a9c09866f9619b44a26b93c9bb19a6e3669a09ae6da5b9b294e5616b9b056e6b1538bc48e7467b9cf5da7347699edee723639569ee712638ba8ce6f06e9aa1b2698649a29926937c9a01f26706c86a11a2386699817267d6799ad9a65b5692c9ae3e25b88c19a198569921d26438c9860d26305c9889c261c6798492e60a4794e5ae3c14b9804ae5f92398f5de62b5694c9ee3ba5b86215a5f0349781d25db8c96c0d25c86c96e9c25b56796a96e5a2579445ae4915b9664ae591239759de5c3669429ee48a6b88819a5883495e1925696495c9f25607c9540f25413c9529125384494a0f25193c948912510449401b21784688219a4f05c95759e5346b94316e4fa6693a95a2006685a15a4d874934a32468249300f24ba449160924a83c9120d24993c9124d24a24492411244024920172471709184e2451389124d246c67916dae4434b90e52e4314790a4fe421339335de4b47b92316e47a5685615a418249021d24028c8e60923f03c8fa912388248f60f2378348f24f2379348f49123c0448dc0923b06c8e85c2391388e04e2379348e759e38b6b8dcd6e3695b8d855e3593f8d44ce3fe778f91ee3bc6b8ea99a1f0668d2092338748cca322b8248c81d231a8c8aa0922a06c8c21922a16c8be5923027c8bc1f2290248b81b21484687619a2d05c8b05c22b1708a85b2299608af59e2ac678a515e2895b8a055e2794b89c51e32e778c55de2ed678b699a2ca5687419a1385689a09225d7089118224a6c88e91a22a6c8851822196c88251a1f96c8791821e96c87651a2536788c9ae2223b8805ae1f13b87448e1c47086d1821aa668689721925c8611821796685c5721615c855182149668505721bd678669ae18a5b85a5ae1595b84e48e765679d319e6a457994dae5eb5b960d2e4e26b90496e3424b8988ce1c85684c11a1007c8480d20f87c8440921026183e5860ea5b83894e0d95b83454df2123846d8e10a637c68ce0f06e8321b20b85c82a92e0a2477e852e0992b82448e0b3567e696de58568220d20786c81a96e0625780856e0592b81448e073668069adea0668120d20383c7fe0d20293c7fe4d203244808111ff024804172001387fe4d1ff34b7fa52dfe1477f64fdfd13380716e00a56792159fc8247ee0f1f78347ea4f1f79347ec911fa0447dc091f906c7e04e1f79347dcd6df695b7d855df593f7d44cdf9c6b7e2999e90667d2091ef06c7ce191ef16c7ca591f327c7c81f1ee0247c41b1e384679e199f005c7bc5b1ee9607b915ded95b7b455dec94b7b051df1d677c2999efa5679c199e28567ae091eaa6c7a65b1e84607a25b1e79467a88ede913b79c48de625c794571e446078e599e315c79696de495b78a48e0c457820d6e0434b7f096df424b7ac8cde6856788119e125b78294de015b77e54d9d1236728cddf064776dc5dba717740d1dd57c777a31d988c7720d1db02476d5f1dbe8c764231da8247669c5d91717609add7a6375296dd716b75a58dc295b66a48dde57e770dcdd436b7689cdc226b6688cdd887e7581f1d5274752231d203474e171d2a7074919dd1a4b74491dc116b6b252dd092b74048dd457774cd59c0a7b6b096d8285673e0d1ce85c73692dcd2476a852dcc92b73048dce3566a696d8185672e0d1ca87e7281f1c82787245a1c6a64720df1c626071a9b1c63747229bdc7a6b71c99dc5a636fa5adb49637144adc4923726dd9be27b6d09cd8a8767100d1c317470a231bc0247064f1c10446ec091c003c6e80d1bf13c6e84d1bfa446fa111b98246f6171bc9706ee4e1ba9386e84d1bc4676ecdadb9b4b6e452db89476e04fdb79337095ddc0c7b6f916dbd256602159b70246d80f1b20346d44f1b21346d6911b48446c6091b385c6ca4e1b21346c6d2db114b6c251db013f6be4cdb445b6cc9597f8566bc091ae03c69c0d1ad13c69c4d1ada446b2111a68246ae0f1a58346aa4f1a59346ac911aa044694091a907e6a21f1a793869c4d1a61386964d1a4b6868e5e1a216468e9f1a19606885b1a1a7469adada53636905bda316b68a59da11636824fda01336b11eda9c736a09d98707667e0919e86c6561919d96c6565919e2746741d1950246521f19c0746525f19b17466ea319a88c64e0919987e6641f17d84666011197d7a6141d99705c6585a1959646525f19417064a5e19116464a9f1909606445b190a746551bd93c6764c5bd9216b64659d9016363e52d8f1476735fd9a5776629d996a566121d97c85663a0918d2716285c58d47d6329198997162e9f98b27c6291f589b716245198817e61e5f185c7061a5f98617c6145198db6f63098d8aa3b62258d8713b61248d7e92360c9718225c6045718015c5fc5117e4705fb5e97d9765f457183c6a60a9ad81a636025ad7f9635f248ddec6f75719dcf36b72cd8dc3b4b6da9adaea6367c92d8e2336101997c0465ec96d7aa535e856d799534dc48d36a335e419177b715d69c5770345dd1f177d8c5ce231768345d40917547c5d76317308c5d209173a715cc5c57226b5c698d6ea5b5c45ad7096357256d349235e11f9763735b8dad742735709ad342335ca1f97007c5bc9d16e88c5b00d16d86c5b29c16c5675ae96d6b25756c5ad4695b5aa4ad6a1235b99dd6d36656a9ed4626b472199698345a21b167a5b59c95d4415b59a4ad661235a0d9943a6b46e199658345921f96407c5889e1631685829916237c58098160a6c580dd162a6f5869ad6126757e98d5896b53a58d5f12b57a48d63b765609ed4e2734921d95e0345745d15c88c5580915b93c56c111550245680f1540345644f1541345669115884454e0915786c55a5c1559385524e15413455959d5536b54ed6d5315b54a55d5213f5464cd5c67756b1ed5846b55c9991a8665440915003c5300d14f13c5304d14fa4453a1114b8245361b14c9385304d14bb5b52c56d4a9575284fd499335391ad4d266466199490245200f14103451c4f14113451e911468445020914583c4fe0d14493c4fe4d1452445101113f02450c1f94287c5064e1411345004e13f9344fada13d9784f05913da7c4ee5813c16c4ee9d140b6b4fcd8d3e16f4f45ad3c9674ec58d3a93f4e84cd4647b50f1cd422764841d9398244e21b12f8644de5b12f9644e09d1370744bc0912e87c4d81d12e97c4d45d135a8c4d22312d8244ce1f93307c45e159320544c79e91f0764c41b1301684be5912e97c4b85c12c9784ac5912ca7c4aa5812b16c4aa9d12f56f4b759d2d16f4b05ad2b9674a858d2995b4a455d36e7f4d19dd32a764c29991e87645a1992882449c9c52417149d5f526a5648e5c525a7e4949f12457d48edc5231564885f92197c47f5c12097e4805f11f15649f1bd2626349292d2296348452d1e92346248d1d26c4709b11b16c4685b1191544615c118e7a45e5d91716c4775a91ca6b46e98d1a96b46658d169235e35bd6fd675a4dad65363576d6d50a6b52298d3925b4a08cd1e0664581591506c44e5811435f44cd5d1295b44854cbd93b453194bd24b446190950464362311087443e1d10d08c43a0910db7d4345c50c36f42ed9d0235742c5ad0a96339a56cbb13b4411fd0f47d3df1d501c673d31550e2733989acbaa4b4321f90a07c24e1190907c41e5c10845f41d15d0695b41854cce94b423594ce25b4161909f0564002310486440e19102e783d11510208c3f41f0ff88c4040910047d3fe5c4fde7c3fb1bcfe4673f515cfc96b3f058ce515b33052d0457f40d5f4f7d7540759cf3c564029cce4a6b32e96cff07e3ee1f09d8563c81f0aa85c3ea150f98563e4150f6e7d3e01f0f70543c61b0ab4603db5f0f62583c41f0f58543d1198ea85c3a8130f44663a6170ef87c3cc090f0e743c6520f0d603c99e8f16722ab5e8f05763be584ee5783b3190ee67c3b1580ecc6c3b19d0eb9483a8d58ea3563bb5bcedd6b3b559ceb5633ab198e9b6638a5acd79633a456ce89533e99ecf8e7a3df9d8f56733d35d8f3c763889ecd72733ca98ca88763bc1b8e806c39c5d0e688c37c090e5974394230de0243761b0e40643765b0e316438e9f0e287c372090e186c2481189c066382170df97037a5c0dd96c374580df56737919cdcc5737056cdb95736c52cda9473999dce4d7738959ce12663809589b866244158da0243521b0d90643525b0d81643629f0d787c34e090d686c2401189a066356170d496c350580d3c5734c56cd295734852cd194735d59cd62663549589986623c158d10243401b0c706433c5b0c716433e9d0ce87431a090c607c3361d0c617c3325d0cd28c330230c502432c1f8ca87c234118c98443255e8a4076322170c796831c590c617c3165c0c417830a590c427c308580c296c3089d0c6c6f31519cc496f30e5acc316730658cc114b30251cce57f32f5dcca276320958a3876230158c00242fc1b0b60642f85b0b61642fa9d0bd8742d6090b507c2f21d0b517c2ee5d0bc28c2ec230b40242e81f8b987c25e158b88542e19e8a18762de1b0b69682d8590b517c2d25c0b31782c6590b327c2c4580b196c2c49d0b5d6f2d159cb396f2ca5acb21672c258cb015b2be55cbd67f2eb9dcb92762dc998a107625a198af0242b4df4abb5d2b8d54a81712b51f4abc5d2b3154a79712ad5f0ab46c2af5f8aad792a95c8a9d712a55c0a857d29f1f4a715629a518a4c702965f8a517c290518a257028c5f8a297c286558adc6f2b0dbca8b4729858ca394b2844ec9893b27f5a09ed722795c09cc602745b09c14626b1809b16c268518991542615c098e7a25e5d89716c2815a89f36f276d9c9b96b26658c9693b2571a094c722511c08e15b24b1809216624657090c602405988f95c23a5108dc702395e88d1762325709556f24f59c9346a2445ac8f16323056d1156f42759d0546f3ed19ce7c573669acd0a632fe96caea4b2821989605622e1188a86c22498089b5f222d5c8825b21e94c3323b22919432b4b21c1900a84620c230860742141d08288c2100d08337d20a9c481b6f204d9c77b572029ac8026317096c30a3b2171fc84c7d1b51d4774671a915483b7316edac3034b2081f87f87c0241187e87c1f49c07dc5f1f315c7c25b1ee94c4424b1f959443b5b1ec190148561d62307a0641e4190786781a71507788c1ca1f07508c1da0d075c7d1d49c47367c1d11bc73c671cb15c7226b1c698c5aa5b10692c79d7f1e35f46d5751dd59c694561d8dcc5a36b104d6c7487e1c41f01305619e1f02005c1c01506f0561ba1506c67d1b61f06c85419c1b020c601b15f06bb5819a1f06b0541a71986005c17e13069c6617c1706507c1a20d06667419c9206656019f9e866e720815e865d7619498463d7818919063e7c1875806246c1879d06124817ed585fb561915bc6356b18b59c60d631811985f3661609ac4d26317a96c5e2531bf9ec6e67a1b59d86ae731a95d86947615edec4cb731a0d8c1e0761921b85d86c1729d05c08c1520d05b27416a2305383414c1b05986414c9b058a64164df05807c1480d05706c01e11811866158170552701509c05326c14a98054d6714f19c5245714696c5125714292c5024716f9dc5a57715f59c56b66156d581106601a1584f8341281b04e8641289b04da64138df04d07c1240d04c06c0161180f86612c1704a26c1269804945712296c4825711e92c4724713359c4bb6612ad580f066012158468341161b03c8641129b03ca64114dd0440740f00d03b87c10c1d03ba7c1089d042b8c1062303a8341021f84007c00a1183f0440fb5e8198760f81703d2680f29903ba7c0ec9c039a780e099039b7c0de9803826c0dedd03c46f0eb19c3a26f0e49ac38a670dc98c36a4b0d891c43d7f1055dc3fb760f6d5819076006158358340d21b02b8640ce9b02ba640d0dd0330740ac0d02a87c0c81d02aa7c0c49d031b8c0c2230298340be1f82f07c0341582e0540b79e8170760b41b02c2680ae9902aa7c0a89c028a7809c99028b7c09a9802726c09add02b56f0a759c2926f0a09ac27a6709898c25a5b09495c32e7f0c19dc2eb760b2d98168760301982483408adf42135d08ed541da7108b1f42145d0891541d2710835f020c6c0855f82057907f5c81f57107b5c01dd7d0751f41ca560709181a47006c9f81aa7c06691817d700629f81827c05c9582346f086dbc1e34706e98c1924b05a8ec0e23b0555a01457204f5c01246004a9b011a4604118010a6c03e9180ea540375c00e67a0349d80ca6c0575a814b6f04cd9c1126b03c98c0c23b02d1a00a4720271c003a5b02118007a6601c970064600169980525c0109100347000f5e802a760089700ad6f02559c08c6a01a9ac04a6300696c86d6f1fd59c7ac6f1c319c5d45713cdac463630d4d6c2434b0581980b85600411bbdc5febb15fadb5fe78d5f7d347db096f64253d4892f4023bc5c56f05153b7652eb613b9de48e1285b78614d7b84b4560ec8b02300204c0003f 17 5 11 11 6
def m_1022 : Nat := 0xffffffffffffffff
def s_1022 : List Nat := [0x5555555555555555, 0x3333333333333333, 0xf0f0f0f0f0f0f0f, 0xff00ff00ff00ff, 0xffff0000ffff, 0xffffffff]
def g_1022 : Nat := 0x151717571757577f
def bds_1022 : List (Nat × List Nat × Nat × Nat) := [(m_972, s_972, 8, g_972), (m_976, s_976, 8, g_976), (m_969, s_969, 8, g_969), (m_974, s_974, 7, g_974), (m_968, s_968, 8, g_968), (m_973, s_973, 8, g_973), (m_966, s_966, 8, g_966), (m_978, s_978, 7, g_978), (m_964, s_964, 7, g_964), (m_970, s_970, 7, g_970), (m_962, s_962, 9, g_962), (m_967, s_967, 9, g_967), (m_963, s_963, 8, g_963), (m_961, s_961, 7, g_961), (m_960, s_960, 8, g_960), (m_958, s_958, 6, g_958), (m_965, s_965, 9, g_965), (m_975, s_975, 9, g_975), (m_977, s_977, 8, g_977), (m_971, s_971, 9, g_971)]
theorem kn_1022 : KnownBin bds_1022 := by
  intro b hb
  simp only [bds_1022, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_972
  · exact lb_976
  · exact lb_969
  · exact lb_974
  · exact lb_968
  · exact lb_973
  · exact lb_966
  · exact lb_978
  · exact lb_964
  · exact lb_970
  · exact lb_962
  · exact lb_967
  · exact lb_963
  · exact lb_961
  · exact lb_960
  · exact lb_958
  · exact lb_965
  · exact lb_975
  · exact lb_977
  · exact lb_971
theorem sub_1022 : ∀ b ∈ bds_1022, m_1022 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1022, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_1022 : ∀ b ∈ bds_1022, canon b.1 g_1022 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1022, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1022 : dagCheckRootsF m_1022 g_1022 bds_1022 (dagRefF 1917 (dagTraceF m_1022 s_1022 11 f_1022) l_1022 0) s_1022 11 = true := by decide +kernel
def node_1022 : Nat → Bool := dagCheckNodeF m_1022 g_1022 bds_1022 1917 (dagTraceF m_1022 s_1022 11 f_1022) l_1022
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_0 : treeBlockF 0 32 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_1 : treeBlockF 32 64 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_2 : treeBlockF 64 96 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_3 : treeBlockF 96 128 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_4 : treeBlockF 128 160 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_5 : treeBlockF 160 192 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_6 : treeBlockF 192 224 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_7 : treeBlockF 224 256 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_8 : treeBlockF 256 288 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_9 : treeBlockF 288 320 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_10 : treeBlockF 320 352 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_11 : treeBlockF 352 384 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_12 : treeBlockF 384 416 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_13 : treeBlockF 416 448 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_14 : treeBlockF 448 480 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_15 : treeBlockF 480 512 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_16 : treeBlockF 512 544 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_17 : treeBlockF 544 576 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_18 : treeBlockF 576 608 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_19 : treeBlockF 608 640 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_20 : treeBlockF 640 672 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_21 : treeBlockF 672 704 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_22 : treeBlockF 704 736 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_23 : treeBlockF 736 768 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_24 : treeBlockF 768 800 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_25 : treeBlockF 800 832 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_26 : treeBlockF 832 864 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_27 : treeBlockF 864 896 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_28 : treeBlockF 896 928 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_29 : treeBlockF 928 960 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_30 : treeBlockF 960 992 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_31 : treeBlockF 992 1024 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_32 : treeBlockF 1024 1056 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_33 : treeBlockF 1056 1088 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_34 : treeBlockF 1088 1120 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_35 : treeBlockF 1120 1152 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_36 : treeBlockF 1152 1184 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_37 : treeBlockF 1184 1216 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_38 : treeBlockF 1216 1248 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_39 : treeBlockF 1248 1280 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_40 : treeBlockF 1280 1312 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_41 : treeBlockF 1312 1344 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_42 : treeBlockF 1344 1376 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_43 : treeBlockF 1376 1408 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_44 : treeBlockF 1408 1440 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_45 : treeBlockF 1440 1472 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_46 : treeBlockF 1472 1504 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_47 : treeBlockF 1504 1536 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_48 : treeBlockF 1536 1568 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_49 : treeBlockF 1568 1600 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_50 : treeBlockF 1600 1632 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_51 : treeBlockF 1632 1664 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_52 : treeBlockF 1664 1696 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_53 : treeBlockF 1696 1728 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_54 : treeBlockF 1728 1760 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_55 : treeBlockF 1760 1792 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_56 : treeBlockF 1792 1824 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_57 : treeBlockF 1824 1856 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_58 : treeBlockF 1856 1888 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_59 : treeBlockF 1888 1917 node_1022 = true := by decide +kernel
theorem nc_1022 : ∀ j, 0 ≤ j → j < 1917 → node_1022 j = true :=
  (joinChecks (joinChecks (joinChecks (joinChecks (joinChecks (certBlock nb_1022_0) (joinChecks (certBlock nb_1022_1) (certBlock nb_1022_2))) (joinChecks (joinChecks (certBlock nb_1022_3) (certBlock nb_1022_4)) (joinChecks (certBlock nb_1022_5) (certBlock nb_1022_6)))) (joinChecks (joinChecks (joinChecks (certBlock nb_1022_7) (certBlock nb_1022_8)) (joinChecks (certBlock nb_1022_9) (certBlock nb_1022_10))) (joinChecks (joinChecks (certBlock nb_1022_11) (certBlock nb_1022_12)) (joinChecks (certBlock nb_1022_13) (certBlock nb_1022_14))))) (joinChecks (joinChecks (joinChecks (certBlock nb_1022_15) (joinChecks (certBlock nb_1022_16) (certBlock nb_1022_17))) (joinChecks (joinChecks (certBlock nb_1022_18) (certBlock nb_1022_19)) (joinChecks (certBlock nb_1022_20) (certBlock nb_1022_21)))) (joinChecks (joinChecks (joinChecks (certBlock nb_1022_22) (certBlock nb_1022_23)) (joinChecks (certBlock nb_1022_24) (certBlock nb_1022_25))) (joinChecks (joinChecks (certBlock nb_1022_26) (certBlock nb_1022_27)) (joinChecks (certBlock nb_1022_28) (certBlock nb_1022_29)))))) (joinChecks (joinChecks (joinChecks (joinChecks (certBlock nb_1022_30) (joinChecks (certBlock nb_1022_31) (certBlock nb_1022_32))) (joinChecks (joinChecks (certBlock nb_1022_33) (certBlock nb_1022_34)) (joinChecks (certBlock nb_1022_35) (certBlock nb_1022_36)))) (joinChecks (joinChecks (joinChecks (certBlock nb_1022_37) (certBlock nb_1022_38)) (joinChecks (certBlock nb_1022_39) (certBlock nb_1022_40))) (joinChecks (joinChecks (certBlock nb_1022_41) (certBlock nb_1022_42)) (joinChecks (certBlock nb_1022_43) (certBlock nb_1022_44))))) (joinChecks (joinChecks (joinChecks (certBlock nb_1022_45) (joinChecks (certBlock nb_1022_46) (certBlock nb_1022_47))) (joinChecks (joinChecks (certBlock nb_1022_48) (certBlock nb_1022_49)) (joinChecks (certBlock nb_1022_50) (certBlock nb_1022_51)))) (joinChecks (joinChecks (joinChecks (certBlock nb_1022_52) (certBlock nb_1022_53)) (joinChecks (certBlock nb_1022_54) (certBlock nb_1022_55))) (joinChecks (joinChecks (certBlock nb_1022_56) (certBlock nb_1022_57)) (joinChecks (certBlock nb_1022_58) (certBlock nb_1022_59)))))))
theorem lb_1022 : LowerBin m_1022 s_1022 g_1022 12 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1022 sub_1022 gl_1022 rc_1022 nc_1022

def wg : List Gate :=
  [⟨GateOp.and, [1, 2]⟩,
    ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [3, 4]⟩,
    ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.and, [7, 9]⟩,
    ⟨GateOp.or, [5, 10]⟩,
    ⟨GateOp.and, [0, 11]⟩,
    ⟨GateOp.or, [6, 12]⟩,
    ⟨GateOp.and, [0, 7]⟩,
    ⟨GateOp.and, [5, 10]⟩,
    ⟨GateOp.or, [8, 14]⟩,
    ⟨GateOp.or, [15, 16]⟩,
    ⟨GateOp.and, [13, 17]⟩]

theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg
  simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) =
    Nat.testBit (3941132456 * 2 ^ 32 + 3903367296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

theorem root_lb : LowerBin fullMask rootStock (canon fullMask (3941132456 * 2 ^ 32 + 3903367296)) (13 - 1) := by
  exact lb_1022

end PEqualNP.Outside.L_meta_47395

theorem PEqualNP.Outside.L_meta_47395 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941132456 * 2 ^ 32 + 3903367296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941132456 * 2 ^ 32 + 3903367296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact PEqualNP.Outside.L_meta_47395.table2_from_lowerBin
    (3941132456 * 2 ^ 32 + 3903367296) 13 PEqualNP.Outside.L_meta_47395.root_lb
    PEqualNP.Outside.L_meta_47395.wg 18 rfl
    PEqualNP.Outside.L_meta_47395.wfits PEqualNP.Outside.L_meta_47395.weval
