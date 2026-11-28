import PEqualNP.Defs

-- Signed circuit checker and project bridge adapted from 37b04d9b0ae1c59cb15f8e7a11426fdd865d59b0,
-- lean/PEqualNP/Outside/L_meta_45112.lean. Packed states and cuts are for the table below.
namespace PEqualNP.Outside.L_meta_49089

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

def rootStock : List Nat := [0xffffffff, 0xffff0000ffff, 0xff00ff00ff00ff, 0xf0f0f0f0f0f0f0f, 0x3333333333333333, 0x5555555555555555]

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

def shardForest (data : Array Nat) (pBits tBits i : Nat) : Nat × Nat :=
  unpackForestF (data.getD (i >>> 6) 0) pBits tBits (i &&& 63)

def shardLinks (data : Array (Nat → Nat → Option Nat)) (p t : Nat) : Option Nat :=
  data.getD (p >>> 6) (fun _ _ => none) (p &&& 63) t


def m_3 : Nat := 0x2020202020202020

def s_3 : List Nat := [0x20202020, 0x202000002020, 0x20002000200020]

def g_3 : Nat := 0x2000202020

def b_3 : List (Nat × List Nat × Nat × Nat) := []

theorem known_3 : KnownBin b_3 := by
  intro b hb
  simp [b_3] at hb

theorem sub_3 : ∀ b ∈ b_3, m_3 &&& b.1 = b.1 := by
  intro b hb
  simp [b_3] at hb

theorem goal_3 : ∀ b ∈ b_3, canon b.1 g_3 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_3] at hb

def fd_3 : Array Nat := #[
  0x7
]

def F_3 := shardForest fd_3 1 3

def ld_3 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_3 := shardLinks ld_3

def st_3 := dagTraceF m_3 s_3 3 F_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_3 : dagCheckRootsF m_3 g_3 b_3 (dagRefF 1 st_3 L_3 0) s_3 3 = true := by
  decide +kernel

def ck_3 := dagCheckNodeF m_3 g_3 b_3 1 st_3 L_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_3_0 : treeBlockF 0 1 ck_3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_3 : ∀ j, 0 ≤ j → j < 1 → ck_3 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_3_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_3 : LowerBin m_3 s_3 g_3 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_3 sub_3 goal_3 rc_3 nc_3

def m_7 : Nat := 0x2200220022002200

def s_7 : List Nat := [0x22002200, 0x220000002200, 0x200020002000200]

def g_7 : Nat := 0x20002002200

def b_7 : List (Nat × List Nat × Nat × Nat) := []

theorem known_7 : KnownBin b_7 := by
  intro b hb
  simp [b_7] at hb

theorem sub_7 : ∀ b ∈ b_7, m_7 &&& b.1 = b.1 := by
  intro b hb
  simp [b_7] at hb

theorem goal_7 : ∀ b ∈ b_7, canon b.1 g_7 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_7] at hb

def fd_7 : Array Nat := #[
  0x7
]

def F_7 := shardForest fd_7 1 3

def ld_7 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_7 := shardLinks ld_7

def st_7 := dagTraceF m_7 s_7 3 F_7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_7 : dagCheckRootsF m_7 g_7 b_7 (dagRefF 1 st_7 L_7 0) s_7 3 = true := by
  decide +kernel

def ck_7 := dagCheckNodeF m_7 g_7 b_7 1 st_7 L_7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_7_0 : treeBlockF 0 1 ck_7 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_7 : ∀ j, 0 ≤ j → j < 1 → ck_7 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_7_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_7 : LowerBin m_7 s_7 g_7 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_7 sub_7 goal_7 rc_7 nc_7

def m_11 : Nat := 0x2222000022220000

def s_11 : List Nat := [0x22220000, 0x22000000220000, 0x202000002020000]

def g_11 : Nat := 0x2000002220000

def b_11 : List (Nat × List Nat × Nat × Nat) := []

theorem known_11 : KnownBin b_11 := by
  intro b hb
  simp [b_11] at hb

theorem sub_11 : ∀ b ∈ b_11, m_11 &&& b.1 = b.1 := by
  intro b hb
  simp [b_11] at hb

theorem goal_11 : ∀ b ∈ b_11, canon b.1 g_11 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_11] at hb

def fd_11 : Array Nat := #[
  0x7
]

def F_11 := shardForest fd_11 1 3

def ld_11 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_11 := shardLinks ld_11

def st_11 := dagTraceF m_11 s_11 3 F_11

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_11 : dagCheckRootsF m_11 g_11 b_11 (dagRefF 1 st_11 L_11 0) s_11 3 = true := by
  decide +kernel

def ck_11 := dagCheckNodeF m_11 g_11 b_11 1 st_11 L_11

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_11_0 : treeBlockF 0 1 ck_11 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_11 : ∀ j, 0 ≤ j → j < 1 → ck_11 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_11_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_11 : LowerBin m_11 s_11 g_11 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_11 sub_11 goal_11 rc_11 nc_11

def m_15 : Nat := 0x2222222200000000

def s_15 : List Nat := [0x222200000000, 0x22002200000000, 0x202020200000000]

def g_15 : Nat := 0x2022200000000

def b_15 : List (Nat × List Nat × Nat × Nat) := []

theorem known_15 : KnownBin b_15 := by
  intro b hb
  simp [b_15] at hb

theorem sub_15 : ∀ b ∈ b_15, m_15 &&& b.1 = b.1 := by
  intro b hb
  simp [b_15] at hb

theorem goal_15 : ∀ b ∈ b_15, canon b.1 g_15 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_15] at hb

def fd_15 : Array Nat := #[
  0x7
]

def F_15 := shardForest fd_15 1 3

def ld_15 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_15 := shardLinks ld_15

def st_15 := dagTraceF m_15 s_15 3 F_15

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsF m_15 g_15 b_15 (dagRefF 1 st_15 L_15 0) s_15 3 = true := by
  decide +kernel

def ck_15 := dagCheckNodeF m_15 g_15 b_15 1 st_15 L_15

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_15_0 : treeBlockF 0 1 ck_15 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_15 : ∀ j, 0 ≤ j → j < 1 → ck_15 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_15_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_15 : LowerBin m_15 s_15 g_15 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_15 sub_15 goal_15 rc_15 nc_15

def m_77 : Nat := 0x2222222222222222

def s_77 : List Nat := [0x22222222, 0x222200002222, 0x22002200220022, 0x202020202020202]

def g_77 : Nat := 0x2022202222222

def b_77 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_7, s_7, 4, g_7), (m_11, s_11, 4, g_11), (m_15, s_15, 4, g_15)]

theorem known_77 : KnownBin b_77 := by
  intro b hb
  simp only [b_77, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_3
  · exact lb_7
  · exact lb_11
  · exact lb_15

theorem sub_77 : ∀ b ∈ b_77, m_77 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_77, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

theorem goal_77 : ∀ b ∈ b_77, canon b.1 g_77 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_77, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

def fd_77 : Array Nat := #[
  0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f
]

def F_77 := shardForest fd_77 6 10

def ld_77 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x8e11c1fc3f07c2f81b43606c0d45a0b40662cc15c2b0542a8148a18420841009f13e0784f01d12b0540a814128050098921222440809001e21e00b001 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d347d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 11 4 10 6 5
]

def L_77 := shardLinks ld_77

def st_77 := dagTraceF m_77 s_77 6 F_77

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_77 : dagCheckRootsF m_77 g_77 b_77 (dagRefF 43 st_77 L_77 0) s_77 6 = true := by
  decide +kernel

def ck_77 := dagCheckNodeF m_77 g_77 b_77 43 st_77 L_77

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_77_0 : treeBlockF 0 16 ck_77 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_77_16 : treeBlockF 16 32 ck_77 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_77_32 : treeBlockF 32 43 ck_77 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_77 : ∀ j, 0 ≤ j → j < 43 → ck_77 j = true :=
  (block_join (fun _ h1 h2 => treeBlockF_at nb_77_0 h1 h2) (block_join (fun _ h1 h2 => treeBlockF_at nb_77_16 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_77_32 h1 h2)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_77 : LowerBin m_77 s_77 g_77 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_77 sub_77 goal_77 rc_77 nc_77

def m_17 : Nat := 0xa000a000a000a00

def s_17 : List Nat := [0xa000a00, 0xa0000000a00, 0x200020002000200]

def g_17 : Nat := 0x20002000a00

def b_17 : List (Nat × List Nat × Nat × Nat) := []

theorem known_17 : KnownBin b_17 := by
  intro b hb
  simp [b_17] at hb

theorem sub_17 : ∀ b ∈ b_17, m_17 &&& b.1 = b.1 := by
  intro b hb
  simp [b_17] at hb

theorem goal_17 : ∀ b ∈ b_17, canon b.1 g_17 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_17] at hb

def fd_17 : Array Nat := #[
  0x7
]

def F_17 := shardForest fd_17 1 3

def ld_17 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_17 := shardLinks ld_17

def st_17 := dagTraceF m_17 s_17 3 F_17

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsF m_17 g_17 b_17 (dagRefF 1 st_17 L_17 0) s_17 3 = true := by
  decide +kernel

def ck_17 := dagCheckNodeF m_17 g_17 b_17 1 st_17 L_17

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_17_0 : treeBlockF 0 1 ck_17 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_17 : ∀ j, 0 ≤ j → j < 1 → ck_17 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_17_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_17 : LowerBin m_17 s_17 g_17 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_17 sub_17 goal_17 rc_17 nc_17

def m_25 : Nat := 0xaa000000aa00

def s_25 : List Nat := [0xaa00, 0xa0000000a00, 0x220000002200]

def g_25 : Nat := 0x20000002a00

def b_25 : List (Nat × List Nat × Nat × Nat) := []

theorem known_25 : KnownBin b_25 := by
  intro b hb
  simp [b_25] at hb

theorem sub_25 : ∀ b ∈ b_25, m_25 &&& b.1 = b.1 := by
  intro b hb
  simp [b_25] at hb

theorem goal_25 : ∀ b ∈ b_25, canon b.1 g_25 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_25] at hb

def fd_25 : Array Nat := #[
  0x7
]

def F_25 := shardForest fd_25 1 3

def ld_25 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_25 := shardLinks ld_25

def st_25 := dagTraceF m_25 s_25 3 F_25

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsF m_25 g_25 b_25 (dagRefF 1 st_25 L_25 0) s_25 3 = true := by
  decide +kernel

def ck_25 := dagCheckNodeF m_25 g_25 b_25 1 st_25 L_25

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_25_0 : treeBlockF 0 1 ck_25 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_25 : ∀ j, 0 ≤ j → j < 1 → ck_25 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_25_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_25 : LowerBin m_25 s_25 g_25 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_25 sub_25 goal_25 rc_25 nc_25

def m_29 : Nat := 0xaa00aa00

def s_29 : List Nat := [0xaa00, 0xa000a00, 0x22002200]

def g_29 : Nat := 0x2002a00

def b_29 : List (Nat × List Nat × Nat × Nat) := []

theorem known_29 : KnownBin b_29 := by
  intro b hb
  simp [b_29] at hb

theorem sub_29 : ∀ b ∈ b_29, m_29 &&& b.1 = b.1 := by
  intro b hb
  simp [b_29] at hb

theorem goal_29 : ∀ b ∈ b_29, canon b.1 g_29 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_29] at hb

def fd_29 : Array Nat := #[
  0x7
]

def F_29 := shardForest fd_29 1 3

def ld_29 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_29 := shardLinks ld_29

def st_29 := dagTraceF m_29 s_29 3 F_29

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsF m_29 g_29 b_29 (dagRefF 1 st_29 L_29 0) s_29 3 = true := by
  decide +kernel

def ck_29 := dagCheckNodeF m_29 g_29 b_29 1 st_29 L_29

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_29_0 : treeBlockF 0 1 ck_29 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_29 : ∀ j, 0 ≤ j → j < 1 → ck_29 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_29_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_29 : LowerBin m_29 s_29 g_29 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_29 sub_29 goal_29 rc_29 nc_29

def m_91 : Nat := 0xaa00aa00aa00aa00

def s_91 : List Nat := [0xaa00aa00, 0xaa000000aa00, 0xa000a000a000a00, 0x2200220022002200]

def g_91 : Nat := 0x20002002a00

def b_91 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7), (m_17, s_17, 4, g_17), (m_25, s_25, 4, g_25), (m_29, s_29, 4, g_29)]

theorem known_91 : KnownBin b_91 := by
  intro b hb
  simp only [b_91, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_7
  · exact lb_17
  · exact lb_25
  · exact lb_29

theorem sub_91 : ∀ b ∈ b_91, m_91 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_91, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

theorem goal_91 : ∀ b ∈ b_91, canon b.1 g_91 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_91, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

def fd_91 : Array Nat := #[
  0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f
]

def F_91 := shardForest fd_91 6 10

def ld_91 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x8e11c1fc3e17c0f81b43516a0d05a0340662cc15c2a1522a41482184027c4f81e13c0780e89d02b05049893024248088910220404801001e21e00b001 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b407c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 11 4 10 6 5
]

def L_91 := shardLinks ld_91

def st_91 := dagTraceF m_91 s_91 6 F_91

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_91 : dagCheckRootsF m_91 g_91 b_91 (dagRefF 43 st_91 L_91 0) s_91 6 = true := by
  decide +kernel

def ck_91 := dagCheckNodeF m_91 g_91 b_91 43 st_91 L_91

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_91_0 : treeBlockF 0 16 ck_91 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_91_16 : treeBlockF 16 32 ck_91 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_91_32 : treeBlockF 32 43 ck_91 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_91 : ∀ j, 0 ≤ j → j < 43 → ck_91 j = true :=
  (block_join (fun _ h1 h2 => treeBlockF_at nb_91_0 h1 h2) (block_join (fun _ h1 h2 => treeBlockF_at nb_91_16 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_91_32 h1 h2)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_91 : LowerBin m_91 s_91 g_91 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_91 sub_91 goal_91 rc_91 nc_91

def m_19 : Nat := 0xa0a00000a0a0000

def s_19 : List Nat := [0xa0a0000, 0xa0000000a0000, 0x202000002020000]

def g_19 : Nat := 0x20000020a0000

def b_19 : List (Nat × List Nat × Nat × Nat) := []

theorem known_19 : KnownBin b_19 := by
  intro b hb
  simp [b_19] at hb

theorem sub_19 : ∀ b ∈ b_19, m_19 &&& b.1 = b.1 := by
  intro b hb
  simp [b_19] at hb

theorem goal_19 : ∀ b ∈ b_19, canon b.1 g_19 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_19] at hb

def fd_19 : Array Nat := #[
  0x7
]

def F_19 := shardForest fd_19 1 3

def ld_19 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_19 := shardLinks ld_19

def st_19 := dagTraceF m_19 s_19 3 F_19

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsF m_19 g_19 b_19 (dagRefF 1 st_19 L_19 0) s_19 3 = true := by
  decide +kernel

def ck_19 := dagCheckNodeF m_19 g_19 b_19 1 st_19 L_19

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_19_0 : treeBlockF 0 1 ck_19 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_19 : ∀ j, 0 ≤ j → j < 1 → ck_19 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_19_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_19 : LowerBin m_19 s_19 g_19 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_19 sub_19 goal_19 rc_19 nc_19

def m_23 : Nat := 0xaa000000aa0000

def s_23 : List Nat := [0xaa0000, 0xa0000000a0000, 0x22000000220000]

def g_23 : Nat := 0x20000002a0000

def b_23 : List (Nat × List Nat × Nat × Nat) := []

theorem known_23 : KnownBin b_23 := by
  intro b hb
  simp [b_23] at hb

theorem sub_23 : ∀ b ∈ b_23, m_23 &&& b.1 = b.1 := by
  intro b hb
  simp [b_23] at hb

theorem goal_23 : ∀ b ∈ b_23, canon b.1 g_23 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_23] at hb

def fd_23 : Array Nat := #[
  0x7
]

def F_23 := shardForest fd_23 1 3

def ld_23 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_23 := shardLinks ld_23

def st_23 := dagTraceF m_23 s_23 3 F_23

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsF m_23 g_23 b_23 (dagRefF 1 st_23 L_23 0) s_23 3 = true := by
  decide +kernel

def ck_23 := dagCheckNodeF m_23 g_23 b_23 1 st_23 L_23

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_23_0 : treeBlockF 0 1 ck_23 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_23 : ∀ j, 0 ≤ j → j < 1 → ck_23 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_23_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_23 : LowerBin m_23 s_23 g_23 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_23 sub_23 goal_23 rc_23 nc_23

def m_33 : Nat := 0xaaaa0000

def s_33 : List Nat := [0xaa0000, 0xa0a0000, 0x22220000]

def g_33 : Nat := 0x22a0000

def b_33 : List (Nat × List Nat × Nat × Nat) := []

theorem known_33 : KnownBin b_33 := by
  intro b hb
  simp [b_33] at hb

theorem sub_33 : ∀ b ∈ b_33, m_33 &&& b.1 = b.1 := by
  intro b hb
  simp [b_33] at hb

theorem goal_33 : ∀ b ∈ b_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_33] at hb

def fd_33 : Array Nat := #[
  0x7
]

def F_33 := shardForest fd_33 1 3

def ld_33 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_33 := shardLinks ld_33

def st_33 := dagTraceF m_33 s_33 3 F_33

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsF m_33 g_33 b_33 (dagRefF 1 st_33 L_33 0) s_33 3 = true := by
  decide +kernel

def ck_33 := dagCheckNodeF m_33 g_33 b_33 1 st_33 L_33

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_33_0 : treeBlockF 0 1 ck_33 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_33 : ∀ j, 0 ≤ j → j < 1 → ck_33 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_33_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_33 : LowerBin m_33 s_33 g_33 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_33 sub_33 goal_33 rc_33 nc_33

def m_99 : Nat := 0xaaaa0000aaaa0000

def s_99 : List Nat := [0xaaaa0000, 0xaa000000aa0000, 0xa0a00000a0a0000, 0x2222000022220000]

def g_99 : Nat := 0x20000022a0000

def b_99 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11), (m_19, s_19, 4, g_19), (m_23, s_23, 4, g_23), (m_33, s_33, 4, g_33)]

theorem known_99 : KnownBin b_99 := by
  intro b hb
  simp only [b_99, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_11
  · exact lb_19
  · exact lb_23
  · exact lb_33

theorem sub_99 : ∀ b ∈ b_99, m_99 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_99, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

theorem goal_99 : ∀ b ∈ b_99, canon b.1 g_99 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_99, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

def fd_99 : Array Nat := #[
  0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f
]

def F_99 := shardForest fd_99 6 10

def ld_99 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x8e11c1fc3e17c0f81b43516a0d05a0340662cc15c2a1522a41482184027c4f81e13c0780e89d02b05049893024248088910220404801001e21e00b001 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b407c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 11 4 10 6 5
]

def L_99 := shardLinks ld_99

def st_99 := dagTraceF m_99 s_99 6 F_99

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_99 : dagCheckRootsF m_99 g_99 b_99 (dagRefF 43 st_99 L_99 0) s_99 6 = true := by
  decide +kernel

def ck_99 := dagCheckNodeF m_99 g_99 b_99 43 st_99 L_99

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_99_0 : treeBlockF 0 16 ck_99 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_99_16 : treeBlockF 16 32 ck_99 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_99_32 : treeBlockF 32 43 ck_99 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_99 : ∀ j, 0 ≤ j → j < 43 → ck_99 j = true :=
  (block_join (fun _ h1 h2 => treeBlockF_at nb_99_0 h1 h2) (block_join (fun _ h1 h2 => treeBlockF_at nb_99_16 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_99_32 h1 h2)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_99 : LowerBin m_99 s_99 g_99 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_99 sub_99 goal_99 rc_99 nc_99

def m_81 : Nat := 0xa0a0a0a0a0a0a0a

def s_81 : List Nat := [0xa0a0a0a, 0xa0a00000a0a, 0xa000a000a000a, 0x202020202020202]

def g_81 : Nat := 0x20202020a0a0a

def b_81 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 4, g_17)]

theorem known_81 : KnownBin b_81 := by
  intro b hb
  simp only [b_81, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_17

theorem sub_81 : ∀ b ∈ b_81, m_81 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_81, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

theorem goal_81 : ∀ b ∈ b_81, canon b.1 g_81 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_81, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

def F_81 : Nat → Nat × Nat := fun _ => (0, 0)

def L_81 : Nat → Nat → Option Nat := fun _ _ => none

def st_81 := dagTraceF m_81 s_81 4 F_81

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_81 : dagCheckRootsF m_81 g_81 b_81 (dagRefF 0 st_81 L_81 0) s_81 4 = true := by
  decide +kernel

def ck_81 := dagCheckNodeF m_81 g_81 b_81 0 st_81 L_81

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_81 : ∀ j, 0 ≤ j → j < 0 → ck_81 j = true :=
  fun _ _ h => absurd h (Nat.not_lt_zero _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_81 : LowerBin m_81 s_81 g_81 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_81 sub_81 goal_81 rc_81 nc_81

def m_83 : Nat := 0xa0a0a0a0a0a0a0a0

def s_83 : List Nat := [0xa0a0a0a0, 0xa0a00000a0a0, 0xa000a000a000a0, 0x2020202020202020]

def g_83 : Nat := 0x2000202020

def b_83 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]

theorem known_83 : KnownBin b_83 := by
  intro b hb
  simp only [b_83, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_3

theorem sub_83 : ∀ b ∈ b_83, m_83 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_83, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

theorem goal_83 : ∀ b ∈ b_83, canon b.1 g_83 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_83, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

def F_83 : Nat → Nat × Nat := fun _ => (0, 0)

def L_83 : Nat → Nat → Option Nat := fun _ _ => none

def st_83 := dagTraceF m_83 s_83 4 F_83

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_83 : dagCheckRootsF m_83 g_83 b_83 (dagRefF 0 st_83 L_83 0) s_83 4 = true := by
  decide +kernel

def ck_83 := dagCheckNodeF m_83 g_83 b_83 0 st_83 L_83

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_83 : ∀ j, 0 ≤ j → j < 0 → ck_83 j = true :=
  fun _ _ h => absurd h (Nat.not_lt_zero _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_83 : LowerBin m_83 s_83 g_83 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_83 sub_83 goal_83 rc_83 nc_83

def m_87 : Nat := 0xaa00aa00aa00aa

def s_87 : List Nat := [0xaa00aa, 0xaa000000aa, 0xa000a000a000a, 0x22002200220022]

def g_87 : Nat := 0x20022002a002a

def b_87 : List (Nat × List Nat × Nat × Nat) := [(m_23, s_23, 4, g_23)]

theorem known_87 : KnownBin b_87 := by
  intro b hb
  simp only [b_87, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_23

theorem sub_87 : ∀ b ∈ b_87, m_87 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_87, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

theorem goal_87 : ∀ b ∈ b_87, canon b.1 g_87 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_87, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

def F_87 : Nat → Nat × Nat := fun _ => (0, 0)

def L_87 : Nat → Nat → Option Nat := fun _ _ => none

def st_87 := dagTraceF m_87 s_87 4 F_87

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_87 : dagCheckRootsF m_87 g_87 b_87 (dagRefF 0 st_87 L_87 0) s_87 4 = true := by
  decide +kernel

def ck_87 := dagCheckNodeF m_87 g_87 b_87 0 st_87 L_87

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_87 : ∀ j, 0 ≤ j → j < 0 → ck_87 j = true :=
  fun _ _ h => absurd h (Nat.not_lt_zero _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_87 : LowerBin m_87 s_87 g_87 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_87 sub_87 goal_87 rc_87 nc_87

def m_95 : Nat := 0xaaaa0000aaaa

def s_95 : List Nat := [0xaaaa, 0xaa000000aa, 0xa0a00000a0a, 0x222200002222]

def g_95 : Nat := 0x22200002a2a

def b_95 : List (Nat × List Nat × Nat × Nat) := [(m_25, s_25, 4, g_25)]

theorem known_95 : KnownBin b_95 := by
  intro b hb
  simp only [b_95, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_25

theorem sub_95 : ∀ b ∈ b_95, m_95 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_95, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

theorem goal_95 : ∀ b ∈ b_95, canon b.1 g_95 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_95, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

def F_95 : Nat → Nat × Nat := fun _ => (0, 0)

def L_95 : Nat → Nat → Option Nat := fun _ _ => none

def st_95 := dagTraceF m_95 s_95 4 F_95

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_95 : dagCheckRootsF m_95 g_95 b_95 (dagRefF 0 st_95 L_95 0) s_95 4 = true := by
  decide +kernel

def ck_95 := dagCheckNodeF m_95 g_95 b_95 0 st_95 L_95

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_95 : ∀ j, 0 ≤ j → j < 0 → ck_95 j = true :=
  fun _ _ h => absurd h (Nat.not_lt_zero _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_95 : LowerBin m_95 s_95 g_95 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_95 sub_95 goal_95 rc_95 nc_95

def m_105 : Nat := 0xaaaaaaaa

def s_105 : List Nat := [0xaaaa, 0xaa00aa, 0xa0a0a0a, 0x22222222]

def g_105 : Nat := 0x22a2a2a

def b_105 : List (Nat × List Nat × Nat × Nat) := [(m_29, s_29, 4, g_29)]

theorem known_105 : KnownBin b_105 := by
  intro b hb
  simp only [b_105, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_29

theorem sub_105 : ∀ b ∈ b_105, m_105 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_105, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

theorem goal_105 : ∀ b ∈ b_105, canon b.1 g_105 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_105, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

def F_105 : Nat → Nat × Nat := fun _ => (0, 0)

def L_105 : Nat → Nat → Option Nat := fun _ _ => none

def st_105 := dagTraceF m_105 s_105 4 F_105

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_105 : dagCheckRootsF m_105 g_105 b_105 (dagRefF 0 st_105 L_105 0) s_105 4 = true := by
  decide +kernel

def ck_105 := dagCheckNodeF m_105 g_105 b_105 0 st_105 L_105

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_105 : ∀ j, 0 ≤ j → j < 0 → ck_105 j = true :=
  fun _ _ h => absurd h (Nat.not_lt_zero _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_105 : LowerBin m_105 s_105 g_105 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_105 sub_105 goal_105 rc_105 nc_105

def m_107 : Nat := 0xaaaaaaaa00000000

def s_107 : List Nat := [0xaaaa00000000, 0xaa00aa00000000, 0xa0a0a0a00000000, 0x2222222200000000]

def g_107 : Nat := 0x2022200000000

def b_107 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]

theorem known_107 : KnownBin b_107 := by
  intro b hb
  simp only [b_107, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_15

theorem sub_107 : ∀ b ∈ b_107, m_107 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_107, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

theorem goal_107 : ∀ b ∈ b_107, canon b.1 g_107 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_107, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

def F_107 : Nat → Nat × Nat := fun _ => (0, 0)

def L_107 : Nat → Nat → Option Nat := fun _ _ => none

def st_107 := dagTraceF m_107 s_107 4 F_107

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_107 : dagCheckRootsF m_107 g_107 b_107 (dagRefF 0 st_107 L_107 0) s_107 4 = true := by
  decide +kernel

def ck_107 := dagCheckNodeF m_107 g_107 b_107 0 st_107 L_107

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_107 : ∀ j, 0 ≤ j → j < 0 → ck_107 j = true :=
  fun _ _ h => absurd h (Nat.not_lt_zero _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_107 : LowerBin m_107 s_107 g_107 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_107 sub_107 goal_107 rc_107 nc_107

def m_189 : Nat := 0xaaaaaaaaaaaaaaaa

def s_189 : List Nat := [0xaaaaaaaa, 0xaaaa0000aaaa, 0xaa00aa00aa00aa, 0xa0a0a0a0a0a0a0a, 0x2222222222222222]

def g_189 : Nat := 0x20222022a2a2a

def b_189 : List (Nat × List Nat × Nat × Nat) := [(m_77, s_77, 7, g_77), (m_91, s_91, 7, g_91), (m_99, s_99, 7, g_99), (m_81, s_81, 5, g_81), (m_83, s_83, 5, g_83), (m_87, s_87, 5, g_87), (m_95, s_95, 5, g_95), (m_105, s_105, 5, g_105), (m_107, s_107, 5, g_107), (m_3, s_3, 4, g_3), (m_7, s_7, 4, g_7), (m_11, s_11, 4, g_11), (m_15, s_15, 4, g_15), (m_17, s_17, 4, g_17), (m_19, s_19, 4, g_19), (m_23, s_23, 4, g_23), (m_25, s_25, 4, g_25), (m_29, s_29, 4, g_29), (m_33, s_33, 4, g_33)]

theorem known_189 : KnownBin b_189 := by
  intro b hb
  simp only [b_189, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_77
  · exact lb_91
  · exact lb_99
  · exact lb_81
  · exact lb_83
  · exact lb_87
  · exact lb_95
  · exact lb_105
  · exact lb_107
  · exact lb_3
  · exact lb_7
  · exact lb_11
  · exact lb_15
  · exact lb_17
  · exact lb_19
  · exact lb_23
  · exact lb_25
  · exact lb_29
  · exact lb_33

theorem sub_189 : ∀ b ∈ b_189, m_189 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_189, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem goal_189 : ∀ b ∈ b_189, canon b.1 g_189 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_189, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def fd_189 : Array Nat := #[
  0xf62907b1403d498012460d2b706958839ac01a3620dd300685b8352781a162009218049082f8be180480be298048e81e8be153480ac1e0541201e8a613c5d09e2883cd482149e10a4b085238440a0214860f350079a403cd000246c05c5f065a40325201909005c5302d2f0291481529c0a14002d23024d200d8a207c5003ca001a9180d2520595202c180044d8076b40425801c2f00414c050780104b008218040640102e0001f,
  0x1d1250e8924744903e24c1d1230e8518792883a04a1dc170e8120750683a04600a298e4920718b20135f1be37004d3c6d490355621acaf0d49400268e0125e19ab08cc578024a631246188250c41184d8a23046c135a78b95805c2b82e150135a38b55804d29e2c25c134a58ab180556b82694714ca60a09505128828144134a189a4ec4d26e012520092708b58848ac02415c115b108c980452dc0124b10ca3083148412bc0124a,
  0x2f92f17c948bd6a04e9472e62f974120b98a64e93d29a2f968d20b44905a04829a29964d20b08a25812e2992914c578a88a4564502a0a9152538a928454140298a314c0c09d24a5145a28dac1441789d0a65004c2742593a10c9d0520082720e2f9325189908c41c5325e2c906d7c958dc41b4f24eb1106d1c834bc4723f23e3011c8dc830bc4185220c27106128898a44184620c211060e8848be4245320c1b00206c814b20145f,
  0x3fc9a1fc1189d8a64eb5e3eab09f49789d6a67b3463d8251ec118e78a27a56039d279e4d70e749677c603bcae1ce91ced498753543ad221d4490e74867392f39c9393ad489d69c6fd6238ab01c4970df8c47036037d3713ad2cdd48c6dc5236d2f13ad28d78a46bc5035ca613ad18ceadc6756234eb019d188d16c06726e33d2619c9889d6864eb4232da41951649d2be6346e31e3618cd889d29e623482f6b1183580c14b85eb62,
  0x4fda027c4953d2a8930374eda924c0d92c6949bc604dc26258d192c48c97a3a4c9a8264d012f46c983404bc9b2585512d2689604649813a549492604c9301e49ca224c0740106686c5f488a32441190d8a686b5e47e2ca1a97d1d8dc86a4f46eb121a91d1727e8c46045c9ba1a1790d0a48684e434252251490d08c8684243a2fa1d14d0d04c0082b42dac93b17cfe6947f3493f9a420c530fe68c7f24640d221fc1290107c7f048,
  0x5f89fafc4dd5b684be14556d27af49155b29ebc3485a2292ecd21686bcb9c505cc122d0d4968682b724e5bc122dc90968680b62305a12f2d48c1682bcb403d56c93ab60fd6449eb224356c1f2b88fd5c46eae13f5709babad215d680ae12756c1ea4c5115928aa7a5d55d22a9e575506d8a8350541a42a09b1502d8a803c53c93a4c179498c0a60345262c29253149098a32375181a28c091260a49304e49826a7a9353d46a9f13d,
  0x6fd2aa4cd7d2668ede3554992fa4c91d97adcdc45865eb136c151978dcd95606ce283640d1978c4cbc596b9af35c0d5978b0cbc5165db732e9b9a88b0d445065ca7347179a38a4d1b5e68c1ab2e531a08b0d045065ca132e1399709acd45e66a29334d7997098cc06c65c2124c8dd94690ca03c64c93a4c57991068c6c606362c31a5318d098c5a3762ca224c549890b89314761c2624c519850989314556da72b6d0d7e47ebf237,
  0x7d6313eb145f58a0fab6e7d5373ea139f68a4fb35e7d92f3ec579f5098f3237798a7bcc539e629af7b607bda83dc49de60bcf30527ae293cc119e606cf302679d1bbcc07801076e245e71229bbe8fddf46eef93f77c9bb89149c46a6ee1557112fb88935d94aae215f710a6bacd21c8ac4ea458721b73a3581d14b8e4362721a8b9a979cd4a4e435072d203909b9c9480e416e71093b8814dc407ce20390041ba4d179c128893452,
  0x8fc1300210e146bd0a3528ecaac2897e396b90a2478511ac6c956142bf1a35c850a3c284d6228dd18354889b745b1b22d48911362889a4c5297a294a51134889d1c4449ba254711116e888194440c21424f0a05e87c2242814e1b6c10db4886c1e42a49e1506b0c04485413c2c1121502f0a0520041fbcd17a11088f345382da3c1691e0c46b0613582c233cd14a094aaf335f81daabcc97e058b0fad6280c2a3eb1ba00ac100034,
  0x9fd22c7e13e7c69d3e14d9c122cf2d3a7949b381459c5b04ed142716a938b489c52a4e255271079381278fc274ced766769b3656099da2cce9766749b3456099d22c7e11e3f08d2bc5a9892e4c4172578ad3056095dab4ae9365d8c12ba35969ac4b4952570bd2c24495c2b47e0de3f06d20b5a949ae4a4172416ad20b4a93a2c49c1324168d265609052b4951824148d23a5891caa48217a452892085690da84844d24108d1f827,
  0xafeb057454aba0bd5d05dae82e57414a3f68f5bb45adc22c7e93ea7ac35994aacca354f582a76bb58560a9caf55c116a72b956560a9ca954e17aa70bb5385ca9c2947e91e878c35113aa8da85444da878c150034a1e2d53b5829d0b943c56a6ab0534172876ad4bd60a5c2e50e95a958c14394ea4c1ad0e532918c143942a1c2750e1368d8a145246a2e2851451a870994405ca1c2147e8de3f0bb425609fdaacfed1681ac13fa55,
  0xbe62d5fc0a2f98a57e360be5b75f4d62f96bd7483fbdc2c5e717ef568979c53bcdaf5d20f6eb8c575c5abae295dcd82eb0dd76358bac2f5d20cee906200927b35a4d9ad16cd48b72135b351fdc1166e029b70042b351bd9a516dd46b6693fb662cdb2936d908566937b5da459d166ce6b36a458b39a55a5182ce68d67246b38a359c0cacd24e0084fb2922d941163f69f5d561b18a558c51abaac15d25db0eb057457ac108b5d15c,
  0xccc17e7c4f3330579db58ceda866609f384819c02ccd09a668173350499a054ccc11dd2d4ae969d95562cbab065c9732a8c596360ca9376540a6e969793a46c9c24e4b14b254bd74b4ac722963e0ff1f0778f837c7c19e391431c0998e040ba5a36235bb11ac58c560c463162cd83114dd89a4cc4c1462298b1105374b43ba5a15d297b0d27d85c52c2d185d291b0926d7495ec1c9f60914b044618215eba4a36040a2f98c580028,
  0xdaa296fc0e76a6a7be05cdec2ced497f6a49bb513eddc1c6e958b758c1ba46eda827ee117b71071b8353da826ed958b6d8c1b606eda821ed41040126fb3359d9c266cc166e98bfadb4ad6da4eb6d2361099adb46d6d236bc4d35b28dae04cd6c24dd314ee96bdab561d592f6ac0a6e96a7a8b46d4d1a6a251b5109399c51d3eb066693f4d6b999a4bd2230690173498a1a4050ccd23e8a93345081a0b54d04146849134104999a43,
  0xee01df7c533b806fde03cee4a27740d3b9049dc033e962976c0e7a56a7d2a3ee94a6f640e3afac5d8460ebe3774a13fab8bdd6038eada9f4a137a7ac5d4460e9c3774a10fa508200a37e69a4f34d179a48bcd23fe691bf38d3f9d0b9ce347e6824f341140129fc835ee41a972c167904bfc8235e40af7200e7916a5c80350049fed517b8d073b5453e011ff008df8007fc414ce001df0c9338006fc203ce04a27040d381069c0033,
  0x7de917ef28bf7849fbc22802d3fd66bbf594dfac26fac8dfd646bf324df991afcc137d626feb135f8ca67bcd17e1299ef245f781b7bc09bd6077eb039f6126fb08d7d829bec135f581bfac0d401687e8349f41a2fa0517d0093e804500527f90d7bc86a5e425ef209af900e7c96a5e40350051ff4b17bc5073d2c53ee09ff704dfb807fe014c
]

def F_189 := shardForest fd_189 10 11

def ld_189 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0xd60d60d03d00ce1ce0ca2ca0c81c80c61bc5bc0bc0bc0ba1b62b41b40b40b02aa3aa0a81a42a40a40a40a40a219a49a09a08e68e08c18c08c08448408028007c27637607417407407027006a36a05e65c15c05a1562560541540540296033001 0x7f1483e8a01ea4c0e5b0073580372d81ba600d49e0775b83aac41c3620d8b70685883009018c5f0be29850d80226a01583c09db0058d202a090110480a22e84f1442205012a4f0912584691c2148616c5f0a62984cd48206a00fb48079a00245401b69008960068a4032120102a007930054a701e508168a407152050a0024d20108a0079400462881c9180d2520e45f0622982e9781348c0615202c18010170084b004b5a01c2f00a0f0808be39c531c1af8dcd3c6968e3425e195298989484b49c2224b1012507891833486192420b91d03a8d80a26c0112e0182980812c0308601019fb9a7faad0fcf49fe3a3fe911bf3253f8f27fb4937ba093d9813e3e0870983f7941db860dd250668602b2701390406c0102e0001f 12 5 11 10 6,
  unpackLinksF 0xd80d61d60d22cc3cc0c82c80c04c00bc29b19a09819429218e28e08648417e37647607227016656606606605a65a05815615605414c44c04824614224204203c33c03823803613032e12e01aa1a01811801801231200e2083080061060003000 0x691b06ad307c498321601e41c0ea0d0634c03c9440c11d0548d81926c3b82e188b00ea0d0674c230a601292c8849603a4a23fa4a1f9248fa9207b48c1a2410bd1d0528d87a28c0c1361e0250ec1207408c392481c62c82e4d0604c037c6e17d310bc9806d4902e2400589a02a490144683595e170a90d95885b4c43525004c9a092da0396c02425819eb088ed68386a43315e0d0a90c89181146c2d15d158aa8c61286208c3046c0411a01e8d05eac007234174ae0b85405aac02c15814ca20b0970462d82b460155ae0a45005329828934144a20a4950372d828144035a20c31445f69e2db470311b0b253c572962a14713ca189c4ec4d26e24b60126b008c9b0482b8232600d52c095588476c42296e10ca3085148412bc04853 12 5 11 10 6,
  unpackLinksF 0xc41be3b64b60b60b41b02b00ae1ae0ae0a64a60a41a409e39e09a29a09629609609228c38c08067e17e07c17827807617607604b64814804804234204014003c23a13623603603603413023003003003002e12e02e02e02e02a20b00a0005000 0x1524d0bf4bc5f2522a09a187588c06c45eb5029c92174120bb8be5cc532c9a816cd20b14c05aa482d024164d20b18a2559462c097158540a9260564502a4a0154538a928456c522aca9150500b78be59c532bd2915c578a728c5303028c2e146d60a48b45105e2802621517cfd8a67e35e3e5a99ccd48e569c6f34b369a51acd18cd686663422751f19257cc529e5e1472e09e83a4d4a524a5085327c2593c10c9d05242836268a31321188406c4bc59256371201b88f0d849d622383711f1809047e472372262910b17c848a64dc5f2622992cd7c9469e493472452f0044948d0bc4605222c271141288808c438422181d1060d80204a40a590ed208628e82d46c0e136 12 5 11 10 6,
  unpackLinksF 0xc62a51a40a029e19459409409408868808428217e27e07e07837807427407216c36a16a056a5605415405404e34e04a24434404214203c33c03c03c03633603413403023002e12e02c12252202202011c21a11a01811421400c40a10a0024001 0x7b2603fc9a1f6d84f56c072359371ac1a8d45096948434941da420ad18ce682822462e49e8524d4b324a8104a400241fc118e38d069c60389ac1f7584e18b4694523e92f19c948f868c7a25d3c12a9624d4f70947b0463d2b01e4960ed4887935c381361e1180ec4807795c3b5261d6490eb48876354345361d4490b02887ac513cd279e292cee48e74a43318a798051caf26a7412f39c939c7180e3ac07036c3892e1c0d80cf6b072562386311be9b8dd48c6e45236d2f14814cd98a46c45035ca61a7180d3ac068a6c345b019e930d5adc6a56234a311a09b8ce4c465b4832a2c95c490c76c063c6c3223718cd88c26c0623482f9a015a490ac268615603052e17c940ab26855124 12 5 11 10 6,
  unpackLinksF 0xd81d23c85c80c61c41c21c20bc3b82b80b80b80b42b40b21ac3ac0aa1a05a009e19e09e09c163d6016006005a35a05a05815805425214e24e04e04c14824804804804804614604604604222302201851801801611601220c30c0082080004000 0x9fb405009ea624d53e24aa124d4d922a828d53d2a8960264eda9268551332a89c4604c4aa26e1312f2a8968344cda8264d01306809a23a4c51b25e4d92d2689cb4a4d9a326a9192e2a8960464a92924e511c28bce04526f9afb7ad1dbb4bedd2476591bb245798a2a4a194d498a531051d8628cc2145568a213c4dc0324ea705e514292881394309a8803a4f01ba740d887054958274a4132500792603a8782648ca32441190e04c8fc59476372321b9180d88dd6245c372311811927e8b93744a2921f17d0e8a69245f48629a40d791e4be8e24f4692393a4d5160bc8a852450272261291108c880422741a90c0a90d04c85b59355a09764f42d26a5b9252d49a99ed31062987c26040c1c1fe0d0f76c081a442e89e8544d4b424a8083e 12 5 11 10 6,
  unpackLinksF 0xb61596b0533a6140e804d39a1306604b1907202404808e2fe1f83e17c0f45e0b0c600c01802e25c0b81702e05c0b8161275396700c99902c6580b01602c0580b01061a6340680c11622c03a0700e010c2003104200800000 0x3028fd8046ebf93f5f89baee49d7529abe1455ac92aea9357a48ab49265d1a82f0d216e680bb3485bc982e91416e480b98245bc122d8d397049cb72425a8a727e0d55d05a990254c00aad88c16a460aeb405de292ead79726a4b8b415b5a02d6979692bcae04d5a01ea620d53e04a9781559527ac890d5e690aeb405891fac28dd6027eaf93757093b06d3982686beb425ed27af253d6724eb303f58c1f2b60f53d04e97017554a6ab25155224aaaa4d55d22aa2499556d8aa35054da42a49b1512d8a803c5612eaac5754f24ea60340ac1a29b1814b8b0a514c524262908dd47068a302449ca22805513e2a896824 11 4 11 10 5,
  unpackLinksF 0xc25c20be2b45b40b02b00a84a80a23a01a009a38e68a28a08a07e67a27627227207206e26e06e06e06e06266206205e25e05c15c05c05c05065004c21d81c01c01821421401211201201200a40a0062060041040021020001000000000000000 0x1b54badfa556ad1aaf6511580d8bd14455c2e36ad75bc6aad52365e4a22ac1b1a6298ce04c6d230371161a5298cd84c5d4a22aa1b1b60a8d98346ce2832214173088da560640b02e45514d0c0aa03c6c81a352571a12a0d7b5e654af31e549530bca58526b81ab50571a02a0b5944548362d2511510d8d4c586a22834d179a58a4d235e5402f294149a306ad0c58682282d05519c8bccdc52669af2a8d49940bcc68526603626e131b9adcdbd626d637363189b08b2d6c586b228b56db9aa4dcc996e630b12ce551a729cd114c67ca129e1b9480c4cf04e67426b321313608acb8425041aa6a09595690ca03c60da632649d91068c846063e2c31c5318d098c623762ca231217187098c284c 12 5 11 10 6,
  unpackLinksF 0x8b0458228312189044822411208904215e56f01770bb05d80ec07413985cc0e607113881c40e016e12bdd582aa1540a985482a214b325812828c446022850488204009e10ec27223809c00d086613209884b0a56129114049843c81e00e847020d60410200084002 0x3ee0f1f6078fcc527e1af3ded49f74bcfb15e812b14051b9ff8c4ff4517f6283f8db9fb4dcf706e7e8273ea131e703cc484461c1a30a111f06c0f7b507b893bd7149270609b84c79d1ba4e512128bd0845382a29410d7e064befa2377cca7be4539f129ae2145498a113e4dc0424ef685e7b0293d4119c408a8983a7a41b1140a9e804cf301e4980eb060c182080c0850600282fe1417e0a0f123f7851bbc04fddf26eea9275f4202f80c1d32baee15572892af60c17a060e9a5d7652ab9049979060bc040749b03acd21cd680bb8505d8203a916175060ba05074ab03a2971cd4a0b90405c4282e00c16e080e5b5e7392f39a949c92bcb68405b0183969016b060b5030725202d20c1d5ac4e9b6e741b139ed45cc6a0e526e720b72ce101274789381c7922f3c714dde8a4eeb53711a7250d35db4beed24d35922bb057dd729a1e14571c93b8c14dc509ca204d7141f3880e588066c303261018ab40c1b946ec194c6dd1bb825117c288ac86c 13 5 11 10 6,
  unpackLinksF 0xb99b61b60b60b03b00ae1ae0ae0a83a80a61a60a22a20a01a00a009849809809808e58e08c18c08a18a08a074b7407407217207207206c36826806616606415c42f72e02e02c12a12812802802421c41c01631601031000a30a0081080080004 0x164b4fae5a3d6c93ea648f43237a14aec3c53e1429ce3147628a11424dc0624f4285d9f827cde139ec095330479942328a109150752b0379541b1180aa4004f1f8268c493c5e5763b2ab131258e5ae45e976364ab121268d1ae45cd82296a1183548ba364529222d4890e86089daf45497a294a51295e8702944e8e22547118c6e79e2f45edba2c6c515b498a1a444c9ba242dd0d06288c194440c21f0890eb60871a44360f21804d0b0168602242c1121a24f0c83585c13c2a05e3d6bd1e352799a7286d363a4bf1c2473951ec6e8d6352bf1994712c9ec644d62124f1005e87829c28149f3096f904a7c424b8a11943082e28367a81ac221120d089060448351ac184d60f68f072478111bc1611a024bb04a557f11ac04d76076aafda368063040b161f909901854806b03e01b1ef07900034 12 5 11 10 6,
  unpackLinksF 0xaad542a8514a214426a4d09a12ca584b09612c22b405801002003e27c0f81f03c2654c0978af05e0b49682a3540a45392704e094928241354680c89903205c8b81702e0548a81232223c8780f01a4340608c016228405000 0x506d568268b402559fd22cb20da4604d3eb4e9f0a6cea5167324b3d34e9e526cea9167224d3b450531a64eed82756a93a3489cd2a4e4552710793da459e0a2ce049ca204e038179b2b04b00d268ac1228249b9aecc2d566d69b35b459a92eca29566949b33a4595c1b488099eb8a4c583096c2e4c6972620b930560968264b0112430492ec60908124b6d625a4a92c2449922d4c315a5f6ad2f24d93522cb88d6172bd2c85e95c2b48209a480b929b5c9482e49f1624e0992656091c2648a11243089254609081a490962472a92294490da84844d2546b528b56941a549ad1a4b4ad24a46854af48c17a440ad20846 11 4 11 10 5,
  unpackLinksF 0xf01f00f00ee1ec1cb1ca0ca0c43c02c00c00b46b21b20b01b00ae1ae0ac1ac0ac0aa1a818718228208208017087006a36816806236016005845615604e44e04c14c04634604414404404404214204013843803420d40c00c0082061060022001 0x15fd60a6892cc4172c8ac362d60b112ed389569946b6115eb00ae57c54abd0bd5e05daec2e4c2156ba0a54184d9ec264d61165f06b5c3459a42ad6e116b02d956160a611b56852ab328d4085d9a02ac98096790b958560ab822d595829724d2905cad6b0d65582b16bb4e355a591b55e57aad2b955952aa82f552176a80b928855a9c29500136780993384592c12d2a572912a151b50874af32054aa4275511369dc2f29a14a5d08b2502563ca8296142a00693b05ca7ab053a172750994683ca6eb0534172730994603ca2c1e531582970b93904ca281e52b1827109ca5042a4c1ad231828d8a145c50a312351451a1b09cc7042a202e49c132a58c350c60a7e2d53915a996ad4b256868af31854a9429d4914ca40a14e0179480a54784ea3826d121324d08b438429701ac9209684ac12d0349882e503582470492905c 12 5 11 10 6,
  unpackLinksF 0x830408a040fe27f03e89d8eec07413a01c46e016b2b4899c4cc16603285940c81595ab0ce7a7013801c00e006e13701b80dc06453201900c426203101880b0a5802a11500a8050228013849c04e02700fa03a21c00e0058c24412009001980820400108080002000 0x350142fe0517e360939ac5f4d613769180c62bfe2d5fb14afb6dd7cb5ea503134e14af70b0d3040bd5a234a1414a080d2032bda2fde914ef36bd4905268821522582ee0d8d0950bb02e340542ee6c176358bc6315e116aef8a56716ea40b14465799f2a57686ea1c315d6179970a51114e2989a016493658bfad453d65af6aad4f326a598b4eca5a5e48d2b1b68d88343c3da161c97b0a48d8415ec0ca359a17e860a71084f7d025b8e11d960877c03fbc81e90c0e41d06b75033ba41894a0940a02b6b127b909adc5166e129b68945b4092dc010add46b6dc59b6926da2916cf24d6c842b51ac5aed22d48b0ca840b4a305ad166d56b369b4ab45a35a091acf28cc9842b381950b175e469b73b49b99a2c78d04fc49b72a45b8d1fdbe8dc6829b6f145b709fdb04decd24f428518801f3240cacb48b36855b2822d865b2bf2c14da35b1ca558c51a840bb360559801acf8132c3ac160845 13 5 11 10 6,
  unpackLinksF 0xfe3f4be87b2ee9d87b0733e61c8788ed4bfd7c2f0de0bc16ced8592ae541e805009a73063ac528a114228441809002003a6740e45c83726e0d85b0360684cc545a533ec7c0e19c02cc580831001a6340680760e010c20004 0xce0125485833e27951850ce418678d633b6a151060cdc102de093394819a844ce0162de4c3350499b934bb83666c173340a9a8451d3927e9892f4748fa0243a8428c5813dff096e80476c421e7e0bf3d0579d027ccc11e5f1832fac19636ccb92e658d83146b18014c4dc2666158b2d8c595a6e6c028dfe136f008395029ca12364e1254b082d7831c9a2964a97ad30bf4f8536b420da41769e0a33b05cc881fe420ef2006f8f833c8e2963d142d10bf4e053c7426638103188c18c560c593662cd831449989828bf8a66355bb19ac58bc62c5537624989fe0b2d6051bf426dde10711052cb821c2da260a511fd093821368981fbf80edca06ed583305c0ae1a4fa9b0a20b015c32296168c3092bd6805fa64298260570926d1203f7ec1db900ddaa06657015c1c9f530144ad02b83452c151860857acf0bf4b05329c0adf91b2950c181028bea2e26e911a90a180028 11 4 11 10 5,
  unpackLinksF 0x940c90a4812218f1468a3411a08a1c5022050a385042821030237f13f81f82f2579031d98c0c606112ca1640b205522a814c4a22500a70938090634a1810b845a12c0912884242020090006103001610a844c424112009004041840c005842061000708304088002 0x1b895cdc02eefc0e77c0b982124dec2cdb417eb10a7bad6cac0306ee0e3758c129458ddab16e91baaf0c5b8838dca2f6e0d4ead0a556160db4366db1836eac56c96eaacb16d81baa70c5c745ee3229eff14b7d6a7bd25fde526e369177829dbc13ec0c935b017ea60a7b984fdbc269141243c08bb5843da820c660fdba0668d02b2f013dee53367099b4359c69a0ecc165b90837b03d0b41a96e0941c02b028496e02096c0d41b02b8a34cd84266a89835e269a9950d49306bc4d3518c193c580a8a21684d019249ae04cd61b0ea0d83306b393358c65a8ec8d2b63693b1348d81a3624d075f48dae9468102cb6e1475b092a4041bd01e8520d4b304a0c0158bc1fc040edd306eda833cbe346311832e6b18114cd62b0e5b16b178a5aba5ec492954a1870109b78841d5814d0e08753269a9a34d51a369e9774b4aba91468042cb6814751092a6841d3eb069a96346489a6b5ccb136692143498a1a2a40d2e306889034a0b9a40505bc1268c93345081a10245bc98684913446a98b26cd0c14682092fc4d99f038 13 5 11 10 6,
  unpackLinksF 0x9804a8e54126293049063c70aa840c10a0810028003e8df40f62781bc01e00ee1741b909c80e216c2b6015aca8254028113c29a24d026813029424a01ad4cc46603301904c046003001800bc23f01f00f0464a3011800b08542262130080c4001c20e0068428600a 0xef8a658c183bb061de03cee80a7740d3bb289d406cee4127864ffc226f86125b1428f820ffbf077de837ee01992606c6c02fd615ceac2ef6c0e6e10bf62053ec2b6586183b2071d846098a2c76358baf8dd61062eb01c75b17bab6a760052afcb07501b3a88c1d4d62b80b757c58ba70dd5d062f1a2f78914fb78a5dab53ed1277688fb9f2bfd994dc6ca2e14496df0bf5c853eb827f54135130926b045e9821f4a1063807ede8332480d8d205d1f056650278d81fc0e0edd906ede033e782ce124939c0b3ce85ce79a7f38d1f8e69bd1b49e89a2f2ed075949bd0a45e811ff3e8df9327d841261a026f361279a08a460418d41fc0c0edd806edd8334781599209c910328e82b32013f2c166dd0bf5c053e45a9730d7b976a5caa5fcc51ef288d7932bdbc146de09b5b817eb60a62583de481cf200d4870628e02b31413eee572b50c3bb05ddb828f1a0e6a706383924dd5b6710123840695a160e20a670c932b30c1c1830e101e70409382069c1944db4367020d38b47fc5237c18935641478907fc383be141bf000cd1b05661827 13 5 11 10 6,
  unpackLinksF 0x9f04f827833c08d8c6823411818254102081021800bb29d80ec07413a01c84e21700b51994aca0640b2018c2b2a5711f64f047803821b08d804351f10f807c03a21d00e807021900c0058418a0a10500188082002 0x6cc8dfed8bbf6b51f1926fe49178e29bf8945d9493bc8137f0093f78457b020c240e5c20629202b4281393606c8002ff1838fb0a6ec0517e726baf92583c2cfd61350508bf1039f681aa080975e249f0838fa126ec0917e746bae9268382cfcc1347b08bf0039f601a8f4057e329881934f84a60f2490cf6901aa48f89a2fc09150226c3c126f7c1b7bc09bb668fbf247d6d1ba004d87624c7f8241d40a7b69350548bed235f64a68f6517d826a9182a3f8131340687402cf5b52704207db177ed6bbdaa47f351efd48dfe946bbe947e5c9efca4dfe426bad12784025c14125dd08ee00418f01efba0efdc073eb837f581aa8a0c5210567e8272600d8e605c97036388178ec1fc120eddc06edf833e5927ef691fc669bea349f4da2f9ad07cc47dac94df48a2f2a4ff7a26f871253f026fa2127d008a8a8418e81fc100eddb06edf0334801492c06c7002e4a81b1bc0bdc817ecb0a7e4b52f39af79ad4bcc4bdda246ed11b74057f3127be5935b8c2fd9214ce507be5039f201aa200c49403637017ec8ae590187b10bbd4851f141cd740c70d249d836cf00247780d2c72c1e014c 13 5 11 10 6
]

def L_189 := shardLinks ld_189

def st_189 := dagTraceF m_189 s_189 9 F_189

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_189 : dagCheckRootsF m_189 g_189 b_189 (dagRefF 1011 st_189 L_189 0) s_189 9 = true := by
  decide +kernel

def ck_189 := dagCheckNodeF m_189 g_189 b_189 1011 st_189 L_189

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_0 : treeBlockF 0 16 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_16 : treeBlockF 16 32 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_32 : treeBlockF 32 48 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_48 : treeBlockF 48 64 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_64 : treeBlockF 64 80 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_80 : treeBlockF 80 96 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_96 : treeBlockF 96 112 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_112 : treeBlockF 112 128 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_128 : treeBlockF 128 144 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_144 : treeBlockF 144 160 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_160 : treeBlockF 160 176 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_176 : treeBlockF 176 192 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_192 : treeBlockF 192 208 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_208 : treeBlockF 208 224 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_224 : treeBlockF 224 240 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_240 : treeBlockF 240 256 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_256 : treeBlockF 256 272 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_272 : treeBlockF 272 288 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_288 : treeBlockF 288 304 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_304 : treeBlockF 304 320 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_320 : treeBlockF 320 336 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_336 : treeBlockF 336 352 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_352 : treeBlockF 352 368 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_368 : treeBlockF 368 384 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_384 : treeBlockF 384 400 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_400 : treeBlockF 400 416 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_416 : treeBlockF 416 432 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_432 : treeBlockF 432 448 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_448 : treeBlockF 448 464 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_464 : treeBlockF 464 480 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_480 : treeBlockF 480 496 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_496 : treeBlockF 496 512 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_512 : treeBlockF 512 528 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_528 : treeBlockF 528 544 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_544 : treeBlockF 544 560 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_560 : treeBlockF 560 576 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_576 : treeBlockF 576 592 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_592 : treeBlockF 592 608 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_608 : treeBlockF 608 624 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_624 : treeBlockF 624 640 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_640 : treeBlockF 640 656 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_656 : treeBlockF 656 672 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_672 : treeBlockF 672 688 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_688 : treeBlockF 688 704 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_704 : treeBlockF 704 720 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_720 : treeBlockF 720 736 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_736 : treeBlockF 736 752 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_752 : treeBlockF 752 768 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_768 : treeBlockF 768 784 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_784 : treeBlockF 784 800 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_800 : treeBlockF 800 816 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_816 : treeBlockF 816 832 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_832 : treeBlockF 832 848 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_848 : treeBlockF 848 864 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_864 : treeBlockF 864 880 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_880 : treeBlockF 880 896 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_896 : treeBlockF 896 912 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_912 : treeBlockF 912 928 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_928 : treeBlockF 928 944 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_944 : treeBlockF 944 960 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_960 : treeBlockF 960 976 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_976 : treeBlockF 976 992 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_992 : treeBlockF 992 1008 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_189_1008 : treeBlockF 1008 1011 ck_189 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_189 : ∀ j, 0 ≤ j → j < 1011 → ck_189 j = true :=
  (block_join (block_join (block_join (block_join (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_189_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_189_16 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_189_32 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_189_48 h1 h2))) (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_189_64 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_189_80 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_189_96 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_189_112 h1 h2)))) (block_join (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_189_128 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_189_144 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_189_160 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_189_176 h1 h2))) (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_189_192 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_189_208 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_189_224 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_189_240 h1 h2))))) (block_join (block_join (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_189_256 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_189_272 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_189_288 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_189_304 h1 h2))) (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_189_320 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_189_336 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_189_352 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_189_368 h1 h2)))) (block_join (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_189_384 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_189_400 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_189_416 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_189_432 h1 h2))) (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_189_448 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_189_464 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_189_480 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_189_496 h1 h2)))))) (block_join (block_join (block_join (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_189_512 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_189_528 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_189_544 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_189_560 h1 h2))) (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_189_576 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_189_592 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_189_608 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_189_624 h1 h2)))) (block_join (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_189_640 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_189_656 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_189_672 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_189_688 h1 h2))) (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_189_704 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_189_720 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_189_736 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_189_752 h1 h2))))) (block_join (block_join (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_189_768 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_189_784 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_189_800 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_189_816 h1 h2))) (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_189_832 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_189_848 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_189_864 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_189_880 h1 h2)))) (block_join (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_189_896 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_189_912 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_189_928 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_189_944 h1 h2))) (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_189_960 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_189_976 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_189_992 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_189_1008 h1 h2)))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_189 : LowerBin m_189 s_189 g_189 10 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_189 sub_189 goal_189 rc_189 nc_189

def m_1 : Nat := 0x4040404040404040

def s_1 : List Nat := [0x40404040, 0x404000004040, 0x40004000400040]

def g_1 : Nat := 0x4000404040

def b_1 : List (Nat × List Nat × Nat × Nat) := []

theorem known_1 : KnownBin b_1 := by
  intro b hb
  simp [b_1] at hb

theorem sub_1 : ∀ b ∈ b_1, m_1 &&& b.1 = b.1 := by
  intro b hb
  simp [b_1] at hb

theorem goal_1 : ∀ b ∈ b_1, canon b.1 g_1 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_1] at hb

def fd_1 : Array Nat := #[
  0x7
]

def F_1 := shardForest fd_1 1 3

def ld_1 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_1 := shardLinks ld_1

def st_1 := dagTraceF m_1 s_1 3 F_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1 : dagCheckRootsF m_1 g_1 b_1 (dagRefF 1 st_1 L_1 0) s_1 3 = true := by
  decide +kernel

def ck_1 := dagCheckNodeF m_1 g_1 b_1 1 st_1 L_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1_0 : treeBlockF 0 1 ck_1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_1 : ∀ j, 0 ≤ j → j < 1 → ck_1 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_1_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_1 : LowerBin m_1 s_1 g_1 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_1 sub_1 goal_1 rc_1 nc_1

def m_5 : Nat := 0x4400440044004400

def s_5 : List Nat := [0x44004400, 0x440000004400, 0x400040004000400]

def g_5 : Nat := 0x40004004400

def b_5 : List (Nat × List Nat × Nat × Nat) := []

theorem known_5 : KnownBin b_5 := by
  intro b hb
  simp [b_5] at hb

theorem sub_5 : ∀ b ∈ b_5, m_5 &&& b.1 = b.1 := by
  intro b hb
  simp [b_5] at hb

theorem goal_5 : ∀ b ∈ b_5, canon b.1 g_5 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_5] at hb

def fd_5 : Array Nat := #[
  0x7
]

def F_5 := shardForest fd_5 1 3

def ld_5 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_5 := shardLinks ld_5

def st_5 := dagTraceF m_5 s_5 3 F_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_5 : dagCheckRootsF m_5 g_5 b_5 (dagRefF 1 st_5 L_5 0) s_5 3 = true := by
  decide +kernel

def ck_5 := dagCheckNodeF m_5 g_5 b_5 1 st_5 L_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_5_0 : treeBlockF 0 1 ck_5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_5 : ∀ j, 0 ≤ j → j < 1 → ck_5 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_5_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_5 : LowerBin m_5 s_5 g_5 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_5 sub_5 goal_5 rc_5 nc_5

def m_9 : Nat := 0x4444000044440000

def s_9 : List Nat := [0x44440000, 0x44000000440000, 0x404000004040000]

def g_9 : Nat := 0x4000004440000

def b_9 : List (Nat × List Nat × Nat × Nat) := []

theorem known_9 : KnownBin b_9 := by
  intro b hb
  simp [b_9] at hb

theorem sub_9 : ∀ b ∈ b_9, m_9 &&& b.1 = b.1 := by
  intro b hb
  simp [b_9] at hb

theorem goal_9 : ∀ b ∈ b_9, canon b.1 g_9 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_9] at hb

def fd_9 : Array Nat := #[
  0x7
]

def F_9 := shardForest fd_9 1 3

def ld_9 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_9 := shardLinks ld_9

def st_9 := dagTraceF m_9 s_9 3 F_9

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_9 : dagCheckRootsF m_9 g_9 b_9 (dagRefF 1 st_9 L_9 0) s_9 3 = true := by
  decide +kernel

def ck_9 := dagCheckNodeF m_9 g_9 b_9 1 st_9 L_9

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_9_0 : treeBlockF 0 1 ck_9 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_9 : ∀ j, 0 ≤ j → j < 1 → ck_9 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_9_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_9 : LowerBin m_9 s_9 g_9 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_9 sub_9 goal_9 rc_9 nc_9

def m_13 : Nat := 0x4444444400000000

def s_13 : List Nat := [0x444400000000, 0x44004400000000, 0x404040400000000]

def g_13 : Nat := 0x4044400000000

def b_13 : List (Nat × List Nat × Nat × Nat) := []

theorem known_13 : KnownBin b_13 := by
  intro b hb
  simp [b_13] at hb

theorem sub_13 : ∀ b ∈ b_13, m_13 &&& b.1 = b.1 := by
  intro b hb
  simp [b_13] at hb

theorem goal_13 : ∀ b ∈ b_13, canon b.1 g_13 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_13] at hb

def fd_13 : Array Nat := #[
  0x7
]

def F_13 := shardForest fd_13 1 3

def ld_13 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_13 := shardLinks ld_13

def st_13 := dagTraceF m_13 s_13 3 F_13

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_13 : dagCheckRootsF m_13 g_13 b_13 (dagRefF 1 st_13 L_13 0) s_13 3 = true := by
  decide +kernel

def ck_13 := dagCheckNodeF m_13 g_13 b_13 1 st_13 L_13

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_13_0 : treeBlockF 0 1 ck_13 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_13 : ∀ j, 0 ≤ j → j < 1 → ck_13 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_13_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_13 : LowerBin m_13 s_13 g_13 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_13 sub_13 goal_13 rc_13 nc_13

def m_73 : Nat := 0x4444444444444444

def s_73 : List Nat := [0x44444444, 0x444400004444, 0x44004400440044, 0x404040404040404]

def g_73 : Nat := 0x4044404444444

def b_73 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_5, s_5, 4, g_5), (m_9, s_9, 4, g_9), (m_13, s_13, 4, g_13)]

theorem known_73 : KnownBin b_73 := by
  intro b hb
  simp only [b_73, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_1
  · exact lb_5
  · exact lb_9
  · exact lb_13

theorem sub_73 : ∀ b ∈ b_73, m_73 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_73, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

theorem goal_73 : ∀ b ∈ b_73, canon b.1 g_73 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_73, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

def fd_73 : Array Nat := #[
  0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f
]

def F_73 := shardForest fd_73 6 10

def ld_73 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x8e11c1fc3f07c2f81b43606c0d45a0b40662cc15c2b0542a8148a18420841009f13e0784f01d12b0540a814128050098921222440809001e21e00b001 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d347d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 11 4 10 6 5
]

def L_73 := shardLinks ld_73

def st_73 := dagTraceF m_73 s_73 6 F_73

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_73 : dagCheckRootsF m_73 g_73 b_73 (dagRefF 43 st_73 L_73 0) s_73 6 = true := by
  decide +kernel

def ck_73 := dagCheckNodeF m_73 g_73 b_73 43 st_73 L_73

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_73_0 : treeBlockF 0 16 ck_73 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_73_16 : treeBlockF 16 32 ck_73 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_73_32 : treeBlockF 32 43 ck_73 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_73 : ∀ j, 0 ≤ j → j < 43 → ck_73 j = true :=
  (block_join (fun _ h1 h2 => treeBlockF_at nb_73_0 h1 h2) (block_join (fun _ h1 h2 => treeBlockF_at nb_73_16 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_73_32 h1 h2)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_73 : LowerBin m_73 s_73 g_73 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_73 sub_73 goal_73 rc_73 nc_73

def m_35 : Nat := 0xc000c000c000c00

def s_35 : List Nat := [0xc000c00, 0xc0000000c00, 0x400040004000400]

def g_35 : Nat := 0x40004000c00

def b_35 : List (Nat × List Nat × Nat × Nat) := []

theorem known_35 : KnownBin b_35 := by
  intro b hb
  simp [b_35] at hb

theorem sub_35 : ∀ b ∈ b_35, m_35 &&& b.1 = b.1 := by
  intro b hb
  simp [b_35] at hb

theorem goal_35 : ∀ b ∈ b_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_35] at hb

def fd_35 : Array Nat := #[
  0x7
]

def F_35 := shardForest fd_35 1 3

def ld_35 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_35 := shardLinks ld_35

def st_35 := dagTraceF m_35 s_35 3 F_35

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsF m_35 g_35 b_35 (dagRefF 1 st_35 L_35 0) s_35 3 = true := by
  decide +kernel

def ck_35 := dagCheckNodeF m_35 g_35 b_35 1 st_35 L_35

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_35_0 : treeBlockF 0 1 ck_35 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_35 : ∀ j, 0 ≤ j → j < 1 → ck_35 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_35_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_35 : LowerBin m_35 s_35 g_35 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_35 sub_35 goal_35 rc_35 nc_35

def m_43 : Nat := 0xcc000000cc00

def s_43 : List Nat := [0xcc00, 0xc0000000c00, 0x440000004400]

def g_43 : Nat := 0x40000004c00

def b_43 : List (Nat × List Nat × Nat × Nat) := []

theorem known_43 : KnownBin b_43 := by
  intro b hb
  simp [b_43] at hb

theorem sub_43 : ∀ b ∈ b_43, m_43 &&& b.1 = b.1 := by
  intro b hb
  simp [b_43] at hb

theorem goal_43 : ∀ b ∈ b_43, canon b.1 g_43 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_43] at hb

def fd_43 : Array Nat := #[
  0x7
]

def F_43 := shardForest fd_43 1 3

def ld_43 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_43 := shardLinks ld_43

def st_43 := dagTraceF m_43 s_43 3 F_43

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsF m_43 g_43 b_43 (dagRefF 1 st_43 L_43 0) s_43 3 = true := by
  decide +kernel

def ck_43 := dagCheckNodeF m_43 g_43 b_43 1 st_43 L_43

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_43_0 : treeBlockF 0 1 ck_43 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_43 : ∀ j, 0 ≤ j → j < 1 → ck_43 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_43_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_43 : LowerBin m_43 s_43 g_43 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_43 sub_43 goal_43 rc_43 nc_43

def m_47 : Nat := 0xcc00cc00

def s_47 : List Nat := [0xcc00, 0xc000c00, 0x44004400]

def g_47 : Nat := 0x4004c00

def b_47 : List (Nat × List Nat × Nat × Nat) := []

theorem known_47 : KnownBin b_47 := by
  intro b hb
  simp [b_47] at hb

theorem sub_47 : ∀ b ∈ b_47, m_47 &&& b.1 = b.1 := by
  intro b hb
  simp [b_47] at hb

theorem goal_47 : ∀ b ∈ b_47, canon b.1 g_47 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_47] at hb

def fd_47 : Array Nat := #[
  0x7
]

def F_47 := shardForest fd_47 1 3

def ld_47 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_47 := shardLinks ld_47

def st_47 := dagTraceF m_47 s_47 3 F_47

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsF m_47 g_47 b_47 (dagRefF 1 st_47 L_47 0) s_47 3 = true := by
  decide +kernel

def ck_47 := dagCheckNodeF m_47 g_47 b_47 1 st_47 L_47

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_47_0 : treeBlockF 0 1 ck_47 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_47 : ∀ j, 0 ≤ j → j < 1 → ck_47 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_47_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_47 : LowerBin m_47 s_47 g_47 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_47 sub_47 goal_47 rc_47 nc_47

def m_121 : Nat := 0xcc00cc00cc00cc00

def s_121 : List Nat := [0xcc00cc00, 0xcc000000cc00, 0xc000c000c000c00, 0x4400440044004400]

def g_121 : Nat := 0x40004004c00

def b_121 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5), (m_35, s_35, 4, g_35), (m_43, s_43, 4, g_43), (m_47, s_47, 4, g_47)]

theorem known_121 : KnownBin b_121 := by
  intro b hb
  simp only [b_121, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_5
  · exact lb_35
  · exact lb_43
  · exact lb_47

theorem sub_121 : ∀ b ∈ b_121, m_121 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_121, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

theorem goal_121 : ∀ b ∈ b_121, canon b.1 g_121 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_121, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

def fd_121 : Array Nat := #[
  0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f
]

def F_121 := shardForest fd_121 6 10

def ld_121 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x8e11c1fc3e17c0f81b43516a0d05a0340662cc15c2a1522a41482184027c4f81e13c0780e89d02b05049893024248088910220404801001e21e00b001 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b407c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 11 4 10 6 5
]

def L_121 := shardLinks ld_121

def st_121 := dagTraceF m_121 s_121 6 F_121

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_121 : dagCheckRootsF m_121 g_121 b_121 (dagRefF 43 st_121 L_121 0) s_121 6 = true := by
  decide +kernel

def ck_121 := dagCheckNodeF m_121 g_121 b_121 43 st_121 L_121

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_121_0 : treeBlockF 0 16 ck_121 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_121_16 : treeBlockF 16 32 ck_121 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_121_32 : treeBlockF 32 43 ck_121 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_121 : ∀ j, 0 ≤ j → j < 43 → ck_121 j = true :=
  (block_join (fun _ h1 h2 => treeBlockF_at nb_121_0 h1 h2) (block_join (fun _ h1 h2 => treeBlockF_at nb_121_16 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_121_32 h1 h2)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_121 : LowerBin m_121 s_121 g_121 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_121 sub_121 goal_121 rc_121 nc_121

def m_37 : Nat := 0xc0c00000c0c0000

def s_37 : List Nat := [0xc0c0000, 0xc0000000c0000, 0x404000004040000]

def g_37 : Nat := 0x40000040c0000

def b_37 : List (Nat × List Nat × Nat × Nat) := []

theorem known_37 : KnownBin b_37 := by
  intro b hb
  simp [b_37] at hb

theorem sub_37 : ∀ b ∈ b_37, m_37 &&& b.1 = b.1 := by
  intro b hb
  simp [b_37] at hb

theorem goal_37 : ∀ b ∈ b_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_37] at hb

def fd_37 : Array Nat := #[
  0x7
]

def F_37 := shardForest fd_37 1 3

def ld_37 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_37 := shardLinks ld_37

def st_37 := dagTraceF m_37 s_37 3 F_37

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsF m_37 g_37 b_37 (dagRefF 1 st_37 L_37 0) s_37 3 = true := by
  decide +kernel

def ck_37 := dagCheckNodeF m_37 g_37 b_37 1 st_37 L_37

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_37_0 : treeBlockF 0 1 ck_37 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_37 : ∀ j, 0 ≤ j → j < 1 → ck_37 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_37_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_37 : LowerBin m_37 s_37 g_37 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_37 sub_37 goal_37 rc_37 nc_37

def m_41 : Nat := 0xcc000000cc0000

def s_41 : List Nat := [0xcc0000, 0xc0000000c0000, 0x44000000440000]

def g_41 : Nat := 0x40000004c0000

def b_41 : List (Nat × List Nat × Nat × Nat) := []

theorem known_41 : KnownBin b_41 := by
  intro b hb
  simp [b_41] at hb

theorem sub_41 : ∀ b ∈ b_41, m_41 &&& b.1 = b.1 := by
  intro b hb
  simp [b_41] at hb

theorem goal_41 : ∀ b ∈ b_41, canon b.1 g_41 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_41] at hb

def fd_41 : Array Nat := #[
  0x7
]

def F_41 := shardForest fd_41 1 3

def ld_41 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_41 := shardLinks ld_41

def st_41 := dagTraceF m_41 s_41 3 F_41

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsF m_41 g_41 b_41 (dagRefF 1 st_41 L_41 0) s_41 3 = true := by
  decide +kernel

def ck_41 := dagCheckNodeF m_41 g_41 b_41 1 st_41 L_41

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_41_0 : treeBlockF 0 1 ck_41 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_41 : ∀ j, 0 ≤ j → j < 1 → ck_41 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_41_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_41 : LowerBin m_41 s_41 g_41 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_41 sub_41 goal_41 rc_41 nc_41

def m_51 : Nat := 0xcccc0000

def s_51 : List Nat := [0xcc0000, 0xc0c0000, 0x44440000]

def g_51 : Nat := 0x44c0000

def b_51 : List (Nat × List Nat × Nat × Nat) := []

theorem known_51 : KnownBin b_51 := by
  intro b hb
  simp [b_51] at hb

theorem sub_51 : ∀ b ∈ b_51, m_51 &&& b.1 = b.1 := by
  intro b hb
  simp [b_51] at hb

theorem goal_51 : ∀ b ∈ b_51, canon b.1 g_51 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_51] at hb

def fd_51 : Array Nat := #[
  0x7
]

def F_51 := shardForest fd_51 1 3

def ld_51 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_51 := shardLinks ld_51

def st_51 := dagTraceF m_51 s_51 3 F_51

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsF m_51 g_51 b_51 (dagRefF 1 st_51 L_51 0) s_51 3 = true := by
  decide +kernel

def ck_51 := dagCheckNodeF m_51 g_51 b_51 1 st_51 L_51

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_51_0 : treeBlockF 0 1 ck_51 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_51 : ∀ j, 0 ≤ j → j < 1 → ck_51 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_51_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_51 : LowerBin m_51 s_51 g_51 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_51 sub_51 goal_51 rc_51 nc_51

def m_129 : Nat := 0xcccc0000cccc0000

def s_129 : List Nat := [0xcccc0000, 0xcc000000cc0000, 0xc0c00000c0c0000, 0x4444000044440000]

def g_129 : Nat := 0x40000044c0000

def b_129 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9), (m_37, s_37, 4, g_37), (m_41, s_41, 4, g_41), (m_51, s_51, 4, g_51)]

theorem known_129 : KnownBin b_129 := by
  intro b hb
  simp only [b_129, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_9
  · exact lb_37
  · exact lb_41
  · exact lb_51

theorem sub_129 : ∀ b ∈ b_129, m_129 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_129, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

theorem goal_129 : ∀ b ∈ b_129, canon b.1 g_129 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_129, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

def fd_129 : Array Nat := #[
  0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f
]

def F_129 := shardForest fd_129 6 10

def ld_129 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x8e11c1fc3e17c0f81b43516a0d05a0340662cc15c2a1522a41482184027c4f81e13c0780e89d02b05049893024248088910220404801001e21e00b001 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b407c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 11 4 10 6 5
]

def L_129 := shardLinks ld_129

def st_129 := dagTraceF m_129 s_129 6 F_129

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_129 : dagCheckRootsF m_129 g_129 b_129 (dagRefF 43 st_129 L_129 0) s_129 6 = true := by
  decide +kernel

def ck_129 := dagCheckNodeF m_129 g_129 b_129 43 st_129 L_129

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_129_0 : treeBlockF 0 16 ck_129 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_129_16 : treeBlockF 16 32 ck_129 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_129_32 : treeBlockF 32 43 ck_129 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_129 : ∀ j, 0 ≤ j → j < 43 → ck_129 j = true :=
  (block_join (fun _ h1 h2 => treeBlockF_at nb_129_0 h1 h2) (block_join (fun _ h1 h2 => treeBlockF_at nb_129_16 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_129_32 h1 h2)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_129 : LowerBin m_129 s_129 g_129 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_129 sub_129 goal_129 rc_129 nc_129

def m_111 : Nat := 0xc0c0c0c0c0c0c0c

def s_111 : List Nat := [0xc0c0c0c, 0xc0c00000c0c, 0xc000c000c000c, 0x404040404040404]

def g_111 : Nat := 0x40404040c0c0c

def b_111 : List (Nat × List Nat × Nat × Nat) := [(m_35, s_35, 4, g_35)]

theorem known_111 : KnownBin b_111 := by
  intro b hb
  simp only [b_111, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_35

theorem sub_111 : ∀ b ∈ b_111, m_111 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_111, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

theorem goal_111 : ∀ b ∈ b_111, canon b.1 g_111 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_111, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

def F_111 : Nat → Nat × Nat := fun _ => (0, 0)

def L_111 : Nat → Nat → Option Nat := fun _ _ => none

def st_111 := dagTraceF m_111 s_111 4 F_111

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_111 : dagCheckRootsF m_111 g_111 b_111 (dagRefF 0 st_111 L_111 0) s_111 4 = true := by
  decide +kernel

def ck_111 := dagCheckNodeF m_111 g_111 b_111 0 st_111 L_111

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_111 : ∀ j, 0 ≤ j → j < 0 → ck_111 j = true :=
  fun _ _ h => absurd h (Nat.not_lt_zero _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_111 : LowerBin m_111 s_111 g_111 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_111 sub_111 goal_111 rc_111 nc_111

def m_113 : Nat := 0xc0c0c0c0c0c0c0c0

def s_113 : List Nat := [0xc0c0c0c0, 0xc0c00000c0c0, 0xc000c000c000c0, 0x4040404040404040]

def g_113 : Nat := 0x4000404040

def b_113 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]

theorem known_113 : KnownBin b_113 := by
  intro b hb
  simp only [b_113, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_1

theorem sub_113 : ∀ b ∈ b_113, m_113 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_113, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

theorem goal_113 : ∀ b ∈ b_113, canon b.1 g_113 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_113, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

def F_113 : Nat → Nat × Nat := fun _ => (0, 0)

def L_113 : Nat → Nat → Option Nat := fun _ _ => none

def st_113 := dagTraceF m_113 s_113 4 F_113

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_113 : dagCheckRootsF m_113 g_113 b_113 (dagRefF 0 st_113 L_113 0) s_113 4 = true := by
  decide +kernel

def ck_113 := dagCheckNodeF m_113 g_113 b_113 0 st_113 L_113

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_113 : ∀ j, 0 ≤ j → j < 0 → ck_113 j = true :=
  fun _ _ h => absurd h (Nat.not_lt_zero _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_113 : LowerBin m_113 s_113 g_113 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_113 sub_113 goal_113 rc_113 nc_113

def m_117 : Nat := 0xcc00cc00cc00cc

def s_117 : List Nat := [0xcc00cc, 0xcc000000cc, 0xc000c000c000c, 0x44004400440044]

def g_117 : Nat := 0x40044004c004c

def b_117 : List (Nat × List Nat × Nat × Nat) := [(m_41, s_41, 4, g_41)]

theorem known_117 : KnownBin b_117 := by
  intro b hb
  simp only [b_117, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_41

theorem sub_117 : ∀ b ∈ b_117, m_117 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_117, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

theorem goal_117 : ∀ b ∈ b_117, canon b.1 g_117 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_117, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

def F_117 : Nat → Nat × Nat := fun _ => (0, 0)

def L_117 : Nat → Nat → Option Nat := fun _ _ => none

def st_117 := dagTraceF m_117 s_117 4 F_117

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_117 : dagCheckRootsF m_117 g_117 b_117 (dagRefF 0 st_117 L_117 0) s_117 4 = true := by
  decide +kernel

def ck_117 := dagCheckNodeF m_117 g_117 b_117 0 st_117 L_117

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_117 : ∀ j, 0 ≤ j → j < 0 → ck_117 j = true :=
  fun _ _ h => absurd h (Nat.not_lt_zero _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_117 : LowerBin m_117 s_117 g_117 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_117 sub_117 goal_117 rc_117 nc_117

def m_125 : Nat := 0xcccc0000cccc

def s_125 : List Nat := [0xcccc, 0xcc000000cc, 0xc0c00000c0c, 0x444400004444]

def g_125 : Nat := 0x44400004c4c

def b_125 : List (Nat × List Nat × Nat × Nat) := [(m_43, s_43, 4, g_43)]

theorem known_125 : KnownBin b_125 := by
  intro b hb
  simp only [b_125, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_43

theorem sub_125 : ∀ b ∈ b_125, m_125 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_125, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

theorem goal_125 : ∀ b ∈ b_125, canon b.1 g_125 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_125, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

def F_125 : Nat → Nat × Nat := fun _ => (0, 0)

def L_125 : Nat → Nat → Option Nat := fun _ _ => none

def st_125 := dagTraceF m_125 s_125 4 F_125

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_125 : dagCheckRootsF m_125 g_125 b_125 (dagRefF 0 st_125 L_125 0) s_125 4 = true := by
  decide +kernel

def ck_125 := dagCheckNodeF m_125 g_125 b_125 0 st_125 L_125

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_125 : ∀ j, 0 ≤ j → j < 0 → ck_125 j = true :=
  fun _ _ h => absurd h (Nat.not_lt_zero _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_125 : LowerBin m_125 s_125 g_125 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_125 sub_125 goal_125 rc_125 nc_125

def m_135 : Nat := 0xcccccccc

def s_135 : List Nat := [0xcccc, 0xcc00cc, 0xc0c0c0c, 0x44444444]

def g_135 : Nat := 0x44c4c4c

def b_135 : List (Nat × List Nat × Nat × Nat) := [(m_47, s_47, 4, g_47)]

theorem known_135 : KnownBin b_135 := by
  intro b hb
  simp only [b_135, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_47

theorem sub_135 : ∀ b ∈ b_135, m_135 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_135, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

theorem goal_135 : ∀ b ∈ b_135, canon b.1 g_135 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_135, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

def F_135 : Nat → Nat × Nat := fun _ => (0, 0)

def L_135 : Nat → Nat → Option Nat := fun _ _ => none

def st_135 := dagTraceF m_135 s_135 4 F_135

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_135 : dagCheckRootsF m_135 g_135 b_135 (dagRefF 0 st_135 L_135 0) s_135 4 = true := by
  decide +kernel

def ck_135 := dagCheckNodeF m_135 g_135 b_135 0 st_135 L_135

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_135 : ∀ j, 0 ≤ j → j < 0 → ck_135 j = true :=
  fun _ _ h => absurd h (Nat.not_lt_zero _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_135 : LowerBin m_135 s_135 g_135 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_135 sub_135 goal_135 rc_135 nc_135

def m_137 : Nat := 0xcccccccc00000000

def s_137 : List Nat := [0xcccc00000000, 0xcc00cc00000000, 0xc0c0c0c00000000, 0x4444444400000000]

def g_137 : Nat := 0x4044400000000

def b_137 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]

theorem known_137 : KnownBin b_137 := by
  intro b hb
  simp only [b_137, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_13

theorem sub_137 : ∀ b ∈ b_137, m_137 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_137, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

theorem goal_137 : ∀ b ∈ b_137, canon b.1 g_137 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_137, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

def F_137 : Nat → Nat × Nat := fun _ => (0, 0)

def L_137 : Nat → Nat → Option Nat := fun _ _ => none

def st_137 := dagTraceF m_137 s_137 4 F_137

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_137 : dagCheckRootsF m_137 g_137 b_137 (dagRefF 0 st_137 L_137 0) s_137 4 = true := by
  decide +kernel

def ck_137 := dagCheckNodeF m_137 g_137 b_137 0 st_137 L_137

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_137 : ∀ j, 0 ≤ j → j < 0 → ck_137 j = true :=
  fun _ _ h => absurd h (Nat.not_lt_zero _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_137 : LowerBin m_137 s_137 g_137 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_137 sub_137 goal_137 rc_137 nc_137

def m_193 : Nat := 0xcccccccccccccccc

def s_193 : List Nat := [0xcccccccc, 0xcccc0000cccc, 0xcc00cc00cc00cc, 0xc0c0c0c0c0c0c0c, 0x4444444444444444]

def g_193 : Nat := 0x40444044c4c4c

def b_193 : List (Nat × List Nat × Nat × Nat) := [(m_73, s_73, 7, g_73), (m_121, s_121, 7, g_121), (m_129, s_129, 7, g_129), (m_111, s_111, 5, g_111), (m_113, s_113, 5, g_113), (m_117, s_117, 5, g_117), (m_125, s_125, 5, g_125), (m_135, s_135, 5, g_135), (m_137, s_137, 5, g_137), (m_1, s_1, 4, g_1), (m_5, s_5, 4, g_5), (m_9, s_9, 4, g_9), (m_13, s_13, 4, g_13), (m_35, s_35, 4, g_35), (m_37, s_37, 4, g_37), (m_41, s_41, 4, g_41), (m_43, s_43, 4, g_43), (m_47, s_47, 4, g_47), (m_51, s_51, 4, g_51)]

theorem known_193 : KnownBin b_193 := by
  intro b hb
  simp only [b_193, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_73
  · exact lb_121
  · exact lb_129
  · exact lb_111
  · exact lb_113
  · exact lb_117
  · exact lb_125
  · exact lb_135
  · exact lb_137
  · exact lb_1
  · exact lb_5
  · exact lb_9
  · exact lb_13
  · exact lb_35
  · exact lb_37
  · exact lb_41
  · exact lb_43
  · exact lb_47
  · exact lb_51

theorem sub_193 : ∀ b ∈ b_193, m_193 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_193, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem goal_193 : ∀ b ∈ b_193, canon b.1 g_193 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_193, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def fd_193 : Array Nat := #[
  0xf62907b1403d498012460d2b706958839ac01a3620dd300685b8352781a162009218049082f8be180480be298048e81e8be153480ac1e0541201e8a613c5d09e2883cd482149e10a4b085238440a0214860f350079a403cd000246c05c5f065a40325201909005c5302d2f0291481529c0a14002d23024d200d8a207c5003ca001a9180d2520595202c180044d8076b40425801c2f00414c050780104b008218040640102e0001f,
  0x1d1250e8924744903e24c1d1230e8518792883a04a1dc170e8120750683a04600a298e4920718b20135f1be37004d3c6d490355621acaf0d49400268e0125e19ab08cc578024a631246188250c41184d8a23046c135a78b95805c2b82e150135a38b55804d29e2c25c134a58ab180556b82694714ca60a09505128828144134a189a4ec4d26e012520092708b58848ac02415c115b108c980452dc0124b10ca3083148412bc0124a,
  0x2f92f17c948bd6a04e9472e62f974120b98a64e93d29a2f968d20b44905a04829a29964d20b08a25812e2992914c578a88a4564502a0a9152538a928454140298a314c0c09d24a5145a28dac1441789d0a65004c2742593a10c9d0520082720e2f9325189908c41c5325e2c906d7c958dc41b4f24eb1106d1c834bc4723f23e3011c8dc830bc4185220c27106128898a44184620c211060e8848be4245320c1b00206c814b20145f,
  0x3fc9a1fc1189d8a64eb5e3eab09f49789d6a67b3463d8251ec118e78a27a56039d279e4d70e749677c603bcae1ce91ced498753543ad221d4490e74867392f39c9393ad489d69c6fd6238ab01c4970df8c47036037d3713ad2cdd48c6dc5236d2f13ad28d78a46bc5035ca613ad18ceadc6756234eb019d188d16c06726e33d2619c9889d6864eb4232da41951649d2be6346e31e3618cd889d29e623482f6b1183580c14b85eb62,
  0x4fda027c4953d2a8930374eda924c0d92c6949bc604dc26258d192c48c97a3a4c9a8264d012f46c983404bc9b2585512d2689604649813a549492604c9301e49ca224c0740106686c5f488a32441190d8a686b5e47e2ca1a97d1d8dc86a4f46eb121a91d1727e8c46045c9ba1a1790d0a48684e434252251490d08c8684243a2fa1d14d0d04c0082b42dac93b17cfe6947f3493f9a420c530fe68c7f24640d221fc1290107c7f048,
  0x5f89fafc4dd5b684be14556d27af49155b29ebc3485a2292ecd21686bcb9c505cc122d0d4968682b724e5bc122dc90968680b62305a12f2d48c1682bcb403d56c93ab60fd6449eb224356c1f2b88fd5c46eae13f5709babad215d680ae12756c1ea4c5115928aa7a5d55d22a9e575506d8a8350541a42a09b1502d8a803c53c93a4c179498c0a60345262c29253149098a32375181a28c091260a49304e49826a7a9353d46a9f13d,
  0x6fd2aa4cd7d2668ede3554992fa4c91d97adcdc45865eb136c151978dcd95606ce283640d1978c4cbc596b9af35c0d5978b0cbc5165db732e9b9a88b0d445065ca7347179a38a4d1b5e68c1ab2e531a08b0d045065ca132e1399709acd45e66a29334d7997098cc06c65c2124c8dd94690ca03c64c93a4c57991068c6c606362c31a5318d098c5a3762ca224c549890b89314761c2624c519850989314556da72b6d0d7e47ebf237,
  0x7d6313eb145f58a0fab6e7d5373ea139f68a4fb35e7d92f3ec579f5098f3237798a7bcc539e629af7b607bda83dc49de60bcf30527ae293cc119e606cf302679d1bbcc07801076e245e71229bbe8fddf46eef93f77c9bb89149c46a6ee1557112fb88935d94aae215f710a6bacd21c8ac4ea458721b73a3581d14b8e4362721a8b9a979cd4a4e435072d203909b9c9480e416e71093b8814dc407ce20390041ba4d179c128893452,
  0x8fc1300210e146bd0a3528ecaac2897e396b90a2478511ac6c956142bf1a35c850a3c284d6228dd18354889b745b1b22d48911362889a4c5297a294a51134889d1c4449ba254711116e888194440c21424f0a05e87c2242814e1b6c10db4886c1e42a49e1506b0c04485413c2c1121502f0a0520041fbcd17a11088f345382da3c1691e0c46b0613582c233cd14a094aaf335f81daabcc97e058b0fad6280c2a3eb1ba00ac100034,
  0x9fd22c7e13e7c69d3e14d9c122cf2d3a7949b381459c5b04ed142716a938b489c52a4e255271079381278fc274ced766769b3656099da2cce9766749b3456099d22c7e11e3f08d2bc5a9892e4c4172578ad3056095dab4ae9365d8c12ba35969ac4b4952570bd2c24495c2b47e0de3f06d20b5a949ae4a4172416ad20b4a93a2c49c1324168d265609052b4951824148d23a5891caa48217a452892085690da84844d24108d1f827,
  0xafeb057454aba0bd5d05dae82e57414a3f68f5bb45adc22c7e93ea7ac35994aacca354f582a76bb58560a9caf55c116a72b956560a9ca954e17aa70bb5385ca9c2947e91e878c35113aa8da85444da878c150034a1e2d53b5829d0b943c56a6ab0534172876ad4bd60a5c2e50e95a958c14394ea4c1ad0e532918c143942a1c2750e1368d8a145246a2e2851451a870994405ca1c2147e8de3f0bb425609fdaacfed1681ac13fa55,
  0xbe62d5fc0a2f98a57e360be5b75f4d62f96bd7483fbdc2c5e717ef568979c53bcdaf5d20f6eb8c575c5abae295dcd82eb0dd76358bac2f5d20cee906200927b35a4d9ad16cd48b72135b351fdc1166e029b70042b351bd9a516dd46b6693fb662cdb2936d908566937b5da459d166ce6b36a458b39a55a5182ce68d67246b38a359c0cacd24e0084fb2922d941163f69f5d561b18a558c51abaac15d25db0eb057457ac108b5d15c,
  0xccc17e7c4f3330579db58ceda866609f384819c02ccd09a668173350499a054ccc11dd2d4ae969d95562cbab065c9732a8c596360ca9376540a6e969793a46c9c24e4b14b254bd74b4ac722963e0ff1f0778f837c7c19e391431c0998e040ba5a36235bb11ac58c560c463162cd83114dd89a4cc4c1462298b1105374b43ba5a15d297b0d27d85c52c2d185d291b0926d7495ec1c9f60914b044618215eba4a36040a2f98c580028,
  0xdaa296fc0e76a6a7be05cdec2ced497f6a49bb513eddc1c6e958b758c1ba46eda827ee117b71071b8353da826ed958b6d8c1b606eda821ed41040126fb3359d9c266cc166e98bfadb4ad6da4eb6d2361099adb46d6d236bc4d35b28dae04cd6c24dd314ee96bdab561d592f6ac0a6e96a7a8b46d4d1a6a251b5109399c51d3eb066693f4d6b999a4bd2230690173498a1a4050ccd23e8a93345081a0b54d04146849134104999a43,
  0xee01df7c533b806fde03cee4a27740d3b9049dc033e962976c0e7a56a7d2a3ee94a6f640e3afac5d8460ebe3774a13fab8bdd6038eada9f4a137a7ac5d4460e9c3774a10fa508200a37e69a4f34d179a48bcd23fe691bf38d3f9d0b9ce347e6824f341140129fc835ee41a972c167904bfc8235e40af7200e7916a5c80350049fed517b8d073b5453e011ff008df8007fc414ce001df0c9338006fc203ce04a27040d381069c0033,
  0x7de917ef28bf7849fbc22802d3fd66bbf594dfac26fac8dfd646bf324df991afcc137d626feb135f8ca67bcd17e1299ef245f781b7bc09bd6077eb039f6126fb08d7d829bec135f581bfac0d401687e8349f41a2fa0517d0093e804500527f90d7bc86a5e425ef209af900e7c96a5e40350051ff4b17bc5073d2c53ee09ff704dfb807fe014c
]

def F_193 := shardForest fd_193 10 11

def ld_193 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0xd60d60d03d00ce1ce0ca2ca0c81c80c61bc5bc0bc0bc0ba1b62b41b40b40b02aa3aa0a81a42a40a40a40a40a219a49a09a08e68e08c18c08c08448408028007c27637607417407407027006a36a05e65c15c05a1562560541540540296033001 0x7f1483e8a01ea4c0e5b0073580372d81ba600d49e0775b83aac41c3620d8b70685883009018c5f0be29850d80226a01583c09db0058d202a090110480a22e84f1442205012a4f0912584691c2148616c5f0a62984cd48206a00fb48079a00245401b69008960068a4032120102a007930054a701e508168a407152050a0024d20108a0079400462881c9180d2520e45f0622982e9781348c0615202c18010170084b004b5a01c2f00a0f0808be39c531c1af8dcd3c6968e3425e195298989484b49c2224b1012507891833486192420b91d03a8d80a26c0112e0182980812c0308601019fb9a7faad0fcf49fe3a3fe911bf3253f8f27fb4937ba093d9813e3e0870983f7941db860dd250668602b2701390406c0102e0001f 12 5 11 10 6,
  unpackLinksF 0xd80d61d60d22cc3cc0c82c80c04c00bc29b19a09819429218e28e08648417e37647607227016656606606605a65a05815615605414c44c04824614224204203c33c03823803613032e12e01aa1a01811801801231200e2083080061060003000 0x691b06ad307c498321601e41c0ea0d0634c03c9440c11d0548d81926c3b82e188b00ea0d0674c230a601292c8849603a4a23fa4a1f9248fa9207b48c1a2410bd1d0528d87a28c0c1361e0250ec1207408c392481c62c82e4d0604c037c6e17d310bc9806d4902e2400589a02a490144683595e170a90d95885b4c43525004c9a092da0396c02425819eb088ed68386a43315e0d0a90c89181146c2d15d158aa8c61286208c3046c0411a01e8d05eac007234174ae0b85405aac02c15814ca20b0970462d82b460155ae0a45005329828934144a20a4950372d828144035a20c31445f69e2db470311b0b253c572962a14713ca189c4ec4d26e24b60126b008c9b0482b8232600d52c095588476c42296e10ca3085148412bc04853 12 5 11 10 6,
  unpackLinksF 0xc41be3b64b60b60b41b02b00ae1ae0ae0a64a60a41a409e39e09a29a09629609609228c38c08067e17e07c17827807617607604b64814804804234204014003c23a13623603603603413023003003003002e12e02e02e02e02a20b00a0005000 0x1524d0bf4bc5f2522a09a187588c06c45eb5029c92174120bb8be5cc532c9a816cd20b14c05aa482d024164d20b18a2559462c097158540a9260564502a4a0154538a928456c522aca9150500b78be59c532bd2915c578a728c5303028c2e146d60a48b45105e2802621517cfd8a67e35e3e5a99ccd48e569c6f34b369a51acd18cd686663422751f19257cc529e5e1472e09e83a4d4a524a5085327c2593c10c9d05242836268a31321188406c4bc59256371201b88f0d849d622383711f1809047e472372262910b17c848a64dc5f2622992cd7c9469e493472452f0044948d0bc4605222c271141288808c438422181d1060d80204a40a590ed208628e82d46c0e136 12 5 11 10 6,
  unpackLinksF 0xc62a51a40a029e19459409409408868808428217e27e07e07837807427407216c36a16a056a5605415405404e34e04a24434404214203c33c03c03c03633603413403023002e12e02c12252202202011c21a11a01811421400c40a10a0024001 0x7b2603fc9a1f6d84f56c072359371ac1a8d45096948434941da420ad18ce682822462e49e8524d4b324a8104a400241fc118e38d069c60389ac1f7584e18b4694523e92f19c948f868c7a25d3c12a9624d4f70947b0463d2b01e4960ed4887935c381361e1180ec4807795c3b5261d6490eb48876354345361d4490b02887ac513cd279e292cee48e74a43318a798051caf26a7412f39c939c7180e3ac07036c3892e1c0d80cf6b072562386311be9b8dd48c6e45236d2f14814cd98a46c45035ca61a7180d3ac068a6c345b019e930d5adc6a56234a311a09b8ce4c465b4832a2c95c490c76c063c6c3223718cd88c26c0623482f9a015a490ac268615603052e17c940ab26855124 12 5 11 10 6,
  unpackLinksF 0xd81d23c85c80c61c41c21c20bc3b82b80b80b80b42b40b21ac3ac0aa1a05a009e19e09e09c163d6016006005a35a05a05815805425214e24e04e04c14824804804804804614604604604222302201851801801611601220c30c0082080004000 0x9fb405009ea624d53e24aa124d4d922a828d53d2a8960264eda9268551332a89c4604c4aa26e1312f2a8968344cda8264d01306809a23a4c51b25e4d92d2689cb4a4d9a326a9192e2a8960464a92924e511c28bce04526f9afb7ad1dbb4bedd2476591bb245798a2a4a194d498a531051d8628cc2145568a213c4dc0324ea705e514292881394309a8803a4f01ba740d887054958274a4132500792603a8782648ca32441190e04c8fc59476372321b9180d88dd6245c372311811927e8b93744a2921f17d0e8a69245f48629a40d791e4be8e24f4692393a4d5160bc8a852450272261291108c880422741a90c0a90d04c85b59355a09764f42d26a5b9252d49a99ed31062987c26040c1c1fe0d0f76c081a442e89e8544d4b424a8083e 12 5 11 10 6,
  unpackLinksF 0xb61596b0533a6140e804d39a1306604b1907202404808e2fe1f83e17c0f45e0b0c600c01802e25c0b81702e05c0b8161275396700c99902c6580b01602c0580b01061a6340680c11622c03a0700e010c2003104200800000 0x3028fd8046ebf93f5f89baee49d7529abe1455ac92aea9357a48ab49265d1a82f0d216e680bb3485bc982e91416e480b98245bc122d8d397049cb72425a8a727e0d55d05a990254c00aad88c16a460aeb405de292ead79726a4b8b415b5a02d6979692bcae04d5a01ea620d53e04a9781559527ac890d5e690aeb405891fac28dd6027eaf93757093b06d3982686beb425ed27af253d6724eb303f58c1f2b60f53d04e97017554a6ab25155224aaaa4d55d22aa2499556d8aa35054da42a49b1512d8a803c5612eaac5754f24ea60340ac1a29b1814b8b0a514c524262908dd47068a302449ca22805513e2a896824 11 4 11 10 5,
  unpackLinksF 0xc25c20be2b45b40b02b00a84a80a23a01a009a38e68a28a08a07e67a27627227207206e26e06e06e06e06266206205e25e05c15c05c05c05065004c21d81c01c01821421401211201201200a40a0062060041040021020001000000000000000 0x1b54badfa556ad1aaf6511580d8bd14455c2e36ad75bc6aad52365e4a22ac1b1a6298ce04c6d230371161a5298cd84c5d4a22aa1b1b60a8d98346ce2832214173088da560640b02e45514d0c0aa03c6c81a352571a12a0d7b5e654af31e549530bca58526b81ab50571a02a0b5944548362d2511510d8d4c586a22834d179a58a4d235e5402f294149a306ad0c58682282d05519c8bccdc52669af2a8d49940bcc68526603626e131b9adcdbd626d637363189b08b2d6c586b228b56db9aa4dcc996e630b12ce551a729cd114c67ca129e1b9480c4cf04e67426b321313608acb8425041aa6a09595690ca03c60da632649d91068c846063e2c31c5318d098c623762ca231217187098c284c 12 5 11 10 6,
  unpackLinksF 0x8b0458228312189044822411208904215e56f01770bb05d80ec07413985cc0e607113881c40e016e12bdd582aa1540a985482a214b325812828c446022850488204009e10ec27223809c00d086613209884b0a56129114049843c81e00e847020d60410200084002 0x3ee0f1f6078fcc527e1af3ded49f74bcfb15e812b14051b9ff8c4ff4517f6283f8db9fb4dcf706e7e8273ea131e703cc484461c1a30a111f06c0f7b507b893bd7149270609b84c79d1ba4e512128bd0845382a29410d7e064befa2377cca7be4539f129ae2145498a113e4dc0424ef685e7b0293d4119c408a8983a7a41b1140a9e804cf301e4980eb060c182080c0850600282fe1417e0a0f123f7851bbc04fddf26eea9275f4202f80c1d32baee15572892af60c17a060e9a5d7652ab9049979060bc040749b03acd21cd680bb8505d8203a916175060ba05074ab03a2971cd4a0b90405c4282e00c16e080e5b5e7392f39a949c92bcb68405b0183969016b060b5030725202d20c1d5ac4e9b6e741b139ed45cc6a0e526e720b72ce101274789381c7922f3c714dde8a4eeb53711a7250d35db4beed24d35922bb057dd729a1e14571c93b8c14dc509ca204d7141f3880e588066c303261018ab40c1b946ec194c6dd1bb825117c288ac86c 13 5 11 10 6,
  unpackLinksF 0xb99b61b60b60b03b00ae1ae0ae0a83a80a61a60a22a20a01a00a009849809809808e58e08c18c08a18a08a074b7407407217207207206c36826806616606415c42f72e02e02c12a12812802802421c41c01631601031000a30a0081080080004 0x164b4fae5a3d6c93ea648f43237a14aec3c53e1429ce3147628a11424dc0624f4285d9f827cde139ec095330479942328a109150752b0379541b1180aa4004f1f8268c493c5e5763b2ab131258e5ae45e976364ab121268d1ae45cd82296a1183548ba364529222d4890e86089daf45497a294a51295e8702944e8e22547118c6e79e2f45edba2c6c515b498a1a444c9ba242dd0d06288c194440c21f0890eb60871a44360f21804d0b0168602242c1121a24f0c83585c13c2a05e3d6bd1e352799a7286d363a4bf1c2473951ec6e8d6352bf1994712c9ec644d62124f1005e87829c28149f3096f904a7c424b8a11943082e28367a81ac221120d089060448351ac184d60f68f072478111bc1611a024bb04a557f11ac04d76076aafda368063040b161f909901854806b03e01b1ef07900034 12 5 11 10 6,
  unpackLinksF 0xaad542a8514a214426a4d09a12ca584b09612c22b405801002003e27c0f81f03c2654c0978af05e0b49682a3540a45392704e094928241354680c89903205c8b81702e0548a81232223c8780f01a4340608c016228405000 0x506d568268b402559fd22cb20da4604d3eb4e9f0a6cea5167324b3d34e9e526cea9167224d3b450531a64eed82756a93a3489cd2a4e4552710793da459e0a2ce049ca204e038179b2b04b00d268ac1228249b9aecc2d566d69b35b459a92eca29566949b33a4595c1b488099eb8a4c583096c2e4c6972620b930560968264b0112430492ec60908124b6d625a4a92c2449922d4c315a5f6ad2f24d93522cb88d6172bd2c85e95c2b48209a480b929b5c9482e49f1624e0992656091c2648a11243089254609081a490962472a92294490da84844d2546b528b56941a549ad1a4b4ad24a46854af48c17a440ad20846 11 4 11 10 5,
  unpackLinksF 0xf01f00f00ee1ec1cb1ca0ca0c43c02c00c00b46b21b20b01b00ae1ae0ac1ac0ac0aa1a818718228208208017087006a36816806236016005845615604e44e04c14c04634604414404404404214204013843803420d40c00c0082061060022001 0x15fd60a6892cc4172c8ac362d60b112ed389569946b6115eb00ae57c54abd0bd5e05daec2e4c2156ba0a54184d9ec264d61165f06b5c3459a42ad6e116b02d956160a611b56852ab328d4085d9a02ac98096790b958560ab822d595829724d2905cad6b0d65582b16bb4e355a591b55e57aad2b955952aa82f552176a80b928855a9c29500136780993384592c12d2a572912a151b50874af32054aa4275511369dc2f29a14a5d08b2502563ca8296142a00693b05ca7ab053a172750994683ca6eb0534172730994603ca2c1e531582970b93904ca281e52b1827109ca5042a4c1ad231828d8a145c50a312351451a1b09cc7042a202e49c132a58c350c60a7e2d53915a996ad4b256868af31854a9429d4914ca40a14e0179480a54784ea3826d121324d08b438429701ac9209684ac12d0349882e503582470492905c 12 5 11 10 6,
  unpackLinksF 0x830408a040fe27f03e89d8eec07413a01c46e016b2b4899c4cc16603285940c81595ab0ce7a7013801c00e006e13701b80dc06453201900c426203101880b0a5802a11500a8050228013849c04e02700fa03a21c00e0058c24412009001980820400108080002000 0x350142fe0517e360939ac5f4d613769180c62bfe2d5fb14afb6dd7cb5ea503134e14af70b0d3040bd5a234a1414a080d2032bda2fde914ef36bd4905268821522582ee0d8d0950bb02e340542ee6c176358bc6315e116aef8a56716ea40b14465799f2a57686ea1c315d6179970a51114e2989a016493658bfad453d65af6aad4f326a598b4eca5a5e48d2b1b68d88343c3da161c97b0a48d8415ec0ca359a17e860a71084f7d025b8e11d960877c03fbc81e90c0e41d06b75033ba41894a0940a02b6b127b909adc5166e129b68945b4092dc010add46b6dc59b6926da2916cf24d6c842b51ac5aed22d48b0ca840b4a305ad166d56b369b4ab45a35a091acf28cc9842b381950b175e469b73b49b99a2c78d04fc49b72a45b8d1fdbe8dc6829b6f145b709fdb04decd24f428518801f3240cacb48b36855b2822d865b2bf2c14da35b1ca558c51a840bb360559801acf8132c3ac160845 13 5 11 10 6,
  unpackLinksF 0xfe3f4be87b2ee9d87b0733e61c8788ed4bfd7c2f0de0bc16ced8592ae541e805009a73063ac528a114228441809002003a6740e45c83726e0d85b0360684cc545a533ec7c0e19c02cc580831001a6340680760e010c20004 0xce0125485833e27951850ce418678d633b6a151060cdc102de093394819a844ce0162de4c3350499b934bb83666c173340a9a8451d3927e9892f4748fa0243a8428c5813dff096e80476c421e7e0bf3d0579d027ccc11e5f1832fac19636ccb92e658d83146b18014c4dc2666158b2d8c595a6e6c028dfe136f008395029ca12364e1254b082d7831c9a2964a97ad30bf4f8536b420da41769e0a33b05cc881fe420ef2006f8f833c8e2963d142d10bf4e053c7426638103188c18c560c593662cd831449989828bf8a66355bb19ac58bc62c5537624989fe0b2d6051bf426dde10711052cb821c2da260a511fd093821368981fbf80edca06ed583305c0ae1a4fa9b0a20b015c32296168c3092bd6805fa64298260570926d1203f7ec1db900ddaa06657015c1c9f530144ad02b83452c151860857acf0bf4b05329c0adf91b2950c181028bea2e26e911a90a180028 11 4 11 10 5,
  unpackLinksF 0x940c90a4812218f1468a3411a08a1c5022050a385042821030237f13f81f82f2579031d98c0c606112ca1640b205522a814c4a22500a70938090634a1810b845a12c0912884242020090006103001610a844c424112009004041840c005842061000708304088002 0x1b895cdc02eefc0e77c0b982124dec2cdb417eb10a7bad6cac0306ee0e3758c129458ddab16e91baaf0c5b8838dca2f6e0d4ead0a556160db4366db1836eac56c96eaacb16d81baa70c5c745ee3229eff14b7d6a7bd25fde526e369177829dbc13ec0c935b017ea60a7b984fdbc269141243c08bb5843da820c660fdba0668d02b2f013dee53367099b4359c69a0ecc165b90837b03d0b41a96e0941c02b028496e02096c0d41b02b8a34cd84266a89835e269a9950d49306bc4d3518c193c580a8a21684d019249ae04cd61b0ea0d83306b393358c65a8ec8d2b63693b1348d81a3624d075f48dae9468102cb6e1475b092a4041bd01e8520d4b304a0c0158bc1fc040edd306eda833cbe346311832e6b18114cd62b0e5b16b178a5aba5ec492954a1870109b78841d5814d0e08753269a9a34d51a369e9774b4aba91468042cb6814751092a6841d3eb069a96346489a6b5ccb136692143498a1a2a40d2e306889034a0b9a40505bc1268c93345081a10245bc98684913446a98b26cd0c14682092fc4d99f038 13 5 11 10 6,
  unpackLinksF 0x9804a8e54126293049063c70aa840c10a0810028003e8df40f62781bc01e00ee1741b909c80e216c2b6015aca8254028113c29a24d026813029424a01ad4cc46603301904c046003001800bc23f01f00f0464a3011800b08542262130080c4001c20e0068428600a 0xef8a658c183bb061de03cee80a7740d3bb289d406cee4127864ffc226f86125b1428f820ffbf077de837ee01992606c6c02fd615ceac2ef6c0e6e10bf62053ec2b6586183b2071d846098a2c76358baf8dd61062eb01c75b17bab6a760052afcb07501b3a88c1d4d62b80b757c58ba70dd5d062f1a2f78914fb78a5dab53ed1277688fb9f2bfd994dc6ca2e14496df0bf5c853eb827f54135130926b045e9821f4a1063807ede8332480d8d205d1f056650278d81fc0e0edd906ede033e782ce124939c0b3ce85ce79a7f38d1f8e69bd1b49e89a2f2ed075949bd0a45e811ff3e8df9327d841261a026f361279a08a460418d41fc0c0edd806edd8334781599209c910328e82b32013f2c166dd0bf5c053e45a9730d7b976a5caa5fcc51ef288d7932bdbc146de09b5b817eb60a62583de481cf200d4870628e02b31413eee572b50c3bb05ddb828f1a0e6a706383924dd5b6710123840695a160e20a670c932b30c1c1830e101e70409382069c1944db4367020d38b47fc5237c18935641478907fc383be141bf000cd1b05661827 13 5 11 10 6,
  unpackLinksF 0x9f04f827833c08d8c6823411818254102081021800bb29d80ec07413a01c84e21700b51994aca0640b2018c2b2a5711f64f047803821b08d804351f10f807c03a21d00e807021900c0058418a0a10500188082002 0x6cc8dfed8bbf6b51f1926fe49178e29bf8945d9493bc8137f0093f78457b020c240e5c20629202b4281393606c8002ff1838fb0a6ec0517e726baf92583c2cfd61350508bf1039f681aa080975e249f0838fa126ec0917e746bae9268382cfcc1347b08bf0039f601a8f4057e329881934f84a60f2490cf6901aa48f89a2fc09150226c3c126f7c1b7bc09bb668fbf247d6d1ba004d87624c7f8241d40a7b69350548bed235f64a68f6517d826a9182a3f8131340687402cf5b52704207db177ed6bbdaa47f351efd48dfe946bbe947e5c9efca4dfe426bad12784025c14125dd08ee00418f01efba0efdc073eb837f581aa8a0c5210567e8272600d8e605c97036388178ec1fc120eddc06edf833e5927ef691fc669bea349f4da2f9ad07cc47dac94df48a2f2a4ff7a26f871253f026fa2127d008a8a8418e81fc100eddb06edf0334801492c06c7002e4a81b1bc0bdc817ecb0a7e4b52f39af79ad4bcc4bdda246ed11b74057f3127be5935b8c2fd9214ce507be5039f201aa200c49403637017ec8ae590187b10bbd4851f141cd740c70d249d836cf00247780d2c72c1e014c 13 5 11 10 6
]

def L_193 := shardLinks ld_193

def st_193 := dagTraceF m_193 s_193 9 F_193

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_193 : dagCheckRootsF m_193 g_193 b_193 (dagRefF 1011 st_193 L_193 0) s_193 9 = true := by
  decide +kernel

def ck_193 := dagCheckNodeF m_193 g_193 b_193 1011 st_193 L_193

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_0 : treeBlockF 0 16 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_16 : treeBlockF 16 32 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_32 : treeBlockF 32 48 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_48 : treeBlockF 48 64 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_64 : treeBlockF 64 80 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_80 : treeBlockF 80 96 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_96 : treeBlockF 96 112 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_112 : treeBlockF 112 128 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_128 : treeBlockF 128 144 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_144 : treeBlockF 144 160 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_160 : treeBlockF 160 176 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_176 : treeBlockF 176 192 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_192 : treeBlockF 192 208 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_208 : treeBlockF 208 224 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_224 : treeBlockF 224 240 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_240 : treeBlockF 240 256 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_256 : treeBlockF 256 272 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_272 : treeBlockF 272 288 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_288 : treeBlockF 288 304 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_304 : treeBlockF 304 320 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_320 : treeBlockF 320 336 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_336 : treeBlockF 336 352 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_352 : treeBlockF 352 368 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_368 : treeBlockF 368 384 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_384 : treeBlockF 384 400 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_400 : treeBlockF 400 416 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_416 : treeBlockF 416 432 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_432 : treeBlockF 432 448 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_448 : treeBlockF 448 464 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_464 : treeBlockF 464 480 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_480 : treeBlockF 480 496 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_496 : treeBlockF 496 512 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_512 : treeBlockF 512 528 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_528 : treeBlockF 528 544 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_544 : treeBlockF 544 560 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_560 : treeBlockF 560 576 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_576 : treeBlockF 576 592 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_592 : treeBlockF 592 608 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_608 : treeBlockF 608 624 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_624 : treeBlockF 624 640 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_640 : treeBlockF 640 656 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_656 : treeBlockF 656 672 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_672 : treeBlockF 672 688 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_688 : treeBlockF 688 704 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_704 : treeBlockF 704 720 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_720 : treeBlockF 720 736 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_736 : treeBlockF 736 752 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_752 : treeBlockF 752 768 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_768 : treeBlockF 768 784 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_784 : treeBlockF 784 800 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_800 : treeBlockF 800 816 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_816 : treeBlockF 816 832 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_832 : treeBlockF 832 848 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_848 : treeBlockF 848 864 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_864 : treeBlockF 864 880 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_880 : treeBlockF 880 896 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_896 : treeBlockF 896 912 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_912 : treeBlockF 912 928 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_928 : treeBlockF 928 944 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_944 : treeBlockF 944 960 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_960 : treeBlockF 960 976 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_976 : treeBlockF 976 992 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_992 : treeBlockF 992 1008 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_193_1008 : treeBlockF 1008 1011 ck_193 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_193 : ∀ j, 0 ≤ j → j < 1011 → ck_193 j = true :=
  (block_join (block_join (block_join (block_join (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_193_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_193_16 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_193_32 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_193_48 h1 h2))) (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_193_64 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_193_80 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_193_96 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_193_112 h1 h2)))) (block_join (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_193_128 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_193_144 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_193_160 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_193_176 h1 h2))) (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_193_192 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_193_208 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_193_224 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_193_240 h1 h2))))) (block_join (block_join (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_193_256 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_193_272 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_193_288 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_193_304 h1 h2))) (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_193_320 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_193_336 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_193_352 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_193_368 h1 h2)))) (block_join (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_193_384 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_193_400 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_193_416 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_193_432 h1 h2))) (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_193_448 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_193_464 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_193_480 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_193_496 h1 h2)))))) (block_join (block_join (block_join (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_193_512 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_193_528 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_193_544 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_193_560 h1 h2))) (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_193_576 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_193_592 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_193_608 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_193_624 h1 h2)))) (block_join (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_193_640 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_193_656 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_193_672 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_193_688 h1 h2))) (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_193_704 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_193_720 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_193_736 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_193_752 h1 h2))))) (block_join (block_join (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_193_768 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_193_784 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_193_800 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_193_816 h1 h2))) (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_193_832 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_193_848 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_193_864 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_193_880 h1 h2)))) (block_join (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_193_896 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_193_912 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_193_928 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_193_944 h1 h2))) (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_193_960 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_193_976 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_193_992 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_193_1008 h1 h2)))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_193 : LowerBin m_193 s_193 g_193 10 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_193 sub_193 goal_193 rc_193 nc_193

def m_53 : Nat := 0xf0000000f000000

def s_53 : List Nat := [0xf000000, 0x300000003000000, 0x500000005000000]

def g_53 : Nat := 0x100000007000000

def b_53 : List (Nat × List Nat × Nat × Nat) := []

theorem known_53 : KnownBin b_53 := by
  intro b hb
  simp [b_53] at hb

theorem sub_53 : ∀ b ∈ b_53, m_53 &&& b.1 = b.1 := by
  intro b hb
  simp [b_53] at hb

theorem goal_53 : ∀ b ∈ b_53, canon b.1 g_53 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_53] at hb

def fd_53 : Array Nat := #[
  0x7
]

def F_53 := shardForest fd_53 1 3

def ld_53 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_53 := shardLinks ld_53

def st_53 := dagTraceF m_53 s_53 3 F_53

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsF m_53 g_53 b_53 (dagRefF 1 st_53 L_53 0) s_53 3 = true := by
  decide +kernel

def ck_53 := dagCheckNodeF m_53 g_53 b_53 1 st_53 L_53

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_53_0 : treeBlockF 0 1 ck_53 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_53 : ∀ j, 0 ≤ j → j < 1 → ck_53 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_53_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_53 : LowerBin m_53 s_53 g_53 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_53 sub_53 goal_53 rc_53 nc_53

def m_59 : Nat := 0xf000f0000000000

def s_59 : List Nat := [0xf0000000000, 0x300030000000000, 0x500050000000000]

def g_59 : Nat := 0x100070000000000

def b_59 : List (Nat × List Nat × Nat × Nat) := []

theorem known_59 : KnownBin b_59 := by
  intro b hb
  simp [b_59] at hb

theorem sub_59 : ∀ b ∈ b_59, m_59 &&& b.1 = b.1 := by
  intro b hb
  simp [b_59] at hb

theorem goal_59 : ∀ b ∈ b_59, canon b.1 g_59 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_59] at hb

def fd_59 : Array Nat := #[
  0x7
]

def F_59 := shardForest fd_59 1 3

def ld_59 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_59 := shardLinks ld_59

def st_59 := dagTraceF m_59 s_59 3 F_59

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsF m_59 g_59 b_59 (dagRefF 1 st_59 L_59 0) s_59 3 = true := by
  decide +kernel

def ck_59 := dagCheckNodeF m_59 g_59 b_59 1 st_59 L_59

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_59_0 : treeBlockF 0 1 ck_59 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_59 : ∀ j, 0 ≤ j → j < 1 → ck_59 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_59_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_59 : LowerBin m_59 s_59 g_59 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_59 sub_59 goal_59 rc_59 nc_59

def m_141 : Nat := 0xf000f000f000f00

def s_141 : List Nat := [0xf000f00, 0xf0000000f00, 0x300030003000300, 0x500050005000500]

def g_141 : Nat := 0x100070007000f00

def b_141 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 4, g_17), (m_35, s_35, 4, g_35), (m_53, s_53, 4, g_53), (m_59, s_59, 4, g_59)]

theorem known_141 : KnownBin b_141 := by
  intro b hb
  simp only [b_141, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_17
  · exact lb_35
  · exact lb_53
  · exact lb_59

theorem sub_141 : ∀ b ∈ b_141, m_141 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_141, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

theorem goal_141 : ∀ b ∈ b_141, canon b.1 g_141 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_141, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

def fd_141 : Array Nat := #[
  0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f
]

def F_141 := shardForest fd_141 6 10

def ld_141 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x8e11c1fc3f07c2f81b43606c0d45a0b40662cc15c2b0542a8148a18420841009f13e0784f01d12b0540a814128050098921222440809001e21e00b001 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d347d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 11 4 10 6 5
]

def L_141 := shardLinks ld_141

def st_141 := dagTraceF m_141 s_141 6 F_141

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_141 : dagCheckRootsF m_141 g_141 b_141 (dagRefF 43 st_141 L_141 0) s_141 6 = true := by
  decide +kernel

def ck_141 := dagCheckNodeF m_141 g_141 b_141 43 st_141 L_141

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_141_0 : treeBlockF 0 16 ck_141 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_141_16 : treeBlockF 16 32 ck_141 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_141_32 : treeBlockF 32 43 ck_141 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_141 : ∀ j, 0 ≤ j → j < 43 → ck_141 j = true :=
  (block_join (fun _ h1 h2 => treeBlockF_at nb_141_0 h1 h2) (block_join (fun _ h1 h2 => treeBlockF_at nb_141_16 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_141_32 h1 h2)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_141 : LowerBin m_141 s_141 g_141 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_141 sub_141 goal_141 rc_141 nc_141

def m_57 : Nat := 0xf0000000f000

def s_57 : List Nat := [0xf000, 0x300000003000, 0x500000005000]

def g_57 : Nat := 0x100000007000

def b_57 : List (Nat × List Nat × Nat × Nat) := []

theorem known_57 : KnownBin b_57 := by
  intro b hb
  simp [b_57] at hb

theorem sub_57 : ∀ b ∈ b_57, m_57 &&& b.1 = b.1 := by
  intro b hb
  simp [b_57] at hb

theorem goal_57 : ∀ b ∈ b_57, canon b.1 g_57 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_57] at hb

def fd_57 : Array Nat := #[
  0x7
]

def F_57 := shardForest fd_57 1 3

def ld_57 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_57 := shardLinks ld_57

def st_57 := dagTraceF m_57 s_57 3 F_57

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsF m_57 g_57 b_57 (dagRefF 1 st_57 L_57 0) s_57 3 = true := by
  decide +kernel

def ck_57 := dagCheckNodeF m_57 g_57 b_57 1 st_57 L_57

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_57_0 : treeBlockF 0 1 ck_57 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_57 : ∀ j, 0 ≤ j → j < 1 → ck_57 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_57_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_57 : LowerBin m_57 s_57 g_57 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_57 sub_57 goal_57 rc_57 nc_57

def m_69 : Nat := 0xff0000000000

def s_69 : List Nat := [0xf0000000000, 0x330000000000, 0x550000000000]

def g_69 : Nat := 0x170000000000

def b_69 : List (Nat × List Nat × Nat × Nat) := []

theorem known_69 : KnownBin b_69 := by
  intro b hb
  simp [b_69] at hb

theorem sub_69 : ∀ b ∈ b_69, m_69 &&& b.1 = b.1 := by
  intro b hb
  simp [b_69] at hb

theorem goal_69 : ∀ b ∈ b_69, canon b.1 g_69 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_69] at hb

def fd_69 : Array Nat := #[
  0x7
]

def F_69 := shardForest fd_69 1 3

def ld_69 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_69 := shardLinks ld_69

def st_69 := dagTraceF m_69 s_69 3 F_69

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_69 : dagCheckRootsF m_69 g_69 b_69 (dagRefF 1 st_69 L_69 0) s_69 3 = true := by
  decide +kernel

def ck_69 := dagCheckNodeF m_69 g_69 b_69 1 st_69 L_69

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_69_0 : treeBlockF 0 1 ck_69 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_69 : ∀ j, 0 ≤ j → j < 1 → ck_69 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_69_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_69 : LowerBin m_69 s_69 g_69 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_69 sub_69 goal_69 rc_69 nc_69

def m_167 : Nat := 0xff000000ff00

def s_167 : List Nat := [0xff00, 0xf0000000f00, 0x330000003300, 0x550000005500]

def g_167 : Nat := 0x170000007f00

def b_167 : List (Nat × List Nat × Nat × Nat) := [(m_25, s_25, 4, g_25), (m_43, s_43, 4, g_43), (m_57, s_57, 4, g_57), (m_69, s_69, 4, g_69)]

theorem known_167 : KnownBin b_167 := by
  intro b hb
  simp only [b_167, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_25
  · exact lb_43
  · exact lb_57
  · exact lb_69

theorem sub_167 : ∀ b ∈ b_167, m_167 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_167, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

theorem goal_167 : ∀ b ∈ b_167, canon b.1 g_167 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_167, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

def fd_167 : Array Nat := #[
  0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f
]

def F_167 := shardForest fd_167 6 10

def ld_167 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x8e11c1fc3f07c2f81b43606c0d45a0b40662cc15c2b0542a8148a18420841009f13e0784f01d12b0540a814128050098921222440809001e21e00b001 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d347d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 11 4 10 6 5
]

def L_167 := shardLinks ld_167

def st_167 := dagTraceF m_167 s_167 6 F_167

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_167 : dagCheckRootsF m_167 g_167 b_167 (dagRefF 43 st_167 L_167 0) s_167 6 = true := by
  decide +kernel

def ck_167 := dagCheckNodeF m_167 g_167 b_167 43 st_167 L_167

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_167_0 : treeBlockF 0 16 ck_167 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_167_16 : treeBlockF 16 32 ck_167 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_167_32 : treeBlockF 32 43 ck_167 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_167 : ∀ j, 0 ≤ j → j < 43 → ck_167 j = true :=
  (block_join (fun _ h1 h2 => treeBlockF_at nb_167_0 h1 h2) (block_join (fun _ h1 h2 => treeBlockF_at nb_167_16 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_167_32 h1 h2)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_167 : LowerBin m_167 s_167 g_167 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_167 sub_167 goal_167 rc_167 nc_167

def m_27 : Nat := 0x5500550000000000

def s_27 : List Nat := [0x550000000000, 0x500050000000000, 0x1100110000000000]

def g_27 : Nat := 0x100150000000000

def b_27 : List (Nat × List Nat × Nat × Nat) := []

theorem known_27 : KnownBin b_27 := by
  intro b hb
  simp [b_27] at hb

theorem sub_27 : ∀ b ∈ b_27, m_27 &&& b.1 = b.1 := by
  intro b hb
  simp [b_27] at hb

theorem goal_27 : ∀ b ∈ b_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_27] at hb

def fd_27 : Array Nat := #[
  0x7
]

def F_27 := shardForest fd_27 1 3

def ld_27 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_27 := shardLinks ld_27

def st_27 := dagTraceF m_27 s_27 3 F_27

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsF m_27 g_27 b_27 (dagRefF 1 st_27 L_27 0) s_27 3 = true := by
  decide +kernel

def ck_27 := dagCheckNodeF m_27 g_27 b_27 1 st_27 L_27

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_27_0 : treeBlockF 0 1 ck_27 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_27 : ∀ j, 0 ≤ j → j < 1 → ck_27 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_27_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_27 : LowerBin m_27 s_27 g_27 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_27 sub_27 goal_27 rc_27 nc_27

def m_45 : Nat := 0x3300330000000000

def s_45 : List Nat := [0x330000000000, 0x300030000000000, 0x1100110000000000]

def g_45 : Nat := 0x100130000000000

def b_45 : List (Nat × List Nat × Nat × Nat) := []

theorem known_45 : KnownBin b_45 := by
  intro b hb
  simp [b_45] at hb

theorem sub_45 : ∀ b ∈ b_45, m_45 &&& b.1 = b.1 := by
  intro b hb
  simp [b_45] at hb

theorem goal_45 : ∀ b ∈ b_45, canon b.1 g_45 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_45] at hb

def fd_45 : Array Nat := #[
  0x7
]

def F_45 := shardForest fd_45 1 3

def ld_45 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_45 := shardLinks ld_45

def st_45 := dagTraceF m_45 s_45 3 F_45

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsF m_45 g_45 b_45 (dagRefF 1 st_45 L_45 0) s_45 3 = true := by
  decide +kernel

def ck_45 := dagCheckNodeF m_45 g_45 b_45 1 st_45 L_45

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_45_0 : treeBlockF 0 1 ck_45 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_45 : ∀ j, 0 ≤ j → j < 1 → ck_45 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_45_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_45 : LowerBin m_45 s_45 g_45 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_45 sub_45 goal_45 rc_45 nc_45

def m_177 : Nat := 0xff00ff0000000000

def s_177 : List Nat := [0xff0000000000, 0xf000f0000000000, 0x3300330000000000, 0x5500550000000000]

def g_177 : Nat := 0x100170000000000

def b_177 : List (Nat × List Nat × Nat × Nat) := [(m_27, s_27, 4, g_27), (m_45, s_45, 4, g_45), (m_59, s_59, 4, g_59), (m_69, s_69, 4, g_69)]

theorem known_177 : KnownBin b_177 := by
  intro b hb
  simp only [b_177, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_27
  · exact lb_45
  · exact lb_59
  · exact lb_69

theorem sub_177 : ∀ b ∈ b_177, m_177 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_177, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

theorem goal_177 : ∀ b ∈ b_177, canon b.1 g_177 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_177, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

def fd_177 : Array Nat := #[
  0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f
]

def F_177 := shardForest fd_177 6 10

def ld_177 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x8e11c1fc3e17c0f81b43516a0d05a0340662cc15c2a1522a41482184027c4f81e13c0780e89d02b05049893024248088910220404801001e21e00b001 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b407c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 11 4 10 6 5
]

def L_177 := shardLinks ld_177

def st_177 := dagTraceF m_177 s_177 6 F_177

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_177 : dagCheckRootsF m_177 g_177 b_177 (dagRefF 43 st_177 L_177 0) s_177 6 = true := by
  decide +kernel

def ck_177 := dagCheckNodeF m_177 g_177 b_177 43 st_177 L_177

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_177_0 : treeBlockF 0 16 ck_177 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_177_16 : treeBlockF 16 32 ck_177 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_177_32 : treeBlockF 32 43 ck_177 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_177 : ∀ j, 0 ≤ j → j < 43 → ck_177 j = true :=
  (block_join (fun _ h1 h2 => treeBlockF_at nb_177_0 h1 h2) (block_join (fun _ h1 h2 => treeBlockF_at nb_177_16 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_177_32 h1 h2)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_177 : LowerBin m_177 s_177 g_177 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_177 sub_177 goal_177 rc_177 nc_177

def m_85 : Nat := 0x5500550055005500

def s_85 : List Nat := [0x55005500, 0x550000005500, 0x500050005000500, 0x1100110011001100]

def g_85 : Nat := 0x100150005005500

def b_85 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]

theorem known_85 : KnownBin b_85 := by
  intro b hb
  simp only [b_85, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_5

theorem sub_85 : ∀ b ∈ b_85, m_85 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_85, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

theorem goal_85 : ∀ b ∈ b_85, canon b.1 g_85 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_85, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

def F_85 : Nat → Nat × Nat := fun _ => (0, 0)

def L_85 : Nat → Nat → Option Nat := fun _ _ => none

def st_85 := dagTraceF m_85 s_85 4 F_85

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_85 : dagCheckRootsF m_85 g_85 b_85 (dagRefF 0 st_85 L_85 0) s_85 4 = true := by
  decide +kernel

def ck_85 := dagCheckNodeF m_85 g_85 b_85 0 st_85 L_85

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_85 : ∀ j, 0 ≤ j → j < 0 → ck_85 j = true :=
  fun _ _ h => absurd h (Nat.not_lt_zero _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_85 : LowerBin m_85 s_85 g_85 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_85 sub_85 goal_85 rc_85 nc_85

def m_115 : Nat := 0x3300330033003300

def s_115 : List Nat := [0x33003300, 0x330000003300, 0x300030003000300, 0x1100110011001100]

def g_115 : Nat := 0x100130003003300

def b_115 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]

theorem known_115 : KnownBin b_115 := by
  intro b hb
  simp only [b_115, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_7

theorem sub_115 : ∀ b ∈ b_115, m_115 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_115, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

theorem goal_115 : ∀ b ∈ b_115, canon b.1 g_115 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_115, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

def F_115 : Nat → Nat × Nat := fun _ => (0, 0)

def L_115 : Nat → Nat → Option Nat := fun _ _ => none

def st_115 := dagTraceF m_115 s_115 4 F_115

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_115 : dagCheckRootsF m_115 g_115 b_115 (dagRefF 0 st_115 L_115 0) s_115 4 = true := by
  decide +kernel

def ck_115 := dagCheckNodeF m_115 g_115 b_115 0 st_115 L_115

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_115 : ∀ j, 0 ≤ j → j < 0 → ck_115 j = true :=
  fun _ _ h => absurd h (Nat.not_lt_zero _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_115 : LowerBin m_115 s_115 g_115 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_115 sub_115 goal_115 rc_115 nc_115

def m_145 : Nat := 0xf000f000f000f000

def s_145 : List Nat := [0xf000f000, 0xf0000000f000, 0x3000300030003000, 0x5000500050005000]

def g_145 : Nat := 0x100000007000

def b_145 : List (Nat × List Nat × Nat × Nat) := [(m_57, s_57, 4, g_57)]

theorem known_145 : KnownBin b_145 := by
  intro b hb
  simp only [b_145, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_57

theorem sub_145 : ∀ b ∈ b_145, m_145 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_145, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

theorem goal_145 : ∀ b ∈ b_145, canon b.1 g_145 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_145, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

def F_145 : Nat → Nat × Nat := fun _ => (0, 0)

def L_145 : Nat → Nat → Option Nat := fun _ _ => none

def st_145 := dagTraceF m_145 s_145 4 F_145

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_145 : dagCheckRootsF m_145 g_145 b_145 (dagRefF 0 st_145 L_145 0) s_145 4 = true := by
  decide +kernel

def ck_145 := dagCheckNodeF m_145 g_145 b_145 0 st_145 L_145

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_145 : ∀ j, 0 ≤ j → j < 0 → ck_145 j = true :=
  fun _ _ h => absurd h (Nat.not_lt_zero _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_145 : LowerBin m_145 s_145 g_145 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_145 sub_145 goal_145 rc_145 nc_145

def m_169 : Nat := 0xff000000ff000000

def s_169 : List Nat := [0xff000000, 0xf0000000f000000, 0x3300000033000000, 0x5500000055000000]

def g_169 : Nat := 0x100000007000000

def b_169 : List (Nat × List Nat × Nat × Nat) := [(m_53, s_53, 4, g_53)]

theorem known_169 : KnownBin b_169 := by
  intro b hb
  simp only [b_169, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_53

theorem sub_169 : ∀ b ∈ b_169, m_169 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_169, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

theorem goal_169 : ∀ b ∈ b_169, canon b.1 g_169 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_169, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

def F_169 : Nat → Nat × Nat := fun _ => (0, 0)

def L_169 : Nat → Nat → Option Nat := fun _ _ => none

def st_169 := dagTraceF m_169 s_169 4 F_169

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_169 : dagCheckRootsF m_169 g_169 b_169 (dagRefF 0 st_169 L_169 0) s_169 4 = true := by
  decide +kernel

def ck_169 := dagCheckNodeF m_169 g_169 b_169 0 st_169 L_169

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_169 : ∀ j, 0 ≤ j → j < 0 → ck_169 j = true :=
  fun _ _ h => absurd h (Nat.not_lt_zero _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_169 : LowerBin m_169 s_169 g_169 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_169 sub_169 goal_169 rc_169 nc_169

def m_173 : Nat := 0xff00ff00

def s_173 : List Nat := [0xff00, 0xf000f00, 0x33003300, 0x55005500]

def g_173 : Nat := 0x7007f00

def b_173 : List (Nat × List Nat × Nat × Nat) := [(m_29, s_29, 4, g_29)]

theorem known_173 : KnownBin b_173 := by
  intro b hb
  simp only [b_173, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_29

theorem sub_173 : ∀ b ∈ b_173, m_173 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_173, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

theorem goal_173 : ∀ b ∈ b_173, canon b.1 g_173 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_173, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

def F_173 : Nat → Nat × Nat := fun _ => (0, 0)

def L_173 : Nat → Nat → Option Nat := fun _ _ => none

def st_173 := dagTraceF m_173 s_173 4 F_173

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_173 : dagCheckRootsF m_173 g_173 b_173 (dagRefF 0 st_173 L_173 0) s_173 4 = true := by
  decide +kernel

def ck_173 := dagCheckNodeF m_173 g_173 b_173 0 st_173 L_173

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_173 : ∀ j, 0 ≤ j → j < 0 → ck_173 j = true :=
  fun _ _ h => absurd h (Nat.not_lt_zero _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_173 : LowerBin m_173 s_173 g_173 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_173 sub_173 goal_173 rc_173 nc_173

def m_197 : Nat := 0xff00ff00ff00ff00

def s_197 : List Nat := [0xff00ff00, 0xff000000ff00, 0xf000f000f000f00, 0x3300330033003300, 0x5500550055005500]

def g_197 : Nat := 0x100170007007f00

def b_197 : List (Nat × List Nat × Nat × Nat) := [(m_91, s_91, 7, g_91), (m_121, s_121, 7, g_121), (m_141, s_141, 7, g_141), (m_167, s_167, 7, g_167), (m_177, s_177, 7, g_177), (m_85, s_85, 5, g_85), (m_115, s_115, 5, g_115), (m_145, s_145, 5, g_145), (m_169, s_169, 5, g_169), (m_173, s_173, 5, g_173), (m_5, s_5, 4, g_5), (m_7, s_7, 4, g_7), (m_17, s_17, 4, g_17), (m_25, s_25, 4, g_25), (m_27, s_27, 4, g_27), (m_29, s_29, 4, g_29), (m_35, s_35, 4, g_35), (m_43, s_43, 4, g_43), (m_45, s_45, 4, g_45), (m_47, s_47, 4, g_47), (m_53, s_53, 4, g_53), (m_57, s_57, 4, g_57), (m_59, s_59, 4, g_59), (m_69, s_69, 4, g_69)]

theorem known_197 : KnownBin b_197 := by
  intro b hb
  simp only [b_197, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_91
  · exact lb_121
  · exact lb_141
  · exact lb_167
  · exact lb_177
  · exact lb_85
  · exact lb_115
  · exact lb_145
  · exact lb_169
  · exact lb_173
  · exact lb_5
  · exact lb_7
  · exact lb_17
  · exact lb_25
  · exact lb_27
  · exact lb_29
  · exact lb_35
  · exact lb_43
  · exact lb_45
  · exact lb_47
  · exact lb_53
  · exact lb_57
  · exact lb_59
  · exact lb_69

theorem sub_197 : ∀ b ∈ b_197, m_197 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_197, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem goal_197 : ∀ b ∈ b_197, canon b.1 g_197 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_197, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def fd_197 : Array Nat := #[
  0x3f2523096cf4948c24318482744f860ad9bb513727c3050c60a09156a332d845598c4b611466226a45cd4089291115e222ba5515888ae14568222aa4c57088a911145230884405860918ca441f0b834d50752a0d06c1b6883413064098c0560106e1d15c392d072560e4941c91838ad8714b0f8ae1c4a4041781457026b604d2c08ad011560229404518162b8113e02264040f8040f8001f,
  0x7e2c4fc1b59a2bb315a798daf3155e436b3157662accc529bab53996c730d8dd599ba33383546e2ccdc17598a3b3146684d4d0969a0b3341566602ecc0540491a335d4668ac44a51929a32515f2528c8ed71b0ae13e462a68c545649f2313b478daac5b11e2aa3b62536c08e9891cb72396d4f6aa8e5b13636239654b2d88e5891caaa40544702c8c48c04238c45a424a084540622b0c356,
  0x521299d4a73a94681b0d013e9d2a73a546742e80b479948d324a6641280a4b944b52895a5094ca025014771cd6639a5c71468e27d1c05404a5c3b5b876930e56a1cab4393e8702a024edf9b1423607e4c4fc5b9f8b6bf16c
]

def F_197 := shardForest fd_197 8 11

def ld_197 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0xc23842ea5d0ba1706d8db0ae95c2b8570ac354691d11a21406805009e334a684b296128648c90902ef5d0ba06e6dc1b0b606a2c8d8123d44288110220440881102204225e8b09602c0580b01602c0580a89502a02e80d001 0xfc949c1512f2627a4a494909d13e2e48070d44b5191b93e25264665b07c221896c2a2983c150b928173501b08855158682b14568262b84c5708c0a1184434ad465598c23317b522d4a458578acae9495c272aa4a54890a28c8662202c3c04c7c2e0e84c1b0783a9506da20f3541c0d83413081220c813448b48315901ab1f25b134927890ced209c95b072926c50cd4a090923180ac1e4a43e2b8b457154b4289584d2509246112b62052c3894819210203c0a4f8162b864570b6b614d2c24ad04156072940c518109f019320207d38d1e6125c9a3b8d2970c4ed9491a28471706e1a0bc040f8001f 11 4 11 8 5,
  unpackLinksF 0xe819f738670cc3982f45e0bc1782f05e0b856c6d85a1b414a290520a4144680c88900f31d8b92720d51a8350682cc5982f45e0bc170ae05a2a8d48a90502a01402714a4941192304428450820127a1b4288500a008c01000 0x856c50698a08b74096d802d8e4595fcb13d1557128afc1b4c832aa8553008ae0511ee36b94657a8aade519e436a6065490aad2055d0b63986c702a8e0d51d6b539566718ccde599b82e938552408ad0055202a118446b4d498999a92d13a56692ccd05591c33110567d8aef8569e0abbb95676294da51db0a3230572108e060759c0bb301557246aa48c801a2e96154262c44a52890af92953480bad8549192e13e4a264b24f87c1a2b16c4f2b83c1114d3029b601d0689ed54701b26c6c4b2d8965b1200a24054578da65195562aaa362524c4a25b940b6a716c4c2ca9458924aa8c8464702cc8d7505aab1b45154b2c294d8128af23b092b2b654d68a8ac13b46246300d8d091a1a50422a06448cc09190044 11 4 11 8 5,
  unpackLinksF 0x2404448810c6183f47e0f858eb10602c01352604c0945281ba3606c0d81a134042880100200400788f00b4104200310600c009001 0xa15861531a44a5fd21849028761838ca813e7f4c9f923979668e53a294629599f54e79517d48e745d411558c45400d4582f0c07cfc479792a6e4692566314b9a4a5f1213e11c542d990942c1f5f15e5e5a9695a455b8b5265529764857857130b650250a07ce84792d66474b8a52a41468f4f9f1323911c443f0907638155915e335b8bd26295a8955a213e764c96057100fc1c1d87056126084d815845310d5d16c 11 4 10 8 5
]

def L_197 := shardLinks ld_197

def st_197 := dagTraceF m_197 s_197 9 F_197

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_197 : dagCheckRootsF m_197 g_197 b_197 (dagRefF 165 st_197 L_197 0) s_197 9 = true := by
  decide +kernel

def ck_197 := dagCheckNodeF m_197 g_197 b_197 165 st_197 L_197

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_197_0 : treeBlockF 0 16 ck_197 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_197_16 : treeBlockF 16 32 ck_197 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_197_32 : treeBlockF 32 48 ck_197 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_197_48 : treeBlockF 48 64 ck_197 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_197_64 : treeBlockF 64 80 ck_197 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_197_80 : treeBlockF 80 96 ck_197 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_197_96 : treeBlockF 96 112 ck_197 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_197_112 : treeBlockF 112 128 ck_197 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_197_128 : treeBlockF 128 144 ck_197 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_197_144 : treeBlockF 144 160 ck_197 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_197_160 : treeBlockF 160 165 ck_197 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_197 : ∀ j, 0 ≤ j → j < 165 → ck_197 j = true :=
  (block_join (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_197_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_197_16 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_197_32 h1 h2) (block_join (fun _ h1 h2 => treeBlockF_at nb_197_48 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_197_64 h1 h2)))) (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_197_80 h1 h2) (block_join (fun _ h1 h2 => treeBlockF_at nb_197_96 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_197_112 h1 h2))) (block_join (fun _ h1 h2 => treeBlockF_at nb_197_128 h1 h2) (block_join (fun _ h1 h2 => treeBlockF_at nb_197_144 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_197_160 h1 h2)))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_197 : LowerBin m_197 s_197 g_197 10 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_197 sub_197 goal_197 rc_197 nc_197

def m_63 : Nat := 0xf0f000000000000

def s_63 : List Nat := [0xf000000000000, 0x303000000000000, 0x505000000000000]

def g_63 : Nat := 0x107000000000000

def b_63 : List (Nat × List Nat × Nat × Nat) := []

theorem known_63 : KnownBin b_63 := by
  intro b hb
  simp [b_63] at hb

theorem sub_63 : ∀ b ∈ b_63, m_63 &&& b.1 = b.1 := by
  intro b hb
  simp [b_63] at hb

theorem goal_63 : ∀ b ∈ b_63, canon b.1 g_63 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_63] at hb

def fd_63 : Array Nat := #[
  0x7
]

def F_63 := shardForest fd_63 1 3

def ld_63 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_63 := shardLinks ld_63

def st_63 := dagTraceF m_63 s_63 3 F_63

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsF m_63 g_63 b_63 (dagRefF 1 st_63 L_63 0) s_63 3 = true := by
  decide +kernel

def ck_63 := dagCheckNodeF m_63 g_63 b_63 1 st_63 L_63

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_63_0 : treeBlockF 0 1 ck_63 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_63 : ∀ j, 0 ≤ j → j < 1 → ck_63 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_63_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_63 : LowerBin m_63 s_63 g_63 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_63 sub_63 goal_63 rc_63 nc_63

def m_149 : Nat := 0xf0f00000f0f0000

def s_149 : List Nat := [0xf0f0000, 0xf0000000f0000, 0x303000003030000, 0x505000005050000]

def g_149 : Nat := 0x1070000070f0000

def b_149 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 4, g_19), (m_37, s_37, 4, g_37), (m_53, s_53, 4, g_53), (m_63, s_63, 4, g_63)]

theorem known_149 : KnownBin b_149 := by
  intro b hb
  simp only [b_149, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_19
  · exact lb_37
  · exact lb_53
  · exact lb_63

theorem sub_149 : ∀ b ∈ b_149, m_149 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_149, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

theorem goal_149 : ∀ b ∈ b_149, canon b.1 g_149 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_149, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

def fd_149 : Array Nat := #[
  0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f
]

def F_149 := shardForest fd_149 6 10

def ld_149 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x8e11c1fc3f07c2f81b43606c0d45a0b40662cc15c2b0542a8148a18420841009f13e0784f01d12b0540a814128050098921222440809001e21e00b001 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d347d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 11 4 10 6 5
]

def L_149 := shardLinks ld_149

def st_149 := dagTraceF m_149 s_149 6 F_149

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_149 : dagCheckRootsF m_149 g_149 b_149 (dagRefF 43 st_149 L_149 0) s_149 6 = true := by
  decide +kernel

def ck_149 := dagCheckNodeF m_149 g_149 b_149 43 st_149 L_149

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_149_0 : treeBlockF 0 16 ck_149 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_149_16 : treeBlockF 16 32 ck_149 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_149_32 : treeBlockF 32 43 ck_149 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_149 : ∀ j, 0 ≤ j → j < 43 → ck_149 j = true :=
  (block_join (fun _ h1 h2 => treeBlockF_at nb_149_0 h1 h2) (block_join (fun _ h1 h2 => treeBlockF_at nb_149_16 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_149_32 h1 h2)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_149 : LowerBin m_149 s_149 g_149 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_149 sub_149 goal_149 rc_149 nc_149

def m_55 : Nat := 0xf0000000f00000

def s_55 : List Nat := [0xf00000, 0x30000000300000, 0x50000000500000]

def g_55 : Nat := 0x10000000700000

def b_55 : List (Nat × List Nat × Nat × Nat) := []

theorem known_55 : KnownBin b_55 := by
  intro b hb
  simp [b_55] at hb

theorem sub_55 : ∀ b ∈ b_55, m_55 &&& b.1 = b.1 := by
  intro b hb
  simp [b_55] at hb

theorem goal_55 : ∀ b ∈ b_55, canon b.1 g_55 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_55] at hb

def fd_55 : Array Nat := #[
  0x7
]

def F_55 := shardForest fd_55 1 3

def ld_55 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_55 := shardLinks ld_55

def st_55 := dagTraceF m_55 s_55 3 F_55

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsF m_55 g_55 b_55 (dagRefF 1 st_55 L_55 0) s_55 3 = true := by
  decide +kernel

def ck_55 := dagCheckNodeF m_55 g_55 b_55 1 st_55 L_55

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_55_0 : treeBlockF 0 1 ck_55 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_55 : ∀ j, 0 ≤ j → j < 1 → ck_55 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_55_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_55 : LowerBin m_55 s_55 g_55 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_55 sub_55 goal_55 rc_55 nc_55

def m_67 : Nat := 0xff000000000000

def s_67 : List Nat := [0xf000000000000, 0x33000000000000, 0x55000000000000]

def g_67 : Nat := 0x17000000000000

def b_67 : List (Nat × List Nat × Nat × Nat) := []

theorem known_67 : KnownBin b_67 := by
  intro b hb
  simp [b_67] at hb

theorem sub_67 : ∀ b ∈ b_67, m_67 &&& b.1 = b.1 := by
  intro b hb
  simp [b_67] at hb

theorem goal_67 : ∀ b ∈ b_67, canon b.1 g_67 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_67] at hb

def fd_67 : Array Nat := #[
  0x7
]

def F_67 := shardForest fd_67 1 3

def ld_67 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_67 := shardLinks ld_67

def st_67 := dagTraceF m_67 s_67 3 F_67

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_67 : dagCheckRootsF m_67 g_67 b_67 (dagRefF 1 st_67 L_67 0) s_67 3 = true := by
  decide +kernel

def ck_67 := dagCheckNodeF m_67 g_67 b_67 1 st_67 L_67

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_67_0 : treeBlockF 0 1 ck_67 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_67 : ∀ j, 0 ≤ j → j < 1 → ck_67 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_67_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_67 : LowerBin m_67 s_67 g_67 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_67 sub_67 goal_67 rc_67 nc_67

def m_163 : Nat := 0xff000000ff0000

def s_163 : List Nat := [0xff0000, 0xf0000000f0000, 0x33000000330000, 0x55000000550000]

def g_163 : Nat := 0x170000007f0000

def b_163 : List (Nat × List Nat × Nat × Nat) := [(m_23, s_23, 4, g_23), (m_41, s_41, 4, g_41), (m_55, s_55, 4, g_55), (m_67, s_67, 4, g_67)]

theorem known_163 : KnownBin b_163 := by
  intro b hb
  simp only [b_163, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_23
  · exact lb_41
  · exact lb_55
  · exact lb_67

theorem sub_163 : ∀ b ∈ b_163, m_163 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_163, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

theorem goal_163 : ∀ b ∈ b_163, canon b.1 g_163 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_163, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

def fd_163 : Array Nat := #[
  0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f
]

def F_163 := shardForest fd_163 6 10

def ld_163 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x8e11c1fc3f07c2f81b43606c0d45a0b40662cc15c2b0542a8148a18420841009f13e0784f01d12b0540a814128050098921222440809001e21e00b001 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d347d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 11 4 10 6 5
]

def L_163 := shardLinks ld_163

def st_163 := dagTraceF m_163 s_163 6 F_163

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_163 : dagCheckRootsF m_163 g_163 b_163 (dagRefF 43 st_163 L_163 0) s_163 6 = true := by
  decide +kernel

def ck_163 := dagCheckNodeF m_163 g_163 b_163 43 st_163 L_163

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_163_0 : treeBlockF 0 16 ck_163 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_163_16 : treeBlockF 16 32 ck_163 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_163_32 : treeBlockF 32 43 ck_163 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_163 : ∀ j, 0 ≤ j → j < 43 → ck_163 j = true :=
  (block_join (fun _ h1 h2 => treeBlockF_at nb_163_0 h1 h2) (block_join (fun _ h1 h2 => treeBlockF_at nb_163_16 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_163_32 h1 h2)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_163 : LowerBin m_163 s_163 g_163 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_163 sub_163 goal_163 rc_163 nc_163

def m_31 : Nat := 0x5555000000000000

def s_31 : List Nat := [0x55000000000000, 0x505000000000000, 0x1111000000000000]

def g_31 : Nat := 0x115000000000000

def b_31 : List (Nat × List Nat × Nat × Nat) := []

theorem known_31 : KnownBin b_31 := by
  intro b hb
  simp [b_31] at hb

theorem sub_31 : ∀ b ∈ b_31, m_31 &&& b.1 = b.1 := by
  intro b hb
  simp [b_31] at hb

theorem goal_31 : ∀ b ∈ b_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_31] at hb

def fd_31 : Array Nat := #[
  0x7
]

def F_31 := shardForest fd_31 1 3

def ld_31 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_31 := shardLinks ld_31

def st_31 := dagTraceF m_31 s_31 3 F_31

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsF m_31 g_31 b_31 (dagRefF 1 st_31 L_31 0) s_31 3 = true := by
  decide +kernel

def ck_31 := dagCheckNodeF m_31 g_31 b_31 1 st_31 L_31

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_31_0 : treeBlockF 0 1 ck_31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_31 : ∀ j, 0 ≤ j → j < 1 → ck_31 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_31_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_31 : LowerBin m_31 s_31 g_31 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_31 sub_31 goal_31 rc_31 nc_31

def m_49 : Nat := 0x3333000000000000

def s_49 : List Nat := [0x33000000000000, 0x303000000000000, 0x1111000000000000]

def g_49 : Nat := 0x113000000000000

def b_49 : List (Nat × List Nat × Nat × Nat) := []

theorem known_49 : KnownBin b_49 := by
  intro b hb
  simp [b_49] at hb

theorem sub_49 : ∀ b ∈ b_49, m_49 &&& b.1 = b.1 := by
  intro b hb
  simp [b_49] at hb

theorem goal_49 : ∀ b ∈ b_49, canon b.1 g_49 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_49] at hb

def fd_49 : Array Nat := #[
  0x7
]

def F_49 := shardForest fd_49 1 3

def ld_49 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_49 := shardLinks ld_49

def st_49 := dagTraceF m_49 s_49 3 F_49

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsF m_49 g_49 b_49 (dagRefF 1 st_49 L_49 0) s_49 3 = true := by
  decide +kernel

def ck_49 := dagCheckNodeF m_49 g_49 b_49 1 st_49 L_49

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_49_0 : treeBlockF 0 1 ck_49 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_49 : ∀ j, 0 ≤ j → j < 1 → ck_49 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_49_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_49 : LowerBin m_49 s_49 g_49 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_49 sub_49 goal_49 rc_49 nc_49

def m_185 : Nat := 0xffff000000000000

def s_185 : List Nat := [0xff000000000000, 0xf0f000000000000, 0x3333000000000000, 0x5555000000000000]

def g_185 : Nat := 0x117000000000000

def b_185 : List (Nat × List Nat × Nat × Nat) := [(m_31, s_31, 4, g_31), (m_49, s_49, 4, g_49), (m_63, s_63, 4, g_63), (m_67, s_67, 4, g_67)]

theorem known_185 : KnownBin b_185 := by
  intro b hb
  simp only [b_185, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_31
  · exact lb_49
  · exact lb_63
  · exact lb_67

theorem sub_185 : ∀ b ∈ b_185, m_185 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_185, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

theorem goal_185 : ∀ b ∈ b_185, canon b.1 g_185 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_185, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

def fd_185 : Array Nat := #[
  0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f
]

def F_185 := shardForest fd_185 6 10

def ld_185 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x8e11c1fc3e17c0f81b43516a0d05a0340662cc15c2a1522a41482184027c4f81e13c0780e89d02b05049893024248088910220404801001e21e00b001 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b407c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 11 4 10 6 5
]

def L_185 := shardLinks ld_185

def st_185 := dagTraceF m_185 s_185 6 F_185

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_185 : dagCheckRootsF m_185 g_185 b_185 (dagRefF 43 st_185 L_185 0) s_185 6 = true := by
  decide +kernel

def ck_185 := dagCheckNodeF m_185 g_185 b_185 43 st_185 L_185

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_185_0 : treeBlockF 0 16 ck_185 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_185_16 : treeBlockF 16 32 ck_185 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_185_32 : treeBlockF 32 43 ck_185 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_185 : ∀ j, 0 ≤ j → j < 43 → ck_185 j = true :=
  (block_join (fun _ h1 h2 => treeBlockF_at nb_185_0 h1 h2) (block_join (fun _ h1 h2 => treeBlockF_at nb_185_16 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_185_32 h1 h2)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_185 : LowerBin m_185 s_185 g_185 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_185 sub_185 goal_185 rc_185 nc_185

def m_93 : Nat := 0x5555000055550000

def s_93 : List Nat := [0x55550000, 0x55000000550000, 0x505000005050000, 0x1111000011110000]

def g_93 : Nat := 0x115000005550000

def b_93 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]

theorem known_93 : KnownBin b_93 := by
  intro b hb
  simp only [b_93, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_9

theorem sub_93 : ∀ b ∈ b_93, m_93 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_93, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

theorem goal_93 : ∀ b ∈ b_93, canon b.1 g_93 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_93, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

def F_93 : Nat → Nat × Nat := fun _ => (0, 0)

def L_93 : Nat → Nat → Option Nat := fun _ _ => none

def st_93 := dagTraceF m_93 s_93 4 F_93

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_93 : dagCheckRootsF m_93 g_93 b_93 (dagRefF 0 st_93 L_93 0) s_93 4 = true := by
  decide +kernel

def ck_93 := dagCheckNodeF m_93 g_93 b_93 0 st_93 L_93

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_93 : ∀ j, 0 ≤ j → j < 0 → ck_93 j = true :=
  fun _ _ h => absurd h (Nat.not_lt_zero _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_93 : LowerBin m_93 s_93 g_93 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_93 sub_93 goal_93 rc_93 nc_93

def m_123 : Nat := 0x3333000033330000

def s_123 : List Nat := [0x33330000, 0x33000000330000, 0x303000003030000, 0x1111000011110000]

def g_123 : Nat := 0x113000003330000

def b_123 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]

theorem known_123 : KnownBin b_123 := by
  intro b hb
  simp only [b_123, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_11

theorem sub_123 : ∀ b ∈ b_123, m_123 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_123, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

theorem goal_123 : ∀ b ∈ b_123, canon b.1 g_123 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_123, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

def F_123 : Nat → Nat × Nat := fun _ => (0, 0)

def L_123 : Nat → Nat → Option Nat := fun _ _ => none

def st_123 := dagTraceF m_123 s_123 4 F_123

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_123 : dagCheckRootsF m_123 g_123 b_123 (dagRefF 0 st_123 L_123 0) s_123 4 = true := by
  decide +kernel

def ck_123 := dagCheckNodeF m_123 g_123 b_123 0 st_123 L_123

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_123 : ∀ j, 0 ≤ j → j < 0 → ck_123 j = true :=
  fun _ _ h => absurd h (Nat.not_lt_zero _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_123 : LowerBin m_123 s_123 g_123 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_123 sub_123 goal_123 rc_123 nc_123

def m_153 : Nat := 0xf0f00000f0f00000

def s_153 : List Nat := [0xf0f00000, 0xf0000000f00000, 0x3030000030300000, 0x5050000050500000]

def g_153 : Nat := 0x10000000700000

def b_153 : List (Nat × List Nat × Nat × Nat) := [(m_55, s_55, 4, g_55)]

theorem known_153 : KnownBin b_153 := by
  intro b hb
  simp only [b_153, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_55

theorem sub_153 : ∀ b ∈ b_153, m_153 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_153, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

theorem goal_153 : ∀ b ∈ b_153, canon b.1 g_153 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_153, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

def F_153 : Nat → Nat × Nat := fun _ => (0, 0)

def L_153 : Nat → Nat → Option Nat := fun _ _ => none

def st_153 := dagTraceF m_153 s_153 4 F_153

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_153 : dagCheckRootsF m_153 g_153 b_153 (dagRefF 0 st_153 L_153 0) s_153 4 = true := by
  decide +kernel

def ck_153 := dagCheckNodeF m_153 g_153 b_153 0 st_153 L_153

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_153 : ∀ j, 0 ≤ j → j < 0 → ck_153 j = true :=
  fun _ _ h => absurd h (Nat.not_lt_zero _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_153 : LowerBin m_153 s_153 g_153 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_153 sub_153 goal_153 rc_153 nc_153

def m_181 : Nat := 0xffff0000

def s_181 : List Nat := [0xff0000, 0xf0f0000, 0x33330000, 0x55550000]

def g_181 : Nat := 0x77f0000

def b_181 : List (Nat × List Nat × Nat × Nat) := [(m_33, s_33, 4, g_33)]

theorem known_181 : KnownBin b_181 := by
  intro b hb
  simp only [b_181, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_33

theorem sub_181 : ∀ b ∈ b_181, m_181 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_181, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

theorem goal_181 : ∀ b ∈ b_181, canon b.1 g_181 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_181, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

def F_181 : Nat → Nat × Nat := fun _ => (0, 0)

def L_181 : Nat → Nat → Option Nat := fun _ _ => none

def st_181 := dagTraceF m_181 s_181 4 F_181

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_181 : dagCheckRootsF m_181 g_181 b_181 (dagRefF 0 st_181 L_181 0) s_181 4 = true := by
  decide +kernel

def ck_181 := dagCheckNodeF m_181 g_181 b_181 0 st_181 L_181

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_181 : ∀ j, 0 ≤ j → j < 0 → ck_181 j = true :=
  fun _ _ h => absurd h (Nat.not_lt_zero _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_181 : LowerBin m_181 s_181 g_181 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_181 sub_181 goal_181 rc_181 nc_181

def m_201 : Nat := 0xffff0000ffff0000

def s_201 : List Nat := [0xffff0000, 0xff000000ff0000, 0xf0f00000f0f0000, 0x3333000033330000, 0x5555000055550000]

def g_201 : Nat := 0x1170000077f0000

def b_201 : List (Nat × List Nat × Nat × Nat) := [(m_99, s_99, 7, g_99), (m_129, s_129, 7, g_129), (m_149, s_149, 7, g_149), (m_163, s_163, 7, g_163), (m_185, s_185, 7, g_185), (m_93, s_93, 5, g_93), (m_123, s_123, 5, g_123), (m_153, s_153, 5, g_153), (m_169, s_169, 5, g_169), (m_181, s_181, 5, g_181), (m_9, s_9, 4, g_9), (m_11, s_11, 4, g_11), (m_19, s_19, 4, g_19), (m_23, s_23, 4, g_23), (m_31, s_31, 4, g_31), (m_33, s_33, 4, g_33), (m_37, s_37, 4, g_37), (m_41, s_41, 4, g_41), (m_49, s_49, 4, g_49), (m_51, s_51, 4, g_51), (m_53, s_53, 4, g_53), (m_55, s_55, 4, g_55), (m_63, s_63, 4, g_63), (m_67, s_67, 4, g_67)]

theorem known_201 : KnownBin b_201 := by
  intro b hb
  simp only [b_201, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_99
  · exact lb_129
  · exact lb_149
  · exact lb_163
  · exact lb_185
  · exact lb_93
  · exact lb_123
  · exact lb_153
  · exact lb_169
  · exact lb_181
  · exact lb_9
  · exact lb_11
  · exact lb_19
  · exact lb_23
  · exact lb_31
  · exact lb_33
  · exact lb_37
  · exact lb_41
  · exact lb_49
  · exact lb_51
  · exact lb_53
  · exact lb_55
  · exact lb_63
  · exact lb_67

theorem sub_201 : ∀ b ∈ b_201, m_201 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_201, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem goal_201 : ∀ b ∈ b_201, canon b.1 g_201 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_201, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def fd_201 : Array Nat := #[
  0x3f2523096cf4948c24318482744f860ad9bb513727c3050c60a09156a332d845598c4b611466226a45cd4089291115e222ba5515888ae14568222aa4c57088a911145230884405860918ca441f0b834d50752a0d06c1b6883413064098c0560106e1d15c392d072560e4941c91838ad8714b0f8ae1c4a4041781457026b604d2c08ad011560229404518162b8113e02264040f8040f8001f,
  0x7e2c4fc1b59a2bb315a798daf3155e436b3157662accc529bab53996c730d8dd599ba33383546e2ccdc17598a3b3146684d4d0969a0b3341566602ecc0540491a335d4668ac44a51929a32515f2528c8ed71b0ae13e462a68c545649f2313b478daac5b11e2aa3b62536c08e9891cb72396d4f6aa8e5b13636239654b2d88e5891caaa40544702c8c48c04238c45a424a084540622b0c356,
  0x521299d4a73a94681b0d013e9d2a73a546742e80b479948d324a6641280a4b944b52895a5094ca025014771cd6639a5c71468e27d1c05404a5c3b5b876930e56a1cab4393e8702a024edf9b1423607e4c4fc5b9f8b6bf16c
]

def F_201 := shardForest fd_201 8 11

def ld_201 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0xc23842ea5d0ba1706d8db0ae95c2b8570ac354691d11a21406805009e334a684b296128648c90902ef5d0ba06e6dc1b0b606a2c8d8123d44288110220440881102204225e8b09602c0580b01602c0580a89502a02e80d001 0xfc949c1512f2627a4a494909d13e2e48070d44b5191b93e25264665b07c221896c2a2983c150b928173501b08855158682b14568262b84c5708c0a1184434ad465598c23317b522d4a458578acae9495c272aa4a54890a28c8662202c3c04c7c2e0e84c1b0783a9506da20f3541c0d83413081220c813448b48315901ab1f25b134927890ced209c95b072926c50cd4a090923180ac1e4a43e2b8b457154b4289584d2509246112b62052c3894819210203c0a4f8162b864570b6b614d2c24ad04156072940c518109f019320207d38d1e6125c9a3b8d2970c4ed9491a28471706e1a0bc040f8001f 11 4 11 8 5,
  unpackLinksF 0xe819f738670cc3982f45e0bc1782f05e0b856c6d85a1b414a290520a4144680c88900f31d8b92720d51a8350682cc5982f45e0bc170ae05a2a8d48a90502a01402714a4941192304428450820127a1b4288500a008c01000 0x856c50698a08b74096d802d8e4595fcb13d1557128afc1b4c832aa8553008ae0511ee36b94657a8aade519e436a6065490aad2055d0b63986c702a8e0d51d6b539566718ccde599b82e938552408ad0055202a118446b4d498999a92d13a56692ccd05591c33110567d8aef8569e0abbb95676294da51db0a3230572108e060759c0bb301557246aa48c801a2e96154262c44a52890af92953480bad8549192e13e4a264b24f87c1a2b16c4f2b83c1114d3029b601d0689ed54701b26c6c4b2d8965b1200a24054578da65195562aaa362524c4a25b940b6a716c4c2ca9458924aa8c8464702cc8d7505aab1b45154b2c294d8128af23b092b2b654d68a8ac13b46246300d8d091a1a50422a06448cc09190044 11 4 11 8 5,
  unpackLinksF 0x2404448810c6183f47e0f858eb10602c01352604c0945281ba3606c0d81a134042880100200400788f00b4104200310600c009001 0xa15861531a44a5fd21849028761838ca813e7f4c9f923979668e53a294629599f54e79517d48e745d411558c45400d4582f0c07cfc479792a6e4692566314b9a4a5f1213e11c542d990942c1f5f15e5e5a9695a455b8b5265529764857857130b650250a07ce84792d66474b8a52a41468f4f9f1323911c443f0907638155915e335b8bd26295a8955a213e764c96057100fc1c1d87056126084d815845310d5d16c 11 4 10 8 5
]

def L_201 := shardLinks ld_201

def st_201 := dagTraceF m_201 s_201 9 F_201

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_201 : dagCheckRootsF m_201 g_201 b_201 (dagRefF 165 st_201 L_201 0) s_201 9 = true := by
  decide +kernel

def ck_201 := dagCheckNodeF m_201 g_201 b_201 165 st_201 L_201

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_201_0 : treeBlockF 0 16 ck_201 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_201_16 : treeBlockF 16 32 ck_201 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_201_32 : treeBlockF 32 48 ck_201 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_201_48 : treeBlockF 48 64 ck_201 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_201_64 : treeBlockF 64 80 ck_201 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_201_80 : treeBlockF 80 96 ck_201 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_201_96 : treeBlockF 96 112 ck_201 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_201_112 : treeBlockF 112 128 ck_201 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_201_128 : treeBlockF 128 144 ck_201 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_201_144 : treeBlockF 144 160 ck_201 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_201_160 : treeBlockF 160 165 ck_201 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_201 : ∀ j, 0 ≤ j → j < 165 → ck_201 j = true :=
  (block_join (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_201_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_201_16 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_201_32 h1 h2) (block_join (fun _ h1 h2 => treeBlockF_at nb_201_48 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_201_64 h1 h2)))) (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_201_80 h1 h2) (block_join (fun _ h1 h2 => treeBlockF_at nb_201_96 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_201_112 h1 h2))) (block_join (fun _ h1 h2 => treeBlockF_at nb_201_128 h1 h2) (block_join (fun _ h1 h2 => treeBlockF_at nb_201_144 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_201_160 h1 h2)))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_201 : LowerBin m_201 s_201 g_201 10 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_201 sub_201 goal_201 rc_201 nc_201

def m_21 : Nat := 0x5050505000000000

def s_21 : List Nat := [0x505000000000, 0x50005000000000, 0x1010101000000000]

def g_21 : Nat := 0x10105000000000

def b_21 : List (Nat × List Nat × Nat × Nat) := []

theorem known_21 : KnownBin b_21 := by
  intro b hb
  simp [b_21] at hb

theorem sub_21 : ∀ b ∈ b_21, m_21 &&& b.1 = b.1 := by
  intro b hb
  simp [b_21] at hb

theorem goal_21 : ∀ b ∈ b_21, canon b.1 g_21 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_21] at hb

def fd_21 : Array Nat := #[
  0x7
]

def F_21 := shardForest fd_21 1 3

def ld_21 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_21 := shardLinks ld_21

def st_21 := dagTraceF m_21 s_21 3 F_21

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsF m_21 g_21 b_21 (dagRefF 1 st_21 L_21 0) s_21 3 = true := by
  decide +kernel

def ck_21 := dagCheckNodeF m_21 g_21 b_21 1 st_21 L_21

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_21_0 : treeBlockF 0 1 ck_21 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_21 : ∀ j, 0 ≤ j → j < 1 → ck_21 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_21_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_21 : LowerBin m_21 s_21 g_21 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_21 sub_21 goal_21 rc_21 nc_21

def m_103 : Nat := 0x5555555500000000

def s_103 : List Nat := [0x555500000000, 0x55005500000000, 0x505050500000000, 0x1111111100000000]

def g_103 : Nat := 0x115155500000000

def b_103 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13), (m_21, s_21, 4, g_21), (m_27, s_27, 4, g_27), (m_31, s_31, 4, g_31)]

theorem known_103 : KnownBin b_103 := by
  intro b hb
  simp only [b_103, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_13
  · exact lb_21
  · exact lb_27
  · exact lb_31

theorem sub_103 : ∀ b ∈ b_103, m_103 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_103, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

theorem goal_103 : ∀ b ∈ b_103, canon b.1 g_103 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_103, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

def fd_103 : Array Nat := #[
  0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f
]

def F_103 := shardForest fd_103 6 10

def ld_103 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x8e11c1fc3f07c2f81b43606c0d45a0b40662cc15c2b0542a8148a18420841009f13e0784f01d12b0540a814128050098921222440809001e21e00b001 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d347d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 11 4 10 6 5
]

def L_103 := shardLinks ld_103

def st_103 := dagTraceF m_103 s_103 6 F_103

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_103 : dagCheckRootsF m_103 g_103 b_103 (dagRefF 43 st_103 L_103 0) s_103 6 = true := by
  decide +kernel

def ck_103 := dagCheckNodeF m_103 g_103 b_103 43 st_103 L_103

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_103_0 : treeBlockF 0 16 ck_103 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_103_16 : treeBlockF 16 32 ck_103 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_103_32 : treeBlockF 32 43 ck_103 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_103 : ∀ j, 0 ≤ j → j < 43 → ck_103 j = true :=
  (block_join (fun _ h1 h2 => treeBlockF_at nb_103_0 h1 h2) (block_join (fun _ h1 h2 => treeBlockF_at nb_103_16 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_103_32 h1 h2)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_103 : LowerBin m_103 s_103 g_103 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_103 sub_103 goal_103 rc_103 nc_103

def m_39 : Nat := 0x3030303000000000

def s_39 : List Nat := [0x303000000000, 0x30003000000000, 0x1010101000000000]

def g_39 : Nat := 0x10103000000000

def b_39 : List (Nat × List Nat × Nat × Nat) := []

theorem known_39 : KnownBin b_39 := by
  intro b hb
  simp [b_39] at hb

theorem sub_39 : ∀ b ∈ b_39, m_39 &&& b.1 = b.1 := by
  intro b hb
  simp [b_39] at hb

theorem goal_39 : ∀ b ∈ b_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_39] at hb

def fd_39 : Array Nat := #[
  0x7
]

def F_39 := shardForest fd_39 1 3

def ld_39 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_39 := shardLinks ld_39

def st_39 := dagTraceF m_39 s_39 3 F_39

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsF m_39 g_39 b_39 (dagRefF 1 st_39 L_39 0) s_39 3 = true := by
  decide +kernel

def ck_39 := dagCheckNodeF m_39 g_39 b_39 1 st_39 L_39

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_39_0 : treeBlockF 0 1 ck_39 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_39 : ∀ j, 0 ≤ j → j < 1 → ck_39 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_39_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_39 : LowerBin m_39 s_39 g_39 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_39 sub_39 goal_39 rc_39 nc_39

def m_133 : Nat := 0x3333333300000000

def s_133 : List Nat := [0x333300000000, 0x33003300000000, 0x303030300000000, 0x1111111100000000]

def g_133 : Nat := 0x113133300000000

def b_133 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15), (m_39, s_39, 4, g_39), (m_45, s_45, 4, g_45), (m_49, s_49, 4, g_49)]

theorem known_133 : KnownBin b_133 := by
  intro b hb
  simp only [b_133, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_15
  · exact lb_39
  · exact lb_45
  · exact lb_49

theorem sub_133 : ∀ b ∈ b_133, m_133 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_133, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

theorem goal_133 : ∀ b ∈ b_133, canon b.1 g_133 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_133, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

def fd_133 : Array Nat := #[
  0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f
]

def F_133 := shardForest fd_133 6 10

def ld_133 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x8e11c1fc3f07c2f81b43606c0d45a0b40662cc15c2b0542a8148a18420841009f13e0784f01d12b0540a814128050098921222440809001e21e00b001 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d347d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 11 4 10 6 5
]

def L_133 := shardLinks ld_133

def st_133 := dagTraceF m_133 s_133 6 F_133

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_133 : dagCheckRootsF m_133 g_133 b_133 (dagRefF 43 st_133 L_133 0) s_133 6 = true := by
  decide +kernel

def ck_133 := dagCheckNodeF m_133 g_133 b_133 43 st_133 L_133

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_133_0 : treeBlockF 0 16 ck_133 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_133_16 : treeBlockF 16 32 ck_133 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_133_32 : treeBlockF 32 43 ck_133 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_133 : ∀ j, 0 ≤ j → j < 43 → ck_133 j = true :=
  (block_join (fun _ h1 h2 => treeBlockF_at nb_133_0 h1 h2) (block_join (fun _ h1 h2 => treeBlockF_at nb_133_16 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_133_32 h1 h2)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_133 : LowerBin m_133 s_133 g_133 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_133 sub_133 goal_133 rc_133 nc_133

def m_61 : Nat := 0xf000f000000000

def s_61 : List Nat := [0xf000000000, 0x30003000000000, 0x50005000000000]

def g_61 : Nat := 0x10007000000000

def b_61 : List (Nat × List Nat × Nat × Nat) := []

theorem known_61 : KnownBin b_61 := by
  intro b hb
  simp [b_61] at hb

theorem sub_61 : ∀ b ∈ b_61, m_61 &&& b.1 = b.1 := by
  intro b hb
  simp [b_61] at hb

theorem goal_61 : ∀ b ∈ b_61, canon b.1 g_61 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_61] at hb

def fd_61 : Array Nat := #[
  0x7
]

def F_61 := shardForest fd_61 1 3

def ld_61 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_61 := shardLinks ld_61

def st_61 := dagTraceF m_61 s_61 3 F_61

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsF m_61 g_61 b_61 (dagRefF 1 st_61 L_61 0) s_61 3 = true := by
  decide +kernel

def ck_61 := dagCheckNodeF m_61 g_61 b_61 1 st_61 L_61

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_61_0 : treeBlockF 0 1 ck_61 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_61 : ∀ j, 0 ≤ j → j < 1 → ck_61 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_61_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_61 : LowerBin m_61 s_61 g_61 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_61 sub_61 goal_61 rc_61 nc_61

def m_65 : Nat := 0xf0f000000000

def s_65 : List Nat := [0xf000000000, 0x303000000000, 0x505000000000]

def g_65 : Nat := 0x107000000000

def b_65 : List (Nat × List Nat × Nat × Nat) := []

theorem known_65 : KnownBin b_65 := by
  intro b hb
  simp [b_65] at hb

theorem sub_65 : ∀ b ∈ b_65, m_65 &&& b.1 = b.1 := by
  intro b hb
  simp [b_65] at hb

theorem goal_65 : ∀ b ∈ b_65, canon b.1 g_65 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [b_65] at hb

def fd_65 : Array Nat := #[
  0x7
]

def F_65 := shardForest fd_65 1 3

def ld_65 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x7 2 1 3 1 2
]

def L_65 := shardLinks ld_65

def st_65 := dagTraceF m_65 s_65 3 F_65

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_65 : dagCheckRootsF m_65 g_65 b_65 (dagRefF 1 st_65 L_65 0) s_65 3 = true := by
  decide +kernel

def ck_65 := dagCheckNodeF m_65 g_65 b_65 1 st_65 L_65

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_65_0 : treeBlockF 0 1 ck_65 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_65 : ∀ j, 0 ≤ j → j < 1 → ck_65 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_65_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_65 : LowerBin m_65 s_65 g_65 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_65 sub_65 goal_65 rc_65 nc_65

def m_159 : Nat := 0xf0f0f0f000000000

def s_159 : List Nat := [0xf0f000000000, 0xf000f000000000, 0x3030303000000000, 0x5050505000000000]

def g_159 : Nat := 0x10107000000000

def b_159 : List (Nat × List Nat × Nat × Nat) := [(m_21, s_21, 4, g_21), (m_39, s_39, 4, g_39), (m_61, s_61, 4, g_61), (m_65, s_65, 4, g_65)]

theorem known_159 : KnownBin b_159 := by
  intro b hb
  simp only [b_159, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_21
  · exact lb_39
  · exact lb_61
  · exact lb_65

theorem sub_159 : ∀ b ∈ b_159, m_159 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_159, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

theorem goal_159 : ∀ b ∈ b_159, canon b.1 g_159 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_159, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

def fd_159 : Array Nat := #[
  0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f
]

def F_159 := shardForest fd_159 6 10

def ld_159 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x8e11c1fc3e17c0f81b43516a0d05a0340662cc15c2a1522a41482184027c4f81e13c0780e89d02b05049893024248088910220404801001e21e00b001 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b407c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 11 4 10 6 5
]

def L_159 := shardLinks ld_159

def st_159 := dagTraceF m_159 s_159 6 F_159

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_159 : dagCheckRootsF m_159 g_159 b_159 (dagRefF 43 st_159 L_159 0) s_159 6 = true := by
  decide +kernel

def ck_159 := dagCheckNodeF m_159 g_159 b_159 43 st_159 L_159

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_159_0 : treeBlockF 0 16 ck_159 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_159_16 : treeBlockF 16 32 ck_159 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_159_32 : treeBlockF 32 43 ck_159 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_159 : ∀ j, 0 ≤ j → j < 43 → ck_159 j = true :=
  (block_join (fun _ h1 h2 => treeBlockF_at nb_159_0 h1 h2) (block_join (fun _ h1 h2 => treeBlockF_at nb_159_16 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_159_32 h1 h2)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_159 : LowerBin m_159 s_159 g_159 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_159 sub_159 goal_159 rc_159 nc_159

def m_155 : Nat := 0xf0f0f0f00000000

def s_155 : List Nat := [0xf0f00000000, 0xf000f00000000, 0x303030300000000, 0x505050500000000]

def g_155 : Nat := 0x107070700000000

def b_155 : List (Nat × List Nat × Nat × Nat) := [(m_59, s_59, 4, g_59)]

theorem known_155 : KnownBin b_155 := by
  intro b hb
  simp only [b_155, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_59

theorem sub_155 : ∀ b ∈ b_155, m_155 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_155, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

theorem goal_155 : ∀ b ∈ b_155, canon b.1 g_155 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_155, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

def F_155 : Nat → Nat × Nat := fun _ => (0, 0)

def L_155 : Nat → Nat → Option Nat := fun _ _ => none

def st_155 := dagTraceF m_155 s_155 4 F_155

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_155 : dagCheckRootsF m_155 g_155 b_155 (dagRefF 0 st_155 L_155 0) s_155 4 = true := by
  decide +kernel

def ck_155 := dagCheckNodeF m_155 g_155 b_155 0 st_155 L_155

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_155 : ∀ j, 0 ≤ j → j < 0 → ck_155 j = true :=
  fun _ _ h => absurd h (Nat.not_lt_zero _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_155 : LowerBin m_155 s_155 g_155 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_155 sub_155 goal_155 rc_155 nc_155

def m_171 : Nat := 0xff00ff00000000

def s_171 : List Nat := [0xff00000000, 0xf000f00000000, 0x33003300000000, 0x55005500000000]

def g_171 : Nat := 0x17007700000000

def b_171 : List (Nat × List Nat × Nat × Nat) := [(m_61, s_61, 4, g_61)]

theorem known_171 : KnownBin b_171 := by
  intro b hb
  simp only [b_171, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_61

theorem sub_171 : ∀ b ∈ b_171, m_171 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_171, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

theorem goal_171 : ∀ b ∈ b_171, canon b.1 g_171 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_171, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

def F_171 : Nat → Nat × Nat := fun _ => (0, 0)

def L_171 : Nat → Nat → Option Nat := fun _ _ => none

def st_171 := dagTraceF m_171 s_171 4 F_171

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_171 : dagCheckRootsF m_171 g_171 b_171 (dagRefF 0 st_171 L_171 0) s_171 4 = true := by
  decide +kernel

def ck_171 := dagCheckNodeF m_171 g_171 b_171 0 st_171 L_171

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_171 : ∀ j, 0 ≤ j → j < 0 → ck_171 j = true :=
  fun _ _ h => absurd h (Nat.not_lt_zero _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_171 : LowerBin m_171 s_171 g_171 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_171 sub_171 goal_171 rc_171 nc_171

def m_179 : Nat := 0xffff00000000

def s_179 : List Nat := [0xff00000000, 0xf0f00000000, 0x333300000000, 0x555500000000]

def g_179 : Nat := 0x177700000000

def b_179 : List (Nat × List Nat × Nat × Nat) := [(m_65, s_65, 4, g_65)]

theorem known_179 : KnownBin b_179 := by
  intro b hb
  simp only [b_179, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_65

theorem sub_179 : ∀ b ∈ b_179, m_179 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_179, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

theorem goal_179 : ∀ b ∈ b_179, canon b.1 g_179 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_179, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel

def F_179 : Nat → Nat × Nat := fun _ => (0, 0)

def L_179 : Nat → Nat → Option Nat := fun _ _ => none

def st_179 := dagTraceF m_179 s_179 4 F_179

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_179 : dagCheckRootsF m_179 g_179 b_179 (dagRefF 0 st_179 L_179 0) s_179 4 = true := by
  decide +kernel

def ck_179 := dagCheckNodeF m_179 g_179 b_179 0 st_179 L_179

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_179 : ∀ j, 0 ≤ j → j < 0 → ck_179 j = true :=
  fun _ _ h => absurd h (Nat.not_lt_zero _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_179 : LowerBin m_179 s_179 g_179 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_179 sub_179 goal_179 rc_179 nc_179

def m_205 : Nat := 0xffffffff00000000

def s_205 : List Nat := [0xffff00000000, 0xff00ff00000000, 0xf0f0f0f00000000, 0x3333333300000000, 0x5555555500000000]

def g_205 : Nat := 0x117177700000000

def b_205 : List (Nat × List Nat × Nat × Nat) := [(m_103, s_103, 7, g_103), (m_133, s_133, 7, g_133), (m_159, s_159, 7, g_159), (m_177, s_177, 7, g_177), (m_185, s_185, 7, g_185), (m_107, s_107, 5, g_107), (m_137, s_137, 5, g_137), (m_155, s_155, 5, g_155), (m_171, s_171, 5, g_171), (m_179, s_179, 5, g_179), (m_13, s_13, 4, g_13), (m_15, s_15, 4, g_15), (m_21, s_21, 4, g_21), (m_27, s_27, 4, g_27), (m_31, s_31, 4, g_31), (m_39, s_39, 4, g_39), (m_45, s_45, 4, g_45), (m_49, s_49, 4, g_49), (m_59, s_59, 4, g_59), (m_61, s_61, 4, g_61), (m_63, s_63, 4, g_63), (m_65, s_65, 4, g_65), (m_67, s_67, 4, g_67), (m_69, s_69, 4, g_69)]

theorem known_205 : KnownBin b_205 := by
  intro b hb
  simp only [b_205, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_103
  · exact lb_133
  · exact lb_159
  · exact lb_177
  · exact lb_185
  · exact lb_107
  · exact lb_137
  · exact lb_155
  · exact lb_171
  · exact lb_179
  · exact lb_13
  · exact lb_15
  · exact lb_21
  · exact lb_27
  · exact lb_31
  · exact lb_39
  · exact lb_45
  · exact lb_49
  · exact lb_59
  · exact lb_61
  · exact lb_63
  · exact lb_65
  · exact lb_67
  · exact lb_69

theorem sub_205 : ∀ b ∈ b_205, m_205 &&& b.1 = b.1 := by
  intro b hb
  simp only [b_205, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem goal_205 : ∀ b ∈ b_205, canon b.1 g_205 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_205, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def fd_205 : Array Nat := #[
  0x3f4987c988c9a1993423b8b26457ce6371914f378a6644f4d1a41a248338a664494041394a4a2949252920b52614a462928c540d0a42301453278b204d7c96370134f024bc4358484af01253024a40493862b10e560186c4305b8649e0c162024860490856298123a136902114c41a8083400246c1ad2034a4064530226c12d2024a401c53054700a4e0141c0234303048040d8040b8001f,
  0x127eeed29dda4bbb487b098eed19dd233c1347728ccd14d99af39d61734bcccd4d99a93334e6aac4dd581aa313526e6b498d498999a1b3342678a6cc0f40493af3495e48abc8fd78a2af13f5f8b2bc49c0427aa35e546a4a897d511aaa15f5426aad1b95093aa05e0107e96d292da4a5b484f29896d192d23261344b08c6514cc9af23d61474bc64d4cc9a91934e3eac485580fa311f26e,
  0x5194da309b2c8de591acf24d9e46b3c136589bcb1359849b308d660a6cc1359606f2c0d405a1c93499228b241140527c635e8c6a51897a309ac60350147f0ed261d22c3a3f8708a0253e01af40352804bf008d600af40035
]

def F_205 := shardForest fd_205 8 11

def ld_205 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0xd639d338670cc398328e50c838c710df3ba5436805009c5382614b1961285eebd0782f01d8bb0742e81b23606c0d45a8341680d0198af45e0bc170ae05a2b41682a3522a0529a32442844f19e03c0780d99a13042f40d001 0x3f4988758906312026e3e4c477164e6371bc53070280c050d5a41a248040286714c0c0a25453496bc8cd4d15a92234e3d68678d08e8af9c14f3627a1e4d4c892810160d46c120d865a616a4c2a068540d089308ea51304945e924b92416246184822a8e8491b159460c26c52118201b13c59258dc38d808ab08db52212bc3054871b00e560192783b5886db10d16e182c42b14c4da409453116a020d001c1a028240e6901a520101206453030480c0d014920534809290080901d1c031380507008d0c222981824288a64cd7c91a791a5e204a63e94879270ba4316484288e83d1b059360206d2ad0e4527c5a3f8629efe4fd9493ae84f5307e6209c040b8001f 11 4 11 8 5,
  unpackLinksF 0xbe17c2e95d0b65686d059199b30258cb08e91c2384618c114628450883012004007e2cb588b10620c41883106029a928a504a0941282504a0905201aa340680c11802c4544a81410fa1c0308600480801001102000400000 0x6a0d4380ab5b4c7b098f04d1e09a3a3616f6a2fcd29f5a4be3487a68cd4d05e5233b9466707a240d4cc12860156e8c0e9585b62939a5e6a4a4dd181bab035a4c6fac4db189b13735262678a6ed14dd5af39353716a4e0d39a5a1b43425e0beaa13d981e878353204a160557c93afc5964692b6d052526b1a456247e4653584a2b013f5e24ea80f95893ab46e5c6bcb6d49692fa223d5946ab057c789eab9355524ea8178d09a850163f6989e531301a26134486c286d4549a528b49506909cd18f9a0a6a463727a244d4cc92a58460802c8518122b0a0c52474bc7c9490a3021560 11 4 11 8 5,
  unpackLinksF 0x2985309712c2584a19410a21042082304200b88700b3158ab056086900a004008010016a2a2540a8150174284500a01402805000a 0x2914d7a5167d35794968c4d4e11668354d095e124a0935ea459f8d5dd269e134b045980d4ac154c090a8149b9353a459a8d6654d2c51661354b098a4168f8f68a37a18d6113d9d4de71357649d6c3d970de58354a09ca0172705e53498fd063a3e755364d45834fd244d92115683f2605c941790d7a3f528e97a215f704f635356217d103d8c0d490173b09e2b4984d05d64d89916223f814f88c4d87115603f3a09ce42785d7a13528397dc23d828d6055e6017c783d800d4e027 11 4 10 8 5
]

def L_205 := shardLinks ld_205

def st_205 := dagTraceF m_205 s_205 9 F_205

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_205 : dagCheckRootsF m_205 g_205 b_205 (dagRefF 165 st_205 L_205 0) s_205 9 = true := by
  decide +kernel

def ck_205 := dagCheckNodeF m_205 g_205 b_205 165 st_205 L_205

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_205_0 : treeBlockF 0 16 ck_205 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_205_16 : treeBlockF 16 32 ck_205 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_205_32 : treeBlockF 32 48 ck_205 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_205_48 : treeBlockF 48 64 ck_205 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_205_64 : treeBlockF 64 80 ck_205 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_205_80 : treeBlockF 80 96 ck_205 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_205_96 : treeBlockF 96 112 ck_205 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_205_112 : treeBlockF 112 128 ck_205 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_205_128 : treeBlockF 128 144 ck_205 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_205_144 : treeBlockF 144 160 ck_205 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_205_160 : treeBlockF 160 165 ck_205 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_205 : ∀ j, 0 ≤ j → j < 165 → ck_205 j = true :=
  (block_join (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_205_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_205_16 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_205_32 h1 h2) (block_join (fun _ h1 h2 => treeBlockF_at nb_205_48 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_205_64 h1 h2)))) (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_205_80 h1 h2) (block_join (fun _ h1 h2 => treeBlockF_at nb_205_96 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_205_112 h1 h2))) (block_join (fun _ h1 h2 => treeBlockF_at nb_205_128 h1 h2) (block_join (fun _ h1 h2 => treeBlockF_at nb_205_144 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_205_160 h1 h2)))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_205 : LowerBin m_205 s_205 g_205 10 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_205 sub_205 goal_205 rc_205 nc_205

def g_206 : Nat := 0x1171777077f7f7f

def b_206 : List (Nat × List Nat × Nat × Nat) := [(m_189, s_189, 10, g_189), (m_193, s_193, 10, g_193), (m_197, s_197, 10, g_197), (m_201, s_201, 10, g_201), (m_205, s_205, 10, g_205)]

theorem known_206 : KnownBin b_206 := by
  intro b hb
  simp only [b_206, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact lb_189
  · exact lb_193
  · exact lb_197
  · exact lb_201
  · exact lb_205

theorem sub_206 : ∀ b ∈ b_206, fullMask &&& b.1 = b.1 := by
  intro b hb
  simp only [b_206, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem goal_206 : ∀ b ∈ b_206, canon b.1 g_206 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [b_206, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def fd_206 : Array Nat := #[
  0x3f
]

def F_206 := shardForest fd_206 1 6

def ld_206 : Array (Nat → Nat → Option Nat) := #[
  unpackLinksF 0x9 0x3f 2 1 6 1 2
]

def L_206 := shardLinks ld_206

def st_206 := dagTraceF fullMask rootStock 11 F_206

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_206 : dagCheckRootsF fullMask g_206 b_206 (dagRefF 1 st_206 L_206 0) rootStock 11 = true := by
  decide +kernel

def ck_206 := dagCheckNodeF fullMask g_206 b_206 1 st_206 L_206

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_206_0 : treeBlockF 0 1 ck_206 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nc_206 : ∀ j, 0 ≤ j → j < 1 → ck_206 j = true :=
  (fun _ h1 h2 => treeBlockF_at nb_206_0 h1 h2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_206 : LowerBin fullMask rootStock g_206 12 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) known_206 sub_206 goal_206 rc_206 nc_206

def witness : List Gate :=
  [⟨GateOp.and, [0, 1]⟩,
   ⟨GateOp.or, [0, 1]⟩,
   ⟨GateOp.or, [3, 4]⟩,
   ⟨GateOp.and, [3, 4]⟩,
   ⟨GateOp.and, [5, 7]⟩,
   ⟨GateOp.and, [2, 8]⟩,
   ⟨GateOp.or, [2, 10]⟩,
   ⟨GateOp.and, [10, 11]⟩,
   ⟨GateOp.and, [9, 12]⟩,
   ⟨GateOp.or, [9, 12]⟩,
   ⟨GateOp.or, [6, 14]⟩,
   ⟨GateOp.or, [13, 16]⟩,
   ⟨GateOp.and, [15, 17]⟩]

theorem witnessMono : Monotone2 ⟨witness, 18⟩ := by
  simp [Monotone2, witness]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 6 → Bool,
    Circuit.eval ⟨witness, 18⟩ (List.ofFn x) =
      Nat.testBit (4276676744 * 2 ^ 32 + 4169171072) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

theorem targetLower : LowerBin fullMask rootStock (canon fullMask (4276676744 * 2 ^ 32 + 4169171072)) (13 - 1) := by
  rw [show canon fullMask (4276676744 * 2 ^ 32 + 4169171072) = g_206 by decide +kernel]
  exact lb_206

end PEqualNP.Outside.L_meta_49089

open PEqualNP.Outside.L_meta_49089 in
theorem PEqualNP.Outside.L_meta_49089 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676744 * 2 ^ 32 + 4169171072) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 4169171072) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  table2_from_lowerBin (4276676744 * 2 ^ 32 + 4169171072) 13 targetLower witness 18 rfl witnessMono witnessCorrect
