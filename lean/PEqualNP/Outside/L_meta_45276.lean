import PEqualNP.Defs

/- The live-wire checker and its soundness proof are from odinfree, open-goat/pequalnp-proofs PR 52901. The circuit and all certificate data below were generated for this table. -/

namespace PEqualNP.Outside.L_meta_45276

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



def m_0 : Nat := 0xa0a00000a0a

def s_0 : List Nat := [0x20200000202, 0xa0000000a, 0xa0a]

def g_0 : Nat := 0x20000020a

def bds_0 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_0 : KnownBin bds_0 := by
  intro b hb; simp [bds_0] at hb

theorem sub_0 : ∀ b ∈ bds_0, m_0 &&& b.1 = b.1 := by
  intro b hb; simp [bds_0] at hb

theorem gl_0 : ∀ b ∈ bds_0, canon b.1 g_0 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_0] at hb

def f_0 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_0 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_0 : dagCheckRootsF m_0 g_0 bds_0 (dagRefF 1 (dagTraceF m_0 s_0 3 f_0) l_0 0) s_0 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_0_0 : treeBlockF 0 1 (dagCheckNodeF m_0 g_0 bds_0 1 (dagTraceF m_0 s_0 3 f_0) l_0) = true := by decide +kernel

theorem join_0_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_0 g_0 bds_0 1 (dagTraceF m_0 s_0 3 f_0) l_0) j = true := (fun _ h₁ h₂ => treeBlockF_at block_0_0 h₁ h₂)

theorem nc_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_0 g_0 bds_0 1 (dagTraceF m_0 s_0 3 f_0) l_0) j = true := join_0_0

theorem lb_0 : LowerBin m_0 s_0 g_0 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_0 sub_0 gl_0 rc_0 nc_0

def m_1 : Nat := 0x44444444

def s_1 : List Nat := [0x4040404, 0x440044, 0x4444]

def g_1 : Nat := 0x40444

def bds_1 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_1 : KnownBin bds_1 := by
  intro b hb; simp [bds_1] at hb

theorem sub_1 : ∀ b ∈ bds_1, m_1 &&& b.1 = b.1 := by
  intro b hb; simp [bds_1] at hb

theorem gl_1 : ∀ b ∈ bds_1, canon b.1 g_1 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_1] at hb

def f_1 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_1 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_1 : dagCheckRootsF m_1 g_1 bds_1 (dagRefF 1 (dagTraceF m_1 s_1 3 f_1) l_1 0) s_1 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_1_0 : treeBlockF 0 1 (dagCheckNodeF m_1 g_1 bds_1 1 (dagTraceF m_1 s_1 3 f_1) l_1) = true := by decide +kernel

theorem join_1_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_1 g_1 bds_1 1 (dagTraceF m_1 s_1 3 f_1) l_1) j = true := (fun _ h₁ h₂ => treeBlockF_at block_1_0 h₁ h₂)

theorem nc_1 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_1 g_1 bds_1 1 (dagTraceF m_1 s_1 3 f_1) l_1) j = true := join_1_0

theorem lb_1 : LowerBin m_1 s_1 g_1 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1 sub_1 gl_1 rc_1 nc_1

def m_2 : Nat := 0xc0c0c0c

def s_2 : List Nat := [0x4040404, 0xc000c, 0xc0c]

def g_2 : Nat := 0x4040c

def bds_2 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_2 : KnownBin bds_2 := by
  intro b hb; simp [bds_2] at hb

theorem sub_2 : ∀ b ∈ bds_2, m_2 &&& b.1 = b.1 := by
  intro b hb; simp [bds_2] at hb

theorem gl_2 : ∀ b ∈ bds_2, canon b.1 g_2 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_2] at hb

def f_2 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_2 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_2 : dagCheckRootsF m_2 g_2 bds_2 (dagRefF 1 (dagTraceF m_2 s_2 3 f_2) l_2 0) s_2 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_2_0 : treeBlockF 0 1 (dagCheckNodeF m_2 g_2 bds_2 1 (dagTraceF m_2 s_2 3 f_2) l_2) = true := by decide +kernel

theorem join_2_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_2 g_2 bds_2 1 (dagTraceF m_2 s_2 3 f_2) l_2) j = true := (fun _ h₁ h₂ => treeBlockF_at block_2_0 h₁ h₂)

theorem nc_2 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_2 g_2 bds_2 1 (dagTraceF m_2 s_2 3 f_2) l_2) j = true := join_2_0

theorem lb_2 : LowerBin m_2 s_2 g_2 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2 sub_2 gl_2 rc_2 nc_2

def m_3 : Nat := 0xcc00cc

def s_3 : List Nat := [0x440044, 0xc000c, 0xcc]

def g_3 : Nat := 0x4004c

def bds_3 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_3 : KnownBin bds_3 := by
  intro b hb; simp [bds_3] at hb

theorem sub_3 : ∀ b ∈ bds_3, m_3 &&& b.1 = b.1 := by
  intro b hb; simp [bds_3] at hb

theorem gl_3 : ∀ b ∈ bds_3, canon b.1 g_3 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_3] at hb

def f_3 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_3 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_3 : dagCheckRootsF m_3 g_3 bds_3 (dagRefF 1 (dagTraceF m_3 s_3 3 f_3) l_3 0) s_3 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_3_0 : treeBlockF 0 1 (dagCheckNodeF m_3 g_3 bds_3 1 (dagTraceF m_3 s_3 3 f_3) l_3) = true := by decide +kernel

theorem join_3_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_3 g_3 bds_3 1 (dagTraceF m_3 s_3 3 f_3) l_3) j = true := (fun _ h₁ h₂ => treeBlockF_at block_3_0 h₁ h₂)

theorem nc_3 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_3 g_3 bds_3 1 (dagTraceF m_3 s_3 3 f_3) l_3) j = true := join_3_0

theorem lb_3 : LowerBin m_3 s_3 g_3 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_3 sub_3 gl_3 rc_3 nc_3

def m_4 : Nat := 0xcccc

def s_4 : List Nat := [0x4444, 0xc0c, 0xcc]

def g_4 : Nat := 0x44c

def bds_4 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_4 : KnownBin bds_4 := by
  intro b hb; simp [bds_4] at hb

theorem sub_4 : ∀ b ∈ bds_4, m_4 &&& b.1 = b.1 := by
  intro b hb; simp [bds_4] at hb

theorem gl_4 : ∀ b ∈ bds_4, canon b.1 g_4 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_4] at hb

def f_4 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_4 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_4 : dagCheckRootsF m_4 g_4 bds_4 (dagRefF 1 (dagTraceF m_4 s_4 3 f_4) l_4 0) s_4 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_4_0 : treeBlockF 0 1 (dagCheckNodeF m_4 g_4 bds_4 1 (dagTraceF m_4 s_4 3 f_4) l_4) = true := by decide +kernel

theorem join_4_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_4 g_4 bds_4 1 (dagTraceF m_4 s_4 3 f_4) l_4) j = true := (fun _ h₁ h₂ => treeBlockF_at block_4_0 h₁ h₂)

theorem nc_4 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_4 g_4 bds_4 1 (dagTraceF m_4 s_4 3 f_4) l_4) j = true := join_4_0

theorem lb_4 : LowerBin m_4 s_4 g_4 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_4 sub_4 gl_4 rc_4 nc_4

def m_5 : Nat := 0xcccccccc

def s_5 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]

def g_5 : Nat := 0x4044c

def bds_5 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_2, s_2, 4, g_2), (m_3, s_3, 4, g_3), (m_4, s_4, 4, g_4)]

theorem kn_5 : KnownBin bds_5 := by
  intro b hb; simp only [bds_5, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_1
  · exact lb_2
  · exact lb_3
  · exact lb_4

theorem sub_5 : ∀ b ∈ bds_5, m_5 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_5, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

theorem gl_5 : ∀ b ∈ bds_5, canon b.1 g_5 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_5, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

def f_5 : Nat → Nat × Nat := unpackForestF 0x1dd0360c4f408858d901918283c409874a4e149b41327c6064ba116422a9c5508a0c9341248240f88170f421c6235086270c42185c2908519094212642138421083e106418cc29985230866108c209800f 5 10

def l_5 : Nat → Nat → Option Nat := unpackLinksF 0x8e11c2384708e11c2384708e11c230c608c114620c408630c210c1182104200bf17c2f81e8bd0782ec5d0b91720e05c03715f09e0fc1781f01e00b001 0xaa40aa40ab40a418a1409930a1409530a3409c2c994095309a409630903c8c4c81417531892969216041503184294021834172327d3e69325c41382178192411774272426d4e69424c31342164191c1163415e4149323122583e4032542e242253424e3149422d22444e40423c2e1c223a42363231422d32284e2442203e1c321a33153311230c3308230413000f 11 4 10 6 5

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_5 : dagCheckRootsF m_5 g_5 bds_5 (dagRefF 43 (dagTraceF m_5 s_5 6 f_5) l_5 0) s_5 6 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_5_0 : treeBlockF 0 16 (dagCheckNodeF m_5 g_5 bds_5 43 (dagTraceF m_5 s_5 6 f_5) l_5) = true := by decide +kernel

theorem join_5_0 : ∀ j, 0 ≤ j → j < 16 → (dagCheckNodeF m_5 g_5 bds_5 43 (dagTraceF m_5 s_5 6 f_5) l_5) j = true := (fun _ h₁ h₂ => treeBlockF_at block_5_0 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_5_16 : treeBlockF 16 32 (dagCheckNodeF m_5 g_5 bds_5 43 (dagTraceF m_5 s_5 6 f_5) l_5) = true := by decide +kernel

theorem join_5_16 : ∀ j, 0 ≤ j → j < 32 → (dagCheckNodeF m_5 g_5 bds_5 43 (dagTraceF m_5 s_5 6 f_5) l_5) j = true := block_join join_5_0 (fun _ h₁ h₂ => treeBlockF_at block_5_16 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_5_32 : treeBlockF 32 43 (dagCheckNodeF m_5 g_5 bds_5 43 (dagTraceF m_5 s_5 6 f_5) l_5) = true := by decide +kernel

theorem join_5_32 : ∀ j, 0 ≤ j → j < 43 → (dagCheckNodeF m_5 g_5 bds_5 43 (dagTraceF m_5 s_5 6 f_5) l_5) j = true := block_join join_5_16 (fun _ h₁ h₂ => treeBlockF_at block_5_32 h₁ h₂)

theorem nc_5 : ∀ j, 0 ≤ j → j < 43 → (dagCheckNodeF m_5 g_5 bds_5 43 (dagTraceF m_5 s_5 6 f_5) l_5) j = true := join_5_32

theorem lb_5 : LowerBin m_5 s_5 g_5 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_5 sub_5 gl_5 rc_5 nc_5

def m_6 : Nat := 0x3300000000003300

def s_6 : List Nat := [0x1100000000001100, 0x300000000000300, 0x3300]

def g_6 : Nat := 0x100000000001300

def bds_6 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_6 : KnownBin bds_6 := by
  intro b hb; simp [bds_6] at hb

theorem sub_6 : ∀ b ∈ bds_6, m_6 &&& b.1 = b.1 := by
  intro b hb; simp [bds_6] at hb

theorem gl_6 : ∀ b ∈ bds_6, canon b.1 g_6 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_6] at hb

def f_6 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_6 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_6 : dagCheckRootsF m_6 g_6 bds_6 (dagRefF 1 (dagTraceF m_6 s_6 3 f_6) l_6 0) s_6 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_6_0 : treeBlockF 0 1 (dagCheckNodeF m_6 g_6 bds_6 1 (dagTraceF m_6 s_6 3 f_6) l_6) = true := by decide +kernel

theorem join_6_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_6 g_6 bds_6 1 (dagTraceF m_6 s_6 3 f_6) l_6) j = true := (fun _ h₁ h₂ => treeBlockF_at block_6_0 h₁ h₂)

theorem nc_6 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_6 g_6 bds_6 1 (dagTraceF m_6 s_6 3 f_6) l_6) j = true := join_6_0

theorem lb_6 : LowerBin m_6 s_6 g_6 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_6 sub_6 gl_6 rc_6 nc_6

def m_7 : Nat := 0x3000300003000300

def s_7 : List Nat := [0x1000100001000100, 0x3000300, 0x300000000300]

def g_7 : Nat := 0x100001000300

def bds_7 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_7 : KnownBin bds_7 := by
  intro b hb; simp [bds_7] at hb

theorem sub_7 : ∀ b ∈ bds_7, m_7 &&& b.1 = b.1 := by
  intro b hb; simp [bds_7] at hb

theorem gl_7 : ∀ b ∈ bds_7, canon b.1 g_7 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_7] at hb

def f_7 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_7 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_7 : dagCheckRootsF m_7 g_7 bds_7 (dagRefF 1 (dagTraceF m_7 s_7 3 f_7) l_7 0) s_7 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_7_0 : treeBlockF 0 1 (dagCheckNodeF m_7 g_7 bds_7 1 (dagTraceF m_7 s_7 3 f_7) l_7) = true := by decide +kernel

theorem join_7_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_7 g_7 bds_7 1 (dagTraceF m_7 s_7 3 f_7) l_7) j = true := (fun _ h₁ h₂ => treeBlockF_at block_7_0 h₁ h₂)

theorem nc_7 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_7 g_7 bds_7 1 (dagTraceF m_7 s_7 3 f_7) l_7) j = true := join_7_0

theorem lb_7 : LowerBin m_7 s_7 g_7 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_7 sub_7 gl_7 rc_7 nc_7

def m_8 : Nat := 0x3000030030000300

def s_8 : List Nat := [0x1000010010000100, 0x30000000300, 0x30000300]

def g_8 : Nat := 0x10010000300

def bds_8 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_8 : KnownBin bds_8 := by
  intro b hb; simp [bds_8] at hb

theorem sub_8 : ∀ b ∈ bds_8, m_8 &&& b.1 = b.1 := by
  intro b hb; simp [bds_8] at hb

theorem gl_8 : ∀ b ∈ bds_8, canon b.1 g_8 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_8] at hb

def f_8 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_8 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_8 : dagCheckRootsF m_8 g_8 bds_8 (dagRefF 1 (dagTraceF m_8 s_8 3 f_8) l_8 0) s_8 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_8_0 : treeBlockF 0 1 (dagCheckNodeF m_8 g_8 bds_8 1 (dagTraceF m_8 s_8 3 f_8) l_8) = true := by decide +kernel

theorem join_8_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_8 g_8 bds_8 1 (dagTraceF m_8 s_8 3 f_8) l_8) j = true := (fun _ h₁ h₂ => treeBlockF_at block_8_0 h₁ h₂)

theorem nc_8 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_8 g_8 bds_8 1 (dagTraceF m_8 s_8 3 f_8) l_8) j = true := join_8_0

theorem lb_8 : LowerBin m_8 s_8 g_8 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_8 sub_8 gl_8 rc_8 nc_8

def m_9 : Nat := 0x1200120012001200

def s_9 : List Nat := [0x200020002000200, 0x120000001200, 0x12001200]

def g_9 : Nat := 0x100010001200

def bds_9 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_9 : KnownBin bds_9 := by
  intro b hb; simp [bds_9] at hb

theorem sub_9 : ∀ b ∈ bds_9, m_9 &&& b.1 = b.1 := by
  intro b hb; simp [bds_9] at hb

theorem gl_9 : ∀ b ∈ bds_9, canon b.1 g_9 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_9] at hb

def f_9 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_9 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_9 : dagCheckRootsF m_9 g_9 bds_9 (dagRefF 1 (dagTraceF m_9 s_9 3 f_9) l_9 0) s_9 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_9_0 : treeBlockF 0 1 (dagCheckNodeF m_9 g_9 bds_9 1 (dagTraceF m_9 s_9 3 f_9) l_9) = true := by decide +kernel

theorem join_9_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_9 g_9 bds_9 1 (dagTraceF m_9 s_9 3 f_9) l_9) j = true := (fun _ h₁ h₂ => treeBlockF_at block_9_0 h₁ h₂)

theorem nc_9 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_9 g_9 bds_9 1 (dagTraceF m_9 s_9 3 f_9) l_9) j = true := join_9_0

theorem lb_9 : LowerBin m_9 s_9 g_9 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_9 sub_9 gl_9 rc_9 nc_9

def m_10 : Nat := 0x1100220011002200

def s_10 : List Nat := [0x220000002200, 0x100020001000200, 0x11002200]

def g_10 : Nat := 0x100000011000200

def bds_10 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_10 : KnownBin bds_10 := by
  intro b hb; simp [bds_10] at hb

theorem sub_10 : ∀ b ∈ bds_10, m_10 &&& b.1 = b.1 := by
  intro b hb; simp [bds_10] at hb

theorem gl_10 : ∀ b ∈ bds_10, canon b.1 g_10 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_10] at hb

def f_10 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_10 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_10 : dagCheckRootsF m_10 g_10 bds_10 (dagRefF 1 (dagTraceF m_10 s_10 3 f_10) l_10 0) s_10 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_10_0 : treeBlockF 0 1 (dagCheckNodeF m_10 g_10 bds_10 1 (dagTraceF m_10 s_10 3 f_10) l_10) = true := by decide +kernel

theorem join_10_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_10 g_10 bds_10 1 (dagTraceF m_10 s_10 3 f_10) l_10) j = true := (fun _ h₁ h₂ => treeBlockF_at block_10_0 h₁ h₂)

theorem nc_10 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_10 g_10 bds_10 1 (dagTraceF m_10 s_10 3 f_10) l_10) j = true := join_10_0

theorem lb_10 : LowerBin m_10 s_10 g_10 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_10 sub_10 gl_10 rc_10 nc_10

def m_11 : Nat := 0x1100110022002200

def s_11 : List Nat := [0x22002200, 0x100010002000200, 0x110000002200]

def g_11 : Nat := 0x100110000000200

def bds_11 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_11 : KnownBin bds_11 := by
  intro b hb; simp [bds_11] at hb

theorem sub_11 : ∀ b ∈ bds_11, m_11 &&& b.1 = b.1 := by
  intro b hb; simp [bds_11] at hb

theorem gl_11 : ∀ b ∈ bds_11, canon b.1 g_11 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_11] at hb

def f_11 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_11 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_11 : dagCheckRootsF m_11 g_11 bds_11 (dagRefF 1 (dagTraceF m_11 s_11 3 f_11) l_11 0) s_11 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_11_0 : treeBlockF 0 1 (dagCheckNodeF m_11 g_11 bds_11 1 (dagTraceF m_11 s_11 3 f_11) l_11) = true := by decide +kernel

theorem join_11_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_11 g_11 bds_11 1 (dagTraceF m_11 s_11 3 f_11) l_11) j = true := (fun _ h₁ h₂ => treeBlockF_at block_11_0 h₁ h₂)

theorem nc_11 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_11 g_11 bds_11 1 (dagTraceF m_11 s_11 3 f_11) l_11) j = true := join_11_0

theorem lb_11 : LowerBin m_11 s_11 g_11 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_11 sub_11 gl_11 rc_11 nc_11

def m_12 : Nat := 0x3300330033003300

def s_12 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]

def g_12 : Nat := 0x100110011001300

def bds_12 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6), (m_7, s_7, 4, g_7), (m_8, s_8, 4, g_8), (m_9, s_9, 4, g_9), (m_10, s_10, 4, g_10), (m_11, s_11, 4, g_11)]

theorem kn_12 : KnownBin bds_12 := by
  intro b hb; simp only [bds_12, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_6
  · exact lb_7
  · exact lb_8
  · exact lb_9
  · exact lb_10
  · exact lb_11

theorem sub_12 : ∀ b ∈ bds_12, m_12 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_12, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem gl_12 : ∀ b ∈ bds_12, canon b.1 g_12 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_12, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def f_12 : Nat → Nat × Nat := unpackForestF 0x63fc774fe9dd27a470fe1dc2784705e0980f 1 10

def l_12 : Nat → Nat → Option Nat := unpackLinksF 0xd0d0d0d0d0d0d0d0d0d0d0d01c01 0x323fb8ee93f94ee127748d83f50ed027308c817104c00f 8 4 10 4 5

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_12 : dagCheckRootsF m_12 g_12 bds_12 (dagRefF 13 (dagTraceF m_12 s_12 5 f_12) l_12 0) s_12 5 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_12_0 : treeBlockF 0 13 (dagCheckNodeF m_12 g_12 bds_12 13 (dagTraceF m_12 s_12 5 f_12) l_12) = true := by decide +kernel

theorem join_12_0 : ∀ j, 0 ≤ j → j < 13 → (dagCheckNodeF m_12 g_12 bds_12 13 (dagTraceF m_12 s_12 5 f_12) l_12) j = true := (fun _ h₁ h₂ => treeBlockF_at block_12_0 h₁ h₂)

theorem nc_12 : ∀ j, 0 ≤ j → j < 13 → (dagCheckNodeF m_12 g_12 bds_12 13 (dagTraceF m_12 s_12 5 f_12) l_12) j = true := join_12_0

theorem lb_12 : LowerBin m_12 s_12 g_12 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_12 sub_12 gl_12 rc_12 nc_12

def m_13 : Nat := 0x5500000000005500

def s_13 : List Nat := [0x1100000000001100, 0x500000000000500, 0x5500]

def g_13 : Nat := 0x100000000001500

def bds_13 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_13 : KnownBin bds_13 := by
  intro b hb; simp [bds_13] at hb

theorem sub_13 : ∀ b ∈ bds_13, m_13 &&& b.1 = b.1 := by
  intro b hb; simp [bds_13] at hb

theorem gl_13 : ∀ b ∈ bds_13, canon b.1 g_13 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_13] at hb

def f_13 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_13 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_13 : dagCheckRootsF m_13 g_13 bds_13 (dagRefF 1 (dagTraceF m_13 s_13 3 f_13) l_13 0) s_13 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_13_0 : treeBlockF 0 1 (dagCheckNodeF m_13 g_13 bds_13 1 (dagTraceF m_13 s_13 3 f_13) l_13) = true := by decide +kernel

theorem join_13_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_13 g_13 bds_13 1 (dagTraceF m_13 s_13 3 f_13) l_13) j = true := (fun _ h₁ h₂ => treeBlockF_at block_13_0 h₁ h₂)

theorem nc_13 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_13 g_13 bds_13 1 (dagTraceF m_13 s_13 3 f_13) l_13) j = true := join_13_0

theorem lb_13 : LowerBin m_13 s_13 g_13 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_13 sub_13 gl_13 rc_13 nc_13

def m_14 : Nat := 0xf00000000000f00

def s_14 : List Nat := [0x500000000000500, 0x300000000000300, 0xf00]

def g_14 : Nat := 0x100000000000700

def bds_14 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_14 : KnownBin bds_14 := by
  intro b hb; simp [bds_14] at hb

theorem sub_14 : ∀ b ∈ bds_14, m_14 &&& b.1 = b.1 := by
  intro b hb; simp [bds_14] at hb

theorem gl_14 : ∀ b ∈ bds_14, canon b.1 g_14 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_14] at hb

def f_14 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_14 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_14 : dagCheckRootsF m_14 g_14 bds_14 (dagRefF 1 (dagTraceF m_14 s_14 3 f_14) l_14 0) s_14 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_14_0 : treeBlockF 0 1 (dagCheckNodeF m_14 g_14 bds_14 1 (dagTraceF m_14 s_14 3 f_14) l_14) = true := by decide +kernel

theorem join_14_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_14 g_14 bds_14 1 (dagTraceF m_14 s_14 3 f_14) l_14) j = true := (fun _ h₁ h₂ => treeBlockF_at block_14_0 h₁ h₂)

theorem nc_14 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_14 g_14 bds_14 1 (dagTraceF m_14 s_14 3 f_14) l_14) j = true := join_14_0

theorem lb_14 : LowerBin m_14 s_14 g_14 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_14 sub_14 gl_14 rc_14 nc_14

def m_15 : Nat := 0xff00

def s_15 : List Nat := [0x5500, 0x3300, 0xf00]

def g_15 : Nat := 0x1700

def bds_15 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_15 : KnownBin bds_15 := by
  intro b hb; simp [bds_15] at hb

theorem sub_15 : ∀ b ∈ bds_15, m_15 &&& b.1 = b.1 := by
  intro b hb; simp [bds_15] at hb

theorem gl_15 : ∀ b ∈ bds_15, canon b.1 g_15 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_15] at hb

def f_15 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_15 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_15 : dagCheckRootsF m_15 g_15 bds_15 (dagRefF 1 (dagTraceF m_15 s_15 3 f_15) l_15 0) s_15 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_15_0 : treeBlockF 0 1 (dagCheckNodeF m_15 g_15 bds_15 1 (dagTraceF m_15 s_15 3 f_15) l_15) = true := by decide +kernel

theorem join_15_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_15 g_15 bds_15 1 (dagTraceF m_15 s_15 3 f_15) l_15) j = true := (fun _ h₁ h₂ => treeBlockF_at block_15_0 h₁ h₂)

theorem nc_15 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_15 g_15 bds_15 1 (dagTraceF m_15 s_15 3 f_15) l_15) j = true := join_15_0

theorem lb_15 : LowerBin m_15 s_15 g_15 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_15 sub_15 gl_15 rc_15 nc_15

def m_16 : Nat := 0xff0000000000ff00

def s_16 : List Nat := [0x5500000000005500, 0x3300000000003300, 0xf00000000000f00, 0xff00]

def g_16 : Nat := 0x100000000001700

def bds_16 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13), (m_6, s_6, 4, g_6), (m_14, s_14, 4, g_14), (m_15, s_15, 4, g_15)]

theorem kn_16 : KnownBin bds_16 := by
  intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_13
  · exact lb_6
  · exact lb_14
  · exact lb_15

theorem sub_16 : ∀ b ∈ bds_16, m_16 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

theorem gl_16 : ∀ b ∈ bds_16, canon b.1 g_16 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

def f_16 : Nat → Nat × Nat := unpackForestF 0x1dd0360c4f408858d901918283c409874a4e149b41327c6064ba116422a9c5508a0c9341248240f88170f421c6235086270c42185c2908519094212642138421083e106418cc29985230866108c209800f 5 10

def l_16 : Nat → Nat → Option Nat := unpackLinksF 0x8e11c2384708e11c2384708e11c230c608c114620c408630c210c1182104200bf17c2f81e8bd0782ec5d0b91720e05c03715f09e0fc1781f01e00b001 0xaa40aa40ab40a418a1409930a1409530a3409c2c994095309a409630903c8c4c81417531892969216041503184294021834172327d3e69325c41382178192411774272426d4e69424c31342164191c1163415e4149323122583e4032542e242253424e3149422d22444e40423c2e1c223a42363231422d32284e2442203e1c321a33153311230c3308230413000f 11 4 10 6 5

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_16 : dagCheckRootsF m_16 g_16 bds_16 (dagRefF 43 (dagTraceF m_16 s_16 6 f_16) l_16 0) s_16 6 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_16_0 : treeBlockF 0 16 (dagCheckNodeF m_16 g_16 bds_16 43 (dagTraceF m_16 s_16 6 f_16) l_16) = true := by decide +kernel

theorem join_16_0 : ∀ j, 0 ≤ j → j < 16 → (dagCheckNodeF m_16 g_16 bds_16 43 (dagTraceF m_16 s_16 6 f_16) l_16) j = true := (fun _ h₁ h₂ => treeBlockF_at block_16_0 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_16_16 : treeBlockF 16 32 (dagCheckNodeF m_16 g_16 bds_16 43 (dagTraceF m_16 s_16 6 f_16) l_16) = true := by decide +kernel

theorem join_16_16 : ∀ j, 0 ≤ j → j < 32 → (dagCheckNodeF m_16 g_16 bds_16 43 (dagTraceF m_16 s_16 6 f_16) l_16) j = true := block_join join_16_0 (fun _ h₁ h₂ => treeBlockF_at block_16_16 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_16_32 : treeBlockF 32 43 (dagCheckNodeF m_16 g_16 bds_16 43 (dagTraceF m_16 s_16 6 f_16) l_16) = true := by decide +kernel

theorem join_16_32 : ∀ j, 0 ≤ j → j < 43 → (dagCheckNodeF m_16 g_16 bds_16 43 (dagTraceF m_16 s_16 6 f_16) l_16) j = true := block_join join_16_16 (fun _ h₁ h₂ => treeBlockF_at block_16_32 h₁ h₂)

theorem nc_16 : ∀ j, 0 ≤ j → j < 43 → (dagCheckNodeF m_16 g_16 bds_16 43 (dagTraceF m_16 s_16 6 f_16) l_16) j = true := join_16_32

theorem lb_16 : LowerBin m_16 s_16 g_16 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_16 sub_16 gl_16 rc_16 nc_16

def m_17 : Nat := 0x5000500005000500

def s_17 : List Nat := [0x1000100001000100, 0x5000500, 0x500000000500]

def g_17 : Nat := 0x100001000500

def bds_17 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_17 : KnownBin bds_17 := by
  intro b hb; simp [bds_17] at hb

theorem sub_17 : ∀ b ∈ bds_17, m_17 &&& b.1 = b.1 := by
  intro b hb; simp [bds_17] at hb

theorem gl_17 : ∀ b ∈ bds_17, canon b.1 g_17 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_17] at hb

def f_17 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_17 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_17 : dagCheckRootsF m_17 g_17 bds_17 (dagRefF 1 (dagTraceF m_17 s_17 3 f_17) l_17 0) s_17 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_17_0 : treeBlockF 0 1 (dagCheckNodeF m_17 g_17 bds_17 1 (dagTraceF m_17 s_17 3 f_17) l_17) = true := by decide +kernel

theorem join_17_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_17 g_17 bds_17 1 (dagTraceF m_17 s_17 3 f_17) l_17) j = true := (fun _ h₁ h₂ => treeBlockF_at block_17_0 h₁ h₂)

theorem nc_17 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_17 g_17 bds_17 1 (dagTraceF m_17 s_17 3 f_17) l_17) j = true := join_17_0

theorem lb_17 : LowerBin m_17 s_17 g_17 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_17 sub_17 gl_17 rc_17 nc_17

def m_18 : Nat := 0xf00000000f00

def s_18 : List Nat := [0x500000000500, 0x300000000300, 0xf00]

def g_18 : Nat := 0x100000000700

def bds_18 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_18 : KnownBin bds_18 := by
  intro b hb; simp [bds_18] at hb

theorem sub_18 : ∀ b ∈ bds_18, m_18 &&& b.1 = b.1 := by
  intro b hb; simp [bds_18] at hb

theorem gl_18 : ∀ b ∈ bds_18, canon b.1 g_18 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_18] at hb

def f_18 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_18 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_18 : dagCheckRootsF m_18 g_18 bds_18 (dagRefF 1 (dagTraceF m_18 s_18 3 f_18) l_18 0) s_18 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_18_0 : treeBlockF 0 1 (dagCheckNodeF m_18 g_18 bds_18 1 (dagTraceF m_18 s_18 3 f_18) l_18) = true := by decide +kernel

theorem join_18_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_18 g_18 bds_18 1 (dagTraceF m_18 s_18 3 f_18) l_18) j = true := (fun _ h₁ h₂ => treeBlockF_at block_18_0 h₁ h₂)

theorem nc_18 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_18 g_18 bds_18 1 (dagTraceF m_18 s_18 3 f_18) l_18) j = true := join_18_0

theorem lb_18 : LowerBin m_18 s_18 g_18 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_18 sub_18 gl_18 rc_18 nc_18

def m_19 : Nat := 0xf000f00

def s_19 : List Nat := [0x5000500, 0x3000300, 0xf00]

def g_19 : Nat := 0x1000700

def bds_19 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_19 : KnownBin bds_19 := by
  intro b hb; simp [bds_19] at hb

theorem sub_19 : ∀ b ∈ bds_19, m_19 &&& b.1 = b.1 := by
  intro b hb; simp [bds_19] at hb

theorem gl_19 : ∀ b ∈ bds_19, canon b.1 g_19 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_19] at hb

def f_19 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_19 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_19 : dagCheckRootsF m_19 g_19 bds_19 (dagRefF 1 (dagTraceF m_19 s_19 3 f_19) l_19 0) s_19 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_19_0 : treeBlockF 0 1 (dagCheckNodeF m_19 g_19 bds_19 1 (dagTraceF m_19 s_19 3 f_19) l_19) = true := by decide +kernel

theorem join_19_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_19 g_19 bds_19 1 (dagTraceF m_19 s_19 3 f_19) l_19) j = true := (fun _ h₁ h₂ => treeBlockF_at block_19_0 h₁ h₂)

theorem nc_19 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_19 g_19 bds_19 1 (dagTraceF m_19 s_19 3 f_19) l_19) j = true := join_19_0

theorem lb_19 : LowerBin m_19 s_19 g_19 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_19 sub_19 gl_19 rc_19 nc_19

def m_20 : Nat := 0xf000f0000f000f00

def s_20 : List Nat := [0x5000500005000500, 0x3000300003000300, 0xf000f00, 0xf00000000f00]

def g_20 : Nat := 0x100001000700

def bds_20 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 4, g_17), (m_7, s_7, 4, g_7), (m_18, s_18, 4, g_18), (m_19, s_19, 4, g_19)]

theorem kn_20 : KnownBin bds_20 := by
  intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_17
  · exact lb_7
  · exact lb_18
  · exact lb_19

theorem sub_20 : ∀ b ∈ bds_20, m_20 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

theorem gl_20 : ∀ b ∈ bds_20, canon b.1 g_20 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

def f_20 : Nat → Nat × Nat := unpackForestF 0x1dd0360c4f408858d901918283c409874a4e149b41327c6064ba116422a9c5508a0c9341248240f88170f421c6235086270c42185c2908519094212642138421083e106418cc29985230866108c209800f 5 10

def l_20 : Nat → Nat → Option Nat := unpackLinksF 0x8e11c2384708e11c2384708e11c230c608c114620c408630c210c1182104200bf17c2f81e8bd0782ec5d0b91720e05c03715f09e0fc1781f01e00b001 0xaa40aa40ab40a418a1409930a1409530a3409c2c994095309a409630903c8c4c81417531892969216041503184294021834172327d3e69325c41382178192411774272426d4e69424c31342164191c1163415e4149323122583e4032542e242253424e3149422d22444e40423c2e1c223a42363231422d32284e2442203e1c321a33153311230c3308230413000f 11 4 10 6 5

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_20 : dagCheckRootsF m_20 g_20 bds_20 (dagRefF 43 (dagTraceF m_20 s_20 6 f_20) l_20 0) s_20 6 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_20_0 : treeBlockF 0 16 (dagCheckNodeF m_20 g_20 bds_20 43 (dagTraceF m_20 s_20 6 f_20) l_20) = true := by decide +kernel

theorem join_20_0 : ∀ j, 0 ≤ j → j < 16 → (dagCheckNodeF m_20 g_20 bds_20 43 (dagTraceF m_20 s_20 6 f_20) l_20) j = true := (fun _ h₁ h₂ => treeBlockF_at block_20_0 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_20_16 : treeBlockF 16 32 (dagCheckNodeF m_20 g_20 bds_20 43 (dagTraceF m_20 s_20 6 f_20) l_20) = true := by decide +kernel

theorem join_20_16 : ∀ j, 0 ≤ j → j < 32 → (dagCheckNodeF m_20 g_20 bds_20 43 (dagTraceF m_20 s_20 6 f_20) l_20) j = true := block_join join_20_0 (fun _ h₁ h₂ => treeBlockF_at block_20_16 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_20_32 : treeBlockF 32 43 (dagCheckNodeF m_20 g_20 bds_20 43 (dagTraceF m_20 s_20 6 f_20) l_20) = true := by decide +kernel

theorem join_20_32 : ∀ j, 0 ≤ j → j < 43 → (dagCheckNodeF m_20 g_20 bds_20 43 (dagTraceF m_20 s_20 6 f_20) l_20) j = true := block_join join_20_16 (fun _ h₁ h₂ => treeBlockF_at block_20_32 h₁ h₂)

theorem nc_20 : ∀ j, 0 ≤ j → j < 43 → (dagCheckNodeF m_20 g_20 bds_20 43 (dagTraceF m_20 s_20 6 f_20) l_20) j = true := join_20_32

theorem lb_20 : LowerBin m_20 s_20 g_20 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_20 sub_20 gl_20 rc_20 nc_20

def m_21 : Nat := 0xf0000f00f0000f00

def s_21 : List Nat := [0x5000050050000500, 0x3000030030000300, 0xf0000000f00, 0xf0000f00]

def g_21 : Nat := 0x50010000700

def bds_21 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]

theorem kn_21 : KnownBin bds_21 := by
  intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8

theorem sub_21 : ∀ b ∈ bds_21, m_21 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_21 : ∀ b ∈ bds_21, canon b.1 g_21 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_21 : Nat → Nat × Nat := fun _ => (0, 0)

def l_21 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_21 : dagCheckRootsF m_21 g_21 bds_21 (dagRefF 0 (dagTraceF m_21 s_21 4 f_21) l_21 0) s_21 4 = true := by decide +kernel

theorem nc_21 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_21 g_21 bds_21 0 (dagTraceF m_21 s_21 4 f_21) l_21) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_21 : LowerBin m_21 s_21 g_21 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_21 sub_21 gl_21 rc_21 nc_21

def m_22 : Nat := 0x5500550000000000

def s_22 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]

def g_22 : Nat := 0x100150000000000

def bds_22 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_22 : KnownBin bds_22 := by
  intro b hb; simp [bds_22] at hb

theorem sub_22 : ∀ b ∈ bds_22, m_22 &&& b.1 = b.1 := by
  intro b hb; simp [bds_22] at hb

theorem gl_22 : ∀ b ∈ bds_22, canon b.1 g_22 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_22] at hb

def f_22 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_22 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_22 : dagCheckRootsF m_22 g_22 bds_22 (dagRefF 1 (dagTraceF m_22 s_22 3 f_22) l_22 0) s_22 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_22_0 : treeBlockF 0 1 (dagCheckNodeF m_22 g_22 bds_22 1 (dagTraceF m_22 s_22 3 f_22) l_22) = true := by decide +kernel

theorem join_22_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_22 g_22 bds_22 1 (dagTraceF m_22 s_22 3 f_22) l_22) j = true := (fun _ h₁ h₂ => treeBlockF_at block_22_0 h₁ h₂)

theorem nc_22 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_22 g_22 bds_22 1 (dagTraceF m_22 s_22 3 f_22) l_22) j = true := join_22_0

theorem lb_22 : LowerBin m_22 s_22 g_22 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_22 sub_22 gl_22 rc_22 nc_22

def m_23 : Nat := 0x50005000a000a00

def s_23 : List Nat := [0xa000a00, 0x100010002000200, 0x50000000a00]

def g_23 : Nat := 0x100050000000200

def bds_23 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_23 : KnownBin bds_23 := by
  intro b hb; simp [bds_23] at hb

theorem sub_23 : ∀ b ∈ bds_23, m_23 &&& b.1 = b.1 := by
  intro b hb; simp [bds_23] at hb

theorem gl_23 : ∀ b ∈ bds_23, canon b.1 g_23 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_23] at hb

def f_23 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_23 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_23 : dagCheckRootsF m_23 g_23 bds_23 (dagRefF 1 (dagTraceF m_23 s_23 3 f_23) l_23 0) s_23 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_23_0 : treeBlockF 0 1 (dagCheckNodeF m_23 g_23 bds_23 1 (dagTraceF m_23 s_23 3 f_23) l_23) = true := by decide +kernel

theorem join_23_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_23 g_23 bds_23 1 (dagTraceF m_23 s_23 3 f_23) l_23) j = true := (fun _ h₁ h₂ => treeBlockF_at block_23_0 h₁ h₂)

theorem nc_23 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_23 g_23 bds_23 1 (dagTraceF m_23 s_23 3 f_23) l_23) j = true := join_23_0

theorem lb_23 : LowerBin m_23 s_23 g_23 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_23 sub_23 gl_23 rc_23 nc_23

def m_24 : Nat := 0x55000000aa00

def s_24 : List Nat := [0xaa00, 0x110000002200, 0x50000000a00]

def g_24 : Nat := 0x150000000200

def bds_24 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_24 : KnownBin bds_24 := by
  intro b hb; simp [bds_24] at hb

theorem sub_24 : ∀ b ∈ bds_24, m_24 &&& b.1 = b.1 := by
  intro b hb; simp [bds_24] at hb

theorem gl_24 : ∀ b ∈ bds_24, canon b.1 g_24 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_24] at hb

def f_24 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_24 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_24 : dagCheckRootsF m_24 g_24 bds_24 (dagRefF 1 (dagTraceF m_24 s_24 3 f_24) l_24 0) s_24 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_24_0 : treeBlockF 0 1 (dagCheckNodeF m_24 g_24 bds_24 1 (dagTraceF m_24 s_24 3 f_24) l_24) = true := by decide +kernel

theorem join_24_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_24 g_24 bds_24 1 (dagTraceF m_24 s_24 3 f_24) l_24) j = true := (fun _ h₁ h₂ => treeBlockF_at block_24_0 h₁ h₂)

theorem nc_24 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_24 g_24 bds_24 1 (dagTraceF m_24 s_24 3 f_24) l_24) j = true := join_24_0

theorem lb_24 : LowerBin m_24 s_24 g_24 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_24 sub_24 gl_24 rc_24 nc_24

def m_25 : Nat := 0x55005500aa00aa00

def s_25 : List Nat := [0xaa00aa00, 0x1100110022002200, 0x50005000a000a00, 0x55000000aa00]

def g_25 : Nat := 0x100150000000200

def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_22, s_22, 4, g_22), (m_11, s_11, 4, g_11), (m_23, s_23, 4, g_23), (m_24, s_24, 4, g_24)]

theorem kn_25 : KnownBin bds_25 := by
  intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_22
  · exact lb_11
  · exact lb_23
  · exact lb_24

theorem sub_25 : ∀ b ∈ bds_25, m_25 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

theorem gl_25 : ∀ b ∈ bds_25, canon b.1 g_25 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

def f_25 : Nat → Nat × Nat := unpackForestF 0x1dd0360a4d288480c4f14a62540426074a4e129b41327c6054ba116422a9c5508a0a92412472450489c8f421c9c39086988d29189c2908519094e128424f8499084e107c18cc2998523087e10bc20f800f 5 10

def l_25 : Nat → Nat → Option Nat := unpackLinksF 0x8e11c2384708e11c2384708e11c230c608c114620c408630c210c2082304200c007e2f85f03d1782ec5d83a1740e45c0b715f09e0fc1781f01e00b001 0xaa40aa40ab40a4149c3c902c9c4ca1288c2c9e40904c8c3c993c954c91408d308141753189296921604d503d482d8425834172327d3e6932584d382d2c1d7815774272426d4e6942443d342d241d641562415e394a31594155392d313c2e201e53424e4e4a424531412925213c4e1c1e3a423632314e2d42293e2532204e1c3e1a33153311230c3f082f041f000f 11 4 10 6 5

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_25 : dagCheckRootsF m_25 g_25 bds_25 (dagRefF 43 (dagTraceF m_25 s_25 6 f_25) l_25 0) s_25 6 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_25_0 : treeBlockF 0 16 (dagCheckNodeF m_25 g_25 bds_25 43 (dagTraceF m_25 s_25 6 f_25) l_25) = true := by decide +kernel

theorem join_25_0 : ∀ j, 0 ≤ j → j < 16 → (dagCheckNodeF m_25 g_25 bds_25 43 (dagTraceF m_25 s_25 6 f_25) l_25) j = true := (fun _ h₁ h₂ => treeBlockF_at block_25_0 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_25_16 : treeBlockF 16 32 (dagCheckNodeF m_25 g_25 bds_25 43 (dagTraceF m_25 s_25 6 f_25) l_25) = true := by decide +kernel

theorem join_25_16 : ∀ j, 0 ≤ j → j < 32 → (dagCheckNodeF m_25 g_25 bds_25 43 (dagTraceF m_25 s_25 6 f_25) l_25) j = true := block_join join_25_0 (fun _ h₁ h₂ => treeBlockF_at block_25_16 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_25_32 : treeBlockF 32 43 (dagCheckNodeF m_25 g_25 bds_25 43 (dagTraceF m_25 s_25 6 f_25) l_25) = true := by decide +kernel

theorem join_25_32 : ∀ j, 0 ≤ j → j < 43 → (dagCheckNodeF m_25 g_25 bds_25 43 (dagTraceF m_25 s_25 6 f_25) l_25) j = true := block_join join_25_16 (fun _ h₁ h₂ => treeBlockF_at block_25_32 h₁ h₂)

theorem nc_25 : ∀ j, 0 ≤ j → j < 43 → (dagCheckNodeF m_25 g_25 bds_25 43 (dagTraceF m_25 s_25 6 f_25) l_25) j = true := join_25_32

theorem lb_25 : LowerBin m_25 s_25 g_25 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_25 sub_25 gl_25 rc_25 nc_25

def m_26 : Nat := 0x5500550055005500

def s_26 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]

def g_26 : Nat := 0x100150011001500

def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_22, s_22, 4, g_22)]

theorem kn_26 : KnownBin bds_26 := by
  intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_22

theorem sub_26 : ∀ b ∈ bds_26, m_26 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_26 : ∀ b ∈ bds_26, canon b.1 g_26 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_26 : Nat → Nat × Nat := fun _ => (0, 0)

def l_26 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_26 : dagCheckRootsF m_26 g_26 bds_26 (dagRefF 0 (dagTraceF m_26 s_26 4 f_26) l_26 0) s_26 4 = true := by decide +kernel

theorem nc_26 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_26 g_26 bds_26 0 (dagTraceF m_26 s_26 4 f_26) l_26) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_26 sub_26 gl_26 rc_26 nc_26

def m_27 : Nat := 0x5a005a005a005a00

def s_27 : List Nat := [0xa000a000a000a00, 0x1200120012001200, 0x5a0000005a00, 0x5a005a00]

def g_27 : Nat := 0x100010001200

def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]

theorem kn_27 : KnownBin bds_27 := by
  intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9

theorem sub_27 : ∀ b ∈ bds_27, m_27 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_27 : Nat → Nat × Nat := fun _ => (0, 0)

def l_27 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_27 : dagCheckRootsF m_27 g_27 bds_27 (dagRefF 0 (dagTraceF m_27 s_27 4 f_27) l_27 0) s_27 4 = true := by decide +kernel

theorem nc_27 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_27 g_27 bds_27 0 (dagTraceF m_27 s_27 4 f_27) l_27) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0xf000f000f000f00

def s_28 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]

def g_28 : Nat := 0x100050001000700

def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 4, g_19)]

theorem kn_28 : KnownBin bds_28 := by
  intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_19

theorem sub_28 : ∀ b ∈ bds_28, m_28 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_28 : Nat → Nat × Nat := fun _ => (0, 0)

def l_28 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_28 : dagCheckRootsF m_28 g_28 bds_28 (dagRefF 0 (dagTraceF m_28 s_28 4 f_28) l_28 0) s_28 4 = true := by decide +kernel

theorem nc_28 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_28 g_28 bds_28 0 (dagTraceF m_28 s_28 4 f_28) l_28) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_28 sub_28 gl_28 rc_28 nc_28

def m_29 : Nat := 0x5500aa005500aa00

def s_29 : List Nat := [0xaa000000aa00, 0x1100220011002200, 0x5000a0005000a00, 0x5500aa00]

def g_29 : Nat := 0x100000011000200

def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]

theorem kn_29 : KnownBin bds_29 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_10

theorem sub_29 : ∀ b ∈ bds_29, m_29 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_29 : ∀ b ∈ bds_29, canon b.1 g_29 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_29 : Nat → Nat × Nat := fun _ => (0, 0)

def l_29 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_29 : dagCheckRootsF m_29 g_29 bds_29 (dagRefF 0 (dagTraceF m_29 s_29 4 f_29) l_29 0) s_29 4 = true := by decide +kernel

theorem nc_29 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_29 g_29 bds_29 0 (dagTraceF m_29 s_29 4 f_29) l_29) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_29 sub_29 gl_29 rc_29 nc_29

def m_30 : Nat := 0xff000000ff00

def s_30 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]

def g_30 : Nat := 0x150000001700

def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]

theorem kn_30 : KnownBin bds_30 := by
  intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_15

theorem sub_30 : ∀ b ∈ bds_30, m_30 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_30 : Nat → Nat × Nat := fun _ => (0, 0)

def l_30 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_30 : dagCheckRootsF m_30 g_30 bds_30 (dagRefF 0 (dagTraceF m_30 s_30 4 f_30) l_30 0) s_30 4 = true := by decide +kernel

theorem nc_30 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_30 g_30 bds_30 0 (dagTraceF m_30 s_30 4 f_30) l_30) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_30 sub_30 gl_30 rc_30 nc_30

def m_31 : Nat := 0xff00ff0000000000

def s_31 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]

def g_31 : Nat := 0x100150000000000

def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_22, s_22, 4, g_22)]

theorem kn_31 : KnownBin bds_31 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_22

theorem sub_31 : ∀ b ∈ bds_31, m_31 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_31 : Nat → Nat × Nat := fun _ => (0, 0)

def l_31 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_31 : dagCheckRootsF m_31 g_31 bds_31 (dagRefF 0 (dagTraceF m_31 s_31 4 f_31) l_31 0) s_31 4 = true := by decide +kernel

theorem nc_31 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_31 g_31 bds_31 0 (dagTraceF m_31 s_31 4 f_31) l_31) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_31 sub_31 gl_31 rc_31 nc_31

def m_32 : Nat := 0xff00ff00ff00ff00

def s_32 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]

def g_32 : Nat := 0x100150011001700

def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 6, g_12), (m_16, s_16, 7, g_16), (m_20, s_20, 7, g_20), (m_21, s_21, 5, g_21), (m_25, s_25, 7, g_25), (m_26, s_26, 5, g_26), (m_27, s_27, 5, g_27), (m_28, s_28, 5, g_28), (m_29, s_29, 5, g_29), (m_30, s_30, 5, g_30), (m_31, s_31, 5, g_31)]

theorem kn_32 : KnownBin bds_32 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_12
  · exact lb_16
  · exact lb_20
  · exact lb_21
  · exact lb_25
  · exact lb_26
  · exact lb_27
  · exact lb_28
  · exact lb_29
  · exact lb_30
  · exact lb_31

theorem sub_32 : ∀ b ∈ bds_32, m_32 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem gl_32 : ∀ b ∈ bds_32, canon b.1 g_32 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def f_32 : Nat → Nat × Nat := unpackForestF 0x112969f2d494a495e321950ca4601f 3 10

def l_32 : Nat → Nat → Option Nat := unpackLinksF 0xb2cb2cb267931c1 0x193184a563274f9b52594915e390c943148c01f 6 2 10 4 3

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_32 : dagCheckRootsF m_32 g_32 bds_32 (dagRefF 9 (dagTraceF m_32 s_32 7 f_32) l_32 0) s_32 7 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_32_0 : treeBlockF 0 9 (dagCheckNodeF m_32 g_32 bds_32 9 (dagTraceF m_32 s_32 7 f_32) l_32) = true := by decide +kernel

theorem join_32_0 : ∀ j, 0 ≤ j → j < 9 → (dagCheckNodeF m_32 g_32 bds_32 9 (dagTraceF m_32 s_32 7 f_32) l_32) j = true := (fun _ h₁ h₂ => treeBlockF_at block_32_0 h₁ h₂)

theorem nc_32 : ∀ j, 0 ≤ j → j < 9 → (dagCheckNodeF m_32 g_32 bds_32 9 (dagTraceF m_32 s_32 7 f_32) l_32) j = true := join_32_0

theorem lb_32 : LowerBin m_32 s_32 g_32 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_32 sub_32 gl_32 rc_32 nc_32

def m_33 : Nat := 0xf00f00000000

def s_33 : List Nat := [0x500500000000, 0x300300000000, 0xf00000000]

def g_33 : Nat := 0x100700000000

def bds_33 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp [bds_33] at hb

theorem sub_33 : ∀ b ∈ bds_33, m_33 &&& b.1 = b.1 := by
  intro b hb; simp [bds_33] at hb

theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_33] at hb

def f_33 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_33 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_33 : dagCheckRootsF m_33 g_33 bds_33 (dagRefF 1 (dagTraceF m_33 s_33 3 f_33) l_33 0) s_33 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_33_0 : treeBlockF 0 1 (dagCheckNodeF m_33 g_33 bds_33 1 (dagTraceF m_33 s_33 3 f_33) l_33) = true := by decide +kernel

theorem join_33_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_33 g_33 bds_33 1 (dagTraceF m_33 s_33 3 f_33) l_33) j = true := (fun _ h₁ h₂ => treeBlockF_at block_33_0 h₁ h₂)

theorem nc_33 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_33 g_33 bds_33 1 (dagTraceF m_33 s_33 3 f_33) l_33) j = true := join_33_0

theorem lb_33 : LowerBin m_33 s_33 g_33 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_33 sub_33 gl_33 rc_33 nc_33

def m_34 : Nat := 0xcc3300000000

def s_34 : List Nat := [0x441100000000, 0x3300000000, 0xc0300000000]

def g_34 : Nat := 0x41300000000

def bds_34 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_34 : KnownBin bds_34 := by
  intro b hb; simp [bds_34] at hb

theorem sub_34 : ∀ b ∈ bds_34, m_34 &&& b.1 = b.1 := by
  intro b hb; simp [bds_34] at hb

theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_34] at hb

def f_34 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_34 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_34 : dagCheckRootsF m_34 g_34 bds_34 (dagRefF 1 (dagTraceF m_34 s_34 3 f_34) l_34 0) s_34 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_34_0 : treeBlockF 0 1 (dagCheckNodeF m_34 g_34 bds_34 1 (dagTraceF m_34 s_34 3 f_34) l_34) = true := by decide +kernel

theorem join_34_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_34 g_34 bds_34 1 (dagTraceF m_34 s_34 3 f_34) l_34) j = true := (fun _ h₁ h₂ => treeBlockF_at block_34_0 h₁ h₂)

theorem nc_34 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_34 g_34 bds_34 1 (dagTraceF m_34 s_34 3 f_34) l_34) j = true := join_34_0

theorem lb_34 : LowerBin m_34 s_34 g_34 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_34 sub_34 gl_34 rc_34 nc_34

def m_35 : Nat := 0xc3c300000000

def s_35 : List Nat := [0x414100000000, 0x30300000000, 0xc300000000]

def g_35 : Nat := 0x14300000000

def bds_35 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_35 : KnownBin bds_35 := by
  intro b hb; simp [bds_35] at hb

theorem sub_35 : ∀ b ∈ bds_35, m_35 &&& b.1 = b.1 := by
  intro b hb; simp [bds_35] at hb

theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_35] at hb

def f_35 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_35 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_35 : dagCheckRootsF m_35 g_35 bds_35 (dagRefF 1 (dagTraceF m_35 s_35 3 f_35) l_35 0) s_35 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_35_0 : treeBlockF 0 1 (dagCheckNodeF m_35 g_35 bds_35 1 (dagTraceF m_35 s_35 3 f_35) l_35) = true := by decide +kernel

theorem join_35_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_35 g_35 bds_35 1 (dagTraceF m_35 s_35 3 f_35) l_35) j = true := (fun _ h₁ h₂ => treeBlockF_at block_35_0 h₁ h₂)

theorem nc_35 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_35 g_35 bds_35 1 (dagTraceF m_35 s_35 3 f_35) l_35) j = true := join_35_0

theorem lb_35 : LowerBin m_35 s_35 g_35 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_35 sub_35 gl_35 rc_35 nc_35

def m_36 : Nat := 0x666600000000

def s_36 : List Nat := [0x222200000000, 0x60600000000, 0x6600000000]

def g_36 : Nat := 0x44600000000

def bds_36 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_36 : KnownBin bds_36 := by
  intro b hb; simp [bds_36] at hb

theorem sub_36 : ∀ b ∈ bds_36, m_36 &&& b.1 = b.1 := by
  intro b hb; simp [bds_36] at hb

theorem gl_36 : ∀ b ∈ bds_36, canon b.1 g_36 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_36] at hb

def f_36 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_36 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_36 : dagCheckRootsF m_36 g_36 bds_36 (dagRefF 1 (dagTraceF m_36 s_36 3 f_36) l_36 0) s_36 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_36_0 : treeBlockF 0 1 (dagCheckNodeF m_36 g_36 bds_36 1 (dagTraceF m_36 s_36 3 f_36) l_36) = true := by decide +kernel

theorem join_36_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_36 g_36 bds_36 1 (dagTraceF m_36 s_36 3 f_36) l_36) j = true := (fun _ h₁ h₂ => treeBlockF_at block_36_0 h₁ h₂)

theorem nc_36 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_36 g_36 bds_36 1 (dagTraceF m_36 s_36 3 f_36) l_36) j = true := join_36_0

theorem lb_36 : LowerBin m_36 s_36 g_36 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_36 sub_36 gl_36 rc_36 nc_36

def m_37 : Nat := 0x5a5a00000000

def s_37 : List Nat := [0xa0a00000000, 0x121200000000, 0x5a00000000]

def g_37 : Nat := 0x105200000000

def bds_37 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_37 : KnownBin bds_37 := by
  intro b hb; simp [bds_37] at hb

theorem sub_37 : ∀ b ∈ bds_37, m_37 &&& b.1 = b.1 := by
  intro b hb; simp [bds_37] at hb

theorem gl_37 : ∀ b ∈ bds_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_37] at hb

def f_37 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_37 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_37 : dagCheckRootsF m_37 g_37 bds_37 (dagRefF 1 (dagTraceF m_37 s_37 3 f_37) l_37 0) s_37 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_37_0 : treeBlockF 0 1 (dagCheckNodeF m_37 g_37 bds_37 1 (dagTraceF m_37 s_37 3 f_37) l_37) = true := by decide +kernel

theorem join_37_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_37 g_37 bds_37 1 (dagTraceF m_37 s_37 3 f_37) l_37) j = true := (fun _ h₁ h₂ => treeBlockF_at block_37_0 h₁ h₂)

theorem nc_37 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_37 g_37 bds_37 1 (dagTraceF m_37 s_37 3 f_37) l_37) j = true := join_37_0

theorem lb_37 : LowerBin m_37 s_37 g_37 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_37 sub_37 gl_37 rc_37 nc_37

def m_38 : Nat := 0x55aa00000000

def s_38 : List Nat := [0xaa00000000, 0x112200000000, 0x50a00000000]

def g_38 : Nat := 0x150200000000

def bds_38 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp [bds_38] at hb

theorem sub_38 : ∀ b ∈ bds_38, m_38 &&& b.1 = b.1 := by
  intro b hb; simp [bds_38] at hb

theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_38] at hb

def f_38 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_38 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_38 : dagCheckRootsF m_38 g_38 bds_38 (dagRefF 1 (dagTraceF m_38 s_38 3 f_38) l_38 0) s_38 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_38_0 : treeBlockF 0 1 (dagCheckNodeF m_38 g_38 bds_38 1 (dagTraceF m_38 s_38 3 f_38) l_38) = true := by decide +kernel

theorem join_38_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_38 g_38 bds_38 1 (dagTraceF m_38 s_38 3 f_38) l_38) j = true := (fun _ h₁ h₂ => treeBlockF_at block_38_0 h₁ h₂)

theorem nc_38 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_38 g_38 bds_38 1 (dagTraceF m_38 s_38 3 f_38) l_38) j = true := join_38_0

theorem lb_38 : LowerBin m_38 s_38 g_38 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_38 sub_38 gl_38 rc_38 nc_38

def m_39 : Nat := 0xffff00000000

def s_39 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]

def g_39 : Nat := 0x155700000000

def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_33, s_33, 4, g_33), (m_34, s_34, 4, g_34), (m_35, s_35, 4, g_35), (m_36, s_36, 4, g_36), (m_37, s_37, 4, g_37), (m_38, s_38, 4, g_38)]

theorem kn_39 : KnownBin bds_39 := by
  intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_33
  · exact lb_34
  · exact lb_35
  · exact lb_36
  · exact lb_37
  · exact lb_38

theorem sub_39 : ∀ b ∈ bds_39, m_39 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem gl_39 : ∀ b ∈ bds_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def f_39 : Nat → Nat × Nat := unpackForestF 0x63fc774fe9dd27a470fe1dc2784705e0980f 1 10

def l_39 : Nat → Nat → Option Nat := unpackLinksF 0xd0d0d0d0d0d0d0d0d0d0d0d01c01 0x323fb8ee93f94ee127748d83f50ed027308c817104c00f 8 4 10 4 5

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_39 : dagCheckRootsF m_39 g_39 bds_39 (dagRefF 13 (dagTraceF m_39 s_39 5 f_39) l_39 0) s_39 5 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_39_0 : treeBlockF 0 13 (dagCheckNodeF m_39 g_39 bds_39 13 (dagTraceF m_39 s_39 5 f_39) l_39) = true := by decide +kernel

theorem join_39_0 : ∀ j, 0 ≤ j → j < 13 → (dagCheckNodeF m_39 g_39 bds_39 13 (dagTraceF m_39 s_39 5 f_39) l_39) j = true := (fun _ h₁ h₂ => treeBlockF_at block_39_0 h₁ h₂)

theorem nc_39 : ∀ j, 0 ≤ j → j < 13 → (dagCheckNodeF m_39 g_39 bds_39 13 (dagTraceF m_39 s_39 5 f_39) l_39) j = true := join_39_0

theorem lb_39 : LowerBin m_39 s_39 g_39 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_39 sub_39 gl_39 rc_39 nc_39

def m_40 : Nat := 0xaaaa0000aaaa

def s_40 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]

def g_40 : Nat := 0x20000020a

def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]

theorem kn_40 : KnownBin bds_40 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0

theorem sub_40 : ∀ b ∈ bds_40, m_40 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_40 : Nat → Nat × Nat := fun _ => (0, 0)

def l_40 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_40 : dagCheckRootsF m_40 g_40 bds_40 (dagRefF 0 (dagTraceF m_40 s_40 4 f_40) l_40 0) s_40 4 = true := by decide +kernel

theorem nc_40 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_40 g_40 bds_40 0 (dagTraceF m_40 s_40 4 f_40) l_40) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_40 sub_40 gl_40 rc_40 nc_40

def m_41 : Nat := 0xf0f00000f0f

def s_41 : List Nat := [0x50500000505, 0x30300000303, 0xf0000000f, 0xf0f]

def g_41 : Nat := 0x5070000070f

def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]

theorem kn_41 : KnownBin bds_41 := by
  intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0

theorem sub_41 : ∀ b ∈ bds_41, m_41 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_41 : ∀ b ∈ bds_41, canon b.1 g_41 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_41 : Nat → Nat × Nat := fun _ => (0, 0)

def l_41 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_41 : dagCheckRootsF m_41 g_41 bds_41 (dagRefF 0 (dagTraceF m_41 s_41 4 f_41) l_41 0) s_41 4 = true := by decide +kernel

theorem nc_41 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_41 g_41 bds_41 0 (dagTraceF m_41 s_41 4 f_41) l_41) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_41 sub_41 gl_41 rc_41 nc_41

def m_42 : Nat := 0xcccc0000cccc

def s_42 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]

def g_42 : Nat := 0x4440000044c

def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]

theorem kn_42 : KnownBin bds_42 := by
  intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4

theorem sub_42 : ∀ b ∈ bds_42, m_42 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_42 : ∀ b ∈ bds_42, canon b.1 g_42 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_42 : Nat → Nat × Nat := fun _ => (0, 0)

def l_42 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_42 : dagCheckRootsF m_42 g_42 bds_42 (dagRefF 0 (dagTraceF m_42 s_42 4 f_42) l_42 0) s_42 4 = true := by decide +kernel

theorem nc_42 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_42 g_42 bds_42 0 (dagTraceF m_42 s_42 4 f_42) l_42) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_42 sub_42 gl_42 rc_42 nc_42

def m_43 : Nat := 0xf0f000000f0f

def s_43 : List Nat := [0x505000000505, 0x303000000303, 0xf0f, 0xf00000000f]

def g_43 : Nat := 0x10500000070f

def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 4, g_18)]

theorem kn_43 : KnownBin bds_43 := by
  intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_18

theorem sub_43 : ∀ b ∈ bds_43, m_43 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_43 : ∀ b ∈ bds_43, canon b.1 g_43 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_43 : Nat → Nat × Nat := fun _ => (0, 0)

def l_43 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_43 : dagCheckRootsF m_43 g_43 bds_43 (dagRefF 0 (dagTraceF m_43 s_43 4 f_43) l_43 0) s_43 4 = true := by decide +kernel

theorem nc_43 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_43 g_43 bds_43 0 (dagTraceF m_43 s_43 4 f_43) l_43) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_43 sub_43 gl_43 rc_43 nc_43

def m_44 : Nat := 0x55550000aaaa

def s_44 : List Nat := [0xaaaa, 0x111100002222, 0x50500000a0a, 0x55000000aa]

def g_44 : Nat := 0x15550000020a

def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_24, s_24, 4, g_24)]

theorem kn_44 : KnownBin bds_44 := by
  intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_24

theorem sub_44 : ∀ b ∈ bds_44, m_44 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_44 : ∀ b ∈ bds_44, canon b.1 g_44 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_44 : Nat → Nat × Nat := fun _ => (0, 0)

def l_44 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_44 : dagCheckRootsF m_44 g_44 bds_44 (dagRefF 0 (dagTraceF m_44 s_44 4 f_44) l_44 0) s_44 4 = true := by decide +kernel

theorem nc_44 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_44 g_44 bds_44 0 (dagTraceF m_44 s_44 4 f_44) l_44) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_44 sub_44 gl_44 rc_44 nc_44

def m_45 : Nat := 0xf00f0000f00f

def s_45 : List Nat := [0x500500005005, 0x300300003003, 0xf0000000f, 0xf00f]

def g_45 : Nat := 0x10070000100f

def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_33, s_33, 4, g_33)]

theorem kn_45 : KnownBin bds_45 := by
  intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_33

theorem sub_45 : ∀ b ∈ bds_45, m_45 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_45 : ∀ b ∈ bds_45, canon b.1 g_45 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_45 : Nat → Nat × Nat := fun _ => (0, 0)

def l_45 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_45 : dagCheckRootsF m_45 g_45 bds_45 (dagRefF 0 (dagTraceF m_45 s_45 4 f_45) l_45 0) s_45 4 = true := by decide +kernel

theorem nc_45 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_45 g_45 bds_45 0 (dagTraceF m_45 s_45 4 f_45) l_45) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_45 sub_45 gl_45 rc_45 nc_45

def m_46 : Nat := 0x5a5a00005a5a

def s_46 : List Nat := [0xa0a00000a0a, 0x121200001212, 0x5a0000005a, 0x5a5a]

def g_46 : Nat := 0x10520000125a

def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_37, s_37, 4, g_37)]

theorem kn_46 : KnownBin bds_46 := by
  intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_37

theorem sub_46 : ∀ b ∈ bds_46, m_46 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_46 : ∀ b ∈ bds_46, canon b.1 g_46 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_46 : Nat → Nat × Nat := fun _ => (0, 0)

def l_46 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_46 : dagCheckRootsF m_46 g_46 bds_46 (dagRefF 0 (dagTraceF m_46 s_46 4 f_46) l_46 0) s_46 4 = true := by decide +kernel

theorem nc_46 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_46 g_46 bds_46 0 (dagTraceF m_46 s_46 4 f_46) l_46) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_46 sub_46 gl_46 rc_46 nc_46

def m_47 : Nat := 0xc0c000000c0c

def s_47 : List Nat := [0x404000000404, 0xc0c, 0xc00000000c]

def g_47 : Nat := 0x400000040c

def bds_47 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_47 : KnownBin bds_47 := by
  intro b hb; simp [bds_47] at hb

theorem sub_47 : ∀ b ∈ bds_47, m_47 &&& b.1 = b.1 := by
  intro b hb; simp [bds_47] at hb

theorem gl_47 : ∀ b ∈ bds_47, canon b.1 g_47 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_47] at hb

def f_47 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_47 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_47 : dagCheckRootsF m_47 g_47 bds_47 (dagRefF 1 (dagTraceF m_47 s_47 3 f_47) l_47 0) s_47 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_47_0 : treeBlockF 0 1 (dagCheckNodeF m_47 g_47 bds_47 1 (dagTraceF m_47 s_47 3 f_47) l_47) = true := by decide +kernel

theorem join_47_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_47 g_47 bds_47 1 (dagTraceF m_47 s_47 3 f_47) l_47) j = true := (fun _ h₁ h₂ => treeBlockF_at block_47_0 h₁ h₂)

theorem nc_47 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_47 g_47 bds_47 1 (dagTraceF m_47 s_47 3 f_47) l_47) j = true := join_47_0

theorem lb_47 : LowerBin m_47 s_47 g_47 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_47 sub_47 gl_47 rc_47 nc_47

def m_48 : Nat := 0x444400008888

def s_48 : List Nat := [0x8888, 0x40400000808, 0x4400000088]

def g_48 : Nat := 0x44400000008

def bds_48 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_48 : KnownBin bds_48 := by
  intro b hb; simp [bds_48] at hb

theorem sub_48 : ∀ b ∈ bds_48, m_48 &&& b.1 = b.1 := by
  intro b hb; simp [bds_48] at hb

theorem gl_48 : ∀ b ∈ bds_48, canon b.1 g_48 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_48] at hb

def f_48 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_48 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_48 : dagCheckRootsF m_48 g_48 bds_48 (dagRefF 1 (dagTraceF m_48 s_48 3 f_48) l_48 0) s_48 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_48_0 : treeBlockF 0 1 (dagCheckNodeF m_48 g_48 bds_48 1 (dagTraceF m_48 s_48 3 f_48) l_48) = true := by decide +kernel

theorem join_48_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_48 g_48 bds_48 1 (dagTraceF m_48 s_48 3 f_48) l_48) j = true := (fun _ h₁ h₂ => treeBlockF_at block_48_0 h₁ h₂)

theorem nc_48 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_48 g_48 bds_48 1 (dagTraceF m_48 s_48 3 f_48) l_48) j = true := join_48_0

theorem lb_48 : LowerBin m_48 s_48 g_48 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_48 sub_48 gl_48 rc_48 nc_48

def m_49 : Nat := 0xa00a00005005

def s_49 : List Nat := [0x5005, 0x200200001001, 0xa00000005]

def g_49 : Nat := 0x200001005

def bds_49 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_49 : KnownBin bds_49 := by
  intro b hb; simp [bds_49] at hb

theorem sub_49 : ∀ b ∈ bds_49, m_49 &&& b.1 = b.1 := by
  intro b hb; simp [bds_49] at hb

theorem gl_49 : ∀ b ∈ bds_49, canon b.1 g_49 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_49] at hb

def f_49 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_49 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_49 : dagCheckRootsF m_49 g_49 bds_49 (dagRefF 1 (dagTraceF m_49 s_49 3 f_49) l_49 0) s_49 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_49_0 : treeBlockF 0 1 (dagCheckNodeF m_49 g_49 bds_49 1 (dagTraceF m_49 s_49 3 f_49) l_49) = true := by decide +kernel

theorem join_49_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_49 g_49 bds_49 1 (dagTraceF m_49 s_49 3 f_49) l_49) j = true := (fun _ h₁ h₂ => treeBlockF_at block_49_0 h₁ h₂)

theorem nc_49 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_49 g_49 bds_49 1 (dagTraceF m_49 s_49 3 f_49) l_49) j = true := join_49_0

theorem lb_49 : LowerBin m_49 s_49 g_49 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_49 sub_49 gl_49 rc_49 nc_49

def m_50 : Nat := 0x882200004411

def s_50 : List Nat := [0x4411, 0x2200000011, 0x80200000401]

def g_50 : Nat := 0x200000411

def bds_50 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_50 : KnownBin bds_50 := by
  intro b hb; simp [bds_50] at hb

theorem sub_50 : ∀ b ∈ bds_50, m_50 &&& b.1 = b.1 := by
  intro b hb; simp [bds_50] at hb

theorem gl_50 : ∀ b ∈ bds_50, canon b.1 g_50 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_50] at hb

def f_50 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_50 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_50 : dagCheckRootsF m_50 g_50 bds_50 (dagRefF 1 (dagTraceF m_50 s_50 3 f_50) l_50 0) s_50 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_50_0 : treeBlockF 0 1 (dagCheckNodeF m_50 g_50 bds_50 1 (dagTraceF m_50 s_50 3 f_50) l_50) = true := by decide +kernel

theorem join_50_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_50 g_50 bds_50 1 (dagTraceF m_50 s_50 3 f_50) l_50) j = true := (fun _ h₁ h₂ => treeBlockF_at block_50_0 h₁ h₂)

theorem nc_50 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_50 g_50 bds_50 1 (dagTraceF m_50 s_50 3 f_50) l_50) j = true := join_50_0

theorem lb_50 : LowerBin m_50 s_50 g_50 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_50 sub_50 gl_50 rc_50 nc_50

def m_51 : Nat := 0x828200004141

def s_51 : List Nat := [0x4141, 0x20200000101, 0x8200000041]

def g_51 : Nat := 0x200000141

def bds_51 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_51 : KnownBin bds_51 := by
  intro b hb; simp [bds_51] at hb

theorem sub_51 : ∀ b ∈ bds_51, m_51 &&& b.1 = b.1 := by
  intro b hb; simp [bds_51] at hb

theorem gl_51 : ∀ b ∈ bds_51, canon b.1 g_51 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_51] at hb

def f_51 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_51 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_51 : dagCheckRootsF m_51 g_51 bds_51 (dagRefF 1 (dagTraceF m_51 s_51 3 f_51) l_51 0) s_51 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_51_0 : treeBlockF 0 1 (dagCheckNodeF m_51 g_51 bds_51 1 (dagTraceF m_51 s_51 3 f_51) l_51) = true := by decide +kernel

theorem join_51_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_51 g_51 bds_51 1 (dagTraceF m_51 s_51 3 f_51) l_51) j = true := (fun _ h₁ h₂ => treeBlockF_at block_51_0 h₁ h₂)

theorem nc_51 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_51 g_51 bds_51 1 (dagTraceF m_51 s_51 3 f_51) l_51) j = true := join_51_0

theorem lb_51 : LowerBin m_51 s_51 g_51 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_51 sub_51 gl_51 rc_51 nc_51

def m_52 : Nat := 0x222200004444

def s_52 : List Nat := [0x4444, 0x20200000404, 0x2200000044]

def g_52 : Nat := 0x200000444

def bds_52 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_52 : KnownBin bds_52 := by
  intro b hb; simp [bds_52] at hb

theorem sub_52 : ∀ b ∈ bds_52, m_52 &&& b.1 = b.1 := by
  intro b hb; simp [bds_52] at hb

theorem gl_52 : ∀ b ∈ bds_52, canon b.1 g_52 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_52] at hb

def f_52 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_52 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_52 : dagCheckRootsF m_52 g_52 bds_52 (dagRefF 1 (dagTraceF m_52 s_52 3 f_52) l_52 0) s_52 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_52_0 : treeBlockF 0 1 (dagCheckNodeF m_52 g_52 bds_52 1 (dagTraceF m_52 s_52 3 f_52) l_52) = true := by decide +kernel

theorem join_52_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_52 g_52 bds_52 1 (dagTraceF m_52 s_52 3 f_52) l_52) j = true := (fun _ h₁ h₂ => treeBlockF_at block_52_0 h₁ h₂)

theorem nc_52 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_52 g_52 bds_52 1 (dagTraceF m_52 s_52 3 f_52) l_52) j = true := join_52_0

theorem lb_52 : LowerBin m_52 s_52 g_52 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_52 sub_52 gl_52 rc_52 nc_52

def m_53 : Nat := 0xa0a00005050

def s_53 : List Nat := [0x5050, 0x20200001010, 0xa00000050]

def g_53 : Nat := 0x200001050

def bds_53 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_53 : KnownBin bds_53 := by
  intro b hb; simp [bds_53] at hb

theorem sub_53 : ∀ b ∈ bds_53, m_53 &&& b.1 = b.1 := by
  intro b hb; simp [bds_53] at hb

theorem gl_53 : ∀ b ∈ bds_53, canon b.1 g_53 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_53] at hb

def f_53 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_53 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_53 : dagCheckRootsF m_53 g_53 bds_53 (dagRefF 1 (dagTraceF m_53 s_53 3 f_53) l_53 0) s_53 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_53_0 : treeBlockF 0 1 (dagCheckNodeF m_53 g_53 bds_53 1 (dagTraceF m_53 s_53 3 f_53) l_53) = true := by decide +kernel

theorem join_53_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_53 g_53 bds_53 1 (dagTraceF m_53 s_53 3 f_53) l_53) j = true := (fun _ h₁ h₂ => treeBlockF_at block_53_0 h₁ h₂)

theorem nc_53 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_53 g_53 bds_53 1 (dagTraceF m_53 s_53 3 f_53) l_53) j = true := join_53_0

theorem lb_53 : LowerBin m_53 s_53 g_53 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_53 sub_53 gl_53 rc_53 nc_53

def m_54 : Nat := 0xaa00005500

def s_54 : List Nat := [0x5500, 0x2200001100, 0xa00000500]

def g_54 : Nat := 0x200001500

def bds_54 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_54 : KnownBin bds_54 := by
  intro b hb; simp [bds_54] at hb

theorem sub_54 : ∀ b ∈ bds_54, m_54 &&& b.1 = b.1 := by
  intro b hb; simp [bds_54] at hb

theorem gl_54 : ∀ b ∈ bds_54, canon b.1 g_54 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_54] at hb

def f_54 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_54 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_54 : dagCheckRootsF m_54 g_54 bds_54 (dagRefF 1 (dagTraceF m_54 s_54 3 f_54) l_54 0) s_54 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_54_0 : treeBlockF 0 1 (dagCheckNodeF m_54 g_54 bds_54 1 (dagTraceF m_54 s_54 3 f_54) l_54) = true := by decide +kernel

theorem join_54_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_54 g_54 bds_54 1 (dagTraceF m_54 s_54 3 f_54) l_54) j = true := (fun _ h₁ h₂ => treeBlockF_at block_54_0 h₁ h₂)

theorem nc_54 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_54 g_54 bds_54 1 (dagTraceF m_54 s_54 3 f_54) l_54) j = true := join_54_0

theorem lb_54 : LowerBin m_54 s_54 g_54 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_54 sub_54 gl_54 rc_54 nc_54

def m_55 : Nat := 0xaaaa00005555

def s_55 : List Nat := [0x5555, 0x222200001111, 0xa0a00000505, 0xaa00000055]

def g_55 : Nat := 0x200001555

def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_49, s_49, 4, g_49), (m_50, s_50, 4, g_50), (m_51, s_51, 4, g_51), (m_52, s_52, 4, g_52), (m_53, s_53, 4, g_53), (m_54, s_54, 4, g_54)]

theorem kn_55 : KnownBin bds_55 := by
  intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_49
  · exact lb_50
  · exact lb_51
  · exact lb_52
  · exact lb_53
  · exact lb_54

theorem sub_55 : ∀ b ∈ bds_55, m_55 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem gl_55 : ∀ b ∈ bds_55, canon b.1 g_55 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def f_55 : Nat → Nat × Nat := unpackForestF 0x637c674de99d27a470fe1dc2f85707e0d80f 1 10

def l_55 : Nat → Nat → Option Nat := unpackLinksF 0xd0d0d0d0d0d0d0d0d0d0d0d01c01 0x3237b8ce93794ce127748d83f50ed02f30ac81f106c00f 8 4 10 4 5

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_55 : dagCheckRootsF m_55 g_55 bds_55 (dagRefF 13 (dagTraceF m_55 s_55 5 f_55) l_55 0) s_55 5 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_55_0 : treeBlockF 0 13 (dagCheckNodeF m_55 g_55 bds_55 13 (dagTraceF m_55 s_55 5 f_55) l_55) = true := by decide +kernel

theorem join_55_0 : ∀ j, 0 ≤ j → j < 13 → (dagCheckNodeF m_55 g_55 bds_55 13 (dagTraceF m_55 s_55 5 f_55) l_55) j = true := (fun _ h₁ h₂ => treeBlockF_at block_55_0 h₁ h₂)

theorem nc_55 : ∀ j, 0 ≤ j → j < 13 → (dagCheckNodeF m_55 g_55 bds_55 13 (dagTraceF m_55 s_55 5 f_55) l_55) j = true := join_55_0

theorem lb_55 : LowerBin m_55 s_55 g_55 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_55 sub_55 gl_55 rc_55 nc_55

def m_56 : Nat := 0xc030000c030

def s_56 : List Nat := [0x40100004010, 0x300000030, 0xc030]

def g_56 : Nat := 0x40300000010

def bds_56 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_56 : KnownBin bds_56 := by
  intro b hb; simp [bds_56] at hb

theorem sub_56 : ∀ b ∈ bds_56, m_56 &&& b.1 = b.1 := by
  intro b hb; simp [bds_56] at hb

theorem gl_56 : ∀ b ∈ bds_56, canon b.1 g_56 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_56] at hb

def f_56 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_56 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_56 : dagCheckRootsF m_56 g_56 bds_56 (dagRefF 1 (dagTraceF m_56 s_56 3 f_56) l_56 0) s_56 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_56_0 : treeBlockF 0 1 (dagCheckNodeF m_56 g_56 bds_56 1 (dagTraceF m_56 s_56 3 f_56) l_56) = true := by decide +kernel

theorem join_56_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_56 g_56 bds_56 1 (dagTraceF m_56 s_56 3 f_56) l_56) j = true := (fun _ h₁ h₂ => treeBlockF_at block_56_0 h₁ h₂)

theorem nc_56 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_56 g_56 bds_56 1 (dagTraceF m_56 s_56 3 f_56) l_56) j = true := join_56_0

theorem lb_56 : LowerBin m_56 s_56 g_56 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_56 sub_56 gl_56 rc_56 nc_56

def m_57 : Nat := 0x3030000c0c0

def s_57 : List Nat := [0x10100004040, 0xc0c0, 0x3000000c0]

def g_57 : Nat := 0x10300000040

def bds_57 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_57 : KnownBin bds_57 := by
  intro b hb; simp [bds_57] at hb

theorem sub_57 : ∀ b ∈ bds_57, m_57 &&& b.1 = b.1 := by
  intro b hb; simp [bds_57] at hb

theorem gl_57 : ∀ b ∈ bds_57, canon b.1 g_57 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_57] at hb

def f_57 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_57 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_57 : dagCheckRootsF m_57 g_57 bds_57 (dagRefF 1 (dagTraceF m_57 s_57 3 f_57) l_57 0) s_57 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_57_0 : treeBlockF 0 1 (dagCheckNodeF m_57 g_57 bds_57 1 (dagTraceF m_57 s_57 3 f_57) l_57) = true := by decide +kernel

theorem join_57_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_57 g_57 bds_57 1 (dagTraceF m_57 s_57 3 f_57) l_57) j = true := (fun _ h₁ h₂ => treeBlockF_at block_57_0 h₁ h₂)

theorem nc_57 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_57 g_57 bds_57 1 (dagTraceF m_57 s_57 3 f_57) l_57) j = true := join_57_0

theorem lb_57 : LowerBin m_57 s_57 g_57 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_57 sub_57 gl_57 rc_57 nc_57

def m_58 : Nat := 0xf0000f000

def s_58 : List Nat := [0x500005000, 0x300003000, 0xf000]

def g_58 : Nat := 0x700001000

def bds_58 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_58 : KnownBin bds_58 := by
  intro b hb; simp [bds_58] at hb

theorem sub_58 : ∀ b ∈ bds_58, m_58 &&& b.1 = b.1 := by
  intro b hb; simp [bds_58] at hb

theorem gl_58 : ∀ b ∈ bds_58, canon b.1 g_58 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_58] at hb

def f_58 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_58 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_58 : dagCheckRootsF m_58 g_58 bds_58 (dagRefF 1 (dagTraceF m_58 s_58 3 f_58) l_58 0) s_58 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_58_0 : treeBlockF 0 1 (dagCheckNodeF m_58 g_58 bds_58 1 (dagTraceF m_58 s_58 3 f_58) l_58) = true := by decide +kernel

theorem join_58_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_58 g_58 bds_58 1 (dagTraceF m_58 s_58 3 f_58) l_58) j = true := (fun _ h₁ h₂ => treeBlockF_at block_58_0 h₁ h₂)

theorem nc_58 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_58 g_58 bds_58 1 (dagTraceF m_58 s_58 3 f_58) l_58) j = true := join_58_0

theorem lb_58 : LowerBin m_58 s_58 g_58 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_58 sub_58 gl_58 rc_58 nc_58

def m_59 : Nat := 0x60600006060

def s_59 : List Nat := [0x20200002020, 0x6060, 0x600000060]

def g_59 : Nat := 0x20000006020

def bds_59 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_59 : KnownBin bds_59 := by
  intro b hb; simp [bds_59] at hb

theorem sub_59 : ∀ b ∈ bds_59, m_59 &&& b.1 = b.1 := by
  intro b hb; simp [bds_59] at hb

theorem gl_59 : ∀ b ∈ bds_59, canon b.1 g_59 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_59] at hb

def f_59 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_59 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_59 : dagCheckRootsF m_59 g_59 bds_59 (dagRefF 1 (dagTraceF m_59 s_59 3 f_59) l_59 0) s_59 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_59_0 : treeBlockF 0 1 (dagCheckNodeF m_59 g_59 bds_59 1 (dagTraceF m_59 s_59 3 f_59) l_59) = true := by decide +kernel

theorem join_59_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_59 g_59 bds_59 1 (dagTraceF m_59 s_59 3 f_59) l_59) j = true := (fun _ h₁ h₂ => treeBlockF_at block_59_0 h₁ h₂)

theorem nc_59 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_59 g_59 bds_59 1 (dagTraceF m_59 s_59 3 f_59) l_59) j = true := join_59_0

theorem lb_59 : LowerBin m_59 s_59 g_59 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_59 sub_59 gl_59 rc_59 nc_59

def m_60 : Nat := 0x50a000050a0

def s_60 : List Nat := [0xa000000a0, 0x10200001020, 0x50a0]

def g_60 : Nat := 0x8000040a0

def bds_60 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_60 : KnownBin bds_60 := by
  intro b hb; simp [bds_60] at hb

theorem sub_60 : ∀ b ∈ bds_60, m_60 &&& b.1 = b.1 := by
  intro b hb; simp [bds_60] at hb

theorem gl_60 : ∀ b ∈ bds_60, canon b.1 g_60 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_60] at hb

def f_60 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_60 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_60 : dagCheckRootsF m_60 g_60 bds_60 (dagRefF 1 (dagTraceF m_60 s_60 3 f_60) l_60 0) s_60 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_60_0 : treeBlockF 0 1 (dagCheckNodeF m_60 g_60 bds_60 1 (dagTraceF m_60 s_60 3 f_60) l_60) = true := by decide +kernel

theorem join_60_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_60 g_60 bds_60 1 (dagTraceF m_60 s_60 3 f_60) l_60) j = true := (fun _ h₁ h₂ => treeBlockF_at block_60_0 h₁ h₂)

theorem nc_60 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_60 g_60 bds_60 1 (dagTraceF m_60 s_60 3 f_60) l_60) j = true := join_60_0

theorem lb_60 : LowerBin m_60 s_60 g_60 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_60 sub_60 gl_60 rc_60 nc_60

def m_61 : Nat := 0xf0f0000f0f0

def s_61 : List Nat := [0x50500005050, 0x30300003030, 0xf0f0, 0xf000000f0]

def g_61 : Nat := 0x50700001050

def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_56, s_56, 4, g_56), (m_57, s_57, 4, g_57), (m_58, s_58, 4, g_58), (m_53, s_53, 4, g_53), (m_59, s_59, 4, g_59), (m_60, s_60, 4, g_60)]

theorem kn_61 : KnownBin bds_61 := by
  intro b hb; simp only [bds_61, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_56
  · exact lb_57
  · exact lb_58
  · exact lb_53
  · exact lb_59
  · exact lb_60

theorem sub_61 : ∀ b ∈ bds_61, m_61 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_61, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem gl_61 : ∀ b ∈ bds_61, canon b.1 g_61 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_61, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def f_61 : Nat → Nat × Nat := unpackForestF 0x63fc774fe9dd27a470de19c2f85707e0d80f 1 10

def l_61 : Nat → Nat → Option Nat := unpackLinksF 0xd0d0d0d0d0d0d0d0d0d0d0d01c01 0x323fb8ee93f94ee127748d83750cd02f30ac81f106c00f 8 4 10 4 5

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_61 : dagCheckRootsF m_61 g_61 bds_61 (dagRefF 13 (dagTraceF m_61 s_61 5 f_61) l_61 0) s_61 5 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_61_0 : treeBlockF 0 13 (dagCheckNodeF m_61 g_61 bds_61 13 (dagTraceF m_61 s_61 5 f_61) l_61) = true := by decide +kernel

theorem join_61_0 : ∀ j, 0 ≤ j → j < 13 → (dagCheckNodeF m_61 g_61 bds_61 13 (dagTraceF m_61 s_61 5 f_61) l_61) j = true := (fun _ h₁ h₂ => treeBlockF_at block_61_0 h₁ h₂)

theorem nc_61 : ∀ j, 0 ≤ j → j < 13 → (dagCheckNodeF m_61 g_61 bds_61 13 (dagTraceF m_61 s_61 5 f_61) l_61) j = true := join_61_0

theorem lb_61 : LowerBin m_61 s_61 g_61 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_61 sub_61 gl_61 rc_61 nc_61

def m_62 : Nat := 0xffff

def s_62 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]

def g_62 : Nat := 0x175f

def bds_62 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]

theorem kn_62 : KnownBin bds_62 := by
  intro b hb; simp only [bds_62, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_15

theorem sub_62 : ∀ b ∈ bds_62, m_62 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_62, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_62 : ∀ b ∈ bds_62, canon b.1 g_62 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_62, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_62 : Nat → Nat × Nat := fun _ => (0, 0)

def l_62 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_62 : dagCheckRootsF m_62 g_62 bds_62 (dagRefF 0 (dagTraceF m_62 s_62 4 f_62) l_62 0) s_62 4 = true := by decide +kernel

theorem nc_62 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_62 g_62 bds_62 0 (dagTraceF m_62 s_62 4 f_62) l_62) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_62 : LowerBin m_62 s_62 g_62 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_62 sub_62 gl_62 rc_62 nc_62

def m_63 : Nat := 0xcc0000003300

def s_63 : List Nat := [0x440000001100, 0x3300, 0xc0000000300]

def g_63 : Nat := 0x40000001300

def bds_63 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_63 : KnownBin bds_63 := by
  intro b hb; simp [bds_63] at hb

theorem sub_63 : ∀ b ∈ bds_63, m_63 &&& b.1 = b.1 := by
  intro b hb; simp [bds_63] at hb

theorem gl_63 : ∀ b ∈ bds_63, canon b.1 g_63 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_63] at hb

def f_63 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_63 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_63 : dagCheckRootsF m_63 g_63 bds_63 (dagRefF 1 (dagTraceF m_63 s_63 3 f_63) l_63 0) s_63 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_63_0 : treeBlockF 0 1 (dagCheckNodeF m_63 g_63 bds_63 1 (dagTraceF m_63 s_63 3 f_63) l_63) = true := by decide +kernel

theorem join_63_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_63 g_63 bds_63 1 (dagTraceF m_63 s_63 3 f_63) l_63) j = true := (fun _ h₁ h₂ => treeBlockF_at block_63_0 h₁ h₂)

theorem nc_63 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_63 g_63 bds_63 1 (dagTraceF m_63 s_63 3 f_63) l_63) j = true := join_63_0

theorem lb_63 : LowerBin m_63 s_63 g_63 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_63 sub_63 gl_63 rc_63 nc_63

def m_64 : Nat := 0xffff0000ffff

def s_64 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]

def g_64 : Nat := 0x15570000175f

def bds_64 : List (Nat × List Nat × Nat × Nat) := [(m_39, s_39, 6, g_39), (m_40, s_40, 5, g_40), (m_41, s_41, 5, g_41), (m_30, s_30, 5, g_30), (m_42, s_42, 5, g_42), (m_43, s_43, 5, g_43), (m_44, s_44, 5, g_44), (m_0, s_0, 4, g_0), (m_45, s_45, 5, g_45), (m_46, s_46, 5, g_46), (m_18, s_18, 4, g_18), (m_24, s_24, 4, g_24), (m_36, s_36, 4, g_36), (m_35, s_35, 4, g_35), (m_47, s_47, 4, g_47), (m_48, s_48, 4, g_48), (m_55, s_55, 6, g_55), (m_61, s_61, 6, g_61), (m_62, s_62, 5, g_62), (m_63, s_63, 4, g_63)]

theorem kn_64 : KnownBin bds_64 := by
  intro b hb; simp only [bds_64, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_39
  · exact lb_40
  · exact lb_41
  · exact lb_30
  · exact lb_42
  · exact lb_43
  · exact lb_44
  · exact lb_0
  · exact lb_45
  · exact lb_46
  · exact lb_18
  · exact lb_24
  · exact lb_36
  · exact lb_35
  · exact lb_47
  · exact lb_48
  · exact lb_55
  · exact lb_61
  · exact lb_62
  · exact lb_63

theorem sub_64 : ∀ b ∈ bds_64, m_64 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_64, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem gl_64 : ∀ b ∈ bds_64, canon b.1 g_64 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_64, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def f_64 : Nat → Nat × Nat := unpackForestF 0x20aeb92566bab1695ab2a415472a5591232146168e28ec4a38937125e2118417001f 4 11

def l_64 : Nat → Nat → Option Nat := unpackLinksF 0xb0b0b0b0b0b0b0b0b0b0a29282564240400f01 0x895d6935594581257b5d5136745a6b5662415a395156412e4a4641463b47323b29472137192f1046082e001f 8 3 11 5 4

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_64 : dagCheckRootsF m_64 g_64 bds_64 (dagRefF 18 (dagTraceF m_64 s_64 7 f_64) l_64 0) s_64 7 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_64_0 : treeBlockF 0 16 (dagCheckNodeF m_64 g_64 bds_64 18 (dagTraceF m_64 s_64 7 f_64) l_64) = true := by decide +kernel

theorem join_64_0 : ∀ j, 0 ≤ j → j < 16 → (dagCheckNodeF m_64 g_64 bds_64 18 (dagTraceF m_64 s_64 7 f_64) l_64) j = true := (fun _ h₁ h₂ => treeBlockF_at block_64_0 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_64_16 : treeBlockF 16 18 (dagCheckNodeF m_64 g_64 bds_64 18 (dagTraceF m_64 s_64 7 f_64) l_64) = true := by decide +kernel

theorem join_64_16 : ∀ j, 0 ≤ j → j < 18 → (dagCheckNodeF m_64 g_64 bds_64 18 (dagTraceF m_64 s_64 7 f_64) l_64) j = true := block_join join_64_0 (fun _ h₁ h₂ => treeBlockF_at block_64_16 h₁ h₂)

theorem nc_64 : ∀ j, 0 ≤ j → j < 18 → (dagCheckNodeF m_64 g_64 bds_64 18 (dagTraceF m_64 s_64 7 f_64) l_64) j = true := join_64_16

theorem lb_64 : LowerBin m_64 s_64 g_64 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_64 sub_64 gl_64 rc_64 nc_64

def m_65 : Nat := 0x5555000000000000

def s_65 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]

def g_65 : Nat := 0x115000000000000

def bds_65 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_65 : KnownBin bds_65 := by
  intro b hb; simp [bds_65] at hb

theorem sub_65 : ∀ b ∈ bds_65, m_65 &&& b.1 = b.1 := by
  intro b hb; simp [bds_65] at hb

theorem gl_65 : ∀ b ∈ bds_65, canon b.1 g_65 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_65] at hb

def f_65 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_65 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_65 : dagCheckRootsF m_65 g_65 bds_65 (dagRefF 1 (dagTraceF m_65 s_65 3 f_65) l_65 0) s_65 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_65_0 : treeBlockF 0 1 (dagCheckNodeF m_65 g_65 bds_65 1 (dagTraceF m_65 s_65 3 f_65) l_65) = true := by decide +kernel

theorem join_65_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_65 g_65 bds_65 1 (dagTraceF m_65 s_65 3 f_65) l_65) j = true := (fun _ h₁ h₂ => treeBlockF_at block_65_0 h₁ h₂)

theorem nc_65 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_65 g_65 bds_65 1 (dagTraceF m_65 s_65 3 f_65) l_65) j = true := join_65_0

theorem lb_65 : LowerBin m_65 s_65 g_65 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_65 sub_65 gl_65 rc_65 nc_65

def m_66 : Nat := 0x3333000000000000

def s_66 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]

def g_66 : Nat := 0x113000000000000

def bds_66 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_66 : KnownBin bds_66 := by
  intro b hb; simp [bds_66] at hb

theorem sub_66 : ∀ b ∈ bds_66, m_66 &&& b.1 = b.1 := by
  intro b hb; simp [bds_66] at hb

theorem gl_66 : ∀ b ∈ bds_66, canon b.1 g_66 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_66] at hb

def f_66 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_66 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_66 : dagCheckRootsF m_66 g_66 bds_66 (dagRefF 1 (dagTraceF m_66 s_66 3 f_66) l_66 0) s_66 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_66_0 : treeBlockF 0 1 (dagCheckNodeF m_66 g_66 bds_66 1 (dagTraceF m_66 s_66 3 f_66) l_66) = true := by decide +kernel

theorem join_66_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_66 g_66 bds_66 1 (dagTraceF m_66 s_66 3 f_66) l_66) j = true := (fun _ h₁ h₂ => treeBlockF_at block_66_0 h₁ h₂)

theorem nc_66 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_66 g_66 bds_66 1 (dagTraceF m_66 s_66 3 f_66) l_66) j = true := join_66_0

theorem lb_66 : LowerBin m_66 s_66 g_66 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_66 sub_66 gl_66 rc_66 nc_66

def m_67 : Nat := 0xf0f000000000000

def s_67 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]

def g_67 : Nat := 0x107000000000000

def bds_67 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_67 : KnownBin bds_67 := by
  intro b hb; simp [bds_67] at hb

theorem sub_67 : ∀ b ∈ bds_67, m_67 &&& b.1 = b.1 := by
  intro b hb; simp [bds_67] at hb

theorem gl_67 : ∀ b ∈ bds_67, canon b.1 g_67 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_67] at hb

def f_67 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_67 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_67 : dagCheckRootsF m_67 g_67 bds_67 (dagRefF 1 (dagTraceF m_67 s_67 3 f_67) l_67 0) s_67 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_67_0 : treeBlockF 0 1 (dagCheckNodeF m_67 g_67 bds_67 1 (dagTraceF m_67 s_67 3 f_67) l_67) = true := by decide +kernel

theorem join_67_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_67 g_67 bds_67 1 (dagTraceF m_67 s_67 3 f_67) l_67) j = true := (fun _ h₁ h₂ => treeBlockF_at block_67_0 h₁ h₂)

theorem nc_67 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_67 g_67 bds_67 1 (dagTraceF m_67 s_67 3 f_67) l_67) j = true := join_67_0

theorem lb_67 : LowerBin m_67 s_67 g_67 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_67 sub_67 gl_67 rc_67 nc_67

def m_68 : Nat := 0xff000000000000

def s_68 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]

def g_68 : Nat := 0x17000000000000

def bds_68 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_68 : KnownBin bds_68 := by
  intro b hb; simp [bds_68] at hb

theorem sub_68 : ∀ b ∈ bds_68, m_68 &&& b.1 = b.1 := by
  intro b hb; simp [bds_68] at hb

theorem gl_68 : ∀ b ∈ bds_68, canon b.1 g_68 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_68] at hb

def f_68 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_68 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_68 : dagCheckRootsF m_68 g_68 bds_68 (dagRefF 1 (dagTraceF m_68 s_68 3 f_68) l_68 0) s_68 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_68_0 : treeBlockF 0 1 (dagCheckNodeF m_68 g_68 bds_68 1 (dagTraceF m_68 s_68 3 f_68) l_68) = true := by decide +kernel

theorem join_68_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_68 g_68 bds_68 1 (dagTraceF m_68 s_68 3 f_68) l_68) j = true := (fun _ h₁ h₂ => treeBlockF_at block_68_0 h₁ h₂)

theorem nc_68 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_68 g_68 bds_68 1 (dagTraceF m_68 s_68 3 f_68) l_68) j = true := join_68_0

theorem lb_68 : LowerBin m_68 s_68 g_68 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_68 sub_68 gl_68 rc_68 nc_68

def m_69 : Nat := 0xffff000000000000

def s_69 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]

def g_69 : Nat := 0x117000000000000

def bds_69 : List (Nat × List Nat × Nat × Nat) := [(m_65, s_65, 4, g_65), (m_66, s_66, 4, g_66), (m_67, s_67, 4, g_67), (m_68, s_68, 4, g_68)]

theorem kn_69 : KnownBin bds_69 := by
  intro b hb; simp only [bds_69, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_65
  · exact lb_66
  · exact lb_67
  · exact lb_68

theorem sub_69 : ∀ b ∈ bds_69, m_69 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_69, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

theorem gl_69 : ∀ b ∈ bds_69, canon b.1 g_69 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_69, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

def f_69 : Nat → Nat × Nat := unpackForestF 0x1dd0360c4f408858d901918283c409874a4e149b41327c6064ba116422a9c5508a0c9341248240f88170f421c6235086270c42185c2908519094212642138421083e106418cc29985230866108c209800f 5 10

def l_69 : Nat → Nat → Option Nat := unpackLinksF 0x8e11c2384708e11c2384708e11c230c608c114620c408630c210c1182104200bf17c2f81e8bd0782ec5d0b91720e05c03715f09e0fc1781f01e00b001 0xaa40aa40ab40a418a1409930a1409530a3409c2c994095309a409630903c8c4c81417531892969216041503184294021834172327d3e69325c41382178192411774272426d4e69424c31342164191c1163415e4149323122583e4032542e242253424e3149422d22444e40423c2e1c223a42363231422d32284e2442203e1c321a33153311230c3308230413000f 11 4 10 6 5

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_69 : dagCheckRootsF m_69 g_69 bds_69 (dagRefF 43 (dagTraceF m_69 s_69 6 f_69) l_69 0) s_69 6 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_69_0 : treeBlockF 0 16 (dagCheckNodeF m_69 g_69 bds_69 43 (dagTraceF m_69 s_69 6 f_69) l_69) = true := by decide +kernel

theorem join_69_0 : ∀ j, 0 ≤ j → j < 16 → (dagCheckNodeF m_69 g_69 bds_69 43 (dagTraceF m_69 s_69 6 f_69) l_69) j = true := (fun _ h₁ h₂ => treeBlockF_at block_69_0 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_69_16 : treeBlockF 16 32 (dagCheckNodeF m_69 g_69 bds_69 43 (dagTraceF m_69 s_69 6 f_69) l_69) = true := by decide +kernel

theorem join_69_16 : ∀ j, 0 ≤ j → j < 32 → (dagCheckNodeF m_69 g_69 bds_69 43 (dagTraceF m_69 s_69 6 f_69) l_69) j = true := block_join join_69_0 (fun _ h₁ h₂ => treeBlockF_at block_69_16 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_69_32 : treeBlockF 32 43 (dagCheckNodeF m_69 g_69 bds_69 43 (dagTraceF m_69 s_69 6 f_69) l_69) = true := by decide +kernel

theorem join_69_32 : ∀ j, 0 ≤ j → j < 43 → (dagCheckNodeF m_69 g_69 bds_69 43 (dagTraceF m_69 s_69 6 f_69) l_69) j = true := block_join join_69_16 (fun _ h₁ h₂ => treeBlockF_at block_69_32 h₁ h₂)

theorem nc_69 : ∀ j, 0 ≤ j → j < 43 → (dagCheckNodeF m_69 g_69 bds_69 43 (dagTraceF m_69 s_69 6 f_69) l_69) j = true := join_69_32

theorem lb_69 : LowerBin m_69 s_69 g_69 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_69 sub_69 gl_69 rc_69 nc_69

def m_70 : Nat := 0x5050505000000000

def s_70 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]

def g_70 : Nat := 0x10105000000000

def bds_70 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_70 : KnownBin bds_70 := by
  intro b hb; simp [bds_70] at hb

theorem sub_70 : ∀ b ∈ bds_70, m_70 &&& b.1 = b.1 := by
  intro b hb; simp [bds_70] at hb

theorem gl_70 : ∀ b ∈ bds_70, canon b.1 g_70 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_70] at hb

def f_70 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_70 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_70 : dagCheckRootsF m_70 g_70 bds_70 (dagRefF 1 (dagTraceF m_70 s_70 3 f_70) l_70 0) s_70 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_70_0 : treeBlockF 0 1 (dagCheckNodeF m_70 g_70 bds_70 1 (dagTraceF m_70 s_70 3 f_70) l_70) = true := by decide +kernel

theorem join_70_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_70 g_70 bds_70 1 (dagTraceF m_70 s_70 3 f_70) l_70) j = true := (fun _ h₁ h₂ => treeBlockF_at block_70_0 h₁ h₂)

theorem nc_70 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_70 g_70 bds_70 1 (dagTraceF m_70 s_70 3 f_70) l_70) j = true := join_70_0

theorem lb_70 : LowerBin m_70 s_70 g_70 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_70 sub_70 gl_70 rc_70 nc_70

def m_71 : Nat := 0x4444444400000000

def s_71 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]

def g_71 : Nat := 0x4044400000000

def bds_71 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_71 : KnownBin bds_71 := by
  intro b hb; simp [bds_71] at hb

theorem sub_71 : ∀ b ∈ bds_71, m_71 &&& b.1 = b.1 := by
  intro b hb; simp [bds_71] at hb

theorem gl_71 : ∀ b ∈ bds_71, canon b.1 g_71 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_71] at hb

def f_71 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_71 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_71 : dagCheckRootsF m_71 g_71 bds_71 (dagRefF 1 (dagTraceF m_71 s_71 3 f_71) l_71 0) s_71 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_71_0 : treeBlockF 0 1 (dagCheckNodeF m_71 g_71 bds_71 1 (dagTraceF m_71 s_71 3 f_71) l_71) = true := by decide +kernel

theorem join_71_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_71 g_71 bds_71 1 (dagTraceF m_71 s_71 3 f_71) l_71) j = true := (fun _ h₁ h₂ => treeBlockF_at block_71_0 h₁ h₂)

theorem nc_71 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_71 g_71 bds_71 1 (dagTraceF m_71 s_71 3 f_71) l_71) j = true := join_71_0

theorem lb_71 : LowerBin m_71 s_71 g_71 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_71 sub_71 gl_71 rc_71 nc_71

def m_72 : Nat := 0x5555555500000000

def s_72 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]

def g_72 : Nat := 0x115155500000000

def bds_72 : List (Nat × List Nat × Nat × Nat) := [(m_65, s_65, 4, g_65), (m_22, s_22, 4, g_22), (m_70, s_70, 4, g_70), (m_71, s_71, 4, g_71)]

theorem kn_72 : KnownBin bds_72 := by
  intro b hb; simp only [bds_72, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_65
  · exact lb_22
  · exact lb_70
  · exact lb_71

theorem sub_72 : ∀ b ∈ bds_72, m_72 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_72, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

theorem gl_72 : ∀ b ∈ bds_72, canon b.1 g_72 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_72, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

def f_72 : Nat → Nat × Nat := unpackForestF 0x1d13369a514c8268e9319a4243440487534e269a4d346a6134ba517462c8c5518a1e924d246a453489a8f4a1e8c391869e8d25188c29285230a3a146c251849b0846106c18dc29b8527086e109c20b800f 5 10

def l_72 : Nat → Nat → Option Nat := unpackLinksF 0x8e11c2384708e11c2384708e11c2384618c118228c418630c218421841046084017e2fc1f0bd17a0f05e03b1742e45c0b715f09e0fc1781f01e00b001 0xa524a84ca534a5349c249014a14c9c348c149d349a4c974890348c2490348c24894d71457d356d25844d4c455c354825824d72457e356926784d344554352815774a73466e466946643d2c3540252415624d4e455e35594d354555353c262016534a4f464a46453d2d3541253c461c163a4a3646323a2e362946253620461c361a37153711270c3708270417000f 11 4 10 6 5

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_72 : dagCheckRootsF m_72 g_72 bds_72 (dagRefF 43 (dagTraceF m_72 s_72 6 f_72) l_72 0) s_72 6 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_72_0 : treeBlockF 0 16 (dagCheckNodeF m_72 g_72 bds_72 43 (dagTraceF m_72 s_72 6 f_72) l_72) = true := by decide +kernel

theorem join_72_0 : ∀ j, 0 ≤ j → j < 16 → (dagCheckNodeF m_72 g_72 bds_72 43 (dagTraceF m_72 s_72 6 f_72) l_72) j = true := (fun _ h₁ h₂ => treeBlockF_at block_72_0 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_72_16 : treeBlockF 16 32 (dagCheckNodeF m_72 g_72 bds_72 43 (dagTraceF m_72 s_72 6 f_72) l_72) = true := by decide +kernel

theorem join_72_16 : ∀ j, 0 ≤ j → j < 32 → (dagCheckNodeF m_72 g_72 bds_72 43 (dagTraceF m_72 s_72 6 f_72) l_72) j = true := block_join join_72_0 (fun _ h₁ h₂ => treeBlockF_at block_72_16 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_72_32 : treeBlockF 32 43 (dagCheckNodeF m_72 g_72 bds_72 43 (dagTraceF m_72 s_72 6 f_72) l_72) = true := by decide +kernel

theorem join_72_32 : ∀ j, 0 ≤ j → j < 43 → (dagCheckNodeF m_72 g_72 bds_72 43 (dagTraceF m_72 s_72 6 f_72) l_72) j = true := block_join join_72_16 (fun _ h₁ h₂ => treeBlockF_at block_72_32 h₁ h₂)

theorem nc_72 : ∀ j, 0 ≤ j → j < 43 → (dagCheckNodeF m_72 g_72 bds_72 43 (dagTraceF m_72 s_72 6 f_72) l_72) j = true := join_72_32

theorem lb_72 : LowerBin m_72 s_72 g_72 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_72 sub_72 gl_72 rc_72 nc_72

def m_73 : Nat := 0xf0f0f0f000000000

def s_73 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]

def g_73 : Nat := 0x10105000000000

def bds_73 : List (Nat × List Nat × Nat × Nat) := [(m_70, s_70, 4, g_70)]

theorem kn_73 : KnownBin bds_73 := by
  intro b hb; simp only [bds_73, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_70

theorem sub_73 : ∀ b ∈ bds_73, m_73 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_73, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_73 : ∀ b ∈ bds_73, canon b.1 g_73 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_73, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_73 : Nat → Nat × Nat := fun _ => (0, 0)

def l_73 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_73 : dagCheckRootsF m_73 g_73 bds_73 (dagRefF 0 (dagTraceF m_73 s_73 4 f_73) l_73 0) s_73 4 = true := by decide +kernel

theorem nc_73 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_73 g_73 bds_73 0 (dagTraceF m_73 s_73 4 f_73) l_73) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_73 : LowerBin m_73 s_73 g_73 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_73 sub_73 gl_73 rc_73 nc_73

def m_74 : Nat := 0xcccccccc00000000

def s_74 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]

def g_74 : Nat := 0x4044400000000

def bds_74 : List (Nat × List Nat × Nat × Nat) := [(m_71, s_71, 4, g_71)]

theorem kn_74 : KnownBin bds_74 := by
  intro b hb; simp only [bds_74, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_71

theorem sub_74 : ∀ b ∈ bds_74, m_74 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_74, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_74 : ∀ b ∈ bds_74, canon b.1 g_74 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_74, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_74 : Nat → Nat × Nat := fun _ => (0, 0)

def l_74 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_74 : dagCheckRootsF m_74 g_74 bds_74 (dagRefF 0 (dagTraceF m_74 s_74 4 f_74) l_74 0) s_74 4 = true := by decide +kernel

theorem nc_74 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_74 g_74 bds_74 0 (dagTraceF m_74 s_74 4 f_74) l_74) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_74 : LowerBin m_74 s_74 g_74 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_74 sub_74 gl_74 rc_74 nc_74

def m_75 : Nat := 0x3333333300000000

def s_75 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]

def g_75 : Nat := 0x113111300000000

def bds_75 : List (Nat × List Nat × Nat × Nat) := [(m_66, s_66, 4, g_66)]

theorem kn_75 : KnownBin bds_75 := by
  intro b hb; simp only [bds_75, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_66

theorem sub_75 : ∀ b ∈ bds_75, m_75 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_75, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_75 : ∀ b ∈ bds_75, canon b.1 g_75 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_75, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_75 : Nat → Nat × Nat := fun _ => (0, 0)

def l_75 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_75 : dagCheckRootsF m_75 g_75 bds_75 (dagRefF 0 (dagTraceF m_75 s_75 4 f_75) l_75 0) s_75 4 = true := by decide +kernel

theorem nc_75 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_75 g_75 bds_75 0 (dagTraceF m_75 s_75 4 f_75) l_75) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_75 : LowerBin m_75 s_75 g_75 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_75 sub_75 gl_75 rc_75 nc_75

def m_76 : Nat := 0xf0f0f0f00000000

def s_76 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]

def g_76 : Nat := 0x107050700000000

def bds_76 : List (Nat × List Nat × Nat × Nat) := [(m_67, s_67, 4, g_67)]

theorem kn_76 : KnownBin bds_76 := by
  intro b hb; simp only [bds_76, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_67

theorem sub_76 : ∀ b ∈ bds_76, m_76 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_76, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_76 : ∀ b ∈ bds_76, canon b.1 g_76 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_76, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_76 : Nat → Nat × Nat := fun _ => (0, 0)

def l_76 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_76 : dagCheckRootsF m_76 g_76 bds_76 (dagRefF 0 (dagTraceF m_76 s_76 4 f_76) l_76 0) s_76 4 = true := by decide +kernel

theorem nc_76 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_76 g_76 bds_76 0 (dagTraceF m_76 s_76 4 f_76) l_76) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_76 : LowerBin m_76 s_76 g_76 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_76 sub_76 gl_76 rc_76 nc_76

def m_77 : Nat := 0xff00ff00000000

def s_77 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]

def g_77 : Nat := 0x17005700000000

def bds_77 : List (Nat × List Nat × Nat × Nat) := [(m_68, s_68, 4, g_68)]

theorem kn_77 : KnownBin bds_77 := by
  intro b hb; simp only [bds_77, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_68

theorem sub_77 : ∀ b ∈ bds_77, m_77 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_77, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_77 : ∀ b ∈ bds_77, canon b.1 g_77 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_77, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_77 : Nat → Nat × Nat := fun _ => (0, 0)

def l_77 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_77 : dagCheckRootsF m_77 g_77 bds_77 (dagRefF 0 (dagTraceF m_77 s_77 4 f_77) l_77 0) s_77 4 = true := by decide +kernel

theorem nc_77 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_77 g_77 bds_77 0 (dagTraceF m_77 s_77 4 f_77) l_77) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_77 : LowerBin m_77 s_77 g_77 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_77 sub_77 gl_77 rc_77 nc_77

def m_78 : Nat := 0xf00ff00f00000000

def s_78 : List Nat := [0x5005500500000000, 0x3003300300000000, 0xf000f00000000, 0xf00f00000000]

def g_78 : Nat := 0x7100700000000

def bds_78 : List (Nat × List Nat × Nat × Nat) := [(m_33, s_33, 4, g_33)]

theorem kn_78 : KnownBin bds_78 := by
  intro b hb; simp only [bds_78, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_33

theorem sub_78 : ∀ b ∈ bds_78, m_78 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_78, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_78 : ∀ b ∈ bds_78, canon b.1 g_78 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_78, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_78 : Nat → Nat × Nat := fun _ => (0, 0)

def l_78 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_78 : dagCheckRootsF m_78 g_78 bds_78 (dagRefF 0 (dagTraceF m_78 s_78 4 f_78) l_78 0) s_78 4 = true := by decide +kernel

theorem nc_78 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_78 g_78 bds_78 0 (dagTraceF m_78 s_78 4 f_78) l_78) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_78 : LowerBin m_78 s_78 g_78 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_78 sub_78 gl_78 rc_78 nc_78

def m_79 : Nat := 0xcc33cc3300000000

def s_79 : List Nat := [0x4411441100000000, 0x33003300000000, 0xc030c0300000000, 0xcc3300000000]

def g_79 : Nat := 0x13041300000000

def bds_79 : List (Nat × List Nat × Nat × Nat) := [(m_34, s_34, 4, g_34)]

theorem kn_79 : KnownBin bds_79 := by
  intro b hb; simp only [bds_79, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_34

theorem sub_79 : ∀ b ∈ bds_79, m_79 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_79, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_79 : ∀ b ∈ bds_79, canon b.1 g_79 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_79, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_79 : Nat → Nat × Nat := fun _ => (0, 0)

def l_79 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_79 : dagCheckRootsF m_79 g_79 bds_79 (dagRefF 0 (dagTraceF m_79 s_79 4 f_79) l_79 0) s_79 4 = true := by decide +kernel

theorem nc_79 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_79 g_79 bds_79 0 (dagTraceF m_79 s_79 4 f_79) l_79) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_79 : LowerBin m_79 s_79 g_79 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_79 sub_79 gl_79 rc_79 nc_79

def m_80 : Nat := 0xc3c3c3c300000000

def s_80 : List Nat := [0x4141414100000000, 0x303030300000000, 0xc300c300000000, 0xc3c300000000]

def g_80 : Nat := 0x103014300000000

def bds_80 : List (Nat × List Nat × Nat × Nat) := [(m_35, s_35, 4, g_35)]

theorem kn_80 : KnownBin bds_80 := by
  intro b hb; simp only [bds_80, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_35

theorem sub_80 : ∀ b ∈ bds_80, m_80 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_80, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_80 : ∀ b ∈ bds_80, canon b.1 g_80 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_80, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_80 : Nat → Nat × Nat := fun _ => (0, 0)

def l_80 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_80 : dagCheckRootsF m_80 g_80 bds_80 (dagRefF 0 (dagTraceF m_80 s_80 4 f_80) l_80 0) s_80 4 = true := by decide +kernel

theorem nc_80 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_80 g_80 bds_80 0 (dagTraceF m_80 s_80 4 f_80) l_80) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_80 : LowerBin m_80 s_80 g_80 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_80 sub_80 gl_80 rc_80 nc_80

def m_81 : Nat := 0xffffffff00000000

def s_81 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]

def g_81 : Nat := 0x117155700000000

def bds_81 : List (Nat × List Nat × Nat × Nat) := [(m_69, s_69, 7, g_69), (m_72, s_72, 7, g_72), (m_31, s_31, 5, g_31), (m_73, s_73, 5, g_73), (m_74, s_74, 5, g_74), (m_75, s_75, 5, g_75), (m_76, s_76, 5, g_76), (m_77, s_77, 5, g_77), (m_39, s_39, 6, g_39), (m_78, s_78, 5, g_78), (m_79, s_79, 5, g_79), (m_80, s_80, 5, g_80)]

theorem kn_81 : KnownBin bds_81 := by
  intro b hb; simp only [bds_81, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_69
  · exact lb_72
  · exact lb_31
  · exact lb_73
  · exact lb_74
  · exact lb_75
  · exact lb_76
  · exact lb_77
  · exact lb_39
  · exact lb_78
  · exact lb_79
  · exact lb_80

theorem sub_81 : ∀ b ∈ bds_81, m_81 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_81, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem gl_81 : ∀ b ∈ bds_81, canon b.1 g_81 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_81, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def f_81 : Nat → Nat × Nat := unpackForestF 0xad11a4428d063f18ec63718cc53f14ec53714cc52f14ac527148c01f 4 10

def l_81 : Nat → Nat → Option Nat := unpackLinksF 0x130984c2613090c46211080bc5e0f070b443801 0x3e30fd13930e913520d8d323fb8eea3798ce13f74ed93754cd12f34ac927148c01f 9 4 10 4 5

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_81 : dagCheckRootsF m_81 g_81 bds_81 (dagRefF 16 (dagTraceF m_81 s_81 8 f_81) l_81 0) s_81 8 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_81_0 : treeBlockF 0 16 (dagCheckNodeF m_81 g_81 bds_81 16 (dagTraceF m_81 s_81 8 f_81) l_81) = true := by decide +kernel

theorem join_81_0 : ∀ j, 0 ≤ j → j < 16 → (dagCheckNodeF m_81 g_81 bds_81 16 (dagTraceF m_81 s_81 8 f_81) l_81) j = true := (fun _ h₁ h₂ => treeBlockF_at block_81_0 h₁ h₂)

theorem nc_81 : ∀ j, 0 ≤ j → j < 16 → (dagCheckNodeF m_81 g_81 bds_81 16 (dagTraceF m_81 s_81 8 f_81) l_81) j = true := join_81_0

theorem lb_81 : LowerBin m_81 s_81 g_81 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_81 sub_81 gl_81 rc_81 nc_81

def m_82 : Nat := 0x1212121212121212

def s_82 : List Nat := [0x202020202020202, 0x12001200120012, 0x121200001212, 0x12121212]

def g_82 : Nat := 0x12101210121212

def bds_82 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]

theorem kn_82 : KnownBin bds_82 := by
  intro b hb; simp only [bds_82, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9

theorem sub_82 : ∀ b ∈ bds_82, m_82 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_82, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_82 : ∀ b ∈ bds_82, canon b.1 g_82 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_82, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_82 : Nat → Nat × Nat := fun _ => (0, 0)

def l_82 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_82 : dagCheckRootsF m_82 g_82 bds_82 (dagRefF 0 (dagTraceF m_82 s_82 4 f_82) l_82 0) s_82 4 = true := by decide +kernel

theorem nc_82 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_82 g_82 bds_82 0 (dagTraceF m_82 s_82 4 f_82) l_82) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_82 : LowerBin m_82 s_82 g_82 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_82 sub_82 gl_82 rc_82 nc_82

def m_83 : Nat := 0x3333000033330000

def s_83 : List Nat := [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000]

def g_83 : Nat := 0x113000011130000

def bds_83 : List (Nat × List Nat × Nat × Nat) := [(m_66, s_66, 4, g_66)]

theorem kn_83 : KnownBin bds_83 := by
  intro b hb; simp only [bds_83, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_66

theorem sub_83 : ∀ b ∈ bds_83, m_83 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_83, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_83 : ∀ b ∈ bds_83, canon b.1 g_83 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_83, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_83 : Nat → Nat × Nat := fun _ => (0, 0)

def l_83 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_83 : dagCheckRootsF m_83 g_83 bds_83 (dagRefF 0 (dagTraceF m_83 s_83 4 f_83) l_83 0) s_83 4 = true := by decide +kernel

theorem nc_83 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_83 g_83 bds_83 0 (dagTraceF m_83 s_83 4 f_83) l_83) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_83 : LowerBin m_83 s_83 g_83 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_83 sub_83 gl_83 rc_83 nc_83

def m_84 : Nat := 0x3030000003030000

def s_84 : List Nat := [0x1010000001010000, 0x3030000, 0x30000000030000]

def g_84 : Nat := 0x10000001030000

def bds_84 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_84 : KnownBin bds_84 := by
  intro b hb; simp [bds_84] at hb

theorem sub_84 : ∀ b ∈ bds_84, m_84 &&& b.1 = b.1 := by
  intro b hb; simp [bds_84] at hb

theorem gl_84 : ∀ b ∈ bds_84, canon b.1 g_84 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_84] at hb

def f_84 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_84 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_84 : dagCheckRootsF m_84 g_84 bds_84 (dagRefF 1 (dagTraceF m_84 s_84 3 f_84) l_84 0) s_84 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_84_0 : treeBlockF 0 1 (dagCheckNodeF m_84 g_84 bds_84 1 (dagTraceF m_84 s_84 3 f_84) l_84) = true := by decide +kernel

theorem join_84_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_84 g_84 bds_84 1 (dagTraceF m_84 s_84 3 f_84) l_84) j = true := (fun _ h₁ h₂ => treeBlockF_at block_84_0 h₁ h₂)

theorem nc_84 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_84 g_84 bds_84 1 (dagTraceF m_84 s_84 3 f_84) l_84) j = true := join_84_0

theorem lb_84 : LowerBin m_84 s_84 g_84 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_84 sub_84 gl_84 rc_84 nc_84

def m_85 : Nat := 0x3030303003030303

def s_85 : List Nat := [0x1010101001010101, 0x3030303, 0x30003000030003, 0x303000000303]

def g_85 : Nat := 0x10101001030303

def bds_85 : List (Nat × List Nat × Nat × Nat) := [(m_84, s_84, 4, g_84)]

theorem kn_85 : KnownBin bds_85 := by
  intro b hb; simp only [bds_85, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_84

theorem sub_85 : ∀ b ∈ bds_85, m_85 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_85, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_85 : ∀ b ∈ bds_85, canon b.1 g_85 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_85, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_85 : Nat → Nat × Nat := fun _ => (0, 0)

def l_85 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_85 : dagCheckRootsF m_85 g_85 bds_85 (dagRefF 0 (dagTraceF m_85 s_85 4 f_85) l_85 0) s_85 4 = true := by decide +kernel

theorem nc_85 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_85 g_85 bds_85 0 (dagTraceF m_85 s_85 4 f_85) l_85) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_85 : LowerBin m_85 s_85 g_85 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_85 sub_85 gl_85 rc_85 nc_85

def m_86 : Nat := 0x3030030300000000

def s_86 : List Nat := [0x1010010100000000, 0x30300000000, 0x30000300000000]

def g_86 : Nat := 0x10010300000000

def bds_86 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_86 : KnownBin bds_86 := by
  intro b hb; simp [bds_86] at hb

theorem sub_86 : ∀ b ∈ bds_86, m_86 &&& b.1 = b.1 := by
  intro b hb; simp [bds_86] at hb

theorem gl_86 : ∀ b ∈ bds_86, canon b.1 g_86 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_86] at hb

def f_86 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_86 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_86 : dagCheckRootsF m_86 g_86 bds_86 (dagRefF 1 (dagTraceF m_86 s_86 3 f_86) l_86 0) s_86 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_86_0 : treeBlockF 0 1 (dagCheckNodeF m_86 g_86 bds_86 1 (dagTraceF m_86 s_86 3 f_86) l_86) = true := by decide +kernel

theorem join_86_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_86 g_86 bds_86 1 (dagTraceF m_86 s_86 3 f_86) l_86) j = true := (fun _ h₁ h₂ => treeBlockF_at block_86_0 h₁ h₂)

theorem nc_86 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_86 g_86 bds_86 1 (dagTraceF m_86 s_86 3 f_86) l_86) j = true := join_86_0

theorem lb_86 : LowerBin m_86 s_86 g_86 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_86 sub_86 gl_86 rc_86 nc_86

def m_87 : Nat := 0x3030030330300303

def s_87 : List Nat := [0x1010010110100101, 0x30300000303, 0x30000300300003, 0x30300303]

def g_87 : Nat := 0x10010310100303

def bds_87 : List (Nat × List Nat × Nat × Nat) := [(m_86, s_86, 4, g_86)]

theorem kn_87 : KnownBin bds_87 := by
  intro b hb; simp only [bds_87, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_86

theorem sub_87 : ∀ b ∈ bds_87, m_87 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_87, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_87 : ∀ b ∈ bds_87, canon b.1 g_87 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_87, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_87 : Nat → Nat × Nat := fun _ => (0, 0)

def l_87 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_87 : dagCheckRootsF m_87 g_87 bds_87 (dagRefF 0 (dagTraceF m_87 s_87 4 f_87) l_87 0) s_87 4 = true := by decide +kernel

theorem nc_87 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_87 g_87 bds_87 0 (dagTraceF m_87 s_87 4 f_87) l_87) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_87 : LowerBin m_87 s_87 g_87 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_87 sub_87 gl_87 rc_87 nc_87

def m_88 : Nat := 0x1111222200000000

def s_88 : List Nat := [0x222200000000, 0x101020200000000, 0x11002200000000]

def g_88 : Nat := 0x111000200000000

def bds_88 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_88 : KnownBin bds_88 := by
  intro b hb; simp [bds_88] at hb

theorem sub_88 : ∀ b ∈ bds_88, m_88 &&& b.1 = b.1 := by
  intro b hb; simp [bds_88] at hb

theorem gl_88 : ∀ b ∈ bds_88, canon b.1 g_88 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_88] at hb

def f_88 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_88 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_88 : dagCheckRootsF m_88 g_88 bds_88 (dagRefF 1 (dagTraceF m_88 s_88 3 f_88) l_88 0) s_88 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_88_0 : treeBlockF 0 1 (dagCheckNodeF m_88 g_88 bds_88 1 (dagTraceF m_88 s_88 3 f_88) l_88) = true := by decide +kernel

theorem join_88_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_88 g_88 bds_88 1 (dagTraceF m_88 s_88 3 f_88) l_88) j = true := (fun _ h₁ h₂ => treeBlockF_at block_88_0 h₁ h₂)

theorem nc_88 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_88 g_88 bds_88 1 (dagTraceF m_88 s_88 3 f_88) l_88) j = true := join_88_0

theorem lb_88 : LowerBin m_88 s_88 g_88 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_88 sub_88 gl_88 rc_88 nc_88

def m_89 : Nat := 0x1111222211112222

def s_89 : List Nat := [0x222200002222, 0x101020201010202, 0x11002200110022, 0x11112222]

def g_89 : Nat := 0x111000211110202

def bds_89 : List (Nat × List Nat × Nat × Nat) := [(m_88, s_88, 4, g_88)]

theorem kn_89 : KnownBin bds_89 := by
  intro b hb; simp only [bds_89, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_88

theorem sub_89 : ∀ b ∈ bds_89, m_89 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_89, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_89 : ∀ b ∈ bds_89, canon b.1 g_89 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_89, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_89 : Nat → Nat × Nat := fun _ => (0, 0)

def l_89 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_89 : dagCheckRootsF m_89 g_89 bds_89 (dagRefF 0 (dagTraceF m_89 s_89 4 f_89) l_89 0) s_89 4 = true := by decide +kernel

theorem nc_89 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_89 g_89 bds_89 0 (dagTraceF m_89 s_89 4 f_89) l_89) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_89 : LowerBin m_89 s_89 g_89 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_89 sub_89 gl_89 rc_89 nc_89

def m_90 : Nat := 0x1111000022220000

def s_90 : List Nat := [0x22220000, 0x101000002020000, 0x11000000220000]

def g_90 : Nat := 0x111000000020000

def bds_90 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_90 : KnownBin bds_90 := by
  intro b hb; simp [bds_90] at hb

theorem sub_90 : ∀ b ∈ bds_90, m_90 &&& b.1 = b.1 := by
  intro b hb; simp [bds_90] at hb

theorem gl_90 : ∀ b ∈ bds_90, canon b.1 g_90 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_90] at hb

def f_90 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_90 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_90 : dagCheckRootsF m_90 g_90 bds_90 (dagRefF 1 (dagTraceF m_90 s_90 3 f_90) l_90 0) s_90 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_90_0 : treeBlockF 0 1 (dagCheckNodeF m_90 g_90 bds_90 1 (dagTraceF m_90 s_90 3 f_90) l_90) = true := by decide +kernel

theorem join_90_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_90 g_90 bds_90 1 (dagTraceF m_90 s_90 3 f_90) l_90) j = true := (fun _ h₁ h₂ => treeBlockF_at block_90_0 h₁ h₂)

theorem nc_90 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_90 g_90 bds_90 1 (dagTraceF m_90 s_90 3 f_90) l_90) j = true := join_90_0

theorem lb_90 : LowerBin m_90 s_90 g_90 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_90 sub_90 gl_90 rc_90 nc_90

def m_91 : Nat := 0x1111111122222222

def s_91 : List Nat := [0x22222222, 0x101010102020202, 0x11001100220022, 0x111100002222]

def g_91 : Nat := 0x111111100020202

def bds_91 : List (Nat × List Nat × Nat × Nat) := [(m_90, s_90, 4, g_90)]

theorem kn_91 : KnownBin bds_91 := by
  intro b hb; simp only [bds_91, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_90

theorem sub_91 : ∀ b ∈ bds_91, m_91 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_91, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_91 : ∀ b ∈ bds_91, canon b.1 g_91 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_91, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_91 : Nat → Nat × Nat := fun _ => (0, 0)

def l_91 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_91 : dagCheckRootsF m_91 g_91 bds_91 (dagRefF 0 (dagTraceF m_91 s_91 4 f_91) l_91 0) s_91 4 = true := by decide +kernel

theorem nc_91 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_91 g_91 bds_91 0 (dagTraceF m_91 s_91 4 f_91) l_91) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_91 : LowerBin m_91 s_91 g_91 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_91 sub_91 gl_91 rc_91 nc_91

def m_92 : Nat := 0x3333000000003333

def s_92 : List Nat := [0x1111000000001111, 0x303000000000303, 0x33000000000033, 0x3333]

def g_92 : Nat := 0x113000000001313

def bds_92 : List (Nat × List Nat × Nat × Nat) := [(m_66, s_66, 4, g_66)]

theorem kn_92 : KnownBin bds_92 := by
  intro b hb; simp only [bds_92, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_66

theorem sub_92 : ∀ b ∈ bds_92, m_92 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_92, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_92 : ∀ b ∈ bds_92, canon b.1 g_92 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_92, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_92 : Nat → Nat × Nat := fun _ => (0, 0)

def l_92 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_92 : dagCheckRootsF m_92 g_92 bds_92 (dagRefF 0 (dagTraceF m_92 s_92 4 f_92) l_92 0) s_92 4 = true := by decide +kernel

theorem nc_92 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_92 g_92 bds_92 0 (dagTraceF m_92 s_92 4 f_92) l_92) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_92 : LowerBin m_92 s_92 g_92 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_92 sub_92 gl_92 rc_92 nc_92

def m_93 : Nat := 0x3333333333333333

def s_93 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]

def g_93 : Nat := 0x113111311131313

def bds_93 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 6, g_12), (m_82, s_82, 5, g_82), (m_75, s_75, 5, g_75), (m_83, s_83, 5, g_83), (m_85, s_85, 5, g_85), (m_87, s_87, 5, g_87), (m_89, s_89, 5, g_89), (m_91, s_91, 5, g_91), (m_66, s_66, 4, g_66), (m_92, s_92, 5, g_92), (m_9, s_9, 4, g_9), (m_86, s_86, 4, g_86), (m_84, s_84, 4, g_84), (m_88, s_88, 4, g_88), (m_90, s_90, 4, g_90)]

theorem kn_93 : KnownBin bds_93 := by
  intro b hb; simp only [bds_93, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_12
  · exact lb_82
  · exact lb_75
  · exact lb_83
  · exact lb_85
  · exact lb_87
  · exact lb_89
  · exact lb_91
  · exact lb_66
  · exact lb_92
  · exact lb_9
  · exact lb_86
  · exact lb_84
  · exact lb_88
  · exact lb_90

theorem sub_93 : ∀ b ∈ bds_93, m_93 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_93, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem gl_93 : ∀ b ∈ bds_93, canon b.1 g_93 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_93, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def f_93 : Nat → Nat × Nat := unpackForestF 0x2084c80531725c4ad292b46448d0ea5c2a928aa46228d069451a114645e191746135180d45a5c16574595c16174585c14d78534e148d05135144d05035140d04b4912d14435d10d44405c0f1683c560ed783b560e57838340d178345a0d148335a0cd5831560ad242b4508d742351085701c5a071581b5e06d58193406178145e05168145204d681356041580b4f02d2c0b4702d0c094f0251c093f024dc084f0211c083f020dc001f 7 11

def l_93 : Nat → Nat → Option Nat := unpackLinksF 0xc618c318630c618c318630c618c310e11c2184308610c2184308610c2184308610c2184308610c2180700600c017c6f0de0bc1782e15c0b816c6d85b0b616c2d0da0b41682c8d81b01602b1560ac1582a8d50aa15427b478796d5d8a2d44ec858ea19426c3580e001 0x2504c92532425c8e11230348ed2a33468a8d2225c8651211348692a1246828d1f35a7ad65194d80514904d7e115f45e7b175494d40515e135301347845760d5a45d6ad75d25c72575c15c504f4f9356e175b05c2e0f470356ad79a34e668d19135624d180355e0d11b4d5cd256b454a4f9635d56d44f136541714c5a511593b5e4cd59295e480d11c5e451690c5240d68fb563c558934d3ad24e345260f8db5d34d44c95c1a0d8c45a2f158b35e2ad58a13426178945e2316884521ed6873561a158634f16d2c534712d0c414f0e51c313f0a4dc204f0611c103f020dc001f 11 4 11 7 5

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_93 : dagCheckRootsF m_93 g_93 bds_93 (dagRefF 75 (dagTraceF m_93 s_93 7 f_93) l_93 0) s_93 7 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_93_0 : treeBlockF 0 16 (dagCheckNodeF m_93 g_93 bds_93 75 (dagTraceF m_93 s_93 7 f_93) l_93) = true := by decide +kernel

theorem join_93_0 : ∀ j, 0 ≤ j → j < 16 → (dagCheckNodeF m_93 g_93 bds_93 75 (dagTraceF m_93 s_93 7 f_93) l_93) j = true := (fun _ h₁ h₂ => treeBlockF_at block_93_0 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_93_16 : treeBlockF 16 32 (dagCheckNodeF m_93 g_93 bds_93 75 (dagTraceF m_93 s_93 7 f_93) l_93) = true := by decide +kernel

theorem join_93_16 : ∀ j, 0 ≤ j → j < 32 → (dagCheckNodeF m_93 g_93 bds_93 75 (dagTraceF m_93 s_93 7 f_93) l_93) j = true := block_join join_93_0 (fun _ h₁ h₂ => treeBlockF_at block_93_16 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_93_32 : treeBlockF 32 48 (dagCheckNodeF m_93 g_93 bds_93 75 (dagTraceF m_93 s_93 7 f_93) l_93) = true := by decide +kernel

theorem join_93_32 : ∀ j, 0 ≤ j → j < 48 → (dagCheckNodeF m_93 g_93 bds_93 75 (dagTraceF m_93 s_93 7 f_93) l_93) j = true := block_join join_93_16 (fun _ h₁ h₂ => treeBlockF_at block_93_32 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_93_48 : treeBlockF 48 64 (dagCheckNodeF m_93 g_93 bds_93 75 (dagTraceF m_93 s_93 7 f_93) l_93) = true := by decide +kernel

theorem join_93_48 : ∀ j, 0 ≤ j → j < 64 → (dagCheckNodeF m_93 g_93 bds_93 75 (dagTraceF m_93 s_93 7 f_93) l_93) j = true := block_join join_93_32 (fun _ h₁ h₂ => treeBlockF_at block_93_48 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_93_64 : treeBlockF 64 75 (dagCheckNodeF m_93 g_93 bds_93 75 (dagTraceF m_93 s_93 7 f_93) l_93) = true := by decide +kernel

theorem join_93_64 : ∀ j, 0 ≤ j → j < 75 → (dagCheckNodeF m_93 g_93 bds_93 75 (dagTraceF m_93 s_93 7 f_93) l_93) j = true := block_join join_93_48 (fun _ h₁ h₂ => treeBlockF_at block_93_64 h₁ h₂)

theorem nc_93 : ∀ j, 0 ≤ j → j < 75 → (dagCheckNodeF m_93 g_93 bds_93 75 (dagTraceF m_93 s_93 7 f_93) l_93) j = true := join_93_64

theorem lb_93 : LowerBin m_93 s_93 g_93 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_93 sub_93 gl_93 rc_93 nc_93

def m_94 : Nat := 0xcc00cc00cc00cc

def s_94 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]

def g_94 : Nat := 0x400440004004c

def bds_94 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]

theorem kn_94 : KnownBin bds_94 := by
  intro b hb; simp only [bds_94, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3

theorem sub_94 : ∀ b ∈ bds_94, m_94 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_94, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_94 : ∀ b ∈ bds_94, canon b.1 g_94 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_94, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_94 : Nat → Nat × Nat := fun _ => (0, 0)

def l_94 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_94 : dagCheckRootsF m_94 g_94 bds_94 (dagRefF 0 (dagTraceF m_94 s_94 4 f_94) l_94 0) s_94 4 = true := by decide +kernel

theorem nc_94 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_94 g_94 bds_94 0 (dagTraceF m_94 s_94 4 f_94) l_94) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_94 : LowerBin m_94 s_94 g_94 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_94 sub_94 gl_94 rc_94 nc_94

def m_95 : Nat := 0xff0000

def s_95 : List Nat := [0x550000, 0x330000, 0xf0000]

def g_95 : Nat := 0x170000

def bds_95 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_95 : KnownBin bds_95 := by
  intro b hb; simp [bds_95] at hb

theorem sub_95 : ∀ b ∈ bds_95, m_95 &&& b.1 = b.1 := by
  intro b hb; simp [bds_95] at hb

theorem gl_95 : ∀ b ∈ bds_95, canon b.1 g_95 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_95] at hb

def f_95 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_95 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_95 : dagCheckRootsF m_95 g_95 bds_95 (dagRefF 1 (dagTraceF m_95 s_95 3 f_95) l_95 0) s_95 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_95_0 : treeBlockF 0 1 (dagCheckNodeF m_95 g_95 bds_95 1 (dagTraceF m_95 s_95 3 f_95) l_95) = true := by decide +kernel

theorem join_95_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_95 g_95 bds_95 1 (dagTraceF m_95 s_95 3 f_95) l_95) j = true := (fun _ h₁ h₂ => treeBlockF_at block_95_0 h₁ h₂)

theorem nc_95 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_95 g_95 bds_95 1 (dagTraceF m_95 s_95 3 f_95) l_95) j = true := join_95_0

theorem lb_95 : LowerBin m_95 s_95 g_95 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_95 sub_95 gl_95 rc_95 nc_95

def m_96 : Nat := 0xff00ff

def s_96 : List Nat := [0x550055, 0x330033, 0xf000f, 0xff]

def g_96 : Nat := 0x17005f

def bds_96 : List (Nat × List Nat × Nat × Nat) := [(m_95, s_95, 4, g_95)]

theorem kn_96 : KnownBin bds_96 := by
  intro b hb; simp only [bds_96, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_95

theorem sub_96 : ∀ b ∈ bds_96, m_96 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_96, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_96 : ∀ b ∈ bds_96, canon b.1 g_96 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_96, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_96 : Nat → Nat × Nat := fun _ => (0, 0)

def l_96 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_96 : dagCheckRootsF m_96 g_96 bds_96 (dagRefF 0 (dagTraceF m_96 s_96 4 f_96) l_96 0) s_96 4 = true := by decide +kernel

theorem nc_96 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_96 g_96 bds_96 0 (dagTraceF m_96 s_96 4 f_96) l_96) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_96 : LowerBin m_96 s_96 g_96 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_96 sub_96 gl_96 rc_96 nc_96

def m_97 : Nat := 0xf00000000f0000

def s_97 : List Nat := [0x50000000050000, 0x30000000030000, 0xf0000]

def g_97 : Nat := 0x10000000070000

def bds_97 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_97 : KnownBin bds_97 := by
  intro b hb; simp [bds_97] at hb

theorem sub_97 : ∀ b ∈ bds_97, m_97 &&& b.1 = b.1 := by
  intro b hb; simp [bds_97] at hb

theorem gl_97 : ∀ b ∈ bds_97, canon b.1 g_97 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_97] at hb

def f_97 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_97 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_97 : dagCheckRootsF m_97 g_97 bds_97 (dagRefF 1 (dagTraceF m_97 s_97 3 f_97) l_97 0) s_97 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_97_0 : treeBlockF 0 1 (dagCheckNodeF m_97 g_97 bds_97 1 (dagTraceF m_97 s_97 3 f_97) l_97) = true := by decide +kernel

theorem join_97_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_97 g_97 bds_97 1 (dagTraceF m_97 s_97 3 f_97) l_97) j = true := (fun _ h₁ h₂ => treeBlockF_at block_97_0 h₁ h₂)

theorem nc_97 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_97 g_97 bds_97 1 (dagTraceF m_97 s_97 3 f_97) l_97) j = true := join_97_0

theorem lb_97 : LowerBin m_97 s_97 g_97 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_97 sub_97 gl_97 rc_97 nc_97

def m_98 : Nat := 0xf000f0000f000f

def s_98 : List Nat := [0x50005000050005, 0x30003000030003, 0xf000f, 0xf00000000f]

def g_98 : Nat := 0x1000500007000f

def bds_98 : List (Nat × List Nat × Nat × Nat) := [(m_97, s_97, 4, g_97)]

theorem kn_98 : KnownBin bds_98 := by
  intro b hb; simp only [bds_98, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_97

theorem sub_98 : ∀ b ∈ bds_98, m_98 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_98, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_98 : ∀ b ∈ bds_98, canon b.1 g_98 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_98, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_98 : Nat → Nat × Nat := fun _ => (0, 0)

def l_98 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_98 : dagCheckRootsF m_98 g_98 bds_98 (dagRefF 0 (dagTraceF m_98 s_98 4 f_98) l_98 0) s_98 4 = true := by decide +kernel

theorem nc_98 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_98 g_98 bds_98 0 (dagTraceF m_98 s_98 4 f_98) l_98) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_98 : LowerBin m_98 s_98 g_98 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_98 sub_98 gl_98 rc_98 nc_98

def m_99 : Nat := 0x55000000aa0000

def s_99 : List Nat := [0xaa0000, 0x11000000220000, 0x50000000a0000]

def g_99 : Nat := 0x15000000020000

def bds_99 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_99 : KnownBin bds_99 := by
  intro b hb; simp [bds_99] at hb

theorem sub_99 : ∀ b ∈ bds_99, m_99 &&& b.1 = b.1 := by
  intro b hb; simp [bds_99] at hb

theorem gl_99 : ∀ b ∈ bds_99, canon b.1 g_99 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_99] at hb

def f_99 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_99 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_99 : dagCheckRootsF m_99 g_99 bds_99 (dagRefF 1 (dagTraceF m_99 s_99 3 f_99) l_99 0) s_99 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_99_0 : treeBlockF 0 1 (dagCheckNodeF m_99 g_99 bds_99 1 (dagTraceF m_99 s_99 3 f_99) l_99) = true := by decide +kernel

theorem join_99_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_99 g_99 bds_99 1 (dagTraceF m_99 s_99 3 f_99) l_99) j = true := (fun _ h₁ h₂ => treeBlockF_at block_99_0 h₁ h₂)

theorem nc_99 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_99 g_99 bds_99 1 (dagTraceF m_99 s_99 3 f_99) l_99) j = true := join_99_0

theorem lb_99 : LowerBin m_99 s_99 g_99 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_99 sub_99 gl_99 rc_99 nc_99

def m_100 : Nat := 0x55005500aa00aa

def s_100 : List Nat := [0xaa00aa, 0x11001100220022, 0x50005000a000a, 0x55000000aa]

def g_100 : Nat := 0x1500550002000a

def bds_100 : List (Nat × List Nat × Nat × Nat) := [(m_99, s_99, 4, g_99)]

theorem kn_100 : KnownBin bds_100 := by
  intro b hb; simp only [bds_100, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_99

theorem sub_100 : ∀ b ∈ bds_100, m_100 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_100, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_100 : ∀ b ∈ bds_100, canon b.1 g_100 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_100, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_100 : Nat → Nat × Nat := fun _ => (0, 0)

def l_100 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_100 : dagCheckRootsF m_100 g_100 bds_100 (dagRefF 0 (dagTraceF m_100 s_100 4 f_100) l_100 0) s_100 4 = true := by decide +kernel

theorem nc_100 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_100 g_100 bds_100 0 (dagTraceF m_100 s_100 4 f_100) l_100) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_100 : LowerBin m_100 s_100 g_100 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_100 sub_100 gl_100 rc_100 nc_100

def m_101 : Nat := 0xf0000f00000000

def s_101 : List Nat := [0x50000500000000, 0x30000300000000, 0xf00000000]

def g_101 : Nat := 0x10000700000000

def bds_101 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_101 : KnownBin bds_101 := by
  intro b hb; simp [bds_101] at hb

theorem sub_101 : ∀ b ∈ bds_101, m_101 &&& b.1 = b.1 := by
  intro b hb; simp [bds_101] at hb

theorem gl_101 : ∀ b ∈ bds_101, canon b.1 g_101 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_101] at hb

def f_101 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_101 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_101 : dagCheckRootsF m_101 g_101 bds_101 (dagRefF 1 (dagTraceF m_101 s_101 3 f_101) l_101 0) s_101 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_101_0 : treeBlockF 0 1 (dagCheckNodeF m_101 g_101 bds_101 1 (dagTraceF m_101 s_101 3 f_101) l_101) = true := by decide +kernel

theorem join_101_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_101 g_101 bds_101 1 (dagTraceF m_101 s_101 3 f_101) l_101) j = true := (fun _ h₁ h₂ => treeBlockF_at block_101_0 h₁ h₂)

theorem nc_101 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_101 g_101 bds_101 1 (dagTraceF m_101 s_101 3 f_101) l_101) j = true := join_101_0

theorem lb_101 : LowerBin m_101 s_101 g_101 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_101 sub_101 gl_101 rc_101 nc_101

def m_102 : Nat := 0xf0000f00f0000f

def s_102 : List Nat := [0x50000500500005, 0x30000300300003, 0xf0000000f, 0xf0000f]

def g_102 : Nat := 0x1000070010000f

def bds_102 : List (Nat × List Nat × Nat × Nat) := [(m_101, s_101, 4, g_101)]

theorem kn_102 : KnownBin bds_102 := by
  intro b hb; simp only [bds_102, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_101

theorem sub_102 : ∀ b ∈ bds_102, m_102 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_102, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_102 : ∀ b ∈ bds_102, canon b.1 g_102 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_102, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_102 : Nat → Nat × Nat := fun _ => (0, 0)

def l_102 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_102 : dagCheckRootsF m_102 g_102 bds_102 (dagRefF 0 (dagTraceF m_102 s_102 4 f_102) l_102 0) s_102 4 = true := by decide +kernel

theorem nc_102 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_102 g_102 bds_102 0 (dagTraceF m_102 s_102 4 f_102) l_102) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_102 : LowerBin m_102 s_102 g_102 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_102 sub_102 gl_102 rc_102 nc_102

def m_103 : Nat := 0x5500aa00000000

def s_103 : List Nat := [0xaa00000000, 0x11002200000000, 0x5000a00000000]

def g_103 : Nat := 0x15000200000000

def bds_103 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_103 : KnownBin bds_103 := by
  intro b hb; simp [bds_103] at hb

theorem sub_103 : ∀ b ∈ bds_103, m_103 &&& b.1 = b.1 := by
  intro b hb; simp [bds_103] at hb

theorem gl_103 : ∀ b ∈ bds_103, canon b.1 g_103 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_103] at hb

def f_103 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_103 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_103 : dagCheckRootsF m_103 g_103 bds_103 (dagRefF 1 (dagTraceF m_103 s_103 3 f_103) l_103 0) s_103 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_103_0 : treeBlockF 0 1 (dagCheckNodeF m_103 g_103 bds_103 1 (dagTraceF m_103 s_103 3 f_103) l_103) = true := by decide +kernel

theorem join_103_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_103 g_103 bds_103 1 (dagTraceF m_103 s_103 3 f_103) l_103) j = true := (fun _ h₁ h₂ => treeBlockF_at block_103_0 h₁ h₂)

theorem nc_103 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_103 g_103 bds_103 1 (dagTraceF m_103 s_103 3 f_103) l_103) j = true := join_103_0

theorem lb_103 : LowerBin m_103 s_103 g_103 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_103 sub_103 gl_103 rc_103 nc_103

def m_104 : Nat := 0x5500aa005500aa

def s_104 : List Nat := [0xaa000000aa, 0x11002200110022, 0x5000a0005000a, 0x5500aa]

def g_104 : Nat := 0x1500020015000a

def bds_104 : List (Nat × List Nat × Nat × Nat) := [(m_103, s_103, 4, g_103)]

theorem kn_104 : KnownBin bds_104 := by
  intro b hb; simp only [bds_104, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_103

theorem sub_104 : ∀ b ∈ bds_104, m_104 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_104, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_104 : ∀ b ∈ bds_104, canon b.1 g_104 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_104, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_104 : Nat → Nat × Nat := fun _ => (0, 0)

def l_104 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_104 : dagCheckRootsF m_104 g_104 bds_104 (dagRefF 0 (dagTraceF m_104 s_104 4 f_104) l_104 0) s_104 4 = true := by decide +kernel

theorem nc_104 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_104 g_104 bds_104 0 (dagTraceF m_104 s_104 4 f_104) l_104) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_104 : LowerBin m_104 s_104 g_104 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_104 sub_104 gl_104 rc_104 nc_104

def m_105 : Nat := 0xff0000000000ff

def s_105 : List Nat := [0x55000000000055, 0x33000000000033, 0xf00000000000f, 0xff]

def g_105 : Nat := 0x1700000000005f

def bds_105 : List (Nat × List Nat × Nat × Nat) := [(m_68, s_68, 4, g_68)]

theorem kn_105 : KnownBin bds_105 := by
  intro b hb; simp only [bds_105, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_68

theorem sub_105 : ∀ b ∈ bds_105, m_105 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_105, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_105 : ∀ b ∈ bds_105, canon b.1 g_105 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_105, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_105 : Nat → Nat × Nat := fun _ => (0, 0)

def l_105 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_105 : dagCheckRootsF m_105 g_105 bds_105 (dagRefF 0 (dagTraceF m_105 s_105 4 f_105) l_105 0) s_105 4 = true := by decide +kernel

theorem nc_105 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_105 g_105 bds_105 0 (dagTraceF m_105 s_105 4 f_105) l_105) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_105 : LowerBin m_105 s_105 g_105 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_105 sub_105 gl_105 rc_105 nc_105

def m_106 : Nat := 0x33000000cc0000

def s_106 : List Nat := [0x11000000440000, 0xcc0000, 0x30000000c0000]

def g_106 : Nat := 0x13000000040000

def bds_106 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_106 : KnownBin bds_106 := by
  intro b hb; simp [bds_106] at hb

theorem sub_106 : ∀ b ∈ bds_106, m_106 &&& b.1 = b.1 := by
  intro b hb; simp [bds_106] at hb

theorem gl_106 : ∀ b ∈ bds_106, canon b.1 g_106 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_106] at hb

def f_106 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_106 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_106 : dagCheckRootsF m_106 g_106 bds_106 (dagRefF 1 (dagTraceF m_106 s_106 3 f_106) l_106 0) s_106 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_106_0 : treeBlockF 0 1 (dagCheckNodeF m_106 g_106 bds_106 1 (dagTraceF m_106 s_106 3 f_106) l_106) = true := by decide +kernel

theorem join_106_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_106 g_106 bds_106 1 (dagTraceF m_106 s_106 3 f_106) l_106) j = true := (fun _ h₁ h₂ => treeBlockF_at block_106_0 h₁ h₂)

theorem nc_106 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_106 g_106 bds_106 1 (dagTraceF m_106 s_106 3 f_106) l_106) j = true := join_106_0

theorem lb_106 : LowerBin m_106 s_106 g_106 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_106 sub_106 gl_106 rc_106 nc_106

def m_107 : Nat := 0x33003300cc00cc

def s_107 : List Nat := [0x11001100440044, 0xcc00cc, 0x30003000c000c, 0x33000000cc]

def g_107 : Nat := 0x1300130004004c

def bds_107 : List (Nat × List Nat × Nat × Nat) := [(m_106, s_106, 4, g_106)]

theorem kn_107 : KnownBin bds_107 := by
  intro b hb; simp only [bds_107, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_106

theorem sub_107 : ∀ b ∈ bds_107, m_107 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_107, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_107 : ∀ b ∈ bds_107, canon b.1 g_107 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_107, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_107 : Nat → Nat × Nat := fun _ => (0, 0)

def l_107 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_107 : dagCheckRootsF m_107 g_107 bds_107 (dagRefF 0 (dagTraceF m_107 s_107 4 f_107) l_107 0) s_107 4 = true := by decide +kernel

theorem nc_107 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_107 g_107 bds_107 0 (dagTraceF m_107 s_107 4 f_107) l_107) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_107 : LowerBin m_107 s_107 g_107 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_107 sub_107 gl_107 rc_107 nc_107

def m_108 : Nat := 0xff00ff00ff00ff

def s_108 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]

def g_108 : Nat := 0x1700570017005f

def bds_108 : List (Nat × List Nat × Nat × Nat) := [(m_94, s_94, 5, g_94), (m_96, s_96, 5, g_96), (m_98, s_98, 5, g_98), (m_100, s_100, 5, g_100), (m_77, s_77, 5, g_77), (m_102, s_102, 5, g_102), (m_104, s_104, 5, g_104), (m_68, s_68, 4, g_68), (m_105, s_105, 5, g_105), (m_107, s_107, 5, g_107)]

theorem kn_108 : KnownBin bds_108 := by
  intro b hb; simp only [bds_108, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_94
  · exact lb_96
  · exact lb_98
  · exact lb_100
  · exact lb_77
  · exact lb_102
  · exact lb_104
  · exact lb_68
  · exact lb_105
  · exact lb_107

theorem sub_108 : ∀ b ∈ bds_108, m_108 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_108, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem gl_108 : ∀ b ∈ bds_108, canon b.1 g_108 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_108, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def f_108 : Nat → Nat × Nat := unpackForestF 0xf5ca4464f64b64764301f 2 10

def l_108 : Nat → Nat → Option Nat := unpackLinksF 0xe38e38c69301 0x6d72c8924f725a91cc8601f 6 3 10 3 4

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_108 : dagCheckRootsF m_108 g_108 bds_108 (dagRefF 7 (dagTraceF m_108 s_108 6 f_108) l_108 0) s_108 6 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_108_0 : treeBlockF 0 7 (dagCheckNodeF m_108 g_108 bds_108 7 (dagTraceF m_108 s_108 6 f_108) l_108) = true := by decide +kernel

theorem join_108_0 : ∀ j, 0 ≤ j → j < 7 → (dagCheckNodeF m_108 g_108 bds_108 7 (dagTraceF m_108 s_108 6 f_108) l_108) j = true := (fun _ h₁ h₂ => treeBlockF_at block_108_0 h₁ h₂)

theorem nc_108 : ∀ j, 0 ≤ j → j < 7 → (dagCheckNodeF m_108 g_108 bds_108 7 (dagTraceF m_108 s_108 6 f_108) l_108) j = true := join_108_0

theorem lb_108 : LowerBin m_108 s_108 g_108 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_108 sub_108 gl_108 rc_108 nc_108

def m_109 : Nat := 0x5050505050505050

def s_109 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]

def g_109 : Nat := 0x10105010101050

def bds_109 : List (Nat × List Nat × Nat × Nat) := [(m_70, s_70, 4, g_70)]

theorem kn_109 : KnownBin bds_109 := by
  intro b hb; simp only [bds_109, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_70

theorem sub_109 : ∀ b ∈ bds_109, m_109 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_109, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_109 : ∀ b ∈ bds_109, canon b.1 g_109 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_109, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_109 : Nat → Nat × Nat := fun _ => (0, 0)

def l_109 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_109 : dagCheckRootsF m_109 g_109 bds_109 (dagRefF 0 (dagTraceF m_109 s_109 4 f_109) l_109 0) s_109 4 = true := by decide +kernel

theorem nc_109 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_109 g_109 bds_109 0 (dagTraceF m_109 s_109 4 f_109) l_109) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_109 : LowerBin m_109 s_109 g_109 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_109 sub_109 gl_109 rc_109 nc_109

def m_110 : Nat := 0xf0f0000

def s_110 : List Nat := [0x5050000, 0x3030000, 0xf0000]

def g_110 : Nat := 0x1070000

def bds_110 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_110 : KnownBin bds_110 := by
  intro b hb; simp [bds_110] at hb

theorem sub_110 : ∀ b ∈ bds_110, m_110 &&& b.1 = b.1 := by
  intro b hb; simp [bds_110] at hb

theorem gl_110 : ∀ b ∈ bds_110, canon b.1 g_110 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_110] at hb

def f_110 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_110 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_110 : dagCheckRootsF m_110 g_110 bds_110 (dagRefF 1 (dagTraceF m_110 s_110 3 f_110) l_110 0) s_110 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_110_0 : treeBlockF 0 1 (dagCheckNodeF m_110 g_110 bds_110 1 (dagTraceF m_110 s_110 3 f_110) l_110) = true := by decide +kernel

theorem join_110_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_110 g_110 bds_110 1 (dagTraceF m_110 s_110 3 f_110) l_110) j = true := (fun _ h₁ h₂ => treeBlockF_at block_110_0 h₁ h₂)

theorem nc_110 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_110 g_110 bds_110 1 (dagTraceF m_110 s_110 3 f_110) l_110) j = true := join_110_0

theorem lb_110 : LowerBin m_110 s_110 g_110 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_110 sub_110 gl_110 rc_110 nc_110

def m_111 : Nat := 0xa0a0a0a

def s_111 : List Nat := [0x2020202, 0xa000a, 0xa0a]

def g_111 : Nat := 0x2020a

def bds_111 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_111 : KnownBin bds_111 := by
  intro b hb; simp [bds_111] at hb

theorem sub_111 : ∀ b ∈ bds_111, m_111 &&& b.1 = b.1 := by
  intro b hb; simp [bds_111] at hb

theorem gl_111 : ∀ b ∈ bds_111, canon b.1 g_111 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_111] at hb

def f_111 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_111 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_111 : dagCheckRootsF m_111 g_111 bds_111 (dagRefF 1 (dagTraceF m_111 s_111 3 f_111) l_111 0) s_111 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_111_0 : treeBlockF 0 1 (dagCheckNodeF m_111 g_111 bds_111 1 (dagTraceF m_111 s_111 3 f_111) l_111) = true := by decide +kernel

theorem join_111_0 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_111 g_111 bds_111 1 (dagTraceF m_111 s_111 3 f_111) l_111) j = true := (fun _ h₁ h₂ => treeBlockF_at block_111_0 h₁ h₂)

theorem nc_111 : ∀ j, 0 ≤ j → j < 1 → (dagCheckNodeF m_111 g_111 bds_111 1 (dagTraceF m_111 s_111 3 f_111) l_111) j = true := join_111_0

theorem lb_111 : LowerBin m_111 s_111 g_111 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_111 sub_111 gl_111 rc_111 nc_111

def m_112 : Nat := 0xf0f0f0f

def s_112 : List Nat := [0x5050505, 0x3030303, 0xf000f, 0xf0f]

def g_112 : Nat := 0x107070f

def bds_112 : List (Nat × List Nat × Nat × Nat) := [(m_110, s_110, 4, g_110), (m_19, s_19, 4, g_19), (m_2, s_2, 4, g_2), (m_111, s_111, 4, g_111)]

theorem kn_112 : KnownBin bds_112 := by
  intro b hb; simp only [bds_112, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_110
  · exact lb_19
  · exact lb_2
  · exact lb_111

theorem sub_112 : ∀ b ∈ bds_112, m_112 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_112, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

theorem gl_112 : ∀ b ∈ bds_112, canon b.1 g_112 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_112, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

def f_112 : Nat → Nat × Nat := unpackForestF 0x1d13369a514c8268e9319a4243440487534e269a4d346a6134ba517462c8c5518a1e924d246a453489a8f4a1e8c391869e8d25188c29285230a3a146c251849b0846106c18dc29b8527086e109c20b800f 5 10

def l_112 : Nat → Nat → Option Nat := unpackLinksF 0x8e11c2384708e11c2384708e11c2384618c118228c418630c218421841046084017e2fc1f0bd17a0f05e03b1742e45c0b715f09e0fc1781f01e00b001 0xa524a84ca534a5349c249014a14c9c348c149d349a4c974890348c2490348c24894d71457d356d25844d4c455c354825824d72457e356926784d344554352815774a73466e466946643d2c3540252415624d4e455e35594d354555353c262016534a4f464a46453d2d3541253c461c163a4a3646323a2e362946253620461c361a37153711270c3708270417000f 11 4 10 6 5

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_112 : dagCheckRootsF m_112 g_112 bds_112 (dagRefF 43 (dagTraceF m_112 s_112 6 f_112) l_112 0) s_112 6 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_112_0 : treeBlockF 0 16 (dagCheckNodeF m_112 g_112 bds_112 43 (dagTraceF m_112 s_112 6 f_112) l_112) = true := by decide +kernel

theorem join_112_0 : ∀ j, 0 ≤ j → j < 16 → (dagCheckNodeF m_112 g_112 bds_112 43 (dagTraceF m_112 s_112 6 f_112) l_112) j = true := (fun _ h₁ h₂ => treeBlockF_at block_112_0 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_112_16 : treeBlockF 16 32 (dagCheckNodeF m_112 g_112 bds_112 43 (dagTraceF m_112 s_112 6 f_112) l_112) = true := by decide +kernel

theorem join_112_16 : ∀ j, 0 ≤ j → j < 32 → (dagCheckNodeF m_112 g_112 bds_112 43 (dagTraceF m_112 s_112 6 f_112) l_112) j = true := block_join join_112_0 (fun _ h₁ h₂ => treeBlockF_at block_112_16 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_112_32 : treeBlockF 32 43 (dagCheckNodeF m_112 g_112 bds_112 43 (dagTraceF m_112 s_112 6 f_112) l_112) = true := by decide +kernel

theorem join_112_32 : ∀ j, 0 ≤ j → j < 43 → (dagCheckNodeF m_112 g_112 bds_112 43 (dagTraceF m_112 s_112 6 f_112) l_112) j = true := block_join join_112_16 (fun _ h₁ h₂ => treeBlockF_at block_112_32 h₁ h₂)

theorem nc_112 : ∀ j, 0 ≤ j → j < 43 → (dagCheckNodeF m_112 g_112 bds_112 43 (dagTraceF m_112 s_112 6 f_112) l_112) j = true := join_112_32

theorem lb_112 : LowerBin m_112 s_112 g_112 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_112 sub_112 gl_112 rc_112 nc_112

def m_113 : Nat := 0x5555000055550000

def s_113 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]

def g_113 : Nat := 0x115000011150000

def bds_113 : List (Nat × List Nat × Nat × Nat) := [(m_65, s_65, 4, g_65)]

theorem kn_113 : KnownBin bds_113 := by
  intro b hb; simp only [bds_113, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_65

theorem sub_113 : ∀ b ∈ bds_113, m_113 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_113, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_113 : ∀ b ∈ bds_113, canon b.1 g_113 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_113, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_113 : Nat → Nat × Nat := fun _ => (0, 0)

def l_113 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_113 : dagCheckRootsF m_113 g_113 bds_113 (dagRefF 0 (dagTraceF m_113 s_113 4 f_113) l_113 0) s_113 4 = true := by decide +kernel

theorem nc_113 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_113 g_113 bds_113 0 (dagTraceF m_113 s_113 4 f_113) l_113) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_113 : LowerBin m_113 s_113 g_113 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_113 sub_113 gl_113 rc_113 nc_113

def m_114 : Nat := 0xc0c0c0c0c0c0c0c

def s_114 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]

def g_114 : Nat := 0x404040004040c

def bds_114 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]

theorem kn_114 : KnownBin bds_114 := by
  intro b hb; simp only [bds_114, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2

theorem sub_114 : ∀ b ∈ bds_114, m_114 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_114, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_114 : ∀ b ∈ bds_114, canon b.1 g_114 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_114, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_114 : Nat → Nat × Nat := fun _ => (0, 0)

def l_114 : Nat → Nat → Option Nat := fun _ _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_114 : dagCheckRootsF m_114 g_114 bds_114 (dagRefF 0 (dagTraceF m_114 s_114 4 f_114) l_114 0) s_114 4 = true := by decide +kernel

theorem nc_114 : ∀ j, 0 ≤ j → j < 0 → (dagCheckNodeF m_114 g_114 bds_114 0 (dagTraceF m_114 s_114 4 f_114) l_114) j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_114 : LowerBin m_114 s_114 g_114 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_114 sub_114 gl_114 rc_114 nc_114

def g_115 : Nat := 0x11715571117175f

def bds_115 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_5, s_5, 7, g_5), (m_32, s_32, 8, g_32), (m_64, s_64, 8, g_64), (m_81, s_81, 9, g_81), (m_93, s_93, 8, g_93), (m_108, s_108, 7, g_108), (m_109, s_109, 5, g_109), (m_69, s_69, 7, g_69), (m_112, s_112, 7, g_112), (m_72, s_72, 7, g_72), (m_9, s_9, 4, g_9), (m_68, s_68, 4, g_68), (m_12, s_12, 6, g_12), (m_113, s_113, 5, g_113), (m_94, s_94, 5, g_94), (m_28, s_28, 5, g_28), (m_67, s_67, 4, g_67), (m_114, s_114, 5, g_114)]

theorem kn_115 : KnownBin bds_115 := by
  intro b hb; simp only [bds_115, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_0
  · exact lb_5
  · exact lb_32
  · exact lb_64
  · exact lb_81
  · exact lb_93
  · exact lb_108
  · exact lb_109
  · exact lb_69
  · exact lb_112
  · exact lb_72
  · exact lb_9
  · exact lb_68
  · exact lb_12
  · exact lb_113
  · exact lb_94
  · exact lb_28
  · exact lb_67
  · exact lb_114

theorem sub_115 : ∀ b ∈ bds_115, fullMask &&& b.1 = b.1 := by
  intro b hb; simp only [bds_115, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem gl_115 : ∀ b ∈ bds_115, canon b.1 g_115 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_115, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def f_115 : Nat → Nat × Nat := unpackForestF 0xe78d339c36ce608f39724ce568f394a6ce40d738ba4ce2e4a38ab6ce1cd7379b50de2db36e92fdba49f6892fda249f59a4cd5e5335614cd5213754841d5053750b60d40d834fa60d36d834d24cd344a34d025d2e9434b150d2ad834a360d2898347135d148f34424cd0e50743835cd4d833245ccc515330a49cc29072f46ccb91932c94fcb251f2c12fcb04af2c127cb048f2ab4cca6d1322b5cc86d5321a7cc30d330b344c10df303374c0c97302b48bfcd22fa036be24d6f0354bc0952ecc6cbaf192ea364ba8d52e8a44b9e10ae6b5cb96db2e5b5cb968e2e586cb931f2e3c74b8ed72e283ab88912e2024b625b2d6c6cb57192d506cb48d32c247cb04d72b9136ae2936b8a35ace4e2b3934ab8d72acc64ab0d52ab354aa8d52a9b44aa6522a9944aa2d32a7b68a9a952a623ea988f2a5234a92d7aa435ea908d29f255a7a9b69e466a76d329c954a705b29c14ca6e4d29b13ca6a8e69a134a66d7a99144a62d5a98a39a624d295a38a568d295934a4a97292a54a4a4929123ca444969015da3e8f28f134a345528d13ca340628d014a324968b93da2c1528b03ca2c0b28b026a2c09289a59a0ed2275c6e9d719a7536e9d4d9a743459d04ee7314b9cc50e6f13c9b64ee6d9339a51d2694649a2dd268b649a0d92683549a04d661b54984d126125c98491260b44982912609459808d2601349800e660035970db25b94f96e50e5914f96450e5904e96410a5835c95d1f25746c95cd2256c7095adf256b6c95a8e256a34958db25635c9588e2561359581b255b609569b2559289564925582995609651a4493e5924f1249384ee4e1379380ea4db54934d724d25c9349124ca449325164c824920d3a47a6c91e5b245a6c916582401748f04ee3c1338ead5638b5e8e2d5a3714b8dc50e2957c8a41522783489b5c22685c8931fa2334488c91222d7e880db21fc7e8769121d57e86b5d20c95b83255e0746c816dc2045688101720234f808d2e02347808d0e0204e8051b1ffb5f7fed6dffb577fed4dff1607f4581fa85c7e80f1f78547dc8fdf723b7dc8ddf72337da0b1f43547cd1bdf34637c71f1f11447c2dbdf0b637c0151ef3547b91bdee4637b893dee24b7b891dee2437b60b1ec02c7ac97deb2537a31f9e857e79f1f9e757e796da1e5864792111e3b6078e1b1e246f78918ddea59766d6dd9b53760d55d83547575c1d536c748991d1d6b74759dd09447344d1cd03472e511ca144722511bdb606ead2dbab436e8db1b76806dd9c1b41446c64d1b0a396c28d5b023f6c08edb02376c08cdad9466b6511ac24f6b090dab1446a84d1a91646a0511a6954698591a546b69518da526f6949ada526769498d9fc5e67cdc19eb4a67ad219ea4a6749399cc6b67318d91b79642d1190a446411e58eb7c638de58ca446311e58b46862b1c18935c61a5b1861246104f182b4760a5198045f60115d801465f85197bb505d31417423f5d08dd724505c6d5570a555c09b56fe795bf1b96f6795bcd996eb5e5bad596ea395b4d7d6d35b5b4d5d6d3535aed956bb555ae0e96b3465ac9196b04a5a8db56a36c5a8d756a23a5a88d96a03a5a6dbd69b6b5a6d9d69b635a4919692445a41295f3545771f15bb5455ede55747955ade556479556dc14d13c528d914835b520d4d462465185194614450e5114017c4fedb93fb664fcdb93f3664fad7d3eb5b4fad5d3eb534f8d993e1344f80d13d1644ec511399544dc5513646b4d918d34d704d25f13436c4d04d12e34a4b8d212e14a4b693d2da4349895524a4448a97922a56486559218224821111d3704745f11cb484725111ab4b46ad0d199444560d11496444c5511246b44918d1236f448dad12367448d8d0b95f42e55d09c6442295508a5441a53d069474175c104a6d4129b10426f41098cfa4703ccd04f2a373ca4ecf29373c4d04f0b583c2954f03483c0914efc6f3bcd7cef3573bc8ececb5b3b2d5cec95b3b255cea2653a6954e92553a31b0e8b5c3a28d4e826d39f190e7b5c39e8e0e7a3539e8d0e793839e4d0e746639b1b8e6c6239ad30e636a398d98e5d6f39718ce546e394d10e526c394990e5128394490e4c6e393198e4a49392914e4a353911b8e4466390d24e424c38edb8e3b6638e934e3a3938e8d4e346e38d198e334938c910e316c38c590e313c38c4d8e313438ad7ce2b5e38ad68e2b5738ad58e2b5238a8f4e2a3b38a8e4e2a3738a8d4e2a3138a4f4e2935388968e2257388958e212d3884ace212938849ce2125388484e202d3880a4e2025388084e125b38495ce105a383188dfa3537c8d4deb6937ad84de46b37918cdda4736ada4dab613691acda463368d88d9854362d24d703435b5a4d6d653591b8d6462357154d587c355190d4b66352d90d4568350170d3b7c34ed90d356934d594d2c5934b154d286c346950d1344344910d035f340d5cd013b3404dccfc7c33edc0cf37c33b5c0ce85c3391c0ce37c338db0cdb54334d90ccb44332110cc354330950cba4432b1b8cac62326d64c8b4e3205f0c817031ed94c7b5531e4ecc793731e0e8c736e31a990c645e318910c5b7c3169f0c597c3165c0c5346314d10c5246314910c514b31451cc504a314118c4b59310db8c436230ed24c356830b9c0c2b6c30ad38c25703085f0c21703079c0c1b6d306db0c1b5d3068e8c1a363064ecc19373060e8c18363051b8c1462304db8c13623044ecc1137300990bfc5e2fe910bf37c2fc9f0bf17c2fc5c0bea462fa910be94b2fa51cbe84a2f8db4be3652f8d64bdc6a2f7198bdb6e2f6d88bd35f2f4d6cbd3572f4d4cbcb5f2f2d6cbcb572f2d4cbbb642ecd50bab7c2e9160ba3542dcda4b73612d75f8b42362cf9fcb397e2ca950b23542c8950b1c5b2c31a0b04582bf1c0af4582bcd60aed692bb584aeb5f2bad5cae83a2b8d50ae2542b6950ad3442b2d10ac3442af16caba562acda4ab3612acd64aab6e2a8954aa0542a6914a92552a28d4a88342a11b8a846229f190a7a4529cd90a723529b5a0a6a5d29a170a63642988d4a502429317ca4b61292d7ca4b53292d2ca4b47292948a437f290dcca4369290d24a3c7f28f1cca3c6928e990a3a4e28d5a0a337f28cdcca336928cd44a305c28b1fca2c7328b1a4a2a6428a938a2824288d90a235f288d5ca1a64286090a1468282990a0a4e2805509f94427d9c09f16c27c1b09e9442764d09d6702745b09d06c2724d09c8342705109b93426e0d09b15c26a4d09a25f26896c9a25726894c9a03626716c99b4226690898c7c262dc098a45260df09823525f5c097a5d25e1709747025cdf09723525ad6496b4b25ad1c963712571c495a7c2555c09537125417094c71252df094a7c2520909437c24f1c093a7c24e0909347024b1c092b7c24a9f0918642401108f95423c5108ee7023a5b08e86c2385108d0342331fc8cc732331648c57f2315cc8c35e2304d08be7022f1fc8bc7322f1848b96c22e1b08b57f22d5cc8b35e22c4d08b03422a5108a1342280d08995c2244d088c6e22318888c5a22315888a5f22296c88a5722294c88a4d2229148856f2211bc8846322116c88457220d08882622209688824a21e97c87a5321cd648725b21c95c8705a21b190863542171f085a7c2169c085354212db884b6221119083a5420e9388347c20cdc482a542095888236f208dac82367208d8c823512075f881b5420495080c582015f8802541fe5907f45e1fc5107eb7c1fa5f07e2461f85187e1441f81187dc691f65907d4711f45f07cd7b1f35cc7cc7e1f25107c5721f05707bb591ee8fc7b36e1ecd887b26f1eb1bc7ac6b1eb19c7ac631e8d247a2471e75a079a651e59c07936c1e35c078a7d1e29f0786701e0db0782351df1b877c621dedb877b621dd5a076d701dadc47636f1d8dac763671d8d8c75e721d6ddc75b6c1d51807495f1d255c741641cf178739441ccdf0733701cc5f072b4b1cad1c729461ca510724691c859071b5e1c64d0714711c45f070b5e1c24d07057b1c15cc7047e1c0dc8701441bedf86f9341bd5c86f15c1bb5ec6ed731bb1f86eb7e1ba4d06e3591b88fc6e2331b71a86dc661b6db86db621b69bc6da631b51bc6d46b1b519c6d4631b4d886d3421b49a86d2421b2d906ca651b0d506c2551aedf06ba7d1ad1606b3541ac9546a2351a68d4692351a2da468b611a0d9067a4419cdf066a5c19a9106647b1991cc6637e1975ec65d731971f865a441951ec65473194df86536c1935ec64d731931f864a4418d5bc6356718d1886336b18cd8c6335b18c8c862a5f18a96c62a5718a94c6215f18856c6215718854c6196418455060c701825f06015417e5905f13417b1c05e97c1784d05d1341731805c96c1704d05ba4f16e92c5ba4716e90c5b56f16d59c5b36216c9885b25a16a97c5aa5b16a95c5aa531691a05a26516716059a551651c05927d16316058b58162954585691615845835f160d5c5823b1608dc5803a15f1a05725c15b1c05625c15893055c721555c85525c1531c854c601515c85425c14f5bc53d6714edb853a6214e9485316414a550524701485f05195413c5904e9341391c04e17c1364d04d47b1351cc4cd7b1335cc4c9341311ec4c4731311804c16c12f5ec4bd7312e4d04a24f12892c4a24712890c49b69126d8449a4f12692c49a4712690c4956712516c493621249a84924212316448a54120d504825411e9904724411b5c046b7c11a9f04687c118d104624411811045b541169504524411316c44b59112d0c4436e110d884346910c5904306410b164429541091c44217c1071644195410459040c5e1025104057c1015c04017c1001f03fc6f0ff19c3fa460fe5183f9440fe1183f8440fd5f83f1540fb9c83ed7b0fb5cc3ec7e0fa5103e6720f85b03e06c0f79f83dd7b0f75cc3dc7e0f65103d36f0f4dac3d3670f4d8c3cb590f2d2c3cb430f15bc3c5630f0db83c3620eeda03b8640ed1643b3580eb1c43ab700e8d6039b680e4d2038d7c0e35c038b700e21f0383480e011037b580dcd2036b600da1b0363480d75a435d610d716c35c530d697c35a570d69383582a0d609c358260d51b8354620d5178354520d49b8352620d31bc34c6b0d319c34c630d1164341540cf164339540cc59032c5e0ca510325700c8df03217c0c81f0319460c6510318460c61103157e0c455030d7b0c35cc30c7e0c2510303590c0d0c2fd630bf1a82fc660bedb82fb620b29f02c3700ae96c2ba570ad1902aa540a958829c640a69142927e0a495028b720a2d602824709f5a827d6809b5a026a6509a97426372098d8025366094d9024a4409118823b6408e99423a3508c9f82324408adc822b5008ad202223b0888dc21c6808497020b6e082988204680809942024d07e9701f35007cd001e264074da01c9640704d01b362066d6419a550661501934906491418b610629b41834906091417c6f05f18c17a5505cd381723505b1b016c6005a9b416a6c05a9801696c05a5801686c0595bc16563058d7c1635b058d5c163530588fc1623b0588dc162350588cc1613f0584ec161370584cc1603a0580d8160340571b815a450555881546b05518c1536e0548d414d620529741485c0515b81446b05118c1436e0508d413c6f04f18c13c5b04f15c13b6f04ed8c13b5b04ed6413b5704ed3c13b4b04ed1c13b4304e56c1395704e15c1345f04d14c1324e04ad8412b4f04ad2c12b4704ad0c125630491bc1246304917c124530489b81224e04809011c6e046dbc11b6b046d9c11b63046d241146f0451ac1146704518c1126e04493810d62042dbc10b6b042d9c10b63042d441085c0411bc1046b04119c104630409b81024e0404a0101240400900fd6f03f5ac0fd6703f58c0fc6b03f18c0fc5b03f14c0fb6f03edb80fb6703ed880fb5f03ed5c0fa6e03e9880f93b03e4dc0f56b03d58c0f26e03c0900ed6f03b5ac0ed6703b58c0ec620395ac0e5630391ac0e46303914c0e36e0389b80e24e0371bc0dc63036dbc0db63036d640db4f036d2c0db47036d0c0da6f03698c0da5503693c0da4b03691c0da430368fc0da3b0368dc0da3303517c0d45b03515c0d453034d7c0d35b034d5c0d353034d3c0d34b034d1c0d3430345380d136032d840cb4f032d2c0cb47032d0c0ca6d03293c0ca4b03291c0ca430328fc0ca3b0328dc0ca330321b00c56f03158c0c46f03118c0c45f03116c0c45703114c0c36f030d8c0c35f030d6c0c357030d4c0c34f030d2c0c347030d0c0c14e0304d80c01402f1b80bb6f02edac0bb6702ed8c0bb4902e9bc0ba6b02e99c0ba6302e9140ba3f02e8ec0ba3702e8cc0b46f02d1ac0b46702d18c0b36f02cd9c0b34f02cd1c0b16e02c5380b13602b5880ab6f02adac0ab6702ad8c0ab5102a9bc0aa6702a9740aa3f02a8dc0a85c0291bc0a46b02919c0a463028dbc0a36b028d9c0a363028d3c0a34b028d1c0a3430285b80a14e0284d809d6f0275ac09d6702758c09c6b02718c09c5b02714c09b6e0269bc09a6b02699c09a6302697c09a5b02695c09a5302693c09a430268d4099620260d00956f0255ac0956702558c0936f024dac09367024d8c0935f024d6c09357024d4c0916e0244d8090140235bc08d6b02359c08d6302318808a6f0229ac08a6702298c08a5f02296c08a5702294c08a4d0215bc0856b02159c085630211ac0846302116c08453020dbc0836b020d9c08363020d7c0835b020d5c08353020d3c083430209b80816e0204d807d6b01f58c07c6f01f1ac07c6701f18c07c5f01f14c07a6e01e9380782401d5bc0756b01d59c0756301d1bc0746b01d19c0746301d17c0745b01d15c0745301c9580716e01c53806d6f01b5ac06d6701b58c06c6f01b1ac06c6701b18c06c5f01b16c06c5701b14c06b6201ad080695a0195ac065630191bc0646b01919c0646301917c064530185b80614e0164bc059270149b40516c0145800512f01449c04c6e0129bc04a630129140496f0124bc049270115880426f0109740416f01049c03b6e00e9bc03a6300e8d40396f00e4bc0392700d1880326f00c98c0324d00c5bc0312f00c49c02a6e00a5bc023620085bc01b6f006d8c0196e0064d80136f004d8c00c5f00316c00c5700314c00b5f002d6c00b57002d4c00b4f002d2c00b47002d0c00a5f00296c00a5700294c00a4f00292c00a4700290c00a3f0028ec00a370028cc0095f00256c0095700254c0094f00252c0094700250c0093f0024ec009370024cc0092f0024ac0092700248c0085f00215c0084f00211c0083f0020dc0082f00209c0081f00205c0003f 11 11

def l_115 : Nat → Nat → Option Nat := unpackLinksF 0x322c0c8b0322c0c8b0322c0c8b0322c0c8b0322c0c8b0322c0c8b0322c0c8b0322c0c8b0322c0c8b0322c0c8b0322c0c8b0322c0c8b0322c0c8b0322c0c8b0322c0c8b0322c0c8b0322c0c8b0322c0c8b0322c0c8b0322c0c8b0322c0c8a072241c89032240c880721c1c870321c0c870321c0c870321c0c86072141c840720c1c83032081c81072001c7f071fc0c7f031fc0c7f031fc0c7f031fc0c7e071f41c7d031f40c7d031f40c7d031f40c7c071ec1c790b1e01c77071dc0c77031dc0c77031dc0c76071d41c75031d40c75031d40c75031d40c75031d40c75031d40c75031d40c75031d40c75031d40c75031d40c75031d40c75031d40c75031d40c75031d40c74071d00c73071cc0c73031cc0c73031cc0c73031cc0c73031cc0c73031cc0c73031cc0c73031cc0c73031cc0c73031cc0c710b1c40c71031c40c71031c40c71031c40c71031c40c71031c40c6f0b1bc0c6f031bc0c6f031bc0c6f031bc0c6f031bc0c6f031bc0c6f031bc0c6f031bc0c6f031bc0c6f031bc0c6f031bc0c6f031bc0c6f031bc0c6d0b1b40c6d031b40c6c071b00c6c031b00c6b071ac0c6b031a81c680b19c1c650b1901c64031900c64031900c5f1717c0c5e071741c5c071700c5b071681c580b1543c51131440c500713c1c4e071302c4c031300c4c031300c4a0b1241c49031201c47071181c46031102c420b1080c42031080c42031080c42031080c42031080c42031080c42031080c42031080c42031080c42031080c42031080c42031080c42031080c42031080c42031041c41031040c41031040c40070f82c3d070ec2c390b0e40c38070dc1c36070d41c35030d40c330b0bc4c2f030b81c2d070b01c2b070ac0c2b030ac0c2b030a81c2a030a80c29070a40c29030a40c29030a01c27070981c240b0900c24030900c24030900c24030900c24030900c24030900c24030900c24030900c24030900c24030900c24030900c24030900c24030900c24030900c24030900c24030900c24030900c24030900c24030900c24030900c24030900c23070881c21070801c20030800c20030800c20030800c20030800c20030800c20030800c1f070781c1d0706c2c1a070680c1a030641c19030640c19030601c18030600c18030600c18030600c18030600c180305c1c170305c0c16070580c16030580c16030580c16030580c16030580c16030580c16030580c140b0500c14030443c11030440c100703c1c0e070341c0c0702c1c0a070241c08070182c06030141c040700c1c02070002bfe0aff80bfa12fe41bf806fdc1bf50afd01bf306fc42bf102fc40bf102fc40bf102fc40bf102fc40bf102fc40bf102fc40bf102fc40bf102fc40bef0afbc0bee06fb80bee02fb41bec06fac1bea06fa41be902fa40be902fa40be902fa01be802fa00be802fa00be802fa00be802fa00be802fa00be802fa00be802fa00be802fa00be802fa00be802fa00be802fa00be802fa00be802fa00be802fa00be802fa00be706f981be602f941be502f940be502f940be502f940be502f940be502f940be502f940be502f940be30af842bde0ef780bde02f780bde02f780bde02f780bde02f780bdc0af700bdc02f700bdc02f700bd90ef601bd802f5c1bd50af444bd102f401bce0af2c3bca06f1c3bc606f0c3bbf12ef81bbd06ef01bbb06eec0bb80eed04bb306ec03bae0aea84ba906ea01ba802e9c1ba606e941ba406e8c1ba206e784b9916e505b910ee383b8c0ae243b860ee084b8106dfc2b7d0ade83b7612dd80b7506dd40b7502dd01b7012dbc1b6f02db81b6e02db41b6912da01b6412d882b6202d802b5e0ad741b5c06d700b5a0ad584b5506d4c2b4e16d245b4806d200b4706d1c0b4702d1c0b4702d1c0b4702d1c0b4702d1c0b4702d1c0b4606d180b4602d180b4602d180b4602d180b4602d180b4602d180b4602d180b4602d180b4602d180b4602d180b4602d180b4602d180b4602d180b430ed003b3d0ecec2b3b02ce42b3902cdc2b3702cdc0b3702cdc0b3702cdc0b3702cd81b3602cd80b340acd00b3402cd00b3402cd00b3402cc43b2e0ecb02b290ec983b2602c980b2602c980b2602c980b2602c980b230ec842b1d12c644b170ac485b0f0ec2c4b0b02c2c0b0b02c2c0b0b02c2c0b0b02c281b080ac200b0802c200b0412bf08af812bcc5af10abb44ae61eb845adb1ab6c0adb02b6c0adb02b6c0adb02b6c0ad90ab640ad70ab5c0ad606b541ad20eb2c7aca06b184ac30eb0c0ac302b0c0ac302b0c0ac302b0c0ac206b041abf0aafc0abf02afc0abd0aaf40abd02af40abd02af40abd02af40abd02af40abd02af01abc02af00abc02af00abc02af00abc02ae82aba02ae80ab906ae40ab806adc1ab50aad40ab502acc2ab302acc0ab302acc0ab302acc0ab302acc0ab302acc0ab206ac80ab202ac41ab006ab04aac02ab00aac02ab00aac02ab00aac02aac1aab02aac0aab02aa42aa902aa40aa806aa00aa60aa980aa506a940aa406a900aa306a842aa006a800aa002a800a9f06a781a9d06a740a9d02a701a9b06a681a9a02a680a9a02a680a9906a640a9902a640a9902a640a9902a640a9902a640a9902a640a9902a640a9902a640a9902a640a9902a640a9902a640a9902a640a9902a601a9706a5c0a950aa540a9502a540a9502a540a9502a540a9502a540a9502a4c2a9302a4c0a9206a480a9202a402a9002a400a9002a2c5a8b02a281a8a02a280a8612a141a8502a140a8502a101a8402a100a8402a100a820aa002a8002a000a8002a000a7e0a9e84a79069e01a78029e00a750e9c83a72029c02a70029b82a6c0a9ac1a680e99c1a650a98c2a63029707a5b0696c0a5b029681a5a029602a54129500a54029500a53069481a51069401a50029400a4e0a9341a4b0a92c0a490a9240a490291c2a470291c0a470291c0a46069180a45069140a45029140a45029140a45029140a45029140a430a90c0a43029042a41029040a41029040a40068fc1a3f028fc0a3f028fc0a3f028f81a3c0a8f00a3b068ec0a3b028e81a39068e01a360a8d02a34028d00a33068cc0a33028c81a32028c80a31068c40a31028c40a31028c40a31028c40a31028c40a31028c40a31028c40a31028c40a31028c01a30028c00a30028bc1a2e068b80a2e028b80a2e028b80a2c0a8ac1a2b028ac0a2b028ac0a2a068a02a28028a00a28028a00a28028982a26028980a26028980a230e8881a200a8686a1a028641a18068600a160a8580a160284c3a13028481a12028441a11028401a100283c1a0f028342a0a0e8241a090280c6a030280c0a030280c0a030280c0a030280c0a03028081a000a7fc19fb127ec09fb027e819f80a7e009f8027e009f8027e009f8027e009f8027e009f7067dc09f7027cc49f3027cc09f3027cc09f3027cc09f2067c809f1067c019ee0a7b419ed027b019eb067a819ea027a419e80679c19e70279819e50679409e50279019e40279009e40279009e30678819e20278809e20278419e10278409df0a77c09df0277c09df0277039dc0277009dc0276829da0276809da0276809d90676409d90276409d90276409d90276409d90276409d90276409d90276409d80675829d60275809d60275419d20e74809ce1272849c61270849bb1e6ec09bb026dc49b7026dc09b40e6c439b1026ac69a71269039a40269009a40269009a40269009a40269009a40269009a40269009a40269009a40269009a30668c09a20668419a102680199f0667c099f02678199d06674099d02674099d0267409991266409980665c19960665419940665009940265009940265009940265009940265009940265009940265009940265009940264c19930264c09930264c099302648199202648099202640299002640099002634398d02634098d02634098c06630098c02630098b0662c09890a61449820e5fc39781e5d43975025d01974025d00974025cc1973025cc0972065c80972025c80971065bc296f025b4296d025b4096b0a5a42969025a40969025a40969025a40969025a40969025a409690259839640a59009640259009640259009630658c096206584196102584096102584096102580196002580095f06578195c0a570095a0a56809580a56009570655c09570255c09570255c09570255429530a54c09530254c09510a544095006540095002540095002540094f06538194d06534094c06530094b0652429490250c69430250c09430250c09430250c09430250c09430250c09430250c09410a504094102504094006500093e0a4f8093e024f8093c0a4f0093b064ec09390a4dc2937024dc0937024dc0937024dc0937024dc0937024dc0937024dc0937024dc0937024dc0937024dc0937024d81936024d80936024d80936024d80936024d80936024cc392e164a4592512484491a1e46029102241c99040e40828fd163c4c8ee0e3b028e81238c58db2236428d51234448cd1232838c80a2f0c8b51e29ce89d2a25878883a1f0c8722a1a0a85e2a15498473a0ecc8294a05d280f22028580516010180011ff047f90dfd057f011fb827e621f9417e111f7447d719f3c87ce05f3807c915f1447c405f0827c009ef047b90dee017b609ed027b209ec027ad0deb407ac05ea827a809e70c79a09e64179709e50379305e40378d0de2c278a05e24178319e04278005df4377a0dde0276f25db0376811d90476011d4cd75109d34474719d08573d15ce8372a41c80a71c11c54770e1dc1886fa31bd846f019bb046e811b9046e209b8416e005b7826db0db6036d801b6006d801b5046d209b4026ce09b3416cd01b2c26c909b2406c805b1826c409b0046bf05af426bc05ae436b21dac026af05aac46a80da9c16a40da80469e09a6c369a05a4c768b21a14668309a00367c119e8267a019e0266e299a456631997076551d948365009938264c0992c1649099183645059101642098f8463b0d8e81638098dc1635098c0562d0d89486220d87c361b1186036131584816100983436091182016050d81016010d80405ff097fc05f9197c875f1057b835e9157a015e70579035df1576075d02172475c70971035c20970415b7296b895ac0969475a309684259d1166835980965c15950964c259205630658a096241588056182582115f45579115c4856e0d5b025671559425620d57c355b11554655015530454715500753c114e825370d4cc45300d4bc152d094a835241947c55172144c45100d438250a1141065020940024f91d3d444ef1939c84e40d38824df0d37034d61933c74cd0933014c61931024c20930024bd0d2e444b4152bc54aa152a804a905288749e1126844980925c14940d24c14910923c248c0d22434880521434820d200247c111dc5473111c0346d0d1a834661116cb45a0516414580515434540514824500913434481511c14460510c3442050f45438150dc1437010d81434090c82431050b4442815088641d15074041c05060441219034540b0902424080501c140310ffc43fd08fec23f518fcc23f300fb853ec08fa823e610f8c33de14f6453ce2cf3023c618f0c33bd18ee443b510ec443af08eb033aa08ea023a50ce8c239e14e64539708e54239308e40338238de8837610dd023710cdbc236b10d98536018d78235914d58335114d44035100d44035100d44035004d3c134d08d30134b04d24234708d14234308d08134008cfc133c0cce8233a00ce0233704cd423320ccc0232d0ccac232a04ca023250cc88332104c7c231f00c78131e00c74131c04c6c131b00c68131a00c68030944bece2f128b7152c850ad142a0509de926938965024e2c8e552168c83491ff387a561db38734e1be3c6b511917061ca179385a5014e6c500e1313c46d610c3c400c0f334390f0ce582fcf0b138271508c401f4f06854178a05c0815c50501c12c50441c0f4703b080e42035100cc2001c80001 0x3b2b44ecad33b2354ec8db3b1a34ec68f3b1244ec4933b0a34ec28f3b0264ec09b3afb54ebed73af05ceba173af24ceba4a3ae364eb8db3adb54eb6d73ad350eb2db3ac12feae49fab12feaa49faa048ea6113aa24cea6533a914cea2173a7850ea0173a884dea0107a794de9d1b3a6a48e98913a5848e88113a7360e9ad83a6260e94173a485ce96d83a406ce94933a4928e90097a3938e8c4d3a2839e860d7a3a50e8c543a2b60e88d83a1a60e82933a1038e844d7a0a44e80123a0a3ce809339f024e7e5079f035e7ad839e358e791739d05ce76d039dc54e721739d249e729079c368e711b39bb50e6f1939b14fe6a51f9a12fe664af99127e6248f98248e60d3397a30e5ed139095ce42db397258e5cd7396a40e5ad539627ce5692395b4ce548c395344e529e394b7ce5098394374e4e97393348e4ad0b92b48e480db91935e42d7391238e34d9391354e429538c255e3c9378bb56e40da39046ce3ed438fc64e3c0e38e838e3cd938eb54e380e38e244e320e38d842e348e38c038e34d738b838e32db38c35ce2e8e38b06ce2ade38ac7ce28d838a474e26d7388838e240eb88a44e2009387934e180d38796ce1cda38746ce1ad4386c64e181b385b4ce14de38547ce12d72f7159e0c4d6cd236e104db83a4de0c8d6db12ae0a4e382134d5ad737fa38de44d781b54db611378935db40d381b5ce048d780a34e004d371038e051937f248e02d537f239dc20e37ea39e00d537e139dc00e37cb6cd4cd937fb54d5a9537f344df69137e948df85137ba34df6d3349360df4da37ca54dea4a37a124dec9537c23edee8f379924dbe0e37b234dbc0e36b834dead7b6a834de8d7b79a34dba0e36a034ddad537736cdd6d3369834d48d975fb5dd4719b75134c50d6350265de4956d892ac38d8378a6dd7a9777823db604ab78466b66d1345a62dde92369044d3ed9b77b4cb66932c5340d6e9ab4f266ddc5537393cdda5b37614cdca4d37496cdc851375934dd05537513cdcc49b71924dd28e774134da20d373b5ed9e0d372248dcc51367044dcad5b72239dc64d366834d389575da4ddc48e370a34dc04d36e034dac0d34db56d6896b6fa5cdbc9536e924db209368034d7297f5925bd3495f43a53db88f36d925db4576d481bdb28f36c125db04d34b256d6256b4a956dae5536b13cdaa0636a014da649757a5bd2895f5715bd2655f6913dc4e16ad401ada21536803cd9e0b367026d9a09366068d9896765b48bd852765139d904d6f5949d924e763935d8b5bb6546ed9319b6436ed8ed9b63345d8a4ef6214bd8650f6113cd824ef60133d7e4e75e935d760e35f139d784d75d038d7f1d35f464d7add35e364d720e35db64d74d535c935d6e4d75a038d620d33916fbf653f5c139d6a4d759838d600d33896fca058efd14fb8450f5c354d5e1535bb44d6c9735aa44d6412357044d68d1359a44d6451758a34d604d357839d5c0d756b6cd5853f55943d4a4e750935d3a0e34b834cde5bf26963d5453f54943bf04fee0933d5013b53842d4c8e352139d404d74e038d4cd7351939d3e4d74d838d2c0d34f125d2a09352c7cd491b351b48d2811351470d42df35036cd3e8e34f234d340e349834d3adb34e35cd368e34d135d321b34c360d2e9b34b128d2a4934a029d2609749244d0a4a342128d0449348964d2049346139d124d744038cda5bf24163bec53ee0143d1e4ef47137d1a0eb46354d16d734525cd1291343848d1091343945d0c09342d6ed0ad3b4226cd065b34126cd0258340174cfe4ef3f133cfad573e038cf60e33e35ecf6d5b3d14bcf250f3b955ce496b3b155ce693f3824bcdc91f36243ce85573c57ccee1533b034ceb5c33a05cce6de339c7ece11e339344ce29133857ecdcde337b6ccdd1fb36478cda9133657ecd75d335046cd20db3515bcd255f3446ccca5b733b70ccd5a33285ccc8d3f31b4bcc4d1f30b43cc013b2fc6ccbcd7f2eb5bcb8d5f2db53cb45832c960cb01731c026cae0f31b826cac1531a826caa8ff2a23bca68df29233ca20b31e94cc785731a144c9e4d328354c6651327134c9f1bf27463c965b31d94cc9b1f32517cc9851325b6fc94d8ef893ec921531d15cc8e4d324354c8c4d323c6fc8d18f22a4fc8892f21a47c8490ef814ec820b32002cc7e97f1f253c7a93f1e24bc7691f1d243c7b1fb1e57ec771fb1d57ec72da31c064c6896b19a6ac6e1131b360c6a1b31a46fc6718f19068c6496718b5bc60d4f17b55c5cd5316d70c58db315a64c555af14d67c50512c7926c4e0d313034c4893ec6926c4e4d313034c4a51312144c46512d012ab3c4ab11360c42d2f10343c3edb30eb75c3da030ee70c3851302136c3455300144c364d30c944c348e70ca35c2093f06243c308ff0ba3bc2c8df0aa33c168caff934c2851b09944c1ed3b0924fc2290f08144c1e4d307164c1a512ff144c144d306154bfa51304934c165930546bc1318f0426fc0e9af03267c0a98f0267ec0917aff252c06dc30134ac02d22fea52c0092affa4ebfd1aefec63bf69aafe25fbf296efba57bea94efe48cbf8de6fcd8cbf6d12fd244bf31e6fbc8cbf0df2fbb79beb632fb244beb1e6fa468be71c2f935cbe25b2f8124bde4f2f7347bda51af645fbd715ef5146bd05baf4946bd0d42f3c50bcc8fef2a37bc9142f1b55bc08eeef237b9a996f1255bbe8e6ee038bc29b6eaa5dbba8d6ed838bc19e6efc6eb98d9aed048bbd9e6eeb66ba49aae5a66bb8d7aedb56ba697ee825bb9495ee1a53bb48e6ecb5fbb0d6eebb57bacd4eeab65ba8d56e983aba4d1ae8a46ba012ae7b6db9cdb2e6b5db988eae5a36b940eae4b6fb90daee3b67b8cd8ee2a46b88912e184ab7e632df18cb84d52de98cb831f2de18cb80d52dfa5fb7c96edea57b7894edfb79b7d1e6deb79b791e6ddb70b744f2dcb64b70d6edbb53b6c91ada946b68512d9944b3e51ad8a44b5e512d8244b645f2d7144b52112d8b6eb60d9ad4034b5edbad7366b4e0d2d2c5bb4714ed6b5fb58d6ed5b57b54d4ece956b52d9ad4134b4e0d2d3164b4a512d2154b44512d1954b42512d146bb4318ed0570b3e5f2cf36cb3a4d2ce34ab36d22cd14ab3293ecc243b2056ac715ab22902cba55b2c912ca828b280a2c9824b2a97aca256b2655ac9022b22112c8370b1e5f2c7348b1a512c634bb16d0ec5144b120d2c3c53b120d2c4164b0c512c3954b0a512c346bb0b18ec236fb06daec1367b02d8ec015fafe55ebf464afa956be254af653ebd147af35c2bc26daee9b2bb26faea98eba470add1baaf4625204aeb6b6fac4d8e3196f66c4fd75137a0857e3105f7e814d4701b4bc05d5292f51a4ad2e92746e48eb9b418de8c99a13f5d04deb923760852564141ae24eeb81375164ad2d9276644fd73137ad91baad46290a9363aa45662535721455124ad1a923ad6dbeb0b63aded06702628f88ea3096f65e4fd719375464b6b7358ad4996b6a55ad8d22b5a458c958ab546f9be98a3016f70451eb4b5fad0d5e6b25f99896e5ba5794494eb3a3ba9a8ddd015b6ce54d4312b46448e8845b8cad0a362425084ad2b12753e4bd4192b4aa49d1812399492a502426fc51d4f12d45e486b335bacad5eb215bac655ddc13f73c4edbe9376ca4cddb94f6c850e6a93f9904ee5a93793c4ce6a24f98e92e5a24793a90d4e01f50206d2981745a04eaf468ac4996a7235ab5162b0a55abeda258265ac0956a9a39a988c6a313da824e69e935a704c54012ba5e0ea97038abf1b286b7cabcd72a8245aba8d696848a42112adb50ab89b669a5daa88f6a7a35a8a4f6a0139a784d69b9314fe4ae9603aa560e290036a3e0d2adc64a10df2ad35caa4926aca38ab08d6aba34aac4e2aa934a54122aa466904df27f35caa2922a6a35a521228f044aa71baa946295ed9aa8b4ca9a919b1163a885369f949a745169b141a5012a93848a3a11a8e044aa0daaa7b6698c9aa57266a968c1b0963a864f69c935a4c0ea92838a360da8d034a9d5bea6c63a1f16e6f26298a96a35a428be5bdbd15765c53d4d92da991baa5b448cc9f2a526ca929926c25ca904a2a3924a481228c844a8d1baa2c66654df22e35ca88926a1a45a848d69f148a461228c044a831baa04669a2dbe6136b95ad9e4d363a7ed269f24ca2e1129eb6ea78d9a6826f9829ae5626793298e9da4da748e69ca357385aa9a9304fc4aa91038a2c0d29c46ea6f19a9b349a6a9115797ca685b2999647a65729913ca624da98134a2a11297b5fa5cd7a96b5aa58d5e95b56a54d4a67a5f98096e55a5793094e94a3da508ee93a39a4c8de92a35a488c69193da444d690a5aa4095e8fa5697e56e55157a3c4b68e92ba384a68d927a344968c92173216e8c02da2e0a68b025a2a0853d81b45404e8115f9ba54e2f05f7e614d4c81f4f406d2881745204e8a25ba2695d3c92b45048e8905aa2318a6e2628b45be091675304b53b92ba1d1f286245a208d53b12ba1b1f285a45a1e8d53a92ba1cda686b614e84ae8646ba1718e2c16f82059d9694fa1491e159697e05853912b8ac5be071679ee57e721578aa17e1485b81a15df70534e006d268174de4ae84b7ca0e8d53712b44c48e8437ca0c8d53692b44a48e84b69a10d867b26d9c29953612b44848e83c6ba0d18e82b629dc9aa352428a65be0516765853e82054a02da681b498d28ca7a1699e4596803599fad56799599e25567fb689fd1a281034a035a6805659ff1ba7f46273056daf1538cb5f27ec559f81f27dc649f4d9a7cb649f15a27b85c9ecdf27ab649e95a679d659e516678c559e01b277a549dcd1276a4476257dae1539cf17a71c529d8d7e75b5775e57dcb15b6e655dad1535fe525619419d44ee749379d11f273b709ccdf272d709c817271c709c4df270b6c9c0d526fb648c89926ca4c9bcd126c25c9ba1126e3549b69526d2448cad666cc6e9b118a3236e6b054d9314d5ae5162905f7d814e6bb599ad9fa2517f7d65ce6b34e64853d601439aa5f26a1709a6d96693558925fdf517364653d5f9439a24ee6813799e0ea6736e88e5bdf49639999fa66a6488c5fdf417399917a65a4464257d5f153994df264a7c9905f26397098cd1a62b44978932622469869122297f7ce5cd9015f57a54e6114b98251e6004a97e11a5f359978d465eb6e978d8a2116f7cc58e5cb69966d865db4994cd06131697c85865be7e9755a254b508805fdf19739739c25c36c96ed398e94f57650e5b57096a5f25a1709679c254460964db658b6c94cd825835d95e8ea5723687e5fdf117363853d5d14395a4ee561379560ea550369531ba5446294edba5336287a5bdf09635f65255c94194a4ee5213787817e1205b80215def8539459fa4ba7c9469921d97f7bc5ce481289184925145e92897250a4463257d5b95391e4a245924940df24fa7c92c9b249a4c93c5f24e97091c4a2451249229324e2469369121d17f7ba5cd8c15f56c54e4d14b93251e469289124924c04a92edb64b36592ad6648b519291aa49c66924dba48b6286e5bdee163920d7e47b5b91cd5e46b53918d7e45b5b914d5e44b5386c17e1105b7fa15ded053910d923f93b90ed524337c90b162423549071f1ca16b6ac58e4147c7265adaa963906da64136172452daa1438c8df1b69578c8dba32b4e9035fa1a17f8665fe402366a654e3fe7f8fc5fa3ea548f8d523da548f516da894386217e0f85b7f215deb8538f31a23a4708f11623bc708e71c23b4588ead623a5698e75863935f8e2d5dc815b69e54e3803a8ded52372548da952363448ce9f232a4469a58e35b448cc9f1a61638d4d1234c5b8d0959a59438ceda6333618cad65a51438c8dba1716f8a299631a558c415230a458bada227a658c09562524f88c92e2024787690e2e46889c99624a5f88a96e1fa5787494e2fa358bc0d22ec6e8b918a2425f88896e1f25787294e2dc648b49162cb6489a9962c2358af5a2262658ac9762a85c8a8d9229a35896d92290248a317e2836189ed7e2735389ad2e26347896949050474020fcf9837894dfe24b73890da623b495684ca2347f88b1ce224698869922124e56650a20d68880dfe1fb7387cda61eb515644ca1e05c8771fe1d4738731a61c26486e9395894286c0921ab64868d7e19b57864992188248611a21724d85e9921724e85a5521614482e4da15e708545b21486c8505120e14e83657a1393484d9c21296c83453a1206c83257a119348440d2109448404d20f83483c5720a94483a4d20e25f83696e0d25783294e0c03682f16e0b34282a90a09c5e81914a0325f80a96e0125780094dfda497ee9060a47c826dc209245822df20427d8208d607d7080e9f60725d81a17206470816df205235812d660434b80ed1dffa427ec8ca0337180b1c60227c8075c201371802172004717fedf1ff27c7fa091fe37c7f71c1fd27c7f2091fc4707ef1c1fb37c7ea9f1e51367e8191f5b5f7d0d6df1b577bcd4dea14c7924d9f536f7cedadf13677bad8de995c7904d9f98447e4551e915c7e2511e39367e19c1f796c7a2531e31367dc1b1f6944782051e21447d80d1e00147d71fdf54737d31658724e7a0539f457f7cf5cdf335e61a979e795e786511f29347c99c1f1c7f7c51cdf0c61618939f016c79c539ef86c7bd5fdeed737b8d7985a5e79a579ed9347b40d1e615c7b2511e11447b04d1eb8347ac571e594c7aa4d1ea46e7a7189e945a7a3159e825f79e96de725779a94de624d796915e556f7931bde446378f16de345778ad09e2262786969e124a78297de025377ed65da35177c96ddea5774e8fdd1a33778169ddc64758915dd354756955dcc7c7709f1dba70754915da35876cd51d4a5576adb9da362767191d9254762939d847c75edc5d725475b589d636f756dadd5367752d8dd435174f5f9d335474a951d24587475f9d12547419f91da36742591c4936741179ca35f4748d9cf9447104d9cf37c4728d9ce97c70e4d9c9b5f7389191c236716531cd946734511c3136732119cc46972e591c514e72d1c5ca97c7295edc9d737251f9c697e722511c857271e571c7359716d45c6a3f718db9c5b627149bdc4c6f7111adc3c6770d18dc0b696f8d85c2b496ecd05c22476dc8fdc1d686f2d41c12656e49753512a7039c1c036c6e29b53492a6ff5c1bf27d6fa9f1b825d4d04a9be6706f1181bdb6c6ecd81b7a6d6f48d53392a6f31b9bc4626eedb9bb3626eb5a1b505c6e95c1b9b716d2171b936f6e2dadb83676ded8db76726dadddb636c6d7181b515f6d255db3e7e6d05919f9366cf179ab35f69ad4da295c6cc5119f1366cadf1b23706c65f1a214c67a4d9aab5f698d4db134b6c2d1da114c6c0519af9446784d9af469696d09ae964682539ae35e672511ad9346b51c5ac97c6a7179ac35e680579ab9346ad5edaad736a91f9a9b7268e5f9a91446a2df9a813469f5c9a715c69b5eda65736971f9a537e68c5f99c1446924d1a4359684d45a3a3f68c8cda2c6a689199a1b6e684d89a0a6f68098d9fc6f67d1ad9ec6767918d9db62674d099ca6a6709099bb6466c9958aa3566ad519a255666df19927d6288d598c58660d5197a556571f19226f6429ad8ea6763298d892456551f191a6f6409ad8e26763098d88a4565c8d58824565a8d596235656da59536164493d8fa4b63691d8ba43652d91850346509118484464edf18403464c97192a4460e1119247b6471cd9137e61c5c990d7b6415cd8fc7e63c9118697263b1ed8e473636df98d36c6185c98cd7b6315cd8bc7e62c9118597261ed118ad6f62959d89c62624dad88b63620d6d87a3261c97d86a5b61895d85a5361457d8495b61055d8395360c5917a13660a551824706065f179936604551809645de051801345dc0517fc705fc5f1768145e25117e9345d80517c17e5ee5f9781445f84d17dc605ec5f97d16c5ea5f97c9345f093d7ba4b5ec91d7aa435e95bd79d675e4d8978a625e096977a5f5dc96d76a575d894d75c685d499567a4d5c51c174c585d095573c705cc9f56724d5c31c172c585c8d6171a555c55a570d615c0d7d6fb575ac97d6aa5b5a695d68a535bc8ed6ea375b80e96dc685b49716cc70598d716c25c5ae9316b4725ab5c96a25c5a71c9694605a35c965b5c5a097167d6f59d59d66b6e59898965a52594591649545911c16397c5544d963154580dbd5f36b576d9d5bb635605f15fb6f57adad5d36756cd8d5797c5524d96296454e511621345871c16117c5824d16047b57f1cd5a27e55c5f95f57b57b5cd59a7e55a5f95e1345771ed5d4735731815927e5585f95c16c56f5ed5b5735629f95597e56a4d15314456893d59a4b56491d58a43560da557b6155c93d56a4b55891d55a4355559d54c5b550d8953a6a54c90952c5954895151b5454495150a645409114fd7053cdf14ea7c5381f14db445229314d2445321114c35452e95149a7e52c9114ac5b528d6548b51526d0d0904f3fe0fd4936e522d89484694df145479644c65394706451b165461545171c54517c4ef1a544c595105513114e50d9f93525650e5913b56b4dd58d4345e4d2999429445095f141d704d09594117c5021f13ad6b4db58d4046f4ff19d33a664fc9193014c4fa5193e1444f61193d0444f35f93c1544ef9c93b57b4eb5cd3a47e4ca5f9399444e59c93896c4e01b137e7e4dd5ed36d734d91f93217e4d65113536f4d2dad343674ced8d333594c0d4532b4b4c8d0d31d6f4c558d30b6e4c0d892fb684bc1912ec59496dc12e3584b71c52d370494dc12cb584b0da120b404765692bb484745a92b57c4ab5c12a3704725692987c480d4129348478d011c16a4a21112835847ed0124b7249ed212736049a1b12437247cd41263484975a52556149316d2445348e97d2325748a9391e24242017d040573fa13d2202a48609d210264831b92046247f1791f45247a9b91e2623f8134f78454771bd1d46b47319d1c46346f1651b15446b1651a1544405391967e466591135634651790f95c4625111857045edf11717c43c5311687c44b58d0e14c45851915944454119148444515f91395444d5ed12d734491f91097e44651111359438d4510b4344158d0fc6a43d1990eb6e438d890da7c434dc10ca5b43095d0bc6442c9510ad624265bd0a4644269150927e4229510837241ed610724741b5a9065684125bd05d6841499504a5d410dc903b6040cd9902b6440891101c624005bd01364402995002353fe9f8ff2443fadc8fe3503f6d20fd23b3f28dcfc4683ead70fba5c3ecdb8faa623e45bcfa4683e6994f924d3e2970f83503ded00f72643dada0f61643d64d0f53623c0dbce9b633d2d64dbb413649bcf42552ec8fcb02372a65bc911631b04fc6113b1664dc5293310a4ac3b1273ce150f33493ca914baa3f2c88ecafa372b68cc6b93f1824ec591371484cc4812f1084ac3a9270ce48cf23613c69b4ba23f2bc8dc6b13f1804ec589371464cc4192b0e849cefb6f3a4d8cdfb593c4d24d8a6f33498cf0a452e68fcb1a3b2ba8dcad2332a45bc909631aa4fc5f93b1604dc5113311e4bc4112b0e649c331233bb5b8f046f3bf18cd726f33298cef25532293cc624b30a91cbfa432a25bc9016321853c7f14b1e451c7394311c4bc4092b0e449c3292337d16cdb4533bad38c825f31696cc22572fc94cb924f2b290cee23521657c7e95b1e255c731531a853c5094311a4bc4012b0e249c321233b71b0ed4603b29b4ec26c3ae980c7a4f31492cc1a472fa90ceb16c3aa5808514f1f852c781471ca50c4612f0fe4ac381270c648cea06c3a75bce956337b16cdac533a2d7ce835b39ed5ce735335a9bccc26331c97cc4a5b30495cbe2532e293cac24339a8fcb5a3d3988ece5a373948d4e4a332a05bc8f96321257c7d95b1de55c721531a653c501433904fce393b38c4dce29331164bc3f12b0de49c311233880e8e18363840d0e0c6e3529bcd126b33c99ccba63380914a716f27e5ac9816723c58c4512f0fa4ac371270c248cdfd6237d1acdec63378db8d426f33a99cb824f3768d4a696f27c5ac9796723a58c6914f13e50c3e12b0da49cdd56234e9bcce267372974a616f27a5ac9716723858c3d92b0d849cdc05c36f5b8db46b36b18cda36e34c9bcd0a6b33699ccb2632de93caba433668d4a596f2785ac9696723658c6894f13c50c4492f0f44ac359270c048cd946f36318cd845b35f15cd736f35ad8cd635b356d64d53572d6d44d4b4f350d2cd3b4734cd0cb423e2ac8c8a516f23458cd295b34855c8394f1f452c769471c650c6793f17c4ec5713713a4ccd18570aa13c270470920fc2103707007c1a01734517cd0c533409388315f1c454c6714f17a52c5694713850ccfb6133cd3cceb4b338d1ccdb4332a9b48294f1f252c761471c250c6693f1784ec561371364cccd5633331bccc46332f17ccb4532ced38caa6e328938a496f23258c8215f1c054c6614f17652c5594713450c2a05f09013c208473260901b81f06605cc946e322dbcc836b31ed9cc736331ad24a396f2765ac9596723058c6593f1744ec551371324ccc646f3171acc546731318cc426e30e938a316f2745ac9516722e58c6514f17252c5494713050cc356230adbcc236b306d9cc1363302d44a296f2725ac9496722c58c6493f1704ec5413712e4ccc005c2ff1bcbf46b2fb19cbe4632f69b8bd24e2885bc9c16b25059c8a96319053c5b94b14e51c4b1432f24a0bc1242ee090bb56f2eb5acba5672e758cb946b2e318cb845b2df14cb736f2dadb8b63672d6d88b535f2d2d5cb426e2ce988a196f26e5ac9396722858c8115f1f056c751571be54c6394f12a50cb313b2ca4dcb256b2c758cb126e2845bc9b16b24c59c8996320257c6f1532c2090b056f2bf5acaf5672bb58cae4622a8934a096f26a5ac9296722458c8015f1ee56c749571ba54cadd6b2b558cacc6b2b118cabc532acdb8aaa6e2a8938a016f2685ac9216722258c7f95f1b854c6314f12850ca9c6f2a518ca8b6f2a0d8ca7b5929cd3ca6b4b298d1ca5b432949bca4a63290954a3a4f28c92ca2a4728890ca1a3f2848eca0a372808cc499320a413c2604708c0fc1f8370760bc1c82727f17c9f45b27b15c9e453276d7c9d35b272d5c9c35326ed3c9b34b26ad1c9a34326653899136262d849834f25ed2c9734725ad0c9626d25693c9524b25291c9424324e8fc9323b24a8dc922332461b09156f24358c9046f23f18c8f45f23b16c8e45723714c8d36f232d8c8c35f22ed6c8b35722ad4c8a34f226d2c89347222d0c6224e2205388793621c05086c6e218dbc85b6b214d9c84b63210d2483a6f20c9ac82a6720898c81a452048fc80a3b2008dc7fa331fd1bc7ec6b1f919c7dc631f4dbc7cb671f0d3c7bb470d08d87b16e1ea5387a1361e75887936f1e2dac783671ded8c773511da9bc762671d69747523f1d28dc3c92a1d017073c6f1cd1ac72c671c918c71b6f1c4dac70b671c0d8c6fb4f1bcd2c6eb471b8d0c6d96e1b45386c9361b15bc6bd6b1ad59c6ad631a91ac69c631a516c68c531a0db867a6f19c9ac66a6719898c65a5f19496c64a5719094c63a4f18c90c62a35188588618341855bc60d6b18159c5fd6317cdbc5eb6b178d9c5db63174d7c5cb5b170d5c5bb5316c5b85a93616805059d6f1655ac58d6716158c57c6215c9bc56a6b15899c55a6315497c54a5b15095c53a5314c93452d6f1495ac51d6714558c50c6b14118c4fc5b13d14c4eb6f138dac4db67134d8c4cb5f130d6c4bb5712cd4c4ab4f128d0c49a6e1245b8489361215ac47d6311d1bc46c6b11919c45c6311517c44c531109b843a4e0ba1bc2c0670a217c2284f07c11c4302410b5bc4256b10759c415631031bc4046b0ff19c3f4630fb17c3e45b0f715c3d4530f29583c16e0ee5383b56f0eb5ac3a5670e758c3946f0e31ac384670df18c3745f0db16c364570d714c353620d2d083415a0b81bc2b8670a017c2585708813c1e8470cf5ac335630cb1bc3246b0c719c314630c317c304530be5b82f14e0ba4bc2e1270b69b42d16c0b25802c12f0ae49c2b46e0aa9bc2a2630a69142916f0a24bc2812709f5882726f09a9742616f09649c2536e0929bc2426308e8d42316f08a4bc221270871882126f08298c2024d07e5bc1f12f07a49c1e26e0765bc1d3620725bc1c36f06ed8c1b16e06a4d81a36f066d8c1945f06316c1845705f14c1735f05ad6c16357056d4c1534f052d2c1434704ed0c1325f04a96c1225704694c1124f04292c1024703e90c0f23f03a8ec0e2370368cc0d15f03256c0c15702e54c0b14f02a52c0a14702650c0913f0224ec0813701e4cc0712f01a4ac0612701648c0505f01215c0404f00e11c0303f00a0dc0202f00609c0101f00205c0003f 18 6 11 11 7

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_115 : dagCheckRootsF fullMask g_115 bds_115 (dagRefF 1894 (dagTraceF fullMask rootStock 11 f_115) l_115 0) rootStock 11 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_0 : treeBlockF 0 16 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_0 : ∀ j, 0 ≤ j → j < 16 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := (fun _ h₁ h₂ => treeBlockF_at block_115_0 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_16 : treeBlockF 16 32 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_16 : ∀ j, 0 ≤ j → j < 32 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_0 (fun _ h₁ h₂ => treeBlockF_at block_115_16 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_32 : treeBlockF 32 48 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_32 : ∀ j, 0 ≤ j → j < 48 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_16 (fun _ h₁ h₂ => treeBlockF_at block_115_32 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_48 : treeBlockF 48 64 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_48 : ∀ j, 0 ≤ j → j < 64 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_32 (fun _ h₁ h₂ => treeBlockF_at block_115_48 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_64 : treeBlockF 64 80 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_64 : ∀ j, 0 ≤ j → j < 80 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_48 (fun _ h₁ h₂ => treeBlockF_at block_115_64 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_80 : treeBlockF 80 96 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_80 : ∀ j, 0 ≤ j → j < 96 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_64 (fun _ h₁ h₂ => treeBlockF_at block_115_80 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_96 : treeBlockF 96 112 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_96 : ∀ j, 0 ≤ j → j < 112 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_80 (fun _ h₁ h₂ => treeBlockF_at block_115_96 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_112 : treeBlockF 112 128 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_112 : ∀ j, 0 ≤ j → j < 128 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_96 (fun _ h₁ h₂ => treeBlockF_at block_115_112 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_128 : treeBlockF 128 144 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_128 : ∀ j, 0 ≤ j → j < 144 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_112 (fun _ h₁ h₂ => treeBlockF_at block_115_128 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_144 : treeBlockF 144 160 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_144 : ∀ j, 0 ≤ j → j < 160 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_128 (fun _ h₁ h₂ => treeBlockF_at block_115_144 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_160 : treeBlockF 160 176 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_160 : ∀ j, 0 ≤ j → j < 176 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_144 (fun _ h₁ h₂ => treeBlockF_at block_115_160 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_176 : treeBlockF 176 192 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_176 : ∀ j, 0 ≤ j → j < 192 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_160 (fun _ h₁ h₂ => treeBlockF_at block_115_176 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_192 : treeBlockF 192 208 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_192 : ∀ j, 0 ≤ j → j < 208 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_176 (fun _ h₁ h₂ => treeBlockF_at block_115_192 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_208 : treeBlockF 208 224 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_208 : ∀ j, 0 ≤ j → j < 224 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_192 (fun _ h₁ h₂ => treeBlockF_at block_115_208 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_224 : treeBlockF 224 240 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_224 : ∀ j, 0 ≤ j → j < 240 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_208 (fun _ h₁ h₂ => treeBlockF_at block_115_224 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_240 : treeBlockF 240 256 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_240 : ∀ j, 0 ≤ j → j < 256 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_224 (fun _ h₁ h₂ => treeBlockF_at block_115_240 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_256 : treeBlockF 256 272 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_256 : ∀ j, 0 ≤ j → j < 272 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_240 (fun _ h₁ h₂ => treeBlockF_at block_115_256 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_272 : treeBlockF 272 288 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_272 : ∀ j, 0 ≤ j → j < 288 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_256 (fun _ h₁ h₂ => treeBlockF_at block_115_272 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_288 : treeBlockF 288 304 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_288 : ∀ j, 0 ≤ j → j < 304 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_272 (fun _ h₁ h₂ => treeBlockF_at block_115_288 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_304 : treeBlockF 304 320 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_304 : ∀ j, 0 ≤ j → j < 320 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_288 (fun _ h₁ h₂ => treeBlockF_at block_115_304 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_320 : treeBlockF 320 336 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_320 : ∀ j, 0 ≤ j → j < 336 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_304 (fun _ h₁ h₂ => treeBlockF_at block_115_320 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_336 : treeBlockF 336 352 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_336 : ∀ j, 0 ≤ j → j < 352 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_320 (fun _ h₁ h₂ => treeBlockF_at block_115_336 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_352 : treeBlockF 352 368 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_352 : ∀ j, 0 ≤ j → j < 368 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_336 (fun _ h₁ h₂ => treeBlockF_at block_115_352 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_368 : treeBlockF 368 384 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_368 : ∀ j, 0 ≤ j → j < 384 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_352 (fun _ h₁ h₂ => treeBlockF_at block_115_368 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_384 : treeBlockF 384 400 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_384 : ∀ j, 0 ≤ j → j < 400 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_368 (fun _ h₁ h₂ => treeBlockF_at block_115_384 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_400 : treeBlockF 400 416 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_400 : ∀ j, 0 ≤ j → j < 416 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_384 (fun _ h₁ h₂ => treeBlockF_at block_115_400 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_416 : treeBlockF 416 432 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_416 : ∀ j, 0 ≤ j → j < 432 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_400 (fun _ h₁ h₂ => treeBlockF_at block_115_416 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_432 : treeBlockF 432 448 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_432 : ∀ j, 0 ≤ j → j < 448 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_416 (fun _ h₁ h₂ => treeBlockF_at block_115_432 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_448 : treeBlockF 448 464 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_448 : ∀ j, 0 ≤ j → j < 464 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_432 (fun _ h₁ h₂ => treeBlockF_at block_115_448 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_464 : treeBlockF 464 480 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_464 : ∀ j, 0 ≤ j → j < 480 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_448 (fun _ h₁ h₂ => treeBlockF_at block_115_464 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_480 : treeBlockF 480 496 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_480 : ∀ j, 0 ≤ j → j < 496 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_464 (fun _ h₁ h₂ => treeBlockF_at block_115_480 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_496 : treeBlockF 496 512 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_496 : ∀ j, 0 ≤ j → j < 512 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_480 (fun _ h₁ h₂ => treeBlockF_at block_115_496 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_512 : treeBlockF 512 528 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_512 : ∀ j, 0 ≤ j → j < 528 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_496 (fun _ h₁ h₂ => treeBlockF_at block_115_512 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_528 : treeBlockF 528 544 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_528 : ∀ j, 0 ≤ j → j < 544 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_512 (fun _ h₁ h₂ => treeBlockF_at block_115_528 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_544 : treeBlockF 544 560 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_544 : ∀ j, 0 ≤ j → j < 560 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_528 (fun _ h₁ h₂ => treeBlockF_at block_115_544 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_560 : treeBlockF 560 576 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_560 : ∀ j, 0 ≤ j → j < 576 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_544 (fun _ h₁ h₂ => treeBlockF_at block_115_560 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_576 : treeBlockF 576 592 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_576 : ∀ j, 0 ≤ j → j < 592 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_560 (fun _ h₁ h₂ => treeBlockF_at block_115_576 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_592 : treeBlockF 592 608 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_592 : ∀ j, 0 ≤ j → j < 608 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_576 (fun _ h₁ h₂ => treeBlockF_at block_115_592 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_608 : treeBlockF 608 624 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_608 : ∀ j, 0 ≤ j → j < 624 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_592 (fun _ h₁ h₂ => treeBlockF_at block_115_608 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_624 : treeBlockF 624 640 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_624 : ∀ j, 0 ≤ j → j < 640 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_608 (fun _ h₁ h₂ => treeBlockF_at block_115_624 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_640 : treeBlockF 640 656 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_640 : ∀ j, 0 ≤ j → j < 656 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_624 (fun _ h₁ h₂ => treeBlockF_at block_115_640 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_656 : treeBlockF 656 672 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_656 : ∀ j, 0 ≤ j → j < 672 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_640 (fun _ h₁ h₂ => treeBlockF_at block_115_656 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_672 : treeBlockF 672 688 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_672 : ∀ j, 0 ≤ j → j < 688 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_656 (fun _ h₁ h₂ => treeBlockF_at block_115_672 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_688 : treeBlockF 688 704 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_688 : ∀ j, 0 ≤ j → j < 704 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_672 (fun _ h₁ h₂ => treeBlockF_at block_115_688 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_704 : treeBlockF 704 720 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_704 : ∀ j, 0 ≤ j → j < 720 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_688 (fun _ h₁ h₂ => treeBlockF_at block_115_704 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_720 : treeBlockF 720 736 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_720 : ∀ j, 0 ≤ j → j < 736 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_704 (fun _ h₁ h₂ => treeBlockF_at block_115_720 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_736 : treeBlockF 736 752 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_736 : ∀ j, 0 ≤ j → j < 752 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_720 (fun _ h₁ h₂ => treeBlockF_at block_115_736 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_752 : treeBlockF 752 768 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_752 : ∀ j, 0 ≤ j → j < 768 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_736 (fun _ h₁ h₂ => treeBlockF_at block_115_752 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_768 : treeBlockF 768 784 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_768 : ∀ j, 0 ≤ j → j < 784 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_752 (fun _ h₁ h₂ => treeBlockF_at block_115_768 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_784 : treeBlockF 784 800 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_784 : ∀ j, 0 ≤ j → j < 800 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_768 (fun _ h₁ h₂ => treeBlockF_at block_115_784 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_800 : treeBlockF 800 816 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_800 : ∀ j, 0 ≤ j → j < 816 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_784 (fun _ h₁ h₂ => treeBlockF_at block_115_800 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_816 : treeBlockF 816 832 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_816 : ∀ j, 0 ≤ j → j < 832 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_800 (fun _ h₁ h₂ => treeBlockF_at block_115_816 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_832 : treeBlockF 832 848 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_832 : ∀ j, 0 ≤ j → j < 848 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_816 (fun _ h₁ h₂ => treeBlockF_at block_115_832 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_848 : treeBlockF 848 864 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_848 : ∀ j, 0 ≤ j → j < 864 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_832 (fun _ h₁ h₂ => treeBlockF_at block_115_848 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_864 : treeBlockF 864 880 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_864 : ∀ j, 0 ≤ j → j < 880 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_848 (fun _ h₁ h₂ => treeBlockF_at block_115_864 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_880 : treeBlockF 880 896 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_880 : ∀ j, 0 ≤ j → j < 896 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_864 (fun _ h₁ h₂ => treeBlockF_at block_115_880 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_896 : treeBlockF 896 912 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_896 : ∀ j, 0 ≤ j → j < 912 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_880 (fun _ h₁ h₂ => treeBlockF_at block_115_896 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_912 : treeBlockF 912 928 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_912 : ∀ j, 0 ≤ j → j < 928 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_896 (fun _ h₁ h₂ => treeBlockF_at block_115_912 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_928 : treeBlockF 928 944 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_928 : ∀ j, 0 ≤ j → j < 944 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_912 (fun _ h₁ h₂ => treeBlockF_at block_115_928 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_944 : treeBlockF 944 960 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_944 : ∀ j, 0 ≤ j → j < 960 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_928 (fun _ h₁ h₂ => treeBlockF_at block_115_944 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_960 : treeBlockF 960 976 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_960 : ∀ j, 0 ≤ j → j < 976 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_944 (fun _ h₁ h₂ => treeBlockF_at block_115_960 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_976 : treeBlockF 976 992 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_976 : ∀ j, 0 ≤ j → j < 992 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_960 (fun _ h₁ h₂ => treeBlockF_at block_115_976 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_992 : treeBlockF 992 1008 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_992 : ∀ j, 0 ≤ j → j < 1008 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_976 (fun _ h₁ h₂ => treeBlockF_at block_115_992 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1008 : treeBlockF 1008 1024 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1008 : ∀ j, 0 ≤ j → j < 1024 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_992 (fun _ h₁ h₂ => treeBlockF_at block_115_1008 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1024 : treeBlockF 1024 1040 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1024 : ∀ j, 0 ≤ j → j < 1040 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1008 (fun _ h₁ h₂ => treeBlockF_at block_115_1024 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1040 : treeBlockF 1040 1056 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1040 : ∀ j, 0 ≤ j → j < 1056 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1024 (fun _ h₁ h₂ => treeBlockF_at block_115_1040 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1056 : treeBlockF 1056 1072 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1056 : ∀ j, 0 ≤ j → j < 1072 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1040 (fun _ h₁ h₂ => treeBlockF_at block_115_1056 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1072 : treeBlockF 1072 1088 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1072 : ∀ j, 0 ≤ j → j < 1088 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1056 (fun _ h₁ h₂ => treeBlockF_at block_115_1072 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1088 : treeBlockF 1088 1104 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1088 : ∀ j, 0 ≤ j → j < 1104 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1072 (fun _ h₁ h₂ => treeBlockF_at block_115_1088 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1104 : treeBlockF 1104 1120 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1104 : ∀ j, 0 ≤ j → j < 1120 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1088 (fun _ h₁ h₂ => treeBlockF_at block_115_1104 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1120 : treeBlockF 1120 1136 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1120 : ∀ j, 0 ≤ j → j < 1136 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1104 (fun _ h₁ h₂ => treeBlockF_at block_115_1120 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1136 : treeBlockF 1136 1152 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1136 : ∀ j, 0 ≤ j → j < 1152 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1120 (fun _ h₁ h₂ => treeBlockF_at block_115_1136 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1152 : treeBlockF 1152 1168 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1152 : ∀ j, 0 ≤ j → j < 1168 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1136 (fun _ h₁ h₂ => treeBlockF_at block_115_1152 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1168 : treeBlockF 1168 1184 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1168 : ∀ j, 0 ≤ j → j < 1184 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1152 (fun _ h₁ h₂ => treeBlockF_at block_115_1168 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1184 : treeBlockF 1184 1200 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1184 : ∀ j, 0 ≤ j → j < 1200 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1168 (fun _ h₁ h₂ => treeBlockF_at block_115_1184 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1200 : treeBlockF 1200 1216 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1200 : ∀ j, 0 ≤ j → j < 1216 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1184 (fun _ h₁ h₂ => treeBlockF_at block_115_1200 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1216 : treeBlockF 1216 1232 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1216 : ∀ j, 0 ≤ j → j < 1232 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1200 (fun _ h₁ h₂ => treeBlockF_at block_115_1216 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1232 : treeBlockF 1232 1248 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1232 : ∀ j, 0 ≤ j → j < 1248 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1216 (fun _ h₁ h₂ => treeBlockF_at block_115_1232 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1248 : treeBlockF 1248 1264 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1248 : ∀ j, 0 ≤ j → j < 1264 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1232 (fun _ h₁ h₂ => treeBlockF_at block_115_1248 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1264 : treeBlockF 1264 1280 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1264 : ∀ j, 0 ≤ j → j < 1280 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1248 (fun _ h₁ h₂ => treeBlockF_at block_115_1264 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1280 : treeBlockF 1280 1296 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1280 : ∀ j, 0 ≤ j → j < 1296 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1264 (fun _ h₁ h₂ => treeBlockF_at block_115_1280 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1296 : treeBlockF 1296 1312 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1296 : ∀ j, 0 ≤ j → j < 1312 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1280 (fun _ h₁ h₂ => treeBlockF_at block_115_1296 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1312 : treeBlockF 1312 1328 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1312 : ∀ j, 0 ≤ j → j < 1328 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1296 (fun _ h₁ h₂ => treeBlockF_at block_115_1312 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1328 : treeBlockF 1328 1344 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1328 : ∀ j, 0 ≤ j → j < 1344 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1312 (fun _ h₁ h₂ => treeBlockF_at block_115_1328 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1344 : treeBlockF 1344 1360 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1344 : ∀ j, 0 ≤ j → j < 1360 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1328 (fun _ h₁ h₂ => treeBlockF_at block_115_1344 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1360 : treeBlockF 1360 1376 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1360 : ∀ j, 0 ≤ j → j < 1376 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1344 (fun _ h₁ h₂ => treeBlockF_at block_115_1360 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1376 : treeBlockF 1376 1392 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1376 : ∀ j, 0 ≤ j → j < 1392 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1360 (fun _ h₁ h₂ => treeBlockF_at block_115_1376 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1392 : treeBlockF 1392 1408 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1392 : ∀ j, 0 ≤ j → j < 1408 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1376 (fun _ h₁ h₂ => treeBlockF_at block_115_1392 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1408 : treeBlockF 1408 1424 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1408 : ∀ j, 0 ≤ j → j < 1424 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1392 (fun _ h₁ h₂ => treeBlockF_at block_115_1408 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1424 : treeBlockF 1424 1440 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1424 : ∀ j, 0 ≤ j → j < 1440 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1408 (fun _ h₁ h₂ => treeBlockF_at block_115_1424 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1440 : treeBlockF 1440 1456 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1440 : ∀ j, 0 ≤ j → j < 1456 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1424 (fun _ h₁ h₂ => treeBlockF_at block_115_1440 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1456 : treeBlockF 1456 1472 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1456 : ∀ j, 0 ≤ j → j < 1472 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1440 (fun _ h₁ h₂ => treeBlockF_at block_115_1456 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1472 : treeBlockF 1472 1488 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1472 : ∀ j, 0 ≤ j → j < 1488 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1456 (fun _ h₁ h₂ => treeBlockF_at block_115_1472 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1488 : treeBlockF 1488 1504 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1488 : ∀ j, 0 ≤ j → j < 1504 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1472 (fun _ h₁ h₂ => treeBlockF_at block_115_1488 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1504 : treeBlockF 1504 1520 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1504 : ∀ j, 0 ≤ j → j < 1520 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1488 (fun _ h₁ h₂ => treeBlockF_at block_115_1504 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1520 : treeBlockF 1520 1536 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1520 : ∀ j, 0 ≤ j → j < 1536 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1504 (fun _ h₁ h₂ => treeBlockF_at block_115_1520 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1536 : treeBlockF 1536 1552 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1536 : ∀ j, 0 ≤ j → j < 1552 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1520 (fun _ h₁ h₂ => treeBlockF_at block_115_1536 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1552 : treeBlockF 1552 1568 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1552 : ∀ j, 0 ≤ j → j < 1568 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1536 (fun _ h₁ h₂ => treeBlockF_at block_115_1552 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1568 : treeBlockF 1568 1584 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1568 : ∀ j, 0 ≤ j → j < 1584 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1552 (fun _ h₁ h₂ => treeBlockF_at block_115_1568 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1584 : treeBlockF 1584 1600 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1584 : ∀ j, 0 ≤ j → j < 1600 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1568 (fun _ h₁ h₂ => treeBlockF_at block_115_1584 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1600 : treeBlockF 1600 1616 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1600 : ∀ j, 0 ≤ j → j < 1616 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1584 (fun _ h₁ h₂ => treeBlockF_at block_115_1600 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1616 : treeBlockF 1616 1632 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1616 : ∀ j, 0 ≤ j → j < 1632 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1600 (fun _ h₁ h₂ => treeBlockF_at block_115_1616 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1632 : treeBlockF 1632 1648 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1632 : ∀ j, 0 ≤ j → j < 1648 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1616 (fun _ h₁ h₂ => treeBlockF_at block_115_1632 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1648 : treeBlockF 1648 1664 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1648 : ∀ j, 0 ≤ j → j < 1664 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1632 (fun _ h₁ h₂ => treeBlockF_at block_115_1648 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1664 : treeBlockF 1664 1680 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1664 : ∀ j, 0 ≤ j → j < 1680 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1648 (fun _ h₁ h₂ => treeBlockF_at block_115_1664 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1680 : treeBlockF 1680 1696 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1680 : ∀ j, 0 ≤ j → j < 1696 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1664 (fun _ h₁ h₂ => treeBlockF_at block_115_1680 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1696 : treeBlockF 1696 1712 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1696 : ∀ j, 0 ≤ j → j < 1712 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1680 (fun _ h₁ h₂ => treeBlockF_at block_115_1696 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1712 : treeBlockF 1712 1728 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1712 : ∀ j, 0 ≤ j → j < 1728 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1696 (fun _ h₁ h₂ => treeBlockF_at block_115_1712 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1728 : treeBlockF 1728 1744 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1728 : ∀ j, 0 ≤ j → j < 1744 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1712 (fun _ h₁ h₂ => treeBlockF_at block_115_1728 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1744 : treeBlockF 1744 1760 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1744 : ∀ j, 0 ≤ j → j < 1760 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1728 (fun _ h₁ h₂ => treeBlockF_at block_115_1744 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1760 : treeBlockF 1760 1776 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1760 : ∀ j, 0 ≤ j → j < 1776 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1744 (fun _ h₁ h₂ => treeBlockF_at block_115_1760 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1776 : treeBlockF 1776 1792 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1776 : ∀ j, 0 ≤ j → j < 1792 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1760 (fun _ h₁ h₂ => treeBlockF_at block_115_1776 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1792 : treeBlockF 1792 1808 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1792 : ∀ j, 0 ≤ j → j < 1808 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1776 (fun _ h₁ h₂ => treeBlockF_at block_115_1792 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1808 : treeBlockF 1808 1824 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1808 : ∀ j, 0 ≤ j → j < 1824 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1792 (fun _ h₁ h₂ => treeBlockF_at block_115_1808 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1824 : treeBlockF 1824 1840 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1824 : ∀ j, 0 ≤ j → j < 1840 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1808 (fun _ h₁ h₂ => treeBlockF_at block_115_1824 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1840 : treeBlockF 1840 1856 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1840 : ∀ j, 0 ≤ j → j < 1856 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1824 (fun _ h₁ h₂ => treeBlockF_at block_115_1840 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1856 : treeBlockF 1856 1872 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1856 : ∀ j, 0 ≤ j → j < 1872 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1840 (fun _ h₁ h₂ => treeBlockF_at block_115_1856 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1872 : treeBlockF 1872 1888 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1872 : ∀ j, 0 ≤ j → j < 1888 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1856 (fun _ h₁ h₂ => treeBlockF_at block_115_1872 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_115_1888 : treeBlockF 1888 1894 (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) = true := by decide +kernel

theorem join_115_1888 : ∀ j, 0 ≤ j → j < 1894 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := block_join join_115_1872 (fun _ h₁ h₂ => treeBlockF_at block_115_1888 h₁ h₂)

theorem nc_115 : ∀ j, 0 ≤ j → j < 1894 → (dagCheckNodeF fullMask g_115 bds_115 1894 (dagTraceF fullMask rootStock 11 f_115) l_115) j = true := join_115_1888

theorem lb_115 : LowerBin fullMask rootStock g_115 12 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_115 sub_115 gl_115 rc_115 nc_115

def wg : List Gate := [⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [6, 0]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [2, 12]⟩, ⟨GateOp.or, [7, 13]⟩, ⟨GateOp.and, [4, 14]⟩, ⟨GateOp.or, [11, 15]⟩, ⟨GateOp.and, [9, 16]⟩, ⟨GateOp.or, [8, 17]⟩]

theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxHeartbeats 0 in
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276677288 * 2 ^ 32 + 4008241312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276677288 * 2 ^ 32 + 4008241312)) (13 - 1) := lb_115

end PEqualNP.Outside.L_meta_45276

theorem PEqualNP.Outside.L_meta_45276 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677288 * 2 ^ 32 + 4008241312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677288 * 2 ^ 32 + 4008241312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_45276.table2_from_lowerBin (4276677288 * 2 ^ 32 + 4008241312) 13 PEqualNP.Outside.L_meta_45276.root_lb PEqualNP.Outside.L_meta_45276.wg 18 rfl PEqualNP.Outside.L_meta_45276.wfits PEqualNP.Outside.L_meta_45276.weval
