import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_44806

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

abbrev ReplayState := Nat × List Nat × List (Nat × Nat × Nat)

def RefTransfers (mask goal count : Nat) (states : Nat → Option ReplayState)
    (reference : Nat → Nat → ReplayState → Bool) : Prop :=
  ∀ parent token current, reference parent token current = true →
    ∃ dest saved, dest < count ∧ states dest = some saved ∧ saved.1 = current.1 ∧
      ∀ k, LiveBin mask goal k current.2.1.toFinset → LiveBin mask goal k saved.2.1.toFinset

theorem plainRefTransfers (mask goal count : Nat) (states : Nat → Option ReplayState)
    (links : Nat → Nat → Option Nat) :
    RefTransfers mask goal count states (dagRef count states links) := by
  intro parent token current h
  unfold dagRef at h
  cases he : links parent token with
  | none => simp [he] at h
  | some dest =>
    simp only [he, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨hlt, hmatch⟩ := h
    cases hs : states dest with
    | none => simp [hs] at hmatch
    | some saved =>
      simp only [hs, Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at hmatch
      exact ⟨dest, saved, hlt, hs, hmatch.1, fun _ hLive => hmatch.2 ▸ hLive⟩

def dagCheckNodeWith (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option ReplayState) (reference : Nat → Nat → ReplayState → Bool)
    (i : Nat) : Bool :=
  match states i with
  | none => false
  | some st => dagCheckChildren mask goal bounds (reference (i + 1)) st

theorem dagAllNodesWith {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {reference : Nat → Nat → ReplayState → Bool}
    (hrefs : RefTransfers mask goal count (dagTrace mask stock fuel forest) reference)
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1) (snd : stock.Nodup)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeWith mask goal bounds
      (dagTrace mask stock fuel forest) reference i = true) :
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
    unfold dagCheckNodeWith at hchk
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
          · obtain ⟨dest, saved, hdest, htr2, hfEq, hMove⟩ :=
              hrefs (i + 1) (makeToken a b op keep) _ href
            have hbelow : rem - 1 < cap := by omega
            exact ih (rem - 1) hbelow dest saved hdest htr2 hfEq k' (by omega) (hMove k' hlive')

theorem lowerDagWith {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {reference : Nat → Nat → ReplayState → Bool}
    (hrefs : RefTransfers mask goal count (dagTrace mask stock fuel forest) reference)
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hroots : dagCheckRoots mask goal bounds
      (reference 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeWith mask goal bounds
      (dagTrace mask stock fuel forest) reference i = true) :
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
  · obtain ⟨dest, saved, hdest, htr, hfEq, hMove⟩ := hrefs 0 tok _ href
    exact dagAllNodesWith hrefs hgm hknown hsub snd hnodes fuel dest saved hdest htr hfEq k
      (by omega) (hMove k hlive')

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
    LowerBin mask stock goal (fuel + 1) :=
  lowerDagWith (plainRefTransfers mask goal count (dagTrace mask stock fuel forest) links)
    hgm hgnz hcs snd hknown hsub hroots hnodes

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

def swapIndex (i : Nat) : Nat :=
  if i < 64 then if i.testBit 3 == i.testBit 4 then i else i ^^^ 24 else i

def swapWord (w : Nat) : Nat :=
  (((w >>> 64) <<< 64) ||| (w &&& 0xff0000ffff0000ff)) |||
    (((w &&& 0x0000ff000000ff00) <<< 8) ||| ((w &&& 0x00ff000000ff0000) >>> 8))

theorem swapIndex_inv (i : Nat) : swapIndex (swapIndex i) = i := by
  by_cases hi : i < 64
  · interval_cases i <;> decide
  · simp [swapIndex, hi]

theorem swapWord_bit (w i : Nat) : (swapWord w).testBit i = w.testBit (swapIndex i) := by
  by_cases hi : i < 64
  · interval_cases i <;>
      simp only [swapWord, Nat.testBit_or, Nat.testBit_and,
        Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
    all_goals norm_num [swapIndex, Nat.testBit, Nat.shiftRight_eq_div_pow]
  · have h64 : 64 ≤ i := by omega
    have h8 : 8 ≤ i := by omega
    have e64 : 64 + (i - 64) = i := by omega
    have hkeep : (0xff0000ffff0000ff : Nat).testBit i = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 0xff0000ffff0000ff < 2 ^ 64)
        (Nat.pow_le_pow_right (by decide) h64))
    have hlow : (0x0000ff000000ff00 : Nat).testBit (i - 8) = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 0x0000ff000000ff00 < 2 ^ 56)
        (Nat.pow_le_pow_right (by decide) (by omega)))
    have hhigh : (0x00ff000000ff0000 : Nat).testBit (8 + i) = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 0x00ff000000ff0000 < 2 ^ 64)
        (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [swapWord, swapIndex, hi, h64, h8, e64, hkeep, hlow, hhigh,
      Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]

theorem swapWord_inv (w : Nat) : swapWord (swapWord w) = w := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [swapWord_bit, swapIndex_inv]

theorem swapWord_injective : Function.Injective swapWord :=
  fun _ _ h => by simpa only [swapWord_inv] using congrArg swapWord h

theorem swapWord_and (x y : Nat) : swapWord (x &&& y) = swapWord x &&& swapWord y := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [swapWord_bit, Nat.testBit_and]

theorem swapWord_or (x y : Nat) : swapWord (x ||| y) = swapWord x ||| swapWord y := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [swapWord_bit, Nat.testBit_or]

theorem swapWord_xor (x y : Nat) : swapWord (x ^^^ y) = swapWord x ^^^ swapWord y := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [swapWord_bit, Nat.testBit_xor]

theorem swapWord_zero : swapWord 0 = 0 := by decide +kernel

theorem canonByTopBit {mask top : Nat} (hp : mask = 2 ^ (top + 1) - 1) (w : Nat) :
    canon mask w =
      if (w &&& mask).testBit top then mask ^^^ (w &&& mask) else w &&& mask := by
  unfold canon; dsimp only
  set v := w &&& mask
  have hhigh (j : Nat) (hj : top < j) :
      v.testBit j = (mask ^^^ v).testBit j := by
    have hj' : ¬ j < top + 1 := by omega
    have hb : mask.testBit j = false := by
      rw [hp, Nat.testBit_two_pow_sub_one]
      simp [hj']
    simp [Nat.testBit_xor, hb]
  have hone : mask.testBit top = true := by
    rw [hp, Nat.testBit_two_pow_sub_one]
    simp
  by_cases hz : v = 0
  · rw [hz]
    simp [bsel]
  by_cases hf : v = mask
  · rw [hf]
    simp [bsel, hone]
  rw [beq_false_ne hz, beq_false_ne hf]
  simp only [Bool.or_false, bsel_false]
  cases hbit : v.testBit top
  · have hv : (mask ^^^ v).testBit top = true := by
      simp [Nat.testBit_xor, hone, hbit]
    have hlt := Nat.lt_of_testBit top hbit hv hhigh
    have hcheck : Nat.blt v (mask ^^^ v) = true := by simpa only [Nat.blt_eq] using hlt
    simp [hcheck, bsel]
  · have hv : (mask ^^^ v).testBit top = false := by
      simp [Nat.testBit_xor, hone, hbit]
    have hlt := Nat.lt_of_testBit top hv hbit (fun j hj => (hhigh j hj).symm)
    have hcheck : Nat.blt v (mask ^^^ v) = false := by
      cases hh : Nat.blt v (mask ^^^ v)
      · rfl
      · rw [Nat.blt_eq] at hh; omega
    simp [hcheck, bsel]

theorem swapWord_canon {mask top : Nat} (hp : mask = 2 ^ (top + 1) - 1)
    (hm : swapWord mask = mask) (ht : swapIndex top = top) (w : Nat) :
    swapWord (canon mask w) = canon mask (swapWord w) := by
  rw [canonByTopBit hp, canonByTopBit hp]
  have h : ((swapWord w) &&& mask).testBit top = (w &&& mask).testBit top := by
    rw [← hm, ← swapWord_and, swapWord_bit, ht, hm]
  rw [h]
  by_cases htop : (w &&& mask).testBit top = true <;>
    simp [htop, swapWord_xor, swapWord_and, hm]

theorem swapWord_gate {mask top : Nat} (hp : mask = 2 ^ (top + 1) - 1)
    (hm : swapWord mask = mask) (ht : swapIndex top = top) (op a b : Nat) :
    swapWord (binOp mask op a b) = binOp mask op (swapWord a) (swapWord b) := by
  unfold binOp
  simp only [bsel]
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;>
    simp [swapWord_canon hp hm ht, swapWord_and, swapWord_or, swapWord_xor, hm]

theorem swapWord_drop (keep : Bool) (w : Nat) (S : Finset Nat) :
    (dropIf keep w S).image swapWord = dropIf keep (swapWord w) (S.image swapWord) := by
  cases keep <;> simp [dropIf, Finset.image_erase swapWord_injective]

theorem swapLiveBin {mask top goal fuel : Nat} {S : Finset Nat}
    (hp : mask = 2 ^ (top + 1) - 1) (hm : swapWord mask = mask) (ht : swapIndex top = top)
    (g : swapWord goal = goal)
    (h : LiveBin mask goal fuel S) : LiveBin mask goal fuel (S.image swapWord) := by
  induction h with
  | done => simpa only [Finset.image_singleton, g] using (LiveBin.done (mask := mask) (goal := goal))
  | @step k T a b op ha hb hab ha0 hb0 hop hz hf keepA keepB tail ih =>
    refine LiveBin.step (a := swapWord a) (b := swapWord b) (op := op)
      (Finset.mem_image_of_mem _ ha) (Finset.mem_image_of_mem _ hb)
      (swapWord_injective.ne hab) ?_ ?_ hop ?_ ?_ keepA keepB ?_
    · intro h; exact ha0 (swapWord_injective (h.trans swapWord_zero.symm))
    · intro h; exact hb0 (swapWord_injective (h.trans swapWord_zero.symm))
    · rw [← swapWord_gate hp hm ht]
      intro h; exact hz (swapWord_injective (h.trans swapWord_zero.symm))
    · rw [← swapWord_gate hp hm ht]
      intro h
      obtain ⟨x, hx, eq⟩ := Finset.mem_image.mp h
      exact hf ((swapWord_injective eq) ▸ hx)
    · simpa only [Finset.image_insert, swapWord_drop, swapWord_gate hp hm ht] using ih

def swapBankF (saved current : List Nat) : Bool :=
  Bool.rec false (allN (fun w => memN (swapWord w) current) saved)
    (allN (fun w => memN (swapWord w) saved) current)

theorem swapBank_image {saved current : List Nat} (h : swapBankF saved current = true) :
    current.toFinset.image swapWord = saved.toFinset := by
  unfold swapBankF at h
  have hboth : (allN (fun w => memN (swapWord w) saved) current) = true ∧
      (allN (fun w => memN (swapWord w) current) saved) = true := by
    cases ht : allN (fun w => memN (swapWord w) saved) current
    · rw [ht] at h; contradiction
    · rw [ht] at h; exact ⟨rfl, h⟩
  simp only [allN_eq, memN_eq, List.all_eq_true, List.contains_iff_mem] at hboth
  ext v; constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact List.mem_toFinset.mpr (hboth.1 w (List.mem_toFinset.mp hw))
  · intro hv
    exact Finset.mem_image.mpr
      ⟨swapWord v, List.mem_toFinset.mpr (hboth.2 v (List.mem_toFinset.mp hv)), swapWord_inv v⟩

def dagRefSwapF (count : Nat) (states : Nat → Option ReplayState)
    (links : Nat → Nat → Option Nat) (parent token : Nat) (current : ReplayState) : Bool :=
  match links parent token with
  | none => false
  | some code =>
    let dest := Nat.shiftRight code 1
    Bool.rec false
      (match states dest with
       | none => false
       | some saved =>
         Bool.rec false
           (Bool.rec (eqListN saved.2.1 current.2.1) (swapBankF saved.2.1 current.2.1)
             (Nat.testBit code 0))
           (Nat.beq saved.1 current.1))
      (Nat.blt dest count)

theorem swapRefTransfers {mask top goal count : Nat} (hp : mask = 2 ^ (top + 1) - 1)
    (hm : swapWord mask = mask) (ht : swapIndex top = top) (hfix : swapWord goal = goal)
    (states : Nat → Option ReplayState) (links : Nat → Nat → Option Nat) :
    RefTransfers mask goal count states (dagRefSwapF count states links) := by
  intro parent token current h
  unfold dagRefSwapF at h
  cases he : links parent token with
  | none => rw [he] at h; contradiction
  | some code =>
    rw [he] at h
    let dest := Nat.shiftRight code 1
    change Bool.rec false _ (Nat.blt dest count) = true at h
    cases hb : Nat.blt dest count
    · rw [hb] at h; contradiction
    · rw [hb] at h
      have hlt : dest < count := by simpa only [Nat.blt_eq] using hb
      cases hs : states dest with
      | none =>
        change (match states dest with | none => false | some _ => _) = true at h
        rw [hs] at h
        contradiction
      | some saved =>
        change (match states dest with | none => false | some _ => _) = true at h
        rw [hs] at h
        change Bool.rec false _ (Nat.beq saved.1 current.1) = true at h
        cases hf : Nat.beq saved.1 current.1
        · rw [hf] at h; contradiction
        · rw [hf] at h
          have hFuel := Nat.beq_eq.mp hf
          refine ⟨dest, saved, hlt, hs, hFuel, ?_⟩
          intro k hLive
          change Bool.rec (eqListN saved.2.1 current.2.1)
            (swapBankF saved.2.1 current.2.1) (Nat.testBit code 0) = true at h
          cases hz : Nat.testBit code 0
          · rw [hz] at h
            change eqListN saved.2.1 current.2.1 = true at h
            rw [eqListN_eq, beq_iff_eq] at h
            exact h ▸ hLive
          · rw [hz] at h
            change swapBankF saved.2.1 current.2.1 = true at h
            simpa only [swapBank_image h] using swapLiveBin hp hm ht hfix hLive

def dagCheckNodeWithF (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option ReplayState) (reference : Nat → Nat → ReplayState → Bool)
    (i : Nat) : Bool :=
  match states i with
  | none => false
  | some st => dagCheckChildrenF mask goal bounds (reference (Nat.add i 1)) st

theorem dagCheckNodeWithF_eq {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (states : Nat → Option ReplayState) (reference : Nat → Nat → ReplayState → Bool) (i : Nat) :
    dagCheckNodeWithF mask goal bounds states reference i =
      dagCheckNodeWith mask goal bounds states reference i := by
  unfold dagCheckNodeWithF dagCheckNodeWith
  cases states i with
  | none => rfl
  | some state => exact dagCheckChildrenF_eq hgoals _ state

theorem lowerDagSwapF {mask top goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {links : Nat → Nat → Option Nat}
    (hp : mask = 2 ^ (top + 1) - 1) (hm : swapWord mask = mask) (ht : swapIndex top = top)
    (hfix : swapWord goal = goal) (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hroots : dagCheckRootsF mask goal bounds
      (dagRefSwapF count (dagTraceF mask stock fuel forest) links 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeWithF mask goal bounds
      (dagTraceF mask stock fuel forest)
      (dagRefSwapF count (dagTraceF mask stock fuel forest) links) i = true) :
    LowerBin mask stock goal (fuel + 1) := by
  have htr : dagTraceF mask stock fuel forest = dagTrace mask stock fuel forest := by
    funext i; exact dagTraceF_eq mask stock fuel forest i
  rw [htr, dagCheckRootsF_eq hgoals] at hroots
  rw [htr] at hnodes
  refine lowerDagWith (swapRefTransfers hp hm ht hfix _ _) hgm hgnz hcs snd hknown hsub hroots ?_
  intro i hlo hhi
  simpa only [dagCheckNodeWithF_eq hgoals] using hnodes i hlo hhi

def f_17 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_17 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
def m_17 : Nat := 0xf0f0
def s_17 : List Nat := [0x5050, 0x3030, 0xf0]
def g_17 : Nat := 0x1070
def bds_17 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_17 : KnownBin bds_17 := by
  intro b hb
  simp [bds_17] at hb
theorem sub_17 : ∀ b ∈ bds_17, m_17 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_17] at hb
theorem gl_17 : ∀ b ∈ bds_17, canon b.1 g_17 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_17] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsF m_17 g_17 bds_17 (dagRefF 1 (dagTraceF m_17 s_17 3 f_17) l_17 0) s_17 3 = true := by decide +kernel
def node_17 : Nat → Bool := dagCheckNodeF m_17 g_17 bds_17 1 (dagTraceF m_17 s_17 3 f_17) l_17
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_17_0 : treeBlockF 0 1 node_17 = true := by decide +kernel
theorem nc_17 : ∀ j, 0 ≤ j → j < 1 → node_17 j = true :=
  (certBlock nb_17_0)
theorem lb_17 : LowerBin m_17 s_17 g_17 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_17 sub_17 gl_17 rc_17 nc_17

def m_45 : Nat := 0xf000f0
def s_45 : List Nat := [0x500050, 0x300030, 0xf0]
def g_45 : Nat := 0x100070
theorem lb_45 : LowerBin m_45 s_45 g_45 4 := by
  refine lowerByRows [0, 0, 0, 0, 4, 5, 6, 7, 0, 0, 0, 0, 20, 21, 22, 23] (by decide +kernel) ?_ (by decide +kernel) lb_17
  intro w hw
  simp only [s_45, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_109 : Nat := 0x22222222
def s_109 : List Nat := [0x2020202, 0x220022, 0x2222]
def g_109 : Nat := 0x20222
theorem lb_109 : LowerBin m_109 s_109 g_109 4 := by
  refine lowerByRows [0, 0, 0, 0, 1, 5, 9, 13, 0, 0, 0, 0, 17, 21, 25, 29] (by decide +kernel) ?_ (by decide +kernel) lb_17
  intro w hw
  simp only [s_109, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_123 : Nat := 0x30303030
def s_123 : List Nat := [0x10101010, 0x300030, 0x3030]
def g_123 : Nat := 0x101030
theorem lb_123 : LowerBin m_123 s_123 g_123 4 := by
  refine lowerByRows [0, 0, 0, 0, 4, 5, 12, 13, 0, 0, 0, 0, 20, 21, 28, 29] (by decide +kernel) ?_ (by decide +kernel) lb_17
  intro w hw
  simp only [s_123, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_128 : Nat := 0x33003300
def s_128 : List Nat := [0x11001100, 0x3000300, 0x3300]
def g_128 : Nat := 0x1001300
theorem lb_128 : LowerBin m_128 s_128 g_128 4 := by
  refine lowerByRows [0, 0, 0, 0, 8, 9, 12, 13, 0, 0, 0, 0, 24, 25, 28, 29] (by decide +kernel) ?_ (by decide +kernel) lb_17
  intro w hw
  simp only [s_128, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_130 : Nat := 0x33330000
def s_130 : List Nat := [0x11110000, 0x3030000, 0x330000]
def g_130 : Nat := 0x1130000
theorem lb_130 : LowerBin m_130 s_130 g_130 4 := by
  refine lowerByRows [0, 0, 0, 0, 16, 17, 20, 21, 0, 0, 0, 0, 24, 25, 28, 29] (by decide +kernel) ?_ (by decide +kernel) lb_17
  intro w hw
  simp only [s_130, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_141 : Nat := 0x44444444
def s_141 : List Nat := [0x4040404, 0x440044, 0x4444]
def g_141 : Nat := 0x40444
theorem lb_141 : LowerBin m_141 s_141 g_141 4 := by
  refine lowerByRows [0, 0, 0, 0, 2, 6, 10, 14, 0, 0, 0, 0, 18, 22, 26, 30] (by decide +kernel) ?_ (by decide +kernel) lb_17
  intro w hw
  simp only [s_141, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_147 : Nat := 0x48484848
def s_147 : List Nat := [0x8080808, 0x480048, 0x4848]
def g_147 : Nat := 0x80848
theorem lb_147 : LowerBin m_147 s_147 g_147 4 := by
  refine lowerByRows [0, 0, 0, 0, 3, 6, 11, 14, 0, 0, 0, 0, 19, 22, 27, 30] (by decide +kernel) ?_ (by decide +kernel) lb_17
  intro w hw
  simp only [s_147, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_152 : Nat := 0x50505050
def s_152 : List Nat := [0x10101010, 0x500050, 0x5050]
def g_152 : Nat := 0x101050
theorem lb_152 : LowerBin m_152 s_152 g_152 4 := by
  refine lowerByRows [0, 0, 0, 0, 4, 6, 12, 14, 0, 0, 0, 0, 20, 22, 28, 30] (by decide +kernel) ?_ (by decide +kernel) lb_17
  intro w hw
  simp only [s_152, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_157 : Nat := 0x55005500
def s_157 : List Nat := [0x11001100, 0x5000500, 0x5500]
def g_157 : Nat := 0x1001500
theorem lb_157 : LowerBin m_157 s_157 g_157 4 := by
  refine lowerByRows [0, 0, 0, 0, 8, 10, 12, 14, 0, 0, 0, 0, 24, 26, 28, 30] (by decide +kernel) ?_ (by decide +kernel) lb_17
  intro w hw
  simp only [s_157, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_159 : Nat := 0x55550000
def s_159 : List Nat := [0x11110000, 0x5050000, 0x550000]
def g_159 : Nat := 0x1150000
theorem lb_159 : LowerBin m_159 s_159 g_159 4 := by
  refine lowerByRows [0, 0, 0, 0, 16, 18, 20, 22, 0, 0, 0, 0, 24, 26, 28, 30] (by decide +kernel) ?_ (by decide +kernel) lb_17
  intro w hw
  simp only [s_159, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_260 : Nat := 0xcc000000cc
def s_260 : List Nat := [0x4400000044, 0xc0000000c, 0xcc]
def g_260 : Nat := 0x40000004c
theorem lb_260 : LowerBin m_260 s_260 g_260 4 := by
  refine lowerByRows [0, 0, 0, 0, 2, 3, 6, 7, 0, 0, 0, 0, 34, 35, 38, 39] (by decide +kernel) ?_ (by decide +kernel) lb_17
  intro w hw
  simp only [s_260, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_267 : Nat := 0xf0000000f0
def s_267 : List Nat := [0x5000000050, 0x3000000030, 0xf0]
def g_267 : Nat := 0x1000000070
theorem lb_267 : LowerBin m_267 s_267 g_267 4 := by
  refine lowerByRows [0, 0, 0, 0, 4, 5, 6, 7, 0, 0, 0, 0, 36, 37, 38, 39] (by decide +kernel) ?_ (by decide +kernel) lb_17
  intro w hw
  simp only [s_267, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_340 : Nat := 0x112200004488
def s_340 : List Nat := [0x2200000088, 0x4488, 0x10200000408]
def g_340 : Nat := 0x2200004080
def bds_340 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_340 : KnownBin bds_340 := by
  intro b hb
  simp [bds_340] at hb
theorem sub_340 : ∀ b ∈ bds_340, m_340 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_340] at hb
theorem gl_340 : ∀ b ∈ bds_340, canon b.1 g_340 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_340] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_340 : dagCheckRootsF m_340 g_340 bds_340 (dagRefF 1 (dagTraceF m_340 s_340 2 f_17) l_17 0) s_340 2 = true := by decide +kernel
def node_340 : Nat → Bool := dagCheckNodeF m_340 g_340 bds_340 1 (dagTraceF m_340 s_340 2 f_17) l_17
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_340_0 : treeBlockF 0 1 node_340 = true := by decide +kernel
theorem nc_340 : ∀ j, 0 ≤ j → j < 1 → node_340 j = true :=
  (certBlock nb_340_0)
theorem lb_340 : LowerBin m_340 s_340 g_340 3 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_340 sub_340 gl_340 rc_340 nc_340

def f_347 : Nat → Nat × Nat := unpackForestF 0xc1832a326219424211007 3 9
def l_347 : Nat → Nat → Option Nat := unpackLinksF 0xe31c30c29301 0xc18424b2a926619211007 6 3 9 3 4
def m_347 : Nat := 0x121200004848
def s_347 : List Nat := [0x20200000808, 0x4848, 0x1200000048]
def g_347 : Nat := 0x20200004000
def bds_347 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_347 : KnownBin bds_347 := by
  intro b hb
  simp [bds_347] at hb
theorem sub_347 : ∀ b ∈ bds_347, m_347 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_347] at hb
theorem gl_347 : ∀ b ∈ bds_347, canon b.1 g_347 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_347] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_347 : dagCheckRootsF m_347 g_347 bds_347 (dagRefF 7 (dagTraceF m_347 s_347 3 f_347) l_347 0) s_347 3 = true := by decide +kernel
def node_347 : Nat → Bool := dagCheckNodeF m_347 g_347 bds_347 7 (dagTraceF m_347 s_347 3 f_347) l_347
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_347_0 : treeBlockF 0 7 node_347 = true := by decide +kernel
theorem nc_347 : ∀ j, 0 ≤ j → j < 7 → node_347 j = true :=
  (certBlock nb_347_0)
theorem lb_347 : LowerBin m_347 s_347 g_347 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_347 sub_347 gl_347 rc_347 nc_347

def m_405 : Nat := 0x444400004444
def s_405 : List Nat := [0x40400000404, 0x4400000044, 0x4444]
def g_405 : Nat := 0x400000444
theorem lb_405 : LowerBin m_405 s_405 g_405 4 := by
  refine lowerByRows [0, 0, 0, 0, 2, 6, 10, 14, 0, 0, 0, 0, 34, 38, 42, 46] (by decide +kernel) ?_ (by decide +kernel) lb_17
  intro w hw
  simp only [s_405, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_606 : Nat := 0x11002200440088
def s_606 : List Nat := [0x2200000088, 0x440088, 0x1000200040008]
def g_606 : Nat := 0x2200400080
theorem lb_606 : LowerBin m_606 s_606 g_606 3 := by
  refine lowerByRows [0, 0, 0, 3, 0, 0, 0, 7, 0, 0, 18, 0, 0, 0, 22, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 37, 0, 0, 48, 0, 0, 0, 52] (by decide +kernel) ?_ (by decide +kernel) lb_340
  intro w hw
  simp only [s_606, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_617 : Nat := 0x12001200480048
def s_617 : List Nat := [0x2000200080008, 0x480048, 0x1200000048]
def g_617 : Nat := 0x2000200400000
theorem lb_617 : LowerBin m_617 s_617 g_617 4 := by
  refine lowerByRows [0, 0, 0, 3, 0, 0, 6, 0, 0, 0, 0, 19, 0, 0, 22, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 36, 0, 0, 0, 0, 49, 0, 0, 52] (by decide +kernel) ?_ (by decide +kernel) lb_347
  intro w hw
  simp only [s_617, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_622 : Nat → Nat × Nat := unpackForestF 0x32d32592c21a424216007 3 9
def l_622 : Nat → Nat → Option Nat := unpackLinksF 0x82e5c3160a4601 0x81841492c424d2db2561a216007 7 3 9 3 4
def m_622 : Nat := 0x14001400280028
def s_622 : List Nat := [0x280028, 0x4000400080008, 0x1400000028]
def g_622 : Nat := 0x4000000200000
def bds_622 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_622 : KnownBin bds_622 := by
  intro b hb
  simp [bds_622] at hb
theorem sub_622 : ∀ b ∈ bds_622, m_622 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_622] at hb
theorem gl_622 : ∀ b ∈ bds_622, canon b.1 g_622 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_622] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_622 : dagCheckRootsF m_622 g_622 bds_622 (dagRefF 7 (dagTraceF m_622 s_622 3 f_622) l_622 0) s_622 3 = true := by decide +kernel
def node_622 : Nat → Bool := dagCheckNodeF m_622 g_622 bds_622 7 (dagTraceF m_622 s_622 3 f_622) l_622
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_622_0 : treeBlockF 0 7 node_622 = true := by decide +kernel
theorem nc_622 : ∀ j, 0 ≤ j → j < 7 → node_622 j = true :=
  (certBlock nb_622_0)
theorem lb_622 : LowerBin m_622 s_622 g_622 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_622 sub_622 gl_622 rc_622 nc_622

def m_688 : Nat := 0x44004400440044
def s_688 : List Nat := [0x4000400040004, 0x4400000044, 0x440044]
def g_688 : Nat := 0x400040044
theorem lb_688 : LowerBin m_688 s_688 g_688 4 := by
  refine lowerByRows [0, 0, 0, 0, 2, 6, 18, 22, 0, 0, 0, 0, 34, 38, 50, 54] (by decide +kernel) ?_ (by decide +kernel) lb_17
  intro w hw
  simp only [s_688, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_845 : Nat := 0x101020204040808
def s_845 : List Nat := [0x20200000808, 0x4040808, 0x1000200040008]
def g_845 : Nat := 0x20204000000
theorem lb_845 : LowerBin m_845 s_845 g_845 4 := by
  refine lowerByRows [0, 0, 0, 3, 0, 0, 18, 0, 0, 0, 0, 11, 0, 0, 26, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 48, 0, 0, 0, 0, 41, 0, 0, 56] (by decide +kernel) ?_ (by decide +kernel) lb_347
  intro w hw
  simp only [s_845, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_943 : Nat := 0x404040404040404
def s_943 : List Nat := [0x4000400040004, 0x40400000404, 0x4040404]
def g_943 : Nat := 0x400040404
theorem lb_943 : LowerBin m_943 s_943 g_943 4 := by
  refine lowerByRows [0, 0, 0, 0, 2, 10, 18, 26, 0, 0, 0, 0, 34, 42, 50, 58] (by decide +kernel) ?_ (by decide +kernel) lb_17
  intro w hw
  simp only [s_943, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_944 : Nat := 0x404040408080808
def s_944 : List Nat := [0x8080808, 0x4000400080008, 0x40400000808]
def g_944 : Nat := 0x400080808
theorem lb_944 : LowerBin m_944 s_944 g_944 4 := by
  refine lowerByRows [0, 0, 0, 0, 3, 34, 11, 42, 0, 0, 0, 0, 19, 50, 27, 58] (by decide +kernel) ?_ (by decide +kernel) lb_17
  intro w hw
  simp only [s_944, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_970 : Nat := 0x50005000a000a00
def s_970 : List Nat := [0xa000a00, 0x100010002000200, 0x50000000a00]
def g_970 : Nat := 0x100010000000a00
theorem lb_970 : LowerBin m_970 s_970 g_970 3 := by
  refine lowerByRows [0, 0, 0, 11, 0, 0, 0, 27, 0, 0, 9, 0, 0, 0, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 42, 0, 0, 0, 58, 0, 0, 40, 0, 0, 0, 56] (by decide +kernel) ?_ (by decide +kernel) lb_340
  intro w hw
  simp only [s_970, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_983 : Nat := 0x50500000a0a0000
def s_983 : List Nat := [0xa0a0000, 0x101000002020000, 0x50000000a0000]
def g_983 : Nat := 0x1010000000a0000
theorem lb_983 : LowerBin m_983 s_983 g_983 3 := by
  refine lowerByRows [0, 0, 0, 19, 0, 0, 0, 27, 0, 0, 17, 0, 0, 0, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 0, 0, 0, 58, 0, 0, 48, 0, 0, 0, 56] (by decide +kernel) ?_ (by decide +kernel) lb_340
  intro w hw
  simp only [s_983, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_1136 : Nat := 0x1010101040404040
def s_1136 : List Nat := [0x40404040, 0x10001000400040, 0x101000004040]
def g_1136 : Nat := 0x10101000000040
theorem lb_1136 : LowerBin m_1136 s_1136 g_1136 4 := by
  refine lowerByRows [0, 0, 0, 0, 36, 6, 44, 14, 0, 0, 0, 0, 52, 22, 60, 30] (by decide +kernel) ?_ (by decide +kernel) lb_17
  intro w hw
  simp only [s_1136, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_1167 : Nat := 0x1100220044008800
def s_1167 : List Nat := [0x220000008800, 0x44008800, 0x100020004000800]
def g_1167 : Nat := 0x100000000000800
theorem lb_1167 : LowerBin m_1167 s_1167 g_1167 4 := by
  refine lowerByRows [0, 0, 0, 30, 0, 60, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 45, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 41] (by decide +kernel) ?_ (by decide +kernel) lb_622
  intro w hw
  simp only [s_1167, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_1177 : Nat := 0x1111000044440000
def s_1177 : List Nat := [0x44440000, 0x101000004040000, 0x11000000440000]
def g_1177 : Nat := 0x111000000040000
theorem lb_1177 : LowerBin m_1177 s_1177 g_1177 4 := by
  refine lowerByRows [0, 0, 0, 0, 48, 18, 52, 22, 0, 0, 0, 0, 56, 26, 60, 30] (by decide +kernel) ?_ (by decide +kernel) lb_17
  intro w hw
  simp only [s_1177, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_1198 : Nat := 0x1200120048004800
def s_1198 : List Nat := [0x200020008000800, 0x48004800, 0x120000004800]
def g_1198 : Nat := 0x100000000800
theorem lb_1198 : LowerBin m_1198 s_1198 g_1198 4 := by
  refine lowerByRows [0, 0, 0, 30, 0, 60, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 0, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27, 0, 57, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 41] (by decide +kernel) ?_ (by decide +kernel) lb_622
  intro w hw
  simp only [s_1198, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_1202 : Nat := 0x1212000048480000
def s_1202 : List Nat := [0x202000008080000, 0x48480000, 0x12000000480000]
def g_1202 : Nat := 0x10000000080000
theorem lb_1202 : LowerBin m_1202 s_1202 g_1202 4 := by
  refine lowerByRows [0, 0, 0, 30, 0, 60, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 0, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27, 0, 57, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 0, 49] (by decide +kernel) ?_ (by decide +kernel) lb_622
  intro w hw
  simp only [s_1202, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_1738 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1738 : Nat → Nat → Option Nat := fun _ _ => none
def m_1738 : Nat := 0xffff
def s_1738 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_1738 : Nat := 0x1f7f
def bds_1738 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 4, g_17)]
theorem kn_1738 : KnownBin bds_1738 := by
  intro b hb
  simp only [bds_1738, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_17
theorem sub_1738 : ∀ b ∈ bds_1738, m_1738 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1738, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1738 : ∀ b ∈ bds_1738, canon b.1 g_1738 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1738, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1738 : dagCheckRootsF m_1738 g_1738 bds_1738 (dagRefF 0 (dagTraceF m_1738 s_1738 4 f_1738) l_1738 0) s_1738 4 = true := by decide +kernel
def node_1738 : Nat → Bool := dagCheckNodeF m_1738 g_1738 bds_1738 0 (dagTraceF m_1738 s_1738 4 f_1738) l_1738
theorem nc_1738 : ∀ j, 0 ≤ j → j < 0 → node_1738 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1738 : LowerBin m_1738 s_1738 g_1738 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1738 sub_1738 gl_1738 rc_1738 nc_1738

def f_1739 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1739 : Nat → Nat → Option Nat := fun _ _ => none
def m_1739 : Nat := 0xff00ff
def s_1739 : List Nat := [0x550055, 0x330033, 0xf000f, 0xff]
def g_1739 : Nat := 0x1f007f
def bds_1739 : List (Nat × List Nat × Nat × Nat) := [(m_45, s_45, 4, g_45)]
theorem kn_1739 : KnownBin bds_1739 := by
  intro b hb
  simp only [bds_1739, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_45
theorem sub_1739 : ∀ b ∈ bds_1739, m_1739 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1739, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1739 : ∀ b ∈ bds_1739, canon b.1 g_1739 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1739, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1739 : dagCheckRootsF m_1739 g_1739 bds_1739 (dagRefF 0 (dagTraceF m_1739 s_1739 4 f_1739) l_1739 0) s_1739 4 = true := by decide +kernel
def node_1739 : Nat → Bool := dagCheckNodeF m_1739 g_1739 bds_1739 0 (dagTraceF m_1739 s_1739 4 f_1739) l_1739
theorem nc_1739 : ∀ j, 0 ≤ j → j < 0 → node_1739 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1739 : LowerBin m_1739 s_1739 g_1739 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1739 sub_1739 gl_1739 rc_1739 nc_1739

def f_1744 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def l_1744 : Nat → Nat → Option Nat := unpackLinksF 0x8e11c1fc3f07c2f81b43606c0d45a0b40662cc15c2b0542a8148a18420841009f13e0784f01d12b0540a814128050098921222440809001e21e00b001 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d347d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 11 4 10 6 5
def m_1744 : Nat := 0x33333333
def s_1744 : List Nat := [0x11111111, 0x3030303, 0x330033, 0x3333]
def g_1744 : Nat := 0x1131333
def bds_1744 : List (Nat × List Nat × Nat × Nat) := [(m_128, s_128, 4, g_128), (m_130, s_130, 4, g_130), (m_123, s_123, 4, g_123), (m_109, s_109, 4, g_109)]
theorem kn_1744 : KnownBin bds_1744 := by
  intro b hb
  simp only [bds_1744, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_128
  · exact lb_130
  · exact lb_123
  · exact lb_109
theorem sub_1744 : ∀ b ∈ bds_1744, m_1744 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1744, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_1744 : ∀ b ∈ bds_1744, canon b.1 g_1744 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1744, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1744 : dagCheckRootsF m_1744 g_1744 bds_1744 (dagRefF 43 (dagTraceF m_1744 s_1744 6 f_1744) l_1744 0) s_1744 6 = true := by decide +kernel
def node_1744 : Nat → Bool := dagCheckNodeF m_1744 g_1744 bds_1744 43 (dagTraceF m_1744 s_1744 6 f_1744) l_1744
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1744_0 : treeBlockF 0 43 node_1744 = true := by decide +kernel
theorem nc_1744 : ∀ j, 0 ≤ j → j < 43 → node_1744 j = true :=
  (certBlock nb_1744_0)
theorem lb_1744 : LowerBin m_1744 s_1744 g_1744 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1744 sub_1744 gl_1744 rc_1744 nc_1744

def m_1748 : Nat := 0x55555555
def s_1748 : List Nat := [0x11111111, 0x5050505, 0x550055, 0x5555]
def g_1748 : Nat := 0x1151555
theorem lb_1748 : LowerBin m_1748 s_1748 g_1748 7 := by
  refine lowerByRows [0, 2, 1, 1, 4, 6, 1, 1, 8, 10, 1, 1, 12, 14, 1, 1, 16, 18, 1, 1, 20, 22, 1, 1, 24, 26, 1, 1, 28, 30] (by decide +kernel) ?_ (by decide +kernel) lb_1744
  intro w hw
  simp only [s_1748, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_1757 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1757 : Nat → Nat → Option Nat := fun _ _ => none
def m_1757 : Nat := 0xaaaaaaaa
def s_1757 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_1757 : Nat := 0xa0a2a
def bds_1757 : List (Nat × List Nat × Nat × Nat) := [(m_109, s_109, 4, g_109)]
theorem kn_1757 : KnownBin bds_1757 := by
  intro b hb
  simp only [bds_1757, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_109
theorem sub_1757 : ∀ b ∈ bds_1757, m_1757 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1757, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1757 : ∀ b ∈ bds_1757, canon b.1 g_1757 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1757, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1757 : dagCheckRootsF m_1757 g_1757 bds_1757 (dagRefF 0 (dagTraceF m_1757 s_1757 4 f_1757) l_1757 0) s_1757 4 = true := by decide +kernel
def node_1757 : Nat → Bool := dagCheckNodeF m_1757 g_1757 bds_1757 0 (dagTraceF m_1757 s_1757 4 f_1757) l_1757
theorem nc_1757 : ∀ j, 0 ≤ j → j < 0 → node_1757 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1757 : LowerBin m_1757 s_1757 g_1757 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1757 sub_1757 gl_1757 rc_1757 nc_1757

def f_1758 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
def l_1758 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607227207206e26c16c06a16a06a06a06a06a06a06246206206206205a45a05a05625605605225015004e14e04e04e04e04e04e04644604604604603e43e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 12 5 10 6 6
def m_1758 : Nat := 0xc3c3c3c3
def s_1758 : List Nat := [0x41414141, 0x3030303, 0xc300c3, 0xc3c3]
def g_1758 : Nat := 0x1030343
def bds_1758 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_1758 : KnownBin bds_1758 := by
  intro b hb
  simp [bds_1758] at hb
theorem sub_1758 : ∀ b ∈ bds_1758, m_1758 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_1758] at hb
theorem gl_1758 : ∀ b ∈ bds_1758, canon b.1 g_1758 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_1758] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1758 : dagCheckRootsF m_1758 g_1758 bds_1758 (dagRefF 64 (dagTraceF m_1758 s_1758 5 f_1758) l_1758 0) s_1758 5 = true := by decide +kernel
def node_1758 : Nat → Bool := dagCheckNodeF m_1758 g_1758 bds_1758 64 (dagTraceF m_1758 s_1758 5 f_1758) l_1758
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1758_0 : treeBlockF 0 64 node_1758 = true := by decide +kernel
theorem nc_1758 : ∀ j, 0 ≤ j → j < 64 → node_1758 j = true :=
  (certBlock nb_1758_0)
theorem lb_1758 : LowerBin m_1758 s_1758 g_1758 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1758 sub_1758 gl_1758 rc_1758 nc_1758

def f_1761 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1761 : Nat → Nat → Option Nat := fun _ _ => none
def m_1761 : Nat := 0xcccccccc
def s_1761 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_1761 : Nat := 0xc0c4c
def bds_1761 : List (Nat × List Nat × Nat × Nat) := [(m_141, s_141, 4, g_141)]
theorem kn_1761 : KnownBin bds_1761 := by
  intro b hb
  simp only [bds_1761, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_141
theorem sub_1761 : ∀ b ∈ bds_1761, m_1761 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1761, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1761 : ∀ b ∈ bds_1761, canon b.1 g_1761 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1761, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1761 : dagCheckRootsF m_1761 g_1761 bds_1761 (dagRefF 0 (dagTraceF m_1761 s_1761 4 f_1761) l_1761 0) s_1761 4 = true := by decide +kernel
def node_1761 : Nat → Bool := dagCheckNodeF m_1761 g_1761 bds_1761 0 (dagTraceF m_1761 s_1761 4 f_1761) l_1761
theorem nc_1761 : ∀ j, 0 ≤ j → j < 0 → node_1761 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1761 : LowerBin m_1761 s_1761 g_1761 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1761 sub_1761 gl_1761 rc_1761 nc_1761

def m_1764 : Nat := 0xf0f0f0f0
def s_1764 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_1764 : Nat := 0x101070
theorem lb_1764 : LowerBin m_1764 s_1764 g_1764 7 := by
  refine lowerByRows [31, 30, 0, 0, 29, 28, 0, 0, 23, 22, 0, 0, 21, 20, 0, 0, 15, 14, 0, 0, 13, 12, 0, 0, 7, 6, 0, 0, 5, 4] (by decide +kernel) ?_ (by decide +kernel) lb_1744
  intro w hw
  simp only [s_1764, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_1765 : Nat := 0xff0000ff
def s_1765 : List Nat := [0x55000055, 0x33000033, 0xf00000f, 0xff]
def g_1765 : Nat := 0x100007f
theorem lb_1765 : LowerBin m_1765 s_1765 g_1765 6 := by
  refine lowerByRows [0, 1, 8, 8, 8, 8, 24, 25, 2, 3, 8, 8, 8, 8, 26, 27, 4, 5, 8, 8, 8, 8, 28, 29, 6, 7, 8, 8, 8, 8, 30, 31] (by decide +kernel) ?_ (by decide +kernel) lb_1758
  intro w hw
  simp only [s_1765, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_1766 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1766 : Nat → Nat → Option Nat := fun _ _ => none
def m_1766 : Nat := 0xff00ff00
def s_1766 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_1766 : Nat := 0x1001f00
def bds_1766 : List (Nat × List Nat × Nat × Nat) := [(m_157, s_157, 4, g_157)]
theorem kn_1766 : KnownBin bds_1766 := by
  intro b hb
  simp only [bds_1766, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_157
theorem sub_1766 : ∀ b ∈ bds_1766, m_1766 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1766, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1766 : ∀ b ∈ bds_1766, canon b.1 g_1766 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1766, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1766 : dagCheckRootsF m_1766 g_1766 bds_1766 (dagRefF 0 (dagTraceF m_1766 s_1766 4 f_1766) l_1766 0) s_1766 4 = true := by decide +kernel
def node_1766 : Nat → Bool := dagCheckNodeF m_1766 g_1766 bds_1766 0 (dagTraceF m_1766 s_1766 4 f_1766) l_1766
theorem nc_1766 : ∀ j, 0 ≤ j → j < 0 → node_1766 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1766 : LowerBin m_1766 s_1766 g_1766 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1766 sub_1766 gl_1766 rc_1766 nc_1766

def f_1767 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1767 : Nat → Nat → Option Nat := fun _ _ => none
def m_1767 : Nat := 0xffff0000
def s_1767 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_1767 : Nat := 0x11f0000
def bds_1767 : List (Nat × List Nat × Nat × Nat) := [(m_159, s_159, 4, g_159)]
theorem kn_1767 : KnownBin bds_1767 := by
  intro b hb
  simp only [bds_1767, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_159
theorem sub_1767 : ∀ b ∈ bds_1767, m_1767 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1767, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1767 : ∀ b ∈ bds_1767, canon b.1 g_1767 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1767, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1767 : dagCheckRootsF m_1767 g_1767 bds_1767 (dagRefF 0 (dagTraceF m_1767 s_1767 4 f_1767) l_1767 0) s_1767 4 = true := by decide +kernel
def node_1767 : Nat → Bool := dagCheckNodeF m_1767 g_1767 bds_1767 0 (dagTraceF m_1767 s_1767 4 f_1767) l_1767
theorem nc_1767 : ∀ j, 0 ≤ j → j < 0 → node_1767 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1767 : LowerBin m_1767 s_1767 g_1767 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1767 sub_1767 gl_1767 rc_1767 nc_1767

def f_1768 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1768 : Nat → Nat → Option Nat := fun _ _ => none
def m_1768 : Nat := 0xff000000ff
def s_1768 : List Nat := [0x5500000055, 0x3300000033, 0xf0000000f, 0xff]
def g_1768 : Nat := 0x150000007f
def bds_1768 : List (Nat × List Nat × Nat × Nat) := [(m_260, s_260, 4, g_260)]
theorem kn_1768 : KnownBin bds_1768 := by
  intro b hb
  simp only [bds_1768, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_260
theorem sub_1768 : ∀ b ∈ bds_1768, m_1768 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1768, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1768 : ∀ b ∈ bds_1768, canon b.1 g_1768 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1768, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1768 : dagCheckRootsF m_1768 g_1768 bds_1768 (dagRefF 0 (dagTraceF m_1768 s_1768 4 f_1768) l_1768 0) s_1768 4 = true := by decide +kernel
def node_1768 : Nat → Bool := dagCheckNodeF m_1768 g_1768 bds_1768 0 (dagTraceF m_1768 s_1768 4 f_1768) l_1768
theorem nc_1768 : ∀ j, 0 ≤ j → j < 0 → node_1768 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1768 : LowerBin m_1768 s_1768 g_1768 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1768 sub_1768 gl_1768 rc_1768 nc_1768

def f_1780 : Nat → Nat × Nat := unpackForestF 0xc7e18eeea65d40b88018de6944d24985018cc29f853b6c98d901a2005374a7894d120c0533385014bca0c052b0a4e28d0291800f 5 10
def l_1780 : Nat → Nat → Option Nat := unpackLinksF 0x1d0e8743a1d0d1e8341a0b9dc2e170b85c28740a0502271080c01e2e1703443801 0x654cc2817102a9451249850f931d2034405a78a4d120c1c282830248051a6e3fd47768de519c53f8276c4dd099992f2256349c291800f 9 4 10 5 5
def m_1780 : Nat := 0x333333330000
def s_1780 : List Nat := [0x111111110000, 0x30303030000, 0x3300330000, 0x33330000]
def g_1780 : Nat := 0x111101130000
def bds_1780 : List (Nat × List Nat × Nat × Nat) := [(m_130, s_130, 4, g_130)]
theorem kn_1780 : KnownBin bds_1780 := by
  intro b hb
  simp only [bds_1780, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_130
theorem sub_1780 : ∀ b ∈ bds_1780, m_1780 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1780, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1780 : ∀ b ∈ bds_1780, canon b.1 g_1780 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1780, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1780 : dagCheckRootsF m_1780 g_1780 bds_1780 (dagRefF 28 (dagTraceF m_1780 s_1780 5 f_1780) l_1780 0) s_1780 5 = true := by decide +kernel
def node_1780 : Nat → Bool := dagCheckNodeF m_1780 g_1780 bds_1780 28 (dagTraceF m_1780 s_1780 5 f_1780) l_1780
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1780_0 : treeBlockF 0 28 node_1780 = true := by decide +kernel
theorem nc_1780 : ∀ j, 0 ≤ j → j < 28 → node_1780 j = true :=
  (certBlock nb_1780_0)
theorem lb_1780 : LowerBin m_1780 s_1780 g_1780 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1780 sub_1780 gl_1780 rc_1780 nc_1780

def f_1786 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1786 : Nat → Nat → Option Nat := fun _ _ => none
def m_1786 : Nat := 0x555500005555
def s_1786 : List Nat := [0x111100001111, 0x50500000505, 0x5500000055, 0x5555]
def g_1786 : Nat := 0x111500001555
def bds_1786 : List (Nat × List Nat × Nat × Nat) := [(m_405, s_405, 4, g_405)]
theorem kn_1786 : KnownBin bds_1786 := by
  intro b hb
  simp only [bds_1786, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_405
theorem sub_1786 : ∀ b ∈ bds_1786, m_1786 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1786, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1786 : ∀ b ∈ bds_1786, canon b.1 g_1786 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1786, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1786 : dagCheckRootsF m_1786 g_1786 bds_1786 (dagRefF 0 (dagTraceF m_1786 s_1786 4 f_1786) l_1786 0) s_1786 4 = true := by decide +kernel
def node_1786 : Nat → Bool := dagCheckNodeF m_1786 g_1786 bds_1786 0 (dagTraceF m_1786 s_1786 4 f_1786) l_1786
theorem nc_1786 : ∀ j, 0 ≤ j → j < 0 → node_1786 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1786 : LowerBin m_1786 s_1786 g_1786 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1786 sub_1786 gl_1786 rc_1786 nc_1786

def m_1798 : Nat := 0xa5a50000a5a5
def s_1798 : List Nat := [0x50500000505, 0x212100002121, 0xa5000000a5, 0xa5a5]
def g_1798 : Nat := 0x10500000525
theorem lb_1798 : LowerBin m_1798 s_1798 g_1798 6 := by
  refine lowerByRows [0, 2, 1, 1, 1, 1, 5, 7, 8, 10, 1, 1, 1, 1, 13, 15, 32, 34, 1, 1, 1, 1, 37, 39, 40, 42, 1, 1, 1, 1, 45, 47] (by decide +kernel) ?_ (by decide +kernel) lb_1758
  intro w hw
  simp only [s_1798, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_1811 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1811 : Nat → Nat → Option Nat := fun _ _ => none
def m_1811 : Nat := 0xcccc0000cccc
def s_1811 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_1811 : Nat := 0x400000c4c
def bds_1811 : List (Nat × List Nat × Nat × Nat) := [(m_405, s_405, 4, g_405)]
theorem kn_1811 : KnownBin bds_1811 := by
  intro b hb
  simp only [bds_1811, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_405
theorem sub_1811 : ∀ b ∈ bds_1811, m_1811 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1811, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1811 : ∀ b ∈ bds_1811, canon b.1 g_1811 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1811, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1811 : dagCheckRootsF m_1811 g_1811 bds_1811 (dagRefF 0 (dagTraceF m_1811 s_1811 4 f_1811) l_1811 0) s_1811 4 = true := by decide +kernel
def node_1811 : Nat → Bool := dagCheckNodeF m_1811 g_1811 bds_1811 0 (dagTraceF m_1811 s_1811 4 f_1811) l_1811
theorem nc_1811 : ∀ j, 0 ≤ j → j < 0 → node_1811 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1811 : LowerBin m_1811 s_1811 g_1811 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1811 sub_1811 gl_1811 rc_1811 nc_1811

def f_1817 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1817 : Nat → Nat → Option Nat := fun _ _ => none
def m_1817 : Nat := 0xf0f00000f0f0
def s_1817 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_1817 : Nat := 0x101000001070
def bds_1817 : List (Nat × List Nat × Nat × Nat) := [(m_267, s_267, 4, g_267)]
theorem kn_1817 : KnownBin bds_1817 := by
  intro b hb
  simp only [bds_1817, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_267
theorem sub_1817 : ∀ b ∈ bds_1817, m_1817 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1817, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1817 : ∀ b ∈ bds_1817, canon b.1 g_1817 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1817, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1817 : dagCheckRootsF m_1817 g_1817 bds_1817 (dagRefF 0 (dagTraceF m_1817 s_1817 4 f_1817) l_1817 0) s_1817 4 = true := by decide +kernel
def node_1817 : Nat → Bool := dagCheckNodeF m_1817 g_1817 bds_1817 0 (dagTraceF m_1817 s_1817 4 f_1817) l_1817
theorem nc_1817 : ∀ j, 0 ≤ j → j < 0 → node_1817 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1817 : LowerBin m_1817 s_1817 g_1817 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1817 sub_1817 gl_1817 rc_1817 nc_1817

def m_1836 : Nat := 0x33003333003300
def s_1836 : List Nat := [0x11001111001100, 0x3000303000300, 0x33003300, 0x3300003300]
def g_1836 : Nat := 0x11001101001300
theorem lb_1836 : LowerBin m_1836 s_1836 g_1836 6 := by
  refine lowerByRows [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 24, 25, 0, 0, 28, 29, 0, 0, 32, 33, 0, 0, 36, 37, 0, 0, 48, 49, 0, 0, 52, 53] (by decide +kernel) ?_ (by decide +kernel) lb_1780
  intro w hw
  simp only [s_1836, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_1846 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1846 : Nat → Nat → Option Nat := fun _ _ => none
def m_1846 : Nat := 0x55005500550055
def s_1846 : List Nat := [0x11001100110011, 0x5000500050005, 0x5500000055, 0x550055]
def g_1846 : Nat := 0x11001500150055
def bds_1846 : List (Nat × List Nat × Nat × Nat) := [(m_688, s_688, 4, g_688)]
theorem kn_1846 : KnownBin bds_1846 := by
  intro b hb
  simp only [bds_1846, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_688
theorem sub_1846 : ∀ b ∈ bds_1846, m_1846 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1846, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1846 : ∀ b ∈ bds_1846, canon b.1 g_1846 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1846, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1846 : dagCheckRootsF m_1846 g_1846 bds_1846 (dagRefF 0 (dagTraceF m_1846 s_1846 4 f_1846) l_1846 0) s_1846 4 = true := by decide +kernel
def node_1846 : Nat → Bool := dagCheckNodeF m_1846 g_1846 bds_1846 0 (dagTraceF m_1846 s_1846 4 f_1846) l_1846
theorem nc_1846 : ∀ j, 0 ≤ j → j < 0 → node_1846 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1846 : LowerBin m_1846 s_1846 g_1846 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1846 sub_1846 gl_1846 rc_1846 nc_1846

def m_1864 : Nat := 0xa500a500a500a5
def s_1864 : List Nat := [0x5000500050005, 0x21002100210021, 0xa5000000a5, 0xa500a5]
def g_1864 : Nat := 0x1000500050025
theorem lb_1864 : LowerBin m_1864 s_1864 g_1864 6 := by
  refine lowerByRows [0, 2, 1, 1, 1, 1, 5, 7, 16, 18, 1, 1, 1, 1, 21, 23, 32, 34, 1, 1, 1, 1, 37, 39, 48, 50, 1, 1, 1, 1, 53, 55] (by decide +kernel) ?_ (by decide +kernel) lb_1758
  intro w hw
  simp only [s_1864, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_1882 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1882 : Nat → Nat → Option Nat := fun _ _ => none
def m_1882 : Nat := 0xcc00cc00cc00cc
def s_1882 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_1882 : Nat := 0x4000c004c
def bds_1882 : List (Nat × List Nat × Nat × Nat) := [(m_688, s_688, 4, g_688)]
theorem kn_1882 : KnownBin bds_1882 := by
  intro b hb
  simp only [bds_1882, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_688
theorem sub_1882 : ∀ b ∈ bds_1882, m_1882 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1882, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1882 : ∀ b ∈ bds_1882, canon b.1 g_1882 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1882, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1882 : dagCheckRootsF m_1882 g_1882 bds_1882 (dagRefF 0 (dagTraceF m_1882 s_1882 4 f_1882) l_1882 0) s_1882 4 = true := by decide +kernel
def node_1882 : Nat → Bool := dagCheckNodeF m_1882 g_1882 bds_1882 0 (dagTraceF m_1882 s_1882 4 f_1882) l_1882
theorem nc_1882 : ∀ j, 0 ≤ j → j < 0 → node_1882 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1882 : LowerBin m_1882 s_1882 g_1882 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1882 sub_1882 gl_1882 rc_1882 nc_1882

def f_1891 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1891 : Nat → Nat → Option Nat := fun _ _ => none
def m_1891 : Nat := 0xf000f000f000f0
def s_1891 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_1891 : Nat := 0x10001000100070
def bds_1891 : List (Nat × List Nat × Nat × Nat) := [(m_267, s_267, 4, g_267)]
theorem kn_1891 : KnownBin bds_1891 := by
  intro b hb
  simp only [bds_1891, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_267
theorem sub_1891 : ∀ b ∈ bds_1891, m_1891 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1891, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1891 : ∀ b ∈ bds_1891, canon b.1 g_1891 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1891, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1891 : dagCheckRootsF m_1891 g_1891 bds_1891 (dagRefF 0 (dagTraceF m_1891 s_1891 4 f_1891) l_1891 0) s_1891 4 = true := by decide +kernel
def node_1891 : Nat → Bool := dagCheckNodeF m_1891 g_1891 bds_1891 0 (dagTraceF m_1891 s_1891 4 f_1891) l_1891
theorem nc_1891 : ∀ j, 0 ≤ j → j < 0 → node_1891 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1891 : LowerBin m_1891 s_1891 g_1891 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1891 sub_1891 gl_1891 rc_1891 nc_1891

def f_1919 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1919 : Nat → Nat → Option Nat := fun _ _ => none
def m_1919 : Nat := 0x505050505050505
def s_1919 : List Nat := [0x101010101010101, 0x5000500050005, 0x50500000505, 0x5050505]
def g_1919 : Nat := 0x101010501050505
def bds_1919 : List (Nat × List Nat × Nat × Nat) := [(m_943, s_943, 4, g_943)]
theorem kn_1919 : KnownBin bds_1919 := by
  intro b hb
  simp only [bds_1919, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_943
theorem sub_1919 : ∀ b ∈ bds_1919, m_1919 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1919, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1919 : ∀ b ∈ bds_1919, canon b.1 g_1919 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1919, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1919 : dagCheckRootsF m_1919 g_1919 bds_1919 (dagRefF 0 (dagTraceF m_1919 s_1919 4 f_1919) l_1919 0) s_1919 4 = true := by decide +kernel
def node_1919 : Nat → Bool := dagCheckNodeF m_1919 g_1919 bds_1919 0 (dagTraceF m_1919 s_1919 4 f_1919) l_1919
theorem nc_1919 : ∀ j, 0 ≤ j → j < 0 → node_1919 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1919 : LowerBin m_1919 s_1919 g_1919 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1919 sub_1919 gl_1919 rc_1919 nc_1919

def f_1920 : Nat → Nat × Nat := unpackForestF 0x52710d7544d11042b94f282c91104276511844106ca3834a0844105c00f 4 10
def l_1920 : Nat → Nat → Option Nat := unpackLinksF 0xb89c98988a8180796a68685a5150493a0e01 0xe0a92131c1a102ce511a2228345058b4f12221d44308830d069412381089049de1ab02b404e506c20b800f 8 3 10 5 4
def m_1920 : Nat := 0x50505050a0a0a0a
def s_1920 : List Nat := [0xa0a0a0a, 0x101010102020202, 0x50005000a000a, 0x50500000a0a]
def g_1920 : Nat := 0x1010105000a0a0a
def bds_1920 : List (Nat × List Nat × Nat × Nat) := [(m_983, s_983, 3, g_983), (m_970, s_970, 3, g_970), (m_944, s_944, 4, g_944)]
theorem kn_1920 : KnownBin bds_1920 := by
  intro b hb
  simp only [bds_1920, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact lb_983
  · exact lb_970
  · exact lb_944
theorem sub_1920 : ∀ b ∈ bds_1920, m_1920 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1920, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl <;> decide +kernel
theorem gl_1920 : ∀ b ∈ bds_1920, canon b.1 g_1920 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1920, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1920 : dagCheckRootsF m_1920 g_1920 bds_1920 (dagRefF 17 (dagTraceF m_1920 s_1920 5 f_1920) l_1920 0) s_1920 5 = true := by decide +kernel
def node_1920 : Nat → Bool := dagCheckNodeF m_1920 g_1920 bds_1920 17 (dagTraceF m_1920 s_1920 5 f_1920) l_1920
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1920_0 : treeBlockF 0 17 node_1920 = true := by decide +kernel
theorem nc_1920 : ∀ j, 0 ≤ j → j < 17 → node_1920 j = true :=
  (certBlock nb_1920_0)
theorem lb_1920 : LowerBin m_1920 s_1920 g_1920 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1920 sub_1920 gl_1920 rc_1920 nc_1920

def m_1964 : Nat := 0xc0c0c0c03030303
def s_1964 : List Nat := [0x404040401010101, 0x3030303, 0xc000c00030003, 0xc0c00000303]
def g_1964 : Nat := 0x401030303
theorem lb_1964 : LowerBin m_1964 s_1964 g_1964 6 := by
  refine lowerByRows [0, 1, 2, 2, 2, 2, 34, 35, 8, 9, 2, 2, 2, 2, 42, 43, 16, 17, 2, 2, 2, 2, 50, 51, 24, 25, 2, 2, 2, 2, 58, 59] (by decide +kernel) ?_ (by decide +kernel) lb_1758
  intro w hw
  simp only [s_1964, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_1994 : Nat := 0x1111111122222222
def s_1994 : List Nat := [0x22222222, 0x101010102020202, 0x11001100220022, 0x111100002222]
def g_1994 : Nat := 0x111111100020222
theorem lb_1994 : LowerBin m_1994 s_1994 g_1994 7 := by
  refine lowerByRows [32, 1, 0, 0, 36, 5, 0, 0, 40, 9, 0, 0, 44, 13, 0, 0, 48, 17, 0, 0, 52, 21, 0, 0, 56, 25, 0, 0, 60, 29] (by decide +kernel) ?_ (by decide +kernel) lb_1744
  intro w hw
  simp only [s_1994, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_1998 : Nat → Nat × Nat := unpackForestF 0x105358612410e6086a063f7c1cbe0d40a7ef13e0296b7d09ce98dc3d6e188149d9466d24c6417b208c0a4aa23a511b2e4f54468a135571a284b54c70a125021f9ed34f49a924c3d1e9e8d50e88784d3e9a1e09808666c4e3613010acc684613d0213935389a844c4e26210106c149c0a4204a70e0c0126c313c14170a088126821280e120213822981134042102064082e000f 7 10
def l_1998 : Nat → Nat → Option Nat := unpackLinksF 0x3686d0d83b0342680d0185f00dd3ba1742e0db1ae95c2b0d42a6335a684c198128a504a0923206313bb760e49c83816c4d81a8b50682aa9502a0504a01402624c09813026040c801001f13e0784f01d13a0650c81812e25c0b81522a03240d801 0x10c24889aa610610730435789625104887afc397c1a930c4782a9031789f2a0fd1866e74c1c923ad09c07adc311a0a8c051a4982c141492358cd407e88336617b208c482a863c5c9ea10855c682014531c07051069ac23a5f1b2d8d08a7ab1355496a84950082581a0c0b248f02a48924c08921f0910e887d344da6a59351c7a8a3540a6954a81a4c804d26151e098e09c6c2633a1184f4b29c5542049294138988408250a200e0c062781c3e08190b0b8504421280e12055302268464e21210f5386a6c253404970613818840819811fbd4fdda5ad9276292a70fce866682b2e139206c082e000f 11 4 10 7 5
def m_1998 : Nat := 0x1111222244448888
def s_1998 : List Nat := [0x222200008888, 0x44448888, 0x101020204040808, 0x11002200440088]
def g_1998 : Nat := 0x111000000040808
def bds_1998 : List (Nat × List Nat × Nat × Nat) := [(m_1177, s_1177, 4, g_1177), (m_845, s_845, 4, g_845), (m_1167, s_1167, 4, g_1167), (m_606, s_606, 3, g_606)]
theorem kn_1998 : KnownBin bds_1998 := by
  intro b hb
  simp only [bds_1998, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_1177
  · exact lb_845
  · exact lb_1167
  · exact lb_606
theorem sub_1998 : ∀ b ∈ bds_1998, m_1998 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1998, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_1998 : ∀ b ∈ bds_1998, canon b.1 g_1998 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1998, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1998 : dagCheckRootsF m_1998 g_1998 bds_1998 (dagRefF 69 (dagTraceF m_1998 s_1998 6 f_1998) l_1998 0) s_1998 6 = true := by decide +kernel
def node_1998 : Nat → Bool := dagCheckNodeF m_1998 g_1998 bds_1998 69 (dagTraceF m_1998 s_1998 6 f_1998) l_1998
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1998_0 : treeBlockF 0 69 node_1998 = true := by decide +kernel
theorem nc_1998 : ∀ j, 0 ≤ j → j < 69 → node_1998 j = true :=
  (certBlock nb_1998_0)
theorem lb_1998 : LowerBin m_1998 s_1998 g_1998 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1998 sub_1998 gl_1998 rc_1998 nc_1998

def m_2003 : Nat := 0x1122112244884488
def s_2003 : List Nat := [0x22002200880088, 0x44884488, 0x102010204080408, 0x112200004488]
def g_2003 : Nat := 0x100110000080408
theorem lb_2003 : LowerBin m_2003 s_2003 g_2003 7 := by
  refine lowerByRows [0, 0, 0, 3, 0, 0, 0, 7, 0, 0, 0, 19, 0, 0, 0, 23, 0, 0, 10, 0, 0, 0, 14, 0, 0, 0, 26, 0, 0, 0, 30, 0, 0, 33, 0, 0, 0, 37, 0, 0, 0, 49, 0, 0, 0, 53, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 56, 0, 0, 0, 60] (by decide +kernel) ?_ (by decide +kernel) lb_1998
  intro w hw
  simp only [s_2003, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_2010 : Nat → Nat × Nat := unpackForestF 0x3d8f 1 6
def l_2010 : Nat → Nat → Option Nat := unpackLinksF 0x119 0x3d8f 3 1 6 1 2
def m_2010 : Nat := 0x1212121248484848
def s_2010 : List Nat := [0x202020208080808, 0x48484848, 0x12001200480048, 0x121200004848]
def g_2010 : Nat := 0x10101000080848
def bds_2010 : List (Nat × List Nat × Nat × Nat) := [(m_1202, s_1202, 4, g_1202), (m_147, s_147, 4, g_147), (m_347, s_347, 4, g_347), (m_1198, s_1198, 4, g_1198), (m_617, s_617, 4, g_617), (m_1136, s_1136, 4, g_1136)]
theorem kn_2010 : KnownBin bds_2010 := by
  intro b hb
  simp only [bds_2010, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_1202
  · exact lb_147
  · exact lb_347
  · exact lb_1198
  · exact lb_617
  · exact lb_1136
theorem sub_2010 : ∀ b ∈ bds_2010, m_2010 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2010, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_2010 : ∀ b ∈ bds_2010, canon b.1 g_2010 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2010, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2010 : dagCheckRootsF m_2010 g_2010 bds_2010 (dagRefF 2 (dagTraceF m_2010 s_2010 6 f_2010) l_2010 0) s_2010 6 = true := by decide +kernel
def node_2010 : Nat → Bool := dagCheckNodeF m_2010 g_2010 bds_2010 2 (dagTraceF m_2010 s_2010 6 f_2010) l_2010
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2010_0 : treeBlockF 0 2 node_2010 = true := by decide +kernel
theorem nc_2010 : ∀ j, 0 ≤ j → j < 2 → node_2010 j = true :=
  (certBlock nb_2010_0)
theorem lb_2010 : LowerBin m_2010 s_2010 g_2010 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2010 sub_2010 gl_2010 rc_2010 nc_2010

def m_2024 : Nat := 0x2211884422118844
def s_2024 : List Nat := [0x11004400110044, 0x884400008844, 0x201080402010804, 0x22118844]
def g_2024 : Nat := 0x11000400110844
theorem lb_2024 : LowerBin m_2024 s_2024 g_2024 6 := by
  refine lowerByRows [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 11, 0, 0, 6, 15, 0, 0, 34, 43, 0, 0, 38, 47, 0, 0, 16, 25, 0, 0, 20, 29, 0, 0, 48, 57, 0, 0, 52, 61] (by decide +kernel) ?_ (by decide +kernel) lb_1780
  intro w hw
  simp only [s_2024, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_2028 : Nat → Nat × Nat := fun _ => (0, 0)
def l_2028 : Nat → Nat → Option Nat := fun _ _ => none
def m_2028 : Nat := 0x2222222222222222
def s_2028 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_2028 : Nat := 0x20222
def bds_2028 : List (Nat × List Nat × Nat × Nat) := [(m_109, s_109, 4, g_109)]
theorem kn_2028 : KnownBin bds_2028 := by
  intro b hb
  simp only [bds_2028, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_109
theorem sub_2028 : ∀ b ∈ bds_2028, m_2028 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2028, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_2028 : ∀ b ∈ bds_2028, canon b.1 g_2028 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2028, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2028 : dagCheckRootsF m_2028 g_2028 bds_2028 (dagRefF 0 (dagTraceF m_2028 s_2028 4 f_2028) l_2028 0) s_2028 4 = true := by decide +kernel
def node_2028 : Nat → Bool := dagCheckNodeF m_2028 g_2028 bds_2028 0 (dagTraceF m_2028 s_2028 4 f_2028) l_2028
theorem nc_2028 : ∀ j, 0 ≤ j → j < 0 → node_2028 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_2028 : LowerBin m_2028 s_2028 g_2028 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2028 sub_2028 gl_2028 rc_2028 nc_2028

def m_2031 : Nat := 0x2222444422224444
def s_2031 : List Nat := [0x444400004444, 0x202040402020404, 0x22004400220044, 0x22224444]
def g_2031 : Nat := 0x400020444
theorem lb_2031 : LowerBin m_2031 s_2031 g_2031 7 := by
  refine lowerByRows [61, 46, 0, 0, 57, 42, 0, 0, 53, 38, 0, 0, 49, 34, 0, 0, 29, 14, 0, 0, 25, 10, 0, 0, 21, 6, 0, 0, 17, 2] (by decide +kernel) ?_ (by decide +kernel) lb_1744
  intro w hw
  simp only [s_2031, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2034 : Nat := 0x2244224422442244
def s_2034 : List Nat := [0x44004400440044, 0x204020402040204, 0x224400002244, 0x22442244]
def g_2034 : Nat := 0x400040244
theorem lb_2034 : LowerBin m_2034 s_2034 g_2034 7 := by
  refine lowerByRows [61, 54, 0, 0, 57, 50, 0, 0, 45, 38, 0, 0, 41, 34, 0, 0, 29, 22, 0, 0, 25, 18, 0, 0, 13, 6, 0, 0, 9, 2] (by decide +kernel) ?_ (by decide +kernel) lb_1744
  intro w hw
  simp only [s_2034, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2035 : Nat := 0x2288114422881144
def s_2035 : List Nat := [0x114400001144, 0x88004400880044, 0x208010402080104, 0x22881144]
def g_2035 : Nat := 0x110400081144
theorem lb_2035 : LowerBin m_2035 s_2035 g_2035 6 := by
  refine lowerByRows [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 19, 0, 0, 6, 23, 0, 0, 34, 51, 0, 0, 38, 55, 0, 0, 8, 25, 0, 0, 12, 29, 0, 0, 40, 57, 0, 0, 44, 61] (by decide +kernel) ?_ (by decide +kernel) lb_1780
  intro w hw
  simp only [s_2035, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2038 : Nat := 0x2424242424242424
def s_2038 : List Nat := [0x404040404040404, 0x24002400240024, 0x242400002424, 0x24242424]
def g_2038 : Nat := 0x400040424
theorem lb_2038 : LowerBin m_2038 s_2038 g_2038 7 := by
  refine lowerByRows [61, 58, 0, 0, 53, 50, 0, 0, 45, 42, 0, 0, 37, 34, 0, 0, 29, 26, 0, 0, 21, 18, 0, 0, 13, 10, 0, 0, 5, 2] (by decide +kernel) ?_ (by decide +kernel) lb_1744
  intro w hw
  simp only [s_2038, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2039 : Nat := 0x2814281428142814
def s_2039 : List Nat := [0x14001400140014, 0x804080408040804, 0x281400002814, 0x28142814]
def g_2039 : Nat := 0x10001400140814
theorem lb_2039 : LowerBin m_2039 s_2039 g_2039 6 := by
  refine lowerByRows [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 11, 0, 0, 18, 27, 0, 0, 34, 43, 0, 0, 50, 59, 0, 0, 4, 13, 0, 0, 20, 29, 0, 0, 36, 45, 0, 0, 52, 61] (by decide +kernel) ?_ (by decide +kernel) lb_1780
  intro w hw
  simp only [s_2039, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2040 : Nat := 0x2828141428281414
def s_2040 : List Nat := [0x141400001414, 0x808040408080404, 0x28001400280014, 0x28281414]
def g_2040 : Nat := 0x101400081414
theorem lb_2040 : LowerBin m_2040 s_2040 g_2040 6 := by
  refine lowerByRows [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 19, 0, 0, 10, 27, 0, 0, 34, 51, 0, 0, 42, 59, 0, 0, 4, 21, 0, 0, 12, 29, 0, 0, 36, 53, 0, 0, 44, 61] (by decide +kernel) ?_ (by decide +kernel) lb_1780
  intro w hw
  simp only [s_2040, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2054 : Nat := 0x3030c0c003030c0c
def s_2054 : List Nat := [0x1010404001010404, 0xc0c000000c0c, 0x3030c0c, 0x3000c00003000c]
def g_2054 : Nat := 0x10000001030c0c
theorem lb_2054 : LowerBin m_2054 s_2054 g_2054 6 := by
  refine lowerByRows [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 52, 0, 0, 17, 53, 0, 0, 24, 60, 0, 0, 25, 61, 0, 0, 2, 38, 0, 0, 3, 39, 0, 0, 10, 46, 0, 0, 11, 47] (by decide +kernel) ?_ (by decide +kernel) lb_1780
  intro w hw
  simp only [s_2054, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2057 : Nat := 0x30c030c0030c030c
def s_2057 : List Nat := [0x1040104001040104, 0xc000c0000c000c, 0x30c030c, 0x30c00000030c]
def g_2057 : Nat := 0x1000010c030c
theorem lb_2057 : LowerBin m_2057 s_2057 g_2057 6 := by
  refine lowerByRows [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 44, 0, 0, 9, 45, 0, 0, 24, 60, 0, 0, 25, 61, 0, 0, 2, 38, 0, 0, 3, 39, 0, 0, 18, 54, 0, 0, 19, 55] (by decide +kernel) ?_ (by decide +kernel) lb_1780
  intro w hw
  simp only [s_2057, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2065 : Nat := 0x33003300cc00cc00
def s_2065 : List Nat := [0x1100110044004400, 0xcc00cc00, 0x30003000c000c00, 0x33000000cc00]
def g_2065 : Nat := 0x100110000000c00
theorem lb_2065 : LowerBin m_2065 s_2065 g_2065 6 := by
  refine lowerByRows [0, 31, 0, 30, 0, 0, 0, 0, 0, 27, 0, 26, 0, 0, 0, 0, 0, 15, 0, 14, 0, 0, 0, 0, 0, 11, 0, 10, 0, 0, 0, 0, 61, 0, 60, 0, 0, 0, 0, 0, 57, 0, 56, 0, 0, 0, 0, 0, 45, 0, 44, 0, 0, 0, 0, 0, 41, 0, 40] (by decide +kernel) ?_ (by decide +kernel) lb_1920
  intro w hw
  simp only [s_2065, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2071 : Nat := 0x33330000cccc0000
def s_2071 : List Nat := [0x1111000044440000, 0xcccc0000, 0x30300000c0c0000, 0x33000000cc0000]
def g_2071 : Nat := 0x1110000000c0000
theorem lb_2071 : LowerBin m_2071 s_2071 g_2071 6 := by
  refine lowerByRows [0, 31, 0, 30, 0, 0, 0, 0, 0, 27, 0, 26, 0, 0, 0, 0, 0, 23, 0, 22, 0, 0, 0, 0, 0, 19, 0, 18, 0, 0, 0, 0, 61, 0, 60, 0, 0, 0, 0, 0, 57, 0, 56, 0, 0, 0, 0, 0, 53, 0, 52, 0, 0, 0, 0, 0, 49, 0, 48] (by decide +kernel) ?_ (by decide +kernel) lb_1920
  intro w hw
  simp only [s_2071, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2097 : Nat := 0x4444444444444444
def s_2097 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_2097 : Nat := 0x400040444
theorem lb_2097 : LowerBin m_2097 s_2097 g_2097 7 := by
  refine lowerByRows [62, 58, 0, 0, 54, 50, 0, 0, 46, 42, 0, 0, 38, 34, 0, 0, 30, 26, 0, 0, 22, 18, 0, 0, 14, 10, 0, 0, 6, 2] (by decide +kernel) ?_ (by decide +kernel) lb_1744
  intro w hw
  simp only [s_2097, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2113 : Nat := 0x50500505a0a00a0a
def s_2113 : List Nat := [0xa0a00a0a, 0x1010010120200202, 0x50500000a0a, 0x50000500a0000a]
def g_2113 : Nat := 0x10010500000a0a
theorem lb_2113 : LowerBin m_2113 s_2113 g_2113 6 := by
  refine lowerByRows [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 52, 0, 0, 34, 54, 0, 0, 40, 60, 0, 0, 42, 62, 0, 0, 1, 21, 0, 0, 3, 23, 0, 0, 9, 29, 0, 0, 11, 31] (by decide +kernel) ?_ (by decide +kernel) lb_1780
  intro w hw
  simp only [s_2113, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_2117 : Nat → Nat × Nat := fun _ => (0, 0)
def l_2117 : Nat → Nat → Option Nat := fun _ _ => none
def m_2117 : Nat := 0x5050505050505050
def s_2117 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_2117 : Nat := 0x10101000101050
def bds_2117 : List (Nat × List Nat × Nat × Nat) := [(m_152, s_152, 4, g_152)]
theorem kn_2117 : KnownBin bds_2117 := by
  intro b hb
  simp only [bds_2117, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_152
theorem sub_2117 : ∀ b ∈ bds_2117, m_2117 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2117, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_2117 : ∀ b ∈ bds_2117, canon b.1 g_2117 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2117, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2117 : dagCheckRootsF m_2117 g_2117 bds_2117 (dagRefF 0 (dagTraceF m_2117 s_2117 4 f_2117) l_2117 0) s_2117 4 = true := by decide +kernel
def node_2117 : Nat → Bool := dagCheckNodeF m_2117 g_2117 bds_2117 0 (dagTraceF m_2117 s_2117 4 f_2117) l_2117
theorem nc_2117 : ∀ j, 0 ≤ j → j < 0 → node_2117 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_2117 : LowerBin m_2117 s_2117 g_2117 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2117 sub_2117 gl_2117 rc_2117 nc_2117

def m_2119 : Nat := 0x5050a0a005050a0a
def s_2119 : List Nat := [0xa0a000000a0a, 0x1010202001010202, 0x5050a0a, 0x5000a00005000a]
def g_2119 : Nat := 0x10000001050a0a
theorem lb_2119 : LowerBin m_2119 s_2119 g_2119 6 := by
  refine lowerByRows [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 52, 0, 0, 18, 54, 0, 0, 24, 60, 0, 0, 26, 62, 0, 0, 1, 37, 0, 0, 3, 39, 0, 0, 9, 45, 0, 0, 11, 47] (by decide +kernel) ?_ (by decide +kernel) lb_1780
  intro w hw
  simp only [s_2119, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2122 : Nat := 0x50a050a0050a050a
def s_2122 : List Nat := [0xa000a0000a000a, 0x1020102001020102, 0x50a050a, 0x50a00000050a]
def g_2122 : Nat := 0x1000010a050a
theorem lb_2122 : LowerBin m_2122 s_2122 g_2122 6 := by
  refine lowerByRows [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 44, 0, 0, 10, 46, 0, 0, 24, 60, 0, 0, 26, 62, 0, 0, 1, 37, 0, 0, 3, 39, 0, 0, 17, 53, 0, 0, 19, 55] (by decide +kernel) ?_ (by decide +kernel) lb_1780
  intro w hw
  simp only [s_2122, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2126 : Nat := 0x550000aa550000aa
def s_2126 : List Nat := [0xaa000000aa, 0x1100002211000022, 0x500000a0500000a, 0x550000aa]
def g_2126 : Nat := 0x10000000100002a
theorem lb_2126 : LowerBin m_2126 s_2126 g_2126 6 := by
  refine lowerByRows [0, 62, 0, 30, 0, 0, 0, 0, 0, 60, 0, 28, 0, 0, 0, 0, 0, 58, 0, 26, 0, 0, 0, 0, 0, 56, 0, 24, 0, 0, 0, 0, 39, 0, 7, 0, 0, 0, 0, 0, 37, 0, 5, 0, 0, 0, 0, 0, 35, 0, 3, 0, 0, 0, 0, 0, 33, 0, 1] (by decide +kernel) ?_ (by decide +kernel) lb_1920
  intro w hw
  simp only [s_2126, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_2129 : Nat → Nat × Nat := fun _ => (0, 0)
def l_2129 : Nat → Nat → Option Nat := fun _ _ => none
def m_2129 : Nat := 0x5500550055005500
def s_2129 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_2129 : Nat := 0x100110001001500
def bds_2129 : List (Nat × List Nat × Nat × Nat) := [(m_157, s_157, 4, g_157)]
theorem kn_2129 : KnownBin bds_2129 := by
  intro b hb
  simp only [bds_2129, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_157
theorem sub_2129 : ∀ b ∈ bds_2129, m_2129 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2129, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_2129 : ∀ b ∈ bds_2129, canon b.1 g_2129 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2129, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2129 : dagCheckRootsF m_2129 g_2129 bds_2129 (dagRefF 0 (dagTraceF m_2129 s_2129 4 f_2129) l_2129 0) s_2129 4 = true := by decide +kernel
def node_2129 : Nat → Bool := dagCheckNodeF m_2129 g_2129 bds_2129 0 (dagTraceF m_2129 s_2129 4 f_2129) l_2129
theorem nc_2129 : ∀ j, 0 ≤ j → j < 0 → node_2129 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_2129 : LowerBin m_2129 s_2129 g_2129 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2129 sub_2129 gl_2129 rc_2129 nc_2129

def f_2135 : Nat → Nat × Nat := fun _ => (0, 0)
def l_2135 : Nat → Nat → Option Nat := fun _ _ => none
def m_2135 : Nat := 0x5555000055550000
def s_2135 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_2135 : Nat := 0x111000001150000
def bds_2135 : List (Nat × List Nat × Nat × Nat) := [(m_159, s_159, 4, g_159)]
theorem kn_2135 : KnownBin bds_2135 := by
  intro b hb
  simp only [bds_2135, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_159
theorem sub_2135 : ∀ b ∈ bds_2135, m_2135 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2135, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_2135 : ∀ b ∈ bds_2135, canon b.1 g_2135 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2135, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2135 : dagCheckRootsF m_2135 g_2135 bds_2135 (dagRefF 0 (dagTraceF m_2135 s_2135 4 f_2135) l_2135 0) s_2135 4 = true := by decide +kernel
def node_2135 : Nat → Bool := dagCheckNodeF m_2135 g_2135 bds_2135 0 (dagTraceF m_2135 s_2135 4 f_2135) l_2135
theorem nc_2135 : ∀ j, 0 ≤ j → j < 0 → node_2135 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_2135 : LowerBin m_2135 s_2135 g_2135 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2135 sub_2135 gl_2135 rc_2135 nc_2135

def m_2136 : Nat := 0x55550000aaaa0000
def s_2136 : List Nat := [0xaaaa0000, 0x1111000022220000, 0x50500000a0a0000, 0x55000000aa0000]
def g_2136 : Nat := 0x1110000000a0000
theorem lb_2136 : LowerBin m_2136 s_2136 g_2136 6 := by
  refine lowerByRows [0, 31, 0, 29, 0, 0, 0, 0, 0, 27, 0, 25, 0, 0, 0, 0, 0, 23, 0, 21, 0, 0, 0, 0, 0, 19, 0, 17, 0, 0, 0, 0, 62, 0, 60, 0, 0, 0, 0, 0, 58, 0, 56, 0, 0, 0, 0, 0, 54, 0, 52, 0, 0, 0, 0, 0, 50, 0, 48] (by decide +kernel) ?_ (by decide +kernel) lb_1920
  intro w hw
  simp only [s_2136, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2137 : Nat := 0x5555555500000000
def s_2137 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_2137 : Nat := 0x111111500000000
theorem lb_2137 : LowerBin m_2137 s_2137 g_2137 6 := by
  refine lowerByRows [32, 36, 0, 0, 0, 0, 34, 38, 40, 44, 0, 0, 0, 0, 42, 46, 48, 52, 0, 0, 0, 0, 50, 54, 56, 60, 0, 0, 0, 0, 58, 62] (by decide +kernel) ?_ (by decide +kernel) lb_1758
  intro w hw
  simp only [s_2137, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2172 : Nat := 0x8844884488448844
def s_2172 : List Nat := [0x44004400440044, 0x804080408040804, 0x884400008844, 0x88448844]
def g_2172 : Nat := 0x400040844
theorem lb_2172 : LowerBin m_2172 s_2172 g_2172 7 := by
  refine lowerByRows [63, 54, 0, 0, 59, 50, 0, 0, 47, 38, 0, 0, 43, 34, 0, 0, 31, 22, 0, 0, 27, 18, 0, 0, 15, 6, 0, 0, 11, 2] (by decide +kernel) ?_ (by decide +kernel) lb_1744
  intro w hw
  simp only [s_2172, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2177 : Nat := 0x8888444488884444
def s_2177 : List Nat := [0x444400004444, 0x808040408080404, 0x88004400880044, 0x88884444]
def g_2177 : Nat := 0x400080444
theorem lb_2177 : LowerBin m_2177 s_2177 g_2177 7 := by
  refine lowerByRows [63, 46, 0, 0, 59, 42, 0, 0, 55, 38, 0, 0, 51, 34, 0, 0, 31, 14, 0, 0, 27, 10, 0, 0, 23, 6, 0, 0, 19, 2] (by decide +kernel) ?_ (by decide +kernel) lb_1744
  intro w hw
  simp only [s_2177, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2277 : Nat := 0xf000f00000f000f0
def s_2277 : List Nat := [0x5000500000500050, 0x3000300000300030, 0xf000f0, 0xf000000000f0]
def g_2277 : Nat := 0x100000100070
theorem lb_2277 : LowerBin m_2277 s_2277 g_2277 7 := by
  refine lowerByRows [63, 62, 0, 0, 61, 60, 0, 0, 23, 22, 0, 0, 21, 20, 0, 0, 47, 46, 0, 0, 45, 44, 0, 0, 7, 6, 0, 0, 5, 4] (by decide +kernel) ?_ (by decide +kernel) lb_1744
  intro w hw
  simp only [s_2277, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2284 : Nat := 0xf0f000000000f0f0
def s_2284 : List Nat := [0x5050000000005050, 0x3030000000003030, 0xf00000000000f0, 0xf0f0]
def g_2284 : Nat := 0x10000000001070
theorem lb_2284 : LowerBin m_2284 s_2284 g_2284 7 := by
  refine lowerByRows [63, 62, 0, 0, 61, 60, 0, 0, 55, 54, 0, 0, 53, 52, 0, 0, 15, 14, 0, 0, 13, 12, 0, 0, 7, 6, 0, 0, 5, 4] (by decide +kernel) ?_ (by decide +kernel) lb_1744
  intro w hw
  simp only [s_2284, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_2289 : Nat := 0xff000000000000ff
def s_2289 : List Nat := [0x5500000000000055, 0x3300000000000033, 0xf0000000000000f, 0xff]
def g_2289 : Nat := 0x10000000000007f
theorem lb_2289 : LowerBin m_2289 s_2289 g_2289 6 := by
  refine lowerByRows [0, 1, 8, 8, 8, 8, 56, 57, 2, 3, 8, 8, 8, 8, 58, 59, 4, 5, 8, 8, 8, 8, 60, 61, 6, 7, 8, 8, 8, 8, 62, 63] (by decide +kernel) ?_ (by decide +kernel) lb_1758
  intro w hw
  simp only [s_2289, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_2296 : Nat → Nat × Nat := unpackForestF 0x18fc63b18df34418cc53f14ec537791053314bc52b149ca34148c01f 4 10
def l_2296 : Nat → Nat → Option Nat := unpackLinksF 0x13098486411188442030078bc1e0e1703443801 0x3230cd11d30791092028d3e3fe8ef637b8ce93f94ee13764cd52f44acd27148c01f 9 4 10 4 5
def m_2296 : Nat := 0x5555555555555555
def s_2296 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_2296 : Nat := 0x111111501151555
def bds_2296 : List (Nat × List Nat × Nat × Nat) := [(m_1748, s_1748, 7, g_1748), (m_2097, s_2097, 7, g_2097), (m_2129, s_2129, 5, g_2129), (m_2135, s_2135, 5, g_2135), (m_1786, s_1786, 5, g_1786), (m_1846, s_1846, 5, g_1846), (m_2117, s_2117, 5, g_2117), (m_1919, s_1919, 5, g_1919), (m_2137, s_2137, 6, g_2137)]
theorem kn_2296 : KnownBin bds_2296 := by
  intro b hb
  simp only [bds_2296, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_1748
  · exact lb_2097
  · exact lb_2129
  · exact lb_2135
  · exact lb_1786
  · exact lb_1846
  · exact lb_2117
  · exact lb_1919
  · exact lb_2137
theorem sub_2296 : ∀ b ∈ bds_2296, m_2296 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2296, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_2296 : ∀ b ∈ bds_2296, canon b.1 g_2296 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2296, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2296 : dagCheckRootsF m_2296 g_2296 bds_2296 (dagRefF 16 (dagTraceF m_2296 s_2296 8 f_2296) l_2296 0) s_2296 8 = true := by decide +kernel
def node_2296 : Nat → Bool := dagCheckNodeF m_2296 g_2296 bds_2296 16 (dagTraceF m_2296 s_2296 8 f_2296) l_2296
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2296_0 : treeBlockF 0 16 node_2296 = true := by decide +kernel
theorem nc_2296 : ∀ j, 0 ≤ j → j < 16 → node_2296 j = true :=
  (certBlock nb_2296_0)
theorem lb_2296 : LowerBin m_2296 s_2296 g_2296 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2296 sub_2296 gl_2296 rc_2296 nc_2296

def f_2297 : Nat → Nat × Nat := fun _ => (0, 0)
def l_2297 : Nat → Nat → Option Nat := fun _ _ => none
def m_2297 : Nat := 0xaaaaaaaaaaaaaaaa
def s_2297 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_2297 : Nat := 0xa0a2a
def bds_2297 : List (Nat × List Nat × Nat × Nat) := [(m_2028, s_2028, 5, g_2028)]
theorem kn_2297 : KnownBin bds_2297 := by
  intro b hb
  simp only [bds_2297, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_2028
theorem sub_2297 : ∀ b ∈ bds_2297, m_2297 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2297, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_2297 : ∀ b ∈ bds_2297, canon b.1 g_2297 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2297, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2297 : dagCheckRootsF m_2297 g_2297 bds_2297 (dagRefF 0 (dagTraceF m_2297 s_2297 5 f_2297) l_2297 0) s_2297 5 = true := by decide +kernel
def node_2297 : Nat → Bool := dagCheckNodeF m_2297 g_2297 bds_2297 0 (dagTraceF m_2297 s_2297 5 f_2297) l_2297
theorem nc_2297 : ∀ j, 0 ≤ j → j < 0 → node_2297 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_2297 : LowerBin m_2297 s_2297 g_2297 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2297 sub_2297 gl_2297 rc_2297 nc_2297

def f_2298 : Nat → Nat × Nat := fun _ => (0, 0)
def l_2298 : Nat → Nat → Option Nat := fun _ _ => none
def m_2298 : Nat := 0x3333333333333333
def s_2298 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_2298 : Nat := 0x111111101131333
def bds_2298 : List (Nat × List Nat × Nat × Nat) := [(m_1744, s_1744, 7, g_1744)]
theorem kn_2298 : KnownBin bds_2298 := by
  intro b hb
  simp only [bds_2298, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_1744
theorem sub_2298 : ∀ b ∈ bds_2298, m_2298 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2298, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_2298 : ∀ b ∈ bds_2298, canon b.1 g_2298 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2298, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2298 : dagCheckRootsF m_2298 g_2298 bds_2298 (dagRefF 0 (dagTraceF m_2298 s_2298 7 f_2298) l_2298 0) s_2298 7 = true := by decide +kernel
def node_2298 : Nat → Bool := dagCheckNodeF m_2298 g_2298 bds_2298 0 (dagTraceF m_2298 s_2298 7 f_2298) l_2298
theorem nc_2298 : ∀ j, 0 ≤ j → j < 0 → node_2298 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_2298 : LowerBin m_2298 s_2298 g_2298 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2298 sub_2298 gl_2298 rc_2298 nc_2298

def f_2299 : Nat → Nat × Nat := fun _ => (0, 0)
def l_2299 : Nat → Nat → Option Nat := fun _ _ => none
def m_2299 : Nat := 0xcccccccccccccccc
def s_2299 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_2299 : Nat := 0x4000c0c4c
def bds_2299 : List (Nat × List Nat × Nat × Nat) := [(m_2097, s_2097, 7, g_2097)]
theorem kn_2299 : KnownBin bds_2299 := by
  intro b hb
  simp only [bds_2299, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_2097
theorem sub_2299 : ∀ b ∈ bds_2299, m_2299 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2299, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_2299 : ∀ b ∈ bds_2299, canon b.1 g_2299 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2299, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2299 : dagCheckRootsF m_2299 g_2299 bds_2299 (dagRefF 0 (dagTraceF m_2299 s_2299 7 f_2299) l_2299 0) s_2299 7 = true := by decide +kernel
def node_2299 : Nat → Bool := dagCheckNodeF m_2299 g_2299 bds_2299 0 (dagTraceF m_2299 s_2299 7 f_2299) l_2299
theorem nc_2299 : ∀ j, 0 ≤ j → j < 0 → node_2299 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_2299 : LowerBin m_2299 s_2299 g_2299 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2299 sub_2299 gl_2299 rc_2299 nc_2299

def f_2300 : Nat → Nat × Nat := fun _ => (0, 0)
def l_2300 : Nat → Nat → Option Nat := fun _ _ => none
def m_2300 : Nat := 0xf0f0f0f0f0f0f0f
def s_2300 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_2300 : Nat := 0x1010105010f0f0f
def bds_2300 : List (Nat × List Nat × Nat × Nat) := [(m_1919, s_1919, 5, g_1919)]
theorem kn_2300 : KnownBin bds_2300 := by
  intro b hb
  simp only [bds_2300, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_1919
theorem sub_2300 : ∀ b ∈ bds_2300, m_2300 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2300, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_2300 : ∀ b ∈ bds_2300, canon b.1 g_2300 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2300, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2300 : dagCheckRootsF m_2300 g_2300 bds_2300 (dagRefF 0 (dagTraceF m_2300 s_2300 5 f_2300) l_2300 0) s_2300 5 = true := by decide +kernel
def node_2300 : Nat → Bool := dagCheckNodeF m_2300 g_2300 bds_2300 0 (dagTraceF m_2300 s_2300 5 f_2300) l_2300
theorem nc_2300 : ∀ j, 0 ≤ j → j < 0 → node_2300 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_2300 : LowerBin m_2300 s_2300 g_2300 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2300 sub_2300 gl_2300 rc_2300 nc_2300

def f_2301 : Nat → Nat × Nat := fun _ => (0, 0)
def l_2301 : Nat → Nat → Option Nat := fun _ _ => none
def m_2301 : Nat := 0xf0f0f0f0f0f0f0f0
def s_2301 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_2301 : Nat := 0x10101000101070
def bds_2301 : List (Nat × List Nat × Nat × Nat) := [(m_1764, s_1764, 7, g_1764)]
theorem kn_2301 : KnownBin bds_2301 := by
  intro b hb
  simp only [bds_2301, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_1764
theorem sub_2301 : ∀ b ∈ bds_2301, m_2301 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2301, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_2301 : ∀ b ∈ bds_2301, canon b.1 g_2301 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2301, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2301 : dagCheckRootsF m_2301 g_2301 bds_2301 (dagRefF 0 (dagTraceF m_2301 s_2301 7 f_2301) l_2301 0) s_2301 7 = true := by decide +kernel
def node_2301 : Nat → Bool := dagCheckNodeF m_2301 g_2301 bds_2301 0 (dagTraceF m_2301 s_2301 7 f_2301) l_2301
theorem nc_2301 : ∀ j, 0 ≤ j → j < 0 → node_2301 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_2301 : LowerBin m_2301 s_2301 g_2301 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2301 sub_2301 gl_2301 rc_2301 nc_2301

def f_2302 : Nat → Nat × Nat := unpackForestF 0x78917c293e04905a7f0d178293c0490527e517b28a5935ec8a0e4104146f7146b89b5c0641287445ea0af5054a826d4019049dc094a0495015e80a94052a028d00190495b8119c06ce02e0421ad17960bcb052581b2c0b810766b5e35a31a8e4d0bc685234251a118d05c082b09290492820bc38441c1a0414820941046081d040d81026001f 6 11
def l_2302 : Nat → Nat → Option Nat := unpackLinksF 0xba1742e8549a81502a04d79a1342684d09a1162284508a0f61e83d07a0f41e8349680d01a0340680d01a02b9560ac1582564a0941282504a079cf01e03c0780f01e03c0780ac9502a0540a81502644c0981302602e00d001 0x1b24df922e88d7d2935141b09cf81258082d039d9a6f4d1792931941e024a01054053b45ed62968d7a229399413c24e41053053323aa8a56051a327579362c10dc0646023645e951d5657aa2a5113aa49b140868032281199294a92a42bd195288a542519207300190c08b0129e08c803a741b380b86044d45e642f30148f074b83658170a08946bc9b46491ca217900a4784a38231a0b8304440441c1a16948a494485e18290a128408c183a081b76d3f749f8a37b4a1ce4edf256d843541d980ac1026001f 11 4 11 6 5
def m_2302 : Nat := 0xff00ff00ff00ff
def s_2302 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_2302 : Nat := 0x110015001f007f
def bds_2302 : List (Nat × List Nat × Nat × Nat) := [(m_1768, s_1768, 5, g_1768), (m_1739, s_1739, 5, g_1739), (m_1891, s_1891, 5, g_1891), (m_1882, s_1882, 5, g_1882), (m_1846, s_1846, 5, g_1846)]
theorem kn_2302 : KnownBin bds_2302 := by
  intro b hb
  simp only [bds_2302, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact lb_1768
  · exact lb_1739
  · exact lb_1891
  · exact lb_1882
  · exact lb_1846
theorem sub_2302 : ∀ b ∈ bds_2302, m_2302 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2302, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_2302 : ∀ b ∈ bds_2302, canon b.1 g_2302 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2302, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2302 : dagCheckRootsF m_2302 g_2302 bds_2302 (dagRefF 63 (dagTraceF m_2302 s_2302 7 f_2302) l_2302 0) s_2302 7 = true := by decide +kernel
def node_2302 : Nat → Bool := dagCheckNodeF m_2302 g_2302 bds_2302 63 (dagTraceF m_2302 s_2302 7 f_2302) l_2302
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2302_0 : treeBlockF 0 63 node_2302 = true := by decide +kernel
theorem nc_2302 : ∀ j, 0 ≤ j → j < 63 → node_2302 j = true :=
  (certBlock nb_2302_0)
theorem lb_2302 : LowerBin m_2302 s_2302 g_2302 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2302 sub_2302 gl_2302 rc_2302 nc_2302

def m_2304 : Nat := 0xffff0000ffff
def s_2304 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_2304 : Nat := 0x111500001f7f
theorem lb_2304 : LowerBin m_2304 s_2304 g_2304 8 := by
  refine lowerByRows [0, 1, 2, 3, 4, 5, 6, 7, 16, 16, 16, 16, 16, 16, 16, 16, 8, 9, 10, 11, 12, 13, 14, 15, 16, 16, 16, 16, 16, 16, 16, 16, 32, 33, 34, 35, 36, 37, 38, 39, 16, 16, 16, 16, 16, 16, 16, 16, 40, 41, 42, 43, 44, 45, 46, 47] (by decide +kernel) ?_ (by decide +kernel) lb_2302
  intro w hw
  simp only [s_2304, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_2306 : Nat → Nat × Nat := unpackForestF 0xcb01372c82ccb20932c041c5c8df2503fcaa5332503bca453329140c940df27930c9e0f325944c960b326034c9609325033c5c8d72414cc82d1720a49c8a91320836c820bb21148c8209b1703bc7e0db17039c629371d23cc760531d040c628d71894dc625071aa4cc6a06318939c6610318935c620e717037c5e8f717035002d0f16035c1ed4714839c520d707b4bc1ed2713144c3f1670fa59c3e13b0f82ec408e310158c3e09b0784bc3b14707849c22d470d038c22d270895dc225470aa5cc2a06308949c2614308945c2212707847c1e11400a4fc1a0d6f7c52c1416705055bded7ef7b5ebded4b03154bff1baffa49bfe1baff82ec008e300148bfe09af783bbfb14af7839be318afd058be2dbaf894dbe2506faa4cbea062f8939be6102f8935be20e6f7837bde0d400a3fbd68d6f5939bd64d6d834bbd28d6d8349bced66d825dbc4d86f1349bc45b6f1161b6091ef0234bacd6eeb353bac57eee26cbac56eed060bac55eec15cbae992eb153b60916e5b5dba6d52e5b5ab96d5ae5b55b96d52e7154b964e6e6358b964d6d823fb92912e1c59b8e9b2e1b55b8653ae2254b864dad814bb82512dfb4fb7e4dad8149b6cd86de138b6cd26db26db70972dc160b6c916db149b6051ed8a5db62936d936cb628fed814500213ed7144ab7146d6144b43582d4d60b52092d0a49b4e132d0a45b4212ad0846b42116d1450b42112adb4fb3d166cf34fab6176ccb5db32d16cca49b32916ad84fb2e8d6ad84eb2a112c7c5eb1f14ac7a4db22972c7a41b1e17aad837b1a112bd451b13582c5350b12912bd34faf4d0ebd13fb0a932bd13bb05142c104caf44debfb40afe4f2bea44afa572bd133af7166bd05dab60dab925eae491abb244ae417ab9a4cae64d2b9046ab60beb5451adb582b6a44ada512b534fad7146b5136ab60bab0b52ac2d2ab3148ac217ab1a38ac6502b0846ac20baad827abc922af148ab8d3eae23aab609800843aae956ab959aae55673b5faaa91673b5eaa68d673b52a94d6aa5356a94d56a5354a9a512a5159a96d72a51559ce97ea445e9ce936a3354a835baa0d62a82dbaa095da8254673a37a7e9529ac5fa6b14e9a94fa769729a94ba721429a947a6e5329b254a6a50e73a35a50d6a94356a50d569825da50d529426da5adb294255a5093694c58a53152942359ce57e93144a2ed769215ca2ed168b96da2e5768b94da2e51a8b945a389368e23da2e5128c348a30d128c244a2e4da73953a2a95286c6ea2697286b45a1a5ba88144a1a58a87244a1a4da7393ba1655284b5fa124da73939a0ed527f56e9fd58a821589fcdba7f25da00932801509fc8d67f1399ce4de7e4589f297e7ca4d9f28f6739359d0d76743459d0926742459e49367923d9d011277b449de912740369d8912761449d00ba74a489d2522740269ce14c0083f9ca512264529c65126c4609c1582700249b09666f05c9b09566c05a9b015a6c0559b2d426c054898d7e6b05499adb66a06c99ad566685a99a15a6685599c9766724d99a1522625f97f5825fa6d9915826404c97e91a5f82a97e09a5f8259811426025d9831426013a97e0922625396edb65bb5596e9665ba559709765c24d96e1522615f962db658b559629b658a599629562605f95e9162605e94c0da5492f9524ae5492795248e5303494c0b25302489814a5045e940d7e5025f942092502538981364f0549311ba4c4629309364d26c9309064c06e8980de4b0448eb14a49460926d02492548ead7e3ab5391ad6246b5491a9523a95f90d5824314c9131424314490f142431348ea54e3a93f9069323a93b9011824004c8ea4de3eb508fa4f23da448f65b23a9338f0d523c2548ea17e3b45e8ea136260368d69ba390248d698a35a468de9523586e8d8932361348d611a2602f8c114a334608cc952331548c0d7e324528c04da30a548c25523005f8980ba2f0548aadba2ab628aad2a2d1588aa1ba2ba388ae5022a8468aa0ba260278a49622915889ad7e26a3a89c9622715889a17e260260020ce2502487c92623b4c88e1321f24587c52a1f1468860f61f14487c12a1f04687c1161f04476314e1e04486f1661b85a86e15a1b85586e151d8a5f86ad5214d618529b61904485297a1492a85249a1701d8524921482a85209a14825852091d8a5384e1521046e84a1121046284012a100468401161004476293e0f35481f58a0e05481e9ba0ca4483209207a6281e9760792a81e49a0a01d81e4920782a81e09a0782581e091d8a438111660425981095604b5e812d4a0405476257e00c6e80292600a4580516601451802111d894f7f9165fe2597fadb1fe25576217dfd3547ec4fdfc1547ec4cdfb03f762179fa0447e293df90247e290dd88527d31b9f70447d3189f4a497d6d71f4a457d21b9d884f7ced51f195f7ca511f19537c617dd884e7c2151ef25f7be091ef253762109e9a6e7b6091e9a627a6979ec0247a6949eb2547a61b9ea2447a6179d882f7a0911e814479314de6a5479a551e485f794911e514479213dd882e78e151deb6e77ad89e204477ad79deb52782561de86e77e521de85e77a0b9d8827772921dc948772111d945376c961db15876417dd9a48766521d904f7620980082b736d29cdb49736d21d594c756501cdb46736919d303e74e051d3032736911d214c736525d1340736515d0244736129cf03e736121ce13473611959453564d79cc354727585c9a5e7264a5ca25072649559353564d495934e71ed51c1d6271b151c6560707189c1a6e70e931c392870e491c1a627064a5c226070649559343564d09c03486ef165bbb5a6eed65bbb586eed59bd3546eed39bc2546eed095915f6e7161ba3406e6951a95616a5185b81446a5179b71346a5149b64686a45b5b53486a4579a914e6a4535b34516a4531b24506a4515a91356c0921b01446b5145ad2516ba961ad15d6b40f9ad0326a44d1ac1346a4069aac516aa0f9a90186a60d1a901656454da83586891b9a6b4869a911a2462696d51a236e692911a2362688d29a2349688d21a234656453da0458682d01a02546395899f1546391b99e1346391898e451672d618e16e66c5319b1346385899a4586385758e14e63853598452638531974606385158e135654921951446491499224164e9219214d6480f9920326384d1911346380698fc5263e0f98e01863a0d18e01656450d8d1286131898c12861314984a6e62a93184a626129798924c6129498496e61d181871346125898495e615141851346125495913f60ad1182a4460a1217d4536031458094e6024957d1525f71497d95e5fa4d17d9525f64957d1425644f57c2405ee8d1714625ea9417a2345c51497126e5e1181782345c49897125e5d9141762345c49497116e5d05717414c5c45897115e5c85b17214c5c45497114d5644cd701445b114d6eb495ba5196c25e5b2d796cb525b24d96c24e5644c5655615951496524d5949056505e5a31456504c59c9316714c5940b965a405965016502656414d5e5625791895e24d5789055e06e5871495e04c5809316014c5780b95ea4057a5015e02656410d5d04456714d59a5f56e09159a5356693d5a02456690d5902900209d5804c54ad155294a54a51955a3d5560f55294454a1295284654a1155323d54a110f145354451151044533185500445331654f04c5321694c8565321554d351532150f135f52c5114b0445175894a0545171b9490445171894806c5161294584651611546452516110f134f5095854225e50891942c5150a4e9420243c494d3ed624fa9b93ea464fd1493f13a4fa090f12434f29b93ca5e4f2090f123b4e51653936d4e4d5539a5d4e6935390543c457d35c6e4d6d7535b454d89353623d4d6110f114f4d0511340444c714d331244c694d321244c690cf113a4bf1892fc524be130f11374b6d212da444b611126453498d4d263434ac4d12b01449854d299344a6051261434984cd2603f49cd49273424980f92603d3c44d8f112f4921112345348cd7d2334f3c44b51f46147d1651f36d47cd551fa5447e0f11f1363c417d1a245476d511a23f4684cd1a12b4680fd1b25446809d1a01f3c417919044460d3d180363c414912d6244b1b912c6244ad7512b454509111403c44a4d91346044a1b8f104f446d510da5f4368d50d9534364ad0d85f43a9110d82743607cf104e4321510bb5f42e0d8f104242a0f109944426111094533c40e905c6e41718905c5e4171490586e416178f103740cd210334440c911030443e114d022543e0d7cf8353402910f834f3e0d0cfe9443fa4d0f81533f4510fd1343e050cfbb543ee950f805f3e8d10fa2443e013cf91343e007cf801d3c40d8f44533d0d7cf434f3d4d78f534e3d08e8f403a3c4098f1c533c6d7cf1b4f3c60d8f101e00206cf02403a0d14e824a3a0924ee1363a0920ed24c3a0918ec1483a0128ea8363aa0b8e80483a2100e88383a20d0e804625914ce3c6139a920e3c5938e968e3a59393144e3a5838e9589635f379588e22583791b8e1248379188de24a378924df452378920de246258d3cdba45370d50dc25436e8fc9625e367584d995e36651896253362510d7b4f35e4d89625235ad50d525f356978d5235258938d0d6234f580d0b623425b8d19443464f0d09623425189624333e550ceb5f33a4d8962423251b8c945e324d88c93523245b8cb13c324588c915e3264f0c91522588ecc714831c510c70482fd14cc5b51316d24bf35e30f148c3b5e30ed48bf34e30adb0bf15f306510bf153302d70bf14f2fe510bf1432588e8bcb482f2910bd03c2f2120bb4532ecd40bb3402588d8b5d612d6d48b5b4a2d6178b82382d6118b64512d88e8b62362d60f0960532c1588b03622c0d28b006e2ca8e0b00462c3148b0a3a2c28d8b003c25810cad3622b4d48ad06e2b4178ad03c2580ecab2482ac520ab04428714ca1a5328690ca913c28654ca813c28650ca715828617ca614828613ca182f290948a42422860b8a285e28a138a182d28607c9603a27ad20a013027a9109e94827a12099c532740d09d02c26614c9b83426e0b09984326a0d09a3432660c09603626211096c5325ad7c96b4f25a0d89601900205c9504c248d149204a2481189204524a8f49204400514c91044237184900442371648d85a2361588d8552361500135f2321108856222e1508846e22a110884622201288804622011488044004d3c84c59212db484b552149748524d2121500115f2051b88135d204d1481a4d2068f48104400453c7f4621fd1487f04c0044dc7c3621f0d487c34a1f28d87c03c00449c7b0441d314c74b5f1d2d3c753431d493c7523f1d453c751431d44fc751331d44ac751271d20b0011251ce4c0702351c04e47003a1c00d8700351c24b470034136d0c6f0341b4d446d3491b45246d04513693c6c0341a51486935e1aa0d0693521a44e4690351368fc6804419b1446694e19a4d84d94319611062c5218a5786393418e0506295218a4d84d933174d785d34e1821105d15e1745485f0341745385d1421760d05d01e1364ac59a5216690859a3a1665785994e1664d84d81f1600e05803414cd0c5324f14c8fc5304f14c10c5303f14c0cc5302b14c09c530261360784e34313893c4e23f13853c4e1431384fc4e1331384ac4e1271360740112411f16447b6d11ed54483491209744a150120914481511205044801e11e4900105f110914463541108fc4403f11009c44017004178430440fed3c3f84c1069383f8361008fc402330fe0d0010520dd1b83e0440dd1883735d0dcd1438b5e0e2d4838a4d0ea50038a350e2504389310e2078371240de0503706e00413c363540ce97c33a350ce17c338270ce05c0104e0ca1502f35f0bc1703125e0bc0d82fa4f0be90c2f0340041082e0440ab14c2d0340acd0c2b1430ac4cc2b01e0aa4900103a0a61502146e085188280440851782145208ed7823b5208ed3823b4208e4e42392908e0782112408a0502106e0860502105e0040dc1f34807cd101f24403114c1e254030d7c0c3530729100c34f030d0c1ab5406a9500c05f064d101924403013c17a4805e8e00c01703005414a3805608014a340524d00cb4304e5100ca4f03290c121340328fc0ca330420900c84303e0900c83303a0900c82b0360940c8290320640c0140040d80b04401f14c0a05401ed7c0904401ed3c0793601e0d80101e01a11001c53006d7c01b4f0120d00334300c93c0323f006490020140060d80101d00204c0001f 11 11
def l_2306 : Nat → Nat → Option Nat := unpackLinksF 0x342c1d0b034281d070f3e4ecf70b3d81cf40b3d00cf3073bc4cee073b80ceb0f3ac0cea073a02ce413358ecd60334c3ccf1333c0ccd0b32c2ccb033242cba3f2e41cb4172c82cb2032c80cb1072b83cac0b2a43ca9032a40ca5132940ca1132840c923f2402c87271a9dc680b178ac5d071701c50331304c4c0312c1c480f11c1c450b1140c45031083c372f0d81c330f0c81c32030c41c2f0b0b42c2d030b40c2a0f0a80c270f09c0c1c2f0682c006aff82bf42afcc1bf206f98cbe212f784bde02f741bda0ef641bd70af5c0bd702f503bc92ef201bc50ef101bc402f0c1bc10aefc2bbf02efc0bbc0eef00bb90eee40bae2eeb02b926ae441b9006e3c1b852ae140b7d22df40b761edd80b7506dd01b7306da89b6a02da41b6902da01b6706d942b6502d883b6202d841b6006d54bb5406d500b5306d4c0b5302d4c0b5302d481b5202d441b4142d040b4006d000b3e0acf41b3d02cec2b3322ccc0b3206cc80b2e12cb41b2d02cb01b2a0aca80b2a02ca02b2802c808b1f06c7c0b1f02c781b1916c058afd12bccaaf302bbc4aef02bbc0aec0ebb00aea0aba41ae902ba40ae902b9c2ad44eb4c1ad302b307acc02b2c1aca06b241abe2eaf80ab81aae00ab706adc0ab606ad80ab40aacc1aa82ea9c1aa312a881aa202a841a9f0aa7c0a9d0aa701a9a0aa641a9902a544a9502a540a930aa4c0a900ea400a8e0aa00ea7f069f42a7d029f01a7c029f00a790e9bcaa6c0e9b00a6c029b00a690e9a40a68069886a610697c2a5f029781a5e029780a5b0e96c0a512a9440a510293c2a4f029285a32628c41a30068bc1a252a8940a1d228701a190e8601a18028600a18028600a170685c0a16068190a06027fc79ff027f819fe027f419fc067ec19f2267c809f1067c409f0067bc19ed0a7b409ea0e7a809e9067a019dd2e77019dc0277009dc0276829da0276809d80a76009d80276009d60a71cf9c70271429c50270839c20270809c10670409c10270409c1026f839be026f809be026ec39ac3e6b009ab066ac09a90a6a019a80269c19a702694299d22674099c0667009981266009970665c09970265819940a650099402648299202628898a0262419880662009831660819800a5f8297c0a5f0097c025e43979025e409770a5dc0977025d42975025d409730a5ac89536253c49452a5140941125040941024f8393e024f0293b064ec093b024ec09390a499392602490292402484392006480092002480092002474390e3e42c390a064202908024104903064081901063fc28ff023fc08fe063e458eb3a3a818e80a39828e40a39008e40238438d92236408d80636008d70635818cb2e32c08c51a30c28c30230c08c20630808be122f808be022e068b7062dc08b7022dc08b6062bc78af022b818ae022b418ad022ac28aa0627cb89e0626848990626408980625828960225808960225808930e244289102244089006240088f0622c48890a22018860a214188502204488102204087f0a1fc087c0e1f0087c021e8287a021e0286a3a1a41869021a018660a19808650619408650218838582a154385502154085502148385202144185102144084f0a12468490212018480211828460211418450211408420e10808382a0e00838020d82836020d80836020d0282f1605d881702050381402050080f1603c080f0203c080c0e02c180b0202818070dfc567f101fc017ef05fbc07ef01fbc07e235f8807e105f8407e101f8017e001f8007e001f7c17de05f7807dd05f7017c94df2407c805f2007c705f1817c601f1807c601ee4d7b901ee017b801edc17b701edc07b509ed407b501ed407b501ed017b305ecc07b205ec4179e4de78079c09e64379901e64079709e40779001e38278b0de2c078b01e2427821de08078009e00077e09dd0a77401dcc177301dc8177201db4576d01db0176c01dac176909da4076901da0176609d98076409d90075a29d68075905d64075805d60075315d4c075205d48075105d3c274e05d38074d05d30174c01d2c174b01d28174a01d24173e2dcf8073e01cf0273c01cf0073a09ce8073a01ce0273411cd0073305ccc073301cc8173201cc8073105cc4073005cc0072725c9c072701c9c07240dc90072401c88272201c88072009c70470365c0c070301bfc46ff01bfc06fc0dbe826fa01be806f905bc486f101bb836ec09ba046e801b9c16e701b9036e401b8c16c771b1426c405b0826c201b0416c005af826b231ab456ab09aa816a809aa006a705a9816a601a9806a601a9806a30da8816a105a7c269331a38568e01a30268b05a2c068a05a24168901a20168801a1c1677419d81676019d0266e199ac366b019a8166a019a416680599826660199026640199006640198c166301984265e0d978065e01970265c01970065b0596c065b01948965201944165101944064f0993c064e058d59635018cc2633018cc06300d8c0062f058bc062e058b4162d018b0162b0586d061a05868061809848661201844161101840160d0d834060b0982c060a0581c36060581026040181006040180c16030180425fe0d7f805fe017f025fc017f005fb057ec05fb017c895f2017c415f1017c405ef097bc05ee0575595d50174c25d30174425cf0973c05ce0573025cc0172c15cb0172c05cb0172425c90172405c90171c25ba356e805ba016e805b4196d005b4016d005b0116c005b0016c005ae096b805aa1169065a40168c15a10968405a005678259e01678059e01670259c01670059c01668259a01668059a0166025980166005980165825960161cf5860560c35830160c05800d600057f055fc057c0d5d47574055d00572095c02570015c0056f055bc056f015b4256d015b4056b0958c856205588056009578255e01578055d05574055d0156c255b0156c055909544855101540155001540054f0553c054f015381549154c19530014b0452c014b0052c014b00526194941525014901524014708500714000500013f434fd013f014fc013e824fa013e804fa013e414e55139404e50138834e20138414e10138014e00137824de0137804de0137414c95132014c80131434c50131404c0152e084b7052dc04b40d2d004b4012bc54a72129c04a70129c04a11928404a005278249e01278049b0d25464950125014920924804920123c34891922404890121c248701218148601214148015200048001200047b151ec047b011ec04780d1dc1476051d80476011d02474011d00472091c80472011c80472011c0246e0918cb45c1d170045a0916414580514c545205148045201140245001140044e0911494440511004430510c04430110c0443011081442010ec743b010e8143a010e02437050dc0436050d80434090d00434010c82432010c41428250a0042705098142601098042601098042505094041e1d078041d05074041b0906c041a05068041809058241505054041405050041305048140a21028040a01028040a0101844060101414050101404040501004040101004020900804020100024000100003fe08ff803fe00ff023fc00fe823fa00fb8c3ec08fa433e60cf9803e600f9023e400f7473db08f6423d708f5813d114ed1d3b10ceac63ab00ea813aa00e9063a400e8823a200e7c339f00e7c039918e60139800e5c13940cdc2436d0cdb4036a0cda8036904da4036804d9c135254d3c334f00d30334c00d24334900d20134800d1c134604cc5533004cc0033000cb8232c08ca8232904c9c231d28c74031c04c7003151cc54031308c4c031204c40230e08c38030d04c30130b04c2c03080cc1822fc28bf002fb04bec02f41cbcc12f204bc412f004bbc12ef00bb422ec04bb002ea08b8492e100b8402e100b6872da00b6802d610b5802d600b5802d210b4802d104b4402d004b4002cf04b3c02ce04b08c2c200b0802c200b0412bd10af402bd00ae832b904ae402b708adc02b700ad032b400ad002b400abc52a720a9812a600a9022a400a9002a10ca8402a100a84029c14a50829400a50029400a50029400a3c528f00a3c028f00a2c428908a1c228700a18128600a14128500a0c228300a04228100a040281009fc227f009fc027d089f40271309c40271009c01270009c0026b149ac026b009a42269009a402670899c026604990225f1497c025d08970125b0496c0256148da0236008c84230088bc122c0c8ac122224839420d0482c220b0082422080482002070481c01f1587c011ee087b801ec087ac11e9087a011e80079c11e70074561d10074011ce0873801ce0072c31c51871401c40470821c20070801bf0c6e461b9006e401b9006cc61b3006cc01b1086c401af086a071a80069821a50469011a40069001a40069001a40069001a40069001a40066c91961465411920c6441190046400190006400188205dd1177005d81176005d80176005acb16b005a8116a005a80169045a4016900578b15e00574115d00570115228548015104544015100544014f0853811442851001440051001430450c0143005081142005080141044d4c135004d40135004d40135004d01128304a0012800498212600498012600498012600498012504490112304460b1180046001180046001180046001180046001180043c91013840010ff043f420fd003f400fd003ec20fb003ec00fb003c4a0e9203a400e9003a010e8003a000e80038470e10037c20df0037c00de0437800de0037020d81035c10d60435020d30434420d10034010d00034000ce0833800ce0033800c42831000c3042ec80bb002e810ba002e800ba002e800b31c2cc00b1082c400b1002c010b0002c000ae082a840a90429c20a70029810a60029800a600284509f0827c009d08270109c00268209904264009900264009900264009900260108f24238108c0822c108908200907f041f8107d041e44078041d82075041d01072081c41071001c4006f081bc006f001b4206d001b4006b081ac006b001ac006a041a800670c19c00660419800660019410650019400640419000630418c006204188006104184005728120f0480011c1047001181046001141045001140040140fc103d080f0103b040ec003a040e8003a000d84036000d4103014051c0014c0001 0xc900718ec0d31d0a265a02ccb204996e53620ca4baa945cb128391e4e71cc9aba9925cb609b104125d5022e58041c8e0738e40d5d4812e5504875004993c0d32a8a6645034ca00618f0933298a6652140c9c0600ac0532809864f03cc980280ac0832601a3a7024c9c288e984d32681664b024cad27f9524ef28c9be4a93374b24b9580ff2a01de51037c94066e9409557c0faaf01b3be02e4a404f240a63a0134c8a0687604d321492642034346048e24d2322922635a4402d28868c923210a4647345c8c4938d2917188a2c4513a73e26cab84a8eb8936310458820759100db218172a902ac8204c4a0088eb00b449a3b74746ee744d8ea09363f0367dc6898f09131d80a63c23cc74080e700900b1a2636148c674881f0510e981263624c02c2987480931a80c07c340c672618cc100e880a63134ec7a49aea89171c91ae3814d5532927645171b8a0e34139c6426b8c40e62201539b02655a03474005a24494aac01ac584bb8349371791ec4692b74324f6b81427282044202a5540358ac97706126e0723dcae46f9248d6d6ca8ce4941aa527b9024ef1f49ce30937c5d26b2964c61ec95b9a927b5a0a3390106a901ee4003bc7c0738c00df1701aca503187a056e6809d5240faa401b39e02e48c04e718202a301ac3b2b338a5071649ae1d0599c40838b00d550c0faa101b39c02e48404f0d0aa626058c4b2b3866556a8c9ee2a939c5326b3724c71282ce19055aa207b8a80e71481acdc03153f03ea7c06ce600b91f013c4c2898824931001a196024a8c6a98569500a4aa196258c4247188056312a2ce24259c294ab8445570882ae2304e9b80858880b94e81561f02623c0453869470ea28d4ca4f9bf487278d530d01c014454c2c2b184e950298aa61625c0282b985406029a28613940c260a184517aa89ace1b351c326938605754ecac9c7155c2e2a3850527090a2e11049a9527f3764cf159a8e2834bc4e69381cd06f34aeb9994dc3d297872527084a3e0f9457e12835264fe6bc99de605d73209b87812f0e024e10047c1e08afc0106a481fcd703353103ea6006ce300b91a013b580a0a5c06ad5ca8dfd949c1b26b6ac146fe824e0d03552b03ea5406ce280b918013bf42898180e2ea4aee0b959c152ab69654702c9cdf9935ba80bb82c1670502ada5051c0a0737e40d549c0fa9301b38602e45804d48c0fa9101b38202e45004f030aa600924c0006864c092e99aa5f5a4402528864c9230091c600148c0a8dd810926fa522df1145c060dd69418af8822e0202e51e0557fc098898115aaa51bfa8a573697ed4529d95344bf40b0048d12fb0a45f3a440a02897d8930090a65f50180a06817ce4c2f98205d446ebf68c57e4dbaf89a75f814d51f2926f0516fb8a0df4139be426b7c40e6e5cafda6953c188a5824d7f041af607352b952bf68254ea3ca6b9093dbfd2777f24e6f849bdef9357bb26372817ed0029d4704d72007b7f80eefe01cdf0037bde06af740c54540fa8a01b37602e43c04ef012a5bc254b922b167d5b2f212add223dbda46b720566dd8aad3393dbd82737ac4d669498de725dbd246b0ee4adbfc93d9f05181a0569dc06c87009de7359b662ab4ba4fe6ac99cbd0334ec03643404ef011a5c7148b704a9748da6f29b0de4349bc62db0ea5a5bdcb2de2161b8c2936dc516f011a5dc168bb02a97709b2e209a5b926cbae2a1768182ec0ae5d7264bbe6b7778d4eee8afddb15bbb22af75854e9649fcd39339780669d406c86009dd3354ba66a9738552e61ac59e56dba86bb748d6ae89ab5d0355b9e6a86dc576e00acdb11554632a34ae535bcc9edcd139b9626af824c6cf030dc9244b8e4d97104d283daa315b58b884a9721166e31aadb6255b6c2ab71453a694a143a93ab8626d704512e01a7dbf1369760870300ee2f5aa5bc13878f8a96e4952dc92e5b8160b6c8dd4ceda6de9b0dbb349b744dadee996db922db61497fa0536c8db2da12edb324db6247f2e80ce05815d9d45dbd46977a0d26a91a0de625d73249b78491eea922dca23f36c29b70852edf0a4db5147b6028a8be50693c9fccc93386d256dda49ece828cb603380e0569c406c84009dac24d86b256dce49ec68135ab35d9974a30d28edb951bdae1445ac26ea264bcba093d8c036ae005d6a8966d60a25a2054ade05d6a9582af01a5a9024b4e0995b80b2ca8225a2450a4d29b6ad58292d2eb6fa4db50493698915ef520d9e16d9ee2bb6781b6ce02ed9404db4a09569011ad1822da1044ad805c8c40aaae813085022af606d67d166cf1a7d22a4f9954870ce8edb5d1bd7a036b120695980d2bb01659c35db2869b66cd1690d2ed20a4db3449366491663520d8f036aea05d59409acb91ac3192b6d324eb4809d4440f971017b2a0895d00b2c892e563034b1248965117ac9a2959224d859492d8e916c8120b62a35af40d963c17ab90175620266c102b62cd7664ca8b5f925b1a089628952c51a858b560b12489614521adc9a57f124b0a4995cc4d2c00a0583450ac84995f84c2c1026580340afe2795f8911ad51a57d15caf68b2d72496c6228d8834fb0e68745e53e63ca1d8613fb082776044debe099b59925af40bb3b813d43c0f96f017a21088ba2132b981a576244ae8498d628d2b989a430b4a6af68d5e097a6352942ca4aaee48d5d417ab9023561036ac204d5bcd75ab51b56b136adeac15b8912b68a256b451ae08a35b0d3daa51b56a1369d609eb340de394125640447b7049598522b211c5631406a7269482d7ab41a956734a6c768d0be929a952356505eac408d5840fab081755f248abc291574d3eae11d42d93a9d009eb280ded6a28da034fa2d49f2fa90e1451db51a37b3a2bb39c53d6489ba8392f2d424f674176cc027d9604e94a084fc00eac701bd79036ae205f5a40b917815560027ab604c1f808a9f91a504244a2a271290d32a292ed59255a8646b418576ac0acd57155a1e2a34504e68189ad55245a9047b09a4ada7c93ca403180c0569c006c83809b4d925aa646b0924ada6493d46354a9a28952cd72a29aed5135aaa06ad53cd56a71aa4a334da5c2dad2a576a60acd4a1557e72a26b04f68509ccfb13543126328c106a422f52b15fa4a2a73e45167b829a6f01b20c027518d529f92a513138a004895155baa22b154336ea842bb08e565a24aad41151a242733fc4d69f92a53b158a6e2894ec9728709a50125ca6c2814e41429b8a6536254a7c8bf4f514e940afd23153a7829f4e852e9c0a3d351439ec0a69b806c82809d07354a604bb4a4956969b6529364a548b14a5152912b6d0635da666b54c8d5a989aad2f35494469b4b89b5a552ed2c255a5649ade48f69411ad22161944083470552930a252415ca322a94604d2880a251d24da3248b4708f68d1a4519344a30489281176929aeb6f34da4668b4889b6910b6d2115da4029b43c52a8f8a351e145a36288fce4ea8b89b4a0051a2a4a944c9728709a507354a20288c4ad228712251446ea2468b3f8916888b750f1629fc28b08e4ea8689b50b154a146bf4244da7a829c0503ba0e6a9410561e25a2501244a02499400542832b7505562a066dd3f8d7a8112eb44a559fe46b3f84e67e22c3eb0299f64bf3e89367c91ecf40538080573c81527802a4ef0349d20693a80927602e4ed02c9e649b3c09167911ecf03449de4893b4912760a24ea2489d22913dcd767b1a2cf52499e848b3c41127701b4eb02e9d004d558d7eaa1af55235293e69b52497ea3926b9023da8046f4d08d6938afd1615335227b4304ee8409ccfd1379f026a85a4c60fc95b439279ce0a727c10600015a6a01b20202738c9360f495b4092792c04d388d7665928c1da3b67f46f3945116409ba8292f2d224f2540da348174e12599c6289364152340174e15608a40693800926f02e46702c93c0a9364d426b0aece24609aa4dacf69766f92ccdd2557e34a32f45b6518a6cb506d93a0bb37016a6d82b4da0559b00a928c1363281721802a8a204c19008a678324d60549a80d92381924681a45e05499e4bb33893647122cca56d9aa6dacf6d76699aacca26194429b2cc1b62e82ecd205a9a20ad3401566682a4a204d7c00752300da6492348b04698604930809244822487034992ac1320132440224860348e40493085b25082e4c113a91226d30514261a284c225d9802752204da50826ccb5609946db3289b5f8d254c72469402bb280175ef0254850468e205b3180aa628134c402597e0492e41923c83247803489c06913c0923083646202c9724bb2e09363c922cbd36d9786ab2ec9665d12acb70548ee06d1800ba268134920348b40691bc0b25a9b6c9d35d9686ab2cc9b62e92ecb22599624ab1c49464c01b46e02e8b204d2bc9160dc95b3892758804ea0607cb300bc1a92966d24abf60f256097cab12b95424f2a448e0c51db35a3795a06d2a00d2538164a60248ec06d2840925222f4a335f9444bf28094e0bd1db33a378ea06d2781523681649a26c8ae0692489524ea3749c46293649b04a92596d22c9924165946b2601ba3a82e46b02e8ac04ccaa0564a1aec8b15165324b2581124992a4933409288c1248952479ac48e35491a4a92245124389a48945090e8a122d582450a648814490c26920c52192c9a47d1249064991b04d23f0a04814608b04991f04c24002647e3508fa2791f09119251a47b16c8f26a91e09523b22f32692592a8a5244d7e481a9c8c15f90a2a72104fe4109dc7f1378f4266c8e4963b82fc7504d50103e59005e2f02a4720245c90991b00d23792a46d24c6454691b04d20b5a5321b468e64dd1c498a095254702468dc0dd1ac11a2a81b4550268d06bac828da3209b4684608ce4a9198552322294622548c22a91a514a329afb1ea368c626d18017d5f81bc5e0548b0088f620922d0ac4582388ae280c764d22e9b745c3628b6694cb6d1a0ad2531ca468b20dd15811a2a81f45502e8a64b11485622792c44e1588a26bf1408ea09c9d44d05f57806f39114a6b9afccc25f97c4a703a8ed8dd1bcb615f93e29aaec4dd3e49795f1279600bf2b817a5282949f04d7ba07525c0de3a01b46a02f8be05c8580aa2a013c4c0260ba04455c4d1dd01a44a0248906990d49820f12844704c7a205910c0f50a00d3b90167dc088ae80d15d012a6801a2ac02d0d09860e928c2424d8924931189160c120c4514a88828d1085115c89aa6712a2aa24cfb41362082544004687e08b0f81115c81abcf02e424054ee00982d81143c04478e0a90cd5b61da2cc244518664c2ae04d5e302ec3a05a8720ad0e01561b82a3e604e7c0084ae00d61a9aa43204485c03af6c0915b8222b7035868ac30ccdb619936c3125e8304a4ad85153289d1511368602550bc49a168923e405e7bc0a4ad8115ed016c2c02a85604d0a80961481242705484a088f101121323742446282e8bb05c9455a89abf906e7e60c4f0c1361182542204684208b0801115a81ac1e3548380a90689120c81241401d7b0048ad01115a01ac1d56282e6bb06c9ba0c13141725d56628a98c4e8a789b41612a82a24d04c491fb8373f106256608af5c0b60901541102682004b03c091db01a3b70247fa6d8f341b1e701640a35e8126a50351660612cc0b2558100a8f8c139e60173b5026766068ed0091f59ae3ca05c79605900d16601228c0646e80a493010915fb03740104479205cec8098a709a3c10347fa6d8f580b1ffa2cbed45178c4baff8965fe12abda25129a24cfa4139ea8173c00267f46a8fe0551fc89fbf71337ec07e9ee07cae00bbf40447e4048fcc93df8921bee044298268efc0d1f59ae3d402c7de8dcfb5189e1926bec2497d448af5c904a58933e906e7a605cef8099f39aa3e51447cc2bef9054df182fa7a81f2b602ef84151ef8123e025f7bc4a6f1c151ed8123c40447b0048f58951ea1223dc26e7b44c4f64979eb92914313628624c7a0491ea8373d305e77a06cef4099e89223d014479c4a8f34551e59223ca14479e8a603e4d9e602fbc904f78e0a8f10111e08ac3bf14878c6dcf14d89e19af3c23523d0268f001b9df02f3bd03e77a05ceec921dd0a43b904476e4b0ed8561da1243b31487708a67a48e9da82fbb204f87a8a70d897e14129c1f24f81c48701c57e000a7ab21354f125e9884a8ac8939421267f60befd4179f80293e804f7c409cf741095901abd202f79005c8440a9de013bb10260a8044dd4545a10a0a5d01a28202ce24d31d60a63ab140740070e700d1d380a39825171e482c1c4b4bd892ba803e74c0649700689f80b179a447482984f4091ba0a8341140744680dcc581a00a8214938740488c144f4bc89ab9e03e738268e5cd85c71a8baf34a75c692eb4d21d51a338634175248ce949115c91f37216167e2a2d30535d18a4ba114566a282c104f50949c9781355be262b5818564028b9f04a73a090e6c1195c814a5a01a27802cd284fd9e899b8d3507188c0e60d518d1262f81407284a0bdc501cbab0b8b45272c4bce18949b88b0b1914d5ec282c504b5ca894b931255ce242964069a40a7b3b14358e08698406c80009b7915f6de2a6e34d41c623038f35471a8a8e31581c492638812870e248c609317a8a03842605e8280e39589c5a3138a26e70c4c4ce85458b8a6af314162225ae144a5c1892ae31214b0034ddc57db68a9ad50534c00363fc04dc01a42de1306d8ad8db05458aa3637a3546f04a8dad5b5bfa2cb4c4516fc6b4df4d65be1ac37b3566286a2de4d39bb9a12b823e6d62c2c404f9790992dc130570052d84511ba1a03601246ea8b0dcc9518192636614c6be268d580618792e2f12506bc288dc0511b709a35d1446d88d0d704d1b51a430213c6cc8a2d91141740a635c16c6b0030d4c051b09243601446ba4b0d7d145af128b5c15d61c25cbc0489ad81f35a0324ae0344ec059ac09a3564516aa07cd4c0d1b92b0b714616de8bcdb51495b1a736b26d61a49cc009317792136b16d6d22bccd4549b40a736714d6ca298d8c515738a13621356b2268ad80e52a8151390266ae034d50061a900b3503585b6260d38d21a69222da1306966a8d249119a22e3341416246b8d3d1b9a623133345d6946dcd20d89a39a534634968a690d10d19889a0ab523e6662a2c304f9770992d813056a052cac511a09a032a1246848b0d009517f92633014c652268c800619f0aa33c1346164b8bb4941940a23393585fc278bf44b17e12633714c66c268c9c5119a22c3261346608a4cb9181720a632615c644030c740519592432a14464e490ca514994120b2614d61425cbb04899281f3240324a80344e00599109a32045263e07cc740d19fab133d46e6768c4ce9145599a733325d61249cbe89317592133816e66a2c4ccc575990a733114d65e298cb4515718a132c135646268acc0e529015136026642034c780618e00b30f160634250c2c5418c0942e835846c4a8c54931721a421d244624498c3d1818709a30b450614268c651898ba2931626e6284c4c4c979889292e224d6202dcc34589860af3091525c4282040081839a23062446062c0bfc5417e0a03050486068a2c085397e0a13011255fa2685ea4917fa292fe15e5f82a4bec4958222980f2366002a4be85096a029ac60435f0480bc49817b91a2f52505da4a0bd08d178a302f02345da8a0bb08d1748ae2e814c5ca2d8b905317b2312f34525e44dcbbc9897712f2eb2525c449aba85b9738b12e615e5c62a4b885352881525101a0200304d40516d1262e0144268048b78d256d1a0add14642b268b6cd796d1a92d91365be8a6b709796c1271e31365a60a6b1410c998122d104c59c068b3c0b16581a2cc0245a28a2b3c931670a62cc240596280b595856aa292d424d5a6482b48179680262cd02e59404cb0c1316001a2c102c57a068af809161a292c124c580298af89015e8a02c856258e8c4b1893562920ac406e584098afc0b95e0132ba04456e048ad00915ca29ab825f56c4a6ad493d59921b9a4537326bce48d4dc89a939034e704686e04d095911f37615f6a22a6d0c53d8d8a1b0813f5f227a8464e4ba89aae11335ae262b2414d5d821ab20294bc03692c0689900b0fd0134b8268ac0131040222070345464baa5c9355611eaab03d4280548180980b0221310245444baa589355311ea082354d205496c0992480e9310155426daa54d75489a6aaf3455124c2a08945570a52ad14655428899c4e92d09b24892e49025a4c04940609124406d45c0ba8b0135548252a804654e08aa941110901d2050363dc04c4c0094f300f00c01d546288a68191510222a00440280a8a781314d1a8aa146153e8b2a451453b0b6a4792e48e25a4bc4940589124206d4200baa741694e02b29b0555320a88881390c0211ed02625e04a7940780580ea971445180a8a581114a02a2920445200d8048111462292955625268dca45189378aea4692e48c25a4b84940509123a06e4620c48ac17507026a8f04a51c08ca34115458221ec02625c04a7900780500ea860244ae2687f8110fe81a28645150a2747f84d93301d256036512ac2a209794392326514a4aa28c880178fe0232840244fe0489504d0fd8221fa0344fe8a49f84e8fd89b26403a4a606ca09589409372802464c62949485191c8371f90464fa0489ec9b93d12f23806e43e0bc7a20d13c8122730643f00c87dc0d13a12e9f82554e649a9dd1653b1b6a753554e40a8878138fb01b26c0543ea0a87d00d1369269f52454d847a9c11b9379aea6e34546e0dc9ac110f981b2691444d0088998491320922674534ca4a698c90cf40930100364c28c49811491a83721c05e4be098974d212e12225b04449e0989381312b89a2560144a826894c051279a924e34247e0bc8a01392d229a593534b068695454d290a1a5113347c0be89c13d2801fa4d03e49807a8d29b90dd2f1f1a464680dc86c178f88230f80244920883c8090788120f00244908a691cd7d231a79f00361d20488981712009a2040344804a88fc0f122230a434594588a2908db5081aea4135547c26c8941390601b2360254766a88d89511e122a3a23f4722668e04ad1b81fa3502746803e8c8111189a7a3003644c0d80581111489a2010344524888a00f11323022e56245a8dc8b1189159aea0e34d45468a89c4d91283720b0364466a88740950e92222225f44246a88054d0f895a1e05f43804e86c07d0c82a21835f42e06c8540f10a0a22130444248a603c0d80a02a0120444084a88049110823720f46241c8bc835148080a220c06e4160bc4b4091049a420834440e4888181110212a2012443fc2887f44d0fd8a21fa1343f06a87dc950fa9a21f42441f22887c84d102a29a0335f4046a6800d3cff9a19fc1533f22867d817cf98279f101f3e003a4b4054d192400801032c4b07ac8e0038081932483d4470018040f59af1ea34e3dc8a67b4d7cf61a79e923a3d12747a00e8028080081240f808801c4902982a0061240a0088010050f32299e535f3c869e014490f181b2a44535306bea28d3d41929a7c2434f04769c457d350a7a6213a4bc26e92c4d925097a4592e48a25a4b04940109123d05f4660bc8bc14912027a1a04e42c0848440e90501b9ef0363ce04c4b0094f100f00201d2814685000d0738101902483c04805ec8d09fc9a13f0341cc020394080ac51d13ea363202747704d8ac01d13e036346698768930ec0a41d29441c80206388e8bc91b15793a27b26c7580d8ea81700903401246074c100e901c1d103439c6da714d74e09a69df34536a4c26a0944ef1251dd2493b6490764918d112098d23a2f046c5d2584b4ca89d794a3a9290742518aac9d13c93626025c0544b4ba0309690513ae094750120e802315503a27806c4c20b80ac1693081e2600323d60487a8088df0103924d06308e06e8081cd2483164703700406d8101c945132c8b8739184e622c9c14513964b4728964e412c1c725632a4a26b0938cf12119b2393144704bc4b80989692f82e02705a4be0789780c8f48121e8022364040df12c1892381ae020710960c411c0d601038449061c8e06a0080d302037c8a464cd30e2ab11c346e3828c46dc9b8d81311c024a37e4926f4920de1231922413344726188e09709701112d25d05c0460b49740f12e0191e70243cc044688081b823e3726a86e0950dd1229b723f34e6c033c0806700818323819a0206d5584d31a919934a2a94946d0578d10a919514a36628c550128660101b114436069e5a290caf51d9af1362d00865780ec7e0119ad3543564686ac978d612f9aa23534e6c0328080d3ab00c9010190020690510d189e0c60202fe470314040d42b11a636233069454e928d28b71a2162324294684518a98250c402033e2a8678d7cb9d2995da3b33a26c5cc14cae81d8fb023186040308080c18a217f1441800206584f05f8100bd0103262782f0080cda3719a45e3326c4660d48cb8b71951623282bc6485485c81018c36c3126b861cd30c752419014831e288638120c61a898b34930e682614574c4a2918835e30e6a4604534c29b61831443026b85fc510c6a2998a35e30c69c5ca94cb3d2198415f3042a660053cbf0a19720532ce0863e808cbd01e17c3482f64885e6520bc8241784532ee6a05d8d00b701e1700442da0585b4920b811c13b9342dc8a25b48e8b611b15293a27526c5d1584b99a917234a2a34944e6918b882f16f0462d607858c0f0b282216202c2c44905948e09c49a1634522c44745848d8a849d1379362d2ac45a0d88b39a514fa4a26d48c5981b8b202316003c2bc6c4574d48ae03715b05e2b4078560920ab8a41560440b20205240f02c01014803c0ae0405484f0a809e14e15828c058530520a2816149252290484518178a28271554532a84a654c90ca88a994f14329a0be52c13ca501794702e28805a50c07c2a8081401302826904fc9109f0a413d0482680604ec0d09d01613803426e0584d40d09a1a18040262788a64e414c9b02193303002003a4c41100400e00701c00c0384c114c979af92e34f25a06c014070e7a299c635f37669e6d8978d91299ae25235249c68090cce12119123b2fa4745d48d8b54a995f9432b327650a4e89949b12c12e01c25a5a814caf82195903b2840744c80d89641700e82d25903c4b00647b8098e88121d00222680407309212a04c07e0880f80d07209207c0441c602838849006c1600d01c1c20284889748c92692523d07e46a0360740680d0f68161ec02a380050909b691835d22869a4a4d140649680c12a1eb24c3d44946f89207b04d25009449c118930229240440b60740f40d80ac1700c82d02a03c0300746f00a0dd124244088370490900220530541b42484851848fa2c91445121b4da4345b405c9680b12a1e924c3d04946c89209806d0a40ba4781688e82b11c0552360a81ac1383202101382e01705a04c0780580e8d80141ae2484641106b0921170541aa0283504908a8220500441a42484615888b23711446220d4ba4185740549680a12a1e724c3cc4946889208b06e10a0c41e81742782691304a22408c4441148802201182e01505a0440780500e90b06406c0c80d40d08592e90a24d06c48a439164869b690c3552120a81a41381a01b1040540660a80c80d08212690323d06646a41d1b8831ae9053451140dc4081101881b1004621fe8a42241b83402f0fe04c0200380bc1101801603023a1f246c3f0d887d9a90fa34a1100dc19c178170230f803c1ec0883c80b0788160f002c1e46863c493c7811f8ef14f1dc2863b44fc760998eb12b1d424e3d514c7a1af8f334f05a06c3a40b01580a0e71300540680a40905880e0090341bc29a3604f47089682a1251a008232c0c4588148c70211ba4ba35c9346a11e8e623519e2a23285047289c8c61310ee07a3900e87181b0e20351c00681640a8140130af01e14803a3780d06e9a88dc3491a868236c5245f8a08c312912a0ba1341346d0228ae01e14603a3600d06a81a0d74521ac6bc350d486989c8bc1311842521d81342581e8d203515a03c2880746802202102419e8a2338538630a10bf13a19a26c2481742c01d02003617005a244074658220c813418e02807c090652290c915e18c2a42f04e86289b07304d0ae0740780d85b81687201d1820882f80d05d81a0c335e18469c3005785f8a90bd14e1782841200d40c81a0b602d17403c1240740d00e01d0241704a42dc9085b11d0b515e1222a42d0538390a104913a16626c240178388270470361620702c00d00d89a01b02803625c2bcd0c571278ad23f15809e2ac10c5501f8a90331500560680a8538138a602614868628c93c5111f8a114f14028627c4fc4f09989d12b13824e37cd0c6c9278d123f1982863104cc5c89588f04f0e007e1540a82301381802616403e2940784d80e89612412a24824c4901e01a09415004e048258d243b9a089525d09a49a24c914490a88911410de07c1140984800f0994590f68a2260db4291ae89735511e2481b81382201b08c35411a48a22c8fc4549f88992711407e22409c4400b88604410606820c9384091f88023310a69e2101304101b07f0340f02480240503b89207c0440ec2481d04901c81a0090340ea2800900903c1af0773520ec49a12c8f43a11a8731410e42621bc1782181307101e0de0281f51b83da3107a35d09e69a1e4d143809206e06e08406c1b0d503592f86a2350d32be1a249c3482f8680270ce02e1941503101a06225e0c049e17c90c321af86305c0c206c1780d02d00a0591240b80881680d02c9a18581430ae2660100982b00f05b4530aa2481344902982a04c1240962481401102509201d02409a6bc130d48259a704a3420922721204a42282f04304e08e03c09c5101e12a0450140482680e49102180a05246e0a28c413d178272290461240880dc10817801c1600301c0580280a80501480a04034807e6880f89101400a0270140784a80980501280a02401407248808c0501100a03635406a4a80ccd101912203024805e4700ac0801611c02a23405226809c5101209a02102403e0480740900d81282834304c49e09490c1191f8222330400860780cc0e01581a0290320320f514c1d9af83a35307069e0dcd0c1a4af83194f0680be0c413c01c0e80301a05c02e0b60581680a81801402c088050150090220154530266be044d3c0809b00f0360120280204900682200712400c2480240d0041a180724f00c47e0100980200a00c4530166be028d3c028920030362468a6468d7c879a7908a5f20349e3f68dc840af90114f1fa26e00a4b4010950f71271d124c3a04944d09208e05f10e0bc1f81483682786604e0ba0841500e82081b81703601d05c00a0b40700f00201dc5a68783893ef711fdaf94fab528739a4fe25c99bb092b56324f6bc13ead021ce603f896066ec00ad588139e181f3c20364ac05c0080980001f 18 6 11 12 7
def m_2306 : Nat := 0xffffffff
def s_2306 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_2306 : Nat := 0x11f1f7f
def bds_2306 : List (Nat × List Nat × Nat × Nat) := [(m_1764, s_1764, 7, g_1764), (m_1748, s_1748, 7, g_1748), (m_1744, s_1744, 7, g_1744), (m_1767, s_1767, 5, g_1767), (m_1738, s_1738, 5, g_1738), (m_1757, s_1757, 5, g_1757), (m_1761, s_1761, 5, g_1761), (m_1739, s_1739, 5, g_1739), (m_1766, s_1766, 5, g_1766)]
theorem kn_2306 : KnownBin bds_2306 := by
  intro b hb
  simp only [bds_2306, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_1764
  · exact lb_1748
  · exact lb_1744
  · exact lb_1767
  · exact lb_1738
  · exact lb_1757
  · exact lb_1761
  · exact lb_1739
  · exact lb_1766
theorem sub_2306 : ∀ b ∈ bds_2306, m_2306 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2306, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_2306 : ∀ b ∈ bds_2306, canon b.1 g_2306 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2306, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2306 : dagCheckRootsF m_2306 g_2306 bds_2306 (dagRefSwapF 1628 (dagTraceF m_2306 s_2306 9 f_2306) l_2306 0) s_2306 9 = true := by decide +kernel
def node_2306 : Nat → Bool := dagCheckNodeWithF m_2306 g_2306 bds_2306 (dagTraceF m_2306 s_2306 9 f_2306) (dagRefSwapF 1628 (dagTraceF m_2306 s_2306 9 f_2306) l_2306)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2306_0 : treeBlockF 0 128 node_2306 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2306_1 : treeBlockF 128 256 node_2306 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2306_2 : treeBlockF 256 384 node_2306 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2306_3 : treeBlockF 384 512 node_2306 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2306_4 : treeBlockF 512 640 node_2306 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2306_5 : treeBlockF 640 768 node_2306 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2306_6 : treeBlockF 768 896 node_2306 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2306_7 : treeBlockF 896 1024 node_2306 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2306_8 : treeBlockF 1024 1152 node_2306 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2306_9 : treeBlockF 1152 1280 node_2306 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2306_10 : treeBlockF 1280 1408 node_2306 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2306_11 : treeBlockF 1408 1536 node_2306 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2306_12 : treeBlockF 1536 1628 node_2306 = true := by decide +kernel
theorem nc_2306 : ∀ j, 0 ≤ j → j < 1628 → node_2306 j = true :=
  (joinChecks (joinChecks (joinChecks (certBlock nb_2306_0) (joinChecks (certBlock nb_2306_1) (certBlock nb_2306_2))) (joinChecks (certBlock nb_2306_3) (joinChecks (certBlock nb_2306_4) (certBlock nb_2306_5)))) (joinChecks (joinChecks (certBlock nb_2306_6) (joinChecks (certBlock nb_2306_7) (certBlock nb_2306_8))) (joinChecks (joinChecks (certBlock nb_2306_9) (certBlock nb_2306_10)) (joinChecks (certBlock nb_2306_11) (certBlock nb_2306_12)))))
theorem lb_2306 : LowerBin m_2306 s_2306 g_2306 10 :=
  lowerDagSwapF (top := 31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2306 sub_2306 gl_2306 rc_2306 nc_2306

def f_2308 : Nat → Nat × Nat := fun _ => (0, 0)
def l_2308 : Nat → Nat → Option Nat := fun _ _ => none
def m_2308 : Nat := 0xffffffff00000000
def s_2308 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_2308 : Nat := 0x111111500000000
def bds_2308 : List (Nat × List Nat × Nat × Nat) := [(m_2137, s_2137, 6, g_2137)]
theorem kn_2308 : KnownBin bds_2308 := by
  intro b hb
  simp only [bds_2308, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_2137
theorem sub_2308 : ∀ b ∈ bds_2308, m_2308 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2308, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_2308 : ∀ b ∈ bds_2308, canon b.1 g_2308 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2308, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2308 : dagCheckRootsF m_2308 g_2308 bds_2308 (dagRefF 0 (dagTraceF m_2308 s_2308 6 f_2308) l_2308 0) s_2308 6 = true := by decide +kernel
def node_2308 : Nat → Bool := dagCheckNodeF m_2308 g_2308 bds_2308 0 (dagTraceF m_2308 s_2308 6 f_2308) l_2308
theorem nc_2308 : ∀ j, 0 ≤ j → j < 0 → node_2308 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_2308 : LowerBin m_2308 s_2308 g_2308 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2308 sub_2308 gl_2308 rc_2308 nc_2308

def f_2362 : Nat → Nat × Nat := unpackForestF 0x14be12e14ad7585d2052734b4a34148c03f 4 10
def l_2362 : Nat → Nat → Option Nat := unpackLinksF 0x166c51a141db862a4601 0x88fa12e6d617482480d2d28d252f74ad127148c03f 7 3 10 4 4
def m_2362 : Nat := 0xfcfcfcfcfcfcfcfc
def s_2362 : List Nat := [0x5454545454545454, 0x3030303030303030, 0xc0c0c0c0c0c0c0c, 0xfc00fc00fc00fc, 0xfcfc0000fcfc, 0xfcfcfcfc]
def g_2362 : Nat := 0x101014001c1c7c
def bds_2362 : List (Nat × List Nat × Nat × Nat) := [(m_1764, s_1764, 7, g_1764), (m_2301, s_2301, 8, g_2301), (m_2299, s_2299, 8, g_2299), (m_1761, s_1761, 5, g_1761), (m_1811, s_1811, 5, g_1811), (m_1882, s_1882, 5, g_1882), (m_2097, s_2097, 7, g_2097), (m_2117, s_2117, 5, g_2117), (m_2277, s_2277, 7, g_2277), (m_1817, s_1817, 5, g_1817), (m_2172, s_2172, 7, g_2172)]
theorem kn_2362 : KnownBin bds_2362 := by
  intro b hb
  simp only [bds_2362, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_1764
  · exact lb_2301
  · exact lb_2299
  · exact lb_1761
  · exact lb_1811
  · exact lb_1882
  · exact lb_2097
  · exact lb_2117
  · exact lb_2277
  · exact lb_1817
  · exact lb_2172
theorem sub_2362 : ∀ b ∈ bds_2362, m_2362 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2362, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_2362 : ∀ b ∈ bds_2362, canon b.1 g_2362 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2362, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2362 : dagCheckRootsF m_2362 g_2362 bds_2362 (dagRefF 10 (dagTraceF m_2362 s_2362 9 f_2362) l_2362 0) s_2362 9 = true := by decide +kernel
def node_2362 : Nat → Bool := dagCheckNodeF m_2362 g_2362 bds_2362 10 (dagTraceF m_2362 s_2362 9 f_2362) l_2362
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2362_0 : treeBlockF 0 10 node_2362 = true := by decide +kernel
theorem nc_2362 : ∀ j, 0 ≤ j → j < 10 → node_2362 j = true :=
  (certBlock nb_2362_0)
theorem lb_2362 : LowerBin m_2362 s_2362 g_2362 10 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2362 sub_2362 gl_2362 rc_2362 nc_2362

def f_2363 : Nat → Nat × Nat := unpackForestF 0xbb2b20297ee49480a5bb129f6252ed5ae58947b2289644f2c4a1d6460ad28b5c0cab4a256161014af464fe8c9dd4450a326f4cd0291225213ca326742912849480a539f4b20257e749f0095b9549f2a92e65ae4aa47964892c4a25521c84609148b240ca452248261012af0e8fe1d1dc64508746f14d0221a244128874670a512149f0095383250fedae012a401287f6c6024bdf4a63aa6b7a2a8f4531d531bb14577064ec511d4970092b6a4bed496dc236380606a4aed6d91ad2a35a4c6b250d494da5a800927026d6ccd5009b18126b634a80498d5d27aba4b5d6b8ba57174282ba4759488b24a164922ba435725eaa90154968123453480a48d008b7a7b504f27890d11213e262404b4689055120a62413c022d6875c1123022240434680459d01a82013c376887b580f4b61ba743b480748d0dcaa1b94c372780458cd1201a12d23468644c0c4921196e2e4685c5308cb515c602b24846598a1201412c274684658895201223423084045140daf81b5b1e8c03c1800dab8da381b27006d4c649401a5b172500694c549e0195b132780654c29278524b0d6a01a5403428052470b2501490c0c920235e046a40a938152102124030640451004918003f 8 11
def l_2363 : Nat → Nat → Option Nat := unpackLinksF 0x1270930c90a4272109084842403200900478a3491a08d046462e51528a8454228312289044462210f284b41ca069030810c009fa6fd07e83f41f82fc07e03e89ec8f607b03d45e64f127883c41e02ee27703b45da0eb272b38c9be8df06f0b781bc0dc26c9b641b02d806c03589ac0d606a8b4c9a06cf1670b345982c8464031c58c2c51602aed5724b725b82d0d644b20579abc15e0af05782bc1586ac05602b01526a904fd27852d0951499240d1e28f045a2285140891440a1c50c28063e99f40fa07a33b21d08e626f43781bc0da46d03609ac4d4269131b180cc005972c81604ae25702b814d0a605302891440a204f226193009624a122310888224011f88f0c7803c01c20e006e23701b08d806a23501a08cc46603301980cc06063001710a5450227113809c04a42230c5036c038001 0x1765660d1f242328227ece4cee494dab5cb3289644f2dca7db14bb428f6250eb81957945ad28961182b0b0d3140a88a14a4c299a052a44a4279544fea49dd3937a3267024bd9891c023e3746544911fc9fb2933a12533e965f49ca49317c476c88ce749f4cb5c974892c4a26d27cd24b9848f2a90e481949a4591489291824130c52308c8a1128c229a044b44882511c8fe351dc5a3787466f64ad8c91bd13938262f28ed8919c31448527d064a2052a40128826d6fed8dd51f3e94c7b2a8f4531dc193c14576288f89ade531ba92e61260c05017c982e930718d8dc9417098380605b260b44c16898373646d4a8d893160a035928734bee496dbd2bb525356260d2d41509024238182a8ccd50dd1c0b15449498285518d2a1c24c122a8bed7178ae2e8505b488b44a1649230a4f60496b891d6121a994f502968851d04a19a9355725e684d559202915f4e2b68655cfca99993509268aa4b4c89a29a4031268a48d134bc181444c288a0d40bd22259444f2787a591312025a34152883251139a226a7c2d4a89455124a62413c454687c580b0a222c6044480564d11ab821a343c2c054510a5221d9442826882d409d221d144402787d580f4b61da403a468265105ca21fb443c4e84c950e4aa1c14c3727864538a4a1128323548062578bcad15956272a4684b4901919130312485e8d0b8a60a93c1925859180ac9214a40282584e8d04c9e0b92c25480488d0cd1a1816e2d2d45459898b11184211248100c04092079240d2483f18030920f0601c470364e0289203840192502e4a0549e0993c060401ed4038a8068500b2500a0c045278824b0c48e1490c101103124052480c93815210435e076a40849085af9035b1d6ae34d4c612d8b253142b62454c249201832676d6cad8d9135b126354468a25bd1cb5a1167362c64451408a25d25fb84b75695e8129cf15f9c2b71e55e10a9bf12f74256d049c04918003f 13 4 11 8 5
def m_2363 : Nat := 0xf3f3f3f3f3f3f3f3
def s_2363 : List Nat := [0x5151515151515151, 0x3333333333333333, 0x303030303030303, 0xf300f300f300f3, 0xf3f30000f3f3, 0xf3f3f3f3]
def g_2363 : Nat := 0x111111101131373
def bds_2363 : List (Nat × List Nat × Nat × Nat) := [(m_1744, s_1744, 7, g_1744), (m_2301, s_2301, 8, g_2301), (m_2298, s_2298, 8, g_2298), (m_1780, s_1780, 6, g_1780), (m_1817, s_1817, 5, g_1817), (m_1891, s_1891, 5, g_1891), (m_1994, s_1994, 7, g_1994), (m_2117, s_2117, 5, g_2117), (m_2028, s_2028, 5, g_2028), (m_2277, s_2277, 7, g_2277), (m_1836, s_1836, 6, g_1836), (m_2284, s_2284, 7, g_2284)]
theorem kn_2363 : KnownBin bds_2363 := by
  intro b hb
  simp only [bds_2363, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_1744
  · exact lb_2301
  · exact lb_2298
  · exact lb_1780
  · exact lb_1817
  · exact lb_1891
  · exact lb_1994
  · exact lb_2117
  · exact lb_2028
  · exact lb_2277
  · exact lb_1836
  · exact lb_2284
theorem sub_2363 : ∀ b ∈ bds_2363, m_2363 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2363, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_2363 : ∀ b ∈ bds_2363, canon b.1 g_2363 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2363, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2363 : dagCheckRootsF m_2363 g_2363 bds_2363 (dagRefF 188 (dagTraceF m_2363 s_2363 9 f_2363) l_2363 0) s_2363 9 = true := by decide +kernel
def node_2363 : Nat → Bool := dagCheckNodeF m_2363 g_2363 bds_2363 188 (dagTraceF m_2363 s_2363 9 f_2363) l_2363
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2363_0 : treeBlockF 0 128 node_2363 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2363_1 : treeBlockF 128 188 node_2363 = true := by decide +kernel
theorem nc_2363 : ∀ j, 0 ≤ j → j < 188 → node_2363 j = true :=
  (joinChecks (certBlock nb_2363_0) (certBlock nb_2363_1))
theorem lb_2363 : LowerBin m_2363 s_2363 g_2363 10 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2363 sub_2363 gl_2363 rc_2363 nc_2363

def f_2365 : Nat → Nat × Nat := unpackForestF 0x271590317e5a44965240c5b90536414c8e5840c5788d2221490314e14550257e01560256dec6d7a9b0095768559d2446ad3dab4b6ad1db4546ad0da14c0254c094f415bd0567409ad715c4098d016f529f14964524f1016b4edf101674a5b10a7442591095c424f101630252cf168231bce1702319c945f3258094572417c905b271b09b60269b090572214009471e990126b18990625c0498c415b12550415304530215b0a5302153044d0112e0250c003f 7 11
def l_2365 : Nat → Nat → Option Nat := unpackLinksF 0xe25b8f706e0d85b0360684ca794328632c61887015d3ba1742d9592b21606c0571ae1586834c49812c650c919211ca30c518a114211c20805001f8bf07e0fc1da338660c4980ae25c0b8168ad05a0b41682d05469550a2103c6744e0984300600b89522a0540a09222403540e001 0x10a5a3c95a71596252ce94798912594952968e25692536414c8e585814b3651e2b488852614555452479415e96c725380559f46d7a9b119491a505d2446cd01b45472d3dc34b6ed1dab435c52c61435a96c5a5376559a14c429a14a705459119645c57159784a5915a7c54591493c4edf121604a5b1227446591115c424f18d6f6159d7a6b5a98d616f505ad31674058cf16834140c850385c0c05032580ac6c28d809a6c3517cc4572e17cb05b2415cec6f3719c145d221407a641457031441253029341a990625c10570214412550515b1054c294c0c56c21531c9ac5a630e5301934044ba6c5f9516e34578714e095f7e56de1576654d914f3e52c81470250c003f 11 4 11 7 5
def m_2365 : Nat := 0x33ff33ff33ff33ff
def s_2365 : List Nat := [0x1155115511551155, 0xcc00cc00cc00cc, 0x30f030f030f030f, 0xff00ff00ff00ff, 0x33ff000033ff, 0x33ff33ff]
def g_2365 : Nat := 0x1111115011f137f
def bds_2365 : List (Nat × List Nat × Nat × Nat) := [(m_1744, s_1744, 7, g_1744), (m_2298, s_2298, 8, g_2298), (m_2302, s_2302, 8, g_2302), (m_1891, s_1891, 5, g_1891), (m_1739, s_1739, 5, g_1739), (m_1768, s_1768, 5, g_1768), (m_1780, s_1780, 6, g_1780), (m_2028, s_2028, 5, g_2028), (m_1846, s_1846, 5, g_1846), (m_1882, s_1882, 5, g_1882), (m_1864, s_1864, 6, g_1864), (m_2057, s_2057, 6, g_2057), (m_1994, s_1994, 7, g_1994)]
theorem kn_2365 : KnownBin bds_2365 := by
  intro b hb
  simp only [bds_2365, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_1744
  · exact lb_2298
  · exact lb_2302
  · exact lb_1891
  · exact lb_1739
  · exact lb_1768
  · exact lb_1780
  · exact lb_2028
  · exact lb_1846
  · exact lb_1882
  · exact lb_1864
  · exact lb_2057
  · exact lb_1994
theorem sub_2365 : ∀ b ∈ bds_2365, m_2365 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2365, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_2365 : ∀ b ∈ bds_2365, canon b.1 g_2365 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2365, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2365 : dagCheckRootsF m_2365 g_2365 bds_2365 (dagRefF 79 (dagTraceF m_2365 s_2365 9 f_2365) l_2365 0) s_2365 9 = true := by decide +kernel
def node_2365 : Nat → Bool := dagCheckNodeF m_2365 g_2365 bds_2365 79 (dagTraceF m_2365 s_2365 9 f_2365) l_2365
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2365_0 : treeBlockF 0 79 node_2365 = true := by decide +kernel
theorem nc_2365 : ∀ j, 0 ≤ j → j < 79 → node_2365 j = true :=
  (certBlock nb_2365_0)
theorem lb_2365 : LowerBin m_2365 s_2365 g_2365 10 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2365 sub_2365 gl_2365 rc_2365 nc_2365

def f_2367 : Nat → Nat × Nat := unpackForestF 0x273590317e5b49965100c5b908ea42388ed840c5788d2622480314e145502d7e035602d6dec6d7a5b00b5768d59d1446a93daa4b6a91db3546a90da23802d4c0b4f415bd0567411ad72384118d036f531f14b6452d71036b4e5f103674adb10c7442d910b5c428e1036302d2cf368231bce3702319c945f32d8094572417c905b271b09a60265b09057221400b471f190146b1919062480518c134e0ed6c43540ed4c123806d6c213806d4c113402d0c003f 7 11
def l_2367 : Nat → Nat → Option Nat := unpackLinksF 0xe25b8f706e0d85b0360684ca794328632c61887015d3ba1742d9592b21606c0571ae1586834c49812c650c919211ca30c518a114211c20805001f8bf07e0fc1da338660c4980ae25c0b8168ad05a0b41682d05469550a2103c6744e0984300600c01712a4540a81412443540e001 0x1145a3d15a735962d2ceb4798d26594453168e456928ea42388ed85834b36d1e2b4988922145554d247b415f16c745380d59f46d7a5b11b491ad05d1446c901b3545cd2c63437293dc24b6e91daa435b16c5c5376d59a238451a14c7054d911b645c8e15b784ad915c7c54d914b5c48d81397c4adb1247446d91135c428e18d6f6159d7c6b5b18d636f50dad336740d8cf36834140c85038dc0c05032d80ac6c28980996c3517cc4572e17cb05b2415cec6f3719c545d221407c64128e02934108e021341b19062480e8e0193410d504b5b0ed4c21380ad6c1b531d1ac5c6314d383238044d26c5f9516e34578714e0b5f7ed6de35766d4d934f3ed2c834702d0c003f 11 4 11 7 5
def m_2367 : Nat := 0x3333ffff3333ffff
def s_2367 : List Nat := [0x1111555511115555, 0xcccc0000cccc, 0x3030f0f03030f0f, 0x3300ff003300ff, 0xffff0000ffff, 0x3333ffff]
def g_2367 : Nat := 0x111111501131f7f
def bds_2367 : List (Nat × List Nat × Nat × Nat) := [(m_2298, s_2298, 8, g_2298), (m_1744, s_1744, 7, g_1744), (m_2304, s_2304, 8, g_2304), (m_1817, s_1817, 5, g_1817), (m_1768, s_1768, 5, g_1768), (m_1738, s_1738, 5, g_1738), (m_1811, s_1811, 5, g_1811), (m_1786, s_1786, 5, g_1786), (m_1836, s_1836, 6, g_1836), (m_2028, s_2028, 5, g_2028), (m_1798, s_1798, 6, g_1798), (m_2054, s_2054, 6, g_2054), (m_1994, s_1994, 7, g_1994)]
theorem kn_2367 : KnownBin bds_2367 := by
  intro b hb
  simp only [bds_2367, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_2298
  · exact lb_1744
  · exact lb_2304
  · exact lb_1817
  · exact lb_1768
  · exact lb_1738
  · exact lb_1811
  · exact lb_1786
  · exact lb_1836
  · exact lb_2028
  · exact lb_1798
  · exact lb_2054
  · exact lb_1994
theorem sub_2367 : ∀ b ∈ bds_2367, m_2367 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2367, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_2367 : ∀ b ∈ bds_2367, canon b.1 g_2367 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2367, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2367 : dagCheckRootsF m_2367 g_2367 bds_2367 (dagRefF 79 (dagTraceF m_2367 s_2367 9 f_2367) l_2367 0) s_2367 9 = true := by decide +kernel
def node_2367 : Nat → Bool := dagCheckNodeF m_2367 g_2367 bds_2367 79 (dagTraceF m_2367 s_2367 9 f_2367) l_2367
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2367_0 : treeBlockF 0 79 node_2367 = true := by decide +kernel
theorem nc_2367 : ∀ j, 0 ≤ j → j < 79 → node_2367 j = true :=
  (certBlock nb_2367_0)
theorem lb_2367 : LowerBin m_2367 s_2367 g_2367 10 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2367 sub_2367 gl_2367 rc_2367 nc_2367

def f_2389 : Nat → Nat × Nat := unpackForestF 0x51fd834e014775c130051bd624cab68c028ce9527d2a4ba70b94a91e95218093f9d69f3ad2e842e4eb479f8a93ad0e75270093b9b6b91c8fe391dcc348970b91c8de552e472338f25f1e4ae45a6479278f2471c130049bc0b4f8b26902d2e20ae4405c8168f0d15205a1c123982463045320523009337e49cfc9180497bd94e7b28c024addda53bb42770780249dc51a3894e7209ce4109c4a3009230108aae93db5222ba4b6b6b8ae91d5d21ab94f67288ae52d95ae2b94757286c49115c97b014457256b8d6171a82e3485724eb48e1611a2c14457246020fd55ae1f23f3e4767c8dd452e1f2334f6b87c4fcf89d9f1374b2b87c4cd252e1f12f472b87c4ad0da821b48436807c49cfd1a201243f2b87c48c041b97a4e2f48c74910bca79b35c366a86c4d0bca59a25c2f28e60d70c1aa181342f286020bc81a510342296b052d40a5a41014f272984052c8da811b48236804051c84a6101430104e3c51045a78e134116963457045a38c134116862a92455208894e12472248c444a30081f0f49004d3c351c0134b0b4a004d1c251c013430669a0cd14092501b4d0368a04908040b8003f 8 11
def l_2389 : Nat → Nat → Option Nat := unpackLinksF 0x22c98a861898411fca7f01f637925e407885e207789de07325ca17281ca07189c607089c016ba5ae06a89a626981a416809a00668d9a066819a0660598064117ca5f017c05e097805e017235c816e25b816e05b8168355a556055814e453814e051914224f893e04c992e24b812e04b812a24815200480120047851e047051c047011c046851a0460518046011614581141450114044850a4428108142010423b30ec03a84ea03a80ea03a04e803984e603980e603904e403884e203804e003800e003610d613580d413408b8c2d08b022c00ae12b80ae02b80a832a00a612980a602980a03251890223088c023008c0218c860210484021008401f8c7e01f047061c006e11b806831a006611980603180060017085c0170058213184c0118c46011044400f8c3e00f043c00f003820e003800d0828600cc001 0x16092aa4a7d194b9a28f1850db827aa0471d03e1c05eb11a5834ea829f4452e64a3c51436c09ea611c6c0f86017a705f420ae5c13c4023ab4654c4fe809dcb137872675c131a81fa90371903e1405eb1264f9398626356d1a94a7cf14b9428f0a50da427a80471703e1005e252245b5ca70b95293ea125d3247a54873a529a027a70473905e5009e54a24fb40a10b93f1526c9a41134a369f44d2e81a3cf3439d49ccc13d34239a83f2606f36d724c2e42140920b930d225c2e4804c954b9065023c2e48b4c9325f244ae4093c79239a47f328ee591bca233812651c131901fa60373305e4409e112a459348668112572202e43454834a9088e60d18c114c8c69f14d2e1da3c2b438148cc613d28239783f2006efe939f9233084f4808ef8539eca32f84f4608ebc1351022ae84d4308af2d29e1a13a9205b09e8411ddc1e2c83f4106ee6139c8213aa347429ce25195c279f0476d488d6d719ca232b5c62488c051168982f3585d6a0b8d2164902d23859468b0511b927b624b6a48ed290da0a7b314b6428ec650d8497af92b5b24eae48d55ae28a5c4f6b896571252e2395c456a088d210da0209204029880491051a1f95c5447ea68ed491ba82334e27e9a4ed309ba51334825e8c4ad08939f1233829264504dc9c989313a48870d70ddaa1b134344b864d70c5aa181343c49c76918e4a79a94b3328e5e50caca6921452a29a46514adac15350296904e53095a8123482368042530b5a5163422829e4c52c88a3901431e2882c5704caa0e1341a2b82a57048aa0c134164922a9044d1c892311d69e36d2c65a38bb431429c225181d2c022500f4901a8e02d280324803480128e01da6833450469a06d1439a78634b0a68e10d0c152501242b147f5e8eeb51bd5233a427f384ee349bc01337d25ef44add893b81236f08aac0fcf41b9702f1f04e2007c040b8003f 14 5 11 8 6
def m_2389 : Nat := 0xffffffffcccccccc
def s_2389 : List Nat := [0x5555555544444444, 0x3333333300000000, 0xf0f0f0f0c0c0c0c, 0xff00ff00cc00cc, 0xffff0000cccc, 0xcccccccc]
def g_2389 : Nat := 0x1111115000c0c4c
def bds_2389 : List (Nat × List Nat × Nat × Nat) := [(m_2308, s_2308, 7, g_2308), (m_1761, s_1761, 5, g_1761), (m_2299, s_2299, 8, g_2299), (m_1811, s_1811, 5, g_1811), (m_2065, s_2065, 6, g_2065), (m_1882, s_1882, 5, g_1882), (m_2010, s_2010, 7, g_2010), (m_2097, s_2097, 7, g_2097), (m_2071, s_2071, 6, g_2071)]
theorem kn_2389 : KnownBin bds_2389 := by
  intro b hb
  simp only [bds_2389, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_2308
  · exact lb_1761
  · exact lb_2299
  · exact lb_1811
  · exact lb_2065
  · exact lb_1882
  · exact lb_2010
  · exact lb_2097
  · exact lb_2071
theorem sub_2389 : ∀ b ∈ bds_2389, m_2389 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2389, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_2389 : ∀ b ∈ bds_2389, canon b.1 g_2389 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2389, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2389 : dagCheckRootsF m_2389 g_2389 bds_2389 (dagRefF 178 (dagTraceF m_2389 s_2389 9 f_2389) l_2389 0) s_2389 9 = true := by decide +kernel
def node_2389 : Nat → Bool := dagCheckNodeF m_2389 g_2389 bds_2389 178 (dagTraceF m_2389 s_2389 9 f_2389) l_2389
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2389_0 : treeBlockF 0 128 node_2389 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2389_1 : treeBlockF 128 178 node_2389 = true := by decide +kernel
theorem nc_2389 : ∀ j, 0 ≤ j → j < 178 → node_2389 j = true :=
  (joinChecks (certBlock nb_2389_0) (certBlock nb_2389_1))
theorem lb_2389 : LowerBin m_2389 s_2389 g_2389 10 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2389 sub_2389 gl_2389 rc_2389 nc_2389

def f_2400 : Nat → Nat × Nat := unpackForestF 0x2e25370290329d8d8ac25360290321d54faa8320553a1a8d098a827d401902a1c7d4a6ea11e528eb74758a3abd1d528e0c8148e207d102e0229c0d4e04a702330224bbd45dca2ec3e76170110d66a6b2535919b54f9aa5cb152581fb10f18858b0335817ad1316858b023022099d48cc62a35032a9258c52a7a65504620191b90aa06462322f1e0b0c8a4715032229a140c85c04230529028c8aca009522519124b412a0423004990e10010dc3150043102178487808520ea80211428a0083e06a8020c80826003f 7 10
def l_2400 : Nat → Nat → Option Nat := unpackLinksF 0xa60a609f79f09f09e19599509508e78d18d08d08c183982182081181081081081081075c7417316e56e06e06e06b36926726706705f85e15d15a35a05a056455155055053252152052050246a4514324304214204203b73b03a13a03913903903813803713703612ac2912722702612602601f71f01e11e01d11d01c11c01c01b11b01a11a01911901810cc01b001 0x2d6a575299490c2165c8a370294010b1542d6c54d519c98d94a64242f8515418d80a4e8434a52ac9f4a4ca08b2e051aa0c8b0466c80b550a7a8d298a6465453e90993d144b84340191008cd9426ea13b5299294b5ba52c5255e90a940165b8a2a4312c10c70641022d8506a2834542287c803288170b08a16a706538119a85018a7055305a943ed45eca29d3228913c0f8e864ec2e1011214c062409940269803481b27c85326a970c4892a80c83c6216124c17098b42c73a9b894dbc66d152489911489987ec0335e17ac08d42a09950209828d413462953d462f21148e08a682e0611231010aa0782c38a81a14156a4a6314ea9245407a44886e40311f178e8a46c45321702088aaa04d502098159409c64492d1c2f0c148388a143e0619108c070803150121e0754028a00d502f29168c8a2a445501e990d1b858c4285e102906114207c0832b729d790ea2a73d438c91c314df892e84356209808c0826003f 12 4 10 7 5
def m_2400 : Nat := 0xafafafafafafafaf
def s_2400 : List Nat := [0x505050505050505, 0x2323232323232323, 0xf0f0f0f0f0f0f0f, 0xaf00af00af00af, 0xafaf0000afaf, 0xafafafaf]
def g_2400 : Nat := 0x1010105010f0f2f
def bds_2400 : List (Nat × List Nat × Nat × Nat) := [(m_1798, s_1798, 6, g_1798), (m_1757, s_1757, 5, g_1757), (m_1919, s_1919, 5, g_1919), (m_2297, s_2297, 6, g_2297), (m_1864, s_1864, 6, g_1864), (m_2028, s_2028, 5, g_2028), (m_2038, s_2038, 7, g_2038), (m_2300, s_2300, 6, g_2300), (m_1964, s_1964, 6, g_1964)]
theorem kn_2400 : KnownBin bds_2400 := by
  intro b hb
  simp only [bds_2400, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_1798
  · exact lb_1757
  · exact lb_1919
  · exact lb_2297
  · exact lb_1864
  · exact lb_2028
  · exact lb_2038
  · exact lb_2300
  · exact lb_1964
theorem sub_2400 : ∀ b ∈ bds_2400, m_2400 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2400, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_2400 : ∀ b ∈ bds_2400, canon b.1 g_2400 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2400, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2400 : dagCheckRootsF m_2400 g_2400 bds_2400 (dagRefF 94 (dagTraceF m_2400 s_2400 8 f_2400) l_2400 0) s_2400 8 = true := by decide +kernel
def node_2400 : Nat → Bool := dagCheckNodeF m_2400 g_2400 bds_2400 94 (dagTraceF m_2400 s_2400 8 f_2400) l_2400
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2400_0 : treeBlockF 0 94 node_2400 = true := by decide +kernel
theorem nc_2400 : ∀ j, 0 ≤ j → j < 94 → node_2400 j = true :=
  (certBlock nb_2400_0)
theorem lb_2400 : LowerBin m_2400 s_2400 g_2400 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2400 sub_2400 gl_2400 rc_2400 nc_2400

def f_2411 : Nat → Nat × Nat := unpackForestF 0x18bfdf0977be5ae77c249ef129fde6d77bcda8f7a35cef327dde250fbc4a0f6a345eef693daa53fbada8f75852eeb0a1daa51fb54a3771356ee64a9dcc913b88af771a5cee30a1dc455bb549ff6a93eed68b5dbad63b752476b15eed96a1db2943b642876b156ed728ddac103b549bf6a1490018a7da44fbb44ac800b5fecece1d9cd87b18abf66670ecb2cdd8c4ffb189f764260ec72cdd8c4dfb149c800b53ebe27fd7c4fbb052875f956ebf081d7c4dfaf4a4800b4feba6b3d744fbac8a5f59149eb34a3d6c4a3acd24f5a150eb348bd6451fa4ab1749462eaf4d9d5c4fbab4b4f4936fe93ac5d52da7aa4b2f49c6fea76d3d265bfa4cb7751672ea26fdd445fba4c9ff4f562e9f4c9d3d1bfa4c9f74a672e948e5d349a3a50bf74c250e942add2b58ba54b774a040e9326fd24544005a3f48259e898dfd1c963a363ef44a6fe8bafbd1298fa2530f32355e8649fd0c90f9f2b4741a65e834c9cf8947a0528f3e955e7d25fcfc0c39f493f3e150e6468fcea9b79d53673b13de7626bcec4979d4b0732c57e72ce1ce51b79952bf37e70e6f8d9cdc99b99527f36670e674cdcce14b9a6b0734256e670a1cca91f995237322590012bf9f358792b38725570e5ace1cb44eb9689b72e670e5a26bcb44d3929b0f2c560e4a4c1cacda7928b6f2625fe536d9c9896f94338728160e4c4afc9c973935b2726253e4a2d9c945833e62bf24351e442adc8c573915ab72214ecf92b7c84d678fe36f20356e3f6c39f255f8ab38f1e570e2aacdc759c78a9a4f1c134e33693c665138d12a71a244e3327dc545ab8c6be715167e2f68dc571b38b522715a61e2b473c5459b3e4a7f14164e274f9c3759f8949a711b61e232d9c3699b88233710166e1b2adc3c59b86ca770e457e1b2799f252f7e338efc56be166e1c2c1c37e2b3f0a17cdf88cfbf119b7e1aff08134e0f8d9bf0d6f834306fc357e0b6b9c151937e1a9f02e71e05475c0c0c38151b6fc351dff6a3bfe57b7fcae70025cdff27dbf05ab7f63e6fc167dfb4b9bf29877e520efc166cf928fbec8e77b62defa150ded6adbe48e37c6b56f6a4fdefad5bda90f7b520e7c946deb269bd2d877a4b66ec266dde8b7bcad83794b66ef457dde69fbc44d3779a5ef015cdde68fbbcd0f7612a6ee26cddb2cdbb053b764ab6ec13ccf9287b239c7743406e837cdd2ce1ba44d3741b86e817cd91acfb22daf645b3ec8b5fdcb269b951b3645adec8b57dc7ad1b859c770ab8ee125edc3ae1b8494b645ab6e035cdbf8c9b22d4f6f4ae6dd356dba2adb744db644b56dc470d912cfb6c9536d236eda246d912cdb611636c1b26d8354d912bfb4d9c76b5366d3566da64abb54d3b6992a6d3245da7ac3b4c913644af6d2136d912b5b41183681b66d0354d912afb299c7675366ca466d946bdb28d4b6512f6ca25dd97ac3b2897365126eca245d912adb244db644a967c93fd7eac3b139c3626b86c4a6dd894d9b15583624b06bf457d878dbafc95f60f38ec246cd834cdafc93f60338ec0266d7e48fafc91b3e49f6bcc70d7b2c9af29f35e4be6a9d67d772a9aeb1b75d4b66a9a66d73acdaa697b5c2336b815ed534adadadb35b5b06ae457d6b269ab8d6f571abeae34fd67269ab8d2f571a3eb2134d5c687aba96b5752b6aea4ed5d495aba91b575216ae136d53499ab319b564b36a9956d556c1aaa9b3554b66aa457d532799f24ef49b38ea6680d4fce1a991c3535346a617cd26acfa959c749a2d6a4134d468b5a8c533498b56a2370d262cfa84d634fe36e9fb4ad3f4c1a4c59b4f23469e358d262bfa74d834d6b369c245d356b1a6c8f74d52469315ed318c1a631634c5b0693157d2f6c1a5319b4a5a9694b50d294a5a548f74a528693156d27299a4c54b3e49be9213cd23489a411c34813e69017ccfaacfa3c55347636e7d266d19acda3515b464a267d25ed148cda2857b455ab68a15ccfa4ada24d834262be85347d0a497a1491f4291fe8523bd0a46fa148cf4249e67d244d076c1a0b19b414b367d156d002cda04953400af680156cfa29d9fad833f53667dc57cfb2ad9f44f33e499800953cf54bf9ea94f3d528e77345cef49f9e214b3c428677a47cef48d9dc924004a7e11562ce26d39d55f338d2fe7436cce34b79c695f3952e672364ce34a79c459308a37e6f936cdf2699a8d273512466e37ccd547f9b4d333551de6aa37cd74799acd1335519e6a144c228c79a25fb344be664465cc96bf99d1b3325ade64b57ccb6d9995193325a9e64164c226df90f9c330fc0662670cc32a990ed7f2fdae65fa38cbf26990ed6f2f3c065e16cc876af97257b2e4ae643b56cb48c9968d732d11c65a134c876a7965e0321d1de54670caece195c5132a1af65435acaace19545732a1ab654352c8747594d58321d1c64f670ca328993c97b284ae64f256c9f47993c94b21d1b64d95cc9b27990e8cf241ad64c258c904bd92c8f32412d648256c9347992094b24094e48121c8726d91093f235ae64424bc8848f914933225aa644243c87269844d8f1eb38642134c816a390257b204ae63d156c7bce18fc5731edab63d936c7b2698f453b08931e3ba61c774b38445bb12eb163a239c4b8c78e31a71c634625a6fc68ce18dd9c31a12f636670c684bb8d55831a12e634255c4b4c78cb9cb195bf625a4fc5fce58bf5cb17d3f63025cc5f4e589690f176b1625a41c51ce18b39c31649a628b51c57ce18a257b156b062895cc52ce18a49731449f625963c4c6bb898d47135ae62613ec4b28784451b08eb1623a65c474c98471bf11122e22244c238c788495708db7620560c236c587b5c30f632e11a6fc234dd8699cb0d23f61a37ec378c98689fb0d4aa61a129c2349f85d9cb0bab961737ec2fae185c9fb08d23e16562c2348d8499c30a33861415cc246ad84c973090ab612136c232c78444f8004a5e0ca4fc19487832907069aee0d351c1b6b98344fb064a1e07946c1049f82091f04123608b5ec116ad824933044ab60812bc0f27c00250eecab7e0434ec0849f81317302494604243bfb8a97fe93f015ae5ffa4bc032a17fe91f00526600354bff4877f6d52ff122dfe244bfb4b376558efe538df9457bf7acb7e496efc92cdfa270bf38ab7e495eec9b75f856cbed8df7dc9c2fb633df6364bb24df7b79c6fa52a5eda6bbe68f97cc5c2f6d33df0e71be34b97c29aaf85335eda45bdcac37b916ef74b05ee457bdb48976498ef65aa5d925fbc6ce57ac99af1a3f5e8f80bd2ce17a4972f452a5e3373bcf6c978c9faf1eb15e3c6fbcbce178f18ef23385e425cbc74c778c912ec92dde234ebc24a9784912ec929dd9d6fbbe4ab77c952eceb1dd9a6fbb34dd76698aecd2fdda672bb66ad76c95aed3385da27ebb34af7648e40049fcaf56fbac2757584daeb09add6134b9c6b3738962e70ac5d4351b9c2ab74c122e7527dd235cb9d49773a91ee85265cf354b9e48973c4a2e7521dce15495eac7734da657a37dcb936b9726972cd6657a2fdca359b8cce5724552e32b95c6e72b8d6fd71a4dae349a5c636195e8af7139e2e25b05c1457b822d1704596e0e2fdc1c57b8368f704592579b7da0671b78f016f1a02df7385bc470b7b2c96f0df2de49a5bc370b40acf6ea4e2dd49a5a036bb722f96e45c2d01b3db835cb406b7680d5ed011ddb615cb404676d4d72d009fdb324cb662c96cc4f2d009ddafe71b632696bedaad7db35af955b5f25b6804ead009c5a0137b50ce36b48f2d41355a8266b574796a096ad412b5aa12cb5047d6a4552d4094da8121b4026d6804d6d31365a6260b478af68e96ed1d2bda3a4bb472476804d2d149e5a0a44b412c9682572d049e5a013395e6c7678562cf0aad9e15495e6bf63f9cace4b659c374b1faff665e02cd49a599138b334716644d2c7e39d97965b2f2c963edfaca6b1595670b2bac16544d2ca5b1d8f938b276e563e4d6c9134592264b208df640d8ec8137d90263b1f2692bcd6ec691c58d138b1a26b6344d2579a9d8967fb172696269a2c512e58a254b132c96259ce579a5d88264afcce3617e02c3532585e80b0b2f95f959ec17c0584274b0591960a912c14a257e46bb032895f916ebf738d80670afd8d55fa4dabf49a57e14e95e4c75f4992b773957c16caf72e95bb5febcd3a57a16caf32e95bb1febbfc0577a44aef2895bb1cebb09e576134aeb2895bb16eb99b8d74134ae66d35cc592b74bf56f672ade8fd5c59c2b7a3956f37eade26d5bc4d2b74a74af25bada2795b44d2b64a2569c5bad48b55a84dab552556a134ad329d2bc94eb02b7d60567acf2c9580dbeb34b256647cac06d75948eab01b4d60367ac76f95891d2b15b2562134ac06c7582dd2b049a56035b95e2df57c9c6aaa2bd5e251aaa68f575596aa92dd5c457aaa4b356c9c2ad62ad55257ab34cd55492eaa91dd57457aae6b755cd2eaa8b0d55b69aab27d55452e578b755413caa648954c512a7e35d5235ba9f2a95451aaa7ca755035ba9f2792bc58ea749b54e35995e2bf5349929db3954ba74a972e94ed1fea4bc054a13ca924895245129da39d48369a764fd4ec9b2a31b8d46369a762fd50f58aa1db7d44670a876c74ec5529ff3953fc7ea83ce14ff1ca9fdbf53fb72a7f2fd4ec53a9deb153e264a776df4f59c29ddb1d3c259a774dd4ec4f2578add39b59a734b54b79ca9c33c538174a5b6ff4d7e029adbe536670a6b2694b6dce995bf532b72a654754ca8da9949b52db61a63d014b65fe98134d30251a5b2fd4b8d86970a252e13ea5b2e52bc55e95927d2b24ba5648f4ac90e954ae528a64a512a94a253a9449e4af153a11cff4971a292db4525b64a4b2c94239ce84639d08c6ba118c7422dfe915b8d08b7ea43269422dce8f5bed1eb4da3e4f947c9328f49b508b72a116df4711f28e5b651c134a116d7422d9e8d5b6519474a336c94644d2845b1d17c78a2f7194225fe8adb5515b66a2b4fb4225fa8a49b508972a268d144cd92844b7d11265a224ab444952844b750e672a1c6fd438dca870bf50e136a112d54351c2844b3d0a672a144fd4289ca85136d0a25da112cd4244da844b14af13f9e2adf41a9568352a4f1563a0b4cb3c51be8212ad042549e28bf4039ca806b9500a6da014d940558a804b04f14579e24df3fc5427f5a3cf126e9fb2c13f515e789314fba469f72533c497e7c7394f8d729f14fd3e291a7c494cf12579eece33dc4da788b1cf36729e66fd3ccdca7a5324f317e9e626d3cc4d2788adcf19369e32693c454e5789f4d867f9df2b93ba992774b24d86739da2cd3b45926c13f4ec12c9b04dd3ad9ca6c1334e156f9d32a938558e709b7ce81349c26c7384d7e7349a4e135b9c26af3944d2709a9ce1a6e9c34c538697a70d2d4e1a569c34a53844da6c1264e01569b02fd3635be6f4aa4d8d639b12dd36257a6ca2fcd94539b24bf36494e6c927cd924b9b248f36490e6c49e4d801895e27731d9fe6aa344d53689ab4a135459263b39cc74729a690134cde2638bfcd1a6a9a34d131c5fa685b44c716f99f47b33c962638b74cce729998e533558a664a64c716a9976e131c59e64b394c937299347b324982638b34c795498f29931c58a5789bcafe7f98b2b9312992624b24afe739874892bf1ce6149e4c224495f8d73044f2605224afc6397f2cd2be9fa5f4aa4afa6e979ce52f25b25e4a24afa6696cadf2ec5525b2b1cb6c5f96d8a72da97e5b529cb6a4f96d4972da91e5b521cb613c95f4892d2dc65a4ab4af97e960adf2ca952594aa4b05639606c72c0d6e5851a4b035395f2792bc4cc0049dbce56f95b259296d2e52d1fcab34c9564a92ac0a252d1dcaa04094b46f2a48f2545a24a5a3394c47b2988e65311aca623194b0652791624f1aa4a3a5d9474b92789664f4a6ca125c9424892845724f497c9f34893f09927c0c24f493c9e15879cac72749864cdabc9c4669334772668e64d53049a36693346ef3918a4c134c9816879c6df25a9764b52e493a5992829b2545724a097c941279272b0f38d7e48e2d491c589234b32179ca4862c485d7291f4732171ca476b448be72917ae522e9fa45d2ec8c5629174b9216986432b148a23990c8c52185be43eb1487c6e90f49321853643097c8612790b2c0f38d5e415adc846709056af20c4b2415a5c7e4688fdcf11fb1e24023448024c8fd4c11fd1a23f4b047e35779c4df1eed3a3dda147ba458f70851ed5a230338c605708e2f011e55a238b404715808efad11d79c23aeb84765608eb4b91c4dc23a2384744688e24f91cc97238938471e708e3ae11c45c230233c7026c8c04d71bd5c230133c6e4688d8ce31b49123613546c2668c04bb197586343384685708d06d91a0d82346b04682608cb8af196d6e32dabc65b4b8cb68f18097232522462b6c8c54d918a9323149446024b8c14b9184972304b046024779c4c717c4b22f5a5c5e45879c4bf17410a2e6b444d6728b569516ad1a2d52344d5728b38c11629d22c4bc44d47f8afcf1155e022ab40455e708ab4891549b2269b9c5446889a4fd13758a291b445236489b8df1455c226db7c4db6389f259136d2e2733844e24489b4c7134971e712dc4c12c89769712697224d2244a14d893250f3894e162b7c47a5588f4a90b158e23532c2c46f88a4ab1149521622fc4425487fce50ff5ca1fd36c3fa6c880ac51004f62009ac4012587f2c10b115e1f2b443e15087a68f0f4956161b7439561873ce10e75c21cdb643a5608732c10e515e161b14382458586bd0dcd12161a942c26f86b2a10d4d1e161374341608678af0b098a194204322468584bf0b39ca1852b42ce7085f4c90b2dfa1653f42d67085bac10b41021652342c25779c48304d9fe15522426d688534b909ada21422c42845084d4c909c492134b4413673826ae5093a021253641337384649908c9121153641336b8424990849120fd3642012483f25104cd8e0eeb7c1e25483bac704cd420da3541b4688364e306c9020993f413d6f8328b106455209eb1c13a638274b705c49209d29c1396f8272bf04e55e0a0b741415e82729b04c4a1e711dc07e7f8236b90411a2084ae41016880fce703ad76075ae407c72810adf034552042b1c084628178e10205be040afc09e708138c102055e0463740814d80f2a0f388dde762fc0324980727f00e4ee01c9bc0401880726700c111e7629c0225979d6bf00409600524bceb4f7ff492fe5589fca313fd5627fa4dcff4095fc928bfac527f52befea4bdfd493bf91507f34b2fe4175e75a3bf75687ee4a0fdc541fb5a3bcea5f7e1ac2fc99c1f92b83f45607e46c0fc89b1f96b03f21607e18aefc295df8523bcea537df08af3a93df5eb13ee2647d78defb59c1f5db1beba6e7d704af3a92df4d223e99287d304af3a90def6b7be7b587cf4a8f7b58def5b1bdeb5b7cb248f944a1ef5a9bdea6e7bf8bef7f14defd29bdfa4b7c3248f7e90defcafbdf94f7bf28ef7a4a1ef412bcea3b7b5adef73161ee52c3dad637b58c4f6a135ed4263cea377b3492f3a13dec528bce8477a38bef5a9b1eb4b03d1c577a36b6f52951ea4943d1b537a7250f46d2de8d2fbd1a577a348ef3a0bde7a2fbcfb6079f2c0f3d15de7413bce04000126ed295bde5c9b3cc022797268f14d65e2d27bca35c78b496f22d71e44a83c5a4778f498f1ad51e34943c5a4378b296f14551a52b1bc345f7868aef0c56de14b234a36f768ce2f044d1da1b5bc025477e4e0efc5f1da1b3bbe264768476ef2591de4ae3b423376fce2eec8f1dbd353ba16076f4ccede4c5dbc94bb813c76f242ed04d9da52dbb61607694aeed24adda491bb41346946c6ecc511d94a5bb21546946beea39c9d7fc03b023875f268ea31cdd74b23a8b7e752ac4eb19c1d66b03ac23c7526c6ea49bdd57383a92637532a8ea44add449a34a35b74f2a8e9c4add349a34a35374b2c8e739c5d13c03a248c747278e88911d17383a21447398d6e7f16dcfdadb9fb4f73f686e72951ceb38b9e67073a8d4e744d9ce52734a2637372c8e259c9cd13a39a1747128fee5fe01cc49e397a4472f288e251cdca9b8b9613472a6d2e54591c493f38fd6271f8c6e3edbdc973838fb6371f69ee3ed0dc82b139024d71f29ce24951c4f39389c7e71bce0e271c9c4dbf389936714ac4e289b9c56b038a262713268e24939a512db86b4f70f268e1ad0dc34a7384a5470a26ce144d1c252734a2537074e2df315dc16b2b7ca5b6f94b2e049c1c062ab7ca576ff4ccdf292dbf5adb7c9616fa6d2df44f9be4a5b4a16e6caadedea955bd52a3655636f28dcde5189bc52ab6536e6efac2d94d89bb2b137626e6ca6b4d949bdb29373652626ca4bedc99c9b91bf37227e6ca4aedbd9c5b833837037c6de8d4dbc4d9b28b1b69e726d38fcdb59c1b4e39369b7e6d66e0dac991b4cbf3699366d3268d9456db409b3681346ca2a6d96df9b2db7365b666cb2fcd944ada509f34ad6f6c7268d88d65b10aab62154695ac6d82595b04b234ab6f6bbce2d764e9aec9b35d9356bb268d2ad8dae0aab5c1546956bed659c9ad4b235937e6b226ad644d1a55adb579356af268d2ad4dab5b4b4a96f6ab6b2d2a57da9f39353b616a72fcd2a55da79bf35213469e6e4d3c5f9a852a34f16e69f4d8d3c599a549fb4b47269a6b0d34961a58b734bb606974c0d2c599a549bb4a12e001266abf5bda39a934735068e2bcd1c5719fe2ab3fa5868b090d00d3da262e34034b6874a0d00d1da15a6341c54683270d00d0da049e34014b67f2a8abf58d9f4b22afc6f67b6f8ceed6d9ddabb3c13c677276cec51157e31b3a13c673296ce455157e2fb3795666f2a8cb99c9972b933617465c8feccb58999637b32b6f666ac4cccd899949b32e36065dadecbb58d9763133056465d6decbc4f1974a9b2e16c55f8aecb49918fb38b2c26464ff00c9fa019533832a14464f8e0ca55c193d3e32816464f2f8c7d59d92e3332595e64b2b8c7c5598feb0b23670646ae0c8cdb18fe2bb1fb5763f69ec7ed1d902b0b2024663f26cc7c53157d31b1e264620ce4c709d18e4b631c174620afec689518d4a631a154620ae6c64591880bf316e7262d2bcc5d5898b4ae310156621ac4c431bd88631b145706216dec42d3d885a3b115626226c4c449198849b31014c55f4b6c3a579874ae30b95661869ec30d1d865a530c136617298abe94d7cf3fb0a15c6104c8c22571844aa3081645f3ce6c1c9d17cebfb0595c60b2a8c149917ceb7b02c706062d8c0c5918153e2f9d676022ccc045917ccbf2fa56f5ff2a8be958d7d237afa45f5fb6d8be915d7d1b7afa35f5f46aebea9b97d52b2fa1365f3298abe92d7833faf815c5ed4c8bdc5717b4b22f06735eb2c8bc05f9786b7af41545e1ac6bc2dbd794aa2f0b5f5e16aebc4d897849b2f014c55f486bbcdf57062baee47c5dbacab82d6d7662aae0b575d5ad4bab5a1755282e0b475d1cf0ba2d81744b62e84575c12c2b9651973136ae625d5cb278b8252d720b32e41645c1276b84599708b22e1a6d5c34bab844f170499aaf96e592adeb791656f22c2de158592ac6b2518d6e2b92dc37e5928b6b2514d6cf38ad995e5b32b8b2458d6b7392d84685ad2fcb5a5796b4ae2c915b5a52bcb4a57169926ad32455a647ab4c8d56949e2c91535a0ae4b415a9682b12d017e592286b395bd674aa2ce563592272b275bd664aa2c9d635938c6b2716d64e29aca45a59329cb244c557ca32b056f58d8aab1a555634aa2b056358a2cab1459158237ac3945587288ac118d5822fac0e725838a0b04551606b92b045757f8caac05bd5f6b42be3475602dcaf45b15e62bab01625768caaed155580afab76725732acadd9c15ba36ab867056e8baadc5f9580abab0d665618fcad5191584bf2b34645668a8accd51584b72b16705628d8ac4db1584b32b014f55f25c0024ad396b7aadb5255b6a0a83155564242a624f5576b8a9892d554282a6247553498aa4d5153121aa6a4e54d494a9a919535212a60225416b0a94921508a7aa3250547078a8c141508a3aa1b4654329ca844f5504ac272d6353f6d09cb1bd4ed2da9e67053b4aea74d2139631a9c3584e58bea6ad694d5ac295e7252bae4a64de14ae3fa9656252f4c8a591bd4b137a9626352b6c09cb15d47630a93a6d5274d8a3b15d49636a8ea57521acca451b14853328ea4f51e8cca3c99947523a72b6250aadea2a9554552a28b14d51628aa2c495454ac28556350a8dca1518942a2f28526f50a4bea179c943738285c7250b4fca1495d395a527345f50468aa0a8fd4151ba820444e68a69ccd7d40422a7334f4fbac49fc8f93f42227dc624fb0ba9ccd1d3e1aaa7c3454e609e9ead753d5a6a730474f26a89e415139e2fa7856c4e78b69d99c13b1b627606c4e78ae9d35813a5ae2745644e78a69cc0dd39418000927002ade9c49713692f26fb5c4df6a09b4949368af26d15d4da2b89b45493262aa649584d78ba992555329a7a69d704d38b8994d2d344282653474cbae099ad3133420265c544cb270994d0d324aa0015634c32d09865953122fa624574c32c80051bd2f4a425e9454be6b697cd5d2f4a20014634b92b09725552e4aa00145f4b42b49685592d0aaa5a15449ace49655812bcaaa584514af2a89355c92b4b62551784abac09545d126a3fa53d624a78de9349812973f24d16d4a0ade94158d286b225036f49a2d893c55126eb124e16449b8de93458000a2ba4c164488ce292c59123bc024a16448ed009239c12452224747048e4f891c5f1222b3a44c664892bc914d59224ae2442560024c690c5911d339241a744832e88e95fd204a623fa5447f2a88e95cd1f4ba23df8047b4888e91cd1d13f23c164475ce48ea5791d4ae23a2560024b68e25791c4ae2382560024a68a79fd1b4ae234a6446a2b88d45511a4b2229e734672d88cc5d114ebfa3195c4632a88c459114eb7a2ec7045e2d88bc591174be229d6745b4888a71cd16522229c6b4574888a718d14e2da2a1664534fc00492d1133fa2815c44c4c889a571134aa226164444ce689491111239a242444448d688c91111231a2227e00248680d17d0fd2121fa4043f29a864d150c8a421e34d43228a8668fd0cd1da1c35043628086c1010cd1ba1a12843346686451101a29a181554066be85c4d5019a9a1614540669e854515066b121445042528a84cd05094a220cc624196de8445150762920eb5f41d4be83a94d07497a0ca5041aadc834949064aea033474078be82c931051a2a0a1454078a682455501dafa081354076a681c51501da7a045624088c4814d490212e20415d40768e80c4b40091a1ebd6f3d7ace804590f5e37a001643ffaf87af1acf5e339fe3703fb4e47af194fe63e1fb5743f78c87ec510f5e319f8e783f32a87e39c0fc4b61ebc573d88be7b115cfb4aa1ec35f3eb8d87b0d6cfa5381ec3573e64c47cc980f61aa9f1b6c3e34c07c3190f849a1ec3533dcad07b9580f71281ee15c3d868e7b49b0f65aa9ec12d3d74680045bcf55be9dd4573d38f87a5594ee9ad9e84553ba6ae7995a8f32b41e61503ba68e7939e0f25b01e44573ba2c278adc4f14a31dd14b3bf6e277e598f02371e04623bf2c87744eceedb89dd9663bb2c87744cc008b71dc264387ce276c570ed5321d87803b34c8761a00ec13e1d817c387ace72b584ea3381d45703abac0750d80ea1361d416c3958ae72d144e8ab01d14603a24b8744940e59a39d056039649673d580e59239ce03839647e72c8ece66301cb23739768872c8cce549e1c3b443908cc724940e45ab1c82343872ac71c550e22b09c4e7038b2a87135c0e25361c445738727800458cdb2b09c15703822da7045b0db22b9c067837f8ae6d85b4df6369b6157379acc6f51b0de4b31b614f3768cc6ec598db0a39b8d61372ae06e45b0dc62b9b612e36f4d86db15cdb4ab1b612d0022c46b3194d95371b3b6c3676c06ca988d94b71acc553634a06b4d54d81291b025035a68a6bc970d6daa9ae25c35b68a6b44b4d651a00115f3574c864d9c8d54b61a9a743532e864d5fcd44a61a7a5434f2a864d5ccd352a19cd6234a4c8694590ce6379a3a4434728867318ccea2919d35f33a6a6685180ce92f99d25333a47e6748ecce91b99db4433b2486748ccce49e1933443378ca64c9f8c993619a2343262fc664590cb33919815432fac46588d0cb0bf19616c3262ac64f588c9e37993c633272dc64c4f0008ad96de723232a863117cc84181901443188b663c5b0c622b98e1443188a663055cc65ae98c1562dbce0627a00c4f3c18a5703132e85b71fcc3bc018747c30fce061c510b6e399861562db8da6159c0b6e2e973d623072885f6d3cc14101821342fb696604940beda397fa382ff2685f6d0cbeca397e24d2fb28c5cf580bdab817b5682f78c05ec590b9db7978e702f16d85e5580bc49a173b632e76ba5dd580b9da69745622e8ac05d0d74ba6b017434d2e725a5b68d0b8f401725702e34685b65fcb81b297035d2db2fc5b91b4b70a316e12c2db2e400455cb551f96aa3b2d546e5acd10b551996a13c2b468859b17cb44a2166c5b2cd8ae59c510b3629963d602c869e590d2cb21a39643432c72b8568990afd1a160b5e2c16b4582d58b05a91605602bf2c8568558ad91a15c34f2b8696574140ae1a395c3432b78a056c550ad0aa15a13c0022a64b99fcabab21574642af8b855c590973399564502ab2a85555c8972b31541542a7ae24b91f8a56b79522402a18a8542d50a84aa14ad6329f288539188a762914e2502958ac535184a55b714c25c2968ac52cdb8a549692e23428eae851d230a4530147c6428f6f851c8d0970bf94446628b6dc511190a26b414445625c2fc5079c4a16b8141d662832884b85c89e6ba13cd642798c84fc9409ea3213e25027a8a84f4d509e51a12e16f2748c84ecd789d22a13a35425c2dc4df9c89c6b8137c7e26f2fc4b85a899fc0133d7c2678f84d19c09a23613436c2674684b859c97f3913235625fce04c4d1897e3612fb7e25f6d84b8598974aa12e16200229e3eb9fc964ae12ba642572c83eb9cc954b612a2741f5afe4a4570945320fad6f24f2c849c9f07d6b391856f24a4a84945508c2b19242642308de48c9508c22f921b602434d846115c8c62f918c532316be462d3c8f12e11e25023168e46297c8c529918a4f23149646cd708c52391a1242314864640a08c51d91813c1f56884528d08b49211496622a8dc4551888a4b20faa7e2278ca3ea9b886f3911215621bce04459c086e2e90e56221f28c439580876b010e34d21b4683ea99885eb790c154217ac63ea9708511a10a1561f52fc3fd198845281083561fe46841c4907f8bf1063641fe2dc4119c0826b01041241fe2cc40c8d07f8290ffa341ff2bc401580806281001241ff2ac3fc1407d4ab0fb56f1fb2a83ed58c7da378fb45f1f74d83ed15c7d49e00114b1deade3e25547c4aa0ef5631de2de3bc57c7af390f597e1eb2883bc55c79eb78f44581e7ac63bc51878eb78f21541e3ac63bc4b877eb78f01541dfac63bc4b4008a505de7f1d7ad03b457075eb20ebc641d72c81779cc2eebf85dd731d32c83a59c42eeb905dd6f1cf2c839d9f02eeb58e5f801cb0e017759c71f380e3c6c1c72d838d9d02eeb18e21740bb8fe3845902ee378e017c0bb8ce37d1406f4aa0ddd721bb8a2177198646b78da4581b48a836c9006d1aa0da154191ac63231bc646318d85611918c432317c6b6b60c8c5b1a9ce03529806a4300c8c571a5ac034ad70695280d25641918a6344590645b78d01541916be33a980674b60c8b5719b28832d188659a08cbc5219768232c940645ab0c94621934b8324d586449685da3418ab003151d062e380c626018b6c83148d02ecbf8bec7117d6d42fad98616b40beb5617e6c22fc9685f92b0bfc5817f2802fc9185f49205d97e16dce22f55c05b6330ba5611758c02ed1405d5280ba35616d4682e44905b4af0b756116f8c02dcd585b4ae05d972163ad02c71d058e320b24581674a02c8d90595280b23541634681765bc576348aec5915d8b02bad94575b205d96e151ce42b59c0546b90ac5621514682ac490544bf0aa1241512bc2a5588544ae05d96a149f002935c05263e0a567014a8c0294db05251a05d967130ce4289168514280a2456130ce02611c84c23089846013fce02611444f73809835d131ac4270d284e42009c346131ac0262d444c5a809a5601316822655804c5268981240bb2cc25a5784b4ae05d9620ffafc1ff5c83feb707fd6a127ce01ff5983feb107fc6611a8dc23518846a2f08d45a11fac023515846a2908e25011a6ac2344b43fd1a08b4701176c022c4903fcbf0892341132482245703fcb908746810e8b021cd903fcb708523410b2482145703fcb50816701028c020d58040a28081d601036a02044903fcb308015c0ff2c41761482f2b787d9540fb0a817958c3e4b205e46f0f72a817917c3d4b605e4570e98be1e25103c422074c530ef2a81d2d7c3b4a2074b4f0ea4a01d45703a5a385e2340e74681785bc3949205e16e0e1ac21c51443851a05e1620df46817857c375aa85e15e0d7ac41b514835d1a06c1240d72dc17856834738068c6c0d2ac01a4d703451a05e1570c5ac418b580336b0062b4d0c88a41911403262806423d0c524818c4903142e85e1560bc2a41808d0304920601540bc0be17a8d02f4b605e0570bb0a000451c176b785b4590b706416d160176b185a67105d8c61619c82c2b905837e05d8b60bb14c2b63102eb560a9ade1545502a6b182eb4e0a1ce214d5c02863305095e0a2ac2145158284ae02e96309ace413d1a0268bf04d15e09bac4134570174ad84b15e0962b812c4f0174a9848d72091ad4123588244bf02e943089ade11c550226b1844b630896b61144d0225a982e93907cade10c5501f2b183e46307c8b61045101f22983e36307c6b60fc4d01f1a983e14e05d2620c55bc1e62c031563077ac20c51881d2b103a36e0628b40c51481c4ae03116306f2b80c456c1b0ae03613c0622a60d45b8188a08334620668a40cc5301889883101f0630780c404c1742102f14b05f2780bc50c17420001146003cfe0b45701613202c164003ce60935bc1512a02a154049ac609517c144a202545304a4be09494c1292782524b04a48e09490c1249e001b440462cc08c59000d3f0221540034dc07f9c8104ab01fe7003f2d800699804eb781e154013ac607459004e37809c630372a802717c04e2d8196700322d806418004e2b8181440138a604f1b809e31013c5e0278b40535800a428013c560278a402653807a2f80f45301e6be03cd4c079a780f34b01e68e03cd0c04ca600e1540148dc029188064a200a45e017288029148050a700a14c0130840069500411a0081560032fc0115bc034aa0045630082dc013588026b00041560032780095bc014aa00256300325800450c0049180003f 12 11
def l_2411 : Nat → Nat → Option Nat := unpackLinksF 0x3deccf7913de40f780bdd65f748bdd01f7403dcc2f6f9fdbc1f6743d963f6393d883f6203d823f5d1fd740f5b8fd6e0f5b83d6a2f5a83d6a0f598bd5c5f5703d563f5583d560f540fd500f5403d500f5213d480f510bd3a5f46c3cf34f3c07cde9f3137cc21f3007cb84f2e03cb61f2d07cb40f2d03cb21f2c07ca08f2423c8c2f2303c8c0f2287c8a0f210fc729f17abc5e0f1707c544f140bc4c2f1303c4a1f1283c443f0f8fc1b2f00b3c020f0007bf84efa23bd0cef403bd00ef11bbc21eed9bbb22eec83bb20eec83ba47ee903ba40ee887b9e2ee707b9a1ee683b962ee583b941ee503b940ee38fb807ed653b371ecd07b2e3ecb83b2c1eca87b2a0eca07b280ec71bb1c0ec703b144ec503b140ec313b0c0ec287b081ec203b023ebd9baea6eba83ae81eba03ae80eba03ae04eb51bad02eb387ac64eb183ac60eb08bac01eaf87aba2eae83aba0eae07ab61eac0fab00ea7a7a8e8e9b47a606e9233a3c6e8e87a3a0e8e83a362e8c8ba1ace850fa0a5e82079f88e7d879f41e7c879f20e7c839ec3e7b039ea1e7a079d69e748b9a57e690399e3e678399a2e649397eae5f8396c9e5a0b952be4bcb9264e498391a6e4683906ae41839041e41039040e41039002e3e8f8fa0e3d8b8f60e3d078f40e3c878f20e3b0f8d0ee34038ce1e31938c60e31078c40e2f138bc0e2f038b25e2c838a66e298389e4e22ab8824e200787e1e1f838745e1d038721e1a938605e180385c2e14978520e119b8460e108b8366e0d838360e0d838341e05bf8160e05838160e05838141e029780a0e02078080e01878060e000f7d18df3877c64df1837c03df0037be1dee8b7ba0ded8b7b22de6b379a0de6077980de4137900de4037900de30b78c0de30378a1de2837881de20377a7dde837781ddd0b7740ddc0b7608dd49f7501dd2137480dd2037423dd0837328dcb0f72a1dc8177200dc70b7125dc19b7060dc08b7001dc0037000dbf876df0db7836dc1db4976d20db4076d00db4036c65db1836c41db1036c21db0836bc3daf036bc0daf036b25dab8b6ae0dab076ac0dab036aa1daa836aa0daa0769a7da6836924da4836920da4076865da08b6820da0076800da0036800da0036800d9f8767e0d9f8366aad9a836643d8ce76209d870b6163d850760e3d838360a2d7dab5f41d7b135ec0d7b035ea1d790f5e40d79035de3d768b5b91d6c8f5b20d6a935aa0d65ab5960d65075940d638f58c1d620b5861d61835803d600357e1d5e0f5780d5d0b5721d5c075700d5b0b56a1d5a835662d59835660d59835660d59835660d569b5489d52035480d510b5440d51035440d4f8f53c1d4aa75224d478b51e0d45935141d44875047d41034f0ad3c034ee1d3b834ea2d3a834e62d39834e41d39034e40d378f4de0d37834d64d35834d41d35034d21d34834d01d31974c60d31834c60d2f174bc0d2e874ba0d2e834ba0d2e834b81d2b1b4aa1d298b488fd22034861d1f9347e0d1f8346aad1a834681d181345e1d178345c1d158f4541d15034540d148744a4d12834462d11834460d11834460d11834460d11834387d0d0b4340d0c874320d099b4260d09834241d09034186d06034180d050b4140d02973f0dcefe73be0cef833be0ced933b60ced833b60cec8b3b20cea9339e6ce1b33803ce00337c2cde873781cdd873760cdd073721cd8273508cd4033500cd28f34a0cd2833462cd1073421cd0073400ccf8733c1ccc1b3246cc9033240cc80b31e1cc70731a1cc6073180cc5873141cc21b2fc6cb8b72de2cb7832d64cb3172cc0cb3032cc0cb01b2be1cae8b2ac7cab032ac0ca9132a40ca9032a40ca9032948ca5032902ca30b28c0ca3032882ca1872860ca1832822ca0832785c9d0b26c4c9b0326c0c9a8726a0c9a072680c998725c5c970325c0c95132521c94832501c940324e1c938324e0c930724c0c930323c8c8e872381c8d872341c8d032321c8c0721e9c7d571e67c79831e41c79031e40c76971d81c76031d61c75831d60c729b1b89c6c131ac2c662b184ac610317c4c5f0317c0c5d1316a5c5a831681c5a031661c59831641c58871528c54831501c52131480c52031480c52031461c4e9b1381c4d0b12a5c4a8312a0c498b1260c49071240c48871220c488311e2c449b1101c44031100c43871083c3b3b0d6bc35830d60c33930ce0c33830c64c31830bc5c2e0b0b23c2b8b0ac1c289709e2c278309e0c278309e0c270709c0c268708e6c230708c0c230308c0c228707e6c1f070782c1d0b0740c1d030702c1c0306e1c1b830645c10c70211c070b0182c06030161c05830160c050700e3bfe2eff42bfc0aff00bfb86fee0bfb82fec1bf98efd0bbef2afba1bee06fb80bee02fb80bed0afae3beb06faa1bea06fa80be90afa40be886fa01be612f980be602f942be21af861be00ef800bdf86f7e0bdf82f7c1bde86f6e6bdb82f6c1bdb02f6a1bd98af641bd78ef5e0bd68af5a0bd606f523bd482f520bd406f4e1bd20ef461bd182f460bd106f3c4bcb9ef2e0bcb06f282bca02f261bc88af220bc882f1e2bc60ef180bc586f122bc482f120bc406f100bc402f0c2bc112efa5bbe82ef81bbe02ef42bbd02ef40bbc86eee2bbb06eec0bbb02eec0bba86eea0bba82ee62bb982ee03bb49eec09baaaeea81baa02ea80ba90ae90aba30ae8c0ba286e7a8b9e82e762b9d06e721b9c06e700b9b86e6e0b9b82e683b93b6e236b8806e127b8482e120b838ae045b8102dfa5b7e06dec6b7a86dea0b7a82dea0b75aadc0bb7002dc00b6e12db80b6b96dae0b6b82dac1b6896d928b619ad860b608ad820b6006d800b5f0ad7c0b5e86d6a8b5a06d661b5792d5e0b5782d564b5582d4c5b518ed403b5002d365b4d06d2a5b4a06d261b4906d1a5b4682d1a0b4606d180b4586d141b402acfc2b3d8ecf60b3d82cf41b3d02cf40b3c86cf01b3c02cec2b3b02cea1b3a82cd89b3222cc80b3202cc42b3102cc40b3102cc40b2baecae0b2b06cac0b2b02cac0b279ec67cb1982c641b180ac584b148ec520b138ac483b1186c460b1106c440b1086c385b0e02c361b0b92c2c1b0a86c2a0b0a06c242b080ac200b051ac140b0502c102b0402c100b0402bfe9af7c2bdc1af702bd63af392bbaaaed0ebb40aec86bb20aec82bac3ae79eb82eae006b765add82b760add06b740adb12b6a1ada82b681ada02b680ad69eb5a0ad50eb521ad482b501ad402b500ad212b369acd82b2c5acb02b2a1aca06b280aca02b261ac792b1a2ac682b1a0ac31eb0c0ac302b082ac10ab040ac102b021ac082afa4abe06af80abe02af61abd82af60abd82ae87ab4aead20ab482ace2ab20eac61ab182ac60ab08aaba4aac16aae1aab82aac1aa912aa40aa80aa984aa602a888aa08ea820a9f8aa7e0a9e8aa724a9c82a720a9b8aa4b2a9206a423a9082a385a8e02a361a8d06a2e3a8b82a2c1a8a86a2a0a898aa241a8902a240a8902a1c4a8702a1c0a858e9faea7e829f81a7d869ec5a7b029e82a7a029e04a78029de1a741e9ce1a709a9b09a6c029a27a68069a00a65969903a640298e1a630697a9a5e0696e5a5b0696c0a5b029644a58869620a58829601a568e9581a56029580a55869560a55069540a521a9442a51029421a508293e2a4f8293a2a4c16918ca45869160a402e9000a40028fc2a3e868fa0a3e828f81a3b968ee0a3b828ee0a3b828ec1a35328d40a34868d20a34828cc3a33028cc0a33028c44a29be8a60a29828a60a298289e4a270689a1a268289a0a231e8882a22028861a21828860a1e1e8723a1c0686e1a1a0e8661a15a28541a131284a1a12068480a12028442a0ca682a4a098a8260a090681c4a05128140a040a8100a03868064a01828060a000e8000a000280009fe8e7fa09fd8a7f419fd027ec49fb027ec09fb027e639f9067e219f8067e009f8027d089f3867c649f1827c609f1827c609f1827ba69ee827b439e0e677479dd0277029d5b675609d40e75009d40274849d20274619d18274229d08273c39caa672059c80271e19c60e71809c58671039c40271009c21270619c18270609c18270609be1e6f809be026f049bc026f009bc026f009bb866ee09bb826de89b7826da29b4926a769a71669c09a58e69419a19e68609a18267e499f82676499d8266e499a8a66a09990e66029980265a39958a65609940e64c299302646399182646099182646099182646098e9a624b9890262219880662009870a61c09870261c09870261c09870261c09870261c09870260c8980965eac9798a5e41979025e40978865d669729a5ca0972825c24970825c2096f8a5be096d925b6096d065b0296b865ae096b825ac1969125a409671259c09670259c09668659249648259209630e570e95a1256809588e55e29549a55209521654809518653e494f8253a294c92532094b8a52e094a8a52a094a8252a09481651e19478251a29468251a09468251a09468251a09468251a0942a2504394102504093f124fc093f024fc093e0a4f8093e024f8093d864ec59343a495e9229648a092206482392006480092002478491e02472391c82470191a8e46a091a8246a091a8245e69122e448091202444290e1a436190d82436090d82430390c02430090b8642a290816408c901864003900023fc28fe863fa08fe063f428f82a3dc28f6863d058f4023d008f28e3c818f2023c618f1823c038ee123b808ee023b618ea1e3a428e61a39618e31638a18e09238018df8637e08df0637638d92635c48d70235638d50635408d50235408d38e34a28d10e330a8c7a631e08c78231c18c70231a18c49230e28c28a30a08c28230438c1022fe38bc9a2e858ba022e808ba022e808b69e2ca88b10e2be38af062b068aa8e2aa08a8922a208a8822a018a59629608a58228c58a30228a18a18a286089f16266b8998226228988225c38970225a18968225818960224a78918a246089106244089102244089086238588e02238088d862360889a22260889062240889022240886962181886022161883921f0f87c021ee187b061e44879021e02875961d60875821d60873921ce08720e1c80870121c0086e121b8086e021b8086d0a1aa586a821a438680a1a008680219c28670219a18668219a08660619808660219428619e174985d02172185b8a16a285a8216438559e14e485382148384e22138084d86136084d82132284c8212e284a8a12a084a82128184a02128084a021188841a61060841821022840060fa383e060f8083d860f6083d820f4183b120e8283a020e61839820e418378e0de0837060da1836820d81835860d60835060d02833860ce08320e0c80831860c60831060c40830860be282c9a08d382112084081f8e07e081e8a07a081e82074381d020721818a206018180206008159605608158205228130e04c081302048281186042280e9203a080e82038180c8e032080c82032080c8202858098602608098202038078601c18068601628048a00e28030600c08030200827fd29fdeb7f515fd407f38dfce07f289fb897ee01fb807ec11fb007ec01fae17eb05fac07ea85faa07ea81faa07e989fa607e905f9677e125f8027df09f7c07df01f7c07df01f7a17dc91f6477d901f6027d801f5e17d60df5807d509f4e37d305f4c07d301f4257d005f4007d001f4007cc21f3007cb85f1c97c701f1c07c701f1637c505f1027c401f0c27c301f0a17c281f0a07c205efe57bf81efe07bc99ef207bc05eee17bb81eec17bb01eea17ba81eea07b71deda17b589ed607b315eca17b281eca07b10dec217b005ec007af85eba27ae81eba07ae81eba07ae81eba07ae05eb807ae01eb807a9a5ea607a525e9407a501e9407a409e9007a401e9007a195e8607a105e8407a085e8207a081e82079f89e7e079f81e7e079e89e7a079e05e78079e01e78079a21e68079a01e68079909e60279041e21078611e18078601e1617840de0e178305e0a178281e0a07810de04078085e02077f89dfe077b25dd8a77601dd8077601dd0477211dbe576f81dba276e81db6276d81db0376c01daa376a81daa076815da0076801d9e176781d9c176701d9c076701d9a17631dd8c076301d8a176281d8a075f1dd62d75881d60175785d5a275415d4e175381d4c17518dd46074f91d38374d85d36074d05d30274c01d30074b85d2e074b05d1e774325d0c074285d0627400dd00073e11cf2373c05cf0073b85cee073b05cdc873701cdc073701cdc073511cd2173481cd0173401cca372f99cbe072d15cb4072d01caa57290dca4072885ca207251dc92172481c90172401c88472109c84072101c84072085c80172001c80072001c7c271b9dc6a271a05c66171889c62071881c60171801c60071785c5837129dc3a870e81c3a070e05c38070c8dc32070c81c2e270a0dc2617080dc20070785c1c170701c1a170605c18070509c14070485c12070481c0e26fea9bf246fc81bf206f7a9bde06f781bda26f50dbd216f389bcc16f285bc436ef8dbbc16ef01bb826ed85bb606ed81bac56ea85baa06ea81ba626e981ba036e785b9e06e781b9a26e681b9a06e681b9626e581b9606e21db8806e201b8426e101b8406e101b8406df11b5926d509b5406d485b5206d481b4476d101b4406d009b4006cf85b3e06cf81b3e06cc99b3206cc81b2e26cb81b2e06cb05b2c06cb01b2446c901b2406c809b2006c611b1426c38db0e06c289b0a06c015b0006c001afe16bf81afe06bf05afc06be85af056bc01af006bc01aec26bb01aec06ba09ae236b1b9aa8f6a811aa006a801aa006a801a9656a505a9406a409a8e16a305a8c06a209a8806a185a8606a089a8206a005a6e9696a9a54369295a4a069205a48069201a46168f91a38368e01a36168c89a2c368b01a2a168891a1a468681a14368409a10068401a10068401a0c267f9d9fe067f819fc167f019fa167e819f8167a9d9d89676019d04674019cc26718d9c60671819c03670019be166f819ba266a259a8066a019a806688d99e26678199e066781998366601998066585996066581992266199978765e01970465c01970065b85968365a0196806598596036580195c26568595a06568195816541194c26530194c06530194636518194416510194406510193c464b2191c86470191c064609914264409910064309904463f8d8f8363e018f2363c818f2063b0d8e25638818de2637818de0636898d62635818d60635818d226330d8cc0633018c82632018c80631858c60631818c60631058c21630818c01630018c0062f098aa9625a989036240188a362281884361e9587a061e05878061e01876161c89872061c05870061c0186c26179d85076138584836120184616110584406108584206100583e160c99832060c81832060b0d82a160a8182a060a8182626088982206088181e26078181e06078181e0606898143600297f845fe017f805fe017e695f80d7e005f8017d845f5097d405f5017d405f38d7ce05f3817cc15f3017cc05f1117c405f1017c405f1017c405f1017bc45ed8d7b605ed817b605ed817ae45eb817ae05eb057a825ea017a805e9857a605e9057a405e9017a215e59977cd5de0977615dd8177225d99976605d98176225d88176205d78975835d58575605d50575215d02573e15cd9173605cd0573215cc8173015cb8572a25c98971e45c78171e05c59171225c48171015c40170275c00570005c0016fe15bf816fe05bf816f835be016f805be016f235ba156caf5abb96a835a9856a415a71169c05a58d69415a40969005a28d68a05a20568425a10168405a101684059f11672559c8166a459a8166a059a05662359881662059789654559121642158e15638058e01636158c8962a458a8162245888162205869161435850160e35830560c0582096061581055fa557b1d5ec057b015ec0579115e215770d5dc0577015da1575895d60575815d22572155c80572015c80572015c80572015c2356e915ba056e055b8056d855b6056d055b4056c855b2056b0d59c85670159c05668559a05650d58e35638158c156209588056201586156105582155e9157a055e05574255c85572055b8956e055b8156835598556415588556205588155a45568155a05558955415531153c854a29512b5448150e25438150e05428950a0542055080541854eec53b054e82534ad4cc3533014ca15310d4be352d914b6052d814b6052c894b2052a154890516dd45815131944c05130143e75093542405071141c05070141445012140404ff8d3f644f9253e214f8813de24f6893c894f08d3b854ed853ac54e4b539204e40539004e38538074df8537e04dd1537214d91d36404d90136404d88535094d40134e14d38134c14d20931b74c50d30a54c28130624c1052fc44bf012fc04bd8d2f604bd812e494b8852e204b8812e014b68d2c894b1092ba54ae812ba04ad0d2b404ac852b204ab0d2ac04aa852aa04a90d2a214a8812a014a8012a004a611282b4a081282049f89274549b8d26e049a0d268049a0126234961525804958525224948125204938924a24928124a04928124624900d240048e8d23a048d89234148c09230048c0122e1484b920c34830120634818120604800d1f6547d811f0347c011ec247a851e62479811d2a472151c80471091c4046d9d1b6046d811a2a468051a004680119e14670519634658119414619d16ec45899154745311144444f8d134544d0112c444b0112444490112214451d11214448110a44428110a04428110a043cb10f2043c810e28432350c80432010c61431810c03430010be142f810bc142f010b8242e010b6142d810ae442b810a07422ad06914190906214178905644158105034128d042441081040140c2102e140a0d02804090901c44051101404040900e14001cffe13ff80ffe03fe0cff613fc88ff013fa8cfea03f988fdc53f700fdc03f608fd803f48cfd013f400fce13f380fc453f100fc213f004fa4e3dfccf7c13dd8cf7603dd04f7213dc80f7013db84f6a23da04f5a73d680f5a03d588f4e43d380f4e03d20cf4803d200f4803d200f4423cf8cf3e03cf80f3e03cd90f1cd3c58cf0873c200f0613bf90efa23bb98eec13ba84ed4b3b38cecc13b18cec413af10ebc03ae84eaa83a988ea603a980ea603a980e9e43a780e9c13a700e9a13a680e9813a600e9803a508e9403a484e82839e14e76139d80e74139c84e6c339a84e66239980e66039904e6403978ce58339128e3e338e88e3a038e80e26a38980e24138884e20138594e16038580e14138408e10038400e0c238284e0a038280e06238088e02038004e00037f08de8a3769cdd8137600dd6137488dd2036f2cdb8236c10db0036b08da0636800d9e136780d9c136608d8e535ea8d76235a1cd68035908d62135614d58035508d52135214d46134f90d3e034f80d38334e00d38034c8cd30134c00d30034c00d2e134b80d2e034b80d2c134b00d2c034a08d1693421cd08034010cfc233e84cf4333c84cee233b80cec133a84cea033a80ce2433880ce2033880ce2033690cc2c32ca0cb0132a8cca8132908c9e332780c96432504c8e332304c8a13210cc66f31888c60131784c5a231490c4e231304c4a131188c3e430f80c2c93098cc1e430498c12030404c10030384c0c130300c08230200c08030108c04030100c0022fa30be612f980be602f904bde32f704bdc02f700bda12f50cbcc42f18cbbe42ef80bbc12ef00bbc02ee84bb242e6b0b9812e600b9612e488b9202e480b8e22e380b8e02e380b8642d944b6402d900b6212d880b6012d610b5232d404b5002d308b4a12d280b4622ce98b3a02ce80b3a02ce80b3242ca90b2a02ca80b2a02ca80b2a02c890b2012c68cb1a02c680b1a02c680b1812c600b1042c384b0832c184af682bc0caee12ba88aea02b890acea2b380aca22b10cab672ad80ab032a994aa602a980aa412a900aa212a614a9802a508a9402a38ca8452a100a7e329f80a7c129f00a782299a4a64129884a62029804a6002968ca52429480a52029404a50029384a48329184a46029104a44028f8ca3a228e04a36128d80a34128d00a32128c80a2c328894a22028880a20128800a1a328604a18028584a16028390a0a228204a06128104a040281009fc427c949f2027c809f0127c009ee127b809ee0279149e40278089bf126d149b4026b109a632661c99802650898c426300988225f9497e025e8896e625b0496c025b0096632598096222588095c32560895802541095002540095002540095002540094c22530094c02530094c02530094a125280948125200946124bb091aa2458891602450491402450091022421090612400c8fe123f048f4423c848ee223b808ee023a0c8e80239848de42341c8ce1233808ca22310c8c40231008c0222f088bc022e848b0522c008ae122b808aa2229888a412280889a32268089812258489602250489402248488e22220c87a721e8087a021e04878021e00878021d8486c5213bc840720e8c83a020a2482612098082412090082402078c81e02078081c1206088180206008161204888120204808101203087f6b1fb907ec11fb007e821f9847de41f1b07bc51ed107b401eb8c7a451e61879801e48c78661df9077a21daa076811d98476601d79075071d30874631d08873a41cd8872e41cb8072a21c90c72211c4a071011c40071001c40070e11c2886f891bc8c6ee21bb806e831b8106de11b6886d621b5046d401b19c6c601b1806c601b00c6b651ad046b021ab846a831a9846a411a78c69e01a60c69611a50469401a218678819e00678019d846703190dc640118f8463e018f8063c118d8c62e418a8862811898462411880861e11878061e01878061e01868860e61801c5f8417d085ee317a885e8117a005e61178885d85175845d22174045d00173845ca216f1c5ba116e045b6116d805b6016d045b4016c845aa41681459e11670459c01668459811629c582416080580115f84574515c8456e215b04568215a005661155a055221540454c21528454a015204540414d94532214c0452e114a8851c71470051821458451221430c50821408c500114000500013f844f2613c044f0013c004ee113b044e82136204c4a130844c2012d984b0312a8c4a431278c49c11251048c412208486112104482112080482011f0c47a111e80478111e00460c1178445e01170445821158445601150445021140045001140044a311204448011184442210f8843c110f0043a110e8043a010d8842e410b804283102bc40811018440410fe943f810fd083f210fb0c3ea10f90c3e400f9003e400f7103dc00f6843da00f5883d600f5803d220edb83b600ed043b400ec843b010ec003ae10ea883aa00ea043a800e9843a410e9003a020e80039e10e60c39610e50439400e50039020e28c38810e10838210df8837e00df0437c00de8437240dc8037010d99436220d80436000d78435a20d68035a00d58833510bfec2f070bb842ee00bb042cd00b2842bc70ae842ba00ae042a880a79429a20a50c29400a50029210a38828a20a28028620a10428400a100280209c9c270109c0026e109b0426c009a8425a809604258009508246709180246009180244108e9423a008e80238108e00238008e00236108b1422c008b0022a108a04228008a0022420890022400890022210880420ca0830020c00818c20600800c2000080001fc207e081f8007d841f6007d041f4007d001f0207c001ee107b801ee007b801e8307a001e80079841c13070001c0006f841b64062d8180506000178405d0816670590416210588015c30570015c00568415a00568015a00568015a00568014a80509014200508013a404e80138104d08134004b8c12e00489812010480011c20468411430440810e10420c1061041041040040840fa403e040f2303c800f2003c800f2003c800f2003b880ee0037a00de0037800de0037800de0037800de0037800ce8033800cc1033000cc0032840ca0032040c80032000bc6029ac0a60029800a22028800a20028040a00028000a000270809440250009400248408e201e2c03bf000f00001 0xc0da3fbb0a3b95ca3779aa33c0d13fbb013b95c13779a13369292f69212b55d1274e31231da454ef9258ef99484e2120ef935c1da25cefa25def6a51ef8249c0ba3d4e11224e0230ef413c4df240ef435cc09b4cef635def5351c08b4d691a3e4de232ef313e4da132690a3eef7a4fba9a49ef2a43ef1a41c07a3d949a35ef714fba9149ef2143ef1141c0713d94913568d92f68d12b55a1274d912354a244edd1446c7934eef349549236ee513eedc136548244eda144edb134546236ee313eed9136bafb59eed351545236ee213eed8136eec052eeb050943244ee615cee714cee7254ee6244ee425cee3050bafb5aee8356941256ee515eee2156940254ede15c6c7934ede3586c7b48edd248edb350eda250ed9050ed703093e246ed7146edf45a93d256edc15eed8156ed6040bfbb4fbabb4b946b47796b43baa24a93c24668c23a541236eee14fba914aeea147ee9146ee113fee013eed51374d8132eb0355ef0345e62a61ceca59ed4a49bfaa3fb9ba3b93ba37789a33e62161cec159ed4149bfa13fb9b13b93b13778913367e92f67e12b5401274c8123eae457ead457cebb5bb9ab4b931b47e1b262a9f24a930246ed213e4c7132eac347ed1a59ce1a4bb99a3b92fa37ed1159ce114bb9913b92f13767c92f67c12b53e1274c2123ecc13eec8144ecf670ece361ecb13eec7136ecc670ecb166ec8260ec7166cdeb5bdd8262cdd25aecd157eca13fec913eec61374c1132cd3a5bec5a39cd315bec513967592f67512b5391274bc123929256c4c156ec1250928256ec0156ebf040b96b4b92cb47a5124a927246c4b147ec313fec213eebe1374bb132ebda49b95a3b926a37ebd149b9513b92613767192f67112b5371274b8123eb6b54ebb359eb5b55eba13e4b7132b94b4b923b47eb4b543f3254eb61283f3450eb4a40eb4150eb7251eb5249eb3245e61a61eb9a4beb8a49eb2a47e4aa41b93a3b922a37e61161eb914beb8149eb2147e4a141b9313b92213766e92f66e12b5341274b3123e60a61eaba51b91a3b920a37e60161eab151b9113b92013766d92f66d12b5331274ae123eaf26ceaab61e1c272eae13e4ac132eada69ea8a51ead169ea815166b92f66b12b5311274a9123e5fb61b90b4b91cb47e58260a7d24a91524666aa3e4a8232ea413fea013ee9c13749d132eaa369669a3e4a7232ea9165e9e13e49b132e9a144ea7369e5eb61912246668a3eea213ee99136b8fa3b91aa37ea4672ea337ee5eb72e7f27e90d256ea217ec1a156e9f264ea0562e9e46fe96040dd2934e9a268e95030e98250e96562e7e26ee9516ee9c672e9b472e7d27e90c256e9917ee97156e94040eab562ea846fe82b6fe59b63b8cb4b916b47e7c26ee57262a7624a90b246664a3e4a6232ea616fea516ee4a162c19147ea113fe9d13ee9313749a132eb1562eb0462eac36fe7ba6fe49a63e92a51b8ba3b90aa37e7b16fe49163e92151b8b13b90a13765b92f65b12b52a127499123e8e37ce8d27de8b271e90259e8e258e8d47de8b57de8f46fe8c26fb87a69e8a263e89261cd0a4be8724fe86243b8aa3b903a37a7bb4a8fdb46e84265e83264e81251e78368e76368e77268e7e030e75259b89a3b8ffa37e80155e7f12fe7d127e85568e74269e82251b88a3b8fca37e7c150d56a62d57b62e7813de77135e76125d54b7257c27e579272e7a26de7926ce75160e7024ee6c246e6f24ce73670e7246de6e24ee6b246e70670e6f46ce6e266e69040e6c670e68040e69560e68256e6b266e6a052e67050e74457d53b6257b26e578262e71257e6d24fb87a4ae66247e65246e88355e7b347e64259cc7a4bbeba3fb81a3b8fba37784a33e60465cc6b69beab4fb80b4b8f5b47783b43c85269b0f24b74a24365923b497233e3d14fe19147dd613fd8f13ed51137385132b7fb4b8f3b47b0e24b65723b495233d8e13ee5f361b7eb4b8f1b47e58260b0c24b65623b493233e3c14ddd513fd8d13ed50137384132a7ac5a8e4c56655249492241dd313de5c135dd2134e5c670d23140654139491131e5f670a79c5a8e2c56653249490241d7c149d22141dd113de5e13ae5d136e5b135e5a134b7db4b8eeb47d8a23ee58560b7cb4b8eab47df4244d8923ed4d144e56369dd1361e2714ae14146dd013ed7a13ad4c136d21132e53268e4e254e5336ce51670e4d250e50160e4e25ce4d364e5425fe5225be4f257e4c253b7aa3b8e7a37b0b13b64f12b48f123b78b4b8e5b47e61670e60570e59361b77b4b8e1b47e57260b0a24b64e23b48d233e5516de4b16ce4a160e3b14de2614be13147e12145df3144dcf13fd8813ed7813bd4b137d1f133381132b76b59e48351dbb13ee4615ce3514cb76b5ae45356e3315edff156be8c5fb74c5b8dfc57781c53e3225edfe256db924ed45246e47156e4414ee42359b72b51e3114de2e14cdfd145db513ed7613ad41136d1d132780b408d295cbe6c5e77fc52b72b5ae40356e2c15ee2415adfa156dea152db814dd44145d3f144e4146de3f361be5b4fb71b4b8ddb4777db43e3014fe2a14ee2214adfc147df8146de8142db713fdb313ed7413ad43137d3e136d1c132e3c574cc5b79e3a349dae13ee3c570e21145dac13ed7313ad39136d1b132e3a671e3716ae2b166db214dd3c145d351446be93db479366bd9356bb934e38134e35254e34244e37349e36144e3313ee3157ce20144e2f346e2d244e2e46ce2c261e2b239e3d671e3b566cc2b6be39349e3216ae30167e2a166e1f145daf13fda513ed7213ad3b137d34136d18132e28164e2727cab018ce21154e1c13ce25134e24361e2316ce20146e1e13ee214666beb59772b51e20166d0013ecc0c6ab41c5a8c5c566beb5a8c7b56e1e166e1c457cc1b5bb70b4b8c6b47e26567cbec6bb6fc5b8c4c57e22266da324eaad17ce1f156e1d14ee1b13ccbdb79b64b59e08351d9e13ede7150de6140dfd47ce17370e1417cde4140e16070e1417cd9c13ed7113ad2e136d17132772c6ce0f368de3150d99144d9b13ce0b344e10134e0f46cb5fc60da0354de1150b559346bed6cd3246ce0a3508c396cddf140e0d060e0b35c8c295cb5fc68e0a464dde150d9a14cd2b144d2d134e06030e08671b66c5a8c1c566beb4eb5fb4de0723ae05236e0316adf9166da214dd31145d29144769936d33135d2c134e0025cb62b59e03351e0215ee0115cdff13edfd47cdfb25cdfa261b61a49df9241e19671e1856be15567e13467e12466cbbb6be1135fe0e35bb5eb59e0c357e09353e04351b6eb4b8c0b47dfe16adfc167df8166ddd140d9f13fd9313ed6f13ad30137d28136d13132df235cdf125ddef251df6239742141df415064d12b48c123df2238df156a740141def56a73f141772963c8315bdf545bdf3356cb8a5bdf024fb5da49dee243ded241c8015baa313973e13164a12b488123deb134dea361de916cddb13edd912cde6360de516cde2134de015cde745bde4457cb7b5bde334fde134bddf347dde343ddc26ccb5c6addb166cb6b5bdd9156cb3c6bde8266ddd254d9124ed262466fc17cdda14edd813cdd5575cb2c79cb0c78b64b5adc6356dae15ed9e156dd3370dad14cd9d144d6e13836f930dd3670d6d148dd2134dd5680dd437cdd1370dd017cdac15cd9c154d6c14836e940db835cd6a158c91934d69148dca3688c7b54d95164d98154d68148dc0354dcb134dca46cb60c64da235cd66158b51934b60b58dbf350da816cdab15cd94154d65148dc7568da715cdc3260dc3570dc6671dc5571b60c5e6bec5db67b4977cb41dc425edc2252dbc16adb41668cb95edb015dda615cdb114dda914cda0145dc035cdbf464db235c6beb4cd63158771934dbd15cb62b5adbc356d03166dbb156dba136db8470db6254db546db61a4adb4246db2458db13646beb58db0354d00154cafb78da7244dad26cdaa34eda7561dae671dac566cadb6adab255da9254da8245da6244cacc6ad00156da4136d27134d0214cda2460da136c6beb68da0354d0116ccabb78d9725cd9d26cd97561d9e671d9c466ca9b6ad9b35ed9a352d9925ed9825dd9625cd9524dd94245ca8c6ad0115ed92136dd6671dcf567cb1c6bca7c6ab6dc5b77bc53dce36bdcd367dcc35fdc935bb5eb5adc8357dc1356dbe353db916adb7167db3166daf15fda515eda315ad9f157d93156d91152d5b14836c940d8d465ca6b68d8524fd81247c7f169b0114b73d14364913938d93164813938c931d8a16064713938a93136fa3ccfda62646129389921d8a560cfeb62d8e670d8d570cfcb72d8c26dd8b26c57923e36ea3dd89160645139388931d8424cd8746dd8324ed80246644139d8446cd85671d83266643139d81671d802666421398c7963c7d15bd8f561d88457cfab62ca5b5ad86257d8224fb5da4ad7f247d7e24657823e36ca3dcff163c7a15bafc14b73914363e139387931d6d24c5d217cd5713cd6d3605d117cd7b164d5512cd7c470d7a27cd7325cd71254d6c24c5d018cd7917cd5a154d5413c57912cd77154d7646dd7516cd59146d15144d73566d14144d1a14cd71466d7015ed1915cd24134d6e36cd6d360d10134d62144d6b134d61134d60134d5f144d67134d5e134d5d144d64134d6225ad61256d6024ed5f24ad5e246d5d242d6c457d6a35bd69357d6834fd6634bd65347d63343d5c136d09134d5a466d59166d57360d5626cd5516cd54457d78567d74266d7225ed6f256d5b24c5cf17cd58156d5313c57812cd50575d4a45aca4b7837494cd4f47037394cd4f670d3a15cd2f154d12140d2423cd4d268d50680d4e470d4c17cd3915cd2e15437194cd11130d4a671d4716ad40166d3d15dd3715cd321556be93db489366bd9356bb934d48134d4745ad4614cd44370d0314cd42358d4146dd4034ad3f260d3d4686bdc58d3c358d0114cd3a360d38245d3623dd39566d373586bbb48ca2a6ad352486bec68d33460d32458d31360d0014cd2f360d2a23dd2e466d2d352d2c350ca0a6ad2b252d29250c9fa5ac9eb6ad2714cd51671d4b567d4945ac9db6ad4516ad43167d3e166d3b15fd3415ed30157d28156d26152cff14d37094cd08130d2413cd232443c917cd07154cfe13cd22470d2127cd1b25cd1725436ea4cd112443c818cd2017cd06154cfc13cd1e154d1d46dd05146d0313ecfb12cd1a144d1a456d1b566d19144d0113ed1514cd15356d17466d1615ed1415cd0013ed12360d1013cd10347d0f24bd0e247d0d23fd0c23bd0b237d0a233d11457d0913cd07360d064666beb59772b51b43b4977ab41d05166d02254c9bc6a6beb5a8c7b56d03166d0115ed00156cfe360cfd26ccfc457c9cb5bb6cb4b779b43cfb156d1f567c9ac6bb6bc5b778c53d1c266d1825ed1325636ca4cd082443c717cd04156cff14ecfa13ce62561e49457c86b5bbdab4fb3fb4b8bfb47767b43c7925bafb24b73824363d23b487233e4315be3e157e2914fe1a14bdf7147dec146dd7143d9013fd7d13ed5213bd25137cf913336b132cf725fb3ea59cf6253cf5251cf2052cf1050cf324fb3ea4acf0247cef246cf4345cee249bd8a3fb3ba3b8bba37763a33cc6361bd7b4fb3ab4b8b8b47762b43c85261af924b73624363b23b485233c75146c4913ecc1472aa0c5a8b1c56cea57cce8268ce5254ce836cce4250ce525cce4364ce925fce725bce6257ce3253b38a3b8b2a37af713b63812b484123ceb369b37b4b8b0b47af624b63723b482233ce2164c4613ecb6472ce0136cdf134cdc37ccda248cd7234cda34ccd6230cd723ccd6344cdb23fcd923bcd8237cd523363412b480123cde349cdd24863323b47e233cd4144c4313ecd217ecd117ccce368ccb354cce46ccca350ccb36ccca464ccf35fccd35bccc357cc9353af313b735133cd0465af224b733243cc8164c70146c4113cb09c5b749c53cc535fcbd357af125b73225347c243cb223bcb023aca6238ca4236c6f156c4014ccaf238cc4154cc4670c6024ccae128ca3124cc5780cad238ca2234cc3154c97134aafb8ccc135ccac248cc0238c95144cbf134cab238caa128ca1124cbd780cb7350ca9238ca0234cbc16cc68164c94134aa4b49741b41cba15ecb915ccb74646fdb8ccb635cca8248c9e244cb5238c92144cb4134cb2780c91144caf35ecab356caf670cae144c9f234cab670caa15ccb0670cad35ecac35aca9356ca8352b00b4b73cb43ca6560c9b363affb4b73bb43ca3144ca115cc9f23cca4670ca225eca0256c9e252c9b23dc902443c618cc9c15cc9b13cc9835cc98258c9623cc9323cc9935ac68356c9725ec9525ac94256c92252c91129c90121c8d258c8a244c8d35cc89240c8a24cc89354b05b4b746b43c8e24fc8c24bc8b247c88243aef14b73014347b133cc6670b04c5b743c53cc235fcbe35bcbb357cb8356cb3353aee25b72e25347a243cb123bca723aca5238c9d236c9a233c7817cc67156c3f14cc8f136c87134bd4c5fb36c5b8aec57761c53c5b256c2a24ec7f14ec84134b34b59c83351c8215ec8115cc2513ec53156c7e15cc7f670b34b5ac7d356c51156c7c136c7b134c85670bd0c5fb31c5b8a9c5775ec53c50256c2324ec80156c7a14eb07b4b748b43ae914b72d143ae714b72b143c78261c77259bcea3fb2ea3b8a7a3775ca33ae513b72913363112b479123c6f261c6624fb2da49c63243c5d241c5b161a8a13972813163012b477123c62251c74239c5f231727141c72469c71468a89139726131c6e25ec6c25dc6a25ca88149725141c6e670c6c670c6a560c6025cc6f670c6d25ec6b25dc6925cc68255c5f252a87149724141c60468c66672c6537ec4f151723141c6025cc63672c62572c6127ec5f272c4e151722141c5a161c5d562c58163b2cb59c5a351c5715ec5515cc5313ec5a670c59134c57670c55560c53670c5225cc5b670b29b59c58351c5615ec5415cc5113ec4d13cc4d35cc4f35dc4e351c4c13ec75562c73463c7026fc67263c6424fb28a49c5e243c5c241c50163c4b143a8613971e13162c12b474123c40360c3e26dc3a24fb2da4ac32247c2c246c2a161ae414b71d14362b13932a931c48265c4726462a139329931c45245c44244629139328931c42255c3823fc30237ae313b71c133ae214b71b143c40560ae114b71a143c2f246628139c3724cc3e570c3d465c3624ec2e246627139ae013b719133c37464c35154c3a672c3947ec3837ec3627e626139c34129c2f27cc2f570c32672c31572c3037ec2e27e625139c11929c29161c2c562c27163b2cb5ac29356c29670c2815cc2625cc2a670b29b5ac27356c25156c24136c49562c4646fc43463c4136ec3f362c3c26fc3b26ec3324fb28a4ac2d247c2b246c23163add14b712143620139326931c1092bcec562ce146fcd3463cc736fc86363bc5b4fb1eb4b899b47750b43c79263adc24b71124361f23b473233c7616ec4a146c2213ec1d151710141c1c15170e141c1b13cc1b35cc1d35dc1c351c1a13ec2024fb1ca49c1f243c1e241bc3a3d895a35c19143a5313970c13161c12b47012361b139c1412961a139c13129c12154c1224cc1435ec13356c11156b1db4a893b46c1724fb1ca4ac16247c15246ad314b7091436171392b4931c1012bbc1b4fb19b4b892b4774cb43ad224b70824361623b46f233c18146c0f13ebc0239c0a241c0a45cc09128c0c34ec0b24fc08243c05258c01244c0535cc00240c03150c0124cc00354c0624fc0424bc02247bff243bfd245bfc244c07454bfe354bea271bd7269bfb259bbd239bf4364bf9271bf7259bf3255bf7565bf4270bf3455bf8457bf625bbf5259bf2257bba251bd524bbf056cbee270bef46fbed467bec364bd4379be4245bdf244be2354be9254bdd244be747cbe1244be6170be325cbdd160be4671be226abe1266bd3269bdd160bdf561bde45bbdc457bd125bbea671bd036bbe826bbe5267bba248be0245bdb244bd9354bd4371bcd244bd6266bc9354bd3254bd3670bd225cbd4780bc7354bd1254bcf364bcb461bc9261bcb670bc9670bc825cbcd562bcc46fbca463bc7263bd7672bd547ebd0373bce27ebc6244bc434ebc3254bc2244bb6461bbf255bbe254bb425646aa54bb7356bb6256bb8672bb5670bb427ebc056fbbd563bbc26fbbb26ebba262bb925fbb3257c0d56fbfa563bf136ebeb26fbda263bd825fbc525bbc1253bb22396c367eb1834b856b4761523b46e233a4f13fa0f13e9e013b9ae13798c1331f31326c7134b17b4a84eb46b16c5a84dc566b437ea4e14d9ac145a4d13dbaf13abae136bad135bac134b1634b852b479ab1446a9572a4d359ba8351a9a168a4b13e9de13a9aa13698a132ba4258ba6048ba1244ba435cba0240ba124cba0354b9f244b9e128a9a459b92355ba524fba324bba2247b9d243b1323b84fa37b10161afa1596c513b61012b46c1236c857eb91465b80371b3a369bab359b1234b84cb47b0f271af9269baa25860f23b468233a99169ba9158ba7155b9c154a4a13fa0c13e9dc13b9a91379881331f0132b70472b9a369b3735ba9f268af625b60d23b465233a0a13eb98136b97134b96359a5125860923b461233a0713eb7f371b94359b78351b0e271a0613eb0d161b7e371b90361b0c271a7d260b92154a0513eb7d470b90672b8947eb7c472b8f37eb78372608249460241abc17eb8e136b8d134b93672b91572b8837fb77373b8c361b0a273a7626060423b45c233abb17ea0013eb8a678b89360a7b260b831746a367e6a5672acf17ea9815aa70156a7c150b8545fb84457b83347af514b6c213b6ba67eb88457af225bb87168b86165b82164a9615ba6f157b7e575b36479af1279a95179b6413ab5b136b7d470a7a270b7d670b4d16cb7b164b79134b7f780b7e680b7c470b7a37cb78370a792709fa13cb4b1346a41346a4234b62148b59144b76138b75134b7317cb72170b61138b58134aaeb8cb7035cb41238b561446be138b662606be168b55134b67264b511446be120b502443c318cb43164b6c15c6be12ca3e134a4538cb6a35cb68148a3d1446bd134b45134b52134b54234b6824cb53244b671646bc144b6613cb63134b52134b54234b64671b6236ab613668c7156b601556bd136b531356bb13477212eb5f12d6be363b3435ba3d13cb53138b44130b5a23cb5723cb54150b52154b5412cb52154b5b671b5926ab58266b5625ab55256b5323e6be23db51129b5012169c372ac417ea9316aa6b166a4314e987142a3d13e6a313db4d26cb4c260b4b4576bd363b3235bb03b4bb4a25bb49257b4824baf015b6bc14b45b133b47123b4513cb4424496a18cb43164b4215c6a314cb4113c6be12cb80671b77567b3146bb02c5b6c037eb7436bb71367b6f35bb6e357aee26b45a243b6d23bb6b233a9116ba6a167a4914f986143b6913fa3c13d9f913cb6513bb5e13ab5d138b5c137b4f136b4e135b46134b40133a1513ea1524b6b913b6ae56eb3e158b3d155b3c154b36471b09271b2d138b3916cb24164b38374aa0278b23134b2c148b35134b33238b36780b29148b22144b34138b32134b081616c6369b07271b30165b2f164b2c361b2b134b2b560b2c670b2a134b2d562b29363b273726ab342ac117eaa7172a3814e984142b25268b24264b2346fb22363aebb4bb2126fb20263a9d233b061636b314b459133b3a672b3757fb31473aeac5bb2e37e6ae34eb04273458243ac017fab217eaa5173a4814f983143b28138b26135b1f134ad7b4b6a8342a3214e981142ad9b4ba652336b014b457133ad8c5b6b736e6b134e456243b1d238a4714f980143b1c138b1b135b1a13496723896794c006130b17134b1525cb14254965128b16c68b13b64b16268964238b1316496494c004130b1867fb12673b02c73aeac6bad8c63ab1b7eb02273aea26bad826345524395f238ab117e95f94c003130b0d465b0c575b09479b102649ef24eb0114eb0d264b0e780b0c680ab028cb0b17cb0015cb08274b09780b0748caaf28cb06244aa4164aff15cb05144aae28c963a5cb03144b00478b00670b01671aff46aafe136afd134b0f671b0a567b0446bb0245b848c57aad27c9ed24eaa3154afc14eaf1471afa2649ec24ea8a154ae414eaf816caf7174af416caf5274af3174a89154ae314ca88164ae215caf17809ea24caf0244ae918ca87164ae115caef144aed13caec134962a5caeb144ae8134ae9371ae7369ae61649e813eae2470ae2670ae4672ae347eae1472ae037eaab17eadf136ade134af9672af657faf247faee473aea45b844c57aaa27e9e524eae517ea86154add14eadb13cada134960a5cad715cad9144ad5144ad524a840a46ad745a83fc56ad6136ad4134ad845b83ec579e224ea53154ad314ea6368cacd2689a768c6a367cacc378acf164ac7364acd164acc47ca40470a2d14c9a41446a334ea4034daca23aa9016aa61166a3014d9a61459a31446ad68cac6360a2c13cac737cac5134a3e368ac5364a40478ac6474a2f38cac4134ac2374ac1134ad156fad0567ace36facb36bac9369ac8367ac3363a3c361ac035ba8f15aa62157a5f156a2e13fa2a13e9d913a9a51379a213697e132ab6364abe271aba259ab5255ab82699fa261abc251ab0171a77150aba565a78160ab8457aac15b6ad14bab6270ab5455ab3266aaf171aae171ab0457aaf35baae34b837b47aac3699ea361aab13eabd457abb347ab925bab7259ab42579f9251ab224bab123b835a37aad161aaa14b6ac13b60112b453123aa813c69b134aa7244aa4164aa215caa6144aa013caa435ba5d156aa246a6a537e6a3372a5c166aa035baa546ba5b266a2824e6ac17eaa3154aa114ea9f13c69a344a2714d9a114599e144a9d1366b31356b2134a9c359a8e1686a6155a2513fa2113e9d713a9a013799d13697c132a95471a9a264a2024e99c246a8a154a8514ea7d13ca7c12ca98274a97174a89154a8414ca7b13ca88164a8315ca7a13ca9413c6a4134a95780a1e24ca93244a8d18ca87164a8215ca8014ca92144a7913ca7812ca90369a1e3616a7156a7f13ea7712ca55154a8d371a8c369a80361a1d13ea88361a88670a8a562a8936fa87363a83470a836706a4134a85672a8447ea82472a8137ea80372a7f17ea7a361a0223ea7c264a7a6709fb23ca782599fb251a7d562a7b36fa79363a7726ea0123ea99672a9647fa91473a8f27ea8e26ca1b24e998246a8b17e6a6166a86154a7e14ea7613c6c7134a6e371a74359a68351a7325aa6317d6c51556c4154a1813e9d613a99513697b132a71678a70174a6c134a6c670a6e780a6d37ca68370a1613ca6b134697344a6937ea68372a6723aa66236a6017ea5e172a1a14d997145992144a651366b01356af134a63680a61269a16261a60251a5e3616a717ea5d144a5c13ea72672a6f37fa6a373a64361a6217fa5f17ea5b1726aa16da54150a1913fa1313e9d513a996137991136978132a5924fa5824ba57247a56243a5515c990136a54264a1124e98e2466aa16ea53154a5214ea5113c9d41481e19406c7134a4e468a4d368a4c364a20178a4b1649d21481df940a4548c6a3340a43134a38134a32134a41380a2b18c9d1148a3f1346a367ea4167da45371a2f17d6c21656c1164a1f15aa17156a3f37ca4148ca3035c9cf158a43134a3f134a3e134a3f27ca3e24c6a537ea4137d6ad34ea4034da1e16aa16166a3d1366bc1356bb134a3a378a14174a151649ce148a35364a39134a3936ca3a47ca1a35c9cc158a38134a34360a2317ca2416c9cb148a3536ca33134a33364a34474a2735c9c9158a32134a30478a2f38c6a3370a2d36aa2c366a2b27d6a217ea2913669a144a27468a2636469e164699134a24265a23255a22254a0212c9fe12c9fb12ca20672a1f37ea1e372a1d17e69e166a1c13698f134a0112c697144a1a4706b937c6a017c696134a18672a1727ea16272a1526d6b826ca1425d6a016ea12136999134a4f67fa4a673a49473a4846ba47463a4637fa4437ea42373a3c372a3b36fa3736ba36367a31363a2e17fa2a17ea28172a2516fa2116ea1b16aa19167a13166a111629c11481de9406951351e3e7e967b4a834b4600623e1e1a3d6001391fc931966a3a832a361e5d7ea05465964b4a831b469f4265a0e255a0d25400423e1dfa3d9ef1719ec1695fe1391fa931a0b2655fd1391f9931a09255a082545fc1391f8931a021605fb1291f7921a025629fe26e9fb262a06672a055729fd27e9fa272a0426da0326ca011605fa1391f693182cb469f32565a0a465f91396cb9299fe1509fd3479eb14b6a513b9fb1609fa4579ea15b6a314b82bb469f82465f81399f71291e4a549f56729f457282ab469f327e9f22465f71399f11299ef671963c5a830c569ee1369e92649ec672962c5a82fc569eb37e9ea3729e817e9e71369e6134961a4a82ea46960c5a82dc569e41369e3134a0f56fa0c563a0a46fa0745fa0045795fb4a826b469ff26f9fc26e9f92629f625f9f025759fa4700323e1dea3d9ed1639e515b9e215369d14b5f31391f59316ca92b9d424c59e15483d93c00612c9be0189df15c59d1449bd0189d313c9de2649d224c9dd16459c15483b93c00412c9bc0189db1669da16483692c9bb01897a1546991369d812c9ba0189d66729c017e97d16c6961369741349b90189d31549731349b80189c81349b70189c71449d01349b60189c61349b50189c51449cd1349b40189c41349b30189c31449ca1349b20189c826e9c72629c625e9c525a9c42569c32529d456f9d25639d136f9cf3639ce35f9cc35b9cb3579c93539c213696c1349b10189c01569b913c9bd1549b813c9b945f9b84539b725f9b62539b524f9b424b9b32479b22439be56f9bc5639bb16e9ba15e9b113c9e067f9dc6739d927e9d726e9d52669c124c9bf17e59b15469514683a93c00312c9b00181e594c9771306c71349ab2509ad4689ac36899c1789aa1641e394c9751309a717d99b16a9941666a313d6bc1356bb1349a74806a34709a63786a214c9a426a9a32686b34689a13686961646a014c99f23d6b235899e25899a14c99a56299c67299b47269616699914c6b047099737069917c69e14c99323d9956729943726af36099226069916e99015498f14c9ae67f9a96739a84729a517f9a217e9a016f99d16e99816a99616799116698e16269d14d1e294c96b1301e1a4c97724408f15496713c98b15c08e14496512c1e093c97613498a2641dfa4c97524498916408d15496413c98724496a18c08c1646a314c96313c98513c98424408b1646ab14496213c08a15498213c9812440891646a814496013c97f1666a213e97d1546a013e97b67296917e97a16c97914469e13e97413c97615497313c97445f97345397225f97125397024f96f24b96e24796d24397756f97556396c13c96a3716ad3696a336196915696625496515496123496756f96456396336396235b96035398c67f98867398647398346b98046397e27e97c26e9782661dea4c96b24496817e08815469d14e95f13cbb056fb9b563b9946fb9545fb8b457b8136fb3f363b3b35fb1e35bb19353b1134b825b47afb263adc25bad22535f223b452233abf16faa916ea9e163a9b15fa7515ba5a157a50153a1013f9e113e9af13b98d13795e1331dd1326c834d89124185623b82423780d04095b12c8fa27095824894f04095223495834c95725494e04095602895123095404094d03095223c8f937095134494c0408f72618ba25994f23d94e23994d23594c23192145595a34b8f62618b925985424b82224795923f95523b95323795023394b03285324a821a466c645d85234a820b4694825d94725c80c05094212e94425c94324494215c93f04c94034893e03084d23b82023794514d94112f93d12794a4589203659493546c334d8f52718b826994625988e24184c23b81f23793c15880504093534493a2619382399342359384668b736a91f4579352609343668b626a91e4579393578f42618b425b84b24b81c24793723b9362399332378662318c63728040508b125b9312698b025b88c24193016880304092e25d92d25c80105092a12e92a15c92b14d92912f92812792c2598892419271588000407ff05092545a9244588f32719232598e52518872417fe0408f226191d2519214588f127191c2618862419151607fd0409141608f027191b26191f2398672319131608ef36091d5688ee37091825c7fc0508ed3707fb0408ec26091856290026e8eb26291c67291b5728ff37e8ea37291a27e8e527291925d91725c7f90508e426188324191114d7f80408e32619142398682317f704091156291046e90f2498823507f60508803508812507f50509155629134628fd26f8e226387f24191216f90e14d90d12f90c1277f404092267292057291e4728fc27f8e127391626187e24190b1607f104090867090612c90245790935b90735790534b87d2407f00409012608fe16090146890024c7ef0408fe46887c2407ee0409036789024788ff26087b2408fd1607ed0409044688fc3576c034d8792407ec0408f25658af3698fa34e8f93428dc24d8f82458f70428f65688f14756bf45d8ae3798783508db25d8d625c7eb0508f05678ad36b84a35b8773508d525c7ea0508ef3608f25688ee3708763508d425c8e41707e90508ed3708e927c8e31708ef5688d135c8ec25c7e80508ec5608ee6708ed5708d035c8eb25c7e70508e94708e84688d24608752407e60408e625c8743507e50508e46708e35708733508682507e40508f37808f16808f05808ea3708723508e727c8e52708cf25c8672508e21707e30508d936c8e026c8de5708d825c7e20508dc4688da2448db6716be45a8c74568d926a8d82668c825a8c32568d44658ac2698d12608d15608d56708d45708d336c8d23608d02608c212c8d65618cf4578ce35b8cd3578cc34b8cb3478aa25b84924b8c92448c836c83728c8c726c8c624c8c51288c21508c225c6be5688c325c8c11607e10508f56718f45708e14676ba45d8a936b87135084834b8df26b8dd2678d725d8ca25c8662508c424b8c02477e00508be12c8bd34b8bc4586b734d86f2407de0408af3618ba0428b95686b645d8ae3718a625c7dd0508ad3718b734a8b63468b52468a54688b34607dc0408b22748a325c8b11787db0508af67889d36c8ac26c7da0608ac6708ab2448ae7808ad68089b36c8aa26c7d90608a84686b434d7d80408a236d89d2618a53688a43648a257089f12c89d67089c2448a65628a346f8a136f8a036389e34b89b26384524b8b86728b45728b047f6b145d8a937384434b8a727e89a25c7d605089812c89734b84124b86e2307d503083f23b89414d7d40406ae45d86d35083e34b89625c8952448931287d205083d34a81bb4600624a1e924686146183c23a81aa3688646587837083b34a819b4689025588f25400424a1e724688d26588b25588a25487737088825487637088316087436088356287c36e87336286b26e86826288213d88113588012588767288657287b37e87237286a27e86727288526d88426c87f16087d56887c15085f24687b34787a25585e24787646587416087456087767087657087536c87316087856187245787024586e344816b4685d256091a4686b15086a347868160867457865040815b4686424644da54814b4686125685c24685f26485b04085b56085c67085a04086267286067085e37e812b4685d27e85924689156f88e56388c46f88945f87e45787936e87136286f35e86d35283a34a80fb4686c26f86926e86626286325f85825700324a090a471e624683d3500062508341287d105085124c85524483312885325c7d00508514588504507cf04084e12485456885236883b35084f26400425084d1688311287ce05084a37184a68083738c84926c8301387cd06084724c84624484526c82f1387cc06084324c8422447cb0408401247ca05084126c82d13883f1287c906083c25483d56f83b56383636e83946a8384688372718362407c80407c70408334588321547c60407c50507c40507c304082e1247c205082914c7c104082814c7c00407bf04082916e82815e83456f83156383026382f25b82d25382c16f82b15f82a15782714d7be04085667f84c67384b57284837384436b83e36383a35083527e0032508261287bc0501e945081ba4081b1507bb8507bb04082335c1e83507ba85082115c7b9850822d688224681e7450820a68819a408201688191507b88507b804081e35d81d35c8181507b785081a15481716d81747081467081346081146e81b56f81956381846281616f81515f81215781014d82467f81f67381cd7281c4721e645080fa4080f1507b48507b40407d123b7bb2377d034a7b934680801880b13f80a13b8091378071337fd3557eb2617dd25980c2497ce23b7b82378060448042597db24b8020258012497af02f7a10277ea2617ff2497e92617fc2517f81507e83607fc5627ef36e7e73627fb26e7fa0257e52517f84527ee25f7e42537f715f7f612f7f51277ad02f79f0277f32597fe5627fd4627ed26f7e32637f92517f41507f205d7ac02f79e0277f05687ef2507ee1507ed3477e94657da3697e83607e51607e85607e55607ea6707e95707e73607e626c7e41607eb5617e34577d935b7cd34b7e22577e12477df0457da3617dc2647da6707dd5627db46f7d93637cc34b7d826e7ab03f7d70257aa02f7ca23b7a902f7c934b7d52447d41287a803f7d30257c71287d03587cf2547c61287c51387c41387cb1247c21387ca1287c31247c745f7c64537c52537c424b7c22437c115f7c014f7bf1477a702f7d156f7ce5637cd3637cc35b7c93537c826e7be1287a603f7bd0257ba4587b92587bb56f7b85637b74627b604d7b504c7b32497b12517ae26c7ad1607aa2547a91287a71287af45f7ac4577ab35b7a83537a634b7a525f7a42577a32477a036079f1607a145f79e45780d45f80545380335f80034f7f13477ec25f7e02537de24f7d624b7d22437bc23b7b42377b204f7b00477a202f79d02795c56f93b56393246292f36f92635f90a35769434d8fb26f8bf2638bb25f89925b89225385724182523b80e23779c0405f123b4512336f713e6c812e7980227991367971346c612e79425878f24479435c79235c78e24079115078f24c78e35478d12879524f79324b79024778c24374b16173715978b14b5ed12b44f12378337176236979635974a2717362695ec23b44b23378a1546f413e6c312e78845f78745778615b73414b73325b7851646f013c6c012e7614797322796ef14c7771366bf12e77514478213478025477413477f27077e17c77313477c2647711446be12c76f2443bd18c77a16477915c77212477623c77416077013c77767177526a7732666be13977213177112976f12176c16075f35b76d25b76b25772f15b44a13376a12b76912378367175e46b78136b77d36772e26b44924377b23b7782336ee14c6e813c76e1367681346ba12e76614476514b7641546b712e7614717492716ed14c75b1346b612e75a14476023876178075714475f13474827175d1646ec13c6b412e75a36175526174516175923c75956075a67075823c75567075315475b56275736375626f75426374416344813375212b76267275e47375c37e7432734472436fe17e6eb14c7511346b112e74f15444613374e12b44524374d1346ae12e74947973d24e74b1646e214e73c25c6e115c7451446e014c74713c74567074978074848c74126473b25c7462446fd18c6df15c74414474245b74135b74034f73f34373c47873c67073d67173b46a73a13674a67174346b73e25473924e6fc17c6dd14e73247172825471d24e7371646dc14e73527472625471c24c7341746db14c72526471b25c6da15c73113c73278072d28c72426471a25c7302446d915c72f1446d714c72c13472d37172b36972a1646d513e72536172114e72567072015c72156272024d72856272746372636f72436372334f72234371f14e71b47071713471613471514471b67071414471526071556071756271626e71426271d67271c47e71a47271937e6fa17e71813671313473667273347f72e47372927e71e25471224e6f917e6d214e70f13471034f70e34370d14e70b13670a13470c25470924e6cf14e7023647072717052597012557055656fb15b7022707014556ff2666fd1716fd35b6fb3696fa13e70645770425b7032597002576e82516fe24b6fc1616f914b5ea12b4441235e913900e9311e51290061216ef3706ed3686f62556f52546e21716dc1695e713900c9311e31290041216f346e6f24626f12556e52476db14b6da1696ef5616d915b6e11616e01616ed5626ec26e6df1636e42565e61396ce1296d814b5e41396cd129611a546e66726e537e6e427e5e31396cc1296e14786e16706e037c6e26716df46a6de1366da4706da6706d717c6d73706d62646dc6726db47e6d94726d837e6d517e6d41366d31346d11366d01346ce37e6cd36e6cc3666cb17e6f756f6f45636f036e6ee3626eb35a6ea26f6e926e6e82626e725f6e32576dd1636d215b6cf1535e01390079316ca12b1e21290031211e593e0061326c71346bf3716b63696c63596c51556c41541e393e0041326c21656c11646a41346bf6716a313d6be13a6bd1366bc1356bb1346b91556b81546b51646b66726b437e6b31356b21346b01356af1346ad3696a33616a71566a213e69a14469b1346ab3596a013e6991366971446981346a96726a83616a717e69e13e6961366a41346a125469f26c6a537e6a33726a217e6a016e69e16669b35869a25869836069726069c47269916e6961666c856f6c35636c036f6ba3636b735f6b135b6ae3536ac16f6aa15f6a615769d13f1e293e69513700313279a56f78956378436f76736376335f75035b74c35373826371125b7082535df23b4432336f816e6c913e69412e61524b5f12435bf14659012e69135269035068f15e68e15c58f12e5bc24668935868b04868534468945c68434068725068534c68445468313868113c68a34f68834b68634768234365a16163c15968014b61313b5ef13366d46568d45565927163b26968c25860f24b5ec24367f1545bb14658c12e66c34763a14b60e13b66b45763725b60d24b67d16458912e67b37c67813c67a35b67935763615b67713b63326b67614458612e67413c67314b60a13b60924b67215458512e65816165727167015666f15458412e66a36065627166116c58112e66936066c17465f16c65526166713666756266636266a56266946f66836f65326360824b5d516e66513665216166056465e13c66356f66256366146265f36f65116365d15360513b66e67266d57266b47f66436064e27360424b5d417e65c16c58012e65657565a2645b525664914c65826464814c65547065227c64714c6556705d227c6541446525705d117c6501646577806566806534705d028c65127c64f17c64d15464514c57912864d46664c15e64b15c64746564113664867064757064636c64013464156164024664956164545764435764334f64234763f13665967164e5675cf27c5b225664a15663e14c57812863c2645b125663015662b14c63916c63a27463817462a14c63514c63625463415462914c6321645af14662e15c62e5626306725ce17e62f15e62d15c62836d6241366285705cd17c5cc16c6221346245625cc36e62336262224662b56262a46f62946362736f62634f6253475cb16e62113663b67263757f6335735ca27e5ac25663117e62c15662014c61e15e61d15c5a71545a91445a81545a614461934a5a834661b34f61a3475a51466181365a425661c15661714c59e25460014c00612861415c6111545ff13c61215c61115459d14461326459c2546101645fe14c00412860e2745fd14c60c15c60b15460a2645fc14c60716c60616460847060527c5fa14c6031666021645ff1545fb36c5f61345f51345f626e5f525660056f5fe5635fd46f5fc45f5fa4575f936f5f835f5f73575f413661567f60f67360d57f60956f6045675c727e59b25460117e5f314c00312859a2545e914c1e51245f015c1e41545e813c5ee15c1e41545991445ef2645982545ed1645e714c1e31245eb1645e81545c417c5c316c5e51545c336e5e23625e956f5e75635e636f5e435f5e33575c216e5e11365f167f5ec6735c127e5922545ea17e5e014c1e21245dc3585de37d5db3595d93555dc47c5db5655d94555d31615d21615d756a5d65685d52505d01713711695791615d36785d23605d116c5d04575cd26d5cc25d5ce1465cb13c5c91665c81645c426d5c325d5c61665c51645c213c5dd4575da35b5d83575d43475cf1613701595781515ca14b5c713b5c11330061491e514159e13959a1315be4595bd4585b51715b11695bc1580041491e314159c1395981315b956a5a31515971415b95725b837e5a21515961415a11515951415b56715b415e5b315c5b04685b16725af17e5ae15e5ad15c5a924d5a82455a723d5a62355ab15e5aa15c5a513c5a35725a256a5a15625a017e59d15459e56f59c56359915459415c59445a59a56f59856359746359645b59545359314e5bf56f5bb5635ba4635b745b5b64535b21635ac15b5a415300314959f1431e214159b13959213100614a1e91461da15c57346158235558146558f45558e15558d15400414a1e714658b16558a16458814558714456f16526b15525f1543f315458345058215458467258157257c17e57917227f16d27416c57715d56c14d21214556a14c57f46556e15656914e20d14657d56857c34757a16c57945756814c20c14456616c56714c57746557645556514e20b14657046d57315656414e20a14656215456314c57067057467257267057146d56f45d56e17e56114e20714656815c56a46456846456745456635456467056346c56236c56c56656b47e56917e56516e56116659056f58c56358946f58646358545f58045757e16f57b16e57816257515f56d15756014f00314a1fd1471e614669256f67e56367c46f67546367145f65b45763d26361f25b6162535f224b5df2435c016e59114655f12e51b34a44212050803044113044013055c35255b35043e12050703055725855904855002055324455735c54f03055224055505054e02055324c55235454d03055024e54f24a54e24654d24255824f55624b55424755124354c02251835851634854a24854313c54703c51734854825054605054434654314e51534a54914f54514754213d43d12053346555a45554b35851434a541a5854115843112050303053245753145753f36851334842f12050203053c67053d25b53b25752937051235853a34842d12053835851134842b12050003053635a5353584291204ff0305303604241204fc03053237852e36042312042113052f26442013041f13041e14053056252e46f52d26f52c26341c13053467253357253147f52637252b3604181204fa03052826d52726c52324d51f24552224c52546d52124e51e24652246c52356652126651f46651e26652946152645752425752024f51d24751814d517145516125515b5851a25551925451515850c25750b25650d47050d67050e67250c47250b27e51b56f51456351346e51246251145e51026f50f25f50a2574fe2544fd24550623f5052374fc3555073455040444f20364f50555010454fe23e4fd0444ec0364ff5624fc4624fb05d4f904d4f30354f93554f83454ed0354f635d4f534d4f04684f33544f20544e93544f056c4ea4604ee6704e84504ed36c4ec06c4ea5604e935c4e85644f145f4ef45b4eb4574e745350845f50345350235f50034f4fa3474f704f4f40474e603755d56f54056353e46f53946353745f52a45751c36250934a4051204e503046eb4b451b4346e24b4512434422342b214f25a14b1f314a1dc1470b914605b1434e225c4e0a504e035c4df35043f2341da15c4e1b5e4deb524e125e4de25243e2344dd15e4dc15d4db15c1d91554da1522b114d1d814543d23443c2342af14c31a5714b14654d745d1d945543b2343b81703571682ae14e25814a1d71460591423195704d335843a1244ce3444d45704d345c4391241454604cd3404361241444704cc3404351244d10504ce34c4cd0404cf5704cc4544cba384cb1384331243184613574594af3554d534f4d234b4d03474ca343498a61486a59469a3b44ca3349816148615946913b44c1334321244ae4654d9455497b71485b69468b4b44bb4349727148526946824b44b2434312343b71713851703561694d81584d61554c91542ad14f25614b1f014a1d61470b51460571434ac45743023440217e35415a31315625414a1c41464c545f4c44574aa347483a4b466a3b48314b46613b4a9457482b5b465b4b48225b46524b42f2344c71684c61654c316435215b31215725314b1c314742e2343f617e35016a30e1664bf35b4be35747fa5b47f15b47eb6b47e26b42d23434e16b30d1674c11484c01454bd14442c23425114a1c214630c34f462a3b46213b26b123461b4b46124b42b2343091654bb1584ba1554b915425014b1c11473f315442a2343b5170496a61496161495b714952714292343b41713f215d4b715a4b61564b51554b41544282342ac14c1be1444b25604272343b31702ab14c1bd1444261244b045149e450494a61494161425124493b714a8b604932714a82604242343b217138417049d1604b11554af1542aa14d1bc1450ad1444ad16c4ab5604a7b604a72604232344ac1784aa1744a016c49b160492b614a85624a746f490b63460b4b3cc16e41b2344a567e3f26724192343f117e3b117224e14a1c01464a15644a356f4a25634a036f36535748ea6345da3b48e16345d13b27f12349e15449c16449d56249b46f4b36724ae5724a947f48db734a6b6045cb4b48d2734a626045c24b4182343f017f3cb17e3af1733811724a416d49f16c49a16036a15d2a914d24d14b1bf1471ba1450ac14449446547db6938e93c49357547cc7938da4c4981640a715638ca4c49616438b93c49247038aa4c4941640a61544926704912443c917c49578049368049047048f27c48c254388a4c3c818c48e17c0a515448a14c48a35648c46648b15e48915c49767148d56747ac6b45ac5b449c53488256387a4c3c717c0a015647d36147814647c47147725632aa4c48616409f156484274329a4c48317448114c480254328a4c47f15447d17447c78047b2443c618c09d1464781644776723c517e47615e47515c48567248257f47e57347a473458c5b447c5347927e474256326a4c3c417e09915647215e47115c456c5b445c534702562b4a4c0951561fca4c08f15400612046d15c46a15408e14446b15c46a1541fb93c46c2641faa4c46916408d15400412046716c1f9a4c46617446415c4631541f8a4c46216445f16c45e1644604701f6a4c45d17c45b2443c318c08c16445924408b16408a15445724408916445416646e67f46867346557f46156f45c56745a47345846b45646345545b45327e1f5a4c3be17e08815400312000ea4c08715400612845015c44d15408614444e15c44d15400d93c44f26400ca4c44c16408515400412844a2443bd18c08016444824407f16407e15444624407d16445167f44b67344947344746b44546344427e007a4c3ba17e07b1540031282a513f24c13b1b913705613341712d2a413d1b613544124244024043f14d1b71452a313d1b513541512d2fd46142735543c34d1b734534d1582a113e24b13a1b413605513241412d2fc4604383501393501383604371404360404341282fb35134d34942524543a23f43923b43523743323342435543e3453ae16134c15943d14843b1454321442a013f24913b1b313705313341312d3ed16e34b14a2f614624813a1a213641212d42334743015534914b2f514724713b1a113741112d3e116e34815a2f115641012d34615b2f015742e13540f12d24613a1a013640e12d2ed15542c14524513b19f13740d12d3ad1613de14d42a14540c12d42845042225029f13c19b1344263414212503ac16142714542514429e13d19a13540b12d4202503ab15142214529d13d19813542145242035f41f25f41e2533dd15f3aa15336314d29c13d24413b19e13719613541d12f41b56e3de56241a2523dc16e3a916224313a19d13640812d42956242446242336f41c2503db16f3a716341915d36214d29b13d24213b19c13719513540712d41624c40b3554153454141454121554101352e815540e14540a25c40a35235e13d29812d19312540c56240b46240925c40815d35d14d29713d19213541745f41345341135f40f35340d34f4073473d815f35a14f2e714729513f19113744245f43145342f35f42d35342b34f4183473d715f39415335914f33814b2e61472d314329413f22f13b19013704813340612d2e568c3ef2343ee2344003683ed12418f68c3ff4783ec2344021643f94643eb2344001643ff57c3ea2341871543f84603e823428c14c1861443fc3703fbb723fb2723e523433715a2e115629314d28a14c18e1453e42343f947c3e22343f71443f74643e11243f857429248c3e02343f61443df23438017028914c1851443de2343f31543dc1243f46783f26703db23437f1803f116c28814c1841442e457c18d57c3eb3683ed1543e43543eb46c1821443e33503e23503e927018113429113d18c1353e72623e626029013d18b1353d912d3e436c3e32603e246428f37c3e113418013417f1343df5683de5603dd2503dc15c17e1343da26c3d93553ef45f3ee4573ec35f3ea35b3e83573e53553e03533db3472e314728e13f22e13a18a13717d1363d812d40456f40356740146f3fe46b3fd4673fa4653f54633f04573d723437e17033615a2e21572df15628d14f28714e22814a18914717c1460451423d33583d537d3d23593d03553d347c3d25653d045538067c3caa613ca1613c9a6137f67d3ce56a3cd5683c8a713cca503c81713cc1503ca6783c93603c84573c6b5b3c3b4b3bdb433c63713c514632793c3c146e3c04623c33713c21663bf1643bd3713bc1663bb16400b93c37e56d3d44573d135b3cf3573cb3473c7a613c4a4b3bea3b3baa333c71613c414b3be13b3ba1333b346538e93c38e12c3b25753ae3443b826428625e17b25638d94c38d13c3b615c3ad3443b526438c94c38c13c38b93c38b12c3ac3443b326428525c17a25438a94c38a13c3a92343a82343b47803b26803a734437f28c3b127c28425c1792543b017c39315438894c38813c3ac4651782463a613c3a513c3ab3601772443a413c1762443ab5601752443921443a213c3a22503ad6703ac5703aa3603a926c1742443a816c3911443a113c3a43553a02593a55603a44603a325c3a22503a056039e56039c0383994603972303973443a64513a134739f24b39d24739b23f39a23b3982373962333ae5613a745717324639014639513c3912343922503913563934663902342dd16638b35538a46538e15438b15438c67038a57038926c38d5613884572dc1563b76713af56739434437e27c2db26628225e16c25638f15638794c38713c38446537493e37412e37393e37312e38457037f17d38316d38216c37b14d37714537193e36e93d37112e36e12d38067837f45737a14c37d46d37914e37614636d93c36d12c37a46c37b56637916637746637616637346537357037216c37456137145736f26c36e45736d15638556138145737e16d37c15737814f37514737093e36c93d37012e36c12d36223428114d27714c22714a15e14616a14515d144368a6023c23436836c367360369b6e366b6236926e36626235f23436516e27f16d27416c28014d27514c16914527e13d16713536325027d13d16613535d12d27c13d16513536125236025027a15d27b13d16413535b12d35e25c35c25c35d35535b34536235535f34527913f16313735a12d36a46536445535923433516827814f27314e22614a16214715c14604314234d23433214634c34435726427225e15b25633115632a94c32a13c34b23435516c34a23434934435427435317432994c32913c34823435114c34723434634435025434f15432894c32813c33013634d25415824632f14634513c34b26434a16434413c34824434714434313c34225d34246033c23033c34433b12434545234435f34335334125f34025333f23f33e23b33d23733a23334c56234946f34646315724633416e32e14633913c33746532d14632793c32712c2c715432c14615613633423426f14e15514633012432f23433216433015432f56233167232e23432d17e32c16c32a56232946f32846332716e35667235257f34e57333834433627e33526c26e25e15025633317e32b15632694c32613c31647d3114713082342e517d26514e22514a1471460421423071243062342d21703231543051243041243210303032342d01703201443012342cf17031e16c1441642ff1242fe2342cd17031c1442fd2342fc12431935d1443552fb12430a46d32245f31f45b31d45731b4532fa2342cc16031a15731815626d14f26314e22314a14f1471431460401422f92343141742f82342f71243145702f61243166803156782f52343131742f423430f1442f32342f212430f6702f112431178031047c2f023430e1442ef2342e017e2de17230c15626b15525f15426c14d26114c14d1452ee23422214a13d14630a6702ed23422114a13c1462f936d2f43612e416d22013a13b1362ec12d3071443050203041343022501381543002382ff1342fc24d1382452ee35d30634f30334b3013472fe3432fd1472fb14626a13f21e13a14c1371371362eb12d2f71642f74602f95702f85682f61642f21342f25602f46702f336c2f113426814526913d14a1352ea12d21d13a1321362e912d2ee56021c13a1311362e812d2e935d2e95602ec5622eb5602ea35d2e834d3085622fa5602f536f2f03632ef35d2ed34d2e316f26713f21b13a1491371301362e712d2e42342e45702e56802e32342e13652e035d2de46d2dd1462dc93c2dc12c32467231767031247f30d47330b46d30945d2e62342e217f2df17e2db1722c615026614f25e14e21a14a14814712f14603e1422d62302d63442d923f2d823b2d72372d52332c51462bd1442d413c2c41442c31542d11442c21442c11542ce1442d245f2d045b2cf4572cd4532c01462b71442cb34f2ca34b2c93472c83432cc5602c715c2bf1462b61442c435e2c335a2c23562c13522c05602c52342bf16425d14c2ba0502bc34f2bb34b2b93472b83432b74502bd2342b615425d14e0969462d33442c626425c25e12c2562be1562b51542b494c2b413c2a52342191581e91442a32342a22341da15c2ab4642af45c2a837c2a11242aa5742b15642a748c2b04642a02342861802721782ae1642171581e71442ac45029f12429e2342851702ab1542aa57229b23428817e28417228115d27715c21214529a2342711682a81542a757129923429217d27015a2601562a424029f35429e4642a345429a37c2a23542a115429d25029f14429d45227e14d21113529e46229c25027d14d21013529712d29a46128f16d29612d29825c29745629636e2a556f2a056329b45629936e28e16f27915f26715720f13529512d29023428f23429126029046428f37c20e13429357429248c28e23420d14428b36e28956828c46628a46428845628557428557028667128456628314427d23420c14427b23427a23427e25027c25027d46427b45427a35428157428056427f46427923420b14427635e27746427545427435427147c27157027267227047e26f17e12d14426a23420a14426923426823420913426a67026946c26836c20813426d78026c57c26b47c26723420714426435626234626567226367026146c26037e25f36c25d1541511442b267f2ad6732a95662a647e29423428d17f28717e28217227816f27316e26e16a26616725e16625c1622161581fd1451e614424c34421925c0ab2541fc94c1fc13c24b23425915c1fb93c1fb12c24a23421814c0aa14424934425826421725c0a92542571641fa94c1fa13c24823425516c2473442542741f994c1f913c24623425215c2453442212742512641f894c1f813c24323424f16424234424e27c22726c2121541f694c1f613c24113c24b25424a15424013c24826423f13c21c26424625423e13c21114423c13c24436024326c21014423b13c23d25c23c25023635c23412423202824145f24045323f35f23e34f23b34723a25f23925323824f23724b23524723324323123b24c56f24956324746f24545f24245722e26e21b25621516e20f14623013c22d15620e13622d12422b46e22a46222e23422c16622916420d14620c14422746503f15420b14622023421f12422246d21e23422415620a14621d23422267021c23421d35d21f14620913621d56022056221e56021c34d20813622567222367022145d21b23421417e04416c20714602514421815402414421956f21756301d14421523421415621023420c15c21125021035620e16e20815620604220404020e12420c36420304020912420204020103020956020003020a6702081241ff04020623420014620112420145020256020012420423420315e1ff15621246620f23420d17e20b16e2071662050521fe0501fb1541f726c1fc56f1fa5631f946f1f845f1f645725a67f25667325357f25056f24d56722f34422827e22626e21a26621625c0a825421317e1fd1561f594c1f513c00467e1e91460ab1451e593e1e193d1e512e1e112d0aa1441e093c1e012c00657e1f21551f11541e71460a91451e393e1df93d1e312e1df12d1ec1560051541ed6721ec17e1eb1441e84581e956f1e75631e41541e556f1e35631e01541e156f1df5631f356f1f05631ef16f1ee15f1ea1571e61460a81451e293e1de93d1e212e1de12d1b92340ab14803d1400fd0501b82341b72341da15c1b52341d34701bd3641b41240fc0401d25801db5681d95641bc4741d84641b323417b18015b1781d71640a914803b1400fa05018e4741b22341c417403914012b0501b123418818c03815012a0601b023415a1781d31641d26711af23418f17d15916a1421661ce5781694641ae2341c21640361401290501c84641ad2341cf1641ce67c1ac23416117c0351501601441280601c95701ab2340341401270501a92340321401cc7801c656014d47c1a82341c017c0311401cb0701260501a72341a62341c96701c846c1a42341c716c1c66741bb5741a323413e17402f1501411441250601a21240f90401a12341c41740f80501a01240f704019f23413c1741c21640f605019d1240f504019c2341c017c15e16c0f40501be45019b12419a23417a1701bd1541992341bc5721bb45119523418417e17917216a15d15d15c1240420f30401b624019b2540f20301b04701b84581b745419a3641b53541781701581681b41540f004018b3641a216412304018317c1220501b056118d16d19412d1ad4681643541a01541210401a63541ad56c1200501a746011f0401a54501ab6701a445014a36c1aa26019d16c1a906011e0401a75601a635c1a52501a456419946413316413613411d0500ef0301a21640ee0400ed0301311641a01540ec0400eb0400ea03019e26019d16c0e904019825017716019b14419725017615019845219734117f15e17515216714d11c03219a46219934119625017e16e17416216614d19212d11b03219325c19446219235611a0421b956f1b35631b246f1b14631af4621ae45f1ac45b1a84571a34531a136f19f35f19c35719535618a16f17d16e17316216315f15715a14915713015619112d1190420e804018d23418b23418c26018d47018b3640e704018f58018e47418a2340e605018312411805018212418112418012418556817e12411704018045817f14018336118225a18125617e2461160320e503018847118736a18636618435617d1241150420e404017a47417823417015c0e305017723416f14c17a57017423416e14c1773640e204017625017645017746017525017856117435617214e1140420e104011304017212411205016f36416f46017056116e35617b67117946617323417115e16d15c1110520e00501682341662341642341672501652501684581663641643540df04016b56816a4741694641632340de05011005010f0500dd04010e03216146916045915f45815e36515d36410d0420dc04015a57015823415215c0db05015a6700da04015856215616e15414e10c0420d90400d80301561240d704010b04015412410a05015256215b67215957215723415517e15315e15115c1090520d605014c2340d505014b23414a2340d40400d30400d203014c67014b46014a36c0d104014f78014e57014d47c1492340d005013b1240cf04013a12413912413812414505013f46114645a14445613d36d1371241080420ce04013612410705013512413412410605013f6701331241050501321240cd04013d6701311240cc0400cb03013904013435113a34a13834613225d1040320ca0301030401345600c90301325600c803013b56213756013635113535013334113124d1020320c703014767214367014247214146114046013e45113c35d1301241010420c404010005012e15e12d15c09613c09692c0ff0520c30501232340f916401b14012223411817c01a1501212340f715401814012023411016c10f14411f2341276700d446c11e2340f516c11d23410516401615010714411b23410e15c0ef15411716c0ed14411f5600d235c0ea15c10313411c25012346e12246212145e12045a11e45611d45211b35611616e11416210c15a10215611a12d11712411736011847011612411314c11312411423411215c11046810f45810e36410b14c10b12410c23410a15c10646010412410312410656010456010335010867010746010545010212410015c06c13c06c92c12b57e12a57212956e12856a12656612556212446611923411517e11117210d16e10916a1011660ff1620131400f32340f21240f11240f02340e31700db1680fc1540fb0540ef1240ee2340f91640ed1240ec2340cc1640f71540ea1240e92340f516c0dd15c0e21600da1580f21440f10440ef1540c81540ed1440eb2500ea15c0f345f0f04530ee35f0ec34f0e93470e715f0e515e0e11520df14f0d914a0d11470c71460c204f0be0470e72340e51240e22340e24510e35610e12340df2340dd3550da2340da4520d815e0d81240db5620d92340d716e0d32340d22340d35600d235c0d56700d446c0d12340cb1240cd35d0ca1240c91240cd5600c81240c924d0c94500cb4520ca4500c823d0c604d0c61240cf5620ce5600cc34d0c71240c505d05f13c05f92c0c11440c11240c22340c01540be2340bd16c0fd56f0fa5630f846f0f645f0f44570e82340e616f0e416e0e01620de15f0dc15e0d615a0d01570c41560c31520bf05f0bc0571dc67f1d66731d557f1d45731d15721d056f1cd56b1ca5671c55631c347f1c146f1bf4671ba46619023418917f17c17e16c17216216f15c16e15016a14816712f16612c1620a81480121400fe0520bb0500ab34e00634d08fa39087a3108f13908713107a0420790500b70320b44710b24690b84590b64580ad3640a934e00434d0a7a7109fa6908da39085a310a717109f16908d1390851310780420770500b46710b156a094a51084a410941510841410760500750500740400b26720b15720b037e093a51083a41093151083141073050092a51081a410921510811410720500a6a610a61610ad4620a5a630a51630aa1540ab56f0a95630a64740a315c0a65700a214c0710500a35610a24560a76710a546608cb49080b410a415e0a115c07005209b15c09e46806f05009b56209f67208bb4907fb4109d17e09c15e09a15c06e05206005006d05006c04205f040089b4907db4109815e09715c09613c06b05205e05006a04009457209356a09256209117e06905008e15408a13408f56f08d56308c36308b35b08935308615406805008214406705007e13406604008756f08556308446308345b08145308036307f35b07d35307c14e065042077470075468079458077561068a4106814107556207436e067a4106714107115c06f15c06d15c06c13c06a16e06846206745206614c06303c07a56f07856307646207345a072452070a6306ea5b06ba53069a41065a3107016306e15b06b15306914106513106482f06282306401f06201305f13c060a4b05ea4306014b05e1430b956f0b55630b34630af45b0ae4530ac3560a834e00334d0a0a63099a5b095a53090a43088a3907ba310a016309915b09515309014308813907b13106104205d04005634403d25400e94c00e13c00612c05523405a15c00d93c00d12c05423403c14405334405926403b25405816400c94c00c13c00412c05213c05112c05525405415405013c05114405245f05045304f25f04e25304d24f04c24b04b24704a24305656f05356301116e04913c04716604616400b93c00b12c04415400a93c00a12c04115600993c00912c04267204067001017e03f16c00893c00812c02514c03c15402414c01c03003a16402e14c01b04002d15c01a05001903003715402c14c01804002b15c02a14c02914c03467003316c02814c03206001704002715c03014401605002a56002905002e46e02d46202c45e02b45a02845602745201504201404002545f02445302335f02235302134f02034b01f34701e34301c15401914401714401b46e01a46201845e01645201514e01414c03d56f03b56303946f03846303645f03545b03145702f45302614e01d14c01304201123401015600d15400a56200956000e56f00c56300b16e00815600515400656f00456305b67f05767304834404527e04326e03e26601225400f17e00794c00713c00312c4e356f4c85634c246f4bc4634b845f499457487b63473b5b46fb53452b4b443b4348726347325b46f25345224b4432434052343d616f3b916e38616336b16235815f32515b2da1572b315325b14f1f414b1dd14a0ba14705c146002143efb45fed3453ed035fec4353ebc34fe91347e63a5fcf8a53ceda4fc21a4bc0ea43bb1a3f95da3b79ba37693a33e6315fcf8153ced14fc2114bc0e143bb113f95d13b79b13769313355e92f55e12b4e412700112300003f 18 5 11 13 6
def m_2411 : Nat := 0xffffffffffffffff
def s_2411 : List Nat := [0x5555555555555555, 0x3333333333333333, 0xf0f0f0f0f0f0f0f, 0xff00ff00ff00ff, 0xffff0000ffff, 0xffffffff]
def g_2411 : Nat := 0x1111115011f1f7f
def bds_2411 : List (Nat × List Nat × Nat × Nat) := [(m_2097, s_2097, 7, g_2097), (m_1764, s_1764, 7, g_1764), (m_2136, s_2136, 6, g_2136), (m_2304, s_2304, 8, g_2304), (m_1744, s_1744, 7, g_1744), (m_2302, s_2302, 8, g_2302), (m_2065, s_2065, 6, g_2065), (m_1920, s_1920, 6, g_1920), (m_2306, s_2306, 10, g_2306), (m_2296, s_2296, 9, g_2296), (m_2297, s_2297, 6, g_2297), (m_2137, s_2137, 6, g_2137), (m_2400, s_2400, 9, g_2400), (m_2172, s_2172, 7, g_2172), (m_2363, s_2363, 10, g_2363), (m_2177, s_2177, 7, g_2177), (m_1798, s_1798, 6, g_1798), (m_1765, s_1765, 6, g_1765), (m_2365, s_2365, 10, g_2365), (m_1864, s_1864, 6, g_1864), (m_2034, s_2034, 7, g_2034), (m_2038, s_2038, 7, g_2038), (m_1964, s_1964, 6, g_1964), (m_2277, s_2277, 7, g_2277), (m_2031, s_2031, 7, g_2031), (m_2289, s_2289, 6, g_2289), (m_2039, s_2039, 6, g_2039), (m_2122, s_2122, 6, g_2122), (m_2126, s_2126, 6, g_2126), (m_2362, s_2362, 10, g_2362), (m_2040, s_2040, 6, g_2040), (m_2389, s_2389, 10, g_2389), (m_1836, s_1836, 6, g_1836), (m_2113, s_2113, 6, g_2113), (m_2367, s_2367, 10, g_2367), (m_1758, s_1758, 6, g_1758), (m_1780, s_1780, 6, g_1780), (m_2010, s_2010, 7, g_2010), (m_2054, s_2054, 6, g_2054), (m_1748, s_1748, 7, g_1748), (m_2119, s_2119, 6, g_2119), (m_2035, s_2035, 6, g_2035), (m_1994, s_1994, 7, g_1994), (m_2024, s_2024, 6, g_2024), (m_2003, s_2003, 7, g_2003)]
theorem kn_2411 : KnownBin bds_2411 := by
  intro b hb
  simp only [bds_2411, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_2097
  · exact lb_1764
  · exact lb_2136
  · exact lb_2304
  · exact lb_1744
  · exact lb_2302
  · exact lb_2065
  · exact lb_1920
  · exact lb_2306
  · exact lb_2296
  · exact lb_2297
  · exact lb_2137
  · exact lb_2400
  · exact lb_2172
  · exact lb_2363
  · exact lb_2177
  · exact lb_1798
  · exact lb_1765
  · exact lb_2365
  · exact lb_1864
  · exact lb_2034
  · exact lb_2038
  · exact lb_1964
  · exact lb_2277
  · exact lb_2031
  · exact lb_2289
  · exact lb_2039
  · exact lb_2122
  · exact lb_2126
  · exact lb_2362
  · exact lb_2040
  · exact lb_2389
  · exact lb_1836
  · exact lb_2113
  · exact lb_2367
  · exact lb_1758
  · exact lb_1780
  · exact lb_2010
  · exact lb_2054
  · exact lb_1748
  · exact lb_2119
  · exact lb_2035
  · exact lb_1994
  · exact lb_2024
  · exact lb_2003
theorem sub_2411 : ∀ b ∈ bds_2411, m_2411 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2411, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_2411 : ∀ b ∈ bds_2411, canon b.1 g_2411 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2411, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2411 : dagCheckRootsF m_2411 g_2411 bds_2411 (dagRefSwapF 3836 (dagTraceF m_2411 s_2411 11 f_2411) l_2411 0) s_2411 11 = true := by decide +kernel
def node_2411 : Nat → Bool := dagCheckNodeWithF m_2411 g_2411 bds_2411 (dagTraceF m_2411 s_2411 11 f_2411) (dagRefSwapF 3836 (dagTraceF m_2411 s_2411 11 f_2411) l_2411)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2411_0 : treeBlockF 0 128 node_2411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2411_1 : treeBlockF 128 256 node_2411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2411_2 : treeBlockF 256 384 node_2411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2411_3 : treeBlockF 384 512 node_2411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2411_4 : treeBlockF 512 640 node_2411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2411_5 : treeBlockF 640 768 node_2411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2411_6 : treeBlockF 768 896 node_2411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2411_7 : treeBlockF 896 1024 node_2411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2411_8 : treeBlockF 1024 1152 node_2411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2411_9 : treeBlockF 1152 1280 node_2411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2411_10 : treeBlockF 1280 1408 node_2411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2411_11 : treeBlockF 1408 1536 node_2411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2411_12 : treeBlockF 1536 1664 node_2411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2411_13 : treeBlockF 1664 1792 node_2411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2411_14 : treeBlockF 1792 1920 node_2411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2411_15 : treeBlockF 1920 2048 node_2411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2411_16 : treeBlockF 2048 2176 node_2411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2411_17 : treeBlockF 2176 2304 node_2411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2411_18 : treeBlockF 2304 2432 node_2411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2411_19 : treeBlockF 2432 2560 node_2411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2411_20 : treeBlockF 2560 2688 node_2411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2411_21 : treeBlockF 2688 2816 node_2411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2411_22 : treeBlockF 2816 2944 node_2411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2411_23 : treeBlockF 2944 3072 node_2411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2411_24 : treeBlockF 3072 3200 node_2411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2411_25 : treeBlockF 3200 3328 node_2411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2411_26 : treeBlockF 3328 3456 node_2411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2411_27 : treeBlockF 3456 3584 node_2411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2411_28 : treeBlockF 3584 3712 node_2411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2411_29 : treeBlockF 3712 3836 node_2411 = true := by decide +kernel
theorem nc_2411 : ∀ j, 0 ≤ j → j < 3836 → node_2411 j = true :=
  (joinChecks (joinChecks (joinChecks (joinChecks (certBlock nb_2411_0) (joinChecks (certBlock nb_2411_1) (certBlock nb_2411_2))) (joinChecks (joinChecks (certBlock nb_2411_3) (certBlock nb_2411_4)) (joinChecks (certBlock nb_2411_5) (certBlock nb_2411_6)))) (joinChecks (joinChecks (joinChecks (certBlock nb_2411_7) (certBlock nb_2411_8)) (joinChecks (certBlock nb_2411_9) (certBlock nb_2411_10))) (joinChecks (joinChecks (certBlock nb_2411_11) (certBlock nb_2411_12)) (joinChecks (certBlock nb_2411_13) (certBlock nb_2411_14))))) (joinChecks (joinChecks (joinChecks (certBlock nb_2411_15) (joinChecks (certBlock nb_2411_16) (certBlock nb_2411_17))) (joinChecks (joinChecks (certBlock nb_2411_18) (certBlock nb_2411_19)) (joinChecks (certBlock nb_2411_20) (certBlock nb_2411_21)))) (joinChecks (joinChecks (joinChecks (certBlock nb_2411_22) (certBlock nb_2411_23)) (joinChecks (certBlock nb_2411_24) (certBlock nb_2411_25))) (joinChecks (joinChecks (certBlock nb_2411_26) (certBlock nb_2411_27)) (joinChecks (certBlock nb_2411_28) (certBlock nb_2411_29))))))
theorem lb_2411 : LowerBin m_2411 s_2411 g_2411 12 :=
  lowerDagSwapF (top := 63) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2411 sub_2411 gl_2411 rc_2411 nc_2411

def wg : List Gate :=
  [⟨GateOp.and, [0, 1]⟩,
    ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.and, [3, 4]⟩,
    ⟨GateOp.or, [6, 7]⟩,
    ⟨GateOp.and, [2, 9]⟩,
    ⟨GateOp.or, [2, 9]⟩,
    ⟨GateOp.or, [8, 10]⟩,
    ⟨GateOp.and, [8, 10]⟩,
    ⟨GateOp.and, [1, 11]⟩,
    ⟨GateOp.or, [0, 14]⟩,
    ⟨GateOp.or, [13, 15]⟩,
    ⟨GateOp.or, [5, 12]⟩,
    ⟨GateOp.and, [16, 17]⟩]

theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg
  simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) =
    Nat.testBit (4277071594 * 2 ^ 32 + 4276150400) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4277071594 * 2 ^ 32 + 4276150400)) (13 - 1) := by
  exact lb_2411

end PEqualNP.Outside.L_meta_44806

theorem PEqualNP.Outside.L_meta_44806 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4276150400) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4276150400) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact PEqualNP.Outside.L_meta_44806.table2_from_lowerBin
    (4277071594 * 2 ^ 32 + 4276150400) 13 PEqualNP.Outside.L_meta_44806.root_lb
    PEqualNP.Outside.L_meta_44806.wg 18 rfl
    PEqualNP.Outside.L_meta_44806.wfits PEqualNP.Outside.L_meta_44806.weval
