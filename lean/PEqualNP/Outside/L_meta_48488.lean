import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48488

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

theorem masked_self (mask : Nat) : Masked mask mask := by
  unfold Masked; simp

theorem masked_land_right (mask w : Nat) : Masked mask (w &&& mask) := by
  unfold Masked; apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and]

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

-- The general checker is from barelyanything's pull request 54457.

theorem blockSpec {f : Nat → Bool} {lo hi : Nat} (h : treeBlockF lo hi f = true) :
    ∀ i, lo ≤ i → i < hi → f i = true := fun _ hlo hhi => treeBlockF_at h hlo hhi

theorem joinBlockSpecs {f : Nat → Bool} {lo mid hi : Nat}
    (first : ∀ i, lo ≤ i → i < mid → f i = true)
    (last : ∀ i, mid ≤ i → i < hi → f i = true) :
    ∀ i, lo ≤ i → i < hi → f i = true := by
  intro i hlo hhi
  by_cases h : i < mid
  · exact first i hlo h
  · exact last i (by omega) hhi


section Relabel

variable {n r : Nat}


def rowPull (p : Fin r → Fin n) (w : Nat) : Nat :=
  (BitVec.ofBoolListLE (List.ofFn fun i : Fin r => w.testBit (p i).val)).toNat

theorem rowPull_testBit (p : Fin r → Fin n) (w i : Nat) :
    (rowPull p w).testBit i = if h : i < r then w.testBit (p ⟨i, h⟩).val else false := by
  simp only [rowPull, BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : i < r <;> simp [h]

theorem rowPull_bit (p : Fin r → Fin n) (w : Nat) (i : Fin r) :
    (rowPull p w).testBit i.val = w.testBit (p i).val := by
  simp only [rowPull_testBit, i.isLt, dite_true]

theorem rowPull_zero (p : Fin r → Fin n) : rowPull p 0 = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : i < r <;> simp [rowPull_testBit, h]

theorem rowPull_and (p : Fin r → Fin n) (a b : Nat) :
    rowPull p (a &&& b) = rowPull p a &&& rowPull p b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : i < r <;> simp [rowPull_testBit, h]

theorem rowPull_or (p : Fin r → Fin n) (a b : Nat) :
    rowPull p (a ||| b) = rowPull p a ||| rowPull p b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : i < r <;> simp [rowPull_testBit, h]

theorem rowPull_xor (p : Fin r → Fin n) (a b : Nat) :
    rowPull p (a ^^^ b) = rowPull p a ^^^ rowPull p b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : i < r <;> simp [rowPull_testBit, h]

def rowCanon (p : Fin r → Fin n) (mask w : Nat) : Nat :=
  canon (rowPull p mask) (rowPull p w)

theorem rowCanon_zero (p : Fin r → Fin n) (mask : Nat) : rowCanon p mask 0 = 0 := by
  rw [rowCanon, rowPull_zero, canon_zero]

theorem rowCanon_canon (p : Fin r → Fin n) (mask w : Nat) :
    rowCanon p mask (canon mask w) = rowCanon p mask w := by
  have cut : rowCanon p mask (w &&& mask) = rowCanon p mask w := by
    rw [rowCanon, rowPull_and, canon_land]
    rfl
  rcases canon_cases mask w with ⟨h0, hz | hm⟩ | ⟨_, h | h⟩
  · rw [h0, rowCanon_zero, ← cut, hz, rowCanon_zero]
  · rw [h0, rowCanon_zero, ← cut, hm, rowCanon, canon_self]
  · rw [h, cut]
  · rw [h, rowCanon, rowPull_xor, canon_xor_mask]
    exact cut

private theorem rowCanon_binOp (p : Fin r → Fin n) (mask op a b : Nat) (hop : op < 4) :
    rowCanon p mask (binOp mask op a b) = 0 ∨
    rowCanon p mask (binOp mask op a b) = rowCanon p mask a ∨
    rowCanon p mask (binOp mask op a b) = rowCanon p mask b ∨
    ∃ k < 4, rowCanon p mask (binOp mask op a b) =
      binOp (rowPull p mask) k (rowCanon p mask a) (rowCanon p mask b) := by
  rcases (show op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 by omega) with rfl | rfl | rfl | rfl
  · rw [show binOp mask 0 a b = canon mask (a &&& b) from rfl, rowCanon_canon]
    simp only [rowCanon, rowPull_and]
    exact canon_and_in_binOp _ _ _
  · rw [show binOp mask 1 a b = canon mask (a ||| b) from rfl, rowCanon_canon]
    simp only [rowCanon, rowPull_or]
    exact canon_or_in_binOp _ _ _
  · rw [show binOp mask 2 a b = canon mask (a &&& (mask ^^^ b)) from rfl, rowCanon_canon]
    simp only [rowCanon, rowPull_and, rowPull_xor]
    simpa only [canon_xor_mask] using
      canon_and_in_binOp (rowPull p mask) (rowPull p a) (rowPull p mask ^^^ rowPull p b)
  · rw [show binOp mask 3 a b = canon mask ((mask ^^^ a) &&& b) from rfl, rowCanon_canon]
    simp only [rowCanon, rowPull_and, rowPull_xor]
    simpa only [canon_xor_mask] using
      canon_and_in_binOp (rowPull p mask) (rowPull p mask ^^^ rowPull p a) (rowPull p b)

theorem avail_rowPull (p : Fin r → Fin n) {mask w : Nat} {bank bank' : List Nat}
    (stocked : ∀ u ∈ bank, Avail bank' (rowCanon p mask u)) (h : Avail bank w) :
    Avail bank' (rowCanon p mask w) := by
  rcases h with rfl | h
  · exact .inl (rowCanon_zero p mask)
  · exact stocked _ h

private theorem gateBin_copy {mask w : Nat} {bank : List Nat} (h : Avail bank w)
    (hc : canon mask w = w) : GateBin mask bank w := by
  refine ⟨w, w, 0, by omega, h, h, ?_⟩
  change w = canon mask (w &&& w)
  rw [Nat.and_self, hc]

theorem gateBin_rowPull (p : Fin r → Fin n) {mask w : Nat} {bank bank' : List Nat}
    (stocked : ∀ u ∈ bank, Avail bank' (rowCanon p mask u)) (h : GateBin mask bank w) :
    GateBin (rowPull p mask) bank' (rowCanon p mask w) := by
  obtain ⟨a, b, op, hop, ha, hb, rfl⟩ := h
  have ha' := avail_rowPull p stocked ha
  have hb' := avail_rowPull p stocked hb
  have hcanon := canon_idem (rowPull p mask) (rowPull p (binOp mask op a b))
  rcases rowCanon_binOp p mask op a b hop with h0 | h1 | h2 | ⟨k, hk, hv⟩
  · exact gateBin_copy (.inl h0) hcanon
  · exact gateBin_copy (h1.symm ▸ ha') hcanon
  · exact gateBin_copy (h2.symm ▸ hb') hcanon
  · exact ⟨_, _, k, hk, ha', hb', hv⟩

theorem buildsBin_rowPull (p : Fin r → Fin n) {mask : Nat} {bank bank' vs : List Nat}
    (stocked : ∀ u ∈ bank, Avail bank' (rowCanon p mask u)) (h : BuildsBin mask bank vs) :
    BuildsBin (rowPull p mask) bank' (vs.map (rowCanon p mask)) := by
  induction vs generalizing bank bank' with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨gateBin_rowPull p stocked h.1, ih ?_ h.2⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact .inr List.mem_cons_self
    · rcases stocked w hw with h0 | hmem
      · exact .inl h0
      · exact .inr (List.mem_cons_of_mem _ hmem)

theorem lowerBin_of_rowPull (p : Fin r → Fin n) {mask goal k : Nat} {stock stock' : List Nat}
    (stocked : ∀ w ∈ stock, Avail stock' (rowCanon p mask w))
    (known : LowerBin (rowPull p mask) stock' (rowCanon p mask goal) k) :
    LowerBin mask stock goal k := by
  intro vs circuit hit
  have projected := buildsBin_rowPull p stocked circuit
  have output : Avail (vs.map (rowCanon p mask) ++ stock') (rowCanon p mask goal) := by
    apply avail_rowPull p _ hit
    intro w hw
    rcases List.mem_append.mp hw with hvs | hs
    · exact .inr (List.mem_append_left _ (List.mem_map_of_mem hvs))
    · rcases stocked w hs with h0 | hmem
      · exact .inl h0
      · exact .inr (List.mem_append_right _ hmem)
  simpa only [List.length_map] using known _ projected output

theorem rowPull_inverse (p : Equiv.Perm (Fin n)) (w : Nat) :
    rowPull p.symm (rowPull p w) = w % 2 ^ n := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : i < n
  · let j : Fin n := ⟨i, h⟩
    simp only [Nat.testBit_mod_two_pow, h, decide_true, Bool.true_and]
    change (rowPull p.symm (rowPull p w)).testBit j.val = w.testBit j.val
    rw [rowPull_bit p.symm, rowPull_bit p, Equiv.apply_symm_apply]
  · simp [rowPull_testBit, Nat.testBit_mod_two_pow, h]

private theorem canon_before_width {mask : Nat} (h : mask < 2 ^ n) (w : Nat) :
    canon mask (w % 2 ^ n) = canon mask w := by
  rw [← canon_land mask (w % 2 ^ n), ← canon_land mask w]
  congr 1
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · simp [Nat.testBit_and, Nat.testBit_mod_two_pow, hi]
  · have hz : mask.testBit i = false := Nat.testBit_lt_two_pow
      (h.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_of_not_lt hi)))
    simp [Nat.testBit_and, hz]

theorem rowCanon_inverse (p : Equiv.Perm (Fin n)) {mask : Nat} (h : mask < 2 ^ n) (w : Nat) :
    rowCanon p.symm (rowPull p mask) (rowCanon p mask w) = canon mask w := by
  change rowCanon p.symm (rowPull p mask) (canon (rowPull p mask) (rowPull p w)) = canon mask w
  rw [rowCanon_canon, rowCanon, rowPull_inverse p mask, rowPull_inverse p w,
    Nat.mod_eq_of_lt h, canon_before_width h]

theorem rowCanon_injective_on_canon (p : Equiv.Perm (Fin n)) {mask a b : Nat}
    (hm : mask < 2 ^ n) (ha : canon mask a = a) (hb : canon mask b = b)
    (h : rowCanon p mask a = rowCanon p mask b) : a = b := by
  have e := congrArg (rowCanon p.symm (rowPull p mask)) h
  simpa only [rowCanon_inverse p hm, ha, hb] using e

end Relabel


def decodeRows (code : Nat) (i : Fin 64) : Fin 64 :=
  ⟨Nat.mod (Nat.shiftRight code (Nat.mul i.val 6)) 64, Nat.mod_lt _ (by decide)⟩

abbrev DagState := Nat × List Nat × List (Nat × Nat × Nat)

def RefSound (mask goal count : Nat) (states : Nat → Option DagState)
    (ref : Nat → Nat → DagState → Bool) : Prop :=
  ∀ parent tok st, ref parent tok st = true →
    ∃ dest saved, dest < count ∧ states dest = some saved ∧ saved.1 = st.1 ∧
      ∀ k, LiveBin mask goal k st.2.1.toFinset → LiveBin mask goal k saved.2.1.toFinset

def checkNodeVia (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option DagState) (ref : Nat → Nat → DagState → Bool) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some st => dagCheckChildren mask goal bounds (ref (i + 1)) st

theorem dagAllNodesRef {mask goal fuel count : Nat} {stock : List Nat}
    {boundsFor : Nat → List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {ref : Nat → Nat → DagState → Bool}
    (hgm : Masked mask goal) (hknown : ∀ i, KnownBin (boundsFor i))
    (hsub : ∀ i, ∀ b ∈ boundsFor i, mask &&& b.1 = b.1) (snd : stock.Nodup)
    (good : RefSound mask goal count (dagTrace mask stock fuel forest) ref)
    (hnodes : ∀ i, 0 ≤ i → i < count → checkNodeVia mask goal (boundsFor i)
      (dagTrace mask stock fuel forest) ref i = true) :
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
    unfold checkNodeVia at hchk
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
          · have hopen := dagLocal_open (state := (rem - 1, ws', (z, x, y) :: hist)) hgm (hknown i) (hsub i) hnd' (k := k') (by omega) hlive'
            rw [hopen] at hloc; exact Bool.noConfusion hloc
          · obtain ⟨dest, saved, hdest, htr', heq, moved⟩ :=
              good (i + 1) (makeToken a b op keep) _ href
            exact ih (rem - 1) (by omega) dest saved hdest htr' heq k' (by omega) (moved k' hlive')

theorem lowerDagRef {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {boundsFor : Nat → List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {ref : Nat → Nat → DagState → Bool}
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hroots : dagCheckRoots mask goal bounds
      (ref 0) stock fuel = true)
    (hknownFor : ∀ i, KnownBin (boundsFor i))
    (hsubFor : ∀ i, ∀ b ∈ boundsFor i, mask &&& b.1 = b.1)
    (good : RefSound mask goal count (dagTrace mask stock fuel forest) ref)
    (hnodes : ∀ i, 0 ≤ i → i < count → checkNodeVia mask goal (boundsFor i)
      (dagTrace mask stock fuel forest) ref i = true) :
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
  · obtain ⟨dest, saved, hdest, htr, heq, moved⟩ := good 0 tok _ href
    exact dagAllNodesRef hgm hknownFor hsubFor snd good hnodes fuel dest saved hdest htr heq k
      (by omega) (moved k hlive')

def chooseBounds : List (Nat × List Nat × Nat × Nat) → Nat → List (Nat × List Nat × Nat × Nat)
  | [], _ => []
  | b :: bs, bits =>
    let rest := chooseBounds bs (Nat.shiftRight bits 1)
    Bool.rec rest (b :: rest) (Nat.testBit bits 0)

theorem chooseBounds_mem {bs : List (Nat × List Nat × Nat × Nat)} (bits : Nat)
    {b : Nat × List Nat × Nat × Nat} (h : b ∈ chooseBounds bs bits) : b ∈ bs := by
  induction bs generalizing bits with
  | nil => simp [chooseBounds] at h
  | cons a tail ih =>
    cases e : Nat.testBit bits 0
    · simp only [chooseBounds, e] at h
      exact List.mem_cons_of_mem _ (ih _ h)
    · simp only [chooseBounds, e] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih _ h)

def checkNodeViaF (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option DagState) (ref : Nat → Nat → DagState → Bool) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some st => dagCheckChildrenF mask goal bounds (ref (Nat.add i 1)) st

theorem checkNodeViaF_eq {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (states : Nat → Option DagState) (ref : Nat → Nat → DagState → Bool) (i : Nat) :
    checkNodeViaF mask goal bounds states ref i = checkNodeVia mask goal bounds states ref i := by
  unfold checkNodeViaF checkNodeVia
  cases states i with
  | none => rfl
  | some st => exact dagCheckChildrenF_eq hgoals _ st

theorem lowerDagRefF {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)} {profile : Nat → Nat}
    {forest : Nat → Nat × Nat} {ref : Nat → Nat → DagState → Bool}
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true) (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (good : RefSound mask goal count (dagTraceF mask stock fuel forest) ref)
    (hroots : dagCheckRootsF mask goal bounds (ref 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → checkNodeViaF mask goal (chooseBounds bounds (profile i))
      (dagTraceF mask stock fuel forest) ref i = true) :
    LowerBin mask stock goal (fuel + 1) := by
  have htr : dagTraceF mask stock fuel forest = dagTrace mask stock fuel forest := by
    funext i; exact dagTraceF_eq mask stock fuel forest i
  rw [htr] at good hnodes
  rw [dagCheckRootsF_eq hgoals] at hroots
  have mem i b (hb : b ∈ chooseBounds bounds (profile i)) := chooseBounds_mem (profile i) hb
  refine lowerDagRef hgm hgnz hcs snd hknown hsub hroots
    (boundsFor := fun i => chooseBounds bounds (profile i))
    (fun i b hb => hknown b (mem i b hb)) (fun i b hb => hsub b (mem i b hb)) good ?_
  intro i hlo hhi
  have h := hnodes i hlo hhi
  rwa [checkNodeViaF_eq (fun b hb => hgoals b (mem i b hb))] at h



theorem image_dropIf (f : Nat → Nat) (drop : Bool) (x : Nat) (S : Finset Nat)
    (hinj : ∀ w ∈ S, f w = f x → w = x) :
    (dropIf drop x S).image f = dropIf drop (f x) (S.image f) := by
  cases drop with
  | false => rfl
  | true =>
    change (S.erase x).image f = (S.image f).erase (f x)
    ext y
    constructor
    · intro hy
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
      exact Finset.mem_erase.mpr ⟨fun eq => hne (hinj w hmem eq), Finset.mem_image_of_mem _ hmem⟩
    · intro hy
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hy
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hmem
      exact Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨fun eq => hne (congrArg f eq), hw⟩)

theorem liveBin_rowPerm {n : Nat} (p : Equiv.Perm (Fin n)) {mask goal k : Nat} {S : Finset Nat}
    (hm : mask < 2 ^ n) (h : LiveBin mask goal k S) (canonical : ∀ w ∈ S, canon mask w = w) :
    LiveBin (rowPull p mask) (rowCanon p mask goal) k (S.image (rowCanon p mask)) := by
  induction h with
  | done =>
    simpa only [Finset.image_singleton] using
      (LiveBin.done (mask := rowPull p mask) (goal := rowCanon p mask goal))
  | @step k S a b op ha hb hab ha0 hb0 hop hz fresh keepA keepB _ ih =>
    let f := rowCanon p mask
    let z := binOp mask op a b
    let after := dropIf (!keepA) a (dropIf (!keepB) b S)
    have cz : canon mask z = z := binOp_canon mask op a b
    have ca := canonical a ha
    have cb := canonical b hb
    have ha' : f a ∈ S.image f := Finset.mem_image_of_mem _ ha
    have hb' : f b ∈ S.image f := Finset.mem_image_of_mem _ hb
    have distinct : f a ≠ f b := fun he => hab (rowCanon_injective_on_canon p hm ca cb he)
    have nonzero {w : Nat} (hw : canon mask w = w) (hn : w ≠ 0) : f w ≠ 0 := by
      intro he
      exact hn (rowCanon_injective_on_canon p hm hw (canon_zero mask)
        (he.trans (rowCanon_zero p mask).symm))
    have new : f z ∉ S.image f := by
      intro hit
      obtain ⟨w, hw, eq⟩ := Finset.mem_image.mp hit
      have he := rowCanon_injective_on_canon p hm (canonical w hw) cz eq
      apply fresh
      change z ∈ S
      rwa [← he]
    have moved : ∃ op' < 4, f z = binOp (rowPull p mask) op' (f a) (f b) := by
      rcases rowCanon_binOp p mask op a b hop with eq | eq | eq | ok
      · exact (nonzero cz hz eq).elim
      · exfalso
        apply new
        change f z = f a at eq
        rwa [eq]
      · exfalso
        apply new
        change f z = f b at eq
        rwa [eq]
      · exact ok
    obtain ⟨op', hop', produced⟩ := moved
    have nextCanonical : ∀ w ∈ insert z after, canon mask w = w := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact cz
      · exact canonical w (dropIf_subset (!keepB) b S
          (dropIf_subset (!keepA) a (dropIf (!keepB) b S) hw))
    have firstDrop : (dropIf (!keepB) b S).image f = dropIf (!keepB) (f b) (S.image f) :=
      image_dropIf f (!keepB) b S (fun w hw => rowCanon_injective_on_canon p hm (canonical w hw) cb)
    have movedAfter : after.image f = dropIf (!keepA) (f a) (dropIf (!keepB) (f b) (S.image f)) := by
      unfold after
      rw [image_dropIf f (!keepA) a (dropIf (!keepB) b S), firstDrop]
      intro w hw
      exact rowCanon_injective_on_canon p hm (canonical w (dropIf_subset (!keepB) b S hw)) ca
    have rest := ih nextCanonical
    change LiveBin (rowPull p mask) (rowCanon p mask goal) k ((insert z after).image f) at rest
    rw [Finset.image_insert, movedAfter, produced] at rest
    exact LiveBin.step ha' hb' distinct (nonzero ca ha0) (nonzero cb hb0) hop'
      (by rw [← produced]; exact nonzero cz hz) (by rwa [← produced]) keepA keepB rest

theorem liveBin_rowSymmetry {n : Nat} (p : Equiv.Perm (Fin n)) {mask goal k : Nat} {S : Finset Nat}
    (hm : mask < 2 ^ n) (hmask : rowPull p mask = mask) (hgoal : rowCanon p mask goal = goal)
    (h : LiveBin mask goal k S) (canonical : ∀ w ∈ S, canon mask w = w) :
    LiveBin mask goal k (S.image (rowCanon p mask)) := by
  simpa only [hmask, hgoal] using liveBin_rowPerm p hm h canonical

structure RowAction64 where
  source : Fin 64 → Fin 64
  apply : Nat → Nat
  testBit_eq : ∀ w (i : Fin 64), (apply w).testBit i.val = w.testBit (source i).val

def RowAction64.id : RowAction64 := ⟨fun i => i, fun w => w, fun _ _ => rfl⟩

def RowAction64.comp (a b : RowAction64) : RowAction64 :=
  ⟨fun i => b.source (a.source i), fun w => a.apply (b.apply w), by
    intro w i
    rw [a.testBit_eq, b.testBit_eq]⟩

private def lowerLane (lo d : Nat) (i : Fin 64) : Bool :=
  decide (d ≤ i.val) && lo.testBit (i.val - d)

private def maskSource (lo hi d : Nat) (i : Fin 64) : Fin 64 :=
  ⟨(if lowerLane lo d i then i.val - d
    else if hi.testBit (d + i.val) then d + i.val else i.val) % 64, Nat.mod_lt _ (by decide)⟩

def goodMaskLanes (lo hi keep d : Nat) (i : Fin 64) : Prop :=
  let a := lowerLane lo d i
  let b := hi.testBit (d + i.val)
  let c := keep.testBit i.val
  (a = true ∧ b = false ∧ c = false) ∨
    (a = false ∧ b = true ∧ c = false ∧ d + i.val < 64) ∨
    (a = false ∧ b = false ∧ c = true)

def maskedRow64 (lo hi keep d : Nat) (cert : ∀ i : Fin 64, goodMaskLanes lo hi keep d i) : RowAction64 :=
  ⟨maskSource lo hi d, fun w => ((lo &&& w) <<< d) ||| ((hi &&& w) >>> d) ||| (keep &&& w), by
    intro w i
    have bits : (((lo &&& w) <<< d) ||| ((hi &&& w) >>> d) ||| (keep &&& w)).testBit i.val =
        ((lowerLane lo d i && w.testBit (i.val-d)) ||
          (hi.testBit (d+i.val) && w.testBit (d+i.val)) ||
          (keep.testBit i.val && w.testBit i.val)) := by
      simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
        lowerLane, Bool.and_assoc]
    rw [bits]
    have h := cert i
    unfold goodMaskLanes at h
    rcases h with ⟨a,b,c⟩ | ⟨a,b,c,h⟩ | ⟨a,b,c⟩
    · have h : i.val-d < 64 := (Nat.sub_le ..).trans_lt i.isLt
      simp [maskSource, a, b, c, Nat.mod_eq_of_lt h]
    · simp [maskSource, a, b, c, Nat.mod_eq_of_lt h]
    · simp [maskSource, a, b, c, Nat.mod_eq_of_lt i.isLt]⟩

theorem fullMask_testBit (i : Nat) : fullMask.testBit i = decide (i < 64) := by
  change (2 ^ 64 - 1).testBit i = _
  exact Nat.testBit_two_pow_sub_one _ _

theorem rowPull_fullMask (p : Fin 64 → Fin 64) : rowPull p fullMask = fullMask := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 64
  · simp [rowPull_testBit, hi, fullMask_testBit, (p ⟨i, hi⟩).isLt]
  · simp [rowPull_testBit, hi, fullMask_testBit]

theorem RowAction64.pull_eq (a : RowAction64) {p : Fin 64 → Fin 64} (h : ∀ i, a.source i = p i)
    (w : Nat) : a.apply w &&& fullMask = rowPull p w := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, fullMask_testBit]
  by_cases hi : i < 64
  · let j : Fin 64 := ⟨i, hi⟩
    simp only [hi, decide_true, Bool.and_true]
    change (a.apply w).testBit j.val = (rowPull p w).testBit j.val
    rw [a.testBit_eq, rowPull_bit, h]
  · simp [hi, rowPull_testBit]

theorem RowAction64.canon_eq (a : RowAction64) {p : Fin 64 → Fin 64} (h : ∀ i, a.source i = p i)
    (w : Nat) : canonF fullMask (a.apply w) = rowCanon p fullMask w := by
  rw [canonF_eq, ← canon_land fullMask (a.apply w), a.pull_eq h, rowCanon, rowPull_fullMask]


def unpackPaged (pages : List Nat) (width pageBits i : Nat) : Nat :=
  unpackF (getDN pages (Nat.shiftRight i pageBits)) width
    (Nat.land i (Nat.sub (Nat.shiftLeft 1 pageBits) 1))

def unpackPagedWidths (pages : List (Nat × Nat)) (pageBits i : Nat) : Nat :=
  let page := pages.getD (Nat.shiftRight i pageBits) (0, 0)
  unpackF page.2 page.1 (Nat.land i (Nat.sub (Nat.shiftLeft 1 pageBits) 1))

def unpackForestRelative (row : Nat → Nat) (tBits : Nat) : Nat → Nat × Nat := fun i =>
  let code := row i
  let distance := Nat.shiftRight code tBits
  (Bool.rec (Nat.sub (Nat.add i 1) distance) 0 (Nat.beq distance 0),
    Nat.land code (Nat.sub (Nat.shiftLeft 1 tBits) 1))

def unpackLinksPaged (index entry : Nat → Nat) (sizeBits tokBits steps : Nat) : Nat → Nat → Option Nat :=
  fun parent tok =>
    let start := index parent
    let sz := Nat.land start (Nat.sub (Nat.shiftLeft 1 sizeBits) 1)
    let off := Nat.shiftRight start sizeBits
    (Nat.rec (motive := fun _ => Nat → Nat → Option Nat) (fun _ _ => none)
      (fun _ next lo hi =>
        Bool.rec none
          (let mid := Nat.shiftRight (Nat.add lo hi) 1
           let code := entry mid
           let key := Nat.land code (Nat.sub (Nat.shiftLeft 1 tokBits) 1)
           Bool.rec
             (Bool.rec (next (Nat.add mid 1) hi) (next lo mid) (Nat.blt tok key))
             (some (Nat.shiftRight code tokBits)) (Nat.beq tok key))
          (Nat.blt lo hi)) steps) off (Nat.add off sz)

abbrev TableSymmetry (mask goal : Nat) :=
  {s : ({p : Equiv.Perm (Fin 64) // rowPull p mask = mask ∧
      rowCanon p mask goal = goal}) × (Nat → Nat) //
    ∀ w, s.2 w = rowCanon s.1.val mask w}

def rowSort (f : Nat → Nat) : List Nat → List Nat
  | [] => []
  | w :: ws => insertSortedF (f w) (rowSort f ws)

theorem rowSort_mem (f : Nat → Nat) (ws : List Nat) (w : Nat) :
    w ∈ rowSort f ws ↔ w ∈ ws.map f := by
  induction ws with
  | nil => rfl
  | cons a as ih => simp only [rowSort, List.map_cons, insertSortedF_eq, insertSorted_mem, List.mem_cons, ih]

theorem rowSort_finset (f : Nat → Nat) (ws : List Nat) :
    (rowSort f ws).toFinset = ws.toFinset.image f := by
  ext w
  simp only [List.mem_toFinset, rowSort_mem, List.mem_map, Finset.mem_image]

def refMatches (mask goal : Nat) (syms : List (TableSymmetry mask goal))
    (sym : Nat) (saved st : DagState) : Bool :=
  if Nat.beq sym 0 then eqListN st.2.1 saved.2.1
  else match syms[sym]? with
  | none => false
  | some p => st.2.1.all (fun w => Nat.beq (canonF mask w) w) &&
      eqListN (rowSort p.val.2 st.2.1) saved.2.1

theorem refMatches_sound {mask goal : Nat} (hm : mask < 2 ^ 64)
    (syms : List (TableSymmetry mask goal)) (sym : Nat) (saved st : DagState)
    (hc : refMatches mask goal syms sym saved st = true) (k : Nat)
    (live : LiveBin mask goal k st.2.1.toFinset) : LiveBin mask goal k saved.2.1.toFinset := by
  unfold refMatches at hc
  split at hc
  · simp only [eqListN_eq, beq_iff_eq] at hc
    exact hc ▸ live
  · split at hc
    · contradiction
    · rename_i p hp
      simp only [Bool.and_eq_true, eqListN_eq, beq_iff_eq] at hc
      have hcanonical : ∀ w ∈ st.2.1.toFinset, canon mask w = w := by
        intro w hw
        have h := Nat.beq_eq.mp (List.all_eq_true.mp hc.1 w (List.mem_toFinset.mp hw))
        rwa [canonF_eq] at h
      have moved := liveBin_rowSymmetry p.val.1.val hm p.val.1.property.1 p.val.1.property.2 live hcanonical
      have haction : p.val.2 = rowCanon p.val.1.val mask := funext p.property
      rw [← haction, ← rowSort_finset, hc.2] at moved
      exact moved

def symDagRef (mask goal count bits : Nat) (syms : List (TableSymmetry mask goal))
    (states : Nat → Option DagState) (links : Nat → Nat → Option Nat)
    (parent tok : Nat) (st : DagState) : Bool :=
  match links parent tok with
  | none => false
  | some code =>
    let dest := Nat.shiftRight code bits
    let sym := Nat.land code (Nat.sub (Nat.shiftLeft 1 bits) 1)
    Nat.blt dest count &&
      (match states dest with
      | none => false
      | some saved => Nat.beq saved.1 st.1 && refMatches mask goal syms sym saved st)

theorem symDagRef_sound {mask goal count bits : Nat} (hm : mask < 2 ^ 64)
    (syms : List (TableSymmetry mask goal)) (states : Nat → Option DagState)
    (links : Nat → Nat → Option Nat) : RefSound mask goal count states
      (symDagRef mask goal count bits syms states links) := by
  intro parent tok st h
  unfold symDagRef at h
  split at h
  · contradiction
  · rename_i code heq
    simp only [Bool.and_eq_true] at h
    obtain ⟨hd, hmoves⟩ := h
    split at hmoves
    · contradiction
    · rename_i saved hstate
      simp only [Bool.and_eq_true] at hmoves
      obtain ⟨hf, hmatch⟩ := hmoves
      exact ⟨_, saved, Nat.blt_eq.mp hd, hstate, Nat.beq_eq.mp hf,
        refMatches_sound hm syms _ saved st hmatch⟩

def cert_mask : Nat := 0xffffffffffffffff
def cert_stock : List Nat := [0xffffffff, 0xffff0000ffff, 0xff00ff00ff00ff, 0xf0f0f0f0f0f0f0f, 0x3333333333333333, 0x5555555555555555]
def cert_goal : Nat := 0x11717570157577f
def cert_bounds : List (Nat × List Nat × Nat × Nat) := [(0xf0f0f0f0f0f0f0f0, [0xf0f0f0f0, 0xf0f00000f0f0, 0xf000f000f000f0, 0x3030303030303030, 0x5050505050505050], 9, 0x10105000505070), (0xcccccccccccccccc, [0xcccccccc, 0xcccc0000cccc, 0xcc00cc00cc00cc, 0xc0c0c0c0c0c0c0c, 0x4444444444444444], 9, 0x404440044444c), (0xff00ff00ff00ff, [0xff00ff, 0xff000000ff, 0xf000f000f000f, 0x33003300330033, 0x55005500550055], 9, 0x1700570057007f), (0xffff0000ffff, [0xffff, 0xff000000ff, 0xf0f00000f0f, 0x333300003333, 0x555500005555], 9, 0x17570000577f), (0x5555555555555555, [0x55555555, 0x555500005555, 0x55005500550055, 0x505050505050505, 0x1111111111111111], 8, 0x115155501555555), (0xaaaaaaaaaaaaaaaa, [0xaaaaaaaa, 0xaaaa0000aaaa, 0xaa00aa00aa00aa, 0xa0a0a0a0a0a0a0a, 0x2222222222222222], 8, 0x202020002022a), (0xf0f0f0f0f0f0f0f, [0xf0f0f0f, 0xf0f00000f0f, 0xf000f000f000f, 0x303030303030303, 0x505050505050505], 8, 0x10707070107070f), (0xffff00000000ffff, [0xffff, 0xff0000000000ff, 0xf0f000000000f0f, 0x3333000000003333, 0x5555000000005555], 10, 0x11700000000577f), (0xff00ff00ff00ff00, [0xff00ff00, 0xff000000ff00, 0xf000f000f000f00, 0x3300330033003300, 0x5500550055005500], 8, 0x100170001005700), (0x3333333333333333, [0x33333333, 0x333300003333, 0x33003300330033, 0x303030303030303, 0x1111111111111111], 8, 0x113131301131333), (0xffff0000ffff0000, [0xffff0000, 0xff000000ff0000, 0xf0f00000f0f0000, 0x3333000033330000, 0x5555000055550000], 8, 0x117000001570000), (0xffffffff00000000, [0xffff00000000, 0xff00ff00000000, 0xf0f0f0f00000000, 0x3333333300000000, 0x5555555500000000], 9, 0x117175700000000), (0xffffffff, [0xffff, 0xff00ff, 0xf0f0f0f, 0x33333333, 0x55555555], 9, 0x157577f), (0x55555555aaaaaaaa, [0xaaaaaaaa, 0x55550000aaaa, 0x55005500aa00aa, 0x50505050a0a0a0a, 0x1111111122222222], 10, 0x11515550002022a), (0x5555555500000000, [0x555500000000, 0x55005500000000, 0x505050500000000, 0x1111111100000000], 7, 0x115155500000000), (0x5500550055005500, [0x55005500, 0x550000005500, 0x500050005000500, 0x1100110011001100], 5, 0x100150001005500), (0xff000000ff, [0xff, 0xf0000000f, 0x3300000033, 0x5500000055], 5, 0x570000007f), (0xf0f0f0f00f0f0f0f, [0xf0f0f0f, 0xf0f000000f0f, 0xf000f0000f000f, 0x3030303003030303, 0x5050505005050505], 10, 0x1010500107070f), (0xaaaaaaaa, [0xaaaa, 0xaa00aa, 0xa0a0a0a, 0x22222222], 7, 0x2022a), (0x5050505050505050, [0x50505050, 0x505000005050, 0x50005000500050, 0x1010101010101010], 5, 0x10105000505050), (0xf0f00000f0f0, [0xf0f0, 0xf0000000f0, 0x303000003030, 0x505000005050], 6, 0x105000005070), (0x33333333, [0x3333, 0x330033, 0x3030303, 0x11111111], 7, 0x1131333), (0xa0a0a0a0a0a0a0a, [0xa0a0a0a, 0xa0a00000a0a, 0xa000a000a000a, 0x202020202020202], 5, 0x202020002020a), (0xff00ff0000000000, [0xff0000000000, 0xf000f0000000000, 0x3300330000000000, 0x5500550000000000], 7, 0x100170000000000), (0xf0f0f0f, [0xf0f, 0xf000f, 0x3030303, 0x5050505], 7, 0x107070f), (0xffff000000000000, [0xff000000000000, 0xf0f000000000000, 0x3333000000000000, 0x5555000000000000], 7, 0x117000000000000), (0x4444444444444444, [0x44444444, 0x444400004444, 0x44004400440044, 0x404040404040404], 5, 0x4044400444444), (0xcc00cc00cc00cc, [0xcc00cc, 0xcc000000cc, 0xc000c000c000c, 0x44004400440044], 6, 0x400440044004c), (0x5555000055550000, [0x55550000, 0x55000000550000, 0x505000005050000, 0x1111000011110000], 5, 0x115000001550000), (0x2222222222222222, [0x22222222, 0x222200002222, 0x22002200220022, 0x202020202020202], 5, 0x2020200020222), (0xaa00aa00aa00aa, [0xaa00aa, 0xaa000000aa, 0xa000a000a000a, 0x22002200220022], 5, 0x200020002002a), (0xc0c0c0c0c0c0c0c, [0xc0c0c0c, 0xc0c00000c0c, 0xc000c000c000c, 0x404040404040404], 5, 0x404040004040c), (0xaaaa0000aaaa, [0xaaaa, 0xaa000000aa, 0xa0a00000a0a, 0x222200002222], 5, 0x2020000022a), (0xff00ff0000ff00ff, [0xff00ff, 0xff00000000ff, 0xf000f00000f000f, 0x3300330000330033, 0x5500550000550055], 10, 0x10017000057007f), (0xcccccccc33333333, [0x33333333, 0xcccc00003333, 0xcc00cc00330033, 0xc0c0c0c03030303, 0x4444444411111111], 10, 0x4044401131333), (0xc0c0c0c0c0c0c0c0, [0xc0c0c0c0, 0xc0c00000c0c0, 0xc000c000c000c0, 0x4040404040404040], 5, 0x4000404040), (0xcccc0000cccc, [0xcccc, 0xcc000000cc, 0xc0c00000c0c, 0x444400004444], 6, 0x4440000444c), (0x3300330033003300, [0x33003300, 0x330000003300, 0x300030003000300, 0x1100110011001100], 4, 0x100130001001300), (0xf000f000f000f0, [0xf000f0, 0xf0000000f0, 0x30003000300030, 0x50005000500050], 6, 0x10005000500070), (0xff000000ff0000, [0xff0000, 0xf0000000f0000, 0x33000000330000, 0x55000000550000], 5, 0x17000000570000), (0xf0f0f0f000000000, [0xf0f000000000, 0xf000f000000000, 0x3030303000000000, 0x5050505000000000], 5, 0x10105000000000), (0xffff, [0xff, 0xf0f, 0x3333, 0x5555], 5, 0x577f), (0xffff00000000, [0xff00000000, 0xf0f00000000, 0x333300000000, 0x555500000000], 5, 0x175700000000), (0x3030303030303030, [0x30303030, 0x303000003030, 0x30003000300030, 0x1010101010101010], 5, 0x10101000101030), (0x3333333300000000, [0x333300000000, 0x33003300000000, 0x303030300000000, 0x1111111100000000], 5, 0x113131300000000), (0xf000f000f000f00, [0xf000f00, 0xf0000000f00, 0x300030003000300, 0x500050005000500], 4, 0x100070001000700), (0xcccccccc00000000, [0xcccc00000000, 0xcc00cc00000000, 0xc0c0c0c00000000, 0x4444444400000000], 5, 0x4044400000000), (0xf0f0f0f00000000, [0xf0f00000000, 0xf000f00000000, 0x303030300000000, 0x505050500000000], 5, 0x107070700000000), (0xff000000ff00, [0xff00, 0xf0000000f00, 0x330000003300, 0x550000005500], 5, 0x170000005700), (0xff00ff, [0xff, 0xf000f, 0x330033, 0x550055], 5, 0x57007f), (0xcccccccc, [0xcccc, 0xcc00cc, 0xc0c0c0c, 0x44444444], 5, 0x44444c), (0xf0f0f0f0, [0xf0f0, 0xf000f0, 0x30303030, 0x50505050], 5, 0x505070), (0xffff0000, [0xff0000, 0xf0f0000, 0x33330000, 0x55550000], 5, 0x1570000), (0x3333000033330000, [0x33330000, 0x33000000330000, 0x303000003030000, 0x1111000011110000], 4, 0x113000001130000), (0xf0f00000f0f0000, [0xf0f0000, 0xf0000000f0000, 0x303000003030000, 0x505000005050000], 4, 0x107000001070000), (0xff00ff00000000, [0xff00000000, 0xf000f00000000, 0x33003300000000, 0x55005500000000], 5, 0x17005700000000), (0xff00ff00, [0xff00, 0xf000f00, 0x33003300, 0x55005500], 5, 0x1005700)]
theorem cert_sub : ∀ b ∈ cert_bounds, cert_mask &&& b.1 = b.1 := by
  have hall : cert_bounds.all (fun b => Nat.beq (Nat.land cert_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem cert_goals : ∀ b ∈ cert_bounds, canon b.1 cert_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : cert_bounds.all (fun b => Nat.beq (canonF b.1 cert_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def cert_forest : Nat → Nat × Nat := unpackForestRelative (unpackPagedWidths [
    (17, 0x19a58ad1c18a81b43091f828df80dc0b7c61a5835c1668e0c600a2a02df126860b7c411f8ed7c18d82b5b11ab82d7018c80b5306380e8dc56c01c7c09b802d20129e08367833031a09ade0c581eb1831a054de0c580d2f8318014ae98460532211bc1488746305221916c14d854570ab20291078a6093405a1881b828c40c5a0423020f81026003f),
    (18, 0x2193ec6f02113dc6302113cc5b021b3bc57055900844e914c1474021106c5b059e0086c1515c1d64051d008440d14c234b06d1c0c5402d0c0864c8dbc1474021d03e7f051900864099cc156f0358c0844b4d3c1578021d03e7f055a00864099cc156f0358c085ca0d1c083406d0c0834028fe596e021500a5f90518124402110345304d90083402d0c126e02919f93e),
    (19, 0x16a4069bc092f80a570d08c029902a3780a44088c6029101a2d80a6c048ae05590052200c530107d5c06cb63596453016a80358ca5b580c8c018a64cd9c063200e7b2369e02d90073d90343038a604d3c05a18e26a0747e02d30151d822370147802d10051980944078a60251015a78125f014a6024d005a18626205ad608dac0db38135f016a60c92804a201c6b012880314c051940017),
    (18, 0xa315c085c0559008449b14c147402110745b059e0086c1715c085c07590147402110345308d2c1b47031500b4302191e36f051d008740f9fc1464021902673055bc0d6302111934f055e008740f9fc1568021902673055bc0d630217143470cd2c2b47031501b43048fc0a37421b80b7c14d2c0d7010d1c145402df02b4302df01a3f031c00a372a1983d6f0d58c2b52),
    (20, 0x9441bb4f013640096401e7b00d6b0093418b4300b6402b4300b6401a3f00a6400a331516e01b430123f00a331316600c5804d6b00a5c03a6b00c7002a6700c5801a5f00a5c00a530d94600a4401c6b00a4400c530b13e031440084c01a3700925008360084404c530194400b5f0084402b4f012440084400c530083e030620085401b5f008560083e0084a8381f008642bc6f008442ac630084429c5b0086c),
    (20, 0x134900b4804453025620156000a3400c6a01b4b00d6e00b430084c102370635200c580515f00c600415701a5f00b6c00a570213d0146200b500092709846009440845b0096c07457015640094405c530094404b4f0095c03b4702c5b024570156400b4800c5300a360082eaa0530094425c6b0094424c53013540095401d6300c530093421b6b0148c0094401c5300b430097c1eb67014640096401e7b00d6b),
    (20, 0x1b4f0095c00b470082edd85b0084432c5b0086c31c570085c01d6400937008442f45300c6403b6f02b5f0235700b540125f00a37008442aa4f015680086407b6f0084e00d70063670545b04c530145900c580325f0146100c6001a5700d6a00a4f0085c21a4701458008541056b0103600834014700087c0dd670103600834014600086c0267401c5800b4a008540956300b4907c5b00b6106c5700b5101d64),
    (20, 0xa6600924009660714700c6805d6f00c700157600c5803d6b0147200c700256700c580156300b6a00946f71231945b18c5700d6417c5300c6400b6f1624f00d680236f0084e00d7000b671324700c5804d6b0083600c70035670083600c600167400c5800d630da3700b5400a5f0213f00b4800c53009270a16e00c580295f00c600195700b500092706846009440545b0096c04457015640094402c5300944),
    (17, 0x632095c828f00c6805bf1f14c48b61c53062902d38a6d43a4f192582d40448e126c05260290c14c00b66bd1a0759428f00c68acbf275f41d188d6f0ac603160eac66c70323003588a8b4446d06be0d17c28f80b480e2983148169409245cbb031c09cec083606380d5d816a824720e340516016f4616e2a3d1318086f40d7019bb08da834d40c60),
    (19, 0x2b10035e006474056304ad60758c06b100c5e7b8f4f51d8263504469078d00d19815b502366024b00295004b320d6f028b203160fab585c710126c131c01d268324901298089140d20809400124c029c0cab381d7e028b203160bab196c6e016cc571acaa350146c014c04f19805b312c63248c4119f81f390357a05ae4051e006340137e016e43716c06b10cc5a188ac119f806320357a),
    (19, 0x30cc02920042f00844cd29e025901eb78095405ad6025f00eb38095401ac78852826bd0457907af00d5d8163d02476026d002d9004bb5667f02ad2035a2a73d81d810128c03602973b81e8e02ad2035a28739809649fafc031da76bdce57a02af8025f266bb00c7697ae72d5c823c703f8206d140ba080ac400d780291c0320a36b580e728bad4025b226b30478e01ae80da2806ba02682),
    (18, 0x32321e7709a381d640519008647d9cded76791f9dc7675198246607190136602d90fd6f02d50ed6b0adf01a39048d4092e029c0bd67095f81c5404d5008542558c2a4f0892c1a47029b00a43029805c6614db8324f0a92c2247049b008240290c0a6004d980b562c8d0146402dd0997e091f01b6c04d58087c1c5d80c7c071d8137e02d90496e0f5ac0c5b0a4900a60),
    (20, 0x9240d96e0ab710158000b8c0934b00d800834700c700145400b8c06343052610147000a7c03a3b00c7002a3700b600134400a7c00a33009240287e01b4300a33009240087c9a9670137c00b5605b4b00d7004b470146000b4e02c540237c01b6c00a600083400b4393966009440545b0096c044570095c0256400b4d00c540094401453009448d9620357602d740247601c7400c640097623e7f00c6422e7b),
    (17, 0xe3e839c018ab6b5f05b20b5f446f80d7009ab020d266a62d7e12b906df826f80b5681a58f5f818d82d7912b9075c4128c0d7061a3831f158fca47c22370317068d22c6212308251828c00b4e2e2a14df822bc085e1dbe028e01adc236c09310298010680b43b11a02e30f6960d8035a3831c028a80b8c25a18e8ec18e02a3705b004d1014f80a33),
    (19, 0x3b1a03e0006b2ccc6f018e80ba34124600e80028cc021124a318368e0131809a080e470148c018cd1716c234700d7c06d120ba0813408095602d00025ba0a2b80d8c15b1c2963022bf00d6c06af20b5c812b881d70028bc025782eb20548e01af8045b804370348c01cfc091f009b900b7001088d714c06b20147d018aa76dbce9b681464016c8095f40eb880c70016ac66d8c16be00d64),
    (20, 0xe46500c660d45b016790096e0bc5701d690145e0095e00d64094530224f01a4b0124700a4300a6005b5500b5604b4b015690095e0334701c590134e0094e00c5400b4300a34fa96f00b6403b4b00d6802b4701c540137400b6400b43f616e01466009440445b0096c0345700c5e01d64011440084400c53f096a00e740158d00d655447f53c7d0157400c7402e8d0268100d80014660098c4fc7302e8c00e74),
    (21, 0x36b7802d500bad60147c005be01159c038a8013540042a00958c036dc01356005310628fc014c80556f0052a0115ac014f8035670052a00958c034dc00c620052b04a8ec018d00556f0062c0115ac018e0035670062c00958c038c400d6a0062d0328dc028c800a64056b780295013ad600a7c046b38069500129800854036b1818db8018ca0526e00635010958048be01c5b00a2b80314c0324800c5b004120028cc0125b09234),
    (18, 0x91900c58051500b6408d0c0a5c028cc0854ec97c0a442516c0a6c2115c0a5c095901a44024f008441514c0b5210918234b06d1c0c5402d0c192402d0c0824c496c536d02df0434b035c03347091501b7c04db0083402d0eba5702910ac5b029b09c57075900c54029107c530cd2c2b47071500b44028d00b4310d900b5a0c918234b06d1c0c5402d0c09248094c0b64),
    (19, 0xbf68e0253c6e2a0d36e014c030d985c9a8a25b0e48a1a8f405220592a0327204078040903928012500a0a8040c01826014b402090152981b6a024dc029980417811340106944d0c162d82457038aa0496c052bcdb5f016ad32d6c0e368126c014c12ad5c0db7013560106922d4c09b700b568e6960497c0529c5b470369c0493c052181c54026dc020d211a186b55016c816d2c06b404b47),
    (19, 0x24c0025b7f5ab80b5434ad606df0051c80a7030ace0ed7c051c02b5b012d806d5c049a00b530a6d81093c1d258135c012b80891c09220092401486029807a330eb6e1c6ac364d405248b45b024c2025804e2b8413f0727602900149b8093c03266044bc049180950096ac0258006330324b012c00719805ab0092801486064d0062d80834c76a608db80db3013560126b84d2c08af8095d),
    (17, 0x2d279492c38f8147004ae0c91c44f80d6c0936024901487ba62052ce717f26bc136e04a2de93c48dc1b5d092b02496a496956945b7035a0f6bc72490ab402970b2bc515d052f1057072a41568042e0817826b8095c04292e91c88dc0a5c19aa8a9b0447c192505af02490e4862b5e11ad06d5826a40a5620978cd6854bc225a0d2b04948125c0927),
    (21, 0x9b5802d8c01289c745b014b78085b402ace00856004b671115c012c80b47e004be0291d81328a0836b025aa810d34014700313a0141d0020a00306c00b6a0041a00cd8c048f400b78009bf002dd80107e01144004226e114c0128a0445b004be80d15c058aa014590062a80455c012aaaa35f026b78111b80349e0092400521802980036cc013560049aa94d6c4c8de25c6d004a209318c488be23b5e03e368025100d8c200d7c),
    (21, 0x4aa02d5cc15ade0095404e370051f4014f80827e016be80255003ae20137c005b80149c8028fa00c7101cbf00c5f4018be0217c00abe8035c4012e5dd467006320419ec029180098c0773b802550088de0094401a358025f0048ce0094400a318025b8018f8095760463f0025b00f8cc07145005ac8135ac026e200b7001ab380b19801aec01b5b006bb002d4c0328800d6b0042273118c012c80447e004be00d1d8058cc02145),
    (22, 0x1b5ac014720029f8055670045600085800f58c00c540055ac00d6700718800c6e0031480a34a008d6c013660028d000b4301e0f001c5b00515c00c55014d7c013560020d003b53004db800b56008d2c0136e0020d000b430020c2ef1270025540856b002634075670025f0065650165a8015690035940416700e5980316500917c01c5300417800852002591ef46f0119fc0096400d5f802c760025b001c66004514009447ab1ac0d57f0025900c57d),
    (17, 0x2a3782d2088d60b701a3382d2048c61469063082d88a8f8425f1d2d831b054ae1b64052a0295014a60b7046bb02da0f8fc0b603633055ac1ace53480eb582dc01ace31481424075ac18b60a3004227918c16d02c7e05b8071d828cc0b48d62d82d2338a63c610e3e0519814881c5b05220314eb6d434690a3a0291038b60a440629c8d88fade0d76),
    (18, 0x1696c158c036004257029702b64029501a8c039f00a7c0294d6b72029a5556f531b80c7e4e97c2d7e08db40a5504db00a664296c5679131f80e780f1b832590a5880e78061b80c6c02188b257295f80a6c24d946d69191b85c5e14978104e021083a5c02970295202570185e02970085208d901a7c048f809280294c0b70d319c0c64579ec1c8c029240b804f9dc0b58),
    (22, 0x35ac0084403718c0094403316c00b64002d2c0b16e002df000b4b02659803d6f0035d802d6b0051c800b7200559c00d6301651800c660111ac01c7e0051980084400918c0147e00319800c5b0024bb5112b00d5ac02d67002dc001d65004da800b6817b1bc06e7f0195f800a6800897c00a5c002d9000a53002dc002c76002d8001c660031b800b4815f1ac22d7f002da021d7d004d60009580815cc1fd6f07d1b80857d01f5c400e8c01a97c00b6c),
    (18, 0xbb1bc3e7f0d5f8097c091d8096c051980944ab1acf57f04590092e375f40954335ccc56f2f1b8757d1b5c40e8c16d7c158c0360043570d5f40b58095c4147c031c00a56024d84372035bc3370051f40c71065f80c5f025f1b46703190ce7b07230138002630ae7702550446f02510346b025f02467025101463025b80c7c155d80964111f8096c0d198156b0359c1944),
    (22, 0x71f00146c00211003a4f00c92c00d7000891c0127c0029b000a430585980546a0035a00426f0029b00326b0035c0022670049b000a3e00298c10956002d980856f01f5ac00c7c01b59c0157e0021500556300d1b400d7c00917c0147c00211000c53006d9800d6a002d580793e0035940636f002d980536b0035f404367002d980336300ad7c00b77006d6c00b4e002d4c0092ee124cc0092e0115ac0092e00d59c0117c0024b801d6500459800964),
    (18, 0xecd8c09640b5f8097c075d81154021537b5f16dfc096412df809340ede83377025f02376024d01372024d31b5b025b30b57329bc0c7c231f8847c1e9b81c7c04df00a7c165f8157c02dc04172021f0307e0a1f01c7c049f0097c021c8326708de81b72029800a760209c09348cd4c1d6e049bc0a6313194147403190324f0a92c0d680691c0a640290dc96e035b45c5d),
    (17, 0x4b67ed981269eb4ef1a682990e6de0c7c31b5829f0a6ce0a6c063a0ed8c14d22a6e0e370496414a20a66b09b029569ad6147c053ecd59e56d5236609bd02dda14be347a163b08db414aa136c05333496ca8dc4c6c21bd035c066ec0b6c11b7031b026c40a593d2b82910c8f40a7c2a3b029b086ca2c5e11a90294024bc0a5c09b2028f814a60934),
    (19, 0x12ce602590423f01164010c81adbc31b38096c0a6cc029a0112f80a5c016c80294c049a01b4e0226c024d391b589d7d01d18235bc16c600c7d032a8031c0042a05d63038de02510063183c7c048be051f0042200c53022f8021f341b380b6458cf60763009c60098c54cee025502a3780944088d6025f01a3380944048c604db405b28096e016f88f1d919b78257e03af8045f804be20b67),
    (20, 0xc8c0d37f02d8c00d8c0193600c7c009340a37300a630093408b710237c01a7d0092400a710627e0247c011360093400b7103a720127d00a710217e0126f00a630097c8dd67009640436f009340336b0097c0236700934013630096e00d7c07676009640657e05b590456600e760324b00d7001e760156800b5c00a470115400854815630357b0148c0098c01d7701565009647db6f0b67f00a560116400864),
    (23, 0x36e2004d7c005ad8149670018f800493c005258129660012a8004d7c005ad810962007cfe00d9ec0173b8026730036fc004dd8005b300c93f0014c80115bc0052a00356b0014f800959c00abf000a54001ac601e4f80063c00667f0018d00159ec00a40000b80007cee0051a0005b40026730038f40051c80063500093785327600edac0049a002b690012f8006d9c008b3000964142ade0025900173f00097c003aec004d64004aa09dd6b0012a803d5b80763f00e47c),
    (18, 0x2590336f0ad9c2366064e81136024d32b6b115f40e8c0d5bc0d8c0958c145f0314c097cb8d9c0b644d9ec0b8c499dc0954111bc09440d1ac097c0919c09440518c096e02df0cc7630dbc1d72045f8097c28d9c9b6624d341b6e025b00b661c8e81462025b80a66148d80b66104e81a6e031880a66084d8156b0359c093468d8c1576025518b5f044dc09345cd6c257d),
    (23, 0x18f804299c005b600fa6600dad600252002eb1800d620098bc0109b801a2c802c510046dc006db000628000b4e0014cc02295400eb5800970001ace01a95000937000a6600a48a00b5ac004b8001d670028be00315c01122000a4400247c0028f405d31800c7c0026ec002d5004d2f803d6f006ad60025c0012b380157e0010a800358c02d1c8009490088b600257c018ad800a600042ae0051980052400094f00106918c4fc00ebd8015650012c80dedbc0273f80447e),
    (23, 0x326e0044b800496c9e1530756cc0075ec00ab2800b640714de01b9fc031bf001c640016b800219002137803a670016d800a99801122801a440014880028f818d3580bd7d001d1802b5bc006c6009d630038de0031b000631807b7c004ade005150005aa000d6300a2e00121f001eb78014540016a800958c00a2f800c530010680021c012d33800a64032cf6002a300c33b800a540088de00291001a35800a7c0048ce00291000a31800a6e0014f804add80913780147e),
    (17, 0x151d888dc14780b440519851c014e27567093302970b4d64d7d1daf831b056b6235705ae0319016a60c700533dc51916ac1466052a1c578cad65d6a2ab1835a886bc0d6219a90318444cc156a06b10297812ace13f0a330291048d6157d053e0319d527c8c5a3eb59d5a826900a482eb18558414bc436a0ab50358856a4156a06b10494814a00956),
    (19, 0x836d6051f404be40367016de1c97c352d86257028de0318c25298126f014c60c57c14ad82157026de02d8c04a98096c6f4cc0b19811a48136401472025b9a4a780b491ead63b5a805a48dd63028a802d20073d0bb5f03cf4059c8049b09b53126a2071a0092c80a410e2dc1918c2e308536e096c4055c006b40324f03ae005580053e01243014820259924a381458014b2315ac1d1f80b4c),
    (23, 0x86ac0071980092a0008440042bc0055a80053300095600c27e00559400532000c6f00827c00b16800eb500136a0014a00025580089b80092e9eb2b6040db401ebe00347d001ce000915400abe800a7c0014b2030d7c00dbe000d7d001472028d4c00ab2800a640048de00519800522000c6300d4c2006df400636800b550094be0101b00062a802b5f0016ac006d4c005aa800a5f0010c139455c004b6001c660026920025102263580097c0878ce002570009ab000934),
    (23, 0x10dac00524800c5b0056aa00519800522000c6b0014b343c57c0ca37800c650306de05e9b802233003b490026c80028e4010b7000a480010bc002110098a7804d6a0086a20091a000d2c800a540014820065b80052080096601c28e0051a00053480256f002aca0031a00053780a946)] 6) 11
def cert_links : Nat → Nat → Option Nat := unpackLinksPaged (unpackPaged [
    0x52020a4001460828c00518009b2013600268104c820970812e00258104b00094081260824420480208f0411c0823410468008c041160821c4043020850410a002140042800820c0fe181d4a03a80074040e8001cc103980072040e4001c4103880070040d6281ac00350206a000d2081a4003402068000cc101980032820620c0c400184103002060000c00017820299603d58003e00001,
    0x8e8a11b0822c2845410880a10f04212304144081060fa201f4003e8007b860f7001ee003cc4079020f2001e4003b84077000ed041da003b01074080e11c1c200384006f060de001bc0036c306d800db001ae2033c8067800cf00198183300066000c90c192003240063840c118182002fc205f800be04174202e4105a880b014160002bc1056060ac00158002a82054820a90014a202940,
    0xcb821970032e0064460c880190043200063c10c78018e0431c0063020c60018c003141060880b82416c102ce2859c00b3021630c2c60058810af8615f002bc0856840ad00159042aa2055400aa80155002a02853c10a70214d042980853000a58214a0428c2051410a280144042880051000a10414104278284f0009e0013c00278004f0009b8a1370026c084d8009a821320c248704882,
    0xfc821f4143e6087ac80f5801eb003d0187a000f3821e3103c60078420f0801e1003b63076c00ed021da003b20875440e70e1ce0039c0072c30e5801cb003901872000e4001c6083803070000e0001bd0c37a006f400dd061ba00374006e020d90c1b200362086c400d8021b000360006a080d4001a70434e0069420d2801a5003461068c00d1021a2003420866480cc8019900330086600,
    0x1358e26b004d6009a0313400267044c428984112f8425f004bc08978012e82257184ae0095c012b80252144a400944112880250044a00093c11278024e0449c0093411230e2460048a089140122022410c48008900011f0423e0047a088ec211c0623800470008dc111a842350046a008cc21190222e1045c008b021160022b0445018859210a0420f1441a1082051038220214400107e86,
    0x17d002f5145e808bd0017a002f2085e010bc00177822e7205bc48b74116e802db085b600b64216c802d9005b008b58216b002d6005a810b308166002ca0859400b1c3163022c50458220b040160022c00057e08afc015f022be0057c00af0215c082ae2853698a64214a0a2901051040a200144002850c50a00a1011400828000500009f4313e8027c044f0209e0013c002750c4ea009c83,
    0x1c9803920471440dd941ba82371106de10da851b482365106c808d7c51ab12355046a028d3c11a78034f0069c08d3801a40c3411c67e10cf8119d0833a0067010cd4319a023340066800cd00199043320066400cc021980032f0465428c945192803250064028c7c118f0231b0c63408c50618a003140062410c4801868a30a0c61400c20218010300005fc10bf4117d842fb005f408be80,
    0x2150c4222081aa903402058440b008140902802040440800810010182203004050480a0100051efc23dc0c7b020f5431e80a3cf0479a10f1c61e3803c60478c00f1411e2023c01078000efc11df023bc0877410ee801dc823b80476e08ed031d5923ab0075408ea411d4803a80474e08e8461d0803a00474000e7c11cf8039e0473228e6401cc023980072c10e5801cb003940872800e4c1,
    0x24402488009100121822408a4810090009200023f8247b108f6011ec023d8047a048f4011e8023c04474108e411181223000460008c001174322e0245b048b211160122b82453108a60114c022902450088a00114002278244f0089e0113032260044b0488e2110072200043f0487e010f8121e8243d00878090f0021e0043c0086c310d4121a8043404866090c422188043100862010c01,
    0x274824e60c9c03137c126e844dc049b4113506269044d2009a4013480268824d00499e0933c0267804cd08984593080261004bf0c97e012fc025e844bd0097a012f4025e024bb04976012e8125a8a4b01495e092bc0257024a818950012982251864a2049440128802500449f049362126c024d8049b0093211264024c804990092e1125812478e48e049181123002460048c00912192240,
    0x2c10058104afa215bce2b78056e04adc015b412b68056b08ad6015a812b30856504ac80958c12b08455f08aba1157012ad825580ca986152c12a50254610a8a0951012a00853a18a70114dc129a8452e1ca5c014b022948652510a422148012900051d0ca361145852890851104a200943432860250b04a140941c3282844fd209f6113d8527b004f4089e6093c81277084ed049d6113a81,
    0x2ec8a5d804bae0975812ea825d014b9a1972442e2885c110b820170402e0805c100b78296f002dd045ba00b74016e412dc025b50cb64196c802d9005b200b64016b842d7005ae00b5c016b802d6825a910b50096a002d4005a800b50016a002d4005a608b442168412d08059824b300166002ca8659500b2a0165402ca8058f18b1e0163812c70058e00b0a4961012c20058304b06016081,
    0x32d0a65808cae0995813298665108c9c1993413258464a04c8e1991813230064600c881190c13208464100c8009900031f0463818c62398c013180062f04c562184993090061200c201183c13068460d00c1a0182c23058060b00c160182813030860210c04018041300025fe08bfc017f022fe005fb04bf4097e022fc005f218be0117bc12f7025ed04bda017b012f28e5e404bc0217782,
    0x371006e104dba21b74036e026db04db601b68136d006d514daa01b501369826d300da409b288364046c704d8a11b083360826c004d7a19ad0935a006b208d6401ac41358806b004d5c11ab80357006ac08d5801a8c9350846a100d4201a78334f0069d04d3809a70034e0069a08d1a699dd633b8067508ce6119c033378266d08cd8099a433348066804ccc1199803328266500cc61197c4,
    0x3c30278408efe29df813be0477a08ef209ddc23bb0277018ede09dbc03b6067690cece11d9423ae127590ceae11d5033a80874e08e9811d2043a38273c2ce7609ce0339b8273508e6809cc823978672d08e5419ca413948071e2ce3619c6c038c8471804e2821c4c13888471004e1e09c30337f1c6fe00df811be8237a0c6f010de001bc00377046eb0cdd601ba423720a6e304dc601b881,
    0x40f8281b110321205c24071280d050180a02c14020e800110000200004000080000ff821fec13fd807f80cfee09fd813f78e7ef00fde01fbc03f48c7e60cfb851f34f3e6807cc04f9801f2823e5007ca00f9401f1c33e1887c300f8601f0423e0807be0cf7c01ef413de807bd00f7419ed843da827b20cf5e19ea073d08e7a004f3e09e7033cc0879704f2819e4c13c60e78a08f1209e1c2,
    0x44c008970512e0225c044a848950112a02254044906892011240224804458e88b011140a228044482889011100a2200443048860110c02214143f8c87f010fc0a1f8043e0487c010f60a1ec043d0287a010f4021e414398c873010e6021c034380086c110d8021a4343480869010d00a194343280865010c80a190043182863010c60218c04318085f110be02178142a9283d61048ca0804,
    0x484009070520e02408548100901052000a3dc947b808f5091e80a3c43478808ef091de023bc0477028e71d1ce023981473008e5051ca023901470088e0011be0a35c846b808d7011aa123540469068d1051a2023440468808cc1518a3a3140460888c10117a222e8345c828b709166222cc0459028b105162022c01457048aa11154022a41454808a8051500229c14518889929132022601,
    0x4c7889881d30c1261804c282985013041a60414c002980012f8225f004be0097c012f0225e004bb82977012ea125d404ba0296b252d6025ac04b5809680d2c62a58424ab16956012ac0255414aa80955012965252c04a30a9450528a02514049e9093d012780a4e824998e93301266024b464960292b052405a4800490009200122e4a458148a0490d1d2180a43004858290a05210124200,
    0x50a82a024d404027fc34ff809ff013fa127e834fd009fa013f20a7e404fc029f8013ee0a7cc44f9029f1053e2027c404f7069ee013dc027ac34f30a9e30d3c01a77434ee809dd013b80a77004ee009da093b40276804ed009d9053b20276014ec009d8013a04273434e6809cc053960a72c04e4849c9013900a71824e08a9c10137a226c4c4d8029b00135a1a6b404d30e9a0193400264cd,
    0x54e82a9d0153a02a70154c08a980153002a5c154b02a92115163aa2c054502a861150c02a18053e92a7d014f80a9ec153d80a6f314d81a9ac153580a680d4d0029a0053400a64114c802990053104a61054c202984052f84a5f014be02974252526a490549202920152304a460148c02918052204a392d472028e4051c80a39014700a8bc951780a2f0145e028bc051780a2f0144c4a8590,
    0x5ae80b5b0969e62d1c85a302b460168c02d08459728b2e0165422ca8059386b260564422c84158f84b1f0163a12c70158e00b181162e0ac54258594b090961202c1c258302b02115f832be045749eae8055c822b90056f0cadb0d5b40ab64156a88ad5015888ab0c156102ac20158402b04155e88abc055760aaec055798aae0555a0aaac255484aa70954c0aa8c355180aa00d54002a782,
    0x5f88cbee0d7dc02fb025f600bec017d21afa405f480be8057d002f9c15f188be3017c602f8425f002be0017bc12f7805ee82bda0d780d2efc15dd88bba0577402ed845db00bb40976802ec825d882baf0975c0aeb025d600ba6197461ae7855cf00b981972e0ae5815ca04b930572602e4035c686b8c0571412e2415c384b81197000adf045b71cb6e016d61adac05b484b5e2d6ba0ad740,
    0x65300ca6019461b28c065180ca00d9400327c164f80c9d0993a03270164b0cc960192c03258064a04c910d92203244064880c8d1191a03234064584c8b0191603224264480c890190c1b1f8862fbec5d098b22316016290cc520189a2b130162504c470d88233100161f82c3f0187e030fc061f80c3919846b3084261080c1e0d8361b06c060c84c180582c1301905ff8ebff017f81afdc5,
    0x69d02d370da6e034d4269a80d320da64034c8069804d2a19a520b4a0169382d240da460b48c069084d1e0da322b458368b00d1409a2803444368880d1101a1a23434068680d0c05a121b420168304d0601a0a0b4083678a2cf1019da233b4067506ce6119c813368a66b08cc34d9860330c066180cc3019801b300065d8acb51996a032d4065a80cb3099640b2bc36548cca805950032982,
    0x6f482de805bc62b78c06f006de001bbc1377416ed84dd615b9c4373416e584dc615b8a0b6fc66df02dbc09b78036e826dc82db121b5a236ac26d502da611b4a0b68c26d102d9f0db3c0b66c36c69cd8b09b140b62026c400d8801b100361046c200d8401b041360806c082d8101b000b60006bf82d7529ae80b5cc16b980d6a25ac24b54ce6a884d4a1da920b52016a208d3d1da7a034ec2,
    0x74c84e9025d2003a24774480e8805d0823a10074104e7e11cfa0b9f4073e02e7c01cf8039e8273d00e7611cec039d0273a00e7401ce8039c0473800e7001cda1b984c7252ee4809c8c13918072186e4301c82138c1171704e2b0dc540b8a0271400e2705c4a13880570e86e1d01c361386c070c06e0c31c1413828070404e0801c0e0b80466ff06dfc09bf0237cc56f902dee11bda0b7a83,
    0x77e82efc05df803be8277d00ef809dec13bb0a77504eea01dd403ba0277400ee411dc21bb84076f06edc09db803b6c176d02ed905dac1bb54176a80ed309da603b4c076884ece0dd922bb24076384ec701d8e03b14276280ec309d648bac8075786eaf01d5e03abc075588eab01d540baa8075482ea901d500baa0075382ea701d442ba84175080e9f09d3e03a74274e80e9d01d3613a6c0,
    0x7b480f6901ecc1bd9417b280f6405ec803d9007b104f5d15eba03d7407ae02f5c01eb413d6807ac04f5801eb003d5437a80af5001e9c13d3807a700f4c09e9803d2c17a406f4801e9003d1c17a380f4701e8a13d0837a100f4105e7633cec079d02f3a01e720bce4079c02f3801e6e0bcdc079b80f3509e6a03cd0179418f115de2203c40178800f0f05e1e03c3c078684f0d01e1a03bf8f,
    0x7ed00fd809fb003f5827ea04fd305f944bf2417e480fc805f9003f1c17e302fc601f8a0bf1407e202fc401f725bee407d812fae09f5c03ea457d480fa805f5003ea007d400fa315f4603e8c07d084fa101f3e13e7c07cf80f9f01f3e03e6857c61cf8c01f160be2c07c502f870df042bde497bc80f7901ef203dd837bb00f7601ee813dcc17b980f7109ee203dbc27b50af6a01ed20bda40,
    0x8250504a020901411c1823810440e0860c0fc481f8103c0e078040ec181c070380206c140d8081b01036020622c0a878150102906052040a40813850231203e2407c080f8101a1603404068080c830190202e1405c08080f00d0e01a0403408068100c060180402c1805810090a01203ff8b7ff00ffd05ffa03ff017fe00ffb05ff603fe817fd00ff905ff203fd447fa80ff015fd043f68e,
    0x85b010b40a168042d00859050b202164042c02857830ae0615c042b41856030a81214e0c29c085285095421261424818470908c0a118042243844810860e1003420008400107f060fa141f4083e8107d020f6141dc483b8106a360d4041a0283383067020ce0418c4831810610a0c20418018300105e0a0bc04174182e8105d020b614158582a05053060a40c144182881051020982c1300,
    0x8908911f0a23e04474288e8111a0e2263c44c0889031100a2200444008880110f062181c43008860110c02214144202884011080220c14418088301102121de9c3bc0877030ee021da0c3b40876030ec021d60c3ac08730b0e40a1c8043882870830df0a1be04378186f010dd061ba04374086d070d5161a41c3249864030c802190043143862030c306176442e8185d010b906172042d83,
    0x8d2811a40633c3467808ce8319a0e32c2465808ca831930a31e2463c08c78118f0231e0463c08c78118f023103c62008c3051860230a0c61408c107182023040460028be0917c022f60c5ec08bd0317a022f4045e028bc01178022ec145d808bb01175062dc3c551a8aa01154022a41454808a80514f0629a144f8f89f0113c0a278044ec189d031380a25a5c4b40896031281224a1c4940,
    0x9160522c024560c8ac09158122b0242ea4854290a812130a426048403908012100241c1480cb901812010a402047f838ff011fd063fa047f018fe011fb063f6047e818fd011f5163e80c7c438f7851ee063da0c79878f2051e4023c80479008f1831e10a3c20478408ef851de063bc0477418ee811dd023b80c76828ed011da023b01470968e1011c20236e5c6dc08db811a54a34a046940,
    0x95a092b4025660cac81959012af0e55c0cab02956012ac025560caac0955812ab025540ca9459500b2a00254004a78294d8729b0253604a64294c81299025300ca60094c012941252804a4829490128146502049fc293d8926e364da0c9b409368126b0a4d6049ac093485265124ca04990193201263064c604988193101262024c01496c591ebd23c064760c8ec09181722f0645c0c8b80,
    0x9ad1934e3265914ca04993833260664814c68a98c833180663004c60098b833140e62804c500989833130262214c440988032fe4a5fc04bf8097d092f9065e43cbc80979012ef0e5d624bac0975812eb025d01cb982973012e5065ca04b940970892e1025c204b7c296d892ce3659c04b2c3965812c61658c04b141962812c40658804b0c1961812c20658404af4595e032ba0a5720cae01,
    0x9fa833f5027e80cfcc19f7893ee067d61cfac09f5813e80e7d004f9c19f3033e5067c80cf9009f1833e2067bc24f6c39e8953ce0e79c04f3809e38f3c50a78a04f0c29e1813c10a78204efc29df813be0677c04ef809de053ad3e73a84e7409ce8139a0e73404e6809cb8738d2a71614e2429c4813890271204e0c69c1813830270214e0409c08137f0a6fe04dfc09be0737c026e064d98a,
    0xa73854e3129b44d3680a69114ce12994253280a65014c222984053080a5d114b612964252c80a59014aa22924c5214da41074800a900052000a3c1146d2e8d61518c8a2f0b45c0a8a8451500a2a0144f168942d1202a218b44302876450dc4a1b814370286e050c07a180142e0a858150a82a150142a02850150a00a14014280284a1d0940a082b3fc527f804ff009fc873f8067ee0cfd81,
    0xb018160302c06057fc4aff815ff02bf81d7c0caf8015f002bdc157988af2835e502bca057940af0895d922b9a656968acd9559712b2a156540ac90759202b24056402ac31558212b04056002aba9757502aea055c44ab80357002ad825588aab00556002abc15550aaa78b54f02a981d52c1aa38954702a82354d0da8abf51502a26154481a870950526a02253e09a7c014f60a9e4253a49,
    0xb4d1369a02d320da448b488169102d1e15a1c8b353b66126cc00d95c9b251b64612c88159100b220163d1ec7a058f01b1c0962e2ac54258984b130162602c4c058941b108962102c3c1d848cb090161202c20158400b080160e0ac0c4580c3] 19 6)
  (unpackPaged [
    0x21053c0dd34f0370d2c0d43470310d0c0bd24f026491c0bc23f02608dc08104602000d807846801c1160068468018116005846001d15bc06c56301909bc05c25f015095c04c264011091003c24400b114003426c00801b802c56400a091001c07e00804d001c343005118801045a01255bc04156301211bc04046300e517c03845b00c115c02445300601b800d05600301181f956f07c558c1f846f07c118c1e945f07a116c1e0457075114c19436f05b4d7c14535705b0d3c14434704c05b8125156049051810013e03901b807c066014415805004600200fa7aec5fa1eb16e4f2c579cab14e7ae35fa1e8d6e4f23579ca8d4da8a34f6a2ad2c7ba3475de8d0e878a5f9eb296e728a5793c294e319a4f853692dc27a47709690e318a3f85328edc2723770928ce87815f9eb056e72815793c054e31914f853452dc26947709450e31813f85304edc2613770904cda8892f6a204ad7781271ee048c6ee05f1bb016c552057154014c2ba84f107a12c006847080a10c2ba03f10780ec00603708080cc41c82f0ae20ac200827001208c41c01f0ae006c200017001004c00003f,
    0x4f05f811813e03c01f80c4076076011002403e07411d01a807407301101c467806e11401a407407001b01a006406e15901b447406701d01b00440680d001a045406a4d3c1a834b0690d1c19c343072517c1c845b06f115c1ac4530660190065056019011819047406301d0178044061119018006405d011017856f05d158c13806e04b415818867f05f19cc13417e04a45980ec07e02f01d805d06605c011016857805901d015005c05715a0158064053017015056f053158c16067f05519cc0e807e02601d8055066052017014003400700b813803404f0d0c13524f04d08fc01802e0228d8808647204b916008407604b0150082462003916812825f020019800c02e04405b810c27e048091011c0440450d901100340430d0c11845304209b810525604109180f434003d11500fd34f03f0d2c0f834703c0d0c0ed24f03a491c0ec23f03a08dc0e037c0340d400d85700330d000d046003311500c837c02441180c037c02141580b436802a0d500b446c0290d400a835c02911900b835f02c0d6c0ac3570280d4c09c470023053c09047c0230dc00883480250d8001634a,
    0x10511bc40c463101517c40445b0ff115c3ec4530ea0dbc38135f0d64d5c38034f0d60d1c33c06e0c301982ed0560bb01182bc03e0a44dbc28536308b49a82102320aa0dec29c37709f09e824c27208208c82ac3540aa158c22926a08a09682a048c0a7114c22525a08909282944640a419ec27827a09109c822126a0a20d9028467b09d09e823427208749a827c45309e4d7c27535309e0d3c27434309a092025c23409a0d3025823009708f025834409b08fc26423b09808dc2542330940510248144090097c23c25308e04d024c4530914d7c2353530910d3c23434308b15ac22836b0890d9c22035f0870d4c214144083051021156b08411ac2084530ad55ac2b446b0ac114c2a436b0a60d9c28d35f0a04d4c28c34f0a00d0c27026a08c098821925a0860928204232063493c1652470624d7c16135707f019007505601200f818125f056495c17d36f0554d9c06d06607d011004003e07309bc1c837f03f01f80dc07607b011003803e07009bc1dc45006f0dfc0f807e03501d81e406c00c00f81b836f03d01b80cc06600b00f81b026f05001b811c02e07715901ac37f,
    0xfd11403d437f0d401f832c07610001b02cc03e0f4097c3cc36f0d301b83280660fe01702c803e0f109bc3f45640f00dfc34807e0c801d83010640c001503f00440b000f83e84740ef01d03e40440f40d003dc6780f311403b80740f601b03b40640f401703cc5640f211d03b00740bf41902fc0540f101103b43400ed11503bd34f0ef0d2c3b83470ec0d0c3e145f0f8116c3d44570f0114c3ac0640be41582f80460e911d03a00740e301103984640e501903880440e315bc3885630e719fc3906730d101f83180760bd41983840440df15e03780740d901703705680db019036005c0d915bc3605630dd19fc3686730d001f83100760bc419835c05c0d30d0034c4540d54d3c35434b0d40d1c3483430d1493c3412470d108fc3402370ce0df03305700ca0d003284540c90df031c37c0c511c033534f0cd0d2c32c3470c80d0c31924f0c4491c31823f0c408dc2fc26f0bf0d4830856f0c1158c3003520be09bc2f425f0bc095c2e82640b809102d82440b211402d026c0b215902c42440b955bc2dd5630b911bc2dc4630b5517c2d445b0b3115c2c045310555bc40d563,
    0x149123051818c1480510518343147114c51417c127455849c1461431190508164140051050056b115018843285a14119ec4d017e12f05d849516613f051044807210b41a84f436413c05904e813413a15ac4ec67b13205f84b817612345984e413404520884dc36404320884d436413309904d8343134493c4c924313408fc4c823304220884c034312f493c4b924312f08fc4b823312c11604a825c12811c049845812409704ac56b12909ac49c267125097c48c253109a168104822121091047c24412055ac48046b11e114c44002e11b0130464034119049446823711800d8470144117011043c03e1140d7c4541441130110444244110011043c453116114c44935f1120d3c43803e10c855043005410a015842c35f109855842403e15255ac54846b150114c52836b1440d9c4f935f1384d4c4f834f1380d0c4c416e12d0598489156122051847413e10d018842105a10801281008320e8493c3792470e74d7c37535710601903090560b900f839525f0db495c39136f0da4d9c30506610401102dc03e0f909bc3e037f0d501f833407610201102d403e0fe0d003d826f,
    0x1774d8461434918115806004501830d8460435118015905f136917c0d645fc34917e0d205ec46817b15805e823417c15885e446a17715b861145f184116c60845717d114c5e135b1764d4c5e034b1760d0c65156f19415ac63c567186158c5a106616801585d404c15620f055802c16a049c5c845816e28f45c046016c28f45b436c16e097c5b025716a11885a43501730d485c4a5f16f295c5aca3d171057c5bc15716b04f45a012715b08d8598144162114056823616405b056423611120b858856415708d858414410f20f857c14415d0570564450159159056034815b517c56c45b15a115c55c453165517c59445b163115c58045315e4d7c57135715e0d3c57034715608d843883e1b9517c6e445b1b7115c6c84531a96d7c65db571a92d3c65cb471a9497c65d2571a9093c65c24717408dc43493e10d04b859d056167011855483e15500b850925f13c494c50536f13b4d8c4ad166153051048013e14e09ac52026711c018812082214d0dec51c37713605f84c0176151051047813e11601c811883214f0d5053815414c04d053045314d158c4a5166129055852c134,
    0x1e7093c7842471d608dc73c16e04ca5581321461c841587200461bc20f86f002e195049c6502371ba011059483e16500b86d8340190049c6d445018f08dc6e006c16320f858c02e18b049c6282371b6017058883e16200b846882e1b428dc6d0137187049c45c82e11700786d456418608dc45893e11604b85cd06417301506cc04416020f858002e1ad01906c446416e61d06b186416e01506b004411420b86b43541af0d7c6b83571ac097c69da571ab08dc44c82e1b00dbc699b6711224f85c506616b01506a804415e20f85b586419f013067c4581a815a05b18741a7019067805c1a5013867004c1a415c066d87c19b017066825d1a0116467c45819d118467046019a15a868845b1a1114c67825f19b095c66424f1a60dbc68c36716f419866005c15c20f8658458195015061004c15b20f056c02c18e158063445018c158064c03619200d062c45018a158064447019001f060804c15a20f056802c18e00d863403418c118062c06c180013056483c15900b056084c17e00f056002c1880d285f834818a19d062445816a41d05a806418701505f404c15720f055c02c,
    0x5cc55bd70d56b5a8559d6195635cc11bd70c46b5a8119d61846357c517d5f045b576115d57845340008d0f8c16f3da05b8f3c16a323059cc541663090588aed15f2b245687f11571ef4558aec14f2b205287f01471ef05187b206f1b7819c3fe85f078a15c3fe04f078811c77c2371c620f871802e1eb11407702371c420f871002e1d908dc70c83e1c300b87ac5641d708dc74217e1c120f870402e1d505f87a44641d406387a036f1e56d9c74c17e04da5987350661bf20f87985681e4013878c5701e50dbc7883671cb41986f483e1e0116076c5601da15807780361d915807744701db00d87684601d205f87646741d8116074418e1df55bc77c56b1dc159c75c5631d005f813e96604f85587250661c901587543541d4097c7483481d1114c7423431d3693c74ca3f1d3453c74c13f1d0049c7384581cc11807283501cd297c72ca571cd057c72c1571c9049c71c1441c3114071416c1c315907081441c005106f815c1c6517c71845b1c4115c7044531bf4d7c6f53571bf0d3c6f43471ed517c7b445b1ec115c7a84531e76d7c785b571e72d3c784b471e7497c785257,
    0x23711488e445b238114c8d834e20105588c835023009b08bc24c234093c8cc24b231091c8b824322d09807fc14626c15bc9a456b25d159c96456325811b895846b25511a8948466250118c93c462246116c91045a24311588e84532350da88b036621405987f815622a15948a447822811a087012421b049089468c21a0490864124218049088c58c21e11a0888458217049085812421e158885412421b15f086447c2160d60860348216114887046d21a117c85c4532150d2889857d22415bc88456322011c087c46021d116885012421211c084003620f11c083435421119d883857620c11c882c46820a116082437a202049080412420004908105701ff049080046020255a880546a1ff519880836a20109a87fc26620759e881557a20355d881c47a206118081437a2030dd87f81242a819fca9467b2a119dca7467329b15f8a6457b29815e8a5457629315cca4857228915aca1c56a28515989f056327711e89d847622b08d089c17e21305d882016e1fd05987e05651fb11a07e44701f815d87dc4581f511c87d04701f211607e856f1f615ac7cc5671f1158c7c036a,
    0x28b1238a2848224608d091423421e05d8a2067224408d087417620b05b082814424308d0a1816c24208d090423428315d09fc48c27e115090023423f08d0a0457423e08d08f423423c08d09fc58827e15e08ec2342841e38a0868a2801a089e858a27d12388e823423908d09e456c23808d08dc23427915888d823427b15ac9e856327811788d423420905b881416622c08d080c15623c15b09bc16426e05509bc25826e09509d446a27411a49cc468272119891c46124e11649084512710da89c036621a05d89b416626b11649a8458201459080115426704d898c14c26004d09801402650934990249262091498424125f049897057d26811c499847025e09c07fd15423c11a086016625c15f893446924511a096c45925a116085c17623c118090445024c15a89005622570d9880815625411b094c26023f114092c56a23e158891c36a2510d9892847c2490d1092847824911a08f035c24e19f893467224c15e892c57223911e892037e2470dc8858166245158885416624111908f437c23c0d108fc46423d11e08f046824219f890057a23e15c88e047a23b0df88dc45c,
    0x2c10490afc0662bd0178c0867f30019ecbf86772f919ccbe05762f711f8bd84762f51198b442342ce05f8b241762c405b88211662bc0110ae81642b80550ad817c1f80518ad01542b915bcadc56b2b5159cacc56327508d09d023427308d09f867c27208d09c42342ab05d09c02342aa05909bc12426e0490aac3682aa0d909b41242b115e8ac05792af15e0ab857628a15c4a445692841584ab447a2ac11d89b02342240618aa417626b08d09a82342a715a4a9856826908d081517426808d099c12426608d084816c2044590a8c1462a01a34a905812a2160097423421105b080d16427e15e097023425b08d096823422205d8a8068e29015e4a2057829f15a4a7856825908d088418625808d0a7016427e15c0a0c56025708d0a3c67a28219c8a6847625608d095423422905f081c166228051095023429715f094823429605f0a0456025108d0a3867a28019c8a2847a29411d894023424f08d087c17420c05b888014424e08d093423428d1630a3045424c08d092c23424a08d092423428d1620a3057824808d09f846c24708d0a4478e2901e08a3c68a28e1a089ec58a,
    0x30f1140c4816c3100570c3414430e0d34c3445430f1590c30144313517cc4c45b311115cc2c45330a4550c281442f408d0c101642f308d0bc82342f108d0c1046430815d8c1c57430611d8c144742f008d0c0c1762a00514bbc2343011190bb823420945d0b0c0442ed08d0b2115c2fd1a34bfc48c2e808d0b1d16c1f80510b9c2342e608d0b942342e40490bf468e2fc1590bec4642e308d0be80642dc08d0b1c15e2114558b6c2342cc05d0a701642c60578b4c23429605f0b3c16c20e4558b482342cb05d8a1816c2c50570bd04662f31190bc83662f10d909701352ef0d50b08034263053098c1342ec08e4bac2352ea04b8b9c57d2ed0df0ba42702e715f8b984542e50d50b900542df09b0b8824f2e1092cb802472de090cb742602d709b0b580242da093cb6424b2d8091cb542432d40980bc056f2ee15acba05672e3158cb704662db0db8b4c3662d20d58b040342d01190b3c3742960d90b3447c29c0df0b3036c2cb0d58b2807c2bf00d0b2047c2c759d8b1957e2c711d8b154542c60df8b143642860d50af50542bd00d0b081242c2116cb002602be0920b0c56b,
    0x36f0d2cd9c3473500d0ccfc16e33f057885114621404d8ca406e32501b0d3838c3460490d283503450490d305803490d00d101243430490d284703420490d041243491150d2038c3400490d0c24034511c0d082303430d80d0834434109f0d1923f34608ecd1023734008ccd3534f34d0d2cd2c3473470d0ccfc12433c5178ccc1243320490cc412433c1600cec38c3300490cdc35032f0490ce45803360d00cb812432d0490cdc47032c0490cac1243361150cd438c32a0490cc934e33211c0cc427c32d0900cbc47032c08c0cb436032c0d10cac27c3334d84ccc26133048fccc023b32e08dcca823333d51c4cf437133a4d3cce834b3380d1ccd03433290490c9812432608ccc9c3433250490b2904e2ca00f8f2d57f3ca55f4a555753c255ccef156f3b5558cf2c47f3ca11f4a544753c211ccef046f3b5118ceb945f3ae116ce9445738e114cd3c23433e05f8cf816e2c9457884d1562c9053884c14632801f8c9007c3220df0c8435631d0d40c7c57031b0d00c7446031c0d38c6026031b1150c6837c3190db0c5c0343204d3cc8034b31e0d1cc583433140510c40340,
    0x3270230e3c04438d1590d9834038759c0e2146038c11f4e1947136e1174e2c4553744d38d9434237f51bcde94633640d088711463881190e1c3643845150e1036436d0d50db457038411c0e1857d38515c4dcd45e3830d58ccc07c21b4558e0056437e19c0e0457c37f11f4df445521a4518dec3642194518de057037a15f4de437c3770d5885d15637600d0cc807c33101f0db457037415f8dcc5723720df8dc437c3700d58d1817e34605b8cc007e36d15f0d8c3403620d40db446c3610d40d8035034505f0cbc07c35f0d40d7825035d0d40d1416e3690518db857e36c15e4dac57236a15c4da057035b0d00d1017e34405b8cb807e36611f0d8c45c36211b0d8845c34305b0cb406c3430578d7814636311b8d844693601188d7c46135d1180d7034e34205b8d0815e32c01b8d0417c32b01f0d0416e3590578d6005e35608e0d5456e3530988d4826036555f8d9157c36511f8d9047c35b1150d6837e3570df0d5036c34005f8d0016e32a01f8c9807c35100d0e2946f38951b4949465382518cdf145f375514ce2836f3890db49483653820d8cdf035f3750d4cdbd34f,
    0x2244558dec2343bb11d0de823437908d088d15637808d0ee068037708d0dd81243ba1a34ee448c3b71198dd42342214598ed804437408d0dcc2343b30630cf008c37208d0d3818c33b0230dc423434e05f8eb068037008d0ed068e3b21a08ec448e3b01230ebc46636f08d0d3418e34d05f8ce808e3ac1a30e8445036e08d0e8046036d08d0eb057c39f1180db023439e1180dac23434c0630ce408c39d1180da82343698d80da412439c1180da023434c05f8ea015639a0d00eb468e3ab1a24ea86823a91a04e9c6803991140d9c23434b0638d2c17e3a605b8ce008e36608d0e9058c3a115b0d9423436408d0e8057c36308d0d882343a015b0d8423436008d0d2817c33701f0d7c23436d8550d7423434a05b8da615635c08d0e8457e39f15e4e7857239d15c4e7057039b1178d6c23434905f8d2416e39a0578cd807e35a08d0d2018c3350230e5c57c3590490d6012435708d0d2017e39605b8e5406e35508d0e4c67e35408d0d4c1243520490e443723900dc0d441243a35a38e8968c3a31638e8858c3991590e6048e3941230e4847c35008d0d1c18e34705f8cd008e,
    0x3f4093cfcc24b3f2091cfc42433f00980fb835634605d8d181663e90d40f9c2303ec15a4e7e5613e60d00d101763440598dc01653eb0578fa44593619144fa034e3420598d081563e70538f9845434005d8d001662585174fbd4552580d74fbc3553ed4d3cfb434b3ea0d1cf9434333f0598cfc15629b55b4ffd56529b11b4ffc4653fd517cff445b3fa115cfd44533e408d0cf817633e0598b3915e2274558b3814e2270518f883643e015a0f783403de1150f743743dc0d90f8534f3e10d2cf7c3473db0d0cf644663d80510f4c45032105d8f5816c3d41178f4c5643d20510f440443d7517cf5c45b3d5115cf4045338d08d0f386743a41140e302343c85e00f2557038b08d0f3458d3c75604eb456d3cc1594ed145e3a31148e282343bf55fcee95733a21148e2423429c05908991562cd0530e2023438708d0f245743c811d0e182343c55590f144743ac1190e1423438408d0eb06803c51600e0c2343b35178f1c68d3c61a04ec956e3c41198e082343c30630cf408c38108d089516638008d0f0067437f08d0df82343be1e00df42343c11a30efc58d3bd1594df0234,
    0x427095909446841c11a108c45842111c107c45841c15a909056f42215ad08056741e158d07446241b1169064464418099102412440b0991058254408049101002441409f103426c407049104414c4120951018124410015103446540b11a902445f408116d01c457406114d01045b41715bd05456b413159d03c56340e0db903026e40a0959014124403009127145f49a516d259457492514d27035f49a0d6d2583574920d4d23d34f48f0d2d2303474850d0d1dc25f463096d160257441094d0c924f426492d069247402490d0c823f42608ed06823740208cd55145f54a516d3f54574c7514d55035f54a0d6d3f43574c70d4d30934f4c20d2d2fc3474a20d0cf9015f34f055cb4514f22b451cb4413f22b04dd00412d1eb817c6d60570fda13c1de8470fd80fc1de0373ef08d0a5817c22a4558b4014c3ee08d0ff84663ed08d0d3418634d05d8fe44603ec08d0fdc3403eb0490ff06793ab99c4fd84503ea08d0d2c18634b05d8ebc17532105d0fec16e3e908d0fa02343e70490fe456936c9584fe045e3e608d0d241763490598fdc15e3f61590f942343470618d1c176,
    0x48451552103554824d3d20834b4800d1d1ec34340e490903823247801511d824446a04911c834047111411d026c46904911c825c46804911bc13c47115911b126446c09511c024446704911b804446500911b03524680d011a045446a4d3d1a834b4690d1d19c3434650d0d1d545f475116d1cc45746d114d1ad25646b0919198124464009118437c44f098117c57045d0d0113826044d094117445445c0df116c36c44a098116803446251b518836d4604d3d18034b45e0d1d164343449094113c374448095115c244446049114c45044e0dd115426c4450491134364452091111012444c095114845444b099114c56444a0dd1144244443049113434044c08d113034444d115112c23444f4d3d13c34b44e0d1d1283434480d69110340444115111934f4460d2d1143474430d0d15945f456116d150457450114d1243644334d790cc34e447495911c246442049110036443e0d510f047c43b0df10e44544380d510dc05443f15bd0f456b43a159d0d85634350db90d035643309890c426442f09510b427c42809910ac25442811890c056f42e15ad0b056742a158d0a426e,
    0x4b549512d42444af00a12b40244b345252cc1394b200792c40124af04a12ac13c4ad00612ac25a4b60da92dd2554b709152d823d4b404a92c01284ae00a92b00264aa00912a036a4a709b92982664b8096d2a42531da817c6320574a500bcd4405748600752f44544bc0db92e83663e505bcd401674b904d529013448504b476606f18a819d28c0344194904f5245d4a1116d28045749f115527825b49d095d0fd24f430492d091247417490d26c35643d497d0b925b422495d05525343c493526446d4950db526026c49709810e924f42c492d081247413490d0e524d437453d0411434950db9250356436497d0a925b41e495d03d25349300d124436e4900d5920826f47509ad180267456098d2283404891140f5256e3f895ace6e56331c958922034048009bd1cc26b45e099d15026348e097d2342533e8916cd7245348b0d391f425f471096d174257453094d22824f489090d16c26546e056d168157488115121c36e47b09bd1b426b459099d14026348600d11fc3424830d911f835048115a11f434047e11611fd56447f11911f445447c0d911e406447a09711e4233,
    0x4c900d13e42394de04d13e837c4f809c13741344f508e13cc16c4f104d13d835f4f40d6d3c83574f00d4d3701344db05113b035c4eb05713641344e9091135c1444e804913b824f4ed092d3a82474e7090d3501344ef0db13982604d304d0b9d14f25c451d25412d377059cb9914d49404b53842494df09853781604da090136013c4d208ed33c2334dc04fd36c13b4d904dd35c1334d604bd3541234d108ed3382334d405413481604d1119933c1604cd04a13343564ce11993301284e0116d3744574d30d5934024b4cb090d32445b376015cb9104f49300753ec56b4f7159d3944664e40db938c356375059cb8d15f259455d3881354ca04d124812d4c800d124412d3ee05bcdc016749004b531836e4c50d993103563ed05bcdbc1674c304d523c12d3f799e8e6a67236c15e8e7e5724be0d00fac17e3d395b8fda56b3de95a8c3e566399958cc6e5624bd0d00fa816f367059d30415f4c0057490c15548c04b4f9e56a36111a8d864623e705b8f9a45b35b914d22234e3e6057cd6c1574be053d22012d354059521c12d4bb09812d83624b608f52a003d4b504a12ac024,
    0x23404d543012d505049545025426345714b446e4ed11894b035d5240d554ac2565240954b8414d233051542c13d50404d499112d52a049549836c52305b147006c51f0531498568522057146405052315a148825c51b017146005051f09793ac252263457147056851b017146435c51805714a0569524117944445d5270db93a83625250d79490249513090548415e520057547815c26245554741522e004f48c413550a04b540c12551a017945c05250f049145025c2df04f48c013550f0d793a035251511b939c4625130d5544826c51108f8b7814d22e051542413d50204d544012550e049098d15c50c0d7942c35a50a0d5942435226449694202562ea4579404136501049941835a2624d5941425e504096940c256502094897d15650104f940412e532117d3e14535310d7939835252e093d4a424b516091d4342432e9453c9791472dd04f48b413550704bd25c12d500049c94c125497098152446f54811b4c3e465546118d51445f4f7514d51036e4e40db551035e4e50d494d02624ff09813f816d2520594ba114f25d451cb7013d22c04d525812d4fc0d51380134,
    0x4a4049077606f191819d58403f4a30490f4406a38f019cc5c0664bf95915d047e57211d92882343f505fcf6c17e3d005e8e3817731605d8c2c17257105155801441dc81fc63e07755f01108f146855805949c515555d051528412d55b05f49c91755570554bd114d270451528012d37d055cbcd14d49f04b49bd15426e45109c9465558116555c45526d451954d46b545519cf4e45d55c116d568457559115554836a5440d9951035654d0d54df016725805755581575550554bc114f26c451d27012d4fa4d913bc354550049154424f511092d4ac24754f090d53826049b04b554c56f4fb558d54846e54d0d995303562ee457c9a5157235051552c13549a04b43ce85f06ea15d50c27049904b499d361542058150427054705113f157c53209c14c4260511094550024d53d09154f0255511092550814454015f14c037c52d11f147c26c53d11f14f04705270df14ec15c53815b143c36c51511f14e427c53709b14d812454311b55044615310db14fc24f53e092d4e8247535090d4cc25953008fd4b423b52708dd4542335300db93b836252c09654ac24552f0514b8813d,
    0x58815ad3201243b6019cbe905f5a619ed68c67759815d965c47e595119931c2343b505dcbe516f2b345a8a751671f14599650145589051161c0443d995b5318234585059131423458305f0f6667e3fe99ecebe67332199c93124504c408d0ff817f3d905e8ebc17732105d8a1816c4c308d15fc36b57e0d8d61047e58211d96044664c208d0ff417f3e105f8f5c17a3ae05dcc8017631305c960014557d0510fee78a3a69e08eac68a3ab9a093064504c108d0fec18e3a6061930023457995bd5e456757881695e00563d599f8fea67b3df99e8c466763a599ccc7a6724bf91412fc2343fa05fcf7c17e3d505e8e9417731e05d8c4417257b05bd5ea16e57a05b55dc16c2850594a161624bc08d0e4817531905d15d41644ba08d15cc17c3dd05b12e423456e11c95b834d4b8049159404d4b704912d812456800d15b423856a00d12b812456809315a892856a00a12b00144ab00515a036a4aa00515b847a56f4d955bc35556e0d355b0a3a56c04e92a412456b00e95a403656700d159047c4a804915903784a7049129812456511e958c37e5620dd92941245700dad598363,
    0x5ab0600f6646d54808d17041642a351c47e54705b629c16d817054704916d4b805b50a015182345b006316a81805bf055169d68c54508d16b418c54408d16f01545ba11f56e427c5b429c16d815454e08d16dc57d5b515c56d037c5b30dc16c447d5b011c53f82345ad117d6914531f945516ac57d5aa15c4a5817c5c215fd70057d31195d56f85735bd15bd68d5635bb11f965c47d5bb11b96604625b82df96c8b725b809f96c82724fd08d16bc17e5ae05f56b017c29505d56a41722fe457cad515a2a1455c7cd1562f805349d81454fc08d169c4644fb08d164814458801113e82345a512313dc2345a4063163c1444f608d16881544f408d16801444f304913c823459e05f13c41244f008d16701445a111bd67c46b59d119d66c4634ef08d166816e59911f139423458e0510f6656d4e408d0a701642fd457ca811573d999f8c866724e308d0edc17759605b0bf115d4e208d13841245930d653801244df04916443715900dc137412458d0d2d62c3434d3049134412458d15d93401244ce049162c5764cb049164856b58f159d63846658c0d6d6283534ca0491324124,
    0x55f8d1d78034369b55bda3556b647559d86956369b11bda3446b647119d868463613517d84c45b55e915d8444536090da98083625f24d697c834a40004807aa06f1d601ac6ca067174018c3ee85f150a16c1d68570aca14c3ee04f150812c1d60470ac810d7b403c5df00c09f957855d08d15702345d605d4ab51655dd055556c23455a08d176c18d2ae46157541653084574ab11553d995f55642345d905f0ef41673074574a7016455808d0aad16455708d0c1115c2aa4550ab95755d615a575456555608d0c0d15e2a945596f035455508d174445f5d0114d72836a5bc0d9973c05e5ce014972d57b5bd55dcf5656d5dc15ad7685675d8159572447a5bb11d96ec4665c811955502343bc05dca6c16d5d705a97501675d305997481655cd0590c0915f2b94568aa11571fa455969547455308d166446455208d172816454d08d0a5817c1f845595302345c705b152c2340f7a17c1c68575cb19fd6996735c915f97204765c6119952823430045bcadd16a2a5459c7d916627705547c01545c505157101440f5a1bc1be8675ba2e316dcb805ba0a316dc28054908d16c418c,
    0x62b15d98a447e62711998403785f94da97d43586240d21880a48620052131c120147a1ac29e86361f012186c0445e600c183c3786190da13181205e500c185c3706070d8131412060e0de881a3604c404817900301e001ac65806361811f9858476615119983037a6050dc98503484c2048077c07b19401cd78c0301d881bc76006b189819c6240634a2959182a47e60391d982837a6030dc97cd3685f30d618483485f3c9217ce1484a2048075e07f1d701ec61a07718601cd7ba0485e081117b803c5e000c183c47c60e11998342444bc95917d334860b09117d21485e28111841561610118583145f60c116d5d245760a114d81c47460609112ee4544ba95918102445f0812182156960811a581545f605116d5ca457603114d80056560015d97dc4725fe11c97d84625fd09f97ecb585fb05617e80585f811517dc56b5f6159d7d046e60115bd7fc56b5fc159d7e45635f511897cc4525f00d997bc2345f1516d7c435b5ee0d0cf4645d5ec116d7ac4575ea11557a03565e700d179436e5e40d5928e4545e20db97840345e9517d7994535e90d7d7983535e34d3d78c34b,
    0x64f097196856965911b98c04626581179948b52657097995025c652054994005e64e0149448130511050197457e62d15c996c36564d0d9193027c64a293192c23e50d050192812867215bd90956367111b98b046266f097d9a425b65e095d9242534ff04c1a3057f68a15f4c2e57568715cda1856f641558da1447e62911f5a1446e62b11899d03726480dc17f135a4fd04817e03484fc04819184645f70d61898348623292188c1484fb04818780444fa04813e41406222d2190c24962205213e013064412319083805f60d6189434862129218841484f704819003584f604813d41306380dc18f83484f404818f03704f204818dc37063a0d213c012063811a58dc46163f11bd8f446b63b119d8e44636360d893bc1204ee04c13b41404ec04c18c846c63009413a813062f09118bc2544e904c18c036462e095139c140634097d8cc25b631095d8b42534e604c18d447c62c0dc139412062a0da13901206280d8138c1205e800c189856b625159c52685b0a8a14d88837062315ad8845675fb4d697e935a61d08c132401061d116d87856b61c08c132001064519ed904677,
    0x6720e015141206710dc151012064b0985a0825d67e095550c13064a2d619f426564b096592815854104c15001306821a319c048c68009a14fc13067b09519b858c6800db14f814053d04c14f013067e16319f458066712319e825053a04c196447c67909f19ec25c67909514e413053804c19dc67c53704c197458c67a0d919e028c67609f14d414068415f5a0c57167111f1a0425f67f096d9f0257675094d4d013053305019cc26953204c19c024f66e092d99c24765d090d4c413053004c19c047e63411c99b426966b09a19a825552e04c14b414065c09914b014066c095595025452b04c19b857e63315c99b436d66b0db199036566a0999990265529050199847c65a09814a013066201f196424052704c149813066619e196025052504c1980060524050194825051d04c147002066219e194014051a008146413066011b193825051704c19a067966415b992c56d66711f98c447266511b998cb62664096596c25164d094198c16251604c198406e65f0189964354515050145013065c09b144c140653294194c150651017193c0506560139954042653097194415c,
    0x584cd1d8633436b31595acc5766b111c9ac03726b415bdac856b6af159dab85636ac11988a01446aa11f9aa44662200511aa00446a611f9a9446620a051165d56f6ab55ad7215676a7558d65c46f6ab11ad7204676a7118da9145f6a4116d604457615914dbfd56f6f755adb615676bd558dbfc46f6f711adb604676bd118daed45f6bb116d5f3457613d14dae016e6b50599ab51566ad0519a8c12e1edc1bc6e7067101e17c1eb857101c13c1eb04755c04817b003055a04817ac03069f0dc15641205ea00c053e85b0aba14da6957b68655dcf4256d6a115ada8056769e1595a6447a68511d9a144666921195a7436a69c0da180535a554048053685b0aaa14d7a403064451d154c1206351191a3c3485520481a5825469809a15441306960971a5436454f0501a5c25f64b096d9a8257694094d5381306930dc180135a54d0481a4436054c0481a3c46e0f2a17c1b685769a19fd91567369915f9a4847669011998203705ff4da9a3834854a04803c286f06ba19d7c403c6840e0152412068b0da152012064a0dc1a0c3805fe4da1a243586882961a20158546048191968c,
    0x62904d965c12e6d551d1b204646fc05f1acd1566fa05b1ab012e0fae17c1d38576fe19fdb596736fd15f9bec4766f91199ac91666f80511aac12e0f8e1bc1cb8676ee0e01b7418c6f50591bd012e6ed0e01b7018c6b04591bc81546d75a31b7c3806da0631bb035d6ea0d55b9c1366e90d95b941366ec1a31b901346e304d1ba858c6e91601b881346e40951b983586e30991b9047c6e311c1b9c57d6e515c5b882566ee15f5bb45716eb0d7dba03576e104d9b7c56f6d4558db7447d6dc11c5b6845f6d3514dbd857f6f315f4c4f5756f115cdbc056f6d2558dbbc47e6c511f5bbc46e6c71189b803726de0dc1b6c17e6d905f1abd15669204d972012e6d71191b081446bf0111b5448c6d40e01b4c18c6c10511b441546cf0511b3417c6cb0511b4046f6ce11adb304676ca118db2416e6c811f1b181646aa04b9b1016c6a904b9b0856b6c1159dafc56b6a80079b5867b6d219ddb1c5766c511f9b0c4666ae4599b001446a704b9af80446b6f1f9ae7c766a4d199ae417e6b605d9af01446a404b9ae83646b94d3dae434b582cd1d85b3436b70df1a9b3566b64d3dad834b,
    0x70b6d39d0c17e73605d9d4013470b04b878a07f1a381ddd3856e74d09bdd3026374a11d1d24464715e5a5d1856871aed71cdda747440991d2c465748093dd1c24b745091dd0c24374115b5cfc47c73e11b1cf4044711e5c5ce857073809f1cdc26c7401175cf024f73b092dce4247736090dccc5686aad195cc426c72c19f5cbc57072d09b1cb023e1f88585cd046a73209bdcc026b72e099dcac26371f0dd9ca436672415f5c9847c71d0999c9057e71c0dd9c8c05472015f1c7847c71d0111c8446d71f117dc7045371a15a9ca056f72715adc94567722158dc6c3667190d59c5c5657150d99c4c57d7110d99c3a37f70e0dddc3034e71495bdc5a56b710959dc4a5637160dbdc5036b7120d9dc4036370f0d7dc3435b70b8d5dc2c35384b15be11056b824159e02c5638040dbdfb436b7d90d9ddfc3637780d7ddb035b76a0d5dd3c35374205b9cd416672a0559c6013e70a04b878606f197819c35a85f051a15c4e083f0a020ddc2012e70604b9c1017c70304b9bf957b6f055dcf5f56d70715adc145677021595bf447a6ef11d9bbc4666fb1195c041667000591ad1156,
    0x7890945e0c25078e0911e3027c78a09b1e1825c7860941e2045e7870d49e1425e7840971e3447a78b11d9e243657830d91e0823e7a915ade985677a50da9e903667a1097de6825b78f095de042537d719edf4c6777bb11e9f184767c50dbddb836a7c00d9def83667bc0d39eec34d72b0599eac13678004d1c4012e73e05d1df816477c05f1d2816c1e681bc6a206773d0199df457e77b15d9d2017e73c05d9de815470f04b879607f1a681ddde405470e84b9dd816477404d1c3812e77105f1dbc1347770dfddd437e7730de9dc83777700dd9db837274705f9cec17670f6579db413470d04b9d17e7a739f9c9c2dd6d719f1b1d1417e73905d9dac16c71904f1c2e12e76509d9d9426676811f1d91b7c7606dc1d8c17c75a01c1d6407076411f1d8c37c76209f1d7407c75801c1d8057c75f0dc1d75a7c75d01f1d69d7c75a11f1d61b7c75909f1d6017c76775f9d99d7c76711f9d9847c7616df9d79b7276509f9d9426e76105f9d7817275c01f9d6c07c75701c9d480257530dd1d4c2607550de9d5037275209d9da426f756099c78e06f1a4819dd440277436df9cd9b76,
    0x7e20511f8c46f7e1118df7847c7dd0111f7c45f7dc114c37284f057a11def067d7ec15f5fa856f7e4158df8047c7c60d89f6c17c72e0559c6c13c71204b9f6807c0daa17c1568577d80d91ea41347a804d1f5858c7d50e31f5018c7a604d1f2817c7d20551f401447ce05f1f2416c7cc0511f2836d7c90d95f4446f7cf11adf344677cb118df2016e7c70df1e901347b004d1ebc13479804d1f1057e7c315f1f0817e7c105f1eb01347bf05b1c4412e72c0599ef41347a504d1ee03787ba0991e8c24c7b40991ee047c7b10df1eb83747a00d71ecc3607b609f1e5c24c7b409b1ecc4747ad0dd1e3435c7b109a5e6c2557af11b9e6046c79b0995eb82597ad0945ee436f7b70daded43677b20d8dec026e7ac0999e9424c7aa0955ea047c7a709f5e8c25f7a0096de5c25778d094de8824f79f092de5424778b090de8c37a7a20dd9e7826979c09a1e6c25578a0991e742557840951e8047a79f11d9e7836d79c0db1e4036579b0999e402657940db1e483607880941e585707940db1e4846c7870941e4056e78215b5e6446e79811b1e5c37a7950dd9e4c36e7910d89e40259,
    0x84215ba06456284111fa10047c83e0dfddcc3798380dce0d43718070dbdf4c36383009fa0ac27282805fa09417c74b05b1c9413e71084ba08c16482104d207c17c81d04d208836f8200dae07836781c0d8e06c16e81a15f20541548180591c9013e71384ba05024b811091e05067681215c204467681015a203c35c815159a00426b7e7099e04c24b80e091e00026b7e5099dc8c02e81919da05c57e7ff0dedf903778160d6603415472204f9c4a12e80c0151f545747d81a3202448c8080631c5c12e7fe09a9fc067e80a15ee01c5778061595ff437a8050591cc815671604b9fa43748020959fac36480105920000647c70d91ff81647fc0591fec0647f805b1c5412e7f40951fd82687f40971fcc3647f5097de0825b79b095dfc82537f104d037e85f05aa15e00c67f7ff19cdff447e7bb11c9fe836f7730da9fe43677f70d99fc034e7bb0d35cc01667ef04d9fb813471404b837686f058a19dc8413c71304b9c8013c7eb1a31f8c48c7df0631c7c13c7de05b1c7813c7e811f5f7847c7e20df1f984707dd01f1c7402c7e91631f8448c7dc0631f9c15471c04f1f94054,
    0x86a15be1a056b866159e18c56386111e217c46885d120217038085a11a216436870c0d0a18067f85e19ee16c67785819ce15c47a85611ca15446a8b895be30a56b887959e2be5638c20dbe2e036b8af0d9e21c3638840d7e20435b76ced5ddb1b5387c85be1e216e87485aa1f0167878059a1d0162854857caca15a86c855e18a15686c04fe18813e85404dcac813285104d1c5612e84f05f1ca413c843115212846a843119a12457a84215da108566847159600c37b7ea0dde14836b8500da613836776e0d85d0017484d059a13016472804f9c5212e81a159212816484805f1c5e12e13d20bc28882784919fa11c57680a0dfdf5c3738460d65cd01648450551c9c13e71684b84ec83f0a120de10c15483f0df60f437183409f20bc2708090d7df5835372604fa0fc48c8330a320a818c74d05b20f013683a04d20f058c82e06020e847c83205f20b417083d16320c428c82c0a020a418c74c05f20ec13683904d20dc26383604d1c4612e83204920d037c83309f60c427182e04da0b413482f11f20b037182a09f60a427182709be098263808097df5025384215fa05c57d,
    0x88986322241348aa05522a01448a605f22901448a911be29c46b8a5119e28c4638a205ba28437c7110d9226023888e04d225023488d04d224c12489704a227857289608e224823489d05fa27017c89004e22301347118d8617215d89705b226036e8960d9a25046289305ba2482668900d9a23446288e09ba23026688a15ae2245678ad19ee2ac67789911ea2804767160dfa27c36f8756daa26c36789a0d99c5034e8990d3625423a89108da16e16f2b585aa1c6167866859a11e15688f04ea22c13688804d1fc012e88695fa21857670b15b9c2e35587e85fe1ea17e87685ea1f817787a05da1d817288505521f7b7f879edfa1d7b7a87d6dde1e5b768756dc9c2e36670b0d3a1f617f87985fa1d617a87d05de1e417687505c9c2f95688304de20813470b64b9c3b98d88015f61fc37187e0d7e1f435b777ed5ddc9b5387b11f1c4dc7d717e5c5c3994b87a093e1e424b775e91ddc1a438770551c45956715e4ba1d835f8750d6ddcfb5776e6d4e1cc67f87219ee1c467787019ce1bc37e86e0dda1b436686b0991c90929869095219457d86709f1acca4686515fa190254,
    0x8ca61107a606f1e901ac6c60671b1018e36fd7e8db75da36e37e8db0dda3683541e881fc7a007b1b081dc6c00738c8e1623218548c880e23200346aa448635057d8d605c235057e8d3015236056f8d715ae3545678d2158e3401498ce057e3302608ca119a3242488cf116e33415b8cb055e32014f779650e4a656f93795ae376567911958e4ee36e93b0d9a34635693709be4a426b911099e3742638d9097e211a5b778e95dde1a538d108e479e06f1e701ac6a60671a9018c38285f13ea16c16e8570a3a14e31e0388c700d04f882f0e020ac28c82705b208e2b057470c0de5c4067e8c515ee2b65778c4159630037a7120d9630c16485e857cade15a872855e1a21568b40dd22843647150d922fc1647158d8630467f8b599ce30047e89911c9c483768be0dbe1d7b6a8bd0d9e2f03667100d3a26434d86085bcae616a873859e1aa166817855a2ec13a8ba04da2e41347bc04b9c3036185985762d868c8b206322d058c8b106322c61548b2117e2c445371419f62dc57d8b515be2cc5637160df62803628b005f216215f2b3856a1c2157863855a2b836488a04d22b038c,
    0x62a19e3340449271a3248c38c91f06024640809220db249458c91c915248438c9218d52470180916020245a05492211b2476344917811248c46f921118c39a84f061a11e47845491d0d5246205491f15be47056391500d24604549170d5008d85491400d245445f914114e46456f916158e34e35691300d237c67d92815f649856f924158e48037c8d28d5a40826291b05c246807c91201c039285f05fa15e32c03491009923b42548e6091239248c90e0a323ac2548e409123ae18090c095242824490809f241824490b11be42446b907119e41446390409ba40c27c8f609523a42448f309123c824490011fa3fc47c8ef09523a02448fd0db23d42748f815b23d02748fa05223c43648f8158a3c03668f111723c44508f511663d04518f30dba3c836c8f00d3a3ec56b8f9158e3dc45e8f609ba3bc2668e58df23b01708ed15ae3ac5678d68d5a3a426e8e8099a3941708e615ae3905678e3117e3884578d4919a38024490f19ee4346778d59199fc045e8de0dea40837690109be1d9a6a8fe099e3f02668ee09563a82548e709163842448df08fa37823d847851637047c,
    0x946158a51056a9431589ba6c6a94f15ae53856a5aa959a52c5636edb1a96d64669480daa5143527f12d42249a6a942094a5042506f195bdbc6d6b5be959da1e56395051aa54045a8916daa244b5a940459a5001566c5917db16c5b597915d8a64538df6d7dc51b5b817ed5def1b538df2d3dc50b4b817cd1def0b436ef917dbbec5b5bb915da164538de6d7e265b5b842ed5deedb538de2d3e264b4b842cd1deecb439c555ae70d5679c511ae70c4676d8917db62c5b5a8915d91e4539bf0dae6f03678dd6d7e21db5b824ed5ddfdb538dd2d3e21cb4b824cd1ddfcb4393d09aa6ac2669a5457e1d115a985455e5a91569a5053e1d014a985051e5a814695804fe54413e93f04dcc2413293e04ba4f412d8db093e219a4b77de91ddeda4390e15d2342038143a12c29684392a19fa4e857b90f95de4e45659380d9235e35693509e850685b0a4a14e33e03892509d240c2649330d724d0464932019233804492f0db03a685f064a15e4ac24493619fe49a6738d89199ef045e9350dfa37837293109be1dba6a930099e4b826692d09164b024492a08fa37823d817851439e86f,
    0x99305ba61816695904fa500136984116260c2598ed28f660024897d08d260034c97c08c25f423c97c0d1260423f97f08ee5f823797b08ce3b0b4c97a11c25e42718eb28f5b7ec6a977099a5d825c9720da25bc35497211b25b835096f0d725b84649730d7e5c435b9700d5e5b435397415f65b04706d4ed6a60856b978159db7ab5a97509ae5ac2678fc697e269a5b835e95def9a538ea28f6575166848c57259c14c5ba959a5a04668986daa0ffb66834cd5259c254848c91258836c95c09b258036095b09b258856a6ecb1aa5805626eab1aa57846195c15aa56c56296515ae59056a5ab959a58c5636eeb1a96de4668966daa0f7b669610d7a57c35282fcd12241a6a95d099a56825e92b2971bda56f6f6b5ad70a56768c958e255c6a841f19a254c5a841d15a23db6a9694d9a23cb5a9690d5a59916e959459a59815e959055a55c466809ed9a55824495415f5f5bb5695309f255556b952559e55446b952119dbce45f6f3b16d70245768a914e103b56840cd19a22562948459a51c36094409825283789460d8253434889469e250c26094c0922528561949097a51c56a,
    0x5b991926a14549a80d90a5a354833e99669d259833c91669c2395b8959a6a84669016dbe27db6b83eed9df15b63830cd566a43499a605ba64d16696604fa67846c99f0db1f11b7199d0db666c3618fb2d7669034999045d259413e94f04d9f0db6199605b1bf294496404fa5381368fa317253014489e6de66683618f92d7668434998f45d264414496304fa52c13699f115267834898d05d257015496204f267467a6ebb5ea63017695a051258413c944051251c13498a05d262c154960053250c14494604d266c67a99a19c9ba2d7a98805da57c14c942051266413694504d265016e987059a5041447f124d26584686fcb1616d2364831e99665425999409063d8a3d98e097662c25198d49b63d5a5d98a49863d1a5d98e15c263456898b15c262856098909f2648463991518a644461693918264145998f514664036e98f0d896ce35498c49be241a69988498e61d2618ef69760b3a5598c093e240a49988090e61c2418ef28f60b32359a315ae68856a5a9959a6805636e0b1a96ca4668fe6dbe26db6b838ed9df01b6399c0d7e23cb599980d4e65c3518ee2d360af345,
    0x978cdc6435b5f8ab6d6df4fb577d36d4e71017c978455a54813e977459a70815c6d7d17db5fc5b5a7d15d91b4536f095bdbc2d6b5bd959da1a5639c14d9a704356975459a5d41569c004d18874529744559b5734f6d5ed2d697347644cd0e6f957d9be11f5b4b45f6d2f16d68f457641d14e6f417c96b455a5ac1469bb0dbe6dd3639b405be6bc16390b64fe2a593b81ce4ddf45933909653e29d94b81ee51df3d94390764fe29593b820e4ddf359339b711be6d84639b305be6b8163905653e28d94b822e51df2d9439b44dbe6cd3639b409be6cc2636ca88fdb2aa3b59b88dd8e62336cc8d3db32b4b59d8d1d8ee3436ce88fdb3aa3b59f88dd8f62339af51be6b94639af0dbe6b83636d08d3db42b4b5a18d1d8fe3439ba4d7e6e535b9b84d5e6d53539ba097e6e425b9b8095e6d42536c888fdb22a3b59988dd8d62339b2057e6c415b9b0055e6b415390364fe28593b81ae4ddf1d93390324be28492b81ac49df1c9236c78d3db1eb4b5988d1d8ae343902693e281a4b819e91df19a4390228fe280a3b819c8ddf18a339ac05b0a5a16c9a805725a013e9a705ba655166,
    0x9df95f678437c9d88d5a760271924697e2cda5b7e4e95df91a539df08e67380709ce80d277456591f6d7a7702646aa0486479b5c9da119a471b6e9d9091273e0449db55be7615639db11be7604636c3917db0ec5b595915d89e45391b6d7a46cb4e9d5519588e3429d511b67340609c035f275947d9d4515675837d9d40d55b5a34f6d6ad2d69a3476458d0e73007061f88ce46993f7da64ce46892f7da248e744455919693e003a47918693673c356916697df97a5702500d27354559cd0d55afe34f6bfad2d62234761e8d0e74145f9ce514e74035f9ce0d4dafa34f6bead2d61e34761b8d0e73025f912693e033a4791228fe03323793e15b67a946d9e2517e7794539ea0db678835f9de0d4daf634f6bdad2d61a34761a8d0e75c2619d3097e6f0a53911693e2bda4b80be91df65a4391128fe2bca3b80bc8ddf64a339ab054a74806c9cb018040e84f07ca11c40e03f07c80dc51082f0a6209e72416c95704fa60d166910697e2b9a5b7d8e95df61a539c8119a43db6f8ad6dae01fb677d76d8e71c349982459a71814495504fa439a4f8ac692df57a477d5690e54a57d,
    0x9fc01127e856a9f9099a380a5c70595bdc16d6b5da959da825638bb6daa7fd3668bb2d6a7fc3569fb45ba7e11669fb057a7e01569f615967d42649f455be79ad639f411be79a463702917dc0ac5b5d8915da7a4539f0459a7c456a9f00da9ef4b509ef0941c1e56f707b5ad7725676a1958e7c946a9f2116a7b91669ee0559bee45f6fbb16d722457692914e4a9b5f7106d6e11fb577f06d4e4a8b4f7102d2e11f3477f02d0e87556f9e2b58e87446f9e2918dbfe45f6ffb16d73245769b914e86c36f9bf2d8e4a5b5f8b86d6e12fb577ed6d4e4a4b4f8b82d2e12f3477ed2d0e86826e93d098a84515f874a56a81d157a00455a84414f874852a81c147a00051a7dc13f9f304fa7b41373cf04ca7b012e93d04b441685f07ea15c41604f07e811c52883f0a920de7a146f9dfb18d8823429d609be6f8a63928693e2dda4b816e91dfb1a437e028c649da5f8b6696dfafa577eb694e7942697e3690679c6709dd09867440609e515f679027c9e915f27a047d9e6115676c2719e30966499a4f8b5692dfffa477ea690e740070925693e2d1a4b7e9e91dfa5a439e015f5f87b56,
    0x6f78d3dbdeb4b5c38d1da36343a1b29ae74ca67a1f09664dda4f8c2692e113a47804690e4dca3f8c228ee11323780428ce86816a152a12c2b684315280ec2b60330ea20ac1948239f495968133699366d7e305b5b803ed5e00db539e105928111569f404fa80d156a1c55968704656fed17dbfbc5b5cbd15da6b4539bd2592805156a010519bf634f6fdad2d7263476998d0e4d5a4f8c0692e127a477fd690e4d4a3f8c028ee1272377fd28ce6b01546aa9194a7216ca1705727f813ea1605ba835166a17515285c36429c8d52859259a1608e684d054a1300d2850248932697dfeda53a13017a7f002ea19119a4c5b6f8be6dae13bb677fa6d8e860349a1505ba8291669fb04fa848044a0e05b1b1a9449fa04fa7c4136a0b05ba8241669ef0511ef4934a0c09528384686c6b162834259a0b09058aa460a094986824241a1015a975e5669306dbe2f5b6b852ed9dfe5b638bb2d6683c351a0a05ba8201669f804fa7b8136a0611a2814269a031596808468a0415be78ed63a0109be704a6392e697e2f1a5b850e95dfdda539f9459a06315c9fd05327f84669fd0952063244,
    0x28915659c40d92882356a2009a64e9a5f8c5696e02ba5780a694e893239a25092689045b9c7b15e870a5b9d4295e4e5a4f8c4692e11ba47806690e888466a21091288156b9c8b59e88046b9c8919dbe645f6f9b16d71a457690914e7b056ea2651ae716c67a23515689836b9c58d9e88c355] 26 7) 6 11 7
def cert_trace := dagTraceF cert_mask cert_stock 12 cert_forest
set_option maxHeartbeats 0 in
def cert_sym0 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def cert_sym1 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78beeb6caeaa68df6d74cf2c709e69648e28607de75c6da6583ce34c2ca2485d65544d24501c61440c2040
  invFun := decodeRows 0xffef7cefae78beeb6caeaa68df6d74cf2c709e69648e28607de75c6da6583ce34c2ca2485d65544d24501c61440c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def cert_sym2 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffeefaf7ce78df6cf2d74c70beeaeab6ca689e68e29648607de6da75c6585d64d25544503ce2ca34c2481c60c2144040
  invFun := decodeRows 0xffeefaf7ce78df6cf2d74c70beeaeab6ca689e68e29648607de6da75c6585d64d25544503ce2ca34c2481c60c2144040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def cert_sym3 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffeefaf7ce78beeaeab6ca68df6cf2d74c709e68e29648607de6da75c6583ce2ca34c2485d64d25544501c60c2144040
  invFun := decodeRows 0xffeefaf7ce78beeaeab6ca68df6cf2d74c709e68e29648607de6da75c6583ce2ca34c2485d64d25544501c60c2144040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def cert_sym4 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0x120941161908328b49369b10530d51571d18738f59779f821a29c31e398a3aabcb3ebb925b2dd35f3d9a7bafdb7fbf
  invFun := decodeRows 0x120941161908328b49369b10530d51571d18738f59779f821a29c31e398a3aabcb3ebb925b2dd35f3d9a7bafdb7fbf
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def cert_sym5 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0x120941161910530d51571d08328b49369b18738f59779f821a29c31e39925b2dd35f3d8a3aabcb3ebb9a7bafdb7fbf
  invFun := decodeRows 0x141120961908349328b69b10551530d71d18759738f79f821c31a29e398a3cb3aabebb925d35b2df3d9a7db7baffbf
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def cert_sym6 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0x141120961908349328b69b10551530d71d18759738f79f821c31a29e398a3cb3aabebb925d35b2df3d9a7db7baffbf
  invFun := decodeRows 0x120941161910530d51571d08328b49369b18738f59779f821a29c31e39925b2dd35f3d8a3aabcb3ebb9a7bafdb7fbf
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def cert_sym7 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0x141120961910551530d71d08349328b69b18759738f79f821c31a29e39925d35b2df3d8a3cb3aabebb9a7db7baffbf
  invFun := decodeRows 0x141120961910551530d71d08349328b69b18759738f79f821c31a29e39925d35b2df3d8a3cb3aabebb9a7db7baffbf
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel


private def axis12 : RowAction64 := maskedRow64
  0x0c0c0c0c0c0c0c0c 0x3030303030303030 0xc3c3c3c3c3c3c3c3 2
  (by unfold goodMaskLanes; decide +kernel)
private def axis34 : RowAction64 := maskedRow64
  0x0000ff000000ff00 0x00ff000000ff0000 0xff0000ffff0000ff 8
  (by unfold goodMaskLanes; decide +kernel)
private def flipSwap13 : RowAction64 := maskedRow64
  0x0033003300330033 0xcc00cc00cc00cc00 0x33cc33cc33cc33cc 10
  (by unfold goodMaskLanes; decide +kernel)
private def flipSwap24 : RowAction64 := maskedRow64
  0x00000f0f00000f0f 0xf0f00000f0f00000 0x0f0ff0f00f0ff0f0 20
  (by unfold goodMaskLanes; decide +kernel)
private def flip0 : RowAction64 := maskedRow64
  0x5555555555555555 0xaaaaaaaaaaaaaaaa 0 1 (by unfold goodMaskLanes; decide +kernel)
private def flip5 : RowAction64 := maskedRow64
  0x00000000ffffffff 0xffffffff00000000 0 32 (by unfold goodMaskLanes; decide +kernel)

private def reversePairs : RowAction64 := flipSwap13.comp (flipSwap24.comp (flip0.comp flip5))

def certifiedFastRows (i : Nat) : RowAction64 :=
  [RowAction64.id, axis34, axis12, axis12.comp axis34, reversePairs,
    axis34.comp reversePairs, axis12.comp reversePairs,
    axis12.comp (axis34.comp reversePairs)].getD i RowAction64.id

def certifiedPermutations (i : Nat) : Equiv.Perm (Fin 64) :=
  [cert_sym0, cert_sym1, cert_sym2, cert_sym3, cert_sym4, cert_sym5, cert_sym6, cert_sym7].getD i (Equiv.refl _)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
theorem certifiedFastRows_source : ∀ k : Fin 8, ∀ i : Fin 64,
    (certifiedFastRows k.val).source i = certifiedPermutations k.val i := by
  decide +kernel

def certifiedFastCanon (k w : Nat) : Nat := canonF fullMask ((certifiedFastRows k).apply w)

theorem certifiedFastCanon_eq (k : Fin 8) (w : Nat) :
    certifiedFastCanon k.val w = rowCanon (certifiedPermutations k.val) fullMask w :=
  (certifiedFastRows k.val).canon_eq (certifiedFastRows_source k) w

set_option maxHeartbeats 0 in
def cert_syms : List (TableSymmetry cert_mask cert_goal) := [
  ⟨(⟨cert_sym0, by decide +kernel⟩, certifiedFastCanon 0),
    fun w => certifiedFastCanon_eq (⟨0, by decide⟩ : Fin 8) w⟩,
  ⟨(⟨cert_sym1, by decide +kernel⟩, certifiedFastCanon 1),
    fun w => certifiedFastCanon_eq (⟨1, by decide⟩ : Fin 8) w⟩,
  ⟨(⟨cert_sym2, by decide +kernel⟩, certifiedFastCanon 2),
    fun w => certifiedFastCanon_eq (⟨2, by decide⟩ : Fin 8) w⟩,
  ⟨(⟨cert_sym3, by decide +kernel⟩, certifiedFastCanon 3),
    fun w => certifiedFastCanon_eq (⟨3, by decide⟩ : Fin 8) w⟩,
  ⟨(⟨cert_sym4, by decide +kernel⟩, certifiedFastCanon 4),
    fun w => certifiedFastCanon_eq (⟨4, by decide⟩ : Fin 8) w⟩,
  ⟨(⟨cert_sym5, by decide +kernel⟩, certifiedFastCanon 5),
    fun w => certifiedFastCanon_eq (⟨5, by decide⟩ : Fin 8) w⟩,
  ⟨(⟨cert_sym6, by decide +kernel⟩, certifiedFastCanon 6),
    fun w => certifiedFastCanon_eq (⟨6, by decide⟩ : Fin 8) w⟩,
  ⟨(⟨cert_sym7, by decide +kernel⟩, certifiedFastCanon 7),
    fun w => certifiedFastCanon_eq (⟨7, by decide⟩ : Fin 8) w⟩]
def cert_profile : Nat → Nat := unpackPagedWidths [
    (42, 0x100299fefc0400a47fff0000091feb80400847dbf0080089fafc0001227eff0000210ffbc0000881f9f0100288fe7c0800a01fdf0100280ff7c0800a01c9a0000080fe780004801d9f0100210ff7c0000081e9f0080088fe7c0000001a020000000000000000002020000000095c0000000000000000000000000841e4b00004007b7c0001223edfc00028873650004021c17c000000117d0000022d170100008f57c0000a23fd90000200ff7c0004825fff0000219fffc0000c65dff0100219fffc0000465eff0000099fffc0080025cff018001973fd0000025eff01000997bfc0001825fff00000317ffc0200247fff20000117efc0200267fbf00200017efc0600265fbf02000817ffc0600245fff00800817ef88000005dbf018001176fc0000007d130180081f4fc0201207dbc0080008fff40600065fff00800197f740200005fff0180209f23c0000000000),
    (56, 0x8000008c5fff00000600a67cff00030000865faf00000600a67cbf00100080a25fbf00000600a67e8f00100800a05fff00000600a67ecf00000600a07e8e00420400825dbf00000600867c8f0000460006bebf0010008002febf00000600227ebf0000062006beff0010080000feff00000600a27eff00000600207ebe0000060806fcbf0042040082fdbf00000600027cbf0000848022debf00008c00a0deff00000000204aa60000840000dcbf0000800004deef00000601267cbf00000644063ebf00100204025ebf00000600067ebf00020608063cbf00420600025cbf00000601027cbf00030004067ebf00030401027cbf00030000025ebf00000600267c8f00000604463eff00100005025eff00000601067eff00020608063cff00420401225cff00000601a27cff00820004047eff00820400807cff00820001005eff00000601267ccf004202008075bb00000600a07cbf000302002074bd00000200227cbf00000201a07cb8000206000654df00000600065ccf00000600a65cc980000600066daf00020600064daf00000600266d8f0000020000098b000202000061ab00000200206dbf00000201202fec00000600264fed00000601266d8c),
    (36, 0x27ace000327aff6001658ff400365aff000825bff0000c5bff200247bff000015bbf200227bbf080005bbf600265bbf800205bff600245bff200205bbe0000159bf6000459bf200005bff60082788f602a270bf602a6788f6460231bf6022679bf6032671bf60a0278bf603a678bf6032278bf60a0230bf6020278bf60226788f6220a31ff6032271bf60326718f400a4399f200263a9f00126339f0012033df00000010400000000000000010400120590f00000000000000000000200192f0000011af400a039bf0402012af200223aff000200202000201a230002013ef0012233bf0012033ef0009271ff0003673ff200327aff6001658ff4003651ff0002613ff2006053bf2002073ff2000511bf6002459bf2012413ff60126308f),
    (53, 0x300533d67804020020162280000c0140f51c00014008259bf0000300433c47800118000aeafc000000025f57e0000600227abf0000310015d7f8040200003ebfc0000c0144f5fe010080000788e0000300103d5f000018200be2fc000280005f17e00006000278bf0000280114d5f80001400826bfc000000040155c00005000098bf0000080006d778000180489e2fc0000c8804757e0000304021abf0000300033d5fc000182018e2fe0002c0004317e00006010278bf00000020b3d5fc000100049e2fc000000024b57e000060026788f0000302211d7f80000414086bfc0000c020cf5ff00006080238ff8000a00910c7f8000180689e3fe100000808f5ff08004000078ff8400000002d7f8000180499e33c000080144f77e0000400a07bff0000000103dd70000100201e6fc000040044f57e0000001227aff0000000401df780000002206e7c000080144773e0000100a01bdf0000200501def8000000080ee78000000900333e000040080399f0000000040d4f8000080088ea7c00002000035be0000001263adf0000000401def8000000259effc000080124f3fe0000000825acb),
    (52, 0x8040200241ebf0000600267c8f00006200a7dff0000031021dbf0000601227dbf8040020007dff8040000a41fff0000601a67d8f00000100015af0000400a07dbf00000402016af0000200223ebf00000102017ef0000001223fbf0000001203fef0000400a43d9f0000200267e9f0000001267f9f0000001207fdf00000200055ff0000000827dff00000402057ff0000000267fff80000002056ff0000200227eff00000800414ff0000600065cff00000800417ff0000400265fff0000000261fff00002006057bf0000200207fbf00082008415bf0000600a45dbf0000201a41fff4040001a07dbb0000000000000000000080058800000000000800400000003d920400200807dab0000601a07cbf8040201207cbd00000000002000200240207ead0000201227cbf00000000028ab004020000292b0000600202dbf0000201207fec0000201a07ca88000600067cef0000600067ccf0000600021fcf0000200065fed0000600a67cc90000601263c8f0000100885bff0000600a678ff0000000925baf0000600a278bf0000000925bbf0000600a67a8f0100800805bff),
    (52, 0x1806000000800381f0000442803a7f000004020080f00000000000020000000001000000000000024300000c122387f0000040000046008084122387f0000040007a6f0000201a0783f0000003827a6f000008182796f00004018279ff0010000a27b6f0000400a27b7f000060002387f000000020286e000040022387f000000182786f0010200a23a7e0010000027a6f0000200a27a7f0000003827f6f0000100a07f2f0000400a27fbf0000100a07f6f0000400a07fff0000000207fae0000100807d2f0000400807dbf0000100007e2f0000200227ebf0000100007e6f0000001227eff0000600221d370000600001d370000200200d260000008000c260000700801d370000200007d2c0000000807fef000000280782f0000010605f9f0000600a27cbf4040000041dbf0000600a67c8f0000644027dbf4040040047dbf0000600267dbf0000450205dbf0000051205fff0000601267dbf0040608027cbf4040200007cbf0000601a67cbf0040610a45cbf0040211205edf0000601227cbf0000628027cbf0000230021cbf0000600027cbf8040220007cbf),
    (55, 0x4004c7d7e0002000010f97c0000000931fff80000000843fdf00000c050c713e0000028a89fcbc0000201513d1f80000822807f7f0000080540f4fe0000208a01e8880000001503d1700400002813c9f0080080500fa5e0000100a01e0fc0000800001c1f800006000238bf00000a1140743f0000140280e87c0000800001c0fc000070002383f8000061140723e0000040209ecbc0000000513c5f8000100100387f000048820470fe0000180408e1fc000000000100000000000213a7f000008024474fe0000100380e9fc0000204f01d3f80000000000002000000000030be0000180100e1fc000000000000200000000001a5f00000800c074fe000000020068180000104701cbf80000001c07b6f0000000344f0fe0001020000e8fc0000150411d1f80000600a23a3f000000004050000000000080e97c0000400101d3f80000a20803a7f00000c014074fe0000000080200000000001014070000080020380e0000144100707c0000080280e8f80000004001c1f8000000000180600800c05007a7e0000180e80e0fc0000000000402800004c0223a3f000000000034080000310080e9fc000000000010200000800203a0e),
    (43, 0x8000212aa110268c2d1c0210f18fa780001821d4f00002083efe0001118fdfc0000000ea98040002355f0004200bafe0000109f5fc0000202fbf80000605f7f0080084fefe000041075fc0200e31fbf8000140457d00002042efe0080200743c0301531d5f80602a63aff00c0548753c0180a18e2fc0b00031c5f806000638bf00c014c717e0580418e3fc0300831c7f8000004280000c004e75fe0180498ebfc0300d31c7f84600263abf00c014c757e000000020000700131d7f80600a63aff000000000000280080e2380300521d5f006080638bf00c074c717e0180698e2fc0000023c0000000047803000014cf13e0000011e0000001d23c0780201a4781f0000748f0200000238e57c0200431cff800008e3b5f008014c76fe0000038e97c0100531d3f80002863f5f00101087e3e0100298fefc0400421faf80400a43fff00000487f3d0000210f47c0200421edf88000043e1f),
    (44, 0x2000400181806200000000000000000000000000001017104401019b47000000100010000001014100000000001000000141550000100c175000000000000000000000000000000000000010140540000000000000000000000000010141410000100c1750000100c1750000182194700c00421f7f0000040457d00000445f3f00021c63d7f00404031f7f800000002630000484027302004001863000008400710000184407304000055f3f0000085457d02000a4000000480a13f7f00400010315000000002000000080027102000000820000008000200000180406102000a0000000000a11b640400181597500001837d7f0000000053200080029d3f0000000081000000005d3300080023d5f00000841d6f00400843f7f0042020175f00080a01d3f00481405d7f00485c21f4f00400413f5f00008a11d3f00400411d7f0000000057d00400011d7f000000109560040001095500000000055),
    (39, 0x800004000000000840000080b88401419f4f0100020206000004050c000008001808141455d0002818afa02050315f4000000029000000016100000036ee00000840480000001b0000000032100010000020002000080000404190000083bb77000002000600000365dc00001fcbbc00001011100000000030000036ddc00000000000000100000000000000000008485a0000000110000000000800002800200000f6ccc20001fdbb8000010363000000008600020065dc200c1dcbb800004336700000206c6000407e5dc0000035bb800000035500020282aa00000d8d5c000004109400185b97780000866ee0000040908000808021000001033280014106e40000000000000000001000001017280000062821004866d1c2001089ab040020137708004226ee00000409000000000004000010112),
    (45, 0x171a8fc0000018143c008005c2a1e0000026150d00000410ea7800014107dfc004088d7efe00001005d7f00100217fbf800000817dfc00c0085fefe00001441d7f00300e31ebf800804081dfc000080002e60400000016102002620fbfa000100844c8000000006c20000000036100000420190800002100d80000090906c600000c7bf7f000000080a18000840375fc0000287fafe0408001015100000000028810001837dfc00800c7fefe00000010363000000000a18000021075fc008030f7afe000008c1f7f00050021bb7800000040d8c0010283fafe00004006f7f000000023ae800000037dfc0000806cebe0008001835300040e2debf80008010ddfc000000206860000101014300040208199800282860dcc0000010004000000000003000000080b981000000c58400902c33e9e0040025137f00210100bbf802002807dfc00840422efe000004103410000200010000001104044c0100000068400001c18163),
    (46, 0xa00000a37dfc804002bff3f800000150584000010c056f8000023075be000010a157f0010023ef5fc0000100c57d00008010dcfc00004006f3f001080805cfc00000040021000000184d94000000000010000000065dc0000086bb3700000000655c0000002f9370000000065dc00000000000000000000858000000040000000008b6ccc0040023fb378000001101840000000016780000200659e000010211370010021ee4dc0000000000000000000000200001014115000000000002000010141010000040305d40000100c17500000010ccdc0000000000000000000000000000000014000000000000000000000008000000504040000000411500000001acdc0040020133700000208641c0000104856d0000000314f48002086bd3f00000421157c000008c453d003002a0fcfc0000026753f20000229f4fc000000005130010040374fc004008c3f3f000000801c7c004048a1d0f00000094d47c000000431070000009844141000026151d),
    (44, 0x80d83400020c4fd3f0000423551f0000001000100000000021000002509110000020032000000250910000000000000000024091000000000822000012559130000023511700000000000000000000000000021091100000200000000002009100000000000000000200800000000008020000125591300001217914000052d7d1c0040025553f00400215137000012431140000124351c00000807d3f00000005f1f00c00003f1f00400023f1f00000005f5f00c00007f5f0000000451e80800002f1e00800006f1e00004005d1f0000000053f0040002151f0040002351f00400007f5f00000006f5f00020041f2f00620023f7f00000041f7f00620043f7f0002004052e0022004272e000008400200002084072e00000841d2f00600843f7f0000004056c0020004276f00000040161000010e176f0000400016180004841f7f0000084006102004848161800008fbf7f00020805d5f0000083fd7f),
    (35, 0x44400000000000428189000847977000000000000850c0c00022d9b80000002000108042400280c4dc0043bc9b800a1001300102042200200008400000d9b800a0021280146766e00280088000000100000002a0008100040000000084c00000000040201b778014276ee00004000800c080098000103560014000000000000000000140000080020000000040000000000000100183000a0000000140760c0020060c80040000100000080200100326e0000000000000000000084012700008200000010441c00021883c0081793700100f22e0000000040042419980000012000109066800000000000420181000001812041898266002020084000000800008002340000000000020000080000040100084c032),
    (38, 0x10200c880000002220012140cc80048c7d7f00000008880042143230010117cfc0000002220012140cc8004a0313f00121df4fc020a10113000002000400081031100020004c4080205f3f0002840cc8400a37f3f0082840cc0000000220208000ac000008103302000000ccc0000002002000857dfe800a04330100285fdfc000010002000704044c00141435f0082800440000000000008000a0000008003102000000c8080020431e00028004c2800a04230000281fcf800080193200000000000008400020000102008000805d3f000000148800084452f000010444040004111f000010d4fc400817d3f00000060080000103430002840c4c0018359770004094ddc0000000000000000000000010303000004000c000000002000280084c0008359570000016ddc000000000),
    (44, 0x8106977f000000183320040087bf3f00800000330028008403300042085bf7f00800000210000000001300280084023000000843f3e0040085bd3f000000000000000000000000000840041000008501210000104816500001069377000000183220040082bb3700000000020000008003000040081bb7700000000000000000000000000080020000000803b060040085b9370000084b9270000084bd3f00000041f2f00420023f3f00000041f7f00420043f7f0002004372e0000000053f00000041d2f00400843d3f0000004376f00c00003f1f00000005f1f00400023f1f00800005f5f00c00007f5f80800002f1200800006f1e00000005d1f0040002351f00400007d1f00000006f5f000000018220000409036300020a1031300005cb5d7f0008142577f800000000400000000002280004010323000000101030080000020200020a103130002002bd3f00004835d5f00004005f7f00000000222),
    (40, 0x21000000000080000100030000000000000000800080000100110000000000000000000000000000000000800003800000333384000013338000010117800083990700000000004000000263000000000040000000420000008000c0000100500000000000c001810042400001337700002000004400211377c00183994700000000000000000060000000000000000000420000008000800001025300000000008001810043c0000033770000000000c400201377800183994700000400400000000000000084802100000000008000014003000000800080002142130000001800000000000000010010000000840003800081011700000100000000013333000000000004000113330000000041800001000000000000000001800000000181000100000000000000271101000083990300008001040000800104),
    (40, 0x20000000000000000a0020000000018020000848023000000000000002010008001219124800085b92700000000000000a0021300000000000000a0021000000000000000a002000000001800000000000000000410008000814013000000020000000313770000000000000000000000000000008000054000004005c03400002050000001253114000081f9178000021377000000000000000000110000001800000000021000000000000000000000000000002000000400008000014012800081f91700000000008000010021000000000080000102630000000002000000000000000000020000840022000000000000000000000000000000000000000000000000000000044020000005c1340000000000000007937780000100000000000000000000000000000440000000854034800085b9270000000000),
    (40, 0x400a01b472000a01b060000a003060000053127000000c117000000e91700008119370000013807000180810300000080020000000000000000000300000000000000000000000000000000000000030000000000000080100300000000000001202003000000000000000110070000813907000080000000008000000000002000060083380700008100070400061107040080190700000002220000000022840005137780008400200000010020800085b9678400011313800081f9138400015377800100c155000101c155800103f957800001333384000113230000229121800087b923800001332384000113338400a39b0300000102008000a002008400a19b47000000000200000000000000a002000000a00302800001312304000611038400819903800002937700000000008000a1022300000000008000a10220),
    (38, 0x403055400101db7700040be55c00000991700000be45c000009937000000000000022fb1710008becdc0000000000000000000000000004000000000000004410000000000000000441210000030454000000014000000000400001000000000400000000440150000040000000010000000011048400000c13500000304d40000573371000944c9c000859b3700000000000000138170000000000000000011100004e0dc000000000000000000000000000000001500500000000000000150084000000000000000000000001401500000500d400000000000000000004008119370000000000000000031000000000000000000110000460dc000850125000082c45c000221125000218e49c000053327000003ac5c4002113370002846cdc400a21b078002806d1c000a11b77),
    (35, 0x2e0200000140000302800000405000000000a00401015c00000013800000000000000040000000014008020a280000c15500000004600002e5dc0000609a80000000000002020100000655c000000000000000008000022aa00004640200000cb180000401401008802800000000000800022800002000000000000000000000000000820000101410000000000000400040080202a0000000000000000010040000100000000000000000000000a00900401655c000220908000000000000000000000000840000000000001014100000000000004001e00802cb38000000000000202000040104140080a0a080001014100203b2ee0000000400000800800001010000202802a0040505040000200a001015957),
    (46, 0x820081fcfc02080a43f3f000202807cfc00600a21f0f008002807d3c00000a11f7f00a00085fdfc02800a41f4f002002807dfc00600a01f4f0000101074fc00200053d3f00000001747c0020000fd1f0000020474fc00000017d3f00000606148c0000001c0020000000400000000201042700000a05408c0000000000400000484808c000000000000000000440bc00000853d3f00000200e040000000000000000020080c0000000478300018021cf63c00000811d3f00180018543c00600801d0f000000040d8400400041b7700000004048800400041977001000944dde00000850302000002140c0a00000849977000002166ddc0000084396700000002ecdc0000000c135000000000000000000000000000001104840000000c1550000000b8d5c0040021d317000002076cdc0000080f9170010000365dc0040021d37700000005055c0040100db570000000aeddc0000000e1350010000365dc0000000011200100403655c00000000000),
    (37, 0x80400afafd824037d7c408057efe0000c453d110007e9f90100365fc0000192bf00000cd5f202002ebf800000357880200babe000004d5f0000026af800001357c80801befe40100df7f000006fbf8004077dfc008017efe00101df7f302002fbf9804017dfc400009efe20102fd7f110044e8f88800bf47c540013e7e08022ff3f300117f9f800000600000000060000000000000000028700000000000000886000000000000000220918000007c7c44011ba3e22000dd3f11002bf9fa000907cbcc004a3e7e000859f3f000000001008004f47c000000020000001d33240009f9f80000514f4000000000400851f3f0000082989012147cfc0010a3e7e22020b51f100110a9f880218f4fc000183e7e200053f3f000002f8f880003fc7cc40423e3e000a11f3f),
    (56, 0x400042787f0000000002425f00000000205a7f00004400427a7f0000000004046f0000000002287f0000440146387f0000000000005f0000000000387f0000048000387f0000000104007f0000000000006f0000000100024f0000000102127f0000000024301f0000000000300f8400000004000f0000040024100f0000000124100c00000000000a7f0000040000087f00000600000aff000002000068ef00000600000aaf020102000048ad000002000068af00000200002aaf00000600000abf00000600004a8f0000020000288f0240020000408f0000020000488f0000020000488c0000020000180f00000000010363000006200c1f7f00000000010322000006800c1f7f00000080241f6f00000600251f7f000002000c0f7f00200000850322000000008d032200200000849d7f000000000c1f7f000000008d9f7f00100400ac1f7f044004048c1f7f04000000ac1d6d005000008c5d6d000000008c1f7f00000200843d7f0000020440bf3f000000000c453d0000022000dd3f0000020002ff5f00000004205f1f0000060021df3f00000000c1df3f0000000040df3f0000020080fd3f0000060400df7f00000004205f5f0000060021df7f),
    (50, 0x1108100000000000000000080310018000000001800000004013083800000000180000000403300bc0000000000000000000000090000000001a0f000088031607c00000000001400000000000040000000000000000000110074000000000000000000000000000000000000000000401300b400000000403d00008801160fc0000000c5a3f000088011e9fc000800241a2f00018001068fc00402004783f001120011e8fc004000041a2f000008000f4fc00000000053f000100000fcfc00000204052d000080211a0fc00002000303f804000080007e01000022002d00000008840fc00020006383f00000001068bc000200043a3f000000001687c000200207a1f00018808068fc004000201a3f000180088683c00000800183f000180000603c00000000401f00000000008fc000440003a3f000000001687c000400023a1f000000001607c00040000781f000000001a97c00000004402f00000000008fc000000041a2f000108008e9fc00000004182f000100010e0fc00000004326f001001118e9fc00440002305f),
    (35, 0x1000040e0000181580000212900100425f0000000000000000000000000000000002700000000000000008008806127800005a7f00000004e01000e9fc0000201e80000000080200b4be0000000000000010100000000000000000500000417e00102d3780000421c010088038000000000008001268000020020020084bc0000000020080010700000000000000a41d00481697c080260168000000000000004040000000000400000000000000000000000800000000000000000000000000000000000000000010000000000000000000000000000000000100000000700000002f00000040404000143e00802d37801005a7f40204f0fe88031607d10033c1faa0045a3f00000000220089e8ff00133d1f800000000),
    (39, 0x4001693e00008852fc101031e5fc002201f3f0c04443d1e00001078bc210011f1f800004366f000000bc3e100008f87c00000372fc004463e7f88000468bf000109f1fc000002f3f800002465f880084fcff100d18f1fc000810b3f8604001b3f040101f6fe080020ecfc700000d9f820022933f04010d767e080020ecfc700000d9f8600a29b3f04010016fe080800723c310060d3f86800c1a7f01004834de18001069fc000060d3f80400c1a7f04000870fe081111e8fc110022c1f800000000000000004040000000000000000000001004c22f000000b43e080019e87c002102d0f8600205a3f800000807b000101687c100003c1f8604205a7f000840b4be18008169fc004802d2f800000455f0c0200b4be081019e9fc110023c1f8400005a7f080200b4fe000000080800000010b8008000000),
    (49, 0x101021e7f800081102fafc00044001b97e000010005f1f000100017fcf8000010817c7c000c0000bd7e004000405f1f000100003e5f8001810037bfc00000840bebe000604005b7f000300002f7fc000020017d7c000c0201bdbe00020402beff000110007e5f80018100175fe000c0200babe00000400000200000000000b000001000900200000000080400000400041e0000040000030000000000008000002008a1c0000000004000000000002000000000001010000000009abe000200004d5f000102001ebf800080401357c00082000befe000411005f7f000008002fbf800005000fdfe00002200befe000201027cff000110044e4f80008800bf27c000540013d7f000200227f1f000048113f9f80018008bfafc000000000000000000000206000000000000000000002001800000000000000000004460c00000000000000000801110bc000000003e1e00022008dc9f000110006e5f8000000317cfc00044008fd7e000800241f2f000300020f5f801008000f47e008900007e7e004002041f2f),
    (39, 0xb83e00000010fc200001a0f8600007d1f0c1000fe3e000001787c200005f0f8000005f1f0000000a7e100002fc7c00000378f802020463b0000483c7e108010fcfc030102f9f8460007f3f004040bc7e188881f8fc000120f9f8440003e1f0c40087e7e1000805cfc10042079fc20484bf7f840001fafe0000013d7e300007fbfc200007d7f0c00002aff180212f5fc20000238f8000000d350401007e7e000011345c100400a8b8600807d1f0401009a7a0000003c7c2005007878200800f7f08100425fe000558ebfc2000909ff8051527bff08100425fe084d49ebfc2000b09ff8211563fff0c26a431fe00204009c030cb10dff86080202ff0822a43bfe0004080ffc001010e0780200803260c40183dfe0200200c98340060f7f8080241f6f0d000836fe1800107bfc000060fbf80420c1f7f),
    (49, 0x100431e9f80000001071bc00000084787e000000005c5f000008011e0f80100080071fc0008020c281e000602021c0f000004135f9f8000000107dbc000000847e7e000000005f5f000208011faf80000a089fcfc00000000bebe000010023f1f000000020fb7800080108fcfc000011403efe000608a21f0f002001100f3f800100888783c001001087efe000000000000000400800029800000000014c001000080a0600000000000000000000000000000000000020010000000a6000000000000000000000000002200d00016c000000000000000801240813000000020a898000000000000000000000000000000000000000401401009800200201fdfc000000081060000000803030000000000800000000200f44c001c010c7b1e000800801f7f000200410e8780000800118ec00040000bc7e000200005e3f00000002231d80000000010fc00000008385e000602043c3f000304021f9f80000001078bc000840007c7e000000041f2f000210001e9f800000010dcbc000008008c7600000400463b),
    (44, 0x80000241f6f00400061f7f00000085e5f00010027f1f00020427c3f80000000043000000002038000000000000000000203008000002170000040030700000000000008000000000000084072b0000000020200400041f7f00000000201000000020030000004032a00400041f7f00000041f7f0000000001600020003d7f00000000a790000000000100408003f7f0000000443d0000000443d000000000000000000000000400841f1f00000000000000000000000000000020200000000000000000000020000000005700400841f2f0000000020100000400249000004000150000000000000000400005000000000000080000021100000000000000000002070000000200200400841f5f00000000000000000444290000000000000000044429000000000000000000020200000000000000000000000000000000000000000001000000000000080000000b0000000020200400841f2f00000841f7f),
    (50, 0x110109f4fc00400000441d000008109707c002000005f5f000010408547c000450025f1f0001150097cfc000004205f5f0001000097cfc0000000000000000000000808000000000000000000000000000000004472b00000001179fc000220467e3f0000100217dfc000040085f7f000000009f4fc000408025e3f000011108787c000206463e3f000002119707c000000000001000080810f17e40000180001f000080408d07c000602467c1f000001000f1fc00000000005f000100401f17c00000100445f001001000f9fc00000000185f000000000415c004400007c5f001000001797c00000126343f000080809f0fc000020429d1f000088108f4fc000200003f7f00000a1087c7c000208083f7f000180108fcfc0000000000000000001020804000000000000000000111102c0000000000000000000020804000000000000000000000000c0000000000010000000000000000000005e4f00000810b707c000020425c3f0001081187cfc0000000002230000000101dbc00000000002300000001075bc000400461f3f),
    (49, 0x100046f2f80208400b7c7c00040010befe00000000001180000000000a800000021394400000000bcbe000210025f3f00000000000a8000000817d7c00040004be7e00000008ca5b000100006d0f800000001286600040000b67e00000000ce1b00000004672d8000000000044000000009c22000200005f3f00400000670d8000800217dfc00040010befe000000085f7f000100142f9f8000800a17dfc00000050befe000400227e3f000000000000000000100001400000000000000000040050d0000000000000000000130014000000000000000000000101000000000ea780000110b707c00000085b87e000004045d7f000000233e9f80008201874fc001000008876000000000000000500420ebf800000000000000000080002200000000003f00000020002780028081074fc001004083ade00040102143f000201031e1f80000810af07c000000017cbe00000008be7f000200215f1f80010201878fc008004093cde000002063c3f000022211f9f800000000080c000080007afe00004102353f),
    (44, 0x201504f7f00601507c7f00608707f7f00001507c7f00000005c5f00601007c5f00608007f5f00000006f5f00000041c6f00602043eff00608043fff000000427ef08211543f7f08211507d7f08610707f7f08601d43d7f0000014377f00000106f7f0040030177f00201101d4f00000841f7f0020404bf7f00001005d7f0020000fd7f00000205f7f0060000ff7f00204003d7f00000841d7f0060184bd7f00201800f7f00001141f7f00213543f7f00009105d5f00211507d7f00000305f7f00200304f5f00610707f7f0000b141d6f0000114056f00603543d7f00008106e7f0000814367f0040830167f0020b101d4f00003021ccf00244461f3f00040841f6f00200061f3f04000041f7f00206461f3f00004041f7f80006041f7f00002063e3f0000400443b0000042dc3f00000085d5f0041002ff7f00208025d3f00020085d5f00000027c3f0000400443b0000042fc3f0000008ce5b00000204e5b),
    (54, 0x100417d7c0000451125ddf00001150497ffc0000410325fff00000100491ffc0000040105f7f00000104417dfc0000011127dff00001060c97bfc0000044521edf0000081858fbfc0000008165cdf0000180c59f37c0000004103e7f0000104441f17c0000001105e7f0000084c49f3fc0000020529ddf0000088048f7fc0000008121fdf0000180048fffc00000000000000000000000090c00000000000000000000011010c0000000000000000000000019200000000000000000000800011280000000001e5f000000810b737c0000020425cff000052815877fe0000000000262800000200001880000008141f6f00001001587ffc0000400761fff0000008109f3fc0000420041dff000000000055a20000400441fff000000801057b40000000000240000000000001800000400541bff000040815057b60000408061fff00000200581ffc0000420541f7f000000000009000000408541f7f00000001507dfc0000020103d7f0000102040fdfc0000000941f7f0000080758f7fc0000000127cdf0000000c4071fc0000603121ccf80000022c07d3c0000008a01f7f00001826c87f3c000040070577f),
    (55, 0x8325e00001002186efc0040000120d9780000400861bbf0000010008044600000000000004000001042003580000000000203000001000826da000012801865fe00000000211004000002004000a00000000000043000000000044a4000000000000000001000000203000008000c367e000000801845b40000010031caf80000000000741000008000c76fe000000041845b40000280020d9f80000500041b3f0000020008367e0000048000e47c000000000050c80000508003b3f00000a0108363e00001402106c7c0000080420d9f80000000085a1f000000000cf53e0000008019e2fc0000100431cdf8000000000581f00000c0000f03e000040000060fc0000300010c478000420404bb3f0000840001f27e00000000013c7c0002300007d9f8000420000393f00000c0000227e0001180212e4fc000010040059f8000020002111f000000000c603e00009000004c7c000000013188f8201000026101d000000004c603e0000000008c03c20080000300078000040006100f000000004c20120000000008623c0000010095e6f80000408761eff00000004293cfe0000000d58f3fc0000022091fff80000020425cdf),
    (52, 0x420a041d3f0000000006b5f00000000060380000002043caf0000000006b1f000002006f89f0000408061abf0004000049a2f00000000638bf0000044067bbf000002006589f0001000005b1f840000000011f000004002111f0000440025b9f0000444225bbf0000004205b1f0000400225bbf0000040085b3f0000040085b3f0000100045a3f0000220067aff00000000279bf0000408225abf0000044065abf0000204067abf000000806589f000060006789f0004004047a3f000000004581f000440004781f0004000005a1f0000004003c3f0000000000447000000004400f0000400007c1f000000200441f000000026703f0000004003abf000000000005f200100000081f000040000289f201000000103f201040000001f201020000001d00002000008bf00002000278bf000002006d9bf00002200679bf0000028065b9f0000600067bbf000000000000000000000442030000000001800000001004400b00000000000000000000444201000000000000000000200440030000000001a0f000002006d89f00000200658bf0000420861bbf0000000000023),
    (49, 0x820000000110d7c0000000000000000000000000000000222938000000017dfc00840004befe000400027f7f000202012bbf8000100017cfc00000004fefe00040802567f000000000101000000000000000000000040400000000025b0000000000000000000000002000000088c4e000000005e5f000101033f3f8000004185dfc0001000c2ede000608041f3f000000020bb682009001875fc0040c00006ce000608041f7f1000244201b38000020000c10000050882ada000060842360001110021ab6800000000088c0018000c3efe0000000002030000004201b380000001069fc0004800c3afe000240041d3f000304002f9f800000101787c00040000fe7e000608005f7f000000006fbf800080009fdfc000401081efe00400806167f0000510201338001a081079fc00400000348a0000000003450000010201338000000000904000000003406000408061e7f0000000001018000002100d9c0000000834fe00008000020400101042013200008811051b4000400080eda000202061c7f),
    (49, 0x3edf801000009fbfe00008000bcbe000202047cbf00080000012180000c10b617c0000608db03e00003042d85f000800200101800008100000c00006085b03e00000014c05d00000022600e80008c113607c00046089b23e00023040d81f0000000800a2800000100051400046081b23e00000000401800000000201c0011000105cfc008400081efe00000004162f002300020f9f80010001870fc0080000c38fe004000000167000250020f378001000105dbc0080100006ca00040a041e6f000000000001801000000040000010000044e0002a8041d6f0010600001938000082100d9c0000000000ca0002a0041d6f0001000207b780000801059bc0084500c3efe000620041f7f000240030f3f800000000098c0000000832fe20200004366f003010030b37800000000051440000000440c2000080003470000000001b380000a010099800409000048e002000000367001304020fbf80010001879fc0000000c38fe000020005d1f000104012ebf800000009f5fc000000000208000000000000),
    (44, 0x8002575f00608005f3f0000000455d0030022153f80300025d7f00608005f7f004000a1f7f003000a5d7f08200005d3f00608005f7f00000085e7f00200007f7f00200804f7f0400802565f0060000de5f004080a1e7f00000004d5d003000a5c7f04208005d1f000000463ff00000007c1f0000102535f00100085b5f01400007b7f0000008595f00400047bff00608001b7f00000085a5f00200847fff000000478ff00000145b1f00608001b1f04200847b9f0000006789f00608005b7f000000c5a5f00200007b7f00608001b1f00000015a1f00200027b1f00200804b5f00000127a5f0140002125f04000067adf0000004789f0000124301800400000bff000008038ff00400000b9f0000082289f00000020adf0000000289f000008008980000000789f00004005d1f00400007fbf04200007fbf00010405f1f00000007cbf00000105f7f00000027cff00000085f3f00000027fff00050005f7f),
    (57, 0x1e07c000004100432be0000000012795f000000008309b7800001820006c7c0000000080b43e00000200007b5f000001004205b780000000010e0bc0000000000f8fe00004000027e7f00000000003e1f8000000000100600000880000ae3e00004200004f5f0000000000230dc0001180001747c0000080004b83e0010000002041b80000200010a0f8000100008850640000800004b8be0000040000575f000001000027af80000100081596c00008410043efe00000000001e5b00000300802eaf8000014042979fc00000c10003efe000005040a5e7f00000000052e3f800000010017cfc00008400043efe00000000027f7f00000204010b3f8000000002178fc0000000004fefe0000000102577f)] 6
def cert_ref := symDagRef cert_mask cert_goal 2599 3 cert_syms cert_trace cert_links
def cert_check : Nat → Bool := fun i => checkNodeViaF cert_mask cert_goal (chooseBounds cert_bounds (cert_profile i)) cert_trace cert_ref i
set_option maxHeartbeats 0 in
theorem cert_roots : dagCheckRootsF cert_mask cert_goal cert_bounds
    (cert_ref 0) cert_stock 12 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row0 : treeBlockF 0 4 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row4 : treeBlockF 4 8 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row8 : treeBlockF 8 12 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row12 : treeBlockF 12 16 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row16 : treeBlockF 16 20 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row20 : treeBlockF 20 24 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row24 : treeBlockF 24 28 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row28 : treeBlockF 28 32 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row32 : treeBlockF 32 36 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row36 : treeBlockF 36 40 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row40 : treeBlockF 40 44 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row44 : treeBlockF 44 48 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row48 : treeBlockF 48 52 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row52 : treeBlockF 52 56 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row56 : treeBlockF 56 60 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row60 : treeBlockF 60 64 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row64 : treeBlockF 64 68 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row68 : treeBlockF 68 72 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row72 : treeBlockF 72 76 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row76 : treeBlockF 76 80 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row80 : treeBlockF 80 84 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row84 : treeBlockF 84 88 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row88 : treeBlockF 88 92 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row92 : treeBlockF 92 96 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row96 : treeBlockF 96 100 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row100 : treeBlockF 100 104 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row104 : treeBlockF 104 108 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row108 : treeBlockF 108 112 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row112 : treeBlockF 112 116 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row116 : treeBlockF 116 120 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row120 : treeBlockF 120 124 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row124 : treeBlockF 124 128 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row128 : treeBlockF 128 132 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row132 : treeBlockF 132 136 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row136 : treeBlockF 136 140 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row140 : treeBlockF 140 144 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row144 : treeBlockF 144 148 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row148 : treeBlockF 148 152 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row152 : treeBlockF 152 156 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row156 : treeBlockF 156 160 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row160 : treeBlockF 160 164 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row164 : treeBlockF 164 168 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row168 : treeBlockF 168 172 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row172 : treeBlockF 172 176 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row176 : treeBlockF 176 180 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row180 : treeBlockF 180 184 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row184 : treeBlockF 184 188 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row188 : treeBlockF 188 192 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row192 : treeBlockF 192 196 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row196 : treeBlockF 196 200 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row200 : treeBlockF 200 204 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row204 : treeBlockF 204 208 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row208 : treeBlockF 208 212 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row212 : treeBlockF 212 216 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row216 : treeBlockF 216 220 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row220 : treeBlockF 220 224 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row224 : treeBlockF 224 228 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row228 : treeBlockF 228 232 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row232 : treeBlockF 232 236 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row236 : treeBlockF 236 240 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row240 : treeBlockF 240 244 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row244 : treeBlockF 244 248 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row248 : treeBlockF 248 252 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row252 : treeBlockF 252 256 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row256 : treeBlockF 256 260 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row260 : treeBlockF 260 264 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row264 : treeBlockF 264 268 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row268 : treeBlockF 268 272 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row272 : treeBlockF 272 276 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row276 : treeBlockF 276 280 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row280 : treeBlockF 280 284 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row284 : treeBlockF 284 288 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row288 : treeBlockF 288 292 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row292 : treeBlockF 292 296 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row296 : treeBlockF 296 300 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row300 : treeBlockF 300 304 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row304 : treeBlockF 304 308 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row308 : treeBlockF 308 312 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row312 : treeBlockF 312 316 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row316 : treeBlockF 316 320 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row320 : treeBlockF 320 324 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row324 : treeBlockF 324 328 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row328 : treeBlockF 328 332 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row332 : treeBlockF 332 336 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row336 : treeBlockF 336 340 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row340 : treeBlockF 340 344 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row344 : treeBlockF 344 348 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row348 : treeBlockF 348 352 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row352 : treeBlockF 352 356 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row356 : treeBlockF 356 360 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row360 : treeBlockF 360 364 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row364 : treeBlockF 364 368 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row368 : treeBlockF 368 372 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row372 : treeBlockF 372 376 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row376 : treeBlockF 376 380 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row380 : treeBlockF 380 384 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row384 : treeBlockF 384 388 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row388 : treeBlockF 388 392 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row392 : treeBlockF 392 396 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row396 : treeBlockF 396 400 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row400 : treeBlockF 400 404 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row404 : treeBlockF 404 408 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row408 : treeBlockF 408 412 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row412 : treeBlockF 412 416 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row416 : treeBlockF 416 420 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row420 : treeBlockF 420 424 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row424 : treeBlockF 424 428 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row428 : treeBlockF 428 432 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row432 : treeBlockF 432 436 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row436 : treeBlockF 436 440 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row440 : treeBlockF 440 444 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row444 : treeBlockF 444 448 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row448 : treeBlockF 448 452 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row452 : treeBlockF 452 456 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row456 : treeBlockF 456 460 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row460 : treeBlockF 460 464 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row464 : treeBlockF 464 468 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row468 : treeBlockF 468 472 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row472 : treeBlockF 472 476 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row476 : treeBlockF 476 480 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row480 : treeBlockF 480 484 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row484 : treeBlockF 484 488 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row488 : treeBlockF 488 492 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row492 : treeBlockF 492 496 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row496 : treeBlockF 496 500 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row500 : treeBlockF 500 504 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row504 : treeBlockF 504 508 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row508 : treeBlockF 508 512 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row512 : treeBlockF 512 516 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row516 : treeBlockF 516 520 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row520 : treeBlockF 520 524 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row524 : treeBlockF 524 528 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row528 : treeBlockF 528 532 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row532 : treeBlockF 532 536 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row536 : treeBlockF 536 540 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row540 : treeBlockF 540 544 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row544 : treeBlockF 544 548 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row548 : treeBlockF 548 552 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row552 : treeBlockF 552 556 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row556 : treeBlockF 556 560 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row560 : treeBlockF 560 564 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row564 : treeBlockF 564 568 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row568 : treeBlockF 568 572 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row572 : treeBlockF 572 576 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row576 : treeBlockF 576 580 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row580 : treeBlockF 580 584 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row584 : treeBlockF 584 588 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row588 : treeBlockF 588 592 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row592 : treeBlockF 592 596 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row596 : treeBlockF 596 600 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row600 : treeBlockF 600 604 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row604 : treeBlockF 604 608 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row608 : treeBlockF 608 612 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row612 : treeBlockF 612 616 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row616 : treeBlockF 616 620 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row620 : treeBlockF 620 624 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row624 : treeBlockF 624 628 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row628 : treeBlockF 628 632 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row632 : treeBlockF 632 636 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row636 : treeBlockF 636 640 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row640 : treeBlockF 640 644 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row644 : treeBlockF 644 648 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row648 : treeBlockF 648 652 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row652 : treeBlockF 652 656 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row656 : treeBlockF 656 660 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row660 : treeBlockF 660 664 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row664 : treeBlockF 664 668 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row668 : treeBlockF 668 672 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row672 : treeBlockF 672 676 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row676 : treeBlockF 676 680 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row680 : treeBlockF 680 684 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row684 : treeBlockF 684 688 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row688 : treeBlockF 688 692 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row692 : treeBlockF 692 696 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row696 : treeBlockF 696 700 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row700 : treeBlockF 700 704 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row704 : treeBlockF 704 708 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row708 : treeBlockF 708 712 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row712 : treeBlockF 712 716 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row716 : treeBlockF 716 720 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row720 : treeBlockF 720 724 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row724 : treeBlockF 724 728 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row728 : treeBlockF 728 732 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row732 : treeBlockF 732 736 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row736 : treeBlockF 736 740 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row740 : treeBlockF 740 744 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row744 : treeBlockF 744 748 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row748 : treeBlockF 748 752 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row752 : treeBlockF 752 756 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row756 : treeBlockF 756 760 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row760 : treeBlockF 760 764 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row764 : treeBlockF 764 768 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row768 : treeBlockF 768 772 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row772 : treeBlockF 772 776 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row776 : treeBlockF 776 780 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row780 : treeBlockF 780 784 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row784 : treeBlockF 784 788 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row788 : treeBlockF 788 792 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row792 : treeBlockF 792 796 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row796 : treeBlockF 796 800 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row800 : treeBlockF 800 804 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row804 : treeBlockF 804 808 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row808 : treeBlockF 808 812 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row812 : treeBlockF 812 816 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row816 : treeBlockF 816 820 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row820 : treeBlockF 820 824 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row824 : treeBlockF 824 828 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row828 : treeBlockF 828 832 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row832 : treeBlockF 832 836 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row836 : treeBlockF 836 840 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row840 : treeBlockF 840 844 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row844 : treeBlockF 844 848 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row848 : treeBlockF 848 852 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row852 : treeBlockF 852 856 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row856 : treeBlockF 856 860 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row860 : treeBlockF 860 864 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row864 : treeBlockF 864 868 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row868 : treeBlockF 868 872 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row872 : treeBlockF 872 876 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row876 : treeBlockF 876 880 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row880 : treeBlockF 880 884 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row884 : treeBlockF 884 888 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row888 : treeBlockF 888 892 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row892 : treeBlockF 892 896 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row896 : treeBlockF 896 900 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row900 : treeBlockF 900 904 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row904 : treeBlockF 904 908 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row908 : treeBlockF 908 912 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row912 : treeBlockF 912 916 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row916 : treeBlockF 916 920 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row920 : treeBlockF 920 924 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row924 : treeBlockF 924 928 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row928 : treeBlockF 928 932 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row932 : treeBlockF 932 936 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row936 : treeBlockF 936 940 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row940 : treeBlockF 940 944 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row944 : treeBlockF 944 948 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row948 : treeBlockF 948 952 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row952 : treeBlockF 952 956 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row956 : treeBlockF 956 960 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row960 : treeBlockF 960 964 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row964 : treeBlockF 964 968 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row968 : treeBlockF 968 972 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row972 : treeBlockF 972 976 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row976 : treeBlockF 976 980 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row980 : treeBlockF 980 984 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row984 : treeBlockF 984 988 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row988 : treeBlockF 988 992 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row992 : treeBlockF 992 996 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row996 : treeBlockF 996 1000 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1000 : treeBlockF 1000 1004 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1004 : treeBlockF 1004 1008 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1008 : treeBlockF 1008 1012 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1012 : treeBlockF 1012 1016 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1016 : treeBlockF 1016 1020 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1020 : treeBlockF 1020 1024 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1024 : treeBlockF 1024 1028 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1028 : treeBlockF 1028 1032 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1032 : treeBlockF 1032 1036 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1036 : treeBlockF 1036 1040 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1040 : treeBlockF 1040 1044 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1044 : treeBlockF 1044 1048 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1048 : treeBlockF 1048 1052 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1052 : treeBlockF 1052 1056 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1056 : treeBlockF 1056 1060 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1060 : treeBlockF 1060 1064 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1064 : treeBlockF 1064 1068 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1068 : treeBlockF 1068 1072 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1072 : treeBlockF 1072 1076 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1076 : treeBlockF 1076 1080 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1080 : treeBlockF 1080 1084 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1084 : treeBlockF 1084 1088 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1088 : treeBlockF 1088 1092 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1092 : treeBlockF 1092 1096 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1096 : treeBlockF 1096 1100 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1100 : treeBlockF 1100 1104 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1104 : treeBlockF 1104 1108 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1108 : treeBlockF 1108 1112 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1112 : treeBlockF 1112 1116 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1116 : treeBlockF 1116 1120 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1120 : treeBlockF 1120 1124 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1124 : treeBlockF 1124 1128 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1128 : treeBlockF 1128 1132 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1132 : treeBlockF 1132 1136 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1136 : treeBlockF 1136 1140 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1140 : treeBlockF 1140 1144 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1144 : treeBlockF 1144 1148 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1148 : treeBlockF 1148 1152 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1152 : treeBlockF 1152 1156 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1156 : treeBlockF 1156 1160 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1160 : treeBlockF 1160 1164 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1164 : treeBlockF 1164 1168 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1168 : treeBlockF 1168 1172 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1172 : treeBlockF 1172 1176 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1176 : treeBlockF 1176 1180 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1180 : treeBlockF 1180 1184 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1184 : treeBlockF 1184 1188 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1188 : treeBlockF 1188 1192 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1192 : treeBlockF 1192 1196 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1196 : treeBlockF 1196 1200 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1200 : treeBlockF 1200 1204 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1204 : treeBlockF 1204 1208 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1208 : treeBlockF 1208 1212 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1212 : treeBlockF 1212 1216 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1216 : treeBlockF 1216 1220 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1220 : treeBlockF 1220 1224 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1224 : treeBlockF 1224 1228 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1228 : treeBlockF 1228 1232 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1232 : treeBlockF 1232 1236 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1236 : treeBlockF 1236 1240 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1240 : treeBlockF 1240 1244 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1244 : treeBlockF 1244 1248 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1248 : treeBlockF 1248 1252 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1252 : treeBlockF 1252 1256 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1256 : treeBlockF 1256 1260 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1260 : treeBlockF 1260 1264 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1264 : treeBlockF 1264 1268 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1268 : treeBlockF 1268 1272 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1272 : treeBlockF 1272 1276 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1276 : treeBlockF 1276 1280 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1280 : treeBlockF 1280 1284 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1284 : treeBlockF 1284 1288 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1288 : treeBlockF 1288 1292 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1292 : treeBlockF 1292 1296 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1296 : treeBlockF 1296 1300 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1300 : treeBlockF 1300 1304 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1304 : treeBlockF 1304 1308 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1308 : treeBlockF 1308 1312 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1312 : treeBlockF 1312 1316 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1316 : treeBlockF 1316 1320 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1320 : treeBlockF 1320 1324 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1324 : treeBlockF 1324 1328 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1328 : treeBlockF 1328 1332 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1332 : treeBlockF 1332 1336 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1336 : treeBlockF 1336 1340 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1340 : treeBlockF 1340 1344 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1344 : treeBlockF 1344 1348 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1348 : treeBlockF 1348 1352 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1352 : treeBlockF 1352 1356 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1356 : treeBlockF 1356 1360 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1360 : treeBlockF 1360 1364 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1364 : treeBlockF 1364 1368 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1368 : treeBlockF 1368 1372 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1372 : treeBlockF 1372 1376 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1376 : treeBlockF 1376 1380 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1380 : treeBlockF 1380 1384 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1384 : treeBlockF 1384 1388 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1388 : treeBlockF 1388 1392 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1392 : treeBlockF 1392 1396 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1396 : treeBlockF 1396 1400 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1400 : treeBlockF 1400 1404 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1404 : treeBlockF 1404 1408 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1408 : treeBlockF 1408 1412 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1412 : treeBlockF 1412 1416 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1416 : treeBlockF 1416 1420 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1420 : treeBlockF 1420 1424 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1424 : treeBlockF 1424 1428 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1428 : treeBlockF 1428 1432 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1432 : treeBlockF 1432 1436 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1436 : treeBlockF 1436 1440 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1440 : treeBlockF 1440 1444 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1444 : treeBlockF 1444 1448 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1448 : treeBlockF 1448 1452 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1452 : treeBlockF 1452 1456 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1456 : treeBlockF 1456 1460 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1460 : treeBlockF 1460 1464 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1464 : treeBlockF 1464 1468 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1468 : treeBlockF 1468 1472 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1472 : treeBlockF 1472 1476 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1476 : treeBlockF 1476 1480 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1480 : treeBlockF 1480 1484 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1484 : treeBlockF 1484 1488 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1488 : treeBlockF 1488 1492 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1492 : treeBlockF 1492 1496 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1496 : treeBlockF 1496 1500 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1500 : treeBlockF 1500 1504 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1504 : treeBlockF 1504 1508 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1508 : treeBlockF 1508 1512 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1512 : treeBlockF 1512 1516 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1516 : treeBlockF 1516 1520 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1520 : treeBlockF 1520 1524 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1524 : treeBlockF 1524 1528 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1528 : treeBlockF 1528 1532 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1532 : treeBlockF 1532 1536 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1536 : treeBlockF 1536 1540 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1540 : treeBlockF 1540 1544 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1544 : treeBlockF 1544 1548 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1548 : treeBlockF 1548 1552 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1552 : treeBlockF 1552 1556 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1556 : treeBlockF 1556 1560 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1560 : treeBlockF 1560 1564 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1564 : treeBlockF 1564 1568 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1568 : treeBlockF 1568 1572 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1572 : treeBlockF 1572 1576 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1576 : treeBlockF 1576 1580 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1580 : treeBlockF 1580 1584 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1584 : treeBlockF 1584 1588 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1588 : treeBlockF 1588 1592 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1592 : treeBlockF 1592 1596 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1596 : treeBlockF 1596 1600 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1600 : treeBlockF 1600 1604 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1604 : treeBlockF 1604 1608 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1608 : treeBlockF 1608 1612 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1612 : treeBlockF 1612 1616 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1616 : treeBlockF 1616 1620 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1620 : treeBlockF 1620 1624 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1624 : treeBlockF 1624 1628 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1628 : treeBlockF 1628 1632 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1632 : treeBlockF 1632 1636 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1636 : treeBlockF 1636 1640 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1640 : treeBlockF 1640 1644 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1644 : treeBlockF 1644 1648 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1648 : treeBlockF 1648 1652 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1652 : treeBlockF 1652 1656 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1656 : treeBlockF 1656 1660 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1660 : treeBlockF 1660 1664 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1664 : treeBlockF 1664 1668 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1668 : treeBlockF 1668 1672 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1672 : treeBlockF 1672 1676 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1676 : treeBlockF 1676 1680 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1680 : treeBlockF 1680 1684 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1684 : treeBlockF 1684 1688 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1688 : treeBlockF 1688 1692 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1692 : treeBlockF 1692 1696 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1696 : treeBlockF 1696 1700 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1700 : treeBlockF 1700 1704 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1704 : treeBlockF 1704 1708 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1708 : treeBlockF 1708 1712 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1712 : treeBlockF 1712 1716 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1716 : treeBlockF 1716 1720 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1720 : treeBlockF 1720 1724 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1724 : treeBlockF 1724 1728 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1728 : treeBlockF 1728 1732 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1732 : treeBlockF 1732 1736 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1736 : treeBlockF 1736 1740 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1740 : treeBlockF 1740 1744 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1744 : treeBlockF 1744 1748 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1748 : treeBlockF 1748 1752 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1752 : treeBlockF 1752 1756 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1756 : treeBlockF 1756 1760 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1760 : treeBlockF 1760 1764 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1764 : treeBlockF 1764 1768 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1768 : treeBlockF 1768 1772 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1772 : treeBlockF 1772 1776 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1776 : treeBlockF 1776 1780 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1780 : treeBlockF 1780 1784 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1784 : treeBlockF 1784 1788 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1788 : treeBlockF 1788 1792 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1792 : treeBlockF 1792 1796 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1796 : treeBlockF 1796 1800 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1800 : treeBlockF 1800 1804 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1804 : treeBlockF 1804 1808 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1808 : treeBlockF 1808 1812 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1812 : treeBlockF 1812 1816 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1816 : treeBlockF 1816 1820 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1820 : treeBlockF 1820 1824 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1824 : treeBlockF 1824 1828 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1828 : treeBlockF 1828 1832 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1832 : treeBlockF 1832 1836 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1836 : treeBlockF 1836 1840 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1840 : treeBlockF 1840 1844 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1844 : treeBlockF 1844 1848 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1848 : treeBlockF 1848 1852 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1852 : treeBlockF 1852 1856 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1856 : treeBlockF 1856 1860 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1860 : treeBlockF 1860 1864 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1864 : treeBlockF 1864 1868 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1868 : treeBlockF 1868 1872 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1872 : treeBlockF 1872 1876 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1876 : treeBlockF 1876 1880 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1880 : treeBlockF 1880 1884 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1884 : treeBlockF 1884 1888 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1888 : treeBlockF 1888 1892 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1892 : treeBlockF 1892 1896 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1896 : treeBlockF 1896 1900 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1900 : treeBlockF 1900 1904 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1904 : treeBlockF 1904 1908 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1908 : treeBlockF 1908 1912 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1912 : treeBlockF 1912 1916 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1916 : treeBlockF 1916 1920 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1920 : treeBlockF 1920 1924 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1924 : treeBlockF 1924 1928 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1928 : treeBlockF 1928 1932 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1932 : treeBlockF 1932 1936 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1936 : treeBlockF 1936 1940 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1940 : treeBlockF 1940 1944 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1944 : treeBlockF 1944 1948 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1948 : treeBlockF 1948 1952 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1952 : treeBlockF 1952 1956 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1956 : treeBlockF 1956 1960 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1960 : treeBlockF 1960 1964 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1964 : treeBlockF 1964 1968 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1968 : treeBlockF 1968 1972 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1972 : treeBlockF 1972 1976 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1976 : treeBlockF 1976 1980 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1980 : treeBlockF 1980 1984 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1984 : treeBlockF 1984 1988 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1988 : treeBlockF 1988 1992 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1992 : treeBlockF 1992 1996 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row1996 : treeBlockF 1996 2000 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2000 : treeBlockF 2000 2004 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2004 : treeBlockF 2004 2008 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2008 : treeBlockF 2008 2012 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2012 : treeBlockF 2012 2016 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2016 : treeBlockF 2016 2020 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2020 : treeBlockF 2020 2024 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2024 : treeBlockF 2024 2028 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2028 : treeBlockF 2028 2032 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2032 : treeBlockF 2032 2036 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2036 : treeBlockF 2036 2040 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2040 : treeBlockF 2040 2044 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2044 : treeBlockF 2044 2048 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2048 : treeBlockF 2048 2052 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2052 : treeBlockF 2052 2056 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2056 : treeBlockF 2056 2060 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2060 : treeBlockF 2060 2064 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2064 : treeBlockF 2064 2068 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2068 : treeBlockF 2068 2072 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2072 : treeBlockF 2072 2076 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2076 : treeBlockF 2076 2080 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2080 : treeBlockF 2080 2084 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2084 : treeBlockF 2084 2088 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2088 : treeBlockF 2088 2092 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2092 : treeBlockF 2092 2096 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2096 : treeBlockF 2096 2100 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2100 : treeBlockF 2100 2104 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2104 : treeBlockF 2104 2108 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2108 : treeBlockF 2108 2112 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2112 : treeBlockF 2112 2116 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2116 : treeBlockF 2116 2120 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2120 : treeBlockF 2120 2124 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2124 : treeBlockF 2124 2128 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2128 : treeBlockF 2128 2132 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2132 : treeBlockF 2132 2136 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2136 : treeBlockF 2136 2140 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2140 : treeBlockF 2140 2144 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2144 : treeBlockF 2144 2148 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2148 : treeBlockF 2148 2152 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2152 : treeBlockF 2152 2156 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2156 : treeBlockF 2156 2160 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2160 : treeBlockF 2160 2164 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2164 : treeBlockF 2164 2168 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2168 : treeBlockF 2168 2172 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2172 : treeBlockF 2172 2176 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2176 : treeBlockF 2176 2180 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2180 : treeBlockF 2180 2184 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2184 : treeBlockF 2184 2188 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2188 : treeBlockF 2188 2192 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2192 : treeBlockF 2192 2196 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2196 : treeBlockF 2196 2200 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2200 : treeBlockF 2200 2204 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2204 : treeBlockF 2204 2208 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2208 : treeBlockF 2208 2212 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2212 : treeBlockF 2212 2216 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2216 : treeBlockF 2216 2220 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2220 : treeBlockF 2220 2224 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2224 : treeBlockF 2224 2228 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2228 : treeBlockF 2228 2232 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2232 : treeBlockF 2232 2236 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2236 : treeBlockF 2236 2240 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2240 : treeBlockF 2240 2244 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2244 : treeBlockF 2244 2248 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2248 : treeBlockF 2248 2252 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2252 : treeBlockF 2252 2256 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2256 : treeBlockF 2256 2260 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2260 : treeBlockF 2260 2264 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2264 : treeBlockF 2264 2268 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2268 : treeBlockF 2268 2272 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2272 : treeBlockF 2272 2276 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2276 : treeBlockF 2276 2280 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2280 : treeBlockF 2280 2284 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2284 : treeBlockF 2284 2288 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2288 : treeBlockF 2288 2292 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2292 : treeBlockF 2292 2296 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2296 : treeBlockF 2296 2300 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2300 : treeBlockF 2300 2304 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2304 : treeBlockF 2304 2308 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2308 : treeBlockF 2308 2312 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2312 : treeBlockF 2312 2316 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2316 : treeBlockF 2316 2320 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2320 : treeBlockF 2320 2324 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2324 : treeBlockF 2324 2328 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2328 : treeBlockF 2328 2332 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2332 : treeBlockF 2332 2336 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2336 : treeBlockF 2336 2340 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2340 : treeBlockF 2340 2344 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2344 : treeBlockF 2344 2348 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2348 : treeBlockF 2348 2352 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2352 : treeBlockF 2352 2356 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2356 : treeBlockF 2356 2360 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2360 : treeBlockF 2360 2364 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2364 : treeBlockF 2364 2368 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2368 : treeBlockF 2368 2372 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2372 : treeBlockF 2372 2376 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2376 : treeBlockF 2376 2380 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2380 : treeBlockF 2380 2384 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2384 : treeBlockF 2384 2388 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2388 : treeBlockF 2388 2392 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2392 : treeBlockF 2392 2396 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2396 : treeBlockF 2396 2400 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2400 : treeBlockF 2400 2404 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2404 : treeBlockF 2404 2408 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2408 : treeBlockF 2408 2412 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2412 : treeBlockF 2412 2416 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2416 : treeBlockF 2416 2420 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2420 : treeBlockF 2420 2424 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2424 : treeBlockF 2424 2428 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2428 : treeBlockF 2428 2432 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2432 : treeBlockF 2432 2436 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2436 : treeBlockF 2436 2440 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2440 : treeBlockF 2440 2444 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2444 : treeBlockF 2444 2448 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2448 : treeBlockF 2448 2452 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2452 : treeBlockF 2452 2456 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2456 : treeBlockF 2456 2460 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2460 : treeBlockF 2460 2464 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2464 : treeBlockF 2464 2468 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2468 : treeBlockF 2468 2472 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2472 : treeBlockF 2472 2476 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2476 : treeBlockF 2476 2480 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2480 : treeBlockF 2480 2484 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2484 : treeBlockF 2484 2488 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2488 : treeBlockF 2488 2492 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2492 : treeBlockF 2492 2496 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2496 : treeBlockF 2496 2500 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2500 : treeBlockF 2500 2504 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2504 : treeBlockF 2504 2508 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2508 : treeBlockF 2508 2512 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2512 : treeBlockF 2512 2516 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2516 : treeBlockF 2516 2520 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2520 : treeBlockF 2520 2524 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2524 : treeBlockF 2524 2528 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2528 : treeBlockF 2528 2532 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2532 : treeBlockF 2532 2536 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2536 : treeBlockF 2536 2540 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2540 : treeBlockF 2540 2544 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2544 : treeBlockF 2544 2548 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2548 : treeBlockF 2548 2552 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2552 : treeBlockF 2552 2556 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2556 : treeBlockF 2556 2560 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2560 : treeBlockF 2560 2564 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2564 : treeBlockF 2564 2568 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2568 : treeBlockF 2568 2572 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2572 : treeBlockF 2572 2576 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2576 : treeBlockF 2576 2580 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2580 : treeBlockF 2580 2584 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2584 : treeBlockF 2584 2588 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2588 : treeBlockF 2588 2592 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2592 : treeBlockF 2592 2596 cert_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem row2596 : treeBlockF 2596 2599 cert_check = true := by decide +kernel
theorem cert_nodes : ∀ i, 0 ≤ i → i < 2599 → cert_check i = true :=
  joinBlockSpecs
    (joinBlockSpecs
      (joinBlockSpecs
        (joinBlockSpecs
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row0)
                    (blockSpec row4))
                  (joinBlockSpecs
                    (blockSpec row8)
                    (joinBlockSpecs
                      (blockSpec row12)
                      (blockSpec row16))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row20)
                    (blockSpec row24))
                  (joinBlockSpecs
                    (blockSpec row28)
                    (joinBlockSpecs
                      (blockSpec row32)
                      (blockSpec row36)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row40)
                    (blockSpec row44))
                  (joinBlockSpecs
                    (blockSpec row48)
                    (joinBlockSpecs
                      (blockSpec row52)
                      (blockSpec row56))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row60)
                    (blockSpec row64))
                  (joinBlockSpecs
                    (blockSpec row68)
                    (joinBlockSpecs
                      (blockSpec row72)
                      (blockSpec row76))))))
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row80)
                    (blockSpec row84))
                  (joinBlockSpecs
                    (blockSpec row88)
                    (joinBlockSpecs
                      (blockSpec row92)
                      (blockSpec row96))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row100)
                    (blockSpec row104))
                  (joinBlockSpecs
                    (blockSpec row108)
                    (joinBlockSpecs
                      (blockSpec row112)
                      (blockSpec row116)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row120)
                    (blockSpec row124))
                  (joinBlockSpecs
                    (blockSpec row128)
                    (joinBlockSpecs
                      (blockSpec row132)
                      (blockSpec row136))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row140)
                    (blockSpec row144))
                  (joinBlockSpecs
                    (blockSpec row148)
                    (joinBlockSpecs
                      (blockSpec row152)
                      (blockSpec row156)))))))
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row160)
                    (blockSpec row164))
                  (joinBlockSpecs
                    (blockSpec row168)
                    (joinBlockSpecs
                      (blockSpec row172)
                      (blockSpec row176))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row180)
                    (blockSpec row184))
                  (joinBlockSpecs
                    (blockSpec row188)
                    (joinBlockSpecs
                      (blockSpec row192)
                      (blockSpec row196)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row200)
                    (blockSpec row204))
                  (joinBlockSpecs
                    (blockSpec row208)
                    (joinBlockSpecs
                      (blockSpec row212)
                      (blockSpec row216))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row220)
                    (blockSpec row224))
                  (joinBlockSpecs
                    (blockSpec row228)
                    (joinBlockSpecs
                      (blockSpec row232)
                      (blockSpec row236))))))
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row240)
                    (blockSpec row244))
                  (joinBlockSpecs
                    (blockSpec row248)
                    (joinBlockSpecs
                      (blockSpec row252)
                      (blockSpec row256))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row260)
                    (blockSpec row264))
                  (joinBlockSpecs
                    (blockSpec row268)
                    (joinBlockSpecs
                      (blockSpec row272)
                      (blockSpec row276)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row280)
                    (blockSpec row284))
                  (joinBlockSpecs
                    (blockSpec row288)
                    (joinBlockSpecs
                      (blockSpec row292)
                      (blockSpec row296))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row300)
                    (joinBlockSpecs
                      (blockSpec row304)
                      (blockSpec row308)))
                  (joinBlockSpecs
                    (blockSpec row312)
                    (joinBlockSpecs
                      (blockSpec row316)
                      (blockSpec row320))))))))
        (joinBlockSpecs
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row324)
                    (blockSpec row328))
                  (joinBlockSpecs
                    (blockSpec row332)
                    (joinBlockSpecs
                      (blockSpec row336)
                      (blockSpec row340))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row344)
                    (blockSpec row348))
                  (joinBlockSpecs
                    (blockSpec row352)
                    (joinBlockSpecs
                      (blockSpec row356)
                      (blockSpec row360)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row364)
                    (blockSpec row368))
                  (joinBlockSpecs
                    (blockSpec row372)
                    (joinBlockSpecs
                      (blockSpec row376)
                      (blockSpec row380))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row384)
                    (blockSpec row388))
                  (joinBlockSpecs
                    (blockSpec row392)
                    (joinBlockSpecs
                      (blockSpec row396)
                      (blockSpec row400))))))
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row404)
                    (blockSpec row408))
                  (joinBlockSpecs
                    (blockSpec row412)
                    (joinBlockSpecs
                      (blockSpec row416)
                      (blockSpec row420))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row424)
                    (blockSpec row428))
                  (joinBlockSpecs
                    (blockSpec row432)
                    (joinBlockSpecs
                      (blockSpec row436)
                      (blockSpec row440)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row444)
                    (blockSpec row448))
                  (joinBlockSpecs
                    (blockSpec row452)
                    (joinBlockSpecs
                      (blockSpec row456)
                      (blockSpec row460))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row464)
                    (blockSpec row468))
                  (joinBlockSpecs
                    (blockSpec row472)
                    (joinBlockSpecs
                      (blockSpec row476)
                      (blockSpec row480)))))))
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row484)
                    (blockSpec row488))
                  (joinBlockSpecs
                    (blockSpec row492)
                    (joinBlockSpecs
                      (blockSpec row496)
                      (blockSpec row500))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row504)
                    (blockSpec row508))
                  (joinBlockSpecs
                    (blockSpec row512)
                    (joinBlockSpecs
                      (blockSpec row516)
                      (blockSpec row520)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row524)
                    (blockSpec row528))
                  (joinBlockSpecs
                    (blockSpec row532)
                    (joinBlockSpecs
                      (blockSpec row536)
                      (blockSpec row540))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row544)
                    (blockSpec row548))
                  (joinBlockSpecs
                    (blockSpec row552)
                    (joinBlockSpecs
                      (blockSpec row556)
                      (blockSpec row560))))))
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row564)
                    (blockSpec row568))
                  (joinBlockSpecs
                    (blockSpec row572)
                    (joinBlockSpecs
                      (blockSpec row576)
                      (blockSpec row580))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row584)
                    (blockSpec row588))
                  (joinBlockSpecs
                    (blockSpec row592)
                    (joinBlockSpecs
                      (blockSpec row596)
                      (blockSpec row600)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row604)
                    (blockSpec row608))
                  (joinBlockSpecs
                    (blockSpec row612)
                    (joinBlockSpecs
                      (blockSpec row616)
                      (blockSpec row620))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row624)
                    (joinBlockSpecs
                      (blockSpec row628)
                      (blockSpec row632)))
                  (joinBlockSpecs
                    (blockSpec row636)
                    (joinBlockSpecs
                      (blockSpec row640)
                      (blockSpec row644)))))))))
      (joinBlockSpecs
        (joinBlockSpecs
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row648)
                    (blockSpec row652))
                  (joinBlockSpecs
                    (blockSpec row656)
                    (joinBlockSpecs
                      (blockSpec row660)
                      (blockSpec row664))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row668)
                    (blockSpec row672))
                  (joinBlockSpecs
                    (blockSpec row676)
                    (joinBlockSpecs
                      (blockSpec row680)
                      (blockSpec row684)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row688)
                    (blockSpec row692))
                  (joinBlockSpecs
                    (blockSpec row696)
                    (joinBlockSpecs
                      (blockSpec row700)
                      (blockSpec row704))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row708)
                    (blockSpec row712))
                  (joinBlockSpecs
                    (blockSpec row716)
                    (joinBlockSpecs
                      (blockSpec row720)
                      (blockSpec row724))))))
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row728)
                    (blockSpec row732))
                  (joinBlockSpecs
                    (blockSpec row736)
                    (joinBlockSpecs
                      (blockSpec row740)
                      (blockSpec row744))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row748)
                    (blockSpec row752))
                  (joinBlockSpecs
                    (blockSpec row756)
                    (joinBlockSpecs
                      (blockSpec row760)
                      (blockSpec row764)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row768)
                    (blockSpec row772))
                  (joinBlockSpecs
                    (blockSpec row776)
                    (joinBlockSpecs
                      (blockSpec row780)
                      (blockSpec row784))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row788)
                    (blockSpec row792))
                  (joinBlockSpecs
                    (blockSpec row796)
                    (joinBlockSpecs
                      (blockSpec row800)
                      (blockSpec row804)))))))
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row808)
                    (blockSpec row812))
                  (joinBlockSpecs
                    (blockSpec row816)
                    (joinBlockSpecs
                      (blockSpec row820)
                      (blockSpec row824))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row828)
                    (blockSpec row832))
                  (joinBlockSpecs
                    (blockSpec row836)
                    (joinBlockSpecs
                      (blockSpec row840)
                      (blockSpec row844)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row848)
                    (blockSpec row852))
                  (joinBlockSpecs
                    (blockSpec row856)
                    (joinBlockSpecs
                      (blockSpec row860)
                      (blockSpec row864))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row868)
                    (blockSpec row872))
                  (joinBlockSpecs
                    (blockSpec row876)
                    (joinBlockSpecs
                      (blockSpec row880)
                      (blockSpec row884))))))
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row888)
                    (blockSpec row892))
                  (joinBlockSpecs
                    (blockSpec row896)
                    (joinBlockSpecs
                      (blockSpec row900)
                      (blockSpec row904))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row908)
                    (blockSpec row912))
                  (joinBlockSpecs
                    (blockSpec row916)
                    (joinBlockSpecs
                      (blockSpec row920)
                      (blockSpec row924)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row928)
                    (blockSpec row932))
                  (joinBlockSpecs
                    (blockSpec row936)
                    (joinBlockSpecs
                      (blockSpec row940)
                      (blockSpec row944))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row948)
                    (joinBlockSpecs
                      (blockSpec row952)
                      (blockSpec row956)))
                  (joinBlockSpecs
                    (blockSpec row960)
                    (joinBlockSpecs
                      (blockSpec row964)
                      (blockSpec row968))))))))
        (joinBlockSpecs
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row972)
                    (blockSpec row976))
                  (joinBlockSpecs
                    (blockSpec row980)
                    (joinBlockSpecs
                      (blockSpec row984)
                      (blockSpec row988))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row992)
                    (blockSpec row996))
                  (joinBlockSpecs
                    (blockSpec row1000)
                    (joinBlockSpecs
                      (blockSpec row1004)
                      (blockSpec row1008)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1012)
                    (blockSpec row1016))
                  (joinBlockSpecs
                    (blockSpec row1020)
                    (joinBlockSpecs
                      (blockSpec row1024)
                      (blockSpec row1028))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1032)
                    (blockSpec row1036))
                  (joinBlockSpecs
                    (blockSpec row1040)
                    (joinBlockSpecs
                      (blockSpec row1044)
                      (blockSpec row1048))))))
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1052)
                    (blockSpec row1056))
                  (joinBlockSpecs
                    (blockSpec row1060)
                    (joinBlockSpecs
                      (blockSpec row1064)
                      (blockSpec row1068))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1072)
                    (blockSpec row1076))
                  (joinBlockSpecs
                    (blockSpec row1080)
                    (joinBlockSpecs
                      (blockSpec row1084)
                      (blockSpec row1088)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1092)
                    (blockSpec row1096))
                  (joinBlockSpecs
                    (blockSpec row1100)
                    (joinBlockSpecs
                      (blockSpec row1104)
                      (blockSpec row1108))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1112)
                    (joinBlockSpecs
                      (blockSpec row1116)
                      (blockSpec row1120)))
                  (joinBlockSpecs
                    (blockSpec row1124)
                    (joinBlockSpecs
                      (blockSpec row1128)
                      (blockSpec row1132)))))))
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1136)
                    (blockSpec row1140))
                  (joinBlockSpecs
                    (blockSpec row1144)
                    (joinBlockSpecs
                      (blockSpec row1148)
                      (blockSpec row1152))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1156)
                    (blockSpec row1160))
                  (joinBlockSpecs
                    (blockSpec row1164)
                    (joinBlockSpecs
                      (blockSpec row1168)
                      (blockSpec row1172)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1176)
                    (blockSpec row1180))
                  (joinBlockSpecs
                    (blockSpec row1184)
                    (joinBlockSpecs
                      (blockSpec row1188)
                      (blockSpec row1192))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1196)
                    (blockSpec row1200))
                  (joinBlockSpecs
                    (blockSpec row1204)
                    (joinBlockSpecs
                      (blockSpec row1208)
                      (blockSpec row1212))))))
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1216)
                    (blockSpec row1220))
                  (joinBlockSpecs
                    (blockSpec row1224)
                    (joinBlockSpecs
                      (blockSpec row1228)
                      (blockSpec row1232))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1236)
                    (blockSpec row1240))
                  (joinBlockSpecs
                    (blockSpec row1244)
                    (joinBlockSpecs
                      (blockSpec row1248)
                      (blockSpec row1252)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1256)
                    (blockSpec row1260))
                  (joinBlockSpecs
                    (blockSpec row1264)
                    (joinBlockSpecs
                      (blockSpec row1268)
                      (blockSpec row1272))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1276)
                    (joinBlockSpecs
                      (blockSpec row1280)
                      (blockSpec row1284)))
                  (joinBlockSpecs
                    (blockSpec row1288)
                    (joinBlockSpecs
                      (blockSpec row1292)
                      (blockSpec row1296))))))))))
    (joinBlockSpecs
      (joinBlockSpecs
        (joinBlockSpecs
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1300)
                    (blockSpec row1304))
                  (joinBlockSpecs
                    (blockSpec row1308)
                    (joinBlockSpecs
                      (blockSpec row1312)
                      (blockSpec row1316))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1320)
                    (blockSpec row1324))
                  (joinBlockSpecs
                    (blockSpec row1328)
                    (joinBlockSpecs
                      (blockSpec row1332)
                      (blockSpec row1336)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1340)
                    (blockSpec row1344))
                  (joinBlockSpecs
                    (blockSpec row1348)
                    (joinBlockSpecs
                      (blockSpec row1352)
                      (blockSpec row1356))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1360)
                    (blockSpec row1364))
                  (joinBlockSpecs
                    (blockSpec row1368)
                    (joinBlockSpecs
                      (blockSpec row1372)
                      (blockSpec row1376))))))
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1380)
                    (blockSpec row1384))
                  (joinBlockSpecs
                    (blockSpec row1388)
                    (joinBlockSpecs
                      (blockSpec row1392)
                      (blockSpec row1396))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1400)
                    (blockSpec row1404))
                  (joinBlockSpecs
                    (blockSpec row1408)
                    (joinBlockSpecs
                      (blockSpec row1412)
                      (blockSpec row1416)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1420)
                    (blockSpec row1424))
                  (joinBlockSpecs
                    (blockSpec row1428)
                    (joinBlockSpecs
                      (blockSpec row1432)
                      (blockSpec row1436))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1440)
                    (blockSpec row1444))
                  (joinBlockSpecs
                    (blockSpec row1448)
                    (joinBlockSpecs
                      (blockSpec row1452)
                      (blockSpec row1456)))))))
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1460)
                    (blockSpec row1464))
                  (joinBlockSpecs
                    (blockSpec row1468)
                    (joinBlockSpecs
                      (blockSpec row1472)
                      (blockSpec row1476))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1480)
                    (blockSpec row1484))
                  (joinBlockSpecs
                    (blockSpec row1488)
                    (joinBlockSpecs
                      (blockSpec row1492)
                      (blockSpec row1496)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1500)
                    (blockSpec row1504))
                  (joinBlockSpecs
                    (blockSpec row1508)
                    (joinBlockSpecs
                      (blockSpec row1512)
                      (blockSpec row1516))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1520)
                    (blockSpec row1524))
                  (joinBlockSpecs
                    (blockSpec row1528)
                    (joinBlockSpecs
                      (blockSpec row1532)
                      (blockSpec row1536))))))
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1540)
                    (blockSpec row1544))
                  (joinBlockSpecs
                    (blockSpec row1548)
                    (joinBlockSpecs
                      (blockSpec row1552)
                      (blockSpec row1556))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1560)
                    (blockSpec row1564))
                  (joinBlockSpecs
                    (blockSpec row1568)
                    (joinBlockSpecs
                      (blockSpec row1572)
                      (blockSpec row1576)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1580)
                    (blockSpec row1584))
                  (joinBlockSpecs
                    (blockSpec row1588)
                    (joinBlockSpecs
                      (blockSpec row1592)
                      (blockSpec row1596))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1600)
                    (joinBlockSpecs
                      (blockSpec row1604)
                      (blockSpec row1608)))
                  (joinBlockSpecs
                    (blockSpec row1612)
                    (joinBlockSpecs
                      (blockSpec row1616)
                      (blockSpec row1620))))))))
        (joinBlockSpecs
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1624)
                    (blockSpec row1628))
                  (joinBlockSpecs
                    (blockSpec row1632)
                    (joinBlockSpecs
                      (blockSpec row1636)
                      (blockSpec row1640))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1644)
                    (blockSpec row1648))
                  (joinBlockSpecs
                    (blockSpec row1652)
                    (joinBlockSpecs
                      (blockSpec row1656)
                      (blockSpec row1660)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1664)
                    (blockSpec row1668))
                  (joinBlockSpecs
                    (blockSpec row1672)
                    (joinBlockSpecs
                      (blockSpec row1676)
                      (blockSpec row1680))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1684)
                    (blockSpec row1688))
                  (joinBlockSpecs
                    (blockSpec row1692)
                    (joinBlockSpecs
                      (blockSpec row1696)
                      (blockSpec row1700))))))
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1704)
                    (blockSpec row1708))
                  (joinBlockSpecs
                    (blockSpec row1712)
                    (joinBlockSpecs
                      (blockSpec row1716)
                      (blockSpec row1720))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1724)
                    (blockSpec row1728))
                  (joinBlockSpecs
                    (blockSpec row1732)
                    (joinBlockSpecs
                      (blockSpec row1736)
                      (blockSpec row1740)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1744)
                    (blockSpec row1748))
                  (joinBlockSpecs
                    (blockSpec row1752)
                    (joinBlockSpecs
                      (blockSpec row1756)
                      (blockSpec row1760))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1764)
                    (blockSpec row1768))
                  (joinBlockSpecs
                    (blockSpec row1772)
                    (joinBlockSpecs
                      (blockSpec row1776)
                      (blockSpec row1780)))))))
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1784)
                    (blockSpec row1788))
                  (joinBlockSpecs
                    (blockSpec row1792)
                    (joinBlockSpecs
                      (blockSpec row1796)
                      (blockSpec row1800))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1804)
                    (blockSpec row1808))
                  (joinBlockSpecs
                    (blockSpec row1812)
                    (joinBlockSpecs
                      (blockSpec row1816)
                      (blockSpec row1820)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1824)
                    (blockSpec row1828))
                  (joinBlockSpecs
                    (blockSpec row1832)
                    (joinBlockSpecs
                      (blockSpec row1836)
                      (blockSpec row1840))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1844)
                    (blockSpec row1848))
                  (joinBlockSpecs
                    (blockSpec row1852)
                    (joinBlockSpecs
                      (blockSpec row1856)
                      (blockSpec row1860))))))
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1864)
                    (blockSpec row1868))
                  (joinBlockSpecs
                    (blockSpec row1872)
                    (joinBlockSpecs
                      (blockSpec row1876)
                      (blockSpec row1880))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1884)
                    (blockSpec row1888))
                  (joinBlockSpecs
                    (blockSpec row1892)
                    (joinBlockSpecs
                      (blockSpec row1896)
                      (blockSpec row1900)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1904)
                    (blockSpec row1908))
                  (joinBlockSpecs
                    (blockSpec row1912)
                    (joinBlockSpecs
                      (blockSpec row1916)
                      (blockSpec row1920))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1924)
                    (joinBlockSpecs
                      (blockSpec row1928)
                      (blockSpec row1932)))
                  (joinBlockSpecs
                    (blockSpec row1936)
                    (joinBlockSpecs
                      (blockSpec row1940)
                      (blockSpec row1944)))))))))
      (joinBlockSpecs
        (joinBlockSpecs
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1948)
                    (blockSpec row1952))
                  (joinBlockSpecs
                    (blockSpec row1956)
                    (joinBlockSpecs
                      (blockSpec row1960)
                      (blockSpec row1964))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1968)
                    (blockSpec row1972))
                  (joinBlockSpecs
                    (blockSpec row1976)
                    (joinBlockSpecs
                      (blockSpec row1980)
                      (blockSpec row1984)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row1988)
                    (blockSpec row1992))
                  (joinBlockSpecs
                    (blockSpec row1996)
                    (joinBlockSpecs
                      (blockSpec row2000)
                      (blockSpec row2004))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2008)
                    (blockSpec row2012))
                  (joinBlockSpecs
                    (blockSpec row2016)
                    (joinBlockSpecs
                      (blockSpec row2020)
                      (blockSpec row2024))))))
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2028)
                    (blockSpec row2032))
                  (joinBlockSpecs
                    (blockSpec row2036)
                    (joinBlockSpecs
                      (blockSpec row2040)
                      (blockSpec row2044))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2048)
                    (blockSpec row2052))
                  (joinBlockSpecs
                    (blockSpec row2056)
                    (joinBlockSpecs
                      (blockSpec row2060)
                      (blockSpec row2064)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2068)
                    (blockSpec row2072))
                  (joinBlockSpecs
                    (blockSpec row2076)
                    (joinBlockSpecs
                      (blockSpec row2080)
                      (blockSpec row2084))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2088)
                    (blockSpec row2092))
                  (joinBlockSpecs
                    (blockSpec row2096)
                    (joinBlockSpecs
                      (blockSpec row2100)
                      (blockSpec row2104)))))))
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2108)
                    (blockSpec row2112))
                  (joinBlockSpecs
                    (blockSpec row2116)
                    (joinBlockSpecs
                      (blockSpec row2120)
                      (blockSpec row2124))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2128)
                    (blockSpec row2132))
                  (joinBlockSpecs
                    (blockSpec row2136)
                    (joinBlockSpecs
                      (blockSpec row2140)
                      (blockSpec row2144)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2148)
                    (blockSpec row2152))
                  (joinBlockSpecs
                    (blockSpec row2156)
                    (joinBlockSpecs
                      (blockSpec row2160)
                      (blockSpec row2164))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2168)
                    (blockSpec row2172))
                  (joinBlockSpecs
                    (blockSpec row2176)
                    (joinBlockSpecs
                      (blockSpec row2180)
                      (blockSpec row2184))))))
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2188)
                    (blockSpec row2192))
                  (joinBlockSpecs
                    (blockSpec row2196)
                    (joinBlockSpecs
                      (blockSpec row2200)
                      (blockSpec row2204))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2208)
                    (blockSpec row2212))
                  (joinBlockSpecs
                    (blockSpec row2216)
                    (joinBlockSpecs
                      (blockSpec row2220)
                      (blockSpec row2224)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2228)
                    (blockSpec row2232))
                  (joinBlockSpecs
                    (blockSpec row2236)
                    (joinBlockSpecs
                      (blockSpec row2240)
                      (blockSpec row2244))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2248)
                    (joinBlockSpecs
                      (blockSpec row2252)
                      (blockSpec row2256)))
                  (joinBlockSpecs
                    (blockSpec row2260)
                    (joinBlockSpecs
                      (blockSpec row2264)
                      (blockSpec row2268))))))))
        (joinBlockSpecs
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2272)
                    (blockSpec row2276))
                  (joinBlockSpecs
                    (blockSpec row2280)
                    (joinBlockSpecs
                      (blockSpec row2284)
                      (blockSpec row2288))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2292)
                    (blockSpec row2296))
                  (joinBlockSpecs
                    (blockSpec row2300)
                    (joinBlockSpecs
                      (blockSpec row2304)
                      (blockSpec row2308)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2312)
                    (blockSpec row2316))
                  (joinBlockSpecs
                    (blockSpec row2320)
                    (joinBlockSpecs
                      (blockSpec row2324)
                      (blockSpec row2328))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2332)
                    (blockSpec row2336))
                  (joinBlockSpecs
                    (blockSpec row2340)
                    (joinBlockSpecs
                      (blockSpec row2344)
                      (blockSpec row2348))))))
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2352)
                    (blockSpec row2356))
                  (joinBlockSpecs
                    (blockSpec row2360)
                    (joinBlockSpecs
                      (blockSpec row2364)
                      (blockSpec row2368))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2372)
                    (blockSpec row2376))
                  (joinBlockSpecs
                    (blockSpec row2380)
                    (joinBlockSpecs
                      (blockSpec row2384)
                      (blockSpec row2388)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2392)
                    (blockSpec row2396))
                  (joinBlockSpecs
                    (blockSpec row2400)
                    (joinBlockSpecs
                      (blockSpec row2404)
                      (blockSpec row2408))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2412)
                    (joinBlockSpecs
                      (blockSpec row2416)
                      (blockSpec row2420)))
                  (joinBlockSpecs
                    (blockSpec row2424)
                    (joinBlockSpecs
                      (blockSpec row2428)
                      (blockSpec row2432)))))))
          (joinBlockSpecs
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2436)
                    (blockSpec row2440))
                  (joinBlockSpecs
                    (blockSpec row2444)
                    (joinBlockSpecs
                      (blockSpec row2448)
                      (blockSpec row2452))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2456)
                    (blockSpec row2460))
                  (joinBlockSpecs
                    (blockSpec row2464)
                    (joinBlockSpecs
                      (blockSpec row2468)
                      (blockSpec row2472)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2476)
                    (blockSpec row2480))
                  (joinBlockSpecs
                    (blockSpec row2484)
                    (joinBlockSpecs
                      (blockSpec row2488)
                      (blockSpec row2492))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2496)
                    (blockSpec row2500))
                  (joinBlockSpecs
                    (blockSpec row2504)
                    (joinBlockSpecs
                      (blockSpec row2508)
                      (blockSpec row2512))))))
            (joinBlockSpecs
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2516)
                    (blockSpec row2520))
                  (joinBlockSpecs
                    (blockSpec row2524)
                    (joinBlockSpecs
                      (blockSpec row2528)
                      (blockSpec row2532))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2536)
                    (blockSpec row2540))
                  (joinBlockSpecs
                    (blockSpec row2544)
                    (joinBlockSpecs
                      (blockSpec row2548)
                      (blockSpec row2552)))))
              (joinBlockSpecs
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2556)
                    (blockSpec row2560))
                  (joinBlockSpecs
                    (blockSpec row2564)
                    (joinBlockSpecs
                      (blockSpec row2568)
                      (blockSpec row2572))))
                (joinBlockSpecs
                  (joinBlockSpecs
                    (blockSpec row2576)
                    (joinBlockSpecs
                      (blockSpec row2580)
                      (blockSpec row2584)))
                  (joinBlockSpecs
                    (blockSpec row2588)
                    (joinBlockSpecs
                      (blockSpec row2592)
                      (blockSpec row2596))))))))))
theorem cert_lower (hknown : KnownBin cert_bounds) : LowerBin cert_mask cert_stock cert_goal 13 :=
  lowerDagRefF (profile := cert_profile) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hknown cert_sub cert_goals
    (symDagRef_sound (by decide +kernel) cert_syms cert_trace cert_links)
    cert_roots cert_nodes

theorem knownNil : KnownBin [] := by
  intro b hb
  exact (List.not_mem_nil hb).elim

theorem knownCons {b : Nat × List Nat × Nat × Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hb : LowerBin b.1 b.2.1 b.2.2.2 b.2.2.1) (hs : KnownBin bounds) : KnownBin (b :: bounds) := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | hm
  · exact hb
  · exact hs a hm

def r0_mask : Nat := 0xcccc0000cccc
def r0_stock : List Nat := [0xcccc, 0xcc000000cc, 0xc0c00000c0c, 0x444400004444]
def r0_goal : Nat := 0x4440000444c
def r0_bounds : List (Nat × List Nat × Nat × Nat) := []
theorem r0_sub : ∀ b ∈ r0_bounds, r0_mask &&& b.1 = b.1 := by
  have hall : r0_bounds.all (fun b => Nat.beq (Nat.land r0_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r0_goals : ∀ b ∈ r0_bounds, canon b.1 r0_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r0_bounds.all (fun b => Nat.beq (canonF b.1 r0_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r0_forest : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def r0_links : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
def r0_trace := dagTraceF r0_mask r0_stock 5 r0_forest
def r0_check : Nat → Bool := dagCheckNodeF r0_mask r0_goal r0_bounds 64 r0_trace r0_links
set_option maxHeartbeats 0 in
theorem r0_roots : dagCheckRootsF r0_mask r0_goal r0_bounds
    (dagRefF 64 r0_trace r0_links 0) r0_stock 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r0_b0 : treeBlockF 0 12 r0_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r0_b12 : treeBlockF 12 24 r0_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r0_b24 : treeBlockF 24 36 r0_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r0_b36 : treeBlockF 36 48 r0_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r0_b48 : treeBlockF 48 60 r0_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r0_b60 : treeBlockF 60 64 r0_check = true := by decide +kernel
theorem r0_nodes : ∀ i, 0 ≤ i → i < 64 → r0_check i = true :=
  joinBlockSpecs
    (joinBlockSpecs
      (blockSpec r0_b0)
      (joinBlockSpecs
        (blockSpec r0_b12)
        (blockSpec r0_b24)))
    (joinBlockSpecs
      (blockSpec r0_b36)
      (joinBlockSpecs
        (blockSpec r0_b48)
        (blockSpec r0_b60)))
theorem r0_known : KnownBin r0_bounds :=
  knownNil
theorem r0_lower : LowerBin r0_mask r0_stock r0_goal 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r0_known r0_sub r0_goals r0_roots r0_nodes

def r1_mask : Nat := 0xf0f00000f0f0
def r1_stock : List Nat := [0xf0f0, 0xf0000000f0, 0x303000003030, 0x505000005050]
def r1_goal : Nat := 0x105000005070
def r1_rows : Fin 64 → Fin 64 := decodeRows 0xbee000b6c0009e60009640000000000000000000000000003ce00034c0001c6000144000
set_option maxHeartbeats 0 in
theorem r1_lower : LowerBin r1_mask r1_stock r1_goal 6 := by
  apply lowerBin_of_rowPull r1_rows (stock' := r0_stock)
  · have hall : r1_stock.all (fun w => availBF r0_stock
        (rowCanon r1_rows r1_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r1_rows r1_mask = r0_mask := by decide +kernel
    have hg : rowCanon r1_rows r1_mask r1_goal = r0_goal := by decide +kernel
    rw [hm, hg]
    exact r0_lower

def r2_mask : Nat := 0xff00ff00
def r2_stock : List Nat := [0xff00, 0xf000f00, 0x33003300, 0x55005500]
def r2_goal : Nat := 0x1005700
def r2_bounds : List (Nat × List Nat × Nat × Nat) := []
theorem r2_sub : ∀ b ∈ r2_bounds, r2_mask &&& b.1 = b.1 := by
  have hall : r2_bounds.all (fun b => Nat.beq (Nat.land r2_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r2_goals : ∀ b ∈ r2_bounds, canon b.1 r2_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r2_bounds.all (fun b => Nat.beq (canonF b.1 r2_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r2_forest : Nat → Nat × Nat := unpackForestF 0x32eb2c32932232132000f 3 9
def r2_links : Nat → Nat → Option Nat := unpackLinksF 0xe78c70c30341 0xb2cb2cd2e92972252132000f 6 3 9 3 4
def r2_trace := dagTraceF r2_mask r2_stock 4 r2_forest
def r2_check : Nat → Bool := dagCheckNodeF r2_mask r2_goal r2_bounds 7 r2_trace r2_links
set_option maxHeartbeats 0 in
theorem r2_roots : dagCheckRootsF r2_mask r2_goal r2_bounds
    (dagRefF 7 r2_trace r2_links 0) r2_stock 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r2_b0 : treeBlockF 0 7 r2_check = true := by decide +kernel
theorem r2_nodes : ∀ i, 0 ≤ i → i < 7 → r2_check i = true :=
  blockSpec r2_b0
theorem r2_known : KnownBin r2_bounds :=
  knownNil
theorem r2_lower : LowerBin r2_mask r2_stock r2_goal 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r2_known r2_sub r2_goals r2_roots r2_nodes

def r3_mask : Nat := 0xaaaa0000aaaa
def r3_stock : List Nat := [0xaaaa, 0xaa000000aa, 0xa0a00000a0a, 0x222200002222]
def r3_goal : Nat := 0x2020000022a
def r3_rows : Fin 64 → Fin 64 := decodeRows 0xbed9e53cd1c5000000000000ae98e12c90c1000000000000
set_option maxHeartbeats 0 in
theorem r3_lower : LowerBin r3_mask r3_stock r3_goal 5 := by
  apply lowerBin_of_rowPull r3_rows (stock' := r2_stock)
  · have hall : r3_stock.all (fun w => availBF r2_stock
        (rowCanon r3_rows r3_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r3_rows r3_mask = r2_mask := by decide +kernel
    have hg : rowCanon r3_rows r3_mask r3_goal = r2_goal := by decide +kernel
    rw [hm, hg]
    exact r2_lower

def r4_mask : Nat := 0xffff
def r4_stock : List Nat := [0xff, 0xf0f, 0x3333, 0x5555]
def r4_goal : Nat := 0x577f
def r4_bounds : List (Nat × List Nat × Nat × Nat) := []
theorem r4_sub : ∀ b ∈ r4_bounds, r4_mask &&& b.1 = b.1 := by
  have hall : r4_bounds.all (fun b => Nat.beq (Nat.land r4_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r4_goals : ∀ b ∈ r4_bounds, canon b.1 r4_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r4_bounds.all (fun b => Nat.beq (canonF b.1 r4_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r4_forest : Nat → Nat × Nat := unpackForestF 0xc7463629d6490a6c43a492209086c00f 3 10
def r4_links : Nat → Nat → Option Nat := unpackLinksF 0x1a2d58b12a44890e8701 0x192430919242090d24209263a88d9d3a54d903a10d800f 7 3 10 4 4
def r4_trace := dagTraceF r4_mask r4_stock 4 r4_forest
def r4_check : Nat → Bool := dagCheckNodeF r4_mask r4_goal r4_bounds 10 r4_trace r4_links
set_option maxHeartbeats 0 in
theorem r4_roots : dagCheckRootsF r4_mask r4_goal r4_bounds
    (dagRefF 10 r4_trace r4_links 0) r4_stock 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r4_b0 : treeBlockF 0 10 r4_check = true := by decide +kernel
theorem r4_nodes : ∀ i, 0 ≤ i → i < 10 → r4_check i = true :=
  blockSpec r4_b0
theorem r4_known : KnownBin r4_bounds :=
  knownNil
theorem r4_lower : LowerBin r4_mask r4_stock r4_goal 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r4_known r4_sub r4_goals r4_roots r4_nodes

def r5_mask : Nat := 0xff000000ff
def r5_stock : List Nat := [0xff, 0xf0000000f, 0x3300000033, 0x5500000055]
def r5_goal : Nat := 0x570000007f
def r5_rows : Fin 64 → Fin 64 := decodeRows 0x2082082082082082082082082082082082082082082082082082082082082082082082089e69648e28601c61440c2040
set_option maxHeartbeats 0 in
theorem r5_lower : LowerBin r5_mask r5_stock r5_goal 5 := by
  apply lowerBin_of_rowPull r5_rows (stock' := r4_stock)
  · have hall : r5_stock.all (fun w => availBF r4_stock
        (rowCanon r5_rows r5_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r5_rows r5_mask = r4_mask := by decide +kernel
    have hg : rowCanon r5_rows r5_mask r5_goal = r4_goal := by decide +kernel
    rw [hm, hg]
    exact r4_lower

def r6_mask : Nat := 0xcccccccc
def r6_stock : List Nat := [0xcccc, 0xcc00cc, 0xc0c0c0c, 0x44444444]
def r6_goal : Nat := 0x44444c
def r6_bounds : List (Nat × List Nat × Nat × Nat) := []
theorem r6_sub : ∀ b ∈ r6_bounds, r6_mask &&& b.1 = b.1 := by
  have hall : r6_bounds.all (fun b => Nat.beq (Nat.land r6_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r6_goals : ∀ b ∈ r6_bounds, canon b.1 r6_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r6_bounds.all (fun b => Nat.beq (canonF b.1 r6_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r6_forest : Nat → Nat × Nat := unpackForestF 0x63a84c203018d981814a452130b0429108400f 4 10
def r6_links : Nat → Nat → Option Nat := unpackLinksF 0xb162c4a910604072e0701 0x253080c181830b2a3a78d95294484829108400f 7 3 10 4 4
def r6_trace := dagTraceF r6_mask r6_stock 4 r6_forest
def r6_check : Nat → Bool := dagCheckNodeF r6_mask r6_goal r6_bounds 11 r6_trace r6_links
set_option maxHeartbeats 0 in
theorem r6_roots : dagCheckRootsF r6_mask r6_goal r6_bounds
    (dagRefF 11 r6_trace r6_links 0) r6_stock 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r6_b0 : treeBlockF 0 11 r6_check = true := by decide +kernel
theorem r6_nodes : ∀ i, 0 ≤ i → i < 11 → r6_check i = true :=
  blockSpec r6_b0
theorem r6_known : KnownBin r6_bounds :=
  knownNil
theorem r6_lower : LowerBin r6_mask r6_stock r6_goal 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r6_known r6_sub r6_goals r6_roots r6_nodes

def r7_mask : Nat := 0xff000000ff00
def r7_stock : List Nat := [0xff00, 0xf0000000f00, 0x330000003300, 0x550000005500]
def r7_goal : Nat := 0x170000005700
def r7_rows : Fin 64 → Fin 64 := decodeRows 0x209000a2900028b000aab00030d000b2d00038f000baf000
set_option maxHeartbeats 0 in
theorem r7_lower : LowerBin r7_mask r7_stock r7_goal 5 := by
  apply lowerBin_of_rowPull r7_rows (stock' := r6_stock)
  · have hall : r7_stock.all (fun w => availBF r6_stock
        (rowCanon r7_rows r7_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r7_rows r7_mask = r6_mask := by decide +kernel
    have hg : rowCanon r7_rows r7_mask r7_goal = r6_goal := by decide +kernel
    rw [hm, hg]
    exact r6_lower

def r8_mask : Nat := 0xffff00000000
def r8_stock : List Nat := [0xff00000000, 0xf0f00000000, 0x333300000000, 0x555500000000]
def r8_goal : Nat := 0x175700000000
def r8_rows : Fin 64 → Fin 64 := decodeRows 0x821000a290008a3000aab000925000b2d0009a7000baf000
set_option maxHeartbeats 0 in
theorem r8_lower : LowerBin r8_mask r8_stock r8_goal 5 := by
  apply lowerBin_of_rowPull r8_rows (stock' := r6_stock)
  · have hall : r8_stock.all (fun w => availBF r6_stock
        (rowCanon r8_rows r8_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r8_rows r8_mask = r6_mask := by decide +kernel
    have hg : rowCanon r8_rows r8_mask r8_goal = r6_goal := by decide +kernel
    rw [hm, hg]
    exact r6_lower

def r9_mask : Nat := 0xffff0000ffff
def r9_stock : List Nat := [0xffff, 0xff000000ff, 0xf0f00000f0f, 0x333300003333, 0x555500005555]
def r9_goal : Nat := 0x17570000577f
def r9_bounds : List (Nat × List Nat × Nat × Nat) := [(0xcccc0000cccc, [0xcccc, 0xcc000000cc, 0xc0c00000c0c, 0x444400004444], 6, 0x4440000444c), (0xf0f00000f0f0, [0xf0f0, 0xf0000000f0, 0x303000003030, 0x505000005050], 6, 0x105000005070), (0xaaaa0000aaaa, [0xaaaa, 0xaa000000aa, 0xa0a00000a0a, 0x222200002222], 5, 0x2020000022a), (0xff000000ff, [0xff, 0xf0000000f, 0x3300000033, 0x5500000055], 5, 0x570000007f), (0xff000000ff00, [0xff00, 0xf0000000f00, 0x330000003300, 0x550000005500], 5, 0x170000005700), (0xffff, [0xff, 0xf0f, 0x3333, 0x5555], 5, 0x577f), (0xffff00000000, [0xff00000000, 0xf0f00000000, 0x333300000000, 0x555500000000], 5, 0x175700000000)]
theorem r9_sub : ∀ b ∈ r9_bounds, r9_mask &&& b.1 = b.1 := by
  have hall : r9_bounds.all (fun b => Nat.beq (Nat.land r9_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r9_goals : ∀ b ∈ r9_bounds, canon b.1 r9_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r9_bounds.all (fun b => Nat.beq (canonF b.1 r9_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r9_forest : Nat → Nat × Nat := unpackForestRelative (unpackPagedWidths [
    (17, 0x10ad0655822940946191d088e832b4084a04160216b502e0854c9af821b306ae085cb9a3849141089595e1da50c958228808440caf02530128d193604221293c12a03a4704260a8dc1028113a049b024a982486a5d31269691424a0094420130c4f4108021350c210410010340814282b10d6816b8335615a508d1834ac12460423020d81026001f),
    (18, 0x2d30123a02148ca5604d600a542c57c094c2856c0b602455c19540453009341c54c094c1852c135002970494706d28125602118285a06d68125602158084ac609c085432d7c086c2ed5c085c2ad1c1236028d0925202918823a02170092a1a5581a5d02570092a121583b5a0cd582b4a08d181a56045280856020da401b029608b5f029807b57029406b47024d85a5a),
    (19, 0x22960251ef4238085c1068e06d2809a300a460c06c0c8ec151b8212f032560449c0491828340146e060b0051b80824ab08602150722f8136c010d83315c042a0ba5f010482a96c043609a57034a804910041207a53010481a92c09ae809500a2ac02d74202b0345a058ac08d580c9c80850010ac0211a341581358014a84f17c05b012c570148c46d680e2f0125a014ac3ed2815a682345),
    (19, 0x10b80a1780d2e0115c012a002148722b00b5c04ac806d70081c00834168a60ad2411a081a5e0248c02910412b01148012881a13c04a40295c04068060b0042600824060960297010238084c012a80210f751b80b5d0548a071600a2a00a540146fac13c21ab8085c0668e0a96c0da501346014ac020db342580b450e4ba0297031238146c018c0128dc08a380927062b80491c051b81950),
    (20, 0xb459324f0cb5f0c35d01c6c0106c008600a35700c5e0934d00a6c0834700a5e073450685f0116c008540505b0246c01b6c0116c0096002857011500085c00964008538624700a5416c5f00d6c15c5b00b5614c5a01a6c0106c0086012c570445e03a5e)] 6) 11
def r9_links : Nat → Nat → Option Nat := unpackLinksPaged (unpackPaged [
    0x28805084a00932726404b8897012c1248843ac860906320c03e1c7b08ec51d4239886e28da11b0236006c00d421a8034086230c4018042f845d10b8116842d005908b20158627204e009a1128625004a009021200240047088e011c023803f4064d0c80190031086200c40188031006200a500d3c01c8001,
    0x42028401013a02040027e8cfd01f813f007d84fb01f603ec07c0cf801ee13dc07b04f221e403c807900ef19de03bc07780ec19bce37806e84dd01b4336806c08d801b0034ca6980cf219e033826494c90192032026118c20184030806100c20184030805d9caf615e02b445604a91952029865300a221440,
    0x5e80b5416a02c865900b2016402bc65780af015e02bc05780af01554aaa05502aa01530a8ec51c0a30546028c0504aa081400a8004fc29f813d127a04f409e813a1a7404dc69b81360a6634cc0980d30026004c00980130025e14a4c8e351c0238046088c01151a2a0448688851102220428e84850902120,
    0x7fc4ff81ff03fe07ec8f9a1f303e417c80f901f203d487a80f501ea03d407a80f295e40bc807846f005dd1bba07740ee05db0bac57580e98dd303a417442daf1b5036056c00d801b0035846910d109a20340267c2cf819f033e066c8c6b98d031246240c30d86030c06088c1018202fe35fc0bf817a2af40,
    0x4da498d5300e5a34b4096812c86523ca4093c727824b24960910f2186420c8408fc71f823f047e08f831c1a38047008d851a0a16f42c0848908860d241a082c505820b0416080d101820114020] 15 6)
  (unpackPaged [
    0x1901b0100640b01500a0340f80503c1241801700c0540221100803414c490518261440585cb451709144f93613c4985a04413651028044148510500441368e04c14c158d28542561385784a1460981580684609015046044088110421500801103a0380e05203e04c0e80503813a0d84d81a046112d3c40b4711093c402470f08dc3493a0d04a818046090050291240a0090200140a89402814408810024a3d0828d42413d0804d41e0420701001a82a06806830b5d042d542eb4d0b2d143025d0409542e24d0b09142793609c4982683609809818014048d701435a040d580e34a030d180a2560209180714601811866c5f18b15c6635f188d5c5e34716497849a461248d85815e122518481360c84901605601211804036932d3e18b4793093e182476e88ddad14f66c52d7b14755c50d1b93b31e4dd1b12b31c49dac04f66812d7a04755810d1a83b31a0dd1a02b31809c9101f24006c6a01700804c0001f,
    0x3d8d60f4254138040f014c3b0d80e8154398530e41343805304c010370d40dbb483689704a010358d28d4256348118ce35a330958ca05645117d10457430d690434a3e0958f215f3b856cea15738854cde14b36051cd005a32012848012310150c006c278190980342f01709a0542e2918b6a442e08d8b62341bc090b22462b0558a405625a118ae05c2b24e8ac12a16817094836250098a615c2a2d749eb552a09749e2552924e8a412a280d689e356270d289a3462609589614a250158c2c5f2fb15cc235f2f8d5cba3472d0948b0a4a2c08e8aa156288158928462480d88e258110040420201f89a08a2601000407a2582189403c0101fa528829461f84e8821360e0080360101d49687e15a1f05587a14a1e05187405a0d00807112c1c00b07004a1d29287423a1c85686e02c23317c88c57230d7c88357210d1c8025a1da9287623a1b45686c05a0c8040460141104902e0641a0150552341504d040124,
    0x62049d84b4761091d822374c20e93002a65ad7592b47658975922476308dd8615c6005417e14b5f051d4193b3ae4dd4112b3ac49d2e83a4b80a8aa01a5e0171720545c2111700345780b15a0245d0d29723465c09193d129394494b901e5b08ed6a2374fe4ece99375a04bd6612b59049d621232dc0795e2375688dd763474e692ce3a474e48ece32372d44b96e8465821116e0365800d15c02c56009154054540db0cc9445381b1260644901114a054518090ad12c5081b13e2544f09113a02448e911220544d8091200364c8d75301504780d92c35d498d54ca8364801412845a499159243564884e51e0562cc0795245f53115d4825f51096d402574e094d3424b37e91d2e156322518b112e4a81591c046460d610a34840899116254420da1123604009510824a438918ce04a3f8d510a45e3f0d590825a418958db945358168560123f88e0fe34c408d35003453f08e8fa052350128cc03a15004852010,
    0x7e4141fab5c7e8971f815c7d85420245e7b117600b5e800979fd15e7d4549fc05e7d0149f035c7b9591e2c647b0d71e22647ac4e1e91347a80e1e8034790d25e2341780979de246770911d2048760521d61447401603a014748521c00447280503a038728131d015c73a111ce0347300b1c8024712d71c425c6f8101c004c6f85521445f84116e0c45a81115df245679914ddab56768959af15f69c56d8d1575dc54dd514f71c52dc31476f450dae05f69816d8c0575d814dd404f71812dc20476f010cbb01f2e806c8401717804db835d6c8d55b02363d44945c0126d1161b24546c2d51b02546dad15b62456b88dd4993b3ce4dd4912b3cc49c580123504d19e0346a0171a00541c84d1a234a680d199e25634a119aac576a8d5da634769096d7f25751692cefa475148ecef237342518d01361b04999c8466700d99034d660d15942564ca0e99425c628571841506411b18e4606205b18216062a91d8a147,
    0x20e25585a8d51793545a0d63cb55938d155393b4564dd5283b4520dcc301f30806c8c01719804e00b648dad51e02348ead5a00b46838d160aa355464e5508397ead724646c802d723a26c9145b2431609101b2420608f9179031254080960e5648ead723a26c7788d236b4e8d8979dc2344064d5011254020d5000258c01a21e0548c05b22e0546780d2200508a91b22836c6509b22616c8905821c0508805421e05c870590fa134928d7e4835d900d5df23558f0d36383478d0d15da2368cc57e2d15b88c55e1b1536ac52d931475364ed119373e44963205f8b016e2205786814daa04b64811d4c83b4420dcf80252fc07cbe01b22005c620138491a20e45485ad52162547c0d521256c809591e4c647909920e356808d56024587b91420ab6c8289b20916c81c5820806c818181fb1507e8141fe05c] 22 7) 5 11 6
def r9_trace := dagTraceF r9_mask r9_stock 8 r9_forest
set_option maxHeartbeats 0 in
def r9_sym0 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r9_sym1 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeaeab6ca689e68e29648607de75c6da6585d65544d24503ce2ca34c2481c60c2144040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeaeab6ca689e68e29648607de75c6da6585d65544d24503ce2ca34c2481c60c2144040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r9_sym2 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa683ce34c2ca2487de75c6da6585d65544d24509e69648e28601c61440c2040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa683ce34c2ca2487de75c6da6585d65544d24509e69648e28601c61440c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r9_sym3 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeaeab6ca683ce2ca34c2487de75c6da6585d65544d24509e68e29648601c60c2144040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeaeab6ca683ce2ca34c2487de75c6da6585d65544d24509e68e29648601c60c2144040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r9_syms : List (TableSymmetry r9_mask r9_goal) := [
  ⟨(⟨r9_sym0, by decide +kernel⟩, rowCanon r9_sym0 r9_mask), fun _ => rfl⟩,
  ⟨(⟨r9_sym1, by decide +kernel⟩, rowCanon r9_sym1 r9_mask), fun _ => rfl⟩,
  ⟨(⟨r9_sym2, by decide +kernel⟩, rowCanon r9_sym2 r9_mask), fun _ => rfl⟩,
  ⟨(⟨r9_sym3, by decide +kernel⟩, rowCanon r9_sym3 r9_mask), fun _ => rfl⟩]
def r9_profile : Nat → Nat := unpackPagedWidths [
    (7, 0xc007e4040091f1f842803f18f620a1c1030000080043e085020800640000078f8000080083010208080021cfe000190002a01037ff83),
    (7, 0x2e0013f06709bc180473f82700047b001017e00000737e136083427c8038f007e0003e000003f8010048840042fff01f020a01e403f),
    (7, 0xf1e3f81ce060e1fe030c2218006703df0effe03220058c06405601782050977276c07efc03f804010c00017ff80099d36100fd00040fc020),
    (7, 0x1000000083d8000000810e081030ebd7a103840008204041c2070800387f807e01c01ceff11cc3e000003fff81fe071010b840015f830b7),
    (7, 0xfffc3fb0200081001c087081f30003800800083080000737f0214007f1ec0810214081)] 6
def r9_ref := symDagRef r9_mask r9_goal 296 2 r9_syms r9_trace r9_links
def r9_check : Nat → Bool := fun i => checkNodeViaF r9_mask r9_goal (chooseBounds r9_bounds (r9_profile i)) r9_trace r9_ref i
set_option maxHeartbeats 0 in
theorem r9_roots : dagCheckRootsF r9_mask r9_goal r9_bounds
    (r9_ref 0) r9_stock 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b0 : treeBlockF 0 12 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b12 : treeBlockF 12 24 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b24 : treeBlockF 24 36 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b36 : treeBlockF 36 48 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b48 : treeBlockF 48 60 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b60 : treeBlockF 60 72 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b72 : treeBlockF 72 84 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b84 : treeBlockF 84 96 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b96 : treeBlockF 96 108 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b108 : treeBlockF 108 120 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b120 : treeBlockF 120 132 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b132 : treeBlockF 132 144 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b144 : treeBlockF 144 156 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b156 : treeBlockF 156 168 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b168 : treeBlockF 168 180 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b180 : treeBlockF 180 192 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b192 : treeBlockF 192 204 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b204 : treeBlockF 204 216 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b216 : treeBlockF 216 228 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b228 : treeBlockF 228 240 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b240 : treeBlockF 240 252 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b252 : treeBlockF 252 264 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b264 : treeBlockF 264 276 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b276 : treeBlockF 276 288 r9_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r9_b288 : treeBlockF 288 296 r9_check = true := by decide +kernel
theorem r9_nodes : ∀ i, 0 ≤ i → i < 296 → r9_check i = true :=
  joinBlockSpecs
    (joinBlockSpecs
      (joinBlockSpecs
        (joinBlockSpecs
          (blockSpec r9_b0)
          (joinBlockSpecs
            (blockSpec r9_b12)
            (blockSpec r9_b24)))
        (joinBlockSpecs
          (blockSpec r9_b36)
          (joinBlockSpecs
            (blockSpec r9_b48)
            (blockSpec r9_b60))))
      (joinBlockSpecs
        (joinBlockSpecs
          (blockSpec r9_b72)
          (joinBlockSpecs
            (blockSpec r9_b84)
            (blockSpec r9_b96)))
        (joinBlockSpecs
          (blockSpec r9_b108)
          (joinBlockSpecs
            (blockSpec r9_b120)
            (blockSpec r9_b132)))))
    (joinBlockSpecs
      (joinBlockSpecs
        (joinBlockSpecs
          (blockSpec r9_b144)
          (joinBlockSpecs
            (blockSpec r9_b156)
            (blockSpec r9_b168)))
        (joinBlockSpecs
          (blockSpec r9_b180)
          (joinBlockSpecs
            (blockSpec r9_b192)
            (blockSpec r9_b204))))
      (joinBlockSpecs
        (joinBlockSpecs
          (blockSpec r9_b216)
          (joinBlockSpecs
            (blockSpec r9_b228)
            (blockSpec r9_b240)))
        (joinBlockSpecs
          (joinBlockSpecs
            (blockSpec r9_b252)
            (blockSpec r9_b264))
          (joinBlockSpecs
            (blockSpec r9_b276)
            (blockSpec r9_b288)))))
theorem r9_known : KnownBin r9_bounds :=
  knownCons r0_lower (
  knownCons r1_lower (
  knownCons r3_lower (
  knownCons r5_lower (
  knownCons r7_lower (
  knownCons r4_lower (
  knownCons r8_lower (
  knownNil)))))))
theorem r9_lower : LowerBin r9_mask r9_stock r9_goal 9 :=
  lowerDagRefF (profile := r9_profile) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) r9_known r9_sub r9_goals
    (symDagRef_sound (by decide +kernel) r9_syms r9_trace r9_links)
    r9_roots r9_nodes

def r10_mask : Nat := 0xf0f0f0f0f0f0f0f0
def r10_stock : List Nat := [0xf0f0f0f0, 0xf0f00000f0f0, 0xf000f000f000f0, 0x3030303030303030, 0x5050505050505050]
def r10_goal : Nat := 0x10105000505070
def r10_rows : Fin 64 → Fin 64 := decodeRows 0x10530d51571d18738f59779f000000000000000000000000925b2dd35f3d9a7bafdb7fbf
set_option maxHeartbeats 0 in
theorem r10_lower : LowerBin r10_mask r10_stock r10_goal 9 := by
  apply lowerBin_of_rowPull r10_rows (stock' := r9_stock)
  · have hall : r10_stock.all (fun w => availBF r9_stock
        (rowCanon r10_rows r10_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r10_rows r10_mask = r9_mask := by decide +kernel
    have hg : rowCanon r10_rows r10_mask r10_goal = r9_goal := by decide +kernel
    rw [hm, hg]
    exact r9_lower

def r11_mask : Nat := 0xcccccccccccccccc
def r11_stock : List Nat := [0xcccccccc, 0xcccc0000cccc, 0xcc00cc00cc00cc, 0xc0c0c0c0c0c0c0c, 0x4444444444444444]
def r11_goal : Nat := 0x404440044444c
def r11_rows : Fin 64 → Fin 64 := decodeRows 0x8328b49369b18738f59779f0000000000000000000000008a3aabcb3ebb9a7bafdb7fbf
set_option maxHeartbeats 0 in
theorem r11_lower : LowerBin r11_mask r11_stock r11_goal 9 := by
  apply lowerBin_of_rowPull r11_rows (stock' := r9_stock)
  · have hall : r11_stock.all (fun w => availBF r9_stock
        (rowCanon r11_rows r11_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r11_rows r11_mask = r9_mask := by decide +kernel
    have hg : rowCanon r11_rows r11_mask r11_goal = r9_goal := by decide +kernel
    rw [hm, hg]
    exact r9_lower

def r12_mask : Nat := 0xff00ff00ff00ff
def r12_stock : List Nat := [0xff00ff, 0xff000000ff, 0xf000f000f000f, 0x33003300330033, 0x55005500550055]
def r12_goal : Nat := 0x1700570057007f
def r12_rows : Fin 64 → Fin 64 := decodeRows 0x208208208208208208208208df6d74cf2c709e69648e28602082082082082082082082085d65544d24501c61440c2040
set_option maxHeartbeats 0 in
theorem r12_lower : LowerBin r12_mask r12_stock r12_goal 9 := by
  apply lowerBin_of_rowPull r12_rows (stock' := r9_stock)
  · have hall : r12_stock.all (fun w => availBF r9_stock
        (rowCanon r12_rows r12_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r12_rows r12_mask = r9_mask := by decide +kernel
    have hg : rowCanon r12_rows r12_mask r12_goal = r9_goal := by decide +kernel
    rw [hm, hg]
    exact r9_lower

def r13_mask : Nat := 0xf0f0f0f
def r13_stock : List Nat := [0xf0f, 0xf000f, 0x3030303, 0x5050505]
def r13_goal : Nat := 0x107070f
def r13_bounds : List (Nat × List Nat × Nat × Nat) := []
theorem r13_sub : ∀ b ∈ r13_bounds, r13_mask &&& b.1 = b.1 := by
  have hall : r13_bounds.all (fun b => Nat.beq (Nat.land r13_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r13_goals : ∀ b ∈ r13_bounds, canon b.1 r13_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r13_bounds.all (fun b => Nat.beq (canonF b.1 r13_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r13_forest : Nat → Nat × Nat := unpackForestRelative (unpackPagedWidths [
    (16, 0x193a152d103e0c360826041ed81b3a3e363a0b4807402a36094c05441e32183a043408300424083604199c17042c9125081e041d8524803e0924044c743d703c1524104c041408440434583a04145036152404140c4c041404443835081504142c340c4c0844041c1c32181e1124041408340414041d0413000f)] 6) 10
def r13_links : Nat → Nat → Option Nat := unpackLinksPaged (unpackPaged [
    0x2d836a1b40da02cc35c59aa4d026813409a04c0a6012c290347863c11a28a1c312104d796b0340da00d005c62e01684b405622b01504a8054029854829c44e026852c49604a0a5012428664302180f8a7c03e01f00e4a7203711b80d826c03220ce4070001] 13 6)
  (unpackPaged [
    0xd423ed023ac4236b8232b554aa5546b513aa5136a012e1c12db444aa4446b403aa4036a102e1d02da101ea001995012940118801038444380349802c8043d7043a5843650435344348002d7002a5802650025340249001e8c01d4c43414024801247c04c484446003468034140246801414014701246c04c6404460034580144c03c440344c01444014501244804c400442603c1102c1001c1101d1001a3901638015340142c04c280442603c2502c2401c1443414024140141812410444100340c0140912d0812a9512694125881248444e7844d7444c5c44a544463c44530444204428403e7803d7403c5c03a540363c03530034200321d02e0902d1c01e0801ddb63fdaa3b9ea3706a33db13fd9d3b9dd3705d33da52fd992b9d92705923dac3fd8c3b9cc3704c33da02fd882b9c82704823d901fd801b9c017040130000f,
    0x240149802424028180101812426c4c604442603c60034f054ab4d46f013ab4936ed12eec12da012508122e844ed5c4ae44465cc42e803ed583ae40365c832e0026a0025dc01e0801dcc348c8340b1924b0824ada34c014cbc14460924ac8346181470010b00341402414120148201581061930ac920ac030a80240c02c1801cd464ed064ac4646b8642] 20 7) 5 10 6
def r13_trace := dagTraceF r13_mask r13_stock 6 r13_forest
set_option maxHeartbeats 0 in
def r13_sym0 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym1 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d96985d65544d14903ce34c2c92881c61440c1080
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d96985d65544d14903ce34c2c92881c61440c1080
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym2 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da4d25d65546584503ce34c2ca0c21c6144248040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da4d25d65546584503ce34c2ca0c21c6144248040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym3 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d94d15d65546984903ce34c2c90c11c6144288080
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d36925d65546516103ce34c2c32821c6144241200
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym4 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65542ca2483ce34c4d24501c61440c2040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65542ca2483ce34c4d24501c61440c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym5 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d96985d65542c92883ce34c4d14901c61440c1080
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d96985d65542c92883ce34c4d14901c61440c1080
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym6 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da2ca5d65546582483ce34c4d20c21c6144450040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da4d25d65542ca0c23ce34c6584501c6144248040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym7 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d92c95d65546982883ce34c4d10c11c6144490080
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d36925d65542c32823ce34c6516101c6144241200
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym8 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da4d25d65542ca0c23ce34c6584501c6144248040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da2ca5d65546582483ce34c4d20c21c6144450040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym9 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da2ca5d65544d20c23ce34c6582481c6144450040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da2ca5d65544d20c23ce34c6582481c6144450040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym10 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d32c35d65546922823ce34c6512411c6144610200
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d32c35d65546922823ce34c6512411c6144610200
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym11 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d94d15d65542c90c13ce34c6984901c6144288080
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6cb68a5d65546496083ce34c4c34821c6144441400
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym12 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d92c95d65544d10c13ce34c6982881c6144490080
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6cb68a5d65544c34823ce34c6496081c6144441400
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_sym13 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6d32c35d65546512413ce34c6922821c6144610200
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6cb4c35d655468a4823ce34c6494411c6144608400
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r13_syms : List (TableSymmetry r13_mask r13_goal) := [
  ⟨(⟨r13_sym0, by decide +kernel⟩, rowCanon r13_sym0 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym1, by decide +kernel⟩, rowCanon r13_sym1 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym2, by decide +kernel⟩, rowCanon r13_sym2 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym3, by decide +kernel⟩, rowCanon r13_sym3 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym4, by decide +kernel⟩, rowCanon r13_sym4 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym5, by decide +kernel⟩, rowCanon r13_sym5 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym6, by decide +kernel⟩, rowCanon r13_sym6 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym7, by decide +kernel⟩, rowCanon r13_sym7 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym8, by decide +kernel⟩, rowCanon r13_sym8 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym9, by decide +kernel⟩, rowCanon r13_sym9 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym10, by decide +kernel⟩, rowCanon r13_sym10 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym11, by decide +kernel⟩, rowCanon r13_sym11 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym12, by decide +kernel⟩, rowCanon r13_sym12 r13_mask), fun _ => rfl⟩,
  ⟨(⟨r13_sym13, by decide +kernel⟩, rowCanon r13_sym13 r13_mask), fun _ => rfl⟩]
def r13_profile : Nat → Nat := unpackPagedWidths [
    (1, 0x0)] 6
def r13_ref := symDagRef r13_mask r13_goal 61 4 r13_syms r13_trace r13_links
def r13_check : Nat → Bool := fun i => checkNodeViaF r13_mask r13_goal (chooseBounds r13_bounds (r13_profile i)) r13_trace r13_ref i
set_option maxHeartbeats 0 in
theorem r13_roots : dagCheckRootsF r13_mask r13_goal r13_bounds
    (r13_ref 0) r13_stock 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b0 : treeBlockF 0 12 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b12 : treeBlockF 12 24 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b24 : treeBlockF 24 36 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b36 : treeBlockF 36 48 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b48 : treeBlockF 48 60 r13_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r13_b60 : treeBlockF 60 61 r13_check = true := by decide +kernel
theorem r13_nodes : ∀ i, 0 ≤ i → i < 61 → r13_check i = true :=
  joinBlockSpecs
    (joinBlockSpecs
      (blockSpec r13_b0)
      (joinBlockSpecs
        (blockSpec r13_b12)
        (blockSpec r13_b24)))
    (joinBlockSpecs
      (blockSpec r13_b36)
      (joinBlockSpecs
        (blockSpec r13_b48)
        (blockSpec r13_b60)))
theorem r13_known : KnownBin r13_bounds :=
  knownNil
theorem r13_lower : LowerBin r13_mask r13_stock r13_goal 7 :=
  lowerDagRefF (profile := r13_profile) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) r13_known r13_sub r13_goals
    (symDagRef_sound (by decide +kernel) r13_syms r13_trace r13_links)
    r13_roots r13_nodes

def r14_mask : Nat := 0x5555555500000000
def r14_stock : List Nat := [0x555500000000, 0x55005500000000, 0x505050500000000, 0x1111111100000000]
def r14_goal : Nat := 0x115155500000000
def r14_rows : Fin 64 → Fin 64 := decodeRows 0xfbceb8000000db4cb0000000bacaa80000009a48a0
set_option maxHeartbeats 0 in
theorem r14_lower : LowerBin r14_mask r14_stock r14_goal 7 := by
  apply lowerBin_of_rowPull r14_rows (stock' := r13_stock)
  · have hall : r14_stock.all (fun w => availBF r13_stock
        (rowCanon r14_rows r14_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r14_rows r14_mask = r13_mask := by decide +kernel
    have hg : rowCanon r14_rows r14_mask r14_goal = r13_goal := by decide +kernel
    rw [hm, hg]
    exact r13_lower

def r15_mask : Nat := 0x5555555555555555
def r15_stock : List Nat := [0x55555555, 0x555500005555, 0x55005500550055, 0x505050505050505, 0x1111111111111111]
def r15_goal : Nat := 0x115155501555555
def r15_bounds : List (Nat × List Nat × Nat × Nat) := [(0x5555555500000000, [0x555500000000, 0x55005500000000, 0x505050500000000, 0x1111111100000000], 7, 0x115155500000000)]
theorem r15_sub : ∀ b ∈ r15_bounds, r15_mask &&& b.1 = b.1 := by
  have hall : r15_bounds.all (fun b => Nat.beq (Nat.land r15_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r15_goals : ∀ b ∈ r15_bounds, canon b.1 r15_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r15_bounds.all (fun b => Nat.beq (canonF b.1 r15_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r15_forest : Nat → Nat × Nat := fun _ => (0, 0)
def r15_links : Nat → Nat → Option Nat := fun _ _ => none
def r15_trace := dagTraceF r15_mask r15_stock 7 r15_forest
def r15_check : Nat → Bool := dagCheckNodeF r15_mask r15_goal r15_bounds 0 r15_trace r15_links
set_option maxHeartbeats 0 in
theorem r15_roots : dagCheckRootsF r15_mask r15_goal r15_bounds
    (dagRefF 0 r15_trace r15_links 0) r15_stock 7 = true := by decide +kernel
theorem r15_nodes : ∀ i, 0 ≤ i → i < 0 → r15_check i = true :=
  fun i _ hi => absurd hi (Nat.not_lt_zero i)
theorem r15_known : KnownBin r15_bounds :=
  knownCons r14_lower (
  knownNil)
theorem r15_lower : LowerBin r15_mask r15_stock r15_goal 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r15_known r15_sub r15_goals r15_roots r15_nodes

def r16_mask : Nat := 0xaaaaaaaaaaaaaaaa
def r16_stock : List Nat := [0xaaaaaaaa, 0xaaaa0000aaaa, 0xaa00aa00aa00aa, 0xa0a0a0a0a0a0a0a, 0x2222222222222222]
def r16_goal : Nat := 0x202020002022a
def r16_rows : Fin 64 → Fin 64 := decodeRows 0x100901101900300b01301b00500d01501d00700f01701f02102903103902302b03303b02502d03503d02702f03703f
set_option maxHeartbeats 0 in
theorem r16_lower : LowerBin r16_mask r16_stock r16_goal 8 := by
  apply lowerBin_of_rowPull r16_rows (stock' := r15_stock)
  · have hall : r16_stock.all (fun w => availBF r15_stock
        (rowCanon r16_rows r16_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r16_rows r16_mask = r15_mask := by decide +kernel
    have hg : rowCanon r16_rows r16_mask r16_goal = r15_goal := by decide +kernel
    rw [hm, hg]
    exact r15_lower

def r17_mask : Nat := 0xf0f0f0f0f0f0f0f
def r17_stock : List Nat := [0xf0f0f0f, 0xf0f00000f0f, 0xf000f000f000f, 0x303030303030303, 0x505050505050505]
def r17_goal : Nat := 0x10707070107070f
def r17_bounds : List (Nat × List Nat × Nat × Nat) := [(0xf0f0f0f, [0xf0f, 0xf000f, 0x3030303, 0x5050505], 7, 0x107070f)]
theorem r17_sub : ∀ b ∈ r17_bounds, r17_mask &&& b.1 = b.1 := by
  have hall : r17_bounds.all (fun b => Nat.beq (Nat.land r17_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r17_goals : ∀ b ∈ r17_bounds, canon b.1 r17_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r17_bounds.all (fun b => Nat.beq (canonF b.1 r17_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r17_forest : Nat → Nat × Nat := fun _ => (0, 0)
def r17_links : Nat → Nat → Option Nat := fun _ _ => none
def r17_trace := dagTraceF r17_mask r17_stock 7 r17_forest
def r17_check : Nat → Bool := dagCheckNodeF r17_mask r17_goal r17_bounds 0 r17_trace r17_links
set_option maxHeartbeats 0 in
theorem r17_roots : dagCheckRootsF r17_mask r17_goal r17_bounds
    (dagRefF 0 r17_trace r17_links 0) r17_stock 7 = true := by decide +kernel
theorem r17_nodes : ∀ i, 0 ≤ i → i < 0 → r17_check i = true :=
  fun i _ hi => absurd hi (Nat.not_lt_zero i)
theorem r17_known : KnownBin r17_bounds :=
  knownCons r13_lower (
  knownNil)
theorem r17_lower : LowerBin r17_mask r17_stock r17_goal 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r17_known r17_sub r17_goals r17_roots r17_nodes

def r18_mask : Nat := 0x33333333
def r18_stock : List Nat := [0x3333, 0x330033, 0x3030303, 0x11111111]
def r18_goal : Nat := 0x1131333
def r18_rows : Fin 64 → Fin 64 := decodeRows 0x8208208208208208208208208208208208208208208208208208275c65808208255445008208234c248082082144040
set_option maxHeartbeats 0 in
theorem r18_lower : LowerBin r18_mask r18_stock r18_goal 7 := by
  apply lowerBin_of_rowPull r18_rows (stock' := r13_stock)
  · have hall : r18_stock.all (fun w => availBF r13_stock
        (rowCanon r18_rows r18_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r18_rows r18_mask = r13_mask := by decide +kernel
    have hg : rowCanon r18_rows r18_mask r18_goal = r13_goal := by decide +kernel
    rw [hm, hg]
    exact r13_lower

def r19_mask : Nat := 0x4444444411111111
def r19_stock : List Nat := [0x11111111, 0x444400001111, 0x44004400110011, 0x404040401010101]
def r19_goal : Nat := 0x4044401111111
def r19_rows : Fin 64 → Fin 64 := decodeRows 0x41041041041041041041041041041041041041041041041041041fbadb2041041baa9a2041041718510041041308100
set_option maxHeartbeats 0 in
theorem r19_lower : LowerBin r19_mask r19_stock r19_goal 7 := by
  apply lowerBin_of_rowPull r19_rows (stock' := r13_stock)
  · have hall : r19_stock.all (fun w => availBF r13_stock
        (rowCanon r19_rows r19_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r19_rows r19_mask = r13_mask := by decide +kernel
    have hg : rowCanon r19_rows r19_mask r19_goal = r13_goal := by decide +kernel
    rw [hm, hg]
    exact r13_lower

def r20_mask : Nat := 0xc0c0c0c030303030
def r20_stock : List Nat := [0x30303030, 0xc0c000003030, 0xc000c000300030, 0x4040404010101010]
def r20_goal : Nat := 0x4000101030
def r20_rows : Fin 64 → Fin 64 := decodeRows 0x10530d00000051571d0000009a7baf000000db7fbf
set_option maxHeartbeats 0 in
theorem r20_lower : LowerBin r20_mask r20_stock r20_goal 7 := by
  apply lowerBin_of_rowPull r20_rows (stock' := r13_stock)
  · have hall : r20_stock.all (fun w => availBF r13_stock
        (rowCanon r20_rows r20_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r20_rows r20_mask = r13_mask := by decide +kernel
    have hg : rowCanon r20_rows r20_mask r20_goal = r13_goal := by decide +kernel
    rw [hm, hg]
    exact r13_lower

def r21_mask : Nat := 0xcc00cc0033003300
def r21_stock : List Nat := [0x33003300, 0xcc0000003300, 0xc000c0003000300, 0x4400440011001100]
def r21_goal : Nat := 0x40001001300
def r21_rows : Fin 64 → Fin 64 := decodeRows 0x20930d00000061971d000000aabbaf000000ebbfbf
set_option maxHeartbeats 0 in
theorem r21_lower : LowerBin r21_mask r21_stock r21_goal 7 := by
  apply lowerBin_of_rowPull r21_rows (stock' := r13_stock)
  · have hall : r21_stock.all (fun w => availBF r13_stock
        (rowCanon r21_rows r21_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r21_rows r21_mask = r13_mask := by decide +kernel
    have hg : rowCanon r21_rows r21_mask r21_goal = r13_goal := by decide +kernel
    rw [hm, hg]
    exact r13_lower

def r22_mask : Nat := 0xcccc000033330000
def r22_stock : List Nat := [0x33330000, 0xcc000000330000, 0xc0c000003030000, 0x4444000011110000]
def r22_goal : Nat := 0x4000001130000
def r22_rows : Fin 64 → Fin 64 := decodeRows 0x41151500000061971d000000cb3db7000000ebbfbf
set_option maxHeartbeats 0 in
theorem r22_lower : LowerBin r22_mask r22_stock r22_goal 7 := by
  apply lowerBin_of_rowPull r22_rows (stock' := r13_stock)
  · have hall : r22_stock.all (fun w => availBF r13_stock
        (rowCanon r22_rows r22_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r22_rows r22_mask = r13_mask := by decide +kernel
    have hg : rowCanon r22_rows r22_mask r22_goal = r13_goal := by decide +kernel
    rw [hm, hg]
    exact r13_lower

def r23_mask : Nat := 0xcccccccc00000000
def r23_stock : List Nat := [0xcccc00000000, 0xcc00cc00000000, 0xc0c0c0c00000000, 0x4444444400000000]
def r23_goal : Nat := 0x4044400000000
def r23_rows : Fin 64 → Fin 64 := decodeRows 0x8a39a7aabbafcb3db7ebbfbf
set_option maxHeartbeats 0 in
theorem r23_lower : LowerBin r23_mask r23_stock r23_goal 5 := by
  apply lowerBin_of_rowPull r23_rows (stock' := r4_stock)
  · have hall : r23_stock.all (fun w => availBF r4_stock
        (rowCanon r23_rows r23_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r23_rows r23_mask = r4_mask := by decide +kernel
    have hg : rowCanon r23_rows r23_mask r23_goal = r4_goal := by decide +kernel
    rw [hm, hg]
    exact r4_lower

def r24_mask : Nat := 0xcccc00003333
def r24_stock : List Nat := [0x3333, 0xcc00000033, 0xc0c00000303, 0x444400001111]
def r24_goal : Nat := 0x44400001333
def r24_rows : Fin 64 → Fin 64 := decodeRows 0x8208208208208208208208208208208208208208208208200110520930d0820820820828a39a7aabbaf082082082082
set_option maxHeartbeats 0 in
theorem r24_lower : LowerBin r24_mask r24_stock r24_goal 5 := by
  apply lowerBin_of_rowPull r24_rows (stock' := r2_stock)
  · have hall : r24_stock.all (fun w => availBF r2_stock
        (rowCanon r24_rows r24_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r24_rows r24_mask = r2_mask := by decide +kernel
    have hg : rowCanon r24_rows r24_mask r24_goal = r2_goal := by decide +kernel
    rw [hm, hg]
    exact r2_lower

def r25_mask : Nat := 0xcc00cc00330033
def r25_stock : List Nat := [0x330033, 0xcc00000033, 0xc000c00030003, 0x44004400110011]
def r25_goal : Nat := 0x4004400130033
def r25_rows : Fin 64 → Fin 64 := decodeRows 0x820820820820820820820820820820820820820820820820011054115150820820820828a39a7cb3db7082082082082
set_option maxHeartbeats 0 in
theorem r25_lower : LowerBin r25_mask r25_stock r25_goal 5 := by
  apply lowerBin_of_rowPull r25_rows (stock' := r2_stock)
  · have hall : r25_stock.all (fun w => availBF r2_stock
        (rowCanon r25_rows r25_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r25_rows r25_mask = r2_mask := by decide +kernel
    have hg : rowCanon r25_rows r25_mask r25_goal = r2_goal := by decide +kernel
    rw [hm, hg]
    exact r2_lower

def r26_mask : Nat := 0xc0c0c0c03030303
def r26_stock : List Nat := [0x3030303, 0xc0c00000303, 0xc000c00030003, 0x404040401010101]
def r26_goal : Nat := 0x4040401030303
def r26_rows : Fin 64 → Fin 64 := decodeRows 0x820820820820820820820820820820820820820820820820012094116190820820820828a3aabcb3ebb082082082082
set_option maxHeartbeats 0 in
theorem r26_lower : LowerBin r26_mask r26_stock r26_goal 5 := by
  apply lowerBin_of_rowPull r26_rows (stock' := r2_stock)
  · have hall : r26_stock.all (fun w => availBF r2_stock
        (rowCanon r26_rows r26_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r26_rows r26_mask = r2_mask := by decide +kernel
    have hg : rowCanon r26_rows r26_mask r26_goal = r2_goal := by decide +kernel
    rw [hm, hg]
    exact r2_lower

def r27_mask : Nat := 0x8888888822222222
def r27_stock : List Nat := [0x22222222, 0x888800002222, 0x88008800220022, 0x808080802020202]
def r27_goal : Nat := 0x20222
def r27_rows : Fin 64 → Fin 64 := decodeRows 0x6316726b36f47357767b77f
set_option maxHeartbeats 0 in
theorem r27_lower : LowerBin r27_mask r27_stock r27_goal 5 := by
  apply lowerBin_of_rowPull r27_rows (stock' := r4_stock)
  · have hall : r27_stock.all (fun w => availBF r4_stock
        (rowCanon r27_rows r27_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r27_rows r27_mask = r4_mask := by decide +kernel
    have hg : rowCanon r27_rows r27_mask r27_goal = r4_goal := by decide +kernel
    rw [hm, hg]
    exact r4_lower

def r28_mask : Nat := 0xcccccccc33333333
def r28_stock : List Nat := [0x33333333, 0xcccc00003333, 0xcc00cc00330033, 0xc0c0c0c03030303, 0x4444444411111111]
def r28_goal : Nat := 0x4044401131333
def r28_bounds : List (Nat × List Nat × Nat × Nat) := [(0x33333333, [0x3333, 0x330033, 0x3030303, 0x11111111], 7, 0x1131333), (0x4444444411111111, [0x11111111, 0x444400001111, 0x44004400110011, 0x404040401010101], 7, 0x4044401111111), (0xc0c0c0c030303030, [0x30303030, 0xc0c000003030, 0xc000c000300030, 0x4040404010101010], 7, 0x4000101030), (0xcc00cc0033003300, [0x33003300, 0xcc0000003300, 0xc000c0003000300, 0x4400440011001100], 7, 0x40001001300), (0xcccc000033330000, [0x33330000, 0xcc000000330000, 0xc0c000003030000, 0x4444000011110000], 7, 0x4000001130000), (0xcccccccc00000000, [0xcccc00000000, 0xcc00cc00000000, 0xc0c0c0c00000000, 0x4444444400000000], 5, 0x4044400000000), (0xcccc00003333, [0x3333, 0xcc00000033, 0xc0c00000303, 0x444400001111], 5, 0x44400001333), (0xcc00cc00330033, [0x330033, 0xcc00000033, 0xc000c00030003, 0x44004400110011], 5, 0x4004400130033), (0xc0c0c0c03030303, [0x3030303, 0xc0c00000303, 0xc000c00030003, 0x404040401010101], 5, 0x4040401030303), (0x8888888822222222, [0x22222222, 0x888800002222, 0x88008800220022, 0x808080802020202], 5, 0x20222)]
theorem r28_sub : ∀ b ∈ r28_bounds, r28_mask &&& b.1 = b.1 := by
  have hall : r28_bounds.all (fun b => Nat.beq (Nat.land r28_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r28_goals : ∀ b ∈ r28_bounds, canon b.1 r28_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r28_bounds.all (fun b => Nat.beq (canonF b.1 r28_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r28_forest : Nat → Nat × Nat := unpackForestRelative (unpackPagedWidths [
    (17, 0x322b02910a4ac0c6020a10e138609a093404a30613010a80842311b8ed2828b0084c11a30691812680846101382940168e08269c218415410a91b5f04220d58854bc205e0c2e8417010a4db470426028dd84bc0b55582f83160146e985e042e02d1d00a40854062f9a0e810a83c6e1a310b16810b81c56083702158406e0b58062f820d81036001f),
    (18, 0x82918d2c5b4a021004b46024d03946091881c5a041b80856040cc08318649c08341d168085c)] 6) 11
def r28_links : Nat → Nat → Option Nat := unpackLinksPaged (unpackPaged [
    0x7a377377076176076076075173273071262f6206206206025f15f05e156856055154148c4804803f93f03e13e03e03e03d13c131b3102f22e12e02862802712612602512412402312212202112102102102012002001a61a01911810bd01a001,
    0xa509d89c19c09939819629519509509508e78d17fe7f07e17e07d1] 12 6)
  (unpackPaged [
    0x8800c610034800171c184c7020f1c002c7c0911b885c6e00f1e04607004d1b92466e0519a8054600131dac61821169f84567a4d59e82567605089205a528159d004e720135b004c5e0115a00425c40d5700256211618004c5a00d168134642d6978b56640d29783465c2959702465821596004654094148347666d1d98a476608dc8a04a56811d420462240e9590375040d88802a56009d400261ef1741bc551801746305a4cc159300554a01507884a062119180443605784805c1ef5b9105623409b90825e2a01b890062400178f805d3c0170400553a0148dac58360130d0237183174c0c55180d74c03550e2118380362c1160a8237260170903472001507845f1a01504805c1811b858462141168404560e01b830056080d601845f48317d2035f380d1cc825e2e017ca005e2201487084a0a211c108461c00e8280370400d80c34f02c93e19a3702a53e1893786049d380430280ec0902b02006c0001f,
    0x10c56e90b18a82a6e3b09890a059900106800293a8086080539ab141f80539a0101f00439604d1e805378058248462901169d81628e01b9a00623a816a3005645117ce445f1cad7a2ab5388ad4a7834b9c0d2a6034694491a5014666014ce204b1c00e628033] 22 7) 4 11 5
def r28_trace := dagTraceF r28_mask r28_stock 9 r28_forest
set_option maxHeartbeats 0 in
def r28_sym0 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040
  invFun := decodeRows 0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r28_sym1 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cdf6e78efad74cf2c70beeb6c9e6a68aea9648e28607de75c6da5545d66584d24503ce34c2ca1441c62480c2040
  invFun := decodeRows 0xffef7cdf6e78efad74cf2c70beeb6c9e6a68aea9648e28607de75c6da5545d66584d24503ce34c2ca1441c62480c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r28_sym2 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cefae78beed74aeac70df6b6ccf2a689e69648e28607de75c6da6585d634c4d22483ce5542ca4501c61440c2040
  invFun := decodeRows 0xffef7cefae78beed74aeac70df6b6ccf2a689e69648e28607de75c6da6585d634c4d22483ce5542ca4501c61440c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r28_sym3 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cbeee78efad74aeac70df6b6c9e6a68cf29648e28607de75c6da34c5d66584d22483ce5542ca1441c64500c2040
  invFun := decodeRows 0xffef7cdf6e78beed749e6c70efab6ccf2a68aea9648e28607de75c6da5545d634c4d21443ce6582ca4501c62480c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r28_sym4 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xffef7cdf6e78beed749e6c70efab6ccf2a68aea9648e28607de75c6da5545d634c4d21443ce6582ca4501c62480c2040
  invFun := decodeRows 0xffef7cbeee78efad74aeac70df6b6c9e6a68cf29648e28607de75c6da34c5d66584d22483ce5542ca1441c64500c2040
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r28_sym5 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xfddf7ced9e78dd5d74cd1c70bcdb6cac9a689c59648c18607def9c6dae985d6d944d2c903ceb8c2caa881c69840c2880
  invFun := decodeRows 0xfddf7ced9e78dd5d74cd1c70bcdb6cac9a689c59648c18607def9c6dae985d6d944d2c903ceb8c2caa881c69840c2880
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r28_sym6 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xfddf7ced9e78bcdd74ac9c70dd5b6ccd1a689c59648c18607def9c6dae985d6b8c4d2a883ced942cac901c69840c2880
  invFun := decodeRows 0xfddf7ced9e78bcdd74ac9c70dd5b6ccd1a689c59648c18607def9c6dae985d6b8c4d2a883ced942cac901c69840c2880
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r28_sym7 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xfddf7cbcde78ed9d74ac9c70dd5b6c9c5a68cd19648c18607def9c6dab8c5d6e984d2a883ced942ca9841c6c900c2880
  invFun := decodeRows 0xfddf7cdd5e78bcdd749c5c70ed9b6ccd1a68ac99648c18607def9c6dad945d6b8c4d29843cee982cac901c6a880c2880
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r28_sym8 : Equiv.Perm (Fin 64) where
  toFun := decodeRows 0xfddf7cdd5e78bcdd749c5c70ed9b6ccd1a68ac99648c18607def9c6dad945d6b8c4d29843cee982cac901c6a880c2880
  invFun := decodeRows 0xfddf7cbcde78ed9d74ac9c70dd5b6c9c5a68cd19648c18607def9c6dab8c5d6e984d2a883ced942ca9841c6c900c2880
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide +kernel
set_option maxHeartbeats 0 in
def r28_syms : List (TableSymmetry r28_mask r28_goal) := [
  ⟨(⟨r28_sym0, by decide +kernel⟩, rowCanon r28_sym0 r28_mask), fun _ => rfl⟩,
  ⟨(⟨r28_sym1, by decide +kernel⟩, rowCanon r28_sym1 r28_mask), fun _ => rfl⟩,
  ⟨(⟨r28_sym2, by decide +kernel⟩, rowCanon r28_sym2 r28_mask), fun _ => rfl⟩,
  ⟨(⟨r28_sym3, by decide +kernel⟩, rowCanon r28_sym3 r28_mask), fun _ => rfl⟩,
  ⟨(⟨r28_sym4, by decide +kernel⟩, rowCanon r28_sym4 r28_mask), fun _ => rfl⟩,
  ⟨(⟨r28_sym5, by decide +kernel⟩, rowCanon r28_sym5 r28_mask), fun _ => rfl⟩,
  ⟨(⟨r28_sym6, by decide +kernel⟩, rowCanon r28_sym6 r28_mask), fun _ => rfl⟩,
  ⟨(⟨r28_sym7, by decide +kernel⟩, rowCanon r28_sym7 r28_mask), fun _ => rfl⟩,
  ⟨(⟨r28_sym8, by decide +kernel⟩, rowCanon r28_sym8 r28_mask), fun _ => rfl⟩]
def r28_profile : Nat → Nat := unpackPagedWidths [
    (10, 0xffccd7340b3ac3810c000111f0201cbfc990040001e39064d90fc6c371ff0fc8047cbf00673354242461f010ff000651fcca1fc00b5bbf001fc6fc004933f000008ed0c00011a298c1fc00603bf0fc1f),
    (10, 0xed37f7f0fe7f37c5f8ad2582d0d3ff3f17c407f401)] 6
def r28_ref := symDagRef r28_mask r28_goal 81 4 r28_syms r28_trace r28_links
def r28_check : Nat → Bool := fun i => checkNodeViaF r28_mask r28_goal (chooseBounds r28_bounds (r28_profile i)) r28_trace r28_ref i
set_option maxHeartbeats 0 in
theorem r28_roots : dagCheckRootsF r28_mask r28_goal r28_bounds
    (r28_ref 0) r28_stock 9 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b0 : treeBlockF 0 12 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b12 : treeBlockF 12 24 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b24 : treeBlockF 24 36 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b36 : treeBlockF 36 48 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b48 : treeBlockF 48 60 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b60 : treeBlockF 60 72 r28_check = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r28_b72 : treeBlockF 72 81 r28_check = true := by decide +kernel
theorem r28_nodes : ∀ i, 0 ≤ i → i < 81 → r28_check i = true :=
  joinBlockSpecs
    (joinBlockSpecs
      (blockSpec r28_b0)
      (joinBlockSpecs
        (blockSpec r28_b12)
        (blockSpec r28_b24)))
    (joinBlockSpecs
      (joinBlockSpecs
        (blockSpec r28_b36)
        (blockSpec r28_b48))
      (joinBlockSpecs
        (blockSpec r28_b60)
        (blockSpec r28_b72)))
theorem r28_known : KnownBin r28_bounds :=
  knownCons r18_lower (
  knownCons r19_lower (
  knownCons r20_lower (
  knownCons r21_lower (
  knownCons r22_lower (
  knownCons r23_lower (
  knownCons r24_lower (
  knownCons r25_lower (
  knownCons r26_lower (
  knownCons r27_lower (
  knownNil))))))))))
theorem r28_lower : LowerBin r28_mask r28_stock r28_goal 10 :=
  lowerDagRefF (profile := r28_profile) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) r28_known r28_sub r28_goals
    (symDagRef_sound (by decide +kernel) r28_syms r28_trace r28_links)
    r28_roots r28_nodes

def r29_mask : Nat := 0xffff00000000ffff
def r29_stock : List Nat := [0xffff, 0xff0000000000ff, 0xf0f000000000f0f, 0x3333000000003333, 0x5555000000005555]
def r29_goal : Nat := 0x11700000000577f
def r29_rows : Fin 64 → Fin 64 := decodeRows 0x141008341010541018741020941028b41030d41038f410410c31410cb3410d35410db7410e39410ebb410f3d410fbf
set_option maxHeartbeats 0 in
theorem r29_lower : LowerBin r29_mask r29_stock r29_goal 10 := by
  apply lowerBin_of_rowPull r29_rows (stock' := r28_stock)
  · have hall : r29_stock.all (fun w => availBF r28_stock
        (rowCanon r29_rows r29_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r29_rows r29_mask = r28_mask := by decide +kernel
    have hg : rowCanon r29_rows r29_mask r29_goal = r28_goal := by decide +kernel
    rw [hm, hg]
    exact r28_lower

def r30_mask : Nat := 0xff00ff00ff00ff00
def r30_stock : List Nat := [0xff00ff00, 0xff000000ff00, 0xf000f000f000f00, 0x3300330033003300, 0x5500550055005500]
def r30_goal : Nat := 0x100170001005700
def r30_rows : Fin 64 → Fin 64 := decodeRows 0x20961900000028b69b00000030d71d00000038f79f000000a29e39000000aabebb000000b2df3d000000baffbf
set_option maxHeartbeats 0 in
theorem r30_lower : LowerBin r30_mask r30_stock r30_goal 8 := by
  apply lowerBin_of_rowPull r30_rows (stock' := r17_stock)
  · have hall : r30_stock.all (fun w => availBF r17_stock
        (rowCanon r30_rows r30_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r30_rows r30_mask = r17_mask := by decide +kernel
    have hg : rowCanon r30_rows r30_mask r30_goal = r17_goal := by decide +kernel
    rw [hm, hg]
    exact r17_lower

def r31_mask : Nat := 0x3333333333333333
def r31_stock : List Nat := [0x33333333, 0x333300003333, 0x33003300330033, 0x303030303030303, 0x1111111111111111]
def r31_goal : Nat := 0x113131301131333
def r31_rows : Fin 64 → Fin 64 := decodeRows 0x82082f7ce78082082d74c70082082b6ca6808208296486008208275c65808208255445008208234c248082082144040
set_option maxHeartbeats 0 in
theorem r31_lower : LowerBin r31_mask r31_stock r31_goal 8 := by
  apply lowerBin_of_rowPull r31_rows (stock' := r17_stock)
  · have hall : r31_stock.all (fun w => availBF r17_stock
        (rowCanon r31_rows r31_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r31_rows r31_mask = r17_mask := by decide +kernel
    have hg : rowCanon r31_rows r31_mask r31_goal = r17_goal := by decide +kernel
    rw [hm, hg]
    exact r17_lower

def r32_mask : Nat := 0xffff0000ffff0000
def r32_stock : List Nat := [0xffff0000, 0xff000000ff0000, 0xf0f00000f0f0000, 0x3333000033330000, 0x5555000055550000]
def r32_goal : Nat := 0x117000001570000
def r32_rows : Fin 64 → Fin 64 := decodeRows 0x41161900000049369b00000051571d00000059779f000000c31e39000000cb3ebb000000d35f3d000000db7fbf
set_option maxHeartbeats 0 in
theorem r32_lower : LowerBin r32_mask r32_stock r32_goal 8 := by
  apply lowerBin_of_rowPull r32_rows (stock' := r17_stock)
  · have hall : r32_stock.all (fun w => availBF r17_stock
        (rowCanon r32_rows r32_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r32_rows r32_mask = r17_mask := by decide +kernel
    have hg : rowCanon r32_rows r32_mask r32_goal = r17_goal := by decide +kernel
    rw [hm, hg]
    exact r17_lower

def r33_mask : Nat := 0xaaaaaaaa
def r33_stock : List Nat := [0xaaaa, 0xaa00aa, 0xa0a0a0a, 0x22222222]
def r33_goal : Nat := 0x2022a
def r33_rows : Fin 64 → Fin 64 := decodeRows 0x4314700000024b34f00000045355700000065b75f
set_option maxHeartbeats 0 in
theorem r33_lower : LowerBin r33_mask r33_stock r33_goal 7 := by
  apply lowerBin_of_rowPull r33_rows (stock' := r13_stock)
  · have hall : r33_stock.all (fun w => availBF r13_stock
        (rowCanon r33_rows r33_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r33_rows r33_mask = r13_mask := by decide +kernel
    have hg : rowCanon r33_rows r33_mask r33_goal = r13_goal := by decide +kernel
    rw [hm, hg]
    exact r13_lower

def r34_mask : Nat := 0xff00ff
def r34_stock : List Nat := [0xff, 0xf000f, 0x330033, 0x550055]
def r34_goal : Nat := 0x57007f
def r34_rows : Fin 64 → Fin 64 := decodeRows 0x2082082082082082082082082082082082082082082082082082082082082082082082085d65544d24501c61440c2040
set_option maxHeartbeats 0 in
theorem r34_lower : LowerBin r34_mask r34_stock r34_goal 5 := by
  apply lowerBin_of_rowPull r34_rows (stock' := r4_stock)
  · have hall : r34_stock.all (fun w => availBF r4_stock
        (rowCanon r34_rows r34_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r34_rows r34_mask = r4_mask := by decide +kernel
    have hg : rowCanon r34_rows r34_mask r34_goal = r4_goal := by decide +kernel
    rw [hm, hg]
    exact r4_lower

def r35_mask : Nat := 0xffffffff
def r35_stock : List Nat := [0xffff, 0xff00ff, 0xf0f0f0f, 0x33333333, 0x55555555]
def r35_goal : Nat := 0x157577f
def r35_bounds : List (Nat × List Nat × Nat × Nat) := [(0xaaaaaaaa, [0xaaaa, 0xaa00aa, 0xa0a0a0a, 0x22222222], 7, 0x2022a), (0x33333333, [0x3333, 0x330033, 0x3030303, 0x11111111], 7, 0x1131333), (0xf0f0f0f, [0xf0f, 0xf000f, 0x3030303, 0x5050505], 7, 0x107070f), (0xff00ff, [0xff, 0xf000f, 0x330033, 0x550055], 5, 0x57007f), (0xff00ff00, [0xff00, 0xf000f00, 0x33003300, 0x55005500], 5, 0x1005700), (0xffff, [0xff, 0xf0f, 0x3333, 0x5555], 5, 0x577f)]
theorem r35_sub : ∀ b ∈ r35_bounds, r35_mask &&& b.1 = b.1 := by
  have hall : r35_bounds.all (fun b => Nat.beq (Nat.land r35_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r35_goals : ∀ b ∈ r35_bounds, canon b.1 r35_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r35_bounds.all (fun b => Nat.beq (canonF b.1 r35_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r35_forest : Nat → Nat × Nat := unpackForestF 0x10fa1b42f4910981f 2 9
def r35_links : Nat → Nat → Option Nat := unpackLinksF 0x38e31c29301 0x410524a1f81b61721301f 6 3 9 3 4
def r35_trace := dagTraceF r35_mask r35_stock 8 r35_forest
def r35_check : Nat → Bool := dagCheckNodeF r35_mask r35_goal r35_bounds 6 r35_trace r35_links
set_option maxHeartbeats 0 in
theorem r35_roots : dagCheckRootsF r35_mask r35_goal r35_bounds
    (dagRefF 6 r35_trace r35_links 0) r35_stock 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r35_b0 : treeBlockF 0 6 r35_check = true := by decide +kernel
theorem r35_nodes : ∀ i, 0 ≤ i → i < 6 → r35_check i = true :=
  blockSpec r35_b0
theorem r35_known : KnownBin r35_bounds :=
  knownCons r33_lower (
  knownCons r18_lower (
  knownCons r13_lower (
  knownCons r34_lower (
  knownCons r2_lower (
  knownCons r4_lower (
  knownNil))))))
theorem r35_lower : LowerBin r35_mask r35_stock r35_goal 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r35_known r35_sub r35_goals r35_roots r35_nodes

def r36_mask : Nat := 0xffffffff00000000
def r36_stock : List Nat := [0xffff00000000, 0xff00ff00000000, 0xf0f0f0f00000000, 0x3333333300000000, 0x5555555500000000]
def r36_goal : Nat := 0x117175700000000
def r36_rows : Fin 64 → Fin 64 := decodeRows 0x821a29c31e398a3aabcb3ebb925b2dd35f3d9a7bafdb7fbf
set_option maxHeartbeats 0 in
theorem r36_lower : LowerBin r36_mask r36_stock r36_goal 9 := by
  apply lowerBin_of_rowPull r36_rows (stock' := r35_stock)
  · have hall : r36_stock.all (fun w => availBF r35_stock
        (rowCanon r36_rows r36_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r36_rows r36_mask = r35_mask := by decide +kernel
    have hg : rowCanon r36_rows r36_mask r36_goal = r35_goal := by decide +kernel
    rw [hm, hg]
    exact r35_lower

def r37_mask : Nat := 0x55005500aa00aa
def r37_stock : List Nat := [0xaa00aa, 0x55000000aa, 0x50005000a000a, 0x11001100220022]
def r37_goal : Nat := 0x1500550002002a
def r37_rows : Fin 64 → Fin 64 := decodeRows 0x5d54d10000001c50c1000000db4cb00000009a48a0
set_option maxHeartbeats 0 in
theorem r37_lower : LowerBin r37_mask r37_stock r37_goal 7 := by
  apply lowerBin_of_rowPull r37_rows (stock' := r13_stock)
  · have hall : r37_stock.all (fun w => availBF r13_stock
        (rowCanon r37_rows r37_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r37_rows r37_mask = r13_mask := by decide +kernel
    have hg : rowCanon r37_rows r37_mask r37_goal = r13_goal := by decide +kernel
    rw [hm, hg]
    exact r13_lower

def r38_mask : Nat := 0x50505050a0a0a0a
def r38_stock : List Nat := [0xa0a0a0a, 0x50500000a0a, 0x50005000a000a, 0x101010102020202]
def r38_goal : Nat := 0x10505050002020a
def r38_rows : Fin 64 → Fin 64 := decodeRows 0x6d94d10000002c90c1000000eb8cb0000000aa88a0
set_option maxHeartbeats 0 in
theorem r38_lower : LowerBin r38_mask r38_stock r38_goal 7 := by
  apply lowerBin_of_rowPull r38_rows (stock' := r13_stock)
  · have hall : r38_stock.all (fun w => availBF r13_stock
        (rowCanon r38_rows r38_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r38_rows r38_mask = r13_mask := by decide +kernel
    have hg : rowCanon r38_rows r38_mask r38_goal = r13_goal := by decide +kernel
    rw [hm, hg]
    exact r13_lower

def r39_mask : Nat := 0x1111111122222222
def r39_stock : List Nat := [0x22222222, 0x111100002222, 0x11001100220022, 0x101010102020202]
def r39_goal : Nat := 0x111111100020222
def r39_rows : Fin 64 → Fin 64 := decodeRows 0x759551000000349141000000f38d30000000b28920
set_option maxHeartbeats 0 in
theorem r39_lower : LowerBin r39_mask r39_stock r39_goal 7 := by
  apply lowerBin_of_rowPull r39_rows (stock' := r13_stock)
  · have hall : r39_stock.all (fun w => availBF r13_stock
        (rowCanon r39_rows r39_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r39_rows r39_mask = r13_mask := by decide +kernel
    have hg : rowCanon r39_rows r39_mask r39_goal = r13_goal := by decide +kernel
    rw [hm, hg]
    exact r13_lower

def r40_mask : Nat := 0x4444444488888888
def r40_stock : List Nat := [0x88888888, 0x444400008888, 0x44004400880088, 0x404040408080808]
def r40_goal : Nat := 0x4044400000008
def r40_rows : Fin 64 → Fin 64 := decodeRows 0x8a6aae000000cb6ebe0000000c72cf0000004d76df
set_option maxHeartbeats 0 in
theorem r40_lower : LowerBin r40_mask r40_stock r40_goal 7 := by
  apply lowerBin_of_rowPull r40_rows (stock' := r13_stock)
  · have hall : r40_stock.all (fun w => availBF r13_stock
        (rowCanon r40_rows r40_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r40_rows r40_mask = r13_mask := by decide +kernel
    have hg : rowCanon r40_rows r40_mask r40_goal = r13_goal := by decide +kernel
    rw [hm, hg]
    exact r13_lower

def r41_mask : Nat := 0x50505050a0a0a0a0
def r41_stock : List Nat := [0xa0a0a0a0, 0x50500000a0a0, 0x50005000a000a0, 0x1010101020202020]
def r41_goal : Nat := 0x10105000000020
def r41_rows : Fin 64 → Fin 64 := decodeRows 0x926b2e000000d36f3e00000014734f00000055775f
set_option maxHeartbeats 0 in
theorem r41_lower : LowerBin r41_mask r41_stock r41_goal 7 := by
  apply lowerBin_of_rowPull r41_rows (stock' := r13_stock)
  · have hall : r41_stock.all (fun w => availBF r13_stock
        (rowCanon r41_rows r41_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r41_rows r41_mask = r13_mask := by decide +kernel
    have hg : rowCanon r41_rows r41_mask r41_goal = r13_goal := by decide +kernel
    rw [hm, hg]
    exact r13_lower

def r42_mask : Nat := 0x55005500aa00aa00
def r42_stock : List Nat := [0xaa00aa00, 0x55000000aa00, 0x50005000a000a00, 0x1100110022002200]
def r42_goal : Nat := 0x100150000000200
def r42_rows : Fin 64 → Fin 64 := decodeRows 0xa2ab2e000000e3af3e00000024b34f00000065b75f
set_option maxHeartbeats 0 in
theorem r42_lower : LowerBin r42_mask r42_stock r42_goal 7 := by
  apply lowerBin_of_rowPull r42_rows (stock' := r13_stock)
  · have hall : r42_stock.all (fun w => availBF r13_stock
        (rowCanon r42_rows r42_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r42_rows r42_mask = r13_mask := by decide +kernel
    have hg : rowCanon r42_rows r42_mask r42_goal = r13_goal := by decide +kernel
    rw [hm, hg]
    exact r13_lower

def r43_mask : Nat := 0x55555555aaaaaaaa
def r43_stock : List Nat := [0xaaaaaaaa, 0x55550000aaaa, 0x55005500aa00aa, 0x50505050a0a0a0a, 0x1111111122222222]
def r43_goal : Nat := 0x11515550002022a
def r43_bounds : List (Nat × List Nat × Nat × Nat) := [(0x5555555500000000, [0x555500000000, 0x55005500000000, 0x505050500000000, 0x1111111100000000], 7, 0x115155500000000), (0xaaaaaaaa, [0xaaaa, 0xaa00aa, 0xa0a0a0a, 0x22222222], 7, 0x2022a), (0x55005500aa00aa, [0xaa00aa, 0x55000000aa, 0x50005000a000a, 0x11001100220022], 7, 0x1500550002002a), (0x50505050a0a0a0a, [0xa0a0a0a, 0x50500000a0a, 0x50005000a000a, 0x101010102020202], 7, 0x10505050002020a), (0x1111111122222222, [0x22222222, 0x111100002222, 0x11001100220022, 0x101010102020202], 7, 0x111111100020222), (0x4444444488888888, [0x88888888, 0x444400008888, 0x44004400880088, 0x404040408080808], 7, 0x4044400000008), (0x50505050a0a0a0a0, [0xa0a0a0a0, 0x50500000a0a0, 0x50005000a000a0, 0x1010101020202020], 7, 0x10105000000020), (0x55005500aa00aa00, [0xaa00aa00, 0x55000000aa00, 0x50005000a000a00, 0x1100110022002200], 7, 0x100150000000200)]
theorem r43_sub : ∀ b ∈ r43_bounds, r43_mask &&& b.1 = b.1 := by
  have hall : r43_bounds.all (fun b => Nat.beq (Nat.land r43_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r43_goals : ∀ b ∈ r43_bounds, canon b.1 r43_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r43_bounds.all (fun b => Nat.beq (canonF b.1 r43_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r43_forest : Nat → Nat × Nat := unpackForestF 0x1f 1 5
def r43_links : Nat → Nat → Option Nat := unpackLinksF 0x9 0x1f 2 1 5 1 2
def r43_trace := dagTraceF r43_mask r43_stock 9 r43_forest
def r43_check : Nat → Bool := dagCheckNodeF r43_mask r43_goal r43_bounds 1 r43_trace r43_links
set_option maxHeartbeats 0 in
theorem r43_roots : dagCheckRootsF r43_mask r43_goal r43_bounds
    (dagRefF 1 r43_trace r43_links 0) r43_stock 9 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r43_b0 : treeBlockF 0 1 r43_check = true := by decide +kernel
theorem r43_nodes : ∀ i, 0 ≤ i → i < 1 → r43_check i = true :=
  blockSpec r43_b0
theorem r43_known : KnownBin r43_bounds :=
  knownCons r14_lower (
  knownCons r33_lower (
  knownCons r37_lower (
  knownCons r38_lower (
  knownCons r39_lower (
  knownCons r40_lower (
  knownCons r41_lower (
  knownCons r42_lower (
  knownNil))))))))
theorem r43_lower : LowerBin r43_mask r43_stock r43_goal 10 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r43_known r43_sub r43_goals r43_roots r43_nodes

def r44_mask : Nat := 0x5500550055005500
def r44_stock : List Nat := [0x55005500, 0x550000005500, 0x500050005000500, 0x1100110011001100]
def r44_goal : Nat := 0x100150001005500
def r44_rows : Fin 64 → Fin 64 := decodeRows 0x218000a3800029a000aba00031c000b3c00039e000bbe000
set_option maxHeartbeats 0 in
theorem r44_lower : LowerBin r44_mask r44_stock r44_goal 5 := by
  apply lowerBin_of_rowPull r44_rows (stock' := r6_stock)
  · have hall : r44_stock.all (fun w => availBF r6_stock
        (rowCanon r44_rows r44_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r44_rows r44_mask = r6_mask := by decide +kernel
    have hg : rowCanon r44_rows r44_mask r44_goal = r6_goal := by decide +kernel
    rw [hm, hg]
    exact r6_lower

def r45_mask : Nat := 0xf0f0f0f00f0f0f0f
def r45_stock : List Nat := [0xf0f0f0f, 0xf0f000000f0f, 0xf000f0000f000f, 0x3030303003030303, 0x5050505005050505]
def r45_goal : Nat := 0x1010500107070f
def r45_rows : Fin 64 → Fin 64 := decodeRows 0xffe104f7c104df6104d74104bee104b6c1049e61049641041046da1046581044d21044501042ca1042481040c2104040
set_option maxHeartbeats 0 in
theorem r45_lower : LowerBin r45_mask r45_stock r45_goal 10 := by
  apply lowerBin_of_rowPull r45_rows (stock' := r28_stock)
  · have hall : r45_stock.all (fun w => availBF r28_stock
        (rowCanon r45_rows r45_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r45_rows r45_mask = r28_mask := by decide +kernel
    have hg : rowCanon r45_rows r45_mask r45_goal = r28_goal := by decide +kernel
    rw [hm, hg]
    exact r28_lower

def r46_mask : Nat := 0x5050505050505050
def r46_stock : List Nat := [0x50505050, 0x505000005050, 0x50005000500050, 0x1010101010101010]
def r46_goal : Nat := 0x10105000505050
def r46_rows : Fin 64 → Fin 64 := decodeRows 0x10c18e92c9ae00000000000051c59ed3cdbe000000000000
set_option maxHeartbeats 0 in
theorem r46_lower : LowerBin r46_mask r46_stock r46_goal 5 := by
  apply lowerBin_of_rowPull r46_rows (stock' := r2_stock)
  · have hall : r46_stock.all (fun w => availBF r2_stock
        (rowCanon r46_rows r46_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r46_rows r46_mask = r2_mask := by decide +kernel
    have hg : rowCanon r46_rows r46_mask r46_goal = r2_goal := by decide +kernel
    rw [hm, hg]
    exact r2_lower

def r47_mask : Nat := 0xa0a0a0a0a0a0a0a
def r47_stock : List Nat := [0xa0a0a0a, 0xa0a00000a0a, 0xa000a000a000a, 0x202020202020202]
def r47_goal : Nat := 0x202020002020a
def r47_rows : Fin 64 → Fin 64 := decodeRows 0xef90006d9000cf10004d1000ae90002c90008e10000c1000
set_option maxHeartbeats 0 in
theorem r47_lower : LowerBin r47_mask r47_stock r47_goal 5 := by
  apply lowerBin_of_rowPull r47_rows (stock' := r6_stock)
  · have hall : r47_stock.all (fun w => availBF r6_stock
        (rowCanon r47_rows r47_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r47_rows r47_mask = r6_mask := by decide +kernel
    have hg : rowCanon r47_rows r47_mask r47_goal = r6_goal := by decide +kernel
    rw [hm, hg]
    exact r6_lower

def r48_mask : Nat := 0xff00ff0000000000
def r48_stock : List Nat := [0xff0000000000, 0xf000f0000000000, 0x3300330000000000, 0x5500550000000000]
def r48_goal : Nat := 0x100170000000000
def r48_rows : Fin 64 → Fin 64 := decodeRows 0xa29aab000000b2dbaf000000e39ebb000000f3dfbf
set_option maxHeartbeats 0 in
theorem r48_lower : LowerBin r48_mask r48_stock r48_goal 7 := by
  apply lowerBin_of_rowPull r48_rows (stock' := r13_stock)
  · have hall : r48_stock.all (fun w => availBF r13_stock
        (rowCanon r48_rows r48_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r48_rows r48_mask = r13_mask := by decide +kernel
    have hg : rowCanon r48_rows r48_mask r48_goal = r13_goal := by decide +kernel
    rw [hm, hg]
    exact r13_lower

def r49_mask : Nat := 0xffff000000000000
def r49_stock : List Nat := [0xff000000000000, 0xf0f000000000000, 0x3333000000000000, 0x5555000000000000]
def r49_goal : Nat := 0x117000000000000
def r49_rows : Fin 64 → Fin 64 := decodeRows 0xc31cb3000000d35db7000000e39ebb000000f3dfbf
set_option maxHeartbeats 0 in
theorem r49_lower : LowerBin r49_mask r49_stock r49_goal 7 := by
  apply lowerBin_of_rowPull r49_rows (stock' := r13_stock)
  · have hall : r49_stock.all (fun w => availBF r13_stock
        (rowCanon r49_rows r49_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r49_rows r49_mask = r13_mask := by decide +kernel
    have hg : rowCanon r49_rows r49_mask r49_goal = r13_goal := by decide +kernel
    rw [hm, hg]
    exact r13_lower

def r50_mask : Nat := 0x4444444444444444
def r50_stock : List Nat := [0x44444444, 0x444400004444, 0x44004400440044, 0x404040404040404]
def r50_goal : Nat := 0x4044400444444
def r50_rows : Fin 64 → Fin 64 := decodeRows 0x8a18e8aa9ae00000000000049a59ecbadbe000000000000
set_option maxHeartbeats 0 in
theorem r50_lower : LowerBin r50_mask r50_stock r50_goal 5 := by
  apply lowerBin_of_rowPull r50_rows (stock' := r2_stock)
  · have hall : r50_stock.all (fun w => availBF r2_stock
        (rowCanon r50_rows r50_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r50_rows r50_mask = r2_mask := by decide +kernel
    have hg : rowCanon r50_rows r50_mask r50_goal = r2_goal := by decide +kernel
    rw [hm, hg]
    exact r2_lower

def r51_mask : Nat := 0xcc00cc00cc00cc
def r51_stock : List Nat := [0xcc00cc, 0xcc000000cc, 0xc000c000c000c, 0x44004400440044]
def r51_goal : Nat := 0x400440044004c
def r51_rows : Fin 64 → Fin 64 := decodeRows 0xdf6000cf20009e60008e20000000000000000000000000005d60004d20001c60000c2000
set_option maxHeartbeats 0 in
theorem r51_lower : LowerBin r51_mask r51_stock r51_goal 6 := by
  apply lowerBin_of_rowPull r51_rows (stock' := r0_stock)
  · have hall : r51_stock.all (fun w => availBF r0_stock
        (rowCanon r51_rows r51_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r51_rows r51_mask = r0_mask := by decide +kernel
    have hg : rowCanon r51_rows r51_mask r51_goal = r0_goal := by decide +kernel
    rw [hm, hg]
    exact r0_lower

def r52_mask : Nat := 0x5555000055550000
def r52_stock : List Nat := [0x55550000, 0x55000000550000, 0x505000005050000, 0x1111000011110000]
def r52_goal : Nat := 0x115000001550000
def r52_rows : Fin 64 → Fin 64 := decodeRows 0x418000c3800049a000cba00051c000d3c00059e000dbe000
set_option maxHeartbeats 0 in
theorem r52_lower : LowerBin r52_mask r52_stock r52_goal 5 := by
  apply lowerBin_of_rowPull r52_rows (stock' := r6_stock)
  · have hall : r52_stock.all (fun w => availBF r6_stock
        (rowCanon r52_rows r52_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r52_rows r52_mask = r6_mask := by decide +kernel
    have hg : rowCanon r52_rows r52_mask r52_goal = r6_goal := by decide +kernel
    rw [hm, hg]
    exact r6_lower

def r53_mask : Nat := 0x2222222222222222
def r53_stock : List Nat := [0x22222222, 0x222200002222, 0x22002200220022, 0x202020202020202]
def r53_goal : Nat := 0x2020200020222
def r53_rows : Fin 64 → Fin 64 := decodeRows 0xf79000759000d71000551000b69000349000961000141000
set_option maxHeartbeats 0 in
theorem r53_lower : LowerBin r53_mask r53_stock r53_goal 5 := by
  apply lowerBin_of_rowPull r53_rows (stock' := r6_stock)
  · have hall : r53_stock.all (fun w => availBF r6_stock
        (rowCanon r53_rows r53_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r53_rows r53_mask = r6_mask := by decide +kernel
    have hg : rowCanon r53_rows r53_mask r53_goal = r6_goal := by decide +kernel
    rw [hm, hg]
    exact r6_lower

def r54_mask : Nat := 0xaa00aa00aa00aa
def r54_stock : List Nat := [0xaa00aa, 0xaa000000aa, 0xa000a000a000a, 0x22002200220022]
def r54_goal : Nat := 0x200020002002a
def r54_rows : Fin 64 → Fin 64 := decodeRows 0xdf59e55d51c5000000000000cf18e14d10c1000000000000
set_option maxHeartbeats 0 in
theorem r54_lower : LowerBin r54_mask r54_stock r54_goal 5 := by
  apply lowerBin_of_rowPull r54_rows (stock' := r2_stock)
  · have hall : r54_stock.all (fun w => availBF r2_stock
        (rowCanon r54_rows r54_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r54_rows r54_mask = r2_mask := by decide +kernel
    have hg : rowCanon r54_rows r54_mask r54_goal = r2_goal := by decide +kernel
    rw [hm, hg]
    exact r2_lower

def r55_mask : Nat := 0xc0c0c0c0c0c0c0c
def r55_stock : List Nat := [0xc0c0c0c, 0xc0c00000c0c, 0xc000c000c000c, 0x404040404040404]
def r55_goal : Nat := 0x404040004040c
def r55_rows : Fin 64 → Fin 64 := decodeRows 0xefa0006da000cf20004d2000aea0002ca0008e20000c2000
set_option maxHeartbeats 0 in
theorem r55_lower : LowerBin r55_mask r55_stock r55_goal 5 := by
  apply lowerBin_of_rowPull r55_rows (stock' := r6_stock)
  · have hall : r55_stock.all (fun w => availBF r6_stock
        (rowCanon r55_rows r55_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r55_rows r55_mask = r6_mask := by decide +kernel
    have hg : rowCanon r55_rows r55_mask r55_goal = r6_goal := by decide +kernel
    rw [hm, hg]
    exact r6_lower

def r56_mask : Nat := 0xff00ff0000ff00ff
def r56_stock : List Nat := [0xff00ff, 0xff00000000ff, 0xf000f00000f000f, 0x3300330000330033, 0x5500550000550055]
def r56_goal : Nat := 0x10017000057007f
def r56_rows : Fin 64 → Fin 64 := decodeRows 0x1208083208105208187208411208493208515208597208208a29208aab208b2d208baf208e39208ebb208f3d208fbf
set_option maxHeartbeats 0 in
theorem r56_lower : LowerBin r56_mask r56_stock r56_goal 10 := by
  apply lowerBin_of_rowPull r56_rows (stock' := r28_stock)
  · have hall : r56_stock.all (fun w => availBF r28_stock
        (rowCanon r56_rows r56_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r56_rows r56_mask = r28_mask := by decide +kernel
    have hg : rowCanon r56_rows r56_mask r56_goal = r28_goal := by decide +kernel
    rw [hm, hg]
    exact r28_lower

def r57_mask : Nat := 0xc0c0c0c0c0c0c0c0
def r57_stock : List Nat := [0xc0c0c0c0, 0xc0c00000c0c0, 0xc000c000c000c0, 0x4040404040404040]
def r57_goal : Nat := 0x4000404040
def r57_rows : Fin 64 → Fin 64 := decodeRows 0x18738f59779f9a7bafdb7fbf
set_option maxHeartbeats 0 in
theorem r57_lower : LowerBin r57_mask r57_stock r57_goal 5 := by
  apply lowerBin_of_rowPull r57_rows (stock' := r4_stock)
  · have hall : r57_stock.all (fun w => availBF r4_stock
        (rowCanon r57_rows r57_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r57_rows r57_mask = r4_mask := by decide +kernel
    have hg : rowCanon r57_rows r57_mask r57_goal = r4_goal := by decide +kernel
    rw [hm, hg]
    exact r4_lower

def r58_mask : Nat := 0x3333000033330000
def r58_stock : List Nat := [0x33330000, 0x33000000330000, 0x303000003030000, 0x1111000011110000]
def r58_goal : Nat := 0x113000001130000
def r58_bounds : List (Nat × List Nat × Nat × Nat) := []
theorem r58_sub : ∀ b ∈ r58_bounds, r58_mask &&& b.1 = b.1 := by
  have hall : r58_bounds.all (fun b => Nat.beq (Nat.land r58_mask b.1) b.1) = true := by decide +kernel
  intro b hb
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp hall b hb)
theorem r58_goals : ∀ b ∈ r58_bounds, canon b.1 r58_goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  have hall : r58_bounds.all (fun b => Nat.beq (canonF b.1 r58_goal) b.2.2.2 && !Nat.beq b.2.2.2 0) = true := by decide +kernel
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, canonF_eq] at h
  exact ⟨h.1, ne_of_beq_false h.2⟩
def r58_forest : Nat → Nat × Nat := unpackForestF 0x1ee 1 4
def r58_links : Nat → Nat → Option Nat := unpackLinksF 0x882 0x3ee 4 2 4 1 3
def r58_trace := dagTraceF r58_mask r58_stock 3 r58_forest
def r58_check : Nat → Bool := dagCheckNodeF r58_mask r58_goal r58_bounds 2 r58_trace r58_links
set_option maxHeartbeats 0 in
theorem r58_roots : dagCheckRootsF r58_mask r58_goal r58_bounds
    (dagRefF 2 r58_trace r58_links 0) r58_stock 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem r58_b0 : treeBlockF 0 2 r58_check = true := by decide +kernel
theorem r58_nodes : ∀ i, 0 ≤ i → i < 2 → r58_check i = true :=
  blockSpec r58_b0
theorem r58_known : KnownBin r58_bounds :=
  knownNil
theorem r58_lower : LowerBin r58_mask r58_stock r58_goal 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    r58_known r58_sub r58_goals r58_roots r58_nodes

def r59_mask : Nat := 0x3300330033003300
def r59_stock : List Nat := [0x33003300, 0x330000003300, 0x300030003000300, 0x1100110011001100]
def r59_goal : Nat := 0x100130001001300
def r59_rows : Fin 64 → Fin 64 := decodeRows 0xf7c000e78000b6c000a6800000000000000000000000000075c00065800034c000248000000000000000000000000
set_option maxHeartbeats 0 in
theorem r59_lower : LowerBin r59_mask r59_stock r59_goal 4 := by
  apply lowerBin_of_rowPull r59_rows (stock' := r58_stock)
  · have hall : r59_stock.all (fun w => availBF r58_stock
        (rowCanon r59_rows r59_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r59_rows r59_mask = r58_mask := by decide +kernel
    have hg : rowCanon r59_rows r59_mask r59_goal = r58_goal := by decide +kernel
    rw [hm, hg]
    exact r58_lower

def r60_mask : Nat := 0xf000f000f000f0
def r60_stock : List Nat := [0xf000f0, 0xf0000000f0, 0x30003000300030, 0x50005000500050]
def r60_goal : Nat := 0x10005000500070
def r60_rows : Fin 64 → Fin 64 := decodeRows 0xdf6000d740009e60009640000000000000000000000000005d60005540001c6000144000
set_option maxHeartbeats 0 in
theorem r60_lower : LowerBin r60_mask r60_stock r60_goal 6 := by
  apply lowerBin_of_rowPull r60_rows (stock' := r0_stock)
  · have hall : r60_stock.all (fun w => availBF r0_stock
        (rowCanon r60_rows r60_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r60_rows r60_mask = r0_mask := by decide +kernel
    have hg : rowCanon r60_rows r60_mask r60_goal = r0_goal := by decide +kernel
    rw [hm, hg]
    exact r0_lower

def r61_mask : Nat := 0xff000000ff0000
def r61_stock : List Nat := [0xff0000, 0xf0000000f0000, 0x33000000330000, 0x55000000550000]
def r61_goal : Nat := 0x17000000570000
def r61_rows : Fin 64 → Fin 64 := decodeRows 0x411000c31000493000cb3000515000d35000597000db7000
set_option maxHeartbeats 0 in
theorem r61_lower : LowerBin r61_mask r61_stock r61_goal 5 := by
  apply lowerBin_of_rowPull r61_rows (stock' := r6_stock)
  · have hall : r61_stock.all (fun w => availBF r6_stock
        (rowCanon r61_rows r61_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r61_rows r61_mask = r6_mask := by decide +kernel
    have hg : rowCanon r61_rows r61_mask r61_goal = r6_goal := by decide +kernel
    rw [hm, hg]
    exact r6_lower

def r62_mask : Nat := 0xf0f0f0f000000000
def r62_stock : List Nat := [0xf0f000000000, 0xf000f000000000, 0x3030303000000000, 0x5050505000000000]
def r62_goal : Nat := 0x10105000000000
def r62_rows : Fin 64 → Fin 64 := decodeRows 0x9259a7b2dbafd35db7f3dfbf
set_option maxHeartbeats 0 in
theorem r62_lower : LowerBin r62_mask r62_stock r62_goal 5 := by
  apply lowerBin_of_rowPull r62_rows (stock' := r4_stock)
  · have hall : r62_stock.all (fun w => availBF r4_stock
        (rowCanon r62_rows r62_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r62_rows r62_mask = r4_mask := by decide +kernel
    have hg : rowCanon r62_rows r62_mask r62_goal = r4_goal := by decide +kernel
    rw [hm, hg]
    exact r4_lower

def r63_mask : Nat := 0x3030303030303030
def r63_stock : List Nat := [0x30303030, 0x303000003030, 0x30003000300030, 0x1010101010101010]
def r63_goal : Nat := 0x10101000101030
def r63_rows : Fin 64 → Fin 64 := decodeRows 0xf7c00075c000d74000554000b6c00034c000964000144000
set_option maxHeartbeats 0 in
theorem r63_lower : LowerBin r63_mask r63_stock r63_goal 5 := by
  apply lowerBin_of_rowPull r63_rows (stock' := r6_stock)
  · have hall : r63_stock.all (fun w => availBF r6_stock
        (rowCanon r63_rows r63_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r63_rows r63_mask = r6_mask := by decide +kernel
    have hg : rowCanon r63_rows r63_mask r63_goal = r6_goal := by decide +kernel
    rw [hm, hg]
    exact r6_lower

def r64_mask : Nat := 0x3333333300000000
def r64_stock : List Nat := [0x333300000000, 0x33003300000000, 0x303030300000000, 0x1111111100000000]
def r64_goal : Nat := 0x113131300000000
def r64_rows : Fin 64 → Fin 64 := decodeRows 0x821a29c31e39000000000000925b2dd35f3d000000000000
set_option maxHeartbeats 0 in
theorem r64_lower : LowerBin r64_mask r64_stock r64_goal 5 := by
  apply lowerBin_of_rowPull r64_rows (stock' := r2_stock)
  · have hall : r64_stock.all (fun w => availBF r2_stock
        (rowCanon r64_rows r64_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r64_rows r64_mask = r2_mask := by decide +kernel
    have hg : rowCanon r64_rows r64_mask r64_goal = r2_goal := by decide +kernel
    rw [hm, hg]
    exact r2_lower

def r65_mask : Nat := 0xf000f000f000f00
def r65_stock : List Nat := [0xf000f00, 0xf0000000f00, 0x300030003000300, 0x500050005000500]
def r65_goal : Nat := 0x100070001000700
def r65_rows : Fin 64 → Fin 64 := decodeRows 0xefa000e78000aea000a680000000000000000000000000006da0006580002ca000248000000000000000000000000
set_option maxHeartbeats 0 in
theorem r65_lower : LowerBin r65_mask r65_stock r65_goal 4 := by
  apply lowerBin_of_rowPull r65_rows (stock' := r58_stock)
  · have hall : r65_stock.all (fun w => availBF r58_stock
        (rowCanon r65_rows r65_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r65_rows r65_mask = r58_mask := by decide +kernel
    have hg : rowCanon r65_rows r65_mask r65_goal = r58_goal := by decide +kernel
    rw [hm, hg]
    exact r58_lower

def r66_mask : Nat := 0xf0f0f0f00000000
def r66_stock : List Nat := [0xf0f00000000, 0xf000f00000000, 0x303030300000000, 0x505050500000000]
def r66_goal : Nat := 0x107070700000000
def r66_rows : Fin 64 → Fin 64 := decodeRows 0x821a29c31e390000000000008a3aabcb3ebb000000000000
set_option maxHeartbeats 0 in
theorem r66_lower : LowerBin r66_mask r66_stock r66_goal 5 := by
  apply lowerBin_of_rowPull r66_rows (stock' := r2_stock)
  · have hall : r66_stock.all (fun w => availBF r2_stock
        (rowCanon r66_rows r66_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r66_rows r66_mask = r2_mask := by decide +kernel
    have hg : rowCanon r66_rows r66_mask r66_goal = r2_goal := by decide +kernel
    rw [hm, hg]
    exact r2_lower

def r67_mask : Nat := 0xf0f0f0f0
def r67_stock : List Nat := [0xf0f0, 0xf000f0, 0x30303030, 0x50505050]
def r67_goal : Nat := 0x505070
def r67_rows : Fin 64 → Fin 64 := decodeRows 0x7de00075c0005d60005540003ce00034c0001c6000144000
set_option maxHeartbeats 0 in
theorem r67_lower : LowerBin r67_mask r67_stock r67_goal 5 := by
  apply lowerBin_of_rowPull r67_rows (stock' := r6_stock)
  · have hall : r67_stock.all (fun w => availBF r6_stock
        (rowCanon r67_rows r67_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r67_rows r67_mask = r6_mask := by decide +kernel
    have hg : rowCanon r67_rows r67_mask r67_goal = r6_goal := by decide +kernel
    rw [hm, hg]
    exact r6_lower

def r68_mask : Nat := 0xffff0000
def r68_stock : List Nat := [0xff0000, 0xf0f0000, 0x33330000, 0x55550000]
def r68_goal : Nat := 0x1570000
def r68_rows : Fin 64 → Fin 64 := decodeRows 0x7de75c6da6580000000000005d65544d2450000000000000
set_option maxHeartbeats 0 in
theorem r68_lower : LowerBin r68_mask r68_stock r68_goal 5 := by
  apply lowerBin_of_rowPull r68_rows (stock' := r2_stock)
  · have hall : r68_stock.all (fun w => availBF r2_stock
        (rowCanon r68_rows r68_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r68_rows r68_mask = r2_mask := by decide +kernel
    have hg : rowCanon r68_rows r68_mask r68_goal = r2_goal := by decide +kernel
    rw [hm, hg]
    exact r2_lower

def r69_mask : Nat := 0xf0f00000f0f0000
def r69_stock : List Nat := [0xf0f0000, 0xf0000000f0000, 0x303000003030000, 0x505000005050000]
def r69_goal : Nat := 0x107000001070000
def r69_rows : Fin 64 → Fin 64 := decodeRows 0xefa000e78000cf2000c700000000000000000000000000006da0006580004d2000450000000000000000000000000
set_option maxHeartbeats 0 in
theorem r69_lower : LowerBin r69_mask r69_stock r69_goal 4 := by
  apply lowerBin_of_rowPull r69_rows (stock' := r58_stock)
  · have hall : r69_stock.all (fun w => availBF r58_stock
        (rowCanon r69_rows r69_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r69_rows r69_mask = r58_mask := by decide +kernel
    have hg : rowCanon r69_rows r69_mask r69_goal = r58_goal := by decide +kernel
    rw [hm, hg]
    exact r58_lower

def r70_mask : Nat := 0xff00ff00000000
def r70_stock : List Nat := [0xff00000000, 0xf000f00000000, 0x33003300000000, 0x55005500000000]
def r70_goal : Nat := 0x17005700000000
def r70_rows : Fin 64 → Fin 64 := decodeRows 0x821000c310008a3000cb3000925000d350009a7000db7000
set_option maxHeartbeats 0 in
theorem r70_lower : LowerBin r70_mask r70_stock r70_goal 5 := by
  apply lowerBin_of_rowPull r70_rows (stock' := r6_stock)
  · have hall : r70_stock.all (fun w => availBF r6_stock
        (rowCanon r70_rows r70_mask w)) = true := by decide +kernel
    intro w hw
    apply availB_spec.mp
    rw [← availBF_eq]
    exact List.all_eq_true.mp hall w hw
  · have hm : rowPull r70_rows r70_mask = r6_mask := by decide +kernel
    have hg : rowCanon r70_rows r70_mask r70_goal = r6_goal := by decide +kernel
    rw [hm, hg]
    exact r6_lower

theorem cert_known : KnownBin cert_bounds :=
  knownCons r10_lower (
  knownCons r11_lower (
  knownCons r12_lower (
  knownCons r9_lower (
  knownCons r15_lower (
  knownCons r16_lower (
  knownCons r17_lower (
  knownCons r29_lower (
  knownCons r30_lower (
  knownCons r31_lower (
  knownCons r32_lower (
  knownCons r36_lower (
  knownCons r35_lower (
  knownCons r43_lower (
  knownCons r14_lower (
  knownCons r44_lower (
  knownCons r5_lower (
  knownCons r45_lower (
  knownCons r33_lower (
  knownCons r46_lower (
  knownCons r1_lower (
  knownCons r18_lower (
  knownCons r47_lower (
  knownCons r48_lower (
  knownCons r13_lower (
  knownCons r49_lower (
  knownCons r50_lower (
  knownCons r51_lower (
  knownCons r52_lower (
  knownCons r53_lower (
  knownCons r54_lower (
  knownCons r55_lower (
  knownCons r3_lower (
  knownCons r56_lower (
  knownCons r28_lower (
  knownCons r57_lower (
  knownCons r0_lower (
  knownCons r59_lower (
  knownCons r60_lower (
  knownCons r61_lower (
  knownCons r62_lower (
  knownCons r4_lower (
  knownCons r8_lower (
  knownCons r63_lower (
  knownCons r64_lower (
  knownCons r65_lower (
  knownCons r23_lower (
  knownCons r66_lower (
  knownCons r7_lower (
  knownCons r34_lower (
  knownCons r6_lower (
  knownCons r67_lower (
  knownCons r68_lower (
  knownCons r58_lower (
  knownCons r69_lower (
  knownCons r70_lower (
  knownCons r2_lower (
  knownNil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem binaryLower : LowerBin cert_mask cert_stock cert_goal 13 :=
  cert_lower cert_known


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev X := Fin 6 → Bool
abbrev F := X → Bool

def target : F := fun x => Nat.testBit 18368186892755183744
  (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def witness : Circuit :=
  ⟨[
    ⟨.and, [3, 4]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [5, 7]⟩,
    ⟨.and, [5, 7]⟩,
    ⟨.or, [0, 9]⟩,
    ⟨.and, [0, 6]⟩,
    ⟨.and, [2, 10]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.or, [6, 13]⟩,
    ⟨.or, [12, 14]⟩,
    ⟨.or, [2, 11]⟩,
    ⟨.and, [14, 16]⟩,
    ⟨.or, [1, 17]⟩,
    ⟨.and, [15, 18]⟩], 19⟩

theorem witness_mono : Monotone2 witness := by simp [Monotone2, witness]

theorem witness_size : witness.size = 14 := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem witness_eval : ∀ x : X, witness.eval (List.ofFn x) = target x := by
  decide +kernel

theorem binaryLowerRoot : LowerBin fullMask rootStock (canon fullMask 18368186892755183744) 13 := by
  intro vs hbuild hhit
  have hstock : ∀ w ∈ rootStock, w ∈ cert_stock := by
    have hall : rootStock.all (fun i => cert_stock.contains i) = true := by decide +kernel
    intro w hw
    exact List.contains_iff_mem.mp (List.all_eq_true.mp hall w hw)
  have hbuild' := builds_weaken hstock hbuild
  have hhit' : Avail (vs ++ cert_stock) (canon fullMask 18368186892755183744) :=
    avail_weaken (fun w hw => by
      rcases List.mem_append.mp hw with hv | hs
      · exact List.mem_append_left _ hv
      · exact List.mem_append_right _ (hstock w hs)) hhit
  exact binaryLower vs hbuild' hhit'

end PEqualNP.Outside.L_meta_48488

theorem PEqualNP.Outside.L_meta_48488 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6
      (fun x : Fin 6 → Bool => Nat.testBit (4276676776 * 2 ^ 32 + 4272466048)
        (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s →
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 4272466048)
        (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_48488.table2_from_lowerBin 18368186892755183744 14
    PEqualNP.Outside.L_meta_48488.binaryLowerRoot PEqualNP.Outside.L_meta_48488.witness.gates PEqualNP.Outside.L_meta_48488.witness.output
    PEqualNP.Outside.L_meta_48488.witness_size PEqualNP.Outside.L_meta_48488.witness_mono PEqualNP.Outside.L_meta_48488.witness_eval
