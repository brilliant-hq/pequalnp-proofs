import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38977_aux

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def mask256 : Nat := 2 ^ 256 - 1

def negD (d w : Nat) : Nat := (w ^^^ mask256) &&& d
def andD (d a b : Nat) : Nat := (a &&& b) &&& d
def orD (d a b : Nat) : Nat := (a ||| b) &&& d
def binD (d : Nat) (isOr : Bool) (a b : Nat) : Nat := if isOr then orD d a b else andD d a b

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def RunD (d y : Nat) (t : ℕ) (ws : List Nat) : Prop :=
  ∀ P : ℕ → List Nat → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (save : Bool),
      negD d a ≠ 0 → negD d a ≠ d → negD d a ∉ (a :: r) →
      P s (negD d a :: kept save a r) → P (s + 1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      (if c then andD d a b else orD d a b) ≠ 0 →
      (if c then andD d a b else orD d a b) ≠ d →
      (if c then andD d a b else orD d a b) ∉ (a :: b :: r) →
      P s ((if c then andD d a b else orD d a b) :: kept ka a (kept kb b r)) →
      P (s + 1) (a :: b :: r)) → P t ws

section
variable {d y : Nat}

theorem Run.done : RunD d y 0 [y] := fun _ dn _ _ _ => dn
theorem Run.perm {s xs zs} (p : List.Perm xs zs) (h : RunD d y s xs) :
    RunD d y s zs := fun P dn q u b => q p (h P dn q u b)
theorem Run.one {s a r} (save : Bool)
    (h0 : negD d a ≠ 0) (hd : negD d a ≠ d) (hm : negD d a ∉ (a :: r))
    (h : RunD d y s (negD d a :: kept save a r)) :
    RunD d y (s + 1) (a :: r) := fun P dn q u b => u save h0 hd hm (h P dn q u b)
theorem Run.two {s a b r} (c ka kb : Bool)
    (h0 : (if c then andD d a b else orD d a b) ≠ 0)
    (hd : (if c then andD d a b else orD d a b) ≠ d)
    (hm : (if c then andD d a b else orD d a b) ∉ (a :: b :: r))
    (h : RunD d y s ((if c then andD d a b else orD d a b) :: kept ka a (kept kb b r))) :
    RunD d y (s + 1) (a :: b :: r) := fun P dn q u v => v c ka kb h0 hd hm (h P dn q u v)

theorem Run.fold {P : ∀ t ws, RunD d y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : RunD d y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (one : ∀ {s a r} (save : Bool)
      (h0 : negD d a ≠ 0) (hd : negD d a ≠ d) (hm : negD d a ∉ (a :: r))
      (h : RunD d y s (negD d a :: kept save a r)),
      P _ _ h → P _ _ (Run.one save h0 hd hm h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h0 : (if c then andD d a b else orD d a b) ≠ 0)
      (hd : (if c then andD d a b else orD d a b) ≠ d)
      (hm : (if c then andD d a b else orD d a b) ∉ (a :: b :: r))
      (h : RunD d y s ((if c then andD d a b else orD d a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two c ka kb h0 hd hm h))
    {t ws} (h : RunD d y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : RunD d y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun k h0 hd hm ⟨h', ih⟩ => ⟨Run.one k h0 hd hm h', one k h0 hd hm h' ih⟩)
    (fun c a b h0 hd hm ⟨h', ih⟩ => ⟨Run.two c a b h0 hd hm h', two c a b h0 hd hm h' ih⟩)
  exact hex.elim fun _ hp => hp
end

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

theorem run_len {d y s xs} (h : RunD d y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one save _ _ _ _ ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb _ _ _ _ ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

theorem zero_done {d y t ws} (h : RunD d y t ws) :
    t = 0 → ws = [y] := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

def IsConst (d w : Nat) : Prop := (w &&& d) = 0 ∨ (w &&& d) = d
def isConstB (d w : Nat) : Bool := (w &&& d == 0) || (w &&& d == d)

theorem isConstB_iff (d w : Nat) : isConstB d w = true ↔ IsConst d w := by
  simp [isConstB, IsConst]

def Avail (d : Nat) (bank : List Nat) (w : Nat) : Prop :=
  IsConst d w ∨ ∃ v ∈ bank, (v &&& d) = (w &&& d)

def availB (d : Nat) (bank : List Nat) (w : Nat) : Bool :=
  let m := w &&& d
  m == 0 || m == d || bank.any (fun v => (v &&& d) == m)

theorem availB_iff (d : Nat) (bank : List Nat) (w : Nat) :
    availB d bank w = true ↔ Avail d bank w := by
  simp [availB, Avail, IsConst, or_assoc]

def NatReach (d : Nat) (roots : List Nat) : Nat → List Nat → Prop
  | 0, bank => bank = roots
  | p + 1, bank =>
    (∃ b a, bank = negD d a :: b ∧ NatReach d roots p b ∧ Avail d b a) ∨
    (∃ b a c op, bank = binD d op a c :: b ∧ NatReach d roots p b ∧ Avail d b a ∧ Avail d b c)

def Lower (d : Nat) (roots : List Nat) (T : Nat) (L : Nat) : Prop :=
  ∀ p bank, NatReach d roots p bank → Avail d bank T → L ≤ p

theorem mask256_bit (i : Nat) : mask256.testBit i = decide (i < 256) := by
  rw [mask256, Nat.testBit_two_pow_sub_one]

theorem negD_and_sub {d d1 : Nat} (hd : d &&& mask256 = d) (hsub : d &&& d1 = d) (a : Nat) :
    negD d1 a &&& d = negD d a := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := congrArg (fun v => v.testBit i) hd
  have h2 := congrArg (fun v => v.testBit i) hsub
  simp only [negD, Nat.testBit_and, Nat.testBit_xor] at *
  cases hi : d.testBit i <;> simp_all

theorem andD_and_sub {d d1 : Nat} (hsub : d &&& d1 = d) (a b : Nat) :
    andD d1 a b &&& d = andD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  have h2 := congrArg (fun v => v.testBit i) hsub
  simp only [andD, Nat.testBit_and] at *
  cases hi : d.testBit i <;> simp_all

theorem orD_and_sub {d d1 : Nat} (hsub : d &&& d1 = d) (a b : Nat) :
    orD d1 a b &&& d = orD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  have h2 := congrArg (fun v => v.testBit i) hsub
  simp only [orD, Nat.testBit_and, Nat.testBit_or] at *
  cases hi : d.testBit i <;> simp_all

theorem negD_const {d : Nat} (hd : d &&& mask256 = d) {a : Nat} (hc : IsConst d a) :
    IsConst d (negD d a) := by
  rcases hc with h0 | h1
  · right; apply Nat.eq_of_testBit_eq; intro i
    have h0i := congrArg (fun v => v.testBit i) h0
    have hdi := congrArg (fun v => v.testBit i) hd
    simp only [negD, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
  · left; apply Nat.eq_of_testBit_eq; intro i
    have h1i := congrArg (fun v => v.testBit i) h1
    have hdi := congrArg (fun v => v.testBit i) hd
    simp only [negD, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all

theorem binD_const_left {d : Nat} {a b : Nat} (op : Bool) (hc : IsConst d a) :
    (binD d op a b &&& d = 0) ∨ (binD d op a b &&& d = d) ∨ (binD d op a b &&& d = b &&& d) := by
  rcases hc with h0 | h1
  · cases op
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h0i := congrArg (fun v => v.testBit i) h0
      simp only [binD, andD, Nat.testBit_and, Nat.zero_testBit, ite_false] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
    · right; right; apply Nat.eq_of_testBit_eq; intro i
      have h0i := congrArg (fun v => v.testBit i) h0
      simp only [binD, orD, Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit, ite_true] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
  · cases op
    · right; right; apply Nat.eq_of_testBit_eq; intro i
      have h1i := congrArg (fun v => v.testBit i) h1
      simp only [binD, andD, Nat.testBit_and, ite_false] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
    · right; left; apply Nat.eq_of_testBit_eq; intro i
      have h1i := congrArg (fun v => v.testBit i) h1
      simp only [binD, orD, Nat.testBit_and, Nat.testBit_or, ite_true] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all

theorem binD_comm (d : Nat) (op : Bool) (a b : Nat) : binD d op a b = binD d op b a := by
  cases op <;> simp [binD, andD, orD, Nat.and_comm, Nat.or_comm]

theorem avail_cons {d : Nat} {bank : List Nat} (z w : Nat) (h : Avail d bank w) :
    Avail d (z :: bank) w := by
  rcases h with hc | ⟨v, hv, he⟩
  · exact Or.inl hc
  · exact Or.inr ⟨v, List.mem_cons_of_mem _ hv, he⟩

theorem avail_of_eq {d : Nat} {bank : List Nat} {v w : Nat}
    (he : v &&& d = w &&& d) (h : Avail d bank v) : Avail d bank w := by
  rcases h with (h0 | h1) | ⟨u, hu, hue⟩
  · exact Or.inl (Or.inl (he.symm.trans h0))
  · exact Or.inl (Or.inr (he.symm.trans h1))
  · exact Or.inr ⟨u, hu, hue.trans he⟩

theorem countP_kept_ge {α : Type} (p : α → Bool) (b : Bool) (a : α) (xs : List α) :
    xs.countP p ≤ (kept b a xs).countP p := by
  cases b <;> simp [kept, List.countP_cons] <;> split <;> omega

theorem contraction {d d1 T : Nat} (hd : d &&& mask256 = d) (hsub : d &&& d1 = d)
    (hnc : ¬ IsConst d T) {s ws} (h : RunD d1 T s ws) {roots p bank}
    (hp : NatReach d roots p bank) (hs : ∀ w ∈ ws, Avail d bank w) :
    ∃ q next, NatReach d roots q next ∧ Avail d next T ∧
      q + ws.countP (isConstB d) ≤ p + s := by
  induction h using Run.fold generalizing p bank with
  | done =>
    have hfalse : isConstB d T = false := by
      cases hc : isConstB d T with
      | false => rfl
      | true => exact absurd ((isConstB_iff d T).1 hc) hnc
    exact ⟨p, bank, hp, hs T (by simp), by simp [hfalse]⟩
  | perm eq _ ih =>
    obtain ⟨q, next, hq, ht, hle⟩ := ih hp (fun w hw => hs w (eq.mem_iff.1 hw))
    rw [eq.countP_eq] at hle
    exact ⟨q, next, hq, ht, hle⟩
  | @one s a r save _ _ _ _ ih =>
    have ha := hs a List.mem_cons_self
    by_cases hca : IsConst d a
    · have hc_neg : IsConst d (negD d1 a) := by
        have e := negD_and_sub hd hsub a
        rcases negD_const hd hca with h0 | h1
        · exact Or.inl (e.trans (by simpa [negD, Nat.and_assoc, Nat.and_self] using h0))
        · exact Or.inr (e.trans (by simpa [negD, Nat.and_assoc, Nat.and_self] using h1))
      have hs' : ∀ w ∈ negD d1 a :: kept save a r, Avail d bank w := by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact Or.inl hc_neg
        · exact hs w (by rw [mem_kept] at hw; rcases hw with ⟨_, rfl⟩ | hw <;> simp [hw])
      obtain ⟨q, next, hq, ht, hle⟩ := ih hp hs'
      have h1 : isConstB d (negD d1 a) = true := (isConstB_iff _ _).2 hc_neg
      have h2 : isConstB d a = true := (isConstB_iff _ _).2 hca
      have hk := countP_kept_ge (isConstB d) save a r
      simp only [List.countP_cons, h1, h2, ite_true] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩
    · have hreach' : NatReach d roots (p + 1) (negD d a :: bank) := Or.inl ⟨bank, a, rfl, hp, ha⟩
      have hneg_av : Avail d (negD d a :: bank) (negD d1 a) :=
        Or.inr ⟨negD d a, List.mem_cons_self, by rw [negD_and_sub hd hsub a]; simp [negD, Nat.and_assoc, Nat.and_self]⟩
      have hs' : ∀ w ∈ negD d1 a :: kept save a r, Avail d (negD d a :: bank) w := by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hneg_av
        · exact avail_cons _ _ (hs w (by rw [mem_kept] at hw; rcases hw with ⟨_, rfl⟩ | hw <;> simp [hw]))
      obtain ⟨q, next, hq, ht, hle⟩ := ih hreach' hs'
      have h2 : isConstB d a = false := by
        cases h : isConstB d a with | false => rfl | true => exact absurd ((isConstB_iff _ _).1 h) hca
      have hk := countP_kept_ge (isConstB d) save a r
      simp only [List.countP_cons, h2, Bool.false_eq_true, ite_false] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩
  | @two s a b r conj ka kb _ _ _ _ ih =>
    have ha := hs a List.mem_cons_self
    have hb := hs b (List.mem_cons_of_mem _ List.mem_cons_self)
    set z1 := if conj then andD d1 a b else orD d1 a b
    set z0 := binD d (!conj) a b
    have hz_eq : z1 &&& d = z0 &&& d := by
      cases conj
      · simp only [z1, z0, Bool.false_eq_true, ite_false, Bool.not_false, binD, ite_true]
        rw [orD_and_sub hsub]; simp [orD, Nat.and_assoc, Nat.and_self]
      · simp only [z1, z0, ite_true, Bool.not_true, Bool.false_eq_true, binD, ite_false]
        rw [andD_and_sub hsub]; simp [andD, Nat.and_assoc, Nat.and_self]
    by_cases hcab : IsConst d a ∨ IsConst d b
    · have hz_av : Avail d bank z1 := by
        apply avail_of_eq hz_eq.symm
        rcases hcab with hca | hcb
        · rcases binD_const_left (!conj) hca with h0 | h1 | he
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm hb
        · dsimp only [z0]; rw [binD_comm]
          rcases binD_const_left (!conj) hcb with h0 | h1 | he
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm ha
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r), Avail d bank w := by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hz_av
        · rw [mem_kept, mem_kept] at hw
          rcases hw with ⟨_, rfl⟩ | ⟨_, rfl⟩ | hw
          · exact ha
          · exact hb
          · exact hs w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))
      obtain ⟨q, next, hq, ht, hle⟩ := ih hp hs'
      have hkr : r.countP (isConstB d) ≤ (kept ka a (kept kb b r)).countP (isConstB d) :=
        le_trans (countP_kept_ge _ kb b r) (countP_kept_ge _ ka a _)
      have hcost : (if isConstB d a = true then 1 else 0) + (if isConstB d b = true then 1 else 0)
          ≤ 1 + (if isConstB d z1 = true then 1 else 0) := by
        rcases hcab with hca | hcb
        · have ha1 : isConstB d a = true := (isConstB_iff _ _).2 hca
          rcases binD_const_left (!conj) hca with h0 | h1 | he
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inl (hz_eq.trans h0))
            simp [ha1, hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inr (hz_eq.trans h1))
            simp [ha1, hz1]; split <;> omega
          · have hzb : isConstB d z1 = isConstB d b := by
              simp only [isConstB, hz_eq.trans he]
            simp [ha1, hzb]
        · have hb1 : isConstB d b = true := (isConstB_iff _ _).2 hcb
          have hz_eq' : z1 &&& d = binD d (!conj) b a &&& d := by rw [hz_eq, binD_comm]
          rcases binD_const_left (!conj) hcb with h0 | h1 | he
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inl (hz_eq'.trans h0))
            simp [hb1, hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inr (hz_eq'.trans h1))
            simp [hb1, hz1]; split <;> omega
          · have hza : isConstB d z1 = isConstB d a := by
              simp only [isConstB, hz_eq'.trans he]
            simp [hb1, hza]
      simp only [List.countP_cons] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩
    · have hna : isConstB d a = false := by
        cases h : isConstB d a with | false => rfl | true => exact absurd (Or.inl ((isConstB_iff _ _).1 h)) hcab
      have hnb : isConstB d b = false := by
        cases h : isConstB d b with | false => rfl | true => exact absurd (Or.inr ((isConstB_iff _ _).1 h)) hcab
      have hreach' : NatReach d roots (p + 1) (z0 :: bank) := Or.inr ⟨bank, a, b, !conj, rfl, hp, ha, hb⟩
      have hz_av : Avail d (z0 :: bank) z1 := Or.inr ⟨z0, List.mem_cons_self, hz_eq.symm⟩
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r), Avail d (z0 :: bank) w := by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hz_av
        · rw [mem_kept, mem_kept] at hw
          rcases hw with ⟨_, rfl⟩ | ⟨_, rfl⟩ | hw
          · exact avail_cons _ _ ha
          · exact avail_cons _ _ hb
          · exact avail_cons _ _ (hs w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)))
      obtain ⟨q, next, hq, ht, hle⟩ := ih hreach' hs'
      have hkr : r.countP (isConstB d) ≤ (kept ka a (kept kb b r)).countP (isConstB d) :=
        le_trans (countP_kept_ge _ kb b r) (countP_kept_ge _ ka a _)
      simp only [List.countP_cons, hna, hnb, Bool.false_eq_true, ite_false] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩

theorem mask_idemp (d w : Nat) : (w &&& d) &&& d = w &&& d := by
  simp [Nat.and_assoc, Nat.and_self]

theorem negD_mask (d a : Nat) : negD d (a &&& d) = negD d a := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [negD, Nat.testBit_and, Nat.testBit_xor]
  cases d.testBit i <;> simp

theorem andD_mask (d a b : Nat) : andD d (a &&& d) (b &&& d) = andD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [andD, Nat.testBit_and]
  cases d.testBit i <;> simp

theorem orD_mask (d a b : Nat) : orD d (a &&& d) (b &&& d) = orD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [orD, Nat.testBit_and, Nat.testBit_or]
  cases d.testBit i <;> simp

theorem pull_one {d Y k ws} (hd : d &&& mask256 = d) (hnd : ws.Nodup)
    (hprop : ∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) (h : RunD d Y k ws)
    {b : List Nat} {a : Nat} (ha : Avail d b a) (hsub : ∀ w ∈ ws, w ∈ negD d a :: b.map (· &&& d)) :
    ∃ k' ws', k' ≤ k + 1 ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
      (∀ w ∈ ws', w ∈ b.map (· &&& d)) ∧ RunD d Y k' ws' := by
  set z := negD d a
  by_cases hzm : z ∈ ws
  · by_cases hzb : z ∈ b.map (· &&& d)
    · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
        rcases List.mem_cons.1 (hsub w hw) with rfl | hm
        · exact hzb
        · exact hm, h⟩
    · have hzp := hprop z hzm
      have ha_nc : ¬ IsConst d a := by
        intro hc
        rcases negD_const hd hc with h0 | h1
        · exact hzp.1 (by simpa [z, negD, Nat.and_assoc, Nat.and_self] using h0)
        · exact hzp.2 (by simpa [z, negD, Nat.and_assoc, Nat.and_self] using h1)
      obtain ⟨v, hv, hve⟩ := ha.resolve_left ha_nc
      set a' := a &&& d
      have ha'_mem : a' ∈ b.map (· &&& d) := List.mem_map.2 ⟨v, hv, hve⟩
      have ha'_prop : a' ≠ 0 ∧ a' ≠ d := ⟨fun e => ha_nc (Or.inl e), fun e => ha_nc (Or.inr e)⟩
      set rest := ws.erase z
      have hrest_nd : rest.Nodup := hnd.erase z
      have hrest_sub : ∀ w ∈ rest, w ∈ b.map (· &&& d) := by
        intro w hw
        have ⟨hne, hm⟩ := hnd.mem_erase_iff.1 hw
        rcases List.mem_cons.1 (hsub w hm) with rfl | hmb
        · exact absurd rfl hne
        · exact hmb
      have hrest_prop : ∀ w ∈ rest, w ≠ 0 ∧ w ≠ d := fun w hw => hprop w (List.mem_of_mem_erase hw)
      have hp1 : ws.Perm (z :: rest) := List.perm_cons_erase hzm
      have ez : negD d a' = z := negD_mask d a
      have h1 : RunD d Y k (negD d a' :: rest) := by
        rw [ez]; exact Run.perm hp1 h
      have hne0 : negD d a' ≠ 0 := ez.symm ▸ hzp.1
      have hned : negD d a' ≠ d := ez.symm ▸ hzp.2
      by_cases ham : a' ∈ rest
      · have hp2 : rest.Perm (a' :: rest.erase a') := List.perm_cons_erase ham
        have h2 : RunD d Y k (negD d a' :: kept true a' (rest.erase a')) :=
          Run.perm (hp2.cons _) h1
        have hnm : negD d a' ∉ (a' :: rest.erase a') := by
          rw [ez, List.mem_cons]; rintro (e | hm)
          · exact hzb (e ▸ ha'_mem)
          · exact hnd.not_mem_erase (List.mem_of_mem_erase hm)
        refine ⟨k + 1, rest, le_rfl, hrest_nd, hrest_prop, hrest_sub, ?_⟩
        exact Run.perm hp2.symm (Run.one true hne0 hned hnm h2)
      · have h2 : RunD d Y k (negD d a' :: kept false a' rest) := h1
        have hnm : negD d a' ∉ (a' :: rest) := by
          rw [ez, List.mem_cons]; rintro (e | hm)
          · exact hzb (e ▸ ha'_mem)
          · exact hnd.not_mem_erase hm
        refine ⟨k + 1, a' :: rest, le_rfl, List.nodup_cons.2 ⟨ham, hrest_nd⟩, ?_, ?_, Run.one false hne0 hned hnm h2⟩
        · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
          · exact ha'_prop
          · exact hrest_prop w hw
        · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
          · exact ha'_mem
          · exact hrest_sub w hw
  · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
      rcases List.mem_cons.1 (hsub w hw) with rfl | hm
      · exact absurd hw hzm
      · exact hm, h⟩

theorem pull_two {d Y k ws} (hnd : ws.Nodup)
    (hprop : ∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) (h : RunD d Y k ws)
    {b : List Nat} {a c : Nat} (op : Bool) (ha : Avail d b a) (hc : Avail d b c)
    (hsub : ∀ w ∈ ws, w ∈ binD d op a c :: b.map (· &&& d)) :
    ∃ k' ws', k' ≤ k + 1 ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
      (∀ w ∈ ws', w ∈ b.map (· &&& d)) ∧ RunD d Y k' ws' := by
  set z := binD d op a c
  have hz_mask : z &&& d = z := by cases op <;> simp [z, binD, andD, orD, Nat.and_assoc, Nat.and_self]
  by_cases hzm : z ∈ ws
  · by_cases hzb : z ∈ b.map (· &&& d)
    · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
        rcases List.mem_cons.1 (hsub w hw) with rfl | hm
        · exact hzb
        · exact hm, h⟩
    · have hzp := hprop z hzm
      have ha_nc : ¬ IsConst d a := by
        intro hca
        rcases binD_const_left op hca with h0 | h1 | he
        · exact hzp.1 (hz_mask.symm.trans h0)
        · exact hzp.2 (hz_mask.symm.trans h1)
        · rcases hc with hcc | ⟨v, hv, hve⟩
          · rcases hcc with h0 | h1
            · exact hzp.1 (hz_mask.symm.trans (he.trans h0))
            · exact hzp.2 (hz_mask.symm.trans (he.trans h1))
          · exact hzb (List.mem_map.2 ⟨v, hv, hve.trans (he.symm.trans hz_mask)⟩)
      have hc_nc : ¬ IsConst d c := by
        intro hcc
        have hz' : z = binD d op c a := binD_comm d op a c
        rcases binD_const_left op hcc with h0 | h1 | he
        · exact hzp.1 (hz_mask.symm.trans (by rw [hz']; exact h0))
        · exact hzp.2 (hz_mask.symm.trans (by rw [hz']; exact h1))
        · rcases ha with hca | ⟨v, hv, hve⟩
          · exact absurd hca ha_nc
          · have he' : z &&& d = a &&& d := hz'.symm ▸ he
            exact hzb (List.mem_map.2 ⟨v, hv, hve.trans (he'.symm.trans hz_mask)⟩)
      obtain ⟨va, hva, hvae⟩ := ha.resolve_left ha_nc
      obtain ⟨vc, hvc, hvce⟩ := hc.resolve_left hc_nc
      set a' := a &&& d
      set c' := c &&& d
      have ha'_mem : a' ∈ b.map (· &&& d) := List.mem_map.2 ⟨va, hva, hvae⟩
      have hc'_mem : c' ∈ b.map (· &&& d) := List.mem_map.2 ⟨vc, hvc, hvce⟩
      have ha'_prop : a' ≠ 0 ∧ a' ≠ d := ⟨fun e => ha_nc (Or.inl e), fun e => ha_nc (Or.inr e)⟩
      have hc'_prop : c' ≠ 0 ∧ c' ≠ d := ⟨fun e => hc_nc (Or.inl e), fun e => hc_nc (Or.inr e)⟩
      have hne_ac : a' ≠ c' := by
        intro heq
        dsimp only [a', c'] at heq
        have hz_eq : z = a' := by
          cases op
          · simp only [z, binD, Bool.false_eq_true, ite_false]; rw [← andD_mask, ← heq]; simp [andD, a', Nat.and_assoc, Nat.and_self]
          · simp only [z, binD, ite_true]; rw [← orD_mask, ← heq]; simp [orD, a', Nat.and_assoc, Nat.and_self]
        exact hzb (hz_eq ▸ ha'_mem)
      set rest := ws.erase z
      have hrest_nd : rest.Nodup := hnd.erase z
      have hrest_sub : ∀ w ∈ rest, w ∈ b.map (· &&& d) := by
        intro w hw
        have ⟨hne, hm⟩ := hnd.mem_erase_iff.1 hw
        rcases List.mem_cons.1 (hsub w hm) with rfl | hmb
        · exact absurd rfl hne
        · exact hmb
      have hrest_prop : ∀ w ∈ rest, w ≠ 0 ∧ w ≠ d := fun w hw => hprop w (List.mem_of_mem_erase hw)
      have hp1 : ws.Perm (z :: rest) := List.perm_cons_erase hzm
      have ez : (if !op then andD d a' c' else orD d a' c') = z := by
        cases op
        · simp [z, binD, a', c', andD_mask]
        · simp [z, binD, a', c', orD_mask]
      have h1 : RunD d Y k ((if !op then andD d a' c' else orD d a' c') :: rest) := by
        rw [ez]; exact Run.perm hp1 h
      set ka := decide (a' ∈ rest)
      set kb := decide (c' ∈ rest)
      set tail := (rest.erase a').erase c'
      have htail_nd : tail.Nodup := (hrest_nd.erase a').erase c'
      have hna_tail : a' ∉ tail := by
        intro hm; exact hrest_nd.not_mem_erase (List.mem_of_mem_erase hm)
      have hnc_tail : c' ∉ tail := (hrest_nd.erase a').not_mem_erase
      have hna_mid : a' ∉ kept kb c' tail := by
        rw [mem_kept]; rintro (⟨_, h⟩ | h)
        · exact hne_ac h
        · exact hna_tail h
      have hrest_perm : rest.Perm (kept ka a' (kept kb c' tail)) := by
        refine (List.perm_ext_iff_of_nodup hrest_nd (nodup_kept ka a' _ (nodup_kept kb c' _ htail_nd hnc_tail) hna_mid)).2 ?_
        intro x
        rw [mem_kept, mem_kept, (hrest_nd.erase a').mem_erase_iff, hrest_nd.mem_erase_iff]
        by_cases hxa : x = a' <;> by_cases hxc : x = c' <;> by_cases hxr : x ∈ rest <;>
          simp_all [ka, kb]
      have h2 := Run.perm (hrest_perm.cons _) h1
      have hne0 : (if !op then andD d a' c' else orD d a' c') ≠ 0 := ez.symm ▸ hzp.1
      have hned : (if !op then andD d a' c' else orD d a' c') ≠ d := ez.symm ▸ hzp.2
      have hnm : (if !op then andD d a' c' else orD d a' c') ∉ (a' :: c' :: tail) := by
        rw [ez, List.mem_cons, List.mem_cons]; rintro (e | e | hm)
        · exact hzb (e ▸ ha'_mem)
        · exact hzb (e ▸ hc'_mem)
        · exact hnd.not_mem_erase (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
      have h3 : RunD d Y (k + 1) (a' :: c' :: tail) := Run.two (!op) ka kb hne0 hned hnm h2
      have hnd3 : (a' :: c' :: tail).Nodup :=
        List.nodup_cons.2 ⟨by simp [hne_ac, hna_tail], List.nodup_cons.2 ⟨hnc_tail, htail_nd⟩⟩
      refine ⟨k + 1, a' :: c' :: tail, le_rfl, hnd3, ?_, ?_, h3⟩
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact ha'_prop
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact hc'_prop
          · exact hrest_prop w (List.mem_of_mem_erase (List.mem_of_mem_erase hw))
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact ha'_mem
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact hc'_mem
          · exact hrest_sub w (List.mem_of_mem_erase (List.mem_of_mem_erase hw))
  · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
      rcases List.mem_cons.1 (hsub w hw) with rfl | hm
      · exact absurd hw hzm
      · exact hm, h⟩

theorem reach_to_run_aux {d : Nat} {roots : List Nat} {p bank} (hd : d &&& mask256 = d)
    (hr : NatReach d roots p bank) :
    ∀ {Y k ws}, ws.Nodup → (∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) →
      (∀ w ∈ ws, w ∈ bank.map (· &&& d)) → RunD d Y k ws →
      ∃ k' ws', k' ≤ p + k ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
        (∀ w ∈ ws', w ∈ roots.map (· &&& d)) ∧ RunD d Y k' ws' := by
  induction p generalizing bank with
  | zero =>
    intro Y k ws hnd hprop hsub hrun
    subst hr
    exact ⟨k, ws, by omega, hnd, hprop, hsub, hrun⟩
  | succ p ih =>
    intro Y k ws hnd hprop hsub hrun
    rcases hr with ⟨b, a, rfl, hrb, ha⟩ | ⟨b, a, c, op, rfl, hrb, ha, hc⟩
    · have hsub' : ∀ w ∈ ws, w ∈ negD d a :: b.map (· &&& d) := by
        intro w hw; have := hsub w hw; simp only [List.map_cons, negD, Nat.and_assoc, Nat.and_self] at this; exact this
      obtain ⟨k1, ws1, hk1, hnd1, hprop1, hsub1, hrun1⟩ := pull_one hd hnd hprop hrun ha hsub'
      obtain ⟨k2, ws2, hk2, hnd2, hprop2, hsub2, hrun2⟩ := ih hrb hnd1 hprop1 hsub1 hrun1
      exact ⟨k2, ws2, by omega, hnd2, hprop2, hsub2, hrun2⟩
    · have hsub' : ∀ w ∈ ws, w ∈ binD d op a c :: b.map (· &&& d) := by
        intro w hw; have := hsub w hw
        have ez : binD d op a c &&& d = binD d op a c := by cases op <;> simp [binD, andD, orD, Nat.and_assoc, Nat.and_self]
        simpa [List.map_cons, ez] using this
      obtain ⟨k1, ws1, hk1, hnd1, hprop1, hsub1, hrun1⟩ := pull_two hnd hprop hrun op ha hc hsub'
      obtain ⟨k2, ws2, hk2, hnd2, hprop2, hsub2, hrun2⟩ := ih hrb hnd1 hprop1 hsub1 hrun1
      exact ⟨k2, ws2, by omega, hnd2, hprop2, hsub2, hrun2⟩

theorem reach_to_run {d : Nat} {roots : List Nat} {T : Nat} {p bank} (hd : d &&& mask256 = d)
    (hnc : ¬ IsConst d T) (hr : NatReach d roots p bank) (ha : Avail d bank T) :
    ∃ s ws, s ≤ p ∧ ws.Nodup ∧ (∀ w ∈ ws, w ∈ roots.map (· &&& d)) ∧ RunD d (T &&& d) s ws := by
  obtain ⟨v, hv, hve⟩ := ha.resolve_left hnc
  have hprop : ∀ w ∈ [T &&& d], w ≠ 0 ∧ w ≠ d := by
    intro w hw; rw [List.mem_singleton.1 hw]
    exact ⟨fun e => hnc (Or.inl e), fun e => hnc (Or.inr e)⟩
  have hsub : ∀ w ∈ [T &&& d], w ∈ bank.map (· &&& d) := by
    intro w hw; rw [List.mem_singleton.1 hw]; exact List.mem_map.2 ⟨v, hv, hve⟩
  obtain ⟨s, ws, hs, hnd, _, hsub', hrun⟩ := reach_to_run_aux hd hr (List.nodup_singleton _) hprop hsub Run.done
  exact ⟨s, ws, by omega, hnd, hsub', hrun⟩

theorem runD_bits {d y s ws} (hd : d &&& mask256 = d) (h : RunD d y s ws) (i j : Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  have hmi : mask256.testBit i = true := by
    have := congrArg (fun v => v.testBit i) hd; simp [Nat.testBit_and, hi] at this; exact this
  have hmj : mask256.testBit j = true := by
    have := congrArg (fun v => v.testBit j) hd; simp [Nat.testBit_and, hj] at this; exact this
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one save _ _ _ _ ih =>
    apply ih; have ha := hw _ List.mem_cons_self
    intro w hm; cases save <;> simp only [kept, Bool.false_eq_true, ite_false, ite_true, List.mem_cons] at hm
    · rcases hm with rfl | hr
      · simp [negD, ha, hi, hj, hmi, hmj]
      · exact hw _ (by simp [hr])
    · rcases hm with rfl | rfl | hr
      · simp [negD, ha, hi, hj, hmi, hmj]
      · exact ha
      · exact hw _ (by simp [hr])
  | two conj ka kb _ _ _ _ ih =>
    apply ih; have ha := hw _ List.mem_cons_self; have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm; cases conj <;> cases ka <;> cases kb <;>
      simp only [kept, Bool.false_eq_true, ite_false, ite_true, List.mem_cons] at hm <;>
      rcases hm with rfl | hr <;>
      first | simp [andD, orD, ha, hb, hi, hj] | exact hw _ (by simp only [List.mem_cons]; tauto)

theorem runD_bits_le {d y s ws} (h : RunD d y s ws) (hl : ws.length = s + 1) (i j : Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws, w.testBit i ≤ w.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (hp.length_eq.trans hl) (fun w h => hw w (hp.mem_iff.1 h))
  | one save _ _ _ h _ => have hh := run_len h; cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb _ _ _ h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self; have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm; simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at hm
    rcases hm with rfl | hr
    · cases conj <;> simp only [andD, orD, ite_true, Bool.false_eq_true, ite_false, Nat.testBit_and, Nat.testBit_or, hi, hj, Bool.and_true] <;> grind
    · exact hw _ (by simp [hr])

theorem lower_base {d : Nat} {roots : List Nat} {T : Nat} (h : availB d roots T = false) :
    Lower d roots T 1 := by
  intro p bank hr ha
  cases p with
  | zero =>
    dsimp only [NatReach] at hr; rw [hr] at ha
    have ht := (availB_iff d roots T).2 ha
    rw [h] at ht; contradiction
  | succ p => omega

def pairOK (d T : Nat) (p : Nat × Nat) : Bool :=
  d.testBit p.1 && d.testBit p.2 && (T.testBit p.1 != T.testBit p.2)

def essOK (d T : Nat) (roots : List Nat) (a : Nat) (p : Nat × Nat) : Bool :=
  pairOK d T p && roots.all (fun v => (v == a) || (v.testBit p.1 == v.testBit p.2))

theorem countP_ge_sublist (p : Nat → Bool) {xs ys : List Nat}
    (hnd : xs.Nodup) (hsub : ∀ a ∈ xs, a ∈ ys) (hall : ∀ a ∈ xs, p a = true) :
    xs.length ≤ ys.countP p := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    have ⟨hna, hnd'⟩ := List.nodup_cons.1 hnd
    have ham : a ∈ ys := hsub a List.mem_cons_self
    have hperm : ys.Perm (a :: ys.erase a) := List.perm_cons_erase ham
    rw [hperm.countP_eq, List.countP_cons, hall a List.mem_cons_self]
    have ih' := ih hnd' (fun x hx => by
      have hne : x ≠ a := fun e => hna (e ▸ hx)
      exact (List.mem_erase_of_ne hne).2 (hsub x (List.mem_cons_of_mem _ hx)))
      (fun x hx => hall x (List.mem_cons_of_mem _ hx))
    simp only [ite_true, List.length_cons]
    omega

theorem lower_slice {d dSub T TSub L : Nat} {roots rootsSub : List Nat}
    (hd : d &&& mask256 = d) (hdSub : dSub &&& mask256 = dSub) (hsub : dSub &&& d = dSub)
    (hT : T &&& dSub = TSub &&& dSub)
    (hnc : isConstB d T = false) (hncSub : isConstB dSub TSub = false)
    (hcov : roots.all (availB dSub rootsSub) = true)
    (singles : List (Nat × Nat × Nat))
    (hs_nd : (singles.map Prod.fst).Nodup)
    (hs_ok : singles.all (fun e => isConstB dSub e.1 && essOK d (T &&& d) (roots.map (· &&& d)) e.1 e.2) = true)
    (hprior : Lower dSub rootsSub TSub L) :
    Lower d roots T (L + singles.length) := by
  have hnc' : ¬ IsConst d T := fun h => by rw [(isConstB_iff _ _).2 h] at hnc; contradiction
  have hncSub' : ¬ IsConst dSub (T &&& d) := by
    intro h
    have e : (T &&& d) &&& dSub = TSub &&& dSub := by
      rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]
    rcases h with h0 | h1
    · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
    · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
  intro p bank hr ha
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run hd hnc' hr ha
  have hws_av : ∀ w ∈ ws, Avail dSub rootsSub w := by
    intro w hw
    obtain ⟨r, hr_m, rfl⟩ := List.mem_map.1 (hws_sub w hw)
    have hav := (availB_iff _ _ _).1 (List.all_eq_true.1 hcov r hr_m)
    exact avail_of_eq (by rw [Nat.and_assoc, Nat.and_comm d dSub, hsub]) hav
  obtain ⟨q, next, hq, ht, hle⟩ := contraction hdSub hsub hncSub' hrun (p := 0) (bank := rootsSub) rfl hws_av
  have hTSub_av : Avail dSub next TSub := avail_of_eq (by
    rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]) ht
  have hL : L ≤ q := hprior q next hq hTSub_av
  have hsin_mem : ∀ a ∈ singles.map Prod.fst, a ∈ ws := by
    intro a ha
    obtain ⟨⟨a', r1, r2⟩, hm, rfl⟩ := List.mem_map.1 ha
    have hok := List.all_eq_true.1 hs_ok (a', r1, r2) hm
    simp only [Bool.and_eq_true, essOK, pairOK, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hok
    obtain ⟨_, ⟨⟨hr1, hr2⟩, hdiff⟩, hiso⟩ := hok
    by_contra hnot
    apply hdiff
    apply runD_bits hd hrun r1 r2 hr1 hr2
    intro w hw
    rcases hiso w (hws_sub w hw) with rfl | heq
    · exact absurd hw hnot
    · exact heq
  have hsin_const : ∀ a ∈ singles.map Prod.fst, isConstB dSub a = true := by
    intro a ha
    obtain ⟨⟨a', r1, r2⟩, hm, rfl⟩ := List.mem_map.1 ha
    have hok := List.all_eq_true.1 hs_ok _ hm
    simp only [Bool.and_eq_true] at hok
    exact hok.1
  have hcnt := countP_ge_sublist (isConstB dSub) hs_nd hsin_mem hsin_const
  simp only [List.length_map] at hcnt
  omega

def runChoices (d : Nat) (pool : List Nat) : Nat → Nat → Option (List Nat)
  | 0, _ => some pool
  | p + 1, bits =>
    let code := bits &&& 1023
    let op := code &&& 3
    let ia := (code >>> 2) &&& 15
    let ib := (code >>> 6) &&& 15
    if ia < pool.length && (op == 2 || ib < pool.length) then
      let a := pool.getD ia 0
      let b := pool.getD ib 0
      let w := if op == 2 then negD d a else binD d (op == 1) a b
      runChoices d (pool ++ [w]) p (bits >>> 10)
    else none

theorem getD_mem {xs : List Nat} {i : Nat} (hi : i < xs.length) : xs.getD i 0 ∈ xs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

theorem runChoices_sound {d : Nat} {roots : List Nat} :
    ∀ (p bits q : Nat) (bank pool result : List Nat),
      NatReach d roots q bank →
      (∀ v ∈ pool, Avail d bank v) →
      runChoices d pool p bits = some result →
      ∃ bank', NatReach d roots (q + p) bank' ∧ ∀ v ∈ result, Avail d bank' v
  | 0, _, q, bank, pool, result, hr, hsup, hok => by
    simp only [runChoices, Option.some.injEq] at hok; subst hok; exact ⟨bank, hr, hsup⟩
  | p + 1, bits, q, bank, pool, result, hr, hsup, hok => by
    simp only [runChoices] at hok
    split at hok
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hcond
      obtain ⟨hia, hopb⟩ := hcond
      set code := bits &&& 1023
      set op := code &&& 3
      set ia := (code >>> 2) &&& 15
      set ib := (code >>> 6) &&& 15
      set a := pool.getD ia 0
      set b := pool.getD ib 0
      set w := if op == 2 then negD d a else binD d (op == 1) a b
      have ha : Avail d bank a := hsup a (getD_mem hia)
      have hr1 : NatReach d roots (q + 1) (w :: bank) := by
        by_cases h2 : op = 2
        · simp only [w, h2, beq_self_eq_true, ite_true]
          exact Or.inl ⟨bank, a, rfl, hr, ha⟩
        · have hib : ib < pool.length := hopb.resolve_left h2
          have hb : Avail d bank b := hsup b (getD_mem hib)
          simp only [w, h2, beq_iff_eq, ite_false]
          exact Or.inr ⟨bank, a, b, (op == 1), rfl, hr, ha, hb⟩
      have hsup1 : ∀ v ∈ pool ++ [w], Avail d (w :: bank) v := by
        intro v hv; rcases List.mem_append.1 hv with hv | hv
        · exact avail_cons _ _ (hsup v hv)
        · rw [List.mem_singleton.1 hv]; exact Or.inr ⟨w, List.mem_cons_self, rfl⟩
      obtain ⟨bank', hrb', hsb'⟩ := runChoices_sound p (bits >>> 10) (q + 1) (w :: bank) (pool ++ [w]) result hr1 hsup1 hok
      exact ⟨bank', by simpa [Nat.add_assoc, Nat.add_comm 1] using hrb', hsb'⟩
    · contradiction

def checkCutEntry (dSub : Nat) (rootsSub : List Nat) (LSub s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  let p := (hint >>> 8) &&& 15
  decide (s + p < LSub + ws.countP (isConstB dSub)) &&
  match runChoices dSub rootsSub p (hint >>> 12) with
  | none => false
  | some pool => ws.all (availB dSub pool)

theorem checkCutEntry_sound {d dSub T TSub LSub s : Nat} {rootsSub ws : List Nat}
    (hdSub : dSub &&& mask256 = dSub) (hsub : dSub &&& d = dSub)
    (hT : T &&& dSub = TSub &&& dSub) (hncSub : isConstB dSub TSub = false)
    (hprior : Lower dSub rootsSub TSub LSub) (hint : Nat)
    (hchk : checkCutEntry dSub rootsSub LSub s ws hint = true) :
    ¬ RunD d (T &&& d) s ws := by
  intro hrun
  simp only [checkCutEntry, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨hineq, hmatch⟩ := hchk
  cases hrc : runChoices dSub rootsSub ((hint >>> 8) &&& 15) (hint >>> 12) with
  | none => rw [hrc] at hmatch; contradiction
  | some pool =>
    rw [hrc] at hmatch
    have hsup0 : ∀ v ∈ rootsSub, Avail dSub rootsSub v := fun v hv => Or.inr ⟨v, hv, rfl⟩
    obtain ⟨bank, hrb, hsb⟩ := runChoices_sound _ _ 0 rootsSub rootsSub pool rfl hsup0 hrc
    simp only [Nat.zero_add] at hrb
    have hws_av : ∀ w ∈ ws, Avail dSub bank w := by
      intro w hw
      have hav := (availB_iff _ _ _).1 (List.all_eq_true.1 hmatch w hw)
      rcases hav with hc | ⟨v, hv, he⟩
      · exact Or.inl hc
      · exact avail_of_eq he (hsb v hv)
    have hnc' : ¬ IsConst dSub (T &&& d) := by
      intro h; have e : (T &&& d) &&& dSub = TSub &&& dSub := by rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]
      rcases h with h0 | h1
      · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
      · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
    obtain ⟨q, next, hq, ht, hle⟩ := contraction hdSub hsub hnc' hrun hrb hws_av
    have hL := hprior q next hq (avail_of_eq (by rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]) ht)
    omega

def coversP (pairs : List (Nat × Nat)) (s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s + 1 then
    pairs.all (fun p => ws.any (fun w => !w.testBit p.1 && w.testBit p.2))
  else
    pairs.all (fun p => ws.any (fun w => w.testBit p.1 != w.testBit p.2))

theorem coversP_ok {d T s : Nat} (hd : d &&& mask256 = d)
    (pairs : List (Nat × Nat))
    (hpairs : pairs.all (fun p => d.testBit p.1 && d.testBit p.2 && !(T &&& d).testBit p.1 && (T &&& d).testBit p.2) = true)
    {ws : List Nat} (h : RunD d (T &&& d) s ws) : coversP pairs s ws = true := by
  unfold coversP
  by_cases hl : ws.length = s + 1
  · simp only [hl, beq_self_eq_true, ite_true, List.all_eq_true, List.any_eq_true]
    intro ⟨u, v⟩ hm
    have hp := List.all_eq_true.1 hpairs (u, v) hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    by_contra! hall
    have hle := runD_bits_le h hl v u hp.1.1.2 hp.1.1.1 (fun w hw => by
      have hbad := hall w hw
      cases hu : w.testBit u <;> cases hv : w.testBit v <;> simp_all)
    rw [hp.1.2, hp.2] at hle; contradiction
  · simp only [hl, beq_iff_eq, ite_false, List.all_eq_true, List.any_eq_true, bne_iff_ne]
    intro ⟨u, v⟩ hm
    have hp := List.all_eq_true.1 hpairs (u, v) hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    by_contra! hall
    have heq := runD_bits hd h u v hp.1.1.1 hp.1.1.2 hall
    rw [hp.1.2, hp.2] at heq; contradiction

def unorientedCov (pairs : List (Nat × Nat)) (ws : List Nat) : Bool :=
  pairs.all (fun p => ws.any (fun w => w.testBit p.1 != w.testBit p.2))

theorem unorientedCov_ok {d T s : Nat} (hd : d &&& mask256 = d)
    (pairs : List (Nat × Nat))
    (hpairs : pairs.all (fun p => d.testBit p.1 && d.testBit p.2 && !(T &&& d).testBit p.1 && (T &&& d).testBit p.2) = true)
    {ws : List Nat} (h : RunD d (T &&& d) s ws) : unorientedCov pairs ws = true := by
  simp only [unorientedCov, List.all_eq_true, List.any_eq_true, bne_iff_ne]
  intro ⟨u, v⟩ hm
  have hp := List.all_eq_true.1 hpairs (u, v) hm
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  by_contra! hall
  have heq := runD_bits hd h u v hp.1.1.1 hp.1.1.2 hall
  rw [hp.1.2, hp.2] at heq; contradiction

def maskP (m : Nat) : Nat := 2 ^ m - 1

def projBit (rs : List Nat) (w : Nat) : Nat :=
  rs.foldr (fun r acc => (acc <<< 1) ||| (if w.testBit r then 1 else 0)) 0

theorem projBit_testBit (rs : List Nat) (w : Nat) (i : Nat) :
    (projBit rs w).testBit i = if h : i < rs.length then w.testBit rs[i] else false := by
  induction rs generalizing i with
  | nil => simp [projBit]
  | cons r rs ih =>
    cases i with
    | zero =>
      simp only [projBit, List.foldr_cons, Nat.testBit_or, Nat.testBit_shiftLeft,
        Nat.not_le.2 Nat.zero_lt_one, decide_false, Bool.false_and, Bool.false_or,
        List.length_cons, Nat.zero_lt_succ, dite_true, List.getElem_cons_zero]
      cases w.testBit r <;> simp
    | succ i =>
      simp only [projBit, List.foldr_cons, Nat.testBit_or, Nat.testBit_shiftLeft,
        Nat.succ_le_succ (Nat.zero_le i), decide_true, Bool.true_and, Nat.add_sub_cancel,
        List.length_cons, Nat.succ_lt_succ_iff, List.getElem_cons_succ]
      have h1 : (if w.testBit r = true then 1 else 0).testBit (i + 1) = false := by
        cases w.testBit r <;> simp [Nat.testBit_succ]
      rw [h1, Bool.or_false]; exact ih i

theorem projBit_negD {dm : Nat} (hd : dm &&& mask256 = dm) {rs : List Nat}
    (hrs : ∀ r ∈ rs, dm.testBit r = true) (w : Nat) :
    projBit rs (negD dm w) = projBit rs w ^^^ maskP rs.length := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [projBit_testBit, Nat.testBit_xor, projBit_testBit, maskP, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < rs.length
  · have hdr := hrs rs[i] (List.getElem_mem hi)
    have hmr : mask256.testBit rs[i] = true := by
      have := congrArg (fun v => v.testBit rs[i]) hd; simp [Nat.testBit_and, hdr] at this; exact this
    simp [hi, negD, hdr, hmr]
  · simp [hi]

theorem projBit_andD {dm : Nat} {rs : List Nat} (hrs : ∀ r ∈ rs, dm.testBit r = true) (a b : Nat) :
    projBit rs (andD dm a b) = projBit rs a &&& projBit rs b := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [projBit_testBit, Nat.testBit_and, projBit_testBit, projBit_testBit]
  by_cases hi : i < rs.length
  · simp [hi, andD, hrs rs[i] (List.getElem_mem hi)]
  · simp [hi]

theorem projBit_orD {dm : Nat} {rs : List Nat} (hrs : ∀ r ∈ rs, dm.testBit r = true) (a b : Nat) :
    projBit rs (orD dm a b) = projBit rs a ||| projBit rs b := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [projBit_testBit, Nat.testBit_or, projBit_testBit, projBit_testBit]
  by_cases hi : i < rs.length
  · simp [hi, orD, hrs rs[i] (List.getElem_mem hi)]
  · simp [hi]

theorem foldl_or_testBit {α : Type} (g : α → Nat) (xs : List α) (acc i : Nat) :
    (xs.foldl (fun a x => a ||| g x) acc).testBit i = (acc.testBit i || xs.any (fun x => (g x).testBit i)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, List.any_cons, Bool.or_assoc]

def coversD (mp s : Nat) (dws : List (Nat × Nat × Nat)) : Bool :=
  if dws.length == s + 1 then
    dws.foldl (fun acc d => acc ||| ((d.2.1 ^^^ mp) &&& d.2.2)) 0 == mp
  else
    dws.foldl (fun acc d => acc ||| (d.2.1 ^^^ d.2.2)) 0 == mp

theorem coversD_eq (pairs : List (Nat × Nat)) (s : Nat) (ws : List Nat) :
    coversD (maskP pairs.length) s (ws.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))) =
      coversP pairs s ws := by
  set r1s := pairs.map Prod.fst
  set r2s := pairs.map Prod.snd
  set mp := maskP pairs.length
  have hr1 : r1s.length = pairs.length := List.length_map _
  have hr2 : r2s.length = pairs.length := List.length_map _
  unfold coversD coversP
  simp only [List.length_map]
  split
  · apply Bool.eq_iff_iff.2
    rw [beq_iff_eq, List.all_eq_true]
    constructor
    · intro heq pr hpr
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hpr
      have hb := congrArg (fun v => v.testBit i) heq
      rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, List.any_map] at hb
      simp only [mp, maskP, Nat.testBit_two_pow_sub_one, hi, decide_true] at hb
      obtain ⟨w, hw, hwt⟩ := List.any_eq_true.1 hb
      simp only [Function.comp_def, Nat.testBit_and, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_true,
        Nat.testBit_two_pow_sub_one, decide_true, Bool.xor_true] at hwt
      exact List.any_eq_true.2 ⟨w, hw, by simpa [r1s, r2s] using hwt⟩
    · intro hall
      apply Nat.eq_of_testBit_eq; intro i
      rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, List.any_map]
      simp only [mp, maskP, Nat.testBit_two_pow_sub_one]
      by_cases hi : i < pairs.length
      · simp only [hi, decide_true]
        obtain ⟨w, hw, hwt⟩ := List.any_eq_true.1 (hall pairs[i] (List.getElem_mem hi))
        exact List.any_eq_true.2 ⟨w, hw, by
          simp only [Function.comp_def, Nat.testBit_and, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_true,
            Nat.testBit_two_pow_sub_one, decide_true, Bool.xor_true, r1s, r2s, List.getElem_map]
          exact hwt⟩
      · simp only [hi, decide_false, List.any_eq_false]
        intro w _
        simp only [Function.comp_def, Nat.testBit_and, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_false,
          Nat.testBit_two_pow_sub_one, decide_false, Bool.xor_false, Bool.and_false, not_false_eq_true, Bool.false_eq_true]
  · apply Bool.eq_iff_iff.2
    rw [beq_iff_eq, List.all_eq_true]
    constructor
    · intro heq pr hpr
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hpr
      have hb := congrArg (fun v => v.testBit i) heq
      rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, List.any_map] at hb
      simp only [mp, maskP, Nat.testBit_two_pow_sub_one, hi, decide_true] at hb
      obtain ⟨w, hw, hwt⟩ := List.any_eq_true.1 hb
      simp only [Function.comp_def, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_true] at hwt
      exact List.any_eq_true.2 ⟨w, hw, by simpa [r1s, r2s, bne] using hwt⟩
    · intro hall
      apply Nat.eq_of_testBit_eq; intro i
      rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, List.any_map]
      simp only [mp, maskP, Nat.testBit_two_pow_sub_one]
      by_cases hi : i < pairs.length
      · simp only [hi, decide_true]
        obtain ⟨w, hw, hwt⟩ := List.any_eq_true.1 (hall pairs[i] (List.getElem_mem hi))
        exact List.any_eq_true.2 ⟨w, hw, by
          simp only [Function.comp_def, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_true, r1s, r2s, List.getElem_map]
          simpa [bne] using hwt⟩
      · simp only [hi, decide_false, List.any_eq_false]
        intro w _
        simp only [Function.comp_def, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_false,
          Bool.xor_false, Bool.false_eq_true, not_false_eq_true]

theorem erase_map_inj {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hinj : Function.Injective f) (xs : List α) (a : α) :
    (xs.map f).erase (f a) = (xs.erase a).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.erase_cons]
    by_cases h : x = a
    · subst h; simp
    · have hf : (f x == f a) = false := beq_false_of_ne (fun e => h (hinj e))
      have hx : (x == a) = false := beq_false_of_ne h
      simp [hf, hx, ih]

def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat + c.toNat
  let y := (!e).toNat + (!f).toNat
  if a then (if d then y else max x (max y (x + y - 1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {d y s ws} (h : RunD d y s ws) (hl : ws.length = s + 1)
    (v : Nat → Nat) (hand : ∀ a b, v (andD d a b) ≤ v a + v b)
    (hor : ∀ a b, v (orD d a b) ≤ v a + v b) : v y ≤ (ws.map v).sum := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => rw [← (p.map v).sum_eq]; exact ih (p.length_eq.trans hl)
  | one save _ _ _ h _ => have hh := run_len h; cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb _ _ _ h ih =>
    have hh := run_len h; cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;>
      first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {dm y s ws} (h : RunD dm y s ws) (hl : ws.length = s + 1)
    (a b c d e f : Nat)
    (ha : dm.testBit a = true) (hb : dm.testBit b = true) (hc : dm.testBit c = true)
    (hd : dm.testBit d = true) (he : dm.testBit e = true) (hf : dm.testBit f = true) :
    eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6, andD, Nat.testBit_and, ha, hb, hc, hd, he, hf, Bool.and_true] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6, orD, Nat.testBit_and, Nat.testBit_or, ha, hb, hc, hd, he, hf, Bool.and_true] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def sumBelow (v : Nat → Nat) : List Nat → Nat → Bool
  | [], n => n != 0
  | w :: ws, n => decide (v w < n) && sumBelow v ws (n - v w)

theorem sumBelow_iff (v : Nat → Nat) (ws : List Nat) (n : Nat) :
    sumBelow v ws n = true ↔ (ws.map v).sum < n := by
  induction ws generalizing n with
  | nil => simp [sumBelow]
  | cons w ws ih => rw [sumBelow, Bool.and_eq_true, decide_eq_true_eq, ih, List.map_cons, List.sum_cons]; omega

def scoreCheck (dm y s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  let a := code &&& 255
  let b := (code >>> 8) &&& 255
  let c := (code >>> 16) &&& 255
  let d := (code >>> 24) &&& 255
  let e := (code >>> 32) &&& 255
  let f := (code >>> 40) &&& 255
  dm.testBit a && dm.testBit b && dm.testBit c && dm.testBit d && dm.testBit e && dm.testBit f &&
    ws.length == s + 1 && sumBelow (eval6 a b c d e f) ws (eval6 a b c d e f y)

theorem scoreCheck_no {dm y s ws} (h : RunD dm y s ws) (code : Nat) :
    scoreCheck dm y s ws code = false := by
  unfold scoreCheck
  by_cases hok : dm.testBit (code &&& 255) = true ∧ dm.testBit ((code >>> 8) &&& 255) = true ∧
      dm.testBit ((code >>> 16) &&& 255) = true ∧ dm.testBit ((code >>> 24) &&& 255) = true ∧
      dm.testBit ((code >>> 32) &&& 255) = true ∧ dm.testBit ((code >>> 40) &&& 255) = true ∧
      ws.length = s + 1
  · obtain ⟨ha, hb, hc, hd, he, hf, hl⟩ := hok
    simp only [ha, hb, hc, hd, he, hf, hl, beq_self_eq_true, Bool.true_and]
    by_contra hbad
    have hsum := (sumBelow_iff _ _ _).1 (Bool.eq_true_of_not_eq_false hbad)
    exact (Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _ ha hb hc hd he hf)) hsum
  · by_contra hbad
    have ht := Bool.eq_true_of_not_eq_false hbad
    simp only [Bool.and_eq_true, beq_iff_eq] at ht
    exact hok ⟨ht.1.1.1.1.1.1.1, ht.1.1.1.1.1.1.2, ht.1.1.1.1.1.2, ht.1.1.1.1.2, ht.1.1.1.2, ht.1.1.2, ht.1.2⟩

def scr (dm y s : Nat) (pool : List Nat) (zs : List Nat) : Bool :=
  zs.length == s + 1 && pool.any (scoreCheck dm y s zs)

theorem scr_no {dm y s : Nat} (pool : List Nat) {zs : List Nat}
    (h : RunD dm y s zs) : scr dm y s pool zs = false := by
  unfold scr; rw [Bool.and_eq_false_iff]; right; rw [List.any_eq_false]
  intro x _; rw [scoreCheck_no h x]; simp

def nextD (dm : Nat) (slack : Nat) (ws : List Nat) (f : List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 &&
      (let w := negD dm a
       w != 0 && w != dm && !(ws.contains w) &&
         (f (w :: ra) || (slack ≥ 2 && f (w :: a :: ra))))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false, true].any fun conj =>
          let w := if conj then andD dm a b else orD dm a b
          w != 0 && w != dm && !(ws.contains w) &&
            (f (w :: r) || (slack ≥ 1 && (f (w :: a :: r) || f (w :: b :: r))) ||
              (slack ≥ 2 && f (w :: a :: b :: r))))

theorem nextD_one {dm y a rest} {save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h0 : negD dm a ≠ 0) (hd : negD dm a ≠ dm) (hnm : negD dm a ∉ (a :: rest))
    (h : RunD dm y s (negD dm a :: kept save a rest))
    (f : List Nat → Bool) (hf : ∀ ys, RunD dm y s ys → f ys = true) :
    nextD dm (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h; have hl := p.length_eq; simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s + 2 - ws.length := by cases save <;> simp [kept] at hh <;> omega
  have hnc : ws.contains (negD dm a) = false := by
    cases h : ws.contains (negD dm a) with
    | false => rfl
    | true => exact absurd (p.mem_iff.2 (by simpa using h)) hnm
  have h0b : (negD dm a != 0) = true := bne_iff_ne.2 h0
  have hdb : (negD dm a != dm) = true := bne_iff_ne.2 hd
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left; rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  simp only [h0b, hdb, hnc, Bool.not_false, Bool.true_and]
  have ht := hf _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true => simp [kept] at ht hh; simp [ht, show 2 ≤ s + 2 - ws.length by omega]

theorem nextD_two_sorted {dm y a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h0 : (if conj then andD dm a b else orD dm a b) ≠ 0)
    (hd : (if conj then andD dm a b else orD dm a b) ≠ dm)
    (hnm : (if conj then andD dm a b else orD dm a b) ∉ (a :: b :: rest))
    (h : RunD dm y s ((if conj then andD dm a b else orD dm a b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool) (hf : ∀ ys, RunD dm y s ys → f ys = true) :
    nextD dm (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h; have hl := p.length_eq; simp only [List.length_cons] at hl hh
  have hnc : ws.contains (if conj then andD dm a b else orD dm a b) = false := by
    cases h : ws.contains (if conj then andD dm a b else orD dm a b) with
    | false => rfl
    | true => exact absurd (p.mem_iff.2 (by simpa using h)) hnm
  have h0b : ((if conj then andD dm a b else orD dm a b) != 0) = true := bne_iff_ne.2 h0
  have hdb : ((if conj then andD dm a b else orD dm a b) != dm) = true := bne_iff_ne.2 hd
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; right; apply List.any_eq_true.2 ⟨b, hb, ?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab, ?_⟩
  apply List.any_eq_true.2 ⟨conj, by cases conj <;> simp, ?_⟩
  simp only [h0b, hdb, hnc, Bool.not_false, Bool.true_and]
  have ht := hf _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true] <;>
    first | (simp [show 2 ≤ s + 2 - ws.length by omega]) | (simp [show 1 ≤ s + 2 - ws.length by omega])

theorem nextD_two {dm y a b rest} {conj ka kb : Bool} {s ws} (p : (a :: b :: rest).Perm ws)
    (h0 : (if conj then andD dm a b else orD dm a b) ≠ 0)
    (hd : (if conj then andD dm a b else orD dm a b) ≠ dm)
    (hnm : (if conj then andD dm a b else orD dm a b) ∉ (a :: b :: rest))
    (h : RunD dm y s ((if conj then andD dm a b else orD dm a b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool) (hf : ∀ ys, RunD dm y s ys → f ys = true) :
    nextD dm (s + 2 - ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact nextD_two_sorted hab p h0 hd hnm h f hf
  · have he : (if conj then andD dm a b else orD dm a b) = (if conj then andD dm b a else orD dm b a) := by
      cases conj <;> simp [andD, orD, Nat.and_comm, Nat.or_comm]
    have hnm' : (if conj then andD dm b a else orD dm b a) ∉ (b :: a :: rest) := by
      rw [← he]; intro hm; exact hnm ((List.Perm.swap _ _ _).mem_iff.1 hm)
    apply nextD_two_sorted (conj := conj) (ka := kb) (kb := ka) hba ((List.Perm.swap _ _ _).trans p)
      (he ▸ h0) (he ▸ hd) hnm' _ f hf
    rw [he] at h; apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]; exact List.Perm.swap _ _ _

theorem nextD_complete {dm y t ws} (h : RunD dm y t ws) :
    ∀ s, t = s + 1 → ∀ zs, ws.Perm zs → ∀ f : List Nat → Bool,
      (∀ ys, RunD dm y s ys → f ys = true) →
      nextD dm (s + 2 - zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one save h0 hd hnm h _ => intro s he zs p f hf; cases he; exact nextD_one p h0 hd hnm h f hf
  | two conj ka kb h0 hd hnm h _ => intro s he zs p f hf; cases he; exact nextD_two p h0 hd hnm h f hf

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, i => f i && span f n (i + 1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o + n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h; intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem range_split {P : Nat → Prop} {lo mid hi : Nat}
    (h1 : ∀ i, lo ≤ i → i < mid → P i) (h2 : ∀ i, mid ≤ i → i < hi → P i) :
    ∀ i, lo ≤ i → i < hi → P i := fun i hlo hhi =>
  if h : i < mid then h1 i hlo h else h2 i (Nat.le_of_not_lt h) hhi

def fld (T w i : Nat) : Nat :=
  (T >>> (w * i)) &&& (if w == 32 then 4294967295 else if w == 52 then 4503599627370495 else if w == 256 then mask256 else 2 ^ w - 1)

def forceN {α : Type} (n : Nat) (k : Nat → α) : α := match n with | 0 => k 0 | m + 1 => k (m + 1)
theorem forceN_eq {α : Type} (n : Nat) (k : Nat → α) : forceN n k = k n := by cases n <;> rfl
def bsr (read : Nat → Nat) (h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      forceN ((lo + hi) / 2) fun mid =>
      if read mid ≤ h then bsr read h f mid hi else bsr read h f lo mid
    else lo

def hw256 (seed w : Nat) : Nat :=
  forceN ((((w &&& 4294967295) ^^^ seed) * 2654435761 +
           (((w >>> 32) &&& 4294967295) ^^^ seed) * 2246822519) &&& 4294967295) fun x =>
  forceN (((x ^^^ (x >>> 16)) * 2246822519) &&& 4294967295) fun y =>
  ((y ^^^ (y >>> 13)) * 3266489917) &&& 4294967295

def hz (seed : Nat) : List Nat → Nat
  | [] => 0
  | w :: t => hw256 seed w + hz seed t

def hk (seed : Nat) (zs : List Nat) : Nat := hz seed zs &&& 4294967295

def found (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (s : Nat) (zs : List Nat) : Bool :=
  decide (idx s zs < N s) && zs.isPerm (S s (idx s zs))

def foundH (S : Nat → Nat → List Nat) (N : Nat → Nat) (htAt : Nat → Nat → Nat)
    (idxH : Nat → Nat → Nat) (s h : Nat) (zs : List Nat) : Bool :=
  forceN (idxH s h) fun i =>
  decide (i < N s) && (htAt s i == h) && zs.isPerm (S s i)

def nextD_decor (dm mp : Nat) (slack : Nat) (dws : List (Nat × Nat × Nat))
    (f : List (Nat × Nat × Nat) → Bool) : Bool :=
  dws.any fun da =>
    let a := da.1
    let ra := dws.erase da
    (slack ≥ 1 &&
      (let w := negD dm a
       w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
         let dw := (w, da.2.1 ^^^ mp, da.2.2 ^^^ mp)
         (f (dw :: ra) || (slack ≥ 2 && f (dw :: da :: ra))))) ||
    ra.any fun db =>
      let b := db.1
      a ≤ b && (let r := ra.erase db
        [false, true].any fun conj =>
          let w := if conj then andD dm a b else orD dm a b
          w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
            let dw := if conj then (w, da.2.1 &&& db.2.1, da.2.2 &&& db.2.2)
                      else (w, da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)
            (f (dw :: r) || (slack ≥ 1 && (f (dw :: da :: r) || f (dw :: db :: r))) ||
              (slack ≥ 2 && f (dw :: da :: db :: r))))

theorem nextD_decor_gen (dm mp : Nat) (dec : Nat → Nat × Nat × Nat)
    (hfst : ∀ w, (dec w).1 = w)
    (hneg : ∀ a, (negD dm a, (dec a).2.1 ^^^ mp, (dec a).2.2 ^^^ mp) = dec (negD dm a))
    (hbin : ∀ (c : Bool) a b,
      (if c then (if c then andD dm a b else orD dm a b, (dec a).2.1 &&& (dec b).2.1, (dec a).2.2 &&& (dec b).2.2)
       else (if c then andD dm a b else orD dm a b, (dec a).2.1 ||| (dec b).2.1, (dec a).2.2 ||| (dec b).2.2)) =
      dec (if c then andD dm a b else orD dm a b))
    (slack : Nat) (ws : List Nat) (g : List (Nat × Nat × Nat) → Bool) :
    nextD_decor dm mp slack (ws.map dec) g = nextD dm slack ws (fun zs => g (zs.map dec)) := by
  have hinj : Function.Injective dec := fun x y h => by rw [← hfst x, ← hfst y, h]
  have herase : ∀ (l : List Nat) x, (l.map dec).erase (dec x) = (l.erase x).map dec :=
    fun l x => erase_map_inj dec hinj l x
  have hcont : ∀ (l : List Nat) w, (l.map dec).any (fun x => x.1 == w) = l.contains w := by
    intro l w; apply Bool.eq_iff_iff.2; simp [hfst]
  unfold nextD_decor nextD
  simp only [List.any_map, Function.comp_def, hfst, herase, hcont, hneg, hbin, List.map_cons]

theorem nextD_decor_eq {dm : Nat} (hd : dm &&& mask256 = dm)
    (pairs : List (Nat × Nat))
    (hr1 : ∀ r ∈ pairs.map Prod.fst, dm.testBit r = true)
    (hr2 : ∀ r ∈ pairs.map Prod.snd, dm.testBit r = true)
    (slack : Nat) (ws : List Nat) (g : List (Nat × Nat × Nat) → Bool) :
    let dec := fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w)
    nextD_decor dm (maskP pairs.length) slack (ws.map dec) g =
      nextD dm slack ws (fun zs => g (zs.map dec)) := by
  intro dec
  apply nextD_decor_gen
  · intro w; rfl
  · intro a
    simp only [dec, projBit_negD hd hr1, projBit_negD hd hr2, List.length_map]
  · intro c a b
    cases c <;> simp only [dec, ↓reduceIte, Bool.false_eq_true, projBit_andD hr1, projBit_andD hr2,
      projBit_orD hr1, projBit_orD hr2]

def colB (mp : Nat) (d : Bool) (p : Nat × Nat) : Nat :=
  if d then (p.1 ^^^ mp) &&& p.2 else p.1 ^^^ p.2

def addC (x : Nat) (c : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (c.1 ||| x, c.2.1 ||| (c.1 &&& x), c.2.2 ||| (c.2.1 &&& x))

def cov3 (mp : Nat) (d : Bool) (dws : List (Nat × Nat × Nat)) : Nat × Nat × Nat :=
  dws.foldl (fun c dw => addC (colB mp d dw.2) c) (0, 0, 0)

def takeOne (c : Nat × Nat × Nat) (x : Nat) : Nat := (c.1 ^^^ x) ||| c.2.1
def takeTwo (c : Nat × Nat × Nat) (x y : Nat) : Nat :=
  (c.1 ^^^ (x ||| y)) ||| (c.2.1 &&& (x ^^^ y)) ||| c.2.2

theorem cov3_bit (mp : Nat) (d : Bool) (dws : List (Nat × Nat × Nat)) (i : Nat) :
    let k := dws.countP (fun dw => (colB mp d dw.2).testBit i)
    (cov3 mp d dws).1.testBit i = decide (1 ≤ k) ∧
    (cov3 mp d dws).2.1.testBit i = decide (2 ≤ k) ∧
    (cov3 mp d dws).2.2.testBit i = decide (3 ≤ k) := by
  have hgen : ∀ (xs : List (Nat × Nat × Nat)) (c : Nat × Nat × Nat) (k0 : Nat),
      (c.1.testBit i = decide (1 ≤ k0) ∧ c.2.1.testBit i = decide (2 ≤ k0) ∧ c.2.2.testBit i = decide (3 ≤ k0)) →
      let k := k0 + xs.countP (fun dw => (colB mp d dw.2).testBit i)
      (xs.foldl (fun acc dw => addC (colB mp d dw.2) acc) c).1.testBit i = decide (1 ≤ k) ∧
      (xs.foldl (fun acc dw => addC (colB mp d dw.2) acc) c).2.1.testBit i = decide (2 ≤ k) ∧
      (xs.foldl (fun acc dw => addC (colB mp d dw.2) acc) c).2.2.testBit i = decide (3 ≤ k) := by
    intro xs
    induction xs with
    | nil => intro c k0 ⟨h1, h2, h3⟩; simp [h1, h2, h3]
    | cons dw xs ih =>
      intro c k0 ⟨h1, h2, h3⟩
      simp only [List.foldl_cons, List.countP_cons]
      have hc : (addC (colB mp d dw.2) c).1.testBit i =
            decide (1 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) ∧
          (addC (colB mp d dw.2) c).2.1.testBit i =
            decide (2 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) ∧
          (addC (colB mp d dw.2) c).2.2.testBit i =
            decide (3 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) := by
        simp only [addC, Nat.testBit_or, Nat.testBit_and, h1, h2, h3]
        cases hb : (colB mp d dw.2).testBit i <;>
          rcases k0 with _ | _ | _ | k0 <;>
          simp [hb, Nat.le_add_left]
      have ih' := ih (addC (colB mp d dw.2) c) (k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) hc
      cases hb : (colB mp d dw.2).testBit i <;> simp only [hb, ↓reduceIte, Bool.false_eq_true, Nat.add_zero] at ih' ⊢
      · exact ih'
      · simpa only [Nat.add_assoc, Nat.add_comm 1] using ih'
  simpa only [cov3, Nat.zero_testBit, Nat.zero_add] using hgen dws (0, 0, 0) 0 (by simp)

theorem cov3_perm (mp : Nat) (d : Bool) {xs ys : List (Nat × Nat × Nat)} (p : xs.Perm ys) :
    cov3 mp d xs = cov3 mp d ys := by
  have heq : ∀ i, (cov3 mp d xs).1.testBit i = (cov3 mp d ys).1.testBit i ∧
      (cov3 mp d xs).2.1.testBit i = (cov3 mp d ys).2.1.testBit i ∧
      (cov3 mp d xs).2.2.testBit i = (cov3 mp d ys).2.2.testBit i := by
    intro i
    obtain ⟨a1, a2, a3⟩ := cov3_bit mp d xs i
    obtain ⟨b1, b2, b3⟩ := cov3_bit mp d ys i
    rw [p.countP_eq] at a1 a2 a3
    exact ⟨a1.trans b1.symm, a2.trans b2.symm, a3.trans b3.symm⟩
  apply Prod.ext
  · exact Nat.eq_of_testBit_eq (fun i => (heq i).1)
  · apply Prod.ext
    · exact Nat.eq_of_testBit_eq (fun i => (heq i).2.1)
    · exact Nat.eq_of_testBit_eq (fun i => (heq i).2.2)

theorem takeOne_eq (mp : Nat) (d : Bool) (a : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) :
    takeOne (cov3 mp d (a :: rest)) (colB mp d a.2) = (cov3 mp d rest).1 := by
  apply Nat.eq_of_testBit_eq; intro i
  obtain ⟨h1, h2, _⟩ := cov3_bit mp d (a :: rest) i
  obtain ⟨r1, _, _⟩ := cov3_bit mp d rest i
  simp only [takeOne, Nat.testBit_or, Nat.testBit_xor, h1, h2, r1, List.countP_cons]
  set k := rest.countP (fun dw => (colB mp d dw.2).testBit i)
  cases ha : (colB mp d a.2).testBit i <;> simp only [ha, Bool.false_eq_true, ↓reduceIte] <;>
    rcases k with _ | _ | _ | k
  · decide
  · decide
  · decide
  · simp only [show 1 ≤ k + 3 by omega, show 2 ≤ k + 3 by omega, decide_true, Bool.xor_false, Bool.or_true]
  · decide
  · decide
  · decide
  · simp only [show 1 ≤ k + 3 + 1 by omega, show 2 ≤ k + 3 + 1 by omega, show 1 ≤ k + 3 by omega,
      decide_true, Bool.xor_true, Bool.or_true, Bool.or_false]

theorem takeTwo_eq (mp : Nat) (d : Bool) (a b : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) :
    takeTwo (cov3 mp d (a :: b :: rest)) (colB mp d a.2) (colB mp d b.2) = (cov3 mp d rest).1 := by
  apply Nat.eq_of_testBit_eq; intro i
  obtain ⟨h1, h2, h3⟩ := cov3_bit mp d (a :: b :: rest) i
  obtain ⟨r1, _, _⟩ := cov3_bit mp d rest i
  simp only [takeTwo, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, h1, h2, h3, r1, List.countP_cons]
  set k := rest.countP (fun dw => (colB mp d dw.2).testBit i)
  cases ha : (colB mp d a.2).testBit i <;> cases hb : (colB mp d b.2).testBit i <;>
    simp only [ha, hb, Bool.false_eq_true, ↓reduceIte] <;>
    rcases k with _ | _ | _ | k <;>
    (first | decide | simp only [
      show 1 ≤ k + 3 by omega, show 2 ≤ k + 3 by omega, show 3 ≤ k + 3 by omega,
      show 1 ≤ k + 3 + 1 by omega, show 2 ≤ k + 3 + 1 by omega, show 3 ≤ k + 3 + 1 by omega,
      show 1 ≤ k + 3 + 1 + 1 by omega, show 2 ≤ k + 3 + 1 + 1 by omega, show 3 ≤ k + 3 + 1 + 1 by omega,
      decide_true, Bool.xor_true, Bool.xor_false, Bool.or_true, Bool.or_false, Bool.and_true, Bool.and_false])

theorem cov3_coversD (mp s : Nat) (dw : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) :
    let d := (dw :: rest).length == s + 1
    ((cov3 mp d rest).1 ||| colB mp d dw.2 == mp) = coversD mp s (dw :: rest) := by
  intro d
  have e : ∀ b : Bool, ((cov3 mp b rest).1 ||| colB mp b dw.2) =
      (dw :: rest).foldl (fun acc x => acc ||| colB mp b x.2) 0 := by
    intro b; apply Nat.eq_of_testBit_eq; intro i
    obtain ⟨h1, _, _⟩ := cov3_bit mp b rest i
    rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, Nat.testBit_or, h1, List.any_cons]
    have hp : decide (1 ≤ rest.countP (fun dw => (colB mp b dw.2).testBit i)) =
        rest.any (fun x => (colB mp b x.2).testBit i) := by
      rw [Bool.eq_iff_iff, decide_eq_true_eq, Nat.succ_le_iff, List.countP_pos_iff, List.any_eq_true]
    rw [hp, Bool.or_comm]
  have hf : ∀ b : Bool, (cov3 mp b rest).1 ||| colB mp b dw.2 =
      (dw :: rest).foldl (fun acc x => acc ||| (if b then (x.2.1 ^^^ mp) &&& x.2.2 else x.2.1 ^^^ x.2.2)) 0 := by
    intro b; simpa only [colB] using e b
  unfold coversD
  dsimp only [d]
  cases (dw :: rest).length == s + 1
  · simpa only [Bool.false_eq_true, ↓reduceIte] using congrArg (· == mp) (hf false)
  · simpa only [↓reduceIte] using congrArg (· == mp) (hf true)

def nextD_cov (dm mp s slack : Nat) (dws : List (Nat × Nat × Nat))
    (f : List (Nat × Nat × Nat) → Bool) : Bool :=
  let len := dws.length
  let covF := cov3 mp false dws
  let covT := cov3 mp true dws
  let du0 := len == s + 1
  let du1 := len + 1 == s + 1
  let db0 := len - 1 == s + 1
  let db1 := len == s + 1
  let db2 := len + 1 == s + 1
  dws.any fun da =>
    let a := da.1
    (slack ≥ 1 &&
      (let pneg := (da.2.1 ^^^ mp, da.2.2 ^^^ mp)
       let uok0 := (takeOne (if du0 then covT else covF) (colB mp du0 da.2) ||| colB mp du0 pneg) == mp
       let uok1 := slack ≥ 2 && (((if du1 then covT.1 else covF.1) ||| colB mp du1 pneg) == mp)
       (uok0 || uok1) &&
       (let w := negD dm a
        w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
          let dw := (w, pneg)
          let ra := dws.erase da
          ((uok0 && f (dw :: ra)) || (uok1 && f (dw :: da :: ra)))))) ||
    (dws.erase da).any fun db =>
      let b := db.1
      a ≤ b &&
        [false, true].any fun conj =>
          let pz := if conj then (da.2.1 &&& db.2.1, da.2.2 &&& db.2.2)
                    else (da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)
          let ok0 := (takeTwo (if db0 then covT else covF) (colB mp db0 da.2) (colB mp db0 db.2) ||| colB mp db0 pz) == mp
          let ok1a := slack ≥ 1 && ((takeOne (if db1 then covT else covF) (colB mp db1 db.2) ||| colB mp db1 pz) == mp)
          let ok1b := slack ≥ 1 && ((takeOne (if db1 then covT else covF) (colB mp db1 da.2) ||| colB mp db1 pz) == mp)
          let ok2 := slack ≥ 2 && (((if db2 then covT.1 else covF.1) ||| colB mp db2 pz) == mp)
          (ok0 || ok1a || ok1b || ok2) &&
          (let w := if conj then andD dm a b else orD dm a b
           w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
             let dw := (w, pz)
             let r := (dws.erase da).erase db
             ((ok0 && f (dw :: r)) || (ok1a && f (dw :: da :: r)) || (ok1b && f (dw :: db :: r)) || (ok2 && f (dw :: da :: db :: r))))

theorem nextD_cov_eq (dm mp s slack : Nat) (dws : List (Nat × Nat × Nat))
    (g : List (Nat × Nat × Nat) → Bool) :
    nextD_cov dm mp s slack dws g =
      nextD_decor dm mp slack dws (fun dzs => coversD mp s dzs && g dzs) := by
  unfold nextD_cov nextD_decor
  dsimp only
  apply Bool.eq_iff_iff.2; simp only [List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨da, hda, hrest⟩
    refine ⟨da, hda, ?_⟩
    rcases hrest with ⟨hsl, _, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩ | ⟨db, hdb, hab, conj, hcj, _, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩
    · left
      refine ⟨hsl, ⟨⟨hw0, hwdm⟩, hnw⟩, ?_⟩
      set dw := (negD dm da.1, da.2.1 ^^^ mp, da.2.2 ^^^ mp)
      set ra := dws.erase da
      have hp : dws.Perm (da :: ra) := List.perm_cons_erase hda
      have hcov0 : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) da.2) ||| colB mp (dws.length == s + 1) (da.2.1 ^^^ mp, da.2.2 ^^^ mp)) == mp) =
          coversD mp s (dw :: ra) := by
        have hl : (dw :: ra).length = dws.length := by simp [hp.length_eq]
        have hc : ∀ d, cov3 mp d dws = cov3 mp d (da :: ra) := fun d => cov3_perm mp d hp
        have hc0 := cov3_coversD mp s dw ra
        rw [hl] at hc0
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc0 ⊢
        · rw [hc false, takeOne_eq, hc0]
        · rw [hc true, takeOne_eq, hc0]
      have hcov1 :
          (((if dws.length + 1 == s + 1 then (cov3 mp true dws).1 else (cov3 mp false dws).1) |||
            colB mp (dws.length + 1 == s + 1) (da.2.1 ^^^ mp, da.2.2 ^^^ mp)) == mp) =
          coversD mp s (dw :: da :: ra) := by
        have hl : (dw :: da :: ra).length = dws.length + 1 := by simp [hp.length_eq]
        have hc : ∀ d, cov3 mp d dws = cov3 mp d (da :: ra) := fun d => cov3_perm mp d hp
        have hc1 := cov3_coversD mp s dw (da :: ra)
        rw [hl] at hc1
        cases hd : (dws.length + 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc1 ⊢
        · rw [hc false, hc1]
        · rw [hc true, hc1]
      rcases hfx with ⟨hu0, hf0⟩ | ⟨⟨hsl2, hu1⟩, hf1⟩
      · left; exact ⟨hcov0 ▸ hu0, hf0⟩
      · right; exact ⟨hsl2, hcov1 ▸ hu1, hf1⟩
    · right
      refine ⟨db, hdb, hab, conj, hcj, ⟨⟨hw0, hwdm⟩, hnw⟩, ?_⟩
      set pz := if conj then (da.2.1 &&& db.2.1, da.2.2 &&& db.2.2) else (da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)
      set w := if conj then andD dm da.1 db.1 else orD dm da.1 db.1
      set dw := (w, pz)
      have hdw : (if conj = true then (w, da.2.1 &&& db.2.1, da.2.2 &&& db.2.2)
                  else (w, da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)) = dw := by cases conj <;> rfl
      simp only [hdw]
      set ra := dws.erase da
      set r := ra.erase db
      have hp : dws.Perm (da :: db :: r) := (List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
      have hlen_r : (dw :: r).length = dws.length - 1 := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_a : (dw :: da :: r).length = dws.length := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_b : (dw :: db :: r).length = dws.length := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_ab : (dw :: da :: db :: r).length = dws.length + 1 := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hc2 : ∀ d, cov3 mp d dws = cov3 mp d (da :: db :: r) := fun d => cov3_perm mp d hp
      have hcov0 := cov3_coversD mp s dw r
      rw [hlen_r] at hcov0
      have hcov0' : ((takeTwo (if dws.length - 1 == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length - 1 == s + 1) da.2) (colB mp (dws.length - 1 == s + 1) db.2) |||
          colB mp (dws.length - 1 == s + 1) pz) == mp) = coversD mp s (dw :: r) := by
        cases hd : (dws.length - 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov0 ⊢
        · rw [hc2 false, takeTwo_eq, hcov0]
        · rw [hc2 true, takeTwo_eq, hcov0]
      have hc_a : ∀ d, cov3 mp d dws = cov3 mp d (db :: da :: r) :=
        fun d => cov3_perm mp d (hp.trans (List.Perm.swap _ _ _))
      have hcov1a := cov3_coversD mp s dw (da :: r)
      rw [hlen_a] at hcov1a
      have hcov1a' : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) db.2) ||| colB mp (dws.length == s + 1) pz) == mp) = coversD mp s (dw :: da :: r) := by
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov1a ⊢
        · rw [hc_a false, takeOne_eq, hcov1a]
        · rw [hc_a true, takeOne_eq, hcov1a]
      have hcov1b := cov3_coversD mp s dw (db :: r)
      rw [hlen_b] at hcov1b
      have hcov1b' : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) da.2) ||| colB mp (dws.length == s + 1) pz) == mp) = coversD mp s (dw :: db :: r) := by
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov1b ⊢
        · rw [hc2 false, takeOne_eq, hcov1b]
        · rw [hc2 true, takeOne_eq, hcov1b]
      have hcov2 := cov3_coversD mp s dw (da :: db :: r)
      rw [hlen_ab] at hcov2
      have hcov2' : (((if dws.length + 1 == s + 1 then (cov3 mp true dws).1 else (cov3 mp false dws).1) |||
          colB mp (dws.length + 1 == s + 1) pz) == mp) = coversD mp s (dw :: da :: db :: r) := by
        cases hd : (dws.length + 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov2 ⊢
        · rw [hc2 false, hcov2]
        · rw [hc2 true, hcov2]
      rcases hfx with ((⟨hu0, hf0⟩ | ⟨⟨hsl1, hu1a⟩, hf1a⟩) | ⟨⟨hsl1, hu1b⟩, hf1b⟩) | ⟨⟨hsl2, hu2⟩, hf2⟩
      · left; left; exact ⟨hcov0' ▸ hu0, hf0⟩
      · left; right; exact ⟨hsl1, Or.inl ⟨hcov1a' ▸ hu1a, hf1a⟩⟩
      · left; right; exact ⟨hsl1, Or.inr ⟨hcov1b' ▸ hu1b, hf1b⟩⟩
      · right; exact ⟨hsl2, hcov2' ▸ hu2, hf2⟩
  · rintro ⟨da, hda, hrest⟩
    refine ⟨da, hda, ?_⟩
    rcases hrest with ⟨hsl, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩ | ⟨db, hdb, hab, conj, hcj, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩
    · left
      set dw := (negD dm da.1, da.2.1 ^^^ mp, da.2.2 ^^^ mp)
      set ra := dws.erase da
      have hp : dws.Perm (da :: ra) := List.perm_cons_erase hda
      have hcov0 : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) da.2) ||| colB mp (dws.length == s + 1) (da.2.1 ^^^ mp, da.2.2 ^^^ mp)) == mp) =
          coversD mp s (dw :: ra) := by
        have hl : (dw :: ra).length = dws.length := by simp [hp.length_eq]
        have hc : ∀ d, cov3 mp d dws = cov3 mp d (da :: ra) := fun d => cov3_perm mp d hp
        have hc0 := cov3_coversD mp s dw ra; rw [hl] at hc0
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc0 ⊢
        · rw [hc false, takeOne_eq, hc0]
        · rw [hc true, takeOne_eq, hc0]
      have hcov1 : (((if dws.length + 1 == s + 1 then (cov3 mp true dws).1 else (cov3 mp false dws).1) |||
            colB mp (dws.length + 1 == s + 1) (da.2.1 ^^^ mp, da.2.2 ^^^ mp)) == mp) =
          coversD mp s (dw :: da :: ra) := by
        have hl : (dw :: da :: ra).length = dws.length + 1 := by simp [hp.length_eq]
        have hc : ∀ d, cov3 mp d dws = cov3 mp d (da :: ra) := fun d => cov3_perm mp d hp
        have hc1 := cov3_coversD mp s dw (da :: ra); rw [hl] at hc1
        cases hd : (dws.length + 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc1 ⊢
        · rw [hc false, hc1]
        · rw [hc true, hc1]
      rcases hfx with ⟨hc0, hg0⟩ | ⟨hsl2, hc1, hg1⟩
      · have hu0 : ((takeOne _ _ ||| _) == mp) = true := hcov0.symm ▸ hc0
        exact ⟨hsl, Or.inl hu0, ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl ⟨hu0, hg0⟩⟩
      · have hu1 : ((_ ||| _) == mp) = true := hcov1.symm ▸ hc1
        exact ⟨hsl, Or.inr ⟨hsl2, hu1⟩, ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inr ⟨⟨hsl2, hu1⟩, hg1⟩⟩
    · right
      refine ⟨db, hdb, hab, conj, hcj, ?_⟩
      set pz := if conj then (da.2.1 &&& db.2.1, da.2.2 &&& db.2.2) else (da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)
      set w := if conj then andD dm da.1 db.1 else orD dm da.1 db.1
      set dw := (w, pz)
      have hdw : (if conj = true then (w, da.2.1 &&& db.2.1, da.2.2 &&& db.2.2)
                  else (w, da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)) = dw := by cases conj <;> rfl
      simp only [hdw] at hfx
      set ra := dws.erase da
      set r := ra.erase db
      have hp : dws.Perm (da :: db :: r) := (List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
      have hlen_r : (dw :: r).length = dws.length - 1 := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_a : (dw :: da :: r).length = dws.length := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_b : (dw :: db :: r).length = dws.length := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_ab : (dw :: da :: db :: r).length = dws.length + 1 := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hc2 : ∀ d, cov3 mp d dws = cov3 mp d (da :: db :: r) := fun d => cov3_perm mp d hp
      have hcov0 := cov3_coversD mp s dw r; rw [hlen_r] at hcov0
      have hcov0' : ((takeTwo (if dws.length - 1 == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length - 1 == s + 1) da.2) (colB mp (dws.length - 1 == s + 1) db.2) |||
          colB mp (dws.length - 1 == s + 1) pz) == mp) = coversD mp s (dw :: r) := by
        cases hd : (dws.length - 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov0 ⊢
        · rw [hc2 false, takeTwo_eq, hcov0]
        · rw [hc2 true, takeTwo_eq, hcov0]
      have hc_a : ∀ d, cov3 mp d dws = cov3 mp d (db :: da :: r) :=
        fun d => cov3_perm mp d (hp.trans (List.Perm.swap _ _ _))
      have hcov1a := cov3_coversD mp s dw (da :: r); rw [hlen_a] at hcov1a
      have hcov1a' : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) db.2) ||| colB mp (dws.length == s + 1) pz) == mp) = coversD mp s (dw :: da :: r) := by
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov1a ⊢
        · rw [hc_a false, takeOne_eq, hcov1a]
        · rw [hc_a true, takeOne_eq, hcov1a]
      have hcov1b := cov3_coversD mp s dw (db :: r); rw [hlen_b] at hcov1b
      have hcov1b' : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) da.2) ||| colB mp (dws.length == s + 1) pz) == mp) = coversD mp s (dw :: db :: r) := by
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov1b ⊢
        · rw [hc2 false, takeOne_eq, hcov1b]
        · rw [hc2 true, takeOne_eq, hcov1b]
      have hcov2 := cov3_coversD mp s dw (da :: db :: r); rw [hlen_ab] at hcov2
      have hcov2' : (((if dws.length + 1 == s + 1 then (cov3 mp true dws).1 else (cov3 mp false dws).1) |||
          colB mp (dws.length + 1 == s + 1) pz) == mp) = coversD mp s (dw :: da :: db :: r) := by
        cases hd : (dws.length + 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov2 ⊢
        · rw [hc2 false, hcov2]
        · rw [hc2 true, hcov2]
      rcases hfx with (⟨hc0, hg0⟩ | ⟨hsl1, ⟨hc1a, hg1a⟩ | ⟨hc1b, hg1b⟩⟩) | ⟨hsl2, hc2', hg2⟩
      · have u0 : ((takeTwo _ _ _ ||| _) == mp) = true := hcov0'.symm ▸ hc0
        exact ⟨Or.inl (Or.inl (Or.inl u0)), ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl (Or.inl (Or.inl ⟨u0, hg0⟩))⟩
      · have u1a : ((takeOne _ _ ||| _) == mp) = true := hcov1a'.symm ▸ hc1a
        exact ⟨Or.inl (Or.inl (Or.inr ⟨hsl1, u1a⟩)), ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl (Or.inl (Or.inr ⟨⟨hsl1, u1a⟩, hg1a⟩))⟩
      · have u1b : ((takeOne _ _ ||| _) == mp) = true := hcov1b'.symm ▸ hc1b
        exact ⟨Or.inl (Or.inr ⟨hsl1, u1b⟩), ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl (Or.inr ⟨⟨hsl1, u1b⟩, hg1b⟩)⟩
      · have u2 : ((_ ||| _) == mp) = true := hcov2'.symm ▸ hc2'
        exact ⟨Or.inr ⟨hsl2, u2⟩, ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inr ⟨⟨hsl2, u2⟩, hg2⟩⟩

def bar (dm Y : Nat) (pairs : List (Nat × Nat)) (r1s r2s : List Nat) (mp : Nat)
    (SD : Nat → Nat → List (Nat × Nat × Nat)) (S : Nat → Nat → List Nat)
    (N : Nat → Nat) (htAt idxH : Nat → Nat → Nat)
    (ori : List Nat → List Nat) (seed : Nat) (pool : List Nat) (cutHitH : Nat → Nat → List Nat → Bool) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [Y])
  | s + 1, i =>
    let dws := SD (s + 1) i
    !(nextD_cov dm mp s (s + 2 - dws.length) dws fun dzs =>
        let zs := dzs.map Prod.fst
        !(scr dm Y s pool zs) &&
        (let cz := ori zs
         forceN (hk seed cz) fun h =>
         !(foundH S N htAt idxH s h cz) && !(cutHitH s h cz)))

theorem bar_all {dm T : Nat} {pairs r1s r2s mp SD S N htAt idxH ori seed pool cutHitH cap}
    (hd : dm &&& mask256 = dm)
    (hr1_eq : r1s = pairs.map Prod.fst) (hr2_eq : r2s = pairs.map Prod.snd) (hmp_eq : mp = maskP pairs.length)
    (hSD : ∀ s j, SD s j = (S s j).map (fun w => (w, projBit r1s w, projBit r2s w)))
    (hpairs : pairs.all (fun p => dm.testBit p.1 && dm.testBit p.2 && !(T &&& dm).testBit p.1 && (T &&& dm).testBit p.2) = true)
    (hr : ∀ {u ys}, RunD dm (T &&& dm) u ys → RunD dm (T &&& dm) u (ori ys))
    (hcut : ∀ {u ys}, cutHitH u (hk seed ys) ys = true → ¬ RunD dm (T &&& dm) u ys)
    (hc : ∀ s ≤ cap, ∀ i < N s, bar dm (T &&& dm) pairs r1s r2s mp SD S N htAt idxH ori seed pool cutHitH s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ RunD dm (T &&& dm) s (S s i) := by
  subst hr1_eq hr2_eq hmp_eq
  have hr1 : ∀ r ∈ pairs.map Prod.fst, dm.testBit r = true := by
    intro r hr'; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr'
    have h := List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.1
  have hr2 : ∀ r ∈ pairs.map Prod.snd, dm.testBit r = true := by
    intro r hr'; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr'
    have h := List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.2
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    have hb := hc s hs i hi
    cases s with
    | zero => simp [bar, zero_done hh rfl] at hb
    | succ s =>
      by_contra! hn
      let F (zs : List Nat) :=
        coversP pairs s zs && !(scr dm (T &&& dm) s pool zs) &&
        (let cz := ori zs
         forceN (hk seed cz) fun h =>
         !(foundH S N htAt idxH s h cz) && !(cutHitH s h cz))
      have hF (zs) (hz : RunD dm (T &&& dm) s zs) : F zs = true := by
        have hcz := hr hz
        have hcutf : cutHitH s (hk seed (ori zs)) (ori zs) = false := by
          cases h : cutHitH s (hk seed (ori zs)) (ori zs) with
          | false => rfl
          | true => exact absurd hcz (hcut h)
        simp only [F, forceN_eq, coversP_ok hd pairs hpairs hz, scr_no pool hz, hcutf, Bool.not_false, Bool.true_and, Bool.and_true, foundH]
        simp only [Bool.not_eq_true', Bool.and_eq_false_imp, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
        rintro ⟨hj, _⟩
        by_contra! hp
        have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact ih s (by omega) (by omega) _ hj (Run.perm p hcz)
      have hN := nextD_complete hh s rfl _ (List.Perm.refl _) F hF
      dsimp only [bar] at hb
      rw [hSD, List.length_map, nextD_cov_eq, nextD_decor_eq hd pairs hr1 hr2] at hb
      have hFeq : (fun zs => coversD (maskP pairs.length) s (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))) &&
          (let zs' := (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))).map Prod.fst
           !(scr dm (T &&& dm) s pool zs') &&
           (let cz := ori zs'
            forceN (hk seed cz) fun h =>
            !(foundH S N htAt idxH s h cz) && !(cutHitH s h cz)))) = F := by
        funext zs
        have hfst : (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))).map Prod.fst = zs := by
          simp [List.map_map, Function.comp_def]
        rw [coversD_eq, hfst]
        simp only [F, Bool.and_assoc]
      rw [hFeq, hN] at hb
      contradiction

def gvN (w : List Nat) (g : Gate) : Nat :=
  match g.op with
  | .and => g.inputs.foldr (fun i acc => andD mask256 (w.getD i 0) acc) mask256
  | .or  => g.inputs.foldr (fun i acc => orD mask256 (w.getD i 0) acc) 0
  | .not => match g.inputs with | [] => mask256 | i :: _ => negD mask256 (w.getD i 0)
  | _ => 0

def execN (gs : List Gate) (w : List Nat) : List Nat :=
  gs.foldl (fun l g => l ++ [gvN l g]) w

theorem gvN_bit (w : List Nat) (g : Gate) (r : Nat) (hr : r < 256)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (gvN w g).testBit r = g.op.eval (g.inputs.map fun i => (w.map (·.testBit r)).getD i false) := by
  have hm : mask256.testBit r = true := by simp [mask256_bit, hr]
  have hgd : ∀ i, (w.map (·.testBit r)).getD i false = (w.getD i 0).testBit r := by
    intro i; simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases w[i]? with | none => simp | some v => rfl
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with h | h | h
  · simp only [gvN, GateOp.eval, h]
    induction g.inputs with
    | nil => simp [hm]
    | cons i l ih =>
      rw [List.foldr_cons, List.map_cons, List.all_cons, id_eq, andD, Nat.testBit_and, Nat.testBit_and, hm, Bool.and_true, hgd, ih]
  · simp only [gvN, GateOp.eval, h]
    induction g.inputs with
    | nil => simp
    | cons i l ih =>
      rw [List.foldr_cons, List.map_cons, List.any_cons, id_eq, orD, Nat.testBit_and, Nat.testBit_or, hm, Bool.and_true, hgd, ih]
  · simp only [gvN, GateOp.eval, h]
    cases g.inputs with
    | nil => simp [hm]
    | cons i l => simp only [List.map_cons, List.headD_cons, negD, Nat.testBit_and, Nat.testBit_xor, hm, Bool.and_true, Bool.xor_true, hgd]

theorem execN_bit (gs : List Gate) (w : List Nat) (r : Nat) (hr : r < 256)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (execN gs w).map (·.testBit r) =
      gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) (w.map (·.testBit r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [execN, List.foldl_cons] at ih ⊢
    rw [ih _ (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))]
    simp [gvN_bit w g r hr (hfan g List.mem_cons_self)]

theorem execN_reach (gs : List Gate) (roots : List Nat)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ (p : Nat) (w bank : List Nat), NatReach mask256 roots p bank →
      (∀ v ∈ w, Avail mask256 bank v) →
      ∃ p' bank', p' ≤ p + gs.length ∧ NatReach mask256 roots p' bank' ∧
        ∀ v ∈ execN gs w, Avail mask256 bank' v := by
  induction gs with
  | nil => intro p w bank hr hsup; exact ⟨p, bank, by omega, hr, hsup⟩
  | cons g gs ih =>
    intro p w bank hr hsup
    have hav_gd : ∀ i, Avail mask256 bank (w.getD i 0) := by
      intro i; by_cases hi : i < w.length
      · exact hsup _ (getD_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))

    have hstep : ∃ p1 bank1, p1 ≤ p + 1 ∧ NatReach mask256 roots p1 bank1 ∧
        (∀ v ∈ w ++ [gvN w g], Avail mask256 bank1 v) := by
      have hg := hfan g List.mem_cons_self
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      obtain ⟨hop, hlen⟩ := hg
      have hand_m : ∀ a, andD mask256 a mask256 &&& mask256 = a &&& mask256 := fun a => by
        simp [andD, Nat.and_assoc, Nat.and_self]
      have hor_0 : ∀ a, orD mask256 a 0 &&& mask256 = a &&& mask256 := fun a => by
        simp [orD, Nat.and_assoc, Nat.and_self]
      have lift_w : ∀ z, (∀ v ∈ w, Avail mask256 (z :: bank) v) := fun z v hv => avail_cons z v (hsup v hv)
      rcases hop with h | h | h
      · rcases hgi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN, h, hgi]))⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
              exact avail_of_eq (hand_m _).symm (hav_gd i)⟩
        · refine ⟨p + 1, binD mask256 false (w.getD i 0) (w.getD j 0) :: bank, le_rfl,
            Or.inr ⟨bank, _, _, false, rfl, hr, hav_gd i, hav_gd j⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
            exact Or.inr ⟨_, List.mem_cons_self, by simp [binD, andD, Nat.and_assoc, Nat.and_self]⟩
        · rw [hgi] at hlen; simp at hlen
      · rcases hgi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inl (by simp [gvN, h, hgi]))⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
              exact avail_of_eq (hor_0 _).symm (hav_gd i)⟩
        · refine ⟨p + 1, binD mask256 true (w.getD i 0) (w.getD j 0) :: bank, le_rfl,
            Or.inr ⟨bank, _, _, true, rfl, hr, hav_gd i, hav_gd j⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
            exact Or.inr ⟨_, List.mem_cons_self, by apply Nat.eq_of_testBit_eq; intro r; simp [binD, orD]; cases mask256.testBit r <;> simp⟩
        · rw [hgi] at hlen; simp at hlen
      · rcases hgi : g.inputs with _ | ⟨i, l⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN, h, hgi]))⟩
        · refine ⟨p + 1, negD mask256 (w.getD i 0) :: bank, le_rfl,
            Or.inl ⟨bank, _, rfl, hr, hav_gd i⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi]; exact Or.inr ⟨_, List.mem_cons_self, rfl⟩
    obtain ⟨p1, bank1, hp1, hr1, hsup1⟩ := hstep
    obtain ⟨p2, bank2, hp2, hr2, hsup2⟩ := ih (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')) p1 _ bank1 hr1 hsup1
    exact ⟨p2, bank2, by simp; omega, hr2, hsup2⟩

def xs256 : List Nat :=
  [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
   0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
   0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
   0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
   0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
   0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
   0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]

theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with | nil => rfl | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
def goal_all : Nat := 0xfeeaeee8fee0ece0
def dom_63 : Nat := 0xffffffffffffffff
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]
def dom_x1_0_x4_1_x5_0 : Nat := 0x33330000
def roots_x1_0_x4_1_x5_0 : List Nat := [0x22220000, 0x30300000, 0x33000000]
def dom_x1_0_x4_1 : Nat := 0x3333000033330000
def roots_x1_0_x4_1 : List Nat := [0x2222000022220000, 0x3030000030300000, 0x3300000033000000, 0x3333000000000000]
def dom_x0_0_x4_1_x5_0 : Nat := 0x55550000
def roots_x0_0_x4_1_x5_0 : List Nat := [0x44440000, 0x50500000, 0x55000000]
def dom_x4_1_x5_0 : Nat := 0xffff0000
def roots_x4_1_x5_0 : List Nat := [0xaaaa0000, 0xcccc0000, 0xf0f00000, 0xff000000]
def dom_x0_0_x4_1_x5_1 : Nat := 0x5555000000000000
def roots_x0_0_x4_1_x5_1 : List Nat := [0x4444000000000000, 0x5050000000000000, 0x5500000000000000]
def dom_x4_1_x5_1 : Nat := 0xffff000000000000
def roots_x4_1_x5_1 : List Nat := [0xaaaa000000000000, 0xcccc000000000000, 0xf0f0000000000000, 0xff00000000000000]
def dom_x4_1 : Nat := 0xffff0000ffff0000
def roots_x4_1 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]
def dom_x0_1_x2_0_x4_0 : Nat := 0xa0a00000a0a
def roots_x0_1_x2_0_x4_0 : List Nat := [0x80800000808, 0xa0000000a00, 0xa0a00000000]
def dom_x2_0_x4_0 : Nat := 0xf0f00000f0f
def roots_x2_0_x4_0 : List Nat := [0xa0a00000a0a, 0xc0c00000c0c, 0xf0000000f00, 0xf0f00000000]
def dom_x0_1_x1_0_x2_0 : Nat := 0x202020202020202
def roots_x0_1_x1_0_x2_0 : List Nat := [0x200020002000200, 0x202000002020000, 0x202020200000000]
def dom_x0_1_x1_0 : Nat := 0x2222222222222222
def roots_x0_1_x1_0 : List Nat := [0x2020202020202020, 0x2200220022002200, 0x2222000022220000, 0x2222222200000000]
def dom_x0_1 : Nat := 0xaaaaaaaaaaaaaaaa
def roots_x0_1 : List Nat := [0x8888888888888888, 0xa0a0a0a0a0a0a0a0, 0xaa00aa00aa00aa00, 0xaaaa0000aaaa0000, 0xaaaaaaaa00000000]
def dom_x0_1_x2_0 : Nat := 0xa0a0a0a0a0a0a0a
def roots_x0_1_x2_0 : List Nat := [0x808080808080808, 0xa000a000a000a00, 0xa0a00000a0a0000, 0xa0a0a0a00000000]
def dom_x1_0_x5_1 : Nat := 0x3333333300000000
def roots_x1_0_x5_1 : List Nat := [0x2222222200000000, 0x3030303000000000, 0x3300330000000000, 0x3333000000000000]
def dom_x1_0_x3_1_x5_0 : Nat := 0x33003300
def roots_x1_0_x3_1_x5_0 : List Nat := [0x22002200, 0x30003000, 0x33000000]
def dom_x1_0_x5_0 : Nat := 0x33333333
def roots_x1_0_x5_0 : List Nat := [0x22222222, 0x30303030, 0x33003300, 0x33330000]
def dom_x1_0_x2_0 : Nat := 0x303030303030303
def roots_x1_0_x2_0 : List Nat := [0x202020202020202, 0x300030003000300, 0x303000003030000, 0x303030300000000]
def dom_x1_0_x3_1 : Nat := 0x3300330033003300
def roots_x1_0_x3_1 : List Nat := [0x2200220022002200, 0x3000300030003000, 0x3300000033000000, 0x3300330000000000]
def dom_x1_0 : Nat := 0x3333333333333333
def roots_x1_0 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]
def dom_x0_0_x5_0 : Nat := 0x55555555
def roots_x0_0_x5_0 : List Nat := [0x44444444, 0x50505050, 0x55005500, 0x55550000]
def dom_x3_1_x5_0 : Nat := 0xff00ff00
def roots_x3_1_x5_0 : List Nat := [0xaa00aa00, 0xcc00cc00, 0xf000f000, 0xff000000]
def dom_x5_0 : Nat := 0xffffffff
def roots_x5_0 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
def dom_x2_0_x4_0_x5_1 : Nat := 0xf0f00000000
def roots_x2_0_x4_0_x5_1 : List Nat := [0xa0a00000000, 0xc0c00000000, 0xf0000000000]
def dom_x2_0_x5_1 : Nat := 0xf0f0f0f00000000
def roots_x2_0_x5_1 : List Nat := [0xa0a0a0a00000000, 0xc0c0c0c00000000, 0xf000f0000000000, 0xf0f000000000000]
def dom_x2_0 : Nat := 0xf0f0f0f0f0f0f0f
def roots_x2_0 : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]
def dom_x0_1_x4_0 : Nat := 0xaaaa0000aaaa
def roots_x0_1_x4_0 : List Nat := [0x888800008888, 0xa0a00000a0a0, 0xaa000000aa00, 0xaaaa00000000]
def dom_x3_0_x4_0_x5_1 : Nat := 0xff00000000
def roots_x3_0_x4_0_x5_1 : List Nat := [0xaa00000000, 0xcc00000000, 0xf000000000]
def dom_x3_0_x5_1 : Nat := 0xff00ff00000000
def roots_x3_0_x5_1 : List Nat := [0xaa00aa00000000, 0xcc00cc00000000, 0xf000f000000000, 0xff000000000000]
def dom_x0_0_x5_1 : Nat := 0x5555555500000000
def roots_x0_0_x5_1 : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]
def dom_x4_0_x5_1 : Nat := 0xffff00000000
def roots_x4_0_x5_1 : List Nat := [0xaaaa00000000, 0xcccc00000000, 0xf0f000000000, 0xff0000000000]
def dom_x5_1 : Nat := 0xffffffff00000000
def roots_x5_1 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]
def dom_x3_0_x4_0 : Nat := 0xff000000ff
def roots_x3_0_x4_0 : List Nat := [0xaa000000aa, 0xcc000000cc, 0xf0000000f0, 0xff00000000]
def dom_x4_0 : Nat := 0xffff0000ffff
def roots_x4_0 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]
def dom_x3_0 : Nat := 0xff00ff00ff00ff
def roots_x3_0 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]
def dom_x3_1 : Nat := 0xff00ff00ff00ff00
def roots_x3_1 : List Nat := [0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000]

namespace S_x1_0_x4_1_x5_0
def pairsG : List (Nat × Nat) := [(17, 21), (17, 25), (20, 21), (20, 28), (24, 25), (24, 28)]
def r1sG : List Nat := [17, 17, 20, 20, 24, 24]
def r2sG : List Nat := [21, 25, 21, 28, 25, 28]
def mpG : Nat := 0x3f
def pool6G : List Nat := [22063651494165]
def xsM : List Nat := roots_x1_0_x4_1_x5_0.map (· &&& dom_x1_0_x4_1_x5_0)
def goalM : Nat := goal_all &&& dom_x1_0_x4_1_x5_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xfb501748
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x3300000000000000303000000000000022220000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x243
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 10
  | _ => 0
def stateM : Nat → Nat
  | 3 => 0x3ff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x30000000000000000c0000000000000003
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x3a000000000000002d0000000000000017
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 3 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 3 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 3 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 3 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 3 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x3) :: stateWiresD n (ids >>> 2)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x3) :: stateWiresS n (ids >>> 2)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x1_0_x4_1_x5_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x1_0_x4_1_x5_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x1_0_x4_1_x5_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x1_0_x4_1_x5_0 goalM u ys) : RunD dom_x1_0_x4_1_x5_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x1_0_x4_1_x5_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool := scr dom_x1_0_x4_1_x5_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x1_0_x4_1_x5_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x1_0_x4_1_x5_0 roots_x1_0_x4_1_x5_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x1_0_x4_1_x5_0 goal_all := by
    have h0 : isConstB dom_x1_0_x4_1_x5_0 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x1_0_x4_1_x5_0
theorem low_x1_0_x4_1_x5_0 : Lower dom_x1_0_x4_1_x5_0 roots_x1_0_x4_1_x5_0 goal_all 4 := S_x1_0_x4_1_x5_0.noCircuit

theorem low_x1_0_x4_1 : Lower dom_x1_0_x4_1 roots_x1_0_x4_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3333000000000000, 17, 49)] (by decide +kernel) (by decide +kernel) low_x1_0_x4_1_x5_0

namespace S_x0_0_x4_1_x5_0
def pairsG : List (Nat × Nat) := [(18, 22), (18, 26), (20, 22), (20, 28), (24, 26), (24, 28)]
def r1sG : List Nat := [18, 18, 20, 20, 24, 24]
def r2sG : List Nat := [22, 26, 22, 28, 26, 28]
def mpG : Nat := 0x3f
def pool6G : List Nat := [22067946461718]
def xsM : List Nat := roots_x0_0_x4_1_x5_0.map (· &&& dom_x0_0_x4_1_x5_0)
def goalM : Nat := goal_all &&& dom_x0_0_x4_1_x5_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xa1e221b5
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x5500000000000000505000000000000044440000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x243
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 10
  | _ => 0
def stateM : Nat → Nat
  | 3 => 0x3ff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x30000000000000000c0000000000000003
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x3a000000000000002d0000000000000017
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 3 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 3 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 3 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 3 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 3 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x3) :: stateWiresD n (ids >>> 2)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x3) :: stateWiresS n (ids >>> 2)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x0_0_x4_1_x5_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x0_0_x4_1_x5_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x0_0_x4_1_x5_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x0_0_x4_1_x5_0 goalM u ys) : RunD dom_x0_0_x4_1_x5_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x0_0_x4_1_x5_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool := scr dom_x0_0_x4_1_x5_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x0_0_x4_1_x5_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x0_0_x4_1_x5_0 roots_x0_0_x4_1_x5_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x0_0_x4_1_x5_0 goal_all := by
    have h0 : isConstB dom_x0_0_x4_1_x5_0 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x0_0_x4_1_x5_0
theorem low_x0_0_x4_1_x5_0 : Lower dom_x0_0_x4_1_x5_0 roots_x0_0_x4_1_x5_0 goal_all 4 := S_x0_0_x4_1_x5_0.noCircuit

theorem low_x4_1_x5_0 : Lower dom_x4_1_x5_0 roots_x4_1_x5_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa0000, 20, 21)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_1_x5_0

namespace S_x0_0_x4_1_x5_1
def pairsG : List (Nat × Nat) := [(50, 54), (50, 58), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [50, 50, 52, 52, 56, 56]
def r2sG : List Nat := [54, 58, 54, 60, 58, 60]
def mpG : Nat := 0x3f
def pool6G : List Nat := [57390296480310]
def xsM : List Nat := roots_x0_0_x4_1_x5_1.map (· &&& dom_x0_0_x4_1_x5_1)
def goalM : Nat := goal_all &&& dom_x0_0_x4_1_x5_1
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x7228e998
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x550000000000000050500000000000004444000000000000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x243
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 10
  | _ => 0
def stateM : Nat → Nat
  | 3 => 0x3ff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x30000000000000000c0000000000000003
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x3a000000000000002d0000000000000017
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 3 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 3 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 3 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 3 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 3 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x3) :: stateWiresD n (ids >>> 2)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x3) :: stateWiresS n (ids >>> 2)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x0_0_x4_1_x5_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x0_0_x4_1_x5_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x0_0_x4_1_x5_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x0_0_x4_1_x5_1 goalM u ys) : RunD dom_x0_0_x4_1_x5_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x0_0_x4_1_x5_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool := scr dom_x0_0_x4_1_x5_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x0_0_x4_1_x5_1 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x0_0_x4_1_x5_1 roots_x0_0_x4_1_x5_1 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x0_0_x4_1_x5_1 goal_all := by
    have h0 : isConstB dom_x0_0_x4_1_x5_1 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x0_0_x4_1_x5_1
theorem low_x0_0_x4_1_x5_1 : Lower dom_x0_0_x4_1_x5_1 roots_x0_0_x4_1_x5_1 goal_all 4 := S_x0_0_x4_1_x5_1.noCircuit

theorem low_x4_1_x5_1 : Lower dom_x4_1_x5_1 roots_x4_1_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa000000000000, 48, 49)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_1_x5_1

namespace S_x4_1
def pairsG : List (Nat × Nat) := [(17, 21), (17, 25), (17, 49), (18, 22), (18, 26), (19, 23), (19, 27), (19, 51), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [17, 17, 17, 18, 18, 19, 19, 19, 20, 20, 20, 24, 24, 24, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [21, 25, 49, 22, 26, 23, 27, 51, 21, 22, 28, 25, 26, 28, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0xffffff
def pool6G : List Nat := [57257051100693, 61796309865756, 61655129789978, 57257150388758, 57390294374934]
def xsM : List Nat := roots_x4_1.map (· &&& dom_x4_1)
def goalM : Nat := goal_all &&& dom_x4_1
def NN : Nat → Nat
  | 5 => 3
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xaf970ecb963ff32842ebc3f7
  | 6, 0, 0 => 0x6eb47690
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xff000000ff0000fff00000fff00000f0f00000f0f00000ffff000000000000ff000000ff000000cccc0000cccc0000aaaa0000aaaa00000f0f00000f0f0000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x4a8f599d45846885
  | 6, 0, 0 => 0x47515
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 22
  | 6 => 19
  | _ => 0
def stateM : Nat → Nat
  | 5 => 0x3fffff
  | 6 => 0x7ffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x1fc7ff0000000000fc3f0000000000001c07000000000000ffc0000000000000e0380000000000000380f800000000000000e70000000000e3f8ff
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0xdc3ad0000000000ff3f7b00000000009d27290000000000ffc0840000000000f23c5200000000004b92f8000000000024c9e7000000000062d8d6
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 8 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 8 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 8 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 8 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 8 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x7) :: stateWiresD n (ids >>> 3)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x7) :: stateWiresS n (ids >>> 3)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x1_0_x4_1 roots_x1_0_x4_1 5 s ws hint
  | 1 => checkCutEntry dom_x0_0_x4_1_x5_0 roots_x0_0_x4_1_x5_0 4 s ws hint
  | 2 => checkCutEntry dom_x4_1_x5_0 roots_x4_1_x5_0 5 s ws hint
  | 3 => checkCutEntry dom_x4_1_x5_1 roots_x4_1_x5_1 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x4_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1_x5_1 _ hc
  · contradiction
def p0Subs : List Nat := [2, 0, 1, 3]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x4_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq, Bool.or_eq_true] at h; rcases h with h1 | h0
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2
  · obtain ⟨k, _, hk⟩ := List.any_eq_true.1 h0; exact checkCutByIdx_sound hk
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x4_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x4_1 goalM u ys) : RunD dom_x4_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x4_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool := scr dom_x4_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_x4_1 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x4_1 roots_x4_1 goal_all 7 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x4_1 goal_all := by
    have h0 : isConstB dom_x4_1 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x4_1
theorem low_x4_1 : Lower dom_x4_1 roots_x4_1 goal_all 7 := S_x4_1.noCircuit

namespace S_x0_1_x2_0_x4_0
def pairsG : List (Nat × Nat) := [(3, 11), (3, 35), (9, 11), (9, 41), (33, 35), (33, 41)]
def r1sG : List Nat := [3, 3, 9, 9, 33, 33]
def r2sG : List Nat := [11, 35, 11, 41, 35, 41]
def mpG : Nat := 0x3f
def pool6G : List Nat := [9909045895947]
def xsM : List Nat := roots_x0_1_x2_0_x4_0.map (· &&& dom_x0_1_x2_0_x4_0)
def goalM : Nat := goal_all &&& dom_x0_1_x2_0_x4_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x46f86fb7
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xa0a0000000000000a0000000a000000080800000808
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x243
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 10
  | _ => 0
def stateM : Nat → Nat
  | 3 => 0x3ff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x30000000000000000c0000000000000003
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x3a000000000000002d0000000000000017
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 3 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 3 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 3 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 3 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 3 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x3) :: stateWiresD n (ids >>> 2)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x3) :: stateWiresS n (ids >>> 2)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x0_1_x2_0_x4_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x0_1_x2_0_x4_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x0_1_x2_0_x4_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x0_1_x2_0_x4_0 goalM u ys) : RunD dom_x0_1_x2_0_x4_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x0_1_x2_0_x4_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool := scr dom_x0_1_x2_0_x4_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x0_1_x2_0_x4_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x0_1_x2_0_x4_0 roots_x0_1_x2_0_x4_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x0_1_x2_0_x4_0 goal_all := by
    have h0 : isConstB dom_x0_1_x2_0_x4_0 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x0_1_x2_0_x4_0
theorem low_x0_1_x2_0_x4_0 : Lower dom_x0_1_x2_0_x4_0 roots_x0_1_x2_0_x4_0 goal_all 4 := S_x0_1_x2_0_x4_0.noCircuit

theorem low_x2_0_x4_0 : Lower dom_x2_0_x4_0 roots_x2_0_x4_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa0a00000a0a, 34, 35)] (by decide +kernel) (by decide +kernel) low_x0_1_x2_0_x4_0

namespace S_x0_1_x1_0_x2_0
def pairsG : List (Nat × Nat) := [(9, 25), (9, 41), (17, 25), (17, 49), (33, 41), (33, 49)]
def r1sG : List Nat := [9, 9, 17, 17, 33, 33]
def r2sG : List Nat := [25, 41, 25, 49, 41, 49]
def mpG : Nat := 0x3f
def pool6G : List Nat := [18730909247769]
def xsM : List Nat := roots_x0_1_x1_0_x2_0.map (· &&& dom_x0_1_x1_0_x2_0)
def goalM : Nat := goal_all &&& dom_x0_1_x1_0_x2_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xe9d5d613
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x20202020000000002020000020200000200020002000200
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x243
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 10
  | _ => 0
def stateM : Nat → Nat
  | 3 => 0x3ff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x30000000000000000c0000000000000003
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x3a000000000000002d0000000000000017
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 3 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 3 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 3 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 3 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 3 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x3) :: stateWiresD n (ids >>> 2)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x3) :: stateWiresS n (ids >>> 2)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x0_1_x1_0_x2_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x0_1_x1_0_x2_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x0_1_x1_0_x2_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x0_1_x1_0_x2_0 goalM u ys) : RunD dom_x0_1_x1_0_x2_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x0_1_x1_0_x2_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool := scr dom_x0_1_x1_0_x2_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x0_1_x1_0_x2_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x0_1_x1_0_x2_0 roots_x0_1_x1_0_x2_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x0_1_x1_0_x2_0 goal_all := by
    have h0 : isConstB dom_x0_1_x1_0_x2_0 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x0_1_x1_0_x2_0
theorem low_x0_1_x1_0_x2_0 : Lower dom_x0_1_x1_0_x2_0 roots_x0_1_x1_0_x2_0 goal_all 4 := S_x0_1_x1_0_x2_0.noCircuit

theorem low_x0_1_x1_0 : Lower dom_x0_1_x1_0 roots_x0_1_x1_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x2020202020202020, 1, 5)] (by decide +kernel) (by decide +kernel) low_x0_1_x1_0_x2_0

theorem low_x0_1 : Lower dom_x0_1 roots_x0_1 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x8888888888888888, 9, 11)] (by decide +kernel) (by decide +kernel) low_x0_1_x1_0

theorem low_x0_1_x2_0 : Lower dom_x0_1_x2_0 roots_x0_1_x2_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x808080808080808, 9, 11)] (by decide +kernel) (by decide +kernel) low_x0_1_x1_0_x2_0

namespace S_x1_0_x5_1
def pairsG : List (Nat × Nat) := [(33, 37), (33, 41), (33, 49), (36, 37), (40, 41), (44, 45), (44, 60), (48, 49), (52, 53), (52, 60), (56, 57), (56, 60)]
def r1sG : List Nat := [33, 33, 33, 36, 40, 44, 44, 48, 52, 52, 56, 56]
def r2sG : List Nat := [37, 41, 49, 37, 41, 45, 60, 49, 53, 60, 57, 60]
def mpG : Nat := 0xfff
def pool6G : List Nat := [48521121902889, 48521189009701, 57317080704305, 57317282031909]
def xsM : List Nat := roots_x1_0_x5_1.map (· &&& dom_x1_0_x5_1)
def goalM : Nat := goal_all &&& dom_x1_0_x5_1
def NN : Nat → Nat
  | 4 => 5
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xdaa29e0ed9246cde51b2e97e404f366434576818
  | 5, 0, 0 => 0x404f3664
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x3333000000000033003300000000030303030000000011111111000000003333000000000000330033000000000030303030000000002222222200000000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x646468544474688468c4
  | 5, 0, 0 => 0x6884
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 16
  | 5 => 16
  | _ => 0
def stateM : Nat → Nat
  | 4 => 0xffff
  | 5 => 0xffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x7f000000000000038f0000000000000c970000000000000ff80000000000000f800000000000000c7000000000000003680000000000000007
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x3b000000000000018d00000000000004960000000000000a400000000000000fc40000000000000e720000000000000b6900000000000005bf
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 8 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 8 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 8 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 8 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 8 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x7) :: stateWiresD n (ids >>> 3)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x7) :: stateWiresS n (ids >>> 3)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 4 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x1_0_x5_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x1_0_x5_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x1_0_x5_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x1_0_x5_1 goalM u ys) : RunD dom_x1_0_x5_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x1_0_x5_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 5) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool := scr dom_x1_0_x5_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 3 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_x1_0_x5_1 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x1_0_x5_1 roots_x1_0_x5_1 goal_all 6 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x1_0_x5_1 goal_all := by
    have h0 : isConstB dom_x1_0_x5_1 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x1_0_x5_1
theorem low_x1_0_x5_1 : Lower dom_x1_0_x5_1 roots_x1_0_x5_1 goal_all 6 := S_x1_0_x5_1.noCircuit

namespace S_x1_0_x3_1_x5_0
def pairsG : List (Nat × Nat) := [(9, 13), (9, 25), (12, 13), (12, 28), (24, 25), (24, 28)]
def r1sG : List Nat := [9, 9, 12, 12, 24, 24]
def r2sG : List Nat := [13, 25, 13, 28, 25, 28]
def mpG : Nat := 0x3f
def pool6G : List Nat := [13233198733581]
def xsM : List Nat := roots_x1_0_x3_1_x5_0.map (· &&& dom_x1_0_x3_1_x5_0)
def goalM : Nat := goal_all &&& dom_x1_0_x3_1_x5_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xa3e95fe9
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x3300000000000000300030000000000022002200
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x243
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 10
  | _ => 0
def stateM : Nat → Nat
  | 3 => 0x3ff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x30000000000000000c0000000000000003
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x3a000000000000002d0000000000000017
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 3 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 3 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 3 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 3 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 3 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x3) :: stateWiresD n (ids >>> 2)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x3) :: stateWiresS n (ids >>> 2)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x1_0_x3_1_x5_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x1_0_x3_1_x5_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x1_0_x3_1_x5_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x1_0_x3_1_x5_0 goalM u ys) : RunD dom_x1_0_x3_1_x5_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x1_0_x3_1_x5_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool := scr dom_x1_0_x3_1_x5_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x1_0_x3_1_x5_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x1_0_x3_1_x5_0 roots_x1_0_x3_1_x5_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x1_0_x3_1_x5_0 goal_all := by
    have h0 : isConstB dom_x1_0_x3_1_x5_0 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x1_0_x3_1_x5_0
theorem low_x1_0_x3_1_x5_0 : Lower dom_x1_0_x3_1_x5_0 roots_x1_0_x3_1_x5_0 goal_all 4 := S_x1_0_x3_1_x5_0.noCircuit

theorem low_x1_0_x5_0 : Lower dom_x1_0_x5_0 roots_x1_0_x5_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x33003300, 17, 25)] (by decide +kernel) (by decide +kernel) low_x1_0_x3_1_x5_0

theorem low_x1_0_x2_0 : Lower dom_x1_0_x2_0 roots_x1_0_x2_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x202020202020202, 24, 25)] (by decide +kernel) (by decide +kernel) low_x0_1_x1_0_x2_0

theorem low_x1_0_x3_1 : Lower dom_x1_0_x3_1 roots_x1_0_x3_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3300330000000000, 9, 41)] (by decide +kernel) (by decide +kernel) low_x1_0_x3_1_x5_0

namespace S_x1_0
def pairsG : List (Nat × Nat) := [(1, 5), (4, 5), (9, 13), (9, 25), (9, 41), (12, 13), (12, 28), (17, 21), (17, 25), (17, 49), (20, 21), (20, 28), (24, 25), (24, 28), (33, 37), (33, 41), (33, 49), (36, 37), (40, 41), (44, 45), (44, 60), (48, 49), (52, 53), (52, 60), (56, 57), (56, 60)]
def r1sG : List Nat := [1, 4, 9, 9, 9, 12, 12, 17, 17, 17, 20, 20, 24, 24, 33, 33, 33, 36, 40, 44, 44, 48, 52, 52, 56, 56]
def r2sG : List Nat := [5, 5, 13, 25, 41, 13, 28, 21, 25, 49, 21, 28, 25, 28, 37, 41, 49, 37, 41, 45, 60, 49, 53, 60, 57, 60]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [48418107693317, 18730909247769, 48521119794473, 61796276307228, 57317078598961, 48418109070341, 61761782351132, 57214201568261, 48452467431685, 48521186908421]
def xsM : List Nat := roots_x1_0.map (· &&& dom_x1_0)
def goalM : Nat := goal_all &&& dom_x1_0
def NN : Nat → Nat
  | 5 => 5
  | 6 => 8
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xf71871dff68c5e80af7648c1aeea356244417414
  | 6, 0, 0 => 0xe3c1d732e335c3d3dda09adcd3b212568cff9f0a788d0285755479d430ead967
  | 7, 0, 0 => 0x653667d8
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x3300000033000000222222220000000022220000222200002200220022002200222222222222222203030303030303033300330033003300000033330000333333333333000000003333000033330000303030303030303011111111111111110033003300330033
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x462155468755432105438705428055
  | 6, 0, 0 => 0x436215043687543628a64362896436c286046285503628b50432805
  | 7, 0, 0 => 0x436285
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 24
  | 6 => 28
  | 7 => 24
  | _ => 0
def stateM : Nat → Nat
  | 5 => 0xffffff
  | 6 => 0xfffffff
  | 7 => 0xffffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x3003000000000000001c0000000000000000380000000000000001c000000000001c39d000000000325f39d00000000031c307c00000000001fc07f0000000003ffc0000000000003e03f800000000000da0c620000000003fe3c620000000000e3cf83
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x390394800000000016fc210000000000161178800000000010c913c00000000016fd7bf000000000125931800000000039cb97c00000000000ec0370000000003ffc2100000000003f13fc80000000002da6ce700000000029028400000000000634683
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 13 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 13 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 13 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 13 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 13 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0xf) :: stateWiresD n (ids >>> 4)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0xf) :: stateWiresS n (ids >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 4 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 5 => 8
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xfdda1512f6b9c127f62dadc892a540658b84ec7a4b03174743e2c35c1be96057
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x8400000000210000000018400000000e10000000038400000000a100000000284000000002100
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 4 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x1_0_x5_1 roots_x1_0_x5_1 6 s ws hint
  | 1 => checkCutEntry dom_x0_1_x1_0_x2_0 roots_x0_1_x1_0_x2_0 4 s ws hint
  | 2 => checkCutEntry dom_x0_1_x1_0 roots_x0_1_x1_0 5 s ws hint
  | 3 => checkCutEntry dom_x1_0_x5_0 roots_x1_0_x5_0 5 s ws hint
  | 4 => checkCutEntry dom_x1_0_x3_1_x5_0 roots_x1_0_x3_1_x5_0 4 s ws hint
  | 5 => checkCutEntry dom_x1_0_x4_1_x5_0 roots_x1_0_x4_1_x5_0 4 s ws hint
  | 6 => checkCutEntry dom_x1_0_x2_0 roots_x1_0_x2_0 5 s ws hint
  | 7 => checkCutEntry dom_x1_0_x3_1 roots_x1_0_x3_1 5 s ws hint
  | 8 => checkCutEntry dom_x1_0_x4_1 roots_x1_0_x4_1 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x1_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_1_x1_0_x2_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_1_x1_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x3_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x4_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x2_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x4_1 _ hc
  · contradiction
def p0Subs : List Nat := [0, 2, 6, 7, 1, 8, 3, 4, 5]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x1_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq, Bool.or_eq_true] at h; rcases h with h1 | h0
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2
  · obtain ⟨k, _, hk⟩ := List.any_eq_true.1 h0; exact checkCutByIdx_sound hk
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x1_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x1_0 goalM u ys) : RunD dom_x1_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x1_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 7) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
  · exact fun i hi => z7 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool := scr dom_x1_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_x1_0 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x1_0 roots_x1_0 goal_all 8 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x1_0 goal_all := by
    have h0 : isConstB dom_x1_0 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x1_0
theorem low_x1_0 : Lower dom_x1_0 roots_x1_0 goal_all 8 := S_x1_0.noCircuit

theorem low_x0_0_x5_0 : Lower dom_x0_0_x5_0 roots_x0_0_x5_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x55550000, 12, 28)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_1_x5_0

theorem low_x3_1_x5_0 : Lower dom_x3_1_x5_0 roots_x3_1_x5_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc00, 8, 10)] (by decide +kernel) (by decide +kernel) low_x1_0_x3_1_x5_0

namespace S_x5_0
def pairsG : List (Nat × Nat) := [(1, 5), (2, 6), (2, 10), (3, 7), (3, 11), (4, 5), (4, 6), (8, 10), (9, 11), (9, 13), (9, 25), (12, 13), (12, 14), (12, 28), (17, 21), (17, 25), (18, 22), (18, 26), (19, 23), (19, 27), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28)]
def r1sG : List Nat := [1, 2, 2, 3, 3, 4, 4, 8, 9, 9, 9, 12, 12, 12, 17, 17, 18, 18, 19, 19, 20, 20, 20, 24, 24, 24]
def r2sG : List Nat := [5, 6, 10, 7, 11, 5, 6, 10, 11, 13, 25, 13, 14, 28, 21, 25, 22, 26, 23, 27, 21, 22, 28, 25, 26, 28]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [13233198733573, 26474497836316, 20942412186886, 20942665026054, 20942597916170]
def xsM : List Nat := roots_x5_0.map (· &&& dom_x5_0)
def goalM : Nat := goal_all &&& dom_x5_0
def NN : Nat → Nat
  | 5 => 1
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x599be9b2
  | 6, 0, 0 => 0x1f16380d
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xf0f0f0f000000000ffff000000000000ff00ff0000000000cccccccc00000000aaaaaaaa000000000f0f0f0f
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x46885
  | 6, 0, 0 => 0x47515
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 19
  | 6 => 19
  | _ => 0
def stateM : Nat → Nat
  | 5 => 0x7ffff
  | 6 => 0x7ffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x7038600000000003ffc0000000000003803f8000000000000f001e00000000000cc71900000000038fc79f
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x2757a6b0000000003ffe4000000000003cabf9400000000012f11de00000000009ccf3900000000018a8594
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 6 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 6 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 6 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 6 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 6 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x7) :: stateWiresD n (ids >>> 3)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x7) :: stateWiresS n (ids >>> 3)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x0_0_x5_0 roots_x0_0_x5_0 5 s ws hint
  | 1 => checkCutEntry dom_x1_0_x5_0 roots_x1_0_x5_0 5 s ws hint
  | 2 => checkCutEntry dom_x3_1_x5_0 roots_x3_1_x5_0 5 s ws hint
  | 3 => checkCutEntry dom_x4_1_x5_0 roots_x4_1_x5_0 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x5_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1_x5_0 _ hc
  · contradiction
def p0Subs : List Nat := [1, 0, 2, 3]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x5_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq, Bool.or_eq_true] at h; rcases h with h1 | h0
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2
  · obtain ⟨k, _, hk⟩ := List.any_eq_true.1 h0; exact checkCutByIdx_sound hk
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x5_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x5_0 goalM u ys) : RunD dom_x5_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x5_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool := scr dom_x5_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_x5_0 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x5_0 roots_x5_0 goal_all 7 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x5_0 goal_all := by
    have h0 : isConstB dom_x5_0 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x5_0
theorem low_x5_0 : Lower dom_x5_0 roots_x5_0 goal_all 7 := S_x5_0.noCircuit

namespace S_x2_0_x4_0_x5_1
def pairsG : List (Nat × Nat) := [(33, 35), (33, 41), (34, 35), (34, 42), (40, 41), (40, 42)]
def r1sG : List Nat := [33, 33, 34, 34, 40, 40]
def r2sG : List Nat := [35, 41, 35, 42, 41, 42]
def mpG : Nat := 0x3f
def pool6G : List Nat := [37525803116835]
def xsM : List Nat := roots_x2_0_x4_0_x5_1.map (· &&& dom_x2_0_x4_0_x5_1)
def goalM : Nat := goal_all &&& dom_x2_0_x4_0_x5_1
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x2977382d
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xf000000000000000c0c0000000000000a0a00000000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x243
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 10
  | _ => 0
def stateM : Nat → Nat
  | 3 => 0x3ff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x30000000000000000c0000000000000003
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x3a000000000000002d0000000000000017
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 3 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 3 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 3 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 3 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 3 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x3) :: stateWiresD n (ids >>> 2)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x3) :: stateWiresS n (ids >>> 2)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x2_0_x4_0_x5_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x2_0_x4_0_x5_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x2_0_x4_0_x5_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x2_0_x4_0_x5_1 goalM u ys) : RunD dom_x2_0_x4_0_x5_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x2_0_x4_0_x5_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool := scr dom_x2_0_x4_0_x5_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x2_0_x4_0_x5_1 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x2_0_x4_0_x5_1 roots_x2_0_x4_0_x5_1 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x2_0_x4_0_x5_1 goal_all := by
    have h0 : isConstB dom_x2_0_x4_0_x5_1 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x2_0_x4_0_x5_1
theorem low_x2_0_x4_0_x5_1 : Lower dom_x2_0_x4_0_x5_1 roots_x2_0_x4_0_x5_1 goal_all 4 := S_x2_0_x4_0_x5_1.noCircuit

theorem low_x2_0_x5_1 : Lower dom_x2_0_x5_1 roots_x2_0_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f000000000000, 33, 49)] (by decide +kernel) (by decide +kernel) low_x2_0_x4_0_x5_1

namespace S_x2_0
def pairsG : List (Nat × Nat) := [(2, 10), (3, 11), (3, 35), (8, 10), (9, 11), (9, 25), (9, 41), (17, 25), (17, 49), (18, 26), (19, 27), (19, 51), (24, 25), (24, 26), (33, 35), (33, 41), (33, 49), (34, 35), (34, 42), (40, 41), (40, 42), (48, 49), (50, 51), (50, 58), (56, 57), (56, 58)]
def r1sG : List Nat := [2, 3, 3, 8, 9, 9, 9, 17, 17, 18, 19, 19, 24, 24, 33, 33, 33, 34, 34, 40, 40, 48, 50, 50, 56, 56]
def r2sG : List Nat := [10, 11, 35, 10, 11, 25, 41, 25, 49, 26, 27, 51, 25, 26, 35, 41, 49, 35, 42, 41, 42, 49, 51, 58, 57, 58]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [20929931977482, 61787955864330, 61655097608729, 36365641779747, 20929932503321]
def xsM : List Nat := roots_x2_0.map (· &&& dom_x2_0)
def goalM : Nat := goal_all &&& dom_x2_0
def NN : Nat → Nat
  | 5 => 1
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x9113e543
  | 6, 0, 0 => 0xf0260ba
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xf000f000f000f000f0f0f0f000000000f0f00000f0f00000c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a000f000f000f000f
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x46885
  | 6, 0, 0 => 0x47515
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 19
  | 6 => 19
  | _ => 0
def stateM : Nat → Nat
  | 5 => 0x7ffff
  | 6 => 0x7ffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x31830780000000003ffc0000000000003e03f800000000000c60e07000000000001cdf60000000000e7cf87
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x39cb6fb0000000003ffc9440000000003e13fa00000000002d66e1f00000000016bddf60000000000634904
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 6 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 6 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 6 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 6 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 6 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x7) :: stateWiresD n (ids >>> 3)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x7) :: stateWiresS n (ids >>> 3)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x0_1_x2_0 roots_x0_1_x2_0 5 s ws hint
  | 1 => checkCutEntry dom_x1_0_x2_0 roots_x1_0_x2_0 5 s ws hint
  | 2 => checkCutEntry dom_x2_0_x4_0 roots_x2_0_x4_0 5 s ws hint
  | 3 => checkCutEntry dom_x2_0_x5_1 roots_x2_0_x5_1 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x2_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_1_x2_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x2_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x5_1 _ hc
  · contradiction
def p0Subs : List Nat := [0, 1, 2, 3]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x2_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq, Bool.or_eq_true] at h; rcases h with h1 | h0
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2
  · obtain ⟨k, _, hk⟩ := List.any_eq_true.1 h0; exact checkCutByIdx_sound hk
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x2_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x2_0 goalM u ys) : RunD dom_x2_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x2_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool := scr dom_x2_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_x2_0 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x2_0 roots_x2_0 goal_all 7 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x2_0 goal_all := by
    have h0 : isConstB dom_x2_0 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x2_0
theorem low_x2_0 : Lower dom_x2_0 roots_x2_0 goal_all 7 := S_x2_0.noCircuit

theorem low_x0_1_x4_0 : Lower dom_x0_1_x4_0 roots_x0_1_x4_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa0a00000a0a0, 1, 5)] (by decide +kernel) (by decide +kernel) low_x0_1_x2_0_x4_0

namespace S_x3_0_x4_0_x5_1
def pairsG : List (Nat × Nat) := [(33, 35), (33, 37), (34, 35), (34, 38), (36, 37), (36, 38)]
def r1sG : List Nat := [33, 33, 34, 34, 36, 36]
def r2sG : List Nat := [35, 37, 35, 38, 37, 38]
def mpG : Nat := 0x3f
def pool6G : List Nat := [37525735744803]
def xsM : List Nat := roots_x3_0_x4_0_x5_1.map (· &&& dom_x3_0_x4_0_x5_1)
def goalM : Nat := goal_all &&& dom_x3_0_x4_0_x5_1
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xd942fcfb
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xf000000000000000cc00000000000000aa00000000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x243
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 10
  | _ => 0
def stateM : Nat → Nat
  | 3 => 0x3ff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x30000000000000000c0000000000000003
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x3a000000000000002d0000000000000017
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 3 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 3 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 3 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 3 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 3 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x3) :: stateWiresD n (ids >>> 2)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x3) :: stateWiresS n (ids >>> 2)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x3_0_x4_0_x5_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x3_0_x4_0_x5_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x3_0_x4_0_x5_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x3_0_x4_0_x5_1 goalM u ys) : RunD dom_x3_0_x4_0_x5_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x3_0_x4_0_x5_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool := scr dom_x3_0_x4_0_x5_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x3_0_x4_0_x5_1 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x3_0_x4_0_x5_1 roots_x3_0_x4_0_x5_1 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x3_0_x4_0_x5_1 goal_all := by
    have h0 : isConstB dom_x3_0_x4_0_x5_1 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x3_0_x4_0_x5_1
theorem low_x3_0_x4_0_x5_1 : Lower dom_x3_0_x4_0_x5_1 roots_x3_0_x4_0_x5_1 goal_all 4 := S_x3_0_x4_0_x5_1.noCircuit

theorem low_x3_0_x5_1 : Lower dom_x3_0_x5_1 roots_x3_0_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000000000, 33, 49)] (by decide +kernel) (by decide +kernel) low_x3_0_x4_0_x5_1

theorem low_x0_0_x5_1 : Lower dom_x0_0_x5_1 roots_x0_0_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555000000000000, 44, 60)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_1_x5_1

theorem low_x4_0_x5_1 : Lower dom_x4_0_x5_1 roots_x4_0_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f000000000, 33, 37)] (by decide +kernel) (by decide +kernel) low_x2_0_x4_0_x5_1

namespace S_x5_1
def pairsG : List (Nat × Nat) := [(33, 35), (33, 37), (33, 41), (33, 49), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (40, 41), (40, 42), (44, 45), (44, 46), (44, 60), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [33, 33, 33, 33, 34, 34, 34, 36, 36, 40, 40, 44, 44, 44, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [35, 37, 41, 49, 35, 38, 42, 37, 38, 41, 42, 45, 46, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0xffffff
def pool6G : List Nat := [61715127215409, 48521121899817, 55118056006947, 57317080704305, 55118258776614, 48521189009701, 55118190945827]
def xsM : List Nat := roots_x5_1.map (· &&& dom_x5_1)
def goalM : Nat := goal_all &&& dom_x5_1
def NN : Nat → Nat
  | 5 => 3
  | 6 => 7
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xd129852f9679e0100854d8be
  | 6, 0, 0 => 0xc5ee96e7b433ea05a716f0c18ec3435845025efc3bd8c2aa009e3c06
  | 7, 0, 0 => 0xbe37fa2f
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xffff00000000fff0fff000000000ffaaffaa00000000fafafafa00000000aaaaaaaa00000000f0f0f0f00000000000ff00ff00000000ffff000000000000ff00ff0000000000cccccccc0000000055555555000000000f0f0f0f00000000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x427055462155432105
  | 6, 0, 0 => 0x43621503627b5493627604627554a3627643862760432705
  | 7, 0, 0 => 0x436275
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 24
  | 6 => 28
  | 7 => 24
  | _ => 0
def stateM : Nat → Nat
  | 5 => 0xffffff
  | 6 => 0xfffffff
  | 7 => 0xffffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x3fff0000000000fc3f800000000000e03e0f00000000001c398f000000000000000f00000000001c398000000000001fc1ff0000000000ffc0000000000000e03e0000000000000380700000000000fffff00000000000e3c67f
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x1ff70000000000ff3fe60000000000f6fedf0000000000bdfbbf000000000024ca9f00000000009d39a200000000000dc1bb0000000000ffe0080000000000f23e4400000000004b95710000000000db3560000000000062c65d
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 12 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 12 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 12 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 12 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 12 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0xf) :: stateWiresD n (ids >>> 4)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0xf) :: stateWiresS n (ids >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 4 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 5 => 8
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xdbed3bd2cf2b795aca328ef0a4c1e84379885aa941067208169ce0f10656cce9
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x8400000000a10000000038400000000a100000000384000000006100000000184000000002100
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 4 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x1_0_x5_1 roots_x1_0_x5_1 6 s ws hint
  | 1 => checkCutEntry dom_x0_0_x4_1_x5_1 roots_x0_0_x4_1_x5_1 4 s ws hint
  | 2 => checkCutEntry dom_x0_0_x5_1 roots_x0_0_x5_1 5 s ws hint
  | 3 => checkCutEntry dom_x4_0_x5_1 roots_x4_0_x5_1 5 s ws hint
  | 4 => checkCutEntry dom_x2_0_x4_0_x5_1 roots_x2_0_x4_0_x5_1 4 s ws hint
  | 5 => checkCutEntry dom_x2_0_x5_1 roots_x2_0_x5_1 5 s ws hint
  | 6 => checkCutEntry dom_x3_0_x4_0_x5_1 roots_x3_0_x4_0_x5_1 4 s ws hint
  | 7 => checkCutEntry dom_x4_1_x5_1 roots_x4_1_x5_1 5 s ws hint
  | 8 => checkCutEntry dom_x3_0_x5_1 roots_x3_0_x5_1 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x5_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x4_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x4_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x5_1 _ hc
  · contradiction
def p0Subs : List Nat := [0, 2, 5, 3, 7, 8, 1, 4, 6]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x5_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq, Bool.or_eq_true] at h; rcases h with h1 | h0
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2
  · obtain ⟨k, _, hk⟩ := List.any_eq_true.1 h0; exact checkCutByIdx_sound hk
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x5_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x5_1 goalM u ys) : RunD dom_x5_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x5_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 7 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 7) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
  · exact fun i hi => z7 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool := scr dom_x5_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_x5_1 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x5_1 roots_x5_1 goal_all 8 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x5_1 goal_all := by
    have h0 : isConstB dom_x5_1 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x5_1
theorem low_x5_1 : Lower dom_x5_1 roots_x5_1 goal_all 8 := S_x5_1.noCircuit

theorem low_x3_0_x4_0 : Lower dom_x3_0_x4_0 roots_x3_0_x4_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff00000000, 3, 35)] (by decide +kernel) (by decide +kernel) low_x3_0_x4_0_x5_1

namespace S_x4_0
def pairsG : List (Nat × Nat) := [(1, 5), (2, 6), (2, 10), (3, 7), (3, 11), (3, 35), (4, 5), (4, 6), (8, 10), (9, 11), (9, 13), (9, 41), (12, 13), (12, 14), (33, 35), (33, 37), (33, 41), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (40, 41), (40, 42), (44, 45), (44, 46)]
def r1sG : List Nat := [1, 2, 2, 3, 3, 3, 4, 4, 8, 9, 9, 9, 12, 12, 33, 33, 33, 34, 34, 34, 36, 36, 40, 40, 44, 44]
def r2sG : List Nat := [5, 6, 10, 7, 11, 35, 5, 6, 10, 11, 13, 41, 13, 14, 35, 37, 41, 35, 38, 42, 37, 38, 41, 42, 45, 46]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [48391969244677, 9909045895946, 48391548175622, 37525867857187]
def xsM : List Nat := roots_x4_0.map (· &&& dom_x4_0)
def goalM : Nat := goal_all &&& dom_x4_0
def NN : Nat → Nat
  | 5 => 1
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x7bde9db2
  | 6, 0, 0 => 0x3b576e79
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xcccc0000cccc0000ffff000000000000ff000000ff000000f0f00000f0f00000aaaa0000aaaa0000333300003333
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x46885
  | 6, 0, 0 => 0x46a95
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 19
  | 6 => 19
  | _ => 0
def stateM : Nat → Nat
  | 5 => 0x7ffff
  | 6 => 0x7ffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0xe003e0000000003ffc0000000000003c03f0000000000033030c0000000000001ce390000000003f1ffc1
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x2ae63be0000000003ffc8200000000003c93f14000000000334b4cb000000000153de790000000001519c41
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 6 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 6 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 6 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 6 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 6 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x7) :: stateWiresD n (ids >>> 3)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x7) :: stateWiresS n (ids >>> 3)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x0_1_x4_0 roots_x0_1_x4_0 5 s ws hint
  | 1 => checkCutEntry dom_x2_0_x4_0 roots_x2_0_x4_0 5 s ws hint
  | 2 => checkCutEntry dom_x3_0_x4_0 roots_x3_0_x4_0 5 s ws hint
  | 3 => checkCutEntry dom_x4_0_x5_1 roots_x4_0_x5_1 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x4_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_1_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_0_x5_1 _ hc
  · contradiction
def p0Subs : List Nat := [0, 1, 2, 3]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x4_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq, Bool.or_eq_true] at h; rcases h with h1 | h0
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2
  · obtain ⟨k, _, hk⟩ := List.any_eq_true.1 h0; exact checkCutByIdx_sound hk
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x4_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x4_0 goalM u ys) : RunD dom_x4_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x4_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool := scr dom_x4_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_x4_0 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x4_0 roots_x4_0 goal_all 7 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x4_0 goal_all := by
    have h0 : isConstB dom_x4_0 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x4_0
theorem low_x4_0 : Lower dom_x4_0 roots_x4_0 goal_all 7 := S_x4_0.noCircuit

theorem low_x3_0 : Lower dom_x3_0 roots_x3_0 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000ff0000, 33, 49)] (by decide +kernel) (by decide +kernel) low_x3_0_x4_0

theorem low_x3_1 : Lower dom_x3_1 roots_x3_1 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc00cc00cc00, 8, 10)] (by decide +kernel) (by decide +kernel) low_x1_0_x3_1

namespace S_63
def pairsG : List (Nat × Nat) := [(1, 5), (2, 6), (2, 10), (3, 7), (3, 11), (3, 35), (4, 5), (4, 6), (8, 10), (9, 11), (9, 13), (9, 25), (9, 41), (12, 13), (12, 14), (12, 28), (17, 21), (17, 25), (17, 49), (18, 22), (18, 26), (19, 23), (19, 27), (19, 51), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28), (33, 35), (33, 37), (33, 41), (33, 49), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (40, 41), (40, 42), (44, 45), (44, 46), (44, 60), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 2, 2, 3, 3, 3, 4, 4, 8, 9, 9, 9, 9, 12, 12, 12, 17, 17, 17, 18, 18, 19, 19, 19, 20, 20, 20, 24, 24, 24, 33, 33, 33, 33, 34, 34, 34, 36, 36, 40, 40, 44, 44, 44, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [5, 6, 10, 7, 11, 35, 5, 6, 10, 11, 13, 25, 41, 13, 14, 28, 21, 25, 49, 22, 26, 23, 27, 51, 21, 22, 28, 25, 26, 28, 35, 37, 41, 49, 35, 38, 42, 37, 38, 41, 42, 45, 46, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x3fffffffffffff
def pool6G : List Nat := [36365641783601, 57390294370822, 36322859485737, 61612045894937, 55165434201610, 57257050179077, 57364140075292, 48418107693317, 36365641779747, 61796308878876, 48521119794473, 55165501311494, 48460671943942, 61655129785866, 48418108546053, 36322860407081, 57317078598961, 61762186577180, 20929931977482, 55118056195619, 20929932503321, 61655096691225, 61612046752793, 61761781368092, 48521186908421, 61612045894922, 48418109070341, 61796545791260, 61761782351132, 48460958074373, 48521086699013, 57214100506117, 61654996421145]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_all &&& dom_63
def NN : Nat → Nat
  | 4 => 3
  | 5 => 52
  | 6 => 381
  | 7 => 1010
  | 8 => 426
  | 9 => 34
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xaf6b5d7370736ecb654bd34c
  | 5, 0, 0 => 0xf1ce14c3f0af1e98eafa4c7fea37c7f0e9d96a65e66532dde5878319df102c71dee4ad51de61ae49d8c5d834d6e128bdd4186361cee2b3d6cc2a04ddca3842f5c7fda723c47af3d8c34281dac102695eb35da5aab087b0feae5530e4ab545013a91a82bfa886be48a4b6ebcfa32d95659731adb788f0cb7c83c2d5d283197457812ed6488018b8ce7fe4f69f7956b50777b99d5c6870d453647b434855742c114a8986dc2eeebf9c2c5eff60268ea30625fade8f205263b21c0673f21bcfb77d147922fe0f0bfe590951877f0361b21d
  | 6, 0, 0 => 0x32f9626032603d5830dfae1d2fe0464e2f83dcc72ed593102e298e272d2083942ccd5d412bedc5d12b9e1db02aa9d1532a5cb8c428d26f982859411427c12ca027ad6f24275b78492611cae921c3b6ed21944677208a8efc1f980b671f2276f01e2caa511e1fb9291daad4191c00c3301af1c7281a28862119754848191d239b18da50a118405eba182be3b617ba9f93173aac76170c4a3716a79a4d169c1b6e1654c0e914a34e531461118f13cd4d1813255dd61182c6e910687c870efd143c0ead6c1b0d891f440c9fc9bf0bd7d43b0af220a50ab1918c0a583cd109fa4f0908770ba607baa5d00792e9c204e26dec03f2125001e8a5df011eecaa0054689b
  | 6, 0, 1 => 0x55b4fa3755a3560155719a6d555ac60b54b154c55461d2e4532cafce532180925293f12b528a3159525eb23950b91342508cbf0e502473694e85d7fc4e5dc7684d79e0f24d7120b14d6e15d94c91a6524acdf15b4aa0de1a4a37c400497e74ef497e0663493bf4dc48893a7a479a82e84792684946a3d46645c3212d459177c3451a7cea4473e56943a3289f42c49e34428f99e1425cb8be4214311041437c423f1028813e3b64933d6089e83cc096733c2d61af3ae7efa03a9b85ae3a542b293a41d16f39166fb838e80d79373d468c36940fc535a33f9635823129351ea90434ab5128347c6e4634736aa63456339d33d936f53345727e3308ecde32fc7e7c
  | 6, 0, 2 => 0x81aacd8b8086a5c87f6419327e457b107e2bc4ef7d8dfd717ccb8c677c2cfebf7c18aa777b3832d67a5bc27979fd6c0379b4647778d48fe278c7d28f77fa924477a096e076a4611575fef8027537e3e274c75554746fb46d74297a2b7322a874729e117d71f2137671c5d73770886c186faa966a6e6536ae6d345f4e6be2dde26b437945687f97a8681bb18d6800f41367bb5db4679ee46f655cc4e464d8049762d4103062ce934a62a8d0aa623aced3619b4dce616c41bc5fb68be25f3c4d2a5e9075435e4903ac5dd174105d92b6175d536f4d5cb4d9595c4d44085bb97f915af05dc159df37c5591e1344590188015738c89656eb287f56b21c8455db3c83
  | 6, 0, 3 => 0xae167fd3ade9db15addc5f7daccd603eac269518ab25f132ab23472da76b4f4da4ff673ca4b2fd4aa4a10bd2a46ba2c5a38d50b3a206e277a0bb338ca0b6bddda0b4d6279e8ae2429df46db99d5cea1a9d13f6189cf1e9e29c9d873e9acaf6509a3dc1749a39e44a99c68c2f9974e37798f4193f977abc839730cef49726d5ed96ca69889667cf3d96053d6d95c54177957e070f94b168c994b018d3947f766c941e120c941965bf91ca4e638fab7dc78f758a308f2b5bc48f1022908ee6b95b8ead5bfe8d43006a8c3abc918c15e12b8a34f76c8930df6e87bc307387a8128b8755af5185d6445b859ab80e856d6097833bb76a82a16a9982435b52823172d8
  | 6, 0, 4 => 0xdb18e957dac6715bdabc9fa1d9a47bd8d7f54830d7cfa697d5acb028d5921e8bd42f64bed41e9489d2186bafd215ea13d19faa06cff14dd8cf55be21ce16313ccdb8af35cda92b94ccf04eb9ccd97be5cba49ca0cb8bc7facb11054ecb073168ca14e71bc8e34624c89b3aa8c84ba573c848c5bcc7cabec7c5d0f72dc24db932c1f018d1c15c545ac036effbbeaf6c7ebe794a80bdfa7ae7bdd5bfc6bdbbaaa5bd9abea3bbe46b30bbbc7503bb679313bb50a6b9bb251300ba04a7adb8a62ccab8336b67b759ca51b7564999b6ed774ab6c7071bb65b39aeb5af61c7b5a82bdcb4e03a77b4991bd1b428acc5b34e062eb1119119b0e5dcdeafda98c9ae57b51a
  | 6, 0, 5 => 0xffdcb913ff7db898fea48a30fe96ee08fe68200cfdbc4825fd7f2f11fb92b748f9dd11f3f90122dcf8fcbbeef7c3c39bf7746301f6c10a60f6649b78f652342df524d58ef4e65fcff478fda7f392bdb6f37b3e7bf29d61bdf2856546f23b759bf1f2b34ef1bfa95ef0d8e625f088a090efc03f07efb22faaee60c998ed289330ed2150faecf11c62ec9aa4e8ec410fe9ebc24527eb865a11eac1c60ee98ccc3de989b504e91c46ace9153832e872ec00e7b4a050e7455612e658d291e57e025ce55a7303e5250e9ce51701ade4c6ae8ce3cbdc13e3992013e312bec2e112f115df4f5b7edf3b142edd589125dc631357dbcf4ee0
  | 7, 0, 0 => 0x109959ad108dfb0010873aff107eac71107c28dc1073336b103915950f4449ac0f0a2ca10ed51c0e0ed4b88e0dba7f720db3e9320daeef0b0d37803a0cbf98d00c76b2fc0c3de4c00c3025590bb4968f0bb355150b50bf8d0b45d6cd0acc9fe20a9cd3050a8dac0c0a868e460a3643350a01adfb09e1d42509a8b188097f42550979a5d3093f465f090422d80895d5190889983b082a1dbb079816f407936aa70750f5920749dc2006dc1cba06d1977a0694c2350674bcee0620bd3c05e0f0500573298d056af0ba0567fa510544534b040aaf0b03f5a318036355ec02d338cd028a2778027dd2a4026aed28022760e6020343d90188bf7200966ccb00242408
  | 7, 0, 1 => 0x1fded0131fd910571fd503bc1fcef5c61fb8fff41fa9b9161f0910ea1ed2190f1e2957a11e28fef71d7fa8f01d714dfe1ca711891c9476741c9385c61c6686f61c1160c61c02e4e51b8f4bc21b5aa7ce1af080381ae554351ac66f0819b45c2418d23d5e18cdcd2718917f94182d0232181b10ba18054bf517e5a7ad17d58bc31769b970176707ad1747ce401736d9ea170095b5169ad4dc1578ae8c15736fd7150dfc8014d3ff0f149a4ea114353874140640e713b13c8e138bc72e1357233a13495b611332ca01129d837a128628ed126f0f311221b4591205328f1204e72a11f47fb211d20ecf11ac3450118defe21182c6e9116e72a11148cdc710d6ef02
  | 7, 0, 2 => 0x2f76da822f3679eb2ee197fb2ededa662ed106232ecaaba12e9f17e82e7b65df2e1f778a2ddc07642d9059d12d7eac952d3304032c2031b22c05dd8b2c002f4b2bfc8b3d2b77caf02b5e9cb32b1b09a12b0c54332adefa3b2ad3cf392ad101ba2ad04e812aafe6892a71985b2a410c032a20277c29d53e962968837429676491294551f02920d6ee28b7dffc289b69732850803028437ca227fa169d27edaeb527d27a5a27c003a927a2b1ad26c80b16267fe0ec264570c026144d3626099ed525b7586925836aef2543e48c246a0b8a2411b25923efb98523c4c6382308cf9f22edaba222ae156b2284b333219084bb21701c682164fee02161cccc20476526
  | 7, 0, 3 => 0x3df9cadc3dccbcab3d6a91643d5edcee3d51cce33d21d1683cf4fcd73cc117773c904c443c8a93293c153f903bd23dc43bc2caa43b6671ed3b1437703ae4477f3aca73853a75cc833a36b6f73a1fbb5339f6d3fc394afc15393fefff392320c838f9f1d038ad22a8382d8f77375cfd2436f1a5a3368845d53622fc1e35f050a6359128c13582312935772437353c599a35389f973532e67c34d6594234adc6723457b9423403b3df33eb7d5533df7b7b33b0f4e3338b14573388509232dd24d032d4864e3269602131f34f6831c94508317dda3a31747fcf314fc4ae3135af8d30a99e1430986860304cf6a4302f8f993020be7a3004a3e92fc216982fbca898
  | 7, 0, 4 => 0x4f004b644edbc49d4ed591294e4076434e1ca4aa4e10be834da171e74ce12a5a4ca0b7c64c9ed9d94c8d80f44c74d9df4c3ce0ae4c153af14bfbeabe4bc432324bb6a0f34baaa6664b7eba714b5012d74b3362094afc9a304a974fec4a50c249499f41ff496afadf4926b5104828eedb47a969a6479a42c34798997147623978471cacd1469151e1463a036a462698db45e12de845bd00e6459ded5345927097458feefb4561370c454de4cd44b0b53e44549336441369d343f8662a43f4158c43a4a4f9436b52c0433fa33f42f9159c42cfc30942b870d0417c5d42417ae7e741588a4440eb971d40ba3bb3405380cd404296163fad42e13f9ec7003e813650
  | 7, 0, 5 => 0x5fdec53c5fbb14d15fa624535f3c4a0f5f13a1b05ed0c0195e24e8325e1a51b35d9e8de65d7fcda25d45a2725d42352f5d03b9ec5cf2b5ff5cddb7cd5ccbc6555c965d485c8704475b850fbb5b60eb4b5b2ea5385aef23a75ab8a9c85a757c2359d2d77958c2518c5895043a5840b374578a7e975755a50e5752e7795745e0fb571324fb56f73cc156d3c25556cd3b8556b21c84569e151f55fc2fa755b28f38559b095255686b30553eb09b54faefe5544d5c3653ed427d539fb7ea534c3a7b52c9606652b519165271f78f51e0511051bb968e51adf7a351a6d5795194e401513f899f50af841c50a6c5dd5011dd494ffb3acc4fb750c94f5a6fd74f4953c8
  | 7, 0, 6 => 0x6efc04706eb6d5ab6e9fdaee6e7696f56e502c896e0d8dc26e02eec26da035b16d5716db6d2479296d1f9e616c76c0d66c5367486bc7b2ce6b3dc8836a697e6b6a5e2e496a3b0f486a38ec4f69cae70769bc6b266991695b697c5b6069658b7469183bbd68c78de0689eda766853fd76676bb23d6767de4a6756843666f87fdc66f54363668c788066731261661766a565ff6a2e6539ae4664ba2fd86494341264545b1d6452eb0d64326e2563df5c5263d7f5596374814a632c349262bc2e5c62adb27b62a0e515623a6240623567bb61c762736158bd67614941da6130f73c6117005560e1902460df19d360c081b760a298186066cd78605cf9926014a9d0
  | 7, 0, 7 => 0x8246e48c81f06d1281450cb28103242c80e5759f80ceed008073fb51806943d17fefa5537f6c93bd7f0c43de7eb814087ea789977e6b005c7e5eb0787dfe4a277dd241b97dab38cc7d4a419d7c9f7e7c7c91203a7b28e4477a9eb29b7a32e6c479eb7a8b79870edd790df74a78fa5a2578ec302a788c2ff5785ddb1277c666a77681c1b3762971fb75f7d78c75c58e567527fdbd75048d0774e4177e74bcc57d747c25d6747a456a73ce6d83735d3d7c7356bdfb73147dc1727f3775722f623071e224f471c5b78b71c45d7b71686d2e715adeae7101265370f3945670e8ab9670d14bca70ca2e0470ac39d1704a4f117029630f701c39856fef05cc6f48dd22
  | 7, 0, 8 => 0x92b63feb91b18ab19199be11916d61b39132cadd9124d9019081cf049061903f9033b524902116718fdbeb5d8f81b9038f2f8aec8ec451bd8d9ceb668d7869e68d73f9a28c86d0e28c4333ad8bfc04118bba63a28b9e40b78b414eb68b34a47b8b33b1068b303b6f8b21bf8e8af4dc708ac154b68aae30e98a7a9db88a16205689cec5d189ae061d8952d79488f9edfc88d106a58844fe92881d533b87f329e787d4247987913dc5877e346f87475200870de19f86bb989c86412037862eae4f861a5c818618a37a85b9af858577d8858574e55285721f6a84fccbd1847d00f2845c63d284582d5583dd9dd683cbd3c0839abc23832cb6db8277192482641cb9
  | 7, 0, 9 => 0xa1a3930fa0d1e825a0ca5129a0ba2447a0a58af5a09a887ca093d74aa0855b69a03a73baa02ab1c09fae04fb9f67cab99f0c24059f06ad0e9e7b41be9e4ff7719e04d2e49ddf60659dcf69d79dccd3d09dac32009cebfdea9c0945a09c029e899bd345fc9bc73dcd9b6f9ad19b62d21f9b5bb1f19b53791e9b27740c9b1d4b609b1b65e69ad61d679aa960819aa7a1379a96a5999a78a26b9a67f3379a4707359996391b998e521e998bcfd198c6cc9598a4197098a2066197e3684197c47c1b977147d6972ae2be9677bd2a964c72dd95c3b198950e4b5f94e87956947f040f946ca34093c3b93993bde836934ff48a93384e8a932b18c39312104f92f9ae42
  | 7, 0, 10 => 0xb1b5697bb177d426b1074598b03e1077b03a9b5bafcbe12cafb5dacfafa76697af7e4e4baf78aea8af0aef8caeba08ffae7a07f8ae158a96adee40ccadce3011adcd7a96ad81abe0acd09142acbf819aac9733e5ac9074a0ac621261abea86aeaab74b74aa82d705aa5f4264a9faaec3a9b63e9ca9744f92a94faecca8fc3611a8ed4db6a8e6f272a898adeca87f486ea85cb27fa859893fa8579795a8255610a80fe5eca7ed6f8ea7eb83f7a7dd0816a7778458a76b4f4da70c7473a6bf7766a6768364a5ef21d7a5eabc38a5da4240a57de989a53f8738a51841d6a4ac608fa406231da3731f65a35a4b36a320cff4a2dee76ea2c58cb3a274f80da24f97f8
  | 7, 0, 11 => 0xc1ffdce4c1fd94bec1c5ae3cc1a1f633c1438dfbc0f3e5dac0ddf788c0b58cbbc071786dc04efcebc02c3e4bc00bab3ac005c2cebfe09626bfb99eacbebd2cbbbe9f0fa5be769f18be672923be390894be159bfbbe04ba19bde508e2bdad5056bd8cffe8bd689c08bd63b217bd3930fbbcf879d7bcf80b4bbcb5f9c4bc8b9d4cbbfcd59abbc7133abbac5b9dbb6bf353ba506113ba2c20fdb9cec865b90b7cabb87a7005b8572b6cb7edea51b7b3f84ab758a4ccb737b8cab72f4b60b71d2d87b6897ce4b63ea31cb6187b80b5e1844eb5af91d3b533f09fb499ca37b492032db3c24a54b3971adbb3124904b2958c05b28f99edb28a2d69b1d74b79b1c6e4a7
  | 7, 0, 12 => 0xd0f46623d0b2fbe9d03db7cad02ede41d008a737d00843b7cff14dd8cfdf5c60cfa9f353cf7ec82acf338479cf2e0516cee27a34ce8d2592ce822d2fce6b0b63ce6a62a9ce3af6aecdfbffc3cd38e321cce0ba88ccc52a17ccbc92c1cc98182ccc5e9a47cc247446cbb2c260cb5012d4cad7f953ca7074eeca2c216cca1247a7ca011952c9c932d0c98b03f2c955416bc92eff1fc92b194cc91d5ae9c8eb9f55c89b3aa8c85246a6c7dfb52bc7dbd7ccc72a8082c7147b79c6e637d6c69e7be3c66f499fc5d00f3ac58eebc9c5342b32c4b98e87c4a8fd0ac48f442bc45b15b3c406c3f6c35a0575c301a16cc29f4858c26e9b1ec2377025c22fa591c20f561c
  | 7, 0, 13 => 0xdf66fd53deeaee19de8ede08ddea6151ddbeb597dd92abf9dd881ad4dd2cc0f5dcf6ae21dcf04b12dc9bdeaedc79da45dc240b61dc0b8b92dbf99c90dba270bddb9e4415db95b675db7af8fbdb18e957daafeb3cd9fde2d5d9e0ee8ed9bc7fd4d9ae803cd959f241d94bf1b5d9137c0cd8f58235d8889027d867a425d83420ded801ed6ad74112a8d5b4d3bbd58f2765d5340983d5279ebcd51552b6d44c5213d404f3a6d3e45aa5d3d3e2c2d3b30ebbd3a8e0f7d39eec29d33b83f8d30a59ccd2b65212d2a7bf81d28da698d26b7512d21f9782d1c7e360d1bac628d1aafba8d18f4277d16ca0bed168f0afd1566dadd136a4a4d130e37ad10ff778d10cbaff
  | 7, 0, 14 => 0xf0c49457f0be3d76f05e0487eff3c330efedc7a9efa703a7ef335fc1ef14a663ef0b3f7fee73db6eee60f2f9ee2e8df6edacebaced2e695fece2987aec9aa4e8ec99ef6dec4e94caec41d777ec40f0a9ec01a134ebc63093eba52384eb5c844eeb1a9bc8e9eb6b25e9e08265e9b79b0ee9840b59e978fceae93d90ece92139dee8d90f31e8cf8ba4e8b1e8cae879cfe1e85a7ff3e7e9b955e71705cde6b6f618e69cad5ce65d6ccfe56c185ee5465ba0e542f83be53fdc1fe4a9c7bfe44a5e60e4052d0ee402f227e38f2d78e38d55f2e311d1c1e2f73a11e2dcb27ae2a3a791e2590ed6e2128133e1e47322e1389b3be0e49234e00de424e00571fedf7eb290
  | 7, 0, 15 => 0xff86098afe6faf54fe69f639fdaefc54fd895fc9fd56bc3dfd42905ffd1964d0fccdb787fcc3aa8ffcaae456facfb439f9611aa0f914bcf6f8e7657ff8dbc959f870fe03f8245b74f7a500cdf79096fdf7712f20f760f6a9f6e37eaff6b5bc52f61b6f81f5e6a71cf57ec026f55337a9f539372af524d273f4e61d0ef4b474e9f499d820f4581c32f43a4527f3a8a818f39639ddf389f601f3201a90f31b8797f2d02965f1e406f9f1e2e744f1d1c126f1a30c32f16d981ff1411580f1382f12f10f47bbf0d31038
  | 8, 0, 0 => 0x207787b8201138cd1cc9b3b41c7f660e1c1160c61c02e4e51bd38e271b96e8611b6588df1ae5543519b22bfc196926bf18b98c20189246be17c028151780280516ed244d169ad4dc1658ec56155b070714c25be7147be17a14445611141f8fdd140ddc3213b478a2132809e312a036a6126ac74e11f546a611c9fc59111d5c611106cdc710af5719108cbea2106602d20f88aeee0f4142b50edcd7070ecd7e060e50224f0de1f81f0db3a33c0d359d660d2c2e290cf6d6570b5d6d29093db68007f908f707f0d02407852a5a076954520737ed1e0544cdf6052b8f990451cc9a0426a5410402104d03a5f4b30355f04502fbbdeb02f5fddb020fff7e00f26ece
  | 8, 0, 1 => 0x47e5621747c656fb47aec13b472d13a346cd9c504621c469455fb1d04541e84844aae86243cfd022436b52c0435961484323f83b42a809fe417604ab414c634940f62fdf3fd89f2f3eca17bc3e51fe3b3dad5fbf3d7b1e3a3d4337b83d32d0403d0508da3cc117773c153f903bcc4b8e3ba453603b4067bb3a1a9e38382614fb3627b04f35db239335a9aa7935895b0434bd92e333c0c900335a9b0e3265f79931b30d7c315f0dca30b17a1b30a94148300d39e92ffd69612ee5f83b2cc710002c33b3742ad2a9b42aa9504828a5bcb42880e0ed280c081527a4a97825e0085924f1d90e24ba3ed6241a19e722f2b39021f40ce021a9023c216845b420bd10b4
  | 8, 0, 2 => 0x6b0a9be56a9da52b690b0d3968f8c50e686021f667e36ec26722ad0067108e5267103ec5664a2e4d6608c413655e0be16535248a64ede01564bb1a6864894ca3644d15206438425e63d8096f628eab4b62125aeb61ede0566131850560c081b76014a9d06013f4555f938c875f40357b5d319ff65b8b47325b1760205a910ab55a0f56b158bcfd2357c4634856a65876567ab1f456713ef9555e780a5516b86d53d94335538ed0be537f76e65310cae852e1023b5264f3015164663951529dc4510cb0e150c1bb7d509f8ca35015e3964fc5f4ae4f85907a4f1c75a54d2e4be94d2885244cd3f7294cae6cf64c8d80f44c50a0f34c02950f4b0d465448be36e9
  | 8, 0, 3 => 0x97e4107297a2ad8895feb81b94ea215094dbd1b49353153f913e368f8f8b65ae8f0950aa8ed4acb68e9d72eb8e6a85208c0b847c8b1d15ca8ae474e18ac1d3288a7a9a9d895dd9a1888801688875e2ba86c3604986bb2776861a5c8185b3ccb1857f37778507f4ca84fccbd184d0ab2d84135e9584013fe783b31a7d8302b3d682843189824f20f6824ebd7681f06d1281d287038128f3f380b185227f2d59fd7e07b0f47db0481d7ac3e1087a98c06579ff8fe9795af53878e4f5a277cbd182779b444e773a3b4c770282c0768e6365764d3db5749a204b742c1b0371e3fb2171cfa26f70d0c1256f36b6b86db5f55b6c96dad26bf88c416bf2d3266bd02c76
  | 8, 0, 4 => 0xbbc01f92bb5f66ffb8db3bf4b4659c05b32747c9b158ad0fb1447d4bb0bd8805b0b62913b0b06ff8b03b1c5fb0049811af0a244ead70d8e4ac272790aba7945fab2b8525aac32e09aa6baa8ba99d0106a8fdcabba8fc3611a8f48ae1a8aceb64a888922ba77db8c7a7420870a69e95f1a64e8b36a61c3eeda5ef21d7a5dd0329a54e664ba54349f0a42a80b8a37ea8d1a32c9765a304b735a258df4ea10a5eb9a022680c9f574e1a9ee8568d9e9b8e0a9e950e899e86591b9deb9d439dc6e8679ce2885c9ca6bdbc9c31e4e49c26fc249bed4a379bea8a5f9bca85189b67b39d9b4c7f429b0132a19a8d182a9a80d3c499d4553f98fd6fd798e639c898c8770b
  | 8, 0, 5 => 0xe3c453f9e3963e6de2760958e1f09bdde17cf3aadde38353ddce86eeddb2f137dd44ebefdcf66048dbff73e2db7c6105dae5b725dae1e332dab6ff36da067d68d982c8fbd80e38fad7fdd228d753c3f4d6363344d5053b33d4f48f2ad43a869fd3d6fe7ad3ba0645d358ca24d277431ed24ac501d11892ced0bc3a17cedaf033ce63f497cdef810bcbbcb7cecb78c448cad7f953caccec61ca2c216cca1e5d15c9ad816cc98e47ffc8e27018c8de18bcc88323f1c82a4e78c7bf284bc77e7691c58557c3c4cca2acc3d12e09c3753fb4c2d474bfc18ac36bc11b76cfc026c9e4bfd6d0e9bf75efa6bebd2cbbbead66f1be769f18be620e8cbe2c3e52bd4fdec7
  | 8, 0, 6 => 0xffb3f673ff18459fff123350fee73185febb539efeaa4057fdf4a2a0fda9c5a0fc4e4806fc4b0b8dfc453af5fb6d2ecffa359d84f9a8b337f8ec2452f8037aa5f7d668baf61649e1f56a71faf4da989ff46969daf2218e7ff1dccc71eeca28f2ee18b783edacebaced03ec8bece046c1ec663512ebf3dd49eb406b8fe9a376e3e9430aa7e8a202a5e836ca65e7f44a52e7d7a280e76e1fb8e6eaac2be5f93c5de50d18f3e44b50b2
  | 9, 0, 0 => 0xfe971ab2f92dd199f61649e1f56a71faee12c54deab44034d8af2972d43a869fc708d5a6c68acfd0c43bc065c02871deba47a138b749d50ab158ad0fb03b1c5fa42346309437159c8ff96af68f8b65ae8d2c30e48302b3d677cbd18269904ec94e31041e3ef2c9303e51fe3b3d084ce73ba45360242a74e0196926bf1957081117a485a0167ebc1d
  | 10, 0, 0 => 0x69904ec9
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xfffffffffafac8c8fafac8c8f0f0f0f0f0f0f0f0eeeeeeeeeeeeeeee0505373705053737ffffffff00000000f00ff00ff00ff00fcccccccccccccccc555555555555555500ff00ff00ff00ffeeeeececeeeeecec050505050f0f0f0fffff0000ffff0000ff00ff00ff00ff00fafafafaf0f0f0f01111131311111313
  | 1 => 0xa5a5a5a5a5a5a5a5aaaaaaaaa0a0a0a0eee0eee0eee0eee0aaaaaaaaaaaaaaaaffaaeeaaff00cc00eeeecccceeeeccccee00ee00ee00ee00aaaaaaaa000000000000333300003333fcfcfcfcfcfcfcfc0f0f0f0f0f0f0f0fffffccccffffcccc55555555ffffffff11111111111111110055337700553377ff00cc00ff00cc00
  | 2 => 0xfff0fff0fff0fff0055505550fff0fffaaaaa0a0aaaaa0a0aaa0aaa0aaa0aaa0fafaf0f0fafaf0f0ffffaaaaffffaaaa1111333311113333050f050f050f050ffaf0faf0faf0faf055aa55aa55aa55aa3333333333333333ffffa0a0ffffa0a0ffa0ffa0ffa0ffa0ececececececececfafa0000fafa0000555555555f5f5f5f
  | 3 => 0xf0f0f0f00000000f0f0f0f0ffffffffff000000ff000000fffffffff0f0f0f0ffffffff55555555ffff5555ffff55555555000055550000f5f5f5f5f5f5f5f550505050505050500000ffff0000fffffcccfcccfcccfcccffffff00ffffff000055555500fffffffafaaaaaf0f00000fffff0f0fffff0f0050555550f0fffff
  | 4 => 0x5f005f005f005ffafafafa00000000eeeeeeee00000000ddddddddddddddddccccffffccccffffffff00ffffff00ff00ff000000ff0000ffff00f0ffff00f0f0fff0fff0fff0ff00f000f000f000f0ffff0055ffff005555ff55ff55ff55ff0055005500550055f0f00000f0f00000f000f000f000f000000f000f000f000f
  | 5 => 0xa0a0a0a0a0a0a0a0eeeeeeeee0e0e0e0111111111f1f1f1ffefefefef0f0f0f0010101010f0f0f0faaaa8888aaaa8888fafaf8f8fafaf8f8a8a8a8a8a8a8a8a8ffaaffaaffaaffaaffaacc88ffaacc88fafafafafafafafaaaffaaff00000000ffffaaaa00000000ffaaffaa00000000ffaa0000ffaa0000a0ffa0ffa0ffa0ff
  | 6 => 0x1133113311331133000500050f0f0f0f0011333300113333fffafffaf0f0f0f0005500550f5f0f5fffaaffaaf0a0f0a0aa55aa55aa55aa55aa00aa00aa00aa00ffffececffffecec131313131313131305050505ffffffff0101333301013333feccfeccfeccfeccffccffccffccffccfefeccccfefecccc0505050505050505
  | 7 => 0xaaffaaffaaffaaff00aa00aa00aa00aaffccccccffcccccca0a0a0a0aaaaaaaafaaafaaaf000f0000a0a0a0a00000000ffaaaaaaff000000ff00aa00ff000000ffaaffaaff00ff00fffafffafff0fff0fa00fa00f000f000eeeeeeeeccccccccfffffafaf0f0f0f0ffffaaaaf0f0a0a0aaaa0000aaaa0000eecceecceecceecc
  | 8 => 0xffccffcccccccccc00ff00ff00000000ccffccffccffccfff0f0f0f000000000fff0fff0ff00ff00fff0ff00fff0ff000f000f000f000f000033003300330033fffcfffcfffcfffcffff000000000000ff00ff00000000005555555500000000ff55ff55ff55ff555500550055005500ff50ff50ff50ff50ffaaffaaffa0ffa0
  | 9 => 0xffcceeccffcceeccfff0aaa0fff0aaa0ffccaa88ffccaa880a000a000a000a00fefcfefcfefcfefcffeeccccffeeccccffecffecffecffecfac8fac8fac8fac811111111fffffffffef0fef0fef0fef0fefefefefefefefefe00fe00fe00fe00ffaaff00ffaaff00ff00aa00ff00aa00fa00fa00fa00fa00fff0fff0f0f0f0f0
  | 10 => 0xfffcfffcfcfcfcfcfffcfcfcfffcfcfcfc00fc00fc00fc000303030303030303fffff0f0f0f0f0f0fff0f0f0fff0f0f0aaaaaa00aaaaaa00ff00f000ff00f0000f0f00000f0f0000ffaa0000ff000000ffffaaaaffff0000fffffafafffff0f0fefefefefcfcfcfcffeeffccffeeffccfefefcfcfefefcfcfff0faf0fff0faf0
  | 11 => 0xff0fff00ff0fff00cfcfcccccfcfcccccfcccfcccfcccfcc0a0a0a0a0a0a0a0affffffffff00cc0000ff33ff00ff33fffff0fcf0fff0fcf0f0f0c0c0f0f0c0c0fff0ccc0fff0ccc0ffffcccc000000000f0f0c0c0f0f0c0cf0f3f0f3f0f3f0f3fcfcccccfcfccccc0f0c0f0c0f0c0f0caa88aa88aa88aa88faf8faf8faf8faf8
  | 12 => 0xffffaaaaaaaaaaaaf0fff0f0f0fff0f0aaffaaaaaaffaaaaaaaa00aaaaaa00aaaafaaafaaafaaafaa0aaa0aaa0aaa0aaf0faf0faf0faf0fafafafafaaaaaaaaaeeeeeeeeececececfafaaaaafafaaaaaffccfcccffccfcccfaaafaaafaaafaaaeeeceeeceeeceeecffffff00ff00ff00ffffcccccccccccc0f0f0f000f0f0f00
  | 13 => 0xfcfcfcfcccccccccfff00000fff00000ffcc0000ffcc0000f0c0f0c0f0c0f0c0fffffcfcfffffcfcfffafffafffafffaffeeffeeffeeffee000f000f0f0f0f0f0033333300333333fafafaf0fafafaf0eeeeeecceeeeeeccffaaffaaaaaaaaaaffaaaaaaffaaaaaa
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x30201004030205044030105064
  | 5, 0, 0 => 0x140210010d0c600340d081c335000302082d0450002010d0c1750014020d1312500140d1812065000302081e285000301082d06500141b020d0c50a02100e0d0c60003020d1e295003102081c305000a020d0c11500030d0518065000a030908075000a2f351c1750002210d0820500032f081c2e500140d0c1e065000302271e25500020d1812175002a020d18295000302082c0450014020c1315500140c1815065000a03082615514100d0c191860003022b1e2550014020d0c04502100d0c1a1860014010d0c065000a030d26255
  | 5, 0, 1 => 0xa09081c365000302221c0450a14100d1d1c6002402081c045000d0c1806175000a03081f065000301221c065002401081c065000a0e0d0c065000302081f0f5000003020105400020e0d0c0f5003132081c065002a0d1a18065000302160c0450003020d1800500020c1815175000323081c045000a020d0c0b5000316010c065
  | 6, 0, 0 => 0xa450d0807066000d081c06170f6000a4a081c15496000a2a0d7125066000a020c1c15176000a14021a1c1560000030201082d500010d081c06366000d1c182506366000a0e0d081c0660002210d081c13600210d081c18066032f800d081c1e7000a0d080706366000a020d081c646000d1c2506360f60003020d1c2025600034d081c1506600020e0d081c0f6000302550d08206001479020d081c6000a02555f2536600033e081c1506600032f4108070f6000a035708441560000030227081e50a142f100d0c1c700030d0854070660003020d081c5d600030216081c046000a1402630d1c600030d221c18066
  | 6, 0, 1 => 0x20d1c1e25366000a510d0807066000a14020d1c6f6003142081c18066002f0201081c366000a030d0c5a066003c140d0c1c06600031c25153f0660000032301081c500081c1506360f6000302081c201560003020d1e682560051020d08070f60003020d1c250460003790d081c066000a14020e0d0c60003554e085f066000a0302161d1c600081c153f0636600020d081c043660014030d0c18066000a030d0844436000d081c1806176003c0302271c256000a480d0807066000a2a0d1a1c0660003010d1c25066000014020d18125000377750d081c600030208182c156000a03020d1c00600030216010c186
  | 6, 0, 2 => 0xa2f411c2536600035c0d081c06600036a0d081c066000a240d08070660003020d1a081e600002a020d1a1850a0210590d081c7000a030d1c502560014010d081c066000d0c081806366000a02072515366000a030d0c58066003c030d07250660003021c1325156000301081c1506600031c182515066001402010d741c6000a0d0c1c06176000a140d1a1c066000a670d221c0660003020d0c082060003023e0d07256000a03080715066003c0d080706366000a2a0871150660000030216010c5000a031a1c150660003020d1c7c2560002081c131536600081c18150636600001452020d0c500031c2515060f6
  | 6, 0, 3 => 0xd081c130636600030d1a1c18066000a14550d0c066000002210d081e50002210d08070f60014081c15060f6000a343d0d07256000a570d68253660003023e08071560000240201081c500000a020e0d0c50003020d0c08046000a03555f25066000a230d1c253660014081c153f066000a2f41081c17600030d081c20066003c03020d1c296001402550d0c0f60003320d081c06600000a142f351c50003020d081c6e60014020d081c04600030d08073f066000a55085f06366000a030d2207066000302555f250f6000302081e681560000310232081c5000a02080715176000302081c150460003010d0c08066
  | 6, 0, 4 => 0xa14100d0c191c7000a0d0807061760072030d081c066000a4b081c15066000a0341080740600030d081c04066001402100d0c186000a1456020d0c6000a020d081c6d60003020c0813156000a140d081c50600030c081815066004e0d081c06366001402010d0c186000a030d08074f6000a0d07250636600020d1807253660a02100d0c1a1c700031b020d081c6003c140d08070660000020d0c18175000a210d0807066001402081c131560014081c18150660003520d080706600000a0302081f5003c030807150660000030201221c500020d0725360f6001402741c1815600030d081807066002a0d081871066
  | 6, 0, 5 => 0x5303081c1506600032f02081c04600030d081c185060003020d081c2e6000a2a020d1c2960002210d081c65600001402010d0c5000a08071506366000a14020c5a1560003020725150f6000a020d1c66366030210010d081c70003081c131506600030d1c1e25066000a31420807066003b020d072536600030d4d0807066032f0201081c1e70003550d081e066000a140c1c15066000a14020d1812600033e0d08070660002080715360f600030d081c7c066000a02100d0c5a6000a1455085f066000d081c1e06366000302270d081e6000a14020d1d1c6003c0302081c2860014020c1c150f60003020d1e71256
  | 6, 0, 6 => 0xa1402701c15600140d0c1c18066000d080706360f60003081c1e15066003c02081c151760000030201082c5000a5521085f066000a03021c2915600030d5e081c066000a610d081c066000301081c5f0660003020d081c5b600000a56020d0c5000a02350d1c17600140d0c1c060f600032f0255081e600035508185f066000a030216010c6003c021c25153660002610d081c0f6000a03085f60066000d4b081c18066000a03570d082660003020127081c6000355085f060f63c142f100d081c700034e081c1506600037b0d081c066000a030725150660003081c157a066000a4a0d0807496000302085f600f6
  | 6, 0, 7 => 0x3c0d1c25063660003570868150f60014020d0c1a186004e210d081c066000a03087f157e6000a1402590d0c600000a0309081c5000a081c15063660003020d13072560003010d0807066000a1408071506600030d180725066000a57020d0c176003c343d0d1c25600030d0c081e0660014020d0c19186000a032f7d161c6000a030d1a07066000a140d0c5a066000d0818070636600030d0725060f6000302081c5f0460014020807150f6000308541c15066030278010d081c700140d081c1e066000a020d1c12176000014020c18155000a14020d1c2960003020d081c336000003020d1a1e5000376750d081c6
  | 6, 0, 8 => 0x302081307156000308180715066000a030d1c660660a02100e0d081c700140d0807060f600030d08182d066003b030d072506600310301081c06600032f020108076000014020d0c135000a240d1c25066000d081c3f063660000140d0c18065000a0d221c063660003080715060f6000a140d701c0660003020d1c660f6003c0d081c0617600140d0c4d1c066000a020d081c116003b0d080706366000a030d1c290660003020d1c1829600000a030d08265000034790d081c5000377780d081c600030807153f06600036c0d081c066000a14032f351c600021601081c3660003020d08070460003020d1c290f6
  | 6, 0, 9 => 0x3020d081c046003b030807150660003020d081c6b6000a41081c40366000014020d0c1e50002010d1c25366000a210d1c25066000a1402010d0c6000a03380837066000a3a0d0839066000a0d4b0807066003c031c2515066000a0d081c4f3660003010d081c066000a030d051c066000003022b081e5000a2f35081c3660002210d1c250f600141b020d081c600520d081c0636600000a030d086950003023e1c25156000a1402741c156003c081c150636600020d4b08070f600310302081c046000d081c1806366000a030d0850076000a51081c15066000014024e0d0c500140d0818070660003020d70081e6
  | 6, 0, 10 => 0x34e0d08070663103020175081c7000a14350d1c06600021c2515360f60014023e081c1560003081c18150660073030d081c0660053030d0807066000a03570d4425600032f0175081c6000379020d1c256000d4d081c06366140210010d081c7000a343d1c25156000a0347080746600030d4c081806600021c25153f366003e0d081c06366003c03022b1c2560003020d0813126001402350d1c0f6000a030d086968600030d08181206600030d081307066000a140d221c0660000032f7b081c50002010d081c176000a140d0c07066003b140d0807066000a6202610d1c6000302160d0c1360003160d0c18066
  | 6, 0, 11 => 0x30d081e070660a140210550d0c7000a14020d5a126000a03020d07296000a081c15061760002081c1815176000302010d082c60003020d081c30600240d081c18066000a020d081c0b600030d221c060f6000a140d1c12066000a02550d0c17600031601081c0660002081c15170f6003c020d0725366000a1c251506366000072020d0871500021c182515366000003020d05185003c14081c15066000a21081c1506600240d081c060f6000a14020c181560003021601741c6000a31421c25066000352081c150660002081c153f1760014020d1c120f6
  | 7, 0, 0 => 0xa03230d1c25600000302081c1e156000a0302081c159c7000302081c07150f7000a0362081c1589700000a025521085f6000003020d5e081c600000a02610d081c6000a030274081c157000a03380d081c067000a030201081c1570057020d081c360f7000a03021c1825157000a0302850807157000a62020d0807367000a03900d081c06700000a343d0d08076000a34030d080706700000a570d08683660000030201081c5f6000003024e0d0c086000a03020d081cb57000a03020dbd081c700000a0355085f066000014020d0c1c0f6000a03c90d081c06700000a230d081c366000003025508185f6000a032f910d081c7000a038f020d0807700030201750d081c7000a03af020d081c7
  | 7, 0, 1 => 0xa03081c0715067000003020d07250f6000a0386081c15067000a03020d081cb27003c03020d081c887000a03aa0216081c7000a0d081c15063670003020d1c25150f70000030d081c13066000a570d081c06367000a033d081c15067000302010d081c047000014020d081c1e6000a03081c1506367000a030d081c2d067000302160d741c18700000a03570d68256003c03020d1a081c7000a2f020d1c2536700a50302081c18157000a030d4c0807067000a1402010d081c70014023d0d081c0f7000a030210081c1570003020d0807060f700000a140d0c1c066003c142f020d081c70003160d081c060f70003020d0807820f7000014020d0c1c186000a2f02210d081c70000020d0807360f6
  | 7, 0, 2 => 0xa0302080715897000a020d1c6825367000a030d1c251506700000a03570d19086000053030d081c066000a0302270d081c7003c3403020d1c257000a2f020d081c177000a140d081c07067000a14020d081cba7000a02160d0807367000003020d0c081e6000a039f020d081c700000a0347081c4660003020d0c08070f7002a0302081c150f7000a143d0d081c067000a038702081c1570014023d0d081c187000a0302470d1c257000a032f620d08077000302160d081c137000a030d08078206700000a03020d1a0760003020d081807067000a0302010d0c087000302550d081c6570003160d081c1806700000a0d08070636600000a14020d0c5a6003c0302081c681570000020d081807366
  | 7, 0, 3 => 0xa023d0d081c5a7000a030d22081c06700000a142f41081c60003020d4108070f7000362020d081c1e7000a030d08070643700003c02210d081c600000a51020d1c256000003020d081e716000a1402910d081c7000302a3010d081c7000a03020d081cd57000a030d8d0807067000a03021c2515a77000a030d087f1c7e70003020d081cac0f7000a03550d081c067000a0302081c15067000a030d0c0807067000a2a03081c150670000034e0d081c06600000a02081c15366000a1402081c153f7000a030291081c157000a0302320d081c700140302010d081c700000a030d072506600000302010d0807600000a14020807156003c030d081c067e7000003020d18072560003020d22081c0f7
  | 7, 0, 4 => 0xa24020d081c067000a2f02081c15367000a03010d081c067000a020d1c5f25367000a03850d080706700140302081c153f7000a1402081c18157003c032f0d081c067000a030d410807067000a0383020d07257000003020807153f60000036c020d081c60a14b902100d081c800000a57510d08686000a03470d0807067000a03028d081c157000a03020d1c25897000a030d087107067000a032f7d0d081c7000a030d081cac06700000a2f510d081c6000a02550d1c25367000a0302a10d1a1c7000302160d0c1c0f7000a036202b30d1c7003c03020d1c25067000acf030d081c06700003c020d1c25366000a31030d0807067000302350d081c0f7000a0d081c18063670000024e210d081c6
  | 7, 0, 5 => 0xa030247081c15700000a24020d1c2560000020d081c3f36600030d081c1806367000a03020d080740700000014020d0c18500000a020d221c366000a03020c081815700140302081c150f700000a14570d0868600a5030d081c18067000003020807150f6000a02550d081c17700000a14020d701c600000a03940d081c60003020d081c120f7000302100d081c187000a0356020d081c7003b03020d08070670000030d081c1e066000a03160d0c1c06700000a14230d081c600003c020d081c17600035702081c150f7000014020d0c4d1c6000a03022b0d1c25700030d081c07060f700003b020d0807366000a036202080715700000a03020d1c296000a03350d081c06700000a03570868156
  | 7, 0, 6 => 0x3c03020d1c7125700000a0308071506600140302081c181570a140210550d081c80000032f41081c0f6002a030d081c060f700000302081807156000a14b7020d081c7000a02081c6815367000a030d081c12067000a1402470d081c7000a03020d081c04700000a03020d1c666000a020d081c88367000a14b602081c157003c1402100d081c7000a0357081c15067003c340302081c157000014020d08070f600030d081c1807067003c3103020d1c257000003020d08182d600003b03020d07256000031030201081c60014020d081c150f70003023d0d081c137000a038a020d08077000a032f021c251570000030d08541c06600033d0d081c18067000a03a0020d081c7000a03020d221c067
  | 7, 0, 7 => 0xa1402081c15a77000a030d080706467000a03021627081c7000a0302630d081c7000a032f02081cac7000a03020d7008077000a037d02081c15700000a0d081c063660000032f41081c186002a030d081c180670000020d081c18366000a0386020d0725700000a5102081c156000a03021c6825157000a0d081c067e367000302910d081c187000a030d087f0706700000a03570d082c6003c0302270d081c7000a03023d0d0725700000a140d0807066000014020d0818076000a0302081c15c07000302553e0d081c7000a03020d0725367000a140d081c15067000a03081c153f067000a03aa020d1c257000a030d4c081c067000a03900255081c7000a1403081c15067000003020d1c253f6
  | 7, 0, 8 => 0xa14020d081c897000a0377020d080770000a6020d081c186000a030219081c157000a032f41081c2c7000a020d1c2506367000302081c15bc0f700000a020d4b0807600003c03021c25156000a03081c1815067000a030d08cb1c067000a03830208071570077020d081c18367003c14020d081c067000362020d08070f7000a032f02160c1c7000a0302a30d081c700000302010d081c6000003570d08680f6002f020d081c360f700000a03020d051c6000a0302081c5a15700000a030d087f7e600000a030d0868436000a4a030d08070670003554e0d081c067000a032f024108077000052020d081c366000003230d081c0f6003c03550d081c067003c0302081c1506700003c02081c15366
  | 7, 0, 9 => 0xa020d081c061770003021601081c18700000357520d0868600003b03020807156000a0390020d0807700030d081c15060f7000a03081c15bc067000a033d0d081c407000a0302920d1c257000a0302160d701c7000a032f020d08077000a03020d1c2c257000302780d081c187000a14022b0d081c7000a03620d0807067000a0323020d08077000a2a2f020d0871700037702010d081c7000a032f020d1a1c7000362020d0818077003b030d081c07067000a2f0d081c06367000003570d0818686002f020d081c18367000a0302550d082c700000a480d081c06600000a02210d1c256000a030d08cd1c06700000a03023808376000003230d081c18600000a3a020d0839600000352020d1c256
  | 7, 0, 10 => 0xa14020d221c6000aab03020d1c257000a0302b40d081c700037d020d081c0f70000030d081807066000a34023d081c1570003020d081c13157000a31023d0d1c257000051020d081c0f600030d081c18150670003020d1c68250f7003c62020d081c36700003c343d0d081c6000a039302081c157000a039d020d081c7000a03021a081c15700000a14020d0c07600003b14020d08076000302160d08070f7000a032f920d081c7000a0302a80d1c257000a03027b0d081c700032f02010d081c7000a142f02081c157000a03081c1506407000a03020d1ca9257000302470d081c187000a0302a10d081c70014030d081c060f7000a03081c15064970000030d0807060f600000302160d0c186
  | 7, 0, 11 => 0xa030d8c080706700007303020d081c6000a038b020d0807700005303020d08076000a03081c15067e7000a037d0d081c06700037d020d081c1870a0362022b0d081c800000a510d081c066000a14020e0d081c7000a02270d081c367000a030d1c68250670000020d4d081c366000051020d081c186000302010d081c687000a1402081c681570003020d1c1868257000a3403021c25157000a14023d0d08077000a03081c15a7067000003020d4c08186000a020d411c253670002550d081c360f7000a03160d08070670000023e0d081c366000a14aa020d081c7003c032f0255081c7000003020d0818126000a0302081c15887000014020d081c3f60014030d081c18067000003020d0813076
  | 7, 0, 12 => 0x3c1402081c156000a03830d08070670003020d1c5f250f700000a0221081c156000024020d081c0f600000a3102421c256003b0362020d08077000a030d081c5a067000a0302270d1c2570000035202081c156000a020d41081c1770003023e0d0c081c70003020d081c18897003c02160d081c367000003024e0d08076000a550d081c06367000a02081c1506367000a2462020d081c7000a142f100d081c70003020d421c250f7000302550d1c250f7000a03a2020d1a1c7003c032f620d081c700005251020d081c600003c2a020d08716000003023e0d1c25600003c03020d1a1c600000a03081c1506600000a1402350d1c600000a14020d741c600003c0d081c0636600000302081c18156
  | 7, 0, 13 => 0xa032f081c150670002010d081c18367000a0302081c15b57000a030d1c5f2506700032f02081c18157000a0302bd081c15700000a240d081c066000a0302081ca9157000024020d081c1860003020d1a081c0f7000a03020d081c6f7000003020d221c0f6000302081c68153f7000a0357270d0868700000a14020d1c126003c030d0c081c067000ac10302081c157000003021601081c6000a030d421c25067000a03550d1c25067000a03021c2515067000a030292081c157000a032b0d081c067000a0302081c2c157000a0362020d221c700001452020d081c600000a021c251536600037702081c1815700003c030d1c25066000a0d081c5f063670003020d19081c18700032f02081c150f7
  | 7, 0, 14 => 0x302010d74081c7000a03aa0d081c067000a0302c90d081c7000302010d1c18257000a030d1a081c06700000a1457020d0c6000a0302100d080770000030d081c3f0660003020d1a081c18700000a030d221c066000003020d221c186000a032f021608077000003020d081e076000a14020d081cb57000a030d081c58067000302081c68150f700000a02081c15176000a0302590d081c7000a03020dd2081c7000a03020d7408077000a0383020d08827000a030d081ccc067000a0302010d080770003023d0d08070f7000a14030d0c1c0673c14032f020d081c8000a03020d1807257003c31030d081c067003c032f020d0807700003b030d0807066000a038302081c15700000352020d0c086
  | 7, 0, 15 => 0x14023e0d081c60000030d081c18066000a030227081c157000003024d081c156000a0302160d741c7000a03b9020d081c7000379020d081c187000a03020807153f7000002210d081c0f6000a0302851c25157000a2f020d4b081c700030255081c150f7000a140d081c6806700000a343d0d1c256000a140302080715700340302010d081c7000003023e081c156003c03020d081c407000a0387020d08077000a03021c7125157000a6202210d081c7000a0302081c15b27000a03860d0807067000a03081c6815067000a140210081c157000302081c1868157000a024e210d081c7003c036202081c157000a033d0d0807067000a3103021c25157000a0285081c15367000a030d080706367
  | 7, 1, 0 => 0x20d1c1825366000302550d0c080f7000a02081c1589367003c03023d0d1c25700003c140d081c0660003020d4d19081c700000a020e0d081c600000a210d081c066003c03020d1c2536700000a14020d0c186000302c40d081c0f7000002210d081c18600000a032f35081c6000a0355081c15067000ac20302081c157000003520d081c066000a03020d0807067000a14032f41081c7000a1402270d081c700000a032f410807600020d0c081c360f7000a2a030d080706700000a020d08073660003020d0c081868700003c03081c15066000a2f620d081c36700020d081c1806367000a0302910d080770014020d42081c0f7001402550d081c0f70000020d1c25360f6000a032f022b081c7
  | 7, 1, 1 => 0x30201081c18157000a03550d0c0806700000a2a020d1a1c6000a032f3d16081c7000a03020d081cd4700000302010d1c25600000a03230d08076000a03021c2515897000a03bf02081c157000a03020d8d08077000a140d081c5f067000a03c40d081c067000a3a03020d07257000a03081c15068e7000a0302081807157000a0d0c081c0636700340302081c153f7000a03ae020d081c7000a142f020d0c1c7003c03020d70081c70000020d081c170f6000a140d42081c067000a030d081c2c06700000a2a020d71256000302010d081c067000a14550d081c067000a1402081c1506700000a030d081c4f6000302920d081c187000a0362470d081c700000a0d1c2506366000002010d081c366
  | 7, 1, 2 => 0x1402100d081c187003c03620d081c067000302081c153f06700340302081c18157000a1456020d081c7000a0302980d081c7000a31030d1c25067000a032f020d07257000a0381020d08077000a0302470d08077000002081c153f3660003020d411c250f7000a31620242081c7000302950d081c0f7000a03c80d081c06700003c03022b081c6000a038f02081c157001402010d081c1870003020d1c71250f70003020d0807150f7000aab030d081c06700001403020d0c186000357020d08070f7000a313d0d081c06700003c020d4b081c6001402100d081c0f700000a0d081c0617600340302081c150f7000a2f020d080736700030274081c181570000020d081c1817600000a0341081c406
  | 7, 1, 3 => 0x3c14020d0c1c6000a140285081c157000a030d411c25067000a020d081c40367000a03950d081c067000003021c25153f60003550d081c060f7000302081c15060f7000a14030d0807067000a03900216081c70000033e0d081c066000002081c15360f6000a03470d1c25067000a030d081cca067000a030d1c7125067000a030d080715067000a1402081c71157000a03620d081c8970003020d1c187125700000a03570d08446000302010d0c08187000a03570d0807067000a6202081c153670000310242081c0f600000379020d081c6000a14100d081c0670003020d081c600f700030d081c186806700000a343d081c156000a3403081c1506700000302554e085f6000302270d081c0f7
  | 7, 1, 4 => 0x3020d42081c137000a03020d1a1c29700003c020d0807366000302550d081c137000a02100d081c5a700030d42081c18067000a032f62081c15700000a2a020871156000a0302160d0c18700000a03021a1c1560003550d081c18067000302081c1815067000a03029b0d081c700000a081c1506366000a037d020d08077000002081c1815366000003021c25150f6000a030d081c07067000255210d081c0f700000a51020d08076000a03020d680725700030d081c5f060f7000a2a0d081c71067000302320d081c18700000a3142081c066000a030d081c600670000310242081c186000a03270d081c0670000030d4d081c066000302163e0d081c7000302270d081c18700000a03020d0c5a6
  | 7, 1, 5 => 0x20d0c0818366000a030c081c15067000a03020d0818127000a03020d190807700000a03020d0c586000a03020d1c44257000a0d081c064636700003c03020d07256000003020d08182c6000a030d081807067000a020d70081c367000a03ce0d081c06700000a031c25150660000030201081c156000a55210d081c067000003021c1825156000a020d1c072536700000a4a0d081c49600032f020d081c1e7000a03020d080789700030d081c185f06700000a020d0c1c17600000a14020d1a1c6000a03020d1d081c700000a67020d221c6000a0216081c15367003c14023d0d081c7000a0302be081c157003c03020d08070670003020c081c150f7003c03160d081c06700000a03020807156
  | 7, 1, 6 => 0xa0347081c15067000a03025591085f7000a142f020d08077000a03081c7115067000a4a030d1c250670014020d41081c0f7000a030d08070649700000302010d0c086000a77020d081c367000a032f3d0d1c257000003025c0d081c600bb1402100d081c7000a3103081c15067000a032f020807157000a030d0807840670000036a020d081c6000a037d02160d1c700000a24020d0807600000a03830d088260062020d081c360f70003020d0c081c9770000343d0d081c0f6000a1402100d0c1c70003010d081c18067000a030d7f1c25067000a03020d081c287000a0399020d221c7000302750d081c187000a038d081c1506700001402010d081c6000a1402081c5a157000a1402081c15897
  | 7, 1, 7 => 0x1402081c153f600002a020d08710f6000003020d1a1c0f6000a03020d080788700000d081c06360f6000003020d081c206000a03020dc3081c7000a34023d0d08077000a14470d081c067000a343d160d081c7000380020d081c1e700000302320d081c6000a90020d081c367000a140d081c710670003020d081c1804700000a03570d08686000a2a62020d08717000a2f020d081c367000a0362020d1a1c7000a0385081c15067000a030255085f067000a0393020d08077000a620d081c06367000a23020d081c367000a03570d700868700a40302010d081c7000a03020d1a080770062020d081c18367000003020d08073f600000a0255085f36600000a03020d220760000343d0d081c186
  | 7, 1, 8 => 0xa2a0d087106600000a030d1a1c066003c030d081c0706700002a020d08187160000020d081c13366000a030d0807067e7000003020d1a1c18600000a1402550d0c600000d081c18063660000030d1c25060f600037602010d081c700001402081c150f6000302081c15890f7000a0390020d1c257000a140302350d1c7000a3403020d07257000a0302960d081c7000a14020d0c1c067000a03b7020d081c700000a56020d081c6000a0302081c1540700a50377020d081c700036202010d081c70002160d081c360f700000a0302555f256000a030d084407067000a03021601081c7000a317d020d081c7000a0302086807157003c032f0216081c7000a140d41081c067000a03d10d081c067
  | 7, 1, 9 => 0xa0302081cb1157000a03087f1c15067000003020d1c1325600000a02210d08076000a57020d1c25367000a03023d1c25157000003010d081c06600000a14081c150660000030d1c1825066000302a30d081c18700001402081c18156000a03081c1589067000a03021c251536700000a9a020d081c6000302081c1815897000a03020d1c2d25700000352020d080760003020dc7081c1e7000a3a030d0807067003c140302081c157000a0302160d1a1c7000a020d080706367000a0302081c4415700003c03020807156000a160d081c06367003c0387020d081c70002160d081c1836700030d0c081c060f700000a030d0807066000a039e020d081c7000003020d08180760a0390020d0c081c8
  | 7, 1, 10 => 0x3d0020d081c0f7000a4a03081c15067000003020c08181560014020db8081c0f7000a03020d081c297000a140d087f1c0670000024e0d081c366003c2a030d081c06700036202081c153f70003024e910d081c7000a03020d0725067000a140d081c5a067000a0302920d080770003020d0807370f70003020d0c081c137000a030270081c15700000a020d072536600030d0c081c18067000a0302081c157e7000377020d0818077000a038f020d0c1c7000a0d8c081c06367000a0386021c25157000302b30d081c0f7000a8b020d081c367000a020d1c251536700003c030227081c6000302c60d081c0f7000302010d081c1e70031030d081c060f700032f020d08070f700003c14020d08076
  | 7, 1, 11 => 0x3081c153f06600030d41081c18067000a020d081cac367000a0355081c5f067000a1402081c15b57000a140db8081c0670003027b0d081c1870003470d081c180670003020d0c1908187000003020d081e68600030d081c1871067000a037702081c157000003024e0d1c256000a03380d080706700000a020d0807176000a030d080737067000a0357470d081c700007203020d081c600000a024b081c156000003020d081c046000a020d081c15177000a020d22081c36700036202081c150f7000a142f3d0d081c7000a03b30d081c067000a03c60d081c067000a57020d081c177000a032f0d080706700000a032fad081c60031030d081c1806700032f020d081807700005303020d1c256
  | 7, 1, 12 => 0x32f0201081c6000302550d08070f700000a14020c1c156000a1490020d081c700030216081c150f7000003023e0d08076000a030d080739067000a03020d7107257000003020d081c7c60003020d081c1e06700000a140255085f6000a2f0216081c367000003081c15060f60000020d081c1e366000a0357020868157000a030d086807067000a039002081c157000a1402100d08077000a3403020807157000a02350d081c367003c0362020d08077000a030d081cbc067000a02010d081c367000a3103020d0725700003c03570d08686003c2f020d081c367000a0362081c1506700036202081c18157000a1402590d081c7000a02210d081c187000a03d00d081c0670003020d41081c137
  | 7, 1, 13 => 0xa0302080715067000a030d1c2506367000a0316081c15067000a14020d0c191c7000a14b9020d081c700000a02080715366000a87020d081c367003c14030d081c06700a50302010d081c700003c030d0807066000a03020e0d081c7000a03020d05081c7000a0302081c6815700000302081c131560003020d70081c0f7000003081c1815066000a0d081c0706367000003020d1c1e25600000a31024208076000014020d741c186000a0302d30d081c7003c03570d081c0670003020d1c07250f7000a0302270d08077000003020d4d08076000a0302010d1c2570003023d0d1c250f70000140d081c060f6000a0302850d0725700000302550d081e60003020d4208070f7003c032f020d1c257
  | 7, 1, 14 => 0xa03c5020d081c70000030d0c0818066000a03620255085f700000a2f41081c366000a0302b00d081c700000a0302072515600000302081c157a6003c037d020d081c7000a030d085f070670000020d4b081c0f6000a14020d08070670000530302081c156000a030d70081c06700003c51020d081c6000a0379020d081c7003c03020d1c682570003020d70081c187000a030d1c072506700030d0c4d081c06700000a030d081c506000a148602081c157000a032f100d081c7000a030d081cb1067000a033d0d1c2506700030d087f1c18067003b032f020d08077000014020d081c136000a14023d081c157000a030d4208070670003023d0d1c182570000140d081c18066000a03550d0807067
  | 7, 1, 15 => 0xa02081c181536700000a032f411c256000a2a030d1c2506700000a0302085f606000014024e0d081c600000a0d4b081c0660003020d740818077000a14020d0c1a1c7000302010d0818077000a0302910d1c2570000020d4b081c1860000030255085f0f6000a03021c25153f7000003024e081c156000003027b0d081c6000a030d0807068e7004a030d081c18067000003020d0c08136
  | 8, 0, 0 => 0xa140357020d081c80a036202550d081c8000a0302dc0d081c7000a0357020d08077000a030d081c68067000a1402100d081c70003020d081c18687000a340302081c157003c0362020d081c7000a3103020d1c257000a02850d081c367000a020d41081c3670a0302554e0d081c80a032f020d081c2c8000a0302c80d081c7000aab03020d081c7000a31023d0d081c70a3103020d081c0680003020d081c680f70a032f02160d081c800000a020d081c176000a0383020d081c7000a0302550d0c087000a032f0d081c0670a0362020d081c688000a0302a80d081c700032f020d081c187000a14020d081c5f7000a0302c40d081c7000a03020d081ca970a03020d0c081c068000a020d0c081c367
  | 8, 0, 1 => 0xa14020d081c0670003020d081c185f7003c0302160d081c7000a030d42081c067000a03550d081c067000a0302081c150670003020d42081c187000ac203020d081c7000302550d081c18700000a02081c1536600003c030d081c066000a03020d081c0770003020d081c5f0f7000a2a020d081c7170a0302850d0c081c800000a310242081c6000a03020d081c607000a0302270d081c7000003020d4d081c60a0362020d081c5f8000a0302850d1c2570003020d42081c0f7000a03020d411c257000a0302950d081c7000302550d081c0f7000a1403020d08077000003023e0d081c60a0302160d081c6880a1403020d081c158000a03020d1c71257000a03020d08071570a0362020d42081c8
  | 8, 0, 2 => 0xa1402850d081c70003020d081c060f7000a14020d41081c7000a03d1020d081c70000020d081c360f60a340302160d081c8000a14020d081c7170a2a032f020d081c8000a030285081c157000a62020d081c36700000a343d0d081c6000a34030d081c0670a0302270d081c688003403020d081c187000a0302081c71157000a038f020d081c70a03020d0c19081c8000a310302081c157000a03020d0807847003403020d081c0f70003020d74081c187000302010d081c1870a032f020d081c0780a032f023d0d081c8000a03020c081c1570a032f020d081c368000a030d081c068e7000a03020d081807700000a03021c251560a03020d081c18158000a0255210d081c7000a030d081c5f067
  | 8, 0, 3 => 0xa030d8d081c067003c2a03020d081c70a0362020d41081c8000a14020d081c5a7000a030d0c081c0670003020d0c081c1870a0362020d081c718000a020d8c081c367003103020d081c0f700000a030d1c2506600000302010d081c600000a1402081c156000003020d1c18256000a0302081c15897000a3a03020d080770a310362020d081c80a0302160d081c068000a02160d081c3670003020d0c081c0f700000a03020d08076000a032f620d081c700000a2a020d0871600000a03020d1a1c60003020d081c18067003c03020d081c07700000a0d081c063660000020d081c18366000003020d1c250f6000a0357020d081c7003c03023d0d081c7003c03020d081c3670a038702160d081c8
  | 8, 0, 4 => 0xa03020d081c40700000302081c150f6000a03020d08680770a030285160d081c80a03020d081c68158000a03020d081cbc7000a036202081c1570a0357020d081c6880a0302160d081c718000a03850d081c067000a03d0020d081c7000a030d41081c06700000302081c153f60003020d41081c187000a030255081c5f7000a03470d081c067000a14020db8081c7000a030d081c71067000a03d6020d081c70003020d081c187170a310302160d081c8000a0302380d08077000a03020d08073770a14032f020d081c8000a0302b30d081c7000a0302c60d081c7000a31030d081c067000a032f020d08077000a03020d8c1c257003103020d081c1870003020d41081c0f70003020d081c710f7
  | 8, 0, 5 => 0x3020d0c08186000a032f3d0d081c7000a030d081c06467000a03020d085f077000a03020d70081c7000a03020d081c7e7000a03020d1c07257000a0386020d1c2570003020d0c4d081c7000a03020d081cb17000a030d087f1c067000a03023d0d1c25700000a140d081c0660a140302550d081c8000a03020d4208077000014020d081c186000a0302550d08077000a03020d1c25367000a030216081c157003c1403020d081c7000a03020d081c44700003c03020d080760a03020d081c0706800000a03081c1506600000302081c18156000a020d081c073670ad80302160d081c8003c0357020d081c7000014020d081c0f6000a038a020d081c7000a03d7020d081c7000a03020d0807397
  | 8, 0, 6 => 0x3020d081c136000a57020d081c367000a03023d081c1570000030d081c180660a03020d70081c688000a0302081c15367000a03020d081c2d7000a03020d4c0807700000a14020d0c1c6000302160d081c0f7000a0302380d081c70000030d081c060f6000a0357020d08687000a0390020d081c7000a3403020d08077000a032f020d081c70a3403020d081c158000a03620d081c067000a0323020d081c7000362020d081c18700000a030255085f60a03020d42081c1880a0302550d081c188000a2a03020d1c257000a0377020d081c700000a020d4b081c6000362020d081c0f7000a14020d8c081c7000a4a030d081c067000a032f0241081c70a2a03020d081c0680a0362da020d081c8
  | 8, 0, 7 => 0xa03020d081cac70a0362020d081c368000acf03020d081c7000a3103020d08077000a020d081c18367000a03020d22081c70a032f020d081c688000a0302550d081c7000a03020d0c08077000a2a0302081c157000a032f570d081c7000003024e0d081c600000a03020d07256000a030d8c081c067000a038b020d081c7000a03020d1c2515700005303020d081c6000a0357020d1c257000a14020d081c077000a1486020d081c7000a14023d0d081c70a1403020d081c068000a03020d0807067000a03160d081c067000a03020d0807827000302160d081c18700000a020d08073660a03020d081c15068000a0302081c07157000a038602081c157000a020d081c15367000a03020d081c687
  | 8, 0, 8 => 0xa2a0362020d081c80003020d081c18077000a033d0d081c0670003023d0d081c187000a5751020d081c7000a030d081c063670003020d081c1836700a503020d081c187000a0302100d081c70a032fdb020d081c80a03020d0c081c188000a032f0216081c7000003020d081c1e6000a0302160d0c1c70003020d081c070f70a032f02550d081c8000a0302350d081c7000a03020d74081c7000a0302010d081c70003023d0d081c0f70a1403020d41081c8000a03020d1c18257000a0302850d08077003c032f020d081c7000a03020d41080770003020d081c360f70a0362020d081c0780a0302850d081c158000a03570d081c687000a03020d08710770a0362020dd9081c80a0362023d0d081c8
  | 8, 0, 9 => 0xa03230d081c6000a03020d8d081c7000a0302081c18157000302554e0d081c7003c0302550d081c7000a03020d081c067000a0357020d0c087000a03020d081c82700000a032f41081c6000a2a030d081c06700000a020d081c366002a03020d081c187000a0302910d081c700000a14020d08076000a14020d081c157000a0302081c153f70a03020d41081c188000a1457020d081c7000a03020d4c081c7000a140302081c1570a0302550d081c68800000a030208071560a038602160d081c8002a03020d081c0f7000a0387020d081c7000a03020d081c1270a03023d160d081c8003c03020d081c687000a035702081c1570a0302160d081c368000a030d081c07067000a03860d081c067
  | 8, 0, 10 => 0xa31032f020d081c8000a0302160d0807700035752020d081c7000a14030d081c06700000a030d0807066001403020d081c187000003020d08180760a340302550d081c8000a020d081c68367000a030d081c150670003020d081c18157000a14b6020d081c70a032f020d0c081c8000a03570d081c067003c3403020d081c7000357020d081c187000a032f020d1c257000a0302470d081c7000a03020d0c08187001403020d081c0f7000003020d08070f60003020d081c150f7000a0302081c15bc7000357020d081c0f70a03020d0c4d081c8000a0362020d0807700000a03570d08686003b03020d081c077000a2f020d081c367000a03020d081c4370a0362020d081c158000a14020d081c187
  | 8, 0, 11 => 0x3c3103020d081c700003b03020d08076000a032f02081c157000a03020d1c5f25700000a24020d081c6003c03020d0c081c70a0302160d081c188000a03020d421c257000a0302550d1c257000a03022b0d081c70a03020d081c5f068000a03020d19081c700003c03020d1c256000a020d081c5f367000a030d081c18067000a0383020d08077000a03020d087f1c7000a03020d081c5a7000a03020d081c8970a0302550d081c068000a02550d081c3670a030255910d081c8003c03020d081c06700000a0302081c15600003c020d081c3660a03020d0c081c688000a03020d8c080770a032f020d081c718000a037d020d081c700000a51020d081c6000a03020d1c68257000a0302081c15a77
  | 8, 0, 12 => 0xa03023d0d081c18800000a02210d081c6000a030255081c15700000352020d081c6000a2a03020d08077000a020d081c0636700003c0302081c15600000a030d081c066000003020d081c1860a3403020d0c081c8000a030d081c067e7000a14020d081c687000a3403020d1c257000a0302ad0d081c7000a0386020d08077000a0302081c681570a030285550d081c8000a03020d081c887000a03023d0d08077000a34023d0d081c7000a03020d0807367000a03aa020d081c7000a0393020d081c7000a03020d1a081c7000003020d081c3f600000a03020d221c6003c03020d081c7170a0362020d081cb18000a142f020d081c7000a03020d081c587000a030d081c06497000a1403020d0c1c7
  | 8, 0, 13 => 0xac103020d081c7000a14020d42081c7000a03020d1c25067000a0302920d081c7000a03020d081c2c7000a1402550d081c700000a020d1c25366000377020d081c18700032f020d081c0f700003c14020d081c6
  | 9, 0, 0 => 0xa030d081c0660003020d081c1860003020d081c0f60a0362020d081c7000a14020d081c6000a0302081c1560a0302850d081c70a03020d41081c70a03020d081c7170a3103020d081c70a03020d0c081c7000a03020d1c2560a03020d081c067000a020d081c3660a3403020d081c70a03020d081c5f70a03020d42081c70a0302550d081c7003c03020d081c60a03020d081c6870a032f020d081c7000a03020d081c60a03020d081c1870a1403020d081c7000a03020d080760a03020d081c1570a0357020d081c70a2a03020d081c70a03020d081c0770a0386020d081c70a03023d0d081c70a03020d081c367
  | 9, 0, 1 => 0xa03020d8c081c70a0302160d081c7
  | 10, 0, 0 => 0xa03020d081c6
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 36
  | 5 => 52
  | 6 => 60
  | 7 => 68
  | 8 => 68
  | 9 => 60
  | 10 => 52
  | _ => 0
def stateM : Nat → Nat
  | 4 => 0xfffffffff
  | 5 => 0xfffffffffffff
  | 6 => 0xfffffffffffffff
  | 7 => 0xfffffffffffffffff
  | 8 => 0xfffffffffffffffff
  | 9 => 0xfffffffffffffff
  | 10 => 0xfffffffffffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x3fffffff0007000007e7003800070e600700e0c00000e01fc0ff1e3f0038fffff818ffc7003fffffc00000000000fe1fc0ffe03f0000e01c00f8003e003ffffc3f18e1c60007f07fc7ff00ff0000e01c00ff003e0038f19c38ff1f3f003ff0003fff000000380f803800ff0000070e63c700e0c0003f1fe3ff00ffc1
  | 1 => 0x38f19c3818010600000003c00000000000000000001e0000000003c0e71e3900380003f80000000000e01c00ff003e0000000000001e0000000003c000000000000fe3c000ffc10007ee7c07f8e0fe0038f19ff8ff1f3f003ff01c3fff003e003ffffc3fffffff003f1fe03f00e1c00007ffffc718ffc70038000038000000
  | 2 => 0x3f0fe03f00ffc0003ff1fc3fff1fff0000000000e700000000000000001e0000070e6007e7e0c0003ff003ffff1e39003f1fe3ff00ffc10038f19ff8ff013f00070e600700fec000380f83f8e7e139003f1fe3ff07ffc1003ff0003fff000000380f803800ff000000e01c00f8003e0007000007e70000003ffffc3fffffff
  | 3 => 0x38f19fc000000000070e603fffffff0038000038000000003fffffc700e0c0003fffffff18e1c6003ffffc3fffe1c6003ff0003f180000003ffffc3f18e1c600070e600700e0c000000fffc000ffff0000ee1c00f8e03e003fff803fffff000007fffc07ffffff00070003c7000000003ffe603fffe0c00038fffc38ffffff
  | 4 => 0x7f07fc7ff00ff00070e63c00000000000e01fc0000000003ffffc3ff8e1fe0000efffc0f8ffff003ff07fffff00ff0007f00007ff0000003ff0603fff00c00007fe7fc7ffe0ff00070060070000c0003ff07c3fff00c6003fffffffffe1ff0007f07c071800c6000700000700000000000e000000e0000000f01fc0ff003f
  | 5 => 0xe01fc0000000003f1fe03fffffff0007ee7fc700e0c00038118038ff1f3f0000000000e7003800070e6007e7e0f80000000000e0003800380f83f8e7ff390038000038e7003800070e63c7e7fef90007f07fc0000000003ff003c000000000380f83c00000000038000038e700000007f07fc7ff00ff
  | 6 => 0x3f1fe3ff07e1c10000f01c38ff1f3f00071fe3c700ffc1003f0fe3c700e0c00007f07c3fff1fff00380f83c000e0000007f07c07181ec60000000000001e00003ff01c3fff003e003f1fe3ff07ffc10038f19c3fffffff00381fe3f800ffc10000ee1c00f8fe3e0038ef9c38f8ff3e0007e01c07ff003e0038f19c38180106
  | 7 => 0x7f07fc7ff1eff00000003c0e700390038e01c38f8003e0000000000e71e3900000e03c000e00000000003c000000000380003f8000000003800003800000000380f83f800ff00003f0fe3ff00ffc000000e000000e0000000e01fc0f8003e003ffe63c700e0c0003ff003c70000000000000000e700000000e01c00f81e3e
  | 8 => 0x38ef9c00f8003e0007f07fc00000000007f07fc7ff00ff00070e6000000000003f0fe03800ff00003f0f803f00ff000038018038001f0000071063c70700c1003feffc3ff8fffe003ff0000000000000380f8000000000003ffffc00000000003ffffc3f18ffc600380f803800e100003f0fe03f00ffc000380f83f800ff00
  | 9 => 0x38e01c38f81e3e003f00003f001e000038e00038f81e380000000000001e000007ee7c07f8fefe0038e01c38ff003e0038ef9c38f8ff3e00000e0000e0fe38003f1fe03fffffff00070e600700fec00007ee7fc7fffeff00000e000000fe0000380f8038e7ff000038000038001e0000000e000000fe00003f0fe00700e0c0
  | 10 => 0x3feffc07f8e0fe003fee7c3ff8e0fe00000e000000e00000381183f8071f01003ffe600700e0c0003f0e603f00e0c00000000000e71e0000380e003800e0000038f00038ff00000038000038000000003ff003ffff0000003ffe63ffffe0c00007ee7fc7f8e0fe0038ef9c38ffff3e0007ee7c07ffe0fe003f0e603f00fec0
  | 11 => 0x38ff8038ffff000038f01c38ff003e0038e19c38f81f3e00000003c0e71e39003ffffff80000000007ffffc7ffffff003f0e603f00e0c00007000007000000003f00003f000000003ff01c000000000038f01c38ff003e00071e63c707e0c10007e01c07f8003e0038e19c38f81f3e0000000000e01e3800070e6007e0fef8
  | 12 => 0x3ff003c0e71e390007fe6007ffe0c00007f003c7ff1e3900000003c0e7003900070063c7e71ef900000003c0e7003900070e63c7e7e0f900070e63c0e71e390000e01fc0f8003e00070003c7e71e390038ee1c38f8e03e00000e03c0e7fe390000e01c00f81e3e003fff803800ff00003ff01c00f8003e0038f18038ff1f00
  | 13 => 0x7ee7c00f8003e003f00003f0000000038e00038f8000000000e000000e000003ffe7c3fffe0fe003f0fe3ffe7fff90038ef9ff8ffff3f0000f01ff8ff1f3f00071fe3c707ffc100070e6007e7fec00000e01c00ff1e3e00380f83c0e71e3900380003f8e71e39
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x3f7befdf002f7c4e6fefcaba00274e68a729e4cb001bf7ffdbff7fff001083b190103545003fffffc084102000243e066484e4200012e55c52f843be0036cd583618c1860003706ec3ad00eb001bf77edbff6fff0010811018520b14003ff8023fff8800003c8f913c52ff14002f7eefe7adf4eb0024088124009000
  | 1 => 0x1183309131254d000932a7c1a53469001bc7f99b7b7fdf000932a7c9e73e79003dbfb7fcd6db34001bf55e5bff4bbe0018879118527f14000932a7c0841020000002a1800034410037ef7cf7f9e7ff0018b19758d61b34003ffd5e7fffcbbe0036cd583f7befdf0024080024008000000242e9820834c3003c8d103c52cb14
  | 2 => 0x3fcff9bf7bffdf0012c1581b7b0bdf0009322289e72c49000902a189633e59002f7e6aafefeccb003ffaa7ffffbe7900240aa1a400b4410010b11650940124002f4ee9af6bfedb0035bd36f5b5c16d002d1aa3ad07bc41003ffa22bfffac49003d8fb1bd73ff5d0013e77cd3f967ff002f78022fef88000036cd583e5acb96
  | 3 => 0x18b1974084102000274e68bf7befdf003c88003c528800003fffffe7adf4eb003ffffff69cd1a6003ffd5a3fffc9860036c800361880000037cf78b739e5cf00264c482608c082000007fdc00077ff0036ef5c76f8e7be003fff933fffff1400024558032967df002f7aa7e7ad9020003ffe6abfffeccb0010855818526fdf
  | 4 => 0x2704e428c00a2002f7eefc0841020001bf7ffc08410200036ed5c76f8c3be0012e7fdd2f877ff003ff86effff88eb0003700203ad0000003ff86abfff88cb00277e6ee7ade4eb00034068832900cb003ff84a3fff88820037fd7ef7bdc1ef0002404802080082002748002729800000240e002400e4000000300640840020
  | 5 => 0x1022081212449001bf7ffc3ad74eb002408003c528b14003fffffe7adf4eb0000000018520b140009300649e70a38002f7e6eefefeefb00012224c1e12679003dbfb7fdf7ff7d003dbd167df7cb3c002f7eefefeffefb000b72efc0841020003ffaa7c0841020003dbfb7c0841020003db8023df788000003726ec3ad24eb
  | 6 => 0x251822a50580410000000018520b14000002a180003441003fffffe7adf4eb000240481a5a0b96003dbfb7e5a5f469000a42c90a4a3e920008028108423e10003fff7effffefff002c18832c069800001081103f7befdf000002a180003441003eefdd7efaffbe003eefdd7efaffbe003ffd5e7fffcbbe0010811010100104
  | 7 => 0xb72efcbef3efb00013026c1a50069003eed5c7efacbbe0001022089632e59002d3ea7e484f4200008308740841020003dbaa7fcd69820003c8a813c529800003dbfb7fcd6ff34003fffffffffffff002c0e812400f400001bf7ffd2fc53be003ffeefe7adf4eb003ffaa7e7adb4690009300209e70800001ae7dd5afa7fbe
  | 8 => 0x3eefdd52f853be0003706ec08400200013f57ed3fd43ff00274e6880000000003fcff9bc52ff14003fcf913f7bff140018819118521b140001102281050041003feffdfffbffff003ff80200840000003c8f91000010000036cd5800000000003ecfd93e5aff9600348d103410c104003ecfd93e5aff96003dbfb7fdf7ff7d
  | 9 => 0x3eefdd7efaffbe003fcaa1bf7bbe59003eea857efabe380008008108421a10003feffdfffbffff003ffd5e7fffcbbe003feffdfffbffff002e6ecd6eeafeba002408003f7befdf003fcff9bf7bffdf003fffffffffffff003c8f913c52ff14003dbf933df7ff14003c8a813c52be10002c0e812c42fe10003fcff9a729f4cb
  | 10 => 0x3feffdf7f9f7ff003fef7cfffbefff00348f103450e7140008108308061800003ffe6aa7ade4cb003fce68bf7beccb0009328309e73e10003c8e003c52ec000018b00218d60800003db8023cd68800003ffaa7ffff9820003ffeeffffffceb003ffffff7fdf7ff003fffdf7fffffbe003fff7effffefff003fcee9bf7bfedb
  | 11 => 0x3cbf933cd6ff14001af55e5afe4bbe001ae5dd5afa5bbe0008308748c61a30003ffffffcd6db34000372efc3ad34eb003fcf78bf7befdf00274c482729c08a003fcd583f7bcb9e003ffd5e408400200018b11658d60b3400275e6aa72de4cb0037ed5c77f9c3be0018a19558d21b340008228548e23e38002f6eedefebfefb
  | 12 => 0x3ffaa7c9e73e7900277e6aa7ade4cb000b72a7cbef3e7900093026c9e70869000b72efcbef3efb00013226c1a5246900277e6ee7ade4eb002f7eefc9e73e79001bf7ffd3fd77ff002f7aa7efefbe79003eef5c7efaefbe002d3ea7ede7fe79001be7fddbfb7fff003fff933cd6ff14003ffd5e52fc43be0018b19318d61b14
  | 13 => 0x37ef7cd2f843be003fc8003f7b8800003ee8003efa880000264e482628e48a003fff7effffefff003fffffffffffff003fffffffffffff0000300658d60b34000112a381053441002f7eebafeffedb001bf7df5bff7fbe003dbfb7c9e73e79003dbaa7fdf7be79
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 221 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem wd_0 : ∀ i, 0 ≤ i → i < 128 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem wd_128 : ∀ i, 128 ≤ i → i < 221 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 93 128 = true)
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 221 → wireDOK i = true := (range_split wd_0 wd_128)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 221 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 221 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0xff) :: stateWiresD n (ids >>> 8)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0xff) :: stateWiresS n (ids >>> 8)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 11 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 4 => 5
  | 5 => 98
  | 6 => 1336
  | 7 => 3139
  | 8 => 362
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x9b88d956894765b9494a64a320966f4d1f70a5ca
  | 5, 0, 0 => 0xa3e576629db324b49d608d9a9a165c2f9974e37796ecb30c905d99848f758a308e943f2e872c26bc86aafb0685c674f6839c761e7ccb8c677caba1bf7c25010f7bcc461a7a63810d76de688b75fa9454740023616a01a3f668cf076064ed1e8d6191b08a602844bd5ff311425fd15d6a5e7831665e3cf58c5d5267e35a50f3fd591be40d57727ce657564b63525eb23951c73e0e461f393e429f800641939e7c4006147f3f94c9c83c3e27bd3b6354cf3a3d8b4c38ef0ab7347c6e463274f69d2f7ba9282ecaaba12df4745925cfc22225115712203f046d1d3c7be41b443d1318a6b4ba15e6c85514c0fed20cf151e40b44a66407baa5d00332ded701db06ca
  | 5, 0, 1 => 0xff7eab06ff2888b8ff274fc6fa1fc206f6538273ef834cdfea6d2edce775c43de6b4230de55337f2e49e62c3e26ea9bbdf01660ddddb9c8ad4bbae8ad12509fdc8b658cbc89948bec7cabec7c52b5fbfc1931029c004fde1bf0606bbbd08ea0fbb50a6b9b655bed8b500d656b3b83a25b3116c4bad06f094ab650f4fa9049208a894edfba729f996
  | 6, 0, 0 => 0xf2143400f0a2ca10ef250a40e2146200e2015620e133edf0db3e9320da7da1f0da501c20d393ad40d2f6b050c76b2fc0c4dcae50c13b4490bfc7ea50be2fe130a7964bc0a34a7db0a1efe5f09e1d42509964555097f42550979a5d3093f465f08b23a3a089328f208707bd2081dc83407f966dd07936aa70751eef80737ed1e06e9b71106c502ec06b678d00604c1e905fcea2e05c8263805a770920592c42b057afeb2054fa6b30544534b051cf175047e0575043b3177040aaf0b03dc99790330b35302f53f7802d338cd026bb60d0242a9bf01ea01900141aa9e0114ff5d0104b42a00f3ed6a00deb03800a0b27c0063d605006230790046e4ed0043b3aa
  | 6, 0, 1 => 0x1afcd8c41af080381ae554351ad371ee1aace10f1a97ec0a1a81704b19f56e3a19b22bfc19a4c687198b6f95196a7d07194947e118c74daa189598ee18917f94184d71d4181b10ba1806661017f732c317e5a7ad17cad52517a479a217802805177d348c1725d81c170095b51658ec56163694bf1616c3731603466915ec3cf415d9e97b15955e0d1561834a153dc90f14b3ba6d14aafd541492d8731461d1371435387413f811b913f7b96e13f2ead713f2479513c88549139343331384e2cd13810b82132809e3131418ed12edb17312cf5422127163cf1216ea1b11fdc217116e72a110edf202107400661030c4820fc8287f0fb963250f6b3e1a0f27dc14
  | 6, 0, 2 => 0x2541ede1251da8c7250a180f25007fbe24f2dcd2248ff59e245f9d952402d8e523d9945d236e59fc22d8472522c3483722a6ff06226a08922240840b223f994722280aee220b916f21f40ce021cd2a9421c92a6d21a84b1b214c46682104964220e8daf220cd4b0e20a69e8e209150eb2044b2091ff2102c1fe4f8cf1fd528dc1fd400841f7006e31ef99aeb1edeee741ec641401e5d01b71e111b2b1e10b40d1e06cafd1df565bf1dec53cd1de53bb91dcbf19e1dbdb0fc1d995eb21d98e2a11d7550671d73e1421d7011b11d5af3161ced0aba1cc1e90f1cc1c7601c46ec571c46abd31c0f791f1beae75f1bb300dd1b75dca91b30e09c1b23da351b090e0b
  | 6, 0, 3 => 0x329f8c5832600aa6325beb0131af297231ad60fd314fc4ae3135af8d3112c04d30c7870c30b17a1b2f3679eb2f1607bd2ee197fb2ece18e22ecaaba12ddc07642dd6a17c2d7eac952d75dabd2d74721a2d1587ee2cee35d32c6ef2492c534feb2c05dd8b2bf9805c2bc33d232bae3c152bad0b982b80b0652b4fd7bb2b37d2ca2b1b09a12af940482aeb8c242ab5e3102aa750422aa5d5152a4abc0b2a410c0329cb842329b322d129a15c2129347f3c2906a23328c1a2d828aa928d282a575427cad47a27c09a0027a2b1ad2760319a272cd589270cc4fa26c1d59326af0876267a6689266f1ae826118be62606cf4325e96bd025c4bd0325a631e7258dd428
  | 6, 0, 4 => 0x3ec8cdfc3eb3446d3e51fe3b3d7b1e3a3d55aa833d4337b83ce2c1c13cc117773c2882643c153f903bf6c37b3bf368d73bd5ac933bd3c3913bcfa0093bcc4b8e3bc7d7653bc2caa43b5c06d43ad4551d3aa310ec3a7cd14d39f86a3f39f7395239f7390539f6d3fc39c880d039b9eed639a69867396aa3ac394afc1539433a053942b7f439103ed738d4220938cb0ba0381f33b937f77bf937c8003637ad796c379be9273793ffe73771214f3747122336e3f78436d19d76366db46a36487ed23625c58f36190ed535f050a635846d3734c9e94434bd92e334702ab83459db523456a4b43434fb9034076c2133fd04f033db68163395d72b33259e9f32b5e9b4
  | 6, 0, 5 => 0x4b5b711e4b4d31944b489ba64b42e60a4b10427e4ae3c8134ab4911e4a92ee044a78a57b4a646a974984fe9d493142284926b51048a662ee48986f36481b4fe548145cde4802432547af81c047aa693847a70187463a036a45dde1b545d34bee45c4f1fd45b84e3845b253f145927097459250e34572b473454a1d3e45280def45097fb844d3ae64446607d343cfd02243a4edaf439cf8a64370e5d7436b52c043596148433fa33f4323f83b430cbdea42a90e5042930919427645f24273376942410deb41fabde641b6d14d4147a92b41204cd84110d8f141034766405380cd400e1f75400d3fc93fff77f53ff7364d3fd129013f72cf1b3f5c92733f304adc
  | 6, 0, 6 => 0x58afb4c057e2b4eb577424145755a50e574cd6fe5745e0fb565b5541563267f655e38e7955e32f63559b0952557f5c9155519d35554cf0e8553d4b085537577c5533c7ce5531f46654c5c28654ae798154703f9a5457bc6f545731af542334c0536156065318a9a352e1023b52d4575d52d25c0652b5191652a34a4e52986325523afa0352378dbf5217357951f280be51c4354c50f2cc3e50c31e4750ac6bf35088ef99504d5df4502e5936502841ac4fdecd1d4faa861b4f7ae5254f5d1f694f5a6fd74f4953c84f408a4a4e7adc564e5e7bec4e57c79e4e4076434ddfaacf4d947f0c4d924fd04d65da604cff85024c34f37a4be0850a4ba07d3a4b7caab0
  | 6, 0, 7 => 0x64f83f6464f0602b64d4253764cc06b764a033556493b3bf64894ca36452eb0d6443ad1c6403483a63d013e763919d55636c94f6632c349262f4714e62ec9c33628524866284d23362762d5962751467623aa496620fb26661eebeb561ede05661e11a9461898ec761514756613b072560e1902460c081b7605cf9926014a9d05fbb14d15f779d215f08e9625e8b8a475e76b1a75e3978aa5e342dd75e0907835dab634b5d9e8de65d319ff65cf2b5ff5cb1fe155c8e153c5c86ba0f5c777a195b6d6f735b2ea5385b29ff8d5acff8145acbc8c65aad18295a8ebb725a59ee845a3b12535a39767159faf6fb59d57e4359d2d7795971727458c3b61b58bcfd23
  | 6, 0, 8 => 0x6fd703756f8372c46eaa40976e1997f16e02eec26dfb84766d8e89fd6d7530a76d3fbd626d3734606d1524fe6d08e4c86d06dcfa6cb8159f6cb285fc6c7981376c76c0d66c01328d6bed34936baf4b8c6baeec006ba26c6a6b96eb706b0a9be56aea53056a8cb2b46a7b4da16a3b0f486a34649d69f85bab69b7b87869721eb3695da308694fe00668ea44c0689eda7668942dae68237a8a679b87ec677fee3067734ea9675864666743361d6705ed8c66af71a666a2e62266750f09666677fc665b6d836650058b664ccf8566427f576640782b6617a20d661467a165f9eeba65e1617a65d496fb658e4a6a6557daac6549d529653d59ad653cf3796535248a
  | 6, 0, 9 => 0x7bf792ae7bd83eff7b958da57ac8168d7abfddae7aaf07167aa94faf7a9e42ec7a98c0657a79b1197a6c593b7a474d4e7a1405c779bf63cc79951c5e79830649797ec6d1795ab038794516e87941a5c67933afc27931f25d7898807c788d557a7863c8f57859c91e78371883782f5f22782d4e62781f4d6577e07d2377837e8676d0ccd076b6f19d769f98727691fc8e76654281764d3db5763fda8e75b43ce2759ba135756fab21751dd97f74bcc57d748d5d87748c0bfb74806490747a456a7423dda973e5ad147357d526732989b472d250c972bc591a7289d0a0724b0e4171a5d5af716d67677148d40e70d0c12570827dc470800c2c701c39856ff0f014
  | 6, 0, 10 => 0x87475200870de19f8704825686fe16d886946032868e1944867bf6978676de0f865ef8c08655b493864aef5b86497357864281b1862eae4f862144cc861f705e85daf65585d9713b85c53f4a858c35e68577d8858562ceb684fccbd18485fe988464003e8451f09b843e7a33841d1a0f8402af9383a84ed48354131d830853a28305193682e2922f828431898246e48c82079cb081f06d1281eb2aab813734568106bffa8103242c80d6d68b808b5c6f8085455380674d8980153bec7fefa5537fdd4dc87fbb75a27facd5a97f7560957f5540ab7f2cd48f7f21c20d7ee125037e94e3447df369a47d30f82c7cd063437cc317d07cad3c347c4604c37c12f7dd
  | 6, 0, 11 => 0x8fb6ae6b8f78e0ca8f47da7d8f218fab8eda850f8ed9aa9e8ecd08e38e9116618e6a85208df10bf98de53a338d8aaf428d59a8068d311de88d1440688d07c0d28ceac1a68ce1a1a98c95ff338c8a39e78c810a2e8c43327e8c3cd7b98c0b847c8bea21d78be0a2098be05f688bcf7f028bc52ca88ba67bbd8b9ab91c8b937bba8b8de4ab8b7137ab8b14aec48af066f98ae4c2aa8a912d0a8a7a9db88a7a9a9d8a65e23c8a19a66b89eeaf3f89cec5d189b348c0897a909f8942d758891bddfe88d5906188d38f7788c0b2fc88ad1ada88a39e3188969a2488931dff8888c9e788517374881d533b87f329e787b05a3d8781cbe3877cf67587755c36876bff36
  | 6, 0, 12 => 0x9e8764349e6b8cd49e5b2cb99e5142a79e50829f9e3c3eec9e1ee3bd9db402419d87cc6d9d2cf5e09d082a5a9cdd57e49c81fb169c1eb7a59bd345fc9bbbe39e9b5a8a139b24b8349ae376b29adefea89aaf153999e0b1c1998bcfd199494fbe98e7c85698a06f229816278597a8008a97a78488978f500b9726496296f05b2496c7b6a49690e4419615da8395b99e2f95b5954c95b07dad959b238995893211957a8657956cd1a7955bd4519530668f94c4131e947799c79474301b946ca34093caa97b9391693f934bf6d8933cb47192e5915892411eb092190231919ed0dd918c056c912f1e399124d90190bef595909947df903b17da900f94ff9000e36c
  | 6, 0, 13 => 0xab28508daaeccdecaabd402daab74b74aa7b60d7aa6ee141a9c9b04ca96993e6a96124b0a947c278a93db95ba913baa0a8fc3611a8e82b79a8afb0eca8a0587ca898adeca880870ea8319cf6a7ed6f8ea7c87262a7b6b997a789e769a7283310a6b9e057a6af8239a67ba414a6660a9fa665e267a65948dca63fc380a61e19b4a5fa39b5a5e717a5a5da4240a5c1ad00a593eb99a58b349aa50f2b4fa4e416e4a4e0dc78a49448e9a4350491a409ce84a338e2d2a2e2833ca2e1e74ba2b299cda236ab55a20ef395a206c1e6a1f7135ca12d0ed1a09a887ca0935a78a0852085a06e9f57a0548a369fae04fb9f67cab99f6427a59eb63d339ea23fe29e950e89
  | 6, 0, 14 => 0xb4697fa9b4458a1bb433f8c4b4241aafb41db11fb41532b5b40655c6b3f4c573b39bb7a3b399b234b3995386b34136d2b30c70b4b2aa4fc4b28a2d69b28409e5b2447a99b23b10d4b219bac1b1ee9db2b1b5697bb1854138b0d5c66fb0b62913b0602e91b04a7997b03ee8f2b03b1c5fb022220fafc5c62faf885bf3af8085e6af16d433aef003aaaecbdfe5aebefc6eaebd64ebae90be8bae7a07f8ae4c6ec9ae1d15d4ae158a96ae118d04ade53914add60807adce3011adb0f589adb0c883ad76b56ead70d8e4ad2cd25fad1a0d32acf79d1bacebf229acb1c5abac9ab39cac420587ac41a57eac1ef04faba30cfaab67c6c6ab51fd75ab36576dab2d1fe0
  | 6, 0, 15 => 0xc1bd5cd1c1438dfbc13d5ef2c0d41187c090776dc072ccddc06edd81c0577498c041544ec01b919bc00bab3abf9bab35bf5e33cbbeee9473bebd2cbbbeb25be4bd73983cbd5ddea2bd1530febd026363bcf879d7bc90b0a3bbf7cea5bbc01f92bba0c856bb9e65c9bb9cd81abb8eba4bbb57f7a1bb53afffba8ba045ba787e02ba5fe039b98347cab90d54f2b90b7cabb8d94b03b8cdd117b89e50edb864725ab82d731cb8012f85b7f49589b7edea51b7ab1b3cb75aaf37b71ef297b6d0b723b695905db6811421b64ff35db64f25f7b62d3a6db621b6e4b61a0171b5f51029b5da9890b5a41b76b574c2ceb50708b9b4aec9a4b498b21fb48889eab4737d18
  | 6, 1, 0 => 0xcfe0f2a3cfdf5c60cfa9f353cfa2773acf54d149cf338479cf25d8b5cee37e53ced9ef7acebcaa6dceb7aaf1ce9226c7ce8d2592ce6a62a9ce5b24b8ce532d8fce2f7354ce1dc8c9cdc5711dcd5d8b38cd43e092cd2f9a87cc8da4f5cc654c7ccc2ae1d0cbea39cccbb7367dcb7a44f6cb69ff8dcb4ccfeecb0b5e96cb094b6dcad7f953cab7206bcaacd43fca58b31cca4d7fe1ca2c216cc9c932d0c9baad68c92eff1fc90fa1e4c90a0ef3c8b74ff0c8a301e3c80053e6c7fdac92c7c29014c7a20538c75f8e1dc6d2b85ac62e2f28c5342b32c52d8b3ec47cb834c4229849c3d1778ac3b3b1e9c3970f0bc3573493c30fb78ac2d474bfc1ffdce4c1cf4e49
  | 6, 1, 1 => 0xd9b5441ad973e9e3d959ecb5d959e9f1d9548351d92abdecd9106fa4d8c0bedad8ad2698d8ab7867d80cee5cd8014eb1d7fb8f7bd7b49524d73fecf8d720f8acd708d53cd6d6f04fd6af5112d68a8ce6d6747561d6564c73d618aa29d5e80059d5d6d97cd5c6639cd5b4d3bbd5757576d56e92dbd56baa2ed51552b6d4c767e0d4861306d43a869fd3d6fe7ad3cf3014d3a4eef8d3a0653cd391183dd389964fd353c2f9d347ade0d2b65212d2555ac5d22a6399d21c0541d1bd3a4ad1bb8cead1b8f7efd1b33d20d1b05fc9d1abd76dd169122dd168f0afd11892ced0f7075bd0a9a204d09966ead08d27ced061bba0d057efc7d03db7cad03781bdd0006acd
  | 6, 1, 2 => 0xe7e8f3aee7772d12e707d935e6c4b3d0e629b85fe5c53e3ee5bae8d3e5a7b643e5565f86e544824ce542f83be53fdc1fe4e943fce4bde241e4ae2957e39955eee3963e6de27e1392e2590ed6e23acc48e2262981e20557a9e1fd7feee17cf3aae1776e77e0cb9690e0c038e8e07b7668e06e8c87e051dbdfdfdb3933dfbcf27fdfaec4dddf951334df66fd53df64590bdf3a5626df247d40dec3330adea38397de78a559de6f49b1de67b7cbde4ed410ddd391e7ddc09bfeddb5f185dd82b20adcf04b12dcc9e4eedca5d980dc7dac72dc646bc5dc240b61dbcd1d99dbb918f5db7af8fbdb242495daead60ddae5b725da6a9860d9f9fb5ad9dcf7f4d9da8537
  | 6, 1, 3 => 0xf5ea5b7df5b269c8f59f1446f59b39d5f5806b80f56a71faf55337a9f47d59d8f46e50dff389f601f33da2c7f320e152f2d2ca9df2b71531f2aa9b9bf2aa959bf28cf32df239b644f1dc4090f1bcb5e5f199fc3ef17e3a7cf15296c4f10f47bbf0f66ff4f0986daff021fed5eff26df1efbe06a7eec41fbbee983d24ee73db6eee5f85e2ee530286ee21d76eedc5d5aced5e15c5ed5744d5ed2e695fecf91666ecb1adebeca2d76cec903820ec878170ec4e94caec40f0a9ebcc16ddeb9cda82eb3293cceb1a9bc8eaee4e27eaeb6526eaa71707ea66e420ea176e26e9fabb05e9f4c564e9f356bae978fceae9141054e8fa658ee836ca65e7f44a52e7e9b955
  | 6, 1, 4 => 0xff91fdf3ff844943ff6eefbcff414a26ff0d80a2feaf165afe8ba7b7fdf9659afdf4a2a0fddb4d95fdc9d080fdc4a1a4fdbd7d26fd895fc9fd56bc3dfccde0cefcae2c90fcaae456fc813e75fc4b0b8dfc43f5e7fc2a5379fb6d2ecffb557527fb2c06dafa901254fa7bb076fa710833fa6801cff9f5fb7ff9a8b337f9561b58f9551d5af914bcf6f8e7657ff87d7e56f84d177af8245b74f80da098f805289ff7d668baf7cf2a9ef7c24833f79096fdf760f6a9f74b216cf72bb804f717ebb4f6f91945f6b5bc52f69881caf62cbc48f61b6f81f61649e1f6019973f5fa0ccc
  | 7, 0, 0 => 0x5f6b71805d62b2705d2cb9505b329cf05b2eac5058f39b4058c7df80583d1110564049705555b1f05406a460533590b052b8f9904ddb57304d064d10494925f0489cb8d047346790408fbf90402805803f53a5403af162503acc1d5036514f10342ee7a0335143e0331cac60303e9c302e42d5302a7bb8302a7a996029a3e050298e12a028e48480285f2df0271efe80259961902463e470244bc38023e56a50229321f01dfe0b301cdedf301be086c01b60d15019f51af019520ef017d5a38015f4010014ed35201271ba701189fc60104b42a00f26ece00d64fc300c2468b006e43f500503e4c003649a000252651001c45a1001528ba001167ce0010041b
  | 7, 0, 1 => 0xb24a2690b236e970b0d59c30b0d46330b0965080af1588d0a75aa570a6346a50a61674a0a5db90d0a51d1c70a5133e10a4ca9000a49c2db0a3a77c00a200d4a0a1018a80a0eeb5709e350fe09d10c45099deaf40993718c097d9607097a53e009684ec4095537f909426d5e093426e0092d9a5f0918ed40090b2c3008f88e9108e3b35808c04d1d0883b66b087d4564086df8bb0869cb9a085d519a0828fed7081475360812e9d208028ac807d4482407cf1bbc07a1618d07983db607852a5a0756b2e107540f08073325e0071ebcc6070b6e270702eb1b06e0c14b06b2f97806a9d42c068d4b130682030e0672c3e8063719b70634e964061286580612365d
  | 7, 0, 2 => 0x103b600510293962101cf3100fe6c67b0fdb63180fcf05c80fb89c5c0fb19ba80f9f8c4e0f88b3880f713d840f6a88660f66eb650f5e8c8c0f5896ee0f4142b50f232de10eeac9300ee047db0edabba70ecd7e060eb3ce750e86711a0e69f5e10e68f5ce0e61175a0e60322b0e5684bd0e4ce4f90e481d260e4468b30e41de8b0dfa82c30df8e8330df69f850de9ba4d0dba68b30db6ae630db3a33c0d7fc1df0d52fdb80d359d660d2f75e70d0bf7290d0b05da0d0ad67c0cfdf2310cf8593e0cd3e9650cbb9b490c9f1b370c7a40d30c7515ce0c4d96010c405b110c28117e0c1de1fe0c10da480c0ce0890c0163050bc598650bac83940b8bbf6b0b830123
  | 7, 0, 3 => 0x15907a511585bdc9155d1ba4154ef378153315f21512d6d0150c422514e6f9fa14d1b9a314c1c47914b7c4bd14a31b911460b592145be6f1145005eb141f8fdd141a49b2140ddc321405c61e13fda56313ec0a3313d693d213c54b9e13b478a213aedd491383ce791370b8f713643d0d135185f91345c7c513436006133bd65513164bbc130e7cdd12e5b16c12d9123b12d4145e12ca7d2a1288b0461264f2e01255565b12492a31122391de121c126e11c9fc5911b565ba11b4999e11a97e741194d57e118ab44a1177b9f71158bc8d1149f222112ec5f51113be0a110fc7821105561310f5763010e737ec10ace4a610987933107f4f4a1056c74b1045aef0
  | 7, 0, 4 => 0x1a3f93451a141c851a0fd8341a0a201f19ed676819d6702619b22bfc19b15e681991f46c198a853419729319196926bf195e483819570811194d07b4194bfe7119324a89191c880718f7b2bb18f4e10a18da7e6718ce2c7618b26e2218a297e5188672a2187627b3184e84e3184a9daa183e4131182077a41805cbd217cbc60d17c2485d17bd685317bc20f017a76cd417a485a0178aee8f1783d36c17749fbd1714a0de17104909170706f51702826616f8c3a616f738fb16e350de16c4ecbb16ab874c169c937016979efd1682538b167ebc1d165c88241658ec561656f99b1637db9c161b60761609134215ef008615d61f6415bf0bfb15b76b33159e41e5
  | 7, 0, 5 => 0x1fba516d1f49dc541f45831e1f2372ba1f0257501ee037e11ecab2ed1ec8714f1eb8c1751eb180c41e85d81f1e7778011e665c391e546ac11e30bcd41e2f7dc81e2098c81e1c99681e0c97d61e0c3dd11df565bf1de04d2a1dda00381dd9276e1dbf2e791da1c6791d64beba1d6292551d60bfef1d2710f51d1a31a91d1011b41d0839f91cfe81b51cf5ee921cc1c7601cbc6c011cb8e6d31c8242da1c7f660e1c711fd81c54452b1c0377111bf4b44a1bd38e271bb5a1481ba9074c1b9b06e31b8f8cf31b8240731b78160c1b77905d1b3609e11b23c71b1b0c122d1af0de741ae2adb71adb9ef91ad1552d1ac426e21a939d131a8c40601a812e9f1a76b50e
  | 7, 0, 6 => 0x242a74e02422aaa3241a19e7241418ae23fa7d6423c8cc8523bd8bf823b0b507239a85c12380f5722379a87f2371f15e237151092363757d234fd88e232fdfb72305e8be22f2b39022cfb36122cf3d0a22b427ba22a61a2122a39c5a226a089222488b21222383cc21f5914321f40ce021f0ebfc21da66e821d6d25821d64afc21c06e8b21bffba721bb080f2185dc3721677a512163001621546758214d3e8521451415212934402126b5152118d8ca210940e420c1d9bd20bd10b420bd045520b6d82820b45b6820a269f0207787b8206d00e32069571d206357f4204cfb9c202b40b22016bee32014b884201138cd20044b421ff874121fcf4aa11fc1b365
  | 7, 0, 7 => 0x2a7f6c962a7e41a82a71ab6e2a6f218f2a5f79ad2a3e98622a2f82d32a2cf1e129d34d2329c9cb4929c2baac297cc0d4297400f82935e7462933058129095e47290449ee28e13c0c28cc0ea028c3a7c328992b9b2896f2082884112e2880e0ed285eafc82841347c283f1c4d28318577280f289427d8185027bf8f0327a4a8492773e486276eca5b2730f4cd2726dd4726f1d26026d06c1026c958ff26c74c0626c65b7f263b8e072613f5a22601ac8525f197ff25c7bf3b25c5d19325c57f8825c5372925b515bc2597e2692579079a255eaa502505a2cd25044d2725029ba324ffd71f24fce11724f4abb424f1d90e24d5ba0324bff0952474a46c245dbecd
  | 7, 0, 8 => 0x2ff39f242fc8ffc52fb65c752fb4080e2fa839992fa732f32f98e1292f953ec82f8670182f775b232f2d333f2f2664432f244e602f0cc4032ef94f442ef590472ee5f83b2e94ca4f2e8270162e80ed852e7ade792e65c3952e5a07312e2cb24b2de088ea2ddc0bb42ddbe4da2dd5e4112dca65fb2d6782ad2d48cd4d2d1a98902d11b3fb2d0065ab2cfd4cb22cddb00c2cd9989b2cd48a3e2cbfb75d2c9d909e2c60eef42c548dc42c35d6762c13df762c0d41422bf3edcf2bb7e6892b9d09942b5379482b411ce62b3e9fc02b351a482b3290202aff1c0f2af61e482aeff1232ae6ef722ae3339f2ada82fe2acda32c2ac5b9242abf74ef2aa950482a88612a
  | 7, 0, 9 => 0x34bd92e334b3dda734aeaf2434a4326c348ee9a334877812346f1f54346473883428a0bd34206ca6341c5d50340e40b1340c055d33b89ba133b8069c33b2c29e33addc9633a0985b338166d6337fa1c6337098c03344a17a331102a833036e7132f008b232c4c0d932be679b3298c993326b44773268995b32681bf431eb022d31c427d731c32ec331b7265a31b30d7c318eb2df316e3c87315f0dca3152907e314f855731345a3031226240311656bb3107d3ae30fab30230ec4ec230d3ff1530d17f8130b4684030b123c530a94148308f3f3f308ead5a30888249306461c73062345c3044b910303247ff302c87ea302b6e7b302a0ae33023b7ec2ffd6961
  | 7, 0, 10 => 0x38fe1c8a38f267cf38de45a838c12eb938a1d70b3895e65338910023388ed17438879a07387cf5323872f208385e3e02382ca96f382a570f382685c9382293d1381ada52380f69e337f723b837e0382c3781b790376a4f69376907f1375454ee374b4bd1371be0213709d18b3705812c36f914db36f03f6536de02f436dc834836db17c736d7b87036ca91d036936f6836817d7636727dff36607174365b88e6364d3cf43620d17b3620a03035e94e9c35db239335d968a535d7765e35aeb398358f846f3578c84e3576bc2135747c403565de74355a85df354c0f9d353f3678352d90be3509393735017f8434f20efe34ea9d8534e922e134c730bd34c38519
  | 7, 0, 11 => 0x3e26d9273e2424c43e19f81b3e1439d73e098a5f3e0301fa3dced0b63dad5fbf3da55a963d964f053d82cf403d784cdd3d71fd593d6e98473d5db2783d4d40833d35d18c3d249fa53d1bf2473d0e653e3d0e5bb43d084ce73d0508da3ce8e9cf3ccff6cb3cbfeb893cb7623b3c83af333c83a3ee3c7bdb083c771e663c71b2763c6977bf3c5fea2a3c5cd0913c57fac93c4b2c0a3c2cf4da3c1fe1e43c0b8a543bed95723be696503bbd9fd83bbb8b303ba453603b7409fd3b22fa393b1fa0fa3b0fb3493aaf31163aa0418d3a99cd023a8e31643a810fb93a6372fa3a4153e53a39bf7f3a1a9e383a1a85c339f2dbb639b2b87239912610395f96ae393738c1
  | 7, 0, 12 => 0x43d387b543cfd02243c11da543a70ae54384a18743596148434d00234329027d4326ac1e4323f83b42fc4e1d42e8b0b9427e2d324266f78e4258c7cf424dd2bc424c735b423d3c4e41d2554b41be98b941bb1fa74197cdb14190951a4183d824417604ab41699faa4163f809415b1094413c5285410ec54a40fd5c8940e6327b40d7019140a8434040a1669c409484b7408d53e2408d440640811af0407b21bb406d164c40302e03401b48293fe8acd03fdb14c03fd89f2f3fd129013fbcee743f96f1e83f84561c3f5b35893f4fbd0e3f4469d73f32ca7c3f12e7d53f0d3cfb3ee60e733ebf5c103eadf8b13e8925ea3e51fe3b3e4848ff3e2a98cc3e294fff
  | 7, 0, 13 => 0x4a3408ba4a09a24d4a06e69a4a0491ce49f1948249ee7a4949e77cd349db8764499b52454988577f496f5b49495faea748ef7a5e48a30f48489cb018486b9cc54860daab485d290d4853a48d4835c0784834c39b4804f0f947e5621747cd22e347b5fc0247449f5b473a9da3473a6d92472d13a3471a6a2446f4d90646f3f1d646da15bd46cd9c5046ba482546b17d45468e95ab4669fc12465232c34621c4694605a55e45f4fb8345eb319d45e428f445d63c9845d5b36a45d2253d45bf65e7458c1b08457649034566e4914541e848453591d2450782cd44e3171544e281d0447f5f9c446609b64458f2cf4430796e4421a80f43ff470e43e3fd0e43e12dec
  | 7, 0, 14 => 0x4f5c9da64f1c75a54f18ab174ef8dc934eef5b634ee29ddf4ee201a54edbdb8e4ed160d14ebdb7684eabf50f4e8225634e4532634e39dea64e31041e4e2e2ce84e19c9cd4defa2b84deb64974dae62e54daa25224d9b2ade4d7c1ea04d7b070d4d6d7cb44d608f404d5067194d2f3c8a4d1a63024d10dd8a4d0e53624d025dfc4ce69ba94cd1cbe04cca48f44cc3be474cb7f0c94cae6cf64c9ad3b34c8364a34c6505a34c63c6984c3ac3c24c3021524c1e31e94c1de4d44c02950f4bf953694bedb5924bcbca9e4ba3ecca4b85183a4b8302974b6d7f204b4480574b3060ba4aee95694ae0b3c94abb17904aac3dc34a9b3bae4a699e564a4cbebc4a469074
  | 7, 0, 15 => 0x548e179a548cc5b55478803b54617bf95431b23f540f9d7653e2635153c86a055396465d538ed0be5385da585363fe365359b3fb5310cae8530dd69552f219fd52e515da52e32ea252dfc42352afc25752996d6752862178528577355270ec6c526f455b52652dd55264f30152504350524b30b65246421652368d0152267abf52084b2c5203ea7051db4f1a51d54e5151b94a6151aee74351a46b69517faf125148472e510f768650fcb6f250fc017750f4e59f50eaed9850e8874550c1bb7d50c1a5e050a7d0d1509f8ca3509287a750903fbe508168075062f21b5047ce89503e3f225037a9b2501bb58b5015e3965013ea855008758d4fd65b6b4fc4d311
  | 7, 1, 0 => 0x59253d1f5922ec46591f80e65914aa6958d6963f58c7437a58bcfd2358a6551258a0143c586da4355867afd6583d0cd8581d1f795813abce580aba2258039e4a57fa7d2b57f82ab457ef3f8d57db40a857d2034457c0dd4e577c15f457362f885735f67a571af9ba56fa16be56f51c3656ed1c7b56d9d0a856c28bb956ae68fc56a3fde0569ced4156951586566f21d3565a3d77564ff1ed5649f124563b9aa755fdc57d55f8209255f262bd55e7a0d655e1e6865593c9de5585c10e557f5c9155784b9c557784d6557159c5556da6c7555e780a555672e1554eef97553f4f795539a68b55181706550f9dbf55073dee54f1735f54bb755d54bb116254b83bed
  | 7, 1, 1 => 0x5de9039b5de391b65ddf67e95dc4fbd95da19dd15d7f3b025d6eca4c5d4fcd3f5d4631575d37c7f85d0c7e285cff8ca15cfac8f65cf0c0825ceb768b5ceb5e295cd1412f5c8e153c5c7c04cf5c47f1045c46243c5c09a8905bff216a5be538835bd02ce85bcd8fcd5b9966485b96d7675b50b99c5b4c7f215b3983f85b26af105b212d615b1b4a615b10def85b0d3dbf5b0631845b04eb6c5af814a75a9cf1fb5a910ab55a79a54a5a5fdbb45a5f46385a55be6c5a4eb54a5a4109985a2e99a559fda14059f11a1459e2499a59dd40be59d8d2e559c5ddbf59c3926a59bf3e1359a2dd63599470e7597be0c15952bf515945debb59458c94592cfafe5926dba9
  | 7, 1, 2 => 0x632405df62fec6b962ee841462e9c1c962b0c67b627e5bbd627d29de6245d47962387e78622d0e096204ad4761f7222a61ede05661e2833e61ddd20d61d9161e61d151f761a2505e619c5b346186cf6061727cfb616dfee36165648b615f64c06151516d611cde09610788a560dd91ac60d6c19560d3573560a42f02609ba710605c2bfe60399b3d602ebcf1602bde88601d50b95ff895245ff7d54a5fe54eea5fcd3a315fae7b465faa2c4f5f8fed345f798e3f5f66e6445f4dc09b5f40357b5f3975ba5f32ed555f20052e5f16df6a5f084a655f0577095ef83f6a5ef7b5895ee935c95e7bcc6d5e6d15f35e50dfc75e4e7aea5e4d75b85e4644e35e02f975
  | 7, 1, 3 => 0x6803f4df6802b2e767f8c41b67e20fe067d0bec567adb0e3679b29296795ef97678d3c2f676ca7536742a7d3673d759c6722ad00671b739667103ec5670627f3670425a96701d8fc66f41fba66e46e6666c18c79669ae63a6684c085667cc29c66704cbc6658320f664ccf85664a2e4d66484c306606f8156603f64965dd7ad365dc2b3565db712965d9faca659ce0e76575a416655c4e5a6555e6036536bacd6535248a6516eece64bb1a6864b7656c64993ea46493563e64894ca364818a93647d1c476461a2856457a1db6456be916441f1ad6438425e6422ed136412729763ff7f4763fe5a4f639d7a81639bf722639a5bfb6388b720633cbe4b632a33a4
  | 7, 1, 4 => 0x6d4f0de56d4c1e466d22410c6cfba4ef6cdf4af96cd332bc6cb058c66c96dad26c95b5226c6b07056c5e9d666c55ce416c453e1d6c419f856c24c4ee6beb02eb6bb6c94b6ba0ff156b95d5b26b7e56f36b6f4ef26b3017626b0b5d396b0a9be56b024b4d6af5272e6ae95ce96ad9b6196ad97ffd6ac5e7666a9da52b6a8339f56a698cb76a5673666a40fc8c6a161b4269e9125369de091c69d46eed69c9e54d69c27d7569c1909169be6e3d69b46fdc69658e996954d60169548d246932738d6920629d690b0d3968ff83c268f8c50e68e1164068ddca6368cd9ffa68badc8d68b1090968a8fe1a68748ab6686021f6685f355268353e596821124f680afefb
  | 7, 1, 5 => 0x72b857c072ab5f4f729b2e07727e079d7278be2072410996720e91ee720d0ca771fe46de71ebea7c71afb552717db904717d774a71784562715f6ccd70f7e40370db175f70d8105170d1106770d0c12570cd5ae470cb1ea570be61217099cb967050cc06704a659070412ff6702759d970228aea7012893a6fec830e6fdc58a56fd9346f6fc727d96f67bb426f658ee36f508a4a6f43ea976f34ebed6f2eb18f6f1f7e7a6ef0f18c6edf7c9c6ed2d11c6e9f61156e991aae6e74d7686e73d1506e6656486e310df96e2a2c416e1a826b6e1219936e00281b6dfb2ed36df9a8166df1abd96df0fec26de554006dc7f9696da8abc16d8386516d72199c6d71deff
  | 7, 1, 6 => 0x77fbc30d77dfd53c77dc6d6977cfa30e77cbd18277b942fa77b2125f777857d877540ede77496a09773a3b4c77323623772ab2d9771e700576f1fb2d76e3013076b692d376b68f5476acad0376a836f7768e6365768d3e1e76883f0f76865e3c7669dadc764e172f763a672e7637294975f001ec75be02f575a42d4775a337077590c5d175619d9a7559b662754e9139753c1a057501c25674fb6bb774f44fdf74cc570674bbff3874a892fc749470847490c7ba7480d247744a6a427440f11774381a627419a07b7412504373b7125c73b11193739f2b39737229507369c58b7366785c735fe387735b37157322a3cc72e3d16772d87a3472bc21e472ba3b11
  | 7, 1, 7 => 0x7d6efcf87d6b70b47d2dc3587d291a647d0c8cbb7cf70da37ce0aeae7cd5890c7cb55eb97ca027e27c7f02d67c3f68397c3b9ef67c3a52057c2e85b57c2dd0197c26f8bd7c22fff67c1ebfe47c1cccda7bac4d1a7b9f80657b9c82b77b8fc70f7b8055d47b70f4f37b5f89e47b5ee8917b3164647b2874407b08be407abc8b8c7aaa9a147a98c0657a8096417a6bf5b27a5716df7a10de7579fd2fbd79f46eb679f2dab479ef6f1079c53e6079901802797ec6d17976ef1679700e8a7968f2b2796641d97943972978e4f5a278de9bf378db4aa878d0df78789ffcfc789e7b0c789de8b6789d0a567877a19e786dfc597860e639785978f07832c40c78250791
  | 7, 1, 8 => 0x83b647ca83b31a7d839a615d8392ebcb838cae8a836650848363c3f6836330ba833e6a8683079e278302b3d682c9e5be82ba668282930f55828b485b82686d6e824ebd7681f2ef0781eb355181c8c2f481b9ebce81a29664819c32b2819b4b08814ec9ba814aa3528128f3f38121df0781214069811ceb0d8119fa028114214f810ac0a180fac72880b8c97c806c43f780458e7c803b486080355c7f8032d812803070bd80231ba07fda735e7fd996ed7fab994b7f5d02fb7f34c9357f2d59fd7f29300d7f2619507f21f4997f1dbf9e7f18940b7f05a1247eee8de77e7ba7e07e761cb27e151cff7e04ecbd7df369a47dec58af7dc7732a7d87996f7d7ff203
  | 7, 1, 9 => 0x88a9727788a2ca0488880168886be25d8869664f885bec33885bde898856fc838856635b8833f5518826a0348820d241881a7216880cdd5b880ca2e487f2185f87e29fff87ca6cc487bf553887ba31dd87b698fb87a82a1f879b616287881d6a8782d64e877ac84d876c4c7d873c288b8738119c87299de486ff2ee886c32c07868c39b58687ba56867dc5fd865fd91e86453eb9864482128617afb1860c2be68602dca985db428985c3ded685b3ccb185a4cbd185a1ba9e8577c6ff855f3280854cb0a8852f6aa28515b8cd8507f4ca84f3169584a52c19847ad7f2845b963e843a120c84366cf7841cbaf9840206a984013fe783fa8b3383f73f8a83e13690
  | 7, 1, 10 => 0x8d2c30e48d227ba88d145d498cd297818cbb13f68cb5433f8ca6ef548c94a7298c839dfd8c7cbb378c6c2dc88c3afb688c1004358c0b847c8c096b588c03c8b18be88e5d8bd6858c8bb9cc5e8bb1328c8ba664528b9a7c8c8b90331e8b67488a8b66e6008b55b5f88b3a1cd38b3625d88b226ac38b1d15ca8b1addd68b0df4778b04dcb88aeaa6c08ae45b378addff2e8ac1d3288abc62618abb70a38ab9e18c8aac706d8aa94f158aa2abe88a5552178a323b078a165d718a1656d289be809e89ba713c89772619896dabdf896336f8895dfe56895dd9a1894e9e1a8947644889403b9989343e5888ef6b0288e7509e88d0391188c8f86088b6d63c88ada850
  | 7, 1, 11 => 0x9200fbc291ecb7d991e1923691d7069f915ee2109151d7769141ad0d911fadd991176ef79112e78990f2ef9690dec3a290a631019097acb3908ece02908d554b9073fab89073d5f2907077f590503754904717af901b86268ff96af68ff880668ff3586c8fdfe3ad8fcffd1f8fccc2048fc876348facd3798fa1464a8f8f80a98f8b65ae8f6eb9328f69047f8f5b4d998f4ddcde8f295bc48f175eb78f0950aa8f088a868ed4acb68ed0cc8d8eb6e2ca8eaae5848e7124918e68f6f78e5725bd8e46ca478e3d634f8e26e5f78e032ec18dff31bb8de24ce58dd05b6d8dc02d048db1fd5d8da850658d9ebf6c8d9af2608d9225708d8425078d7aed198d7627a0
  | 7, 1, 12 => 0x971d87a996f3abaf96ed6b4b96e89d9396d72ef996d56fee96d0132196c0b12c96bb290b96ac7d51965c9589962fdc8c95f8182795e626af95d6492b95cc8b0495c62ad995b99e2f95b0bda2959ee858957a19a9956b848a956af0e49556175c95522fc3954d6df6954c91e4954a07bc95225003950f352694ffe11f94ef594494ea215094e699e494dbd1b494b0dbf1949410e39493f2d89492ddb2948722919466b5f3945c2a619437159c94359cbc9410b3b793e35c0593db4aaa93da0a2093a98caf938b73e2935cf7b593593a8c9353153f934f2dc4932e3239930fd33992dd99ca92ce46f592ad62a592acd3a992813d8e923924e7923619c0922628d2
  | 7, 1, 13 => 0x9be5eaa99bda856f9bd8f2ff9bca85189b9c0f759b77c2189b67b39d9b65def89b5a8a139b52b2589b4c7f429b2dce579b0132a19aeb76b19ae20b659abdc1009ab8455a9aa6da719a8bf7aa9a8bcbe09a8445699a7253f19a47b1c99a43ff869a1e8be49a1dcd2a9a1c8ce899f1845d99b836349990d194998dc66d9971633f9944d26b99243b9f991a12f1990ffb6b990e95b29909283a99016ebb98fd6fd798f5fe4c98b76a5d98a9b595989a6e7d98925296989031fa984429e79832fbc79811ba8397fdddae97fc608297e67aaf97c4975d97ad5fb7979fbb96979e957997941ecf9785ee34977cddc1976c89139765e29c9747c874973b0d54971f7fbf
  | 7, 1, 14 => 0xa0591b68a053e24fa04daaf9a039bc45a0353164a028cb9ca0230024a022680ca01eb416a0195ee59fec64eb9fe0fc489fc81bf19fc62d649fa3366c9f8844ec9f7bf9f09f56ae149f210c3d9f1c440a9f1871cb9f135f8f9ec637229eb1c3c19eab00239e9b8e0a9e983b039e9559b99e8fb9389e7534569e5912e49e56811f9e52ceb09e33d4ec9e210ad89e0665df9dfc23f69dfb72369df4f9a79deb9d439de0fd1e9dcf7e389d97ea119d57fc609d3e8f329d3df8079d1bdcb79d17c8749d04d4cd9cf729b79cf6d7539ce83a339ce2885c9c926e6c9c865d569c7f2c819c6d66999c64495e9c464a4e9c44bee19c27b13a9c26f80f9c14133a9c063563
  | 7, 1, 15 => 0xa5dd0329a5d302cca59a240ca596fabaa593fad9a58b8199a56dc7a2a55e128ca54ca654a54714f0a54213c6a5272ae5a50155e6a4d36ceca4d35194a4cc9566a4b7b929a4963bdfa470cd21a4484375a42a80b8a427599ba4234630a402c7d9a3f6f2dea3bd8ff3a3b74bbea3ac4ce7a3a12717a39e26e6a39c6b8ea37ea8d1a317fe4ba304b735a2f38e3ea2ed028ba2ab898aa28a69a4a27b6232a26ac316a25bd4b1a258df4ea241a4fda22151bea214873fa2066a62a1b636a0a18fd52ca18ed7a9a17579d7a16b8987a15def42a14a8c27a13bd84ba10bf6fba10a5eb9a104f34fa0f982e0a0ee7702a0e2096ca09c7f18a091e7eea06bbb55a065d3c7
  | 7, 2, 0 => 0xaaeb2637aadc7a81aacb382daac32e09aab8de38aab3f282aaaa4cddaa98f8b4aa8ba3f5aa6baa8baa4f8b80aa452991aa26b1caaa0ec6dfa9f9f4e4a9ce7a41a9c34916a9bf1c36a99d0106a99951aaa9925c3da9907e58a98ae791a987160ea97724a4a96b3d5ea9536d8da93978e1a927f774a917ebcda8e68456a8ae77c7a89c906ba894d850a888922ba86f31f2a86c13e6a84135a5a821f9f1a82101fba7fd1eefa7db6d6fa78974f5a77d7de0a7752a14a76a235fa76199bca74efc98a7352dc1a73369e3a7070867a6ea9da8a6ae84b7a69e95f1a697cd48a6892a12a667d7aea640a41ca6375980a6272164a61de4fea602acd0a5f87e3ba5f66f26
  | 7, 2, 1 => 0xafec201eafe9653dafdef203afd6dd83afd5efccafbef88aafae9a9dafac1eafaf7e5c2daf6a54ceaf365ea7af359018af331a1caf31501aaf2bc6ccaf2022c0af0046c8aee1256baedd696eaed207f3aeb8f7e5aea8cd7caea402e0ae8056fcae619b76ae5db543ae49084eae45eeb5ae37ebe9ae1d15d4adf95653ade8f265addc392fadd89541adcfb474adbb5be8adb1d04aadb0dd5dada685f3ad9e7681ad7c2950ad70d8e4ad13ee5aacf6a118accc3a68acbd3eedaca5b365ac7da328ac77f2fbac5efcdbac584a90ac451088ac272790ac139c47ac11c4d5ac08d977abd61055aba7945fab9bd696ab803d66ab7bab3aab6a6e98ab65e7feab377bdc
  | 7, 2, 2 => 0xb4d3a14db4d28f2cb4c9c506b4b7ad7cb4ae3bd5b4abb72fb44a929fb426fbacb420beb5b40748eeb403b48eb3f37ff8b3ef1ffcb3c9c30bb3520c41b34d471eb345a3a5b341a868b33dffa7b32747c9b3156a73b3129c5ab2eeaacbb2aa8f41b2aa4fc4b2a16f37b26a3914b242d2e4b23ccd8fb22e5d43b1ea3e9eb19e29acb19cb481b1918fb0b1908a5bb18896bbb1838f47b176d427b15dc9c3b15c16f7b158ad0fb14a7c74b1498684b14872c1b146c193b1447d4bb11cca9ab118dd33b0e3b6cab0cd4dcbb0b06ff8b094df54b0917dc9b0772feeb0728791b0598918b048318cb044ba39b03b1c5fb01c3732b00c731fb0049811aff43d18afedb434
  | 7, 2, 3 => 0xb96f2564b954389eb941a5deb9238bb6b9114bf3b906d2ffb8fa157bb8db78a7b8db3bf4b8ce80d4b8c42226b8b97ddfb8b4c543b89aa85bb88ec8b7b877b3cfb839de42b802dc33b7d97460b7d57de9b7d3b0e4b7c1e9f1b7bed18eb7a8f6efb7401fceb72d9c79b71ef297b70f3d79b7043cc0b6fad8c9b6e531a4b6e2d1dcb6b17062b6b0f2bcb6af85aab6aa2f82b6837379b63e8ff7b6358400b6355c70b619a837b612cc7fb5ff4747b5f8321ab5ed3c51b5ec76f9b5e0fc76b5df9bc7b5de5852b5ca4c10b5c7e6b8b5b77e2ab5b461f1b59bbf22b5902909b581960ab579183ab554a760b5409f12b5227ed9b5088a0ab4f0c84ab4de6d1fb4d870c0
  | 7, 2, 4 => 0xbd97614cbd8d30adbd5c6ceabd569d44bd53855abd481cb7bd197d31bd16353ebd0f2ad7bcf03cf9bcdc53d7bcd3a035bccfcb9bbccd3d8ebccbccecbc885194bc7ca571bc77fd23bc6f13e9bc5fbe37bc4e1733bc4e049dbc475fcdbc1d99c2bbf51af2bbf2c6b6bbf2c071bbecc5edbbe6e79bbbdea910bbd5d798bbcd479fbbb6e8b7bba23f4cbb9554cdbb8a8b6fbb83e04cbb806acdbb6f7b9cbb5f66ffbb47bb4abb35131dbb2895d7bb216fb8bae435a9badf96d8bab4727abaaa26d3ba9c640eba90fbf4ba6ddb7aba6bf53cba4d6184ba0d7012ba0bd188ba0a4a0bb9fb3ed2b9dd9279b9ca7d3ab9c6ad7bb9a5abf7b99a9a36b985498cb97a58bb
  | 7, 2, 5 => 0xc23be256c22b236ac2238e8ec2157f87c210f4a6c2052f8ec201d380c1fec366c1de7afec18fbe0fc18e2004c18ac36bc1881394c186b0a2c184087ec180557dc1651cbfc157bd32c152eb7fc124aa0ac11a504dc10c93d2c10593c9c0e7a473c0c437dac0abe54bc0a7fd53c091d8acc0429fd7c0324461c02871dec026c9e4c00e3379bfd73578bfcdc6ffbfbe674cbfbbd587bfaacdbebf8fc338bf866c7abf851e63bf75efa6bf6dea7dbf666733bf61785ebf2b5d91bf1361a9bef59e9abee8615dbecd8a39bec5fc52bec4b84bbead66f1beab9042be9147e6be8a4766be54e56bbe4929dbbddfe1a1bdcd0c10bdbb02bebdb3ec25bd9d51f4bd9d191f
  | 7, 2, 6 => 0xc7e4a5b2c7db80e1c7b58e37c7abb727c77e063ac7781b5fc775e74ec76f3b0ac76c6475c75da8f3c75aa013c722d832c71fc81ac708d5a6c701f6d2c6af14d6c68acfd0c686c8f2c677c7a3c673f56fc654fc98c61d4f36c613f6dfc6033cefc58557c3c55c4746c53d52fac532c1fdc51c6308c5067b7fc4fe2ab6c4f3c18dc4cf5180c4c83208c489c356c4828b8bc47d52b3c4775350c46975e9c4588134c447e9a6c43bc065c4237999c4164caec3f04a81c3e22da4c3d28b09c3d12e09c3a26885c3975ae4c3962a92c3827a75c353aa7fc3474cc9c344729ac33655bdc331d3dec33155b1c301791cc2ef53cbc2e7ba3dc2daf057c2d474bfc29ee904
  | 7, 2, 7 => 0xcd43454dcd359d45cd083060ccef4fa8cce6e03ecce31d9cccbd92f6cc86101fcc5b0663cc4309eccc42fc48cc3dbb03cc329e27cc26775ccc224b71cbda3838cbd1d700cb9f0c58cb9adf78cb87cac1cb7d8f0bcb7d4e04cb7a5a8bcb78c448cb76685acb69ce5ecb50d9e6cb349801caef0791caea07e8cadcbb49caccec61cab12130caac0d7dca546425ca537f57ca30e3fcca04774ec9f8ee7ac9f3d846c9e8e892c9d4865ac9c45eccc98e47ffc978e544c93bd55cc93615f1c9240959c8f98b0cc8e2cba9c8e27018c8da031cc8c0596ec88bdcdec88322c2c87eab19c86aea85c8439af0c836f3c2c81b12f1c8144c74c80f6f46c7edc099c7e9b3ce
  | 7, 2, 8 => 0xd3304b68d3265b1ad31e59f0d2f6e418d2e2b363d2d17233d2ce1507d2c17b0bd28c47b6d257e8b9d24ac501d248728ed24558f5d23c8d64d23889ebd21dd0abd21ac315d1cf1eb4d1b1b30ed1ac10d2d19abbccd175aa0ed11c0b79d111535ad10ba971d0eed897d0d31777d0c9d227d0bc3a17d0b92cb0d094765bd06fa9abd0657b73d062548ed000bef7cff609b7cfed907acfd785f5cfd29977cfc309abcfb93b24cf9b40d6cf73c5f6cf65523ecf43767acf0d0abbcf0c9d9dcf0bda5bcee52cedce9c234ace9bbdfbce20d3cace16f6e3ce0b07cdce07748ecdef810bcdaa44eccd900d75cd887d41cd8357a1cd74fbe3cd66305ecd52d7cdcd4803e3
  | 7, 2, 9 => 0xd7e5e446d7db0a89d7bcbfb8d7aa6bbad79d9abed7899138d77efc9fd75e8d0fd7461506d73f0427d734ab98d72f32a2d719f753d710e7d1d6e2b88bd6cc8efcd6b9fbc8d6a4d1c7d6a1a49bd698d3ddd6827ea1d6683848d666a11bd655a816d643c187d64187a9d62f68fbd62f196ed5fede1cd5e404bfd5a576d8d57f7a4cd56908f6d558a97bd522d0f2d5081364d4f48f2ad4f0f799d4ee2432d4a3bcb0d49fd409d4861306d47d3279d47ce68ad47b92b8d4468e80d43a869fd430d163d41890d1d40fe3a9d3ff0dd7d3f580b8d3d6fe7ad3cd493ed3cbe778d3b5450fd3a2fce4d39ab699d388e184d379eceed36d52f2d35f5289d358ca24d33722c4
  | 7, 2, 10 => 0xdd22f5f6dd193586dd09945fdced4dafdcc898cddcc510c9dcc2d6ebdcae8f9bdc9a6785dc7a461adc771e0fdc15be7adc06615adbff3966dbea5838dbc5bda8dbb5b57bdbaaaeb5db95469fdb94eee6db7c6105db657adadb3dab48db152e11db0231fbdb008209dae88803dae38110dae1e332dabc24d6dab6ff36da9544d8da9132ebda868036da61dd2cda29768ed9e8712bd9df23c3d9d3059ed9c9b650d9b44a16d99d2432d98f9349d984ba31d97cde91d95b6233d94644ced93d87e6d92ea3f0d916e5cfd9095fbbd8ed43cdd8eb00bbd8b63777d88137bcd8721ea9d8602d31d82ac424d825c4b2d823951fd8114742d80e38fad808765ed7f0e012
  | 7, 2, 11 => 0xe41a242ee414a759e3fc82ace398d376e3963e6de37f5dabe3412cc1e3106e12e30df211e2d32023e2d1c9bae2af43c4e2a5fae3e2974d4be28a04cae283c095e2785dd5e26d9beee232f697e20ff168e1edd638e1de2ce3e1d915bae1d7e8aee19798c9e1938d46e1560784e14f1b93e1410c7ae10c9b80e0ebc0e2e0e569efe0ce06f0e0b13948e0953493e04d6edde032dea1dfec358ddfb96348dfa83d6ddf68f3efdf4022ffdf38302cdf382235df130c3cdf0bc77bdef54073deeb28edded551a2deb1fadbde9849e3de8c5845de808106de559161de4dbcd2de49630fde3f5106de3eec65de318c70ddf1f4bcddc76448dd5c2e0fdd580b4fdd44ebef
  | 7, 2, 12 => 0xeaac3b0beaa78c21ea9c0e9dea6c0015ea6043fdea5d0618ea297667ea080100e9f1eafae9c5a95ae9877a69e979a0dce940a7a9e935373ae8b32ee1e8a202a5e89fb0f7e892569fe881f5cbe8764198e8538ae5e80761dfe803d04be7efba21e7deeac6e7b52c4fe7a1d2c5e78c552be76d1024e75cc097e743e23ae73ba6c9e7311744e72b167be71e5c90e6ed781be6eaac2be6e489dbe6a00801e68fcee2e674c767e65915f5e645392be6334511e626c786e5f93c5de5f2c308e5ad3e0ee59d96b3e58377c9e54da510e5260c39e5159907e50d18f3e4c211b0e4aea01ae4a63fcce480f5c6e47fbc49e46f7636e46d6be2e466cd84e461410ce45de151
  | 7, 2, 13 => 0xef3e65bdef2e9b0fef16e17ceeea3911eede5f57eeca28f2ee894606ee876a10ee82c328ee4c34a6ee459ecdee36c9a5ee343295ee33f0d4ee23135cee18b783ee12c54dee091011edf3b601edf34286edde2550eddbee4dedd4dd83edafec3bedad9a42ed8af1beed7dc820ed6973f8ed333564ed2a2a1aed105b43ed0f2146ed01c25becf6989eeccf22c6ecc5cb2aec9ca3e1ec8a4b5dec87d0bfec83f7cfec79fad7ec72facaec6e369fec663512ec55144bec489e51ec2e8d50ec20b13cec1a7a9bec167598ebfd1c1cebdaeb21ebc722e3ebbb66bdeb9304d6eb7e1f2aeb72283ceb650627eb406b8feb222eefeb00fb13ead54e4eeac65055eabefb5e
  | 7, 2, 14 => 0xf4ee8542f4d2a75af4c930adf4b303e2f4ad3575f4a423e9f49e69cff4857ffdf4782ca3f44e454bf426cf73f42435d0f4211c37f3f19c1ef3aae1f6f391ebd2f3785de9f3733036f36d6c95f367d1f7f35752b0f311585ef3031826f2eab183f2c10465f280ddebf27b317ef26fedb7f2386bdff2218e7ff21bf636f1fe0360f1f4b290f1ce1097f1b84c83f1b2d8fef195bf85f1784439f1770418f173b0a8f1649c4df16191faf153f5cff153a027f136cbbdf1350785f11de759f0eeb9e8f0d9ba7bf0b6b375f08b0e3ff0857a5ff07c42f8f0799319f05ab396f04f03a7f047ce9cf041e202f00adb8eefd9a278efb9323aefaf0f89efae69a2ef57b8fa
  | 7, 2, 15 => 0xfaa91da6faa81eb5fa9321d7fa6a2533fa401aa7fa0187f4f9f5fb7ff9e0add1f9c44b15f9b50926f99310e1f990188cf98630cef955b00df9552142f93a5051f9158fc7f8ec2452f88e786af8806e93f87cb44af848f742f8456696f82e5cddf82ca004f82530ccf821a1bdf81aa65df7f54a0af7e7d309f7d8efe4f7cbf583f7998eaff7813a1af75b3d8ef7568747f750e12cf721c153f6f4ac3ff6e481d6f6e1cd84f6af65a7f68e4a3df66cf4acf6653863f65218f3f644b462f642186cf61649e1f6144ec5f60e6587f60c94a5f5e05daef5c74da0f5ae0132f574dc78f56a71faf5635cbbf560bcbef5373f08f5325572f51b75b9f5118c29f4fa1d32
  | 7, 3, 0 => 0xffb3113affaa18f5ff9b1b81ff794e6aff640b3dff58e3f3ff4da10aff3d1588ff27bc33ff2757a7ff123350ff0402b5fefe038cfedd3cb7fec7e6ddfebe2d6bfeaa4057fe971ab2fe7e7e7afe7dc54dfe554becfe52e151fe282b53fe24198cfdf4a2a0fdf3875ffdf0164bfdeaed64fddd6bbcfdb3f8dffd9d02e8fd99ff10fd93ab53fd3ce5b2fcecae0dfcb0afc1fcaa14ddfc8bca0cfc4e4806fc34fec9fc30d494fc02cecffbeba59dfbcb785cfbc7748afbc60337fbc1bc8dfba57992fb8f8f90fb8d1e6afb88fb78fb797b61fb6b568bfb3e6e67fb2e4632fb2d2338fb2a5f25fb138c2ffaf9a1abfaf397f8facf948dfabf7ea4fab21684fab042fe
  | 7, 3, 1 => 0xffff0634fffea3a6fffd9e4b
  | 8, 0, 0 => 0x232623972209c1492085ba6f1fbe639e1f505e561eb180c41eaec2be1e21c84f1da3c2791d42c60e1cf1298c1cc1ea541c3bd1d81c1a73291b9b06e31b54b30e1a51558f19b15e68194d07b41917953718ed5c081867ad1418035660179ba5681773f915174164871703b38d16ff67ae16c885cc169f5cd912c7ac7e12b53745128177ed126f593f1101c9f510bcd6ce109989db0f970d4b0eb2ba8a0db6ae630d2e3d660cda57470cd4669f0c5bdf350bedd9ed0b8bbf6b0b15b6280af1fed60a9f6c030a5133e109efeca509d69a71092808eb0907828d08719fb807a389060790ca2a07540f0804be9b5d03e5727602c7e1c601c0cf2f01737d880132a60a
  | 8, 0, 1 => 0x564fc87855da718055b00d5b5514da2a55119db15400b90d53ebb6ee532b31af52d41b9452c6dafb52652dd550ba5f8b50a840dd509cfade4fed6a864f01e97c4ef5be6c4dcff4e94d476b1d4d2f3c8a4c8364a34bba970048a30f484749554c4716cec6452bb7f6449d41de43cb072843a4cbbe42ed440f411da5b740b9cff8409e34a4408d4406400015073eb72f933d41059b3c8ae61d3c5cd09139559c2f376a4f6936aa157736209e1535e8537e352b3a5934bca48e33e83ed833ac494931c32ec330cd8a4230797d6f30452eee2f1583e82dbb214e2d6782ad2cbbaac62c9d909e2b5379482b3beed92990644b292c0d9726c74c062595651923fc0e44
  | 8, 0, 2 => 0x85823cea852f6aa2836a9b7e83490ab082fc9636816c4ed8801c3ae37f82a65d7f1e4fa97dd7bdf57d57e2b57c3a52057c1b05047b4367897ae9648876b73a477673e45e75a33707759045d8752fd481745985b3739f2b3972f58c2c7278be2071801e4470e422b070821968706ffaba705b213270227bd66f9675c96f653f376f321f156ebd78496ea16f056d97aec66d42739e6cd46e566c8cdfa26bf5ec266b58cb236b3d020a6af4746f6aeac5db6a866f276a314b07690b8184688b911168273a5d6716b47363ff7f4763e020e4621b7fc560f5b64260bf4dc9604bbc7e60364b425e6214035dfdbd4f5bf8a09c5b8a9b545b7badac572b3dcc56cdce4e
  | 8, 0, 3 => 0xad48081daa70fe3da9536d8da92e1f67a91c00b9a86c13e6a7697e48a6ea9da8a643b4c5a549f6c7a4c9dd97a4ae5f18a3d3d878a3ac4ce7a38fee89a26835d3a203df1fa1ea2ffda185d949a184c90da08ce91fa039bc459f9b20929f36c9de9d717a869d3b975e9b87d20b9b237b57979476b89790a9e095cb9afe959b5dd2956af0e49492ddb294213f909406f9df92e1305c92bd4609928a0576917f8e9790dec3a2903af60b8f95124e8f87e3d58ea1b5b78e5c135a8e3118c78d8425078d4f66ca8cb80d3c8c53b6888c27a7848b9a7c8c8b3625d88969c3558911bc2488c8f86088a3b6dc87a84624877f470c8646d6de86448212861b4d8585db4289
  | 8, 0, 4 => 0xe286305de27df1c3e2182b15deae0fc1ddf5fcc6db747efcdabcacbbda70651bda1ba67fda025fd3d9f67adfd9e2caf7d992242bd676da41d58f793dd35f5289d175aa0ed111535ad0c9d227d0657b73cee4c42bce16f6e3ce0e84ffcd79adfbcd52d7cdcccd458fcb884e68cb694c08ca5896e9c972257ac90dcec6c8f91191c7fd48dcc7abb727c74aa3c2c6dc9e7ac5742e9cc52d073fc242cba7c2157f87c02126d4bfa320febd541193bb67486ebb553d6fbb32f41dbab4727aba53eca2b9fc0058b96ac126b940c30cb806c79fb7acf0edb6b375dab5f8321ab5e0fc76b3ef6d88b399a266b1838f47b14a7c74b141b29aaf99e6ccaf359018af1d0a4e
  | 8, 0, 5 => 0xff89d50dff652815ff257e59fe5a0e72fddc089cfbcfa734fb8cf931fb3c38d9fab21684f7af6be0f779aaaaf6b22f67f6b00b97f4ed8e48f4c886ecf4b6683ef4643038f452118af42e45c1f3c7c4c5f303e5cdf29f8f19f1de1c4af179c596f029aa86ef96d1c2ef2e9b0fee9a4055ee82c328eb8687baeb500845ea5d0618e9877a69e8a9e5dbe78c552be72b167be7125d9fe6c3db03e6a45857e5685c65e445238de3a3bb46
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x4125500300104d5400c0000000c0101000003004044125500300
  | 5, 0, 0 => 0x105104814001050020040055300c3800350412040001441481000000c11020000020440c00000c01010000040041000000c11020000030440800000c01010004140080000105002000005540081000000811030000020440c00001001040010510481400001001040010510481400000c1102000414008000000100104000d5400800000510921400014424850000501220410495400c0000254c02120011500881000000c0101
  | 5, 0, 1 => 0x40043800000811030009540080000051052040010001881100154c030e0000020440c00350812040009540080000000c01010000020440c0025500200000954008000015500204000003044080005109214000003044084125500300000d540080000000811030009540080000000811030000040041000214842040000010441c000008110300014424850000010010e0000030040400000c0101000954008000041441205
  | 5, 0, 2 => 0x30440800000811030000010441c00414412050000010441c0000081103000d54008000000081103000414008000000081103000144248500005109214000003044080005109214000d5400800000510921400114104810000008110300095400800003010020e000d540080000000811030010002881000105002000000030440900154c030e0000020440c00000811030000020440c00414412050000020440c00000c0101
  | 5, 0, 3 => 0x144248500000081103
  | 6, 0, 0 => 0x38400001550020400000400450000280e21200006028810000000e100000554008100000041100000d520084800000061120000040043800000c11020009430481000214842040011410481000000061050000040045000154c020e0000002843800000c01040000020440c000001210500000018448000000210000014048810004140a204000003044080000002104000060288480010500200000000284380015500204
  | 6, 0, 1 => 0x10d430848000000e10500000324450000080e21200000304408000001211400014414810004140e2120000003843800001001140000040041000204802040000020440c004144121200100018810000080e21200105038848000590020400014424850000010010400000048450000081221200095100810000000a11200100038810000000210500000048450000000a10e00000008414003504120400000028414000000e104
  | 6, 0, 2 => 0x304408000181220400000314438000000a11400000018438004144120500002038848000000210e00014414810000001210500115008810000000210e00105038848000000e11400055400848004144121200002038848001541220400000400438003508120400000028450000000a10e00000018450004000a20400000300410000010011400000038450000510520400000400450004500620400000038400000000e10e
  | 6, 0, 3 => 0x38438000000e1050000603881000450c12120000203884800008062040000002844800000811030010502881000008122040000040043800000c510e00000008400000080620400000324400000080a20400115210810000080620400000304408000000e10500100008810000000a1050000002841400314c420400000414410000000a10e00000038400000010010400000018438000000e11400000048400000000a112
  | 6, 0, 4 => 0x30440800000c510e00105104814000000610000105008810000080a20400000038448000000210e00000038400000000a1120000040041000400c020e00000048438000010510400100038810000180a2040009430481000000c110200014424850000010010000100018810000000a11400000008448004140a212000d4204810000008110300101400848001550021200055400810000381221200000400450000010010e
  | 6, 0, 5 => 0x414414000000a10500000028450000004110000000424400000000211400000018414000280e20400000028400004000620400000304408000000e11400000414448000501220400000424400000180e2120000010441c000000610e0000001841000000c110200105028848000080a2040009540084800154c020e00000008438000000a105000004144140041441205001000088100000806212000000484380002812204
  | 6, 0, 6 => 0x38448000000211200114018810000010010e00105038810002048021200000400438000081221200000028414000080e204000004244500003806204000954008000005109214000000384100015500204000d5100810000590020400000008438000000210e00100028810001550020400000018450002148420400105104848000000a10e00041400800000000e10e00000028414004144121200000008410000010010e
  | 6, 0, 7 => 0x204881000000c11020000004841400154802120000000843800454022040009540080000000121140000604881000324c8204000d5100810000001211400000038438000001210e00000400410002048020400094104810000080a21200000304408004140e2120000001843800001001140000002843800354402040009410481000000121040000010441400000c110200114204810000000e100000000084500045480212
  | 6, 0, 8 => 0x40043800000c510e00100008810000180a20400100018810000000a1050000003844800000811120000031443800350412040000a048810000000210000000300404000000a10e00000400450000080e2120000040043800000c510e00114018810000004110000000424450000381220400002048810000010010400000018410000000210e00000028400000000a104000001044000000081103000411008100010500200
  | 6, 0, 9 => 0x10002881000000021050000000841000304c02040000042445000000c010400002028848000280e20400000300438004000e20400000424400000000610e00055300848000004110000000028400000001210400100008810000000a11400000038438003508120400002028810004000620400105008810000001211400100008810000080a20400000414410000000210500000038414000000610500100008810000080e212
  | 6, 0, 10 => 0x400400004000620400000008414000000a1040010503884800000121040000031443800155002040000001841000304c02120000040041000038122040000003841400000c010e0000a048848000080e21200000048448000000e1140000002843800214842040000a008810000180a21200095400800000001210500000038448000010010e00000008410000004110000000038448004540220400016400810000280e212
  | 6, 0, 11 => 0x105018810000180a2120000030440800450412040000e028810000000e10e000004244000000002114000954008480003900204000060288480005012204000d4104810000000e10500000038438004000a20400085210810000180a20400006048848000000610000000048438000010011400016400810000010911400000414414000001211200105104848000380220400000400410004140e204001000288100045081212
  | 6, 0, 12 => 0x38438000001210000105104848000000610e001141048100005905212000c130084800000061000000001841000000c110200000038448000010010e00000008438000000a10e0000041441000154c020e0000203884800001001040005504884800000c510e00000414410001044020400002028848000001210000000048438000010010e00000424450000001210e00000400438000010010e00000028410000001210e
  | 6, 0, 13 => 0x8450000008110300000400438004500620400000018438000000211200000028414000000a10400105008848000000e1000011430484800000121120001441481000350412040000003841400001001000000020440c004540220400000304408000001210e00000018438004144121200000400438000010010e00115008810003544020400114018810000010010e0000001843800454022040000a0488100025500212
  | 6, 0, 14 => 0x424400000001210e00000048448000000610400095400800000000a10000000028438000510520400000038400000000e11400000048410000010011400000028438004540220400002028810004144121200014414810000090020400014424850000010510500000314438000000210e0001640081000000c010e000000384000040002204001000288100000002114000000484480000081103000020388480001812204
  | 6, 0, 15 => 0x1640081000204802040001442485000000061040000a048848000001211200000400410000000a10500000028400000010010e00000314438000010010e00002048848000000210500000400450000180e2120011430481000214842040010502884800000811030000030440800001001040001441481000414022040000040041000000c110200000104414004250821200055048810000180a2040000e0488480040006204
  | 6, 1, 0 => 0x41400800000000e10500000018414000180e20400105104814000010910000000048414000001210400000018450000008110300016400810000000a10e0010002881000000c510e00114104810000001210500000304408000010010e00000008448000000210000000028448000000611200000018400000510921400000028410000080620400000038450000001210e00000400400000180a21200000414414000000a104
  | 6, 1, 1 => 0x100300838000000a10400000018414004000e20400000028438000010010e00085210810000000610500095400800004140a2040000003843800350412040000002843800000c110200105028848000004110000055200848000000a1000005540081000001091140000602884800000061120000040040000001001040010502884800000c1102000020188480015500204000001044140015412204000000284480041406204
  | 6, 1, 2 => 0x40040000051052040001441481000255002000000020440c00104402040000003841400000c110200000008438001550020400105104814000000a10e00016400810000008110300000414410000000a10e0000001843800000c110200000314438004504120400000038414000001210e00000038410000390020400000018450000000e10400101400848000000e104001050288100000006114000020388480000006114
  | 6, 1, 3 => 0x28448000000a1140008120081000001051120000002843800000c510e0010d430848000010010e0000a048810000080e2120010d430848003508120400000400438002504120400002038848000000e10e00000028448000010510500000300404004144121200000048438001550020400095100810004140e2040000004841000000c1102000000384140045081212000004004100000100100000954008000000006114
  | 6, 1, 4 => 0x28400000004110500016400810001541220400000018450004000a20400000048450000000a10e00002018810004000620400000018410000010010e00002048810000000a1040000003840000450812120000a03884800001001040000204881000000c010100000008450004050021200000028438002048020400000018438004540220400000400438000000610000000324450000000a11200000400410000000210e
  | 6, 1, 5 => 0x40045000214842040010000881000155002120000000841000000c010e0000e048848000000e10000105104848002048020400000038438000000210500000300438000000e10500000424400000000e10000000028414000001210000105104814002550020000000008438001050020000002038810000000210e00000028450004140e2120000031443800254c021200105104848000010010e00014414810000000a112
  | 6, 1, 6 => 0xe048810000010010e00000048438002504120400000008414000010010e0000a03881000450c120400000028414000280e21200000038450004000e2040000030043800000411000000040045000314c42040000001843800000c01010008521081000454c82040000000845000000c110200000028448000080a2040000a038848003504120400000038450000080a204000c9320810000010511200000048400000080a212
  | 6, 1, 7 => 0x38414000000e10000105104814000000211400000414414000008110300000400400000000610500114104810000000210000000204448000180e21200000018438000010010000105028848000010511200000018438000000a1140000e04884800001001140000603881000414412050009530084800000021040000001841000414022120000604884800414412050000020440c001050020000000008438000000e112
  | 6, 1, 8 => 0x8120081000000411050000030043800059052040000000844800000121140000040043800000c510e0000020440c00000061040000010441400105002000000040045000000c110200000028450004140e20400095100810000280e2040000e008810000000a10e00100038810000000610000100018810000000a10e00000048438000000a10500055400810000000a10e000020488480000100114000004144140000002105
  | 6, 1, 9 => 0x38414000010010000000018438004144120500000038450000001211400000008400000000e1140000001845000304c02120000040045000000121000000203884800000c010100000400450000000210e000000384480025041204000d4104810000081220400000048410000000610e00000038438000000e10e0000010440000000811030000002843800008062120000a048848000000e104000001044000015500204
  | 6, 1, 10 => 0x100008810000000210000000008450000180e20400000400450000000e10000114018810000000e11200000038400004000220400000400400000280e21200006048848000080a20400000304408000000a1040010000881000000021050000040041000000c510e00085210810004500620400000400400004144120500115008810002550020000000038448000281221200000018410000180a212000004004380005105204
  | 6, 1, 11 => 0x2018848000001210e0010003881000000c510e0000a038848000000e11200000434400000280e21200000400400000080e21200000028438000000210e0000201881000009002040000042445000001001140000204884800214842040000e048848000000a11400000314438000000e10500000424450000008110300000048450000004110000000314438004500620400000424400000381220400000038450000000e10e
  | 6, 1, 12 => 0xc1300810004140e2120000a04884800000c510e00000038450000000a10e00006028810000001211400000008410000010010e00000400450000000610000000400450004000620400100038810000000e1120000003841400000021040000001843800001001040000204884800000c110200006048848000080e21200006048810000000e10500000018400000001210500000008414000010010e000954008000041441212
  | 6, 1, 13 => 0x20440c000180a20400041100810000008110300000008438000000a10e00002018848004000a2040000031443800400062040000004840000154c020e0000020440c000000a11200055400810000004110000000400438000180e21200002028810000004110000100038810001050020000000048400002148420400000400438000010010000000018400000000e104000954008000045081212001143048480000109100
  | 6, 1, 14 => 0x114304848000381221200105008848001550020400000038400002550020000000028414001541220400000400400000010010e00055400810001550020400000018414000001210e00016414810000000e1050000002843800450812040000003845000000121050010001881000000c11020000010441c0005905212000060288480000100114000d4104810001550020400105018810000080a212000164008100000100114
  | 6, 1, 15 => 0x314438000381221200095100810000000e11400000028448000000210500114104810000000e10500114018810004140a21200000400438000180e20400000028438004140a20400081200810000010010e0000020440c000000610500000008410004508120400000008438000000610400000028400002544020400115008810000510921400000038400000000610400000400438000001210e00055048848000000a114
  | 6, 2, 0 => 0x202881000254c02120000e048848000181220400002400810004000220400000038450004000e20400000048414000000a10000000048400000010010e0000000841000000021140000020440c0041441212000000284380040002204000000184500015500204000d4204810000008110300114018810000001210e00105104814000001210e00041400800000000a10e00000414414000081220400114018810000010010e
  | 6, 2, 1 => 0x105018810000180a20400100028810000000a1050000201884800400062040000040043800000021040000042440000400062040000204884800000c510e000d420481000000021050000000840000000c510e00000424450000281220400000400438000000e10500000414414000000a10000105008848000008110300000414448000010910000000028438000010010e0000031443800000c510e0000040043800000c1102
  | 6, 2, 2 => 0x38448000000610400105038810000000211200000018438004140e21200014048810004140220400000430414000000e10500002038810000080a21200000008450000001210500114204848000180e2120010500881000450812040010001881000000411000000a04881000254c0212000d4204810000080a2120000004843800051052040000202884800001001000000000844800059002040000020440c0015412204
  | 6, 2, 3 => 0x400410000381220400000304408001550020400016400810000000610500000414414004000a20400000028438001550020400000324450000010010e00115310810000000210000105028848000001210e0000a018810003010020e00000008438004140a204000020388480005105204000000084000000081103000d4104810000080621200100018810004000a204000004144100041402212000000484140021484204
  | 6, 2, 4 => 0x20440c000010911400000028438000010010000000018400000000a10e0000041441400000c11020000040043800001091140011420481000400c020e000000384000000100104000d5400800000280e2120000030044800450412040000203881000000c11020000604884800450412040000203881000105002000000e018810002550021200000104400000010510400041400800000381220400114204848000000210e
  | 6, 2, 5 => 0x41100810000000210e00000048400000000211200055300838000000e10e0000040043800059052120000040045000000411050000a03884800000121120010510484800000c010e000000484000001812204001150088100000100114000c130084800350812040010503881000038122120000a03881000354402040000a038810004000e20400000400438000000a11400000300438000000210e000554008100005109214
  | 6, 2, 6 => 0x40040000254c02120000003841000000c110200000400410000010010e00000028414000010910000000038400000010011400055400810000008110300014414810000010010400105028848000180a20400055048810004000220400000008410000000e100000000484500015500212000c130081000000061140000203884800000c510e00000204448000180e212000001044000045006204000001004100000002112
  | 6, 2, 7 => 0x41441400000021050000002843800000c510e0000040045000001001040000e048810000000210500105104814000000a10e00000324400004140e21200002038848000080a2120000003845000000021120000603884800000c110200014424850004140a20400100300838000000e10500000048450004000a20400000038438004000a20400100018810000000210500000028450001548021200000028450000080e212
  | 6, 2, 8 => 0x843800001051050000020440c00324c821200014424850000001211200114204810000000e1140000a048848000010010e00000400438000000e10400000018450000590020400000304408000000610e00105018810000010510500000304408004000a20400000038438000000210e0010500884800000c110200000008450000080620400002038810002148420400000400438000000a104000000084100035081204
  | 6, 2, 9 => 0x3044080000002104001000388100000006105000140488100000100104000000084500001812204000000384100000105105000144248500000012100000d410481000450412040000e02881000000121050000020440c00039002040000201881000001051040000020440c000000e105000d41048100035041204
  | 7, 0, 0 => 0x28450000000610400000400410000004010400000038438000001211400000028410000000a10500002028810000000e10400000028438004350c21200000008410000000a11400000310410004000220400002048848000000610e00000104410000000610400000018448000000e10400000038410000004110000000038410000000e10400000424400000280e204000000384000000806204000001044140000012112
  | 7, 0, 1 => 0x8438000010010000000100410000001210400000018400004140220400000018438000000211200000018438000010010400000028438000000211200000104410000000a10400000048438000010010e00000008410000010511200000008400000004111200000400438000000e10e000004244000000002105000c932084800304c021200000028410000010911200000018410000000a105000000084480000101112
  | 7, 0, 2 => 0x4845000038122120000002844800000c111200002018848003508120400000214410000000a10400000048448000000210000000038400000010510400085210810000000210e0000002844800000c011200000400400000000e104000000484480000006112000000384100000006104000000284380000105105000000184480000108104000000384000000006112000d5200848000010010e000004144480010440204
  | 7, 0, 3 => 0x28450000000210400000048448000001210400000400410004250821200000018410000010511200000038450000281220400000048450000000211200000008400000000e1140000000845000000121000000031444800000061040000042444800000c511200000400450000000210000000038448004050021200000018438000001210e0005540084800304c021200000028410000000a104000000284000000041104
  | 7, 0, 4 => 0x10d430848004140220400000400448001541221200000214410000000a10400000048448000010510400000104448000000e10e0000000841000000851040000000840000001001040000003844800001051120000002843800001081120000002844800000c111200000038438000008111200055048810000010010e0000000845000324c82040000041444800000841040000040041000324c8204000000184100000002114
  | 7, 0, 5 => 0x40045000001001000000e048810000010910000000028414000180e2120000e048810000000211200000038448000000a1120000040041000000811120000032444800000021120010502884800000c8104000000184480000002100000000384380040500212000000284000000002112000000284500000109100000000284500000105112000003244480002812212000d52008480000109114000000184500000006112
  | 7, 0, 6 => 0x100018810000008110300000314438002544020400000104400004140a20400000018410000010010400000038450000590020400000038400000000611200000008438004000a2040000000844800001001140000a048848000010010400000400400000000a10e000c1300848000001210400000414448000010011200000038438000000210e00000038450000010010e000c531081000000021050000000843800000c8112
  | 7, 0, 7 => 0x114304848000000a11400000434448000080e21200000038448000000610400000414410000008111200000214410000080e20400000400410000000211200000008410000010010400000414414000004110400000200410000008111200000304448000180e20400000400410000000210000000038450000000210400000204410000000610e0000041444800001001140000041441000000c9112000004004100000006112
  | 7, 0, 8 => 0x210410000000a1040000a038810000008510400000320410000010010400000028448004000e20400000314410004000e20400081200848000000a10500000314410000000e10500000400438000001210400000028450000000210400000430410000001211400000038410000000210400000400410000000e11200000414410000000610400000048450000000610e000812008100000002105000004004000000012114
  | 7, 0, 9 => 0x11430481000000c111200000210410000381221200002048810000000210000000038448000000210400000314438000000210400000048448000000210400000048448000010c1040000000841000000c510e000000284100000012112000000384100000002112000c130081000354402040000002844800000c01040000040041000304c020400000018450000008511200000300410000280e204000000484500000012100
  | 7, 0, 10 => 0x214410000000a10e00000400450000000211200000048410000000211200000008400000000a10e00000048450000000211200000048448000280e21200000400438000000210e00000008410000000211200114304848000000611400000028448000001211400000028400000000210e00000300410000001210400000038414000000a114000001044140040500212000000084380015500212000004044480000002100
  | 7, 0, 11 => 0x314448000010510400000100410000010010000000314438000000a11200055400810000000a10400000018410000000a1120000003845000000c511200055400810000000610400000028438004504120400000200448000010010400000038450000010010400000028448000000e11200000400450000010810400000038410000000e1140000203884800001051120000040045000001051120000003844800000c9112
  | 7, 0, 12 => 0x8448000001211200000414448000000e1050000e048810000000211200000400438000000210400100008810000004111200000008414000180e2120000003841000000c911400000028438000000610400000314448000008111200105028848000000a10400000018448004140e21200000204410000000211200000018448000000211400000008448000010010e000003204100000002104000000384000000012105
  | 7, 0, 13 => 0x304410004350c21200000038448000010010400000204410000010011400000314438000000610000000028448002148420400000038438000008111200000400438000000a11200000414448000000e10e00000038410000000211200000414410000010011400000314438000010910000000028400000010511200000400410000000a11200000048414000000610400002028810000000e1120000003841000000c010e
  | 7, 0, 14 => 0x8400000010010400000008414000080a21200000314438000000610500000314438000000a1120000031441000001001040000030043800000021000000000841000000c010400000038438000008010400000028410000000611200000008450001044020400002028848000000211200000008448000010911200000018410000001211400115200848000000610400000018410000000a104000000384500000006114
  | 7, 0, 15 => 0x28438000000a10400000038448000010910000000038448000000610e0009530084800001051050010500884800324c820400000414410000000210e00000038448000008010400000324448002544020400000018414000000610e0000003841400000061040000040041000000c1102000004144480000100104000000484500000012114000002004100035081204000004144480000105112000000184100000002105
  | 7, 1, 0 => 0x38438000000e11400000048448000000e11400000424448000000610e0000a038848000001211200000048410000010011400000018438000000a11200000018400004548021200000038450000010510400000018410000001210e00000018410000000a11400000028448000000211200000104400004140e20400000038400000000e1040000000843800000c510e00000008438000000210000000008448000000610e
  | 7, 1, 1 => 0x4841000000121120000040045000000c010400000424450000010511200000400450000000e11400000048448000000210e00000018448000000210400000204448000000a11200000204448000001210e00000028450000000210400000424450000000210500000038448000001211200014414810000000a11400000304408004500620400000048414000381220400000018400000000a1040000000845000000c9112
  | 7, 1, 2 => 0x314410000000210400000038414000000a11200000310410000001211200000038410004140a20400000048448004140e21200000038414000000a10000002038810000000610500101400848000000610400000038438001550021200000008410000000e10000000008414000000e10400000414448000000e11200000038450000000e1140000e048848000000a11200000008400000000a112000004004100000100100
  | 7, 1, 3 => 0x48448000001211400000008438000008510400000008448004500620400000314448000000a10400000214448000000610e00006048810000000210500000018448000010010400006048810000004010400000008438000001210e0000041444800000c11120000e048848000000a10e00000008450000000e104000004004100000012112000d4104810000010010e00055200848000010510400000104410000000a105
  | 7, 1, 4 => 0xd510081000000061120000001841000304c02040000000844800000021140000003841000000c010400000400438000010010000000048438000000211400000038448000280e2040000030041000001001140000040441000000c410400000424448000000611200000008438000000210000000008448000000a11400100038810000008511200000008448004000a2040000001841400000c510e000000384480000002114
  | 7, 1, 5 => 0x21441000000021140000003841400008062040000010440000354402040000004841000001001140000001840000000061120000002845000000061120000004841000000c010400000210410003548021200000424400000010911400000028410000000610e0000002841400000021040000040045000000c510e00000400410000001211200000104448000001210500000028438000000e112000004244000000081112
  | 7, 1, 6 => 0x28438000000210400000008448000010510400000028450000001210e00006028810000010011400000038438000000210500000400438000180a2040000020441000400062040000001840000304c021200100018810004540220400000028400000000a10400000038448001548021200006048810000010011400000300438000001211200000214410000000e11200000008414000001210e000000384480000105104
  | 7, 1, 7 => 0x48448000000a10e0000002843800000061050000a038848000000210e00000048438000008510400000324450004504120400000324400000010010e00000028448000000e11400000028448004140220400000008410000000e112000000284480000105104000000084100000006104000000084480041402204000550488480045006204000000384500000084104000554008100000012100000002144480000006104
  | 7, 1, 8 => 0x300438000010910000000028400000000a10400000410410000000e11200000008410002148420400000400410000000a10400000028438000010010400000200410000000e10400000038448000000211200000008400000010010400000018410004500620400000038448000010d11200000304448000004010400101400848000000e11200000048410000000e10400000008410000000211400000018448000000a114
  | 7, 1, 9 => 0x400400000000a1040000002841400000021040000040043800000061040000032044800000c510e00000200410000010010400000018438000008511200105038848000180a20400000038410000010510400081200848000000210000000414448000000a11400100018810000001210400000414448000000a1040000000840000000c810400000008448000010911400000314438000000211200000028448000000e100
  | 7, 1, 10 => 0x38410000000a10400000008448000000a10400000008448000010010400000028448000010010400000400410000000a10500000038448004508121200000018410000000211200000400450000000a11200000038438000000e11200006048810000001211200000018448000010510500000048410002048020400000038400000000210e00000028438000000a10e00000048448000000e112000002044480000002105
  | 7, 1, 11 => 0x414410000000210e0010510484800001051040000003841000000021120000040045000000121040000002841000000021050000040041000000c910400000400410000000e11200000210410000181221200002038810000000610e00000104448000010510500000028438000001211400000028410000000e10e00000038448000000a10000000430448000080e212000003004100000105112000004144100000006104
  | 7, 1, 12 => 0x2841000000c410400000414410000000610000000048438000000e10000000018438000010010400000400450000004110400000400410000000e10400000018438000000a11200000400400004500620400000314438000000e1040000031443800254402040000040041000000021040000003841000000061120000004840000250412040000002840000000121040000020041000001051050000004843800000c510e
  | 7, 1, 13 => 0x400450000000210e00000304448000000211400105018810000000610400000028414000000610e000c531081000000021000000003841000204802040000000844800000c510e00000400410000004111200055048848000000e1120000002841400000c01040000040041000000c510e0000000843800450c121200000430410000010511200000324400000000a10400000028410000000e114000000384480000105104
  | 7, 1, 14 => 0x38448000010010400000028414000181220400000008448000590521200000400438000008110300041100810000004010400000028448000081221200000048448000004110500000038448000000e11400114204810000000a10e00000204410000010511200000414410000181221200000314448000000610400000008400004540220400000304408000010011400000038438000000e114000002144100000041112
  | 7, 1, 15 => 0x18410000000610000000048400000280e2040000a038848000010010e00000400450000000a11200081200848000000e11200000028448000010510400000018448000000a10e00000008410000000e10000000104410000010910000000008400000000a10400002048810003504120400000008450000000210500000304448000000a11200000400438000000a10e000000484500000100100000060388100000006100
  | 7, 2, 0 => 0x324448000000e1120000002841000001001140000002844800001051050000004841000000c911200000048448000281220400000008410000000211200000400438000281220400000314438000001211200000028400000000e10400000414448000000a11200000018410000000a11400000028448000000a10500000008448000004010400000008438000080620400000038410000000a10e000001004100000105105
  | 7, 2, 1 => 0x304448000000211400000314448000010911400000048448000000a10e00000028448000000a10400000018450000010910000000300438000010511200000400410000000e10e0000201884800000061120000040041000001011120000003841000000021120000032041000000c010400000008448000001211200000028410000000e11400000314438000000a10000000424400000010511200000008414000000a104
  | 7, 2, 2 => 0x8448000000a11200000008410000008010400105008810000000a10500000424450000080a20400000008450000001210000000018410000000210000000008438000000e11400105028848000000e10500000414410004000220400000414448000000610e00006028810000000611400000414448000010c10400000400450000000210e0000000841000000c01120000003843800000c510e001000188100000109100
  | 7, 2, 3 => 0x210410000590020400115200848000010910000000400410000590020400000008448004000a20400000018410000000a10e00000018400002048021200000320410000000a10e00100028810000000e1000000010441400000061120000003840000000c810400000038410000010510400000028410000010910000000400400000010d112000001004100000012114001051048480000002104000000184100000012114
  | 7, 2, 4 => 0x203881000000121120000003843800000021000000003841000000c810400002038810000000611200000008448000001210400000048438000010511200000414414000000e1040000003844800000c11120000003844800000021050000021441000000061040000003845000000c911400000048448000000e11200000400438000010010400000038438000000e10400000430410000000a104000004104100035081204
  | 7, 2, 5 => 0x8448000001210e00000400450000000610000000424400000010011400000038400000081221200000018400000000611400000104448004250821200000008448000010010e00000434448000004110400000400400000001211200000430448000000e11200000300448000000210400000038410000010c11200000048438000001210000000048438000001210400000018448000000e10e000000284480000006104
  | 7, 2, 6 => 0x404448000008111200114304810000000e1050011430481000028122120000000844800001051040000002841000000c110200000008438000000e11400000028448000001210000000400410000000e1120000021441000000c510e00000008448001548021200000038410000000e1040000040041000001001040000001841000000c011200000048438004140e20400000038450000010c10400000038410000000e114
  | 7, 2, 7 => 0x31041000324c820400000404448000000610e00000038414000000a10e0000003844800000411040001441481000000c91140000a048810000000610e00000008410000001211200000400410000010010400000008410000010010e00000400410000000a10400000008450000010511200000028438000000210e000000484380000006104000000084480000080104000000084500000006112000003204100000002114
  | 7, 2, 8 => 0x48414000010010e00055048810000000211200000038410000000610400000400438004504120400000314438000000210500081200848000000a10000114104810000000a10e00002018848000008110300000038400000000a10e00000038438000000210e00000028410000001211200000038438000001210400000018448000010010e000004004000000080104000004004380000100104000000284480000002100
  | 7, 2, 9 => 0x38410000010911200000300438000000210400000410410000010c10500000008450000000e10000000414448000180a212000000284100000002105000004204100000040104000c1300810000010010000000008450000000a10e00000304448000001210e00000048448000000210400000324448000010010400000028438000010010e00000048438000000e100000000184100000006100000003244500000105104
  | 7, 2, 10 => 0x38410000000e10500000400400001044020400000048400000000610400000314438000001211400000400410000010911400002048810000010c1040008120081000314c420400000320410000000a10e00000048410000000a10400000018448000010010e0000040043800000c510e00000204448000000e11200000038448000000610400000404448000010010e0000020441000000c510e0000a0488480000100104
  | 7, 2, 11 => 0x8438000000610400000008448000000611200000038448000010010e00016414848000010010e0000603881000000121000000000844800001051050000002840000000061050000040044800000c010e0000004841000000c010400000018410000000e10400000048400004140a20400000028410000010010400000028400000000a11200000314438000010c10400000048438000010010400000018448000000610e
  | 7, 2, 12 => 0x28450000000e11200000400400000004110000000008450004144121200002028848000000a112000c1300810000000e1040000031443800000c010400000048448000180a21200000104410000000e1120000004841000314c42040000a038810000000e1050000a048810000000e1040010942084800000c91120010003881000450c121200115008810000000210000000414410000000e11200000018414000000e100
  | 7, 2, 13 => 0x114018810000000e10e00000310410004508121200000214410000004010400000104400004140e20400000038400000000e11200000028410000000e11400000038448000001210400000038448000080a20400000008448000000a11400000028438000010010000000400410000000a104000004344480000100114000000284100000109100000004004100040002204000002144480000100104000000384480000002104
  | 7, 2, 14 => 0x18410000000e11200000420410000000e10e00006048848000010511200000028400000510520400000008414000000e10000000048438000510520400000028448000000610400105008848000010511200000028410000010010000000008400000000a10400000008448000000e100000003144480000012112000000084500000002112000d54008480000812212000060288100000084104000004004100000100100
  | 7, 2, 15 => 0x41441000351052120010000881000000c410400000038410000000e11200000038414000000a104000c932084800000021040000002843800000021040000002841000000121120000000845000000c910400000008448000010911400000008448004140e21200002048848000000611200016400810000010010400000008438000010511200000008410000000210000000400410004350c212001000288100015500204
  | 7, 3, 0 => 0x18400003508120400000200410000000610400000018410000000e10000000400410000000210400000048410000001210400000028400000000210400000410410000000211200000008438000000210400000028400000001210e00000028410000000a11400000038410000010910000000018438000000611200000400410000080e20400000320410000010511200000028400000000a112000852108100000105112
  | 7, 3, 1 => 0x48410000000e10e0001641484800450c120400000048400000000610400000048438000008410400000104410000081221200000200410000000211200000008448000010d11200000018400000001210500000028450000004110000000424450000000a10e00000314438000008110400000018410000000211200000414414000010511200000028450000010511200000400400000010010e0000000841400000c0104
  | 7, 3, 2 => 0x48448000000e11200000400438000000210e00002028848000010510400000008448000080e21200000018400000000a10400000048448000000a10400000028448000000a1120000040041000000c111200000424450000010010400000018450000010010400000008450000000210e00000018450000080620400000400410000010511200000018410000000e112000000284480000041112000020188100000108104
  | 7, 3, 3 => 0x1844800000c510e00000008410000000210400000028450000004010400000038410000000210e00000018448000000a1040000002841000000021000000003841000000021120000040040000405002120000001840000324c8204000d520084800155002120000002840000000121050010501881000001001040011410481000001001040000041444800000061040000e048848000000a10e00000414448000000a112
  | 7, 3, 4 => 0x8410000000a10e0000040040000000121120000001841000304c02120000040043800414022120000001844800000121040000201881000000c911400114018810000010511200002018848000010010e00000324450000000610500114204810000000a1040000021041000000811040000001843800000c510e00000320410000000210400000048400000000e105000000084100000002112000000284100000105112
  | 7, 3, 5 => 0x414410000010911400000214448000000611200000008400000000a10400000028438000000210e00000048410000000e10e00000008438000000211200000414410000000210400000400410000010c11200000414410000381220400000028410002148420400000430410000000e10400000038400000000a10e00000214410000001210000000414410000000e10400000304410000000e112000000284480000100104
  | 7, 3, 6 => 0x104410000000a1120000004845000001051040000e048848000008110400000414414000000210400000038414000000a100000004204480000006105000000484480000109100000000284140000041112000060388480000012112000000084480000006104000c9320848000008111200105028848000010911200000008448000000a10e000000384380000006112000000384100000012112000000084480000105104
  | 7, 3, 7 => 0x400410000000611200000038410000000210400000400400000010511200000314438000000a1040000042440000000061040000003840000000021120000004843800000411120000004845000000061040000030043800001001040000000843800001091000000040040000000c510e0000031041000000c511200000028448000008111200055400848000000a10400000038448000000a105001150088100000105112
  | 7, 3, 8 => 0x840000000c0104000000484480000100112000c1300810000000a10400000048410000000a1040000043044800000c010400000100410000010011400000018410000010511200000400410000280e20400000048448000000610e00000008448000000e10000000100410000001210400100038810000010011400000414414000000610000000400400000000a10400000414410000281220400000048448000000e112
  | 7, 3, 9 => 0x4843800001051120000004844800000c911200002038848000000e10400000038448000010011400095100810000010010400006038848000010910000000204448004140a21200000008410000000210000000304410000000611200000018448000000a1040000001840000000c1112000000084100000002104000004304100000002100000000084500000002112000000084100000085112000004104100041441212
  | 7, 3, 10 => 0x18448000000211200000048414000281221200000018450003548021200000048400000000211400000048450000004111200000028438000000a10400000038450000000a1120000000845000000c510400006028810000010010e00000200410000010011400000048400000510520400000400410000000610400000038448000000e11200000400410000000e114001000188100002812212001050388100025440204
  | 7, 3, 11 => 0x420410000010010400000038400000000211200000008450004140620400000324448000000e10e00000038448000000a1040000000843800000021000000004844800000021040000031041000250c120400000018448000010010400000008438000010011200055400810000000610400000414410000000211200000018414000001210400081200810000000a10000081200810004000a2040000004841400000c5112
  | 7, 3, 12 => 0x414414000081220400000400410000001210e00000018448000000a10000000048410000000211200000048448000081220400000424400000000a1120000004841000000021120000030043800450c121200000414448000000210e00000324448000001211200000210410000001210500000028410000010410400002028848000010010000000300410000001210e0000003844800450812120000004841000304c0212
  | 7, 3, 13 => 0x40040000000c510e00000400450000000a1120000002840000000061050000002845000000c810400006028848000010d11200000414410000010511200000038400000010010400000038448000010111200000028400000000211400000028438000010010000000424400000010810400000310410000000e11200000048438000008510400000424448000008410400000018450000010010e00000204410000180a212
  | 7, 3, 14 => 0x18410000000e11400000028400001541220400000400448000000211400000400410000000a11400000400410000010011400000048450000000a10400002018810000000a11400000038400000010c10500000048400000010010400000028450000008010400000038438000000211400000018410000010010000000038400000000e11400000414448000000210400000018414000010010400000018400000010010e
  | 7, 3, 15 => 0x38448000080a20400000028448000000e10e00000324448004000220400000028448000010010e00000400410000000a11200000028410004000220400000400410000000e1120000002840000001051040000000840000001001040000020440c000000a10e0000003845000324c82120000032441000000c110200000018448000000610e00000018400000000e10400000018414000010c105000004004380000100114
  | 7, 4, 0 => 0x38448004350c21200000214410000000610e00000400410000000e11200000038410000080e21200000300438000001210400000008448000000e11200000008448004500620400000008410000000e10e0000004844800000021120000202884800000121120000002843800000c011200000038438000000210400000400438000000611400002028810000010511200000400410000010010e000000284100000100104
  | 7, 4, 1 => 0x4841000001051050000032445000000811040000000840000000c510e00006038810003504120400000028448000000210400000008410000000e11400000414410000010511200114018810002148420400000028448000000a1000000001841000001001140000003840000314c420400114204810000000610500105028810000010911400000038410000010910000000038400000000a104000004004000000081103
  | 7, 4, 2 => 0x845000000021050000004841400000061140000002841000000121040000001843800104402040011520084800000021040010d430848000000e112000002144100000002112000000184380000100114000d4204810001550021200000420410000000610400000018410003508120400000414448000000611400000008450000000a1120000004841400000c911400105008848000010010000000008450000280e212
  | 7, 4, 3 => 0x38438000000210e00000028410000000211200006048810000000a10000000038400004140e21200002048810000000611400105038810000000610400000400410003548021200000008448000000210400000414448000000611400000028448004140e20400000038448000000a10e0000001841000000c911200114304848000000610e000000384100000012112000004144480000002104000000184480000012104
  | 7, 4, 4 => 0x414448000000610400000008438000000e10500000028448000001210400000104414000000210000000028410000000e1120000031444800000c911400000008438000008110400000008410000008410400000400450000590020400000038400000000210000000028414000000210e00055300848000000a10500000414410000000e112000000384100000105105000000084480000100100000000384140000002104
  | 7, 4, 5 => 0x400438000000210000000400410000010911400000008450000008410400000048410000000a10400000324450000010910400000200410001548021200000320448000001210000000414448000280e21200000008450000000e10000000008438000008111200000008400000000211400000028410000000610500000028448000000a1120000003841000001001040000002844800304c0212000000184500000006104
  | 7, 4, 6 => 0x4841000000c810400000008438000010010e00000008414000000e10400000028448000000211200000200410000000610400000028450000001210400000008448000000a10400000018410000000e11200000414410000001210500000204410000001210e0000002841000001091140000003841000000411120005504881000000061120000040041000001091140000040041000000c510e000000184140025440204
  | 7, 4, 7 => 0x40043800000121000010002881000038122120000040043800414022040000000841000000c4104000000284480000100104000004004100000108104000000184480000041100000000184000000012112000c9320848000000210500006028810002048020400000048400004140e21200000048448000000a11200000018450004000620400000414448000000a10500000028410000000610e000004244000000002100
  | 7, 4, 8 => 0x314438000010010400000400410000010911400000414414000000a11400000410410000000a10400055048848000000e10400000008438000010010000000048410004540220400000008448000010511200000324410000010911400000018400000000e11200000038448000001210000000304448000010510400000048450004050021200000028448000000210e00055400848000010111200000424448000000a104
  | 7, 4, 9 => 0x104448000000a10500000028400000000e10400105028810000000e112000000284140000041112000004004380000012104000d510081000000121120000002841400000c010400000048400000008111200000008448003544020400000028400000000a10e00000028410000080e20400000310410000010511200000304408000000210500000038438000081220400000008450000001211400000414410000000e100
  | 7, 4, 10 => 0x214410000000e1000000020444800000811040010502884800000c510e00000008400000000611200000008448000000210400000008450000000211200000414448000010010000000008448004540220400000008438000000611200115200848000000e11200000008448000001210000115008810000000e10400000028410000080e21200000008448000010d1120000002843800154802120000000844800000c510e
  | 7, 4, 11 => 0x400410000000210000000400410000000e11200000038400000004110500000414414000000e11400000214410000004110400000414414000000a1120000003841000000c911200105028848004504120400000400400000000e10000000400450000001210400000008410000000210000000038438000000a11200081200848000010010000000028400000000a10500000104448000180e2120000031441000000c1112
  | 7, 4, 12 => 0x38400000010c1120011430484800038122040000001841000000021040000002841400414022120000040041000000c010400000400400000010911400002028810000000e1140000020041000001001040000004844800000121000011401881000000c010400000100410000000e11400100008810000010011400114018810000000a11400000018438000004010400000028410000000a112000000084480000041112
  | 7, 4, 13 => 0x18410000000e10400000018400000000610400114204848000010911400000038448000010010e00114204848000000210400000424450000000e11200000028410000010810400000400400000000e1000000021041000304c020400000028414000000610e000c9320810000001210400000028400000010010000000214410000010511200055200848000000211200000008414000010510500000400438000000a104
  | 7, 4, 14 => 0x18448000000a11400000048438000000210e000d4204810000000210e0000000841000018122120000001843800000c510e00000048448000000a10e00000038448000010010e0000001840000000c511200000028450000080e21200000400438002048021200000400438000000e11200000104414004144121200000204448000000e10500000008448000000a10e00000018438000004110500000300448000000e104
  | 7, 4, 15 => 0x28410000000e10400000300410004140e20400000008410000008410400000300448000280e20400000028450000001210000000400410000000211200000400450000000211200000430448004000e20400000028450000000e11200000038400000004110500000038438000000611400000414410000000a10400000048438000001210400000214410000000a11200000400400000000a112001142048100000100104
  | 7, 5, 0 => 0x40041000000021040000000841000000c51040000000844800000121140000040041000000c510e00000048410000000a10500002048848000000210e0000002844800001051040000040040000000c510e00000300438000008510400000008410000000a1040000000841000000c510e00000018438000000210400000304448000010510500000028414000000e1050000040041000104402040000001841000324c8204
  | 7, 5, 1 => 0x55400810000000210e00000018410000000610400000038450004140620400000400438000010010400000018438000000a10e00000320410000000610400000028448000000a10e00000008448000004010400000018450000000a1050000a048810000010010e00000038400000000a10400000048414000000a10400000028448000000a11200000018448000010010400000200410000000e112001051048480000002104
  | 7, 5, 2 => 0x200410000001211200000320410004508120400000038448000000210400115200848004508120400000104400000000e1120000003844800000c810400000028438000000e10000000018410000000a11400000038448000010510500000028438000000210400000048448000010911400000008400000000a10e00000008438000010010000000018450000000a10e00000028410000000e112000000084480005905212
  | 7, 5, 3 => 0x200410000000e11400000028410000010510400000214448000081221200000200410000000a1000000041441000000121120000004840000001001140000000841000001001040000000844800350412040000041444800450c120400000410410000000a1120000201884800350412040000001844800000c010e00000414414000000210400000430410000010010400000028448000000210e00000028448000000a100
  | 7, 5, 4 => 0x104414000001210e0000000844800001001040000041444800000c510e00000200410000000a10500000420448000590020400000018410000000e11200105018810000000210400000204448000001210e0000000840000000c011200100028810000000e10400000038414004508121200000420410000010010e0000031443800000061050000002840000000021120000003844800000c010400000008410000001210e
  | 7, 5, 5 => 0xa038848000000e10400000048450000000210e0000003844800000411050000000841000454022040000003841000324c821200000028448000080e2040000042041000000121120000020041000000021120000003840000000121050000042440000000021000000020041000154802120000604884800001051040000020440c000010511200000008410000004110000000038438000000a105000000384480035440204
  | 7, 5, 6 => 0x8450000010510400000400438000080620400000414448000001210000000018450000000211400000038414000000611400000038400000001210e00000320410000000211200000038414000280e212000000184500042508212000020188480000100100000d5200848000001210400000018448000180e20400000028448000001210500000324400000008011200000414410000000e114000000284100000041104
  | 7, 5, 7 => 0x430410000000210000000414410000001211200000008448004250821200000404448000004110400000018448000000210400000048450000000211200114018810000000e10400000028438000000e10000002028810000000e1050000003841000000c510e00000310410000010010e0000003840000001001000010503884800450c120400000018410004500620400000028438000004010400000414448000000210e
  | 7, 5, 8 => 0x204448000001210400000424450000000211200000214410000281221200000048438000010010e00000400438000000a10400000038414000001211400000028400000004010400000414410000010010400000018410004504120400000018414000010011400000104410000000e11400000008410000000611400000028400000590521200000324450000001210e0000010440000000c510e000004004500000104104
  | 7, 5, 9 => 0x320410000000611200000210410000000e1120000040041000000021040000040045000001091000000000840000001051040000002841000000c510e0000000840000000021140000004845000000c010400000048448000010010e00006048810000000211400000038414002148420400000008400000000e10000000008448000010010000000028448000000e10400000104448000000210e00000400400000000a10e
  | 7, 5, 10 => 0x400450000001210400000048410000000e11200000038414003510521200000038450000000210e00000414448000000a10e00000008438000000211400000214410000000211400000400410000001210400000018400000010511200000414448000000610400000400438000010010400000018448000000a10000000028438000010010e00000008450000000a11200000038450000000e11400000400438000000e100
  | 7, 5, 11 => 0x8438000000a10400100038810000000210e00114204848000008410400000038410001541220400000400410000000210400000008438000000e11400000008410000000611400055048810000000211200000048410000001211400000008448000180a2120000043444800000c81040000010441c000010511200000038450000010011400000008410000000e10e00055048848000000a10e000000384480000002112
  | 7, 5, 12 => 0x38410000000210000000400410004140220400000018450000000611400000038414000000210400000424450000010c10400000400410000000210400000048400000000610400000038438004140620400000320410000000e11400095400848000180a20400055400810000000a11400000324448000000a1120000002840000000121040000040045000400062040000000844800000c8104000000184480000012100
  | 7, 5, 13 => 0x48448000000a10400109420848000001211200105028810000181221200000200410003504120400000018438000010010400000400410000000a1040000003844800000c510e00000038414000010910000000400410000080a212000004004100000012104000000284480025440204000000484140000006105001142048100000002114000c53108100000109114000004144480000080104000000384100000012100
  | 7, 5, 14 => 0x400410000000e1120000003840000000061040000031444800304c021200000008448000000210e0000040041000001001000000003843800155002040000020440c00000c111200006038810000008510400000028410000010c11200081200810000000e11400006038810000000a10e00014414810003504120400000400410000010510400000400450000000210400000008448000010010e00105028810000000a104
  | 7, 5, 15 => 0x38410000010010400000018448004144121200000038438000000e10000000048448000000610400000008414000010511200000424400000010510500000008448000010010000000008410000000e10000041100810000000210000000400400000000210500000204410000000e10e0000002841000028122120000001843800000021040000e04881000000021040000e0488480041402212000000084480000105112
  | 7, 6, 0 => 0x28448000001210e00000018410004350c21200000028450000180e2040000032444800000c110400000028450000000210400000400410000000a11200000028438000000a11400000018448000000e10500000400438000010010e00002028848000010d11200000028410000000a1120000004841000324c821200000008410000000e1120000040041000000c9104000004004100000100104000000484480000109114
  | 7, 6, 1 => 0x414448000000a10500000048448004000e20400000048448000008510400000038400000180a21200000008448000010011400000028410000180e21200000204410000001210e00000414410000000210e00000104410000010410400000048400000000e10e00000038438000000e11200000008410000001211200000038410000000a10000000008410000000611400000324448000000210400000018438000000e112
  | 7, 6, 2 => 0x12100000000284480041402212
  | 8, 0, 0 => 0x8410000010c1040000032044800000c810400000200448000000e10400000400448000000a10400000048448000000211200000104448000010811200000204448000000610400000430448000010511200000424448000000211200000048448000000611200000200410000000a1120000002841000000c111200000214410000000e10400000104448000000e112000000484480000006112000004044480000100104
  | 8, 0, 1 => 0x41444800000c41040000043444800000c410400000104410000000a1120000001841000001081040000021041000000c11040000041441000000c51040000041444800001091120000000844800000c01040000002844800000021040000000841000000c81120000030444800000061040000001841000001011120000000844800000c5104000002044100000040104000004004480000081104000002004100000109112
  | 8, 0, 2 => 0x400448000000e11200000038410000004110400000314448000010911200000008448000008410400000008410000004111200000018410000010410400000314448000008110400000324410000000611200000008448000010510400000028448000008111200000304448000000e11200000028410000010010400000048448000000610400000414448000010010400000400410000000a112000004044480000040104
  | 8, 0, 3 => 0x21041000001051120000041041000000c91120000041444800000c010400000314448000008510400000304410000008510400000028448000000210400000430410000000a1120000031441000000c011200000320410000000e10400000300410000000a1040000040041000000851120000003844800001001040000021444800000121040000021441000000c91120000021444800000c81120000002841000000c9104
  | 8, 0, 4 => 0x10041000000c810400000404448000000e1040000042044800000811120000003844800000021120000031041000000c911200000310410000004110400000104410000010c1120000004844800001051040000041441000000c51120000001841000000021120000043044800000121120000042041000000c01120000020044800000801040000020041000001081120000020444800000c1104000004204480000108104
  | 8, 0, 5 => 0x400410000010010400000420448000000611200000204448000010d1120000030444800000c91040000032441000000121040000003844800000121120000020041000000c110400000200448000010111200000300448000000210400000214448000010d11200000018410000000e10400000204410000000e11200000200448000008510400000008410000010c10400000430410000010d112000001004100000104104
  | 8, 0, 6 => 0x8410000000611200000018410000010c11200000048448000008110400000320448000010511200000008448000010011200000028448000010c11200000038448000010410400000304448000001211200000100410000000a10400000028410000010911200000038410000000e1040000041444800000c410400000008448000004110400000200448000000a11200000104448000010510400000304448000000a104
  | 8, 0, 7 => 0x320410000000a10400000038410000000210400000430410000010010400000320410000001211200000038410000010010400000038448000010511200000320448000001211200000324448000010810400000420410000008410400000210410000010011200000404448000000a1120000030041000000c01040000042444800000c91040000031441000000c5104000004344480000041112000000084480000100112
  | 8, 0, 8 => 0x314448000000a11200000310410000004110400000008410000008511200000324448000000e1120000042041000000841040000030041000000c011200000414448000000a11200000008448000008010400000320448000000a1120000031441000000c11120000040044800000c511200000414448000000610400000304410000010911200000028448000000e112000001044480000006104000000184100000085104
  | 8, 0, 9 => 0x42044800000121120000020444800000801120000040041000000c910400000048410000010811200000200410000008111200000410410000000e10400000410410000008511200000300448000000e11200000028410000000a1040000040041000001001040000021441000000021040000032044800000c011200000018410000000610400000100410000008110400000324448000001210400000048410000000a104
  | 8, 0, 10 => 0x314410000000211200000434448000010c11200000008410000010c10400000008410000010c1040000032444800000121120000032041000000c810400000038410000000e10400000404448000010511200000028410000010d11200000400410000008110400000100410000000210400000038448000000a10400000038410000001210400000310410000008011200000104410000000211200000414410000010c112
  | 8, 0, 11 => 0x30441000000c011200000304410000010810400000210410000000e1120000030041000000c9104000000484480000104104
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 13 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x4_1 roots_x4_1 7 s ws hint
  | 1 => checkCutEntry dom_x2_0_x4_0 roots_x2_0_x4_0 5 s ws hint
  | 2 => checkCutEntry dom_x0_1 roots_x0_1 6 s ws hint
  | 3 => checkCutEntry dom_x0_1_x2_0 roots_x0_1_x2_0 5 s ws hint
  | 4 => checkCutEntry dom_x1_0 roots_x1_0 8 s ws hint
  | 5 => checkCutEntry dom_x5_0 roots_x5_0 7 s ws hint
  | 6 => checkCutEntry dom_x1_0_x3_1_x5_0 roots_x1_0_x3_1_x5_0 4 s ws hint
  | 7 => checkCutEntry dom_x4_1_x5_0 roots_x4_1_x5_0 5 s ws hint
  | 8 => checkCutEntry dom_x1_0_x3_1 roots_x1_0_x3_1 5 s ws hint
  | 9 => checkCutEntry dom_x0_1_x1_0_x2_0 roots_x0_1_x1_0_x2_0 4 s ws hint
  | 10 => checkCutEntry dom_x0_1_x2_0_x4_0 roots_x0_1_x2_0_x4_0 4 s ws hint
  | 11 => checkCutEntry dom_x1_0_x5_1 roots_x1_0_x5_1 6 s ws hint
  | 12 => checkCutEntry dom_x0_0_x4_1_x5_1 roots_x0_0_x4_1_x5_1 4 s ws hint
  | 13 => checkCutEntry dom_x0_0_x4_1_x5_0 roots_x0_0_x4_1_x5_0 4 s ws hint
  | 14 => checkCutEntry dom_x2_0 roots_x2_0 7 s ws hint
  | 15 => checkCutEntry dom_x0_1_x1_0 roots_x0_1_x1_0 5 s ws hint
  | 16 => checkCutEntry dom_x0_1_x4_0 roots_x0_1_x4_0 5 s ws hint
  | 17 => checkCutEntry dom_x3_0_x5_1 roots_x3_0_x5_1 5 s ws hint
  | 18 => checkCutEntry dom_x5_1 roots_x5_1 8 s ws hint
  | 19 => checkCutEntry dom_x3_0_x4_0_x5_1 roots_x3_0_x4_0_x5_1 4 s ws hint
  | 20 => checkCutEntry dom_x4_0 roots_x4_0 7 s ws hint
  | 21 => checkCutEntry dom_x0_0_x5_0 roots_x0_0_x5_0 5 s ws hint
  | 22 => checkCutEntry dom_x3_1_x5_0 roots_x3_1_x5_0 5 s ws hint
  | 23 => checkCutEntry dom_x0_0_x5_1 roots_x0_0_x5_1 5 s ws hint
  | 24 => checkCutEntry dom_x3_0_x4_0 roots_x3_0_x4_0 5 s ws hint
  | 25 => checkCutEntry dom_x3_0 roots_x3_0 6 s ws hint
  | 26 => checkCutEntry dom_x4_1_x5_1 roots_x4_1_x5_1 5 s ws hint
  | 27 => checkCutEntry dom_x1_0_x4_1_x5_0 roots_x1_0_x4_1_x5_0 4 s ws hint
  | 28 => checkCutEntry dom_x1_0_x2_0 roots_x1_0_x2_0 5 s ws hint
  | 29 => checkCutEntry dom_x3_1 roots_x3_1 6 s ws hint
  | 30 => checkCutEntry dom_x2_0_x5_1 roots_x2_0_x5_1 5 s ws hint
  | 31 => checkCutEntry dom_x2_0_x4_0_x5_1 roots_x2_0_x4_0_x5_1 4 s ws hint
  | 32 => checkCutEntry dom_x1_0_x5_0 roots_x1_0_x5_0 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_63 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_1_x2_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x3_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_1_x1_0_x2_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_1_x2_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_1_x1_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_1_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x4_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x4_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x2_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x4_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x5_0 _ hc
  · contradiction
def p0Subs : List Nat := [14, 21, 20, 3, 2, 0, 4, 18, 5, 13, 9, 29, 16, 22, 25, 15, 10, 8, 6, 1, 24, 17, 23, 7, 27, 28, 19, 12, 31, 30, 32, 26, 11]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_63 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq, Bool.or_eq_true] at h; rcases h with h1 | h0
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2
  · obtain ⟨k, _, hk⟩ := List.any_eq_true.1 h0; exact checkCutByIdx_sound hk
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_63 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_63 goalM u ys) : RunD dom_63 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_63 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 52 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 52 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 64 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 64 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_64 : ∀ i, 64 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 64 64 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_128 : ∀ i, 128 ≤ i → i < 192 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 64 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_192 : ∀ i, 192 ≤ i → i < 256 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 64 192 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_256 : ∀ i, 256 ≤ i → i < 320 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 64 256 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_320 : ∀ i, 320 ≤ i → i < 381 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 61 320 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 381 → Z 6 i = true := (range_split (range_split z6_0 (range_split z6_64 z6_128)) (range_split z6_192 (range_split z6_256 z6_320)))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 64 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_64 : ∀ i, 64 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 64 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_128 : ∀ i, 128 ≤ i → i < 192 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_192 : ∀ i, 192 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 192 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_256 : ∀ i, 256 ≤ i → i < 320 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 256 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_320 : ∀ i, 320 ≤ i → i < 384 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 320 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_384 : ∀ i, 384 ≤ i → i < 448 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 384 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_448 : ∀ i, 448 ≤ i → i < 512 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 448 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_512 : ∀ i, 512 ≤ i → i < 576 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 512 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_576 : ∀ i, 576 ≤ i → i < 640 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 576 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_640 : ∀ i, 640 ≤ i → i < 704 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 640 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_704 : ∀ i, 704 ≤ i → i < 768 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 704 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_768 : ∀ i, 768 ≤ i → i < 832 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 768 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_832 : ∀ i, 832 ≤ i → i < 896 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 832 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_896 : ∀ i, 896 ≤ i → i < 960 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 896 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_960 : ∀ i, 960 ≤ i → i < 1010 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 50 960 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 1010 → Z 7 i = true := (range_split (range_split (range_split (range_split z7_0 z7_64) (range_split z7_128 z7_192)) (range_split (range_split z7_256 z7_320) (range_split z7_384 z7_448))) (range_split (range_split (range_split z7_512 z7_576) (range_split z7_640 z7_704)) (range_split (range_split z7_768 z7_832) (range_split z7_896 z7_960))))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 64 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_64 : ∀ i, 64 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 64 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_128 : ∀ i, 128 ≤ i → i < 192 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_192 : ∀ i, 192 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 192 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_256 : ∀ i, 256 ≤ i → i < 320 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 256 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_320 : ∀ i, 320 ≤ i → i < 384 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 320 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_384 : ∀ i, 384 ≤ i → i < 426 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 42 384 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 426 → Z 8 i = true := (range_split (range_split z8_0 (range_split z8_64 z8_128)) (range_split (range_split z8_192 z8_256) (range_split z8_320 z8_384)))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 34 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 34 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 10) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
  · exact fun i hi => z7 i (Nat.zero_le i) hi
  · exact fun i hi => z8 i (Nat.zero_le i) hi
  · exact fun i hi => z9 i (Nat.zero_le i) hi
  · exact fun i hi => z10 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool := scr dom_63 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 6 5 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : RunD dom_63 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_63 roots_63 goal_all 11 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_63 goal_all := by
    have h0 : isConstB dom_63 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_63
theorem low_63 : Lower dom_63 roots_63 goal_all 11 := S_63.noCircuit

def pt6 (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val
theorem roots_63_bits : ∀ r : Fin 64, roots_63.map (·.testBit r.val) = List.ofFn (pt6 r.val) := by decide +kernel
theorem dom_63_lt : ∀ r : Fin 64, dom_63.testBit r.val = true := by decide +kernel
theorem lower_to_circuit6 (f : (Fin 6 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 64, T.testBit r.val = f (pt6 r.val))
    (hncT : ¬ IsConst dom_63 T)
    (hlow : Lower dom_63 roots_63 T lb) :
    ∀ t : ℕ, HasCircuitSize 6 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ roots_63, Avail mask256 roots_63 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots_63 hfan 0 roots_63 roots_63 rfl hsup0
  set out := (execN C.gates roots_63).getD C.output 0
  have hout : out &&& dom_63 = T &&& dom_63 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 64
    · rw [dom_63_lt ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots_63 r (by omega) (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [roots_63_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots_63).map (·.testBit r)).getD C.output false =
          out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots_63)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt6 r)).trans (hT ⟨r, hlt⟩).symm)
    · have hd : dom_63.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h64 : dom_63 < 2 ^ 64 := by decide
        exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : Avail mask256 bank out := by
    by_cases hi : C.output < (execN C.gates roots_63).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hd63 : dom_63 &&& mask256 = dom_63 := by decide
  have hm256 : mask256 &&& mask256 = mask256 := by decide
  have houtm : (out &&& mask256) &&& dom_63 = T &&& dom_63 := by
    rw [Nat.and_assoc, Nat.and_comm mask256 dom_63, hd63, hout]
  have hnc_m : ¬ IsConst dom_63 (out &&& mask256) := fun hc => hncT (by rcases hc with h0 | h1; exact Or.inl (houtm.symm.trans h0); exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd63]))
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 hnc_256 hr hav_out
  have hws63 : ∀ w ∈ ws, Avail dom_63 roots_63 w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_63, hd63]⟩
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd63 hd63 hnc_m hrun (show NatReach dom_63 roots_63 0 roots_63 from rfl) hws63
  have hL := hlow q next hq (avail_of_eq houtm hav_q)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩], 16⟩
theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by simp [wit, PEqualNP.MetaComplexity.Monotone2]
theorem wit_size : wit.size ≤ 11 := by decide
theorem wit_eval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = ((fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4276153568) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))) x := by decide +kernel
theorem hT6 : ∀ r : Fin 64, goal_all.testBit r.val = ((fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4276153568) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))) (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4276153568) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 11 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4276153568) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_all 11 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_38977_aux

theorem PEqualNP.Outside.L_meta_38977 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4276153568) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4276153568) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s hs
  have hlb : 11 ≤ s := PEqualNP.Outside.L_meta_38977_aux.lower s hs
  exact ⟨PEqualNP.Outside.L_meta_38977_aux.wit, PEqualNP.Outside.L_meta_38977_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_38977_aux.wit_size hlb, PEqualNP.Outside.L_meta_38977_aux.wit_eval⟩
