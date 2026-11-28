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

namespace PEqualNP.Outside.L_meta_36378_aux

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

section RunFacts
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
end RunFacts

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

def moveBits (tag d w : Nat) : Nat :=
  ((w &&& tag) <<< d) ||| ((w >>> d) &&& tag) |||
    (w ^^^ ((w &&& tag) ||| (w &&& (tag <<< d))))

theorem moved (tag d i w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d + i)
       else if (tag <<< d).testBit i then w.testBit (i - d) else w.testBit i) := by
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  simp only [moveBits, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and,
    Nat.testBit_shiftRight, Nat.testBit_xor] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind

theorem move_hom (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) (a b : Nat) :
    moveBits tag d (a &&& b) = (moveBits tag d a &&& moveBits tag d b) ∧
    moveBits tag d (a ||| b) = (moveBits tag d a ||| moveBits tag d b) ∧
    moveBits tag d (a ^^^ b) = (moveBits tag d a ^^^ moveBits tag d b) := by
  refine ⟨?_, ?_, ?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, moved tag d i _ h] <;>
    split_ifs <;> simp

theorem move_zero (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) : moveBits tag d 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro i; rw [moved tag d i 0 h]; split_ifs <;> simp

def applyMoves (ms : List (Nat × Nat)) (w : Nat) : Nat :=
  ms.foldl (fun acc p => moveBits p.1 p.2 acc) w

def moveOK256 (p : Nat × Nat) : Bool :=
  (p.1 &&& (p.1 <<< p.2) == 0) && (moveBits p.1 p.2 mask256 == mask256)

theorem applyMoves_hom (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true) :
    (∀ a b, applyMoves ms (a &&& b) = applyMoves ms a &&& applyMoves ms b) ∧
    (∀ a b, applyMoves ms (a ||| b) = applyMoves ms a ||| applyMoves ms b) ∧
    (∀ a b, applyMoves ms (a ^^^ b) = applyMoves ms a ^^^ applyMoves ms b) ∧
    applyMoves ms 0 = 0 ∧ applyMoves ms mask256 = mask256 := by
  induction ms with
  | nil => exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
  | cons p ps ih =>
    simp only [List.all_cons, Bool.and_eq_true, moveOK256, beq_iff_eq] at hok
    obtain ⟨⟨hz, hm⟩, hps⟩ := hok
    obtain ⟨hand, hor, hxor, h0, h256⟩ := ih hps
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a b; simp only [applyMoves, List.foldl_cons, (move_hom p.1 p.2 hz a b).1]; exact hand _ _
    · intro a b; simp only [applyMoves, List.foldl_cons, (move_hom p.1 p.2 hz a b).2.1]; exact hor _ _
    · intro a b; simp only [applyMoves, List.foldl_cons, (move_hom p.1 p.2 hz a b).2.2]; exact hxor _ _
    · simp only [applyMoves, List.foldl_cons, move_zero p.1 p.2 hz]; exact h0
    · simp only [applyMoves, List.foldl_cons, hm]; exact h256

theorem move_invol (tag d w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    moveBits tag d (moveBits tag d w) = w := by
  apply Nat.eq_of_testBit_eq; intro i
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  rw [moved tag d i _ h]
  by_cases h1 : tag.testBit i = true
  · simp only [h1, ite_true, moved tag d (d + i) w h]
    have h2 : tag.testBit (d + i) = false := by
      have htd := congrArg (fun v : Nat => v.testBit (d + i)) h
      simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.zero_testBit] at htd
      have hge : d ≤ d + i := Nat.le_add_right d i
      have hsub : d + i - d = i := Nat.add_sub_cancel_left d i
      simp [hge, hsub, h1] at htd; exact htd
    have h3 : (tag <<< d).testBit (d + i) = true := by
      simp [Nat.testBit_shiftLeft, Nat.le_add_right, Nat.add_sub_cancel_left, h1]
    simp [h2, h3, Nat.add_sub_cancel_left]
  · simp only [h1, ite_false]
    by_cases h2 : (tag <<< d).testBit i = true
    · simp only [h2, ite_true, moved tag d (i - d) w h]
      rw [Nat.testBit_shiftLeft] at h2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
      simp [h2.2, Nat.add_sub_of_le h2.1]
    · simp [h1, h2, moved tag d i w h]

theorem applyMoves_inj (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true) :
    Function.Injective (applyMoves ms) := by
  induction ms with
  | nil => intro a b h; exact h
  | cons p ps ih =>
    simp only [List.all_cons, Bool.and_eq_true, moveOK256, beq_iff_eq] at hok
    intro a b h
    simp only [applyMoves, List.foldl_cons] at h
    have h1 := ih hok.2 h
    have := congrArg (moveBits p.1 p.2) h1
    rwa [move_invol p.1 p.2 a hok.1.1, move_invol p.1 p.2 b hok.1.1] at this

theorem applyMoves_runD {d Y s} (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd : applyMoves ms d = d) (hY : applyMoves ms Y = Y) {ws} (h : RunD d Y s ws) :
    RunD d Y s (ws.map (applyMoves ms)) := by
  obtain ⟨hand, hor, hxor, h0, h256⟩ := applyMoves_hom ms hok
  have hinj := applyMoves_inj ms hok
  have hneg : ∀ a, applyMoves ms (negD d a) = negD d (applyMoves ms a) := fun a => by
    simp only [negD, hand, hxor, h256, hd]
  have hand' : ∀ a b, applyMoves ms (andD d a b) = andD d (applyMoves ms a) (applyMoves ms b) := fun a b => by
    simp only [andD, hand, hd]
  have hor' : ∀ a b, applyMoves ms (orD d a b) = orD d (applyMoves ms a) (applyMoves ms b) := fun a b => by
    simp only [orD, hand, hor, hd]
  rw [← hY]
  induction h using Run.fold with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map _) ih
  | @one s a r save hne0 hned hnm _ ih =>
    have e1 : (negD d a :: kept save a r).map (applyMoves ms) =
        negD d (applyMoves ms a) :: kept save (applyMoves ms a) (r.map (applyMoves ms)) := by
      simp [kept_map, hneg]
    rw [e1] at ih
    refine Run.one save ?_ ?_ ?_ ih
    · intro e; rw [← hneg] at e; exact hne0 (hinj (e.trans h0.symm))
    · intro e; rw [← hneg] at e; exact hned (hinj (e.trans hd.symm))
    · rw [← hneg, ← List.map_cons, List.mem_map]; rintro ⟨x, hx, he⟩; exact hnm (hinj he ▸ hx)
  | @two s a b r conj ka kb hne0 hned hnm _ ih =>
    have eop : applyMoves ms (if conj then andD d a b else orD d a b) =
        (if conj then andD d (applyMoves ms a) (applyMoves ms b) else orD d (applyMoves ms a) (applyMoves ms b)) := by
      cases conj <;> simp [hand', hor']
    have e1 : ((if conj then andD d a b else orD d a b) :: kept ka a (kept kb b r)).map (applyMoves ms) =
        (if conj then andD d (applyMoves ms a) (applyMoves ms b) else orD d (applyMoves ms a) (applyMoves ms b)) ::
          kept ka (applyMoves ms a) (kept kb (applyMoves ms b) (r.map (applyMoves ms))) := by
      simp [kept_map, eop]
    rw [e1] at ih
    refine Run.two conj ka kb ?_ ?_ ?_ ih
    · intro e; rw [← eop] at e; exact hne0 (hinj (e.trans h0.symm))
    · intro e; rw [← eop] at e; exact hned (hinj (e.trans hd.symm))
    · rw [← eop, ← List.map_cons, ← List.map_cons, List.mem_map]; rintro ⟨x, hx, he⟩; exact hnm (hinj he ▸ hx)

theorem reach_map_moves (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    {d1 d2 : Nat} (hd : applyMoves ms d2 = d1)
    {roots1 roots2 : List Nat} (hroots : ∀ r ∈ roots2, Avail d1 roots1 (applyMoves ms r)) :
    ∀ {p bank}, NatReach d2 roots2 p bank →
      ∃ bank', NatReach d1 roots1 p bank' ∧ ∀ v ∈ bank, Avail d1 bank' (applyMoves ms v) := by
  obtain ⟨hand, hor, hxor, h0, h256⟩ := applyMoves_hom ms hok
  have hav : ∀ {b b' w}, (∀ v ∈ b, Avail d1 b' (applyMoves ms v)) →
      Avail d2 b w → Avail d1 b' (applyMoves ms w) := by
    intro b b' w hbb hw
    rcases hw with (hz | h1) | ⟨v, hv, he⟩
    · exact Or.inl (Or.inl (by rw [← hd, ← hand, hz, h0]))
    · exact Or.inl (Or.inr (by rw [← hd, ← hand, h1]))
    · have hve : applyMoves ms v &&& d1 = applyMoves ms w &&& d1 := by rw [← hd, ← hand, ← hand, he]
      exact avail_of_eq hve (hbb v hv)
  intro p
  induction p with
  | zero =>
    intro bank hr; subst hr
    exact ⟨roots1, rfl, hroots⟩
  | succ p ih =>
    intro bank hr
    rcases hr with ⟨b, a, rfl, hrb, ha⟩ | ⟨b, a, c, op, rfl, hrb, ha, hc⟩
    · obtain ⟨b', hrb', hbb⟩ := ih hrb
      have ha' := hav hbb ha
      refine ⟨negD d1 (applyMoves ms a) :: b', Or.inl ⟨b', applyMoves ms a, rfl, hrb', ha'⟩, ?_⟩
      intro v hv; rcases List.mem_cons.1 hv with rfl | hv
      · exact Or.inr ⟨negD d1 (applyMoves ms a), List.mem_cons_self, by simp only [negD, hand, hxor, h256, hd]⟩
      · exact avail_cons _ _ (hbb v hv)
    · obtain ⟨b', hrb', hbb⟩ := ih hrb
      have ha' := hav hbb ha; have hc' := hav hbb hc
      refine ⟨binD d1 op (applyMoves ms a) (applyMoves ms c) :: b',
        Or.inr ⟨b', applyMoves ms a, applyMoves ms c, op, rfl, hrb', ha', hc'⟩, ?_⟩
      intro v hv; rcases List.mem_cons.1 hv with rfl | hv
      · exact Or.inr ⟨binD d1 op (applyMoves ms a) (applyMoves ms c), List.mem_cons_self, by
          cases op <;> simp only [binD, andD, orD, hand, hor, hd, ite_true, ite_false, Bool.false_eq_true]⟩
      · exact avail_cons _ _ (hbb v hv)

theorem lower_iso {d1 d2 T1 T2 L : Nat} {roots1 roots2 : List Nat}
    (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd : applyMoves ms d2 = d1) (hT : applyMoves ms T2 = T1)
    (hroots : roots2.all (fun r => availB d1 roots1 (applyMoves ms r)) = true)
    (h1 : Lower d1 roots1 T1 L) : Lower d2 roots2 T2 L := by
  obtain ⟨hand, _, _, h0, _⟩ := applyMoves_hom ms hok
  have hr : ∀ r ∈ roots2, Avail d1 roots1 (applyMoves ms r) := fun r hr =>
    (availB_iff _ _ _).1 (List.all_eq_true.1 hroots r hr)
  intro p bank hreach ha
  obtain ⟨bank', hrb', hbb⟩ := reach_map_moves ms hok hd hr hreach
  apply h1 p bank' hrb'
  rcases ha with (hz | ho) | ⟨v, hv, he⟩
  · exact Or.inl (Or.inl (by rw [← hT, ← hd, ← hand, hz, h0]))
  · exact Or.inl (Or.inr (by rw [← hT, ← hd, ← hand, ho]))
  · have hve : applyMoves ms v &&& d1 = T1 &&& d1 := by rw [← hT, ← hd, ← hand, ← hand, he]
    exact avail_of_eq hve (hbb v hv)

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

def bsr (read : Nat → Nat) (h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      (if read ((lo + hi) / 2) ≤ h then bsr read h f ((lo + hi) / 2) hi
       else bsr read h f lo ((lo + hi) / 2))
    else lo

def hw256 (seed w : Nat) : Nat :=
  let x := (((w % 170141183460469231731687303715884105727) ^^^ seed) * 0x9e3779b97f4a7c15f39cc0605cedc835) &&& 0xffffffffffffffffffffffffffffffff
  let y := ((x ^^^ (x >>> 61)) * 0xc2b2ae3d27d4eb4f165667b19e3779f9) &&& 0xffffffffffffffffffffffffffffffff
  y >>> 96

def hz (seed : Nat) : List Nat → Nat
  | [] => 0
  | w :: t => hw256 seed w + hz seed t

def hk (seed : Nat) (zs : List Nat) : Nat := hz seed zs &&& 4294967295

def found (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (s : Nat) (zs : List Nat) : Bool :=
  decide (idx s zs < N s) && zs.isPerm (S s (idx s zs))

def foundH (S : Nat → Nat → List Nat) (N : Nat → Nat) (htAt : Nat → Nat → Nat)
    (idxH : Nat → Nat → Nat) (s h : Nat) (zs : List Nat) : Bool :=
  let i := idxH s h
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
         let h := hk seed cz
         !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz)))

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
         let h := hk seed cz
         !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz))
      have hF (zs) (hz : RunD dm (T &&& dm) s zs) : F zs = true := by
        have hcz := hr hz
        have hcutf : cutHitH s (hk seed (ori zs)) (ori zs) = false := by
          cases h : cutHitH s (hk seed (ori zs)) (ori zs) with
          | false => rfl
          | true => exact absurd hcz (hcut h)
        simp only [F, coversP_ok hd pairs hpairs hz, scr_no pool hz, hcutf, Bool.not_false, Bool.true_and, foundH]
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
            let h := hk seed cz
            !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz)))) = F := by
        funext zs
        have hfst : (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))).map Prod.fst = zs := by
          simp [List.map_map, Function.comp_def]
        rw [coversD_eq, hfst]
        simp only [F, Bool.and_assoc]
      rw [hFeq, hN] at hb
      contradiction

def pickMin (seed : Nat) (orig : List Nat) : List (List (Nat × Nat)) → List Nat → Nat → List Nat
  | [], best, _ => best
  | ms :: rest, best, bestH =>
    let img := orig.map (applyMoves ms)
    let h := hk seed img
    if h < bestH then pickMin seed orig rest img h else pickMin seed orig rest best bestH

theorem pickMin_runD {dm Y u} (seed : Nat) (orig : List Nat) (h0 : RunD dm Y u orig) :
    ∀ (syms : List (List (Nat × Nat))) (best : List Nat) (bestH : Nat),
      syms.all (fun ms => ms.all moveOK256 && (applyMoves ms dm == dm) && (applyMoves ms Y == Y)) = true →
      RunD dm Y u best →
      RunD dm Y u (pickMin seed orig syms best bestH)
  | [], _, _, _, hb => hb
  | ms :: rest, best, bestH, hok, hb => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hok
    unfold pickMin; dsimp only; split
    · exact pickMin_runD seed orig h0 rest _ _ hok.2 (applyMoves_runD ms hok.1.1.1 hok.1.1.2 hok.1.2 h0)
    · exact pickMin_runD seed orig h0 rest best bestH hok.2 hb

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

def pt8 (r : Nat) : Fin 8 → Bool := fun i => r.testBit i.val

theorem xs256_bits : ∀ r : Fin 256, xs256.map (·.testBit r.val) = List.ofFn (pt8 r.val) := by
  decide +kernel

theorem lower_to_circuit (f : (Fin 8 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 256, T.testBit r.val = f (pt8 r.val))
    (hlow : Lower mask256 xs256 T lb) :
    ∀ t : ℕ, HasCircuitSize 8 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ xs256, Avail mask256 xs256 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates xs256 hfan 0 xs256 xs256 rfl hsup0
  have hout : (execN C.gates xs256).getD C.output 0 &&& mask256 = T &&& mask256 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and, mask256_bit]
    by_cases hlt : r < 256
    · simp only [hlt, decide_true, Bool.and_true]
      have h1 := execN_bit C.gates xs256 r hlt (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [xs256_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates xs256).map (·.testBit r)).getD C.output false =
          ((execN C.gates xs256).getD C.output 0).testBit r := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates xs256)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      have h3 : (C.wires (List.ofFn (pt8 r))).getD C.output false = f (pt8 r) := hev (pt8 r)
      exact h2.trans (h3.trans (hT ⟨r, hlt⟩).symm)
    · simp [hlt]
  have hav_out : Avail mask256 bank ((execN C.gates xs256).getD C.output 0) := by
    by_cases hi : C.output < (execN C.gates xs256).length
    · exact hsup _ (getD_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hL := hlow p bank hr (avail_of_eq hout hav_out)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xfeecf8a8feecf8a8feecf8a8feecf8a8feecf8a8feecf8a8feecf8a8feecf8a8
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xeeeeeeaaeecc8888eeeeeeaaeecc8888eeeeeeaaeecc8888eeeeeeaaeecc8888
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfcfcfc00fcccf000fcfcfc00fcccf000fcfcfc00fcccf000fcfcfc00fcccf000
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xfeaafeaaf8a8f8a8feaafeaaf8a8f8a8feaafeaaf8a8f8a8feaafeaaf8a8f8a8
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_47_16 : Nat := 0xffff0000ffff0000
def goal_47_16 : Nat := 0xfefefefefeecfeecfefefefefeecfeecfefefefefeecfeecfefefefefeecfeec
def roots_47_16 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_15_16 : Nat := 0xffff0000
def goal_15_16 : Nat := 0xfeecfeecfeecfeecfeecfeecfeecfeecfeecfeecfeecfeecfeecfeecfeecfeec
def roots_15_16 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0]

def dom_27 : Nat := 0xf0f0f0f
def goal_27 : Nat := 0xeecc8888eecc8888eecc8888eecc8888eecc8888eecc8888eecc8888eecc8888
def roots_27 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_51_8 : Nat := 0xf000f000f000f00
def goal_51_8 : Nat := 0xeeeeeeeeeeee8888eeeeeeeeeeee8888eeeeeeeeeeee8888eeeeeeeeeeee8888
def roots_51_8 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfafafaaafaa0f0a0fafafaaafaa0f0a0fafafaaafaa0f0a0fafafaaafaa0f0a0
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefeaaaaececa8a8fefeaaaaececa8a8fefeaaaaececa8a8fefeaaaaececa8a8
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55_8 : Nat := 0xff00ff00ff00ff00
def goal_55_8 : Nat := 0xfefefefefefef8f8fefefefefefef8f8fefefefefefef8f8fefefefefefef8f8
def roots_55_8 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_23_8 : Nat := 0xff00ff00
def goal_23_8 : Nat := 0xfefef8f8fefef8f8fefef8f8fefef8f8fefef8f8fefef8f8fefef8f8fefef8f8
def roots_23_8 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_39_16 : Nat := 0xff000000ff0000
def goal_39_16 : Nat := 0xfefefefeececececfefefefeececececfefefefeececececfefefefeecececec
def roots_39_16 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0]

def dom_39_8 : Nat := 0xff000000ff00
def goal_39_8 : Nat := 0xfefefefef8f8f8f8fefefefef8f8f8f8fefefefef8f8f8f8fefefefef8f8f8f8
def roots_39_8 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0]

def dom_43 : Nat := 0xf0f00000f0f
def goal_43 : Nat := 0xeeaaeeaa88888888eeaaeeaa88888888eeaaeeaa88888888eeaaeeaa88888888
def roots_43 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_29 : Nat := 0x33333333
def goal_29 : Nat := 0xfaa0f0a0faa0f0a0faa0f0a0faa0f0a0faa0f0a0faa0f0a0faa0f0a0faa0f0a0
def roots_29 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_53 : Nat := 0x33003300330033
def goal_53 : Nat := 0xfafaaaaaa0a0a0a0fafaaaaaa0a0a0a0fafaaaaaa0a0a0a0fafaaaaaa0a0a0a0
def roots_53 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_45_16 : Nat := 0x3333000033330000
def goal_45_16 : Nat := 0xfafafafafaa0faa0fafafafafaa0faa0fafafafafaa0faa0fafafafafaa0faa0
def roots_45_16 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfefefeaafeecf8a8fefefeaafeecf8a8fefefeaafeecf8a8fefefeaafeecf8a8
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

namespace S_31
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (2, 3), (2, 18), (4, 5), (4, 12), (6, 7), (6, 14), (6, 22), (8, 12), (9, 11), (9, 13), (9, 25), (10, 11), (10, 14), (10, 26), (16, 18), (17, 19), (17, 21), (17, 25), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28)]
def r1sG : List Nat := [1, 1, 2, 2, 4, 4, 6, 6, 6, 8, 9, 9, 9, 10, 10, 10, 16, 17, 17, 17, 20, 20, 20, 24, 24, 24]
def r2sG : List Nat := [3, 5, 3, 18, 5, 12, 7, 14, 22, 12, 11, 13, 25, 11, 14, 26, 18, 19, 21, 25, 21, 22, 28, 25, 26, 28]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [2203654948099, 6601533293317, 4402745773061, 6601701459203, 2203722519043, 10999815541251, 21994931817477, 26426968507161, 2203470007043, 9904481436940, 6601516518147, 9913071371532, 26461361407257, 22063651294213, 18730454223897, 17600928613138, 11034175279619]
def xsM : List Nat := roots_31.map (· &&& dom_31)
def goalM : Nat := goal_31 &&& dom_31
def NN : Nat → Nat
  | 4 => 1
  | 5 => 25
  | 6 => 19
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xac05225e
  | 5, 0 => 0xf0b2ef13de66a692d591247cac05225ea571db928c616cec81ea162e7873cae76f5141bc6baa581364d4803364ae694e5e1d4aa85299e96d4ca62407439e85fd419de0e53a6b8d413649f21e32f633fb2637312d25e0cf661d973d961ac7d7cf08a43bb3
  | 6, 0 => 0xd051f507ce00c9b9be3a6442ac05225ea0508cfd93c0f7228c616cec7ecfa1837702c5a9744473ec554c825e5299e96d3a6b8d4130706e42276bea4325303d37206585ea1b8a7ef10241d3e1
  | 7, 0 => 0xac05225e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xaa00aa0000000000000000000000000000000000000000000000000000000000a0a0a0a0000000000000000000000000000000000000000000000000000000008888888800000000000000000000000000000000000000000000000000000000555555550000000000000000000000000000000000000000000000000000000033333333000000000000000000000000000000000000000000000000000000000f0f0f0f0000000000000000000000000000000000000000000000000000000000ff00ff000000000000000000000000000000000000000000000000000000000000ffff
  | 0, 1 => 0xf0f0000000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000cccc888800000000000000000000000000000000000000000000000000000000cc00cc0000000000000000000000000000000000000000000000000000000000c0c0c0c000000000000000000000000000000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000000aaaa0000
  | 0, 2 => 0xff00000000000000000000000000000000000000000000000000000000000000fcfcfcfc00000000000000000000000000000000000000000000000000000000fcccfccc00000000000000000000000000000000000000000000000000000000fafafafa00000000000000000000000000000000000000000000000000000000faaafaaa00000000000000000000000000000000000000000000000000000000fa00fa0000000000000000000000000000000000000000000000000000000000f8f8f8f800000000000000000000000000000000000000000000000000000000f0f0f0f0
  | 0, 3 => 0xffff000000000000000000000000000000000000000000000000000000000000fff0fff000000000000000000000000000000000000000000000000000000000ffccffcc00000000000000000000000000000000000000000000000000000000ffaaffaa00000000000000000000000000000000000000000000000000000000ffa0ffa000000000000000000000000000000000000000000000000000000000ff88ff8800000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ff00f000
  | 0, 4 => 0xffffff0000000000000000000000000000000000000000000000000000000000fffff00000000000000000000000000000000000000000000000000000000000ffffcccc00000000000000000000000000000000000000000000000000000000ffffaaaa
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x1f6503495
  | 5, 0, 0 => 0x64d242015f6490c257d944d255f78e34957d9349095f65010357da40d256265034957d940d115f6d034957cd242055f65434657d240d255f61034957d0344055f65340d5
  | 5, 0, 1 => 0x1f65628958d740d255f71034757d940d255034904057d0349055f7502c957d9550255f6503095
  | 6, 0, 0 => 0x1f65034957d940d24567d9590349601f40d24157d940d24368df65034967d940d28967d940d248601f64d242501f65034457dd650349681f65034967d940e34967d951034967d940d24067d940f3496
  | 6, 0, 1 => 0x7d940d244685f65034967d95d03496
  | 7, 0, 0 => 0x1f6503495
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 34
  | 5 => 34
  | 6 => 40
  | 7 => 34
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 6 0) :: stateWires n (ids >>> 6)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x1c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003f1e3fc0000000000000000000000000000000000000000000000000000000003ff1e3300000000000000000000000000000000000000000000000000000000038ffe0f00000000000000000000000000000000000000000000000000000000007f01ff000000000000000000000000000000000000000000000000000000000000ffff
  | 0, 1 => 0x7000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e1cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e00000000000000000000000000000000000000000000000000000000000000001c000000000000000000000000000000000000000000000000000000000000e1c0300000000000000000000000000000000000000000000000000000000000e0000
  | 0, 2 => 0x3800000000000000000000000000000000000000000000000000000000000000070e1fc000000000000000000000000000000000000000000000000000000000000e1cc00000000000000000000000000000000000000000000000000000000007e1df300000000000000000000000000000000000000000000000000000000000e1c030000000000000000000000000000000000000000000000000000000000001c0000000000000000000000000000000000000000000000000000000000007001f000000000000000000000000000000000000000000000000000000000007001f0
  | 0, 3 => 0x3ff00000000000000000000000000000000000000000000000000000000000003f0fff0000000000000000000000000000000000000000000000000000000000380ffcc00000000000000000000000000000000000000000000000000000000038efe03000000000000000000000000000000000000000000000000000000000380fe00000000000000000000000000000000000000000000000000000000000380fe00000000000000000000000000000000000000000000000000000000000380fe000000000000000000000000000000000000000000000000000000000003800000
  | 0, 4 => 0x3fffe000000000000000000000000000000000000000000000000000000000003ff00000000000000000000000000000000000000000000000000000000000003ffe1cc0000000000000000000000000000000000000000000000000000000003ff1c03
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x883c0000000000000000000000000000000000000000000000000000000000001408520000000000000000000000000000000000000000000000000000000000022445000000000000000000000000000000000000000000000000000000000361c3a80000000000000000000000000000000000000000000000000000000002dc1a3200000000000000000000000000000000000000000000000000000000018bb40d000000000000000000000000000000000000000000000000000000000037015f0000000000000000000000000000000000000000000000000000000000006ef7
  | 0, 1 => 0x27401000000000000000000000000000000000000000000000000000000000002404aa0000000000000000000000000000000000000000000000000000000000123e5cd000000000000000000000000000000000000000000000000000000000123a54d000000000000000000000000000000000000000000000000000000000100e48000000000000000000000000000000000000000000000000000000000002041c000000000000000000000000000000000000000000000000000000000009e3c5700000000000000000000000000000000000000000000000000000000009e1000
  | 0, 2 => 0x3c89000000000000000000000000000000000000000000000000000000000000377efff000000000000000000000000000000000000000000000000000000000363efed0000000000000000000000000000000000000000000000000000000002fe7ff70000000000000000000000000000000000000000000000000000000002de7ef70000000000000000000000000000000000000000000000000000000002c87ea00000000000000000000000000000000000000000000000000000000002766ff70000000000000000000000000000000000000000000000000000000002744bf2
  | 0, 3 => 0x3ff91080000000000000000000000000000000000000000000000000000000003fcfff20000000000000000000000000000000000000000000000000000000003ebffed0000000000000000000000000000000000000000000000000000000003defef70000000000000000000000000000000000000000000000000000000003dcfef20000000000000000000000000000000000000000000000000000000003cafee50000000000000000000000000000000000000000000000000000000003c8fea00000000000000000000000000000000000000000000000000000000003c8daa0
  | 0, 4 => 0x3ffffa80000000000000000000000000000000000000000000000000000000003ffdba80000000000000000000000000000000000000000000000000000000003fff5cd0000000000000000000000000000000000000000000000000000000003ffbd5f
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 36 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 36 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 36 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 36 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 6 0) :: stateWiresD n (ids >>> 6)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 6 0) :: stateWiresS n (ids >>> 6)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 6 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_31 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_31 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_31 == dom_31) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_31 goalM u ys) : RunD dom_31 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_31 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_16 : ∀ i, 16 ≤ i → i < 25 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 9 16 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 25 → Z 5 i = true := (range_split z5_0 z5_16)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 16 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_16 : ∀ i, 16 ≤ i → i < 19 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 3 16 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 19 → Z 6 i = true := (range_split z6_0 z6_16)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := z7_0
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
def RootG (s : Nat) : Bool :=
  scr dom_31 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_31 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_31 roots_31 goal_31 8 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_31 goal_31 := by
    have h0 : isConstB dom_31 goal_31 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_31

theorem low_31 : Lower dom_31 roots_31 goal_31 8 := S_31.noCircuit

namespace S_59
def pairsG : List (Nat × Nat) := [(1, 3), (1, 33), (2, 3), (2, 18), (9, 11), (9, 25), (9, 41), (10, 11), (10, 26), (10, 42), (16, 18), (17, 19), (17, 25), (17, 49), (24, 25), (24, 26), (32, 33), (34, 35), (34, 42), (34, 50), (40, 41), (40, 42), (48, 49), (48, 50), (56, 57), (56, 58)]
def r1sG : List Nat := [1, 1, 2, 2, 9, 9, 9, 10, 10, 10, 16, 17, 17, 17, 24, 24, 32, 34, 34, 34, 40, 40, 48, 48, 56, 56]
def r2sG : List Nat := [3, 33, 3, 18, 11, 25, 41, 11, 26, 42, 18, 19, 25, 49, 25, 26, 33, 35, 42, 50, 41, 42, 49, 50, 57, 58]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [2203722519043, 18700440240914, 26427506364953, 44023433724714, 18700691902979, 37387860837153, 26461866696985, 11034175279619, 44126780850986, 61718966895402, 61611877466905]
def xsM : List Nat := roots_59.map (· &&& dom_59)
def goalM : Nat := goal_59 &&& dom_59
def NN : Nat → Nat
  | 4 => 3
  | 5 => 28
  | 6 => 19
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xc3827481bbe5e99c0b674889
  | 5, 0 => 0xce5b8369c54abd37c3827481b9ed760eb9d56310b9879e3193b906c58c5020338bab304b6cc1455569369245674a875b5f210ebd54363a354cac355d4599038c37f8ccf426f145cd26bc2b5e243e20471ba5db2b1b891d4416a6bae61475eb730f49a64c09710d2b06d5b4db061f7558
  | 6, 0 => 0xcd1774a2c6eafbb0c3827481a48636c1a052ac9e8ea8457e87084d026e9b733a6c35459f652e56205a3c9a365878c3dd4cac355d4599038c418db97037f8ccf42a5942f414d4acce006bb7a1
  | 7, 0 => 0xc3827481
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xa0a00000a0a00000000000000000000000000000000000000000000000000000a000a000a000a00000000000000000000000000000000000000000000000000080808080808080800000000000000000000000000000000000000000000000005050505050505050000000000000000000000000000000000000000000000000303030303030303000000000000000000000000000000000000000000000000000f000f000f000f00000000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000000000000000000000000000000000000000f0f0f0f
  | 0, 1 => 0xe0e0e0e0c0c0c0c0000000000000000000000000000000000000000000000000e0e0e0e000000000000000000000000000000000000000000000000000000000e000e000e000e000000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000000c0c0c0c000000000000000000000000000000000000000000000000000000000c0c00000c0c00000000000000000000000000000000000000000000000000000c000c000c000c000000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a
  | 0, 2 => 0xf0c00000f0c00000000000000000000000000000000000000000000000000000f0a0f0a0f0a0f0a0000000000000000000000000000000000000000000000000f080f080f080f080000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000f000f000f0000000000000000000000000000000000000000000000000000000f000f000a000a000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e
  | 0, 3 => 0xf0f0c0c0f0f0c0c0000000000000000000000000000000000000000000000000f0f0a0a0f0f0a0a0000000000000000000000000000000000000000000000000f0f0a0a0f0f00000000000000000000000000000000000000000000000000000f0f08080f0f08080000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000f0c0f0c0f0c0f0c0000000000000000000000000000000000000000000000000f0c0f000f0c0f00
  | 0, 4 => 0xf0f0f0f0f0f00000000000000000000000000000000000000000000000000000f0f0f0f0f000f000000000000000000000000000000000000000000000000000f0f0f0f0f0000000000000000000000000000000000000000000000000000000f0f0f0f0a0a0a0a0000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000f0f0f000f0f0f000000000000000000000000000000000000000000000000000f0f0f000f0f00000000000000000000000000000000000000000000000000000f0f0f000f000f00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x236d4308502684c21009e03084
  | 5, 0, 0 => 0x50c20101635d430858db50c11636cc20258d4308056379430758e244c21636d330856d438c21636d410358db48c21636c80c258dc50c21637d428858d420305676943085
  | 5, 0, 1 => 0x95b50c21636d530858db50c21636d830858db50f215b5080c058db510156381b30858dd50c215b30808058db34c21636d63065
  | 6, 0, 0 => 0x8db65430869e36d430868db50c28868db69430868db50c20568db50c2c869236d430868de6d430868db50c24860236d430450236cc20259a36d4308602350c20158db50c20468db50c20068db5113086
  | 6, 0, 1 => 0x8db50c20268db51030860236d43085
  | 7, 0, 0 => 0x236d43085
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 34
  | 5 => 34
  | 6 => 40
  | 7 => 34
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 6 0) :: stateWires n (ids >>> 6)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3800000000000000000000000000000000000000000000000000000000000000007000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ffc78c0000000000000000000000000000000000000000000000000000000003f1fc730000000000000000000000000000000000000000000000000000000000cf3c0f00000000000000000000000000000000000000000000000000000000003f03ff000000000000000000000000000000000000000000000000000000000000ffff
  | 0, 1 => 0xe038c00000000000000000000000000000000000000000000000000000000000e000000000000000000000000000000000000000000000000000000000000000003f000000000000000000000000000000000000000000000000000000000000e038c00000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003800000000000000000000000000000000000000000000000000000000000003873
  | 0, 2 => 0x300c000000000000000000000000000000000000000000000000000000000000330fbf3000000000000000000000000000000000000000000000000000000000330c3f0000000000000000000000000000000000000000000000000000000000330c3f0000000000000000000000000000000000000000000000000000000000330c0000000000000000000000000000000000000000000000000000000000003300070000000000000000000000000000000000000000000000000000000000300c00000000000000000000000000000000000000000000000000000000000000e3bff
  | 0, 3 => 0x3ceff8c0000000000000000000000000000000000000000000000000000000003c0fc730000000000000000000000000000000000000000000000000000000003c0fc000000000000000000000000000000000000000000000000000000000003c0fc000000000000000000000000000000000000000000000000000000000003c0fc000000000000000000000000000000000000000000000000000000000003c0000000000000000000000000000000000000000000000000000000000000033ec3fc000000000000000000000000000000000000000000000000000000000330c3f0
  | 0, 4 => 0x3fffc000000000000000000000000000000000000000000000000000000000003ffc3f00000000000000000000000000000000000000000000000000000000003ffc0000000000000000000000000000000000000000000000000000000000003ff38730000000000000000000000000000000000000000000000000000000003ff00000000000000000000000000000000000000000000000000000000000003f0fff00000000000000000000000000000000000000000000000000000000003f0fc000000000000000000000000000000000000000000000000000000000003f0c3f0
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x140782000000000000000000000000000000000000000000000000000000000011050f000000000000000000000000000000000000000000000000000000000000208950000000000000000000000000000000000000000000000000000000002ac870800000000000000000000000000000000000000000000000000000000015170620000000000000000000000000000000000000000000000000000000000cb2c0f00000000000000000000000000000000000000000000000000000000003702d7000000000000000000000000000000000000000000000000000000000000ddbd
  | 0, 1 => 0x3ffafdf0000000000000000000000000000000000000000000000000000000003ff2242000000000000000000000000000000000000000000000000000000000334d3f00000000000000000000000000000000000000000000000000000000002ae8f9d0000000000000000000000000000000000000000000000000000000002ae02000000000000000000000000000000000000000000000000000000000002888d08000000000000000000000000000000000000000000000000000000000224839000000000000000000000000000000000000000000000000000000000015378f7
  | 0, 2 => 0x388dd28000000000000000000000000000000000000000000000000000000000377fbf7000000000000000000000000000000000000000000000000000000000336dbf5000000000000000000000000000000000000000000000000000000000334d3f0000000000000000000000000000000000000000000000000000000000334d36000000000000000000000000000000000000000000000000000000000033452f0000000000000000000000000000000000000000000000000000000000300d1200000000000000000000000000000000000000000000000000000000003ffffff
  | 0, 3 => 0x3eeffbd0000000000000000000000000000000000000000000000000000000003dbfdff0000000000000000000000000000000000000000000000000000000003dbfd6a0000000000000000000000000000000000000000000000000000000003cafdbd0000000000000000000000000000000000000000000000000000000003c8fd280000000000000000000000000000000000000000000000000000000003c820000000000000000000000000000000000000000000000000000000000003bedffd0000000000000000000000000000000000000000000000000000000003bcdff8
  | 0, 4 => 0x3ffff6a0000000000000000000000000000000000000000000000000000000003fff3f20000000000000000000000000000000000000000000000000000000003fff3620000000000000000000000000000000000000000000000000000000003ff7af70000000000000000000000000000000000000000000000000000000003ff22420000000000000000000000000000000000000000000000000000000003fcfff80000000000000000000000000000000000000000000000000000000003fcff680000000000000000000000000000000000000000000000000000000003fcf3f0
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 40 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 40 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 40 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 40 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 6 0) :: stateWiresD n (ids >>> 6)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 6 0) :: stateWiresS n (ids >>> 6)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 6 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_59 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_59 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_59 == dom_59) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_59 goalM u ys) : RunD dom_59 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_59 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_16 : ∀ i, 16 ≤ i → i < 28 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 16 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 28 → Z 5 i = true := (range_split z5_0 z5_16)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 16 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_16 : ∀ i, 16 ≤ i → i < 19 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 3 16 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 19 → Z 6 i = true := (range_split z6_0 z6_16)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := z7_0
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
def RootG (s : Nat) : Bool :=
  scr dom_59 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_59 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_59 roots_59 goal_59 8 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_59 goal_59 := by
    have h0 : isConstB dom_59 goal_59 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_59

theorem low_59 : Lower dom_59 roots_59 goal_59 8 := S_59.noCircuit

namespace S_62
def pairsG : List (Nat × Nat) := [(2, 18), (4, 12), (6, 14), (6, 22), (8, 12), (10, 14), (10, 26), (10, 42), (16, 18), (20, 22), (20, 28), (20, 52), (24, 26), (24, 28), (34, 42), (34, 50), (36, 44), (36, 52), (38, 46), (38, 54), (40, 42), (40, 44), (48, 50), (48, 52), (56, 58), (56, 60)]
def r1sG : List Nat := [2, 4, 6, 6, 8, 10, 10, 10, 16, 20, 20, 20, 24, 24, 34, 34, 36, 36, 38, 38, 40, 40, 48, 48, 56, 56]
def r2sG : List Nat := [18, 12, 14, 22, 12, 14, 26, 42, 18, 22, 28, 52, 26, 28, 42, 50, 44, 52, 46, 54, 42, 44, 50, 52, 58, 60]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [44126830726186, 37426683972650, 52931345910836, 44144010595370, 44023753740842]
def xsM : List Nat := roots_62.map (· &&& dom_62)
def goalM : Nat := goal_62 &&& dom_62
def NN : Nat → Nat
  | 4 => 1
  | 5 => 3
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xa91103de
  | 5, 0 => 0xe324ca91a91103de0ebf8666
  | 6, 0 => 0xa91103de
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x5555555500000000000000000000000000000000000000000000000000000000555500005555000000000000000000000000000000000000000000000000000055005500550055000000000000000000000000000000000000000000000000005050505050505050000000000000000000000000000000000000000000000000444444444444444400000000000000000000000000000000000000000000000000005555000055550000000000000000000000000000000000000000000000000000000055555555
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x6b1a5
  | 5, 0, 0 => 0x16341758d2e8d15
  | 6, 0, 0 => 0x6b1a5
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 19
  | 5 => 19
  | 6 => 19
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 3 0) :: stateWires n (ids >>> 3)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3ffc0000000000000000000000000000000000000000000000000000000000003c03f0000000000000000000000000000000000000000000000000000000000033030f000000000000000000000000000000000000000000000000000000000000f0e0e00000000000000000000000000000000000000000000000000000000000cc0ed00000000000000000000000000000000000000000000000000000000003fc0ff0000000000000000000000000000000000000000000000000000000000003fff
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3ffc8800000000000000000000000000000000000000000000000000000000003cabf4900000000000000000000000000000000000000000000000000000000033574f60000000000000000000000000000000000000000000000000000000002af2e3e00000000000000000000000000000000000000000000000000000000015cd3ed00000000000000000000000000000000000000000000000000000000003540b6000000000000000000000000000000000000000000000000000000000000377f
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 7 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 7 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 7 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 7 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 3 0) :: stateWiresD n (ids >>> 3)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 3 0) :: stateWiresS n (ids >>> 3)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_62 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_62 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_62 == dom_62) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_62 goalM u ys) : RunD dom_62 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_62 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := z5_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := z6_0
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_62 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_62 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_62 roots_62 goal_62 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_62 goal_62 := by
    have h0 : isConstB dom_62 goal_62 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_62

theorem low_62 : Lower dom_62 roots_62 goal_62 7 := S_62.noCircuit

namespace S_47
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 33), (2, 3), (4, 5), (4, 12), (6, 7), (6, 14), (8, 12), (9, 11), (9, 13), (9, 41), (10, 11), (10, 14), (10, 42), (32, 33), (34, 35), (34, 42), (36, 37), (36, 44), (38, 39), (38, 46), (40, 41), (40, 42), (40, 44)]
def r1sG : List Nat := [1, 1, 1, 2, 4, 4, 6, 6, 8, 9, 9, 9, 10, 10, 10, 32, 34, 34, 36, 36, 38, 38, 40, 40, 40]
def r2sG : List Nat := [3, 5, 33, 3, 5, 12, 7, 14, 12, 11, 13, 41, 11, 14, 42, 33, 35, 42, 37, 44, 39, 46, 41, 42, 44]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [11000085094659, 6601533293317, 4403014732805, 44023433724714, 37388364161283, 4402510037793, 35188837581601]
def xsM : List Nat := roots_47.map (· &&& dom_47)
def goalM : Nat := goal_47 &&& dom_47
def NN : Nat → Nat
  | 4 => 2
  | 5 => 7
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xb1293d950f1fce07
  | 5, 0 => 0xf641318c8888432e5cdf53735ba073fa5b61388b530ab5460f1fce07
  | 6, 0 => 0xf1fce07
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xfcfc0000fcfc0000000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000cccc0000cccc0000000000000000000000000000000000000000000000000000aaaa0000aaaa0000000000000000000000000000000000000000000000000000555500005555000000000000000000000000000000000000000000000000000033330000333300000000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000000000000000000000000000000000000ff000000ff
  | 0, 1 => 0xffff0000f0f00000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000ffaa0000ffaa0000000000000000000000000000000000000000000000000000ff000000ff00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xb8744a86545
  | 5, 0, 0 => 0xa65405a86425a96545a85415a86535b86545a86545
  | 6, 0, 0 => 0xa86545
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 24
  | 5 => 24
  | 6 => 24
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 4 0) :: stateWires n (ids >>> 4)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3f70f800000000000000000000000000000000000000000000000000000000003c00f000000000000000000000000000000000000000000000000000000000003370c80000000000000000000000000000000000000000000000000000000000000e070000000000000000000000000000000000000000000000000000000001fff1f80000000000000000000000000000000000000000000000000000000001cc8f370000000000000000000000000000000000000000000000000000000001c3ff0f00000000000000000000000000000000000000000000000000000000003f80ff
  | 0, 1 => 0x1ff80f00000000000000000000000000000000000000000000000000000000001ff80000000000000000000000000000000000000000000000000000000000001c07f070000000000000000000000000000000000000000000000000000000001c07f00
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1bf77fb00000000000000000000000000000000000000000000000000000000013c25f20000000000000000000000000000000000000000000000000000000000b372c90000000000000000000000000000000000000000000000000000000000559e5f0000000000000000000000000000000000000000000000000000000001aa61a000000000000000000000000000000000000000000000000000000000014c8d360000000000000000000000000000000000000000000000000000000000c3da0d000000000000000000000000000000000000000000000000000000000015805f
  | 0, 1 => 0x1ffedf60000000000000000000000000000000000000000000000000000000001ffc8040000000000000000000000000000000000000000000000000000000001ffffff0000000000000000000000000000000000000000000000000000000001ea7fa0
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 12 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 12 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 12 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 12 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 4 0) :: stateWiresD n (ids >>> 4)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 4 0) :: stateWiresS n (ids >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 4 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_47 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_47 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_47 == dom_47) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_47 goalM u ys) : RunD dom_47 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_47 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 7 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 7 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 7 → Z 5 i = true := z5_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := z6_0
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_47 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_47 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_47 roots_47 goal_47 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_47 goal_47 := by
    have h0 : isConstB dom_47 goal_47 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_47

theorem low_47 : Lower dom_47 roots_47 goal_47 7 := S_47.noCircuit

namespace S_47_16
def pairsG : List (Nat × Nat) := [(16, 18), (17, 19), (17, 21), (17, 25), (17, 49), (20, 21), (20, 22), (20, 28), (20, 52), (24, 25), (24, 26), (24, 28), (48, 49), (48, 50), (48, 52), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [16, 17, 17, 17, 17, 20, 20, 20, 20, 24, 24, 24, 48, 48, 48, 56, 56, 56]
def r2sG : List Nat := [18, 19, 21, 25, 49, 21, 22, 28, 52, 25, 26, 28, 49, 50, 52, 57, 58, 60]
def mpG : Nat := 0x3ffff
def pool6G : List Nat := [22063651494165]
def xsM : List Nat := roots_47_16.map (· &&& dom_47_16)
def goalM : Nat := goal_47_16 &&& dom_47_16
def NN : Nat → Nat
  | 4 => 2
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x73240d52201cf257
  | 5, 0 => 0x73240d52
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffff0000ff000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000cccc0000cccc0000000000000000000000000000000000000000000000000000aaaa0000aaaa0000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x234428a884
  | 5, 0, 0 => 0x46885
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 19
  | 5 => 19
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 3 0) :: stateWires n (ids >>> 3)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3fe00000000000000000000000000000000000000000000000000000000000003f0000000000000000000000000000000000000000000000000000000000000038e0000000000000000000000000000000000000000000000000000000000000001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3ff98000000000000000000000000000000000000000000000000000000000003f1100000000000000000000000000000000000000000000000000000000000038e8800000000000000000000000000000000000000000000000000000000000249e40000000000000000000000000000000000000000000000000000000000012443000000000000000000000000000000000000000000000000000000000000923e
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 6 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 6 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 6 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 6 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 3 0) :: stateWiresD n (ids >>> 3)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 3 0) :: stateWiresS n (ids >>> 3)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_47_16 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_47_16 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_47_16 == dom_47_16) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_47_16 goalM u ys) : RunD dom_47_16 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_47_16 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := z5_0
theorem checked (s : Nat) (hs : s ≤ 5) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_47_16 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_47_16 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_47_16 roots_47_16 goal_47_16 6 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_47_16 goal_47_16 := by
    have h0 : isConstB dom_47_16 goal_47_16 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_47_16

theorem low_47_16 : Lower dom_47_16 roots_47_16 goal_47_16 6 := S_47_16.noCircuit

namespace S_15_16
def pairsG : List (Nat × Nat) := [(16, 18), (17, 19), (17, 21), (17, 25), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28)]
def r1sG : List Nat := [16, 17, 17, 17, 20, 20, 20, 24, 24, 24]
def r2sG : List Nat := [18, 19, 21, 25, 21, 22, 28, 25, 26, 28]
def mpG : Nat := 0x3ff
def pool6G : List Nat := [22063651494165]
def xsM : List Nat := roots_15_16.map (· &&& dom_15_16)
def goalM : Nat := goal_15_16 &&& dom_15_16
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x202b72e1
  | 4, 0 => 0x202b72e1
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000cccc000000000000000000000000000000000000000000000000000000000000aaaa0000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xe44
  | 4, 0, 0 => 0xe44
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 12
  | 4 => 12
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 2 0) :: stateWires n (ids >>> 2)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x38000000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3c800000000000000000000000000000000000000000000000000000000000002740000000000000000000000000000000000000000000000000000000000000123000000000000000000000000000000000000000000000000000000000000009e
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 4 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 4 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 4 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 4 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 2 0) :: stateWiresD n (ids >>> 2)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 2 0) :: stateWiresS n (ids >>> 2)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_15_16 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_15_16 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_15_16 == dom_15_16) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_15_16 goalM u ys) : RunD dom_15_16 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_15_16 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
theorem checked (s : Nat) (hs : s ≤ 4) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_15_16 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_15_16 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_15_16 roots_15_16 goal_15_16 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_15_16 goal_15_16 := by
    have h0 : isConstB dom_15_16 goal_15_16 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_15_16

theorem low_15_16 : Lower dom_15_16 roots_15_16 goal_15_16 5 := S_15_16.noCircuit

namespace S_27
def pairsG : List (Nat × Nat) := [(1, 3), (2, 3), (2, 18), (9, 11), (9, 25), (10, 11), (10, 26), (16, 18), (17, 19), (17, 25), (24, 25), (24, 26)]
def r1sG : List Nat := [1, 2, 2, 9, 9, 10, 10, 16, 17, 17, 24, 24]
def r2sG : List Nat := [3, 3, 18, 11, 25, 11, 26, 18, 19, 25, 25, 26]
def mpG : Nat := 0xfff
def pool6G : List Nat := [17600928613138, 9904598880771]
def xsM : List Nat := roots_27.map (· &&& dom_27)
def goalM : Nat := goal_27 &&& dom_27
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x317f6efe
  | 4, 0 => 0x317f6efe
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0000000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000c0c0c0c000000000000000000000000000000000000000000000000000000000a0a0a0a
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xe44
  | 4, 0, 0 => 0xe44
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 12
  | 4 => 12
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 2 0) :: stateWires n (ids >>> 2)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xf800000000000000000000000000000000000000000000000000000000000000c7800000000000000000000000000000000000000000000000000000000000000660000000000000000000000000000000000000000000000000000000000000319
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfd40000000000000000000000000000000000000000000000000000000000000e7800000000000000000000000000000000000000000000000000000000000009ef000000000000000000000000000000000000000000000000000000000000073b
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 4 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 4 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 4 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 4 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 2 0) :: stateWiresD n (ids >>> 2)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 2 0) :: stateWiresS n (ids >>> 2)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_27 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_27 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_27 == dom_27) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_27 goalM u ys) : RunD dom_27 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_27 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
theorem checked (s : Nat) (hs : s ≤ 4) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_27 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_27 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_27 roots_27 goal_27 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_27 goal_27 := by
    have h0 : isConstB dom_27 goal_27 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_27

theorem low_27 : Lower dom_27 roots_27 goal_27 5 := S_27.noCircuit

namespace S_51_8
def pairsG : List (Nat × Nat) := [(9, 11), (9, 25), (9, 41), (10, 11), (10, 26), (10, 42), (24, 25), (24, 26), (40, 41), (40, 42), (56, 57), (56, 58)]
def r1sG : List Nat := [9, 9, 9, 10, 10, 10, 24, 24, 40, 40, 56, 56]
def r2sG : List Nat := [11, 25, 41, 11, 26, 42, 25, 26, 41, 42, 57, 58]
def mpG : Nat := 0xfff
def pool6G : List Nat := [11034175346955]
def xsM : List Nat := roots_51_8.map (· &&& dom_51_8)
def goalM : Nat := goal_51_8 &&& dom_51_8
def NN : Nat → Nat
  | 3 => 2
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xded4059299c5d67d
  | 4, 0 => 0xded40592
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf000f000f0000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000c000c000c000c000000000000000000000000000000000000000000000000000a000a000a000a00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x68841083
  | 4, 0, 0 => 0x6884
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 16
  | 4 => 16
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 3 0) :: stateWires n (ids >>> 3)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xfc00000000000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000380000000000000000000000000000000000000000000000000000000000000007
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xff60000000000000000000000000000000000000000000000000000000000000f240000000000000000000000000000000000000000000000000000000000000cd20000000000000000000000000000000000000000000000000000000000000ab9000000000000000000000000000000000000000000000000000000000000054f
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 5 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 5 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 5 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 5 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 3 0) :: stateWiresD n (ids >>> 3)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 3 0) :: stateWiresS n (ids >>> 3)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_51_8 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_51_8 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_51_8 == dom_51_8) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_51_8 goalM u ys) : RunD dom_51_8 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_51_8 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 2 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 2 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 2 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
theorem checked (s : Nat) (hs : s ≤ 4) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_51_8 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_51_8 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_51_8 roots_51_8 goal_51_8 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_51_8 goal_51_8 := by
    have h0 : isConstB dom_51_8 goal_51_8 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_51_8

theorem low_51_8 : Lower dom_51_8 roots_51_8 goal_51_8 5 := S_51_8.noCircuit

def isoMv_61 : List (Nat × Nat) := [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_61 : Lower dom_61 roots_61 goal_61 8 :=
  lower_iso isoMv_61 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59

def isoMv_55 : List (Nat × Nat) := [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_55 : Lower dom_55 roots_55 goal_55 7 :=
  lower_iso isoMv_55 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47

def isoMv_55_8 : List (Nat × Nat) := [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_55_8 : Lower dom_55_8 roots_55_8 goal_55_8 6 :=
  lower_iso isoMv_55_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47_16

def isoMv_23_8 : List (Nat × Nat) := [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_23_8 : Lower dom_23_8 roots_23_8 goal_23_8 5 :=
  lower_iso isoMv_23_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_16

def isoMv_39_16 : List (Nat × Nat) := [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]
theorem low_39_16 : Lower dom_39_16 roots_39_16 goal_39_16 5 :=
  lower_iso isoMv_39_16 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_16

def isoMv_39_8 : List (Nat × Nat) := [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]
theorem low_39_8 : Lower dom_39_8 roots_39_8 goal_39_8 5 :=
  lower_iso isoMv_39_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_16

def isoMv_43 : List (Nat × Nat) := [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]
theorem low_43 : Lower dom_43 roots_43 goal_43 5 :=
  lower_iso isoMv_43 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27

def isoMv_29 : List (Nat × Nat) := [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_29 : Lower dom_29 roots_29 goal_29 5 :=
  lower_iso isoMv_29 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27

def isoMv_53 : List (Nat × Nat) := [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_53 : Lower dom_53 roots_53 goal_53 5 :=
  lower_iso isoMv_53 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27

def isoMv_45_16 : List (Nat × Nat) := [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_45_16 : Lower dom_45_16 roots_45_16 goal_45_16 5 :=
  lower_iso isoMv_45_16 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_51_8

namespace S_63
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 33), (2, 3), (2, 18), (4, 5), (4, 12), (6, 7), (6, 14), (6, 22), (8, 12), (9, 11), (9, 13), (9, 25), (9, 41), (10, 11), (10, 14), (10, 26), (10, 42), (16, 18), (17, 19), (17, 21), (17, 25), (17, 49), (20, 21), (20, 22), (20, 28), (20, 52), (24, 25), (24, 26), (24, 28), (32, 33), (34, 35), (34, 42), (34, 50), (36, 37), (36, 44), (36, 52), (38, 39), (38, 46), (38, 54), (40, 41), (40, 42), (40, 44), (48, 49), (48, 50), (48, 52), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 4, 4, 6, 6, 6, 8, 9, 9, 9, 9, 10, 10, 10, 10, 16, 17, 17, 17, 17, 20, 20, 20, 20, 24, 24, 24, 32, 34, 34, 34, 36, 36, 36, 38, 38, 38, 40, 40, 40, 48, 48, 48, 56, 56, 56]
def r2sG : List Nat := [3, 5, 33, 3, 18, 5, 12, 7, 14, 22, 12, 11, 13, 25, 41, 11, 14, 26, 42, 18, 19, 21, 25, 49, 21, 22, 28, 52, 25, 26, 28, 33, 35, 42, 50, 37, 44, 52, 39, 46, 54, 41, 42, 44, 49, 50, 52, 57, 58, 60]
def mpG : Nat := 0x3ffffffffffff
def pool6G : List Nat := [2203654948099, 10999815608579, 11000085094659, 18700440240914, 44023702164010, 26427102724889, 18735051641347, 2203655148035, 6601533293317, 37388364161283, 6601701459203, 9913071371532, 18709281836037, 26461361407257, 18730454223897, 4403014732805, 21994931817477, 6601701721347, 37387860837153, 22024879146252, 52862476420404, 43984930603809, 18730925560345, 26461629842713, 26397021635346, 39668471109940, 26405745788172, 39587052520737, 39621243831073, 41807363441923, 4403150201093, 37456748741409, 10999747577091, 52862744855860, 44126830726186, 52931329590580, 26427272725785, 52781192054049, 26461464036121, 11034175346955, 22063651294213, 44023567942442, 9904531309827, 18709551390981, 9904533538051, 18700624332035, 18709048066821, 18700626560259]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_63 &&& dom_63
def NN : Nat → Nat
  | 4 => 1
  | 5 => 20
  | 6 => 104
  | 7 => 395
  | 8 => 193
  | 9 => 18
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x14decb0d
  | 5, 0 => 0xe10e9cd3dac7954bcbde72a69ee2c50d9e95d73499e60c52970636278f3ca71c613c9bff5ceb3b16514b82dd5034d3004e2545fc4e1ba7d049ca46e748c2a6613bf1c2702d5f5e901a3e6a6115480163
  | 6, 0 => 0x785e7a40734bd994719d8c916ecfff346a8772f967e27d696751c7e764cb4e696198c32060bfdce05f7599dc5f398d535e2f68925b7b181b5871d44e57530f605675e06155957ecd54652c984fa929cb4fa17b0b4e74494649af0ae04917095748cbb65d4595c4c03c8086dc3b2526c23912399b36bd7d7435b28ad233255a0b239d187921e0032420bd424e1baee7ce1ae1c6821acbab4019d64a3919d2733e18f3b343167a4a5715db8c9815a66114153b04791338cb6511c605760ea7e5180ea48ca60b2f0aa10a6c0c690a6084d10a02438a09d1550208f317a506165d7606120315060534dd04773d450416fc8903d8aca30251b5a2024b42200017d736
  | 6, 1 => 0xf8dc0f96f3d6a6a3e6ee6dd1e122f7d0dcef2076d6f5018bd4e034e8d4de3103ced710a4caf5a39dcaf24955c816967bc5a8ce97c54f1ca7c0a10220c0a0deadbab9a1bdb98b8af6b8e76ab4b75f5d0cb7166ab7a3f576889f61c4f89e0172c69a9dac1499008a4d9576008f952b560094d2bf9d91249fa68c61d8ac8400471b825eaa8c7e79e21e7d5bffbb7cf06b427c95abe27bab94857b28099b79d53888
  | 7, 0 => 0x1edd0b6f1ed55caf1ea663541d85da9b1d1165dd1cd038361c0dd5381b27d2611b16f5ed1afecaa01a4dc7a419f37e0719ba301a1966b80018595dba181431aa1813153418103f8816446b9c158287a513af4bd913a79d1912bb8144112506a81120d64610bf6ca61004efa20f7093b80e7db3450e0550e70df43bd90df124ef0dd633720db753420d6066c90d05cbda0ccdc9130c6ed2f30c13a5aa0c0bf6ea0b50e2ee0a0f28af09bdf0a00938390c0919997808b46af10835ef3307ca96c5078179cf06e8585f065d5685064cb8090562a0ac04232342030a418d01eac28901cde8810185b85101551783014ecf680124c53e00d76e02002f1772002d875e
  | 7, 1 => 0x38c68766381fcf1437b0076a37a858aa3791ff6b375091353748575a364691d83615bd7836093879353aa3c6350ff6a133e6b2b633cd017f33b85c4333511330332a82ad32a889b1317b51d930e94f8c30dba2142fa88bf32f954dd02f3594f12e9b5e9e2e3a69332d98c7d02d618f3b2d4518622c8e77b92c7c27652c42325c2c3593cc2c1a29112c009a592bbea46f2b81626d2b811d732b2c9bd22b27b74c2ad9fd9b2a65405529af2b6428222a1a27b87eed2724c80b26f6bf9d26f168c925a9c20524dd90d22414ae9a2341f140232c6add2256936121eaa96f21997fae219634db21718caa20d5617920810030204fb0ae203a91681fd3c25f1efda323
  | 7, 2 => 0x53e591e8531108a65257aedf5248446851cda2a2512059fd50e2359450a1ed2e506b190f504513214fbdd0064f49dd644f050fd04ea474154e3a3a904d84259f4cd6bec54c16af5f4b8c97694b50406a4aeba8ec4ae43b454ab3aee74aabf4e84a9428d24a4249ab4a20e91b4a2002e848f2fa87480eeebd47b76ea34772c4c347722ff546ec901e46c7cf0745a7f59844f4548e44f40dc34408d56743c1fcc94397d1404336d2af431f7df742e7b5af41b7ba04412c1b3840e5429a3fc11baf3f3bf5403f291ad13e791ea93dce4f973d8f565c3d2c7c353b2275e13b05d6f73a9a85bd3a4fc2063a3e996d39b5e922399f4d1239234c07391f1ec038eeefa6
  | 7, 3 => 0x6f5e8b526ecfcc7c6def4db26d65318d6d04869a6cbe8b686c3bd30b6bf899566b846d316b302ff16a08bb0569da0c1f680f7993672edba1658a45f964e44f0364548dd86407b8f163da183963bad2eb63b3242b63939f33636b8ef76332600f626e480a62381e2561cf8f73610c35a860ad45a2602e455b601d48af5fd7fc205fd04d605f18482b5edbff035ecd913b5e5492d85dd08b735d48a8d45cea4ee05c97debb5bb357745b6b678f5b34bf745b00c4075ad883ea5a38516e595c19525925466958b561005859718357dd7a9357a487195732c6a956488c3a55a5888d55739b7c54f0369654e7b9da54af2ec554acafc454a96c0954a9557c54a26862
  | 7, 4 => 0x95d4c56f95c7f3849595a4cf954c87d9954b64c19515305d94e56e84938861299372f1e3931be89e92fea01592b8eaa0919a80f89147ad6a9112800b8f20258d8f052a2c8e46f5cc8e1260558d869bbd8cd916648cd7ccae8abb56b989cee35d8756c63885f1f72685a623a084d9addf849124c684520cd5840799a683dadf9b82673617814d04b7812adf7780b2da9b80b2a53b80ab0b5c807ff039800c7ccf7eff2d3a7eeeae697e7a0a4c7e704a887ca9b5577a399f0c79f05dc07847c1c2779c985d76ef06c676a7491376863e3b765ba643761880e674b866d574ae2b3473d644c7739a9980731a9a37730c5ff871d78ca27199ea0a70a579f870120e99
  | 7, 5 => 0xe8f0997ae28853e8de72546fddf8e307db51c5cfd96035f2d9588732d9288e6bd872797ad67aeb44d5b38d53d5877e98d3661707d282c284cf527d16ceca13bacd0facd0ccc7daa6cbedcfe9c6379303c3606443c20018d3c1eeb825c111313ec0f590b7bf58fb9bbf01fb40bebb555abe0cd55bbd2fc437bc9691cebab9a1bdbaa65613ba05b9e8b68386c9b3e7728fb2131be6b1cb86b2b1522b5ab0de38b8b0cf1072b046a32dae2a8799aca81979aca06ab9abfd546aaa00aaa3a994b72fa94c64a9a8cca005a8249059a5141b3ba4ba3818a4943c01a46ef71ea277e12da04d10569fe125ff9f9298bf9f1c706f9ec0d7899d42c3eb9cefd78c967fbfcb
  | 7, 6 => 0xfc6afe7dfc465d48fad9fd75f72a0023f6281cb5f5e5463cf48bd63cf250bba1eef3064dee5bfb02eb4fcf47
  | 8, 0 => 0x3129ad3f30bda81a302ca7772fc976f62f1362052de85b922d90db782b81626d2acd7a9828a4a83e2774c4602705880d26beaf6f2509c4b824296515233e51982310763b22c735132219ec0a21a5f9682081cc611e3d0e221e08e1531d89743f1d81c57f1d29fe0a1c1ffead1923eb0b1881f68617a8202616b50ee91581f8c8141a4f1c1413d60812baa67712b8884a1232479711981144103ead2a0f8b2a5f0f8898390f6b9a140e7e15130e7dd0190dfb96ef0d91ebc20d61f2fb0d52c9a60d4d98860cabde0a0c167f100bd753a909ee1b6f07d82e3c0754ea1506291d8305ad2f34059e8b1705869eb103e36454023f103c01013f360086a50c00273479
  | 8, 1 => 0x77211a3f72b283397260e48f70c4152b6f6c29a26f3b46226bed6d236be1bd3a6bcb63fb6b46b4d16a7ff6686a0139de67f1c0d367044c4c65b4b6696554bad1651506a464e30e646449b75d6401590261ca400860b58bf55fbac6fd5b2acd5958905d13584e132a568ff7f1567ee6cd54ed1c755342fdb7531915d1530ec13f52f2fea452942b7251d2062b514aca6d51099cc6500139404f490be64ec05ebd4d17706a4c4c79c44bc969994b0c2c394a3f78dc49e125c647e101a9472e33c145f6b58443a9f848413f306a4079af6340455b7a3cedcf813c39fd5e3a861c993a305add37dd7e80359aee6d358e7c13355e29ce330961a632ba82ac31381b07
  | 8, 2 => 0xf6657479f33b5fd0f109fd47eef3064de606f433e575a6eae1b94d76e0d9cf49d1293c1cd0e5095fd0dd3a20cea2794cc7554d2ec7466283c5690328c1043454bf01fb40bef4bb49bef1afedbe4be64fb59a84ddb559ed2fb4e46fecb37ef559b253eee6b0f51e5baabfa2cba98e4816a8e78fc4a8d9852aa80fa957a4dede88a309310c9e58572e9985b80798411d8197ec88bb97a4f387967182b59351acbb92ef4533928df7689117715e8f6e24048dbfa66d8d5eaaf98a81f0ca89211e6a877c8a9f8651842c85f48e9f85520fcd8492c7cd83f048fb7d356db97cd372a07bf0d3337b25f4ae7ae97d0f7ab5972579e15a287952d27477d135d07770373f
  | 8, 3 => 0xfb7259a6
  | 9, 0 => 0xf33b5fd0f2854adfb47be6218ab84b5d7f4590c97e1a8a5676f0de3361ca40085fbac6fd5cde0cce51bb2a0f5059633d4aee737942b779a33e277fff1606144c0e7e151305169eb0
  | 10, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x55ff55ff000000000000000000000000000000000000000000000000000000005555555500000000000000000000000000000000000000000000000000000000333333330000000000000000000000000000000000000000000000000000000011111111000000000000000000000000000000000000000000000000000000000f0f0f0f00000000000000000000000000000000000000000000000000000000030303030000000000000000000000000000000000000000000000000000000000ffffff0000000000000000000000000000000000000000000000000000000000ff00ff
  | 0, 1 => 0xffff0000ffff0000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000aaaa0000aaaa000000000000000000000000000000000000000000000000000055550000555500000000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000000000000000000000000000000000000ff000000ff00000000000000000000000000000000000000000000000000000000ffffffff00000000000000000000000000000000000000000000000000000000fefefefe
  | 0, 2 => 0x5050505050505050000000000000000000000000000000000000000000000000303030303030303000000000000000000000000000000000000000000000000010101010101010100000000000000000000000000000000000000000000000000ff00ff00ff00ff000000000000000000000000000000000000000000000000005555550055555500000000000000000000000000000000000000000000000000550055005500550000000000000000000000000000000000000000000000000033003300330033000000000000000000000000000000000000000000000000000f000f000f000f
  | 0, 3 => 0x55550000555500000000000000000000000000000000000000000000000000005550555055505550000000000000000000000000000000000000000000000000550055005500550000000000000000000000000000000000000000000000000054545454545454540000000000000000000000000000000000000000000000003333333333333333000000000000000000000000000000000000000000000000111133331111333300000000000000000000000000000000000000000000000011111111111111110000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f
  | 0, 4 => 0xaa00aa00aa00aa00000000000000000000000000000000000000000000000000a8a8a8a8a8a8a8a8000000000000000000000000000000000000000000000000555555555555555500000000000000000000000000000000000000000000000055555555550055000000000000000000000000000000000000000000000000005555555550505050000000000000000000000000000000000000000000000000555555005555550000000000000000000000000000000000000000000000000055555050555550500000000000000000000000000000000000000000000000005555444455554444
  | 0, 5 => 0xaaaaaaaaaaaaffff000000000000000000000000000000000000000000000000aaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000aaaaaaaaaaaa0000000000000000000000000000000000000000000000000000aaaaaaaaaa000000000000000000000000000000000000000000000000000000aaaaaa00aaaaaa00000000000000000000000000000000000000000000000000aaaa5555aaaa5555000000000000000000000000000000000000000000000000aaaa0000aaaa0000000000000000000000000000000000000000000000000000aaa0aaa0aaa0aaa0
  | 0, 6 => 0xcdcdcdcdcdcdcdcd000000000000000000000000000000000000000000000000cceecceecceeccee000000000000000000000000000000000000000000000000ccccccccdddddddd000000000000000000000000000000000000000000000000ccccccccccffccff000000000000000000000000000000000000000000000000cccccccccccccccc000000000000000000000000000000000000000000000000abababababababab000000000000000000000000000000000000000000000000aaaabbbbaaaabbbb000000000000000000000000000000000000000000000000aaaaaaffaaaaaaff
  | 0, 7 => 0xeeeeeeeeeecccccc000000000000000000000000000000000000000000000000eeeeeeeeee00ee00000000000000000000000000000000000000000000000000eeeecccceeeecccc000000000000000000000000000000000000000000000000eeee0000eeee0000000000000000000000000000000000000000000000000000eee0eee0eee0eee0000000000000000000000000000000000000000000000000eecceecceecceecc000000000000000000000000000000000000000000000000ee00ee00ee00ee00000000000000000000000000000000000000000000000000ddccddccddccddcc
  | 0, 8 => 0xfafa0000fafa0000000000000000000000000000000000000000000000000000faf0faf0faf0faf0000000000000000000000000000000000000000000000000f5f0f5f0f5f0f5f0000000000000000000000000000000000000000000000000f0f0f5f5f0f0f5f5000000000000000000000000000000000000000000000000f0f0f3f3f0f0f3f3000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000eeeeeeeeeeeeeeee000000000000000000000000000000000000000000000000eeeeeeeeeeee0000
  | 0, 9 => 0xfcfc0000fcfc0000000000000000000000000000000000000000000000000000fca8fca8fca8fca8000000000000000000000000000000000000000000000000fc00fc00fc00fc00000000000000000000000000000000000000000000000000fafafafafafafafa000000000000000000000000000000000000000000000000fafafafafaf0f0f0000000000000000000000000000000000000000000000000fafafafafa00fa00000000000000000000000000000000000000000000000000fafafa00fafafa00000000000000000000000000000000000000000000000000fafaf0f0fafaf0f0
  | 0, 10 => 0xfefcfefcfefcfefc000000000000000000000000000000000000000000000000feaafeaafeaafeaa000000000000000000000000000000000000000000000000fe00fe00fe00fe00000000000000000000000000000000000000000000000000fcfcfcfcfcfcfcfc000000000000000000000000000000000000000000000000fcfcfcfcfcfc0000000000000000000000000000000000000000000000000000fcfcfcfca8a8a8a8000000000000000000000000000000000000000000000000fcfcfc00fcfcfc00000000000000000000000000000000000000000000000000fcfca8a8fcfca8a8
  | 0, 11 => 0xff00ff00aa00aa00000000000000000000000000000000000000000000000000ff00fc00ff00fc00000000000000000000000000000000000000000000000000ff0000ffff0000ff000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000fefefefefefefefe000000000000000000000000000000000000000000000000fefefefe00000000000000000000000000000000000000000000000000000000fefefeaafefefeaa000000000000000000000000000000000000000000000000fefe0000fefe0000
  | 0, 12 => 0xffccccccffcccccc000000000000000000000000000000000000000000000000ffaaffaaffaaffaa000000000000000000000000000000000000000000000000ffaaffaaffaa0000000000000000000000000000000000000000000000000000ffaaaaaaffaaaaaa000000000000000000000000000000000000000000000000ffa8ffa8ffa8ffa8000000000000000000000000000000000000000000000000ff00ffaaff00ffaa000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000ff00ff00fa00fa00
  | 0, 13 => 0xfffafafafffafafa000000000000000000000000000000000000000000000000fff0fff0fff0fff0000000000000000000000000000000000000000000000000fff0fff0fff00000000000000000000000000000000000000000000000000000fff0f0f0fff0f0f0000000000000000000000000000000000000000000000000fff0ccc0fff0ccc0000000000000000000000000000000000000000000000000fff0aaa0fff0aaa0000000000000000000000000000000000000000000000000ffeeffeeffeeffee000000000000000000000000000000000000000000000000ffccffccffccffcc
  | 0, 14 => 0xffff0000ffff0000000000000000000000000000000000000000000000000000ffff0000ffcc0000000000000000000000000000000000000000000000000000ffff0000eeee0000000000000000000000000000000000000000000000000000ffff0000aaaa0000000000000000000000000000000000000000000000000000fffcfffcfffcfffc000000000000000000000000000000000000000000000000fffcfcfcfffcfcfc000000000000000000000000000000000000000000000000fffc0000fffc0000000000000000000000000000000000000000000000000000fffafffafffafffa
  | 0, 15 => 0xfffff0f0fffff0f0000000000000000000000000000000000000000000000000ffffeeeeffffeeee000000000000000000000000000000000000000000000000ffffccccffffcccc000000000000000000000000000000000000000000000000ffffccccaaaa8888000000000000000000000000000000000000000000000000ffffaaaaffffaaaa000000000000000000000000000000000000000000000000ffffaa00ffffaa00000000000000000000000000000000000000000000000000ffff5500ffff5500000000000000000000000000000000000000000000000000ffff00aaffff00aa
  | 1, 0 => 0xfffffff0fffffff0000000000000000000000000000000000000000000000000ffffffccffffffcc000000000000000000000000000000000000000000000000ffffffaaffffffaa000000000000000000000000000000000000000000000000ffffff00ffffff00000000000000000000000000000000000000000000000000ffffff00ff000000000000000000000000000000000000000000000000000000ffffff00aaaaaa00000000000000000000000000000000000000000000000000fffffcfcfffffcfc000000000000000000000000000000000000000000000000fffffafafffffafa
  | 1, 1 => 0xffffffffaaaa0000000000000000000000000000000000000000000000000000ffffffffaa00aa00000000000000000000000000000000000000000000000000ffffffffa8a8a8a8000000000000000000000000000000000000000000000000ffffffff55550000000000000000000000000000000000000000000000000000ffffffff11111111000000000000000000000000000000000000000000000000ffffffff03030303000000000000000000000000000000000000000000000000ffffffff01010101000000000000000000000000000000000000000000000000ffffffff00000000
  | 1, 2 => 0xfffffffffcfcfcfc000000000000000000000000000000000000000000000000fffffffffafafafa000000000000000000000000000000000000000000000000fffffffffafaf0f0000000000000000000000000000000000000000000000000fffffffffaf0faf0000000000000000000000000000000000000000000000000fffffffff0f0f0f0000000000000000000000000000000000000000000000000ffffffffeeeeeeee000000000000000000000000000000000000000000000000ffffffffcccccccc000000000000000000000000000000000000000000000000ffffffffaaaaaaaa
  | 1, 3 => 0xfffffffffff0f0f0000000000000000000000000000000000000000000000000ffffffffffccffcc000000000000000000000000000000000000000000000000ffffffffffcccccc000000000000000000000000000000000000000000000000ffffffffffaaffaa000000000000000000000000000000000000000000000000ffffffffffaaaaaa000000000000000000000000000000000000000000000000ffffffffff00ff00000000000000000000000000000000000000000000000000ffffffffff000000000000000000000000000000000000000000000000000000fffffffffefefefe
  | 1, 4 => 0xffffffffffffff00000000000000000000000000000000000000000000000000fffffffffffff0f0000000000000000000000000000000000000000000000000ffffffffffffcccc000000000000000000000000000000000000000000000000ffffffffffffaaaa000000000000000000000000000000000000000000000000ffffffffffff0000000000000000000000000000000000000000000000000000fffffffffff0fff0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x9f9d84542e5
  | 5, 0, 0 => 0x9f9d7761542e69f998454332e6009b8442332c50099842e1b18500994233250a500998542332559d937761542e60099844b332e500885d42332550042332e0a015008542332e01500994233302e59f9d8442332e600998433251850084332e18015009942332e225
  | 5, 0, 1 => 0x99423325225008861332a185008442332501500995142332e5
  | 6, 0, 0 => 0x9d88776642332e79188776154462e700775a5542332e60091887b61423d68d77736142332e70099844c42332e6006142251b0f096007761251b18096009977664c4233600997b61423325600776642271b096938e776154332e7008862332e180f600885c4233302e600939177612e16600008442332e015
  | 6, 0, 1 => 0x9f99776154332e79388776761542e7009b776142332c60099848342332e60088585542332e600885c4233250a68877615942332e7008877665446336009977612e1b1860088855c4233256009f998442332e600887742271b12600997b6642332e6000099844233255937c776142332e700887b676142416
  | 6, 0, 2 => 0x99918442332e600776142332501600997b61332e1860099908442332e600998884423325693917761423d2e7009b998442332e60091776153422e60088845c2e1b18600776646423309600888442332e0160093917761542568d77686154422e700882e1b18140f600887b423d3314600937761542e056
  | 6, 0, 3 => 0x9d93776142332e7008861251b180f69991776154422e700887766271b18600423325140f09600997b61422e1b600997761423f2e600776642332e01600009984332e18500887b33291814600887763544c33600a19a8442332560088663327180f600887b6142331a600885c5142332e600612e1b180f096
  | 6, 0, 4 => 0x885c42332522600939177615b2e600009942332e0a59f88776154332e7007b6142291b0960000998542332e500939161542e0f60099845442332e60000885d42332e500885e4f42332e60096917761542e6009377614a332e600845c42332509600998442332e256007742251b140960091776152422e6
  | 6, 0, 5 => 0x885c42332e22600845c332e1809600998442332e01600998442332e2c69f9d776142332e7008877614e4c3360000886142332a500887b613d331860088423325140f600998442332e2b600332e18140f096939177615c542e7009977613325186007761332e18016918e776154422e700998884332e186
  | 6, 0, 6 => 0x776142332e08600664233270f0960088845c332518693917761542e2779f90776142332e79f9b776142332e70088332518140f60089776142332e6
  | 7, 0, 0 => 0xa18877332e18147009a93776154332e7008877656142332e70077615c4233250970099776142332e257009288776154422e70088614233251d0f70092887742332e14700887e7761332e187008877555442332e700887f774233251470088776133251f18700a4887761423325700614241332e0f0970091886154422e0f70088776133251d187
  | 7, 0, 1 => 0x8882776142332e7009977615442332e7918877614842332e8008877614233250a700918877615b422e700a188614233251f7009790776142332e700978877614233257009c88775f42332e78877736142332e2680091887761423d2e7009088845c42332e7000088332e18140f6008885776142332579391776142332e27800908877422e1b147
  | 7, 0, 2 => 0x887761423325107008a88776142332e70088776a6142332e70077665c42332e097009390776154332e700938877615433257008877422e1b140f700887b6c6142332e7009f88776142332e700887e61423c332e7009188845c42332e70088776142251b14700938861422e1b0f7008877676142412e700887b615c332e18700918e776142332e7
  | 7, 0, 3 => 0x93907742332e1470093887742332514700887766422e1b147007b77614233250970088776e664233257008861424133250f7008877614c332e167000088845c332e186008877615042332e700a18877422e1b147007d7761332e1809700887761413325187000088772e1b181460088776861544c2e7008877544c332e1470088776154332e037
  | 7, 0, 4 => 0x93917742332e14700887768664233257009a887761332518700887742332e14037008842332e25140f700a28877614233257007f7761423325097008877615342332e7008877694239332e700887b615c422e1b7008877614237332e700887764614241337008877332e25181470091887761422e197007761332e180f097009588776142332e7
  | 7, 0, 5 => 0x8871615442332e70088776c6154332e70088776148422e1b700776661332e18097000088614233250f600885442332e140f7918877615c54422e80088775b5542332e7008877614233322e700888461332e180f7000061332e180f09600887a7761332e1870099887761332e1870091887742412e14793887761423d332e8009a88614233250f7
  | 7, 0, 6 => 0x88776e422e1b14700a1888461332e187008877665c423325700887b676142332e70090887761332518700887761332e18057008877614442332e700886142332e160f700666142332e0f097008f887761332e1870088776154332e177008b88776142332e7009c887761422e1b70088686154422e0f70088847f6142332570088776142332e1e7
  | 7, 0, 7 => 0x887742332e171470088775b42332e1470091907761332e18700918877613325187009a88776142251b700a19a7761332e1870088776154423d2e700887d7761332518700a38877614233257009188776642332770088845c42332e257008877423d332e147008877614342332e7008877422e251b147009088614233250f7007761422e1b0f097
  | 7, 0, 8 => 0x776661422e1b0970088776142332520700928877614233257008877726142332e70088845c5442332e7000061422e1b0f0960000887842332e14600888477612e1b1870088776142332e047000077612e1b180960000997b6142332e6008877614233252470091776142332e06700887d614233250f78877686154422e268007761544c332e097
  | 7, 0, 9 => 0x998442332e500a188614233250f7009a887766422e1b7000088613325180f6009b88776142332e700887b77614133187000088664233270f6006142332e250f0970088777061423325700887761423325007006e6142332e0f0970088614233250f0e7008f887761422e1b700008877663327186007761332e25180970088776661544c337
  | 7, 0, 10 => 0x8877614233250c700615442332e0f09700887742332e1914700887b77332e1814700686142332e0f09700a1917761332e187000088855c42332e6008877615142332e7008866614233250f700887761544c3326700978877614c332e7998877615442332e8938877676142332e800776861332e18097008877666133251870077646142332e097
  | 7, 0, 11 => 0x887b6142413c337009a776142332e037008877615242332e7009993776142332e70099776142332e2c79190776e6142332e80088776146422e1b78f8877615442332e800887761422e1b127008877614233252370088614c422e1b0f70088776142251b0f70000885c42332e0a6009a93776142332570088847742332514700007742332514096
  | 7, 0, 12 => 0x886142251b0f60077615b42332e097008e886142332e0f700776c6142332e09700887761423e332e79188776154422e2980000887761251b186007761423d332e0970088776f6142332e79188776154422e27800887761544c332570088775442412e1470077615c332e18097000088776642271b60099776142332e01700887f614233251f7
  | 7, 0, 13 => 0x88776142332503700886e614233250f700a0887761422e1b700887b77422e1b14700888077614233257008877612e1b181470097886142332e0f7009388774c332e14700887761423b332e70088776142412e05700939077614233257008877666142251b7008861584c42332e70088776142332e1a70093776142332e05700776142332e17097
  | 7, 0, 14 => 0xa191776e6142332e800887768613325187009388776042332e7009190776142412e700918877614241257008877665442332770088776461423325700887f77422e1b147887761565442332e800939177614233257008c88776142332570096887742332e147008861422e1b140f700887766614233177008877332e29181470090776142332e037
  | 7, 0, 15 => 0x93917761542e6008477614233250970088776142332e2470088776142332f2e7008861423a332e0f70088774236332e147008877614233312e7008861332e180f0d7007766614c423309700886141332e180f7008877615b42332670088614233250f0c7008861544233250f700007b61423329096919077615c42332e80093886154332e0f7
  | 7, 1, 0 => 0x88776142383325700a191776142412e70099887b6142332e700a58877614233257009a88847742332570091887761422e167918877665c42332e8008877615b42332570088776c614233257008877422e291b1470088845c42332e2b700774241332e14097009688776042332e7009188766142332e7008877615c332518700938842332e140f7
  | 7, 1, 1 => 0x8877615448332e7006142332e270f09700887761332e18067007761332e291809700938877422e1b1470077614c4233250970088776142332521700938e776142332e70088776142332e0270088776e66422e1b7008877614240332e7007761332e271809700887b615c42413370088776d6142332e700887761422e1b107008877614235332e7
  | 7, 1, 2 => 0x8877424133251470091887f7761542e7009388776154412e7008877734d42332e70092887761332e1870088776142332522700887b614233250f70000776142332e016008877554c42332e7009a8877612e1b187008879776142332570088776142332e1379a887761544c332e80093887766614c33700886142332e0f067000099888442332e6
  | 7, 1, 3 => 0x77614233251d0970000887766464233600908861422e1b0f700a18861332e180f700887761454233257008875614241332e7007742332e140f097009977614c42332e70000a19a8442332e60088817761423325700a1887b61423325700908877612e1b18700776142332514097008861332e180f0e7008877614234332e700887f614233250f7
  | 7, 1, 4 => 0x8877614942332e7008d77615442332e70093887766423327700887761422e1b00700887742332e140570088776142332e077009691776142332e70088776861422e16700939177614c332e7009a936142332e0f7009f99776142332e700888777614233257000042332e140f096009488776142332e700009977614233256000088614233290c6
  | 7, 1, 5 => 0x887f776861542e700887b77424133147008877614233250b70091887761423a2e70091887761412e1870088776461332e18700884c42332e140f7008877423325140f70000845c42332e0969088776c6142332e80077614842332e0970093906142332e0f7009388614233250f7009088756142332e7009888776142332e700887766612e1b187
  | 7, 1, 6 => 0x887c776142332e7000088845c4233256007d77614233250970088776142332e0170088845c4c42332e700776142332e16097008877614233251c70088776142332e22700886e61422e1b0f70077686154422e09700888477614233257008877612e251b187008877635442332e700847761332e1809700887768544d422e7000088423325140f6
  | 7, 1, 7 => 0xa19a776142332570077614c422e1b097939177615c42332e80088776142332516700887768615442257009990776142332e700998877614233257008884776133251870000776133251809600887761332e191870088776c61422e1b70088776e4233251d7009b99776142332e7008877615c2e1b18700887761544c412e700887b665c42332e7
  | 7, 1, 8 => 0x88776142332e157008877612e271b1870077615442332509700908842332e140f70088776142332e1c7008877615742332e7008877614233302e70088776b6142332e700008842332e140f60077615b5a42332e70000997761332e186
  | 8, 0, 0 => 0x908877614c42332e800007761332e1809688776e6142332e288938877615c42332e8009a88776142332579c9088776142332e88877614241332e14800887742332e2514700776142332e0f0978877614c4742332e80088776e42332e147888177615442332e8918884776142332e8000088845c42332e69a8877614c42332e8007d776142332e097
  | 8, 0, 1 => 0x918877614c42332e8008f88776142332e70088776142332e117887d77614c42332e80088776142332e1670077666142332e0970088846142332e0f7008877686154422e700006142332e0f09600887f7b6142332e7000088776142332560088775442332e14700887a776142332e7009988776142332e70088847761332e1870088776842332e147
  | 8, 0, 2 => 0x93887b776142332e80088776142332e1270088614c42332e0f7008877614233250f7a18877614c42332e89088776142332e148008886776142332e7009190776142332e70091887761423325700a19a776142332e700887d77614233257009a88776642332e700a188846142332e7a188776142332e2d8009088776142332570088776142332e057
  | 8, 0, 3 => 0x887b7742332e14700a191776142332e700887761332e18147888477615442332e80077615442332e0970077686142332e09700887766614233257000088614233250f600887b77614241337000088776133251868884776142332e2580000887766423327600776142332e250979188776142332e148887766614c42332e8008877614642332e7
  | 8, 0, 4 => 0x887742332e2914700887761422e1b1470088776142332e0a7887768614c42332e8009788776142332e7008885776142332e7887761544f42332e80077615c42332e097887770614c42332e89388776142332e2989388776142332e27800887f7742332e14700a488776142332e700886142332e140f7008877614c422e1b700a088776142332e7
  | 8, 0, 5 => 0x969388776142332e88877615442332e14800886142332e0f0d70088776e6642332e70088614241332e0f700887761423a332e7979188776142332e88877615442332e1688877615c4c42332e80088776142332e1079a887d776142332e80088776154423325788776142332e2514800887768614233257009388776154332e78877614241332e0f8
  | 8, 0, 6 => 0x90887761332e1879188776142332e0f800776142332e27097928877614241332e8008877666142332e70088847f6142332e70000886142332e0f6009a886142332e0f790887d776142332e8009a887761332e18700a288776142332e7008877615c4233257888077614c42332e888776142413c332e8887766614241332e80093887742332e147
  | 8, 0, 7 => 0x886142332e0f0e7009288776142332e79a88776142332e258908877746142332e8887d77666142332e89088776142332e0688877614c42332e1780091887761332e187009a887761422e1b78877615b4c42332e800887d7761332e187908877666142332e80090886142332e0f70088776142332e067008877665c42332e78884776142332e2b8
  | 8, 0, 8 => 0x908877615442332e8908877686142332e89188776142332e2589188776e6142332e8887d776142332e258887d776e6142332e8a18877666142332e8978877615442332e80088776661332e18700a1886142332e0f7929088776142332e89a8877615442332e800008861332e180f6a39188776142332e8008877706142332e70088776142332e007
  | 8, 0, 9 => 0x84776142332e097887766615442332e8a18877686142332e80088776861332e187009188776142412e7008877646142332e7009391776142332e700886e6142332e0f7908877615c42332e8008880776142332e700887761332e251870088776661422e1b79e9188776142332e800008861422e1b0f600008877612e1b18600887761544c332e7
  | 8, 0, 10 => 0x88847761423325700887b6142332e0f78877615c42332e25800007761423325096888477614c42332e891887f776142332e80077614c42332e0978877615442332e2588877686142332e25891887b776142332e800a588776142332e70088776142332e177008877615b42332e78877615442332e2680088776c6142332e7008877615c332e187
  | 8, 0, 11 => 0x8877614c4241332e8008884776142332e78877615442332e27800008842332e140f6008877614233251d78877615b5442332e8887f77686142332e80093886142332e0f7000099776142332e600887761332e29187008877614c423325700887761332e27187008881776142332e78877615c5442332e8887f77666142332e8887b77666142332e8
  | 8, 0, 12 => 0x908884776142332e8
  | 9, 0, 0 => 0x88776142332e2778877615c42332e78877615442332e78877686142332e788776142332e2578877666142332e700886142332e0f600887761332e1869188776142332e7887d776142332e79088776142332e70088776142332e69a88776142332e788776142332e1470088776142332568877614c42332e7
  | 9, 0, 1 => 0x8884776142332e700776142332e096
  | 10, 0, 0 => 0x88776142332e6
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 44
  | 5 => 52
  | 6 => 60
  | 7 => 68
  | 8 => 68
  | 9 => 60
  | 10 => 52
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 8 0) :: stateWires n (ids >>> 8)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x7fff87ff000000000000000000000000000000000000000000000000000000007f0f87f8000000000000000000000000000000000000000000000000000000007ff87c67000000000000000000000000000000000000000000000000000000007f0804600000000000000000000000000000000000000000000000000000000070fffc1f0000000000000000000000000000000000000000000000000000000070f87c07000000000000000000000000000000000000000000000000000000000fffffff000000000000000000000000000000000000000000000000000000000ff803ff
  | 0, 1 => 0xfff8007ffff00000000000000000000000000000000000000000000000000000e000007fc00000000000000000000000000000000000000000000000000000000000000780700000000000000000000000000000000000000000000000000000fff800787f800000000000000000000000000000000000000000000000000000e078007fc1f000000000000000000000000000000000000000000000000000001ff800003ff000000000000000000000000000000000000000000000000000000007fffffff000000000000000000000000000000000000000000000000000000000ff7fbff
  | 0, 2 => 0x3fe07f00f84180000000000000000000000000000000000000000000000000003fe00f0f87c070000000000000000000000000000000000000000000000000003fe00f0080400000000000000000000000000000000000000000000000000000071ff8ff803ff00000000000000000000000000000000000000000000000000007fff8f0f87f8000000000000000000000000000000000000000000000000000071ff8f0803f8000000000000000000000000000000000000000000000000000070388ff800670000000000000000000000000000000000000000000000000000700780f8001f
  | 0, 3 => 0x3f0007f08000000000000000000000000000000000000000000000000000000038ff87f0787e000000000000000000000000000000000000000000000000000038e0070078400000000000000000000000000000000000000000000000000000001ff0f0783f80000000000000000000000000000000000000000000000000003fe38fff87c670000000000000000000000000000000000000000000000000003fe38ff087c670000000000000000000000000000000000000000000000000003fe38ff0804600000000000000000000000000000000000000000000000000003fe07f0fffc1f
  | 0, 4 => 0x780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ffffff0f87f80000000000000000000000000000000000000000000000000003fffff00784000000000000000000000000000000000000000000000000000003ffff8f0003e00000000000000000000000000000000000000000000000000003fe007f0f84000000000000000000000000000000000000000000000000000003f1f87f0803e00000000000000000000000000000000000000000000000000003f1c77f0f8398
  | 0, 5 => 0xf7ffff0000000000000000000000000000000000000000000000000000000000f078070000000000000000000000000000000000000000000000000000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0780000000000000000000000000000000000000000000000000000000fff80f787f80000000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000000007800
  | 0, 6 => 0x3ffc7f00f8798000000000000000000000000000000000000000000000000000001c700f7839f000000000000000000000000000000000000000000000000000001c77f0f87f8000000000000000000000000000000000000000000000000000001c70fff83ff000000000000000000000000000000000000000000000000000001c7000783980000000000000000000000000000000000000000000000000003fe00f0f87c0700000000000000000000000000000000000000000000000000000e3880f07c67000000000000000000000000000000000000000000000000000001ff80f07bff
  | 0, 7 => 0x1c700078398000000000000000000000000000000000000000000000000000001c70007f800000000000000000000000000000000000000000000000000000001c700f783980000000000000000000000000000000000000000000000000000000000f00000000000000000000000000000000000000000000000000000000001c00007fb80000000000000000000000000000000000000000000000000000001c70007fb98000000000000000000000000000000000000000000000000000000000007f80000000000000000000000000000000000000000000000000000038fc770078798
  | 0, 8 => 0xff00000000000000000000000000000000000000000000000000000000001f80f007be000000000000000000000000000000000000000000000000000038ff87f0787e000000000000000000000000000000000000000000000000000000fff8f0787f800000000000000000000000000000000000000000000000000000ff88f007fe7000000000000000000000000000000000000000000000000000001f80f0003e0000000000000000000000000000000000000000000000000000001c700f7fb9f000000000000000000000000000000000000000000000000000001c700f00000
  | 0, 9 => 0xf00000000000000000000000000000000000000000000000000000000000000000780000000000000000000000000000000000000000000000000000000000000078000000000000000000000000000000000000000000000000000000001f80ff07be7000000000000000000000000000000000000000000000000000001f80f0003e0000000000000000000000000000000000000000000000000000001f800007800000000000000000000000000000000000000000000000000000000000ff07800000000000000000000000000000000000000000000000000000001f80ff003e0
  | 0, 10 => 0x1ff0f07fbf80000000000000000000000000000000000000000000000000000000000f7f807000000000000000000000000000000000000000000000000000000000007f800000000000000000000000000000000000000000000000000000001ff0f0783f8000000000000000000000000000000000000000000000000000001ff0f000000000000000000000000000000000000000000000000000000000001ff00000000000000000000000000000000000000000000000000000000000000000f078000000000000000000000000000000000000000000000000000000000000f000000
  | 0, 11 => 0x38e00000078000000000000000000000000000000000000000000000000000003800070078000000000000000000000000000000000000000000000000000000381fff00003ff0000000000000000000000000000000000000000000000000003800070000000000000000000000000000000000000000000000000000000000001ff0ff7fbff000000000000000000000000000000000000000000000000000001ff00000000000000000000000000000000000000000000000000000000000000000ff7f807000000000000000000000000000000000000000000000000000000000ff00000
  | 0, 12 => 0x381c77007839800000000000000000000000000000000000000000000000000038e0070f7fc0700000000000000000000000000000000000000000000000000038e0070f000000000000000000000000000000000000000000000000000000003800070f0780700000000000000000000000000000000000000000000000000038e007007fc0000000000000000000000000000000000000000000000000000038e007007fc0700000000000000000000000000000000000000000000000000038e007007fc0000000000000000000000000000000000000000000000000000038e0000007800
  | 0, 13 => 0x381f87ff07be700000000000000000000000000000000000000000000000000038ff87f07ffe000000000000000000000000000000000000000000000000000038ff87f000000000000000000000000000000000000000000000000000000000381f87f0003e0000000000000000000000000000000000000000000000000000381c07f078380000000000000000000000000000000000000000000000000000380007f00780000000000000000000000000000000000000000000000000000038fc770f7ff9f00000000000000000000000000000000000000000000000000038fc77007ff98
  | 0, 14 => 0x3f0007ff800000000000000000000000000000000000000000000000000000003f000700000000000000000000000000000000000000000000000000000000003f00000f000000000000000000000000000000000000000000000000000000003f00000f0000000000000000000000000000000000000000000000000000000038fff7f07fff8000000000000000000000000000000000000000000000000000381ff7f0783f8000000000000000000000000000000000000000000000000000380007f00000000000000000000000000000000000000000000000000000000038ff87ff7ffe7
  | 0, 15 => 0x3f1f87ff803e00000000000000000000000000000000000000000000000000003f1c77ffffb9f0000000000000000000000000000000000000000000000000003f1c77fff83980000000000000000000000000000000000000000000000000003f1c700f000000000000000000000000000000000000000000000000000000003f0007ff878070000000000000000000000000000000000000000000000000003f0007ff878000000000000000000000000000000000000000000000000000003fe007fff84000000000000000000000000000000000000000000000000000003f0007ff80007
  | 1, 0 => 0x3fff87fffffe00000000000000000000000000000000000000000000000000003ffc77fffff980000000000000000000000000000000000000000000000000003fe007ffffc070000000000000000000000000000000000000000000000000003fe007ffffc000000000000000000000000000000000000000000000000000003fe00700000000000000000000000000000000000000000000000000000000003fe0000f078000000000000000000000000000000000000000000000000000003f1ff7fff83f80000000000000000000000000000000000000000000000000003f1f87ff87be7
  | 1, 1 => 0x3ffff80f000000000000000000000000000000000000000000000000000000003ffff800078000000000000000000000000000000000000000000000000000003ffff800000000000000000000000000000000000000000000000000000000003ffffff0800000000000000000000000000000000000000000000000000000003ffffff0804600000000000000000000000000000000000000000000000000003fffff0f87c070000000000000000000000000000000000000000000000000003fffff00804000000000000000000000000000000000000000000000000000003ffff80000000
  | 1, 2 => 0x3ffff8f0783f80000000000000000000000000000000000000000000000000003ffff8ff07be70000000000000000000000000000000000000000000000000003ffff8ff003e00000000000000000000000000000000000000000000000000003ffff8f007be00000000000000000000000000000000000000000000000000003ffff8f0003e00000000000000000000000000000000000000000000000000003ffff80f7fb9f0000000000000000000000000000000000000000000000000003ffff800783980000000000000000000000000000000000000000000000000003ffff80f07807
  | 1, 3 => 0x3ffffff0003e00000000000000000000000000000000000000000000000000003fffff007ff980000000000000000000000000000000000000000000000000003fffff00783980000000000000000000000000000000000000000000000000003fffff0f7fc070000000000000000000000000000000000000000000000000003fffff0f078070000000000000000000000000000000000000000000000000003fffff007fc000000000000000000000000000000000000000000000000000003fffff00000000000000000000000000000000000000000000000000000000003ffff8ff7fbff
  | 1, 4 => 0x3fffffffffc000000000000000000000000000000000000000000000000000003fffffff803e00000000000000000000000000000000000000000000000000003ffffffff83980000000000000000000000000000000000000000000000000003fffffff878070000000000000000000000000000000000000000000000000003fffffff800000000000000000000000000000000000000000000000000000003ffffff07ffe0
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x673b07fb00000000000000000000000000000000000000000000000000000000660b07500000000000000000000000000000000000000000000000000000000055603462000000000000000000000000000000000000000000000000000000004400044000000000000000000000000000000000000000000000000000000000305aa81900000000000000000000000000000000000000000000000000000000104020000000000000000000000000000000000000000000000000000000000003399ffb00000000000000000000000000000000000000000000000000000000033802bb
  | 0, 1 => 0xedb8005ddef00000000000000000000000000000000000000000000000000000e920005dd40000000000000000000000000000000000000000000000000000002498000d8af00000000000000000000000000000000000000000000000000000c9200050540000000000000000000000000000000000000000000000000000006038004c80d00000000000000000000000000000000000000000000000000000049800000af00000000000000000000000000000000000000000000000000000000777bbffb00000000000000000000000000000000000000000000000000000000777bbffb
  | 0, 2 => 0x12406200e00100000000000000000000000000000000000000000000000000000920090c0600400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000716d8bb802bf00000000000000000000000000000000000000000000000000006db60a0d0750000000000000000000000000000000000000000000000000000061240a0802100000000000000000000000000000000000000000000000000000502889a00026000000000000000000000000000000000000000000000000000030058098001d
  | 0, 3 => 0x361246e0a021000000000000000000000000000000000000000000000000000034db26e07074000000000000000000000000000000000000000000000000000030c926407054000000000000000000000000000000000000000000000000000036db66e0f07500000000000000000000000000000000000000000000000000002da38dde0746600000000000000000000000000000000000000000000000000024a38cc005466000000000000000000000000000000000000000000000000000248304c0004400000000000000000000000000000000000000000000000000001b607b0dee81d
  | 0, 4 => 0x82001040f80000000000000000000000000000000000000000000000000000000049013098ab00000000000000000000000000000000000000000000000000036db66e0f075000000000000000000000000000000000000000000000000000036db66c07054000000000000000000000000000000000000000000000000000036db64e05074000000000000000000000000000000000000000000000000000036db66e0f0750000000000000000000000000000000000000000000000000000369b46e0b0750000000000000000000000000000000000000000000000000000365a66e0f0310
  | 0, 5 => 0x924991f1fdef0000000000000000000000000000000000000000000000000000924991f0f8af0000000000000000000000000000000000000000000000000000924991f060040000000000000000000000000000000000000000000000000000924990c060040000000000000000000000000000000000000000000000000000920011f0f80000000000000000000000000000000000000000000000000000009c9211f525400000000000000000000000000000000000000000000000000000900011f02000000000000000000000000000000000000000000000000000000082481160f8a2
  | 0, 6 => 0x125c7221f8b99000000000000000000000000000000000000000000000000000135cfa3bf8bbf000000000000000000000000000000000000000000000000000125c7661f8fd9000000000000000000000000000000000000000000000000000125c7233f8bbb000000000000000000000000000000000000000000000000000125c7221f8b990000000000000000000000000000000000000000000000000000924991f0f8af00000000000000000000000000000000000000000000000000009a5991f0fcef0000000000000000000000000000000000000000000000000000924991f0f8af
  | 0, 7 => 0x1b7cfb2dfeb9d0000000000000000000000000000000000000000000000000001b7cfb0c7f9040000000000000000000000000000000000000000000000000001b5c733ffab990000000000000000000000000000000000000000000000000001b10433fa2210000000000000000000000000000000000000000000000000000187ca3367fba20000000000000000000000000000000000000000000000000001a7c7325ffb99000000000000000000000000000000000000000000000000000186823047f90000000000000000000000000000000000000000000000000000032dd7661f8fd9
  | 0, 8 => 0x2d1205ff022000000000000000000000000000000000000000000000000000002cbf85f61ffe200000000000000000000000000000000000000000000000000034dfa6f2717e200000000000000000000000000000000000000000000000000024dfa4f2517e200000000000000000000000000000000000000000000000000024bf8cf2157e6000000000000000000000000000000000000000000000000000249f84f2117e20000000000000000000000000000000000000000000000000001b7cfb3fffbbf0000000000000000000000000000000000000000000000000001b7cfb3fe6214
  | 0, 9 => 0x361246f3a021000000000000000000000000000000000000000000000000000030cdb65379deb00000000000000000000000000000000000000000000000000030c9264079d400000000000000000000000000000000000000000000000000002dbf9dff1ffef0000000000000000000000000000000000000000000000000002dbf9dfe177e60000000000000000000000000000000000000000000000000002dbf9dcc1fd440000000000000000000000000000000000000000000000000002dbb05ff1ff400000000000000000000000000000000000000000000000000002d9f85ff137e2
  | 0, 10 => 0x3efff7f7ffffb00000000000000000000000000000000000000000000000000039edbf5f7fdef00000000000000000000000000000000000000000000000000038e927447fd4000000000000000000000000000000000000000000000000000036dff6f3f9ffb00000000000000000000000000000000000000000000000000036dff6f3e021000000000000000000000000000000000000000000000000000036dff093498ab00000000000000000000000000000000000000000000000000036db66f3f9f500000000000000000000000000000000000000000000000000003616d6f3a9abb
  | 0, 11 => 0x38e921044f80000000000000000000000000000000000000000000000000000038c927447bd4000000000000000000000000000000000000000000000000000038049f44220af00000000000000000000000000000000000000000000000000038000744220000000000000000000000000000000000000000000000000000003ffffffffffff0000000000000000000000000000000000000000000000000003ffff888440040000000000000000000000000000000000000000000000000003ffffffffffff0000000000000000000000000000000000000000000000000003f1247ffa2210
  | 0, 12 => 0x3a5c7765fab9900000000000000000000000000000000000000000000000000039edbf5f7fdef00000000000000000000000000000000000000000000000000039edbf5f6600400000000000000000000000000000000000000000000000000039249f5f2f8af00000000000000000000000000000000000000000000000000038edb7577fdeb00000000000000000000000000000000000000000000000000038edbf447fdef00000000000000000000000000000000000000000000000000038e927447fd4000000000000000000000000000000000000000000000000000038e925445fd40
  | 0, 13 => 0x3dbf9fff3ffef0000000000000000000000000000000000000000000000000003cffa7f67ffe20000000000000000000000000000000000000000000000000003cffa7f6662000000000000000000000000000000000000000000000000000003c9f87f6337e20000000000000000000000000000000000000000000000000003c5e27f67ab800000000000000000000000000000000000000000000000000003c3687f62faa20000000000000000000000000000000000000000000000000003bfdff7ffffff0000000000000000000000000000000000000000000000000003afd7765fffd9
  | 0, 14 => 0x3f1247ffa22100000000000000000000000000000000000000000000000000003f1247eda22100000000000000000000000000000000000000000000000000003f1243bfa22100000000000000000000000000000000000000000000000000003f12419f020000000000000000000000000000000000000000000000000000003efff7f7ffffb0000000000000000000000000000000000000000000000000003edff7f7fbffb0000000000000000000000000000000000000000000000000003e1247f7a22100000000000000000000000000000000000000000000000000003dffbfff7ffef
  | 0, 15 => 0x3f9fc7ffb37f20000000000000000000000000000000000000000000000000003f7effffffbbf0000000000000000000000000000000000000000000000000003f5e77fffab990000000000000000000000000000000000000000000000000003f5e719f4a8890000000000000000000000000000000000000000000000000003f36dfffafabf0000000000000000000000000000000000000000000000000003f3247ffafa100000000000000000000000000000000000000000000000000003fdb67fff27500000000000000000000000000000000000000000000000000003f16dfffa22bf
  | 1, 0 => 0x3fffe7ffffff20000000000000000000000000000000000000000000000000003fff77fffffd90000000000000000000000000000000000000000000000000003ffffffffffff0000000000000000000000000000000000000000000000000003ffb67fffff500000000000000000000000000000000000000000000000000003ffb67cc660000000000000000000000000000000000000000000000000000003ffb619f4f8000000000000000000000000000000000000000000000000000003fdff7fffbffb0000000000000000000000000000000000000000000000000003fbfdfffbffff
  | 1, 1 => 0x3ffff99f460040000000000000000000000000000000000000000000000000003ffff98c4f8040000000000000000000000000000000000000000000000000003ffff89b4d8af0000000000000000000000000000000000000000000000000003ffffee8e42140000000000000000000000000000000000000000000000000003ffffcc8444440000000000000000000000000000000000000000000000000003ffff98c460040000000000000000000000000000000000000000000000000003ffff888440040000000000000000000000000000000000000000000000000003ffff88844004
  | 1, 2 => 0x3ffffefbfdfff0000000000000000000000000000000000000000000000000003ffffdff5ffef0000000000000000000000000000000000000000000000000003ffffdff577e60000000000000000000000000000000000000000000000000003ffffdfe5ffe60000000000000000000000000000000000000000000000000003ffffcfa557e60000000000000000000000000000000000000000000000000003ffffbbfffbbf0000000000000000000000000000000000000000000000000003ffffaa9fcb9d0000000000000000000000000000000000000000000000000003ffff99f4f8af
  | 1, 3 => 0x3ffffffe777e60000000000000000000000000000000000000000000000000003fffffedfffdd0000000000000000000000000000000000000000000000000003fffffedfeb9d0000000000000000000000000000000000000000000000000003fffffdf7fdef0000000000000000000000000000000000000000000000000003fffffdf6f8af0000000000000000000000000000000000000000000000000003fffffcc7fd440000000000000000000000000000000000000000000000000003fffffcc660040000000000000000000000000000000000000000000000000003ffffffffffff
  | 1, 4 => 0x3ffffffffff540000000000000000000000000000000000000000000000000003ffffffff77f60000000000000000000000000000000000000000000000000003ffffffffeb9d0000000000000000000000000000000000000000000000000003fffffffefabf0000000000000000000000000000000000000000000000000003fffffffe62140000000000000000000000000000000000000000000000000003ffffffe7ffe6
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 166 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 166 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 166 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 166 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 8 0) :: stateWiresD n (ids >>> 8)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 8 0) :: stateWiresS n (ids >>> 8)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 10 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 5 => 38
  | 6 => 424
  | 7 => 1691
  | 8 => 491
  | 9 => 9
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0xe9af5f4eb6e80d6aaf9c93baab4b32d1a69a28269c853db79acb318791249fa690b36ae98e431950854243ba7e0e28c87d13b5847513e8cd706ed35c6ff17322682153e7678eaa4f4fd9417047722ff542b779a341582bf44085596433e974ad322c7bc82daeb2ee2d6ca1df2a70eab82a16ecff226528651e45ab2f1809c6db1338cb65117e5ae409b1822a0858b8aa0824bf5405323e3c
  | 6, 0 => 0x16eb0e0416718ae7161c81b3160c315a151ef48314e4822513c93bbb13bf8c241356a1bd12ee29ce126bfdab12648d5b122cdb69105ef3e91056a0980fca74160fa22a3f0f8898390f124bee0f115ba20ef08abd0eb903040e7e15130e1cb4fc0e15721d0da6e0160d4ae8920cabde0a0ca8f48b0c69bfd00c6584570c236eef0bd5dce90a1efef009d43afa09cab3ef098b9ffe096e9438095d62600956f267091999780901497508697de008531ca106f6939e06e9115106e433630612708805ca702105b8649705a805b7053f9f860505ca7204c58478040779340373c604023123c802291043011daf4c01132c3101013f3600e3021600c447de00bbc069
  | 6, 1 => 0x300024392fd64be42f37b6b72e5cd50e2cadc4612c7a55332c45359f2c2816dc2be3fc842b81626d2b3f49ac2b3720452ab77fdf2a2ac81c29eedbb82907425528a4a83e2899c1c7281a6a4327d9de4a2779c54f27320b4f2705880d26c09f4926b76139261bbf1925d32ac224f85f8a23e3e51a22cdf8ec22c397a522b5ff3021b06328213869ba211cf30c20d8cb391d600c9e1be447e11bd06d721ba9ade81ae2b9091a88a8e91a2639791a1c5a8c1a0f2ada1a0dbb1919f7890919d5fa50197c4452195d4ed31907cfbb190722ad18f26c4c187d0f6b186cfbda17ea453517c6219b17c1f8db176424311755fd74173c6c161734bd56170619d117016561
  | 6, 2 => 0x4ddb76074d84259f4c30865f4beee6fc4bcf16184ab3aee749376aa9486fe221486f70364841176a48388c2847b4abff47722ff5476435d84724ee6c46b110c0464d910745f9e6bc45a7f598451f7c0844debeae44b3865944540250442e328f43daba4142e2365142b779a3429d7e91420e8bc441cdfba641a885d34166a38140ef423c40722d163e30959e3db22c033d513e8d3c61985c3bac7cde3ae7821438ced83238a27cd73896d40737809ff03761c3f3376135eb36c1640236bfe51836812025355171d63536fa9d3535686134b427f234a7feb133a8b0d7333d305e32fe99e432fa2f95326c226030ef49ec30c8d3d030625b533037bc2b3031bd6b
  | 6, 3 => 0x701596636f8cf6046e09c3cf6c407a466c3e88df6b3aaaec6aae745d692ba2fb68716f4067d2ecc667a7b8ad676fce606759339d670d50ea660cf11265b7c46d64f1f45764da421264c6eb2f649bbfe3647c796e64683a6a64610497645b98ab63fb6a7f637eec3e63474bf4633b241c6296399e61e8177e6118463c608535a55fe3d1285fbac6fd5fac40685f772fc05db7f7b65d903ee95d71535d5c1752f25b399d1f5967c8f75925466958e251305833dde557bd5a1b56c4e88f56474569557c9ff554fb57fa545a40c853f2805153e59131533e153352d1cdb7520bcc1b51d3bdbf51cc3e21518fb60c50c755c14f1bb8244ebf453b4e29c7d14e1eb31a
  | 6, 4 => 0x96181c3c94f1379493ea938093b4f6c1936c0306930ac8c492a61c5c92879af9927cdf3d91d2873e9148b10390fd764c90e2f0448f344b4a8e999bd18dde9fde8dc733e58d5eaaf98d3d25558cedacd18cb824a98bb136488ab4d0818a81f0ca888265a5874936a1873e250985e097ab85965ce1842ebc3f842bd5eb8370a7f4833452068319ef288315b24682f377b081e9f85c81a4c77f817ebe3580feb7d980e6615380bc3ac37e601bf47e34a38b7c347e527c2f9e497c039c0f7b8be45d7b03809c7a5971ad79e15a2879c7a151791205e278f86d6077919af7777cb77e7592030a754fe6cf72c5d620722eeeb672157d2371a7a8897134af5a704d5e58
  | 6, 5 => 0xc8d1092fc814806cc6a07237c67def90c4cf7f70c31c7fe0c275c635c24f89c6c219efd3c0d13c78bf8f9076be4be64fbd8203c1bc0e36a8bbb787aabb5bf358b950c2ecb87b1668b7aa0c84b6d8a086b6688cecb65be785b55610b3b5082829b326e2eab31fa38db22bdbebb14d1a14b0e177f3b0c17e9db092cc10b037660bafee86afaf988793af7a591dad99850ead64f2d1abea3691a99994daa8112672a7482f20a6d2ddc5a621259fa47ac71da3c65a94a22de227a1d961dfa0156c749f9e06679ec0d7899d8a59eb9cefd78c9c97795a9c5f57449b7186cd997feab4994bd1c298a19efa989eac8e97ac0d10975c29ad972eb7d796db332596ced852
  | 6, 6 => 0xfed2e10cfa818023f9262a4ff5f6f027f1d8600eeef3064ded7883eeeb738980eb4fcf47eb2171faea8c7e56e751feeee545e120e3af474de2fac4fee1de3ec8e176c27ddefb0a41ddfb04cddde8557bdd76d249dd256194dc730934dba68411db711277daaef95ad9257160d6e25d60d666d900d5806030d1deb035d1293c1ccd8d4f4cccc7daa6ccbba923cb7d3a0dcb0f381bca5f7c46c9fccdb9c928f482
  | 7, 0 => 0x60e01a405ad2f3405725c9f052aa49505169eb00509fa1f04e37e8404c021da04bca65904ba8cc304aea85504aaa2b0048dacd704824cd4046088880459b5e30442bd8604427d3b042b89970375c6cf035987fe033b05b5033a727c0318307a02dc927b02c16857029bda2f0299fc920295a270028de01e026249d20249a99b02470b1b023f5c5b02363de202102cb9020b934d01e3cad001b5ee8d01abdea401a6e4da01a5e674019fd767019f361a019c9fad016603570165a78a01652a32015fcb3e014fcec7014268c7012a584001189ba9011182d801013f3600f9b8fb00f5a3d200ea38dd00c4d48b00b34936009aeaed00955441003b1ab40029bfef
  | 7, 1 => 0xaee98b70ae653d70ae34fac0acf09dd0ab8b2690aad79ad0aa03d900a7677f50a5e33fe0a53c4d609ee1b6f09ec2ffe09eb9e2109ea0c3209d9969709c0e32809bd51ef09a18f540989c7c309643386093e73560913c1b1090dfc8408fadadf08e4c69e08df973908cbc54008b081660899ab530865d84f0844bf83083004ee081c74db081be46607f92a9407f1b6d607ed8a3207c038b307a3436a0790b29f078f1e53078c6002078b6284074eba94073d42b70737882a0720ca0a071cbf990715437d07073daf06fb5c5206a8768f068bc39d06735b22065dc92d0659598f065401810651b5d50638a75e062e761d06291d8306237d4e060f596e060e91e7
  | 7, 2 => 0xf6b9a140f56ffe60f53334a0f3d84400f3a3da50f1a8f2b0f1986a90f16fff20f06017a0eed14a20ee0af2a0ed019dd0ebfb63b0e974d5b0e90cf7c0e7e15130e7dd0190e7515ed0e5d94ed0e4ddd170e1f184a0e05ccb20df565b60df435510de1cc4b0dcd46f30dc23f740db432850d86001e0d7f85ab0d61f2fb0d5a81df0d570f570d49c4170d40e0e10d3586890cf439bf0cea20e10cba81470c8c4ccf0c825c970c60dcf80c498d8c0c3486130c2ad96d0c232aad0c22507d0c03b9010bd70bfb0bd3d3cb0bb6718b0bb0c3ae0ba0f9160b9beb890b985bbe0b8ad6cc0b76e6c50b5bd3a60b2c8ce60b2912830b2179b20b1a7d630af89e950af197a6
  | 7, 3 => 0x155cba4e154b39521517feab14e2d7e014db29201499cfe51480f23a147d1c17146bdca814649f8f1415063f13ea83c213e90d2b13c146b6136d10ac1368a986133c08ef13346ed11317dd2b12ff424112ddb43412a8595d1280f92b126ef838124d6d631247bf781234695d1228cbf912245a68122261f8121617f5120061e011c1f92a11bd50f4119b91ab11981144118eca21118d0e1d1187183a117804a4114c695c11171f8f10de35ff109faa42109ef9a3109bbfbb109410fb108bef5710835d3110783863104ef361104862a5103ead2a102c960a1015aee70fec104b0fceabe00fb1a7760faa77070f9788b90f8898390f808c130f7ac0e10f78ea77
  | 7, 4 => 0x1a13ea6d19fc1ed919e220af19ddb2d519c7c79119b1d44819a917ce198916cb1980bc2919403fcf19399e18192a0dd61923eb0b1921f28d18ef4baf18eb5771189d69961891280c188349881881f68618787ffd1860cf5518545dd61830634d182bf92618261f78181c0a6c17e7c6aa17e4d13d17ddd95917d64a9117c5c22e17bf920f17b7e34f17b0da9817a3f1f5179c6b23177154d6176aac0017246252171f64aa1706ecff16d77b9d16d21d8816c91dcd16b01e5416987722168bc85d167d3186166385a0165a143316573f0016528f35164f38e0164042a2160c7aef1606144c15e9498b15d3b4e415c4f37415ba6e6315af65f115776f95156445b9
  | 7, 5 => 0x2015ae6f2014c6441fed21a51fecb1011fd3d3851fad31dc1fac1ffd1fa565611fa432931f75faad1f5f0d481f3e5d811f3387171edb86661e5ad6651e56e02b1e2acf241e08e1531e0576261de45f961daeb8c11d9e38471d98a19b1d85cfcc1d81c57f1d73f5661d6198e01d2a81d31d1067761d07cbc61cfd2fc91ceeb9671cd93b5f1caf33921ca81a3a1ca481c01ca0b1831c32bad41c228a231c1ffead1c193f401bf5be811bc7d4b01baf8e761b9935371b9386ad1b933b9e1b62a5db1b6003b71b52f3321b5233871ae9b4a21ac819931ac6cf551ab858541ab658ae1a90e4691a7c026f1a6a04de1a58a2341a548add1a4058c31a2660db1a1cf344
  | 7, 6 => 0x2750b4f62748e4d0273e087b2705880d26eeeb7b26dd32d726d16b4626d0c80326beaf6f26bb2fef26b48b0426b1ab7426ad119126a8a450269ac23a26640762265363bb2648e3a826396ad4260a164f25e4685525de408525d992dc259a3137258a599a2578e98e252f3bbb250b3e6a250aba5724f9ef9824f9d1c424f27cee24c9ba2d24bf6a36247cc1fc2444866924429b14243971d52437f8a923e6546623e3ab7622c96b3022c7351322986b962289ec0b228054752246c5202219ec0a21e6cbde21de28f921ce372521c636b821b5c2d421a5f9682177d428214d3bd72145ca59213f9045213bddeb213819c920e2e2e9205b0a2a203e530f203dbfd6
  | 7, 7 => 0x2d70ced82d3e70562d17f6e82d14647b2d014b912cc795ae2c7afb6d2c58dac22c18d8712be239292b87620c2b81faf52b5913022b3e6d342b19bbf42b0fca262b08f8cc2afee4492afda44c2af8e8dd2af3c5ea2acd7a982a95391c2a8e42722a8999b02a6cf0712a5617002a5335872a4993872a2491622a245e7b2a1706c029f9c57229f0b1cd29ed6e3b29e0d67129b1bd8a2992b93229922d3f298b593d2989cbc0297c99f8296b38aa29428e4b292af8b729259dd72920d8b3291d2a9e2912a749290cb43028a4a83e28a46344289a985c28819c6b284514cc2842fbd3281a4d9f27fd4ed027d2573727c12562279f070c27795cd1276dc634275dc420
  | 7, 8 => 0x342cdee934171dd833dbf57633da662c339be8303398d185338d060c3389f6ab335ce2943350a101334a7e3633422da53327d92c330961a632eb626b32e16b8932d045d132cae7bc32a1bcd53264f194326007a83241705c31ffed833177ea883159aba131389c993129ad3f311853993117236230ff3b4730dee9b130ddf491306aaa7f306330683056dbb2302ca777301b2a85301052cd3006014230010ce22fbdf3d12f98f4ff2f8af2362f7e6ae62f3c81e32f2d39052f1d2f5b2ef04e032eba05a82e8af7a22e89c73d2e7ac5422e3b996a2e1a843f2df741622df013cb2de6358a2dd75a262dcb18752dc874d12dbac35e2d93a3d72d90db782d7484b6
  | 7, 9 => 0x39fa66b039f7e21b39e16a4739c282b039ba3c4439ae44eb39a3264a394f14203926b9f8390476fc38ed825b38e1a69e38bbb164389cbe36388be5c4387c22163872edd9386585533864ee2738422411383a0cba382eb67e38120974380d7bfe37d4a1c237c3b2cc37ad2a94379a8891376ecd623747e8a73743a61d36b5383e36b521a23678c0eb366fa2723644f7dd36273865361d50e7361262443601d28435a0b6f0359f67e7359e211635974020358e7c13358833f8357bcd573579865d357193a635009d3534f524f934ecd7be34ceb8d134a771a73492603134886bc33466ebee345ddff53453b6c5344f47aa344da13934487e1234417d0f343a84db
  | 7, 10 => 0x403af74d402fc56c401a1c4f3fdba9f43fd72a663fd3ef6d3fb404613f85b1273f6aee9b3f5aa7ff3f4a127a3f4622693f2afc363f15457d3ef9b7083ef484683e444aad3e3c0ae43e3a3ac43e277fff3de291263de1cf0e3dbf16b33d96c6f03d8a3cae3d6d79af3d64e4c33d3e89f93d333acb3d1f3f593d18fbc93d0f7e103cedcf813cedc83e3ce437ac3cda06bb3cbde0b03c9f3cdf3c78ad2f3c47e00f3c407f353c24c28b3c21b4153b9f7aeb3b8aa58d3b5dab7f3b40a23f3b3af5c13b34c0e23b3477b43b33d6c03b0f10343b0c2ead3b08dcd23af6ada23ae826bb3acedf3f3a97b4d03a8e04dd3a64e63a3a4b4a043a2d6c623a2d4b643a03d4b1
  | 7, 11 => 0x476a5be9476409d74727debc471a541a471718c446f1b31146de759446cefcc046c9322546ba5dbb469461624667f2b7462601954625da8246074adf45f6b58445f5ff6d45f28fa645f126ed456daacd4563ccbf4529a6cb45179a8f44df840d44d46f78440913f443eb0c0643df582343d7832c43c469ce43be7d4943a9f848435ea1784356b115434ac032433f660a433cb82e4325dcc443110caa42ee3b3942eda89a42b779a342b451b0428dbbfe4270b5be425bc8a4424d728e424acd374240830841d387bf41b8ea3b418c5819417515864149098f413f306a40fe085a40e8120340d845e240c11d8e40b5da8040a8378340846bf6406f21e9404b3013
  | 7, 12 => 0x4db9926b4d77b7814d630dbe4d3fd3814d3fd1c54cfd734b4ce115d74cc999094c70a3534c4491e44c23a9c54bff26be4bf147df4beb8c424bacc54f4ba1260e4b9665454b6e21e64b5eae324b48acc94b2d583b4b25a97b4b226b904b1cd1974b17d9624b0c2c394b093b3e4aee73794acc75434aca3bcf4aa02b774a8b09ee4a83c1d64a77d2104a55e6434a3f5f3c4a0d197449f3d2f349e125c649e0f04f49c3e2a949bb2fc349af3f14498effba4987e828497e1ccf49787d01496fc9e4496885e54958591349469c9d493c34104939f5304931ec38492acee949148db048f0ff0048c35a8b48a6ffde48360ca14833939947d0c7f247ba59f747946ea9
  | 7, 13 => 0x55f9c36e55eeb91a559d3a725571ce4a55122fc95509167754de0ffe54c66e2d54bebf6d54b8020854b47b98546d88345467b4c6545f13eb544bdb3154324e155416d04b540a4dbd53f747b753dbb72c53d248aa53ca920853b2be72530ec13f530ba7bc52dbe80452a2b541528ce0195253af2952534f94524a17a852477438523dc21151d2062b51bb2a0f519006da514aca6d5136a9a3512495015121a07a51099cc650eca9cc50dc89c5509f541650754638505beeb35059633d50490acd502b26865014114e4fff2dd54ff820184fb50f3e4fa260824f84bcf94ef54bfc4ea43e9e4e5372144e3b68614e18a5394e1717654e0a16a24de2370b4dd3ad48
  | 7, 14 => 0x5dbe740c5d6dd96d5cde0cce5cd9f6e05c4918f65c33c1815c1f443a5c0bbbc75bea2b975bccb9a15bb301c65bb03c075b8c3f8e5b6b6fdf5b65c3955b4dbe2c5b2acd595b1f7a795aecd9575aa2af7a5a8d74075a8322685a7ee5485a6fa4e45a6beea55a62dc0f5a3ecee159fcbebe59f11cdb59e5b39359b8610d59b3a05959a3041859a0c2fc5996f4f5597bfa895936765a5931d5e85927b4ea58e6c54658bb531a58715e9458236952581a3e365810d46d5802414f578969f3576d4781576b2807575675b3574ab38e5744b4ce571462ac570c318b5707fb67568ff7f1568d8c7e567ee6cd5672b54a5659605e56427f92564030685618ad1556005707
  | 7, 15 => 0x6502386064edbd3264c5236664b8ff5c64b23f0e649ea5e0646b21fb643988c9642e54a0641ca4e76413866e63fb6a7f63e50b4763bdab156387900b6386d6c46320cbf7631fb153630aea4563020dca62d73fc862c7c6f46296399e62729ccd627050f962623a356247a48a623466376212b35a61f427ee61de9b7b61d0c2e561ca400861a45f8b61874d9061306f516108511860fe5bb260f47f6c60c0e6cc60b772cb60b58bf560afae3b60a4435560723ebc60617b6c604693fd6042b3646008d5905fd7d1ae5fbe37825fbac6fd5f7ab97d5f492eb65ef408b65ed6a3f15ec2fe405e618c165e427dc45e394d3c5dfe16575de083ce5dda43b15dd41be5
  | 7, 16 => 0x6b715d986b67104f6b3934176b1be3666b1a64bf6b0959bc6afc1fc26afac8926abcdfc56a8f01346a8281de6a4320db6a41599e6a2ef61d6a0829146a02e0d669c6754c69b0c44b69b08c9069218327691a8b436909bb466909685e6909578d689b9903688d1b5568439ee9683daa90682efe6168090f896807b6766805cfb767f1c0d367d9415267bb746067a71cda67852479675e86876733942567322581671066ce66fc748866e5ae6b669e5573669b518a6685c72066730cef666aceee66596eea665174db6627df6e6625b9e9661f8dfe6617db0a65fd862665d6d88f65b4b66965b3f9f765a7b45e65524fc665438d01653315e46532bf646518844a
  | 7, 17 => 0x761a42bc7601ef8775cf5cc17584e5a5756ef7e975576ffc7554e38675230650751532dd74c85d02746a0e0a73ea5b6e73e9ae997393454b73823427736647aa734eaa0d73437dc273275b597301de5f72b28339727f14f372301b0f72286c4f71ffefc671c52b6a71b731cf71a6de3f71a26241719e52c1718aa31d715dd49f7158096d70b531da6fb3739e6f97884f6f71e1b36eeb6aab6ee8713b6ec7a3626ec76b136ec28c856ea4ed216e97376a6e16b7eb6e01e9f06dec12c46dab2ce86d916c166d79ee906d72ad596d545ce36d35546a6d0540346cd622c66cbe1d396c9c25686c96b4706c85f2fa6c70829f6c2bf7316bba04806ba44eea6b9d976b
  | 7, 18 => 0x7f4590c97f28314b7f0df4cc7ef20d5d7ead80c27ea020fc7e4b58517e1a8a567e16e3887ddeb6337db1e1917db173387da0a7537cf889057c826dfd7c4bfba17c1abb197c140d477bf8b5337bf0d3337ba3c0797b86605a7b75c3147b665f577b5e52fc7a01223179ff769679e5550479e15a2879dfaf4e79bb6d1e79952bdb79737713797234ad797004af796fc1e1796deb39791e9fb779135b8878e9916b78d1319678b54ae278ac62e3785ddf577800865577d135d077ae3ab077abf41377abcbfa778509c27753784a77231e6a77211a3f771f39f87705d5e176f0de3376f096c376df94a676d6e32176b871ac7677af7c766c84577643e1797626fba5
  | 7, 19 => 0x89fab42489ba9fdf89b60485899788de894ebb5e893adf988934bc8a88c15bf788b1c0eb888f7ea4884d6a8e882e82c9882be4e18826fc398824c1658803a86a87b2ceb487526f628744f2368730fd46869b75948680741c863f7c59863f5b5b85fa1a2f85f2ac228542769185260ae184fb0b2c84d7d6fc84b6ffd7849e475c847e77b18450d9fa844c644984064fcd83fe99eb838f94ca836211778323a63b82e8729d82e2ff4782dd367682b803c382b3ae80827963fa823f6b2781f114c781b726b381ad224981303d8c8101e0aa80977014809286e38069eaef805c90738040d07880087aa87fee056d7fda9b807fb50b547fadfc4e7f8c014d7f4af1e4
  | 7, 20 => 0x9630ff519551aacc951cbb3294ae151694aba5ca947da14a947d9aae942a4f20941d35b8937619ce9351acbb93342c2792f99b54928df768927345059224c3ed9222139b91c9a379919f9a929196ca6a917adf6f916bb6609161e4a791592acd913e5b3c9117715e90f610e690cd968f90cac90790a7a0859022657e8ff6aa358fd08d408fa972eb8f7b76b18f7301af8f6e24048f68c10c8f6057d08f5f11de8e9fcbf58e92684e8e1426838dc4f0798d5eaaf98cfa91f68cebbc678cd766ed8cae17488cad401e8c73f3678c66e23c8c18237f8bddfc858b7531c58b6aabe78b1e27148ab84b5d8aa44b2d8aa3b04f8a80a9f98a59424c8a0d8ef78a0b34fc
  | 7, 21 => 0xa010db98a00b64c39fd738f39fb4bcba9f8732b19f76ec7a9f3584529f28b2e59edbc97b9ed6de7b9ed600aa9ed1e5489e9ab5fc9e56566f9e418da49e14ab229e1370af9debfd949de416229d33d63f9d0504429cd4fd939cccd4969cad2a7e9caba4cf9c9ee27d9c9b27e79c70cc409bf3d47a9bbf435b9b6512559b258fe99b18954a9ae5da449aabbbef9a8abc959a7a06c29a6914bc9a07492d99f128fd99ce680e9997d904998cea0d992721c299004fbf98f4ca5a98e9771598bfc76298a19efa989a6927984961e09847a6bd9823da6497d874bc97d41f8597ce2acb97a4f38797a00225977488ac972f419096bae4c8969aeb7296964552968d4d5f
  | 7, 22 => 0xab55c58dab3f45e1aae9b6bbaac711ecaabfa2cbaaacc2cbaaa935daaa8b3282aa732844aa2ce68baa2cb15ca9dd3bf7a99868aba8e78fc4a8c9d8aaa8afe02ea89eb231a893279da85b062fa827e4dca7e1ec9aa7ba35d6a7b5ef13a7a9082ba7a2a7a3a73b62e2a71e49bea6f3a76da6d56581a6bc62c7a6a209e6a65c3616a656ba0ba5fb7157a59b5408a4eede4aa4c4fe3ba4ae7b11a477d6c5a44634c2a40b50aca3f399afa3d366b3a3c65a94a3c1ab4ba3ad5187a3a56a26a390017ea3744415a3697d85a309310ca2cd8bc3a29245d0a26534afa22b6a16a1feca93a1ded325a170cb80a13f99cfa0f696e5a0c208bfa0bf578aa05ab451a0566735
  | 7, 23 => 0xbd7e86ebbd5fbcfebd386403bccd4b3fbcc8e334bcbbca35bc87e6edbc36ee53bc042ef7bb80d0edbae8aadfb9bbecabb97b0eeab94d1047b7ef6c85b7ea5dacb7aa0c84b7a1fd24b75d88c1b72e368bb71329c5b6cb1964b6c50266b666254db5f36f3fb5e82352b5b55af9b4d0d4a4b4b838bfb47be621b3b09514b35f854ab33f92c7b30843b8b27690e8b2118fd6b2109beab1aab58bb110e951b09815e0b06379a0b04d71d7b0433de6b03d009fb0231954afa1d792af80d0deaf79b774af75ff26af6b3d75af647c31af13a005aeae39fdae68ce65adf352c3adab993dad4120a3ad34d12aacb48a93ac7b9e87ac54c35bac1d3e4eabc73af8ab676f4f
  | 7, 24 => 0xcd0bb369cccaebe6ccb4b64fcc994278cc513b19cc396419cbe02962cbdbb155cbd77c2fcbaeeccfcb7281a8cb6178aacb3988b3cb099803cae6a019ca740502ca5180ccca0e29ffc9fcc544c9c359b5c996b3b6c92a9c24c871b992c72863d7c6c77138c694f8b9c682e025c63e6ab8c60d321bc5ff83fec5e5017dc5b1003bc5821593c52f7576c510d9fac4ffdd0ac4e635f6c4b9fc07c4949487c406f821c3e2d77bc3e1a744c3b4db41c3651e39c35be029c3332a36c30e22efc2dde247c285e459c2363c82c2009875c1f9d8fcc1dbd993c19d30e4c031db64bf6247b9befa2055bef4bb49bec33186be51e5eebe4be64fbdf49afebde1cfb5bd82ee2a
  | 7, 25 => 0xe76202ffe606f433e5cc13a1e56d3923e4f751b8e4f0a946e4e88dfde3ecbae8e2aad18ce298b8f8e24d2a46e1760161e1283faae1151f08e0d9cf49dfb2a488df9dc7dcdf87b76edf33ac1cdee6275bdede789bdec49712dd0995b1db29872fdb23cb92da650bedda4ab022da411fa3da329af0d9680625d937fb5cd8811cb7d87f9952d7799b21d735f252d6382f23d615987fd6073c10d5f29d0bd5dffed2d5735722d568ff65d53d3f66d52b0a13d4b15a72d4001a12d3ab69cdd3039b18d2e9db6bd2b422bed26d319fd2290b9fd1293c1cd1145570d07c82adcfe37fabcfdba189cfaaeb5dcf33b5c0cf010deccef767cfce80e88ace67a484cd853652
  | 7, 26 => 0xff88f5fdff0db492fe69481bfb379514fafc002efab495f5f908e400f8b72109f6875a6cf6535463f4f9312af462ddedf33b5fd0f33384e5f2854adff265e2cdf2000644f171c893f10d01a6f0132cb6eeb4af79ed7abd14ed37c018ecbba0bdecb47af8eb2980d5eb1cf74c
  | 8, 0 => 0x1528ba3c1415063f14121a0c13b5da6d136d10ac131bfefa1317dd2b129997eb12798028124e263511ed84b711eb7ccf11d748061187183a11761aa81142fa411134c93410d1aa960ff073950fd4c3f50fc22fb60f5c5cfb0f3badb20edd17080ea68d810e8414b20e783ebe0df078900db675560d9cbe430cf91d9f0cea20e10cc7aa850cb3009d0c867e660c2cfbb60c22507d0bb2ffb10b989d440b41c7720acf09dd0ab0afbb0a9628be0a172c4908786758075140fd06ecbabd06b07a030663442505c61dd60590310f05169eb0040745c6033b05b5033a727c02e9d44b02d5abde0291d00a024a740d023c952e0188fb4b00dd496a0064991500103def
  | 8, 1 => 0x26e36c2426bb2fef26aa53c3265363bb264ea12126488ebe26396ad4262d41fb26093241258a6ea424cb7b29246554a623a7fde62325e28c231857ea23038dd422daf26b22d85c9a22543c1c21e9d24d2179389d204aaf2d2046aaad203e530f203cd04e2015ae6f1fd3d3851f9bef851f608b651f3d31db1ee4e3db1ebb13731eb3facb1e8eec381e7359ed1d989e101d73f5661c53b96d1bde45011b70b1901b52f3321b1036f41a5d39541a45ab1d1a4058c31a2bfa9c1a0ece7019f08aad19e3604919deb3e219b1d4481979f417196672e1192a0dd61900f42918787ffd181aa941175a929b1729918f16e8db181662ea0a1606144c15f86a801561a43a
  | 8, 2 => 0x3afd7b253a8b9b213a8b1a653a47663439de879e3950034038ad846e387c2216378f31e83724f45b36f4981f36c744ae36b6da923678c0eb366fa272363c57f435d89aaa359f67e7357bcd573518dab134ceb8d134746a9f34744a7f342cdee933d93c6b33ab0d0833193e9a32e7627a3264f194319b3e42317141fd315024ba3122199e30f26f093055c0a62fa1c82a2eedfa852edbd6b52ea0b9112e9e70832e46479b2d770a592d6df75a2d014b912cf085992cb7e2692ca821632c9946a22ba0a43a2ba064522b0f56702a7c85282a6cf0712a6bdfc02a5e00e12a5175e42964176b292df8a1291abe562889888f2882e2b22775450f275958f227277073
  | 8, 3 => 0x4e0e9fc94e00c0ea4de27c5e4dd111674dc27b5b4d2b306b4cd8ba054ca60af44c173de94bff26be4bf147df4bb13b214b62f61f4afc5e1e4aee73794a0d1974499cfa0a499b08ca49148db048b0ac9d484e6acf47f69d26475141bb46e1bded46e149a246ba5dbb465e79d545c07cca457c5ed145179a8f43cee64d43b9f0a343b42571433f660a4309ffd842b779a342815d8a4223bdb941d9fb7841d622d341a4b5d6413ca69640db2d8b40bb2834405c8f3d3ffca0873f49363a3ee6de3d3e277fff3dff89d03df1aaf13dc32c533d8620523d6d0b963d18fbc93d0124c93cd7d7c23c9f3cdf3c9dc2fe3c9d75a23c8fe41f3bf3e2703b76a7473b3c318a
  | 8, 4 => 0x69d0a4b069b2eaed68b561d0688d1b556709aa6164ffcc4e64cf00c563669d95633635116329b29363275f1562b43c1761f427ee6129ea2960d158045f5d13a95f492eb65f2a63495ec2fe405ebcebc25e06e6065dc82fa15d93d62e5d7bf2db5d6275f45d3a46645d2e415c5cde0cce5c0095e65b4388f85af03eb05a437adf59f223e55992adb05943cbfb57c3519856dbe56f56abec62564030685592bd7c54b47b9853b7a8b553b3d16b5314eaf652e996fb52943af5528ca242523dc211520a3fab51efbb6051e81d5151bb2a0f516924ff51007c3a50c9577f50c4b4ed50a706e8505beeb35059633d5038abd64f8c57c24e79bd534e1db72a4e171765
  | 8, 5 => 0x8ab84b5d8a8bfac78a7994f88a0d10dd89f226db8968a0cb88edfe0d886bb2a5881ad29987ca80ca872610b8869b7594862851b985e99b548549f6d285210b0383d9bb2c83c5bc5283233d80830766bf804281917fe35f827f5f0e0b7f4590c97f27d8097e1a8a567dfd47397dd5c4a57db1e1917dad4e397d776c2f7d33ff317cea112d7b2b17a17aa157477a85129f79a4d76c798a90b2791d9b41785a178976f0de3376eecc3f76db0b2e74f2245d72e03d9b727daf3d72739f547263b2ee71fb25a26e834bca6e8018a76e34ebde6d45b13a6d2657c06cd622c66c4b6e046bc490ee6b7c11ab6b58c0516b1be3666af785736a5eea176a510b386a2a46cf
  | 8, 6 => 0xc21dcfbbc1c6e06ec110cb7dbeb2f988bcc8e334bcb2dff7bc5e25f5bbec3344bad4da24baa8a17cba477786b9782853b84d21e0b6edc245b644e080b4d0d4a4b47be621b32b1ae2b22e7c90b1b17014b12375bdb0ec7e1fb04d71d7afebec7daf95e2ffaf01b67aaec64c0eadab993dabe5308aabbe6e52ab681b8eaaa935daaa38618da9cb11c2a98c5b5da8d69abba62fa927a5103ec2a35f8a0fa0b267039ffd08839f9262399e3c45669de9f1209d42bc1d9bfcd792996c23f4992721c298fcecee985a34f7981b7e929710a45896a4b77d9603a49895a996be956125c692b08ece90061e318f6680978e2374cd8ce77a638c1a6ee88bbc73f08b7e195e
  | 8, 7 => 0xfc7cb7dbfc3e0176fabc44b5fab495f5f8b72109f5a8ee32f2854adff1c31697f1c1f496f171c893f03d9387ed71b5aeeb3fcd10e8f19d4fe8b54ab1e2f7dbbfe2f02cffe1283faadfa5c541df71e0b2dede789bdec49712dd0995b1d958a3e4d87f9952d69e993fd697c1d4d64007d5d3b34341d30f653ad2da325bd27a66b2d0ab600ed0317033c7ad77bcc707ac1ec61b5c10c5e58a67c5dca5abc52f7576c4eae2e7c4605fcec30bd3fa
  | 9, 0 => 0xbad4da248a7994f87cea112d4f8c57c22eedfa851e7359ed1729918f1561a43a1142fa41
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0x10d10600000000c1104000000010d106000004148520500000000000030000000006101000000000210000000000061000000000000008000004350c20000151324c8301000000000e100000000000000a000004350c200000000000000000151324c8301000000000e100000000010d1060000000000008000000000210000000544c820300151324c830200000514c82000000000000004000000010d1060000000000000000000000210400000000000100000052440200000004350c200000000000e1010000000000001
  | 5, 1 => 0x10000000000210100000000c911000000000c911000000000000110000000000010
  | 6, 0 => 0x2000000000a1000000053081200000000000a1020000000000002000000480e2010000000002104000000000e103000000380a20100000304c02020000000012103000000000a104000000000000c000000000a103000000380a2020000042485204000000280220000000000000020000000002104000000480a201000000000000b00000000000010000002806202000000000210000000540c52000000000000010000000000a1000000000000004000004350c200000000000000200000000000000000001802200
  | 6, 1 => 0x2802202000000000a1040000000002102000000480e200000000000210400000000851000000000012103000002048020100000038062010000000000000000000010d1000000000012104000000000000100000000061050000053085201000000000a104000000380a201000000001210000000038062020000000002102000005308120000000018022010000000002100000000001210200000000000020000000000007000000000e102000000000a10000000000000040000053081200000000000000a0000000006103
  | 6, 2 => 0x324c8201000000280220100000000061000000000002100000000000a103000004350c2000000000006104000000001210000000000000000000053081200000000000e10100151324c83010000004806201000000000e10200000000021030000000012103000000480a200000000000000a000000000e100000000001210500000324c82020000000000000000000000a101000000000210000000000000050000000006103000000000e10000000000000110000000000000000000000210000000000061030000052440200
  | 6, 3 => 0x21020000000012105000000000e1010000000002104000000000e101000005308120000000000000010000000002105000000000e103000000480220000000000021030000000000002000000000e10300000000000000000000006104000000000610300000028022000000000000003000004350c200000000000e104000000480e202000000480220000000304c0200000000480e2000000000000003000000010c1000000003802200000000000a103000000380a2000000000085105000000010d1060000051480200
  | 6, 4 => 0x300000000000010000000000001000000000a10200000038022000000000000001000000000000100000304c0200000004350c2000000053101202000000000e105000000480220200000304c020200000038062000000000002100000000000000b0000000000005000000380620000000000851040000000012101000000000e101000000000e103000004350c20000000544c4201000000000e10400000000021020000000000000000000000001000000000021010000000002105000000480e2010000000002101
  | 6, 5 => 0xa10100000038022000000003802201000000000000f000000000210500000000c11040000000006105000000000000400000000121040000000006102000002048020200000204802010000000000004000000000e103000000000210000000000000000000000000008000000010d106000000380220100000048062020000052504200000000000000400000038062010000000012105000000000e104000000000000500000000000000000004802200000000000e1010000004802201000000010d1060000000006102
  | 6, 6 => 0x21050000000012100000000000000000000544c8201000000000610000000000021050000053440201000000000610100000000021040000000000007000000380220200000000061000000000000003000000000a1040000000000010000000000210200000000021040000000002101000000000000600000000021000000000000003000000180220000151324c83020000000000002000000000a100000000000e101000000008510500000000000000000002806200000000000a102000001044020100000304c0200
  | 6, 7 => 0x100000000002104000000000000e000000000000100000544402010000000006104000000010d10600000000000100000000012100000000000a102000000280620000000504c8200000000000e102000000000e103000000000210200000000021000000000002100000000000001000000000021000000000000005000000000610200000000021040000000002101000000000a1020000000000003000000000a1040000000000010000000180220000000540c520000000000000000000001802202000000000e104
  | 6, 8 => 0x6102000000000000d00000028062010000000000006000000001210000151324c83020000052440201000000000e1030000000000006000000000000400000000061020000000000005000000000000100000000000020000000002102000000000a103000004350c2000000000012100000000480a2000000000000002000000000610000000000121010000000000011000000000a100000000480a2000000052504200000000000000a00000028022020000000012100000002148420100000000000110000002802201
  | 6, 9 => 0x2102000000000210100000531012020000000000001000000000210500000000c110400000000061010000053041201000000000000600000038062020000000002102000000480a200000000480220100151324c83010000000000000000000000e10000000000021000000004806200000004350c20000000544402010000000000001000000380a20000151324c83010000002806200000000000210200000000c11040000000000004000000480620200000000000050000000006103000000000e1010000000002105
  | 6, 10 => 0x204802010000000000007000000010d10600000000c911000000000000020000000000003000000000a1040000000000002000000000a10500000000121000000004806201000000480620000000540412000000052440201000000180220200000000121020000000085105000000480e20000000304c0202000000000210400000000000050000000000010000000280220100000000000080000000002105000005304120100000000061000000000002103000000000e104000000000210300000000000100000000000001
  | 6, 11 => 0x2102000000008510300000304c0200000000480e201000000380220000000048062000000052101201000000280620000000018022010000000012102000004350c200000000000210000000000121030000000002102000005310120200000000000020000053041201000000000210000000520c52010000000006101000000000210200000000000040000000105105000004350c200000000000a100000000000000d00000000061030000000000000000000000a10400000028022000000053041202000000010d107
  | 6, 12 => 0x544c82010000000000001000000000000300000000000030000000006101000005244020000000000000030000000000006000000010d106000000480220100000000021010000000012102000000000e104000000010d106000000000000c000000000e1010000000002101000000000000300000000c11040000000006102000000380220100000000000030000000000008000000010c10000000000000080000000002104000000010d107000000000e10200000544c8201000000000e104000000000000600000000c1104
  | 6, 13 => 0x800000000000080000000012104000004350c20000000544c8201000000480e2000000000000006000000000a104
  | 7, 0 => 0x21000000000002101000000000000200000048022020000000101101000000480a201000000000e1000000000000000000000000000d0000000000008000000000210000000000851010000001802202000000000610400000000c1100000000000e101000000000000500000000021040000000085101000000000000900000000000000000000000004000000000001100000000000000000000002101000000000e10100000000061040000000109104000000000000300000000000060000000012102
  | 7, 1 => 0x480220100000000121000000000000004000000000000200000000811000000000006101000000000e10100000000000050000000000005000000010c10000000000000100000000000006000000008510100000000121030000002802200000000000a1010000003802202000000000610000000000021040000000000006000000010d1000000000000004000000000a101000000000a100000000000e10000000304c020000000000000050000000000000000000000a104000000000210100000000000000000000000007
  | 7, 2 => 0x3806200000000000a100000000000001100000000000110000000012105000000000e101000000000a103000000000610100000000c01020000000000003000000000000b00000000c51010000004802200000000000000600000000000070000000000003000000000000700000018022010000000000003000000000e100000000000610400000000061010000000101100000000000e1050000000000004000000000210100000000000060000000002105000000000a10300000000021030000000080102000000000000e
  | 7, 3 => 0xf0000000000006000000000000300000000000030000001802201000000000e1010000000012102000000000000a00000000000010000000002100000000000001100000000121050000000105100000000000a1020000000000005000000000e10000000000811000000000002101000000000a10100000000000020000000000000000000000000500000000c8102000000000000900000000021040000000000004000000010510100000000061010000004802200000000000a10500000000c0100
  | 7, 4 => 0x38062010000000012101000000000e101000000000a1020000000000007000000000e10000000000000030000000000005000000000210300000324c82020000000000007000000000000700000000061000000001802200000000000a1020000000000006000000000000300000000c5101000000000000100000000000030000000006101000000000000100000000061030000000000000000000001210100000544c820200000000c91020000000000010000000000e105000000010910100000000121000000000002103
  | 7, 5 => 0xc110100000000000020000000000002000000000000100000000121000000000105101000000010d102000000480a202000000000210400000000000030000000000003000000000e1000000000000005000000000a10200000000121040000000002100000000000a101000000000e103000000000e10300000000000080000000085102000000000000b000000000a101000000000000700000000000050000000081100000000000a10500000000000030000000000005000000000210300000000c9101000000000a102
  | 7, 6 => 0x12104000000000a103000000000000500000000c11000000000000007000000000000500000000021010000000012102000000000a104000000004110300000000021050000000000001000000000e10500000000061000000001802200000000000a105000000000000800000000c11040000000000007000000000000a000000000000400000000000100000000000000000000000a101000000000000900000000021010000000000001000000000a10400000000121000000000002100000000000a1030000000000000
  | 7, 7 => 0x400000000c1102000000010d101000000000a100000000280220000000000000060000000105100000000000000500000544c820100000000c0101000000000000300000000c91010000000000003000000000a101000000010c100000000000e10500000304c020000000000121010000000002100000000000000700000028022000000000002100000000000210100000000000030000000041100000000000000700000000000010000000000004000000000e101000000000610200000000000100000000006101
  | 7, 8 => 0x1210000000048022000000000000001000000000e100000000000a10000000000811000000000000001000000000e10000000000061030000000002100000000001210200000000021000000004802201000000000e10100000000000110000000002100000000008510500000000061030000000041101000000000000100000000000030000000000005000000380a200000000480a200000000000e10000000000c91000000003802200000000000e1000000004802200000000000a10200000000000050000000000005
  | 7, 9 => 0x7000000000e103000000000000e00000000021020000000000010000000000a101000000000210000000000021010000004806202000000000e103000000000e102000000000000400000000c11000000000000003000000000000600000544c82010000000000006000000000000a00000000c0101000000010d100000000000000400000000000110000000000003000000000a10300000000c9102000000000a103000000000000f00000000000020000000002101000000180220000000000811020000003802202
  | 7, 10 => 0x4000000000e100000000000000b0000000000001000000008110000000000021020000000002102000000001210300000000c11020000000000003000000000a10000000000061000000000000005000000008110000000000000030000000000004000000000210200000000000060000000012105000000000a10200000304c02000000000000004000000000a10100000000000000000000105102000000000a103000000000000a000000010d1000000000000003000000000000a0000000105100
  | 7, 11 => 0xe1010000000000001000000000e10500000000061020000000000003000000000a1010000000000001000000000a101000000000000300000000000030000000006100000000000a10200000000000000000000002102000000000210500000000c5100000000000000500000000c91020000000000001000000000000e00000028022010000000109104000000000e103000000000000100000000021000000000000004000000000a1040000000000008000000000a105000000004110200000000000070000000000001
  | 7, 12 => 0x610400000000000050000000000004000000000000100000000000000000000000002000000000000200000000021050000000000000000000000e1020000000000007000000000a101000000000000b00000000411000000000000001000000000e101000000000e10100000000c11000000000000007000000000000a00000000000050000000002104000000000a10000000000851000000000000006000000000610500000000000070000000105101000000000000300000000c41010000000000004000000000e105
  | 7, 13 => 0x61010000000000007000000000e10000000000000030000000000008000000000000500000000000050000000000000000000000210000000000c01010000000105101000000000000b00000028062000000000000001000000000000400000000c110000000000c81010000002806202000000000a1010000000002100000000000210500000000000040000000006103000000000210000000000000020000000000006000000010510500000000000010000000000007000000000000400000000000020000000000004
  | 7, 14 => 0x121010000000000004000000000e10500000000021030000000085101000000004110200000000c110100000000c810200000048062000000000000006000000000000200000000021010000000000011000000380a20200000000c51020000000000000000000000000700000000c51020000000002101000000000a101000000000000500000000000040000004806200000000000000c00000000000020000000105102000000000e10300000000000010000000000009000000000001000000000000020000000000003
  | 7, 15 => 0x2102000000000610300000000000050000000085105000000000e1020000000000001000000000e10000000000061010000000002105000000010d100000000000e10100000000000010000000000005000000000000000000000061000000002802202000000010d100000000000000600000000000030000000012102000000001210000000000c1102000000000000400000000000020000000002104000000000a101000000000000b000000010c1000000000002102000000000a10400000028062010000000006102
  | 7, 16 => 0x600000000000040000000000008000000000a101000000000e103000000001210300000000000040000000000004000000000000b00000001051020000000000000000004050020000000000000030000000002101000000000610000000000021000000000000004000000001210100000000c5100000000000000800000000061030000000000002000000000a1020000000012102000000000210100000000000060000000012102000000000000a0000000002104000000000a1040000000000003000000000a101
  | 7, 17 => 0x12100000000000a105000000000e10500000204802020000000000001000000008510000000000061020000040500200000000000a100000000000a104000000000001000000000000060000000000004000000000e105000000000000d0000000006101000000000210200000000021000000000012105000000000e101000000000000400000000000090000000002101000000000000500000000000000000000000001000000000000a000000000e1030000000000004000000000a10500000000061040000000000008
  | 7, 18 => 0x380a201000000000000000000000000010000000012102000000000000b000000000000b000000000000100000000000040000000000006000000000610100000000000020000000002100000000000a101000000000a10400000000000040000001802202000000000e100000000000000e000000000610000000000c01020000000000003000000000000a00000000000060000000000006000000000a105000000000e102000000000210400000000000030000000000003000000000a10100000000000040000000000007
  | 7, 19 => 0x610300000000000070000000000004000000000a1000000000000004000000010d1010000000000006000000000000000000000000080000000002104000000000e101000000000a100000000001210300000038022000000000000007000000000e10200000000021030000000000000000000000000400000000000050000000006100000000000e1000000000000003000000010910100000000c110200000000000050000000000000000000000a10400000000c11000000000000005000000000e105000000000a101
  | 7, 20 => 0x600000000000100000000081100000000000000e000000000e104000000001210000000000000010000000000006000000000e1010000000000004000000000a102000000000001100000000021000000000012102000000000610100000000000050000000000003000000008510000000324c8202000000000000000000000000060000000000001000000000a10200000000c910000000000c010100000000000050000000006105000000000a1040000000000004000000000000a000000000000a000000000a100
  | 7, 21 => 0x121010000000006102000000000a102000000000e10200000000000020000000012102000000000a101000000000e1000000000002100000000000e100000000000e10100000000121030000000002103000000000000300000000000030000000000000000000480220100000000c9101000000000210000000000000000000000000011000000008510100000000000040000000000004000000004110200000000021000000000080101000000000a1020000000000005000000000e100000000000e1010000000000011
  | 7, 22 => 0x1000000000e105000000000000200000000c0101000000380a2010000000006100000000000000b00000000851000000000000005000000000000000000000c5100000000000e102000000000000a0000000000008000000000e10000000000c11020000000012105000000000000000000000021030000000101100000000000000a000000000a10200000000000060000000006101000000000210100000000c11040000000000001000000000e1000000000000004000000000210500000000061020000000000001
  | 7, 23 => 0x30000000000011000000000a1040000003806202000000000a1000000000002102000000480620200000000121010000000000000000000000000100000000000060000000002102000000000e10000000000000110000000006101000000000a10300000000000000000000002101000000010910000000000000030000000000002000000000e104000000000000400000000000020000000101101000000000a10300000000000010000000085100000000000a1000000000000007000000000e103000000000a102
  | 7, 24 => 0x2101000000380a201000000000000200000000c5101000000000e1000000000012100000000000210200000000000050000000002102000000480e202000000010d1000000000000006000000000210100000000000070000000002105000000000000600000000000030000000000004000000010c1000000000081101000000001210100000000000020000000012100000000000a100000000000000300000324c8201000000000000a000000000e1010000000000000000000000001100000000411000000000006105
  | 7, 25 => 0x6104000000000210300000000000060000000006100000000000a100000000000610000000000061010000000000007000000000a10300000000000070000000000000000000000e1020000000012100000000000000700000000c91020000000105101000000000a101000000000000000000001091010000000006103000000010110200000000021020000000041100000000000e104000000000610400000000021010000000000003000000000000000000000c910100000000c910200000000c11010000000081100
  | 7, 26 => 0x2102000000000e1030000000000000000000001210000000000811010000000006100000000000000500000544c8201000000000e1020000000000002000000000e105000000000a100000000000a10300000000000020000000105100000000480a20100000000000040000000000011000000000a1000000000006100000000000a101000000000a104000000010d1010000000006103000000000000c000000480a200000000000000b000000000e100000000000000200000000121010000000006104000000000e100
  | 7, 27 => 0x10000000000004000000480a200000000000a1010000000000000000000008510400000000121010000000000003000000000000300000000000030000000002102000000000000b000000480a2010000000002103000000000a105000000000210000000000c01000000000000007000000000610500000000811010000000000006000000000e1010000000002100000000000e100000000000000a000000001210000000038062020000000101102000000000a102000000000210000000000000020000040500200
  | 7, 28 => 0xa100000000000e101000000000e100000000000e10100000000021000000000000009000000000000000000000c1101000000000000400000000c1102000000010910400000000000040000002806201000000000001000000000121040000000002103000000000e1050000000002102000000480e20100000000021010000000000010000000000000500000000061010000000101100000000000000a0000000002104000000000000b00000001001000000000000005000000000210100000001091020000000000005
  | 7, 29 => 0xb0000000002101000000000a1000000000000001000000000e10300000000021010000000000007000000000e103000000380620100000000021020000000012101000000008110100000000121020000000012100000000000001000000000000090000000012100000000004110000000000000040000000000006000000010d1000000002806200000000480a20200000000000030000000105101000000010d100000000000000700000000061010000000000006000000000000500000000000070000000000004
  | 7, 30 => 0xc1100000000000000300000000000050000000000007000000000a100000000000000f000000010510100000000c9102000000000e10500000000c9101000000001210200000000000010000000109101000000000000500000000411010000000000004000000380620100000000000050000000000005000000001210000000000c1105000000000a102000000280620000000001091010000000000004000000010d10200000000000060000000002105000000000a100000000000a10000000000000100000000012102
  | 7, 31 => 0x10000000000003000000000a1020000000085103000000000000000000000121030000000000001000000000000200000000000070000000006100000000000610100000000000030000000012100000000000e10100000000061010000000000006000000000a100000000000610400000000000000000000000011000000180220200000000021010000000000004000000000210300000204802020000000000002000000000e1040000000000006000000000000500000000c010200000000121020000004806200
  | 7, 32 => 0x121000000000000002000000010910300000000000000000000000001000000008510000000000000020000000000007000000480e20000000000000050000000081100000000000a10100000000121000000000000006000000000a101000000000000000000000000040000000000004000000000000200000038062020000000000004000000480a2000000000012100000000000e10000000000c11040000003802202000000000000300000000000030000000000001000000000610100000000021010000000105105
  | 7, 33 => 0x81101000000000610100000000021000000000000003000000000e102000000000a10100000000021040000000000000000000000610400000000c010200000000061020000004806200000000000610100000324c820100000000000030000000002101000000000000700000001011020000000002100000000000e101000000480620000000000000020000000000006000000000210000000028022010000000100100000000001210000000000061020000000006101000000000a100000000000a101000000480e201
  | 7, 34 => 0x610500000000000040000000000007000000000e1050000000000009000000380a20100000000000100000020480201000000000001100000000000080000000000010000004350c200000000000a103000000480a20200000001011000000000012102000000000e1020000000000005000000000000c000000010c100000000000a1010000000081100000000000e100000000000000000000000000060000000012104000000000a10300000001011020000000012101000000001210200000000000050000000101101
  | 7, 35 => 0xb000000001210500000000000010000000105102000000000000200000000121030000000002101000000000e105000000000000d0000000000003000000000a10000000000000000000000006102000000000000600000000021040000000012104000000000000300000038022010000000000008000000000000f00000000411000000000000005000000000e10000000038022000000000002100000000000000b0000000081101000000000000000000000000030000000000003000000000e1000000000006100
  | 7, 36 => 0x801010000003802200000000000000b00000028062020000000012105000004350c2000000000000004000000000a10400000000000030000000012105000000000e101000000000000b000000008510100000000811010000020480201000000000e1020000000002101000000000210200000000000030000000000008000000000000400000000000050000000101100000000000210000000000c5100000000000000a000000001210000000028062000000002802202000000000a10000000000000040000000000003
  | 7, 37 => 0x85100000000000000700000000121000000000000005000000000e1020000000000007000000004110200000000c510000000000000060000000000008000000000e10000000000000020000000012102000000001210000000000000040000000006101000000000a104000000000210000000000000100000000081101000000000000300000000061000000000000006000000000610100000000000000000000000001000000000000400000000c0102000000000e101000000008510400000000811020000004806200
  | 7, 38 => 0xc000000000a10000000000000030000000000005000000380220100000000121040000000101102000000000000800000000000000000000012103000000001210400000000c1104000000000a10400000000811010000000000004000000000000f000000000000c0000000000004000000000610200000000000070000000000003000000000a103000000000e10100000000000030000000000002000000000000500000000c110500000000000040000000000003000000010c1000000002806201000000000e104
  | 7, 39 => 0x280220200000000121010000000000004000000010d106000000000e103000004350520100000000000010000000000004000000008510000000000021040000000012103000000000a10100000000000000000000105100000000000210100000000000000000000002102000000000000600000000851050000000000003000000000210000000000000030000000000003000000000000a00000000000010000000000004000000000a105000000000000700000000000020000000000011000000000000600000000c8101
  | 7, 40 => 0x3000000001210300000000021010000000000004000000008110200000000c11050000000000006000000000210400000000c1102000000480a20200000000021020000000000007000000000e102000000004010100000000411010000004802201000000000e100000000000000300000000c1101000000000610400000000c51020000000000003000000000a1030000000000003000000480e200000000010c100000000000000a0000000101102000000000000200000000c810200000000c110000000304c0201
  | 7, 41 => 0x61040000000006102000000000000e0000000002105000000000a10000000000000000000000000003000000001210100000000000050000000000011000000000e1010000000000004000000008510000000000c1101000000000e104000000000e1010000000000005000000000000500000000000060000000000010000000000000000000001011010000000000001000000000000400000000021040000000002101000000480220100000000061000000000012102000000001210000000304c02020000000000000
  | 7, 42 => 0xc010000000000000030000000000001000000000000800000038062000000000006103000000000a1030000000000000000000000e10000000000c1100000000008110100000000c0100000000000000000000000000030000000000001000000000610500000000000040000000000001000000000e10500000000000110000000006102000000000a10500000000121000000000006100000000000000400000000021010000000006100000000000e10100000000000040000000002100000000010d1020000000000002
  | 7, 43 => 0xa1020000000012101000000000e10500000544c82010000000000007000000000000a0000000000004000000000a1020000000000003000000000000200000000021040000000002100000000000000700000000c01010000000000003000000000000000000000000060000000012105000000000000300000000000050000000000001000000000a1010000000000006000000000000100000000061030000000000004000000001210000000000000020000000000001000000000000b0000000000002000000000e102
  | 7, 44 => 0x6000000000e103000000010c10000000000121010000000000011000000000210400000000000050000000000003000000480a200000000000000100000544c820100000000000040000000000002000000004110100000304c0202000000001210000000000021010000000012105000000010d1000000000041101000000000a10000000000021000000020480202000000000210100000000000040000000006101000000001210300000000000050000002802200000000000a10300000001001000000000101102
  | 7, 45 => 0x61050000000000001000000000a1010000000000004000000010d1000000000000003000000000210000000028022020000000012100000000000000d000000000610200000000000000000000105102000000004110100000000000110000000000003000000000a102000000000e1020000000000003000000000000200000000000000000000000009000000010110200000000c11020000000000006000004350c20000000000811000000000012104000000000000500000000021010000000000004000000000e102
  | 7, 46 => 0x12100000000001210500000000000050000000000007000000000a10200000304c020200000000000040000000105101000000000e101000000000000000000000c010000000000000020000000002101000000000000c000000000e1050000000012104000000000e1050000000000007000000000210200000000811000000000000010000000000e102000000000e100000000000e1000000000000007000000000000a00000000c1101000000000e10300000000000040000000100100000000008510000000000c8101
  | 7, 47 => 0x380a201000000010c1000000000000003000000000000400000000c810100000000000020000000000007000000000000600000000021010000000012103000000000a1020000000002100000000000e100000000000a1020000003806201000000000000400000000000050000000000001000000000000200000000000080000000085100000000000000300000000411020000000000002000000000a10300000000c5100000000000000e0000000000003000000000210000000000c01000000000000004000000000a100
  | 7, 48 => 0x2000000000a100000000000e1000000000101104000000000001000000000851000000000000000000000000a103000000001210300000001001000000000002101000000480e200000000000000300000000c110500000000411010000000000003000000010c10000000000c81010000000000000000000000000c0000000000003000000380a2010000000000011000000000210500000000021000000000000004000000000e10000000000121010000000002100000000000a1030000000000001000000010d100
  | 7, 49 => 0xb000000000000f00000000000000000000000005000000000e104000000000a10200000000061010000000000004000000480e2000000000000011000000000210400000000000040000000000006000000000e1020000000006100000000000a100000000000000200000000121050000000000004000000000a1010000000041101000000000000100000000000040000000012102000000000a101000000000000000000000021000000000000007000000000e105000000000a1010000000006102000000000e100
  | 7, 50 => 0x801010000000000003000000000000600000000000010000000081102000000480a201000000000a1010000000000005000004350c2000000000000000000000010510100000000801010000000109100000000000e10200000324c82010000000002100000000000e1040000000006101000000004110200000000121010000000000004000000000a10000000000c11000000000012104000000010d100000000000a101000000000e10100000000021050000000006103000000001210000000000000110000000000005
  | 7, 51 => 0x12100000000000000300000000000040000004806202000000000000300000000021040000000000003000000000a10300000000021000000000002100000000000a1020000002802202000000000210100000000021010000000012100000000000000600000000000020000000000002000000000210400000000000030000000002100000000000a1020000000002101000000480e200000000000000700000000c110200000000021010000000085100000000000000d000000000610200000000000020000000000003
  | 7, 52 => 0x600000000021000000000000000000000000000600000000121030000000002100000000000e10000000000021000000000000000000000000610100000000c51020000000081102000000010d10000000000000000000000000000000000000000200000028022010000000000003000000000000800000000851000000004806201000000000000a000004350c2000000000000008000000000000000000000000070000000000011
  | 8, 0 => 0x20000000109101000000000610000000000c9101000000000a102000000000000300000000000010000000006100000000000000300000000c81010000000000000000000000000c00000000411000000000000000000000000000700000000411010000000000004000000000000200000000000060000000000001000000000000a000000000000400000000000050000000000005000000010c1000000000041101000000000a102000000000e10000000000000000000000000006000000000000100000000c9102
  | 8, 1 => 0xc000000000000300000000000070000000000003000000000000400000000021000000000000003000000000000000000000c91000000000000007000000000000e0000000041102000000000210000000000000030000000000005000000000000100000000c91000000000109101000000000000200000000000040000000041100000000010110000000000c0101000000000000b00000000000060000000000001000000000000f00000000000000000000000005000000000000100000000801010000000000005
  | 8, 2 => 0x7000000000e10000000000000000000000101101000000000000400000000000010000000000007000000008510000000000021020000000000004000000000000400000000c5100000000000000500000000851000000000101100000000000000500000000000000000000000003000000000a10100000001011010000000000002000000000000400000000c51000000000000004000000000000a0000000000002000000000000000000001091020000000000004000000000000500000000000030000000000001
  | 8, 3 => 0x10c10000000000000030000000000000000000000000500000000000010000000000002000000000a10100000000000000000000000002000000000000200000001051000000000105101000000000000a0000000000004000000000e10200000000c5101000000000a1020000000000002000000000000000000000c1101000000010910200000000000020000000105101000000000000400000000411000000000000004000000000000300000000000000000000000000000000000000100000000c51010000000000000
  | 8, 4 => 0x3000000010c1000000000081101000000008010200000000000000000000100100000000000e1020000000000007000000000e101000000000000000000000c9102000000000000400000000000000000000012102000000000000700000000c01000000000085101000000000000400000001011020000000000002000000000a1010000000109102000000000000000000000121000000000000001000000000000a0000000000002000000000e1010000000000003000000000000100000000000020000000041100
  | 8, 5 => 0xc9101000000008110200000000000010000000012101000000000000000000000000030000000000001000000000e102000000000000100000000000000000000000006000000000000100000000c01010000000000000000000000000100000000c1100000000000000000000000061020000000000004000000000000500000000000030000000081101000000008010100000000121000000000000005000000000000300000000000000000000100100000000000e1010000000012100000000000000a000000000a100
  | 8, 6 => 0x50000000000004000000000000200000000000000000000109100000000000e102000000000000700000000021010000000000001000000010910000000000000020000000105100000000000610000000000c810200000000411020000000006101000000000000000000000000020000000000000000000000000100000000c110000000000411010000000000004000000000000200000001011000000000012100000000000000200000000000010000000105100000000000000000000000121000000000000004
  | 8, 7 => 0x8110200000000c11000000000000000000000000000100000000000010000000000000000000000000100000000851010000000006100000000000e10200000000121000000000080101000000000210000000001091020000000000000000000000e10000000000000050000000002101000000000a1000000000002102000000000000300000000000040000000000003000000000000000000000000060000000000001000000000000000000000000030000000002101000000000000500000000000010000000000000
  | 8, 8 => 0xc81010000000101102000000000000200000001051020000000002101000000000000400000000000030000000085100000000000000400000000000020000000100100000000000000500000000c5100000000000210200000000c91000000000000001000000000a1010000000000000000000000000500000000000050000000000006000000008510100000000c010000000000000020000000000002000000000a1020000000000002000000000000300000000000070000000000002
  | 8, 9 => 0x6102000000000000100000000000040000000000002000000000000500000000000070000000000001000000000000300000000000000000000002100000000000e10200000000000040000000002100000000010d1000000000000002000000000a102000000010c100000000000000400000000000000000000000005000000000a1010000000000001000000000000100000000c81010000000000007000000000000200000000000010000000000007000000000000600000000851020000000000000
  | 8, 10 => 0x2000000000000200000000000020000000000000000000000000a0000000000007000000000000300000001091020000000000003000000010c1000000000000003000000000000b00000000000070000000012101000000000000000000000000030000000000006000000000a101000000010d102000000010910000000000000040000000000000000000000e100000000000000300000000000060000000085100000000010d1000000000000005000000010d102000000000000200000000c51000000000000000
  | 8, 11 => 0x400000000000020000000000001000000000000b000000000000a00000000c010100000000c0100000000000000000000000000030000000000005000000008010100000000021000000000000005000000010910100000000c0101000000010110200000000000060000000002102000000008510200000000801010000000000003000000000000700000000000020000000000001000000000000300000000000020000000000002000000000000b0000000000005000000010110000000000000030000000081100
  | 8, 12 => 0x1051010000000000005000000008110100000000c510100000000000070000000000001000000000a10200000000c0100000000008110000000000000000000000000001000000000000000000000000000000000081102000000000000100000000000030000000000006000000000000400000000c510100000000061020000000109101000000000000300000000c1101000000000000700000001011010000000000002000000010d100000000000e1000000000000002000000000000200000000000020000000000001
  | 8, 13 => 0xa00000000c910100000000121010000000002101000000000000400000000000030000000000001000000000000200000000000000000000000002000000008110100000000000020000000000002000000000000000000000000000000000000003000000000000300000000c5102000000000000b00000000000070000000002102000000000e1000000000000000000000000000500000000c1102000000008510000000000c1102000000000e1000000000000001000000000000200000000000070000000002100
  | 8, 14 => 0x60000000105100000000000000000000000000030000000000000000000000210000000000021010000000000004000000010d1000000000000003000000000a102000000000210100000000000070000000000003000000000000000000000851010000000000000000000000000c0000000000004000000000000000000000c810100000001051020000000041100000000010d1000000000000001000000000000500000000c91010000000085101000000001210100000000c810200000000000040000000000000
  | 8, 15 => 0x50000000080101000000000000000000000021000000000002100000000000000700000000000000000000000006000000000e10000000000000030000000000001
  | 9, 0 => 0x10000000000002000000000000200000000000000000000000000000000000000000000000000010000000000001
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_31 roots_31 8 s ws hint
  | 1 => checkCutEntry dom_59 roots_59 8 s ws hint
  | 2 => checkCutEntry dom_61 roots_61 8 s ws hint
  | 3 => checkCutEntry dom_62 roots_62 7 s ws hint
  | 4 => checkCutEntry dom_47 roots_47 7 s ws hint
  | 5 => checkCutEntry dom_55 roots_55 7 s ws hint
  | 6 => checkCutEntry dom_47_16 roots_47_16 6 s ws hint
  | 7 => checkCutEntry dom_55_8 roots_55_8 6 s ws hint
  | 8 => checkCutEntry dom_15_16 roots_15_16 5 s ws hint
  | 9 => checkCutEntry dom_23_8 roots_23_8 5 s ws hint
  | 10 => checkCutEntry dom_39_16 roots_39_16 5 s ws hint
  | 11 => checkCutEntry dom_39_8 roots_39_8 5 s ws hint
  | 12 => checkCutEntry dom_27 roots_27 5 s ws hint
  | 13 => checkCutEntry dom_43 roots_43 5 s ws hint
  | 14 => checkCutEntry dom_29 roots_29 5 s ws hint
  | 15 => checkCutEntry dom_53 roots_53 5 s ws hint
  | 16 => checkCutEntry dom_51_8 roots_51_8 5 s ws hint
  | 17 => checkCutEntry dom_45_16 roots_45_16 5 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_63 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_61 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_62 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_43 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_29 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_53 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_51_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_45_16 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_63 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_63 == dom_63) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_63 goalM u ys) : RunD dom_63 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_63 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_16 : ∀ i, 16 ≤ i → i < 20 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 16 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 20 → Z 5 i = true := (range_split z5_0 z5_16)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 16 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_16 : ∀ i, 16 ≤ i → i < 32 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_32 : ∀ i, 32 ≤ i → i < 48 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_48 : ∀ i, 48 ≤ i → i < 64 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_64 : ∀ i, 64 ≤ i → i < 80 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_80 : ∀ i, 80 ≤ i → i < 96 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_96 : ∀ i, 96 ≤ i → i < 104 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 96 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 104 → Z 6 i = true := (range_split (range_split (range_split z6_0 z6_16) (range_split z6_32 z6_48)) (range_split (range_split z6_64 z6_80) z6_96))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 16 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_16 : ∀ i, 16 ≤ i → i < 32 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_32 : ∀ i, 32 ≤ i → i < 48 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_48 : ∀ i, 48 ≤ i → i < 64 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_64 : ∀ i, 64 ≤ i → i < 80 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_80 : ∀ i, 80 ≤ i → i < 96 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_96 : ∀ i, 96 ≤ i → i < 112 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_112 : ∀ i, 112 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_128 : ∀ i, 128 ≤ i → i < 144 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_144 : ∀ i, 144 ≤ i → i < 160 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_160 : ∀ i, 160 ≤ i → i < 176 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_176 : ∀ i, 176 ≤ i → i < 192 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_192 : ∀ i, 192 ≤ i → i < 208 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_208 : ∀ i, 208 ≤ i → i < 224 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_224 : ∀ i, 224 ≤ i → i < 240 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_240 : ∀ i, 240 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_256 : ∀ i, 256 ≤ i → i < 272 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_272 : ∀ i, 272 ≤ i → i < 288 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 272 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_288 : ∀ i, 288 ≤ i → i < 304 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 288 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_304 : ∀ i, 304 ≤ i → i < 320 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 304 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_320 : ∀ i, 320 ≤ i → i < 336 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 320 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_336 : ∀ i, 336 ≤ i → i < 352 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 336 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_352 : ∀ i, 352 ≤ i → i < 368 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 352 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_368 : ∀ i, 368 ≤ i → i < 384 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 368 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_384 : ∀ i, 384 ≤ i → i < 395 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 11 384 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 395 → Z 7 i = true := (range_split (range_split (range_split (range_split (range_split z7_0 z7_16) (range_split z7_32 z7_48)) (range_split (range_split z7_64 z7_80) (range_split z7_96 z7_112))) (range_split (range_split (range_split z7_128 z7_144) (range_split z7_160 z7_176)) (range_split (range_split z7_192 z7_208) (range_split z7_224 z7_240)))) (range_split (range_split (range_split (range_split z7_256 z7_272) (range_split z7_288 z7_304)) (range_split (range_split z7_320 z7_336) (range_split z7_352 z7_368))) z7_384))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 16 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_16 : ∀ i, 16 ≤ i → i < 32 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_32 : ∀ i, 32 ≤ i → i < 48 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_48 : ∀ i, 48 ≤ i → i < 64 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_64 : ∀ i, 64 ≤ i → i < 80 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_80 : ∀ i, 80 ≤ i → i < 96 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_96 : ∀ i, 96 ≤ i → i < 112 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_112 : ∀ i, 112 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_128 : ∀ i, 128 ≤ i → i < 144 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_144 : ∀ i, 144 ≤ i → i < 160 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_160 : ∀ i, 160 ≤ i → i < 176 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_176 : ∀ i, 176 ≤ i → i < 192 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_192 : ∀ i, 192 ≤ i → i < 193 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 192 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 193 → Z 8 i = true := (range_split (range_split (range_split (range_split z8_0 z8_16) (range_split z8_32 z8_48)) (range_split (range_split z8_64 z8_80) (range_split z8_96 z8_112))) (range_split (range_split (range_split z8_128 z8_144) (range_split z8_160 z8_176)) z8_192))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_0 : ∀ i, 0 ≤ i → i < 16 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_16 : ∀ i, 16 ≤ i → i < 18 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 2 16 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 18 → Z 9 i = true := (range_split z9_0 z9_16)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_0 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := z10_0
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
def RootG (s : Nat) : Bool :=
  scr dom_63 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 6 5 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : RunD dom_63 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_63 roots_63 goal_63 11 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_63 goal_63 := by
    have h0 : isConstB dom_63 goal_63 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_63

theorem low_63 : Lower dom_63 roots_63 goal_63 11 := S_63.noCircuit

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

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 15]⟩], 16⟩

theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by
  simp [wit, PEqualNP.MetaComplexity.Monotone2]

theorem wit_sz : wit.size ≤ 11 := by decide

set_option maxRecDepth 40000 in
theorem wit_ev : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = Nat.testBit (4278124202 * 2 ^ 32 + 4276943016) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_63.testBit r.val = (fun x : Fin 6 → Bool => Nat.testBit (4278124202 * 2 ^ 32 + 4276943016) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) (pt6 r.val) := by decide +kernel

theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124202 * 2 ^ 32 + 4276943016) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 11 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (4278124202 * 2 ^ 32 + 4276943016) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_63 11 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_36378_aux

theorem PEqualNP.Outside.L_meta_36378 :
  ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124202 * 2 ^ 32 + 4276943016) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124202 * 2 ^ 32 + 4276943016) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  exact ⟨PEqualNP.Outside.L_meta_36378_aux.wit, PEqualNP.Outside.L_meta_36378_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_36378_aux.wit_sz (PEqualNP.Outside.L_meta_36378_aux.lower s hs), PEqualNP.Outside.L_meta_36378_aux.wit_ev⟩
