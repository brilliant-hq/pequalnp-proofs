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

namespace PEqualNP.Outside.L_meta_40507_aux

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

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xeeeaeeeaec80ec80eeeaeeeaec80ec80eeeaeeeaec80ec80eeeaeeeaec80ec80
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xfce0ec80fce0ec80fce0ec80fce0ec80fce0ec80fce0ec80fce0ec80fce0ec80
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_59_4 : Nat := 0xf0f0f0f0f0f0f0f0
def goal_59_4 : Nat := 0xffeeeeeeffeeee88ffeeeeeeffeeee88ffeeeeeeffeeee88ffeeeeeeffeeee88
def roots_59_4 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_27_4 : Nat := 0xf0f0f0f0
def goal_27_4 : Nat := 0xffeeee88ffeeee88ffeeee88ffeeee88ffeeee88ffeeee88ffeeee88ffeeee88
def roots_27_4 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfaaaaaaaf0a0a000faaaaaaaf0a0a000faaaaaaaf0a0a000faaaaaaaf0a0a000
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_47_16 : Nat := 0xffff0000ffff0000
def goal_47_16 : Nat := 0xfeeafeeafce0fce0feeafeeafce0fce0feeafeeafce0fce0feeafeeafce0fce0
def roots_47_16 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xeaeaeaeae0e08080eaeaeaeae0e08080eaeaeaeae0e08080eaeaeaeae0e08080
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfcc0ccc0fcc0cc00fcc0ccc0fcc0cc00fcc0ccc0fcc0cc00fcc0ccc0fcc0cc00
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_31_32 : Nat := 0xffffffff00000000
def goal_31_32 : Nat := 0xfeeaeeeafeeaeeeafeeaeeeafeeaeeeafeeaeeeafeeaeeeafeeaeeeafeeaeeea
def roots_31_32 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_61_2 : Nat := 0xcccccccccccccccc
def goal_61_2 : Nat := 0xfffafffafff0ffa0fffafffafff0ffa0fffafffafff0ffa0fffafffafff0ffa0
def roots_61_2 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_15_48 : Nat := 0xffff000000000000
def goal_15_48 : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeea
def roots_15_48 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0]

def dom_23 : Nat := 0xff00ff
def goal_23 : Nat := 0xe0e08080e0e08080e0e08080e0e08080e0e08080e0e08080e0e08080e0e08080
def roots_23 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_45_2 : Nat := 0xcccc0000cccc
def goal_45_2 : Nat := 0xfffafffaffa0ffa0fffafffaffa0ffa0fffafffaffa0ffa0fffafffaffa0ffa0
def roots_45_2 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_53_2 : Nat := 0xcc00cc00cc00cc
def goal_53_2 : Nat := 0xfafafafaf0f0a0a0fafafafaf0f0a0a0fafafafaf0f0a0a0fafafafaf0f0a0a0
def roots_53_2 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_30_32 : Nat := 0x5555555500000000
def goal_30_32 : Nat := 0xfcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0
def roots_30_32 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_15 : Nat := 0xffff
def goal_15 : Nat := 0xec80ec80ec80ec80ec80ec80ec80ec80ec80ec80ec80ec80ec80ec80ec80ec80
def roots_15 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0]

def dom_62_1 : Nat := 0xaaaaaaaaaaaaaaaa
def goal_62_1 : Nat := 0xfffffffffcf0fcc0fffffffffcf0fcc0fffffffffcf0fcc0fffffffffcf0fcc0
def roots_62_1 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_29 : Nat := 0x33333333
def goal_29 : Nat := 0xf0a0a000f0a0a000f0a0a000f0a0a000f0a0a000f0a0a000f0a0a000f0a0a000
def roots_29 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_57_4 : Nat := 0x3030303030303030
def goal_57_4 : Nat := 0xffaaaaaaffaaaa00ffaaaaaaffaaaa00ffaaaaaaffaaaa00ffaaaaaaffaaaa00
def roots_57_4 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_30_1 : Nat := 0xaaaaaaaa
def goal_30_1 : Nat := 0xfcf0fcc0fcf0fcc0fcf0fcc0fcf0fcc0fcf0fcc0fcf0fcc0fcf0fcc0fcf0fcc0
def roots_30_1 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_46_1 : Nat := 0xaaaa0000aaaa
def goal_46_1 : Nat := 0xfffffffffcc0fcc0fffffffffcc0fcc0fffffffffcc0fcc0fffffffffcc0fcc0
def roots_46_1 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_58_4 : Nat := 0x5050505050505050
def goal_58_4 : Nat := 0xffccccccffcccc00ffccccccffcccc00ffccccccffcccc00ffccccccffcccc00
def roots_58_4 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_39 : Nat := 0xff000000ff
def goal_39 : Nat := 0xeaeaeaea80808080eaeaeaea80808080eaeaeaea80808080eaeaeaea80808080
def roots_39 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfeeaeeeafce0ec80feeaeeeafce0ec80feeaeeeafce0ec80feeaeeeafce0ec80
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

namespace S_47
def pairsG : List (Nat × Nat) := [(1, 33), (2, 10), (3, 7), (3, 11), (3, 35), (5, 7), (5, 13), (5, 37), (6, 7), (6, 14), (6, 38), (8, 10), (9, 11), (9, 13), (9, 41), (12, 13), (12, 14), (32, 33), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (40, 41), (40, 42), (44, 45), (44, 46)]
def r1sG : List Nat := [1, 2, 3, 3, 3, 5, 5, 5, 6, 6, 6, 8, 9, 9, 9, 12, 12, 32, 34, 34, 34, 36, 36, 40, 40, 44, 44]
def r2sG : List Nat := [33, 10, 7, 11, 35, 7, 13, 37, 7, 14, 38, 10, 11, 13, 41, 13, 14, 33, 35, 38, 42, 37, 38, 41, 42, 45, 46]
def mpG : Nat := 0x7ffffff
def pool6G : List Nat := [5510594890247, 5510594890503, 9917130475277, 8804767696650, 6618746784263, 13215715690253, 6610527592711, 13216186960397, 13233367163149, 35188770211617]
def xsM : List Nat := roots_47.map (· &&& dom_47)
def goalM : Nat := goal_47 &&& dom_47
def NN : Nat → Nat
  | 3 => 1
  | 4 => 6
  | 5 => 27
  | 6 => 19
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x3b78a324
  | 4, 0 => 0xa31c0c445121794a26643839137979bc0f1fce070867e269
  | 5, 0 => 0xd4c9adb2c99008f2bc1fa3eca7e1de7ea23e1564a1c0b4b889c1804888e2183d71f40ace6fa9a6b367ae8f7563710a0761862ddf5ba073fa5b61388b57ee549052ee9a9e4fada6a445c6b42942c1d77f3234260c2a48ff951b2929df1412d30a0f1fce070afba44c03b0c7d7
  | 6, 0 => 0xf11b066eb7253fbda1c0b4b8a12a17a39f39fa5295fc1c0b7445a6b572657d5c6b7180a3686e9bda6594bfe25ba073fa5b61388b4d7877b92fef2b28270b03de160058940f1fce070da784ce
  | 7, 0 => 0xf1fce07
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xaa000000aa000000000000000000000000000000000000000000000000000000a0a00000a0a000000000000000000000000000000000000000000000000000008888000088880000000000000000000000000000000000000000000000000000555500005555000000000000000000000000000000000000000000000000000033330000333300000000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000000000ffff
  | 0, 1 => 0xeeee000000000000000000000000000000000000000000000000000000000000e0e00000e0e00000000000000000000000000000000000000000000000000000cccc0000cccc0000000000000000000000000000000000000000000000000000cccc000000000000000000000000000000000000000000000000000000000000cc000000cc000000000000000000000000000000000000000000000000000000c0c00000c0c00000000000000000000000000000000000000000000000000000aaaa0000aaaa0000000000000000000000000000000000000000000000000000aaaa0000a0a0
  | 0, 2 => 0xfafa0000f0f00000000000000000000000000000000000000000000000000000fafa000000000000000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000f0c00000f0c00000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000eeee0000eeee0000000000000000000000000000000000000000000000000000eeee0000cccc
  | 0, 3 => 0xfff00000f0f00000000000000000000000000000000000000000000000000000ffcc0000ffcc0000000000000000000000000000000000000000000000000000ffaa0000ffaa0000000000000000000000000000000000000000000000000000ffaa0000ff000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000fcfc0000fcfc0000000000000000000000000000000000000000000000000000fc000000fc00
  | 0, 4 => 0xffff0000ff000000000000000000000000000000000000000000000000000000ffff0000f0f00000000000000000000000000000000000000000000000000000ffff0000f0000000000000000000000000000000000000000000000000000000ffff0000aaaa0000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000fff00000fff00000000000000000000000000000000000000000000000000000fff00000ff00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x203483
  | 4, 0, 0 => 0x1b50d210099f349401b58d1900960349489b54d25408932c94
  | 5, 0, 0 => 0x227db349502271534950226cd24250226d534450226d534850226ce349502285234950226d7349502234908150226d5409501b54f349501b5490c050246d534950226d5349502275534750266953495
  | 5, 0, 1 => 0x226d510350226d9289502261534950226cd102589b34a246601b54d24050226d3349501534904050226d544550225490c150227952c95
  | 6, 0, 0 => 0x89b551349689b54d245689b655349689d6d5349689b54d2c9689b54d289689b552349689b54d30960226cd24250226d5344589b54d24469626d534968e26d5349689b69534960226d5349589b54d2416
  | 6, 0, 1 => 0x9a26d5349689b54d242601b54d2405
  | 7, 0, 0 => 0x226d53495
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 22
  | 4 => 34
  | 5 => 40
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
  | 0, 0 => 0x700000000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000000001c0000000000000000000000000000000000000000000000000000000007ff8f020000000000000000000000000000000000000000000000000000000007e3f8e100000000000000000000000000000000000000000000000000000000019e781f00000000000000000000000000000000000000000000000000000000007e07ff000000000000000000000000000000000000000000000000000000000001ffff
  | 0, 1 => 0x1c000000000000000000000000000000000000000000000000000000000000000007e000000000000000000000000000000000000000000000000000000000001c071e00000000000000000000000000000000000000000000000000000000001c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000070fd00000000000000000000000000000000000000000000000000000000000000e0
  | 0, 2 => 0x66187e0000000000000000000000000000000000000000000000000000000000660000000000000000000000000000000000000000000000000000000000000066187e000000000000000000000000000000000000000000000000000000000066000000000000000000000000000000000000000000000000000000000000006018700000000000000000000000000000000000000000000000000000000000601800000000000000000000000000000000000000000000000000000000000001c77ff00000000000000000000000000000000000000000000000000000000001c071e
  | 0, 3 => 0x7e187e000000000000000000000000000000000000000000000000000000000079dff1e000000000000000000000000000000000000000000000000000000000781f8fd000000000000000000000000000000000000000000000000000000000781f800000000000000000000000000000000000000000000000000000000000781f800000000000000000000000000000000000000000000000000000000000780000000000000000000000000000000000000000000000000000000000000067d87fe0000000000000000000000000000000000000000000000000000000006018000
  | 0, 4 => 0x7fff8000000000000000000000000000000000000000000000000000000000007ff87e00000000000000000000000000000000000000000000000000000000007ff80000000000000000000000000000000000000000000000000000000000007fe70fd0000000000000000000000000000000000000000000000000000000007fe00000000000000000000000000000000000000000000000000000000000007e1ffe00000000000000000000000000000000000000000000000000000000007e1f800
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x280f048000000000000000000000000000000000000000000000000000000000220a1e4000000000000000000000000000000000000000000000000000000000004113c0000000000000000000000000000000000000000000000000000000005590e020000000000000000000000000000000000000000000000000000000002a2e0c1000000000000000000000000000000000000000000000000000000000196581b00000000000000000000000000000000000000000000000000000000006e05b5000000000000000000000000000000000000000000000000000000000001bb6e
  | 0, 1 => 0x7fe4491000000000000000000000000000000000000000000000000000000000669a7e400000000000000000000000000000000000000000000000000000000055d1f3e00000000000000000000000000000000000000000000000000000000055c04100000000000000000000000000000000000000000000000000000000005111a0a00000000000000000000000000000000000000000000000000000000044907240000000000000000000000000000000000000000000000000000000002a6f1fd0000000000000000000000000000000000000000000000000000000002a6e1f5
  | 0, 2 => 0x6efe7f50000000000000000000000000000000000000000000000000000000006ee4491000000000000000000000000000000000000000000000000000000000669a7e40000000000000000000000000000000000000000000000000000000006680480000000000000000000000000000000000000000000000000000000000649a764000000000000000000000000000000000000000000000000000000000601a2400000000000000000000000000000000000000000000000000000000007ffffff0000000000000000000000000000000000000000000000000000000007ff5fbf
  | 0, 3 => 0x7f9e7e40000000000000000000000000000000000000000000000000000000007ddff7e0000000000000000000000000000000000000000000000000000000007b7fbff0000000000000000000000000000000000000000000000000000000007b7fadb000000000000000000000000000000000000000000000000000000000791fa4a000000000000000000000000000000000000000000000000000000000790400000000000000000000000000000000000000000000000000000000000077dbffe000000000000000000000000000000000000000000000000000000000711ba4a
  | 0, 4 => 0x7fffedb0000000000000000000000000000000000000000000000000000000007ffe7f50000000000000000000000000000000000000000000000000000000007ffe6d10000000000000000000000000000000000000000000000000000000007fef5fd0000000000000000000000000000000000000000000000000000000007fe44910000000000000000000000000000000000000000000000000000000007f9ffee0000000000000000000000000000000000000000000000000000000007f9feca
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 39 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 39 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 39 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 39 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_47 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_47 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
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
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_16 : ∀ i, 16 ≤ i → i < 27 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 11 16 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 27 → Z 5 i = true := (range_split z5_0 z5_16)
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
  scr dom_47 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_47 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_47 roots_47 goal_47 8 := by
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

theorem low_47 : Lower dom_47 roots_47 goal_47 8 := S_47.noCircuit

namespace S_31
def pairsG : List (Nat × Nat) := [(2, 10), (3, 7), (3, 11), (5, 7), (5, 13), (5, 21), (6, 7), (6, 14), (6, 22), (8, 10), (9, 11), (9, 13), (12, 13), (12, 14), (12, 28), (17, 21), (18, 22), (18, 26), (19, 23), (19, 27), (20, 21), (20, 22), (20, 28), (24, 26), (24, 28), (25, 27), (25, 29)]
def r1sG : List Nat := [2, 3, 3, 5, 5, 5, 6, 6, 6, 8, 9, 9, 12, 12, 12, 17, 18, 18, 19, 19, 20, 20, 20, 24, 24, 25, 25]
def r2sG : List Nat := [10, 7, 11, 7, 13, 21, 7, 14, 22, 10, 11, 13, 13, 14, 28, 21, 22, 26, 23, 27, 21, 22, 28, 26, 28, 27, 29]
def mpG : Nat := 0x7ffffff
def pool6G : List Nat := [6618746784263, 5510594890247, 8805020341770, 13215715690253, 22011809498901, 9917382920717, 26465925862922, 22011910556949, 22041857428764, 22016087623446]
def xsM : List Nat := roots_31.map (· &&& dom_31)
def goalM : Nat := goal_31 &&& dom_31
def NN : Nat → Nat
  | 4 => 6
  | 5 => 32
  | 6 => 18
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xb19e9137ac05225e977a363d91fadbc52e416dae12e7ff0c
  | 5, 0 => 0xe457f490b19e9137ac05225e9e9c03b29df29cfa8c616cec81ea162e7dd26df173a0d5136baa58136112f50b5e1d4aa85d1936d05c943edf5c5c027555fbf4bf537bfbe75299e96d526e44fc3cf0896d3a6b8d413a3350d732f633fb30de30f42637312d2465644e1f7c8e901d0f71261ac7d7cf18c3dfb008137f24032905ee
  | 6, 0 => 0xfd575aabac05225ea0508cfd93c0f7228c616cec7ecfa1837702c5a95c943edf554c825e5299e96d3a6b8d4130706e42276bea4325303d37206585ea1b8a7ef1126b25b70241d3e1
  | 7, 0 => 0xac05225e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x5f5f5f5f00000000000000000000000000000000000000000000000000000000555555550000000000000000000000000000000000000000000000000000000033333333000000000000000000000000000000000000000000000000000000000f0fffff000000000000000000000000000000000000000000000000000000000f0f0f0f0000000000000000000000000000000000000000000000000000000000ff00ff000000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000f0f0
  | 0, 1 => 0xcc00cc0000000000000000000000000000000000000000000000000000000000afafafaf00000000000000000000000000000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000000aaaaa0a000000000000000000000000000000000000000000000000000000000aaaa000000000000000000000000000000000000000000000000000000000000aaa0aaa000000000000000000000000000000000000000000000000000000000a0a0a0a00000000000000000000000000000000000000000000000000000000088888888
  | 0, 2 => 0xfafa000000000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000f0f0a0a000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000eeeeeeee00000000000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000ccc0ccc0
  | 0, 3 => 0xffff0f0f00000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000fff0fff000000000000000000000000000000000000000000000000000000000ffccffcc00000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000fcfcfcfc00000000000000000000000000000000000000000000000000000000fcf0fcf000000000000000000000000000000000000000000000000000000000fafafafa
  | 0, 4 => 0xffffff0000000000000000000000000000000000000000000000000000000000ffffcc0000000000000000000000000000000000000000000000000000000000ffffaaaa00000000000000000000000000000000000000000000000000000000ffffaa00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x1b511251e6d644d501b4491100511242401b51131006d544b4
  | 5, 0, 0 => 0x6d6446055e6d1343579b592215e591242579b591195b5944465791343095b591340579b611255f6d644d579b590355e6d644a5796446095e6d944d579b511255e6d12435
  | 5, 0, 1 => 0x85b5912d406d4449479b591355e58d14256d7591355e591342579c58f355e6d6447579b44e0d5b44d0c1581b591355e75344d589b591355e6d644956d6511255e6d544d5
  | 6, 0, 0 => 0x79b591348679b69644d601e591342579b59134568de6d644d601e6d6449579b59134b601e6d1343501e6d6446579c6d644d685e6d644d679b59344d679b61644d679b591341679b5913cd679b59444d6
  | 6, 0, 1 => 0x79b591343601e6d644d5
  | 7, 0, 0 => 0x1e6d644d5
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
  | 0, 0 => 0x7ffffc70000000000000000000000000000000000000000000000000000000001f373c10000000000000000000000000000000000000000000000000000000007f0fe3800000000000000000000000000000000000000000000000000000000078fffff00000000000000000000000000000000000000000000000000000000078f8e0700000000000000000000000000000000000000000000000000000000007f81ff0000000000000000000000000000000000000000000000000000000000007fff00000000000000000000000000000000000000000000000000000000000071f8
  | 0, 1 => 0x78f8e3f00000000000000000000000000000000000000000000000000000000060c8c3e00000000000000000000000000000000000000000000000000000000060c803800000000000000000000000000000000000000000000000000000000060c80000000000000000000000000000000000000000000000000000000000006000c38000000000000000000000000000000000000000000000000000000000000003800000000000000000000000000000000000000000000000000000000000c0006
  | 0, 2 => 0x67c800000000000000000000000000000000000000000000000000000000000007071f800000000000000000000000000000000000000000000000000000000007000380000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000060f8dff00000000000000000000000000000000000000000000000000000000000f01c700000000000000000000000000000000000000000000000000000000000001c0
  | 0, 3 => 0x7ff8e070000000000000000000000000000000000000000000000000000000007ff80000000000000000000000000000000000000000000000000000000000007f07ff800000000000000000000000000000000000000000000000000000000078f7fc70000000000000000000000000000000000000000000000000000000007807e0000000000000000000000000000000000000000000000000000000000007f71ff00000000000000000000000000000000000000000000000000000000007071f800000000000000000000000000000000000000000000000000000000067cfdfe
  | 0, 4 => 0x7fffe000000000000000000000000000000000000000000000000000000000007ff80000000000000000000000000000000000000000000000000000000000007ff8c3e0000000000000000000000000000000000000000000000000000000007ff8c00
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3eb67850000000000000000000000000000000000000000000000000000000001e36381000000000000000000000000000000000000000000000000000000000550d83000000000000000000000000000000000000000000000000000000000028a3edf00000000000000000000000000000000000000000000000000000000028a0605000000000000000000000000000000000000000000000000000000000035816a0000000000000000000000000000000000000000000000000000000000003edf00000000000000000000000000000000000000000000000000000000000038da
  | 0, 1 => 0x28a268500000000000000000000000000000000000000000000000000000000069e9e7f00000000000000000000000000000000000000000000000000000000061c9c7e00000000000000000000000000000000000000000000000000000000061c987a00000000000000000000000000000000000000000000000000000000061c802000000000000000000000000000000000000000000000000000000000061c9c7e000000000000000000000000000000000000000000000000000000000414987a00000000000000000000000000000000000000000000000000000000020c044e
  | 0, 2 => 0x77dc120000000000000000000000000000000000000000000000000000000000575f9fa000000000000000000000000000000000000000000000000000000000575d97a000000000000000000000000000000000000000000000000000000000575c12000000000000000000000000000000000000000000000000000000000054078900000000000000000000000000000000000000000000000000000000006bfbfff0000000000000000000000000000000000000000000000000000000002af27cf0000000000000000000000000000000000000000000000000000000002af27cf
  | 0, 3 => 0x7ffc7250000000000000000000000000000000000000000000000000000000007ffc1200000000000000000000000000000000000000000000000000000000007ffffff0000000000000000000000000000000000000000000000000000000007ef7fdf0000000000000000000000000000000000000000000000000000000007ca7e950000000000000000000000000000000000000000000000000000000007ffffff0000000000000000000000000000000000000000000000000000000007ffffff00000000000000000000000000000000000000000000000000000000077dfdfe
  | 0, 4 => 0x7ffffb50000000000000000000000000000000000000000000000000000000007ffe7a50000000000000000000000000000000000000000000000000000000007ffdd7e0000000000000000000000000000000000000000000000000000000007ffdd34
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 7 0 (NN s)
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

def symsG : List (List (Nat × Nat)) := [[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
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
private theorem z4_0 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_16 : ∀ i, 16 ≤ i → i < 32 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 16 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 32 → Z 5 i = true := (range_split z5_0 z5_16)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 16 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_16 : ∀ i, 16 ≤ i → i < 18 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 2 16 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 18 → Z 6 i = true := (range_split z6_0 z6_16)
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

namespace S_59_4
def pairsG : List (Nat × Nat) := [(5, 7), (5, 13), (5, 21), (5, 37), (6, 7), (6, 14), (6, 22), (6, 38), (12, 13), (12, 14), (12, 28), (20, 21), (20, 22), (20, 28), (36, 37), (36, 38), (44, 45), (44, 46), (44, 60), (52, 53), (52, 54), (52, 60)]
def r1sG : List Nat := [5, 5, 5, 5, 6, 6, 6, 6, 12, 12, 12, 20, 20, 20, 36, 36, 44, 44, 44, 52, 52, 52]
def r2sG : List Nat := [7, 13, 21, 37, 7, 14, 22, 38, 13, 14, 28, 21, 22, 28, 37, 38, 45, 46, 60, 53, 54, 60]
def mpG : Nat := 0x3fffff
def pool6G : List Nat := [6618746850567, 22041857428764, 22016087623446, 13219994076942, 22011809498901, 13215715952397, 22011910555413, 13215951754503, 13215951750925, 22011910556949, 13215951754509, 48464512550684, 48464495707932, 13220246722062, 39603996591909, 22016087623462, 13219994076966, 39608274716454]
def xsM : List Nat := roots_59_4.map (· &&& dom_59_4)
def goalM : Nat := goal_59_4 &&& dom_59_4
def NN : Nat → Nat
  | 3 => 1
  | 4 => 13
  | 5 => 38
  | 6 => 18
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xe6dde99b
  | 4, 0 => 0xfd97003af04667e4df6fc12eccdc81d8b3dc912aae484157a111e04c89a9a1a28625e74959a198c84f722dbd31230a5e2c83a511
  | 5, 0 => 0xf0712538eaf43a4adee054fbca113452c6acf761bd450f739980a90d9932bf3f946f96e389a9a1a26e1087db6c7847d9667bce6263b51881592c82d54c889e274659dcf0463fd9af40c9955c3f6c1fd33205d85b2e4b4f1d2a93f0e92679f43225d8b0fa24cf6fc1232ba250212d34bf1c1fd7b516a2ecc714922a9e11d48077109e7e830be8b62f09c88c08096d94f407e009cb03fbdaf6
  | 6, 0 => 0xf2d75889ddf35383ab6ac147a29b3d889980a90d93105dcc8a1ab9ee89a9a1a26c7847d9548ee642481bdf54372fbb86346712e021e7ef56212d34bf20def6a21fc19f2516a2ecc7
  | 7, 0 => 0x89a9a1a2
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x80808080808080800000000000000000000000000000000000000000000000005050505050505050000000000000000000000000000000000000000000000000303030303030303000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000f000f0000000000000000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000000000000000000000000000000000000000f0f0f0f0000000000000000000000000000000000000000000000000000000000000f0f0
  | 0, 1 => 0xe0e0c0c0e0e0c0c0000000000000000000000000000000000000000000000000e0a0e0a0e0a0e0a0000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000000c0c0c0c000000000000000000000000000000000000000000000000000000000c000c000c000c000000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a0000000000000000000000000000000000000000000000000a0a0a0a000000000000000000000000000000000000000000000000000000000a000a000a000a000
  | 0, 2 => 0xf080f080f080f080000000000000000000000000000000000000000000000000f000f0f0f000f000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e0000000000000000000000000000000000000000000000000e0e0e0e0c0c0c0c0000000000000000000000000000000000000000000000000e0e0e0e000000000
  | 0, 3 => 0xf0f00000f0f0f0f0000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000f0e0f0e0f000f000000000000000000000000000000000000000000000000000f0c0f0c0f0c0f0c0000000000000000000000000000000000000000000000000f0c0f000f0c0f000000000000000000000000000000000000000000000000000f0c0c0c0f0c0c0c0000000000000000000000000000000000000000000000000f0a0f0a0f0a0f0a0
  | 0, 4 => 0xf0f0f0f080808080000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000f0f0f000f0f0f000000000000000000000000000000000000000000000000000f0f0c0c0f0f0c0c0000000000000000000000000000000000000000000000000f0f0c0c0f0f00000000000000000000000000000000000000000000000000000f0f0a0a0f0f0a0a0000000000000000000000000000000000000000000000000f0f0a000f0f0a000000000000000000000000000000000000000000000000000f0f000f0f0f00000
  | 0, 5 => 0xf0f0f0f0f0f0f000000000000000000000000000000000000000000000000000f0f0f0f0f0f00000000000000000000000000000000000000000000000000000f0f0f0f0f000f000000000000000000000000000000000000000000000000000f0f0f0f0f0000000000000000000000000000000000000000000000000000000f0f0f0f0c000c000000000000000000000000000000000000000000000000000f0f0f0f0a0a0a0a0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x2d64a3
  | 4, 0, 0 => 0x9de5524026959290081534a40267974900b5334a40287954500ade64a499e54d294058d282402691a292692255250268953d0079c34a4
  | 5, 0, 0 => 0xb1e55234a601534a081502679954a50268d534a502979534a502c79534a501e54d283502654d2825026795487502b54d282502b79434a501e54d181502685534a502679544a599e6d834a602c7952855
  | 5, 0, 1 => 0x1e54d281502d79534a502779534a502679534a502b79334a5026795285501e55034a502679734a502b78d284502679538d502c89534a5028795349502678a144502679b2ca502a79534a59a279548d6
  | 5, 0, 2 => 0x1e34a103502634a1025026795185501e54d280501f79534a502695334a5
  | 6, 0, 0 => 0x99e54d28769a579534a601e54d281599e55234a699e75534a602679534a5026795285599e54d286699e54d30a699e6d534a699e54d2816a2679534a602c79534a599e54d2886ae679534a602654d2825
  | 6, 0, 1 => 0x99e55334a699e54d2846
  | 7, 0, 0 => 0x2679534a5
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 22
  | 4 => 34
  | 5 => 40
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
  | 0, 0 => 0x3ffff000000000000000000000000000000000000000000000000000000000003fff0f000000000000000000000000000000000000000000000000000000000038f8ff000000000000000000000000000000000000000000000000000000000038c000000000000000000000000000000000000000000000000000000000000007c7ff0000000000000000000000000000000000000000000000000000000000003fff00000000000000000000000000000000000000000000000000000000000007ff
  | 0, 1 => 0xf0000000000000000000000000000000000000000000000000000000000000000f00000000000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 0, 2 => 0x70700000000000000000000000000000000000000000000000000000000000007c70000000000000000000000000000000000000000000000000000000000000707000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000f00000000000000000000000000000000000000000000000000000000000000000
  | 0, 3 => 0x383fff00000000000000000000000000000000000000000000000000000000003838000000000000000000000000000000000000000000000000000000000000380000000000000000000000000000000000000000000000000000000000000007070000000000000000000000000000000000000000000000000000000000000707f0000000000000000000000000000000000000000000000000000000000007070000000000000000000000000000000000000000000000000000000000000000f0000000000000000000000000000000000000000000000000000000000007070f
  | 0, 4 => 0x3fc00000000000000000000000000000000000000000000000000000000000003fc00000000000000000000000000000000000000000000000000000000000003f3f0000000000000000000000000000000000000000000000000000000000003838f00000000000000000000000000000000000000000000000000000000000383800000000000000000000000000000000000000000000000000000000000038380f0000000000000000000000000000000000000000000000000000000000383800000000000000000000000000000000000000000000000000000000000038f800
  | 0, 5 => 0x3fff0000000000000000000000000000000000000000000000000000000000003ff80000000000000000000000000000000000000000000000000000000000003fc70000000000000000000000000000000000000000000000000000000000003fc00000000000000000000000000000000000000000000000000000000000003fc00000000000000000000000000000000000000000000000000000000000003fc00f
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x11000000000000000000000000000000000000000000000000000000000036b6e000000000000000000000000000000000000000000000000000000000002d6d0e000000000000000000000000000000000000000000000000000000000018d8dd000000000000000000000000000000000000000000000000000000000018c088000000000000000000000000000000000000000000000000000000000003c3bb0000000000000000000000000000000000000000000000000000000000003f770000000000000000000000000000000000000000000000000000000000000333
  | 0, 1 => 0x1a9af500000000000000000000000000000000000000000000000000000000000b4b3f00000000000000000000000000000000000000000000000000000000001292f100000000000000000000000000000000000000000000000000000000001280800000000000000000000000000000000000000000000000000000000000020220000000000000000000000000000000000000000000000000000000000009491f00000000000000000000000000000000000000000000000000000000000940080000000000000000000000000000000000000000000000000000000000010102
  | 0, 2 => 0x272733000000000000000000000000000000000000000000000000000000000027e7aa00000000000000000000000000000000000000000000000000000000002727220000000000000000000000000000000000000000000000000000000000270000000000000000000000000000000000000000000000000000000000000024240000000000000000000000000000000000000000000000000000000000001bdbff00000000000000000000000000000000000000000000000000000000001bd2f900000000000000000000000000000000000000000000000000000000001bc088
  | 0, 3 => 0x3c3f7700000000000000000000000000000000000000000000000000000000003c3c4400000000000000000000000000000000000000000000000000000000003c000000000000000000000000000000000000000000000000000000000000003fe7aa000000000000000000000000000000000000000000000000000000000037b7f30000000000000000000000000000000000000000000000000000000000373762000000000000000000000000000000000000000000000000000000000036b6f100000000000000000000000000000000000000000000000000000000002f6f3f
  | 0, 4 => 0x3fc09900000000000000000000000000000000000000000000000000000000003fc08800000000000000000000000000000000000000000000000000000000003f3f6600000000000000000000000000000000000000000000000000000000003ebef500000000000000000000000000000000000000000000000000000000003ebcc400000000000000000000000000000000000000000000000000000000003d7d5f00000000000000000000000000000000000000000000000000000000003d3d4600000000000000000000000000000000000000000000000000000000003cfccc
  | 0, 5 => 0x3fffee00000000000000000000000000000000000000000000000000000000003ffccc00000000000000000000000000000000000000000000000000000000003fe7aa00000000000000000000000000000000000000000000000000000000003fe48800000000000000000000000000000000000000000000000000000000003fc2a800000000000000000000000000000000000000000000000000000000003fc99f
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 46 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 46 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 46 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 46 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 7 0 (NN s)
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_59_4 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_59_4 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_59_4 == dom_59_4) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_59_4 goalM u ys) : RunD dom_59_4 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_59_4 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 13 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 13 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 13 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_16 : ∀ i, 16 ≤ i → i < 32 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_32 : ∀ i, 32 ≤ i → i < 38 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 32 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 38 → Z 5 i = true := (range_split (range_split z5_0 z5_16) z5_32)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 16 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_16 : ∀ i, 16 ≤ i → i < 18 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 2 16 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 18 → Z 6 i = true := (range_split z6_0 z6_16)
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
  scr dom_59_4 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_59_4 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_59_4 roots_59_4 goal_59_4 8 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_59_4 goal_59_4 := by
    have h0 : isConstB dom_59_4 goal_59_4 = false := by decide +kernel
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

end S_59_4

theorem low_59_4 : Lower dom_59_4 roots_59_4 goal_59_4 8 := S_59_4.noCircuit

namespace S_27_4
def pairsG : List (Nat × Nat) := [(5, 7), (5, 13), (5, 21), (6, 7), (6, 14), (6, 22), (12, 13), (12, 14), (12, 28), (20, 21), (20, 22), (20, 28)]
def r1sG : List Nat := [5, 5, 5, 6, 6, 6, 12, 12, 12, 20, 20, 20]
def r2sG : List Nat := [7, 13, 21, 7, 14, 22, 13, 14, 28, 21, 22, 28]
def mpG : Nat := 0xfff
def pool6G : List Nat := [6618746850567, 22041857428764, 22016087623446, 13219994076942, 22011809498901, 13215715952397, 6618881592583, 13220246722062]
def xsM : List Nat := roots_27_4.map (· &&& dom_27_4)
def goalM : Nat := goal_27_4 &&& dom_27_4
def NN : Nat → Nat
  | 3 => 3
  | 4 => 6
  | 5 => 5
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xde1ca231294c465c24466917
  | 4, 0 => 0xde1ca23121ffb4a51fa9d1ad131d72670eeeb4e7002eea28
  | 5, 0 => 0xde1ca23146a46e6f107722cb0a521d7d002eea28
  | 6, 0 => 0xde1ca231
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0a0a0a000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000e0e0c0c000000000000000000000000000000000000000000000000000000000c0c0c0c000000000000000000000000000000000000000000000000000000000a0a0a0a000000000000000000000000000000000000000000000000000000000a000a00000000000000000000000000000000000000000000000000000000000505050500000000000000000000000000000000000000000000000000000000030303030
  | 0, 1 => 0xf0f0f00000000000000000000000000000000000000000000000000000000000f0f0a0a000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000f0a0f0a0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x964340a653ba844
  | 4, 0, 0 => 0x96434096104098424097644ba6435096414
  | 5, 0, 0 => 0x96434964315b96435964325096414
  | 6, 0, 0 => 0x96434
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 20
  | 4 => 24
  | 5 => 24
  | 6 => 20
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 4 0) :: stateWires n (ids >>> 4)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x700000000000000000000000000000000000000000000000000000000000001c000000000000000000000000000000000000000000000000000000000000000380000000000000000000000000000000000000000000000000000000000000038000000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ff80000000000000000000000000000000000000000000000000000000000000fc7
  | 0, 1 => 0xfc00000000000000000000000000000000000000000000000000000000000000e070000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000000001c7
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xb4f00000000000000000000000000000000000000000000000000000000000009d200000000000000000000000000000000000000000000000000000000000006bd00000000000000000000000000000000000000000000000000000000000004b9000000000000000000000000000000000000000000000000000000000000024f00000000000000000000000000000000000000000000000000000000000000420000000000000000000000000000000000000000000000000000000000000db00000000000000000000000000000000000000000000000000000000000000b46
  | 0, 1 => 0xff60000000000000000000000000000000000000000000000000000000000000f6f0000000000000000000000000000000000000000000000000000000000000f240000000000000000000000000000000000000000000000000000000000000bdf
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_27_4 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_27_4 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_27_4 == dom_27_4) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_27_4 goalM u ys) : RunD dom_27_4 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_27_4 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := z5_0
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
  scr dom_27_4 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_27_4 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_27_4 roots_27_4 goal_27_4 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_27_4 goal_27_4 := by
    have h0 : isConstB dom_27_4 goal_27_4 = false := by decide +kernel
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

end S_27_4

theorem low_27_4 : Lower dom_27_4 roots_27_4 goal_27_4 7 := S_27_4.noCircuit

namespace S_61
def pairsG : List (Nat × Nat) := [(1, 33), (5, 13), (5, 21), (5, 37), (9, 13), (9, 41), (12, 13), (12, 28), (17, 21), (17, 49), (20, 21), (20, 28), (24, 28), (25, 29), (25, 57), (32, 33), (36, 37), (40, 41), (44, 45), (44, 60), (48, 49), (52, 53), (52, 60), (56, 57), (56, 60)]
def r1sG : List Nat := [1, 5, 5, 5, 9, 9, 12, 12, 17, 17, 20, 20, 24, 25, 25, 32, 36, 40, 44, 44, 48, 52, 52, 56, 56]
def r2sG : List Nat := [33, 13, 21, 37, 13, 41, 13, 28, 21, 49, 21, 28, 28, 29, 57, 33, 37, 41, 45, 60, 49, 53, 60, 57, 60]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [13215951754509, 22041857428764, 13233735932941, 22012447759381, 22064188693525]
def xsM : List Nat := roots_61.map (· &&& dom_61)
def goalM : Nat := goal_61 &&& dom_61
def NN : Nat → Nat
  | 4 => 2
  | 5 => 7
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x995298d18bc37aaa
  | 5, 0 => 0xd268f7e7ce2fdbfd9c1be658995298d13e3ca5392ac4f6e510bacbc3
  | 6, 0 => 0x995298d1
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x30300000303000000000000000000000000000000000000000000000000000003000300030003000000000000000000000000000000000000000000000000000222222222222222200000000000000000000000000000000000000000000000022222222000000000000000000000000000000000000000000000000000000001111111111111111000000000000000000000000000000000000000000000000030303030303030300000000000000000000000000000000000000000000000000003333000033330000000000000000000000000000000000000000000000000000000033333333
  | 0, 1 => 0x3333333300000000000000000000000000000000000000000000000000000000333300003333000000000000000000000000000000000000000000000000000033003300330033000000000000000000000000000000000000000000000000003030303030303030
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xba98550b7654
  | 5, 0, 0 => 0xba9835a98545a98505ba9855ba9525b98515b98755
  | 6, 0, 0 => 0xba9855
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
  | 0, 0 => 0x600c0000000000000000000000000000000000000000000000000000000000000c00c0000000000000000000000000000000000000000000000000000000000000633f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001ff9cc0000000000000000000000000000000000000000000000000000000000192f33100000000000000000000000000000000000000000000000000000000000f80ff0000000000000000000000000000000000000000000000000000000000007fff
  | 0, 1 => 0x1ff80000000000000000000000000000000000000000000000000000000000001f07f0000000000000000000000000000000000000000000000000000000000018e70f000000000000000000000000000000000000000000000000000000000006d0cce
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1683d8400000000000000000000000000000000000000000000000000000000014c38d20000000000000000000000000000000000000000000000000000000000b7e77f0000000000000000000000000000000000000000000000000000000000b7c2290000000000000000000000000000000000000000000000000000000001481880000000000000000000000000000000000000000000000000000000000092c221000000000000000000000000000000000000000000000000000000000007807b0000000000000000000000000000000000000000000000000000000000003dd6
  | 0, 1 => 0x1ffc2290000000000000000000000000000000000000000000000000000000001f87f840000000000000000000000000000000000000000000000000000000001ce78f200000000000000000000000000000000000000000000000000000000016d3dde
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_61 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_61 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_61 == dom_61) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_61 goalM u ys) : RunD dom_61 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_61 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_61 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_61 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_61 roots_61 goal_61 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_61 goal_61 := by
    have h0 : isConstB dom_61 goal_61 = false := by decide +kernel
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

end S_61

theorem low_61 : Lower dom_61 roots_61 goal_61 7 := S_61.noCircuit

namespace S_47_16
def pairsG : List (Nat × Nat) := [(17, 21), (17, 49), (18, 22), (18, 26), (19, 23), (19, 27), (19, 51), (20, 21), (20, 22), (20, 28), (24, 26), (24, 28), (25, 27), (25, 29), (25, 57), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [17, 17, 18, 18, 19, 19, 19, 20, 20, 20, 24, 24, 25, 25, 25, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [21, 49, 22, 26, 23, 27, 51, 21, 22, 28, 26, 28, 27, 29, 57, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [22067946461718, 55062422100502, 26474482112028, 22072258073878, 26465925862938, 22072679011861, 22064189742101, 27574632782869]
def xsM : List Nat := roots_47_16.map (· &&& dom_47_16)
def goalM : Nat := goal_47_16 &&& dom_47_16
def NN : Nat → Nat
  | 4 => 3
  | 5 => 7
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xc90bf30773240d5201b9a758
  | 5, 0 => 0xeddd1af5d827a5f7d7c737eb73240d521a2873311391194e05dfb75b
  | 6, 0 => 0x73240d52
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xcccc0000cccc0000000000000000000000000000000000000000000000000000aaaa0000aaaa0000000000000000000000000000000000000000000000000000aaaa0000a0a00000000000000000000000000000000000000000000000000000aaaa00000000000000000000000000000000000000000000000000000000000055550000555500000000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000000000ffff0000
  | 0, 1 => 0xffff0000f0f00000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000fafa0000f0f00000000000000000000000000000000000000000000000000000f0f00000f0f00000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xa8754ba87650a9764
  | 5, 0, 0 => 0xa87605ba7625ba8735ba8765ca8765a87645b87615
  | 6, 0, 0 => 0xba8765
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
  | 0, 0 => 0x7007c0000000000000000000000000000000000000000000000000000000000007073000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001ff8f8c0000000000000000000000000000000000000000000000000000000001c7fc7f00000000000000000000000000000000000000000000000000000000003f83ff0000000000000000000000000000000000000000000000000000000000007fff
  | 0, 1 => 0x1ff83800000000000000000000000000000000000000000000000000000000001ff80000000000000000000000000000000000000000000000000000000000001c07c0000000000000000000000000000000000000000000000000000000000003803800000000000000000000000000000000000000000000000000000000000380380
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x97157c000000000000000000000000000000000000000000000000000000000049f0f3000000000000000000000000000000000000000000000000000000000049e0d3000000000000000000000000000000000000000000000000000000000049c0420000000000000000000000000000000000000000000000000000000001b60f0c0000000000000000000000000000000000000000000000000000000000c5d46a00000000000000000000000000000000000000000000000000000000001b81d70000000000000000000000000000000000000000000000000000000000003fbd
  | 0, 1 => 0x1ffebd70000000000000000000000000000000000000000000000000000000001ffc0420000000000000000000000000000000000000000000000000000000001e47e2800000000000000000000000000000000000000000000000000000000017bebd700000000000000000000000000000000000000000000000000000000013a2b95
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 13 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 13 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 13 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 13 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_47_16 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_47_16 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
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
private theorem z4_0 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := z4_0
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
  scr dom_47_16 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_47_16 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_47_16 roots_47_16 goal_47_16 7 := by
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

theorem low_47_16 : Lower dom_47_16 roots_47_16 goal_47_16 7 := S_47_16.noCircuit

namespace S_55
def pairsG : List (Nat × Nat) := [(1, 33), (3, 7), (3, 35), (5, 7), (5, 21), (5, 37), (6, 7), (6, 22), (6, 38), (17, 21), (17, 49), (18, 22), (19, 23), (19, 51), (20, 21), (20, 22), (32, 33), (34, 35), (34, 38), (36, 37), (36, 38), (48, 49), (50, 51), (50, 54), (52, 53), (52, 54)]
def r1sG : List Nat := [1, 3, 3, 5, 5, 5, 6, 6, 6, 17, 17, 18, 19, 19, 20, 20, 32, 34, 34, 36, 36, 48, 50, 50, 52, 52]
def r2sG : List Nat := [33, 7, 35, 7, 21, 37, 7, 22, 38, 21, 49, 22, 23, 51, 21, 22, 33, 35, 38, 37, 38, 49, 51, 54, 53, 54]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [6618881594631, 6610527592711, 22063819923733, 22016087623446, 22064088028693, 22011809498901]
def xsM : List Nat := roots_55.map (· &&& dom_55)
def goalM : Nat := goal_55 &&& dom_55
def NN : Nat → Nat
  | 3 => 1
  | 4 => 3
  | 5 => 9
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xc0a0b975
  | 4, 0 => 0x8647ec728050ef7847baa070
  | 5, 0 => 0xfd05eeb0dc541c4eae0dadfba4f836c38a64578173ea86206b85db7447baa07045f82275
  | 6, 0 => 0x47baa070
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xcc00cc00cc00cc00000000000000000000000000000000000000000000000000c000c000c000c000000000000000000000000000000000000000000000000000aa00aa00aa00aa00000000000000000000000000000000000000000000000000550055005500550000000000000000000000000000000000000000000000000033003300330033000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000000ff000000ff0000000000000000000000000000000000000000000000000000000000ff00ff
  | 0, 1 => 0xff00ff00ff000000000000000000000000000000000000000000000000000000ff00ff00f0000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000f0000000f00000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xc653
  | 4, 0, 0 => 0xb86540c9754ba9755
  | 5, 0, 0 => 0xba7525ba9655db9755ba9745ba9535a97505b97515ba9755b98755
  | 6, 0, 0 => 0xba9755
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 16
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
  | 0, 0 => 0xc639c600000000000000000000000000000000000000000000000000000000000001c0000000000000000000000000000000000000000000000000000000000000363f0000000000000000000000000000000000000000000000000000000003ffc9c0000000000000000000000000000000000000000000000000000000000339c6390000000000000000000000000000000000000000000000000000000000e73e0700000000000000000000000000000000000000000000000000000000001f01ff000000000000000000000000000000000000000000000000000000000000ffff
  | 0, 1 => 0x3fffe000000000000000000000000000000000000000000000000000000000003ffc0000000000000000000000000000000000000000000000000000000000003ff00000000000000000000000000000000000000000000000000000000000003e0fe00000000000000000000000000000000000000000000000000000000000318c1f8000000000000000000000000000000000000000000000000000000000300c000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x2d6b9ce00000000000000000000000000000000000000000000000000000000029499ca00000000000000000000000000000000000000000000000000000000016b767f00000000000000000000000000000000000000000000000000000000029489800000000000000000000000000000000000000000000000000000000001294631000000000000000000000000000000000000000000000000000000000063240500000000000000000000000000000000000000000000000000000000001f016f000000000000000000000000000000000000000000000000000000000000dada
  | 0, 1 => 0x3ffffb50000000000000000000000000000000000000000000000000000000003ffffb50000000000000000000000000000000000000000000000000000000003ff25250000000000000000000000000000000000000000000000000000000003e0fe9000000000000000000000000000000000000000000000000000000000039cdbfa000000000000000000000000000000000000000000000000000000000380da90
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 14 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 14 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 14 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 14 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 5 0 (NN s)
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_55 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_55 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_55 == dom_55) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_55 goalM u ys) : RunD dom_55 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_55 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 9 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 9 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 9 → Z 5 i = true := z5_0
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
  scr dom_55 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_55 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_55 roots_55 goal_55 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_55 goal_55 := by
    have h0 : isConstB dom_55 goal_55 = false := by decide +kernel
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

end S_55

theorem low_55 : Lower dom_55 roots_55 goal_55 7 := S_55.noCircuit

namespace S_62
def pairsG : List (Nat × Nat) := [(2, 10), (6, 14), (6, 22), (6, 38), (8, 10), (12, 14), (12, 28), (18, 22), (18, 26), (20, 22), (20, 28), (24, 26), (24, 28), (34, 38), (34, 42), (36, 38), (40, 42), (44, 46), (44, 60), (50, 54), (50, 58), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [2, 6, 6, 6, 8, 12, 12, 18, 18, 20, 20, 24, 24, 34, 34, 36, 40, 44, 44, 50, 50, 52, 52, 56, 56]
def r2sG : List Nat := [10, 14, 22, 38, 10, 14, 28, 22, 26, 22, 28, 26, 28, 38, 42, 38, 42, 46, 60, 54, 58, 54, 60, 58, 60]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [8805020341770, 37418629338634, 13203066852874, 22041874270748, 48524945000998, 22016743054358, 26397206386186, 26474751330844]
def xsM : List Nat := roots_62.map (· &&& dom_62)
def goalM : Nat := goal_62 &&& dom_62
def NN : Nat → Nat
  | 3 => 1
  | 4 => 4
  | 5 => 11
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x48adb61c
  | 4, 0 => 0xa91103de8744a4645edf7fd809720071
  | 5, 0 => 0xea0fcbf7e324ca91deee3556c894e17cc2d3007eb197e02ea91103de45028db13a415d321002c7d80ebf8666
  | 6, 0 => 0xa91103de
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x50500000505000000000000000000000000000000000000000000000000000004444444444444444000000000000000000000000000000000000000000000000444444440000000000000000000000000000000000000000000000000000000011111111111111110000000000000000000000000000000000000000000000000505050505050505000000000000000000000000000000000000000000000000005500550055005500000000000000000000000000000000000000000000000000005555000055550000000000000000000000000000000000000000000000000000000055555555
  | 0, 1 => 0x55555555000000000000000000000000000000000000000000000000000000005555444455550000000000000000000000000000000000000000000000000000555500005555000000000000000000000000000000000000000000000000000055005500550055000000000000000000000000000000000000000000000000005050505050505050000000000000000000000000000000000000000000000000505050505050000000000000000000000000000000000000000000000000000050505050000000000000000000000000000000000000000000000000000000005050404050500000
  | 0, 2 => 0x55555555555500000000000000000000000000000000000000000000000000005555555555005500
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x31063
  | 4, 0, 0 => 0x7b58b3281ac51900c49cc80731664
  | 5, 0, 0 => 0x41ac5995ac5980af6b16456b1662abd8b3995ed5984af6b16657b5861ac5ac5995ac5a4caf62cc15
  | 6, 0, 0 => 0xf6b1665
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 19
  | 4 => 29
  | 5 => 29
  | 6 => 29
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 5 0) :: stateWires n (ids >>> 5)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x600600000000000000000000000000000000000000000000000000000000000018618f00000000000000000000000000000000000000000000000000000000001860000000000000000000000000000000000000000000000000000000000001e79e700000000000000000000000000000000000000000000000000000000001997991000000000000000000000000000000000000000000000000000000000078e78f000000000000000000000000000000000000000000000000000000000007e07f0000000000000000000000000000000000000000000000000000000000001fff
  | 0, 1 => 0x1ffe0000000000000000000000000000000000000000000000000000000000001f87f800000000000000000000000000000000000000000000000000000000001f81f800000000000000000000000000000000000000000000000000000000001871870000000000000000000000000000000000000000000000000000000000066866e000000000000000000000000000000000000000000000000000000000066860000000000000000000000000000000000000000000000000000000000006680000000000000000000000000000000000000000000000000000000000000600600
  | 0, 2 => 0x1ffff800000000000000000000000000000000000000000000000000000000001fff870
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x16c16c40000000000000000000000000000000000000000000000000000000000bbebbf0000000000000000000000000000000000000000000000000000000000bbe00800000000000000000000000000000000000000000000000000000000014414400000000000000000000000000000000000000000000000000000000000914911000000000000000000000000000000000000000000000000000000000028a28c000000000000000000000000000000000000000000000000000000000003e03b0000000000000000000000000000000000000000000000000000000000001ff7
  | 0, 1 => 0x1ffe0080000000000000000000000000000000000000000000000000000000001ffffcc0000000000000000000000000000000000000000000000000000000001fc1fc40000000000000000000000000000000000000000000000000000000001d75d7300000000000000000000000000000000000000000000000000000000016eb6ee00000000000000000000000000000000000000000000000000000000016eb6cc00000000000000000000000000000000000000000000000000000000016ea00800000000000000000000000000000000000000000000000000000000016eb6cc
  | 0, 2 => 0x1ffffcc0000000000000000000000000000000000000000000000000000000001fffd7b
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 18 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 18 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 18 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 18 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 5 0) :: stateWiresD n (ids >>> 5)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 5 0) :: stateWiresS n (ids >>> 5)
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 5 0 (NN s)
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

def symsG : List (List (Nat × Nat)) := []
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
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 11 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 11 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 11 → Z 5 i = true := z5_0
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

namespace S_31_32
def pairsG : List (Nat × Nat) := [(32, 33), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (40, 41), (40, 42), (44, 45), (44, 46), (44, 60), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [32, 34, 34, 34, 36, 36, 40, 40, 44, 44, 44, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [33, 35, 38, 42, 37, 38, 41, 42, 45, 46, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x1fffff
def pool6G : List Nat := [39729390955046, 57321576999462, 44127370356266]
def xsM : List Nat := roots_31_32.map (· &&& dom_31_32)
def goalM : Nat := goal_31_32 &&& dom_31_32
def NN : Nat → Nat
  | 4 => 1
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x5f5ce351
  | 5, 0 => 0x5f5ce351
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffff000000000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000aaaaaaaa00000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x46885
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
  | 0, 0 => 0x1ff80000000000000000000000000000000000000000000000000000000000001c07c00000000000000000000000000000000000000000000000000000000000038730000000000000000000000000000000000000000000000000000000000000700e0000000000000000000000000000000000000000000000000000000000000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1ffc0000000000000000000000000000000000000000000000000000000000001e47c8000000000000000000000000000000000000000000000000000000000013a73400000000000000000000000000000000000000000000000000000000000972ae0000000000000000000000000000000000000000000000000000000000049953
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_31_32 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_31_32 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_31_32 == dom_31_32) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_31_32 goalM u ys) : RunD dom_31_32 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_31_32 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_31_32 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_31_32 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_31_32 roots_31_32 goal_31_32 6 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_31_32 goal_31_32 := by
    have h0 : isConstB dom_31_32 goal_31_32 = false := by decide +kernel
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

end S_31_32

theorem low_31_32 : Lower dom_31_32 roots_31_32 goal_31_32 6 := S_31_32.noCircuit

namespace S_61_2
def pairsG : List (Nat × Nat) := [(2, 10), (3, 7), (3, 11), (3, 35), (6, 7), (6, 14), (6, 22), (6, 38), (18, 22), (18, 26), (19, 23), (19, 27), (19, 51), (34, 35), (34, 38), (34, 42), (50, 51), (50, 54), (50, 58)]
def r1sG : List Nat := [2, 3, 3, 3, 6, 6, 6, 6, 18, 18, 19, 19, 19, 34, 34, 34, 50, 50, 50]
def r2sG : List Nat := [10, 7, 11, 35, 7, 14, 22, 38, 22, 26, 23, 27, 51, 35, 38, 42, 51, 54, 58]
def mpG : Nat := 0x7ffff
def pool6G : List Nat := [6610527593223, 37409217775398]
def xsM : List Nat := roots_61_2.map (· &&& dom_61_2)
def goalM : Nat := goal_61_2 &&& dom_61_2
def NN : Nat → Nat
  | 4 => 1
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xf32b5140
  | 5, 0 => 0xf32b5140
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xcccccccc00000000000000000000000000000000000000000000000000000000cccc0000cccc0000000000000000000000000000000000000000000000000000cc00cc00cc00cc00000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c00000000000000000000000000000000000000000000000008888888888888888
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x46885
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
  | 0, 0 => 0x7e0000000000000000000000000000000000000000000000000000000000000071f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f00000000000000000000000000000000000000000000000000000000000001c0e
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x7f0880000000000000000000000000000000000000000000000000000000000071f400000000000000000000000000000000000000000000000000000000000048a2500000000000000000000000000000000000000000000000000000000000245f20000000000000000000000000000000000000000000000000000000000013c1e
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_61_2 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_61_2 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_61_2 == dom_61_2) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_61_2 goalM u ys) : RunD dom_61_2 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_61_2 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_61_2 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_61_2 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_61_2 roots_61_2 goal_61_2 6 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_61_2 goal_61_2 := by
    have h0 : isConstB dom_61_2 goal_61_2 = false := by decide +kernel
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

end S_61_2

theorem low_61_2 : Lower dom_61_2 roots_61_2 goal_61_2 6 := S_61_2.noCircuit

namespace S_15_48
def pairsG : List (Nat × Nat) := [(48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x3ff
def pool6G : List Nat := [57390296480310]
def xsM : List Nat := roots_15_48.map (· &&& dom_15_48)
def goalM : Nat := goal_15_48 &&& dom_15_48
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x8a5bc14c
  | 4, 0 => 0x8a5bc14c
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000cccc000000000000000000000000000000000000000000000000000000000000aaaa000000000000
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
  | 0, 0 => 0x3800000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3c80000000000000000000000000000000000000000000000000000000000000274000000000000000000000000000000000000000000000000000000000000012e0000000000000000000000000000000000000000000000000000000000000093
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_15_48 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_15_48 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_15_48 == dom_15_48) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_15_48 goalM u ys) : RunD dom_15_48 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_15_48 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_15_48 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_15_48 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_15_48 roots_15_48 goal_15_48 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_15_48 goal_15_48 := by
    have h0 : isConstB dom_15_48 goal_15_48 = false := by decide +kernel
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

end S_15_48

theorem low_15_48 : Lower dom_15_48 roots_15_48 goal_15_48 5 := S_15_48.noCircuit

namespace S_23
def pairsG : List (Nat × Nat) := [(3, 7), (5, 7), (5, 21), (6, 7), (6, 22), (17, 21), (18, 22), (19, 23), (20, 21), (20, 22)]
def r1sG : List Nat := [3, 5, 5, 6, 6, 17, 18, 19, 20, 20]
def r2sG : List Nat := [7, 7, 21, 7, 22, 21, 22, 23, 21, 22]
def mpG : Nat := 0x3ff
def pool6G : List Nat := [6618881594631]
def xsM : List Nat := roots_23.map (· &&& dom_23)
def goalM : Nat := goal_23 &&& dom_23
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x678b910d
  | 4, 0 => 0x678b910d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000cc00cc0000000000000000000000000000000000000000000000000000000000aa00aa
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
  | 0, 0 => 0x3e0000000000000000000000000000000000000000000000000000000000000031e00000000000000000000000000000000000000000000000000000000000000d900000000000000000000000000000000000000000000000000000000000000a7
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3f400000000000000000000000000000000000000000000000000000000000003ff00000000000000000000000000000000000000000000000000000000000002db00000000000000000000000000000000000000000000000000000000000001af
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_23 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_23 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_23 == dom_23) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_23 goalM u ys) : RunD dom_23 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_23 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_23 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_23 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_23 roots_23 goal_23 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_23 goal_23 := by
    have h0 : isConstB dom_23 goal_23 = false := by decide +kernel
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

end S_23

theorem low_23 : Lower dom_23 roots_23 goal_23 5 := S_23.noCircuit

namespace S_45_2
def pairsG : List (Nat × Nat) := [(2, 10), (3, 7), (3, 11), (3, 35), (6, 7), (6, 14), (6, 38), (34, 35), (34, 38), (34, 42)]
def r1sG : List Nat := [2, 3, 3, 3, 6, 6, 6, 34, 34, 34]
def r2sG : List Nat := [10, 7, 11, 35, 7, 14, 38, 35, 38, 42]
def mpG : Nat := 0x3ff
def pool6G : List Nat := [6610527593223]
def xsM : List Nat := roots_45_2.map (· &&& dom_45_2)
def goalM : Nat := goal_45_2 &&& dom_45_2
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xa6268017
  | 4, 0 => 0xa6268017
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xcccc000000000000000000000000000000000000000000000000000000000000cc000000cc000000000000000000000000000000000000000000000000000000c0c00000c0c00000000000000000000000000000000000000000000000000000888800008888
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
  | 0, 0 => 0x38000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000000e
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3c800000000000000000000000000000000000000000000000000000000000002250000000000000000000000000000000000000000000000000000000000000172000000000000000000000000000000000000000000000000000000000000009e
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_45_2 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_45_2 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_45_2 == dom_45_2) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_45_2 goalM u ys) : RunD dom_45_2 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_45_2 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_45_2 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_45_2 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_45_2 roots_45_2 goal_45_2 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_45_2 goal_45_2 := by
    have h0 : isConstB dom_45_2 goal_45_2 = false := by decide +kernel
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

end S_45_2

theorem low_45_2 : Lower dom_45_2 roots_45_2 goal_45_2 5 := S_45_2.noCircuit

namespace S_53_2
def pairsG : List (Nat × Nat) := [(3, 7), (3, 35), (6, 7), (6, 22), (6, 38), (18, 22), (19, 23), (19, 51), (34, 35), (34, 38), (50, 51), (50, 54)]
def r1sG : List Nat := [3, 3, 6, 6, 6, 18, 19, 19, 34, 34, 50, 50]
def r2sG : List Nat := [7, 35, 7, 22, 38, 22, 23, 51, 35, 38, 51, 54]
def mpG : Nat := 0xfff
def pool6G : List Nat := [37409217775398, 6610527393287]
def xsM : List Nat := roots_53_2.map (· &&& dom_53_2)
def goalM : Nat := goal_53_2 &&& dom_53_2
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xf53251d
  | 4, 0 => 0xf53251d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xcc00cc0000000000000000000000000000000000000000000000000000000000cc000000cc000000000000000000000000000000000000000000000000000000c000c000c000c00000000000000000000000000000000000000000000000000088008800880088
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
  | 0, 0 => 0xf000000000000000000000000000000000000000000000000000000000000000ce0000000000000000000000000000000000000000000000000000000000000001c00000000000000000000000000000000000000000000000000000000000000c3
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xf920000000000000000000000000000000000000000000000000000000000000ce80000000000000000000000000000000000000000000000000000000000000a7d00000000000000000000000000000000000000000000000000000000000005c7
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_53_2 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_53_2 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_53_2 == dom_53_2) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_53_2 goalM u ys) : RunD dom_53_2 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_53_2 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_53_2 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_53_2 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_53_2 roots_53_2 goal_53_2 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_53_2 goal_53_2 := by
    have h0 : isConstB dom_53_2 goal_53_2 = false := by decide +kernel
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

end S_53_2

theorem low_53_2 : Lower dom_53_2 roots_53_2 goal_53_2 5 := S_53_2.noCircuit

namespace S_30_32
def pairsG : List (Nat × Nat) := [(34, 38), (34, 42), (36, 38), (40, 42), (44, 46), (44, 60), (50, 54), (50, 58), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [34, 34, 36, 40, 44, 44, 50, 50, 52, 52, 56, 56]
def r2sG : List Nat := [38, 42, 38, 42, 46, 60, 54, 58, 54, 60, 58, 60]
def mpG : Nat := 0xfff
def pool6G : List Nat := [57321576999462, 44127370356266]
def xsM : List Nat := roots_30_32.map (· &&& dom_30_32)
def goalM : Nat := goal_30_32 &&& dom_30_32
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x4b5c3f1e
  | 4, 0 => 0x4b5c3f1e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x5555000000000000000000000000000000000000000000000000000000000000550055000000000000000000000000000000000000000000000000000000000050505050000000000000000000000000000000000000000000000000000000004444444400000000
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
  | 0, 0 => 0xfc00000000000000000000000000000000000000000000000000000000000000c38000000000000000000000000000000000000000000000000000000000000033400000000000000000000000000000000000000000000000000000000000000c3
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfe00000000000000000000000000000000000000000000000000000000000000eba0000000000000000000000000000000000000000000000000000000000000b7500000000000000000000000000000000000000000000000000000000000005df
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_30_32 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_30_32 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_30_32 == dom_30_32) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_30_32 goalM u ys) : RunD dom_30_32 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_30_32 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_30_32 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_30_32 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_30_32 roots_30_32 goal_30_32 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_30_32 goal_30_32 := by
    have h0 : isConstB dom_30_32 goal_30_32 = false := by decide +kernel
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

end S_30_32

theorem low_30_32 : Lower dom_30_32 roots_30_32 goal_30_32 5 := S_30_32.noCircuit

namespace S_15
def pairsG : List (Nat × Nat) := [(2, 10), (3, 7), (3, 11), (5, 7), (5, 13), (6, 7), (6, 14), (8, 10), (9, 11), (9, 13), (12, 13), (12, 14)]
def r1sG : List Nat := [2, 3, 3, 5, 5, 6, 6, 8, 9, 9, 12, 12]
def r2sG : List Nat := [10, 7, 11, 7, 13, 7, 14, 10, 11, 13, 13, 14]
def mpG : Nat := 0xfff
def pool6G : List Nat := [5506283145735, 5510594890247, 6618746784263]
def xsM : List Nat := roots_15.map (· &&& dom_15)
def goalM : Nat := goal_15 &&& dom_15
def NN : Nat → Nat
  | 3 => 2
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xaf8140c7a8d11512
  | 4, 0 => 0xa8d11512
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000cccc000000000000000000000000000000000000000000000000000000000000aaaa000000000000000000000000000000000000000000000000000000000000a0a0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x11038d14
  | 4, 0, 0 => 0x8d14
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
  | 0, 0 => 0xf800000000000000000000000000000000000000000000000000000000000000c780000000000000000000000000000000000000000000000000000000000000067000000000000000000000000000000000000000000000000000000000000031e0000000000000000000000000000000000000000000000000000000000000018
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfd50000000000000000000000000000000000000000000000000000000000000e7a00000000000000000000000000000000000000000000000000000000000009ef000000000000000000000000000000000000000000000000000000000000073e000000000000000000000000000000000000000000000000000000000000063a
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_15 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_15 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_15 == dom_15) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_15 goalM u ys) : RunD dom_15 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_15 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_15 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_15 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_15 roots_15 goal_15 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_15 goal_15 := by
    have h0 : isConstB dom_15 goal_15 = false := by decide +kernel
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

end S_15

theorem low_15 : Lower dom_15 roots_15 goal_15 5 := S_15.noCircuit

def isoMv_62_1 : List (Nat × Nat) := [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]
theorem low_62_1 : Lower dom_62_1 roots_62_1 goal_62_1 6 :=
  lower_iso isoMv_62_1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_61_2

def isoMv_29 : List (Nat × Nat) := [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]
theorem low_29 : Lower dom_29 roots_29 goal_29 5 :=
  lower_iso isoMv_29 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23

def isoMv_57_4 : List (Nat × Nat) := [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]
theorem low_57_4 : Lower dom_57_4 roots_57_4 goal_57_4 5 :=
  lower_iso isoMv_57_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_53_2

def isoMv_30_1 : List (Nat × Nat) := [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]
theorem low_30_1 : Lower dom_30_1 roots_30_1 goal_30_1 5 :=
  lower_iso isoMv_30_1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_53_2

def isoMv_46_1 : List (Nat × Nat) := [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]
theorem low_46_1 : Lower dom_46_1 roots_46_1 goal_46_1 5 :=
  lower_iso isoMv_46_1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_45_2

def isoMv_58_4 : List (Nat × Nat) := [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]
theorem low_58_4 : Lower dom_58_4 roots_58_4 goal_58_4 5 :=
  lower_iso isoMv_58_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_53_2

def isoMv_39 : List (Nat × Nat) := [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]
theorem low_39 : Lower dom_39 roots_39 goal_39 5 :=
  lower_iso isoMv_39 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

namespace S_63
def pairsG : List (Nat × Nat) := [(1, 33), (2, 10), (3, 7), (3, 11), (3, 35), (5, 7), (5, 13), (5, 21), (5, 37), (6, 7), (6, 14), (6, 22), (6, 38), (8, 10), (9, 11), (9, 13), (9, 41), (12, 13), (12, 14), (12, 28), (17, 21), (17, 49), (18, 22), (18, 26), (19, 23), (19, 27), (19, 51), (20, 21), (20, 22), (20, 28), (24, 26), (24, 28), (25, 27), (25, 29), (25, 57), (32, 33), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (40, 41), (40, 42), (44, 45), (44, 46), (44, 60), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 2, 3, 3, 3, 5, 5, 5, 5, 6, 6, 6, 6, 8, 9, 9, 9, 12, 12, 12, 17, 17, 18, 18, 19, 19, 19, 20, 20, 20, 24, 24, 25, 25, 25, 32, 34, 34, 34, 36, 36, 40, 40, 44, 44, 44, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [33, 10, 7, 11, 35, 7, 13, 21, 37, 7, 14, 22, 38, 10, 11, 13, 41, 13, 14, 28, 21, 49, 22, 26, 23, 27, 51, 21, 22, 28, 26, 28, 27, 29, 57, 33, 35, 38, 42, 37, 38, 41, 42, 45, 46, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0xffffffffffffff
def pool6G : List Nat := [6610527592711, 9904279324426, 9917130475277, 9917399632397, 9921459193610, 5510594890503, 8809062663946, 13233735932941, 13207109175050, 5510863849991, 6610527593223, 22063819923733, 22011809498901, 48404434586150, 48417739251981, 8805020341770, 26397206386186, 6618746784263, 6619217857031, 22024677559580, 22041857428764, 35188770211617, 9908574291722, 61796562373148, 37409217644326, 22011910556949, 37409318309158, 22016087623446, 57196819516693, 26465673217802, 19825906423306, 26465925862922, 13216455395853, 22016743054358, 57200527608358, 22064188693525, 37409251198758, 13219994076938, 39608274454310, 57200460498726, 43989929301514, 37418629338634, 37387793467169, 6618881594631, 48524692359718, 37409486083622]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_63 &&& dom_63
def NN : Nat → Nat
  | 4 => 2
  | 5 => 14
  | 6 => 107
  | 7 => 389
  | 8 => 227
  | 9 => 27
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x3e979b5017b42a42
  | 5, 0 => 0xfd2cb01fe9af5f4ee5c254cee460028ad8f80e79b2149d6b84f8298b78541dd672d0ffe04eb8c479474517e01d72b6530b36f6d90058ccbe
  | 6, 0 => 0xa3c12202a306cbaaa1822dd7a08748f29f7d99be9f59250e9e1b117199aeb74592314b3491d2873e8d47c0e48c65bcd58b33922d8729ea2b8250d0be7bfeb7897b28099b7a9edee0734bd99471acb9636f9408c46f7ca6206ecfff346a8772f96986825464f3d1b763f5006b614722226118463c5fa1771b5e2f68925e2d8aab5e2c2c165c7c3c6a5a51a85d53b44d124c688a9d47fc363747dbde103c86b61d38c8eb4e37dcf20736bd7d743492314e2d78614d2d1055ac2c22e3092a7bd19529f1c6ed2779c54f1f589cb415a661140d3173090b1f72c00a516e2c09d65bad0914f67308f317a506e4336304773d4504077934036e95b70316892b02291043
  | 6, 1 => 0xfd1d4291fb39c754fac1864cf8745fd1f6bf844df548b52cf4437d94f3d6a6a3efced257eca992adea635f01e85d85b9e64569a2e580cb8ae246f27ae20fc8aee08b4c69dbe7812edb91cf32d4e034e8d2c818d1d181366dcf8e049ecf88cc23ce112c9dcc64bb85cb5a385fc8e131a8c8bf894dc4e6c501c247cfacc0f5e299c008db81bf9904feb9318e1bb914bc42b53ec163b5041020b254f826aae91467a7005ac4a5e385d9a4f0fefc
  | 7, 0 => 0x2d28c7b32ce139a22cadc4612b0fca262afe09d52af8e8dd2a56170029259dd728b1318527795cd1276fb0f926f168c92648e3a8232c6add229eb02f22986b9622480f69204fb0ae1ea663541de177831c96ea491c10e1eb1afecaa01a25944819f37e0719dc1ae919ba301a181c7acd17e4d13d17c5c22e16995adb153fc09e14e907ff1488e2b213aad82f12ff4241117804a41161181a1020e5be0fcb33c20f7093b80f16fff20ee2d2210e05ccb20d570f570d40e0e10b9beb890b88cc090b2c8ce60b2912830a7677f5096433860919997807ca96c507073daf04ccdfdc04963a7b048faf4c0442bd86042d77d502363de20166035700d76e02002d875e
  | 7, 1 => 0x5462936b540a4dbd53dd4ed0539201445372c4795318541d52a2b541506b190f4e3a3a904dc8be514db8aa404d84259f4d2ff4d14d1a0f054b50406a4b25a97b4aeba8ec49e125c649c3e2a949bb2fc347b76ea347703dcb46f1b31146c7cf0745f28fa645a7f598457ae3f04458f2e54408d56743c1fcc9433cb82e412c1b383f3bf5403e0fc03d3d4e5b033d2c7c353cedc83e3c21f90f3b40a23f3b05d6f73a8512d9390ed69f3888964038695c3f37b018593791ff6b374fedbb36b521a2364691d836273865345154f533cd017f338d060c330f905c3241f7723241705c31fd931f30a9d7c9309ade1b2f653d432e9b5e9e2dcb18752d70ced82d451862
  | 7, 2 => 0x7c1542a07bd0c6937b66491479c219c9796fc1e1791c125477ae3ab077abf413779c985d778509c27677af7c761d3e0674cf39e47406feac73de49db73437dc2730c5ff871c52b6a710cff026ee8713b6ecfcc7c6ec7a3626df7e42c6dbbe1966d024fde6c64553c6c0188046b302ff16a610cd96a27cc6b6921832768fa0825689b990367d50da7678524796732258166e4732066b2ba9b6625b9e96413866e640f62e36407b8f162c7c6f4627050f960fe5bb260afae3b60ad45a25f991b495f26c7b65ecd913b5e13ada65dd08b735d71535d5b8c3f8e5b34bf745a7ee5485931d5e859254669582291a25810d46d578d26c056488c3a54a96c0954a00c23
  | 7, 3 => 0xaabd8836aa904610a9efcd79a994b72fa7cfd832a7853e24a5ed4e39a5141b3ba0d050949ec0d7899e4021fd9db654639cd4fd939cbb54e09c9a324b9ba5785f9b5bed5b9b3d4dac9966843499265abf98f4208d982e64fb9823da6497d806639742e105970d4168969645529595a4cf958086b29551aacc9520bde994a83048945c0e2c91ed9b59919a80f8903733998f6e24048f5f73c98f052a2c8ed973b68b27f4e18a516cc3894cf98588e0387f88ceb15587f2d3ba87edb1a287de9c8a879add6783ea69c5836211778317fdaf8265c20c817106db814d04b780d909847f75d2d77f6323277e9aa7927dc60fd37d45306b7cfbabd27c6664907c4c7c10
  | 7, 4 => 0xd67aeb44d5bb9267d46c70aad3b6fe4ed3a84f1fd3801716d3295e77d282ff82d0ad1508cbedcfe9cb5a385fcb08702ac96968fbc934441dc8205f4fc7b46166c7a4d130c72a74d0c5e5017dc5ae265bc5a7e1c2c50c7b54c4ef24d3c4d7a737c4d20e6dc4a50f80c3432490c28877b3c1980f89c1041042bfa659cfbebb555abd209ae2bcc91ac8bc1a5d6dbc042ef7bbf021b9bab9a1bdba86b3c0ba33995fb9218214b8a185a6b7f92244b7dce78eb764087ab5f6eebfb5dd345bb5bed785b5446adbb413f1b2b40478deb1ff7463b191d7e7b06379a0b017831cafaab267af647c31af616e2bae1abeb8acba04cfac71715eab79c6cbab583dfdaae6feaf
  | 7, 5 => 0xfdf6b6b9fcf048affc465d48fbf342e7fbccf7fafbba9a94fb03a34bf9b835b8f9aef702f7f1aadbf72a0023f681b3f2f63c8b9cf4a631d0f377c984f318916ef2000644f0f8df95efafc882eda593bbed4e20d2eca5df3cec3462fdebefca4beba5c6a6eba28a2aeae79972ea630ca9e9e0e609e9bbe516e849f352e8027d18e74be456e5dbe277e5b9b349e5786fb8e52d0e51e4893a20e37abf1ee2f6af66e2d732e2e24a45f5e1760161e0f77e7be04445eee041dc16dff3a4ccde900726de8141e7dd6521e7dc5112fbdb93cc5bdb711277db56751ddb4f33a9da650bedda1cea69d9288e6bd9196516d8c3dd20d7fa8692d7f9e631d740303ad6d35949
  | 7, 6 => 0xffcf0a7cff939cefff6c71b0ff231777fecffd16
  | 8, 0 => 0x3a8b9b213a3129ab387c22163732d33a36e4026d366fa272359f67e734064f6c330961a6317141fd3129ad3f302ca7772f7655c82e9e70832de85b922d90db782d6df75a2cb7e2692ba0a43a2b81626d2b0f56702a6cf07129e942c428a4a83e2774c4602705880d26beaf6f26396ad423e92d1223afce9222c7351321e9d24d20df43cc20292edb2014c6441e3d0e221d81c57f1c1ffead1b8548e619b1d448196672e11923eb0b17d6fff416e8db1816b50ee91581f8c8153eaa1812baa677124e26351198114410c280c50faa77070f8898390e7e15130e783ebe0d9cbe430d61f2fb0d52c9a60c6d390f0c22507d09ee1b6f0762c30706291d8300273479
  | 8, 1 => 0x7e1a8a567dfd47397db173387d356db97bf0d3337b2b17a17ab2c9087a2bf43679e15a28798a90b2789257757770373f7540089873f60c3a72b2833970cdf074705b5d9f6f6c29a26ebe77696e834bca6db8095f6d483b2f6bcb63fb6a7ff66869c0add467f1c0d367044c4c6449b75d63353df461ca400861aa33685f492eb65dc82fa15d3a46645ba915895b2acd595aa8a6b9568173f9564030685550fad054c1de10523dc21151bf3f2b51099cc65038abd6500139404fb2394c4f717d1d4f57c7d64e2ce2974c1e35cd4bff26be4bb8974e4a6707154a3f78dc49e125c649226c8f48c2474243a9f848434ac0323d6d0b963c21f90f3b5624293afd7b25
  | 8, 2 => 0xd697c1d4d1efb8f3d17f337bcf9551ebcea2794ccd5fbf4fcbfcbae9cb46a5f8c8d8951dc5d3e588c33e8ebcbf01fb40beb2f988be907f01be4be64fbde1cfb5bd199d0fbc545819bc18011aba45dd7fb837fe7bb272f2abb253eee6b0e1dcffabbe6e52aab1140caa56a296a98c5b5da8d69abba840633ca817ae6ba77ce252a494c22fa309310c9db654639d3508f49d2d50bb9b1dd7b09aec1f2b9ab47d5a99ed5e879985b80798411d8197ec88bb9710a45897012b8493f42b8d93602c469117715e8f6e24048e7679718e35cdb08d5eaaf98ce2cfc48bc68b508a81f0ca877910e28651842c8492c7cd82739f2081bd8a2f7f5f0e0b7ecd8d627ebbf601
  | 8, 3 => 0xffcceadcffa13466ff939ceffce2758bfc3e0176fbefb591fb192d73fac274d4f9824cb5f6e94291f3dfbe5ff1027f58f053c1fdf03d9387eef3064dee6cfdefed5ae6a4ec164c1eeabec0cdeaa64cb1e9b38944e73f702ce6e4feb6e606f433e48a3599e3d420a8e21fca1de1ccafbce0f3695fdfb32b5bdf91a28ddec9aaa0dd547ea2da26b2c9d96359b3
  | 9, 0 => 0xf33b5fd0f2854adfd1efb8f3c2afde01b47be621a1f16def9b34b1218a7994f87e1a8a567cea112d76f0de33705b5d9f61ca40085fbac6fd5e22a7545cde0cce51bb2a0f5059633d4aee737942b779a33e277fff34064f6c2efbd9641b78d4bc1b1e63461606144c0e7e1513
  | 10, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f00000f0f000000000000000000000000000000000000000000000000000000000ffffffff00000000000000000000000000000000000000000000000000000000eeeeeeee00000000000000000000000000000000000000000000000000000000555555550000000000000000000000000000000000000000000000000000000033ff33ff0000000000000000000000000000000000000000000000000000000033333333000000000000000000000000000000000000000000000000000000000fff0fff0000000000000000000000000000000000000000000000000000000000ff00ff
  | 0, 1 => 0xcc00cc00cc00cc00000000000000000000000000000000000000000000000000aa00aa00aa00aa0000000000000000000000000000000000000000000000000077007700770077000000000000000000000000000000000000000000000000005f005f005f005f0000000000000000000000000000000000000000000000000055005500550055000000000000000000000000000000000000000000000000003f003f003f003f00000000000000000000000000000000000000000000000000330033003300330000000000000000000000000000000000000000000000000000ffff0000ffff
  | 0, 2 => 0xf0f3f3f0f0f3f3f0000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f000000000000000000000000000000000000000000000000070777770707777700000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000ff00ff00ff000000000000000000000000000000000000000000000000000000ff00ff00aa00aa00000000000000000000000000000000000000000000000000ff00aa00ff00aa00000000000000000000000000000000000000000000000000f000f000f000f0
  | 0, 3 => 0x1f1f1f1f1f1f1f1f000000000000000000000000000000000000000000000000115511551155115500000000000000000000000000000000000000000000000011111111111111110000000000000000000000000000000000000000000000000f5f0f5f0f5f0f5f0000000000000000000000000000000000000000000000000f3f0f3f0f3f0f3f0000000000000000000000000000000000000000000000000f1f0f1f0f1f0f1f0000000000000000000000000000000000000000000000000f0f7f7f0f0f7f7f0000000000000000000000000000000000000000000000000f0f5f5f0f0f5f5f
  | 0, 4 => 0x55555555555555550000000000000000000000000000000000000000000000005500550055005500000000000000000000000000000000000000000000000000505050505050505000000000000000000000000000000000000000000000000044444444444444440000000000000000000000000000000000000000000000003333333333333333000000000000000000000000000000000000000000000000330033003300330000000000000000000000000000000000000000000000000030303030303030300000000000000000000000000000000000000000000000002222222222222222
  | 0, 5 => 0xaa88aa88aa88aa88000000000000000000000000000000000000000000000000aa55aa55aa55aa55000000000000000000000000000000000000000000000000aa00faf0aa00faf0000000000000000000000000000000000000000000000000aa00aa00aa00aa00000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a000000000000000000000000000000000000000000000000099999999999999990000000000000000000000000000000000000000000000008888f8f88888f8f80000000000000000000000000000000000000000000000008888888888888888
  | 0, 6 => 0xcc88cc88cc88cc88000000000000000000000000000000000000000000000000cc33cc33cc33cc33000000000000000000000000000000000000000000000000cc00fcf0cc00fcf0000000000000000000000000000000000000000000000000cc00cc00cc00cc00000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000000bbaabbaabbaabbaa000000000000000000000000000000000000000000000000aafaaafaaafaaafa000000000000000000000000000000000000000000000000aaaaaaaaaaaaaaaa
  | 0, 7 => 0xeac0eac0eac0eac0000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e0000000000000000000000000000000000000000000000000e0c0e0c0e0c0e0c0000000000000000000000000000000000000000000000000e0a0e0a0e0a0e0a0000000000000000000000000000000000000000000000000ddccddccddccddcc000000000000000000000000000000000000000000000000cf0fcf0fcf0fcf0f000000000000000000000000000000000000000000000000cccccccccccccccc000000000000000000000000000000000000000000000000cccccccc88888888
  | 0, 8 => 0xf000f000f000f000000000000000000000000000000000000000000000000000eeeeeeeeeeeeeeee000000000000000000000000000000000000000000000000eeeeeeee00000000000000000000000000000000000000000000000000000000eecceecceecceecc000000000000000000000000000000000000000000000000eeaaeeaaeeaaeeaa000000000000000000000000000000000000000000000000ecececececececec000000000000000000000000000000000000000000000000eca0eca0eca0eca0000000000000000000000000000000000000000000000000eaeaeaeaeaeaeaea
  | 0, 9 => 0xf0f0a0a0f0f0a0a0000000000000000000000000000000000000000000000000f0f0a000f0f0a000000000000000000000000000000000000000000000000000f0f08080f0f08080000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000f0e0f0e0f0e0f0e0000000000000000000000000000000000000000000000000f0c0f0c0f0c0f0c0000000000000000000000000000000000000000000000000f0a0f0a0f0a0f0a0000000000000000000000000000000000000000000000000f080f080f080f080
  | 0, 10 => 0xfaf0aa00faf0aa00000000000000000000000000000000000000000000000000faaafaaafaaafaaa000000000000000000000000000000000000000000000000f8f88888f8f88888000000000000000000000000000000000000000000000000f888f888f888f888000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000f0f0f000f0f0f000000000000000000000000000000000000000000000000000f0f0c0c0f0f0c0c0000000000000000000000000000000000000000000000000f0f0c000f0f0c000
  | 0, 11 => 0xffa0ffa0ffa0ffa0000000000000000000000000000000000000000000000000ff88ff88ff88ff88000000000000000000000000000000000000000000000000ff44ff44ff44ff44000000000000000000000000000000000000000000000000ff00ff00ff55ff55000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000ff00ff00aa00aa00000000000000000000000000000000000000000000000000fcf0cc00fcf0cc00000000000000000000000000000000000000000000000000fcccfcccfcccfccc
  | 0, 12 => 0xffeeffeeffeeffee000000000000000000000000000000000000000000000000ffe0ffe0ffe0ffe0000000000000000000000000000000000000000000000000ffccffccffccffcc000000000000000000000000000000000000000000000000ffccffccaa88aa88000000000000000000000000000000000000000000000000ffccaa88ffccaa88000000000000000000000000000000000000000000000000ffc0ffc0ffc0ffc0000000000000000000000000000000000000000000000000ffaaffaaffaaffaa000000000000000000000000000000000000000000000000ffaacc88ffaacc88
  | 0, 13 => 0xffffcc00ffffcc00000000000000000000000000000000000000000000000000ffffaaaaffffaaaa000000000000000000000000000000000000000000000000ffffaa88ffffaa88000000000000000000000000000000000000000000000000ffffaa00ffffaa00000000000000000000000000000000000000000000000000ffff8888ffff8888000000000000000000000000000000000000000000000000ffff0000ffff0000000000000000000000000000000000000000000000000000fff0ffc0fff0ffc0000000000000000000000000000000000000000000000000fff0ffa0fff0ffa0
  | 0, 14 => 0xffffffff33003300000000000000000000000000000000000000000000000000ffffffff22222222000000000000000000000000000000000000000000000000ffffffff11111111000000000000000000000000000000000000000000000000ffffffff00aa00aa000000000000000000000000000000000000000000000000ffffffff00000000000000000000000000000000000000000000000000000000ffffff00ffffff00000000000000000000000000000000000000000000000000ffffccccffffcccc000000000000000000000000000000000000000000000000ffffcc88ffffcc88
  | 0, 15 => 0xfffffffff000f000000000000000000000000000000000000000000000000000ffffffffeeeeeeee000000000000000000000000000000000000000000000000ffffffffcccccccc000000000000000000000000000000000000000000000000ffffffffcc00cc00000000000000000000000000000000000000000000000000ffffffffaaaaaaaa000000000000000000000000000000000000000000000000ffffffffaa00aa00000000000000000000000000000000000000000000000000ffffffff88888888000000000000000000000000000000000000000000000000ffffffff55005500
  | 1, 0 => 0xffffffffffff0000000000000000000000000000000000000000000000000000ffffffffffccffcc000000000000000000000000000000000000000000000000ffffffffffaaffaa000000000000000000000000000000000000000000000000ffffffffff00ff00000000000000000000000000000000000000000000000000fffffffff0f0f000000000000000000000000000000000000000000000000000fffffffff0f08080
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x73594a2747359301b4
  | 5, 0, 0 => 0x736a532e235736a392e165736a4a413056a533630065734c4a34275734c34301b573655953275736a5b2a1650073594a304736a3630165735b53461557361575323573555346145736a5336275
  | 6, 0, 0 => 0x736a3430160965b534628080667365534c34276736a532c230b600734c4a34305756a5b393016673534a3430086736f5b39271667f6a5b53272365b5327230806673534628140866a61532c23066736a462816146735b5339353067353392714076736a392c160b6
  | 6, 0, 1 => 0x736a61533f396805b534d393067f5b533023086736a5b3a39276735b4339160866553343008066735b5350392766a5b533023056735b595339276736a625239306733023161408600736a533630573555339301467361534c2c236736a655341306735b4e3933306
  | 6, 0, 2 => 0x6a53272314066735b534339076735b2723160867361532c23086736a624939306736a5f4a39306736a612c231665339271408066735b533930156735330231407673655334270867c5b534c39276736a653427166736c5b30231667361392c1608600736a5b532a5
  | 6, 0, 3 => 0x73534c27231467c6a5b3927166735b5327230765b534c39300366f5b533927066734c4a39301466a533930140566a53462814066736a5334301b6735b462816086736a4a34302b6736153392c076736a5b391e16673534d39301466b5339301406600735b5553465
  | 6, 0, 4 => 0x735b534e30236736a5b39301a6816a5b533023673534c462814673706153392c6735b5346280766a533430090660073655953305736a534a342766a5b533023016735b4c39301b67365343016086735b575330236736d6553343067c5b533927086735b3a3930086
  | 6, 0, 5 => 0x7353272314086786a5b5327236736a2723161466a5b3930160365b534339080667365533430076735b4c4a39276736a5334270967339271614086786a5b3927166735b533930196735b4c39301f600736a53392e5735b5339302965330231408066736a532723146
  | 6, 0, 6 => 0x736a5b281d166734c3e3930146735b5339302d67f5b5339270866a655334270666c5b5330230667c5b3930160866153392c080660073615753395736b393016146756a5b5327236
  | 7, 0, 0 => 0x73726a5b5346287736a61393016147006a5b534628066736a535139301470073393016140867b736a533023147736a5b532725237736a615b4639167736a5b5453393076a533930140e067735b53392723087736a5b5339300c7736a5b534f39277736a5b3927231675b5346393008067736a5b392726167
  | 7, 0, 1 => 0x736a5b39342716700735b534c27236736a5b532726237736a533930141376a5b53463023067006a5b53464528600735b4c4a3930600736a533430096736a5b5327231476a533930140f067006a5b533930056736153393014087735b53473023087735b534a3930087736a5b534b39307736a655334302f7
  | 7, 0, 2 => 0x73655b534c39277736a39302716147736a61533023147736a5b534a30237007353302314086735b534c302314785736a533023147736a5b5139302b7736a5b463927167735b5339302c07700736a302316146735e5b533930087736a5b533e39277735b53393427087736b5b533930147736a5e5b3930167
  | 7, 0, 3 => 0x73534c3930140e7736a5b393016097007f5b533930086736a533927140f773726a5f5339307006a65533430066736553393014087735339302814087736a65534a34307736a65393016147736a5b53523927782735b533927087736a39302816147735339302714087736a5b493933307736a53493930147
  | 7, 0, 4 => 0x73716a5b392716782736153393008777736a5b5330237736a53302723147736a5b30232216700735b534c4628600735b534339086726a5339301406700736c5b393016685736a5b5343397736a5b53433c39700736a5b4339166615b53393008067716a5b533023067736a5b53462723783736a5b5330237
  | 7, 0, 5 => 0x6a615b53302306700736f5b3930166007f6a5b5330236005b53302308066736a5b3930160b700736a5b5327236736a5b53302523773726a5b30231677d735b533927087736a5b53392721773625b533930087736a685b533930773534c3930140f782736a5b5327237007353393014076735339333014087
  | 7, 0, 6 => 0x655b53393008067736a655b533927773716a5b53272375b5339302808067736a615b3927167735339302b1408700736a65533427682736a615330237736a5b53513927700735b39271608600736c5b53302367b736a5b532723700736153392c0865b533930270806773533930141008700736a61392c166
  | 7, 0, 7 => 0x6a5b53302723067736a53393014117736a53302314107007365534c34306736a605b533930700736a5b4b39306735b39302316087736a5b5330230b773726a533927147736a5f533930147736a5b565330237006a53392714066735b39301614087736a53403930147736e6a3930161477d736a5b5327237
  | 7, 0, 8 => 0x736a5b534939277736e6a533023147736a5b533c39307736a5b30231614700736b5b39301666a655b533023067736a615b53272376a533930231406774736a53393014700735b532723086736f5b533930277736a53302b2314785736a5b532723700736a5b272316600736a61532c236736a5c5b5339307
  | 7, 0, 9 => 0x736a5339272514773615b534c30237736a5b533d39307736a5339301412773655b533927087736a5b532723217735b39343016087736a5b534f30237736a5b53463e287736a655b3927167736a5b533927107736a615339372c7736a645b53393076a5b53302320067735b53302314087736c5b533933307
  | 7, 0, 10 => 0x6a534639301406773533930140e08700736a5b53391e6736a393016140e7726a5b533927067736a615339332c7736a5b5339300d7736a5b5343392b700735b595339306736a5b39272416700735b4c3e39306735b46393016087736a5b533930177736a5b443930167735b533e39300877a736a5b5330237
  | 7, 0, 11 => 0x735b535039306736a5b463023167735b53393014077736a5b533e30237736a393016140f7736a665b5339307736a615349392c700735b534628086736a5b533b39277736a655b5327237736a533927231470073534c392714600736a5b4628166736a5b58533927700735b533927076735b53393327087
  | 7, 0, 12 => 0x6a5b533930016736a695b53393077b736a65533430773534c393023147736a533023140e7736a5b5339301875b5339302c08067735b53393023077736a534a39301476e6a5b533023067736a5d5b5339277736a533927140b700735b575339306735b534c3027237736f5b5339302b773533930140f087
  | 7, 0, 13 => 0x735b533934300776a5b53302c230676a5b53392714067736a5b4a39302b7736a615b5330237716a53393014067736a5346392714783736a53393014779736a533930147736a5e533930147736a5b535230237007c6a5b533927682735b53302308773726a62533930700736a5b3a39306736e6a5b3927167
  | 7, 0, 14 => 0x736e6a5b532723700735b534e39306735b5346393007782736a53392714773615b39301608700736553343008673716a5b3023167736a5b43393016700816a5b53393066a5b5339272306785736a6553343077b735b533023087007c5b534c3930600736a653430166736a5b5339301b7736a5b533023047
  | 7, 0, 15 => 0x736a625339301476a5b53393427067736d655b5339307736a615b3023167736a5b53513023700735b3023160867b736a533927147736a5b5330230076a615339301406700533930140806600735b55533930600736a533927146736a53393025147736a5b53483930773726a39301614773534c463930147
  | 7, 1, 0 => 0x73655b393016087735b39302816087735b53393010087736a533930140b7736a53393130147735b5349393008773726a533023147736a5b5339301f7736a65533430277006a53302314066735b393027160877d736a53392714773615b533023087735b5347392708773716a5339271476a5e5b533930067
  | 7, 1, 1 => 0x6a6553393014067736a61533927147736a5b534727237736a5b534a392776a5339302814067007353392714086735b534c302c237735b534c392714785736a53392714700786a5b533927676736a5b533023700736a392716146736a635b53393076a5339302714067736a655f5339307736a5b5327231d7
  | 7, 1, 2 => 0x6c5b53393006673615b533930077736a655b3023167736a5b4f3933307736a534f3930147006a5b534339066736a5b533230237736a39302316147736a5b533930117736a5b533023107736b5b5347393076a5b53393009067735b53302723087736a5b534930237735b534c3927237736a5b302723167
  | 7, 1, 3 => 0x736a5b39301d16700735b533023076736a675b3930167006f5b533930066736a655334302b7735e5b534c39307735b534c393427700736b533930146726a5b533023067716a5b53392706700736a532723146736a5b3023201677361534c39301476a5b53302322067006a5b533930036735339302314087
  | 7, 1, 4 => 0x736a5b533927097736a46393016147735b53393027077735f5b533930087007f6a5b5339276736a533e3930147005b53392708066736e6a655334307007c5b53393008673726a5b3927167736a65533927147736a5b5339300a70073534c3023146736a5b533930127007c6a5b3930166006a6153392c066
  | 7, 1, 5 => 0x736a625b5339277735b53302b230877365534c3930147736a53393327147736a5b53272322773534c39302814773655b53393007700736a5b53281d65b5339301408067735b53393028077736a533927241476e6a53393014067736a533930100f7735346393014087736a5b53413930773534c393027147
  | 7, 1, 6 => 0x736a5339271410700756a5b533930600736f5b533927600735b534c4339600736a534a3430673726a5b5327237736a5f5b5330237006a5b532723066735b39302c16087736a5b533f39307736a5b52393330782735339301408700736a534628146736e6a5b30231675b533930230806700736a53392c0b6
  | 7, 1, 7 => 0x7d7353393014087736e6a533927147736a5b302c23167736a5b3927161475b53393430080677370615b533930782736a53302314773716a3930161476a655b53392706700735b534d393067b7353393014087736a62615339307736a53393014047736a5b5339301c76a5b53302314067006b5b533930066
  | 7, 1, 8 => 0x6a5b5344393006700736a533023146007361534c392c6735b53302c23087735b53392714087
  | 8, 0, 0 => 0x73726a615b5339308006a615b53393006700827d6a5b533930700007f6a5b533930600005b533930080660000736a5b5339276736a655b5339302f800736a5b5339302570073726a5b393016700736a6553393014700735b534c463930700736a533930281470082736a5b533927700735b534c393430700736a5339302714700716a5b533930067
  | 8, 0, 1 => 0x73726a5b533023700006a5b53302306600736a5b5653393077b736a5b533930148007d736a5b53392770073716a5b533927700736a625b533930700736a5339333014700736a5b5330232270082736a6153393070000736c5b533930682736a5b533930238007b736a5b533927700736a5b5339300270000736a5b534339600736a5b533930097
  | 8, 0, 2 => 0x73726a5b533930288006a5b53393028067736a655b534a393080000735b5339270867b736a5b53393830800736a5339302b1470085736a5b53392770000736a5b392716673726a5b5339302780000736a6153392c6006a5b5339302706700736a533930141070000736f5b53393067b736a5b53393023800736a5b5339300b7736e6a5b534739308
  | 8, 0, 3 => 0x736a615b5339302380073615b534c3930700735b533930230877b736a5b53393430885736a5b53393023800736a5b534f3930700736a5b39302316700736a5b53463930700735b5339301408785736a5b53393014800736e6a53393014700736a5b39301614782736a5b53463930873726a655b5339308006a655b53393006700736a615b5339277
  | 8, 0, 4 => 0x735b534c393027700736a5b46393016700736a5b533e3930700735b5339343008773726a5b5339302b885736a5b533934308736a5b5339302714800736a655b533927700736a5b3934301670000735b534c3023600736a5b5330231470000736b5b5339306736a5b53463e393080000736a5b5327236007a736a5b533930773726a5b533933308
  | 8, 0, 5 => 0x736a5b5339333014882736a615b533930800736a5b5352393070082735b5339300870000736a5b53462860073655b534c3930700736a5b53393327700735b534c393028700736a533930140e700736a5b533927247006e6a5b53393006700735b53463930087736a5b5339302814800736a5b534439307736a5b5339302723885736a5b534639308
  | 8, 0, 6 => 0x736a5b533023673716a615b5339308007d735b533930087736a5b5339302b14800736e6a5b533927700736a5b5339302170082736a5b53302370073716a5b393016700736a5b534239307007b735b53393008700736a5b533930047006a5b5339302c067736a5b5339343027800736a615b533930700736a5b53463023700736a533930140f7
  | 8, 0, 7 => 0x736a655b53393070073716a5b533023700736a5b53433930785736a615b533930800736a615b39301670000736a655334306736e6a5b53393023800736a5b5351393070000735b39301608682736a655b5339308007b736a5b533023700736a5b533930007736e6a5b533930148736a5b5339302b238007e736a5b53393077d736a615b5339308
  | 8, 0, 8 => 0x736a5b39302716700736a615b533023700736a5b534739277736e6a5b5339343080000735b53302308600735b534c39302c70085736a5b53302370000736a5b3023166736a5b533934302b87b736a655b533930873716a5b5339302780073726a53393014700006a53393014066007d736a5b53302370073615b5339300870084736a5b5339307
  | 8, 0, 9 => 0x736a5b53302723700726a5b5339300670000736a533927146736a615b533937308736a65615b53393080073655b53393008700736a5b5330232177b736a5b5a533930800735b5339302808785736a655b533930800736a655b3930167007d736a5b534630700736a5b39302816700736a5b53393010700735b5339302708700736a5b534939307
  | 8, 0, 10 => 0x7c6a5b533930600736a5b5339301d700736e6a5b393016700736a675b533930700735b5339302b087736a615b534939308736a655b53393027800736a5b53302320700736a655b533023700736a53393023147000073534c3930146736a615b53393330873716a5b5339302b800736a5b5853393070000735b53393007600735b53393330087
  | 8, 0, 11 => 0x736a655b5339302b80000736a53393014600735b5339302c08700736e6a5b533023700736a5b39302c1670082736a53393014773726a5b533930238006a5b5339302306700736a5b53302b237006a5b5339301406700736a534639301470073726a5b5339277736a5b5339333027800736a5f5b533930700006a5b53392706600736a5b534039307
  | 8, 0, 12 => 0x736a615b5346397736e6a5b53393330800736a5b5339272370000735b534c3927600736a5b53392726773726a5b534639308006a5b5346393006700736a5b53302c23700736a5b533927147007d736a53393014700735b534739300870073716a533930147006a5b53393430067736e6a655b5339308007b736a53393014700736a5b533927257
  | 8, 0, 13 => 0x736a5b53473930288736a5b533933302c80079736a5b533930700736a5e5b533930700736a5b533934277007c736a5b5339307736a5b5347393027800735b534c393023700736a6153393014700736a5b53473023700736a5b534a393070000735339301408600735b534c39301470085736a5339301470000736a393016146006a5b53464539307
  | 8, 0, 14 => 0x736a5b5346392770083736a5b53393070000736a533023146
  | 9, 0, 0 => 0x736a5b5330236736a615b533930700735b53393008685736a5b533930700736a5b39301667d736a5b533930773716a5b53393077b736a5b533930700736a5b533930682736a5b5339307736a5b534639307736a5b533934307736a5b53393023700735b534c39306736a5b53393014700736a5b5339276
  | 9, 0, 1 => 0x73726a5b5339307006a5b53393006600736a533930146736a5b534739307736a5b5339302c7736e6a5b5339307736a5b5339302b7736a5b533933307736a655b5339307736a5b533930287736a5b533930277
  | 10, 0, 0 => 0x736a5b5339306
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 36
  | 5 => 44
  | 6 => 52
  | 7 => 60
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
  | 0, 0 => 0x3980000e1fe000000000000000000000000000000000000000000000000000000007ffffffff0000000000000000000000000000000000000000000000000000000707f1dfff00000000000000000000000000000000000000000000000000000000f8ce3e0200000000000000000000000000000000000000000000000000000007ffffffff00000000000000000000000000000000000000000000000000000007f83fe1e100000000000000000000000000000000000000000000000000000007fff1ffff000000000000000000000000000000000000000000000000000000003ff01fff
  | 0, 1 => 0x3807007c01e1e00000000000000000000000000000000000000000000000000000000073001fd000000000000000000000000000000000000000000000000001fc1f838f01fe3000000000000000000000000000000000000000000000000001fc1f83ff01e1f000000000000000000000000000000000000000000000000001fc1f838c01e02000000000000000000000000000000000000000000000000001fc1f83ff001ff000000000000000000000000000000000000000000000000001c4188383001e100000000000000000000000000000000000000000000000000003ff8000fffff
  | 0, 2 => 0xe3ffffc7ffe1ff00000000000000000000000000000000000000000000000000e3c67fc7f1e01f00000000000000000000000000000000000000000000000000e3ffffc0ffffe3000000000000000000000000000000000000000000000000001fc1f83ff01fff000000000000000000000000000000000000000000000000001fc1f83ff00000000000000000000000000000000000000000000000000000001fc1f8073001fd000000000000000000000000000000000000000000000000001fc0003ff001fd000000000000000000000000000000000000000000000000001c018038001fe0
  | 0, 3 => 0xffffffffffe01f00000000000000000000000000000000000000000000000000fffff8f8ce3e0200000000000000000000000000000000000000000000000000fc7f88f80e200000000000000000000000000000000000000000000000000000ffc7fffff1fe1f00000000000000000000000000000000000000000000000000ffc7fffff1e1ff00000000000000000000000000000000000000000000000000ffc7fffff1e01f00000000000000000000000000000000000000000000000000e3ffffc7ffffff00000000000000000000000000000000000000000000000000e3ffffc7fffe1f
  | 0, 4 => 0xfffff8f8ce3e0200000000000000000000000000000000000000000000000000e03e00c00e2000000000000000000000000000000000000000000000000000001c3980380e1e000000000000000000000000000000000000000000000000000003807000c01e0200000000000000000000000000000000000000000000000000fc7f8ff83fe1e100000000000000000000000000000000000000000000000000e03e07c00fe000000000000000000000000000000000000000000000000000001c3980380e01e0000000000000000000000000000000000000000000000000000000070031c1e1
  | 0, 5 => 0x70701c01c000000000000000000000000000000000000000000000000001fc1ff38c1de0200000000000000000000000000000000000000000000000000003987000fdfe0000000000000000000000000000000000000000000000000000000070001c00000000000000000000000000000000000000000000000000000000000000001e000000000000000000000000000000000000000000000000000fc7f88ff0e201c00000000000000000000000000000000000000000000000000003980070e1ffc000000000000000000000000000000000000000000000000000000000700001c
  | 0, 6 => 0x700001c000000000000000000000000000000000000000000000000001c4188383001e100000000000000000000000000000000000000000000000000003980000e1fe000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e0000000000000000000000000000000000000000000000000000e03e07c73fe1fd000000000000000000000000000000000000000000000000001c01873f31dffd000000000000000000000000000000000000000000000000000000070731c1fd
  | 0, 7 => 0x70001de000000000000000000000000000000000000000000000000000000000000001fe00000000000000000000000000000000000000000000000000000000000001e0000000000000000000000000000000000000000000000000000000000000001e000000000000000000000000000000000000000000000000000e3be70c7ce3e1e00000000000000000000000000000000000000000000000000e3c67fc7f1e01f0000000000000000000000000000000000000000000000000003807007c01e1e000000000000000000000000000000000000000000000000000380700700001c
  | 0, 8 => 0x3800000e00000000000000000000000000000000000000000000000000000003807707f1dfff00000000000000000000000000000000000000000000000000038070000000000000000000000000000000000000000000000000000000000003807707c1de1e000000000000000000000000000000000000000000000000000000070731c1fd0000000000000000000000000000000000000000000000000003807007c01ffe00000000000000000000000000000000000000000000000000000000000001e0000000000000000000000000000000000000000000000000000000070731dffd
  | 0, 9 => 0x1c0000380001e0000000000000000000000000000000000000000000000000001c000038000000000000000000000000000000000000000000000000000000001c000038000000000000000000000000000000000000000000000000000000001c00003800000000000000000000000000000000000000000000000000000000003800000e1fe000000000000000000000000000000000000000000000000000003800000e1e0000000000000000000000000000000000000000000000000000003800000e01e000000000000000000000000000000000000000000000000000003800000e0000
  | 0, 10 => 0x1c00073801c00000000000000000000000000000000000000000000000000000003807073fc1fd000000000000000000000000000000000000000000000000001c00003f00001c00000000000000000000000000000000000000000000000000003800070e001c000000000000000000000000000000000000000000000000001c3980380e1fe0000000000000000000000000000000000000000000000000001c3800380e0000000000000000000000000000000000000000000000000000001c000038001e00000000000000000000000000000000000000000000000000001c000038000000
  | 0, 11 => 0xe03e07c00fe1e000000000000000000000000000000000000000000000000000e03e07c70fe01c00000000000000000000000000000000000000000000000000e3be77c0cffe0200000000000000000000000000000000000000000000000000e03e07f8cffe0200000000000000000000000000000000000000000000000000e03e07c00fe00000000000000000000000000000000000000000000000000000e03e070001c000000000000000000000000000000000000000000000000000001c0000380000000000000000000000000000000000000000000000000000000003b87007ce1e1e
  | 0, 12 => 0xe3be77c7ffffff00000000000000000000000000000000000000000000000000e03e07c00fffe000000000000000000000000000000000000000000000000000e3be77c7cffe1e00000000000000000000000000000000000000000000000000e3be770701c01c00000000000000000000000000000000000000000000000000e38007c7c1c01c00000000000000000000000000000000000000000000000000e03e07c00ffe0000000000000000000000000000000000000000000000000000e03e07c73fe1fd00000000000000000000000000000000000000000000000000e00007c730001c
  | 0, 13 => 0xffc007fff0000000000000000000000000000000000000000000000000000000ffc007fff1c1fd00000000000000000000000000000000000000000000000000ffc007fff1c01c00000000000000000000000000000000000000000000000000ffc007fff1c00000000000000000000000000000000000000000000000000000ffc007fff0001c00000000000000000000000000000000000000000000000000ffc007fff0000000000000000000000000000000000000000000000000000000fc3e07f80ffe0000000000000000000000000000000000000000000000000000fc3e07f80fe1e0
  | 0, 14 => 0xffffffc00fe00000000000000000000000000000000000000000000000000000ffffff0031c1e100000000000000000000000000000000000000000000000000fffff8f80e200000000000000000000000000000000000000000000000000000fffff8073001fd00000000000000000000000000000000000000000000000000fffff80000000000000000000000000000000000000000000000000000000000fffe07ffffe00000000000000000000000000000000000000000000000000000ffc077fff01e1e00000000000000000000000000000000000000000000000000ffc007fff0001c
  | 0, 15 => 0xfffff8000e000000000000000000000000000000000000000000000000000000ffffff07f1dfff00000000000000000000000000000000000000000000000000fffff807c01e1e00000000000000000000000000000000000000000000000000fffff80000000000000000000000000000000000000000000000000000000000ffffff0731c1fd00000000000000000000000000000000000000000000000000ffffff0001c00000000000000000000000000000000000000000000000000000fffff80700001c00000000000000000000000000000000000000000000000000fffff8c00e2000
  | 1, 0 => 0xfffffffff0000000000000000000000000000000000000000000000000000000ffffffc7cffe1e00000000000000000000000000000000000000000000000000ffffffc73fe1fd00000000000000000000000000000000000000000000000000ffffffc00fe00000000000000000000000000000000000000000000000000000fffff8380e000000000000000000000000000000000000000000000000000000fffff838000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x19a00006976400000000000000000000000000000000000000000000000000000003fbdeeeee000000000000000000000000000000000000000000000000000000035bd6eeee00000000000000000000000000000000000000000000000000000000f0cc2c0200000000000000000000000000000000000000000000000000000002b95a8ae400000000000000000000000000000000000000000000000000000002a81a80c0000000000000000000000000000000000000000000000000000000015bd06aae0000000000000000000000000000000000000000000000000000000019500aa4
  | 0, 1 => 0x9813015401a340000000000000000000000000000000000000000000000000004c0980d3003b5000000000000000000000000000000000000000000000000000d41a8187019810000000000000000000000000000000000000000000000000009c1381460181100000000000000000000000000000000000000000000000000090120104018000000000000000000000000000000000000000000000000000004c0980c300191000000000000000000000000000000000000000000000000000440880830018100000000000000000000000000000000000000000000000000001ff80007f77f
  | 0, 2 => 0x62cedd46a3e15b0000000000000000000000000000000000000000000000000062c65d46a1601b00000000000000000000000000000000000000000000000000625fec40a7b543000000000000000000000000000000000000000000000000000dc1b81d701bb5000000000000000000000000000000000000000000000000000dc1b81d701991000000000000000000000000000000000000000000000000000dc1b80d3013b5000000000000000000000000000000000000000000000000000dc0981d700bb5000000000000000000000000000000000000000000000000000d01a019501ba4
  | 0, 3 => 0xf2e65de6a9601b00000000000000000000000000000000000000000000000000992120b048180000000000000000000000000000000000000000000000000000902000a0080000000000000000000000000000000000000000000000000000006bc77d56e1781b0000000000000000000000000000000000000000000000000066c6dd4eb1619b0000000000000000000000000000000000000000000000000062c65d46a1601b0000000000000000000000000000000000000000000000000062dffd46a7f55b0000000000000000000000000000000000000000000000000062d77d46a5741b
  | 0, 4 => 0xdb3560f0cc3c0200000000000000000000000000000000000000000000000000d23440e08c240200000000000000000000000000000000000000000000000000993120b04c1c00000000000000000000000000000000000000000000000000004b156050c43c0200000000000000000000000000000000000000000000000000b46a8ea83b81c100000000000000000000000000000000000000000000000000b02a06a00b804000000000000000000000000000000000000000000000000000942882a81a81c000000000000000000000000000000000000000000000000000244a8e083381c1
  | 0, 5 => 0x208a170703c27c00000000000000000000000000000000000000000000000000290b271243d84800000000000000000000000000000000000000000000000000201ba70207d76c00000000000000000000000000000000000000000000000000200a070203c04800000000000000000000000000000000000000000000000000040882091283e40000000000000000000000000000000000000000000000000090a011a708423c000000000000000000000000000000000000000000000000000099b10706d77c000000000000000000000000000000000000000000000000000080110700423c
  | 0, 6 => 0x4294514784663e000000000000000000000000000000000000000000000000004654c94ab4658b00000000000000000000000000000000000000000000000000421de14286f76e000000000000000000000000000000000000000000000000004214414284640a0000000000000000000000000000000000000000000000000009112011441e2400000000000000000000000000000000000000000000000000b4ea9faf3bc3fd000000000000000000000000000000000000000000000000002dcbbf1f73dbfd0000000000000000000000000000000000000000000000000024ca9f0f33c3fd
  | 0, 7 => 0x291b271347de6c000000000000000000000000000000000000000000000000000d19a219569fe40000000000000000000000000000000000000000000000000009192211469e6400000000000000000000000000000000000000000000000000041882091687e400000000000000000000000000000000000000000000000000dbb571f7cc7e3e0000000000000000000000000000000000000000000000000062d65d46a5641b000000000000000000000000000000000000000000000000004b957157c47e3e000000000000000000000000000000000000000000000000004b95710700523c
  | 0, 8 => 0x903802a00e8440000000000000000000000000000000000000000000000000006fdfff5ff7ffff000000000000000000000000000000000000000000000000006fdffc04211111000000000000000000000000000000000000000000000000006b9f7757c7fe7e0000000000000000000000000000000000000000000000000066dedf4fb7e7ff000000000000000000000000000000000000000000000000004f9df35fd6fffe00000000000000000000000000000000000000000000000000461cc34b96e7ee000000000000000000000000000000000000000000000000002ddbbf1f77dffd
  | 0, 9 => 0x9d2882b95a8be4000000000000000000000000000000000000000000000000009d2802b95a88c0000000000000000000000000000000000000000000000000009d2002b9580aa4000000000000000000000000000000000000000000000000009d2002b9580880000000000000000000000000000000000000000000000000009d39a2b95e9fe400000000000000000000000000000000000000000000000000993922b14e9e6400000000000000000000000000000000000000000000000000943882a91e87e400000000000000000000000000000000000000000000000000903802a10e8664
  | 0, 10 => 0xbd2a07bb5bc8c800000000000000000000000000000000000000000000000000b4fa9faf3fc7fd000000000000000000000000000000000000000000000000009da013bf584abc0000000000000000000000000000000000000000000000000090b813a70ec67c000000000000000000000000000000000000000000000000009d39a2b95e9fe4000000000000000000000000000000000000000000000000009d3802b95e8cc0000000000000000000000000000000000000000000000000009d3122b95c1ea4000000000000000000000000000000000000000000000000009d3002b95c0c80
  | 0, 11 => 0xf63ec7eb9fe7ee00000000000000000000000000000000000000000000000000f2be57e78fe67e00000000000000000000000000000000000000000000000000fb3f67f2cffc4a00000000000000000000000000000000000000000000000000f23e47f2cfec4a00000000000000000000000000000000000000000000000000f23e47e28fe44a00000000000000000000000000000000000000000000000000f23e470203c04800000000000000000000000000000000000000000000000000df3443fbdc6c8a00000000000000000000000000000000000000000000000000dbbd73f7cefe7e
  | 0, 12 => 0xffffffffffffff00000000000000000000000000000000000000000000000000ff3fe7fbdfffee00000000000000000000000000000000000000000000000000fbbf77f7cffe7e00000000000000000000000000000000000000000000000000fbbf770703d27c00000000000000000000000000000000000000000000000000fbaa17f7cbca7c00000000000000000000000000000000000000000000000000fb3f67f3cffe6e00000000000000000000000000000000000000000000000000f6fedfefbfe7ff00000000000000000000000000000000000000000000000000f6f457efbc66be
  | 0, 13 => 0xfff447fffc6c8a00000000000000000000000000000000000000000000000000ffea9ffffbcbfd00000000000000000000000000000000000000000000000000ffea17fffbcafc00000000000000000000000000000000000000000000000000ffea07fffbc8c800000000000000000000000000000000000000000000000000ffe017fff84abc00000000000000000000000000000000000000000000000000ffe007fff8088000000000000000000000000000000000000000000000000000ff3f67fbdffeee00000000000000000000000000000000000000000000000000ff3ec7fbdfefee
  | 0, 14 => 0xfffffea42b915100000000000000000000000000000000000000000000000000fffffe0c3391d100000000000000000000000000000000000000000000000000fffffca429111100000000000000000000000000000000000000000000000000fffffc0d3113b500000000000000000000000000000000000000000000000000fffffc0421111100000000000000000000000000000000000000000000000000fffe47ffffecca00000000000000000000000000000000000000000000000000fff577fffc7ebe00000000000000000000000000000000000000000000000000fff457fffc6ebe
  | 0, 15 => 0xfffffea42f955100000000000000000000000000000000000000000000000000ffffff5ff7ffff00000000000000000000000000000000000000000000000000fffffd57e57f3f00000000000000000000000000000000000000000000000000fffffd46a5751b00000000000000000000000000000000000000000000000000ffffff0f33d3fd00000000000000000000000000000000000000000000000000ffffff0623d15900000000000000000000000000000000000000000000000000fffffd0721533d00000000000000000000000000000000000000000000000000fffffce4ad3513
  | 1, 0 => 0xfffffffff9199100000000000000000000000000000000000000000000000000fffffff7efff7f00000000000000000000000000000000000000000000000000ffffffefbff7ff00000000000000000000000000000000000000000000000000ffffffe6aff55b00000000000000000000000000000000000000000000000000fffffebd7f9dd100000000000000000000000000000000000000000000000000fffffebd791bb5
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 134 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 134 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 134 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 134 then wireAt i else 0
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
  | 4 => 3
  | 5 => 41
  | 6 => 561
  | 7 => 3132
  | 8 => 1016
  | 9 => 17
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0x58cfe2d3574f3107229ed11c
  | 5, 0 => 0xf18a0a78ed65c9fbec8c197ddfb8a37ed3582146d1e55450cd8ba78acce1dc47c0fb8285bcff4445b0cbc762ae341093a7efb5c6a35c9dd6a0ae5c209f9ca3939f30710e9dafbf4296254ab492d5f19f879396758502b70a7f569d5f7b30d80568ff5f575f155fa151957ea84dd1aa3c42b779a3415c807e406cb67e371934b33694744e32b728ea2bcc88c52b54974c1e4092cc0dfb5be70cf91af109f56582044cc036
  | 6, 0 => 0x1980682c18f26c4c189a029d181877cf17d6fff4178b4c4e1725f0f216eb0e0416d31cb716509bfe164ba18915b544a6155608d6153eaa181488e2b213c93bbb12908867121ab1a412183e0611f45ea911417f60107b9173103dbd961009f8d10fce77530fb3ce380faa77070fa22a3f0f8898390ee2d2210e7e15130dfc2cef0d3f24990c7d6fbb0c2a9c4c0b7421250b4d81f00b09be8409a6f41607cc26e607c0ce650774b3fd0748db5e06165d760603175b05a197e905941c820505ca7204e4143604a0f63a04955e22035fd28003560a040319042502e6255902cc506b01af582a015ae24a011d463900bbc06900620ac000583e5600453e520026e37e
  | 6, 1 => 0x2f52d6ce2eaf75dd2e6465742d1301a72cce811c2be61f7b2be313dc2bab4e122b87ab452b81626d2b7f3dc02aec59c62a758cfc29c8f25a2937eecd292f8a3b2909654c28ce93e328b4110828a4a83e28236680271c2ea6270f28642705880d26d3ff3726c09f4926b0cd08267b20552629ae6e261931b925eb0f4225d32ac22598027525958ed724f85f8a24bd998d24b8c602249d0b2023e92d1223de903323ddefb323ac1b172279d1d72244ea16217c18ce2130058120dad03e20d6910f20bc756a206d0bcf20292edb1f698d5e1edeef8d1e9cc3911dcf29111d53ac7e1cd0211a1c96ea491bf6a8921bcf59401b4977b719ef48f119ba301a199304db
  | 6, 2 => 0x51808105517680e65147ce624fcbca934efe4b864e71e0994e6543824e0df3394d84259f4d3623874c30865f4b0b1ee84ade027d4aae3b9e4a8a38274a76e1cb4973e8a5490bcbdb48cbb65d48c2474248b438cc489483bc48558c3948027d4547d9c4f647b4abff46f1b31146d4578c45870eb2451f7c0844bfc70a44540250441eb01f434ac03242b779a3429d7e9142886158414d38a1413a622b40722d1640466cb23fc4defb3dc4c9ba3d9419de3d513e8d3c6254223c21f90f3b932d743954a7aa388623e637c8237437bb82de37b1143237809ff0376135eb3660102c3599238b34b9518233e52db032e5408e3099cb892f72e55f2f68da3b2f653d43
  | 6, 3 => 0x751113a0750aabcf74894935743d2db173f7fa30727718da722eeeb671178bf7705b5d9f701ba1776fa9caa86e8cbcc66e2027196db8946f6d71c6146bf7365b6bb3a4396ab595706aa951c76a06bd6d695529b96862a2c067d8db4167bc3f5c67b0443e67aab8ca67a4845b6703e91c66786f8a657fa7266576d7bc654b05bf64a12107644f053863fb6a7f63097c7562ef3d9e62501bbd61933ed5610f13f760bfdce0600575d46001c70a5fe5db6e5ed01fcc5d26770c5d09213f5aa8a6b959b9852d5925466958419b775774ee2e57589e9f57530f6056dd108056488c3a55f5b47b54a96c09546ec5c45444baa4536178d7533e15335318541d530132d1
  | 6, 4 => 0x9043d1318f7a66348e8df0778e4d0a488e104c5c8e04dd068d5eaaf98cde5e8b8c9dac058c97da0f8c5a26b38b1537598a81f0ca8a2d572e888e1594885b4f3687fe15ec87f229bf87c857ce87bd0eb9876db589876876b08744a6f8872c5dc98728e3098724c50f858963a384480ae0842ebc3f84129c40840a8ac983f2b51a839d4e8f8229ac8481bd8a2f815c694d80feb7d980ef16e580cb09e980bc381980739fc780311ee57ee807d27e21fdaa7d8ecad87d10a7c77cddd30b7c95abe27c3be1d57c1c3a667c1542a07bb1b30a7b41725c7b2b17a17ace616f79e15a2877ed7ef2779763ed773db5b17733516276835e3b761d3e0676076b4675628073
  | 6, 5 => 0xb2341140b1697430b0f4679dafa719ddaf988793af616e2baf3a42ecaec033a4ae7f853aabf2df9aabed000faae0d45daa56a296a9b9269ca8e458e3a817ae6ba7bf7c17a68fa675a5ab77aea575eddca49e2ac1a47ac71da454196aa3dff9aea3481cd9a2cebd7fa29515b3a1d961dfa1c17092a099576a9eb0e2fe9ea53c809e499af29e150ffe9db654639d7364f79d1bf20e9c6c69fb9baa556c9b3d4dac9aa633da99af20c799a56c00993f2f2f989eac8e986022359801f4a797d04e5497bc493a97ac0d10976bc39697065c2596c3c09c963bd5cb94d2bf9d944e6e9593e6fabf936b6ca092c480a2919f4e7b9138155891086f4990a397f89082705d
  | 6, 6 => 0xcc074e3dcbe405f9cb634545cb1c4c97c9f2a206c9880156c95fc938c8dcf747c8d3a4c2c77f38fbc6a44c39c5b50a75c52c43f5c48f92c7c456b3eec43ecf6ec42d6449c3b8464bc376efa7c3246aaec17a36c2c153d67dc135d26fc10f4154c0c03103c06966bbc0614fa0c0450afebfeeb6fabfd55147bee05fb4bedf2cdebe9d7c93be75d1f4be657855be5a52f5be4be64fbd220369bd199d0fbcbf7b05bc907cb5bc7d54cbbc33c7a4bbe603b1bb897c82bb5d9909bab9a1bdb969d830b9570d75b8e76ab4b866b528b84eea26b7dce78eb6841c7bb6314f13b5e991b2b591959eb563e0d7b4462e5fb3d7fc1ab3c1ad82b3a5b92fb2f8b09db2bc8ad0
  | 6, 7 => 0xe9ee24e9e9c801bde91f1bc4e919e04ae909a655e8d9024ce8321d65e8001871e749bbc4e71dbef7e70eea5be6ee6dd1e6e4feb6e523aca9e47180a9e45c71a1e4299312e40c8193e3d2cc05e389f5f5e2dd6198e276b9c4e254d007e2526437e250936de1cb645bdf5d199fdf415612df330e7fdf0da044de72f46edd92dd54dca7d42fdc4a1fc3dacd29a7dab625c4daa96d91da6e9c28d9d87172d89d39a8d7fa8692d7ca6921d5d46a6bd5a4d300d58c5584d531990cd4b32340d3b847d9d343e014d28e4411d2485b2cd1fd464ad1efb8f3d1a6b841d02a929ace7fd441ce6d09a2ce2cdb74cdf424b0cdd47ee7cd47ff8dccd45e46cc869a53cc389808
  | 6, 8 => 0xfff9fcc0ff939cefff7c7227ff7467c6ff2b818cfed30435feb4b37efdc42e8ffd801952fd47e974fd29b1f9fc7a83edfc3a8f2efaf243d0fac52187fa704343fa6bbea2fa401789f97998eef8cf82a7f7f1aadbf6671af1f5c4434bf597a5a2f590cb54f575c6d4f43d7841f3e34996f3175066f2da6a70f2cacc14f2b41125f2b05f50f22119bdf0fce731f0f9ec74f0f8df95f04a511defe22592efd4a863eef3064dedee8207eddd9179ed9421ccecdaea36ec164c1eebefca4beacc61b6ea742c98
  | 7, 0 => 0x52aa495051ecc0c051a6ec905169eb00509fa1f04eede2204e553f804dbb86404d8394304bca65904b413c504890ef504824cd40479bbe104696107046088880459b5e304427d3b041b5fb5040d80d603d4cc410375c6cf030a418d02e9d44b02d6a72e02d3da1402c1685702a27623029f514b029aef9e0299fc920294122e028de01e0266400402502c670249a99b023f5c5b020b934d01eac28901cde88101b5ee8d019fd767019f361a0198403d018309d901794b5f01752afa01667c3e01652a32015fcb3e01551783014ecf68014268c70124c53e011182d8010b91e100f9b8fb00f94cd000ea38dd00b912070094e5e900481fea0031a7ea0029bfef
  | 7, 1 => 0xa7a55280a6426b20a5e33fe09ee1b6f09d9969709d1727609bd51ef09b1e68209a7f214099096e20989c7c3097689a80925d5bd08df973908c5dc3f08b46af10899ab530893911a0865d84f0844bf83083004ee081c74db07f70b8707ed8a3207c20e2707a99a0b07a3436a0790b29f078c6002078179cf0720ca0a071cbf990715437d0709752006fe4f3806fb5c5206dc984206c4413d06acd7de06a8768f06a13685068d7fe1068bc39d06735b220665520c065d56850659598f065401810651b5d5064f4535064cb80906457cb90638a75e062e761d06291d83060f596e060e01a405f7c51b05e9221005c61dd605ad2f3405a9e53f057c0b7a05576f3c
  | 7, 2 => 0xe974d5b0e90cf7c0e7e15130e7dd0190e7db3450e7515ed0e737a980e67dc250e3f844d0e302b3c0e1f184a0e06518a0df435510df1ea5d0df124ef0dc23f740db9c7830d9cbe430d8a87100d7f85ab0d5a81df0d52c9a60d3586890d05cbda0cfc43180cedf22c0cedec0c0cea20e10ce9b2880cd896110cb5970c0c867e660c825c970c6ed2f30c6d8e9c0c6d390f0c687b0e0c232aad0c22507d0c1e8e5d0c0bf6ea0bd3d3cb0bb0c3ae0ba8c1380b985bbe0b80dabe0b76e6c50b50e2ee0b41c7720b2179b20b216c4f0b1a7d630afb5dd30af89e950af197a60ae653d70ae34fac0acf09dd0ac616070ac4d5b90ab8b2690aad79ad0aa0caca0a7e53d6
  | 7, 3 => 0x13e0e2a713bd0dcc13a8dfe013967e2f139302bf1384597d13728f56136dc90413470650133c08ef1317dd2b130a5a8912ddb43412cec45012bb814412baa67712a8595d127638531233466a12300b711228cbf912245a68122261f8121617f5120d1dd3120061e011c1f92a11bd50f411981144118eca21115e1032114c695c1142fa4111062b7210de35ff10aeb074109bbfbb109410fb108bef57104862a5102d8cd3101fadf4101f34a20ff651070fec104b0fb1a7760fa2a5570f9aa5fd0f808c130f7ac0e10f799f850f53334a0f3d85820f3d84400f1986a90f115ba20ee0af2a0edfaa8e0edf18670ed68c150ed019dd0ecc23a60ebfb63b0ea800b8
  | 7, 4 => 0x18f302eb18eed24c18e242ff18d274d918ccee3b18c40ebb18c378e018ac994f1895d6311891280c1871e2ca1862a4c9184a30ad183afea718261f78181c0a6c17ddd95917d9c21d17d64a9117bf920f17bcd81e17b7e34f17a3f1f5176f5810175a929b172462521706ecff16dbf17016d77b9d16d21d8816c91dcd16b01e5416859a0f1673385e16528f35164042a2161648bc1612f34116118174160c7aef1606144c15ff6d7d15f4eac915d3b4e415cb6ef015c1920715be15cb15ba6e6315af65f11596d48d157b3ef6155ed0bb154b3952153eaa18153802db14db292014db18b514cc203914c0d43c1480f23a14696ac214466a841420fefd13ea83c2
  | 7, 5 => 0x1d85da9b1d826c881d81c57f1d7c58d21d75a3ee1d5319ea1d4c60a11d345f2e1d2d215e1d2a81d31d160c6b1cd93b5f1cd038361ca81a3a1ca481c01ca0b1831c7f55261c6af0321c53915b1c397d011c228a231c1ffead1c1b0f141c0c1b4b1bc7d4b01bc210541bb1776b1ba99d041b9935371b8548e61b78d4bc1b6c71d91b55df541b52f3321b27d2611b1e63461b0bab3e1ae9b4a21ac819931ac6e6c71ac6cf551ab658ae1aabb3a51a87fcc01a7be4741a6a04de1a63b4731a4dc7a41a4058c31a39c2a21a33b1c31a1f1cf019fc1ed919e5257c19ddb2d519c7c79119b1d44819a917ce19912262198e7f10198916cb196672e11923eb0b19224d72
  | 7, 6 => 0x237315dc2353b18e22e093b222d85c9a22d25b5c22c96b3022c7351322c4f10a2289ec0b2280547522758e6922740317226fd98422599897225693612227e6972213883721eaa96f21e6cbde21de28f921c636b821b5c2d421a5f968218956322145ca59213f9045213bddeb2117964020df43cc20cdfb2c20b8602f208879802062e284203dbfd6203a916820350eec20292edb2014c6442014059b200df9ca1fed21a51fecb1011fa565611fa432931fa23c8a1f8738591f59336e1f4cfea11f3e5d811f3387171f15ac8f1efe2b8f1edb86661ed55caf1e8f50351e8c48a51e8657331e2d04af1e08e1531df73f721de45f961dbe4d991daeb8c11d98a19b
  | 7, 7 => 0x28bd116f28a4a83e286822e328668e6d286658d0286028b1285f6112285ce7a3285879f1284514cc2844d63928222a1a281909f628175891281012c927d2573727c3516e27c1256227bb223c279f070c275958f22750b4f6273e087b2738adc8272630b12724c80b2713cf002710b40c2705880d26eeeb7b26dab06026d0c80326beaf6f26ad11912693cc3a26640762265b050526488ebe26396ad4260a164f2609324125d992dc259a3137258a6ea4258a599a25645cee25471fea250aba5724f9d1c424f59d0824df459a24c9ba2d24851f7024763bd424429b1424425a8424374d472414ae9a2409402823f0c29e23e6546623cff39623a73b32237418ee
  | 7, 8 => 0x2d618f3b2d52d1502d4b28f82d3e70562d1b653b2cfe0cfa2cf8cd042cdf3e6c2cc795ae2c86b1b52c7afb6d2c58dac22c2026e82c1b9a942c18d8712bbea46f2baefdce2baea7c42b87620c2b81faf52b81626d2b811d732b75aae22b5913022b2253022b19bbf42b15732c2b13e5c22af68de12ae913f02ad26e7b2aa4abb42aa00b9d2a9ddf912a95810c2a8e42722a8999b02a6cf0712a6540552a541ffe2a4f06f42a4993872a3198e02a2628ce2a245e7b2a14d0f729f9c57229ed6e3b29e942c429e0d67129d10a3229b291b729af2b642993998d2989cbc0297c99f8296669a229428e4b2936b6b729342757292c9652291385ac28e1d56328c73e98
  | 7, 9 => 0x32d045d132cae7bc32ba82ac32a1bcd53294f0e0328546223264f194326007a83252e2e032440aae32113f4a31f5eab3318b16ac31647c2b31470cdc3129ad3f3122199e312099a030de567830ddf49130dba21430d52820308db8473086a299306f6ccb303f34b8303037e9302ca777301b2a85301052cd2fbf35272fbdf3d12fbbf89b2fb1aafd2fa88bf32f8f1ff32f8af2362f86b33f2f8141142f7a8db12f67316b2f48cad42f2d39052f2cdf472f1d2f5b2efbd9642ede098d2ebd3d6c2ea71a0b2ea523322e8a65942e89c73d2e3b996a2e38cc412e28d5a52df877932df741622df013cb2de85b922de6358a2dc5ce1f2dbac35e2d90db782d7f4474
  | 7, 10 => 0x37a4666c379a889137997d533778a28c37596ec33743a61d36e9c65936e2575236b5383e36a47dd93678c0eb3669c03b366487033644f7dd3615bd78360938793601d28435e7486435d89aaa35abdc1135a0b6f0359f67e7358e7c13358833f8358749443579865d353aa3c63536fd9035239d6d3506a70335009d3534f8c82434f524f934d7e3e934a771a7349995fb34926031348b4368347c735e3466ebee3453b6c53451707d3450bbda344f47aa34487e12343eb0573434573834171dd8340fff2c34064f6c33df688433da662c33d93c6b33d8677333b85c43339be83033511330334a7e36332a82ad330bca3f330a8e35330961a632ecdd7e32def36c
  | 7, 11 => 0x3d18139e3d12016d3cedcf813cdf82eb3cda06bb3cbde0b03cba78eb3cb0a1003c82fc633c644fe93c21b4153c0ce04f3bcc8c933bbe60cd3b9f7aeb3b945c8c3b8dd07c3b754d643b5dab7f3b43ce223b3e76333b33d6c03af6ada23ac923d83a9f5d673a9a85bd3a8e04dd3a690eef3a67daad3a64e63a3a4fc2063a3b596f3a3129ab3a2d6c623a111d0b39ff1f0a39fa66b039f7e21b39e1752a39ddf64839c6347939b5e92239a3264a39693dae39631e873956e3ad3926ffe83926b9f839234c0738ed825b38c8629238bbb164389cbe3638962217387c22163872edd9385c966b382f747e382eb67e381fcf1437ea8af437d59bc637a858aa37a858a7
  | 7, 12 => 0x425bc8a4424d728e42408308422797774221143d4214fad141b8ea3b41b5ff6441a0c12841751586416695634149098f4110f4a840e8120340e5429a40c96f0f40bbc12740a60e3740936de140846bf6406f21e9405ffdff405e8a73405c8f3d404b301340419ef2401a1c4f3fed881a3fe000373fdba9f43fd72a663fd3ef6d3fca826d3fb404613fb101cf3f8ddd6d3f85b1273f6b35ef3f6236343f5aa7ff3f545ac33f4622693f3721633f2f2fec3f2afc363f291ad13f15457d3f086e6d3ef484683ee6de3d3ebac68e3e791ea93e6664c13e444aad3e3c0ae43e38a55b3e277fff3e247c763de291263de1cf0e3d99ff873d8a3cae3d3e89f93d333acb
  | 7, 13 => 0x47d7f35a47ba59f747b5a73d47946ea94755b8444727debc471a541a471718c4470caff646f379b846ec901e46df279b46de759446cefcc046c7c635469949b54681c35d4667f2b7466764c54654163446260195461ef30245f6b58445af24d2459774c2453d0c694526b40844e5077444cd758b44ae84d94493839c4486548a447c8c184442cf3244324d9e441caf3c440fd5ef440913f443f5039043eb0c0643e3db9743a9f8484397d1404382cd09435ea178434bdc184344cc0c43415cc54336d2af432dfd824325dcc4431f7df743110caa430c7f9b4305883642fe183e42fbf37742e7b5af42e28e1442c7651642b779a342b451b0429130724270b5be
  | 7, 14 => 0x4c1e35cd4c173de94c16af5f4c1064844bf147df4bd0b1094bacc54f4b8c97694b83f6714b81ba084b6de5b24b6978864b6231954b5e75fd4b51d8934b40496e4b2e44754b2472944b226b904b21fba14b196cdc4b17d9624b0d87ba4b0c2c394aee73794ad1055a4ac64d7b4abe875c4abd1d0b4ab9f0674a9428d24a932f4e4a8291714a77d2104a44957f4a3f5f3c4a0d19744a0b38054a0125c049f3d2f349e8ddff49e3bfbd49dd0e9149b6983f498f6d66498effba497e1ccf49787d0149780ea84975de44493c341049335f8e49292ce2491e4f54490584c948f6d72e48f6c24648f0ff0048d58fd648c35a8b48c2474248a6ffde480eeebd47e43cbf
  | 7, 15 => 0x50eca9cc50e2359450a9730450a1bacb509f54165096359d507c4096507546385070134c506e67a450659ad75059633d50490acd50381f73502b26865012b59d4fff2dd54ffcc3574fd720e24fc71f074fbdd0064fa260824f9d2f8d4f7141a24f57c7d64f54e6cc4f49dd644f0494734ea817a54ea4fa1c4ea474154e9a87094e8c86004e7855394e5372144e3cd4e24e3b68614e2cfa994e2ce2974e2566f84decf5114de2370b4dd542384dd3ad484dc9c7c04dc7b19a4db248164dace24a4d8cd6aa4d86bbea4d77b7814d3fd1c54d3c580d4d159afc4cfd734b4cd6bec54cc999094c9aca3e4c70a3534c6ebdd84c51dc5f4c4491e44c388e2d4c29021d
  | 7, 16 => 0x566430dc56403068563580cb5618cb345618ad1556185cdb5600570755f9c36e55d8ab8a55914c4d557cb754554bcaab551f842c5509b11854f251df54d5ab8054c1de1054b47b98548e6dd8546b22205467b4c65465171a5457bcd654324e1553e18f1b53cbf68653ca920853c0149953b2be7253ad163d5395ea58537c0e455372efcc536b8d0a534b32e953466db8533a10a7533669d9530ec13f530840ea52e2321e52dbe80452d0b5be52ce9ec25292ddd95281620b526ca24b5253af29524e709e523dc211523a2c705209977e51f6a40d51ccc13e51bb2a0f51b101cb518d110e5184d1d45160844351501bab5136a9a351099cc650f9411850ef3542
  | 7, 17 => 0x5a97dc395a97a4eb5a9469955a8322685a6afd255a5bc6655a2473d259fcbebe59e5b39359d1670559b3a05959a0c2fc5996f4f5597e76b4597bfa895946af9f5944bdd6593aae785936765a592f0198591e47e658eb4e3858e6c54658c9505058bad09958b5610058ae4c9d58a96b3458597183582969ea581fb8f6581a3e36580e3478580006e257e57fa757c5f7ae57ab48c157a487195795fc8d578e67bf578012d0577efaba576d4781576c925c576b280757685cd7576751eb575675b3574ab38e5744b4ce5727b7f45722dfa4571462ac5707fb6756f3df7156e6f7eb56c5d00a568d8c7e56892c32568173f9567ee6cd567c7f51567043f55665d776
  | 7, 18 => 0x5f871fd25f4d90645f4c3dc55f492eb65f3e2dba5f18482b5f025f375ef408b65ede10445edbff035ec5fd9a5ec2fe405eb642b75e90963d5e75f8765e5492d85e441ef45e427dc45e394d3c5e22a7545e1bc49c5ddab89c5dda43b15dd41be55da6006b5da0f0ae5d5fdc975d5624535d53729c5d505dcd5d48a8d45d3f7bd25d0b15675d00c56d5cde0cce5cb746015cac318a5c91de815c7a05f25c5ccb105c3f74815c33c1815c1f443a5c0bbbc75be0d81b5bccb9a15bb639285bb357745ba4e2a65ba3354b5b6976d55b65c3955b4dbe2c5b3bed485aecd9575aea31985add23155ada88c35ad8bcec5ac7832c5ac679ad5aa8a6b95aa5f5965aa52f8d
  | 7, 19 => 0x6566e4ba653315e464e6ab0264aa6b44649ea5e0646b28aa644d72e664497e5c643ac406643609f56433ac9f642e54a0642d74f3641ca4e763fb6a7f63e50b4763b3242b63939f33637c7ea66332600f631fb15363020dca62e8da6d62d73fc8628e144f626898c062623a35625d8697624d6d5b62261eff6202e0dd61f5a73b61f427ee61de9b7b61d0c2e561ca400861b8723761aa3368618b6f36616fe8b46154c9cb613f4bb661306f51610c35a860fbe7f960bd229660b772cb60a7ce44609eba3e607f1ebe60778b6b607744386066e79960530ca5604fd85a604693fd6043727f601d48af601579706008d5905fbe37825fbac6fd5fa8e5035fa00125
  | 7, 20 => 0x6a2e06a76a2177b56a13aebb6a0829146a00c0a569da0c1f69cd7e5369c0add469b0c44b69b08c90697e5b01693c91ca69250df3691674076909578d68ade545686d07d468439ee9683daa90682efe61682c83d8682a00956827ae8568201ef1680f7993680bbea96807b6766805cfb76804070267eb4a3067df3ad067c13f69679093bc67891a306781da446776f078676198836760ca9b672edba167240676671ea51e671066ce66fc748866dd631466c97260669e5573669a488666816af866730cef666aceee66601a936644c8f86644be35663e596f663e41f0663dd1146627df6e6617db0a6604d30365d6d88f65b3f9f765a8269665a7b45e65692795
  | 7, 21 => 0x6f410f6b6f13e0ff6f0f44366eeb6aab6ee46b536ee314666edb0ec36ec28c856e9f9b6a6e5e503d6e16b7eb6e01e9f06dec12c46de93f766dd08b0e6dafa0f16dab2ce86d9d833c6d916c166d483b2f6d1f6cf16d18b8176d04869a6cd622c66ccba29b6cbe8b686cb5c7a36cac52696c85f2fa6c4b6e046c41d5016c2229556bf899566bf58d8b6be5d2566bcb63fb6bc715e96bba04806bb102606bab48676ba44eea6ba0665d6b76748c6b70d1e96b67104f6b50e1d96b35d9546b1be3666b0d63fc6b0959bc6afc1fc26afac8926ae97d196ae5c9b86adb14436ad99b6f6ac5c8b56abcdfc56a95be0b6a91b37d6a8281de6a76d3786a4320db6a41599e
  | 7, 22 => 0x75249840752306507502d39f74f8ca7a74ae2b347485a1e97481ccfa74789e64744813417432116374238cce73f993ba73ea5b6e739a99807394bd34736647aa73627f61735308ce734eaa0d73493a277326682873170721730cc97a72f4555e72e9411572bb7e8b72b28339729a86c6727f14f3727718da724693b772464c2172301b0f72286c4f721cd83371fa161671b7c8f271905291718aa31d7179360f7166cf87715dd49f7158096d70fe4ee070eea42e70b68b1c70a8072470a579f87066c39370607efa705b5d9f705437727053725e701d07ab701a846e7014198970120e997005f1236fb8decd6fb3739e6f778dfb6f7090bd6f6815276f4ebd9a
  | 7, 23 => 0x79cce61979c0734279b70aa979a30aba799c0d0f79952bdb79737713797234ad796deb3978e9916b78e65c2c78e4358b78dd6d3878d751e178b54ae278b0103578ac62e378a666597895dbbe789257757872d0267847c1c2781289727800865577ee2d5277d135d077b0fd7077abcbfa77a74e9577a5fcd4778424c2777d8546777652a77753784a7746c83977231e6a771fe4247710f44076f0de3376f096c376e1a5f076df94a676d6e32176c6508b76b871ac769ee490769e1cc8769b1dfd76863e3b7677504c766e04be76607b8d765bdd3276549099764e5f617613d46a7601ef8775ea2a0475cfa8b475598b3975576ffc75516084753f33837539d269
  | 7, 24 => 0x7f0df4cc7eeb32617edbceae7ecd8d627ec8ba827ebbf6017eadd0e57ead80c27e7a0a4c7e704a887e31bdc77e22428f7e1a8a567e16e3887e0371a67dffd2af7dfb85ac7df7c5a07df703d67ddacfa87dd765af7dd747b97dc3639f7db1e1917da51d3c7da0a7537d7d57bc7d4bf7b77d2d908b7d00cd2d7cea112d7ca8786f7c89c6577c88cd607c69c65e7c592d007c4bfba17c4260817c3be1d57c1abb197c170b2e7c140d477c08287b7bf0d3337be9041f7bc57d837bbafb617b86605a7b701aaf7b6e4ed87b665f577b3a2bd27b2b17a17af39e807ae6a9707ada8ab67ac1d9027ab1cd807aa157477a7f403579f7001d79e5550479de8c0179d3e13a
  | 7, 25 => 0x8433dbed842557f58422cac9840994f6840799a683fe99eb83f53a1c83e740ff83e4146483c7f1fb83c702f183b1739883aaf517838341f4836290978350a05e833df9038323a63b8323215e83101f7d82f4decc82e2ff4782d3eb99827963fa82585f948220babb821853fe81fd9d3781f3450081cb688981c4e67381bd8a2f817be6a2816ee385814e796781303d8c812adf7780b8cef280b2a53b80ab0b5c80aa07e380a74cdf80977014809286e38069eaef806266ad804124a9800c7ccf7fe516d97fe1a60d7fdec0a27fd8d7587fca544a7f8c014d7f78c21c7f75ea277f685e077f65878f7f54e5c77f4af1e47f4590c97f3407087f2c02b87f181117
  | 7, 26 => 0x89fab42489f4a11d89f4840589f142f789f05af589efee9189ecd54589e77a5d89e1803a89d9702089ba9fdf89b52b5089a86b2589a3f71c899b6c728983c1878948c6a28945a6a989312aef88ede02888e50a9488d9be1688ba8c0588a82a5488416ce5884052b7881f30c0881af3898816e94987ef605987ec230287e75edb87e12fc387b2ceb4878343c2877779c3876ece5a8752d38b872d9429871ec9f8871e3ea487062e308703169686c3fb2e869b7594868952b78681b5e98679f841867726a1866d344c861dc986861a00e9860c78ef85f1f72685c39cf285a623a085644eea85505e688542769185355bfe8475b53384594c5e8450d9fa843e7d10
  | 7, 27 => 0x906837b89061f6a59049058a902a64c69022657e90061e318ff460758fc68d1e8fc3c7a68fb5d0938fa972eb8fa2db658fa19e1f8f9d1d5f8f980bea8f80fc978f7b76b18f78512d8f7637028f6301198f5f11de8ebf00228eb70d658e9fcbf58e9deb6a8e92684e8e7679718e52fbf68e3f8c778e3f5deb8e2302ba8e1426838dc0b2f38da5c8bf8d5eaaf98d5c0a998d395ff68d1b84e68ced12b28cde80148cd916648cd7ccae8cd766ed8cae17488c66e23c8bc68b508ba51dad8b8fda438b7531c58b1fd6d78b1e27148b0cdb878b080e6a8abb56b98aafa50e8aa44b2d8aa3b04f8a81f0ca8a7994f88a59424c8a571a718a4b88898a37c65d8a0d8ef7
  | 7, 28 => 0x9689804d966c3f3d965db2649648b9589644454f9630ff519625511595daf82895d4c56f95c353b495b93d7695ad9990956ca7b19566b56d954b64c195370e769536a67a94fe5d2694e56e8494d4832a94c7ea7294bb41bc94b8834e94ae1516949f308d947da14a9473849994528761944ede00944e2f4d94302b6c940d56da93f91dd793f42b8d93e2499393602c46932ed1f7931c4d07931be89e9318892f92fea01592b8eaa092acc722927d83849272b1cc921c7d4491e8ccbe91d9edf19196ca6a918c7c03918bb4fb918b0169915bff5891503a309147ad6a912821e49117715e9112800b90f68a7190f610e690dc3b5a90c97f5390c13a9b90846297
  | 7, 29 => 0x9bbebdb69b9060219b82597c9b36b6809b34b1219b258fe99b1ef25d9b1dd7b09b18954a9b0094939aec1f2b9ae5da449adfac1e9ab52eeb9ab4c0929aabbbef9a88f9d89a7a06c29a741ded9a6914bc9a3dde069a1f18269a07492d99f0f1bf99eaf18f99d6685399bed3f9999971879985a1369933b443992721c298f6084098e9771598e2892c98d57d5998bfc7629882e2ec986b97ef9848d5ba98411d8197f3060497ec88bb97d874bc97cf645297ce2acb97aa9cac97a85c9d97a4a4a197a3eae797a0022597885ff9977526929768e4e39767190c976491d09756cee9972f419097012b8496f768a496f60d7996b2cff2969b0257969aeb72968d2378
  | 7, 30 => 0xa13f7ec0a12818cfa11662b6a0c208bfa0bf578aa09db9cca08609cca07b3991a06b55ada0566735a041465da0309aeba0219339a010db98a00b64c39ffac0159fe125ff9fc0bc2f9f8fc8a09f7986cc9f76ec7a9f728aec9f5ea4e59f307a4a9f2e5adb9f22e88e9f1c706f9ee2b6579edbc97b9e93ebe99e75c3909e5fc6b79e5adc459e418da49e3e2dc49e3acf2b9e14ab229e1370af9df1ef879df088639debfd949de5cf519dbc54029da9d51f9d9a91c89d65b4079d648c2e9d609f369d45ceeb9d42c3eb9d3bb9e79d28b7e09d0504429cfa7ec49cf2a1969ce7c5ba9cd8b9f79caba4cf9c625b659c068d939be41d5a9bd78ad69bc7f7b09bbf435b
  | 7, 31 => 0xa56effffa55beef2a550f087a5311dc7a508355ea4ef705ca4d69db9a4c4fe3ba4be299da4ba3818a4ae7b11a499e38aa4961296a494c22fa4943c01a476e968a434b4b6a41b12e0a411e8baa40b50aca407673fa3f2435da3e19170a3c1ff9da3ad8f9ba3a56a26a39ec2eea387b4c7a37f7be7a37a73fba3697d85a34d458fa34731dba343ddefa32cb193a3147353a30d2ce2a2c55a8fa2a97873a2a6f9a5a2a54ffca284b47ea26534afa264c4f2a2598ba9a256c1a0a2501c7ba2377ba9a22b6a16a224956da212b62da20703a0a206a488a1fff7b4a1feca93a1f2e5c7a1f16defa1f0ea91a1e69cf3a1878b6fa15ebe12a1521c33a14e6349a13f99cf
  | 7, 32 => 0xaae9b6bbaac7bae2aab1140caaacc2cbaaa935daaa99e01daa8b3282aa75a9a3aa732844aa56a296aa43ea8eaa2cb15caa00aaa3a9f3d131a99ee458a99c3196a9983258a9789813a9647ee6a95dfcd0a9501df1a94423c3a909e4c1a8f0d2eda8e9f882a8e78fc4a8c9d8aaa8b83798a89eb231a89d0c9ca88166b8a877d909a840633ca828f69ba8249059a81c3a5aa81a824fa7fc3b8ea7fc18f5a7c9a009a7b5ef13a7b45be4a70f3f44a70962efa6f3a76da6bc62c7a69b8dd7a6910249a661d0dfa65c3616a63f2c4fa63c52c1a639bfbaa6332d68a6193286a610e76ca5f12d82a5ed1e7ba5d4719da5c6a8f2a5c2748aa5b66d6ea5b36a13a57519cc
  | 7, 33 => 0xaf80d0deaf7d6f06af76925faf75ff26af73e99baf6f05a2af6b3d75af4d0594af4578aeaf28e2e6af1123ebaf0c12d5aeef6ae1aeeb3210aedf1679aec7458daeb40751ae6f23d3ae6de29cae6872d8ae1e846dae18ff3dae064aa9adf352c3adec3e13adeaf2e8ade6658daddfe763adab993dad965e55ad86bf71ad855048ad7309f1ad58a5d0ad4120a3ad3bbe89ad1391a5ad096b8bacac34b6aca9b064aca628bfaca06ab9ac9bcfe8ac8a86ebac7b9e87ac5fd9fdac59c64aac41cfbeac41a9b3ac06f897abdc18a3abc6268babbe6e52abbd86cdaba603dfaba341bcab9f69a8ab7c17aeab671e17ab6407b8ab55c58dab555734ab3f45e1ab227451
  | 7, 34 => 0xb5e82352b5b55af9b5b49d4db593ef12b59006feb5546fedb5417191b512b256b50f2cb0b4efd615b4c2adf4b4abe74eb4a8fae1b47be621b4520808b43f5990b435aab5b41b0a9db40220bbb3e7728fb3b09514b36df0c6b33f92c7b3216c62b30843b8b2df7a82b2bd69c7b28d9c6cb272d876b253b846b245d9dab22053d7b2131be6b2109beab20f961db2026dacb1fba0bfb1effe29b1ce22c6b1ca4356b1bbd0a8b182f0c4b169cadfb169bc48b1522b5ab150db15b12d5351b127beafb0e1dcffb0de38b8b0cf1072b08e74bcb0848746b081bca1b077cf95b04ea841b0347cebb02ed722b028f5a0b02513ebb0231954afc49eb7afa8260baf9abc18
  | 7, 35 => 0xbc545819bc3b0a4bbc398ae1bc2c003fbc28c4e9bc268fe5bc0c7999bba66d37bb80d0edbb75fc4ebb6820b3bb65c259bb5716a2baf70c47baed3e7abae9d770bae8aadfbadd43f2ba9cdb19ba8683abba701036ba460977ba45dd7fb9e4c7c8b9bbecabb98f294db95a5302b94d1047b932cbabb921fd5ab91d4ce9b90994d0b8fcb82bb8e21df1b8d90467b89c56bbb889a36bb871b7fdb86243b6b85c2f59b7f88c30b7ef6c85b7d6b31fb7d2d7acb793d28db7892a55b745623eb73f506eb7309443b72f93ffb71b5ed7b7186549b6fcccb8b6f964b2b6a064f5b691c424b6855c3db67647cbb666254db64ecbd7b62a6f1cb6251136b623fb60b60f96a1
  | 7, 36 => 0xc1ebf1e0c1dbd993c1a3757dc19d30e4c154e976c148abb5c111313ec0f590b7c0e08b57c0dfa7c3c0d8bcdac0a55ccdc0938b43c088640ac0705a57c05fc100c05a58eec031db64c02e5d34c0216780c01695c8c0144dd9c00c7e66bffb5e0fbfb4dd66bfa41077bf6247b9bf4172fabf01fb40beffe354befa2055bef0b2a0becf96e5bec33186bec0a575be907f01be6dddd6be5eb282be4be64fbe4ba155be4769d9be3add0dbe2639d5be110a0dbde1cfb5bde0f6a6bdc9682bbd82ee2abd6a8f7fbd46bf61bd41015bbd386403bd376e02bd367e88bd323f75bd2fc437bd20e303bd1c3529bd199d0fbcdd2ef2bcb9a3e3bc87e6edbc7e8f37bc62e41e
  | 7, 37 => 0xc667cc40c6614a2ac63e6ab8c5ff83fec5eadd1ec5d3e588c5c29045c5c1d047c5b1003bc5899ec0c5736c6ac55096e5c54fca04c548e825c543b096c5368674c530ad7ec5294a98c510d9fac4e635f6c4e09fabc4cfc905c4be72dac4b48854c4b40ca7c496691ec47d35c1c469c87ec4298755c4297888c3e2d77bc3e02969c3c26a3dc3b9c3cac3b4db41c3b34d4ec3ad2618c398766ec3848ffbc3651e39c33e8ebcc3347db3c3334588c325aa70c31b6fd9c30d3654c3007652c2ec71a1c2dde247c2afde01c2a091e1c2932210c27c2edfc266f667c25c674ac2517deac23e4196c22bf79cc21a72e7c2138c1cc20f81e7c1fa1783c1f2c1fcc1f12b01
  | 7, 38 => 0xcbd77c2fcbd5b4f2cb8dd51ccb67cfd6cb6178aacb531a22cb46a5f8cb2f7209cb20c46ecb099803cafe9774cae6a019cabb86a9caa6b7f9ca8e6379ca740502ca4b1c80ca48fbdaca14a60bca0e29ffc9fddb4fc9ee7b2ec9ecc21fc9e14f8ec9db9549c9d8b236c9c359b5c9be5be9c9a019fdc97fa584c96f57afc93e1327c93c7368c8f1bc47c8e779a6c8d8951dc8c1bbacc8baaba0c8a7967dc8a47d2ac871b992c85ae621c82cddd4c7f917b0c7e47b16c7d22c68c7c7a4ddc7b65101c7ac8334c7ac348bc7914283c75da4c0c7327c7fc730d938c7290bd7c6dfc8e3c6d2c7e1c6cb05bec6c817b7c6c77138c69f77c7c68515fbc682e025c67f9f17
  | 7, 39 => 0xd1e7bd46d1d6d4a7d1c001f7d1921bd3d1879d90d17bf5cfd173caa4d14d3a21d11e0aacd0e05608d0c5752fd0afe803d0a5ce8bd07ce3f6d07c82add0776fbad0418164d028b587d0188098d010ef66d00c244bcfe29780cfa1a4c1cf96c9c3cf9551ebcf94ce8dcf84fccdcf84fcadcf7d9acacf33b5c0cf25c9ebcf010deccef767cfcef6002fced23ed4ceb06fbbce844c52ce52b7face40adbdce1f1d8dcde52a59cdd6b28fcdd2d617cda6e723cd5cbbc6cd4f96bbcd41c6a2cd223ed1ccf052c5cccaebe6ccca3424ccc7daa6ccb4b64fcc804dadcc6ac460cc5ce581cc513b19cc452051cc396419cc375d6acc260ed1cc1d4d7bcbf17797cbe82736
  | 7, 40 => 0xd7e8ebedd79dcf25d7970f9bd7896e3ad786c099d7492ad9d732a860d7168563d70c7ee5d70862e2d6bc63dbd6acef47d68cb177d68b73c0d67f4ddfd67f4dd9d6382f23d619fd3dd6165ffad612c66fd6073c10d5e44738d5ce88c2d5c0efffd5bfd6fdd5a0d46dd57db6c6d5583fe0d52b0a13d520c64ed4894f7ed46d133fd4569f34d445852fd405b4dbd4001a12d3fa20bfd3f10f9fd3ab90abd3980975d39553b9d35f8c6fd34d4128d33a4f21d31b7f98d317dc6dd3152e0bd30c22d4d3039b18d2f22ff3d2def3e9d2b422bed295064fd29440d5d282c284d26b44f3d25e91a6d23dc786d2370a95d2299bdcd222b1abd2099c14d1efb8f3d1e93658
  | 7, 41 => 0xdc44c054dc35b29bdc2c6374dc05489adbf42843dbe6b227dbd11a6cdbc7af05dbbcb6fbdbae9429dba15c1fdb6940c7db4f7d39db37660edb2f28e1db29872fdb29855cdb23cb92db01ce84dafef9a9dae51d0fdae0a906daaefcd0daa10b17da9fdba6da7890dfda5018b2da4ab022da446b89da3ac1adda362501da26b2c9da20e016d9e9f37cd9c29a4fd9b71400d9891486d9840b17d97fc822d969f47bd9680625d96359b3d9612da7d957a573d9512280d91b4e74d8b7122cd8b0bc51d88e1e1cd88d7dfad884cac0d87f9952d872b987d872797ad86386c7d85d0165d85aabdfd84d19d6d84ccd00d833d47fd832781cd80862e0d8081e09d803eed7
  | 7, 42 => 0xe175a2ade171d949e15e97d0e1489438e1283faae10a457be0f3695fe0b9173ae0930e9de0800c8de07b344ee04e0661e026649fe01ebd33e0129c16dffa78b3dfe9bdd6dfe0ba32dfdba1afdfd44c62dfbea839dfb031ebdfafa89bdf942e03df91a28ddf7c0fd5df75e0f9df7206c2df397890df33ac1cdf1659addeff409cdede789bdec9dac1dec49712debf7146de7f46b1de74f913de5cb0fbde3c10adde35f7a5de312a05de2d0779de1fa90dddf155d3dded8854ddd55853ddc64cabddbf0999ddaa279ddda2c60fdd9deab9dd5eacb4dd4f56b5dd4db3aadd420304dd1abbaedd0995b1dcfabaabdccf1ccddcc1922bdcaf7ec7dc9f55a6dc891c35
  | 7, 43 => 0xe6d0b57ee6a36757e65393cae648521fe63d73aee606f433e603a7e6e5eac700e5e14f13e5d45f7de5cb74e9e5c83741e5c2ba49e5b7261de56d3923e55dcfb7e55c4d4fe5510a84e54af070e5499e93e5179d48e504ee61e4ed6809e4ea867be4a5c591e491a641e4625a30e4489ffce3ef42d0e3ecbae8e3e18a9be3d420a8e3ca2ab6e3c6ad28e3a8b115e3a5ddcee39d9b64e35f42cae358b1ffe3415187e335f380e31a7a5ae30e0cd1e2ff2848e2f911b0e2aad18ce2a0b98ae29f438ce298b8f8e28cec1ae28853e8e281e22ce280ec37e274b8a0e2550512e254a19ee24d2a46e232c2d0e230c8c7e21fca1de1ccafbce195a639e18ace26e1808a81
  | 7, 44 => 0xebdc8430ebdb61b4ebca1dd1ebc28ee5ebbeebd1eb93c63beb88fc71eb85b3b1eb7ec6ceeb259a9deb23f565eb21901aeb1f94e4eb154746eae154d9ead62371eabec0cdeabd810beabbbb9deaa64cb1ea99b7d8ea81aee3ea812a8bea39f55dea378291ea35abe9ea326695e9fefae7e9f83c15e9ee01dde9d230c7e9cf7cc3e9b0c204e9ab449de97bba2fe9674be0e93d2869e93a90d6e9296a68e926a1dae8e376bce8df0d24e8a3caf6e88d44c1e872edc8e86bd220e863d8b7e85b8981e81160aae7fb1212e7eb888ae7e9c17be7e8d4afe7b0d071e7a75556e786527ae76202ffe7561702e73f702ce7283c3de712a48ae6f5ef60e6e4feb6e6e4b9bc
  | 7, 45 => 0xf0fa8a62f0e8b557f0e272b8f0cef1a4f0b082cdf0a96dc2f0985b0df0556ec8f053c1fdf03d9387f0297054f02597d4f01ca677f0187b65f012b294f0010e1beff3c368efdd5beeefd9c9c0efd4f348efc2e112efaf60deef885172ef321432ef1bf88cef099ce9eef3064deed743b2eed63fa9eec40f0ceebe9aeaeeb4af79eea98865ee9ef80aee9092a6ee8dd083ee71c1e8ee6cfdefee4f0bb0ee1e2c58ee000531edfb3d90ede8e26bede0877aedd26beeed7d44f8ed7abd14ed5ae6a4ed56b179ed3bc136ed243597ed215bcfed143cc0ece6cd05eccef605ecbba0bdecb4322bec989f45ec4917e0ec3e9026ec297df4ec164c1eec04ee7fec01ec82
  | 7, 46 => 0xf57698bff52ab2dbf50a354cf4fad81af4f9312af4e56bcbf4dff160f4dbe8a1f49f240af489c5a0f486e850f469637df4535bf8f44d45f4f418610ef3ec3289f3e2aa94f3dfbe5ff3cea65ff3b0d898f3a1e699f3983283f395a0bef389ecdef381f6adf341502cf33b5fd0f334359ff33384e5f32d82bcf32a1730f30e72ccf2f3ae00f2d35972f2c41b18f2b97b7df2a74266f29edce5f2854adff25014fff249a559f218bdebf20f2a2ef20c2781f1febaa9f1ed8e22f1e2cc0df1d45c2af1cfcdb1f1cd5c84f1c51099f1a91aa5f19a7985f18ad4aef1820790f17a65ebf171c893f153019ff1510a14f14ae4adf13c5a6af12c673ef10d01a6f1027f58
  | 7, 47 => 0xfac274d4fab495f5fa728806fa510104fa06476afa0234daf9d9be86f9cab482f9afb2a4f9a7b435f9876158f96feb04f94691eaf9462d6ff944e068f9050bc6f8f8ed24f8f03dcbf8eb2a3df8d5ce41f8c7e701f8bf6874f8ba5c5ff8b72109f8a43307f8a016c6f890187ef87e7dd9f87cadc2f87bafe7f86c0c02f85b44fef81e1534f80299a1f7f914b1f7f41e79f7e6759ef7c55aa5f7a45692f77bde39f755edc8f74c3499f743fdf9f737c7bbf6f01bfdf6d3c780f6af2fc8f69357a9f68b5da2f666a70df650f9aaf641e9b1f6338be1f5ea9f66f5e8af22f5e5463cf5d2c480f5c486c0f5ba3ec9f5ab4c3ff59108abf58f108cf58d3b0df58017a1
  | 7, 48 => 0xfffb2919fff37a59ffee5704ffcceadcffc6e326ffa13466ff98826cff7c1db2ff77da54ff6dda91ff63e5f3ff6283a0ff55b127ff4cb230ff4c58d9ff3e3073ff259912ff2325baff0db492ff046885fedfda0afeb8db38feaf7861fea58edcfea05477fe88ed5bfe811e1cfe3673f0fe2c0696fe2b8d04fe2a185cfdfab3d3fde4e8a1fd7e81a8fd634e2cfd16c02afcfeb677fcfc3ae9fcaa882bfc94efe7fc86bf18fc807a7ffc50f767fc4a1fedfc250e5efc0c146cfc0b585bfbeed6c8fbec0709fbe1c5f5fbb566aefba53b3bfb2e1eb6fb19fc8afb195303fb192d73fafc002efaec6079fad9fd75fad8dc57
  | 8, 0 => 0x103ead2a102d8cd30ff61b8b0fc22fb60f5c5cfb0f3badb20edd17080ea68d810e8414b20e7dd0190dfb96ef0df078900db675560d9a92370d4d98860cf91d9f0cea20e10cc7aa850cb3009d0cabde0a0c867e660c2cfbb60bb2ffb10b989d440b41c7720acf09dd0ab8b26f0ab7b9ae0ab0afbb0a71f9560878675807d82e3c07bd347d07af559e0754ea150754e428075140fd0733ffed06b07a0306634425065223ce05c61dd605ad2f3405a3eb0a0590310f05869eb105169eb0040745c6036df150033a727c02e9d44b0296f5790291d00a024a740d023f103c023c952e01a603fb0188fb4b018309d90129b75501013f3600dd496a0086a50c00103def
  | 8, 1 => 0x2081cc61204aaf2d2046aaad203e530f203cd04e1fd3d3851fb72b911f608b651ee4e3db1ebb13731eb3facb1e8eec381e7359ed1e1aa3ae1e08e1531d989e101d73f5661c53b96d1bea35011bde45011b8f7b921b78d4bc1b61a0cd1b52f3321b325a461b2d157f1b1e63461a45ab1d1a4058c31a0ece701a0dc40d19f08aad19e360491979f417191531f41900f42918e3fb0a181aa94117d07b0017a820261729918f170db67f16d8a81c168e69a21606144c15f86a801561a43a141a4f1c1415063f13b5da6d136d10ac135211a2131bfefa1317dd2b12b8ab4112b8884a12ae5da3129997eb11ed84b711d748061187183a11761aa81142fa4110d1aa96
  | 8, 2 => 0x326a06213264f1943243d5cd315024ba31381b073122199e30ccd1eb3055c0a62fc976f62fa1c82a2f1362052efbd9642eedfa852ea0b9112d770a592d014b912cf3c0ef2cf085992cae27f22ca821632c9946a22c2d83092c1543872bdd94e82baacaed2a7c85282a6bdfc02a5e00e12a2213b229c478db2964176b292df8a1291abe5628c04ce02882e2b2284db2db2838c79a2727707326d2458e26aa53c326a4b5bf264ea12126488ebe262d41fb261c309d2609324125bece64258a6ea4255ffecb2509c4b824cb7b292485a934246554a62429651523a7fde623555d1c233e51982310763b23038dd422daf26b22d85c9a2219ec0a21a5f9682179389d
  | 8, 3 => 0x413f306a40db2d8b40bb28344079af63405c8f3d40455b7a4025ca0a3f49363a3f086e6d3ee6de3d3e277fff3e1c8eb63dff89d03df1aaf13dc32c533d8620523d18fbc93d0124c93cedcf813cd7d7c23c9f3cdf3c9dc2fe3c9d75a23c8fe41f3c3d49423bd0b7833b3c318a3b23954e3acd3e823a8b1a653a861c993a67daad3a47663439de879e396f572d395003403899ed1837a1ed1c378f31e8375fd1e83724f45b36c744ae36b6da9236ad5160368990f73678c0eb363c57f436224d1b361b1af435d89aaa359aee6d358e7c13357bcd57355e29ce354bc4fd3544f6713518dab13481847a34746a9f34744a7f342cdee933193e9a32ba82ac3294bf40
  | 8, 4 => 0x4f9b055d4f943bc44f8c57c24f624ff44f490be64f0fba7a4eb549044e9d19034e79bd534e7327324e1db72a4e1717654e0e9fc94e00c0ea4de27c5e4dc27b5b4d2b306b4d0476064cfd734b4cd8ba054ca60af44c173de94c1326ad4bf147df4bc969994bb13b214b7591cb4b62f61f4b40518f4b0c2c394b02825d4afc5e1e4aee73794a5928364a0d1974499cfa0a499b08ca49148db048fa38cc48ebd2aa48b0ac9d484e6acf475141bb472e33c146e1bded46e149a2465e79d54609964845f6b58445c07cca457c5ed145179a8f44cd758b43cee64d43b9f0a343b425714309ffd84305883642b779a34223bdb94214fad141d9fb7841d622d341a83906
  | 8, 5 => 0x5e1657ce5e06e6065debf6475d9647d45d93d62e5d7bf2db5d2e415c5d23bf8f5cde0cce5c9fbd605c91de815c50bd215c0095e65bff541c5b4388f85a73054d5a7078f85a437adf59f223e559e9c31b59e5330159d66aa059d395c75992adb0596bf2065923c1c65905159658a5f17758905d13584e132a581fb8f65806ebe257c3519857ac7a6c56dbe56f56da22f0568ff7f1567ee6cd56240dff55df5df855ab6c46558b875054b47b985342fdb7531915d1531692945314eaf6530ec13f52acbe7d52942b72528ca2425275541c51e81d5151d2062b51bb2a0f516924ff515c2919514f645451007c3a50c9577f50c4b4ed50a706e8505beeb35059633d
  | 8, 6 => 0x6e9f1e276e8018a76e38e6f66e1ad9ba6ddedbb86d5cb0976d2657c06cd622c66be1bd3a6bc490ee6b89f08a6b58c0516b1be3666af785736adde2696a5eea176a510b386a4fc62d6a4f22086a2a46cf6a0139de69f5d2f969c031bf69b2eaed692e70ee6920920f688d1b55683fb3fc679d352a67425c616709aa6166fb4c91668c47706659a12a663575426554bad1651506a464ffcc4e64e30e6464789948645092fc64015902638147926379a67663669d956347643b633af0116336351163275f1562e07e9b6292bf2262623a3561f427ee6129ea2960d1580460c016455fbac6fd5f5d13a95eebace45edafec85ec6f1c75ec2fe405e90082e5e22a754
  | 8, 7 => 0x7f1797dc7ef7ebec7e8559377e22428f7dd5c4a57db1e1917dad4e397d7d57bc7d776c2f7d303bbe7cea112d7c439fcf7c0721267bc86ac17b4614867b25f4ae7ae97d0f7ab597257aa157477a85129f7a5857927a2bfc5d79a4d76c7952d27478f04d34785a178978493a7f77f10ba277d135d07733bc5377211a3f76fcab1e76f0de3376f0916b76db0b2e76bdf4b976b015da766385db764e5f61759ff9f37521769374f2245d749b9886745a681c73a1eeb7739b9ac47341d2fd7333c42e73227b8e72e03d9b727daf3d7260e48f721cd83371fb25a271be65bd714a8ba970c4152b70946692707cee8d7005f1236fa6c90d6f69601f6f3b46226eba9933
  | 8, 8 => 0x8ebf00228e4941358e27eed18e2374cd8e21c9a38dbfa66d8d92f6958d6fdaea8d3d413a8d1e3ac28ce77a638c8386ea8bedc1998bbc73f08b8fda438b7e195e8aef68758ab84b5d8a8bfac78a7994f88a18c2888a0d10dd89beef4c899b6c728958e8bc88edfe0d88ede028886bb2a587ec230287cdddd087ca80ca877c8a9f876b3203872610b887080352869b7594867726a1862851b985f48e9f85e99b5485ba4fb985520fcd85210b03850f030e844c1a2d83f048fb83d9bb2c83c5bc52838341f4833df903830766bf82ddd8a582d3eb99828511a4827639728241b05981b633a581102355806266ad804281917fc0036d7f97da8d7f4590c97f27d809
  | 8, 9 => 0x9c3d6b929c36144f9c27c3cd9bfcd7929b9a2f2b9b71391a9b34b1219b16c7a49ab0be7a9a81c9ca9a36658d99bbfbc9997d4564992721c298d839699882e2ec985a34f798553ede981b7e9297a5128c974e731797251c989721f5ed96fad25696e3fc3596a4b77d965f3458963c456d9603a49895fe78aa95a996be956125c6955a08989502be1694b8834e9497281e944ede009396353d9351acbb934043b8933bc3c792efa74792ef453392b08ece92a6c201929a9c84928df768927d83849272b1cc925c0be491b98d1291426eab913b5e9f908ca444906d26119037c66b9011f582900c696690061e318fa2db658f9d1d5f8f7fd14d8f78512d8f668097
  | 8, 10 => 0xaf95e2ffaf935789aef43dc2aee65ee3aec64c0eaebd223cae8d3699ae5c9576ae064aa9adab993dada32de2ad85a160ad1a90a7ace974c5acac34b6ac3ab49dac23afedabe5308aab94b348aabfa2cbaaa935daaa8df529aa87c3f1aa38618daa2867c5aa21bb6da9cb11c2a9647ee6a95dfcd0a8e78fc4a80d4bfda8098f40a71939e5a661d0dfa6563cc3a62fa927a623790ea5e4c2a9a5cabbeaa5103ec2a4dede88a4a02823a499e38aa3f2435da36baaf7a35f8a0fa302d5f5a2d8fffaa1f16defa1c6431fa0c045e2a0b26703a07b3991a02ef21ba00d2aa29eab30d29e6bbe4b9e58572e9de9f1209da1794d9d61744b9d42bc1d9c97dd089c48de23
  | 8, 11 => 0xbef4bb49bef1afedbe3418b4be2639d5be1fe45dbe107ab6bddd5bacbd5c9ba0bd2744b8bcf5d0c6bcb2dff7bbec3344bb3f92c0bad4da24bab08b31baa8a17cba572e16ba477786ba1f06b4b9782853b96ec08eb85c2f59b84d21e0b81d78f4b7a3f583b7610a65b749840db6edc245b6be7634b69fded2b65f3e8fb644e080b63701c7b604cd19b5c9ec3db59a84ddb55b444cb559ed2fb52557b8b5195244b4e46fecb4d0d4a4b47be621b3feb3cab3f8265db37ef559b315333eb2f03ccbb23cd636b2313513b2306866b22e7c90b210ca3fb1b17014b12375bdb0f51e5bb0ec7e1fb080f6ebb07bc511b04d71d7b02268afb01ae1b0affee213afebec7d
  | 8, 12 => 0xcf6e15b1cf5856edcef7401aceecb93fceeb1ad8cecb96dfce8cc780ce6b8b90cdd2d617cda803e7cc0d7bc5cc0b8b0bcba24973cba07d9ccb26fa2bcaec3482cae6d7d7ca5eb5a5c9f2a206c9e24337c9d88a90c9a019fdc8e779a6c876c3bec846bb6ac7ad77bcc7a3ca76c7554d2ec73804a5c707ac1ec6ea46f2c689fa79c62ad07cc61b5c10c5e58a67c5dca5abc5c226a0c59d6c30c5899ec0c5690328c52f7576c4eae2e7c4ac2c82c483e9fec4605fcec3d681efc398766ec37f968dc34f33b5c31b6fd9c30bd3fac2afde01c278c27bc23de552c21dcfbbc1c6e06ec1c5a5bec1c16a74c150c440c110cb7dc1043454bf46884bbf4172fabef5700a
  | 8, 13 => 0xdf7fbf91df71e0b2df6d0221df41afa0dee29a6adede789bdec49712de7f8515de1b0bb2ddd7f9c9dd9de376dd7d8853dd4db3aadd0995b1dcd6712cdc240579dbeeb34ddaf5c757da8fa153da8008d2da7890dfda52a0c6da0af02ed9eccea3d9e7a089d958a3e4d90de9d2d8f62b1fd8e7dfa1d8cf7726d8653959d7d8277ed7c2c847d7661623d69e993fd6890d25d64007d5d630e845d62ad27fd5d7c256d5d13c99d58853add56748abd4fb6d4fd4f736c8d43f7d82d3fa20bfd38eac86d355d4ffd3152e0bd2da325bd27a66b2d229a3e5d1d3f658d1b38e6dd1786b89d0e5095fd0dd3a20d0a7e5c1d051c79bd0317033d010ef66cfe713d2cf84bc20
  | 8, 14 => 0xf171c893f15afe71f15a4793f109fd47f0f10dbef0c2900fefeaeca8efdfd1c7efdef6d4ef907b32ef0e3eb4eec76f65eeae7dabeeab662cee22ff53ee1e2c58ee185818edf5513bede64ad6edc88ddded71b5aeeca193e2ec848404ebc28ee5eb7a065aeb3fcd10eaf7dac4ea782c38ea39f55dea04555ae9f23fa9e8b54ab1e8b03ee3e878be20e86f0f45e812cbdfe7a75556e73c37a0e7283c3de7199440e5d4dd4ce5c6ac76e5179d48e49194eae4625a30e45c7de4e4402e8ee3624776e33582dbe32cc12de2f7dbbfe2f6cc76e2f02cffe2e94854e25263cde1c2a466e1b94d76e1283faae0d9cf49e088d44de07b344ee04a17a1e044fe41dfdba1af
  | 8, 15 => 0xff5a28feff3df527ff3992a2fefc312dfefb8721fef2bd64fed37441fe9afd92fe809189fe12eeb4fe091979fdf560cffd875a02fd75d7f8fcb0a9dbfc7cb7dbfc3cf275fbe5e7c4fb7259a6fb113ac2fabc44b5fab903a7fab495f5faa130d0fa6ea56dfa4dc81bf9acd0faf96feb04f9092d95f9091127f8b72109f80ff336f80fe67ff7fbcecdf7e68aa8f772bfb1f734b506f725d631f6657479f6655c2cf646c3bff637ead7f62c0f9af5a8ee32f5493ef0f5210d0ef50771aef39bac49f33b5fd0f32a1730f2854adff22186e7f1c7ebb4f1c31697f1c1f496f17a65eb
  | 9, 0 => 0xdee29a6add9de376c3d681efbad4da24b6be7634a6563cc38ab84b5d7f4590c9764e5f6155df5df84f8c57c22eedfa851e7359ed1729918f1561a43a1142fa4105169eb0
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x8411600000000841160010d21484303
  | 5, 0 => 0x214842030000000000013000000000000e0000000000013000000000000400000310842040010d20480303000000000001600000000000160014d104403020000000000004000003108420400188314c43000000000000012000000000000e0010d214843030000031084204000000000000e000000000000e000000000000000188314c43000014d214843020014520480302000000000000e0010d104403030010d104403030014d2148430200188314c43000000000000012000000000000e0014d20480302000000000000e
  | 5, 1 => 0x21484202000000000000f000000000001300000310842040014d2148430200000000000060008550484302000000000000e0000000000016
  | 6, 0 => 0x4344020300000000c81060000000012104000000000a10200000000c8106000000001210400000534842020000050484202000000000e1040000021484202000000000000f0000001802203000000000a1000000010440201000000000e1000000000000013000000000610400000000000040000000000009000002148420300188314c4300000000001210500000000000120000000000005000000000a104000000001210400000544c42000000001802200000000000a10200000001091050000000002106000000000a104
  | 6, 1 => 0x6100000001044020000000314c4201000000000210600000000c01000000000000005000000000a1060000003802200000000000a1030000053480202000000000a1060000001909202000000280220200000504c420000000018022000000000012106000000000e104000000280220000000534402020000000100104000000000210700000304c0200000000000000b0000053480202000000000000a000000000610400000544c8200000000380a202000000001210000000000411010000000002100000000000000b
  | 6, 2 => 0x180220000000000c41040000000002106000005204120000000000c8106000001044020300000000c410000000544c8200000000000e1010000003802203000000000000b0000000012104000005048420200000520c52000000000000012000000000a104000000001210400000104402020000004806200000000000e104000000000000a000000000000900000534842020000000002104000004348420300000038062000000000000009000000004110300000000c4104000000001210700000028062020000020480202
  | 6, 3 => 0xe1020000001802202000000000000e0000043480203000000000000e000000000000b0000043484203000000000e10400000104402030000000002100000000000000e000000000001600000000c810600000000061060000000006107000000010010400000000411030000000006104000000000e1070000002802200000000000210400000000c4104000000000000200000304c02000000000000011000000480e20100000028022020000000000016000000001210000000000c410400000028022030000003802201
  | 6, 4 => 0x1044020000000000401000000000000000000000480220100000000c4107000000000210600000028062010000051480202000000000001600000314c4200000000000000e0000000000009000000380220100000000c81060000001802200000005244020200000000021070000053480202000000000001300000000841030000000000004000000480220000000038062010000000006104000000000e104000005448420200000000c81060000001802202000000480a2010000000000009000000000a1020000050484202
  | 6, 5 => 0x16000000380a2020000032084206000000380620000000000121060000000000016000000000a1050000043440203000000380220100000104402020000003802202000004348020300000000c4104000000280220200000104402000000000000004000000000001300000000c4107000000280620000000000061000000000000000000000000000e000000000a107000000000210200000000021060000020480202000000000210400000039092020000004802202000002148420300000000000090000003806202
  | 6, 6 => 0x314c420000000000c4104000000000000600000000000110000000012106000000380220000000000c81060000003908201000000380a20000000104402010000005909202000000000e10400000520122010000000012104000000000610400000104402000000053440202000000180220000000000c41070000001909202000000001210600000038062030000000012106000000180220200000520412000000000006106000000380220100000000121060000000000011000000180220100000000000090000000000016
  | 6, 7 => 0x2148420200000039092020000021484202000000380620000000028062000000000000004000000000000f00000000021060000000006100000000000000e00000544c8200000000000000500000000021020000021484202000000000a10500000000021020000000006104000000000e104000000000210600000000c4107000000000e10600000000000020000000006104000000000000400000000841040000002802203000000001210000000000c4107000000000a106000005148020200000504c4200000000380a200
  | 6, 8 => 0x21000000000000000000000480e2000000050484202000000000e1060000000006105000000008410400000000000090000000012105000000000000f0000000002106000000000a1060000052041200000005204120000000000c8106000000480220000000510c9200000000000a10000000534842020000000000008000000000000800000314c4200000000000a106000000000a100000000380a20200000000c810600000304c020000000028062020000000006104000000380220000000000061040000000006104
  | 6, 9 => 0x2802202000000000e104000000480e2010000010440200000000000001300000038022020000000006100000005048420200000000061040000000000011000000180220000000000061040000002806200000000000a10400000028062020000000012106000005350020000000520c5200000000280620300000314c42000000000000000000000000000e000000380620200000038022000000053484202000000000e10700000038062030000000006107000000000610700000524402020000052041200000000000000e
  | 6, 10 => 0xa107000002108020000000038022000000040484203000002148420300000000021050000000012100000005348020200000000c41040000000000009000000000000e00000510c920000000000061010000000002104000000000e1010000000000012000002148420200000000021070000053480202000000000a104000000480e2020000053484202000000480620000000520c5200000000000001100000000121070000000000012000000000610600000000000090000000000013000000000000a000000000a100
  | 6, 11 => 0x2148420300000544c920200000000c81060000054484202000000000000a0000003806201000002048020300000001091050000000000000000000001210600000000021010000010440200000000000e10000000000c410400000534842020000000000000000004344020300000544c4200000000480e20100000000c4104000000000000b000000480620100000000021060000000000016000000000a104000000380a201000000000210400000028022000000005909202000000000000f00000000021040000020480202
  | 6, 12 => 0xa1060000000012104000000280220200000304c02000000004802200000000000210600000544c4200000000000000a00000520c5200000000000a101000000000e106000000000e1060000000002102000000000000e0000003802200000000000e101000000000a106000000380a203000005344020200000310842040000002802202000000000210400000000c410400000214842020000000006104000005348020200000544c820000000009092020000001802202000000000000900000314c42010000003802202
  | 6, 13 => 0x1210400000000c410400000314c4200000000480220100000524c42000000002806203000000000000e00000520c520000000534842020000000006104000000000000000000214842020000004806201000005148020200000018022030000001802201000000380620000000000c4107000000000e10500000000c4104000000000e1060000000002104000000000a1060000000000000000000380620100000000000130000000006104000000000000900000000851030000000084104000000000000e0000000012107
  | 6, 14 => 0x4000000000000f000002148420200000000000070000000000011000000000210400000504c4200000000000000a00000038062000000000000009000000000a1040000000000013000000380a200000002048020200000000061060000052440202000000000610700000214842020000010440202000000000a100000000000e100000002148420200000304c020000000000841040000000012101000000000210400000000c41040000000006102000000000a10600000000061060000000006106000000000a102
  | 6, 15 => 0x50484202000001044020300000544c820000000018022020000003806200000000380a202000000000000e00000000021040000000041103000000380a20300000000c410400000028022000000000002100000000000000b00000000c4107000000000210400000520c520000000000121050000052041200000000000210400000104402030000003802202000000000000f000000000a104000000000000f0000043480203000000280220100000000000090000040484203000000000610100000048062000000000000005
  | 6, 16 => 0x534402020000002806202000000000000a0000053440202000000480e20000000000121040000000909202000000000e106000000380220300000534842020000000000010000000180220200000018022010000021484202000000000a10600000000121040000002806202000000000a1040000020480203000000000000800000314c4200000000380620200000314c4200000000000e10000000038022000000043484203000000000000a0000000000006000000380a2000000001802201000000000a105000000000a104
  | 6, 17 => 0xe0000003806200000005048420200000000000000000002806200000000000001600000504c42000000000006107000000001210400000000c81060000000012101000000000000f00000000c8106000000480e2000000000002104000000000e1050000001802200
  | 7, 0 => 0x210200000000000040000000002100000000000000900000000021010000000000012000000000000f000000000a105000000000a1030000000012100000000000210100000000000050000000000004000000000000100000504c4201000000000000500000000c1101000000000e1020000002802202000000280220000000000021000000000002102000000000000100000000021020000000006102000000000000f00000000021000000000002107000000000e102000000000210400000000000120000000012104
  | 7, 1 => 0x4000000004010300000544c420000000000811000000000006102000000000610000000000411030000000000004000000000e105000000000000600000000c010000000000000080000000012107000000000000400000000000050000002802200000000000a1030000000006101000000000000600000544c020100000000061010000000000005000000000001300000000c41010000000041103000000000a10200000304c020000000000000080000002806201000000000000400000000000010000000002102
  | 7, 2 => 0xa000000000a10200000000000040000000000007000000000000c00000000c81000000000006100000000000e101000000000000600000000000040000000006100000000000610300000000411020000000000015000000000e100000000000000000000000021020000000085103000000480220000000520c520000000000000050000000002106000000000a107000000000000f00000000021030000000000013000000000a10600000000000040000000012100000005344020200000048062010000000108101
  | 7, 3 => 0x61020000000085102000000000e1000000000002101000000000a104000000000e101000000000e10100000000000050000053480202000000000e1000000000002102000000000000500000000000070000000002100000000000e10600000000021050000000006103000000000a1020000000002100000000000a10600000000c0101000000380620100000000000020000000012106000000000000e0000000000013000000000000600000000061060000020480202000000000a103000000000000c0000000000007
  | 7, 4 => 0x210700000000021000000000012104000000004110000000038062000000001802201000000000a10400000000121050000000002102000000000000200000000000070000000085103000000000a106000000000610700000000c910300000000000080000000006101000000000e10600000000061020000000109102000000000000000000000121010000001802202000000000000a00000000000050000000000007000000000210000000000000090000000000007000000180220000000000000040000000000006
  | 7, 5 => 0xf00000000121000000000002100000000000a1020000003806202000000000e106000000008110200000000000040000000108101000000000e10000000000061020000000006102000000000000f00000000061010000000000008000000000a1050000000012104000000000210200000000000000000000002107000000000a1040000000000006000000000000f0000000002105000000000000800000000411010000000000005000000000e10100000000000060000000000000000000000a1040000000006101
  | 7, 6 => 0x61000000000002100000000000000600000000061010000001802201000000000a106000000000e105000000000000400000544c420100000000811020000000081102000000000a10200000000021020000000000007000000000a10400000000021000000000002106000000000e101000000000000400000000c51000000000000002000000000000900000000000070000000000007000000010810100000000000090000000080100000000000e101000000180220200000000000060000000000004
  | 7, 7 => 0x400000000801030000000084103000000000a101000000000000f000000000e1000000000000000000000000a102000000000000600000304c020100000000021010000000000004000000280220100000000c8106000000380620000000000000090000000002101000000000a107000000000000400000000121040000000000000000000000e102000000000a1000000002909202000000000a10000000000061020000000012100000000380220000000000c1101000000000000f0000000002104000000000a100
  | 7, 8 => 0xb00000000121010000000000007000000380a2010000000040103000000000610000000314c4201000000480a201000000000e1000000000006102000005344020200000038022010000000000004000000000e100000000000000b0000004802201000000000a1040000000000011000000000000100000000061020000000006105000000000000400000000000040000002802201000000000000100000018022000000004802200000000010510100000000801000000000040103000000000000000000000c9102
  | 7, 9 => 0xb00000214842020000000000005000005210120100000000000000000000002104000000190820100000540412000000000000004000000000e10500000000c41000000000000009000000000000f0000000002101000000000a1070000000000002000000180220000000000021030000000000009000000001210100000544402010000004802201000000000e10100000000c41070000000000002000000000e1010000000002101000000000000a000000001210000000000021010000000002103000000000e102
  | 7, 10 => 0x70000000002100000000000a1000000000000000000000000a1020000000012106000000000a104000000000000400000304c0201000000000a103000000008410300000000000060000000002102000000000e100000000000210300000000c510300000000000060000000002101000000000001100000000000090000000000000000000000000900000000021040000000081103000000000a102000000000210100000000c110200000000411030000000002102000000000000400000000c11010000000000000
  | 7, 11 => 0x12000000000000500000000021010000000041100000000000000a00000544c0201000000000000b000000190820100000000000000000000012100000000000610300000000000010000000000013000000000e101000000000000b000000000000200000544c8200000000000000a000000000000b00000000000040000000002104000000000210000000000c8106000000000000400000000000070000000006106000000000000000000000061040000000006101000000008510200000000061000000000006102
  | 7, 12 => 0x5000000000e102000000000000900000520122010000000006101000000008110200000000c11000000000000007000000000e1060000000006104000000380a20000000000000060000000006102000000010910200000000000060000000006103000000000a1040000000000001000000000610600000000021070000000002104000000280220200000000000050000000012101000000000e104000000001210100000000c5100000000000e1050000000000009000000000000a00000000021060000000002100
  | 7, 13 => 0x210200000000851020000000000004000000004010100000544c8200000000000e104000000000000a0000000006102000000380a2020000000041101000000000000600000039082010000000000002000000000000a0000000002105000000000e10000000504c42000000004802202000000000a10000000000c1101000000000a10200000000000060000000002100000000008410200000000000050000000006105000000000000a00000000c4107000000000610000000000061050000054484202000000000a107
  | 7, 14 => 0x21010000002806201000000004110200000000c110000000018022010000000000004000000000a102000000000210100000000c4101000000000a10000000000021010000000006100000000000000400000000061030000000084100000000000000800000000000040000000006107000000000a10500000000061000000000041102000000004110000000000000010000000000004000000488020100000000021030000000006106000000000a1040000000002106000000000610100000001081010000000000006
  | 7, 15 => 0x40000000002102000000000000e00000504c420000000000021040000000006101000000000a1070000000006100000000180220100000048062010000000000005000000000a10500000000000060000000002105000000000e102000000000e1070000000002102000000000a102000000000e105000000001210200000000000020000000006102000000000e101000000000000a0000000000004000000000000f0000000006101000000000a10300000000000060000000012100000000000000b0000000000001
  | 7, 16 => 0x13000000000e106000000000000500000000000040000000002100000000000a102000000000a1000000000006104000000000a102000000000210000000000000010000000012100000000000000f000000000000400000000c5103000000000e1060000000002100000000000210700000001091020000000002104000000000e10300000000000040000004806201000000000000500000000000060000000002102000000000e102000001044020000000000c1102000000008110300000000841020000000000007
  | 7, 17 => 0x800000104402020000000012104000000000210300000000c410700000048062000000000000006000000000a10100000000061030000000002101000000000e1010000000000002000000000000b00000000801020000000002106000000008110300000000000060000052012201000000000e10200000000c91020000000002100000000380a202000000000a102000000000e105000000000610500000000061000000000000005000000001210600000000000050000000000003000000000e1000000000000013
  | 7, 18 => 0x12101000000000e10400000000061030000000000004000000000000100000000c110200000544402010000000000001000000000a102000000000000400000000021020000000006101000000000610100000000c41000000000000006000000000000600000000021020000000006100000000000e10200000000c5101000000000a105000000000a10200000000021040000000000004000000000000f000000001210400000000c51010000000002102000000000000b000000000210000000000000070000000000012
  | 7, 19 => 0x21000000000002101000000000610200000000121060000000006101000000000000b000000000a100000000000000000000048022000000000012102000000290d202000000000000400000000000040000000084106000000000e105000000000e100000000004010100000544c42000000000006102000000001210500000000021030000010440201000000000610600000000c810600000314c420000000000021040000000012104000000000a102000000000e10700000000121070000000000000000000000000e
  | 7, 20 => 0x61000000001880201000000000000f000000000000400000000000050000000000005000000000000a000000000a1060000000002100000000000000600000000061000000000000006000000000a1020000000000005000000000a105000000380a20000000000c81000000000041100000000004010200000304c02000000000000002000000000a102000000000001300000000000020000004806200000000008110300000028062020000000012107000000000a101000000000e10000000000000040000000000000
  | 7, 21 => 0x40101000000000a1000000000000007000000000000600000000c8100000000000e10600000000000060000000000004000000000a10200000000021060000000000001000000000000e000001044020000000000121040000000002105000000000000f000000000000000000000121010000000000001000000008510200000001051000000000006102000000000e100000000000a10000000000000070000002802200000000000210000000000c4101000000000000000000000c410400000000000020000001908201
  | 7, 22 => 0xc110000000304c0200000000000000e0000000085103000000000a100000000000e10500000038022010000000000007000000000a104000000000000a00000000c5100000000001210600000000411010000000006100000000010810100000000121050000000002100000000000e102000000000000400000000121070000003802201000000000000f000000000610000000000021070000000006105000000000a105000000000e101000000000a102000000000a102000000000000900000000021030000010440202
  | 7, 23 => 0x13000000000000600000000c11000000000040102000000000000a000000000e100000000000e1020000000080103000000000000900000000c510000000028062020000000000009000000280220000000000121010000000006105000000000610100000000c4100000000000000a0000000012104000000000000900000000061060000000040100000000000000f00000000c4104000000000e1050000000000008000000000610600000000000050000000000006000000000a10000000000061030000000081102
  | 7, 24 => 0x13000000000a10200000028062000000000000007000000000e10100000000021030000000002102000000000e10100000000000050000000012107000000000e10000000000000060000000006102000000000000a0000000002105000000000000700000000000010000000006100000000000000b000000000000a000000000000f000000000210300000000000020000054484202000000010d10000000000000090000000006100000000000000200000000061000000021484202000000000a104000000000e105
  | 7, 25 => 0x12102000000000e101000000480a2020000000041102000000000000700000000021020000000006105000000010d100000000000000f000000000e1050000000002105000000000e100000000000610000000000021030000000002103000000000210300000000021070000054440202000000004110300000000021060000000006104000000000a1020000000000009000000000610100000000c1102000000000e102000000000000f00000000000000000000006102000000000e10400000000000040000000012104
  | 7, 26 => 0x610600000520122010000000006103000000480a2020000000002103000000000a1070000000000001000000000210200000000000110000000006106000000000210200000000c8106000000000a103000000000e10400000000841020000000109102000000000001100000000811030000000006101000000480e20200000304c0200000000000e1040000000006102000005201220100000000000060000000002100000000000000400000000c5102000000000000000000000c510000000001081010000000000011
  | 7, 27 => 0x5000000004110100000000000000000003806200000000000a104000000000a100000000000a100000000000a10100000000021060000000000001000000000210000000104402010000000040103000000000a103000000000e107000000000e10000000039082010000000002104000000000e102000000000a100000000000e1010000000002100000000000e1000000000006102000000000000400000039082010000000000001000000008510200000000061010000000000000000000000a1020000000012104
  | 7, 28 => 0x11000000000e100000000000610200000000c5102000000000e10100000000000080000000000000000000001210100000000021040000000000005000000000001100000314c4200000000000a1020000000000005000000000000f0000000002106000000000000a000000000610500000000000020000000006100000000000000400000000000050000000006100000000180220000000000000080000000002105000005048420200000000841000000000006100000000000e10500000000851030000000006106
  | 7, 29 => 0x411020000000006100000000480e2020000000000007000000001210000000000c01000000000006105000000000000f000000000000e00000000000070000053480202000000000210700000000000100000000002101000000000000900000000c11000000000000009000000000e1000000000041101000000000000400000000411030000000006100000000000000600000000021020000000101100000000000610000000000000000000000002100000000000000900000000061030000000000013000000000000a
  | 7, 30 => 0xf00000304c0201000000480a2010000000002102000000000e102000000000e1000000000041102000000000e107000000000000500000000061000000021484202000000000e1010000010440201000000000000500000000000040000000081102000000000000600000000000040000000006100000000000a1010000000000004000000000a10400000000061010000000002100000000000000f00000000000000000000002106000000000a1030000000000006000000000000d00000001091020000000002104
  | 7, 31 => 0x4000000000610200000000000040000000000004000000000a10100000000c11020000000000004000000000a1070000000000008000000008410400000000000050000000000000000000480e200000000000000200000000000000000000002100000000000a1010000000012102000000000a10300000000000070000003806202000000000a10000000314c4201000000000000400000000021000000000081103000000180220000000000000070000000006102000000004110100000009092020000000002106
  | 7, 32 => 0x8010000000000000050000000000005000000000610100000000000060000000000005000000000e101000000000610300000000000050000000012101000000000e1000000002802201000000008410000000000000040000000000011000000000a1070000000000004000000000210400000000c11000000000000007000000000000a00000504842020000000105100000000000a1040000000000004000000000e104000000000000400000000000010000000006101000000004110000000000061030000000000004
  | 7, 33 => 0x610000000000021020000000041101000000000a10300000000000110000000000013000000000e1050000000041102000000008110300000544c420000000000801030000000085102000000000210500000000851020000010440200000000000a10300000000000060000000000007000000000a1060000000000005000000480a20200000534802020000000081102000000000210100000000061060000000085103000000000e102000000480620200000000021010000000000004000000000a1050000000012101
  | 7, 34 => 0x8510300000000c4101000000000e103000000000610300000544c8200000000000000c0000000000001000000000e1020000053484202000000000e10000000000021070000000109102000000000e106000000000210700000000851020000000002104000000000e1030000000002103000000000a1000000000085103000000000a1050000000006102000000000000f00000314c4200000000000a100000000000a10200000000c410400000000c510000000000021000000000000009000000000e1050000000002104
  | 7, 35 => 0x8410200000000061000000000006101000000280620100000000000000000000012104000000000a1030000000006102000000000000600000000061000000000000000000000000e102000000000e1010000000080100000000000a10000000000c410400000000c4101000000000000600000000021010000000006107000000000000500000000c410100000000c110200000000c410400000000000000000000012102000000000000600000000c4107000000000000b000000000000400000000000060000000000000
  | 7, 36 => 0x28062020000000000004000000000a100000000480620200000000000040000000006101000000480e2000000000000004000000000000500000028022000000020480202000000000e1070000000000004000000000210400000000c1103000000000000900000000c410700000000000010000000002106000000000a105000000000000800000000000040000000000000000000000a1020000000000002000000000e100000000000a104000000000000a000000000e102000000000000400000000401010000000006100
  | 7, 37 => 0x100000000061060000000000004000000000a104000000000a10000000038022020000000908201000000280620100000000c41040000000006102000000000210700000000000000000000002100000000000e100000000000000600000000021020000000002106000000000e100000000280220200000000000000000000000004000000000a10600000424812020000000012104000000004110300000000c0100000000480620100000000000010000000012100000000000000e000000000e10200000504c4200
  | 7, 38 => 0x12100000000480620100000000c1100000000000000a0000000000004000000000e103000000000000000000000c41070000000000006000000000000f000000000a10200000000000000000000006101000000000e1060000000000006000000000000900000000021040000000012100000005348420200000000021000000000108101000000000000400000000000020000054484202000000380a200000000280220200000038062020000000000006000000000000000000000021010000054041202
  | 7, 39 => 0xa1010000000006100000000000000100000000000040000000012107000000000610200000000c5103000000000210500000000021040000000000009000000380a2010000000000002000000000610000000000061010000000000006000000001210100000000000110000020480202000000000610100000028062020000000006100000000000610200000000061020000000006107000000000a102000000000000600000000000040000000000007000000000a107000005204120000000000021010000000000000
  | 7, 40 => 0xc51000000000002102000000000000f000000000000600000314c42010000000002100000000001210000000000061030000000006102000000480e2010000000000006000000000210200000000c4101000000000a10200000000000010000000000005000000000000200000000000010000000040100000000004110200000000841060000000000005000000000e10000000028062000000000000004000000480a2010000000084103000000000e101000000000e10700000000000080000000000007000000000e101
  | 7, 41 => 0xa103000000000000700000000000120000000000007000000000e10400000000021000000000000001000000004110200000000000090000000002101000000000210200000000121050000000000006000000000e1030000000002101000000004110300000000c4104000000001210100000000061040000000006102000000000000700000048062000000000109102000000000e10000000038022020000000006106000000000a103000000000e1030000000002102000000000610300000000c41070000053484202
  | 7, 42 => 0xa100000000000210200000000c1103000000000610100000000811020000000012100000000000610000000000000040000000000006000000000e1030000000012101000000000000700000000061020000000085102000000000000900000000000060000000012100000000000a1070000000002100000000000000100000000c1103000000001210100000000c9102000000000a102000000000e1020000000006100000000000000900000000061050000000006104000000000e10200000000061000000000006102
  | 7, 43 => 0x13000000000a1070000000012106000000000e106000000000000b000000000610500000000061070000000012100000000090d2020000000081103000000000a10700000000121060000000101101000000000610200000104402000000000041103000000001210400000000000060000000006100000000000610200000000c41040000000000006000000000000e000000000e1010000000040100000000000000f000000000a10200000000021070000002802202000000000000200000038022000000000000012
  | 7, 44 => 0xe101000000380220100000000021000000000000005000000000e1070000000000005000000000e10100000000000050000000000005000000000610000000000061060000000000009000000000000400000000c11030000000085102000000280220000000000021020000002802202000000000610000000000000070000000041103000000004010200000000411030000000000001000000380a202000000000a1000000001802202000000000a10200000000401020000000000006000000000a1020000000000000
  | 7, 45 => 0x2104000000000e1060000000002103000000000000900000000021020000000006101000000000000a000000000000a000000008510200000000061040000000000007000000000210200000000000010000003806200000000000a1020000000012100000000000000a000000000610200000000000050000000109102000000000000500000000000050000000000009000000000000a000000001210700000000061000000000041101000000000e100000000000000600000000000040000000012104000000000a106
  | 7, 46 => 0x1210100000000000070000000012101000000001210200000000841030000000000005000000000210000000000c51010000053440202000000000e1050000000012101000000000610400000028062010000000000001000000480620000000000000060000000002105000000000a105000000000000f00000038022000000000000000000000000210400000000c910000000000000110000000012106000000008110300000000c910200000000061000000000012107000000000e10300000000021060000000006101
  | 7, 47 => 0x210400000000121020000000006103000000000e10400000520022010000004806201000000000000200000038022000000000012106000000000a10000000000c11010000000006101000005048420200000000411000000000012106000000180220200000000c810000000000061030000000000002000000000610100000038022000000000000009000000000610400000000851020000000084102000000000000200000038062010000000002100000000000e100000000010110000000000000070000000000004
  | 7, 48 => 0x52012201000000000610400000000000040000000006102000000000610200000000021020000000000002000000000a10000000000061010000000002101000000000000600000000811020000000002101000000000210000000000000040000000006101000000001210000000000841030000000006102000000000e1000000000000004000000000000a000000000a1010000000000001000000000e10200000000000140000000006101000000000e102000000000000f0000010440200000000000000f0000000100107
  | 7, 49 => 0x121000000000000008000000000210100000000c1100000000390820100000000c51010000000000004000000000000e0000000000015000000008010300000000c1102000000000000400000000c51000000000000005000000000210500000000000040000000000004000000000000000000000021020000000000006000000000210000000000000010000000012101000000000e1010000000000009000000480620200000000000040000000000006000000000e101000000000a10200000000401000000000002107
  | 7, 50 => 0xe10400000000000060000000000002000000000a1000000000002103000000000000400000028062020000004802202000000000000600000000851020000000000007000000000a107000000000e1020000000000004000000000000600000544802020000000000001000000000210400000000121040000053440202000000000000700000000061060000054484202000000000610000000544c8200000000000e104000000000a104000000000e100000000008510000000000c41000000000000006000000000e100
  | 7, 51 => 0x6105000000000000e00000018022000000000000000000000000000b000000000e1070000000000004000000004110200000000021040000004806202000000000001500000544c8200000000000a10400000000061000000000000005000000000e100000000000000400000000121020000000000005000000090820100000000c41040000000012107000000000e100000000008110200000000021070000000000009000000000e10300000000021040000000081102000000090820100000000c4104000000000e101
  | 7, 52 => 0xe1060000000002100000000000a1000000000006101000000000610200000000000040000000012101000000000e100000000000000500000000021000000000000006000000000000e00000000021010000000000000000000000a10200000544c4201000000000000400000000c410400000000021020000000000004000000000000a000000000610300000000061060000000002105000000000e1010000000006102000000000a106000000000210500000000c5103000000000a102000000000a1010000000041100
  | 7, 53 => 0x21060000000006105000000000e101000000000e100000000000000500000000000040000003802201000000000000a0000000000000000000480e20100000000801030000000000007000000000000a000000000210400000000000060000000000000000000000000e00000504c420000000000021030000000000007000000000e10300000000000000000000000006000000000e101000000380a2010000000000008000000000e106000000000000a0000000006101000000380220100000000000010000000006101
  | 7, 54 => 0x14000000000a102000000000610000000504c420100000000000040000004802202000000000a10400000000000080000000041103000000000000a0000004802200000000000e1000000000006100000000000610000000544c42000000000006100000000000a1070000000006102000000480e201000000000000400000000021060000000002100000000000e100000002048020200000000000090000000006102000000008410000000000061000000000000007000000000000e000000000000700000000c1101
  | 7, 55 => 0x6000000000e101000000001210200000000021060000000006100000000000000400000544c020100000000c51030000054484202000000000000b00000000121070000000109102000000000000400000000021010000000006100000000000e103000000000210200000000000060000000000005000005200220100000000021000000000080100000000000e10100000000061000000000084102000000480e200000000000210200000314c42000000010440202000000000210400000000021040000000002104
  | 7, 56 => 0x401010000000002100000000000000100000000811020000000000004000000000e1010000000002102000000000610200000000021050000000006103000000000000e00000000c0101000000000a102000000000000400000000000010000000000009000000000a103000000000210400000000c4101000000000000600000000000060000000000007000000000a1000000000000006000000000210200000000000090000000000008000000480220200000000841000000000109102000000000e1010000000006102
  | 7, 57 => 0xe10000000038802010000050484202000000004110200000000c41040000000006100000000000210100000000000040000000000012000000000000500000000021020000000000006000000000a10600000000021060000000002102000000000000600000000c5101000000000a104000000480e200000000000e1020000000006103000000000000e0000000000004000000000210600000000021070000000000001000000000000b00000000c5102000000000a102000005201220100000048062000000000002100
  | 7, 58 => 0x9000000008510300000544c42000000000006106000000008410000000000841040000000006104000000008510200000000061050000000041101000000000a1030000000000006000000000610100000000c110100000000c8106000000000e104000000000610400000000021020000000012101000000001210500000000021000000000002104000000000000900000028062000000000084100000000000a10200000000811020000004802200000000000210300000000c810600000000021010000003908201
  | 7, 59 => 0x3806201000000001210600000000c4107000000000a1050000000080100000000000e104000000000210000000000c510000000000c010100000000061000000000006102000000000000700000000c4104000000000e10600000000000130000000085102000000000610400000038062010000000000012000000000610700000000000060000000000001000000000a107000000000e1050000000000000000000000000500000000000010000001802202000000000610300000314c420100000000c01010000053480202
  | 7, 60 => 0x700000000000070000053440202000000000a1030000000000001000000000210000000000c010000000000c410700000000121060000000109107000000000a10200000028062000000000002102000000000e10400000000061070000000000011000000000e10700000000000020000000081102000000000e1010000000041102000000000a1060000000006100000000000610000000000000060000002802200000000000000e00000544c4201000000000a10300000000021040000000000007000000000000b
  | 7, 61 => 0x61020000000012107000000000000a0000002802201000000000a10200000000061040000000000007000000000e10000000000000040000000000009000000000e10700000000000020000000006103000000000e1000000000085103000000000000f000000390920200000018022020000000085102000000000e102000000000e10000000000c510300000000021040000000000006000000000e10000000304c0201000000000210200000000000060000000000007000000000000a000000000a1020000000000009
  | 7, 62 => 0x40000000006105000000000210200000000061070000000000004000000000610300000104402000000000000008000000000e10000000000000050000000002101000000000000000000000000020000000000001000000000a107000000000210100000000000060000000000000000000000a10100000000c8106000000000000500000000000120000000002102000000000000f0000000000000000000000e101000000000a1040000000002100000000000000a000000000000500000000c81060000000012106
  | 7, 63 => 0x1210100000000411030000000000006000000000000000000534842020000000012101000000000000c00000000061000000000000006000000000000f0000000002100000000000a1020000000002103000000000210700000000000080000000000006000000000000200000000c4100000000000000f000000480a201000000008410200000000061020000000000006000000000a106000000000610300000000c41000000004802201000000000e103000000000a105000000000e1040000000012105000000000e105
  | 7, 64 => 0x8510200000000061010000020480202000000000e101000000000e10500000000061000000000000005000000001210000000000000080000000012100000000000000600000000801020000000012100000000000210300000000841020000000000000000000000e1010000000006100000000380220100000000000050000000006102000000001210600000000061010000000000006000000000e107000000000610300000504c4201000000000a1030000000109102000000000610400000000021060000000006102
  | 7, 65 => 0xe100000000000e100000000000a10400000000000070000000002101000000000e100000000380220000000000000010000000012101000000000e100000000000a10200000000061040000000000002000000010d10100000000061070000000000001000000000000400000000000060000000002101000000000000400000000c410100000000021020000000000002000000000000a000000000610600000000000020000000006100000000000000200000000061060000000002102000000000e10300000000c4104
  | 7, 66 => 0x80000000000004000000000e1050000000006101000000000e101000000000e104000000000e1000000000000004000000000e106000000380220200000000061000000000000001000000000e1070000000000009000000000000a00000000021020000000000000000000000000a00000000000060000000000004000000000000400000000401010000000041102000000000000a000000000000400000000c4107000000000000500000000c1100000000000610600000000000040000000002103000000000a102
  | 7, 67 => 0xe1060000000000000000000000e100000000380a202000000000000800000000c110100000000000080000000000006000000000000000000000021000000000000001000000000e100000000000a10200000000000090000000006104000000000000f0000000006105000000000000400000504c42000000000000004000000000210600000000021010000000000004000000000e1010000000041102000000000000a00000000021070000000000000000000000e1000000000000007000000008110200000000c8100
  | 7, 68 => 0x41103000000000a104000000001210000000000c1100000000000000c000000000610000000000000070000000002102000000000e10400000000c110200000504c42010000000000001000000380a202000000001210400000000c1101000000000a1020000000000004000000380220000000000121000000000040100000000008510300000019092020000000006106000000000e10300000000000160000000080103000000180220000000504c42010000000002102000000000000900000000000070000000000012
  | 7, 69 => 0xc5101000000000000d000000000210200000000121040000000006101000000480a202000000000a10400000000061020000000000007000000000000e00000038062000000002806201000000000000a00000000c0100000000008010000000018022010000000002100000000000000400000544c0201000000000000900000000000000000000002105000000001210100000000000060000000012102000000390820100000544c0201000000000a1030000000000011000000008010200000000000000000000000002
  | 7, 70 => 0xa10700000000000020000000085102000000000a10200000000000060000000000004000000000000c0000000006100000000000e100000000000000e00000000000000000000000006000000000000400000000021060000000002103000000000610600000000841030000000000009000000000e10300000000061060000000006100000000000a10200000000000000000000002107000000000000a000000000e10100000000000040000000000004000000000e107000000000000400000000000110000000006101
  | 7, 71 => 0x90000000041103000000000e100000000000e100000000000e101000000590920200000000841000000000002100000000001210000000000021020000054440201000000000e1000000000908201000000000000800000000121010000021484202000000000a104000000000000400000000121070000000012105000000000000100000000121010000000000009000000000210600000000021010000000002102000000000a103000000000a10400000000000040000000006103000000000000700000000c8100
  | 7, 72 => 0x544c4201000000000e10100000000000020000000081102000000000001300000000c11000000000002101000000480a20200000104402020000000000006000000000e10100000028062000000000041102000000010d1070000000012105000000010d10100000000021030000000006106000000180220200000000021060000000000000000000000a103000000000e10200000000c910300000000000070000000002107000000000000400000000000040000000006102000000000000200000001001040000000006105
  | 7, 73 => 0x304c02010000000000007000000000e102000000380a2020000000012102000000000000a000000000000a000000380620200000000000090000001908201000001044020200000000000060000000006100000000380a201000000000a10200000314c4201000000000a107000000000610200000000000060000000006106000000280620200000544c42010000000012100000000001210400000000000010000000000000000000000210500000000000040000000002100000000000610600000000021010000000002105
  | 7, 74 => 0x2100000000000a10400000000000020000000000004000000000210000000000000000000000006104000000480e201000000000000f0000000000009000000000000000000000411030000000000004000000000001300000000c41000000000002100000000000000700000000c810000000000c11020000000000008000000008410300000000851020000000000004000000000e101000000000e10200000000021060000000084100000000000e1020000050484202000000000001400000028062020000000000006
  | 7, 75 => 0x4802201000000000e1040000000000002000000000a102000000000e102000000000e1010000000000006000000000e100000000000e10100000000000060000000002102000000000000800000000061010000000000011000000000000e000000000210100000000851030000000041100000000000e10100000000c910300000000c1100000000280220100000000000050000000006104000000000e100000000000a102000000000a1020000053440202000000000e10000000000c810600000000121050000000006101
  | 7, 76 => 0x210000000000c110100000000000060000000006102000000000000e0000000006102000000000e105000000008510200000000000000000000000005000000000610400000000c51020000000000007000000380a200000000000000500000000000070000004802201000000000a100000000000e10400000000000040000000000005000000000610100000000021000000000000007000000380a20000000000021070000000000005000000000e100000000000210500000000c810600000000021010000000002100
  | 7, 77 => 0xe100000000000a1020000000006101000000000000a00000000000000000000085103000000000610100000000121000000004802200000000000e10400000000000000000000006101000000000000400000000000090000000000006000000000a10100000000c0101000000000a10100000000000160000000012106000000000000000000544c420000000038062020000000006102000000001210500000000c8106000000000a102000000480e2000000000000006000000000a10300000000000070000000006100
  | 7, 78 => 0x6107000000000610500000000000070000000002106000000000000200000000c5100000000000a1070000003806200000000000000e000000001210500000000061020000000041103000000000000f00000000021010000000012100000000004010000000000021010000000000015000000000000000000000021000000000000001000000000000a00000000c41010000000000001000000000e1000000000000009000000000e100000000000a100000000000e105000000000000400000000000060000000084104
  | 7, 79 => 0x480e202000000010810100000000000010000000084102000000000a10000000000411030000004802200000000280220200000009082010000000000006000000000000400000000000010000000000005000000190d20200000000c1101000000000e10000000544c4200000000004110200000000121010000000000004000000001210000000000811030000000012100000000000000f000000000610000000038062010000000012102000000000e101000000000a102000000000e102000000000a1020000000002102
  | 7, 80 => 0x401030000000000009000000380620100000000061000000000006100000000001210100000000c91030000000000004000000000a10500000000c01010000000000001000000000e10400000009082010000000002100000000000000700000000121020000000002101000000000e100000000008510300000000061020000000000012000000000000700000028062000000000000000000000000e10200000028062020000000000009000000010110200000000061010000000109102000000000e1000000000084103
  | 7, 81 => 0xa1070000050484202000000000000500000000000060000000000004000000000000e000000000e10100000000000000000000084106000000180220100000000c9102000000000000a00000000021000000000006102000000000210500000000000070000000002102000000000e1010000000012104000000000a100000000000a10300000000000090000000000004000000000000000000000000060000000000008000000008510200000048062000000000080102000000000e10400000000000080000000000005
  | 7, 82 => 0x1200000000c41040000000006100000000000210100000000061000000000000009000000000000a0000000081102000000000a10600000000021020000000002106000000000000e0000000002100000000000a10000000000811020000000002106000000001210000000000000060000000000008000000000000200000000c4104000000000210300000000061050000000000002000000000a1060000001802201000000380a2010000000000013000000480e200000000004110200000000811030000000006104
  | 7, 83 => 0xe106000000000a1040000000000006000000000210000000000021040000000000000000000000000700000104402020000000002100000000000e102000000000000200000000000070000003806200000000000e1060000000000000000000480e2010000000006100000000000000f000000000a10700000000c11000000000000013000000000e10400000000c5100000000000000f000000000e100000000000e101000000380620000000000021020000002802202000000000a1030000053480202000000000e101
  | 7, 84 => 0x21010000021484202000000000e1000000000000001000000000210100000000021040000000000004000004348520200000544c8200000005444020100000000c410400000000061020000000006101000000000a102000000000a1030000000006101000000000a10000000000000050000000006100000000000000f0000000000012000000000a10400000000021020000000006107000000000e1010000000002100000000000a10200000000121000000000012100000005444020100000000061040000000000011
  | 7, 85 => 0x9000005148020200000000c110300000000000110000000002102000000000e100000000000e101000000000610100000000000050000000081103000000000000200000000000010000000000001000000000e1070000000006100000000000a1030000000006100000000000610500000000021000000000006102000000000000700000000061070000000002105000000000a104000000000e100000000000e104000005444020100000000021070000000000006000000000210000000000000070000000041101
  | 7, 86 => 0x504c4200000000000a10600000019082010000000006102000000000000700000000121040000000000004000000000000500000000c41070000000000008000000000a106000000000610200000000000060000000002101000000000e10300000000021060000000002101000000000e107000000480620200000000061010000000085103000000000210700000000021030000000109102000000000a104000000480e202000000000000900000000061060000000002106000000000000500000000801000000000000004
  | 7, 87 => 0x40101000000000e1060000000000007000005348420200000000c110300000000021060000000002102000000000e106000000000000200000000021050000000000007000000000e105000000000210000000038022000000000006103000000010d102000000480a202000000000a103000000000e1050000000012100000000000e100000000000610000000019082010000000000011000000000e102000000000610100000000061000000000000004000000000000a000000000a10700000000000070000000041101
  | 7, 88 => 0x504c4201000000000e101000000000e101000000000000600000000121050000000002100000000000000300000000c510200000000061000000000000000000000000e10400000000000060000000000006000000000000f000000004010300000000061020000000109102000000000610200000000000050000000000009000005048420200000000021020000000041100000000000a10300000000121010000000002100000000000210400000000021000000000006105000000000e1020000000002100000000000a102
  | 7, 89 => 0xa000000380620100000000000040000000000011000000000000a000000000e10500000000000040000000002103000000000000600000000c0101000000000000e0000000108101000000008410200000000000160000003806202000000004110100000000000040000000000004000000000000a000005244020200000000021010000053480202000000000210000000000061040000000012106000000000000900000000811030000000000009000000000000200000000c51000000000002105
  | 7, 90 => 0x500000000021040000000002102000000000000a0000000000009000000000e100000000000a10400000000000060000000000004000000000e1000000000006103000000380220200000000000010000000000001000000000e100000000000e10000000000000070000000006107000000000a10400000000c9102000000000e104000000001210000000000121000000000012105000000000a102000000000610000000544c020100000000000070000000002105000000000a1020000000002100000000000e100
  | 7, 91 => 0x504c42000000000000005000000000000f0000000000005000005448420200000000c1101000000000000f000000000000500000000061020000000085102000000010910700000000021000000000000004000000000e107000000000000000000304c020000000000000060000000002105000000000e102000000004010000000000000020000000002102000000000000200000314c4200000000000210300000000c8106000000000e100000000000e1020000000012107000000000000900000000000050000004806200
  | 7, 92 => 0x6101000000480620200000000c5100000000000000900000000c8106000000000a102000000001210000000000411000000000000006000000000a10200000000021040000000080100000000480a2010000000000005000000480220200000000000020000000002104000000000000e00000000411000000000006103000000000a1040000000081103000000000000c000000000610100000000000060000000000011000000180220000000001081010000000006100000000000e10000000000121050000000000006
  | 7, 93 => 0xe1050000000002102000000000001100000000000040000000006102000000001210000000000000010000000006105000000380a20100000000401020000000002100000000000e1020000000000000000000000a10300000000000000000000085102000000000a10400000000061000000000000005000000000a1040000000012101000000000000200000000c4100000000000210200000000121060000000006103000000000000000000000121010000000000001000000000210700000000c8100000000000a100
  | 7, 94 => 0x20000000006101000000000e10300000000021000000000000004000000000e1000000000000000000000480e2010000000000004000000000000400000000061060000000000006000000000e106000001044020100000000000060000053484202000000000610600000000000130000000000004000000000e100000000000a107000000000610000000000021030000000000002000000000e103000000480e2000000000085102000000000a10200000304c0200000001044020100000000000040000000000001
  | 7, 95 => 0x210400000000021010000000081102000000380220200000000000090000000006107000000000e102000000004110200000204802020000054484202000000000e10500000000000010000000041101000000000610000000000000040000000002103000000000000f0000000084103000000380a20000000000000070000000002100000000000210600000000021000000000002101000000000000400000000411000000000006103000000001210700000000000040000000081102000000000000f00000544c4201
  | 7, 96 => 0x21020000003802202000000000000000000000411030000000012104000000000e10200000000801020000002802201000000000210200000000061000000000000004000000000e1000000000000004000000000000f00000000000060000021484202000000000000600000314c4200000000000001600000000000060000000041103000000000e107000000000e10200000000000020000000000013000000000a103000000004110100000000000040000000012107000000000000400000048022020000000000005
  | 7, 97 => 0x12101000000480220100000000c01000000000000007000000000000f00000000c11010000000000009000000000e100000000000610200000000121000000000006101000000000210200000000121010000000109102000000000e101000000380a20000000000021030000000084100000000000210100000000000000000000002101000000000610200000000c41040000000002100000000000a1020000002806200000000180220200000000c5102
  | 8, 0 => 0x40000000006101000000000000f0000000108101000000000000000000000801010000000041102000000000000000000000000040000000000004000000001210000000000000040000000000000000000000a1020000000000002000000000000500000000c410100000000000020000000000006000000008410100000000411000000000000006000000000000b000000000e10100000000841020000000000001000000000000400000000000010000000000000000000000000000000001091020000000000000
  | 8, 1 => 0x40000000000000000000004110000000001011010000000080100000000010d10000000000000000000000000002000000000a10200000000000050000000000001000000000000600000000000060000000101102000000000000700000000000060000000000004000000010d1000000000000003000000000610100000000000050000000000000000000000000200000000061010000000000007000000000000500000000c410000000000c8100000000000000200000000411010000000000008
  | 8, 2 => 0x10d1000000000101100000000004010100000000c5101000000000000100000000801020000000040101000000000000500000000000010000000000007000000000000600000000000030000000000006000000000000000000000000020000000105102000000000000500000000000070000000000000000000008010100000000021010000000000007000000000000100000000c510200000000000040000000000001000000000000d00000000021010000000000002000000000000600000000000000000000109102
  | 8, 3 => 0x10d102000000000000400000001051000000000000000000000004110100000000000000000000000002000000000000100000000000000000000000001000000000000a000000000e10100000000000000000000000003000000000000500000001011020000000000000000000000000200000000000020000000085102000000000000000000000000040000000000000000000000210000000000c41010000000000002000000000000000000000c5101000000000000600000001011010000000000005000000000e100
  | 8, 4 => 0x4000000000000000000000c010000000000061000000000000006000000004110100000000c91020000000101100000000008410100000000000020000000000004000000000000100000000121020000000000004000000000000400000000061000000000084101000000000000f0000000105101000000000000800000001051020000000081102000000000000f0000000000003000000000000200000000c110200000000c5102000000000e1000000000000004000000000e1020000000002100000000000000c
  | 8, 5 => 0x7000000000e1020000000000005000000000a10100000000000020000000000007000000010d10200000000c110000000000c91020000000000006000000001210200000000000040000000000001000000000610000000001051000000000000000000000000000000000000000010000000000000000000010910200000000c01010000000000000000000000000000000000c81000000000000005000000000000400000000000060000000000001000000000000300000000000070000000000002000000000e100
  | 8, 6 => 0x3000000000000000000000000050000000002102000000000a1000000000084100000000000000000000000801010000000000001000000000000200000000c810000000000000040000000000000000000000000100000000c11010000000000004000000008010100000000000010000000080102000000000a102000000000000000000000000020000000000004000000000000200000000000060000000000004000000008110200000000000060000000012101000000000000100000000061020000000000001
  | 8, 7 => 0x500000000411000000000105101000000008510200000000061010000000000002000000000000d0000000040102000000000000700000000061000000000000001000000010110100000000000040000000000001000000000000200000000c110000000000000000000000000000000000000000500000001011010000000000000000000000000400000000000020000000105101000000000000a00000000c41000000000000000000000000000400000000c8101000000000000200000000121000000000000006
  | 8, 8 => 0x10000000000001000000000e101000000000a1020000000002102000000000a1010000000012100000000008410100000000000070000000000007000000000000700000000411000000000000001000000000000500000000000010000000000004000000000e100000000000210200000000021000000000000000000000000610100000000000020000000000000000000000000600000000000090000000006102000000000000000000000c41000000000002102000000000000a00000000000070000000000009
  | 8, 9 => 0x21000000000040102000000000000000000000c010100000001051020000000006102000000000000200000000000030000000000007000000000000100000000000090000000000004000000000000600000000c110100000000000010000000000002000000000000100000000c41010000000000004000000000000200000000c5100000000000610000000000000030000000012101000000000000b000000000000600000000401000000000002101000000000000100000000021020000000000003000000010d100
  | 8, 10 => 0x1011000000000000002000000000000400000000000000000000000005000000000210000000000121020000000000000000000000000400000000c110100000000000070000000041100000000000000a00000000401010000000000004000000000a1020000000002100000000000a10200000000c5101000000000000000000000000060000000000000000000000000100000000000060000000040101000000010d1000000000000006000000010d102000000008510200000000c010100000000000040000000000000
  | 8, 11 => 0x101100000000000e100000000000000400000000c810100000000000020000000000002000000000000000000000000020000000000002000000000000400000000061010000000000005000000000000a0000000000004000000000000500000000000010000000000004000000000000100000000000010000000040102000000000000600000000c5100000000000000100000000000010000000000009000000000000400000000841000000000040100000000000000b000000000000300000000000060000000006102
  | 8, 12 => 0x12100000000000000100000000841000000000000005000000000000300000000000060000000105100000000000000400000000c11020000000000009000000000000000000000061000000000000002000000000000400000000000040000000000006000000000210100000000000020000000084102000000000000400000000000000000000002101000000010d101000000000000100000000000000000000000009000000008410100000000c81010000000000008000000000000000000001051000000000000000
  | 8, 13 => 0xc110000000000000050000000000004000000000e101000000000000200000000000000000000000001000000000e101000000000000300000000000000000000084102000000010d101000000000000600000000000000000000000006000000000000400000000c5101000000000000600000000000050000000000001000000000000a00000000000040000000080100000000000a10000000000000040000000040101000000000000000000000000070000000041102000000000000000000000000000000000000007
  | 8, 14 => 0x70000000080100000000008010200000000000040000000084101000000010110100000000000020000000000005000000000000300000000c110000000000c110200000000c9102000000000000400000000000020000000000007000000000000600000000000060000000000008000000000000300000000000110000000002102000000000000500000001091020000000000000000000010110000000000411020000000000000000000000a1000000000080101000000000000900000000000080000000084102
  | 8, 15 => 0x610200000000000000000000101102000000000000400000000c110000000000000060000000000000000000000000400000000c01000000000006100000000000000400000000000040000000041100000000000000400000000000060000000000000000000000000800000001091020000000000004000000000000100000000000000000000000008000000000a1020000000000008000000000610200000000000110000000000003000000000000500000000000020000000040100000000000000000000000c4100
  | 8, 16 => 0x801010000000080102000000000a10100000000021010000000000004000000010d100000000000001100000000000030000000000005000000010510200000000000070000000000002000000000000000000000c510200000000c910200000000021000000000006100000000000000700000000c01000000000109102000000000000600000000021000000000000002000000000000700000000000080000000000005000000000000400000000000070000000000006000000000000100000000000020000000000007
  | 8, 17 => 0x500000001051020000000101101000000000e101000000010d101000000000000800000000000060000000000001000000000000f000000000000900000000c51020000000000007000000000000400000000000090000000000004000000000000300000000c51000000000000000000000000000400000000000020000000002100000000000e10000000000401000000000000006000000000000500000000c0101000000000000700000000000010000000000001000000000000500000000000060000000101102
  | 8, 18 => 0x200000000801020000000000004000000000000c000000000a1020000000006101000000000e102000000000000a00000001081010000000000000000000010110000000000000030000000000006000000008410200000000000020000000000006000000000a1020000000000011000000010d10200000000c510000000000c81000000000000003000000000a10000000000c01000000000040100000000008010000000000000040000000000006000000000210200000000061000000000000007000000010d101
  | 8, 19 => 0x20000000000006000000000000500000000000070000000000000000000000000f00000000000020000000000002000000010d102000000000000300000000411020000000105100000000000000300000000000070000000000006000000000000500000000000000000000000011000000000000400000000411020000000084100000000000a10200000000c8101000000000000500000000811020000000000003000000000000300000000000010000000000007000000000000600000000000050000000081102
  | 8, 20 => 0xc4101000000000e101000000000000000000000000080000000000000000000000000300000000000070000000000002000000000a1000000000000002000000000a10200000000061020000000000003000000000000600000000c4100000000010d10200000000000000000000109102000000000000600000000c0101000000000e10000000000000020000000000006000000000000400000000c8100000000008110200000000000010000000084100000000000000b00000000000010000000006102000000000e102
  | 8, 21 => 0x50000000000000000000000000600000000c810100000000000000000000000004000000010110200000000801000000000000004000000000e1000000000000009000000000000000000000000060000000006102000000000e100000000000000400000000411010000000000000000000000000900000000000050000000002101000000000000400000000021020000000000003000000000000a000000000000400000000c110000000000021010000000000004000000000000200000000411000000000080100
  | 8, 22 => 0x40000000108101000000000000500000000c91020000000000002000000010510200000000411020000000000000000000001210200000000000070000000000006000000000000f00000000000000000000002102000000000000100000000801010000000000005000000000e1010000000000002000000010d100000000000000000000000851020000000000007000000000000b000000000e1010000000040102000000000000200000000000010000000000001000000008410200000000000000000000000006
  | 8, 23 => 0x21000000000000006000000000e1010000000000003000000000000200000000000040000000000000000000000000700000000000070000000000007000000000000000000000000000000000000001000000000000700000000851020000000000002000000000000700000000000090000000040102000000000000500000000061000000000000004000000000000400000000061010000000000000000000010810100000000000010000000000000000000000000300000000061010000000000001
  | 8, 24 => 0x500000000c510000000000c9102000000000000400000001051000000000000003000000000000700000000811020000000012102000000004010000000000000040000000000004000000000000000000000000010000000000000000000000000f00000000c510100000000000070000000000001000000000000200000000000040000000000007000000000000f00000000000000000000000006000000000000000000000c01000000000012100000000000000a000000000000100000000000060000000101100
  | 8, 25 => 0x700000000000000000000000000000000004110100000000000040000000000002000000000000500000000c810100000000061020000000000005000000000000100000000000030000000000000000000000000400000000c4101000000000000300000000000030000000000001000000000000200000000c410100000000000010000000000006000000000000600000001051010000000000000000000010d10100000000c010000000000000020000000000005000000000000200000000000060000000000006
  | 8, 26 => 0x200000000000020000000000001000000000a10200000000000010000000000001000000000000700000000c810000000000c110000000000c11020000000000007000000000a10100000000c5102000000000000300000000061020000000000006000000000000200000000000070000000000001000000008410000000000000000000000000002000000000000300000000c5102000000000a10000000000021020000000006100000000000000f00000000411010000000000004000000000001100000000c8100
  | 8, 27 => 0x6000000010d101000000000000f000000000000100000000000010000000000007000000000e10000000000c11020000000000003000000000610200000000000010000000000002000000000210200000000021000000000000002000000000000700000000c0101000000000000300000000021020000000000005000000000e10100000000000010000000101102000000000000600000000c1101000000000000a0000000000001000000000000900000000000000000000000003000000000a1020000000012101
  | 8, 28 => 0xa102000000000610100000000000000000000080102000000000000500000000000070000000002100000000000000100000000000010000000000004000000000e100000000000e1000000000006100000000000000200000000c410000000000000000000000080100000000000000300000000000010000000000002000000000210100000000811020000000000001000000000000600000000851020000000002102000000000e10200000000401020000000000002000000000000500000000000040000000000007
  | 8, 29 => 0x60000000084102000000000000700000000801020000000040100000000000e10000000000061010000000000000000000000000600000001081010000000002101000000000000f0000000000007000000000000b0000000006102000000000000600000000000020000000000001000000000000100000000000020000000000005000000000000100000001051010000000000006000000000610100000001051010000000002100000000000e1010000000002100000000000610000000000000000000000000007
  | 8, 30 => 0x7000000000000100000000000020000000000001000000000a10100000000000010000000002101000000000000400000000021020000000000000000000000000000000001051000000000006100000000000000000000000411020000000000006000000000000200000000c510100000000000010000000000009000000000000500000000000020000000040101000000000000500000000000000000000000005000000000000100000000c510000000000c11020000000000005000000000e1000000000006102
  | 8, 31 => 0x1210000000000000020000000085102000000000000500000000c510000000000000040000000000002000000000000500000000841000000000000006000000004010200000000c110100000000c4100000000000000000000000c110100000000c010000000000000070000000012101000000000000b00000000000080000000000001000000000000000000000021010000000012101
  | 9, 0 => 0x10000000000001000000000000200000000000010000000000000000000000000200000000000000000000000002000000000000200000000000000000000000000000000000000100000000000000000000000001000000000000200000000000000000000000002
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 13 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_47 roots_47 8 s ws hint
  | 1 => checkCutEntry dom_31 roots_31 8 s ws hint
  | 2 => checkCutEntry dom_59_4 roots_59_4 8 s ws hint
  | 3 => checkCutEntry dom_27_4 roots_27_4 7 s ws hint
  | 4 => checkCutEntry dom_61 roots_61 7 s ws hint
  | 5 => checkCutEntry dom_47_16 roots_47_16 7 s ws hint
  | 6 => checkCutEntry dom_55 roots_55 7 s ws hint
  | 7 => checkCutEntry dom_62 roots_62 7 s ws hint
  | 8 => checkCutEntry dom_31_32 roots_31_32 6 s ws hint
  | 9 => checkCutEntry dom_61_2 roots_61_2 6 s ws hint
  | 10 => checkCutEntry dom_62_1 roots_62_1 6 s ws hint
  | 11 => checkCutEntry dom_15_48 roots_15_48 5 s ws hint
  | 12 => checkCutEntry dom_23 roots_23 5 s ws hint
  | 13 => checkCutEntry dom_29 roots_29 5 s ws hint
  | 14 => checkCutEntry dom_45_2 roots_45_2 5 s ws hint
  | 15 => checkCutEntry dom_53_2 roots_53_2 5 s ws hint
  | 16 => checkCutEntry dom_57_4 roots_57_4 5 s ws hint
  | 17 => checkCutEntry dom_30_32 roots_30_32 5 s ws hint
  | 18 => checkCutEntry dom_30_1 roots_30_1 5 s ws hint
  | 19 => checkCutEntry dom_46_1 roots_46_1 5 s ws hint
  | 20 => checkCutEntry dom_58_4 roots_58_4 5 s ws hint
  | 21 => checkCutEntry dom_15 roots_15 5 s ws hint
  | 22 => checkCutEntry dom_39 roots_39 5 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_61 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_62 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31_32 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_61_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_62_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_48 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_29 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_45_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_53_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_57_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_30_32 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_30_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_46_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_58_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_63 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := []
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
private theorem z4_0 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 14 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 14 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 14 → Z 5 i = true := z5_0
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
private theorem z6_96 : ∀ i, 96 ≤ i → i < 107 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 11 96 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 107 → Z 6 i = true := (range_split (range_split (range_split z6_0 z6_16) (range_split z6_32 z6_48)) (range_split (range_split z6_64 z6_80) z6_96))
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
private theorem z7_384 : ∀ i, 384 ≤ i → i < 389 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 384 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 389 → Z 7 i = true := (range_split (range_split (range_split (range_split (range_split z7_0 z7_16) (range_split z7_32 z7_48)) (range_split (range_split z7_64 z7_80) (range_split z7_96 z7_112))) (range_split (range_split (range_split z7_128 z7_144) (range_split z7_160 z7_176)) (range_split (range_split z7_192 z7_208) (range_split z7_224 z7_240)))) (range_split (range_split (range_split (range_split z7_256 z7_272) (range_split z7_288 z7_304)) (range_split (range_split z7_320 z7_336) (range_split z7_352 z7_368))) z7_384))
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
private theorem z8_192 : ∀ i, 192 ≤ i → i < 208 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_208 : ∀ i, 208 ≤ i → i < 224 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_224 : ∀ i, 224 ≤ i → i < 227 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 224 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 227 → Z 8 i = true := (range_split (range_split (range_split (range_split z8_0 z8_16) (range_split z8_32 z8_48)) (range_split (range_split z8_64 z8_80) (range_split z8_96 z8_112))) (range_split (range_split (range_split z8_128 z8_144) (range_split z8_160 z8_176)) (range_split (range_split z8_192 z8_208) z8_224)))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_0 : ∀ i, 0 ≤ i → i < 16 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_16 : ∀ i, 16 ≤ i → i < 27 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 11 16 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 27 → Z 9 i = true := (range_split z9_0 z9_16)
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

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 13]⟩], 16⟩

theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by
  simp [wit, PEqualNP.MetaComplexity.Monotone2]

theorem wit_sz : wit.size ≤ 11 := by decide

set_option maxRecDepth 40000 in
theorem wit_ev : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4242599040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_63.testBit r.val = (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4242599040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) (pt6 r.val) := by decide +kernel

theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4242599040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 11 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4242599040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_63 11 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_40507_aux

theorem PEqualNP.Outside.L_meta_40507 :
  ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4242599040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4242599040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  exact ⟨PEqualNP.Outside.L_meta_40507_aux.wit, PEqualNP.Outside.L_meta_40507_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_40507_aux.wit_sz (PEqualNP.Outside.L_meta_40507_aux.lower s hs), PEqualNP.Outside.L_meta_40507_aux.wit_ev⟩
