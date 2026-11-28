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

namespace PEqualNP.Outside.L_meta_38083_aux

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

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfcfcfcc0fcccf0c0fcfcfcc0fcccf0c0fcfcfcc0fcccf0c0fcfcfcc0fcccf0c0
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_31_32 : Nat := 0xffffffff00000000
def goal_31_32 : Nat := 0xfefefee8fefefee8fefefee8fefefee8fefefee8fefefee8fefefee8fefefee8
def roots_31_32 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xfee8fee8fae8fae8fee8fee8fae8fae8fee8fee8fae8fae8fee8fee8fae8fae8
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_15_32 : Nat := 0xffff00000000
def goal_15_32 : Nat := 0xfee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8
def roots_15_32 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0]

def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xfeeefae8feeefae8feeefae8feeefae8feeefae8feeefae8feeefae8feeefae8
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xeeeeee88eeeeaa88eeeeee88eeeeaa88eeeeee88eeeeaa88eeeeee88eeeeaa88
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_27 : Nat := 0xf0f0f0f
def goal_27 : Nat := 0xeeeeaa88eeeeaa88eeeeaa88eeeeaa88eeeeaa88eeeeaa88eeeeaa88eeeeaa88
def roots_27 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_43 : Nat := 0xf0f00000f0f
def goal_43 : Nat := 0xee88ee88aa88aa88ee88ee88aa88aa88ee88ee88aa88aa88ee88ee88aa88aa88
def roots_43 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_23 : Nat := 0xff00ff
def goal_23 : Nat := 0xeeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8
def roots_23 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_27_32 : Nat := 0xf0f0f0f00000000
def goal_27_32 : Nat := 0xeeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88
def roots_27_32 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefee8e8eeeee8e8fefee8e8eeeee8e8fefee8e8eeeee8e8fefee8e8eeeee8e8
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_23_32 : Nat := 0xff00ff00000000
def goal_23_32 : Nat := 0xfefee8e8fefee8e8fefee8e8fefee8e8fefee8e8fefee8e8fefee8e8fefee8e8
def roots_23_32 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfafafaa0faaafaa0fafafaa0faaafaa0fafafaa0faaafaa0fafafaa0faaafaa0
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_29 : Nat := 0x33333333
def goal_29 : Nat := 0xfaaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0
def roots_29 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_53 : Nat := 0x33003300330033
def goal_53 : Nat := 0xfafaa0a0aaaaa0a0fafaa0a0aaaaa0a0fafaa0a0aaaaa0a0fafaa0a0aaaaa0a0
def roots_53 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_46 : Nat := 0x555500005555
def goal_46 : Nat := 0xfcc0fcc0f0c0f0c0fcc0fcc0f0c0f0c0fcc0fcc0f0c0f0c0fcc0fcc0f0c0f0c0
def roots_46 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_54 : Nat := 0x55005500550055
def goal_54 : Nat := 0xfcfcc0c0ccccc0c0fcfcc0c0ccccc0c0fcfcc0c0ccccc0c0fcfcc0c0ccccc0c0
def roots_54 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_30_32 : Nat := 0x5555555500000000
def goal_30_32 : Nat := 0xfcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0
def roots_30_32 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfefefee8feeefae8fefefee8feeefae8fefefee8feeefae8fefefee8feeefae8
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

namespace S_62
def pairsG : List (Nat × Nat) := [(2, 6), (2, 18), (4, 6), (4, 12), (8, 12), (10, 14), (10, 26), (10, 42), (16, 18), (20, 22), (20, 28), (20, 52), (24, 26), (24, 28), (34, 38), (34, 42), (34, 50), (36, 38), (36, 44), (36, 52), (40, 42), (40, 44), (48, 50), (48, 52), (56, 58), (56, 60)]
def r1sG : List Nat := [2, 2, 4, 4, 8, 10, 10, 10, 16, 20, 20, 20, 24, 24, 34, 34, 34, 36, 36, 36, 40, 40, 48, 48, 56, 56]
def r2sG : List Nat := [6, 18, 6, 12, 12, 14, 26, 42, 18, 22, 28, 52, 26, 28, 38, 42, 50, 38, 44, 52, 42, 44, 50, 52, 58, 60]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [4407040281606, 11012869326348, 44126830726186, 52931211691572, 11012699982854, 21999429879314, 44023753740842, 37426683972650, 61727304713780, 52931345909300, 61727438931508, 4407308717062, 39729121332230, 52862493787700, 52862628005428]
def xsM : List Nat := roots_62.map (· &&& dom_62)
def goalM : Nat := goal_62 &&& dom_62
def NN : Nat → Nat
  | 4 => 3
  | 5 => 28
  | 6 => 19
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xa91103de7e8ff0066bf7855d
  | 5, 0 => 0xe324ca91debd4524d91db3e8d3b5bfdece4dc514aab11039a91103dea640536d9dd0d40c9830476e8d4721e18c3fc1847adfbf29762415b258d74d135803aed04fa943704b89a7b448d34d1947ccf1b445028db1449cb7de22b0e5b51901fc09174662b6107902ba0ebf8666039f5043
  | 6, 0 => 0xe324ca91cd5dd687b2cded72a91103de9b7d27a89352573f929bbc978920bf4e5c81a6f046ecb51545028db139f193b0276abb79247a69281b12df040fe7d2510ebf866605cc22e2058f0e8d
  | 7, 0 => 0xa91103de
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x44440000444400000000000000000000000000000000000000000000000000004400440044004400000000000000000000000000000000000000000000000000404040404040404000000000000000000000000000000000000000000000000011111111111111110000000000000000000000000000000000000000000000000505050505050505000000000000000000000000000000000000000000000000005500550055005500000000000000000000000000000000000000000000000000005555000055550000000000000000000000000000000000000000000000000000000055555555
  | 0, 1 => 0x54545454000000000000000000000000000000000000000000000000000000005444544454445444000000000000000000000000000000000000000000000000540054005400540000000000000000000000000000000000000000000000000050505050505050500000000000000000000000000000000000000000000000005050000050500000000000000000000000000000000000000000000000000000500050005000500000000000000000000000000000000000000000000000000044444444444444440000000000000000000000000000000000000000000000004444444400000000
  | 0, 2 => 0x55505550555055500000000000000000000000000000000000000000000000005550555000000000000000000000000000000000000000000000000000000000554455445544554400000000000000000000000000000000000000000000000055005500550055000000000000000000000000000000000000000000000000005500550050005000000000000000000000000000000000000000000000000000550055000000000000000000000000000000000000000000000000000000000055000000550000000000000000000000000000000000000000000000000000005454545454545454
  | 0, 3 => 0x55555500550055000000000000000000000000000000000000000000000000005555550000000000000000000000000000000000000000000000000000000000555550505555505000000000000000000000000000000000000000000000000055555000555550000000000000000000000000000000000000000000000000005555444455554444000000000000000000000000000000000000000000000000555540405555404000000000000000000000000000000000000000000000000055550000555500000000000000000000000000000000000000000000000000005555000000000000
  | 0, 4 => 0x55555555550055000000000000000000000000000000000000000000000000005555555555000000000000000000000000000000000000000000000000000000555555554444444400000000000000000000000000000000000000000000000055555555444400000000000000000000000000000000000000000000000000005555555540404040000000000000000000000000000000000000000000000000555555550000000000000000000000000000000000000000000000000000000055555500555555000000000000000000000000000000000000000000000000005555550055550000
  | 0, 5 => 0x5555555555550000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x2265430950287cc25009a13094
  | 5, 0, 0 => 0x8995040d62694309589954c196271430958994cc2559594309550c241015e65430958995090d6250c101595950c215950c100588c242056265438c589430905646543095
  | 5, 0, 1 => 0x6543090162654405589b50c1d6285130958d950c25625090c1589950c2567652309599950c256264d30956543cc25628143095
  | 6, 0, 0 => 0x22654309589950c2c9689950c28968995d4309689950c242689951030969626543096022654243589950c24568a16543096a22654309689d654309689950c243602250c241589961430968995113096
  | 6, 0, 1 => 0x1950c240589950c240689950c2486
  | 7, 0, 0 => 0x226543095
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
  | 0, 0 => 0xe000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003fe3f1c0000000000000000000000000000000000000000000000000000000003f1f1f30000000000000000000000000000000000000000000000000000000000cfcf0f00000000000000000000000000000000000000000000000000000000003fc0ff0000000000000000000000000000000000000000000000000000000000003fff
  | 0, 1 => 0xfc000000000000000000000000000000000000000000000000000000000000001c0e300000000000000000000000000000000000000000000000000000000000000e000000000000000000000000000000000000000000000000000000000000e0e0c0000000000000000000000000000000000000000000000000000000000000e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c0e3000000000000000000000000000000000000000000000000000000000001c000
  | 0, 2 => 0x33e3efc00000000000000000000000000000000000000000000000000000000033e0000000000000000000000000000000000000000000000000000000000000331f0f300000000000000000000000000000000000000000000000000000000033030f000000000000000000000000000000000000000000000000000000000033000000000000000000000000000000000000000000000000000000000000003300000000000000000000000000000000000000000000000000000000000000300300000000000000000000000000000000000000000000000000000000000000fceef
  | 0, 3 => 0x3f030f00000000000000000000000000000000000000000000000000000000003f000000000000000000000000000000000000000000000000000000000000003ce3f0c0000000000000000000000000000000000000000000000000000000003c03f000000000000000000000000000000000000000000000000000000000003c1ffe30000000000000000000000000000000000000000000000000000000003c03f000000000000000000000000000000000000000000000000000000000003c03f000000000000000000000000000000000000000000000000000000000003c00000
  | 0, 4 => 0x3fff0f00000000000000000000000000000000000000000000000000000000003fff0000000000000000000000000000000000000000000000000000000000003ffc0e30000000000000000000000000000000000000000000000000000000003ffc0000000000000000000000000000000000000000000000000000000000003ffc0000000000000000000000000000000000000000000000000000000000003ffc0000000000000000000000000000000000000000000000000000000000003f03ff00000000000000000000000000000000000000000000000000000000003f03f00
  | 0, 5 => 0x3ffff00
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x141134200000000000000000000000000000000000000000000000000000000011090e000000000000000000000000000000000000000000000000000000000000242250000000000000000000000000000000000000000000000000000000002ac2c1800000000000000000000000000000000000000000000000000000000015191c20000000000000000000000000000000000000000000000000000000000cb4b07000000000000000000000000000000000000000000000000000000000036c0bd000000000000000000000000000000000000000000000000000000000000377f
  | 0, 1 => 0x3ffc880000000000000000000000000000000000000000000000000000000000377f7ff000000000000000000000000000000000000000000000000000000000334b4f80000000000000000000000000000000000000000000000000000000002ae6e3d0000000000000000000000000000000000000000000000000000000002882e000000000000000000000000000000000000000000000000000000000002242438000000000000000000000000000000000000000000000000000000000153d3e7000000000000000000000000000000000000000000000000000000000153c080
  | 0, 2 => 0x3befefd0000000000000000000000000000000000000000000000000000000003bec880000000000000000000000000000000000000000000000000000000000377f7ff000000000000000000000000000000000000000000000000000000000334b4f8000000000000000000000000000000000000000000000000000000000334a4b8000000000000000000000000000000000000000000000000000000000334808000000000000000000000000000000000000000000000000000000000030034400000000000000000000000000000000000000000000000000000000003ffffff
  | 0, 3 => 0x3fdbcf80000000000000000000000000000000000000000000000000000000003fd88800000000000000000000000000000000000000000000000000000000003ef7f7f0000000000000000000000000000000000000000000000000000000003ed3f7a0000000000000000000000000000000000000000000000000000000003dbffe70000000000000000000000000000000000000000000000000000000003cb7f670000000000000000000000000000000000000000000000000000000003c93f420000000000000000000000000000000000000000000000000000000003c90800
  | 0, 4 => 0x3fffcf80000000000000000000000000000000000000000000000000000000003fffcc00000000000000000000000000000000000000000000000000000000003ffdbe70000000000000000000000000000000000000000000000000000000003ffdbc20000000000000000000000000000000000000000000000000000000003ffcaa50000000000000000000000000000000000000000000000000000000003ffc8800000000000000000000000000000000000000000000000000000000003fdbffa0000000000000000000000000000000000000000000000000000000003fdbfc2
  | 0, 5 => 0x3ffffc2
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 41 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 41 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 41 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 41 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_62 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_62 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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
  scr dom_62 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_62 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_62 roots_62 goal_62 8 := by
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

theorem low_62 : Lower dom_62 roots_62 goal_62 8 := S_62.noCircuit

namespace S_31_32
def pairsG : List (Nat × Nat) := [(33, 35), (33, 37), (33, 41), (33, 49), (34, 35), (34, 38), (34, 42), (34, 50), (36, 37), (36, 38), (36, 44), (36, 52), (40, 41), (40, 42), (40, 44), (48, 49), (48, 50), (48, 52), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [33, 33, 33, 33, 34, 34, 34, 34, 36, 36, 36, 36, 40, 40, 40, 48, 48, 48, 56, 56, 56]
def r2sG : List Nat := [35, 37, 41, 49, 35, 38, 42, 50, 37, 38, 44, 52, 41, 42, 44, 49, 50, 52, 57, 58, 60]
def mpG : Nat := 0x1fffff
def pool6G : List Nat := [37525735744803, 44135640278316, 44127050343210, 39729003569958, 44122772218665, 39724725445413, 37525803050531, 39724826503459, 37525803116838, 52931733824820, 37525803116835]
def xsM : List Nat := roots_31_32.map (· &&& dom_31_32)
def goalM : Nat := goal_31_32 &&& dom_31_32
def NN : Nat → Nat
  | 3 => 5
  | 4 => 19
  | 5 => 32
  | 6 => 13
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x5700f3434ef0d4f1487424c52ddb2d7c169b33d8
  | 4, 0 => 0x75a2902570098b3e6ad2ce7e6151fc205f5ce35159ebddb6550bda743c333842303673832bbbc96820ec3cb51f595f0b1d9046ec1122d21f0bc6adc00920a6b907c952e203b8452f029bd4bf
  | 5, 0 => 0xfb45fe20cce3300ecb3ae2afa3f473a9755f4b167523d75b6ad2ce7e64f09133643ce693608578e95f5ce3515c39dabe557cf2c0550bda74482cfb7b3a877c603514590531f0505630c7babe250d0c12239e6b931cea898f137e182610bda8ec0c70127509f3bf1207c952e206fdef450467640c0433e158035c036f02a103ae
  | 6, 0 => 0xccf2db857523d75b608578e95fcdfb9d5f5ce351550bda74527e04583c41593330c7babe2f5e14ef273b926c1dcf2103059706fd
  | 7, 0 => 0x5f5ce351
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x555555550000000000000000000000000000000000000000000000000000000033333333000000000000000000000000000000000000000000000000000000000f0f0f0f0000000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ff0000000000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000ff0000000000000000000000000000000000000000000000000000000000000000ff00000000
  | 0, 1 => 0xf0f0000000000000000000000000000000000000000000000000000000000000eeeeeeee00000000000000000000000000000000000000000000000000000000ecececec00000000000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000cccccc0000000000000000000000000000000000000000000000000000000000c0c0c0c000000000000000000000000000000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000000aa00aa0000000000
  | 0, 2 => 0xfcfcfccc00000000000000000000000000000000000000000000000000000000fcccfccc00000000000000000000000000000000000000000000000000000000fafafafa00000000000000000000000000000000000000000000000000000000fafafaf000000000000000000000000000000000000000000000000000000000fafaaaaa00000000000000000000000000000000000000000000000000000000faf0faf000000000000000000000000000000000000000000000000000000000f8f8f8f800000000000000000000000000000000000000000000000000000000f0f0f0f000000000
  | 0, 3 => 0xffffc0c000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000fff0fff000000000000000000000000000000000000000000000000000000000ffaaffaa00000000000000000000000000000000000000000000000000000000ff00ffff00000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000fcfcfcfc00000000
  | 0, 4 => 0xfffffff000000000000000000000000000000000000000000000000000000000ffffffcc00000000000000000000000000000000000000000000000000000000ffffffc000000000000000000000000000000000000000000000000000000000ffffffaa00000000000000000000000000000000000000000000000000000000ffffff0000000000000000000000000000000000000000000000000000000000fffff0f000000000000000000000000000000000000000000000000000000000fffff00000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x2244e30265c939a56094024609389854e4
  | 4, 0, 0 => 0x1e691391e690309502240d25008903094022246150089828949a540c255e69854e501f698250040c1c0402440c2525898409502250c250040c240402248c250079d5894
  | 4, 0, 1 => 0x9502c9489854c25408903074
  | 5, 0, 0 => 0x1b690309502240c2425022790309502240c246501e4091845022850309502240c28950238903095020690309501e710308500040c2404022690307501e68c1c5579a55038c601e69340c501f6903095
  | 5, 0, 1 => 0x2265030950103091025010309081501a40c240502240c240501e6903075000890307401a40c243501e690349501a40c242501e690309502240c2c9502240f3095000890309402240e309501e6982895
  | 6, 0, 0 => 0x89e690309601e690307501a40c242579a40f309601e6903095000890309479a40e309679a40c2426022790309579a40c246685e690309679a40c289679a6503096
  | 7, 0, 0 => 0x1e6903095
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 28
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
  | 0, 0 => 0x1ffff000000000000000000000000000000000000000000000000000000000001fff0f00000000000000000000000000000000000000000000000000000000001ff0ff0000000000000000000000000000000000000000000000000000000000038fff00000000000000000000000000000000000000000000000000000000000380000000000000000000000000000000000000000000000000000000000000007fff00000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000000fff
  | 0, 1 => 0xff00000000000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0000000000000000000000000000000000000000000000000000000000000000
  | 0, 2 => 0xf000000000000000000000000000000000000000000000000000000000000000f00000000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000f00000000000000000000000000000000000000000000000000000000000000000f0000000000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000000f00
  | 0, 3 => 0x1f800000000000000000000000000000000000000000000000000000000000001f800000000000000000000000000000000000000000000000000000000000001c7f0000000000000000000000000000000000000000000000000000000000001c700f00000000000000000000000000000000000000000000000000000000001c7fff00000000000000000000000000000000000000000000000000000000001c700000000000000000000000000000000000000000000000000000000000001c00000000000000000000000000000000000000000000000000000000000000000ff0
  | 0, 4 => 0x1fff0000000000000000000000000000000000000000000000000000000000001ff0f000000000000000000000000000000000000000000000000000000000001ff00000000000000000000000000000000000000000000000000000000000001ff00f00000000000000000000000000000000000000000000000000000000001ff00000000000000000000000000000000000000000000000000000000000001f8f0000000000000000000000000000000000000000000000000000000000001f8000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1b6ee0000000000000000000000000000000000000000000000000000000000016dd0e00000000000000000000000000000000000000000000000000000000000db0dd0000000000000000000000000000000000000000000000000000000000038bbb0000000000000000000000000000000000000000000000000000000000038888000000000000000000000000000000000000000000000000000000000000777700000000000000000000000000000000000000000000000000000000000074440000000000000000000000000000000000000000000000000000000000000333
  | 0, 1 => 0x12080000000000000000000000000000000000000000000000000000000000000db3ff00000000000000000000000000000000000000000000000000000000000923f300000000000000000000000000000000000000000000000000000000000922f100000000000000000000000000000000000000000000000000000000000920c00000000000000000000000000000000000000000000000000000000000000220000000000000000000000000000000000000000000000000000000000004911f0000000000000000000000000000000000000000000000000000000000041004
  | 0, 2 => 0x1b6ef100000000000000000000000000000000000000000000000000000000001966f1000000000000000000000000000000000000000000000000000000000016df3f000000000000000000000000000000000000000000000000000000000016df2e000000000000000000000000000000000000000000000000000000000016991f0000000000000000000000000000000000000000000000000000000000165f260000000000000000000000000000000000000000000000000000000000124f330000000000000000000000000000000000000000000000000000000000124f22
  | 0, 3 => 0x1f8aa800000000000000000000000000000000000000000000000000000000001f888800000000000000000000000000000000000000000000000000000000001e7f6600000000000000000000000000000000000000000000000000000000001cf55f00000000000000000000000000000000000000000000000000000000001c777700000000000000000000000000000000000000000000000000000000001c744400000000000000000000000000000000000000000000000000000000001c000000000000000000000000000000000000000000000000000000000000001b6ff3
  | 0, 4 => 0x1fffee00000000000000000000000000000000000000000000000000000000001ffefd00000000000000000000000000000000000000000000000000000000001ffeec00000000000000000000000000000000000000000000000000000000001ffddf00000000000000000000000000000000000000000000000000000000001ffccc00000000000000000000000000000000000000000000000000000000001fcfaa00000000000000000000000000000000000000000000000000000000001fcc88
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_31_32 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_31_32 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 5 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 5 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 5 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 16 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_16 : ∀ i, 16 ≤ i → i < 19 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 16 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 19 → Z 4 i = true := (range_split z4_0 z4_16)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_16 : ∀ i, 16 ≤ i → i < 32 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 16 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 32 → Z 5 i = true := (range_split z5_0 z5_16)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 13 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 13 0 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 13 → Z 6 i = true := z6_0
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
  scr dom_31_32 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_31_32 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_31_32 roots_31_32 goal_31_32 8 := by
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

theorem low_31_32 : Lower dom_31_32 roots_31_32 goal_31_32 8 := S_31_32.noCircuit

namespace S_47
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (2, 3), (2, 6), (4, 5), (4, 6), (4, 12), (8, 9), (8, 12), (10, 11), (10, 14), (10, 42), (33, 35), (33, 37), (33, 41), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (36, 44), (40, 41), (40, 42), (40, 44)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 4, 4, 4, 8, 8, 10, 10, 10, 33, 33, 33, 34, 34, 34, 36, 36, 36, 40, 40, 40]
def r2sG : List Nat := [3, 5, 9, 3, 6, 5, 6, 12, 9, 12, 11, 14, 42, 35, 37, 41, 35, 38, 42, 37, 38, 44, 41, 42, 44]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [37388294685955, 10999984423689, 4402476484869, 44126511366954, 11000085088515, 4406653551366, 4407310289926, 11012969991174, 36301735463173, 11012869326348, 37426362385706, 37426412913962, 39587284386565, 44023482287402, 8813290259724, 8800455886089]
def xsM : List Nat := roots_47.map (· &&& dom_47)
def goalM : Nat := goal_47 &&& dom_47
def NN : Nat → Nat
  | 3 => 1
  | 4 => 8
  | 5 => 44
  | 6 => 19
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x7359feac
  | 4, 0 => 0xa4f9c590871356397e10ec9377c04265624656ad2af35fd40f1fce070b1c9d1e
  | 5, 0 => 0xf443723eee021f3cec8f6e8dca341921a7e1de7ea1c0b4b896a733ef9667f880955faf5b91ca44208cad58428888432e87dd0f4f855d4d367b1ce2dc76f2530174be6f4b6fd1ad856fa9a6b36e75ebdf67ae8f755b61388b53d7f7b54bffd7464a268dfc48c0935144dbae4a42829c103ce6ec40391be2b23147f1812bcc03e1216a94f31b2929df167583a50fdea1890f1fce070afba44c040f1dd303b0c7d70335d817029f811a0218bf2701458476
  | 6, 0 => 0xe9082d54e505bdfaa7da18faa1c0b4b8a1712e8b8c5e12728888432e7ea52a9a72657d5c6949f7d6686e9bda5b61388b4d7877b94a268dfc391be2b2270b03de160058940f1fce070da784ce
  | 7, 0 => 0xf1fce07
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x555500000000000000000000000000000000000000000000000000000000000033330000333300000000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000000000000000000000000000000000000ff0000ffff000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000ff000000000000000000000000000000000000000000000000000000000000000f0f
  | 0, 1 => 0xcccc000000000000000000000000000000000000000000000000000000000000cc000000cc000000000000000000000000000000000000000000000000000000cc00000000000000000000000000000000000000000000000000000000000000aaaa0000aaaa0000000000000000000000000000000000000000000000000000aaaa000000000000000000000000000000000000000000000000000000000000aa000000aa000000000000000000000000000000000000000000000000000000a0a00000a0a00000000000000000000000000000000000000000000000000000555500005555
  | 0, 2 => 0xf0f00000f0f00000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000eeaa0000aaaa0000000000000000000000000000000000000000000000000000ecec0000ecec0000000000000000000000000000000000000000000000000000cccc0000cccc0000000000000000000000000000000000000000000000000000cccc000088880000000000000000000000000000000000000000000000000000cccc000000cc
  | 0, 3 => 0xff000000fa000000000000000000000000000000000000000000000000000000ff00000033000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000fccc0000fccc0000000000000000000000000000000000000000000000000000fafa0000fafa0000000000000000000000000000000000000000000000000000faaa0000faaa0000000000000000000000000000000000000000000000000000f8f80000f8f80000000000000000000000000000000000000000000000000000f0f00000ffff
  | 0, 4 => 0xfff00000fff00000000000000000000000000000000000000000000000000000ffcc0000ffcc0000000000000000000000000000000000000000000000000000ffcc000000000000000000000000000000000000000000000000000000000000ffaa0000ffaa0000000000000000000000000000000000000000000000000000ffaa0000aaaa0000000000000000000000000000000000000000000000000000ffaa000000000000000000000000000000000000000000000000000000000000ffa00000ffa00000000000000000000000000000000000000000000000000000ff000000ff00
  | 0, 5 => 0xffff0000fafa0000000000000000000000000000000000000000000000000000ffff0000f0f00000000000000000000000000000000000000000000000000000ffff0000cccc0000000000000000000000000000000000000000000000000000ffff0000c0c00000000000000000000000000000000000000000000000000000ffff0000aaaa0000000000000000000000000000000000000000000000000000ffff0000a0a00000000000000000000000000000000000000000000000000000ffff000033330000000000000000000000000000000000000000000000000000ffff00000000
  | 0, 6 => 0xffff0000ff00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x265d43
  | 4, 0, 0 => 0x205d0310099734c40205d449007d748c40289da49007973064a205d23140a206d34
  | 5, 0, 0 => 0x205d2300502075748c502b5d23035a2799748c681b5d23cc60205cc18250205d2207502881c5cc502881748c502891748a502281748c503075748c502881948c502c81748c50205cf30650298173065
  | 5, 0, 1 => 0x2981748c5020757488502e81648c50205d230450205d244c501748f30350285cc18350205d2301502899738c5028817488502885748c502061748c502b81748c502381748c502581748c50285d22035
  | 5, 0, 2 => 0x2f81748c50205d2202502881b48950205d2307502881220550205d2302502b812305502b81748850268173cc50205d234c502a81748c50288173065
  | 6, 0, 0 => 0x205d23025a205d23096a205d230b60288173065a205d23026a205d238c6a2781748c6a205d548c60288174885a205d2308602b81748c502075748c5ae881748c6a2075748c602881748c5a205d23036
  | 6, 0, 1 => 0xa2681748c6b6881748c6a206d748c6
  | 7, 0, 0 => 0x2881748c5
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
  | 0, 0 => 0x1ff00000000000000000000000000000000000000000000000000000000000001f8e3e70000000000000000000000000000000000000000000000000000000001c7ff1f00000000000000000000000000000000000000000000000000000000003fffff00000000000000000000000000000000000000000000000000000000003fe0ff0000000000000000000000000000000000000000000000000000000000001fff0000000000000000000000000000000000000000000000000000000000001f000000000000000000000000000000000000000000000000000000000000001f1f
  | 0, 1 => 0x700000000000000000000000000000000000000000000000000000000000000001c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e007000000000000000000000000000000000000000000000000000000000000e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001ff1ff8
  | 0, 2 => 0x3800e000000000000000000000000000000000000000000000000000000000003800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e0070000000000000000000000000000000000000000000000000000000000071c180000000000000000000000000000000000000000000000000000000000071c1800000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000000070018
  | 0, 3 => 0x1c000000000000000000000000000000000000000000000000000000000000001c003000000000000000000000000000000000000000000000000000000000001c000000000000000000000000000000000000000000000000000000000000000071c18000000000000000000000000000000000000000000000000000000000038e0e7000000000000000000000000000000000000000000000000000000000000e00700000000000000000000000000000000000000000000000000000000003800e00000000000000000000000000000000000000000000000000000000000381fff
  | 0, 4 => 0x1f81fe00000000000000000000000000000000000000000000000000000000001c71f180000000000000000000000000000000000000000000000000000000001c700000000000000000000000000000000000000000000000000000000000001c0ff070000000000000000000000000000000000000000000000000000000001c0e0070000000000000000000000000000000000000000000000000000000001c0e0000000000000000000000000000000000000000000000000000000000001c01f000000000000000000000000000000000000000000000000000000000001c01f00
  | 0, 5 => 0x1ffe0e70000000000000000000000000000000000000000000000000000000001ffe0e00000000000000000000000000000000000000000000000000000000001fffc180000000000000000000000000000000000000000000000000000000001ffe0000000000000000000000000000000000000000000000000000000000001ffe0070000000000000000000000000000000000000000000000000000000001ffe0000000000000000000000000000000000000000000000000000000000001ffe3e70000000000000000000000000000000000000000000000000000000001ffe000
  | 0, 6 => 0x1ffff00
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1b61000000000000000000000000000000000000000000000000000000000000168c3a60000000000000000000000000000000000000000000000000000000000c5b50d00000000000000000000000000000000000000000000000000000000001b6fff00000000000000000000000000000000000000000000000000000000001b607b0000000000000000000000000000000000000000000000000000000000000fff0000000000000000000000000000000000000000000000000000000000000f84000000000000000000000000000000000000000000000000000000000000050d
  | 0, 1 => 0x9730000000000000000000000000000000000000000000000000000000000000841c000000000000000000000000000000000000000000000000000000000000841000000000000000000000000000000000000000000000000000000000000049e52f000000000000000000000000000000000000000000000000000000000049e000000000000000000000000000000000000000000000000000000000000040850400000000000000000000000000000000000000000000000000000000000840220000000000000000000000000000000000000000000000000000000001b61ad0
  | 0, 2 => 0x13a4af200000000000000000000000000000000000000000000000000000000013a40000000000000000000000000000000000000000000000000000000000001200a800000000000000000000000000000000000000000000000000000000000cdf52f00000000000000000000000000000000000000000000000000000000009f7c7b0000000000000000000000000000000000000000000000000000000000973c5900000000000000000000000000000000000000000000000000000000009734090000000000000000000000000000000000000000000000000000000000973059
  | 0, 3 => 0x1e49f840000000000000000000000000000000000000000000000000000000001e493840000000000000000000000000000000000000000000000000000000001e490000000000000000000000000000000000000000000000000000000000001b73ed900000000000000000000000000000000000000000000000000000000017befff000000000000000000000000000000000000000000000000000000000169efaf00000000000000000000000000000000000000000000000000000000013b6efb00000000000000000000000000000000000000000000000000000000013a4fff
  | 0, 4 => 0x1fedff60000000000000000000000000000000000000000000000000000000001f7bfdd0000000000000000000000000000000000000000000000000000000001f7b0000000000000000000000000000000000000000000000000000000000001edffaf0000000000000000000000000000000000000000000000000000000001edf52f0000000000000000000000000000000000000000000000000000000001edf0000000000000000000000000000000000000000000000000000000000001ecdfa60000000000000000000000000000000000000000000000000000000001e49f84
  | 0, 5 => 0x1ffffff0000000000000000000000000000000000000000000000000000000001fffaf20000000000000000000000000000000000000000000000000000000001fffc590000000000000000000000000000000000000000000000000000000001fff8500000000000000000000000000000000000000000000000000000000001fff52f0000000000000000000000000000000000000000000000000000000001fff0220000000000000000000000000000000000000000000000000000000001fff3a60000000000000000000000000000000000000000000000000000000001fff000
  | 0, 6 => 0x1ffff84
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 49 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 49 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 49 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 49 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_47 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_47 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
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
private theorem z4_0 : ∀ i, 0 ≤ i → i < 8 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 8 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_16 : ∀ i, 16 ≤ i → i < 32 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_32 : ∀ i, 32 ≤ i → i < 44 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 32 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 44 → Z 5 i = true := (range_split (range_split z5_0 z5_16) z5_32)
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

namespace S_15_32
def pairsG : List (Nat × Nat) := [(33, 35), (33, 37), (33, 41), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (36, 44), (40, 41), (40, 42), (40, 44)]
def r1sG : List Nat := [33, 33, 33, 34, 34, 34, 36, 36, 36, 40, 40, 40]
def r2sG : List Nat := [35, 37, 41, 35, 38, 42, 37, 38, 44, 41, 42, 44]
def mpG : Nat := 0xfff
def pool6G : List Nat := [37525735744803, 44135640278316, 44127050343210, 39729003569958, 44122772218665, 39724725445413, 39729121471014, 44122805904169, 44122805904681]
def xsM : List Nat := roots_15_32.map (· &&& dom_15_32)
def goalM : Nat := goal_15_32 &&& dom_15_32
def NN : Nat → Nat
  | 3 => 3
  | 4 => 6
  | 5 => 5
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x5e2aba2c39fef78313b7d8f9
  | 4, 0 => 0x76c5eadc5e2aba2c5d5304c75454674e1263c5e60e88ccf1
  | 5, 0 => 0x5e2aba2c5d5304c72ff9f6242b88ef700bf6c491
  | 6, 0 => 0x5e2aba2c
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0000000000000000000000000000000000000000000000000000000000000eeee000000000000000000000000000000000000000000000000000000000000cccc000000000000000000000000000000000000000000000000000000000000aaaa000000000000000000000000000000000000000000000000000000000000888800000000000000000000000000000000000000000000000000000000000033330000000000000000000000000000000000000000000000000000000000000f0f00000000000000000000000000000000000000000000000000000000000000ff00000000
  | 0, 1 => 0xfff0000000000000000000000000000000000000000000000000000000000000ffcc000000000000000000000000000000000000000000000000000000000000ffaa000000000000000000000000000000000000000000000000000000000000ff88000000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000fcfc000000000000000000000000000000000000000000000000000000000000fcf0000000000000000000000000000000000000000000000000000000000000fafa00000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xb7544fd8540e943
  | 4, 0, 0 => 0x742040b75440b74240b7634eb76450c7544
  | 5, 0, 0 => 0xb75440b7424b75435b75415ba7545
  | 6, 0, 0 => 0xb7544
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
  | 0, 0 => 0x1c0000000000000000000000000000000000000000000000000000000000000003f0000000000000000000000000000000000000000000000000000000000000038000000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fc70000000000000000000000000000000000000000000000000000000000000e3f00000000000000000000000000000000000000000000000000000000000001ff
  | 0, 1 => 0xfc00000000000000000000000000000000000000000000000000000000000000e380000000000000000000000000000000000000000000000000000000000000e070000000000000000000000000000000000000000000000000000000000000e000000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000000001f800000000000000000000000000000000000000000000000000000000000001c000000000000000000000000000000000000000000000000000000000000001c7
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x9d200000000000000000000000000000000000000000000000000000000000006ff00000000000000000000000000000000000000000000000000000000000004b9000000000000000000000000000000000000000000000000000000000000024f00000000000000000000000000000000000000000000000000000000000000090000000000000000000000000000000000000000000000000000000000000b46000000000000000000000000000000000000000000000000000000000000062d00000000000000000000000000000000000000000000000000000000000000db
  | 0, 1 => 0xff60000000000000000000000000000000000000000000000000000000000000fbd0000000000000000000000000000000000000000000000000000000000000f6f0000000000000000000000000000000000000000000000000000000000000f2d0000000000000000000000000000000000000000000000000000000000000f240000000000000000000000000000000000000000000000000000000000000dfb0000000000000000000000000000000000000000000000000000000000000df20000000000000000000000000000000000000000000000000000000000000bdf
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 16 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 16 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 16 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 16 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_15_32 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_15_32 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_15_32 == dom_15_32) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_15_32 goalM u ys) : RunD dom_15_32 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_15_32 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_15_32 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_15_32 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_15_32 roots_15_32 goal_15_32 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_15_32 goal_15_32 := by
    have h0 : isConstB dom_15_32 goal_15_32 = false := by decide +kernel
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

end S_15_32

theorem low_15_32 : Lower dom_15_32 roots_15_32 goal_15_32 7 := S_15_32.noCircuit

namespace S_31
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (1, 17), (2, 3), (2, 6), (2, 18), (4, 5), (4, 6), (4, 12), (8, 9), (8, 12), (10, 11), (10, 14), (10, 26), (16, 17), (16, 18), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28)]
def r1sG : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 4, 4, 8, 8, 10, 10, 10, 16, 16, 20, 20, 20, 24, 24, 24]
def r2sG : List Nat := [3, 5, 9, 17, 3, 6, 18, 5, 6, 12, 9, 12, 11, 14, 26, 17, 18, 21, 22, 28, 25, 26, 28]
def mpG : Nat := 0x7fffff
def pool6G : List Nat := [4402375426821, 2203385726211, 8813290259724, 17600793871122, 8800455886089]
def xsM : List Nat := roots_31.map (· &&& dom_31)
def goalM : Nat := goal_31 &&& dom_31
def NN : Nat → Nat
  | 4 => 1
  | 5 => 5
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xac05225e
  | 5, 0 => 0xac05225e8c616cec5299e96d3a6b8d412b0e7274
  | 6, 0 => 0xac05225e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffff000000000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000aaaaaaaa0000000000000000000000000000000000000000000000000000000055555555000000000000000000000000000000000000000000000000000000000f0f0f0f0000000000000000000000000000000000000000000000000000000000ff00ff
  | 0, 1 => 0xfffff0f0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x765435
  | 5, 0, 0 => 0x765435754305764315765425865435
  | 6, 0, 0 => 0x765435
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
  | 0, 0 => 0x7f80000000000000000000000000000000000000000000000000000000000000707c0000000000000000000000000000000000000000000000000000000000000e03800000000000000000000000000000000000000000000000000000000000007070000000000000000000000000000000000000000000000000000000000000000f00000000000000000000000000000000000000000000000000000000007ffff0000000000000000000000000000000000000000000000000000000000071fc7f00000000000000000000000000000000000000000000000000000000000f83ff
  | 0, 1 => 0x7f8380
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x7fc0480000000000000000000000000000000000000000000000000000000000787e0400000000000000000000000000000000000000000000000000000000004e2ba20000000000000000000000000000000000000000000000000000000000257171000000000000000000000000000000000000000000000000000000000012949f00000000000000000000000000000000000000000000000000000000006d6b60000000000000000000000000000000000000000000000000000000000031d45d00000000000000000000000000000000000000000000000000000000000781fb
  | 0, 1 => 0x7febea
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 9 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 9 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 9 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 9 then wireAt i else 0
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
  scr dom_31 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_31 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_31 roots_31 goal_31 7 := by
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

theorem low_31 : Lower dom_31 roots_31 goal_31 7 := S_31.noCircuit

namespace S_59
def pairsG : List (Nat × Nat) := [(1, 3), (1, 9), (1, 17), (2, 3), (2, 18), (8, 9), (10, 11), (10, 26), (10, 42), (16, 17), (16, 18), (24, 25), (24, 26), (33, 35), (33, 41), (33, 49), (34, 35), (34, 42), (34, 50), (40, 41), (40, 42), (48, 49), (48, 50), (56, 57), (56, 58)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 8, 10, 10, 10, 16, 16, 24, 24, 33, 33, 33, 34, 34, 34, 40, 40, 48, 48, 56, 56]
def r2sG : List Nat := [3, 9, 17, 3, 18, 9, 11, 26, 42, 17, 18, 25, 26, 35, 41, 49, 35, 42, 50, 41, 42, 49, 50, 57, 58]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [37388364155139, 2203587842307, 10999984423689, 17596649965841, 10999815080195, 44126511366954, 17600793871122]
def xsM : List Nat := roots_59.map (· &&& dom_59)
def goalM : Nat := goal_59 &&& dom_59
def NN : Nat → Nat
  | 3 => 1
  | 4 => 4
  | 5 => 11
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xda5ccfbf
  | 4, 0 => 0xec7cc462c55915c3c38274819c7929d7
  | 5, 0 => 0xeaaab64ac3827481925f5c6889b786ce7628b61a4cac355d4599038c420b4f1b3b045f9c37f8ccf41d620181
  | 6, 0 => 0xc3827481
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xc0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000000c0c0c0c000000000000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a00000000000000000000000000000000000000000000000005050505050505050000000000000000000000000000000000000000000000000303030303030303000000000000000000000000000000000000000000000000000f000f000f000f00000000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000000000000000000000000000000000000000f0f0f0f
  | 0, 1 => 0xf0f0f0f000000000000000000000000000000000000000000000000000000000f0f0f000f0f0f000000000000000000000000000000000000000000000000000f0f0f000f0f0a000000000000000000000000000000000000000000000000000f0f0f000f0f00000000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000f000f000a000a000000000000000000000000000000000000000000000000000f000f0000000000
  | 0, 2 => 0xf0f0f0f0f0f00000000000000000000000000000000000000000000000000000f0f0f0f0a0a0a0a
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x34e53
  | 4, 0, 0 => 0x2d272a018a3951eb51caa08b8e54
  | 5, 0, 0 => 0x2d472815eb51caaf5a8a355a9072ac56a3955eb51c8af59ca255a8e62ac16a3955ea3942af72ce55
  | 6, 0, 0 => 0xf5a8e55
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
  | 0, 0 => 0x701d80000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000000e0070000000000000000000000000000000000000000000000000000000001ff1ff80000000000000000000000000000000000000000000000000000000001f8fe27000000000000000000000000000000000000000000000000000000000067e61f00000000000000000000000000000000000000000000000000000000001fe1ff0000000000000000000000000000000000000000000000000000000000001fff
  | 0, 1 => 0x1ffe0000000000000000000000000000000000000000000000000000000000001f81fe00000000000000000000000000000000000000000000000000000000001f81e000000000000000000000000000000000000000000000000000000000001f81e000000000000000000000000000000000000000000000000000000000001e01e0000000000000000000000000000000000000000000000000000000000019819e000000000000000000000000000000000000000000000000000000000019800000000000000000000000000000000000000000000000000000000000001980000
  | 0, 2 => 0x1fffe000000000000000000000000000000000000000000000000000000000001ffe007
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x15735d900000000000000000000000000000000000000000000000000000000015721000000000000000000000000000000000000000000000000000000000000a9ea6f00000000000000000000000000000000000000000000000000000000015615900000000000000000000000000000000000000000000000000000000000a8ca26000000000000000000000000000000000000000000000000000000000065a61d00000000000000000000000000000000000000000000000000000000001b616b0000000000000000000000000000000000000000000000000000000000001eff
  | 0, 1 => 0x1ffe1000000000000000000000000000000000000000000000000000000000001fedff60000000000000000000000000000000000000000000000000000000001fedff60000000000000000000000000000000000000000000000000000000001fedf940000000000000000000000000000000000000000000000000000000001e49e9400000000000000000000000000000000000000000000000000000000019a59e200000000000000000000000000000000000000000000000000000000019a496200000000000000000000000000000000000000000000000000000000019a4100
  | 0, 2 => 0x1ffff940000000000000000000000000000000000000000000000000000000001ffeb6f
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_59 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_59 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := []
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
  scr dom_59 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_59 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_59 roots_59 goal_59 7 := by
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

theorem low_59 : Lower dom_59 roots_59 goal_59 7 := S_59.noCircuit

namespace S_27
def pairsG : List (Nat × Nat) := [(1, 3), (1, 9), (1, 17), (2, 3), (2, 18), (8, 9), (10, 11), (10, 26), (16, 17), (16, 18), (24, 25), (24, 26)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 8, 10, 10, 16, 16, 24, 24]
def r2sG : List Nat := [3, 9, 17, 3, 18, 9, 11, 26, 17, 18, 25, 26]
def mpG : Nat := 0xfff
def pool6G : List Nat := [2203587842307, 17596515746577]
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
  | 0, 0 => 0xf000000000000000000000000000000000000000000000000000000000000000ce000000000000000000000000000000000000000000000000000000000000000d80000000000000000000000000000000000000000000000000000000000000007
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xf940000000000000000000000000000000000000000000000000000000000000ce20000000000000000000000000000000000000000000000000000000000000ad9000000000000000000000000000000000000000000000000000000000000056f
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

def symsG : List (List (Nat × Nat)) := [[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]]
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

namespace S_43
def pairsG : List (Nat × Nat) := [(1, 3), (1, 9), (2, 3), (8, 9), (10, 11), (10, 42), (33, 35), (33, 41), (34, 35), (34, 42), (40, 41), (40, 42)]
def r1sG : List Nat := [1, 1, 2, 8, 10, 10, 33, 33, 34, 34, 40, 40]
def r2sG : List Nat := [3, 9, 3, 9, 11, 42, 35, 41, 35, 42, 41, 42]
def mpG : Nat := 0xfff
def pool6G : List Nat := [37388364155139, 8800961168137]
def xsM : List Nat := roots_43.map (· &&& dom_43)
def goalM : Nat := goal_43 &&& dom_43
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x12562096
  | 4, 0 => 0x12562096
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0000000000000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000c0c00000c0c00000000000000000000000000000000000000000000000000000a0a00000a0a
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_43 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_43 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_43 == dom_43) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_43 goalM u ys) : RunD dom_43 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_43 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_43 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_43 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_43 roots_43 goal_43 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_43 goal_43 := by
    have h0 : isConstB dom_43 goal_43 = false := by decide +kernel
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

end S_43

theorem low_43 : Lower dom_43 roots_43 goal_43 5 := S_43.noCircuit

namespace S_23
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 17), (2, 3), (2, 6), (2, 18), (4, 5), (4, 6), (16, 17), (16, 18), (20, 21), (20, 22)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 2, 4, 4, 16, 16, 20, 20]
def r2sG : List Nat := [3, 5, 17, 3, 6, 18, 5, 6, 17, 18, 21, 22]
def mpG : Nat := 0xfff
def pool6G : List Nat := [2203385726211]
def xsM : List Nat := roots_23.map (· &&& dom_23)
def goalM : Nat := goal_23 &&& dom_23
def NN : Nat → Nat
  | 3 => 2
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xa5e04b24678b910d
  | 4, 0 => 0x678b910d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00f00000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000cc00cc0000000000000000000000000000000000000000000000000000000000aa00aa
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x10836884
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_23 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_23 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]]
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

namespace S_27_32
def pairsG : List (Nat × Nat) := [(33, 35), (33, 41), (33, 49), (34, 35), (34, 42), (34, 50), (40, 41), (40, 42), (48, 49), (48, 50), (56, 57), (56, 58)]
def r1sG : List Nat := [33, 33, 33, 34, 34, 34, 40, 40, 48, 48, 56, 56]
def r2sG : List Nat := [35, 41, 49, 35, 42, 50, 41, 42, 49, 50, 57, 58]
def mpG : Nat := 0xfff
def pool6G : List Nat := [37525803116835]
def xsM : List Nat := roots_27_32.map (· &&& dom_27_32)
def goalM : Nat := goal_27_32 &&& dom_27_32
def NN : Nat → Nat
  | 3 => 2
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xa501b4489713a9dd
  | 4, 0 => 0x9713a9dd
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0f00000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000c0c0c0c000000000000000000000000000000000000000000000000000000000a0a0a0a00000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x10836884
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_27_32 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_27_32 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_27_32 == dom_27_32) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_27_32 goalM u ys) : RunD dom_27_32 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_27_32 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_27_32 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_27_32 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_27_32 roots_27_32 goal_27_32 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_27_32 goal_27_32 := by
    have h0 : isConstB dom_27_32 goal_27_32 = false := by decide +kernel
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

end S_27_32

theorem low_27_32 : Lower dom_27_32 roots_27_32 goal_27_32 5 := S_27_32.noCircuit

def isoMv_55 : List (Nat × Nat) := [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_55 : Lower dom_55 roots_55 goal_55 8 :=
  lower_iso isoMv_55 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47

def isoMv_23_32 : List (Nat × Nat) := [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_23_32 : Lower dom_23_32 roots_23_32 goal_23_32 7 :=
  lower_iso isoMv_23_32 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_32

def isoMv_61 : List (Nat × Nat) := [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_61 : Lower dom_61 roots_61 goal_61 7 :=
  lower_iso isoMv_61 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59

def isoMv_29 : List (Nat × Nat) := [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_29 : Lower dom_29 roots_29 goal_29 5 :=
  lower_iso isoMv_29 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27

def isoMv_53 : List (Nat × Nat) := [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_53 : Lower dom_53 roots_53 goal_53 5 :=
  lower_iso isoMv_53 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_43

def isoMv_46 : List (Nat × Nat) := [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem low_46 : Lower dom_46 roots_46 goal_46 5 :=
  lower_iso isoMv_46 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_43

def isoMv_54 : List (Nat × Nat) := [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_54 : Lower dom_54 roots_54 goal_54 5 :=
  lower_iso isoMv_54 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_43

def isoMv_30_32 : List (Nat × Nat) := [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem low_30_32 : Lower dom_30_32 roots_30_32 goal_30_32 5 :=
  lower_iso isoMv_30_32 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27_32

namespace S_63
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (1, 17), (2, 3), (2, 6), (2, 18), (4, 5), (4, 6), (4, 12), (8, 9), (8, 12), (10, 11), (10, 14), (10, 26), (10, 42), (16, 17), (16, 18), (20, 21), (20, 22), (20, 28), (20, 52), (24, 25), (24, 26), (24, 28), (33, 35), (33, 37), (33, 41), (33, 49), (34, 35), (34, 38), (34, 42), (34, 50), (36, 37), (36, 38), (36, 44), (36, 52), (40, 41), (40, 42), (40, 44), (48, 49), (48, 50), (48, 52), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 4, 4, 8, 8, 10, 10, 10, 10, 16, 16, 20, 20, 20, 20, 24, 24, 24, 33, 33, 33, 33, 34, 34, 34, 34, 36, 36, 36, 36, 40, 40, 40, 48, 48, 48, 56, 56, 56]
def r2sG : List Nat := [3, 5, 9, 17, 3, 6, 18, 5, 6, 12, 9, 12, 11, 14, 26, 42, 17, 18, 21, 22, 28, 52, 25, 26, 28, 35, 37, 41, 49, 35, 38, 42, 50, 37, 38, 44, 52, 41, 42, 44, 49, 50, 52, 57, 58, 60]
def mpG : Nat := 0x3fffffffffff
def pool6G : List Nat := [8800455886089, 4406653551366, 11012869326348, 17596515746577, 21995134911761, 26392742986513, 2203385726211, 52931194848564, 17600793871122, 44126511366954, 4402744920325, 2203722057987, 8813290259724, 44023753737770, 10999984423689, 37426683972650, 52931345908532, 21999226326019, 44023753737514, 52793908527924, 52862628004660, 21994931293189, 22033585668870, 26392910365955, 52931345122100, 61658721027636, 10999815080195, 2204260633603, 2203388742659, 44127048237866, 4402377789957, 22024609399564, 11012699982854, 52931345910836, 26405476303628, 2203453229315, 26474195780882, 26396886893842, 21999429879314, 52780887836177, 39668488475188, 4402912297733, 61615939782186, 4403150196997, 21994563834385, 2203992066307, 39591412370438, 61718697411370]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_63 &&& dom_63
def NN : Nat → Nat
  | 4 => 1
  | 5 => 40
  | 6 => 146
  | 7 => 382
  | 8 => 135
  | 9 => 15
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x60accfa2
  | 5, 0 => 0xf9e781c9eefabc86dd562f69da979bdcb49c3c0bb198ac4d99e21d69980cfc849324d3678d17103087bfc70582bc0a98791153127116973c64f770ba621c927a5a38dc3f508105504f617bc34bd1c7de4a2fe1793eb2d2973d7244df3d6a961f3a8c25d332f5096731dbd62c27dc4fe82442bff72171cbeb1edd025c1d814a5016e67879147d91650bdbd6f40a9410ee056c27b4019394c800efc12d00dc39ff
  | 6, 0 => 0x4b5f5c8c4b2f2c654b266b6b4752be7f469ca98e449441b3447b530343f12e64438e83ea411ec8a33e7b061b3d1f78b13a8df35d36f812fb36bd7d74369e232b32eece5732eded4832328f84315c080730ef49ec30159264301133192d909c982af16a5b29bb8f20260717a225c59cec23bbb3642280af1021c6747b21af853d20fa792c205772ea202108ed1f990ef21f7b5ec71ed4d8781df2b89d1bf81e491bd606951ae1c6821ac782031a459ae017639a2316ad85321643e44815ed543d1356a1bd1260bdcc12593c6b0fb6dc480fa22a3f0f02d2520eb4e7340e29400b0d3755480bf0ddbb0bd82d050b575d5c072e561606165d7601aa933f00086150
  | 6, 1 => 0xce88a2aac9c2af35c8b1a951c480ced8c2219e93c219efd3c148c600c038d657bfbc76bbbf1ff3e7bbaf3958ba4e66f8b2f9e2bdb162d637aeef705bae3211d5adf9cc1eaa26e078a89169afa851971fa621259fa0faae6296db332594cb35d4948c25539324bee98f436aa28a224e5d892f89dd885c641a83e3015082f377b0814de50380b221047fa76e187dd566d57ce54173769d69d3764c0b8073bd60fa734bd99471a3faaf7134af5a6f4c2b3e6e0648ba6d34d03365696e1061ddcef0607bcbf760741d375f86fcac5e7407325c0e05b85b974d035a332a0159d1f0cc5967c8f758421cea553537e84fbb048c4eef474b4d6ed5974cd589e94c30865f
  | 6, 2 => 0xfdd6dd26fa2a5962f9cc6ac4efcf53caefafdf64ed1f4209ec7a9118e9f0118fe9a6ca6ee2467c58defb0a41dedff55fde29e06edc0cc109d8aba3b0d7385bcad4e034e8d2e159e1
  | 7, 0 => 0x182bf926181a04811813153417d64a91172f396116e24b2d16987722165a14331640b40615eeff3915ea9fee15c35559154b39521499cfe51432396c13ea83c213346ed1130cc1b31247bf781232479711fd2b13118eca21117804a410d7221f104862a50f97753d0e1f184a0e19c3470d86abda0d49c4170d3586890d05cbda0c83298b0c232aad0bd3d3cb0bc7415d0ac5e2020a4eea9609ec2ffe091999780905f9ab086d1673060e01a405f2ecc20585bda2057729b6053cd7d104aea855048eab8804831d8d0442bd860404ee0e02dea06a0249a99b023a3df801d18b1e01d1462401cde8810198403d016db2170166035701551783012a584000f9b8fb
  | 7, 1 => 0x31968b4130b973d6306aaa7f2fbdf3d12f3594f12f34e7c52f2d39052e5c0f322e414d792e3fb1002d98c7d02c8e77b92c7c27652c58dac22b811d732b27b74c2ad9fd9b2a4774b22a245e7b29b1bd8a29922d3f294a3d0b29428e4b2912a74928a46344282426c927eaac2227bb223c2759c5772748e4d027162c5026f62f8326b3685326ac92fa26548cc425c30139245472f0241577b9231ced0122f8e58621ce372521c636b8213d50c5213a8cc120d56179204b60b61ed8ca961e790bb91e3844ef1d2d13f91d2aeaa91c3b9b761c0dd5381bb55db81b1c36fd1a13ea6d19ff9c8019ba301a1966b80018ef4baf18b903881891280c1860cf5518595dba
  | 7, 2 => 0x4a8b09ee4a83d73a49c3e2a9498effba498185ac497382e2493c34104939f53048a6ffde47340050462000d2461b66ed46074adf45a7f59844f40dc343c469ce43acd94843992f1e424acd3741de0f1c41da79664170b9d840cde8cc3fc11baf3fab5da13f6a09b43e8f3b893e7691863e5fa2443e3c0ae43de1cf0e3dc07c953d727f8e3d51fe0d3d0f7e103cedc83e3cc472893c6b32503c407f353c21b4153bb1f7013b72da473b6f72873b05d6f73a4fc20639a504973961b02b392d295a38eeefa638c68766388be5c4381fcf1436b521a236a8e1d9364691d83643e73e347c735e343a84db33e6b2b633c3d979333ea61a32e16b8932139fa731f65c8a
  | 7, 3 => 0x6c3bd30b6b715d986b31778b6b302ff1680f7993672751d866dfb3f666d1c7a965c3cd306580daed653a6e246532bf6464497e5c643a3fff6407b8f16332600f60f6bf84604693fd602e455b6008d5905f18482b5ecd913b5c97debb5b65c3955a83226859fcbebe595c19525925466958ec052358b7554858b5610058715e945802414f571462ac56ba13a0568d8c7e56503afa56488c3a562807655521817b551db61354af2ec553d248aa530e3d0852e2321e52a2b541527d165f522c1d2d520461be506b190f503182d94fbdd0064fb50f3e4d1a0f054d0bceb24ce115d74c99f1af4bacc54f4b8c97694b6231954b50406a4aceaac74aca3bcf4aabf4e8
  | 7, 4 => 0xa8193e84a3ad5187a277e12da20e930ba0c208bf9f1c706f9c3b05cf9b3ef8b79917c0ab9847a6bd9823da64972d561a96ced85294ad81c7938ab7de937619ce931be89e90f610e68f6057d08e2b23528e0b555c8d7e05af8cbf99ff8b830d788a81f0ca89f4a11d87c1a7e6871e3ea4836290978320fd1b827963fa8069eaef7f55144d7f3dc0ab7f28314b7eeeae697ead80c27d0510077c7494757bf8b5337b4e627f79f05dc0778509c276df94a67677af7c7677504c761a42bc7481ccfa73437dc2729906d472847ea2727253ef726c78f871cca4b3716e00616ec76b136ea4ed216e65b5e26e2c96216e24e7616e1b180f6dafa0f16d2c12e76ccacce0
  | 7, 5 => 0xfe4b532dfc6afe7dfad9fd75f6535463f4f9312af48bd63cf250bba1f1b199daf02f43ceee5bfb02eb93c63be68ed5dbe56d3923e28853e8dfb2a488de0091c7ddf8e307ddd5ae60dc16fe65db51c5cfd9288e6bd872797ad735f252d67aeb44d37ccbb3d26d319fd201f6a4d139d7dbc996b3b6c73369bbc71007f0c63e6ab8c5e5017dc4b9fc07c30e22efc20018d3c19d30e4c0f590b7c031db64bc36ee53baff17d9bab9a1bdbaa8c339baa65613ba05b9e8b7ef6c85b7784d34b6c50266b68386c9b5eebe46b3cc7367b2118fd6b1522b5ab072d957af13a005adcdd0fead6e83e8acb48a93ab225dd6a9c667e4a994b72fa94c64a9
  | 8, 0 => 0x514aca6d51099cc650c4b4ed4ec05ebd4c4c79c44b13daf94b0c2c394a24047e49e125c646e149a2425327d741a4b5d6413f306a4079af63405c8f3d3d6d0b963cedcf813afd7b253a8b9b213a4766343a305add38ad846e387c221636f4981f360aefae359f67e7358e7c1334746a9f32ba82ac3264f1943129ad3f2fc976f62f1362052b81626d2acd7a9828ac56fe28a4a83e272770732468a85e23038dd422c735132219ec0a1f3d31db1e08e1531c1ffead1bde45011b8548e619b1d44814121a0c12baa67712b8884a123247970f8b2a5f0f6b9a140e7dd0190d61f2fb0cabde0a0c2cfbb60b41c77206ecbabd06b07a030452788e03e3645400f5a3d2
  | 8, 1 => 0xe1b94d76e12fee6ae1283faad958a3e4c7554d2ec5e58a67c5690328c52f7576bf01fb40be4be64fbde1cfb5baa8a17cb59a84ddb4e46fecb031ca64af01b67aabbe6e52ab681b8ea98e4816a98c5b5da8e78fc4a25e4bf19e58572e996c23f498411d819351acbb928df7688f6e24048df2ab598d5eaaf98ce77a638bbc73f08a81f0ca89211e6a869b759483f048fb83d9bb2c8029ed027fe35f827f4590c97dfd47397d33ff317bf0d33379e15a2877d135d073e4c231729906d46f6c29a26d9b14bb6bed6d236b46b4d16a7ff66868b561d063669d9560b58bf55d7bf2db5cde0cce5c50bd215c0095e65af03eb05647df2856403068556f069554ed1c75
  | 8, 2 => 0xf5a8ee32f1c31697eef3064dee22ff53ed71b5aeea68185de575a6ea
  | 9, 0 => 0xf33b5fd0f2854adfbad4da248a7994f87f4590c97e1a8a5661ca40085fbac6fd5cde0cce5059633d42b779a31561a43a0e85c3d30e7e151305169eb0
  | 10, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x33330000333300000000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000000000000000000000000000000000000ffffffffff000000000000000000000000000000000000000000000000000000ff000000ff00000000000000000000000000000000000000000000000000000055555555550000000000000000000000000000000000000000000000000000005500000055000000000000000000000000000000000000000000000000000000330000003300000000000000000000000000000000000000000000000000000000ffffffff
  | 0, 1 => 0xf000f000f000f0000000000000000000000000000000000000000000000000005000555555555000000000000000000000000000000000000000000000000000500050005000500000000000000000000000000000000000000000000000000030003000300030000000000000000000000000000000000000000000000000000ffff0000ffff0000000000000000000000000000000000000000000000000000fefe0000fefe000000000000000000000000000000000000000000000000000055550000555500000000000000000000000000000000000000000000000000003f3f00003f3f
  | 0, 2 => 0x101010155555555000000000000000000000000000000000000000000000000010101010101010100000000000000000000000000000000000000000000000000ff00ff00ff00ff0000000000000000000000000000000000000000000000000055005500550055000000000000000000000000000000000000000000000000003f003f003f003f00000000000000000000000000000000000000000000000000330033003300330000000000000000000000000000000000000000000000000011001100110011000000000000000000000000000000000000000000000000000f000fffffffff
  | 0, 3 => 0xf0a0f0a0f0a0f0a0000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e0000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000000505050555555555000000000000000000000000000000000000000000000000050505050505050500000000000000000000000000000000000000000000000003030303ffffffff00000000000000000000000000000000000000000000000003030303575757570000000000000000000000000000000000000000000000000303030303030303
  | 0, 4 => 0x30303030303030300000000000000000000000000000000000000000000000001515151515151515000000000000000000000000000000000000000000000000151515150000000000000000000000000000000000000000000000000000000011111111111111110000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000f0f0f000f0f0f000000000000000000000000000000000000000000000000000f0f0c0c0f0f0c0c0000000000000000000000000000000000000000000000000f0c0f0c0f0c0f0c
  | 0, 5 => 0xaaaaaaffaaaaaaff000000000000000000000000000000000000000000000000aaaaaaaaffffffff000000000000000000000000000000000000000000000000aaaaaaaaaaaaaaaa00000000000000000000000000000000000000000000000055555555555555550000000000000000000000000000000000000000000000003333333333333333000000000000000000000000000000000000000000000000333333330000000000000000000000000000000000000000000000000000000033303330333033300000000000000000000000000000000000000000000000003322332233223322
  | 0, 6 => 0xcccccc00cccccc00000000000000000000000000000000000000000000000000ccc0ccc0ccc0ccc0000000000000000000000000000000000000000000000000c8c8c8c8c8c8c8c8000000000000000000000000000000000000000000000000c3c3c3c3c3c3c3c3000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000000babababababababa000000000000000000000000000000000000000000000000abababababababab000000000000000000000000000000000000000000000000aaaabbbbaaaabbbb
  | 0, 7 => 0xeeeeee00eeeeee00000000000000000000000000000000000000000000000000eee0eee0eee0eee0000000000000000000000000000000000000000000000000eaeaeaeaeaeaeaea000000000000000000000000000000000000000000000000e8e8e8e8e8e8e8e8000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e0000000000000000000000000000000000000000000000000cdcdcdcdcdcdcdcd000000000000000000000000000000000000000000000000cccccccccccccccc000000000000000000000000000000000000000000000000cccccccc00000000
  | 0, 8 => 0xf0f0f0fff0f0f0ff000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000f0f0f000f0f0f000000000000000000000000000000000000000000000000000f0f0c0c0f0f0c0c0000000000000000000000000000000000000000000000000eeeeeeeeeeeeeeee000000000000000000000000000000000000000000000000eeeeeeeeaaaaaaaa000000000000000000000000000000000000000000000000eeeeeeee00000000
  | 0, 9 => 0xfcfcfcfca8a8a8a8000000000000000000000000000000000000000000000000fcfcfcfc00000000000000000000000000000000000000000000000000000000fcfcfc00fcfcfc00000000000000000000000000000000000000000000000000fafafafafafafafa000000000000000000000000000000000000000000000000fafafafaaaaaaaaa000000000000000000000000000000000000000000000000fafafa00fafafa00000000000000000000000000000000000000000000000000fafac8c8fafac8c8000000000000000000000000000000000000000000000000f0f0f3f3f0f0f3f3
  | 0, 10 => 0xfefefefeaaaaaaaa000000000000000000000000000000000000000000000000fefefefe00000000000000000000000000000000000000000000000000000000fefe0000fefe0000000000000000000000000000000000000000000000000000fe00fe00fe00fe00000000000000000000000000000000000000000000000000fcfcfcfcfcfcfcfc000000000000000000000000000000000000000000000000fcfcfcfcf0f0f0f0000000000000000000000000000000000000000000000000fcfcfcfce8e8e8e8000000000000000000000000000000000000000000000000fcfcfcfccccccccc
  | 0, 11 => 0xff11ff11ff11ff11000000000000000000000000000000000000000000000000ff0cff0cff0cff0c000000000000000000000000000000000000000000000000ff05ff05ff05ff05000000000000000000000000000000000000000000000000ff01ff01ff01ff01000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000fefefefefefefefe000000000000000000000000000000000000000000000000fefefefefafafafa000000000000000000000000000000000000000000000000fefefefeeaeaeaea
  | 0, 12 => 0xffeeffeeffeeffee000000000000000000000000000000000000000000000000ffeaffeaffeaffea000000000000000000000000000000000000000000000000ffe8ffe8ffe8ffe8000000000000000000000000000000000000000000000000ffe0ffe0ffe0ffe0000000000000000000000000000000000000000000000000ffccffccffccffcc000000000000000000000000000000000000000000000000ffc8ffc8ffc8ffc8000000000000000000000000000000000000000000000000ffc0ffc0ffc0ffc0000000000000000000000000000000000000000000000000ffaaffaaffaaffaa
  | 0, 13 => 0xfffefffefffefffe000000000000000000000000000000000000000000000000fffcfffcfffcfffc000000000000000000000000000000000000000000000000fffafffafffafffa000000000000000000000000000000000000000000000000fffafffaaaaaaaaa000000000000000000000000000000000000000000000000fffafffa00000000000000000000000000000000000000000000000000000000fff0fff0fff0fff0000000000000000000000000000000000000000000000000fff0fff000000000000000000000000000000000000000000000000000000000fff0ccc0fff0ccc0
  | 0, 14 => 0xffffcccc00000000000000000000000000000000000000000000000000000000ffffc8c8ffffc8c8000000000000000000000000000000000000000000000000ffffc0c0ffffc0c0000000000000000000000000000000000000000000000000ffffaaaaffffaaaa000000000000000000000000000000000000000000000000ffff0c0cffff0c0c000000000000000000000000000000000000000000000000ffff0303ffff0303000000000000000000000000000000000000000000000000ffff000fffff000f000000000000000000000000000000000000000000000000ffff0000ffff0000
  | 0, 15 => 0xfffffcfcfffffcfc000000000000000000000000000000000000000000000000fffffcfc00000000000000000000000000000000000000000000000000000000fffffafafffffafa000000000000000000000000000000000000000000000000fffff0f0fffff0f0000000000000000000000000000000000000000000000000ffffeeeeffffeeee000000000000000000000000000000000000000000000000ffffeeeeaaaaaaaa000000000000000000000000000000000000000000000000ffffeaeaffffeaea000000000000000000000000000000000000000000000000ffffccccffffcccc
  | 1, 0 => 0xffffffccffffffcc000000000000000000000000000000000000000000000000ffffffcc00000000000000000000000000000000000000000000000000000000ffffffc0ffffffc0000000000000000000000000000000000000000000000000ffffffaaffffffaa000000000000000000000000000000000000000000000000ffffffaaaaaaaaaa000000000000000000000000000000000000000000000000ffffffaa00000000000000000000000000000000000000000000000000000000ffffff00ffffff00000000000000000000000000000000000000000000000000ffffff0000000000
  | 1, 1 => 0xffffffffc3c3c3c3000000000000000000000000000000000000000000000000ffffffffaaaaaaaa000000000000000000000000000000000000000000000000ffffffff03030303000000000000000000000000000000000000000000000000ffffffff00000000000000000000000000000000000000000000000000000000fffffffcfffffffc000000000000000000000000000000000000000000000000fffffff0fffffff0000000000000000000000000000000000000000000000000fffffff000000000000000000000000000000000000000000000000000000000ffffffeeffffffee
  | 1, 2 => 0xffffffffeaeaeaea
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x837c63532d5
  | 5, 0, 0 => 0x706c634642500705b53513d500837c5b4c395008e705b53265817c63534e2d600705b342d005807c6346422d60090705b53265008c7463463f5837c5b53392d600705b5326005008d705b342d500705b58533d500705b534f3d583705b534c396008c70342d155
  | 5, 0, 1 => 0x8c7065533d5008e705b3d185837c6346392d60090705b3d185008c5b53260b500705b3d1800500705b4e342d581807c63532d6008d705b3d185008c703d1815500705b534e265008c7c634d2d5008c70634c3e5005b534e3d0b5008e705b342d5008c705b342c5
  | 5, 0, 2 => 0x705b5326255008c705b2618500705b57533d5008c533d150b500705b4e3d18500807c63532d5008f705b342d580705b534c426
  | 6, 0, 0 => 0x8c5b332d180b600705b5753332d6008c70463926156008c6a604c390b6008c53332d150b600807c5b462d2b6005b5746392d0b6008c7f745b464260070696346392c600705b46392d03600705b57392d236008c705b53421b68c8a7c7063532d700705b2c2b23006008c463d39150b6007c7a5b46392d6
  | 6, 0, 1 => 0x705b463926256008c706a604c2b6008c70665b533d6008c70624c46426008c78745b46246005b4e46392c0b600755b46392c00600705b4e392c236008c70604a46396008c555446392d6008c7062534c2d60083706346392d68c81705b534c42700705b534c42006008c7063463f2d681807c5b53392d7
  | 6, 0, 2 => 0x705b46392600600695b46392c0b600705b2e2d2b236008c81746346426008c817c63532d600705b4f392d2360070695b392c2368070634c46392d78c817c5b53422d7008c705b3d2d186008c70533d2d15600805b46392d0668c7c74635b532d700705b534e332c6007a7046392d1560000705b534e3d5
  | 6, 0, 3 => 0x8c5b533d0b5008c706a674c396007877745b464268c81705b533d2d700705b533d2d0060090705b4639266007046392d13006008c765b4c464260070695b462c2b6008c705b342d1860077705b2d2b2360083705b392d236008c70625a462d60080706346392c6008c2d2b23150b600705b534f332d6
  | 6, 0, 4 => 0x8e7046392d136008c7046392c13683705b5346392d700696346392d0b600008c705b5326500706963392d23600705b534e4c4260080705b392c236008c705c46392d60090705b533d2d6008c706a634c426008c8a70604c396008e705b4639266008c70605b533d6008c46392d15086008c5b53332c0b6
  | 6, 0, 5 => 0x695b392d230b6005b4e462d2b0b600706c5b392d23600705b4e2d2b2360083705b4c463968c81745b5346427008c785b4642096005b534e332d0b6008c5b2c2b230b600008c705b342d5008c7c745b53426817063534e462d7007c775b4c392d6005b4e392d230b600807c5b53392d68c817c634c392d7
  | 6, 0, 6 => 0x7c70635b534e2d78c7c706a63532d700775b46392d0660070605b574639600705b332d18006008c7c5b49392d6008c70634d462d600695b462d2b0b6008c705b5a533d600706c5b462d2b6008d705b332d18600705b534e3d2d681807c6346392d700705b46392d0e6008c5b534c420b6008c5b46392d0a6
  | 6, 0, 7 => 0x705b46392d196008c705b4946426008c70604c390f6008c705b532d266008e705b332d186008c705b332c18600008c705b3d185008c6146392c0b68c817c6053392d780705b4c46423970080705b2d2b23680705b534c392d7008c7f705b533d60080706346422d6008c7f705b4c426008c705b53342d6
  | 6, 0, 8 => 0x8c705b4c42186000090705b533d5008c705b533d3c6008c70675b534c6007a705b4c4639600705b46392d17600705b4e332d186004e46392d150b600705b53332c006008c81705b533d60000705b533d0058c817c6353392d700807c6346392d6008c705b533d266008c392c23150b60070696353462d6
  | 6, 0, 9 => 0x8c705b533d18600008e705b533d5
  | 7, 0, 0 => 0x705b392e2d236008a80705b46392d7008c5b46392c2b0b7008c7c785b46422d70070635b534e462d7008c705b46392d117008c785b46392d0670000705b4e46392c60070534e46392d157008c7b705b392d237008c75745b46392d7008e705b392d2b237008c705b392c2b237008c7c7046392c157008c706e5b53332d7008c8a705b462d2b7
  | 7, 0, 1 => 0x70695b4c46392d7008c705b462c2b2a7008c705b392d2321700706b605b46392d78c8170605346392d8008c705b46392d1c7008c705b46423909700008c392d23150b6008c706a5b4c4239700706a5b46392d10700705b4639332c007008c81705b463d39700705b4e46392d187008c705b5946392d70000705b463d39006008c817063392d237
  | 7, 0, 2 => 0x705b53332d006008678705b46392d7008c706a46392d147008c705b46392d187008c705b534c42397008c705f5b46392d700705b46422d2b007000077705b392d236008c7046392d15097008c705b4b4642397008c706e5b462d2b7008c705b5246392c7008c7f705b46422d700705b392d231d007008c7870462d2b157008c705b46392c047
  | 7, 0, 3 => 0x8c817063462d2b7008c85706146392d7008c705b46392c0f7008c705b462d2b287007e78705b46392d7000090705b463d396008c7d705b53392d7008c705b53423b2d7008c705b4c46392470000705b4f46392d6000070695b46392c6007770605b46392d7008c7b705b462d2b7008c71705b46392d7008c70675b4c46397008c81705b53332d7
  | 7, 0, 4 => 0x8c70635b4c464278c7870635b53462d8008c704c464239157008c706046392d047008c705b4c392d187008180706346392d7008c705b41392d237008c706346392d147008c706e5b46362d700008c702d2b23156008c70635b534c2d7008c8b705b46392d700705b5346392d1a7008c7046392d15077008c705b462d2b067008c70534c392d157
  | 7, 0, 5 => 0x8c81706746392d7008c706e5b46422d7008c70644642392d7008c787046422d157000077705b462d2b6008c705b46392d22781705b534e46392d8000083705b46392d600706d6b5b46392d7008c7d7046392d15700008e705b463d396008274705b46392d7008c705b463a392d700706b6a5b46392d7008c78705b462d247007877705b392d237
  | 7, 0, 6 => 0x8c705b4639312d70077706a5b46392d7008c70462d2b27157008c70635b532d237008c7c745b392d237008e705b392d231d7008c705b392c231d7008c705b46392d0c7008c7053392d23157008c8170604c463978c7c70635b46422d8008c757046392d15700705b4e4642392d7008c706046392d0f78c8170635346392d800705b5346392e2d7
  | 7, 0, 7 => 0x8c7546392d156008c81706346422d7008c7f745b46392d7008c5b46392d120b7008c5b46392d180b700008e705b53332d600008c705b53332c60000008c705b533d58c8a7c706346392d800705b575346392d7008c705b53392d1b7008c635b53462d0b7008c817c5b46392c7008c705b392d23187008c5346392d150b7008c705a5446392d7
  | 7, 0, 8 => 0x705b534c392d007008c7046392d1b157008c706346392d047008c705a46392d157008c4639332d150b7008c74706146392d7008c78705b392c2370080705b4c46392d7008c70665b46392d7008c84706346392d7008c705b4846392d7008c8a705b44392d70077705b5346392d7008c705b53332d187007770635b46392d7007877705b462d2b7
  | 7, 0, 9 => 0x8c705b5046422d70077705b46392d077008c7c745b462d2b7008c705b392d23147008c7c785b43392d7008c8a745b46392d7008c5b4c392d230b7008c7053462d2b157008c817c6046392d70070695b4642392d7008c815b46392d097008c81705b2d2b2370000705b2d2b230068c81705b534c392d8008c706a6346392c7008c70635b5a462d7
  | 7, 0, 10 => 0x78705b4e46392d7008c706346392d0f7008c78745b4642397008c7c785b53392d7008c70624c46392d7000070696346392d6008670635b46392d7008c70605b534c397000080705b46392c6008c7c704c392d157008180705b392d2378c81705b4c464239800705b534e46392c7008c705b392d23227008c705b392d2320700705b4c464239007
  | 7, 0, 11 => 0x705b564c46392d7007877705b46422d7008c78705b462c2b7008c88705b46392d700706a695b46392c78c7c70605b53392d8008c705b392d231f700705b53392d23007008c787446392d157008c70665b463d397008c705b46392d1e7007e705b5346392d7008c7c705b2d2b27700008c5b392c230b6008c74705b4239237008c705d5b46392d7
  | 7, 0, 12 => 0x8c817c5b4642392d8008c705b462d2b1470000705b4e392d236008c5b4c462d2b0b7008c7c70392d23157008c70463d392d157008c7c7846392d157008c705b4c2d2b237008c70635b462d247008c87705b462d2b7008c7046392d24157008c705b46322d2b7008c7470392d231578c7c74635b46392d8008c81706346372d7008c705b4d46392d7
  | 7, 0, 13 => 0x8c817c6346392d7008c84705b392d2370000705b534e332d6008c7f7046392d15700008e705b2d2b23600008c705b2c2b236008c705b4c392d0f7008c7c7b5b46392d70070605b4e46392d7008c705346422d157008c745b46392d06700005b4e46392d0b6008c81755b46392d7008c5b392d2b230b700705b534f46392d70000755b46392d006
  | 7, 0, 14 => 0x8180705b5346392d8008c705b392d231e7008c70605b46391b7008c5b462d2b230b7008c6a5b46392c0b7008c7470462d2b157008c705b463e392d7008c705b392d23047008c705b2d2b2a237008c705b2d2b2318700705b46392d1b00700008c5b462c2b0b6008c705b46422d12700706a696046392d700705b5a46392d007008c74705b46422b7
  | 7, 0, 15 => 0x8c705b4639302d7008c706a60392d237000080706346392d6008c5b42392d230b7008c5b5346392c0b70000695b46392d0b600008c705b534c426008c7c70605b4c3978c7c70635b53392d80000706c5b46392d6008e705b53392d237008c705b53392c237008c75705b46392c7008c87705b46422d7008c70635b392c237008c7c70462d2b157
  | 7, 1, 0 => 0x8c5b4639332c0b700705b534e46392d7008281705b46392d700008c5b463d390b60080705b46392d047007c78775b46392d70070635b4e46392d7008c705b53392d067008c705b4746392d78c81705b463d392d800008e755b46392d600008c755b46392c6008480705b46392d700705b463d392d007007e7c705b46392d7008c73705b392d237
  | 7, 1, 1 => 0x90705b463d392d700706d695b46392d7008c817046392d127008c706a60462d2b7008c5b46422d2b0b70081705b46392d05700705b534e4c392d7008c81706353462d7007f77705b46392d7008c705b462d2b0f7008c70635b462c2b7008c7b7046392d157008c7046392c2b157008c81745b392d237008c636046392d0b7008c70605b463d397
  | 7, 1, 2 => 0x8c7f705b46392c700705b46392c23007008c72705b46392d7007f7e705b46392d7000080705b392d236008180745b46392d700705b534e392d237008c877c5b46392d700008c705b2d2b236008c81745b462d2b7008c706a63392d237008c87745b46392d7008c85705b46392d700008c705b4639266008c70605b53332d700008c5b53332d0b6
  | 7, 1, 3 => 0x8c705b4c4239237008c705b422d231d7008c70635b462d187008c705e5b392d237008c705b39382c237008c8a705b46392c700705b5a4e46392d7008c706a63462d2b700706c6a5b46392d7008c7c745b4642397008c78705b2d2b23700008c78745b4642600008c705b533d2d600008c7046392d1360078777046392d157008c7c745b53392d7
  | 7, 1, 4 => 0x8c705b4c4642357008c705b534c2d2b7008c705b46392c067008681705b46392d7008c706a6346422d7008c705b46392d0d7008c4c46392d150b70080705b5346392d700706b5b4c46392d7008c706a5b4c2d2b7008c79755b46392d7008c7d705b392d237008d705b46392d187008c706a6746392d7008c70605b2d2b237008c705b4a46392d7
  | 7, 1, 5 => 0x8c705b532d2b237008c706f5b46392d7008c70635b2d2b23700705b565346392d7008c705b5a392d23700705b46392d18007008c46392d23150b7008c6a5b462d2b0b7008c7d705b462d2b7008482705b46392d78c8a7c705b53392d800008c46392c150b6007f705b4e46392d7008c7c70635b532d7008c7470464239157008c5b462d2b270b7
  | 7, 1, 6 => 0x8c705b46392d027008e705b46392d187008c705b46392c187008c7c705b4c2d2b7008a89705b46392d7008c70635b53462c7008c81705b392c2370000705b392c23006008c705b46392d017008c705b392d24237008381705b46392d7008c705b5a46352d7008777705b46392d78c7c706a6346392d8008c705b5a53332d7008c705b46392d297
  | 7, 1, 7 => 0x8c705b463d39267008c705b46392d16700705b5346392c00700008c705b332d186008c7f705b462d2b7008c705b46392f2d7008c70685b46392d70000705b5746392d6008180705b46392c700705b5a5646392d7008c705b46392d2670081705b4e46392d700705b392d2b2300700705b4c462d2b007
  | 8, 0, 0 => 0x8c706e6a5b46392d8008c705b46392d1278c78705b4c46392d8008c705b46392d187008c70635b53462d7008c7c745b46392d7008c705346392d157008c81705b392d2370000705b392d230068c81705b4644392d8008c705b46452d2b78c8a706a5b46392d88c705b4642392d238007877705b46392d78c7f705b5346392d8008c705b4641392d7
  | 8, 0, 1 => 0x705b5346392d00700008c5b46392c0b6008c74705b464239700008e705b392d23600008c705b392c2368c705b464240392d8008180705b46392d78c78705b46392d238008c705b46392d147008c5b4c46392d0b7008c705b4c392d237008c87705b46392d7008c78705b46392c78c706e635b46392d8008c70615b46392d7008c704639332d157
  | 8, 0, 2 => 0x8c84705b46392d78c81705b4639332d88c70605b46392d2b800705b4639332d0078c706d5b4c46392d88c706a5b4c46392d8008c5b46392d2b0b78c8a7c705b46392d80000705b4e46392d6008c705b392d2b237008c7c7046392d1578c70605b46392d238008c705b4c462d2b7008c5b46392d230b7008c747046392d1578c81705b5346392d8
  | 8, 0, 3 => 0x8c706a6046392d7008c5b4642392d0b78c70635b46392d2388c705b5346392d188008c705b46392d0f7008e705b5346392d7008c705b5346392c7000070695b46392d6008c70635b46392c78c7b74705b46392d8008c705b5246392d78c705b534c46392d8008c705b46392d0478c70635b4c46392d8008c705b462d2b2a78c705b46423b392d8
  | 8, 0, 4 => 0x8c706a6346392d78c705b4c46392d1b88c705b5a4c46392d8008c78705b392d2378c7c705b4c46392d800008c705b53332d6008c817c5b46392d7008c705b392d231d700008c705b392d236008c81745b46392d78c8470605b46392d88c706a5b4639362d8008e705b4639332d7008c705b4639332c700008c705b463d3968c7d705b4c46392d8
  | 8, 0, 5 => 0x8c705b2d2b236008c705b534c392d7008c705b4639382c78c78706a5b46392d88c8a81705b46392d8008c706a5b4c392d78c706a5b46392d0f8008c705b5346392d7008c78705b462d2b78c705b4c4639382d8008c70605b392d23700008c5b392d230b6008c706d5b46392d7000080705b46392d600705b534e46392d78c7870605b46392d8
  | 8, 0, 6 => 0x8c70635b462d2b78c706d6a5b46392d8008c705b46392d1b78c70605b4639332d8008c705b5a46392d700008c755b46392d68c70605b5346392d8008c705b53392d237008c70635b392d237008c6a5b46392d0b7008c7d705b46392d7008c70605b462d2b7008c705b4c464239700008c5b462d2b0b68c78705b5346392d88c7870635b46392d8
  | 8, 0, 7 => 0x8c7c70635b46392d8008e705b46392d237008c705b46392c2378c7067605b46392d8008c7f705b46392d78c81705b46392d2388c7c70605b46392d800705b46392d23007008c81705b46392c70000705b46392c006008c705b463d392d78c70635b5346392d88c81705b4c46392d800705b4c46392d007008c7c705b4c392d78c705b534e46392d8
  | 8, 0, 8 => 0x8c7067635b46392d88c81705b46392d04800008c46392d150b68c705b46392d2b2388c8481705b46392d80000705b46392e2d68c705b5a5346392d8
  | 9, 0, 0 => 0x8c81705b46392d700705b46392d0068c705b4639382d78c705b4639332d78c705b5346392d78c70635b46392d78c70605b46392d7008c5b46392d0b6008c705b392d2368c78705b46392d7008c705b46392d68c705b46392d237008e705b46392d6008c705b46392c68c705b4c46392d7
  | 10, 0, 0 => 0x8c705b46392d6
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
  | 0, 0 => 0xfe1e000f8f000000000000000000000000000000000000000000000000000000e1fe00fc7f0000000000000000000000000000000000000000000000000000001fffffffff0000000000000000000000000000000000000000000000000000001ffe0003ff0000000000000000000000000000000000000000000000000000001fe1fffff00000000000000000000000000000000000000000000000000000001fe00003f00000000000000000000000000000000000000000000000000000001e1e00038f0000000000000000000000000000000000000000000000000000000001ffffff
  | 0, 1 => 0x701fe03007f00000000000000000000000000000000000000000000000000000701e1fffff000000000000000000000000000000000000000000000000000000701e0030070000000000000000000000000000000000000000000000000000007001e03000f000000000000000000000000000000000000000000000000000000fffe00ffff0000000000000000000000000000000000000000000000000000001ffe00f3ff000000000000000000000000000000000000000000000000000000ffe000fff0000000000000000000000000000000000000000000000000000000fffe00ffff
  | 0, 2 => 0x3fe001fffff000000000000000000000000000000000000000000000000000003fe001c30c000000000000000000000000000000000000000000000000000000071ffe3f03ff0000000000000000000000000000000000000000000000000000071fe03f03f00000000000000000000000000000000000000000000000000000071ffe3f03ff0000000000000000000000000000000000000000000000000000071e1e3f038f0000000000000000000000000000000000000000000000000000071e003f038000000000000000000000000000000000000000000000000000000701ffffffff
  | 0, 3 => 0x38e01fc0fc0f00000000000000000000000000000000000000000000000000000001fe00f07f00000000000000000000000000000000000000000000000000000001e000f07000000000000000000000000000000000000000000000000000003fe1e1fffff000000000000000000000000000000000000000000000000000003fe1e1c3fc7000000000000000000000000000000000000000000000000000003fe01fffffff00000000000000000000000000000000000000000000000000003fe01fffffff00000000000000000000000000000000000000000000000000003fe01fc30c0f
  | 0, 4 => 0x1e003c038000000000000000000000000000000000000000000000000000003fffe1fffff000000000000000000000000000000000000000000000000000003fffe000000000000000000000000000000000000000000000000000000000003ffe01ff0f8000000000000000000000000000000000000000000000000000003fe1ffc3fc7f00000000000000000000000000000000000000000000000000003fe001c3fc0000000000000000000000000000000000000000000000000000003f01e1c3f070000000000000000000000000000000000000000000000000000038e1e1c0fc70
  | 0, 5 => 0x1ffe0003ff000000000000000000000000000000000000000000000000000000001fffffff000000000000000000000000000000000000000000000000000000001e00000f00000000000000000000000000000000000000000000000000003fffe1fffff000000000000000000000000000000000000000000000000000003ffe1fff0f8f00000000000000000000000000000000000000000000000000003ffe1e000000000000000000000000000000000000000000000000000000000038fe01fc0f80000000000000000000000000000000000000000000000000000038e01fc00c0f
  | 0, 6 => 0xf000000000000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003fe01fc30c0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e1e3c038f00000000000000000000000000000000000000000000000000003fe01fc30c0f000000000000000000000000000000000000000000000000000000fe1e000f8f
  | 0, 7 => 0xf000000000000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000001e00000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003fe1e1c3fc7000000000000000000000000000000000000000000000000000000001e000f07000000000000000000000000000000000000000000000000000000001e0000000
  | 0, 8 => 0x1ffe3c03ff0000000000000000000000000000000000000000000000000000001e003c03800000000000000000000000000000000000000000000000000000001e0000000000000000000000000000000000000000000000000000000000000000003c000000000000000000000000000000000000000000000000000000000000003c000000000000000000000000000000000000000000000000000000000001fe00f07f00000000000000000000000000000000000000000000000000000001fe00000f00000000000000000000000000000000000000000000000000000001fe000000
  | 0, 9 => 0x1fe00000000000000000000000000000000000000000000000000000000000001fe000000000000000000000000000000000000000000000000000000000000000003cf0000000000000000000000000000000000000000000000000000000001e1e3c038f0000000000000000000000000000000000000000000000000000001e1e00000f00000000000000000000000000000000000000000000000000000000003c000000000000000000000000000000000000000000000000000000000000003c0000000000000000000000000000000000000000000000000000000000fe1e3c0f8f
  | 0, 10 => 0x1ffe00000f0000000000000000000000000000000000000000000000000000001ffe00000000000000000000000000000000000000000000000000000000000000003c0000000000000000000000000000000000000000000000000000000000000000f0000000000000000000000000000000000000000000000000000000001fe03cf3f00000000000000000000000000000000000000000000000000000001fe03c03800000000000000000000000000000000000000000000000000000001fe00000000000000000000000000000000000000000000000000000000000001fe000f070
  | 0, 11 => 0x3ffe01ffff80000000000000000000000000000000000000000000000000000038e1e1c0fc7000000000000000000000000000000000000000000000000000003fe1e1c3fc7000000000000000000000000000000000000000000000000000003fe001c3fc00000000000000000000000000000000000000000000000000000038e001c0fc000000000000000000000000000000000000000000000000000000001ffe3cf3ff0000000000000000000000000000000000000000000000000000001ffe3c038f0000000000000000000000000000000000000000000000000000001ffe00000f
  | 0, 12 => 0x38e1ffc0fc7f000000000000000000000000000000000000000000000000000038e01fc0fc0f000000000000000000000000000000000000000000000000000038e001c0fc00000000000000000000000000000000000000000000000000000038e001c0fc00000000000000000000000000000000000000000000000000000038e1e1c0fc70000000000000000000000000000000000000000000000000000038e001c0fc00000000000000000000000000000000000000000000000000000038e001c0fc00000000000000000000000000000000000000000000000000000038e01fc0fc0f
  | 0, 13 => 0x38fffffcffff000000000000000000000000000000000000000000000000000038ffe1fcfff0000000000000000000000000000000000000000000000000000038fe1ffcff8f000000000000000000000000000000000000000000000000000038fe1e00000f000000000000000000000000000000000000000000000000000038fe1e000000000000000000000000000000000000000000000000000000000038fe01fcff80000000000000000000000000000000000000000000000000000038fe000000000000000000000000000000000000000000000000000000000000380001fcf000
  | 0, 14 => 0x3f01e000000000000000000000000000000000000000000000000000000000003f0001ff000000000000000000000000000000000000000000000000000000003f0001ff000000000000000000000000000000000000000000000000000000003f001fff000f00000000000000000000000000000000000000000000000000003f01e1fff07000000000000000000000000000000000000000000000000000003fe01fff0c0f00000000000000000000000000000000000000000000000000003f01ffff007f00000000000000000000000000000000000000000000000000003f0001ff0000
  | 0, 15 => 0x3f1fe1fff3f000000000000000000000000000000000000000000000000000003f1fe000000000000000000000000000000000000000000000000000000000003f1e1fff038f00000000000000000000000000000000000000000000000000003f1e01ff038000000000000000000000000000000000000000000000000000003f01fffff07f00000000000000000000000000000000000000000000000000003f01fe00000f00000000000000000000000000000000000000000000000000003f001fff000f00000000000000000000000000000000000000000000000000003f01e1fff070
  | 1, 0 => 0x3fe1e1fffc7000000000000000000000000000000000000000000000000000003fe1e000000000000000000000000000000000000000000000000000000000003fe001fffc0000000000000000000000000000000000000000000000000000003fe01ffffc0f00000000000000000000000000000000000000000000000000003fe01e00000f00000000000000000000000000000000000000000000000000003fe01e00000000000000000000000000000000000000000000000000000000003fe001fffc0000000000000000000000000000000000000000000000000000003fe000000000
  | 1, 1 => 0x3fffffc30c0f00000000000000000000000000000000000000000000000000003ffffe00000f00000000000000000000000000000000000000000000000000003fffffc30c0f00000000000000000000000000000000000000000000000000003ffffe00000000000000000000000000000000000000000000000000000000003fffe1fffff000000000000000000000000000000000000000000000000000003ffe01ffff8000000000000000000000000000000000000000000000000000003ffe0000000000000000000000000000000000000000000000000000000000003fe1fffffc7f
  | 1, 2 => 0x3ffffe00000f
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xaa0c000e8600000000000000000000000000000000000000000000000000000060aa0094150000000000000000000000000000000000000000000000000000000667df7fff00000000000000000000000000000000000000000000000000000006660001b300000000000000000000000000000000000000000000000000000004419a6b60000000000000000000000000000000000000000000000000000000044000012000000000000000000000000000000000000000000000000000000002040000820000000000000000000000000000000000000000000000000000000001df7fff
  | 0, 1 => 0x3013203005900000000000000000000000000000000000000000000000000000201019a6b6000000000000000000000000000000000000000000000000000000201000200400000000000000000000000000000000000000000000000000000010010010008000000000000000000000000000000000000000000000000000000eeee00bfb7000000000000000000000000000000000000000000000000000000eeee00bfb7000000000000000000000000000000000000000000000000000000ccc000ab20000000000000000000000000000000000000000000000000000000eaae009e97
  | 0, 2 => 0x19a6b60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000717762f01fb00000000000000000000000000000000000000000000000000000615402a016000000000000000000000000000000000000000000000000000000713362700db000000000000000000000000000000000000000000000000000005121425008a00000000000000000000000000000000000000000000000000000410002000000000000000000000000000000000000000000000000000000000030133df7fff
  | 0, 3 => 0x1960bac1d41d00000000000000000000000000000000000000000000000000001b61bac3d45d00000000000000000000000000000000000000000000000000001241a282d05100000000000000000000000000000000000000000000000000001241819aeb60000000000000000000000000000000000000000000000000000012418082c0400000000000000000000000000000000000000000000000000000092019df7fff0000000000000000000000000000000000000000000000000000092019db6f6c000000000000000000000000000000000000000000000000000009201841040c
  | 0, 4 => 0x249a05340a82000000000000000000000000000000000000000000000000000036d981b2ca40000000000000000000000000000000000000000000000000000036d9802080000000000000000000000000000000000000000000000000000000249801300a0000000000000000000000000000000000000000000000000000001b61bac3d45d00000000000000000000000000000000000000000000000000001b6198c3d44c00000000000000000000000000000000000000000000000000001b41b2c3d05900000000000000000000000000000000000000000000000000001a61aac2d455
  | 0, 5 => 0x9267e4515bf000000000000000000000000000000000000000000000000000009223fdf7fff000000000000000000000000000000000000000000000000000009223e45149f000000000000000000000000000000000000000000000000000036ddc1baeb6000000000000000000000000000000000000000000000000000002dba1d750e8e00000000000000000000000000000000000000000000000000002dba1c20000000000000000000000000000000000000000000000000000000002cba0d740e86000000000000000000000000000000000000000000000000000029aa1d550e8e
  | 0, 6 => 0x1241808af04000000000000000000000000000000000000000000000000000001044c088f1200000000000000000000000000000000000000000000000000000000462083131000000000000000000000000000000000000000000000000000009245849252c000000000000000000000000000000000000000000000000000000044008212000000000000000000000000000000000000000000000000000002dba3f751e9f000000000000000000000000000000000000000000000000000009223e45149f000000000000000000000000000000000000000000000000000009aa3e451e9f
  | 0, 7 => 0x1b6198cff44c00000000000000000000000000000000000000000000000000001866ccccf5a6000000000000000000000000000000000000000000000000000009267e4d35bf00000000000000000000000000000000000000000000000000000006660c31b300000000000000000000000000000000000000000000000000000006440c21a200000000000000000000000000000000000000000000000000001245e28af17100000000000000000000000000000000000000000000000000001245e28af17100000000000000000000000000000000000000000000000000001245e2008000
  | 0, 8 => 0x249e673c2bb30000000000000000000000000000000000000000000000000000249e453c2ba20000000000000000000000000000000000000000000000000000249e4420000000000000000000000000000000000000000000000000000000002498013c2a0000000000000000000000000000000000000000000000000000002414413c212000000000000000000000000000000000000000000000000000001b67fecff5ff00000000000000000000000000000000000000000000000000001b67fe45949f00000000000000000000000000000000000000000000000000001b67fe008000
  | 0, 9 => 0x36dfe6249093000000000000000000000000000000000000000000000000000036dfe6208000000000000000000000000000000000000000000000000000000036d981befa4000000000000000000000000000000000000000000000000000002dbe7f7d3fbf00000000000000000000000000000000000000000000000000002dbe7e65149f00000000000000000000000000000000000000000000000000002db8197d3e0c00000000000000000000000000000000000000000000000000002d14737d3139000000000000000000000000000000000000000000000000000024be4d3c2fa6
  | 0, 10 => 0x3ffffe65949f00000000000000000000000000000000000000000000000000003ffffe20800000000000000000000000000000000000000000000000000000003f1111ff4048000000000000000000000000000000000000000000000000000038e889d0fe04000000000000000000000000000000000000000000000000000036dfe7befbf3000000000000000000000000000000000000000000000000000036dfe73caba2000000000000000000000000000000000000000000000000000036dfe62cb1b3000000000000000000000000000000000000000000000000000036dfe6aaf171
  | 0, 11 => 0x3cf889f0fe0400000000000000000000000000000000000000000000000000003ae9abd2fe5500000000000000000000000000000000000000000000000000003ae989d2fe44000000000000000000000000000000000000000000000000000038e889d0fe04000000000000000000000000000000000000000000000000000038e889d0fe0400000000000000000000000000000000000000000000000000003fffffffffff00000000000000000000000000000000000000000000000000003fffff7dbfbf00000000000000000000000000000000000000000000000000003ffffe6db5bf
  | 0, 12 => 0x3befffdfffff000000000000000000000000000000000000000000000000000039eeffddffbf000000000000000000000000000000000000000000000000000038eeefdcffb7000000000000000000000000000000000000000000000000000038eecddcffa600000000000000000000000000000000000000000000000000003aedebdaff75000000000000000000000000000000000000000000000000000038ecebd8ff35000000000000000000000000000000000000000000000000000038ecc9d8ff24000000000000000000000000000000000000000000000000000039eabfd5fe9f
  | 0, 13 => 0x3fffffffffff00000000000000000000000000000000000000000000000000003effeffefff700000000000000000000000000000000000000000000000000003dfefffdffbf00000000000000000000000000000000000000000000000000003dfefe65949f00000000000000000000000000000000000000000000000000003dfefe20800000000000000000000000000000000000000000000000000000003cfecdfcffa600000000000000000000000000000000000000000000000000003cfecc20800000000000000000000000000000000000000000000000000000003c54c1fcf120
  | 0, 14 => 0x3f55f220800000000000000000000000000000000000000000000000000000003f1573ff717900000000000000000000000000000000000000000000000000003f1551ff616800000000000000000000000000000000000000000000000000003f333fff54df00000000000000000000000000000000000000000000000000003f51b3ffd05900000000000000000000000000000000000000000000000000003f3119ff444c00000000000000000000000000000000000000000000000000003f1133ff405900000000000000000000000000000000000000000000000000003f1111ff4048
  | 0, 15 => 0x3fdff7fffbfb00000000000000000000000000000000000000000000000000003fdff620800000000000000000000000000000000000000000000000000000003fbf7fff7fff00000000000000000000000000000000000000000000000000003f9f55ff6bea00000000000000000000000000000000000000000000000000003f77fffff5ff00000000000000000000000000000000000000000000000000003f77fe65949f00000000000000000000000000000000000000000000000000003f377fff75ff00000000000000000000000000000000000000000000000000003f55f3fff179
  | 1, 0 => 0x3ffdfbffff7d00000000000000000000000000000000000000000000000000003ffdfa20800000000000000000000000000000000000000000000000000000003ffdd9ffff6c00000000000000000000000000000000000000000000000000003ffbbffffedf00000000000000000000000000000000000000000000000000003ffbbe65949f00000000000000000000000000000000000000000000000000003ffbbe20800000000000000000000000000000000000000000000000000000003ff999fffe4c00000000000000000000000000000000000000000000000000003ff998208000
  | 1, 1 => 0x3ffffe69a52c00000000000000000000000000000000000000000000000000003ffffe65949f00000000000000000000000000000000000000000000000000003ffffe61840c00000000000000000000000000000000000000000000000000003ffffe20800000000000000000000000000000000000000000000000000000003fffffffffff00000000000000000000000000000000000000000000000000003fffddffffee00000000000000000000000000000000000000000000000000003fffdc20800000000000000000000000000000000000000000000000000000003fffffffffff
  | 1, 2 => 0x3ffffe6db5bf
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 145 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 145 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 145 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 145 then wireAt i else 0
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
  | 5 => 63
  | 6 => 590
  | 7 => 1513
  | 8 => 469
  | 9 => 13
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0xfcbd941cf962e301f60b7af8efcf53caeca5d4c5de29e06ed9af3450d60cadecce3402e8cc358b43c7cf81f1c74c2571c148c600afb3df48af55e9b6aaae3f8fa9575e6ba05339f79e4151239e27884d8fd2d58e8a9513b587bd66e484463489819209577e7a56637dfa0e777dcf50ff7d0f489273d07a706d621fbe627f712d61f5770b61d7af805f8957c04ce6565e4c4b52524b5f5c8c42b779a33c9d1a263c7ac0fa3b2fe8e938e6358338459fbc31c2eb322e5c0f322e20e92a25dd1fc62579821923ff1930234f730422e782b621af853d1c42d419172da6bc16403235117e5ae40fd9cc740cd2a1240ba23d770b6b91df0ae840140483a49e
  | 6, 0 => 0xcabde0a0c236eef0c0630490bf978d50bc2eecc0b2972550b173c4f0aae691e0aa700cb0a8a47a80a6c0c690a1efef00a17ef7c09f4089109ced05e09c2689c09b7c852094b73de090ae15508febdff08f317a5089c361b083131ec0828b35007e998db0759d80b075388ef07514ebe072b7cd50727ebe6070027ca06f5a2b906e4336306db0e23067d6016067c7986063e917206393aa705ff25a705fd2b7305a805b7055669d7053cd7d10512d1890505ca72045412d004324d500418e88a0414a3550407793403e2f3f802dc1b2602ce271e02afd615027a14b1026dfa60025fa4b80229104301d18b1e01aaa9db013f19960107a89000c203220081b482
  | 6, 1 => 0x212e0b952075da64202116661fca8cda1fc8a6441faae4fb1fa0bfc01f916b441f7dd1fa1f636afc1f32ec5b1e6007391e1ca92f1dc96b4f1d4394ac1c8f41911bf543b11be2e8291acbab401a9290141a58fe181a2639791a0f2ada19ba301a190a1b2718ad5ed2188f92a418674fd2185eb47517642431175fb2e617497f4a173f3e79172c13601701656116ec765a16eb0e0416e24b2d167df75e15eeff3915a6611415215ed9150d4cfa1504f3e714e0d35f14a896c913b8cc28124b29e1121c7581109f8fb31088cb410f711a090f3fbb520f124bee0ef08abd0eb9c2b30eb903040ea1bc0a0e98ce120db1b6820daabbb60d6e8d170d4ae8920d3ca1fd
  | 6, 2 => 0x32f24c9332ecef4e32e5408e324af7da31fd931f31968b413147765d3108de5830c0e57d30531a683037bc2b2ffbb9dc2ff0ebad2fcce5c12f7ac49a2f242cf22ee671c32ebd3fd12eab3f582e95a51c2e5c0f322e32c8c32dacfc532cce811c2c9f77672c58e4c52c3803702be9f1092b81626d2b3c92b72ab77fdf2aa964312a71da712a3c73b92a1fc85a29f1c6ed29cc158e28ac56fe28a4a83e284a715827e9389d27d9de4a27d2a8772713e0e72668cbab261e21d025ebfbc325d9debf24d9e22d24497b2c240f87f823d08b7f23b3e2f223720709230fc2b32240252b2216d66a22161ee321b0632821a83e9a2191f8e22185771a217c18ce213869ba
  | 6, 3 => 0x45a878b2457ae3f044fa88f844f229b144540250443dd3da43daba4143bccaae42c88acd42c5586342b779a34298de82424f44f4420e8bc441ec74b741ccf2d041b571854189b8df4184574b418109bb4176068d4157c04a4063e2794057fcab3ffc32e03f4f329f3f399e6c3e438e3e3e409e1f3e039a673dde76173d94c6ab3d5329983d52b1513c9ca9593bd82cc93bc70d473babe4053b63e3f03b5816813afcd3513af5ae8e3a4fc20639fb55ff39f331913921cc443896d407373133c336aa29373693090836495ec1360aefae35ee51be35ba19d835abd13a359826f8350f49b33505b6fb34add7c634a62906345cc7b033e59887332a32e3330ebc15
  | 6, 4 => 0x5d71535d5cde0cce5cc66ceb5caeaafb5c1752f25b9c99b85b8797025b0a5f395a870a3058d5e29558a3acfa5887bf1e57f00393575c33c057530f605750b7ef573bd79156ba13a05657614256503afa56488c3a55fa26b1556f06955501a81c54fe5a8c54de6a7c545b5df75407fd72539ef6105275c619523ede1551cc3e2151872e0e5136721b4fe6daa94e41a4674e29c7d14e249fb04ddb76074cf6e4114c551aef4c38351f4c187e4f4c128a274bf409854beee6fc4bcf16184b4ac0984b1210934a24047e4a0eeaab49a0b8ec49376aa94904488248d5c85748cbb65d486f70364841176a47c6ff6347b4abff4712aa5546fb2756468c225545c848ab
  | 6, 5 => 0x765ce0ec7617e5ee73e4c231737d02ed735bf0b37353885472db411f72ac2835727253ef726613cd722eeeb67227450771a7a88970eea42e70b4df8670972da6704d5e58701596636f9599c06f149dd46ecfff346e8cbcc66e7e8dac6e24e7616dcabe306d33441d6c52b0586b632bb26b0eb2d56adfcf326a8772f9699076f36971a092692d2566692ba2fb6889fe0d680c889867d2ecc667b1bd8267854e43670d50ea66276d02660cf11264a1fc87645b98ab643f09a863669d95633b241c63374e1062f9b0eb62a21d51629d2282629573c262950bd962160fd6621531946118463c60bfdce05ec715395e511c6f5e2f68925e1834e35d8c42c05d7297ea
  | 6, 6 => 0x94d778219493e62394921e3b936c84d592d6317c91e86a1191d2873e91654ffe9148b10391286ffd90e2f04490a6fd2a908be4898fa28c2a8edbba138ed40b538d5eaaf98cf0e0088cb824a98bf515058acaef6d8a81f0ca8a426ef48947578b8853294c884b7a8c882be4e187e53ae187be0786869c4f238674a04385e2daf08423f81384129c40833452068319ef288315b24682c20968824d18c18211e0e081e6ae83818040d7817ebe358154e8ae80dacb43804a5e088032585e7fd001297f7b54597d7f4a157d6730d47cf270267c039c0f7b28099b7af5220a7ac586e57a9e767b79e15a28792a94af7923a7e17920d8f3785236fa784bad827680fac4
  | 6, 7 => 0xb8e76ab4b8d58b9eb8ab2689b6688cecb660e5eeb5ac93d1b4aea468b2d2c51bb2c83225b2c0fc52b22bdbebaf918285af3fa94faed414f2ada5e64bad68591aacba1dc6a8e4ce14a8db08d3a7f187d2a78c41cfa76e2b52a7228789a547d07fa522df3ea4e24862a4400c23a2ec1b9ea25e4bf1a252780ca1d961dfa195b1bfa1367b9ba0848f66a05b43e5a05b39a2a05a8e69a0207bb0a01637eba0156c749fa381259ea46bf69d5e0e199d54cb8a9d4790469cf3b6b49c96775d9c1de56d9c19b6b29bd07a1d9bc8cb5d9b7186cd9aeccae79a2f0dd398d55b879847c54a977d71029708ff3f9620d1f695c7f38495a465ac9542bb3194f1379494ec1a10
  | 6, 8 => 0xeebf80f6ee0a9ec1ea68185de6ee6dd1e6a7bd05e545e120e2924128e28f6d59e1b59aa9e142ab19e090f5b4dfb8cdf2de287881dd445c18dcff6832dcfd9555dcf85272dc2aec62dc272ba0dba78fe2dba68411d979864fd93cd747d9352887d7705c43d6e25d60d6c6d6abd6a0d661d666d900d50110d5d4e7e3a8d4de3103d1c136f2d16d83ccd14c6d48d0c6f25dd0669516d05546f8d0022fedce63320fccbfb618cc26ccdbcafa56c2c766315ac64582f6c63e4d23c5d0441dc54f1ca7c34ff323c25165c3c1e70f7dc10f4154c0408517c0098957becd9540be6ff607be4be64fbd8203c1bd78354abd3c5e53bc7e122fb9d13a31b9661604b950c2ec
  | 6, 9 => 0xfeaa28bffdf52334fd1fa54ffcda1054fc56b3d4fafb8335f8dc0f96f6535463f546fa4bf454b541f40f6e34f34882a6f1b199daeef3064d
  | 7, 0 => 0x5e922100590ddec057ed236057c0b7a056ad819052aa49505169eb00512d1890509fa1f04e37e8404bca65904aaa2b00496704c04941f6a048dacd704824cd4046088880452788e044a6c4604427d3b042abe3b04108cb803d333c003856d130375c6cf035cf7bf033b05b5033a727c031d0181030a418d02c7a620029f514b029bda2f029aef9e02958ede028de01e028da25d0235e80302102cb9020b934d01eac28901d78abd01abdea401a5e674019c9fad0185b85101794b5f015fcb3e015cc643015a7e8d014ecf68014268c701385c4e0124c53e01195bd501189ba900f91aa800d76e0200c4d48b00b91207004fceaa00481fea003b1ab4002d875e
  | 7, 1 => 0xbe712130ba9c0d30ba8521d0ba0f9160b9beb890b8ad6cc0b41c7720b2c8ce60b2912830b2179b20b05d34b0af197a60ae34fac0ace38ec0ac986c50abb3de50ab5286d0aad79ad0aa03d900a7a55280a7677f50a6426b209eba6f409d9969709d87349098d4fc70989c7c3097adec20964338609598a57093e73560926f007090dfc8408e6fd4608e4c69e08df973908cd39f508bc19b108b51a4508b46af10865d84f085c29ce0844bf83083843fe081c74db07f70b8707f1b6d607f0433f07db2a7f07ca96c507c038b3078b6284078179cf076b65b7074eba940737882a07073daf06cbc555068bc39d06596495064cb80906291d8306237d4e05fd0f11
  | 7, 2 => 0x115b67ca114c695c11408e9a10ef472310de35ff10bf6ca610a80043109faa42108ef5b9108bef5710835d311015aee7100fe2f80ff805cc0ff651070fceabe00fc7e3a30fb1a7760f9aa5fd0f9788b90f8b2a5f0f7842780f7093b80f622c520f3d84400f37de040f23a9e00f1bfb200eef2d5f0ee57fac0e974d5b0e85c3d30e8414b20e7e15130e7dd0190e7db3450e4ddd170e48fbaa0e39d93f0e2172070e1ee4940e05ccb20df565b60db9c7830db432850d7f85ab0d6e8d170d66037f0d61f2fb0d570f570d40e0e10d0d7a9a0cf439bf0cf3298c0cabde0a0c867e660c825c970c6d8e9c0c687b0e0c61b8110c60dcf80c2ad96d0c1e8e5d0c0bf6ea
  | 7, 3 => 0x183afea71835a708182464af181c0a6c181ac3f418103f8817ddd95917d6fff417ce2ba217c5c22e17b7e34f175a929b172938d716da766916b01e5416654882165ce3e91653e747164f38e016446b9c164042a216100cbf160c7aef1606463715f3a7e415d3ee2015d3b4e415c1920715ba6e6315b3f79d15776f951561a43a15602014155ed0bb14ee289d14db292014c7c3fb14466a8414446e3c1422b86f1420fefd1415063f13fd04b313c146b613b3dc4e13b3a35d13aa68241368b3e2131ac6fe12ddb43412bb814412b8ab4112a8595d1276385312300b7112245a68120d1dd3120061e011d306b611c1f92a11a18517119557c61187183a1167b40d
  | 7, 4 => 0x1e25f90f1e08e1531dfefe1b1df5f1361de631f51dc79dfc1d9c94d41d940b681d7215931d68e5f71d19149d1d160c6b1d1165dd1cfd2fc91cd7e6f61cd038361cce2f151ca481c01ca0b1831c8d62a61c60ae701c4a8ac61c2568921c193f401bf5be811bc210541b9386ad1b933b9e1b827f451b62a5db1b27d2611b25c5621b16f5ed1b02bfb21afecaa01ac819931a7bac721a63b4731a5fb1a01a56a8731a4dc7a41a39c2a21a2660db19fb2cc719f37e0719ddb2d519d2796319c7c79119b64fa119a917ce1990c58b1980bc29196672e1194727b519468cb7191911e118eed24c18e4a1d018c40ebb18af851c18ab6b3618787ffd186366e3184b4579
  | 7, 5 => 0x25d0c2d925cb291025c5c2a225bd2022258d7136258a6ea4250b3e6a250aba5724f9d1c424e53f9224e504de24dd90d224c9ba2d24bcbbe924b5fa3e249aafe72468a85e243971d5241d33132414ae9a24123a1f2409402823fa873323bb3be3237d543d233e5198232c6add22e55f9722d85c9a22c96b302289ec0b2256b04f220e7a9821eaa96f21e6cbde21d8db4721a5f968219634db216dbf8b2161be9a215e4c98213bddeb20e2e2e92063e54f205b0a2a204fb0ae2015ae6f1fed34831fecb1011fd3c25f1fb72b911fad31dc1fa565611fa23c8a1f6fbf471f5f0d481f4cfea11f3108e21efe2b8f1ed55caf1ea663541ea60e4c1ea17ced1e2d04af
  | 7, 6 => 0x2bc2b7902bbea46f2b9c405e2b87620c2b81faf52b5913022b496d122b25f1c52b0fca262ae9f3842a98b5e72a6540552a5617002a430f592a4014db2a121f8d29f0b1cd29ed6e3b29e11e8129ba407729b291b729af2b642992b9322989cbc0297c99f8296b38aa2964176b29259dd72920d8b3291d2a9e28e3ecc328bda13e28ac56fe28a4a83e286e0790286658d028531ebf284f2ae5284514cc281f07512819312c281758912803ddcb27d2573727a27600279f070c27795cd1275dc420275a7690275958f22750b4f6273a8680272cb27626f168c926beaf6f26ad1191267c3f242668cbab265b33f62648e3a8263fdb2926146422260a164f26049315
  | 7, 7 => 0x32d045d132ba82ac32a889b1326bf53f3268ea173264f194322e87c4322a33b231ffed83318125c63177ea8831660f0b315024ba31472fc2312ae6df30e3267e30ddf49130a5e21830748bb13048c4d23046e378303037e9302ca7773016b5f93014f875300601422ff7be3e2fec250b2fc976f62fbbf89b2fb1aafd2f954dd02f7a8db12f67316b2f37b6b72f2288ef2f1d2f5b2f15a0e52f1362052ee5e2102ec68d272e9b5e9e2e9987ce2e3084652e28d5a52e2509872e1a843f2df877932dd75a262dcb18752d787d982d70ced82d618f3b2d4fca342d4518622d19df392d17f6e82cfe0cfa2cdf3e6c2c83d6252c69613a2c40d19a2c18d8712c119b4b
  | 7, 8 => 0x3926b9f839234c0738ed9e2f38ed825b38e1a69e38d186c938a80b97389cbe36387c22163872edd9383a0cba3819b83437d8b58137d4a1c237a858aa3791ff6b378f8af0378ba63f374d282d36e2575236d5d48e36c9ea4736c744ae36b5383e368939d0366946d03668643f364e4098363ae8203615bd7836126244360aefae35d89aaa35abdc1135a69de235a563b8359f67e7359e2116359740203581351d357f0e7b3579865d35787e2634d2d5ac34b7779434a771a73481847a346bd1e4345ddff534487e1233d93c6b33d8677333cd017f339be8303398d185338d060c33864f1f33511330332a82ad330bca3f330a8e35330961a632f5d1bd32e38d4f
  | 7, 9 => 0x4176068d416bf5b84149098f412c1b3840fe085a40e5429a40936de1408a06cf40846bf64079f6e6406f21e9405ffdff405c8f3d40455b7a403af74d401a1c4f3fed881a3fe000373fd3ef6d3fb404613f8aca813f5aa7ff3f55675e3f4a127a3f3bf5403f291ad13f227ddf3f15457d3ee6de3d3eb160ae3eabffa33e896cb83e72aa493e444aad3e3a3ac43de291263d8f565c3d8a3cae3d5b65d93d44b5c43d3e89f93d2c7c353ce1683c3cbde0b03c84d54c3c346cd83c34563c3b5dab7f3b18ef823b0db0ad3b0c2ead3af6ada23a97b4d03a8e04dd3a8b1a653a64e63a3a4d6a953a17220e39fa66b039e16a4739c6347939a3264a39695eeb394f1420
  | 7, 10 => 0x4987e828497e1ccf49292ce249148db048fe85ee48f6d72e48c35a8b48bb35fd4850b42848360ca14834edba480eeebd47d0c7f247bf1d6347b76ea3476a5be9476409d74755b84447335cda4727debc471a541a46f1b31146de759446c9322546946162468eecc84667f2b74625da8245f5ff6d45f28fa645ef297545e1e20f45d91ef145afa45845a2cc4a4563ccbf4549390b453e55c1452fb72e4529a6cb44fe769744c22fd144ae84d94493839c4408d56743d7832c43a9f848439f80004397d14043555fb0434ac032433cb82e431f7df742e7b5af42dfcdcd42b779a3427042cf425bc8a44214dd16420d2e5641ec4f6f41d387bf41a58777417fec1d
  | 7, 11 => 0x5059633d5002261d500139404fff2dd54ffcc3574ff820184fa260824f9d1e774f84bcf94f518c244f49dd644f2dc6724f17f0274f0c43334f050fd04ea817a54e81f8b04e5372144e3b68614e3a3a904e26d84a4e086b364de2370b4dd542384dc9c7c04dc27b5b4d84259f4d77b7814d3fd1c54cfef3264cf929a74cde6d854cd6bec54c77c2484c70a3534c5ceb2b4c30b0dd4c173de94c16af5f4bf837324bf088724becd9904b9665454b86b0b34b5eae324b25a97b4b13daf94b0c2c394b093b3e4aee73794aeba8ec4acc75434ac64d7b4aa02b774a9bd7924a9428d24a932f4e4a83c1d64a77d2104a44957f4a4249ab4a3f5f3c49cb916949c9cfdc
  | 7, 12 => 0x58a76094588df5d9584e132a581a3e365810d46d57ef778e57b42182576d4781576751eb576611cb575e2473575675b3574ab38e5742a795573f8ef45707fb675703920356f8e29d567c7f515600570755ea83405571ce4a556f06955530a86c55100dac54fd3cee54ef689a54e7b9da54de0ffe54b8020854acafc454a96c0954a268625476a805546df95f5467b4c6545f13eb544bdb31540a4dbd53f747b753e591e853dbb72c53ca920853b2be7253842852536bdc28534afad352dbe8045289b2c45282040452747f075253af2952534f9451dd55d151bb2a0f5184d1d450eca9cc50e499dd50df0cf150dc89c550c8fcab509f54165096359d50754638
  | 7, 13 => 0x60a44355607f1ebe6058ad0a601d48af5fff9ba05fbac6fd5f9ee40f5f735dff5f5675315f1ff6eb5ef408b65edbff035ed6a3f15e5c41985e5492d85e427dc45e394d3c5dfe16575dd41be55dd08b735da6006b5d7bf2db5d6dd96d5d4be8d35d4b941a5d48a8d45d0f81b75ce5bb8e5cde0cce5cab1e5b5c4918f65c3b70415c33c1815c2c84db5c1f443a5bf13ab45bdd230c5bd468615bccb9a15b8c3f8e5b4dbe2c5b3c6e345b34bf745b26580e5b1f7a795b00c4075aecd9575aa52f8d5a7ee5485a6fa4e45a6beea55a5bc6655a4f521459f11cdb59c5935f59a3041859a0c2fc597bfa8959737dfd5936765a592cf529590d716858e6c54658bb531a
  | 7, 14 => 0x6909578d68ff6c1a68ec85cb689b99036874fb72684a9053683daa90682efe616817285368090f8967d94152673394256729b3cc67240676671ea51e671066ce66fc748866e5ae6b669e5573669a48866685c72066730cef6625b9e96617db0a65f74f0265bde69f6560b6cd651506a464bd70fe64b23f0e649466f26472b701646b28aa64512d1c642e54a0641ca4e76413866e640f67b163939f33637c7ea663669d956320cbf7631fb1536310f02f630aea4563020dca62deee88629d973362623a356243e4b461ff498161d0c2e561ca400861a45f8b613fcc2c61306f51610c35a86108511860fbe7f960f47f6c60c0e6cc60bd229660afae3b60ad45a2
  | 7, 15 => 0x730c5ff87301de5f72db63be728270b472739f54725db7fb71ffefc671c52b6a71b731cf7108872f70f943ac70e9cc8f70cc75eb70c13a8170ad28b870a579f8706e72537066c393703d873870120e996fb3739e6f9599c06f4c3cf56ee8713b6ecfcc7c6ecdef756ec911ee6ec7a3626e16b7eb6d916c166d35546a6d32e2006cf4f29e6cd257906ccaab146c85f2fa6c79ed6a6c4b6e046c24b1656bfd3c4b6bf899566bf58d8b6be1bd3a6bcb63fb6ba71d766ba0665d6b9d976b6b846d316b67104f6b0438936acf6be56abcdfc56ababa2c6ab78b856a8281de6a7ff6686a607cbb6a44543e6a4320db6a41599e6a08bb0569da0c1f69b2eaed69218327
  | 7, 16 => 0x7bf865d47bf0d3337b86605a7b6ec17b7b665f577b1fa70a7b12c27b7ac586e57aa157477a05242f7a03bbf57a01223179e85dd379e15a2879a30aba79952bdb797234ad79717a8d796fc1e17951d578794d3dac793a18dc792b8cc878e9916b78d131967800865577d135d077abf413778cb882776db3d87723c8d077231e6a771f39f87710f44076f9d20c76d063dd76c5d6f276b871ac76863e3b767f5e3c765c3f59765ba6437626fba5761e2a8775d20e9175cfa8b475cef4d375ace69a756ef7e9756948e6755c92467554e3867539d26975230650751532dd7508768874b5d9f474ae2b34746a0e0a7448134173a48879739a9980739a0e54734b2c82
  | 7, 17 => 0x8824c165881775a687e75edb87d85aa087b2ceb48788fa958786ba788756c638871ec9f88680741c8672012f8607548a85f1f72685ceb5ca85ab6563854276918527bd3a84fb0b2c84e60ad184c93e8b847e85678323a63b82effa2282de71178276397282585f948186abcb817be6a281303d8c8101e0aa80b9a05080b2da9b80b2a53b80ab0b5c809286e3808528c4807ff0398040d07880087aa87fe1a60d7f4af1e47f4590c97f445ff37ea020fc7e704a887e63c5ee7e4b58517e1a8a567e0bc1687e05acff7dffd2af7ddeb6337dd9697e7dcd0b037da0a7537d8293c07d2e7cf97c88cd607c60a6ce7c4bfba17c1abb197c170b2e7c140d477c001494
  | 7, 18 => 0x9322c34693049ac992f7889692d769a092b8eaa0928df76891fd1dbb919f9a92919a80f89147ad6a9117715e90d21748908eddba902de3229022657e90061e318fd08d408fa972eb8fa19e1f8f980bea8f7b76b18f6e24048f5f11de8f20258d8f0cd8ec8f052a2c8ef89bfa8ea2abb28e9fcbf58e965ddb8e94ccd38e1426838dc3e5858d869bbd8d5eaaf98cfa91f68ced12b28cd916648cd7ccae8cd766ed8cad401e8c9a327f8c73f3678c66e23c8b7e195e8b1fd6d78aa44b2d8a7994f88a4b88898a4b2c568a1fecb88a0b34fc89e4bd8189b9a4c589b019e589a86b25894ebb5e89211e6a8906426c88f834fd88cd013b888f7ea4882e82c9882be4e1
  | 7, 19 => 0xa170cb80a0c9b77fa0566735a048d476a046c73fa041465da0369f44a030bf879fada3039f8732b19f5ea4e59f27e99f9f241f2f9ed6de7b9ec9ae489ec0d7899e1370af9debfd949dce524d9d6fd84f9d65b4079d3121ea9d0504429cf2a1969cb3538f9cad2a7e9c6f504e9bf3d47a9be3e09c9bbf435b9b6512559b258fe99aebfe8a9aabbbef9a8abc959a7a06c29a70c37c99ee388299ce680e998cea0d996c23f498e9771598bfc76298a19efa989a692798411d819832c62697a00225977488ac9710a458967fbfcb960bb76c960434e995fc862995d4c56f959bf1de9595a4cf9551aacc947da14a942a4f209402c40593e5c51a93ad21ba9323975e
  | 7, 20 => 0xb43f5990b3c1e194b3b09514b0de38b8b0d3c397b0b9922fb08b6c2bb06379a0b03d009fb02ac814b0231954afa8260baf79b774af75ff26af47d2e4aeaf3682aeae39fdae68ce65ae28502fae1759bbad8797a6ad7f4391ad4120a3ad3b090dacf689daacc73d6aaca06ab9ac7b9e87abd8f0d3ab676f4faac711ecaabd8836aa9545c7aa8b3282aa5e717daa2ce68baa2cb15caa00aaa3a9dd3bf7a977e211a94093e3a8e78fc4a8cb32a4a81e26c1a80fa957a7cf5c2ca7a9082ba7347521a70ef21ea65c3616a57a8d62a5535ce4a4eede4aa4dede88a4c4fe3ba4ae7b11a40b50aca3c1ab4ba390017ea3744415a2cd8bc3a29245d0a265fcc7a25e4bf1
  | 7, 21 => 0xc92a9c24c75fdf6ac7554d2ec7337313c72863d7c6bef9f1c6b11a16c637c9f1c60d321bc5ff83fec5821593c52f7576c510d9fac4e635f6c4b48854c4949487c3b4db41c3651e39c3606443c330dcd0c30d6fe3c2b84f8ac2009875c1eeb825c1dbd993c1ad43f5c00f108cbf58fb9bbefa2055bebb555abe51e5eebdc979a2bdb6b306bd2fc437bd1242f4bcbbca35bc9691cebc87e6edbc10ccdcbc0c7999bc042ef7bbe593ebbbae1bf7bba6dd86bba66d37bae8aadfbad4da24bac49c6dbac1507dba701036b9916a0eb8f398fbb8c9f8fbb7a1fd24b7694f48b75d88c1b72e368bb68b3589b666254db62eb3cdb5f36f3fb5eeb176b5e702b6b4bad623
  | 7, 22 => 0xde90f3a7de4eb049ddfb04cddd3b7b48dcd4de65dc2aec62dba78fe2db76ec15db59748fdb29872fdb23cb92da650bedda525ee2da4ab022da42d052da411fa3d979864fd9719f58d9680625d937fb5cd9303d2bd80862e0d675048ed615987fd5f531afd5b24264d5877e98d57db6c6d52b0a13d50bf219d4a12453d4001a12d3ab69cdd2e9db6bd2e808a9d2ddd086d2b422bed282c284d26c6f3ed2440c1fd0e5095fd0022fedcfaaeb5dcf527d16cf33b5c0cef767cfcea2794cce540370cd8c6716ccf052c5ccc7daa6cc8129dacc513b19cbedcfe9cbd77c2fcb7a3068cb7281a8cb71c13acb099803cae6a019ca740502ca5180ccc9f05afdc9c359b5
  | 7, 23 => 0xff9c5d73ff88f5fdfe69481bfc465d48fb97c126fb379514fab495f5f8dc8889f7e041b5f72a0023f6875a6cf6623816f462ddedf33b5fd0f2854adff265e2cdf2000644f10d01a6f087d5f3f03d9387eeb4af79ee0a9ec1ed86fa4eed7abd14ecbba0bdecb47af8eb3b1836eb2980d5e5fe1d32e5cc13a1e5a92eafe5192fc1e4e88dfde44f55b6e3ecbae8e3dbcae0e298b8f8e1760161e12fee6ae1283faae1151f08
  | 8, 0 => 0x141a4f1c13b5da6d135211a212b8ab4112ae5da312798028124e26351234695d11eb7ccf11d74806119811441142fa411134c93410d1aa96103ead2a0fc22fb60f8898390f5c5cfb0f3d84400ea68d810e85c3d30e8414b20e7e15130e783ebe0d52c9a60d4d98860cea20e10cc7aa850c867e660c22507d0c167f100b989d440acf09dd0a9628be0a71f95609ee1b6f09eba6f40878675807bd347d0754ea1506634425064612c706291d8305c61dd605ad2f3405a3eb0a059e8b170590310f05869eb105169eb0040745c602d5abde0296f5790291d00a023f103c01a603fb0198251c0129b75501013f3600dd496a0086a50c006499150027347900103def
  | 8, 1 => 0x284db2db2775450f2774c460275958f22705880d26beaf6f26bb2fef26a4b5bf265363bb264ea12126488ebe26396ad425bece64258a6ea424cb7b2924a7e76c246554a62429651523a7fde62310763b225e4221225c733222543c1c2236825921e9d24d21ada82821a5f96821a1d2672081cc612064873a204aaf2d203e530f203cd04e1fd3d3851f3108e21ee4e3db1ebb13731eb3facb1e7359ed1d989e101d81c57f1ca0b1831c27ad6d1b70b1901b5aa1f21b52f3321a5d39541a45ab1d1a2bfa9c1a0ece70196672e1195294511900f42918e3fb0a1881f686181aa941175a929b1729918f16e8db181606144c15ff8a4715f86a8015f022ce1561a43a
  | 8, 2 => 0x3ee6de3d3e80cd693e277fff3dc32c533d8620523d6054973d18fbc93cd7d7c23c9f3cdf3c9dc2fe3c9d75a23c8fe41f3c39fd5e3bf3e2703b3c318a3b23954e3acd3e823a8b1a653a861c993950034037a1ed1c36c744ae36ad51603678c0eb366fa272363c57f4361b1af435d89aaa357bcd57355e29ce3518dab13481847a345b6585342cdee933d93c6b339be83033193e9a330961a632d2967c315024ba31381b073055c0a6302ca7772eedfa852edbd6b52ea0b9112e9e70832de85b922d988a382d90db782d6df75a2d014b912cb7e2692c9946a22bcf9a012ba0a43a2b89112d2b698d6c2a9b9ca62a7c85282a6cf0712964176b291abe562889888f
  | 8, 3 => 0x55ab6c46552722ed54b47b9853b7a8b55342fdb7531915d1530ec13f52942b72528ca242523dc211520a3fab51efbb6051d2062b51bb2a0f516924ff505beeb35059633d4f943bc44f8c57c24e9d19034e7327324e1db72a4e1717654e0e9fc94e00c0ea4de27c5e4dd111674dc27b5b4d17706a4cfd734b4cd8ba054ca60af44c173de94bff26be4bf147df4bc969994aee73794a0d197449e8d486499cfa0a499b08ca49148db048f0bd7d48ebd2aa48b85b5d472e33c146e1bded45f6b58445179a8f43a9f84843555fb0433f660a432891ef4309ffd842bf286342b779a342815d8a41d9fb78413ca69640db2d8b40bb283440455b7a3f8b9abe3f49363a
  | 8, 4 => 0x76f0de3376db0b2e76b015da764692e674f2245d72b28339727daf3d72739f546e34ebde6cd622c66c4b6e046be1bd3a6bcb63fb6bc490ee6b7c11ab6b58c0516b1be3666aa2ab606a5eea176a510b386a0139de69d0a4b069b2eaed67f1c0d36709aa616554bad1651506a464ffcc4e64cf00c5647899486449b75d640159026347643b62623a3561f427ee61ca400860d158045fbac6fd5f5d13a95f492eb65eebace45ec2fe405ebcebc25dc82fa15d9647d45d93d62e5d6275f45d3a46645d2e415c5d23bf8f5bff541c5b4388f85b2acd595a437adf59f684b25905159658905d13584e132a56fffaeb56dbe56f568ff7f15686958d567ee6cd55bb43f7
  | 8, 5 => 0xa309310ca16c46909ffd08839d42bc1d9d3121ea9ce015509bfcd7929985b80798fcecee985a34f7981b7e929710a458965f34589603a49895a996be956125c69396353d92b08ece92278ab59117715e91015b8b90061e318f6680978f46f2108e2374cd8d7f04bb8c1a6ee88bed86128ab84b5d8a8bfac78a7994f889f226db8968a0cb89605ac2886bb2a5877c8a9f872610b886a324548651842c85e99b5485520fcd8492c7cd83233d80804a30517f5f0e0b7e1a8a567dd5c4a57dad4e397d356db97d303bbe7cea112d7cd372a07c439fcf7b2b17a17ab597257aa1574779dc30da79c9043d79a4d76c798a90b2794717d6791d9b4178f04d3477211a3f
  | 8, 6 => 0xd87f9952d69e993fd697c1d4d64007d5d27a66b2d0e5095fd0e4e8e0d0dd3a20d0317033cea2794cca35eab9c7ad77bcc7466283c707ac1ec6b603d4c61b5c10c5dca5abc4ac2c82c4605fcec30bd3fac21dcfbbc1c6e06ec110cb7dc1043454bf09aa00bef4bb49beb2f988bcc8e334bc5e25f5bc4e7163bbec3344bad4da24ba477786b9782853b84d21e0b7a3f583b644e080b559ed2fb4d0d4a4b47be621b37ef559b32b1ae2b253eee6b1b17014b18cc501b0f51e5bb0ec7e1fb04d71d7af95e2ffaec64c0eadab993dac3ab49daabfa2cbaaa935daaa8df529a9cb11c2a8d9852aa8d69abba71939e5a70b5b06a6c41187a5103ec2a4dede88a4a02823
  | 8, 7 => 0xfc3e0176fb7259a6fab495f5f8b72109f6657479f33b5fd0f2854adff109fd47f03d9387eb3fcd10e9d3bc26e878be20e606f433e0d9cf49df71e0b2dede789bdec49712dd114471dd0995b1da4c5f43d8dd76c6
  | 9, 0 => 0xb47be6218ab84b5d7cea112d76f0de3351bb2a0f4f8c57c24aee73793e277fff2eedfa851e7359ed1729918f1606144c1142fa41
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0x8550484301000000000e100000000000000700000000000090000000000000000000000000000085504843020000000000000000855048430300000000000000000000006100000000000e1000000054041200000855048430300000104402000000050484200000000000000900000000000000008550484301000005408520000000000000000000000104107000000000610300085404843040008550484301000000000000e00000000121000008540484304000c9504c8302000000000000c00000000021000000000006100
  | 5, 1 => 0x31485204000000000000a00000001081030008550484301000855048430200085504843010008550484301000000000000900000000000090000000000009000000000000900085504843010000000006107000855048430300000540c1200000854048430400000000021000008540484304000000000a10000000104402000000050484203000000000a100000000000000c0008550484302000005344020000000000000000000000006102000000000000a000000000e10000000000000090008540484305
  | 6, 0 => 0x380a200000000000a106000000190c203000000000e1000000000006102000000010c102000000000210600000204412040000000002102000000000a10700000504842010000000006107000000380a2000000000000006000000000a101000000180220000000000000030000002806200000000000e107000000000000600000104402000000000006102000000000610600000540c920300000534402000000002806200000005404120000085504843030000001802201000005404120000000001041070000000006104
  | 6, 1 => 0x48062000000000006100000000000a10000000000000080000050504202000000000000000000000000090000000006100000000000a100000000000e107000000000000f000000000a10600085504843020000010440200000000000610600000540c920200000000121060000000006101000000000610700000000c110000000018022040000000000009000000000a101000000000a10800000540c12000000000000003000000000610200000000000000000000002108000000000000800000019082030000003802200
  | 6, 2 => 0x2106000000000a1030000000012100000000001210800000038022020000050484201000000000000a00000540412000000002802200000000000e10700000000000070000000000006000000000610000000000061030000050484202000000000a108000000000e108000000000000a0000004806200000000010c1030000000006108000000280620200000540812030000021484201000000180220000000540c1200000000000e107000000000000300000000061030000000000007000000000e1080000000002101
  | 6, 3 => 0x12101000000000000a00000028062010000054041200000000010410200000000000080000000002100000000000a106000855048430300000000121070000000006103000000000610000000039082030000000000000000000290c203000000010c1080000053440200000000000000000000038022020008550484301000005404120000000514c820200000048022000000002806203000000000610700000000121070000000000000000000000a1060000000104107000000000e106000000010c108000000000a103
  | 6, 4 => 0xe10700000000000090000000000000000000280620300085504843010000000006100000000000610000000000000010000000000000000000000e102000000000a10000000314852020000000000007000000000a107000000001210700000000061020000021484201000000000000700000504c820200000000c5104000000000a1060000002806201000000000e10200000404842040000001802200000000000e10800000214842020000021484202000000000a104000000000000000000000000030000003802202
  | 6, 5 => 0x8510400000001011080000000002108000000290c2030000000006100000005348420300000540852000000000101107000000190c2030008550484302000002148420400000000000060000054041200000000000e107000000010910600000540c5203000000000a108000000190820300000000c1100000003250c2030000000000007000000010c103000000000000c000000380620300000540c9200000000001210700085504843010008550484301000000000e1000000000012100000000000e1000000000006103
  | 6, 6 => 0x504842010000000000007000000000a10200000000000000000000000003000000090420200000001011070000000002100000000000000100000000000000000002806201000000010910600000534402000000000002100000000000e103000000000610600000540c92000008550484301000000004110200000540412000000000000002000000000a103000000000000600000000c9107000000000610400000524402000000000101107000000000210700000000021080000040484204000000000a1020000000006106
  | 6, 7 => 0xa0000000002100000000000000200000000000000000003806203000000000e107000000000e1020000000000002000003148520200000000c5106000000000000000000000000070000050484201000000000e10700000001011070000000000009000000000210200000324c82020000000006100000000000610000000000000010000001904202000000000e1030000000109106000005050c2020000000002108000000000000800000000061070000040484204000000000a10300000540c52030000031504202
  | 6, 8 => 0x5348420200000214842040000002904202000001044020000000324c5202000000000a1000000052440200000000290c202000002148420400000524402000000005904202000000000a108000000000000c000000000210300000214842010000050484201000005408520000000000000090000000000000000000000610300000540c9200000000000a10700000028062020000000012102000000000610800000314852040000010440200000000000000000000000411040000000002101000000190c203
  | 6, 9 => 0x610000000000061000000000006107000000090c2020000000006107000000000a101000000000000200000540c920000000540412000000050484203000004350920100000540c92000000010440200000000000a1000000002806204000000000e10300000000121060000000104107000000010c10800000018022000000001802200000000000610700000000401000000000002100000000000210000000000061070000000000003000000000a102000000000210600000540852000000000000009000000000e107
  | 6, 10 => 0x1041070000054041202000000380a202000000380a200000000000e100000000000e10200000324852030000000006102000000000e1000000050484200000000000210800000540c1200000000000a10800000000000000000010440200000000180220100000534402000000053484203000000000e100000001044020000000104402000000000000001000000000e1060000054085200000000280220300000028062000000054085200000000000a10000000038062000000000000009000000000e1020000000109106
  | 6, 11 => 0x8550484302000000000a10700000540c920000000000021000000054085203000000280620400000000121070000054085203000005048420200000028062010000002802200000005408520000000214842030000000002100000000010c108000003250c2030000002806200000000000000e0000000000007000000000000b000000180220000000000000000000054085203000005344020000000540c920000000038022010000000012107000000000e106000000010c102000000000e101000000380220400000514c8202
  | 6, 12 => 0x380620200000000000000000000006108000000000000a00000038062020000054085202000000010410200000540412000000054085200000000004110000000000000000000054085200000000000210000000540c1202000000390c2020000000012108000005244020000000000000060000000002108000005348420000000524c02000000001802205000000000000b0000000000001000000000a1070000003806200000000280220000000000000080000000000000000000090c20200000104402000000050484201
  | 6, 13 => 0x21000000000000009000000000e1000000000000000000005408520000000000000010000003806200000000000000100000514c02000000053484202000000480620000000540c1200000000000e1080000000000009000000010110700000000021070000003802200000000000000700000504842000000054085202000000590c202000000180220000000544842010000000012108000000010110700000000021070000054041200000000000e102000000000e10000000000000090000031485204000000000e107
  | 6, 14 => 0xc910700000540412000000000006107000000000a10700000000000000000010440200000000000e1080000000012108000000000000000000000021060000021484203000000001210700000000021070000000012101000000000000000000104402000010d424853010000000101108000000000210800000028022030000000101108000000000a103000000000000b0000000002106000000000e1000000000104107000000010c1030000000000000000000010810300000000000060000000002107000000000a101
  | 6, 15 => 0x380a20400000540852020000000000007000000000210800000001041070000000000001000000010d1010000054041200000000000a1020000000006100000000000610000000505042020000054085202000000000a10700000540c52030000052440200000000000000600000019042020000000000009000000000210600000000021000000000002101000000000000300000001011080000000908203000000000000a000004348420400000039042020000053440200000000000a1060000002802202000000000e108
  | 6, 16 => 0x4048420400000540c92000000000000001000000000000000000000000010000004806200000000000610700000000000020000000002102000000000000000000000061000000040484204000000000610200000000021000000000006107000000000000e0000053484200000000000a108000000000e1000000000000002000004348420400000000000080000054085200000000480e20100000000121000000000012100000005404120000000000121070000000104107000000000210100000000061070000021484202
  | 6, 17 => 0x540c9200000000000000100000000121000000002802202000000000a1060000000006103000000000001100000000000060000054041200000005050c2020000000000006000002148420400000000c910800000000000000000000000002000001044020000000104402000000000000006000000000a1060000000000001000000000e100000000000000700000001011070000000002107000000000210600000000061080000050484203000000000e10700000028022020000000000006000000380a2040000000000001
  | 6, 18 => 0x2107000000090c20200000000000090000000000009000002148420100000104402000000000000001000000000610700000000000090000054085202000000000000100000000000090000054041200000000380a200
  | 7, 0 => 0x30000000000007000000010110700000000021070000000006102000005408520300000000851020000000012100000000000e10100000001041080000000085105000000000000a00000000c510200000000851030000000006101000000380a203000000000e10400000000851010000000006100000000000210200000000c510200000000021010000000108103000000000000500000000000020000000041104000000000a10200000000021000000000101107000000000210700000000c91030000000006100
  | 7, 1 => 0xa103000000000a106000000000e102000000000610400000000000060000000000008000000000000000000000000080000002806201000000000a1020000000000003000000004110200000540852020000000000006000000000000c00000000121000000002802202000000010410200000000061040000000006101000000000000100000000401000000000006103000000010410200000000000010000000006101000000000e1000000000000003000000010c103000000000e10000000000851020000000006108
  | 7, 2 => 0x3000000000610300000000000050000000002102000000000a10100000000c9100000000010410700000000c9100000000000210200000000c1100000000000a103000000000000000000000061030000000006100000000000000d000000000210000000000061010000003806201000000000a10200000000c5102000000380a201000000000000400000000c510300000000c510000000000021000000000084104000000480620100000000061000000004802202000000000a10000000000021000000000000007
  | 7, 3 => 0x600000000000060000052440200000000280620100000000000070000000000006000000000610100000000c9100000000000a103000000000e1030000000000007000000000210000000000000010000000002100000000000000300000000c910800000019012020000001802202000000000a102000000280620300000000121000000000000007000000000000200000038062010000000104102000000000000600000000021030000000012100000000000a107000005408520300000000000080000000908203
  | 7, 4 => 0x70000000000000000000008510300000048062010000000000001000000010c1020000000006101000000008510100000000c5100000000000e103000000000e10200000000061040000000000000000000000210000000000000070000000104102000000000a1020000003806203000000000e107000000000e104000000000000d0000000108103000000000a1010000000006101000000000210000000048062030000003806202000000000000100000000c4102000000000610100000000000040000000002101
  | 7, 5 => 0x7000000000a1020000000040100000000010d10100000000021020000000041102000000000000800000000000070000021484202000000000a1030000000000004000000000a104000000010c1020000000085102000000000000e00000434c520100000000851040000000006100000000000a108000000000a1020000000085103000000190120300000018022030000000081103000000000a10300000000c9103000000010110800000000021080000000002102000000000000600000038062010000000000000
  | 7, 6 => 0x7000000000210000000000851010000002802201000000000a104000000001210000000000851040000053440200000000000000200000000000000000000000007000000000a103000000010410200000000000080000043501201000000000000a000000000a1010000000006100000000380620200000000061010000000002101000000000a1000000000006105000000000e100000000000a1020000002806203000000000000800000000121020000052440200000000008510400000000000000000000000007
  | 7, 7 => 0x1001000000000085101000000010c103000000000000c000000000a105000000000000100000018022020000000000000000000000000700000038022030000004802201000000004010000000000000020000000041100000000000e1030000053440200000000000610800000000851050000000000003000000000000d000000000a1050000000081102000000380a2030000000000010000000008110500000000000030000000002105000000000e102000000000e100000000000000800000000000030000000006100
  | 7, 8 => 0xd00000001041020000003806201000000000a1080000000000008000000000210100000000000070000050412203000000000a1040000000002103000000000e102000000000610000000000061000000000002108000000000a102000000000a101000000000000200000000021010000000006100000000480a202000000000610300000000c51000000000000000000000000000700000000851030000000000007000000000210100000540c920200000000000060000000000002000000000000700000000c9108
  | 7, 9 => 0x8510100000000c5102000000000000500000000000070000000000000000000000000400000000000040000000041101000000000210600000000000050000000085100000000001210700000000851000000000081103000000000e100000000000e10000000001081070000000012101000000000000700000000000080000000041103000000000610100000000000040000000012100000000000000d00000000061030000000000003000000008110100000324852030000000000000000000000a102000000000e102
  | 7, 10 => 0x401000000000002104000000000a1020000000000007000000000e100000000004110300000000000060000000000002000000000000900000000c91000000000000000000000000a10200000214842020000002806200000000000000200000000c51000000000006100000000480a2020000000000000000000000a103000000380a20200000000061070000053484202000000000610100000000061010000000000007000000000210000000038022010000000006103000000000000800000000121000000000084104
  | 7, 11 => 0x42485201000000000000500000000000070000000002107000000000a10700000000061020000000000007000000000000100000000000080000000081100000000000000b00000000811000000000006102000000000a10400000000851010000000012100000000010c102000000000000800000000000030000002802201000000000a10200000000061030000050484202000000000000c00000544842010000000000000000000380a200000000000000b0000000100100000000000e100000000000e1030000053484203
  | 7, 12 => 0x6100000000000610000000019012030000001802203000000010c1020000000081104000000000610400000000c9100000000000000700000000c9100000000000a102000000000e10000000314c12020000000081105000000000a10300000000000000000000000000000000008410300000000061030000000000007000005408520300000048022010000000012100000000280620300000000000070000000000008000005400a202000000280620000000544c5201000000001210200000000021010000000000001
  | 7, 13 => 0xc5100000000000a1050000000041103000000000e10800000000000070000000000003000000010d1010000000000003000000000210300000540c12000000000085101000000000a102000000000e1030000000000002000000000000000000000000080000000000002000000480e201000000004010000000000061040000000002108000000000a10400000000000000000003806203000000000000c0000000000008000000000a103000000380a2000000000000002000000008110500000000061020000050484203
  | 7, 14 => 0x84105000000000a108000000001210100000000000070000000006101000000000000e0000000085101000000000a101000000008110300000000c110400000000000080000000006105000000000210800000000000090000000000008000000000000700000000c1100000000000610400000000021000000000002100000000000000100000000061020000000006101000000000000000000000000030000004806202000000000a1060000000000004000000000a107000000000e107000000000a10000000000c9100
  | 7, 15 => 0x21020000000002100000000290d20100000000000000000050412202000000000a102000000010c102000000000000900000000021070000000006108000000000000300000000c1103000000000610000000000c1101000005048420200000540c120000000000021040000000000002000000000000800000540c120000000000000000000000012108000000000a103000000000a104000000008110300000000000020000000081105000005244020000000000851020000000006104000000000e103000000000000d
  | 7, 16 => 0x100100000000000000700000000000060000000000003000000000610800000000000080000000002101000000290120200000000061010000002802202000000000610100000314c1202000000000a10100000000c110000000000000070000000100100000000000e108000000000a1000000000000003000000000a107000000280220000000000061000000000085101000000280620300000000000070000004806202000000000610300000000121000000000006100000000000e10200000000000060000000000007
  | 7, 17 => 0x61040000000002102000000000000b000000000e107000000000a101000000000000200000000021060000000002105000000000610200000000021000000000006104000000000000000000104402000000000000002000000280220100000018022010000000006102000000000000000000000c91000000000000008000000000a101000000008110300000000000070000021484203000000008110100000000021010000000108103000000000a1040000000085103000000000210100000000000070000000000006
  | 7, 18 => 0x10c1080000004802203000000000210600000000061020000000085102000000008110300000000811050000000000007000000000a10800000000061040000000006107000000000a100000000000a1010000000000007000000000e1070000000006104000000010c102000000000000700000000c51020000000006103000000000000300000038062010000000006100000000000a1020000000000003000000000000600000000061000000000000002000000280220000000000c510200000000000050000000000006
  | 7, 19 => 0x1000000010c102000000000e102000000000610000000000061070000004806200000000000000100000000851020000000002103000000000a103000000000a103000000000a10300000000061010000000000001000000480a2020000002802200000000000000200000000000080000000006105000000000a1070000000006104000000000e10400000000000020000000085102000000000610500000000c1100000002148420200000000000000000000006102000000010410200000000000060000053484203
  | 7, 20 => 0xa10400000000021010000000000008000000000000300000000000060000000108103000000000e1020000000000008000000000a10100000000000020000002806200000000000e100000000000000100000000061030000000085100000000008510000000000000070000000000000000000000e10300000000c9104000000000210200000540852020000000000000000000010c102000000008110400000001011020000000002102000000000000800000000c510400000504842010000000006108
  | 7, 21 => 0x610000000000411030000000000008000000000a10100000019012020000001802202000000008410200000000841020000000084104000000000e1070000000000006000000000a10500000000411020000000006100000000000610000000000000000000000085102000000000a108000000010c103000000000a102000000000a10200000000021030000004806200000000008110100000000c910000000000000090000001802201000000190d2010000000085104000000000210700000000c91080000000000006
  | 7, 22 => 0xe100000000000e101000000000a1000000032481203000000000210000000000061010000000085104000000008510000000000851000000000084101000000000e102000000000a100000000000a1010000001802201000000004110000000000411000000000000000000000000000000000000c5104000000000a1020000000000002000000000000d000000000e100000000000e100000000000000e0000000002102000000000e1020000000006107000000004110000000000c110000000000061040000000000001
  | 7, 23 => 0xc110000000000061010000000000000000000000a10600000000121080000000006101000000000a1020000021484201000000000a1010000001901202000000180220200000540c120000000001051010000000000000000000000e1020000000000007000000000a10100000038062000000000012101000000000210300000000c510200000000021000000000006102000000000a1030000000100100000000000610000000000021050000000002100000000000a1040000000012107000000000a101000000000e100
  | 7, 24 => 0xc510000000000851000000000012107000000000a1050000000002100000000000a10300000000c110300000000061030000000041102000000000000e000000000e107000000000210500000000411030000000012107000005048420100000000411040000000104100000000010410000000000c9100000000000a100000000000210500000000000080000000101100000000000e10700000000c110000000000000000000050484201000000000e10300000000c1103000000000a1050000000000007000000000a100
  | 7, 25 => 0xa1010000053484201000000000a10100000000000020000002802200000000000e102000000000210200000000021000000000084103000005048420200000000061040000000002108000000008410400000000c9102000000000a1020000000006107000005150820300000540c920200000000c510300000000000030000000104102000000000e10200000000000070000000000007000004348520100000000000080000000041100000000004110000000000121000000000000000000000480a2020000000002100
  | 7, 26 => 0x280220200000000121000000000085100000000000000000000000000080000000006105000000000210800000000061050000000000001000000000210000000000021000000000085100000000004110100000000811020000000000002000000000610200000000061050000000000000000000000a1010000004802200000000010410200000000c11020000000085104000000000a101000000000e100000000000a102000000000610600000000021010000000006104000000280620200000000c11030000000000002
  | 7, 27 => 0xc91030000000000000000000000e10800000028062000000000081104000000000e10000000540412000000000000006000000008510400000000c910400000018022000000000006101000002148420100000000c510000000000c5100000000000e1020000000002103000000000a1010000000012108000000280620300000504842010000000000007000000004110000000540c920200000000c91030000000012101000000010c1020000000006100000000000610000000000c9107000000000e1000000002901202
  | 7, 28 => 0x61070000000084104000000000000100000000061050000000006107000000000a105000000004110000000000061060000000000007000000000a10100000000061020000000000008000000000e10400000000061010000000006100000000000000c000000000610300000504842020000000006101000000380220000000000000000000000000000000000000610700000000c5103000000000e101000000000a101000000000000200000214842010000000000002000000000610400000048022000000003806203
  | 7, 29 => 0x210100000001011070000043509201000000000a10000000540c120000000000c1100000000000610800000018022000000000085104000000000a101000000000000800000000000000000000085101000000000a1010000000000008000000000e10400000000000030000000000001000000380a2010000000000006000000590d201000000000a103000000380a203000000480a20100000000c91000000000081101000000000000200000000061000000000000007000000000a10500000000411040000050484201
  | 7, 30 => 0x10010000000000c91000000000000000000000000a100000000004110300000000000000000000006101000000010110800000038062000000000002108000000000a101000000000610100000434c52010000000012101000002148420100000000811050000000006103000000190820300000000061030000000006102000000000000000000540c12000000000006108000000000a10200000504122030000054041200000000000610200000000021000000000041100000000000e100000000000a102000000000e107
  | 7, 31 => 0x41105000000000000c00000000c91030000000000002000000008510100000000841010000000002101000000380a2000000000085100000000000000800000000000080000000084102000000000610200000000c510100000029012020000002802202000000010110700000000021070000054041200000000480e20100000000851030000000000007000002148420100000028062000000000002104000000010410200000000411040000000040100000000000a1000000000006102000000380a2010000000002104
  | 7, 32 => 0x300000000000000000000084104000005344020000000001041000000002806201000000000210100000000061050000000002100000000090d2010000000000000000000000000700000324c520100000000000070000000000001000005348420300000000000080000000000008000000000610000000000061000000000002100000000000e103000000000000a000000000000700000000411000000000041100000000000a10100000000000070000000000007000000280220000000000841030000000084104
  | 7, 33 => 0xc5100000000000610000000000061010000000000000000000000610700000000000080000000000006000000000000100000000061010000000000000000000001210300000000811030000000000000000000000a1020000003806203000000480620100000038022020000000000002000000000a1030000000000009000000000e10400000540c52030000000041100000000000a102000000000000000000000811000000000085100000000000e1000000000006105000000000610100000000000070000000085104
  | 7, 34 => 0x38062010000000012100000000000a100000000000000700000000c5100000000000000800000000000030000000002100000000000e1020000000041100000000000000b00000000851000000004806200000000000000300000000811020000000081100000005408520200000000000020000000000008000000000000100000000000050000000104107000000001210800000000811040000000000002000000000610800000000000000000000006107000000000a1020000000006103000000000210400000000c5100
  | 7, 35 => 0x21020000000006104000000000610100000000000060000000002102000000000000400000000851050000000081103000000000e102000000000000000000000061000000000002105000000280620100000540c920000000544842010000000006100000001044020000000000000080000000000002000000000a10100000000c510000000000c91040000000000006000000000000700000000000030000000002100000000010c102000000000e100000000000a1020000000081100000000010c1020000004806200
  | 7, 36 => 0x20000000085103000000000610200000104402000000000006103000000000a10100000000c910000000048022020000000000000000000000a10600000000c510000000000061020000000000001000000000610800000000c51000000000040100000000000e10700000000c910300000000411050000000006100000000000a104000000000000800000000401000000000040100000000000e100000000004110000000324c5201000000000001000000000c51030000000002102000000000a1030000000000006
  | 7, 37 => 0x90000000006102000000010c1030000031441202000000280620100000000c5100000000000000700000000c91020000004802203000000000a10200000000061000000000000008000000000000600000000411050000000002100000000000610300000000000000000000012100000000004010000000000061020000000006100000000000210000000000021020000000002102000000000a100000000000a100000000000610000000534842030000000006102000000000a10200000544842010000000002100
  | 7, 38 => 0x40000000000007000000000a104000000000610500000000061000000000012107000000000e104000000000000000000000000070000000000007000000000210000000000000020000000000000000000000a10300000000c1103000001044020000000000061010000000006100000000000e100000000008110000000001011030000000002103000000001210000000540412000000004806201000000000a1030000000002105000000480a203000000000a101000000000000700000000000080000000085104
  | 7, 39 => 0x6108000000000a101000000000610100000505042020000000000003000000000e1000000000000008000000000000700000000121020000000085103000000004010000000544c520100000000c910400000000000080000000000008000000000e104000000000e100000000001210300000544842010000050484202000000000e1080000000000007000000000000700000000061020000000006100000000000000700000000000060000000000007000004344120100000000121010000000000008000000000e108
  | 7, 40 => 0x54484201000000380220200000540c5203000000000000a00000000061080000000000001000000008110400000000c510000000000000000000000041100000000000000800000540c9200000000000000200000540412000000000002100000000010410200000000851010000000006102000000004110300000540c12000000000012100000000000a10200000000061020000004802201000000000a104000000004110000000000c910400000000061000000000041100000000480620000000000811030000000000007
  | 7, 41 => 0x2108000000000000a00000000000020000003802202000000000000000000000000020000053440200000000000e10700000000000020000002901203000000280220300000000000000000000012102000000000e103000000010c1030000000000007000000000a100000000000e108000000000000600000540c920000000000c5104000000008510000000000c51030000000041102000000000610000000000121000000004802201000000000e100000000000a107000002148420200000000000020000000084103
  | 7, 42 => 0x50412203000000000a1040000000000009000000000000800000000851030000000000001000000000000800000000841020000000002107000000010c102000000010110200000000000090000000002102000000000610300000001001000000000000001000000000e10400000000000060000000006102000005041220200000000000080000000000003000000000a10100000000000080000000000001000000000a10400000000000080000000012100000000000a100000000010110700000000021070000000100100
  | 7, 43 => 0x700000000000080000000085102000000004010000000000121080000000000003000000000a1050000000000000000000000e103000000000a1070000000000002000000000a1010000000041105000000000a101000000180220000000000000060000000006100000000380a200000000008110200000000401000000000000007000000010d1010000000000006000000004110000000000000000000000108103000000008510300000000851050000000012100000000180220000000000121080000054484201
  | 7, 44 => 0xa102000000000e10200000000000060000000000006000000000210000000028062020000000104102000000000610700000000061000000000000008000000000a1030000000041100000000000e1030000000006100000000000610000000000000020000000000008000000000210600000000021020000000000006000000000e1020000000002104000000000e102000000010110200000000021020000000081101000000000e1080000000006101000000000a104000000000000800000000c11000000002806200
  | 7, 45 => 0x70000000084103000000000210100000434c120100000000851030000000000006000000000000100000534842030000000085105000000480e201000000004110300000000c110300000001011080000000002108000000001210100000000000010000000000008000000000000d000000000a1030000000000008000000000a104000000000000700000000061000000000000000000000000000700000000021020000000085100000000000000c0000010440200000000000000200000000121000000000006102
  | 7, 46 => 0x480e20100000000851010000000012100000000000610300000000c9100000000001210000000000811000000000002103000000000e10400000000000000000000084103000000480620200000000000010000000000007000000000e10200000000c1104000000000000600000000c1102000000010d10100000540c9200000000000000200000540c9200000000000210600000000000000000000012107000000000a100000000000a1040000000012100000000000a100000000000610000000000061000000000006100
  | 7, 47 => 0x84101000000000e10200000000c11040000001802200000000008510400000000c1102000000001210000000000411000000000084101
  | 8, 0 => 0x400000000841030000000002101000000000000200000000000000000000006103000000004110300000000000020000000000007000000000a100000000000000000000000121020000000000007000000008110200000000000020000000000003000000000000000000000c5103000000010410200000000000080000000041102000000010d101000000000a103000000000a1010000000000006000000000000200000000000020000000081101000000008510100000000000040000000000002
  | 8, 1 => 0x81101000000000000000000001001000000000000006000000000000300000000000030000000000003000000000000100000000811020000000104100000000000000500000000000020000000000005000000000a10100000000000020000000041102000000000000400000000000040000000000007000000010d101000000000000000000000000080000000000000000000008110000000000000030000000000000000000000e10100000000000080000000006103000000000a10000000000851000000000084101
  | 8, 2 => 0x41101000000000000000000000000070000000000002000000000000100000000c11010000000000001000000000a10100000000021010000000000007000000000000400000000851030000000101102000000000210200000000c51000000000000003000000000000700000000000040000000006103000000000000600000000000050000000000000000000010d10100000000c510000000000000080000000000000000000000610100000000000030000000000007000000000000000000000000040000000000007
  | 8, 3 => 0x6102000000010910100000000c910000000000000080000000000000000000001210000000000000000000000084103000000000000300000000c9103000000000000300000000000030000000006101000000000610200000000c11000000000000005000000000a101000000000000000000000c51030000000101101000000000000100000001041020000000000001000000000a10200000000c11030000000101102000000000210200000000000060000000081101000000000000000000000411030000000000002
  | 8, 4 => 0x1000000000e100000000000000300000000000070000000000004000000000e10300000000000010000000006100000000000000100000000c1102000000000a103000000000000100000001001000000000006102000000000000300000000000050000000000000000000000000000000000c91000000000000002000000001210000000001001000000000000006000000000000c0000000000004000000000a10200000000000010000000006101000000000a10000000000000070000000000008000000000a102
  | 8, 5 => 0x610200000000000010000000000001000000000000300000000c1102000000010810300000000000020000000000004000000000000200000000c51030000000000000000000010510100000000851020000000000001000000000000200000000000080000000104103000000000610000000000121020000000000000000000008410200000000000070000000000008000000000000500000000000070000000000000000000010410000000000000060000000000002000000000000100000000000030000000000007
  | 8, 6 => 0x6102000000000e1030000000012101000000010510100000000000000000000000005000000000000500000000000030000000006100000000000a101000000000a1020000000000007000000000000000000000411020000000000001000000000a1000000000000002000000000610300000000000080000000000002000000000000200000000411010000000000000000000000000000000000c9103000000000000e000000000000400000000411020000000000004000000000000100000000000070000000000000
  | 8, 7 => 0x210000000000000050000000000000000000004110000000000411020000000000000000000000e10100000000851030000000081100000000000000000000000c91020000000000007000000000e10000000000000010000000000003000000000000800000000000020000000006100000000000000200000000000010000000000003000000000000c0000000000008000000000000300000000c110100000000000010000000085102000000000000700000000811020000000000001000000000000700000000c5102
  | 8, 8 => 0x70000000000008000000000000200000000000000000000000004000000000000200000001051010000000000003000000004010000000000000020000000000001000000008410300000001081030000000000000000000000a10200000000c1101000000000000200000000000070000000002100000000010d10100000000121010000000000001000000000000700000000841020000000105101000000000a101000000000000100000000000080000000000001000000010110200000000021020000000000001
  | 8, 9 => 0x84101000000000000200000000c1102000000000000100000000121030000000000006000000000000400000000000050000000000000000000000a101000000000610100000001051010000000085101000000000000400000000000000000000000001000000000000300000000c510100000000000000000000000001000000000a1020000000012101000000000000200000000c9100000000000a10100000000c910000000000c9101000000000000000000000121000000000041101
  | 8, 10 => 0x61000000000104102000000001210000000000851010000000006100000000000000100000000c5101000000008410100000000c910100000000c110000000000c910200000000000000000000006101000000000000300000000c1102000000000000200000000c110100000000061020000000000000000000008510100000000000070000000000003000000008510100000000061010000000000001000000000000100000000c910300000000c51010000000000006000000000000000000000000080000000000002
  | 8, 11 => 0x40000000000004000000000000700000000000010000000000007000000000a103000000000000000000000c5101000000010910100000000000020000000000008000000000610000000000841010000000000000000000000000d0000000000003000000000000800000000841010000000000006000000000610000000001001000000000000008000000000000300000001001000000000104103000000000000900000000851020000000000002000000000000200000000c1100000000000000700000000c9103
  | 8, 12 => 0x411000000000081100000000000610300000000000010000000109101000000000000000000000000000000000041100000000000000200000000811000000000000003000000000a103000000010110100000001081030000000000004000000000000d0000000000002000000000e102000000004010000000000000010000000002103000000000210000000000c1102000000004110000000000c11000000000104103000000000000100000000000010000000000000000000000a1020000000000007
  | 8, 13 => 0x100000000811000000000000001000000008410200000000061000000000000000000000000000000000000411030000000006100000000000000300000000c910000000000851020000000000007000000000000600000000c51020000000000008000000004010000000000c1100000000000000100000000c110000000000000020000000012102000000000000000000000000040000000000002000000004010000000000000020000000000002000000000000000000000000020000000000001
  | 8, 14 => 0x40100000000010d101000000000210100000000000000000000000000000000000000200000000000010000000041100000000000000700000000000040000000006100000000000000800000000000000000000012101000000010d1010000000000000000000000e1020000000101102000000000210200000000000000000000104103
  | 9, 0 => 0x200000000000000000000000000000000000000100000000000020000000000001000000000000100000000000010000000000002000000000000000000000000030000000000002
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_62 roots_62 8 s ws hint
  | 1 => checkCutEntry dom_31_32 roots_31_32 8 s ws hint
  | 2 => checkCutEntry dom_47 roots_47 8 s ws hint
  | 3 => checkCutEntry dom_55 roots_55 8 s ws hint
  | 4 => checkCutEntry dom_15_32 roots_15_32 7 s ws hint
  | 5 => checkCutEntry dom_23_32 roots_23_32 7 s ws hint
  | 6 => checkCutEntry dom_31 roots_31 7 s ws hint
  | 7 => checkCutEntry dom_59 roots_59 7 s ws hint
  | 8 => checkCutEntry dom_61 roots_61 7 s ws hint
  | 9 => checkCutEntry dom_27 roots_27 5 s ws hint
  | 10 => checkCutEntry dom_43 roots_43 5 s ws hint
  | 11 => checkCutEntry dom_29 roots_29 5 s ws hint
  | 12 => checkCutEntry dom_53 roots_53 5 s ws hint
  | 13 => checkCutEntry dom_46 roots_46 5 s ws hint
  | 14 => checkCutEntry dom_54 roots_54 5 s ws hint
  | 15 => checkCutEntry dom_23 roots_23 5 s ws hint
  | 16 => checkCutEntry dom_27_32 roots_27_32 5 s ws hint
  | 17 => checkCutEntry dom_30_32 roots_30_32 5 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_62 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31_32 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_32 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23_32 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_61 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_43 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_29 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_53 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_46 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_54 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27_32 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_30_32 _ hc
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
private theorem z5_16 : ∀ i, 16 ≤ i → i < 32 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_32 : ∀ i, 32 ≤ i → i < 40 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 32 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 40 → Z 5 i = true := (range_split (range_split z5_0 z5_16) z5_32)
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
private theorem z6_96 : ∀ i, 96 ≤ i → i < 112 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_112 : ∀ i, 112 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_128 : ∀ i, 128 ≤ i → i < 144 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_144 : ∀ i, 144 ≤ i → i < 146 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 2 144 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 146 → Z 6 i = true := (range_split (range_split (range_split (range_split z6_0 z6_16) (range_split z6_32 z6_48)) (range_split (range_split z6_64 z6_80) (range_split z6_96 z6_112))) (range_split z6_128 z6_144))
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
private theorem z7_368 : ∀ i, 368 ≤ i → i < 382 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 14 368 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 382 → Z 7 i = true := (range_split (range_split (range_split (range_split (range_split z7_0 z7_16) (range_split z7_32 z7_48)) (range_split (range_split z7_64 z7_80) (range_split z7_96 z7_112))) (range_split (range_split (range_split z7_128 z7_144) (range_split z7_160 z7_176)) (range_split (range_split z7_192 z7_208) (range_split z7_224 z7_240)))) (range_split (range_split (range_split z7_256 z7_272) (range_split z7_288 z7_304)) (range_split (range_split z7_320 z7_336) (range_split z7_352 z7_368))))
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
private theorem z8_128 : ∀ i, 128 ≤ i → i < 135 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 7 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 135 → Z 8 i = true := (range_split (range_split (range_split (range_split z8_0 z8_16) (range_split z8_32 z8_48)) (range_split (range_split z8_64 z8_80) (range_split z8_96 z8_112))) z8_128)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_0 : ∀ i, 0 ≤ i → i < 15 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 15 0 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 15 → Z 9 i = true := z9_0
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

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 14]⟩], 16⟩

theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by
  simp [wit, PEqualNP.MetaComplexity.Monotone2]

theorem wit_sz : wit.size ≤ 11 := by decide

set_option maxRecDepth 40000 in
theorem wit_ev : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = Nat.testBit (4278124264 * 2 ^ 32 + 4277074664) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_63.testBit r.val = (fun x : Fin 6 → Bool => Nat.testBit (4278124264 * 2 ^ 32 + 4277074664) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) (pt6 r.val) := by decide +kernel

theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124264 * 2 ^ 32 + 4277074664) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 11 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (4278124264 * 2 ^ 32 + 4277074664) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_63 11 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_38083_aux

theorem PEqualNP.Outside.L_meta_38083 :
  ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124264 * 2 ^ 32 + 4277074664) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124264 * 2 ^ 32 + 4277074664) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  exact ⟨PEqualNP.Outside.L_meta_38083_aux.wit, PEqualNP.Outside.L_meta_38083_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_38083_aux.wit_sz (PEqualNP.Outside.L_meta_38083_aux.lower s hs), PEqualNP.Outside.L_meta_38083_aux.wit_ev⟩
