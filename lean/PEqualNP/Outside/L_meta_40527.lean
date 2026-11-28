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

namespace PEqualNP.Outside.L_meta_40527_aux

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
def goal_31 : Nat := 0xfee88888fee88888fee88888fee88888fee88888fee88888fee88888fee88888
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_47_16 : Nat := 0xffff0000ffff0000
def goal_47_16 : Nat := 0xfeeafeeafee8fee8feeafeeafee8fee8feeafeeafee8fee8feeafeeafee8fee8
def roots_47_16 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_15_16 : Nat := 0xffff0000
def goal_15_16 : Nat := 0xfee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8
def roots_15_16 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfaaaaaaafaa00000faaaaaaafaa00000faaaaaaafaa00000faaaaaaafaa00000
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xeaeaeaeae8e88888eaeaeaeae8e88888eaeaeaeae8e88888eaeaeaeae8e88888
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55_8 : Nat := 0xff00ff00ff00ff00
def goal_55_8 : Nat := 0xfefeeeeefefe8888fefeeeeefefe8888fefeeeeefefe8888fefeeeeefefe8888
def roots_55_8 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_31_32 : Nat := 0xffffffff00000000
def goal_31_32 : Nat := 0xfeeaeeeafeeaeeeafeeaeeeafeeaeeeafeeaeeeafeeaeeeafeeaeeeafeeaeeea
def roots_31_32 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xeeeaeeea88888888eeeaeeea88888888eeeaeeea88888888eeeaeeea88888888
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_15_48 : Nat := 0xffff000000000000
def goal_15_48 : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeea
def roots_15_48 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0]

def dom_23_8 : Nat := 0xff00ff00
def goal_23_8 : Nat := 0xfefe8888fefe8888fefe8888fefe8888fefe8888fefe8888fefe8888fefe8888
def roots_23_8 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_39 : Nat := 0xff000000ff
def goal_39 : Nat := 0xeaeaeaea88888888eaeaeaea88888888eaeaeaea88888888eaeaeaea88888888
def roots_39 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0]

def dom_29 : Nat := 0x33333333
def goal_29 : Nat := 0xfaa00000faa00000faa00000faa00000faa00000faa00000faa00000faa00000
def roots_29 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_30_32 : Nat := 0x5555555500000000
def goal_30_32 : Nat := 0xfcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0
def roots_30_32 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_23 : Nat := 0xff00ff
def goal_23 : Nat := 0xe8e88888e8e88888e8e88888e8e88888e8e88888e8e88888e8e88888e8e88888
def roots_23 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xeeaaeeaaee888888eeaaeeaaee888888eeaaeeaaee888888eeaaeeaaee888888
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59_4 : Nat := 0xf0f0f0f0f0f0f0f0
def goal_59_4 : Nat := 0xffeeeeeeffee8888ffeeeeeeffee8888ffeeeeeeffee8888ffeeeeeeffee8888
def roots_59_4 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_27_4 : Nat := 0xf0f0f0f0
def goal_27_4 : Nat := 0xffee8888ffee8888ffee8888ffee8888ffee8888ffee8888ffee8888ffee8888
def roots_27_4 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_43 : Nat := 0xf0f00000f0f
def goal_43 : Nat := 0xeeaaeeaa88888888eeaaeeaa88888888eeaaeeaa88888888eeaaeeaa88888888
def roots_43 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_51_12 : Nat := 0xf000f000f000f000
def goal_51_12 : Nat := 0xffffeeeeffff8888ffffeeeeffff8888ffffeeeeffff8888ffffeeeeffff8888
def roots_51_12 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_45_16 : Nat := 0x3333000033330000
def goal_45_16 : Nat := 0xfaaafaaafaa0faa0faaafaaafaa0faa0faaafaaafaa0faa0faaafaaafaa0faa0
def roots_45_16 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_30 : Nat := 0x55555555
def goal_30 : Nat := 0xfcc00000fcc00000fcc00000fcc00000fcc00000fcc00000fcc00000fcc00000
def roots_30 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfeeaeeeafee88888feeaeeeafee88888feeaeeeafee88888feeaeeeafee88888
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

namespace S_31
def pairsG : List (Nat × Nat) := [(1, 3), (2, 3), (5, 7), (5, 21), (6, 7), (6, 22), (9, 11), (9, 25), (10, 11), (10, 26), (12, 28), (13, 15), (13, 29), (14, 15), (14, 30), (17, 19), (17, 21), (17, 25), (18, 19), (18, 22), (18, 26), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28)]
def r1sG : List Nat := [1, 2, 5, 5, 6, 6, 9, 9, 10, 10, 12, 13, 13, 14, 14, 17, 17, 17, 18, 18, 18, 20, 20, 20, 24, 24, 24]
def r2sG : List Nat := [3, 3, 7, 21, 7, 22, 11, 25, 11, 26, 28, 15, 29, 15, 30, 19, 21, 25, 19, 22, 26, 21, 22, 28, 25, 26, 28]
def mpG : Nat := 0x7ffffff
def pool6G : List Nat := [2203655214339, 26474465269020, 6601701725443, 2203722586371, 10999815608579, 5506485064963, 9904598948099, 6618881594627, 11034107974915, 18717552739094, 21998840644374, 21994562519829, 22016087622422, 22011809497877, 26431381373722, 26427103249177]
def xsM : List Nat := roots_31.map (· &&& dom_31)
def goalM : Nat := goal_31 &&& dom_31
def NN : Nat → Nat
  | 4 => 6
  | 5 => 32
  | 6 => 18
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xbee8438cac05225e72d944c672a18fee4d4eae6f30331b08
  | 5, 0 => 0xf8c80e39d68db2b9c56e12e7c5159104bee8438cb9d3a5c5b5aa084fac05225e7094d1496f5141bc6baa581369bef9695e1d4aa8578462a3537bfbe75299e96d526e44fc4ca62407439e85fd4166ee5a3d6007a93a6b8d4132f633fb305a4c6e2637312d1d973d961ac7d7cf1749ddc815863287155d31791344b69a1072b843
  | 6, 0 => 0xe40c141be0bddffac5159104b4992a82ac05225ea0508cfd7ecfa1837702c5a9578462a3554c825e5299e96d3a6b8d41276bea4325303d37206585ea1b8a7ef1126b25b70241d3e1
  | 7, 0 => 0xac05225e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x555555550000000000000000000000000000000000000000000000000000000033333333000000000000000000000000000000000000000000000000000000000f0fffff000000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000f0f00000000000000000000000000000000000000000000000000000000000000ffffff0000000000000000000000000000000000000000000000000000000000ff00ff000000000000000000000000000000000000000000000000000000000000ffff
  | 0, 1 => 0xcccccccc00000000000000000000000000000000000000000000000000000000cccc888800000000000000000000000000000000000000000000000000000000cccc000000000000000000000000000000000000000000000000000000000000cc00cc0000000000000000000000000000000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000000aaaa000000000000000000000000000000000000000000000000000000000000a0a0a0a00000000000000000000000000000000000000000000000000000000088888888
  | 0, 2 => 0xff00f00000000000000000000000000000000000000000000000000000000000ff00cc0000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000fafafafa00000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000eeeeeeee
  | 0, 3 => 0xffff888800000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000fff0fff000000000000000000000000000000000000000000000000000000000fff0000000000000000000000000000000000000000000000000000000000000ffc0ffc000000000000000000000000000000000000000000000000000000000ff88ff8800000000000000000000000000000000000000000000000000000000ff00ffff00000000000000000000000000000000000000000000000000000000ff00ff00
  | 0, 4 => 0xffffff0000000000000000000000000000000000000000000000000000000000fffff0f000000000000000000000000000000000000000000000000000000000ffffcccc00000000000000000000000000000000000000000000000000000000ffffaaaa
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x1548f2d1e6133cb501c44f2d005d23cb401548f1d0048f2c24
  | 5, 0, 0 => 0x7984d0215e6131c6579a4cf2d5e5933cb57983cb155e6133c7578f2c405594cf2c0579850f255e5d33cb57933c7055e6533cb579b4cf2d5e5523cb561548f2d5e54f2c45
  | 5, 0, 1 => 0x7184cf2d626123cb58584cd2d584cf2c0501548f2d1e60f2c357d84cf2d5e6133cb56123cb015e61338b560f2c4015e6122c6579d44f2d5e6123cb56133c7015e60f2c45
  | 6, 0, 0 => 0x184cf2c057984d03cb601e6133cb57984cf2c867984cf2c668de6133cb601e6123cb57984cf2ca601e60f2c4501e6133c7581e6133cb67984d13cb67985133cb67984cf2c067984cf30b67984d23cb6
  | 6, 0, 1 => 0x79d6133cb67984cf2c16
  | 7, 0, 0 => 0x1e6133cb5
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
  | 0, 0 => 0x7fc67320000000000000000000000000000000000000000000000000000000007e39ccd00000000000000000000000000000000000000000000000000000000071fffff00000000000000000000000000000000000000000000000000000000071f83c300000000000000000000000000000000000000000000000000000000071f80000000000000000000000000000000000000000000000000000000000000ffffff0000000000000000000000000000000000000000000000000000000000ff803f0000000000000000000000000000000000000000000000000000000000007fff
  | 0, 1 => 0x1c633200000000000000000000000000000000000000000000000000000000001c000000000000000000000000000000000000000000000000000000000000001c0000000000000000000000000000000000000000000000000000000000000000630000000000000000000000000000000000000000000000000000000000000398cd0000000000000000000000000000000000000000000000000000000000038000000000000000000000000000000000000000000000000000000000000000180c0000000000000000000000000000000000000000000000000000000000000000
  | 0, 2 => 0x7007c00000000000000000000000000000000000000000000000000000000000700630000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000000e3fcfd0000000000000000000000000000000000000000000000000000000000e07c3c0000000000000000000000000000000000000000000000000000000000e000000000000000000000000000000000000000000000000000000000000000007c0000000000000000000000000000000000000000000000000000000000001ffbff
  | 0, 3 => 0x7ff80000000000000000000000000000000000000000000000000000000000007ff80000000000000000000000000000000000000000000000000000000000007e07ffc0000000000000000000000000000000000000000000000000000000007e000000000000000000000000000000000000000000000000000000000000007007ff00000000000000000000000000000000000000000000000000000000007007fc00000000000000000000000000000000000000000000000000000000007007fff0000000000000000000000000000000000000000000000000000000007007fc0
  | 0, 4 => 0x7ffffc00000000000000000000000000000000000000000000000000000000007fffc3c0000000000000000000000000000000000000000000000000000000007ffe3320000000000000000000000000000000000000000000000000000000007ff98cd
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x6d846200000000000000000000000000000000000000000000000000000000005a31488000000000000000000000000000000000000000000000000000000000316abd700000000000000000000000000000000000000000000000000000000031683c3000000000000000000000000000000000000000000000000000000000316828000000000000000000000000000000000000000000000000000000000006da97f00000000000000000000000000000000000000000000000000000000006d803f0000000000000000000000000000000000000000000000000000000000002957
  | 0, 1 => 0x25ceb7700000000000000000000000000000000000000000000000000000000025ceb7700000000000000000000000000000000000000000000000000000000025cc2200000000000000000000000000000000000000000000000000000000002106b40000000000000000000000000000000000000000000000000000000000127b9df0000000000000000000000000000000000000000000000000000000001279088000000000000000000000000000000000000000000000000000000000021381c000000000000000000000000000000000000000000000000000000000004a957
  | 0, 2 => 0x7927e800000000000000000000000000000000000000000000000000000000007927fc000000000000000000000000000000000000000000000000000000000079256800000000000000000000000000000000000000000000000000000000005effdff0000000000000000000000000000000000000000000000000000000004e97c3c0000000000000000000000000000000000000000000000000000000004e954280000000000000000000000000000000000000000000000000000000004807c0000000000000000000000000000000000000000000000000000000000037ffbff
  | 0, 3 => 0x7ffffff0000000000000000000000000000000000000000000000000000000007ffd6a80000000000000000000000000000000000000000000000000000000007fb7ffc0000000000000000000000000000000000000000000000000000000007fb56a80000000000000000000000000000000000000000000000000000000007da7ff4000000000000000000000000000000000000000000000000000000000796ffd70000000000000000000000000000000000000000000000000000000007927fd70000000000000000000000000000000000000000000000000000000007927fc0
  | 0, 4 => 0x7ffffe80000000000000000000000000000000000000000000000000000000007fffebc0000000000000000000000000000000000000000000000000000000007ffffff0000000000000000000000000000000000000000000000000000000007ffffff
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

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
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

namespace S_47_16
def pairsG : List (Nat × Nat) := [(17, 19), (17, 21), (17, 25), (17, 49), (18, 19), (18, 22), (18, 26), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [17, 17, 17, 17, 18, 18, 18, 20, 20, 20, 24, 24, 24, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [19, 21, 25, 49, 19, 22, 26, 21, 22, 28, 25, 26, 28, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x7fffff
def pool6G : List Nat := [19864560735507, 22063550436117, 26474465269020, 26465875333914, 22067828560662, 26461597209369, 55062422100243, 19865065959699, 22068483332627, 55061885098262, 55078997595418, 57252318550550, 57277987296028, 55061885229590, 61650834822682, 55079534859802, 19864628041235, 19864628107539, 61659391071772, 55062422100502]
def xsM : List Nat := roots_47_16.map (· &&& dom_47_16)
def goalM : Nat := goal_47_16 &&& dom_47_16
def NN : Nat → Nat
  | 3 => 1
  | 4 => 13
  | 5 => 44
  | 6 => 17
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x552483e
  | 4, 0 => 0x8605132e7b57f3a873240d52665cd1f1623820ac335d3dad14c61d48109e81a30d17dbc007b17cb407a9afcc01b9a7580075b94b
  | 5, 0 => 0xeddd1af5d7c737ebc55fbe6fb5819b607f2c0bd67ecb9dca7de2939e7894b1f3783443e773b692c173240d526ae3500052e0b39a5280458e51fd9d194ff0bc2c4c0e0adf40af8d083ccad0903c2876f433320f703152eda52615a1f4251230a620e49f441eae5e501d226cf71bb081c51b543d561a2873311a24c5f91391194e1077f6f70bda6bc40bce8c130b73653d0b51185a09e8339c07261408066cda4905dfb75b01e0734e01b9a75801141bf7
  | 6, 0 => 0xef4cf998eddd1af5d7c737ebc998fb3f98f9af0473abf9b973240d524bce347c3c1f9360301879e728531e57204c65761a287331195e30fe18dba2f41391194e05dfb75b
  | 7, 0 => 0x73240d52
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x333300000000000000000000000000000000000000000000000000000000000011110000333300000000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000aaaa00000000000000000000000000000000000000000000000000000000000000ff0000
  | 0, 1 => 0xaaaa0000aaaa0000000000000000000000000000000000000000000000000000aaaa0000aa000000000000000000000000000000000000000000000000000000aaaa000000000000000000000000000000000000000000000000000000000000aa000000aa000000000000000000000000000000000000000000000000000000888800008888000000000000000000000000000000000000000000000000000055550000ffff000000000000000000000000000000000000000000000000000055550000555500000000000000000000000000000000000000000000000000003333000033330000
  | 0, 2 => 0xf0f00000f0f00000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000eeee0000eeee0000000000000000000000000000000000000000000000000000eeee0000eecc0000000000000000000000000000000000000000000000000000eeee0000cccc0000000000000000000000000000000000000000000000000000eaea0000eaea0000000000000000000000000000000000000000000000000000cccc0000cccc0000000000000000000000000000000000000000000000000000c0c00000c0c00000
  | 0, 3 => 0xff00000000000000000000000000000000000000000000000000000000000000fcfc0000fcfc0000000000000000000000000000000000000000000000000000fafa0000fafa0000000000000000000000000000000000000000000000000000fafa0000f8f80000000000000000000000000000000000000000000000000000fafa0000f0f00000000000000000000000000000000000000000000000000000faf00000faf00000000000000000000000000000000000000000000000000000faaa0000faaa0000000000000000000000000000000000000000000000000000f8f80000f8f80000
  | 0, 4 => 0xfff00000fff00000000000000000000000000000000000000000000000000000ffcc0000ffcc0000000000000000000000000000000000000000000000000000ffc00000ffc00000000000000000000000000000000000000000000000000000ffaa0000ffaa0000000000000000000000000000000000000000000000000000ffaa0000ff000000000000000000000000000000000000000000000000000000ffaa000000000000000000000000000000000000000000000000000000000000ff000000ffff0000000000000000000000000000000000000000000000000000ff000000ff000000
  | 0, 5 => 0xffff0000fcfc0000000000000000000000000000000000000000000000000000ffff0000f0f00000000000000000000000000000000000000000000000000000ffff0000f0000000000000000000000000000000000000000000000000000000ffff0000cccc0000000000000000000000000000000000000000000000000000ffff0000aaaa0000000000000000000000000000000000000000000000000000ffff0000aa000000000000000000000000000000000000000000000000000000ffff000055550000000000000000000000000000000000000000000000000000ffff000000000000
  | 0, 6 => 0xffff0000ff000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x207153
  | 4, 0, 0 => 0x8173c640245d1392881744f50206d12500a2061540289d94500a2578f40205d43d008d74cf40235cf21289e678f50206d13d2881e7555
  | 5, 0, 0 => 0x205d13ce502e81744f502981744950205d13cd50308173c850205d13ca502881754b501744f10350205d13c0502f81744f502d81744f5a2681754f60285d13c4502881e40f500081b44f40288174915
  | 5, 0, 1 => 0x2044f14250205d124250205d344f50205d13c7502e81644f50205d13c15028811245503091744f502895744f502181744f5a2799744f6c2079744f60288174cf502881a44f502a81744f5a2481d5d16
  | 5, 0, 2 => 0x205d13c25028817449502b81744d502981744f502e8113c5502e81744950206d13cd502044f34550205d1349502281744f502881744f502844f1445
  | 6, 0, 0 => 0x205d13c250288174495a205d13c26ae881744f6a2075744f602881744f5a205d13c96a205d13cc6a2079744f6a205d13c86a205d140f602e81744f5a207d744f6b2881744f60205d13cd50285d13c45
  | 6, 0, 1 => 0xa205d13cd6
  | 7, 0, 0 => 0x2881744f5
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
  | 0, 0 => 0x7e200000000000000000000000000000000000000000000000000000000000007e3f8f000000000000000000000000000000000000000000000000000000000071fc7f00000000000000000000000000000000000000000000000000000000000fe3ff00000000000000000000000000000000000000000000000000000000000fe0000000000000000000000000000000000000000000000000000000000000001fff000000000000000000000000000000000000000000000000000000000000000f00000000000000000000000000000000000000000000000000000000000003ff
  | 0, 1 => 0xf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007fffff00000000000000000000000000000000000000000000000000000000007ffff000000000000000000000000000000000000000000000000000000000007e3f8f
  | 0, 2 => 0xe038000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000000001c07f000000000000000000000000000000000000000000000000000000000001c070000000000000000000000000000000000000000000000000000000000001c070000000000000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000001c0700000000000000000000000000000000000000000000000000000000000000000
  | 0, 3 => 0x70000000000000000000000000000000000000000000000000000000000000000fc3f000000000000000000000000000000000000000000000000000000000000e038f00000000000000000000000000000000000000000000000000000000000e038000000000000000000000000000000000000000000000000000000000000e038000000000000000000000000000000000000000000000000000000000000e0380000000000000000000000000000000000000000000000000000000000000000f00000000000000000000000000000000000000000000000000000000000e0380
  | 0, 4 => 0x7e1f80000000000000000000000000000000000000000000000000000000000071dc700000000000000000000000000000000000000000000000000000000000701c000000000000000000000000000000000000000000000000000000000000701c0f0000000000000000000000000000000000000000000000000000000000701c0000000000000000000000000000000000000000000000000000000000007000000000000000000000000000000000000000000000000000000000000000701fff0000000000000000000000000000000000000000000000000000000000701c00
  | 0, 5 => 0x7fe3f000000000000000000000000000000000000000000000000000000000007fe38000000000000000000000000000000000000000000000000000000000007fe00000000000000000000000000000000000000000000000000000000000007fe07000000000000000000000000000000000000000000000000000000000007fe00f00000000000000000000000000000000000000000000000000000000007fe00000000000000000000000000000000000000000000000000000000000007ffff000000000000000000000000000000000000000000000000000000000007fe000
  | 0, 6 => 0x7ffc00
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x5a200800000000000000000000000000000000000000000000000000000000004816860000000000000000000000000000000000000000000000000000000000316c5d000000000000000000000000000000000000000000000000000000000006e1bb000000000000000000000000000000000000000000000000000000000006e0080000000000000000000000000000000000000000000000000000000000001ff7000000000000000000000000000000000000000000000000000000000000049700000000000000000000000000000000000000000000000000000000000001b3
  | 0, 1 => 0x12649f000000000000000000000000000000000000000000000000000000000012640c00000000000000000000000000000000000000000000000000000000001260080000000000000000000000000000000000000000000000000000000000100404000000000000000000000000000000000000000000000000000000000000401100000000000000000000000000000000000000000000000000000000006d9ff700000000000000000000000000000000000000000000000000000000006d9b6000000000000000000000000000000000000000000000000000000000005a368e
  | 0, 2 => 0x4e93a200000000000000000000000000000000000000000000000000000000004e8000000000000000000000000000000000000000000000000000000000000037edff000000000000000000000000000000000000000000000000000000000037ed7d000000000000000000000000000000000000000000000000000000000037e979000000000000000000000000000000000000000000000000000000000016e5bf000000000000000000000000000000000000000000000000000000000025c9710000000000000000000000000000000000000000000000000000000000048120
  | 0, 3 => 0x79000000000000000000000000000000000000000000000000000000000000006fdbf300000000000000000000000000000000000000000000000000000000005ef7bf00000000000000000000000000000000000000000000000000000000005ef3bb00000000000000000000000000000000000000000000000000000000005ef3aa00000000000000000000000000000000000000000000000000000000005e97a600000000000000000000000000000000000000000000000000000000005a769f00000000000000000000000000000000000000000000000000000000004ed3b3
  | 0, 4 => 0x7f9fe600000000000000000000000000000000000000000000000000000000007ddf7500000000000000000000000000000000000000000000000000000000007d9f6400000000000000000000000000000000000000000000000000000000007b7edf00000000000000000000000000000000000000000000000000000000007b7e4c00000000000000000000000000000000000000000000000000000000007b60080000000000000000000000000000000000000000000000000000000000791ff70000000000000000000000000000000000000000000000000000000000791e44
  | 0, 5 => 0x7ffbfb00000000000000000000000000000000000000000000000000000000007ff3aa00000000000000000000000000000000000000000000000000000000007ff20800000000000000000000000000000000000000000000000000000000007fe97900000000000000000000000000000000000000000000000000000000007fe49f00000000000000000000000000000000000000000000000000000000007fe40c00000000000000000000000000000000000000000000000000000000007ffb6800000000000000000000000000000000000000000000000000000000007fe008
  | 0, 6 => 0x7ffe4c
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_47_16 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_47_16 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
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
private theorem z5_32 : ∀ i, 32 ≤ i → i < 44 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 32 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 44 → Z 5 i = true := (range_split (range_split z5_0 z5_16) z5_32)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 16 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_16 : ∀ i, 16 ≤ i → i < 17 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 16 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 17 → Z 6 i = true := (range_split z6_0 z6_16)
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
  scr dom_47_16 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_47_16 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_47_16 roots_47_16 goal_47_16 8 := by
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

theorem low_47_16 : Lower dom_47_16 roots_47_16 goal_47_16 8 := S_47_16.noCircuit

namespace S_15_16
def pairsG : List (Nat × Nat) := [(17, 19), (17, 21), (17, 25), (18, 19), (18, 22), (18, 26), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28)]
def r1sG : List Nat := [17, 17, 17, 18, 18, 18, 20, 20, 20, 24, 24, 24]
def r2sG : List Nat := [19, 21, 25, 19, 22, 26, 21, 22, 28, 25, 26, 28]
def mpG : Nat := 0xfff
def pool6G : List Nat := [19864560735507, 26474465269020, 26465875333914, 22067828560662, 26461597209369, 22063550436117, 26461630894873, 22063651492629, 19864628107539]
def xsM : List Nat := roots_15_16.map (· &&& dom_15_16)
def goalM : Nat := goal_15_16 &&& dom_15_16
def NN : Nat → Nat
  | 3 => 3
  | 4 => 6
  | 5 => 5
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x5f52b8b3202b72e10619aa1d
  | 4, 0 => 0x6a2e6bc2202b72e11f58d4260d8d20b506dd279c05c93d22
  | 5, 0 => 0x6a2e6bc2202b72e119ec07501375cbc2111eaaac
  | 6, 0 => 0x202b72e1
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xeeee000000000000000000000000000000000000000000000000000000000000eaea000000000000000000000000000000000000000000000000000000000000cccc000000000000000000000000000000000000000000000000000000000000c0c0000000000000000000000000000000000000000000000000000000000000aaaa0000000000000000000000000000000000000000000000000000000000008888000000000000000000000000000000000000000000000000000000000000555500000000000000000000000000000000000000000000000000000000000033330000
  | 0, 1 => 0xffcc000000000000000000000000000000000000000000000000000000000000ffc0000000000000000000000000000000000000000000000000000000000000ffaa000000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000fcfc000000000000000000000000000000000000000000000000000000000000fafa000000000000000000000000000000000000000000000000000000000000f0f00000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xec874b85340da33
  | 4, 0, 0 => 0xb85140b85340b8104b987550b86540b8724
  | 5, 0, 0 => 0xb85140b8534b85435b85315cb8535
  | 6, 0, 0 => 0xb8534
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
  | 0, 0 => 0x3f000000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000000380000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ff80000000000000000000000000000000000000000000000000000000000000fc7
  | 0, 1 => 0xe380000000000000000000000000000000000000000000000000000000000000e000000000000000000000000000000000000000000000000000000000000000e070000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000000001f800000000000000000000000000000000000000000000000000000000000001c700000000000000000000000000000000000000000000000000000000000001c0
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x6ff00000000000000000000000000000000000000000000000000000000000002df00000000000000000000000000000000000000000000000000000000000004b90000000000000000000000000000000000000000000000000000000000000090000000000000000000000000000000000000000000000000000000000000024f00000000000000000000000000000000000000000000000000000000000000090000000000000000000000000000000000000000000000000000000000000db00000000000000000000000000000000000000000000000000000000000000b46
  | 0, 1 => 0xfbd0000000000000000000000000000000000000000000000000000000000000fb40000000000000000000000000000000000000000000000000000000000000f6f0000000000000000000000000000000000000000000000000000000000000f240000000000000000000000000000000000000000000000000000000000000dfb0000000000000000000000000000000000000000000000000000000000000bdf00000000000000000000000000000000000000000000000000000000000009d2
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 15 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 15 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 15 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 15 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_15_16 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_15_16 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
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
  scr dom_15_16 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_15_16 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_15_16 roots_15_16 goal_15_16 7 := by
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

theorem low_15_16 : Lower dom_15_16 roots_15_16 goal_15_16 7 := S_15_16.noCircuit

namespace S_61
def pairsG : List (Nat × Nat) := [(1, 33), (5, 21), (5, 37), (9, 25), (9, 41), (12, 28), (13, 29), (13, 45), (17, 21), (17, 25), (17, 49), (20, 21), (20, 28), (24, 25), (24, 28), (32, 33), (36, 37), (40, 41), (44, 45), (44, 60), (48, 49), (52, 53), (52, 60), (56, 57), (56, 60)]
def r1sG : List Nat := [1, 5, 5, 9, 9, 12, 13, 13, 17, 17, 17, 20, 20, 24, 24, 32, 36, 40, 44, 44, 48, 52, 52, 56, 56]
def r2sG : List Nat := [33, 21, 37, 25, 41, 28, 29, 45, 21, 25, 49, 21, 28, 25, 28, 33, 37, 41, 45, 60, 49, 53, 60, 57, 60]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [22063651494165, 22012447759381, 26427674139673, 26474465269020, 26392911418649, 26461630895385]
def xsM : List Nat := roots_61.map (· &&& dom_61)
def goalM : Nat := goal_61 &&& dom_61
def NN : Nat → Nat
  | 4 => 2
  | 5 => 7
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x995298d1571cd9a2
  | 5, 0 => 0xd268f7e7ce2fdbfd9c1be658995298d13e3ca5392ac4f6e50a45683c
  | 6, 0 => 0x995298d1
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x30303030303030300000000000000000000000000000000000000000000000003030000030300000000000000000000000000000000000000000000000000000222222222222222200000000000000000000000000000000000000000000000022222222000000000000000000000000000000000000000000000000000000001111111111111111000000000000000000000000000000000000000000000000030303030303030300000000000000000000000000000000000000000000000000003333000033330000000000000000000000000000000000000000000000000000000033333333
  | 0, 1 => 0x3333333300000000000000000000000000000000000000000000000000000000333300003333000000000000000000000000000000000000000000000000000033003300330033000000000000000000000000000000000000000000000000003300000033000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xba97550b8654
  | 5, 0, 0 => 0xba9735a97545a97505ba9755ba9525b97515ba8755
  | 6, 0, 0 => 0xba9755
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
  | 0, 0 => 0x6d18e6000000000000000000000000000000000000000000000000000000000060180000000000000000000000000000000000000000000000000000000000000007df00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001fff820000000000000000000000000000000000000000000000000000000000192e71900000000000000000000000000000000000000000000000000000000000f80ff0000000000000000000000000000000000000000000000000000000000007fff
  | 0, 1 => 0x1ff80000000000000000000000000000000000000000000000000000000000001f07f0000000000000000000000000000000000000000000000000000000000018e60f80000000000000000000000000000000000000000000000000000000001806000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x16d59e600000000000000000000000000000000000000000000000000000000016859620000000000000000000000000000000000000000000000000000000000b7afdf0000000000000000000000000000000000000000000000000000000000b784950000000000000000000000000000000000000000000000000000000001485020000000000000000000000000000000000000000000000000000000000092a61900000000000000000000000000000000000000000000000000000000000780950000000000000000000000000000000000000000000000000000000000007b6a
  | 0, 1 => 0x1ff84950000000000000000000000000000000000000000000000000000000001f87f6a0000000000000000000000000000000000000000000000000000000001ce72f80000000000000000000000000000000000000000000000000000000001c87268
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

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
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

namespace S_62
def pairsG : List (Nat × Nat) := [(6, 22), (6, 38), (10, 26), (10, 42), (12, 28), (14, 30), (14, 46), (18, 22), (18, 26), (20, 22), (20, 28), (24, 26), (24, 28), (34, 38), (34, 42), (36, 38), (40, 42), (44, 46), (44, 60), (50, 54), (50, 58), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [6, 6, 10, 10, 12, 14, 14, 18, 18, 20, 20, 24, 24, 34, 34, 36, 40, 44, 44, 50, 50, 52, 52, 56, 56]
def r2sG : List Nat := [22, 38, 26, 42, 28, 30, 46, 22, 26, 22, 28, 26, 28, 38, 42, 38, 42, 46, 60, 54, 58, 54, 60, 58, 60]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [22067946461718, 22016743054358, 26431969696794, 26474482112028, 26465925862938]
def xsM : List Nat := roots_62.map (· &&& dom_62)
def goalM : Nat := goal_62 &&& dom_62
def NN : Nat → Nat
  | 4 => 3
  | 5 => 7
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xa91103de7be3913609720071
  | 5, 0 => 0xe324ca91deee3556c894e17ca91103de45028db13a415d320ebf8666
  | 6, 0 => 0xa91103de
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x50505050505050500000000000000000000000000000000000000000000000004444444444444444000000000000000000000000000000000000000000000000444444444444000000000000000000000000000000000000000000000000000044444444000000000000000000000000000000000000000000000000000000001111111111111111000000000000000000000000000000000000000000000000050505050505050500000000000000000000000000000000000000000000000000005555000055550000000000000000000000000000000000000000000000000000000055555555
  | 0, 1 => 0x55555555555500000000000000000000000000000000000000000000000000005555555500000000000000000000000000000000000000000000000000000000555544445555000000000000000000000000000000000000000000000000000055550000555500000000000000000000000000000000000000000000000000005500550055005500
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xb987650987540a8764
  | 5, 0, 0 => 0x987605b98735987645b98765b98625c98765b87615
  | 6, 0, 0 => 0xb98765
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
  | 0, 0 => 0x66867300000000000000000000000000000000000000000000000000000000001861ef000000000000000000000000000000000000000000000000000000000018618000000000000000000000000000000000000000000000000000000000001860000000000000000000000000000000000000000000000000000000000001e79e10000000000000000000000000000000000000000000000000000000000199798c000000000000000000000000000000000000000000000000000000000007e07f0000000000000000000000000000000000000000000000000000000000001fff
  | 0, 1 => 0x1ffff800000000000000000000000000000000000000000000000000000000001ffe0000000000000000000000000000000000000000000000000000000000001f87f800000000000000000000000000000000000000000000000000000000001f81f80000000000000000000000000000000000000000000000000000000000187187c
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x16eb6f30000000000000000000000000000000000000000000000000000000000bbebef0000000000000000000000000000000000000000000000000000000000bbebef0000000000000000000000000000000000000000000000000000000000bbe04a0000000000000000000000000000000000000000000000000000000001441410000000000000000000000000000000000000000000000000000000000091490c000000000000000000000000000000000000000000000000000000000003e04a0000000000000000000000000000000000000000000000000000000000001fb5
  | 0, 1 => 0x1ffffff0000000000000000000000000000000000000000000000000000000001ffe04a0000000000000000000000000000000000000000000000000000000001ffffff0000000000000000000000000000000000000000000000000000000001fc1fb50000000000000000000000000000000000000000000000000000000001d75d7c
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_62 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_62 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
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

namespace S_55
def pairsG : List (Nat × Nat) := [(1, 3), (1, 33), (2, 3), (5, 7), (5, 21), (5, 37), (6, 7), (6, 22), (6, 38), (17, 19), (17, 21), (17, 49), (18, 19), (18, 22), (20, 21), (20, 22), (32, 33), (34, 35), (34, 38), (36, 37), (36, 38), (48, 49), (50, 51), (50, 54), (52, 53), (52, 54)]
def r1sG : List Nat := [1, 1, 2, 5, 5, 5, 6, 6, 6, 17, 17, 17, 18, 18, 20, 20, 32, 34, 34, 36, 36, 48, 50, 50, 52, 52]
def r2sG : List Nat := [3, 33, 3, 7, 21, 37, 7, 22, 38, 19, 21, 49, 19, 22, 21, 22, 33, 35, 38, 37, 38, 49, 51, 54, 53, 54]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [2203655214339, 37387793466145, 22063819923733, 6601701725443, 19795841258755, 37388296790275]
def xsM : List Nat := roots_55.map (· &&& dom_55)
def goalM : Nat := goal_55 &&& dom_55
def NN : Nat → Nat
  | 4 => 3
  | 5 => 8
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x8050ef7847baa0701459cffc
  | 5, 0 => 0xfd05eeb0ae0dadfba4f836c38a64578173ea86206b85db7447baa07045f82275
  | 6, 0 => 0x47baa070
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0000000f0000000000000000000000000000000000000000000000000000000cc00cc00cc00cc00000000000000000000000000000000000000000000000000aa00aa00aa00aa00000000000000000000000000000000000000000000000000550055005500550000000000000000000000000000000000000000000000000033003300330033000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000000ff000000ff0000000000000000000000000000000000000000000000000000000000ff00ff
  | 0, 1 => 0xff00ff00ff000000000000000000000000000000000000000000000000000000ff00ff00f0000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000f000f000f00000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xc9654ba96550b8654
  | 5, 0, 0 => 0xba6525db9655ba9645ba9535a96505b96515ba9655b97655
  | 6, 0, 0 => 0xba9655
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
  | 0, 0 => 0x300c0000000000000000000000000000000000000000000000000000000000000c631c40000000000000000000000000000000000000000000000000000000000000e3b0000000000000000000000000000000000000000000000000000000003fff1c4000000000000000000000000000000000000000000000000000000000339ce3b0000000000000000000000000000000000000000000000000000000000e73e0700000000000000000000000000000000000000000000000000000000001f01ff000000000000000000000000000000000000000000000000000000000000ffff
  | 0, 1 => 0x3fffe000000000000000000000000000000000000000000000000000000000003ffc0000000000000000000000000000000000000000000000000000000000003ff00000000000000000000000000000000000000000000000000000000000003e0fe00000000000000000000000000000000000000000000000000000000000318c1f8000000000000000000000000000000000000000000000000000000000318c000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x380e4900000000000000000000000000000000000000000000000000000000002d6b3cd00000000000000000000000000000000000000000000000000000000016b5e7f000000000000000000000000000000000000000000000000000000000294a1800000000000000000000000000000000000000000000000000000000001294c320000000000000000000000000000000000000000000000000000000000631a0700000000000000000000000000000000000000000000000000000000001f016f000000000000000000000000000000000000000000000000000000000000f6dd
  | 0, 1 => 0x3ffffb20000000000000000000000000000000000000000000000000000000003ffedb20000000000000000000000000000000000000000000000000000000003ff09220000000000000000000000000000000000000000000000000000000003e0fe9000000000000000000000000000000000000000000000000000000000039ce5f800000000000000000000000000000000000000000000000000000000039ce5b0
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
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 8 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 8 → Z 5 i = true := z5_0
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

namespace S_55_8
def pairsG : List (Nat × Nat) := [(9, 11), (9, 25), (9, 41), (10, 11), (10, 26), (10, 42), (12, 28), (13, 15), (13, 29), (13, 45), (14, 15), (14, 30), (14, 46), (24, 25), (24, 26), (24, 28), (40, 41), (40, 42), (44, 45), (44, 46), (44, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [9, 9, 9, 10, 10, 10, 12, 13, 13, 13, 14, 14, 14, 24, 24, 24, 40, 40, 44, 44, 44, 56, 56, 56]
def r2sG : List Nat := [11, 25, 41, 11, 26, 42, 28, 15, 29, 45, 15, 30, 46, 25, 26, 28, 41, 42, 45, 46, 60, 57, 58, 60]
def mpG : Nat := 0xffffff
def pool6G : List Nat := [15432558455051, 14337341794571, 11034175346955, 26427674663961, 44023568468778, 61612046752793, 44019290344233]
def xsM : List Nat := roots_55_8.map (· &&& dom_55_8)
def goalM : Nat := goal_55_8 &&& dom_55_8
def NN : Nat → Nat
  | 3 => 1
  | 4 => 3
  | 5 => 9
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x1add1e32
  | 4, 0 => 0xc22d231e9b57b19f2ae7e23a
  | 5, 0 => 0xfa2330d0c9b32fd6c22d231eab6275a79192a4a67a5e75656d93d5d33356818827f195c0
  | 6, 0 => 0xc22d231e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0000000f0000000000000000000000000000000000000000000000000000000ee00ee00ee00ee00000000000000000000000000000000000000000000000000cc00cc00cc00cc00000000000000000000000000000000000000000000000000aa00aa00aa00aa0000000000000000000000000000000000000000000000000055005500550055000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000000ff000000ff0000000000000000000000000000000000000000000000000000000000ff00ff00
  | 0, 1 => 0xff00ff00ff000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000fc00fc00fc00fc00000000000000000000000000000000000000000000000000fa00aa00fa00aa00000000000000000000000000000000000000000000000000f000f000f000f000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xd953
  | 4, 0, 0 => 0xcb85450d75440cb954
  | 5, 0, 0 => 0xdb85450cb54250cb85450cb75450c854150b85405cb865460cba5450cb8535
  | 6, 0, 0 => 0xcb8545
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 16
  | 4 => 24
  | 5 => 28
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
  | 0, 0 => 0x1fbf0000000000000000000000000000000000000000000000000000000000001c3800000000000000000000000000000000000000000000000000000000000003870000000000000000000000000000000000000000000000000000000000fffc780000000000000000000000000000000000000000000000000000000000e3e03f00000000000000000000000000000000000000000000000000000000001f1fff000000000000000000000000000000000000000000000000000000000000ffff
  | 0, 1 => 0xffe0000000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000e0e00000000000000000000000000000000000000000000000000000000000001c1ff8000000000000000000000000000000000000000000000000000000000000038700000000000000000000000000000000000000000000000000000000001c1fc0
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x90894000000000000000000000000000000000000000000000000000000000006f7fbf00000000000000000000000000000000000000000000000000000000004a5cb9000000000000000000000000000000000000000000000000000000000025278f0000000000000000000000000000000000000000000000000000000000dad870000000000000000000000000000000000000000000000000000000000063603f00000000000000000000000000000000000000000000000000000000000f16ad000000000000000000000000000000000000000000000000000000000000eddb
  | 0, 1 => 0xfffb760000000000000000000000000000000000000000000000000000000000ff12240000000000000000000000000000000000000000000000000000000000f0e9520000000000000000000000000000000000000000000000000000000000dedff90000000000000000000000000000000000000000000000000000000000b5afcf00000000000000000000000000000000000000000000000000000000009c9fc0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_55_8 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_55_8 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0x2222222222222222222222222222222222222222222222222222222222222222, 1)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_55_8 == dom_55_8) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_55_8 goalM u ys) : RunD dom_55_8 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_55_8 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_55_8 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_55_8 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_55_8 roots_55_8 goal_55_8 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_55_8 goal_55_8 := by
    have h0 : isConstB dom_55_8 goal_55_8 = false := by decide +kernel
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

end S_55_8

theorem low_55_8 : Lower dom_55_8 roots_55_8 goal_55_8 7 := S_55_8.noCircuit

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

namespace S_47
def pairsG : List (Nat × Nat) := [(1, 3), (1, 33), (2, 3), (5, 7), (5, 37), (6, 7), (6, 38), (9, 11), (9, 41), (10, 11), (10, 42), (13, 15), (13, 45), (14, 15), (14, 46), (32, 33), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (40, 41), (40, 42), (44, 45), (44, 46)]
def r1sG : List Nat := [1, 1, 2, 5, 5, 6, 6, 9, 9, 10, 10, 13, 13, 14, 14, 32, 34, 34, 34, 36, 36, 40, 40, 44, 44]
def r2sG : List Nat := [3, 33, 3, 7, 37, 7, 38, 11, 41, 11, 42, 15, 45, 15, 46, 33, 35, 38, 42, 37, 38, 41, 42, 45, 46]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [2203924701443, 6601971212547, 11000085094659, 35188770210593]
def xsM : List Nat := roots_47.map (· &&& dom_47)
def goalM : Nat := goal_47 &&& dom_47
def NN : Nat → Nat
  | 4 => 2
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xf65ed8d10f1fce07
  | 5, 0 => 0xf1fce07
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffff000000000000000000000000000000000000000000000000000000000000fff00000fff00000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000cccc0000cccc0000000000000000000000000000000000000000000000000000aaaa0000aaaa
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x584256885
  | 5, 0, 0 => 0x56885
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
  | 0, 0 => 0x1ff80000000000000000000000000000000000000000000000000000000000001f87ff80000000000000000000000000000000000000000000000000000000001e07f8000000000000000000000000000000000000000000000000000000000019878780000000000000000000000000000000000000000000000000000000000076664000000000000000000000000000000000000000000000000000000000000199b
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1ffd5520000000000000000000000000000000000000000000000000000000001fe7ff80000000000000000000000000000000000000000000000000000000001e47f8000000000000000000000000000000000000000000000000000000000019a78780000000000000000000000000000000000000000000000000000000001576eed0000000000000000000000000000000000000000000000000000000000a9bbbf
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_47 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_47 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
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
  scr dom_47 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_47 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_47 roots_47 goal_47 6 := by
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

theorem low_47 : Lower dom_47 roots_47 goal_47 6 := S_47.noCircuit

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

namespace S_23_8
def pairsG : List (Nat × Nat) := [(9, 11), (9, 25), (10, 11), (10, 26), (12, 28), (13, 15), (13, 29), (14, 15), (14, 30), (24, 25), (24, 26), (24, 28)]
def r1sG : List Nat := [9, 9, 10, 10, 12, 13, 13, 14, 14, 24, 24, 24]
def r2sG : List Nat := [11, 25, 11, 26, 28, 15, 29, 15, 30, 25, 26, 28]
def mpG : Nat := 0xfff
def pool6G : List Nat := [26431381375770, 26427103251225]
def xsM : List Nat := roots_23_8.map (· &&& dom_23_8)
def goalM : Nat := goal_23_8 &&& dom_23_8
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x7711a25
  | 4, 0 => 0x7711a25
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000cc00cc0000000000000000000000000000000000000000000000000000000000aa00aa00
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
  | 0, 0 => 0xe0000000000000000000000000000000000000000000000000000000000000001f0000000000000000000000000000000000000000000000000000000000000018c0000000000000000000000000000000000000000000000000000000000000063
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xf5a00000000000000000000000000000000000000000000000000000000000009f000000000000000000000000000000000000000000000000000000000000005ad00000000000000000000000000000000000000000000000000000000000002e7
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_23_8 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_23_8 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0x2222222222222222222222222222222222222222222222222222222222222222, 1)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_23_8 == dom_23_8) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_23_8 goalM u ys) : RunD dom_23_8 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_23_8 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_23_8 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_23_8 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_23_8 roots_23_8 goal_23_8 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_23_8 goal_23_8 := by
    have h0 : isConstB dom_23_8 goal_23_8 = false := by decide +kernel
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

end S_23_8

theorem low_23_8 : Lower dom_23_8 roots_23_8 goal_23_8 5 := S_23_8.noCircuit

namespace S_39
def pairsG : List (Nat × Nat) := [(1, 3), (1, 33), (2, 3), (5, 7), (5, 37), (6, 7), (6, 38), (32, 33), (34, 35), (34, 38), (36, 37), (36, 38)]
def r1sG : List Nat := [1, 1, 2, 5, 5, 6, 6, 32, 34, 34, 36, 36]
def r2sG : List Nat := [3, 33, 3, 7, 37, 7, 38, 33, 35, 38, 37, 38]
def mpG : Nat := 0xfff
def pool6G : List Nat := [6601971212547, 35188770210593]
def xsM : List Nat := roots_39.map (· &&& dom_39)
def goalM : Nat := goal_39 &&& dom_39
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x257ee561
  | 4, 0 => 0x257ee561
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000cc000000cc000000000000000000000000000000000000000000000000000000aa000000aa
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
  | 0, 0 => 0xf800000000000000000000000000000000000000000000000000000000000000c780000000000000000000000000000000000000000000000000000000000000364000000000000000000000000000000000000000000000000000000000000001b
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfd20000000000000000000000000000000000000000000000000000000000000e780000000000000000000000000000000000000000000000000000000000000b6d00000000000000000000000000000000000000000000000000000000000005bf
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_39 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_39 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_39 == dom_39) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_39 goalM u ys) : RunD dom_39 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_39 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_39 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_39 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_39 roots_39 goal_39 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_39 goal_39 := by
    have h0 : isConstB dom_39 goal_39 = false := by decide +kernel
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

end S_39

theorem low_39 : Lower dom_39 roots_39 goal_39 5 := S_39.noCircuit

namespace S_29
def pairsG : List (Nat × Nat) := [(5, 21), (9, 25), (12, 28), (13, 29), (17, 21), (17, 25), (20, 21), (20, 28), (24, 25), (24, 28)]
def r1sG : List Nat := [5, 9, 12, 13, 17, 17, 20, 20, 24, 24]
def r2sG : List Nat := [21, 25, 28, 29, 21, 25, 21, 28, 25, 28]
def mpG : Nat := 0x3ff
def pool6G : List Nat := [22063651494165]
def xsM : List Nat := roots_29.map (· &&& dom_29)
def goalM : Nat := goal_29 &&& dom_29
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x13ac53d7
  | 4, 0 => 0x13ac53d7
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x33330000000000000000000000000000000000000000000000000000000000003300330000000000000000000000000000000000000000000000000000000000303030300000000000000000000000000000000000000000000000000000000022222222
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
  | 0, 0 => 0x3f0000000000000000000000000000000000000000000000000000000000000030e00000000000000000000000000000000000000000000000000000000000000cd000000000000000000000000000000000000000000000000000000000000003b
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3ff00000000000000000000000000000000000000000000000000000000000003ae00000000000000000000000000000000000000000000000000000000000002dd000000000000000000000000000000000000000000000000000000000000017b
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_29 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_29 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_29 == dom_29) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_29 goalM u ys) : RunD dom_29 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_29 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_29 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_29 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_29 roots_29 goal_29 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_29 goal_29 := by
    have h0 : isConstB dom_29 goal_29 = false := by decide +kernel
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

end S_29

theorem low_29 : Lower dom_29 roots_29 goal_29 5 := S_29.noCircuit

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

namespace S_23
def pairsG : List (Nat × Nat) := [(1, 3), (2, 3), (5, 7), (5, 21), (6, 7), (6, 22), (17, 19), (17, 21), (18, 19), (18, 22), (20, 21), (20, 22)]
def r1sG : List Nat := [1, 2, 5, 5, 6, 6, 17, 17, 18, 18, 20, 20]
def r2sG : List Nat := [3, 3, 7, 21, 7, 22, 19, 21, 19, 22, 21, 22]
def mpG : Nat := 0xfff
def pool6G : List Nat := [2203655214339]
def xsM : List Nat := roots_23.map (· &&& dom_23)
def goalM : Nat := goal_23 &&& dom_23
def NN : Nat → Nat
  | 3 => 2
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x678b910d503eed74
  | 4, 0 => 0x678b910d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000000cc00cc0000000000000000000000000000000000000000000000000000000000aa00aa
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x8c840883
  | 4, 0, 0 => 0x8c84
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
  | 0, 0 => 0xfc00000000000000000000000000000000000000000000000000000000000000c3c0000000000000000000000000000000000000000000000000000000000000c00000000000000000000000000000000000000000000000000000000000000033200000000000000000000000000000000000000000000000000000000000000cd
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfe80000000000000000000000000000000000000000000000000000000000000ebc0000000000000000000000000000000000000000000000000000000000000ea80000000000000000000000000000000000000000000000000000000000000b7700000000000000000000000000000000000000000000000000000000000005df
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

def isoMv_59 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem low_59 : Lower dom_59 roots_59 goal_59 7 :=
  lower_iso isoMv_59 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55

def isoMv_59_4 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem low_59_4 : Lower dom_59_4 roots_59_4 goal_59_4 7 :=
  lower_iso isoMv_59_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55_8

def isoMv_27_4 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem low_27_4 : Lower dom_27_4 roots_27_4 goal_27_4 5 :=
  lower_iso isoMv_27_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23_8

def isoMv_43 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem low_43 : Lower dom_43 roots_43 goal_43 5 :=
  lower_iso isoMv_43 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39

def isoMv_51_12 : List (Nat × Nat) := [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]
theorem low_51_12 : Lower dom_51_12 roots_51_12 goal_51_12 5 :=
  lower_iso isoMv_51_12 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_48

def isoMv_45_16 : List (Nat × Nat) := [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem low_45_16 : Lower dom_45_16 roots_45_16 goal_45_16 5 :=
  lower_iso isoMv_45_16 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23_8

def isoMv_30 : List (Nat × Nat) := [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem low_30 : Lower dom_30 roots_30 goal_30 5 :=
  lower_iso isoMv_30 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_29

namespace S_63
def pairsG : List (Nat × Nat) := [(1, 3), (1, 33), (2, 3), (5, 7), (5, 21), (5, 37), (6, 7), (6, 22), (6, 38), (9, 11), (9, 25), (9, 41), (10, 11), (10, 26), (10, 42), (12, 28), (13, 15), (13, 29), (13, 45), (14, 15), (14, 30), (14, 46), (17, 19), (17, 21), (17, 25), (17, 49), (18, 19), (18, 22), (18, 26), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28), (32, 33), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (40, 41), (40, 42), (44, 45), (44, 46), (44, 60), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 2, 5, 5, 5, 6, 6, 6, 9, 9, 9, 10, 10, 10, 12, 13, 13, 13, 14, 14, 14, 17, 17, 17, 17, 18, 18, 18, 20, 20, 20, 24, 24, 24, 32, 34, 34, 34, 36, 36, 40, 40, 44, 44, 44, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [3, 33, 3, 7, 21, 37, 7, 22, 38, 11, 25, 41, 11, 26, 42, 28, 15, 29, 45, 15, 30, 46, 19, 21, 25, 49, 19, 22, 26, 21, 22, 28, 25, 26, 28, 33, 35, 38, 42, 37, 38, 41, 42, 45, 46, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0xffffffffffffff
def pool6G : List Nat := [26474465269020, 2203655214339, 37387793466145, 37426632399146, 37409452528934, 61659123688988, 57278257047068, 9904598948099, 6601701725443, 10999815608579, 2204059175683, 61616341523482, 57201115143190, 61616341785626, 37404973335329, 37422220575521, 2203890815747, 61612046228505, 57196819848213, 61650834822682, 57252855421462, 39586816721697, 43984930603809, 61796276311324, 48434448302876, 48438726427420, 22012111886613, 19864560735491, 15398198452483, 48400155935509, 37388296790275, 22063550432021, 19795908630787, 39608207344422, 26427103249177, 22011809497877, 48383043961633, 22016087622422, 26431314002714, 26461597205273, 61646238778137]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_63 &&& dom_63
def NN : Nat → Nat
  | 5 => 7
  | 6 => 109
  | 7 => 343
  | 8 => 180
  | 9 => 23
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xb7a0f6137b30d80578541dd6468f8d1214e5fc0c0dfb5be70c6ef09d
  | 6, 0 => 0x722eeeb671acb963700b04826ecfff346bc292956b09813368e5d86667aab8ca65e2c3696235cd006118463c5e2f68925e2d8aab5bd115da5a0da17356488c3a539c8a95530ac3c94f7c60744c30865f482c6f6445870eb2451f7c084454025043fca3fa4373d88143660a1b4238b8e53f8d72f83e14d73f3c86b61d3a08dc5f36bd7d742b87ab452909654c2889f370265cf52f25dd6b70249d0b2022d854ad21ed19f0206d0bcf1e9cc39119ba301a18f3b34316408604160507ce15dac5e91587986414e6f175136f20cf133e0914119dfe100fa22a3f0f78074a0de65d2b0ce13a310b1f72c00925d4db06e4336306df8a7906165d7604773d4504077934
  | 6, 1 => 0xfff9fcc0fc40a38ff3175066ea635f01e580cb8ae276b9c4dff65054dfeec148defb0a41de95794fd9e26087d9c98b24d7ca6921d71e8632d4e034e8c9880156c7c00bf5c2756faec00ecba5bdf3a472bbeae9ffb7dce78eb561eb82b3f33d10b36bb360b2bc8ad0ab03f1a5a5d9ec86a4160171a3f5768899af20c792c480a2913815588f0b27718744285984b59d3980f736817ba3862e79e6d451767c5d427556c12f75413da6741577f374150697734bd994
  | 7, 0 => 0x204fb0ae203a91681f4cfea11f129f391ed55caf1d75a3ee1cd038361c96ea491bee157b1a888b6819f37e0719ba301a198e7f101862a4c917d64a9117c5c22e1701656116b01e54161648bc15fc5b66155ed0bb14e907ff14cc203913a8dfe013346ed1117804a41161181a0f06017a0ee2d2210ecc23a60e974d5b0e0550e70db753420d570f570cd412060c64f8630ba8521d0b7002330ae653d70aad79ad0a7677f50919997808e6fd4608b0816607ca96c50787d7a507073daf060f596e060e01a404e553f80442bd8603f8e99a030a418d02d6a72e02867f1c020b934d01eac28901e79c2301e3cad001660357014ecf6800d6e3c30031a7ea002d875e
  | 7, 1 => 0x45a7f598446729e64458f2e54408d567437c154542672086412c1b3840e5429a401a1c4f3fb101cf3f7f6a493f3bf5403e4693da3e444aad3e1ba00c3d18139e3c82fc633c21f90f3c21b4153a4fc2063829639837b0076a37a858aa3791ff6b36d69bdf36b521a23669c03b361d50e735c94199357f73883579865d350ff6a133df688433cd017f333d305e317b51d930dba2142fa88bf32f2d39052ee5d0702de6358a2dbac35e2d7f44742d70ced82d52d1502d4fca342c42325c2bbea46f2b811d732a245e7b293f76f02934275729259dd728e1d56328a4a83e2750b4f62724c80b2648e3a82566dfcd232c6add21a4509b219634db214f0d1120810030
  | 7, 2 => 0x6c2229556b9d976b6b302ff16aefcfd96a95be0b6a27cc6b69b0c44b68fa082566e4732066b2ba9b6407b8f1636b8ef760afae3b601d48af6008d5905f18482b5dd08b735d6dd96d5c97debb5b8c3f8e5b34bf745b3409c15ad883ea5a7ee54859a0445d592546695810d46d580e34785711b93d56488c3a54d5ab8054a96c095476a8055467b4c65462936b53c0149953447d0452a2b541526b84d85139dea74fbdd0064ebf453b4e2ce2974db8aa404d84259f4d2ff4d14d1a0f054cad82f14b8c97694b6231954b2d583b4b25a97b4abd1d0b4ab9f0674a9428d249c0fcf449780ea8490584c948c26bde480eeebd47b76ea347703dcb46de759445ff7132
  | 7, 3 => 0x9be41d5a9af9d2839ab4c0929a1c27f998f4208d985e9e2897a00225970d416895b93d769551aacc94a8304893886129934a18bd926ae7a99231308290f610e690c318fc8f980bea8f5f11de8e4706038e3f8c778a81f0ca89312aef888f7ea4881af38987be0786871506e9867351b2864f5914858e52b88436e17f812adf7780b2a53b80ab0b5c8069eaef7fdb49947ead80c27e704a887da51d3c7bd0c69379e5550479d342cd79c0734279b70aa978a666597836088a77abf413779c985d778509c276721d75765bdd3274cf39e47406feac739a9980730cc97a730c5ff872579db970e34a0670607efa6fb8decd6f410f6b6d04869a6c64553c6c41d501
  | 7, 4 => 0xe9f83c15e82ca1a0e6f5ef60e5dbe277e4dd38a3e2f6af66e247b55edff3a4ccdf3d5635dd6521e7dc8a5345daa10b17d97fc822d957a573d6d35949d5e44738d5a7fca5d445852fd434e645d3a84f1fd37b9b4dd26e2c13d2299bdcd1296545cfe29780cedb460fce1f1d8dcde52a59cc98d68ac97fa584c8c1bbacc73369bbc5736c6ac548d783c543b096c4d7a737c3ad2618c1eeb825c1980f89c0f590b7c0d8bcdabc545819bc1a5d6db7f92244b7f32202b7dce78eb6855c3db5bed785b49eb830b46b6d4cb03615abaf9abc18ac25a728abd7936dab79c6cba994b72fa97aa236a7dcb9bea4c7accca2d05d47a0566735a02193399f65a7529d51cc8a
  | 7, 5 => 0xfe2b8d04fe1106f7fb19fc8afaddb0c9f9aef702f8eb2a3df808cdccf4d74db7f44d45f4f44935f4f4483035f31deba9f2d35972f1e2cc0df1510a14f0f8df95eedca26fec164c1eebefca4bebdb61b4eafba6c3ead93aa9ea6cc730
  | 8, 0 => 0x499b08ca45f6b584457c5ed1433f660a4309ffd8430588364214fad1410d76963ee6de3d3d6d0b963c3d49423c21f90f3b5624293a8b9b213a476634387c22163732d33a359f67e734064f6c32ba82ac3264f1943055c0a6302ca7772f7655c82de85b922d90db782cb7e2692b81626d2a6cf07128a4a83e2705880d26beaf6f261c309d258a6ea4246554a623afce922219ec0a20292edb2014c6441d989e101d89743f1d81c57f1b61a0cd1b52f3321b1e87e219b1d448196672e119169d3316e8db1816b50ee91581f8c8141a4f1c11eb7ccf119811440e7e15130e7dd0190d4d98860cabde0a0c22507d09ee1b6f06b07a0306291d830291d00a01a603fb
  | 8, 1 => 0x97ec88bb97a4f38793f42b8d9351acbb8f7fd14d8e7679718d5eaaf98d1e3ac28a81f0ca877910e28651842c85e99b5485520fcd83c5bc5283233d807f5f0e0b7e8559377db173387bf0d3337a38d5c279e15a287892577573f60c3a72b28339727daf3d705b5d9f6f69601f6e834bca6be1bd3a6bcb63fb6ababa2c69b2eaed679d352a6733942567044c4c651506a4640159026379a67663669d9563353df4631f350061f427ee61aa33685cde0cce5aa8a6b9567ee6cd564030685342fdb7531915d1530ec13f523dc21151099cc6500139404fb2394c4f943bc44f0fba7a4e9d19034e2ce2974ca60af44c1326ad4bff26be4b7591cb4b02825d49e125c6
  | 8, 2 => 0xffcceadcfce2758bfbefb591f9acd0faf7e68aa8f6e94291f22186e7f053c1fdee22ff53ec164c1eeabec0cdea555bf2e73f702ce7283c3de4625a30e3d420a8e1283faadfb32b5bd96359b3d697c1d4d1b38e6dcb46a5f8cae6d7d7c9f2a206c8d8951dc6a44c39c52f7576c398766ebf8705ebbe4be64fbcc8e334bc545819ba88bda4b837fe7bb3feb3cab253eee6b0e1dcffb080f6ebada32de2abbe6e52aa87c3f1a98c5b5da840633ca6910249a5d7b751a494c22fa3f2435da07b39919b71391a9b1dd7b09a36658d99ed5e87
  | 9, 0 => 0xf2854adfc2afde01b6be76349b34b1217e1a8a567cea112d76f0de33764e5f61705b5d9f5fbac6fd5cde0cce51bb2a0f4f8c57c24aee737942b779a33e277fff34064f6c2efbd9641b78d4bc1561a43a1142fa410e7e151305169eb0
  | 10, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xeeeeeeee00000000000000000000000000000000000000000000000000000000777777770000000000000000000000000000000000000000000000000000000055555555000000000000000000000000000000000000000000000000000000003333ffff0000000000000000000000000000000000000000000000000000000033333333000000000000000000000000000000000000000000000000000000000f0fffff0000000000000000000000000000000000000000000000000000000000ffffff00000000000000000000000000000000000000000000000000000000000fffff
  | 0, 1 => 0x11111111111111110000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000505555505055555000000000000000000000000000000000000000000000000030333330303333300000000000000000000000000000000000000000000000000ff00ff00ff00ff000000000000000000000000000000000000000000000000000fffff000fffff0000000000000000000000000000000000000000000000000000ffff0000ffff00000000000000000000000000000000000000000000000000000000ffffffff
  | 0, 2 => 0x33003300330033000000000000000000000000000000000000000000000000003232323232323232000000000000000000000000000000000000000000000000303030303030303000000000000000000000000000000000000000000000000022222222222222220000000000000000000000000000000000000000000000001155115511551155000000000000000000000000000000000000000000000000113311331133113300000000000000000000000000000000000000000000000011115555111155550000000000000000000000000000000000000000000000001111333311113333
  | 0, 3 => 0x50505050505050500000000000000000000000000000000000000000000000004444444444444444000000000000000000000000000000000000000000000000333333333333333300000000000000000000000000000000000000000000000033333333330033000000000000000000000000000000000000000000000000003333333322222222000000000000000000000000000000000000000000000000333300003333000000000000000000000000000000000000000000000000000033303330333033300000000000000000000000000000000000000000000000003322332233223322
  | 0, 4 => 0x8888ffff8888ffff0000000000000000000000000000000000000000000000008888888888888888000000000000000000000000000000000000000000000000555555555555555500000000000000000000000000000000000000000000000055550000555500000000000000000000000000000000000000000000000000005550555055505550000000000000000000000000000000000000000000000000554455445544554400000000000000000000000000000000000000000000000055005500550055000000000000000000000000000000000000000000000000005454545454545454
  | 0, 5 => 0xcc00cc00cc00cc00000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000000babababababababa000000000000000000000000000000000000000000000000aaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000aaaa0000aaaa0000000000000000000000000000000000000000000000000000aa00aa00aa00aa00000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a00000000000000000000000000000000000000000000000009999999999999999
  | 0, 6 => 0xecececececececec000000000000000000000000000000000000000000000000eca0eca0eca0eca0000000000000000000000000000000000000000000000000eaeaeaeaeaeaeaea000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e0000000000000000000000000000000000000000000000000ddddccccddddcccc000000000000000000000000000000000000000000000000ddccddccddccddcc000000000000000000000000000000000000000000000000cccccccccccccccc000000000000000000000000000000000000000000000000cccc0000cccc0000
  | 0, 7 => 0xeeeeeeee00000000000000000000000000000000000000000000000000000000eeeecccceeeecccc000000000000000000000000000000000000000000000000eeeeaaaaeeeeaaaa000000000000000000000000000000000000000000000000eeee0000eeee0000000000000000000000000000000000000000000000000000eee0eee0eee0eee0000000000000000000000000000000000000000000000000eecceecceecceecc000000000000000000000000000000000000000000000000eeaaeeaaeeaaeeaa000000000000000000000000000000000000000000000000ee00ee00ee00ee00
  | 0, 8 => 0xfaaafaaafaaafaaa000000000000000000000000000000000000000000000000f8f8f8f8f8f8f8f8000000000000000000000000000000000000000000000000f8f88888f8f88888000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000f0e0f0e0f0e0f0e0000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000eeeeeeeeeeeeeeee
  | 0, 9 => 0xfcfcccccfcfccccc000000000000000000000000000000000000000000000000fcfc0000fcfc0000000000000000000000000000000000000000000000000000fcf0fcf0fcf0fcf0000000000000000000000000000000000000000000000000fcccfcccfcccfccc000000000000000000000000000000000000000000000000fafafafafafafafa000000000000000000000000000000000000000000000000fafaaaaafafaaaaa000000000000000000000000000000000000000000000000fafa0000fafa0000000000000000000000000000000000000000000000000000faf0faf0faf0faf0
  | 0, 10 => 0xff888888ff888888000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000fefefefefefefefe000000000000000000000000000000000000000000000000fefeccccfefecccc000000000000000000000000000000000000000000000000fef0fef0fef0fef0000000000000000000000000000000000000000000000000fe00fe00fe00fe00000000000000000000000000000000000000000000000000fcfcfcfcfcfcfcfc
  | 0, 11 => 0xffee0000ffee0000000000000000000000000000000000000000000000000000ffccffccffccffcc000000000000000000000000000000000000000000000000ffccccccffcccccc000000000000000000000000000000000000000000000000ffcc0000ffcc0000000000000000000000000000000000000000000000000000ffc0ffc0ffc0ffc0000000000000000000000000000000000000000000000000ffaaffaaffaaffaa000000000000000000000000000000000000000000000000ffaaaaaaffaaaaaa000000000000000000000000000000000000000000000000ff88ff88ff88ff88
  | 0, 12 => 0xfffcccccfffccccc000000000000000000000000000000000000000000000000fffaaaaafffaaaaa000000000000000000000000000000000000000000000000fff88888fff88888000000000000000000000000000000000000000000000000fff0fff0fff0fff0000000000000000000000000000000000000000000000000fff00000fff00000000000000000000000000000000000000000000000000000ffeeffeeffeeffee000000000000000000000000000000000000000000000000ffeeeeeeffeeeeee000000000000000000000000000000000000000000000000ffeeaaaaffeeaaaa
  | 0, 13 => 0xffffffff99999999000000000000000000000000000000000000000000000000ffffffff88888888000000000000000000000000000000000000000000000000ffffffff55550000000000000000000000000000000000000000000000000000ffffffff30303030000000000000000000000000000000000000000000000000ffffffff22222222000000000000000000000000000000000000000000000000ffffffff11111111000000000000000000000000000000000000000000000000ffffffff00000000000000000000000000000000000000000000000000000000ffff0000ffff0000
  | 0, 14 => 0xffffffffeeeeeeee000000000000000000000000000000000000000000000000ffffffffcccccccc000000000000000000000000000000000000000000000000ffffffffcccc0000000000000000000000000000000000000000000000000000ffffffffcc00cc00000000000000000000000000000000000000000000000000ffffffffc0c0c0c0000000000000000000000000000000000000000000000000ffffffffaaaaaaaa000000000000000000000000000000000000000000000000ffffffffaa00aa00000000000000000000000000000000000000000000000000ffffffffa0a0a0a0
  | 0, 15 => 0xfffffffffff00000000000000000000000000000000000000000000000000000ffffffffffcc0000000000000000000000000000000000000000000000000000ffffffffff00ff00000000000000000000000000000000000000000000000000ffffffffff000000000000000000000000000000000000000000000000000000fffffffffcfc0000000000000000000000000000000000000000000000000000fffffffff0f0f0f0000000000000000000000000000000000000000000000000fffffffff0f00000000000000000000000000000000000000000000000000000fffffffff000f000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x1a72d6890174d688a04ae9d15940e5dfa2b4450ba2b447ea1745688a042ead15a2285
  | 6, 0, 0 => 0x1e744462945b00fda2b44587580698cc560b12c034e8af5a240601a746483013300d34172c1625b4e8c95a2b158fa6bd6890d8ac701a746498b0eb00d5a2b315839b768c95a1b158e034c48098589601a324762b04300d15929d1c218068b51151d10c034e8809870b6
  | 6, 0, 1 => 0x1a561d1c2c4b00d15a03f4c398068acc560e0ec034e8ad4a026601ff35688c56300d38e2314a858068ad0130e10c034e8c91d8a5601ff45688b0eb00d3a2b546899806ad15a22c3ac034e8587470b601f345658747300f35aacb62b18063ad118ac00c034e8a2d18ac6
  | 6, 0, 2 => 0x1e744b62b05b00dba2b444a758069d15a24050c034d6a0b9289601a2b4858744300d15a6b14a218068bcbd60e10c034e482b0e89601ff1d688c52b00dd8eb4462b18068acc560e0cc031d688c5288601b745662947300ad118ac14218068ad1161d0ec03cd6ab1161d6
  | 6, 0, 3 => 0x1a74444c3c5b00d36a22a3a258068ad1161d04c034e8b4a8e8e601ba231582c4b00d3a2b428099806ed0c560e16c034314a38588601a725586c52b00ad121b158058069d1797a51cc034da62a8709600034e8ad114280d1118ac16118069ad118a514c034e8ac94e8e6
  | 6, 0, 4 => 0x1a2b3158380b00d15a23f4c3d8068ad1130f10c03568ad1130f601a324c62b04300dba2b4458758069d1923ac3ac0345862b0708601a25b1522c4300d37eb448099806ed1920b158c03e56890d8a5601a324162944300eba22314a2d8069c91d8ac12c034d64a747096
  | 6, 0, 5 => 0x1a324158744300d2c528e16258068587470b10c034e4ab0d61d601d743158385b00d38eb444a75807fcf5a23158c034d688b0e8a601a74314a385b00d35a42c3a258079d15a2253ac03e56970d8ac601a6b4d62944b00d3a324c6295807fc75a22c3ac031d688b0e886
  | 6, 0, 6 => 0x34d68898789601a724c62b04b00d3a32414a75806ad15a2253ac034e84a7470b601a724162944b00d3a20bb62b1b756ab121b158e03456a0b9288601a71d689013300d396b4462b1807cd16a22c3ac034e8ad1140f6
  | 7, 0, 0 => 0x1a2b4462b9288701a2b407ec560e701a6b446294e89701a745688c560c701a6b446295089701a2b447ed18ac701a7467ad118ac701a2b446294f08701df4e888c560b701a7456a5018ac701cb4e8c9058ac701a74566294e8e701a7456629520e701a71d688c5626701a2b4480c5607701a7456629508e7
  | 7, 0, 1 => 0x1f3456a1118ac701a6b4482b0e89701a745688f58a570003cd6ab118ac601a745b88c562570003de8ad118ac601a745688c5622701a7456890d29d700034568901308600034b15838589601a746488b0e97701db4e8c9058ac701cb4e888b0e8b701bb456ab118ac701a74568894f9d701a74568901c267
  | 7, 0, 2 => 0x34568cc5608600034e482c5609601bb4e8acc560e701a745688c560d701a745696c549d701a745662bd28e701a7456889521d701d34e8acc560e70003456a0b9608601a2b4480b0e88700034568901fa6601a745693118a57000345688c5607601a74568894e8e701db4e888b0e8b701a745dad1202c7
  | 7, 0, 3 => 0x1a7431589470b701db4e8ad1160f701b34e8ad1161d701a745688cd8ac701eb4e888c528b701cb4e8ad11cb1701a6b4480c5289700034c45874589601a7460ad118ac7000345690c5608601a745680c528e700034e8587470b601a2b446ec5608701a2b4480fd61d701a745688b0e98701a6b4462bd2897
  | 7, 0, 4 => 0x1a684462b0589701a74445874a8b7000345688c5606601a7456890e026701a62315898589701a745696c57a9700034e8acc528e600034e8c90561d601db4e8890160b701a7431589870b700036e8ad118a5601a62315894589701a7464ad3d8ac701a746288e18ac701a7456a7118ac701a7459ad120317
  | 7, 0, 5 => 0x1a746482c5626701a74445894e8b70003ae8acc560e601a745aab118a5701cb4e8acc528e701a745662b0703700034e8ad41725601a6b55890d8a5701a746482c5625701a745688f18a5701a2b4472c5608701a7456890129d701a7456890130e701a74569d1161d701a745688c5623701a2d5662b07087
  | 7, 0, 6 => 0x1a745688b0e9c700034e8ad1129d601a745088b0e8b700034565874708601d745aad118ac701db968acc560e701db4e8acc528e701f74e8ad1129d701a745ead3e22c701a62315cb0589701a6b445874b89701a745ead11f2c701a744f88c560b701a7457ad118ac701a745662c128e701a74447cc560b7
  | 7, 0, 7 => 0x34d66294709601a745685018ac701cb4e8ad1129d700034da88c5509601a745690c561d7000345688c5602600034e8b4c550e601a2b315894708701a74445874a0b701a74565874d0e701bb45689058ac701a2d5688b0e88701a7464ad298ac701a2b4482c5288701a6d55890d8ac701a6b4788c56097
  | 7, 0, 8 => 0x1a744462b078b701a745688b561d701db968ad1161d701db4e8ad1129d701a745688c5612701a2b445874a88701a6d5688c528970003ce888c560b601a745688e58a5701a745688b121d701a7456970d61d701a2f5662b0708701a745aacc528e701a623158a4589701a2b315898708701a7464ab118a57
  | 7, 0, 9 => 0x1a7464acc529f701a22315838588701a2b445894e88701a325688b0e88701a6fd689018ac701a6b315874709701a744a88c560b701a745688c5616701a6b4b88b0e897000376888c560b601a745680c560e701a74568f1161d700034446294588601a6b315838589701a74446ac560b701d7464ad118ac7
  | 7, 0, 10 => 0x1a7456587470b701a7456a0c529f701a745688ed8ac701a2f5688b0e88701a745aad1129d701a74567ac560e701a745688c5610701a22315874588700036e8ad118ac600034d68894e89601a744458a4e8b701a2b4c88c5608700034e8c91d8ac600034e8ac94e8e601c34e888c560b700034e8b51151d6
  | 7, 0, 11 => 0x1a2b4462b0788701cb4e8ad4172c701a6b4062b0709701a7466ad118ac701ab45688c560f701a745674c560e701a745688b0e9b701c74e8ad1161d701a6f5688c5289701a74568894e95701a745eacc528e701a7459ad118a5701a2b445874a08701a743158ac70b701a6b445874709701a725688c52897
  | 7, 0, 12 => 0x1a745ead1129d700031d688c5608600034d688c5627600034e8ad0130e601a745699118a5701a744458ace8b701a2b447ec560f701a224062b0588701a74569f118a5701a7456931161d701a7444629470b701a7464ad1129d701a6b446294f09701a6b4474c5609701a74566294f0e701a744486c528b7
  | 7, 0, 13 => 0x1eb4e888b0e8b701a2b4b88c5288700034d6a0b9609601a745aaac560e701a6b4480b0e89701a2b3158a8708701a745688e961d701a745680b0e8e701a74568901e26701a745aad2a231700034569ac5608601e34e8ad1161d701a2b4458a4e8870003fe3ad118ac600034d68901309601a745688c98a57
  | 7, 0, 14 => 0x1a6b55890d61d701a745688f161d701a745cad118a5700034d688c560a601a7464ad12026700034e8acb0e8e601a2b446294f88701a7463ad118a5701a745688c528f700034d690c5609601a7461ad118ac701a73e3ad118ac70003ce8ad118a5601a7458890d8ac700034d68cc5609601a745662b07057
  | 7, 0, 15 => 0x34315838588601a74569711eb1701a6b4472c5609700034e4ab0d8ac601a6d5662b0709700034e8ad2161d601a7456a0b9625701a2b446294e88700034e8ad358a5600034e8bcbd60e601a745688b0e85701f345697118ac701e745688c561d700034e3ad118a5601bb45688c560e701a2b4462947087
  | 7, 1, 0 => 0x1ff4e3ad118ac7d3a325588c5626801a745688c5611701a2b4480c528870003e68b5118ac601e745689018ac701a6b4482c5289701a745aacb0e8e7000346482c5608601a7464ab1161d701a745696b0e95701a745db5118ac701df4e8ad1161d701a2b4482b0e88701a71d688c561d7d35aac486c56268
  | 7, 1, 1 => 0x34e8c9058a5601a7459ad1161d701a6b4c88c5609701a7431587470b701a745688c529a701a745688c52a0701a6b445894e89701a725688b0e89701a7456a912026701a745688c560f701a7456890529d701af4e8ad1161d701a71d689018ac700034e8629470b601a2b4480fd8a5701a74568894e8f7
  | 7, 1, 2 => 0x1db4e3ad118ac701a7456890130f701a74569f1161d701a745e88bd629701a745688f961d701a746482c561d701cb4e8ad358ac700034e8b0c560e601a2b4788c5608701cb4e3ad118ac701a744486b0e8b701a6b445874a097000345688c5604601a22315cb0588701a6f5688b0e89701a745688c56197
  | 7, 1, 3 => 0x1a745688b0e8f70003ce8ad1161d600034d69ac5609601a6b4458a4e8970003ae8ad118a5600034e8ad1130f601ab45689018ac701a745688d98ac700034e8c9318ac601a744062b070b7000375688c5609601a74568906026701a745688c5613701a6b4462b07897000345a88c5508601a7456991161d7
  | 7, 1, 4 => 0x1a745688b0e99701cb4e862b070b70003fe8ad118ac600034e3ad1161d601bb464ad118ac701a2b445874708701a325688c5288701a74568894e9a70003568ad118ac601a7363ad118ac700034e862b070b600034568894e88601a74568f118a5701a746483018ac701a745688cd8a5701a7463ad1161d7
  | 7, 1, 5 => 0x1a6b446294709701b745688c52a4701db4e862b070b701a71d688c5625701a2f5688c5288701a743160b070b701a745688c52a37
  | 8, 0, 0 => 0xfba745688c561d801cb4e8ad118a5701a745688c56037eda745697118ac8d3a2b4b88c582c801a2d5688c5608700034e8ad118a5601a745088c560b7e5a745697118ac8000345662b0708601a744462b130b701f74e8ad118a57d3a2b4480c560e801a744462b128b7d3a2b4487018ac8d3a2b4462bd60e8
  | 8, 0, 1 => 0x1a325688c5608701a745688b0e9a7eda745688c560e8e5a745688c561d801a6b4b88c56097000345688b0e88601a74568f118ac7e5a745688c560e801db968ad118ac701db4e8ad118a5701a745688c5624701a745688c5825701a7456970d8ac701a744462b960b701a745688b0e9770003ae8ad118ac6
  | 8, 0, 2 => 0xe5a745688c57ac801a745662b0e8e701a745689018ac701a7456971161d701a6b4462b07097d3a2d56890d8ac801a745662b070b7fba745689018ac801a2f5688c5608701a745aad118a5701a2b4462b1308700034d688c5289601a744462b148b700034e8acc528e600034e8b5118aa601a2b4462b12887
  | 8, 0, 3 => 0xd3a2b4462b128e801a744462b158b7d3a2b4486c5625801a745693118ac7eda745689018ac801a745688b0e8e701a7464ad118a5701a745688f58ac701a7456890d61d7d3a2b4480d18ac8e5a745689018ac800034e8ad1129d601c74e8ad118ac7d3a2d5688c561d801a2b4462b9608701a6b4462b0e897
  | 8, 0, 4 => 0xd3a2d5689018ac801eb4e888c560b701a745688c529e701a6b4480c5609701a745688e98ac7d3a2b4462b129d8d3a2b4462b130e8d3a325688c561d801cf4e8ad118ac701a745680c560e7d3a2f56890d8ac801e34e8ad118ac701a6b4462bd6097d3a2b4486c5626801a2b4462b1488701a745ead118a57
  | 8, 0, 5 => 0xd3a325689018ac800034e8ad198ac601a745688c5605701cb4e8acc560e7efa745689018ac8d3a2b5588c561d800034e8ad4172c6d3a2b4462bd625801a6b55890d8ac701a745688f18ac701a7456890161d700034e8acc560e600034e8ad12026601a7456ab118a5701a745688c57257d3a2b4480f18ac8
  | 8, 0, 6 => 0xe5a7464ad118ac801a745688e58ac701a745aacc560e701a7464ab118ac700034d662b0709601cb4e8ad1161d7d3a2b4462b149d801df4e8ad118ac701a2b4482c5608700034e8ad1161d6d3a2f5689018ac8d3a2b4462b148b801db4e8acc560e701f74e8ad1161d700034e8ad218ac601a745662c160e7
  | 8, 0, 7 => 0x1db4e8ad1202c701a7459ad118ac701a6b4462b1289701a725688c56097d3a2b4462b159d801a745689058a5700034d688b0e896eda745ead118ac800034e8acb0e8e6d3a2b4462bd6298e5a745ead118ac8fba745688c572c8eda7464ad118ac8d3a2b4462c16258d3a325688c582c801db4e8ad1161d7
  | 8, 0, 8 => 0x1a745688b0e947d3a325688c56268d3a2b4480c560f801a745ead1161d7d3a325688c56258d3a2d5688c572c801a745699118ac701a74569f118ac701a745688f98ac701a745688b129d701a7464ad1161d701a744486c560b7d3a2b4482c561d801a6f5688c56097d3a2b5489018ac801a6b4462b13097
  | 8, 0, 9 => 0xeda745689058ac801a2b4462b0e887e5a745689058ac800034e8ad358ac601a745688b149d700034e3ad118ac601a2b4462b0708701a745cad118ac70003768ad118ac6000345688c5288601a7463ad118ac701a745688c560f70003ce8ad118ac601a6b4462b14897d3a2b4483018ac8d3a2f5688c56258
  | 8, 0, 10 => 0x1a745688c561a7d3a2b4482c56258d3a2f5688c562b801a7456890561d7d3a2b4462b0e8e800034e862b070b601a2b4480fd8ac7d3a325688c562b801a745688c529d701a745688c52a4701a745688b159d701a2b4480c5608701a745688c528e701a6b4482c5609701a745688c529f7d3a2f5688c56298
  | 8, 0, 11 => 0x1a745689018a57d3a2b4482c5626801bb4e8ad118ac700034e8c9058ac6
  | 9, 0, 0 => 0xd3a325688c56380d3a2b4458758069ad118ac12c034e8acc560e6eda745688c563e9d15a23160b1f969d15a23158e034e8ad118ac6fba745688c563e9d15a24062b1f4e8ad118af58fa745688c561d7d3a2b4462b073e9d15a24362b1c069d15a2314ada745697118ac7
  | 9, 0, 1 => 0xd15a2315821b4e8ad120b158fa745688c562b7d3a2b4462b14be9d17ab4462b1f4e8ad118ac4cfa745688c56257
  | 10, 0, 0 => 0x34e8ad118ac6
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 39
  | 6 => 53
  | 7 => 60
  | 8 => 60
  | 9 => 53
  | 10 => 46
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 7 0) :: stateWires n (ids >>> 7)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x1fff7fff00000000000000000000000000000000000000000000000000000007ffffffff00000000000000000000000000000000000000000000000000000007fc38f1c400000000000000000000000000000000000000000000000000000007e3ffffff00000000000000000000000000000000000000000000000000000007e3c78e3b000000000000000000000000000000000000000000000000000000071fffffff00000000000000000000000000000000000000000000000000000000ffffffff000000000000000000000000000000000000000000000000000000001fffffff
  | 0, 1 => 0xfc7f8fe000800000000000000000000000000000000000000000000000000000e3c67f1fc07e0700000000000000000000000000000000000000000000000000e3ffff1c38f1c400000000000000000000000000000000000000000000000000e07f8f03c78e3b000000000000000000000000000000000000000000000000001fc1f8ffc001ff0000000000000000000000000000000000000000000000000003fff81fffffff00000000000000000000000000000000000000000000000000003ff8003fffff00000000000000000000000000000000000000000000000000000007ffffffff
  | 0, 2 => 0xe03e0700078e00000000000000000000000000000000000000000000000000001c3980e3c78e3b000000000000000000000000000000000000000000000000001c3980e00780380000000000000000000000000000000000000000000000000000000003c70e3b00000000000000000000000000000000000000000000000000fffffffc0081c400000000000000000000000000000000000000000000000000fc7f8fe3c0803b00000000000000000000000000000000000000000000000000fc7fffe038f1c400000000000000000000000000000000000000000000000000fc7f8fe0078e3b
  | 0, 3 => 0x1c3980e03881c0000000000000000000000000000000000000000000000000000380701c3871c400000000000000000000000000000000000000000000000000fc7f8fe3c78e3b00000000000000000000000000000000000000000000000000fc7f8f00078e0000000000000000000000000000000000000000000000000000fc7f8803c70e3b00000000000000000000000000000000000000000000000000fc4007e3c0000000000000000000000000000000000000000000000000000000fc3f87e0078e3800000000000000000000000000000000000000000000000000e03e0703c78e3b
  | 0, 4 => 0x3ff8003fffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fffffffc38f1c400000000000000000000000000000000000000000000000000ffc007fc00000000000000000000000000000000000000000000000000000000fc3f87e038f1c000000000000000000000000000000000000000000000000000e3be771c38f1c400000000000000000000000000000000000000000000000000e03e070038f000000000000000000000000000000000000000000000000000001fb9f0fc38f1c4
  | 0, 5 => 0x38700000000000000000000000000000000000000000000000000000000000003801c0000000000000000000000000000000000000000000000000001c3980e3c78e3b0000000000000000000000000000000000000000000000000000000003c70e3b0000000000000000000000000000000000000000000000000000000003c000000000000000000000000000000000000000000000000000000000000000070e00000000000000000000000000000000000000000000000000000000000007003800000000000000000000000000000000000000000000000000fc7f8fe0008000
  | 0, 6 => 0x380701c3f71fc00000000000000000000000000000000000000000000000000000000003f70380000000000000000000000000000000000000000000000000000000003ff0ffb00000000000000000000000000000000000000000000000000000000003f01f800000000000000000000000000000000000000000000000000ffc077fc3871c400000000000000000000000000000000000000000000000000e3be771c38f1c4000000000000000000000000000000000000000000000000000380701c3871c4000000000000000000000000000000000000000000000000000380001c000000
  | 0, 7 => 0x3807000000000000000000000000000000000000000000000000000000000000380701ff871c4000000000000000000000000000000000000000000000000000380001fc70e3b000000000000000000000000000000000000000000000000000380001fc0000000000000000000000000000000000000000000000000000000000000003f7ff8000000000000000000000000000000000000000000000000000380701c3f7fc40000000000000000000000000000000000000000000000000000000003ff7e3b00000000000000000000000000000000000000000000000000000000003f7e00
  | 0, 8 => 0x380003ff8e3b000000000000000000000000000000000000000000000000001c3980e03f81f8000000000000000000000000000000000000000000000000001c0000e0000000000000000000000000000000000000000000000000000000001c3980e03f81f8000000000000000000000000000000000000000000000000001c0000e000000000000000000000000000000000000000000000000000000000003800003f81f800000000000000000000000000000000000000000000000000003800003f8000000000000000000000000000000000000000000000000000000380701fff7fff
  | 0, 9 => 0x1f8070fc3871c4000000000000000000000000000000000000000000000000001f8000fc000000000000000000000000000000000000000000000000000000001c3980e03ff1f80000000000000000000000000000000000000000000000000003b8701c3ff1c4000000000000000000000000000000000000000000000000001c3980e3ff8ffb000000000000000000000000000000000000000000000000001c0000e3c70e3b000000000000000000000000000000000000000000000000001c0000e3c00000000000000000000000000000000000000000000000000000001c3980e03f8ff8
  | 0, 10 => 0xe000070000000000000000000000000000000000000000000000000000000000e03e07003ffe0000000000000000000000000000000000000000000000000000e0000700000000000000000000000000000000000000000000000000000000001fb9f0ffffffff000000000000000000000000000000000000000000000000001f8070fff871c4000000000000000000000000000000000000000000000000001c3980e03ffff800000000000000000000000000000000000000000000000000003800003ffe00000000000000000000000000000000000000000000000000001fb9f0fc3ff1fc
  | 0, 11 => 0xe380071fc0000000000000000000000000000000000000000000000000000000e3be771c3fffc400000000000000000000000000000000000000000000000000e380771c3871c400000000000000000000000000000000000000000000000000e380071c00000000000000000000000000000000000000000000000000000000e03e07003fffc000000000000000000000000000000000000000000000000000e03e0703fffe3b00000000000000000000000000000000000000000000000000e0000703c70e3b00000000000000000000000000000000000000000000000000e03e07003ffe00
  | 0, 12 => 0xff8077fc3871c400000000000000000000000000000000000000000000000000fc0007e3c70e3b00000000000000000000000000000000000000000000000000fc0007e000000000000000000000000000000000000000000000000000000000fc3f87e03ffff800000000000000000000000000000000000000000000000000fc0007e000000000000000000000000000000000000000000000000000000000e3be771fffffff00000000000000000000000000000000000000000000000000e380771fff7fff00000000000000000000000000000000000000000000000000e380071fc70e3b
  | 0, 13 => 0xffffffe000800000000000000000000000000000000000000000000000000000fffff80000000000000000000000000000000000000000000000000000000000fffffffc00000000000000000000000000000000000000000000000000000000fffff8e007803800000000000000000000000000000000000000000000000000fffff803c70e3b00000000000000000000000000000000000000000000000000ffffffe000800000000000000000000000000000000000000000000000000000fffff80000000000000000000000000000000000000000000000000000000000ffc007ffc00000
  | 0, 14 => 0xfffff81fff7fff00000000000000000000000000000000000000000000000000fffff81c3871c400000000000000000000000000000000000000000000000000fffff81c00000000000000000000000000000000000000000000000000000000fffff80038700000000000000000000000000000000000000000000000000000fffff8003801c000000000000000000000000000000000000000000000000000fffff803c70e3b00000000000000000000000000000000000000000000000000fffff800070e0000000000000000000000000000000000000000000000000000fffff800070038
  | 0, 15 => 0xffffffe000000000000000000000000000000000000000000000000000000000ffffff1c00000000000000000000000000000000000000000000000000000000ffffff003ffe0000000000000000000000000000000000000000000000000000ffffff0000000000000000000000000000000000000000000000000000000000fffff8fc00000000000000000000000000000000000000000000000000000000fffff8e03f81f800000000000000000000000000000000000000000000000000fffff8e000000000000000000000000000000000000000000000000000000000fffff8003f8000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x37ddb36dd00000000000000000000000000000000000000000000000000000007f992a49000000000000000000000000000000000000000000000000000000006d810a08000000000000000000000000000000000000000000000000000000005a18b965d00000000000000000000000000000000000000000000000000000005a1828410000000000000000000000000000000000000000000000000000000031549364d000000000000000000000000000000000000000000000000000000006cc912dd000000000000000000000000000000000000000000000000000000000449124d
  | 0, 1 => 0x902004800080000000000000000000000000000000000000000000000000000062c65b17407e07000000000000000000000000000000000000000000000000004215621020610000000000000000000000000000000000000000000000000000204a8903040c22000000000000000000000000000000000000000000000000000dc1b86ec001ff0000000000000000000000000000000000000000000000000000dff8066d5b6f00000000000000000000000000000000000000000000000000001ff8002d5b6f00000000000000000000000000000000000000000000000000000007fddbb6dd
  | 0, 2 => 0xb02a0581068c0000000000000000000000000000000000000000000000000000b46a8da3868c3200000000000000000000000000000000000000000000000000942884a086803000000000000000000000000000000000000000000000000000244a8923860c3200000000000000000000000000000000000000000000000000992124c80081800000000000000000000000000000000000000000000000000094608ca2808032000000000000000000000000000000000000000000000000009035648020c10000000000000000000000000000000000000000000000000000902a8c80048822
  | 0, 3 => 0x993124c8308180000000000000000000000000000000000000000000000000004b15625830618000000000000000000000000000000000000000000000000000b46a8da3868c3200000000000000000000000000000000000000000000000000b46a8d83068c2200000000000000000000000000000000000000000000000000b46a8923860c3200000000000000000000000000000000000000000000000000b46005a382841000000000000000000000000000000000000000000000000000b42a85a1868c3000000000000000000000000000000000000000000000000000b46a8da3868c32
  | 0, 4 => 0x9ff8046d5b6f000000000000000000000000000000000000000000000000000080100449124d00000000000000000000000000000000000000000000000000db3566d830e18000000000000000000000000000000000000000000000000000db2006d810a08000000000000000000000000000000000000000000000000000db3566d830e18000000000000000000000000000000000000000000000000000db3566d830e18000000000000000000000000000000000000000000000000000d234469030e00000000000000000000000000000000000000000000000000000db3566d830e180
  | 0, 5 => 0x4214421039720000000000000000000000000000000000000000000000000000091120483901c800000000000000000000000000000000000000000000000000b4ea9da7cf9e7f0000000000000000000000000000000000000000000000000024ca9927cf1e7f0000000000000000000000000000000000000000000000000024c00127c2041000000000000000000000000000000000000000000000000000200a01010f1e0000000000000000000000000000000000000000000000000000040880208f00780000000000000000000000000000000000000000000000000090a0148449924d
  | 0, 6 => 0x4f9df27cff73fd00000000000000000000000000000000000000000000000000461cc230bf7278000000000000000000000000000000000000000000000000002ddbb96fff1fff000000000000000000000000000000000000000000000000000d19a068bf01f800000000000000000000000000000000000000000000000000dbb576dc79f3cd00000000000000000000000000000000000000000000000000dbb576dc79f3cd000000000000000000000000000000000000000000000000004b95725c7973cd000000000000000000000000000000000000000000000000004b80025c502080
  | 0, 7 => 0x6fdff802244922000000000000000000000000000000000000000000000000006fd5737ffb77dd000000000000000000000000000000000000000000000000006fca9b7fdf3eff000000000000000000000000000000000000000000000000006fc0037fd22490000000000000000000000000000000000000000000000000006f1fe379bf7ff8000000000000000000000000000000000000000000000000006b9f735d7f7fcd0000000000000000000000000000000000000000000000000066dedb37ff7e7f00000000000000000000000000000000000000000000000000621e43113f7e00
  | 0, 8 => 0xb4fa9da7ff9e7f000000000000000000000000000000000000000000000000009db9b4ecff93fd000000000000000000000000000000000000000000000000009da014ecdb92dd000000000000000000000000000000000000000000000000009d39a4e8bf81f8000000000000000000000000000000000000000000000000009d2004e8928090000000000000000000000000000000000000000000000000009d39a4e8bf81f800000000000000000000000000000000000000000000000000903804803f8000000000000000000000000000000000000000000000000000006fdffb7fff7fff
  | 0, 9 => 0xdfb576fcfbf3dd00000000000000000000000000000000000000000000000000dfa006fcd2a09000000000000000000000000000000000000000000000000000df3de6f8bff3f800000000000000000000000000000000000000000000000000dbbd76dc7ff3cd00000000000000000000000000000000000000000000000000bdfbbdefff9fff00000000000000000000000000000000000000000000000000bdea9defdf9eff00000000000000000000000000000000000000000000000000bde005efd2849000000000000000000000000000000000000000000000000000bd3ba5e9bf9ff8
  | 0, 10 => 0xf2a017955bb64d00000000000000000000000000000000000000000000000000f23e47913ffe0000000000000000000000000000000000000000000000000000f220079112a40000000000000000000000000000000000000000000000000000ffffffffffffff00000000000000000000000000000000000000000000000000fff577fffbf7dd00000000000000000000000000000000000000000000000000ff3fe7f9bffff800000000000000000000000000000000000000000000000000f23e47913ffe0000000000000000000000000000000000000000000000000000dfbdf6fcfff3fd
  | 0, 11 => 0xffe007ffd2a49000000000000000000000000000000000000000000000000000fbbf77dd7fffcd00000000000000000000000000000000000000000000000000fbb577dd7bf7cd00000000000000000000000000000000000000000000000000fba007dd52a48000000000000000000000000000000000000000000000000000fb3f67d93fffc800000000000000000000000000000000000000000000000000f6fedfb7fffe7f00000000000000000000000000000000000000000000000000f6ea9fb7dfbe7f00000000000000000000000000000000000000000000000000f2be57957ffe4d
  | 0, 12 => 0xffb577fdfbf7dd00000000000000000000000000000000000000000000000000ffea9fffdfbeff00000000000000000000000000000000000000000000000000ffa017fddbb6dd00000000000000000000000000000000000000000000000000ff3fe7f9bffff800000000000000000000000000000000000000000000000000ff2007f992a49000000000000000000000000000000000000000000000000000ffffffffffffff00000000000000000000000000000000000000000000000000ffffffffffffff00000000000000000000000000000000000000000000000000ffea9fffdfbeff
  | 0, 13 => 0xfffffc866ddb6f00000000000000000000000000000000000000000000000000fffff8066d5b6f00000000000000000000000000000000000000000000000000fffffeda34e9a200000000000000000000000000000000000000000000000000fffffca2a6c93200000000000000000000000000000000000000000000000000fffff923a64d3200000000000000000000000000000000000000000000000000fffffc8224c92200000000000000000000000000000000000000000000000000fffff80224492200000000000000000000000000000000000000000000000000ffe007ffd2a490
  | 0, 14 => 0xfffffb7fff7fff00000000000000000000000000000000000000000000000000fffffa5e7d7bef00000000000000000000000000000000000000000000000000fffffa5e7469a200000000000000000000000000000000000000000000000000fffffa123d7b2200000000000000000000000000000000000000000000000000fffff84a3d49ea00000000000000000000000000000000000000000000000000fffff927ef5f7f00000000000000000000000000000000000000000000000000fffff9032f5f2200000000000000000000000000000000000000000000000000fffff822af497a
  | 0, 15 => 0xfffffffbb6edb200000000000000000000000000000000000000000000000000ffffffdf76eda200000000000000000000000000000000000000000000000000ffffff933fff2200000000000000000000000000000000000000000000000000ffffff9336ed2200000000000000000000000000000000000000000000000000fffffefef6e9b200000000000000000000000000000000000000000000000000fffffceabfc9fa00000000000000000000000000000000000000000000000000fffffceab6c9b200000000000000000000000000000000000000000000000000fffffc823fc922
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 128 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 128 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 128 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 128 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 7 0) :: stateWiresD n (ids >>> 7)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 7 0) :: stateWiresS n (ids >>> 7)
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
  | 5 => 5
  | 6 => 445
  | 7 => 2054
  | 8 => 702
  | 9 => 10
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0xa35c9dd66dbc262942b779a335de7fb22719e33d
  | 6, 0 => 0x15215ed91499d35c140ae8b113c93bbb13967e2f1356a1bd12fc993212811c9f11f45ea911ed6bfa114c834e11027a491098c65a1086077f105e20a00fb8ab870f0731ff0ee2d2210eb903040e98ce120e7e15130e6fc91f0e6ec3600e5d008b0e2dbbf60dfc2cef0d3f24990d0073760cabde0a0bc688930b931def0b473e830b13235e0b09be840a2e374109d0c57e096e94380919997808f8b29208f317a508ea0cab08531ca10840dbaa0772c9e8076e47da07517d1206ff5f2205aa5cc505a197e905941c82052feefa0505ca720480989f04465ad3025334cb0229104301e6efe701e085fd01c03b0201af582a01aa03700169a0a4011138840035be98
  | 6, 1 => 0x2e6465742d6774cc2d0fd3a02cab1c642c2816dc2be61f7b2b81626d2a71da7129f1c6ed292f8a3b2907425528ce93e328b0dc0f28a4a83e288e426d2796dd782791d30f2779c54f274008b72705880d26d3ff3726acc7fc268b8b8e2629ae6e25d32ac22596955e257d59b82566dfcd24f17cc624a37411248ba27c242df0e3240fb77123e3e51a23b5d9fe2379f29f22ed54d222bbb1f1229ccada2244ea1621a326f9213869ba20292edb1fdef7c21e02d8001d7f45531d600c9e1c96ea491b6d57411a85e0ab19ea4e6519d5fa50194cd8471937f12c19169d33190722ad18f26c4c18c1be6718ae189c1702d2d716f646d616ec765a16eb0e04154b8fd4
  | 6, 2 => 0x46e4d62d466521354642c44a462570b34605aa1845a7f5984545237444a5495d447b5303446e880f44171c5a4410cedd440fb91144081bfe434ac03243091b4242b779a3426a2d27422278a241c1c8b2413a622b408ab1bd4063e2793fd8c2543fc0c4623f4ef09c3d9f94a43d513e8d3ce4326c3c90e5203c21f90f3b932d743aefa4b03a4fc206399af8df39957fd3393cca5b38cea9a837bb82de378bd8c23761c3f3376135eb3710815436a8c2383660102c363bd369360ac24835dd329c358ad894355171d6344f2edf342382853404b2bb32e5408e32973ec6317a69f6315db1f13099cb8930924cb830625b533037bc2b2fbc5b6d2ef292772ed4161b
  | 6, 3 => 0x63e7901f63669d95632a28cb62ba72926213072461f5a73b61bcf3e0619ad28a60e1145a60bfdce060741d37600575d45fc63bae5f6a6de05e76a8da5db263ce5da597495d5e93455d4c3cf25d26770c5cde0cce5bbb72fe5aa8a6b95a657cac5a16d00059a0445d59254669584a41b757530f6056e35aec56a640ba5678aa8554bc1240547f9cb8546ec5c453b44d125384a2f6533e153353327396516e8881511c0fe950e09c1a50407db84ffd7cef4fc9e1344f0d9c4b4ebf453b4dd8e4694d84259f4d40ae504c56afea4c42ae274b27218a4b24895f4aba82fd4aae3b9e4a6f824f4a34f31549e9f93549603f00495b4db148cbb65d48558c3947b4abff
  | 6, 4 => 0x8d5eaaf98bb136488a81f0ca870b766e862ff0fc8576a60484670fcc82b1f70a80feb7d9805f6c4f7f78bc997f0d3e2d7f01a2127e34a38b7e159c437daae9a37d8ecad87d5cbd9a7cacac927b5aa26779e15a28787cbaa177ec429877be1087777cb77e774de0997749b4e376a391b77562807374e00fc474cf39e4743d2db173c6d788738810d3735b09347283a7e7727718da7272405d723b692c711d96fc705b5d9f701a425c6fe4edb86f70d59c6ecb5e0c6e2f9b786e194f236dd38ed86d6752b56c0c15f06ababa2c6a8772f96943710f68eb1e2568dbf4ab68c914856733942566b07251663f3663654b05bf64cbb148647c796e6425399863f5bffd
  | 6, 5 => 0xc3e4acefc35d2172c2217eaac219efd3c00fd164bfa40e66bf8705ebbe4be64fbd3c5e53bcbf7b05bbcbb14aba88bda4ba762a6eb8e76ab4b633b794b5640a2ab53b7098b309a8e9b24f00d3b1b0cf21b065425baea8bef3abf5bd73ab3d878cab2b47bcaa5a7cbca850eeb5a8112672a7ebe2bba764573ea621259fa5109808a3ffc12ea352a66ea2cebd7fa1a0b745a01d11f79ed6cc0e9d036fc99cf000b59c280e959be530079be41d5a9b9efe689b9d37b39b7186cd9b34369199a3b3d79947bb24986cdbad98602235985f71fa97ac0d10972eb7d796c3c09c968281c393b996fe92aff4bf926ae7a992183538919f4e7b90e2f0448f7a66348e4d0a48
  | 6, 6 => 0xfe71e535fd4ecf59fc5a8b42fac52187fa401789fa3cba86f9acd0faf96feb04f90b6e1df5fcd64df5061260f47b805bf465566cf4483035f2da6a70f1d8600ef0f8df95efa77ca6edb06ad3ed2ae9e7ecc12505ecae38b7eca992adec164c1eebefca4bea70c2cfe99c23e4e64f26d8e4162929e389f5f5e2fe02e2e2f6af66e239d3cee207e790dff2e4cfdd1a69d6db8c9188dafe8bd3daa96d91d9af5a0fd9352887d8d02dfad832dd31d6209a43d460f073d279eabad00bf48acf45a100cf449b41ca5bf32ac9f2a206c9c1e28dc945fe97c928f482c858f251c83e807fc75137bbc73fff91c6a44c39c67def90c43ecf6e
  | 7, 0 => 0x4c021da04bca65904963a7b048faf4c04890ef504824cd40479bbe10460888804427d3b042b899704278c9404253990035eb4ec0355cd580341d11b033b05b50330c8120318307a03087e0402e9d44b02dc927b02c16857029f514b0295a2700294122e028de01e02898f5e026640040257ffd002502c67024ad8f90248132d02470b1b023f5c5b02075cec01cde88101b5ee8d01abdea401a6e4da019f361a019c9fad01794b5f0165a78a01652a32015fcb3e015517830146c416014268c7012a58400124c53e011f27fd01189ba9011182d800f9b8fb00f5a3d200ea38dd00d76e0200ccfaeb00b9120700b34936009b3f220082d9db006c268400481fea
  | 7, 1 => 0xa2deef809ee1b6f09d9969709c0e32809bdf0a009bd51ef0989c7c3098773d9093e735608fadadf08e4c69e08c7c03908c5dc3f08b46af10899ab5308739b700865d84f08586f940848694b0844bf83083fa81e083004ee081c74db0815b7f907f70b8707ed8a3207c20e2707c038b30790b29f078f1e53078c6002078179cf074eba9407492140071cbf990715437d06fb5c5206e5daf3068bc39d0681af190680b92c06735b220665520c0659598f065401810651b5d5064cb80906457cb9062e761d06291d8306237d4e05e9221005c61dd605b86497057ed236057c0b7a05687e890562a0ac055afcf40555b2b9052aa49505169eb00512d1890509fa1f
  | 7, 2 => 0xeed14a20ee0af2a0edf18670ed019dd0ea51df30e96d1cc0e90cf7c0e7e15130e7dd0190e7db3450e7515ed0e66678e0e38b6fe0e1f184a0e05ccb20df565b60df435510df1ea5d0df124ef0dcab45d0dc23f740db9c7830d9cbe430d7f85ab0d6e8d170d61f2fb0d49c4170d40e0e10d3dec4f0d3586890cedf22c0cea20e10ce9b2880cd4b54f0cba81470cb5970c0cabde0a0c8c4ccf0c825c970c6ed2f30c6d8e9c0c687b0e0c2ad96d0c232aad0c22507d0c0bf6ea0ba0f9160b985bbe0b88cc090b5bfccf0b5bd3a60b4d39680b41c7720b2c8ce60b2912830b2179b20b05d34b0afb5dd30af197a60acf09dd0ac4d5b90ab8b2690a7a55280a6572fc
  | 7, 3 => 0x13e030a013967e2f139302bf13728f56133c08ef1317dd2b130a5a891305f52212ed063c12ddb43412cd450012bb814412a8595d127638531233466a1232479712300b711228cbf912245a68122261f8120d1dd3120061e011f373c011d640d011c1f92a11bd50f4118eca21118d0e1d116b4724115e1032114c695c1142fa4111408e9a113ec3a41106ad5710de35ff10bf6ca6109bbfbb109410fb108ef5b9107838631070f4c710431b29102d4a7a101f34a21004221f0ffdfe370ff3cd480fec104b0fcb33c20fb1a7760fa2a5570f9aa5fd0f9550a90f8e38f60f8899180f8009980f7ac0e10f78ea770f53334a0f1c66040f1bfb200f1a8f2b0eef2d5f
  | 7, 4 => 0x18eb577118ccee3b18c40ebb18c13d3918ac994f1882b16918595dba18545dd6184c7d92183afea71830634d18261f78181c7acd1813153418043d6917e4d13d17ddd95917d9c21d17b7e34f17b77a5217a3f1f5175c2c75175a929b172938d7171f64aa1712096e1706ecff16dbf17016d21d8816c91dcd16bceacf1695814b16859a0f1673385e16573f0016528f35164042a2163cc6661612f34116118174160c7aef15f4eac915e9498b15d3b4e415cb6ef015ba6e6315af65f1158287a51561a43a154b3952153fc09e1517feab14e9d80214e2d7e014db292014d6eb7414c7c3fb14c37a0914c0d43c146bdca814466a841420fefd13ea83c213e0e2a7
  | 7, 5 => 0x1e2780c41df73f721de886c51de45f961de177831db574801daeb8c11d98a19b1d85da9b1d83b5c31d826c881d81c57f1d68e5f71d2d215e1d160c6b1d1165dd1d07cbc61cfd2fc91cd93b5f1caf33921ca81a3a1ca481c01c397d011c1ffead1c193f401bc7d4b01bc210541baf8e761b9935371b8e87e31b78d4bc1b61a0cd1b55df541b52f3321b3ea0591b27d2611afecaa01ae9b4a21ac819931ac6e6c71ac6cf551ab658ae1a6b63331a6a04de1a63b4731a58a2341a4dc7a41a39c2a21a33b1c31a1f1cf019fc1ed919d2796319c7c79119c2b1f019b1d44819a917ce198916cb1980bc29196672e1192a0dd619224d721921f28d1921237f18f302eb
  | 7, 6 => 0x25685a9d250aba5724fc57bc24f59d0824f27cee24dd90d224cc78e024c9ba2d24955146241b265d23fade1623f0c29e23abbd1f23aa74da2360951f2353b18e2341f1402325c90b2314f10022d85c9a22c96b3022c7351322c4f10a229eb02f2289ec0b22805475226fd984225693612202198b21eaa96f21e6cbde21de28f921d8db4721c636b821b5c2d421a5f9682145e8492145ca59213f9045213bddeb20e249a720df43cc20cdfb2c205b0a2a203dbfd620292edb1fecb1011fd3c25f1fa565611fa432931fa23c8a1f3e5d811f3387171f3108e21f2183b71f15ac8f1f0c9a181f05df5c1ec0fa371ea663541e7be0ab1e5ad6651e2d04af1e2acf24
  | 7, 7 => 0x29ed6e3b29e942c429e188d329c478db29b291b729af2b6429a6739a2993998d2992b93229740e86296af49a2964176b29428e4b292c9652292af8b7291385ac29025cbe28e3ecc328b13185286658d0286028b1285879f128483606284514cc281a4d9f281909f62803ddcb27fcc31727df15f327d866c027d2573727c3516e27c1256227bb223c27b87eed279f070c27795cd1273e087b272630b12713cf002710b40c26f87edc26f6561a26f168c926dd32d726d0c80326beaf6f26b886cd26b1ab7426ad119126a8a45026786863265b050526396ad426146422260a164f260932412604931525eb7b5225de408525d992dc259a3137258a6ea42581e570
  | 7, 8 => 0x2f8af2362f67316b2f3c81e32f3594f12f2cdf472f20329b2f1d2f5b2efbd9642ec68d272ec30bf92eba05a82ea523322e9b5e9e2e8fba352e8a65942e45ee3b2e3b996a2e3a69332e28d5a52df013cb2dcb18752d9f970e2d93a3d72d627bcd2d618f3b2d4b28f82d4518622d3ff5e92d3e70562d19df392d06d0c22cfe0cfa2cf8cd042ce139a22cdf3e6c2cd4f0ce2cc795ae2c86b1b52c7afb6d2c58dac22c3e81882c2da7a52c009a592bfc7bed2badab652b87620c2b81626d2b43cf532b2253022b15a4b82b09ceab2afda44c2ae2f53d2aa00b9d2a9ddf912a9cb57b2a8e42722a8c3c9c2a6cf0712a5617002a4993872a430f592a14d0f72a06a6fe
  | 7, 9 => 0x34c7ff3c34a771a73481cae43481847a347c735e346f23283466ebee345ddff53453b6c5344f47aa34487e1234171dd834064f6c33da662c33d93c6b33d8677333ce134333b85c4333a8219a338e027c335d819533511330334a7e36332a82ad330bca3f330a8e3532fa2f9532e16b8932def36c32d045d132cae7bc32ba82ac32a1bcd53294f0e0328546223264f1943252e2e0324a6b8732440aae3241705c32113f4a31f5eab331752de73159aba1315024ba31389c993129ad3f3122199e30de567830d5282030b1e59a3093efd2308db847303f34b8303037e9302ca777301b2a853014f8752fec250b2fc6445a2fbf35272fbbf89b2fb9bd7a2fb1aafd
  | 7, 10 => 0x39b5e92239a3fedd39a3264a399f4d123977520139631e873961b02b3956e3ad392f38243929da4e390ed69f38ed825b38e1a69e38c8629238c6876638bbb164389f41cf389cbe363899ed183896221738889640387c22163864ee273856408c382f747e3821da663821d53c381fcf1438120974380d7bfe37d8b58137a4666c37997d533778a28c3729e7e336fb367836e2575236de7a8736c744ae36b5383e3681559c366fa27236648703364691d83644f7dd362738653619ea8d3615bd78360938793601d28435f2a55735e7486435d89aaa35cf863235bf14c3359f67e7358833f8357193a6353aa3c63536fd9035239d6d35009d3534ecd7be34d2fbb7
  | 7, 11 => 0x3f227ddf3ee6de3d3ec1acba3e8cd15e3e791ea93e3a3ac43e277fff3e0954d53df99e973de1cf0e3da1e2333d8a3cae3d820b7b3d67d4943d64e4c33d4903cd3d3e89f93d2c7c353d2562093d10cdeb3cfeefc53ce437ac3cda06bb3cd948b53cbde0b03c4154063c38e0113c346cd83c34563c3c0ce04f3bf021da3bd6ad1d3bcc8c933ba7c5f03ba5ac113b9f7aeb3b9031bd3b795ba03b754d643b5dab7f3b40a23f3b3e76333b0db0ad3b08dcd23b05d6f73af6ada23aab48ca3a9a85bd3a8cc1993a8b1a653a8512d93a822ece3a8122023a64e63a3a63374c3a5b11913a3b596f3a2d6c6239ff1f0a39fa66b039e99ade39e1752a39ddbebc39c63479
  | 7, 12 => 0x43c1fcc94397d140433f660a4336d2af432dfd824325dcc4431f7df74305883642ef746f42e7b5af42b779a34299a036428dbbfe4288da784270b5be425bc8a4424d728e424083084221143d4214fad142100287420d2e5641ec4f6f41b8ea3b41b7ba04417adc044170bcbe416abf894149098f4110f4a8410d769640d845e240c96f0f40c11d8e40bbc12740a8378340a60e3740936de14071490e406f21e940651e98405ffdff405c8f3d4052419f40455b7a4042c3c840419ef2403af74d402fc56c40120e7d400945b43ff4ef3e3fed881a3fe000373fd72a663fd62b933fd3ef6d3fca826d3fb404613f6aee9b3f55675e3f4622693f2cd2183f2afc36
  | 7, 13 => 0x4a20e91b4a0d19744a0125c049f3d2f349e8ddff49e3bfbd49e125c649d9a14a49cc486f49c3e2a949bb2fc349b6983f497e1ccf49787d014975de444939f53049148db04905a44648f6d72e48cda8094850b42847d7f35a47c3548547ba59f747a3d52347946ea94772c4c3476a5be9476086824755b8444727debc471a541a471718c446df279b46cefcc046cdf1d246c9322546c7cf0746ba812f469cb097469949b546769a764667f2b7466764c54626019546230322462000d245f6b58445b72538459774c2458207674526b408450ea01a44fe769744f4548e44e5077444cd758b44ae84d9449785304493839c4486548a445ca64c440fd5ef43eb0c06
  | 7, 14 => 0x5059633d504f4f6650490acd5036f025500139404fff2dd54ff820184fb50f3e4fa260824f9d1e774f8c57c24f7141a24f49dd644f08c8964f0494734ea817a54ea4fa1c4e9a87094e7855394e5372144e4388a54e3cd4e24e3b68614e3a3a904e18a5394e086b364de2370b4dc9c7c04dc27b5b4dace24a4d8cd6aa4d77b7814d5001c34d3c580d4d2f3d364d159afc4cfd734b4ccdf14b4ca859dc4ca1aa074c77c2484c29021d4c1fc4a74c1e35cd4c173de94c0122844bacc54f4b6978864b5e75fd4b50406a4b48acc94b2472944b226b904b17d9624b11aa524aee73794aeba8ec4ae43b454ad1055a4acde2064a9a544d4a77d2104a55e6434a44957f
  | 7, 15 => 0x570c318b5707fb6756ff19ed56f13b0e56c5d00a567ee6cd567c7f51565ed38556403068563580cb5618ad155615047155f9c36e55f6748055dc8b8955a5888d55739b7c5530a86c54fd3cee54f251df54f0504c54dad9b254d391cb54b5735e54b47b9854a9557c54a00c23548e6dd85479ade6546df95f54324e1553ca92085395ea58537c0e455377f3e6536a1507534934bd53466db8530ec13f52dbe80452ce9ec2529fbf6552943af5528ce0195281620b5257aedf5253af2952534f94523dc21151dd55d151bb2a0f518820f75184d1d45160844351501bab5136a9a35133fceb51099cc650e23594509f5416509f358a507c4096506b190f505beeb3
  | 7, 16 => 0x5d7d6e2d5d7bf2db5d71535d5d65f9355d5fdc975d5624535d48a8d45d0b15675cde0cce5cd798925cb55e505c91de815c8bac4c5c3b8dfc5c33c1815c1f443a5c098ff55bf13ab45bea2b975be9d2375bccb9a15bb357745bb301c65b796d475b3bed485ac679ad5aa8a6b95aa52f8d5a97dc395a97a4eb5a9469955a8322685a6d6fbe5a6afd255a5bc66559fcbebe59efad2e5996f4f5597bfa89595c195259483db55944bdd65936765a592f0198592ae1565927b4ea58eb4e3858e6c54658b56100588df5d9588ac935588269ee58597183582969ea57a487195795fc8d578e67bf578d26c0576d4781575675b3574ab38e5744b4ce573f8ef45727b7f4
  | 7, 17 => 0x63b3242b63939f33637c7ea66320cbf7631fb15363020dca62fa02de62dfa08f62da87e162d73fc862c7c6f4624ac82b62261eff62256876621d1ce6621bcd566202e0dd61fe39a261f427ee61d0c2e561cf8f7361ab00a961aa3368618ab60c61874d90616fe8b4613fcc2c613f4bb661176eed60fbe7f960f47f6c60d62fb160b772cb608a33c1607f1ebe60617b6c6058ad0a604693fd6042b3645fd0ae2c5fbe37825fbac6fd5fa8e5035fa001255f4ce3e85f4569945f35ba935f26c7b65ef408b65edbff035ed6a3f15ecd913b5ec5fd9a5e82f8175e618c165e5e95475e441ef45e394d3c5e13ada65e10c3f05dfe16575dd41be55da6d4765d8bf147
  | 7, 18 => 0x6a00c0a569da0c1f69b2eaed69b08c9069ac572569a9dbb8694fc71e69250df3691674076909bb4668c3ac2e6885fcc068439ee9682efe61682a009568240a4468201ef16805cfb767fd902f67891a30678524796752b39f6732258167240676671066ce66fc748866e5ae6b66c9726066be8369669a488666730cef664cb0966644c8f8663dd1146639b9d8662ac0886624d4f6661f8dfe661dc2cd6617db0a6604d30365d6d88f65b3f9f765a826966566e4ba6557fc2665438d01653364ff6532bf6465291588651506a464e6ab0264aa6b4464a0c73f646b28aa64548dd864497e5c643ac4066433ac9f642e54a0642d74f3641ca4e763fb6a7f63bad2eb
  | 7, 19 => 0x71ca317b71b7c8f2719e52c17193d4b1718aa31d7166cf877158096d70f943ac70b68b1c7066c393705b5d9f701d07ab70120e997005f1236fa5e0046f6a8dfb6f43e1be6f13e0ff6f0f44366eeb6aab6ee8713b6edb0ec36eb15a926e9f9b6a6e8379536e5e503d6e5a9f856e4e17c76e16b7eb6de93f766dd08b0e6db3cd8b6d916c166d7b510a6d79ee906d483b2f6d35546a6d26125d6d1c77766d18b8176cd622c66c96b4706c4b6e046c49cc986c48199a6bf899566be5d2566be1bd3a6bd3e8686bcb63fb6bc67ad66bb065b86b76748c6b67104f6b3934176b22b0746b0959bc6ac5c8b56aa508c56a91b37d6a7ff6686a4320db6a2e06a76a082914
  | 7, 20 => 0x78925775785ca3c67850917f78493a7f7847c1c27812897277ae3ab077abcbfa778f984b777d8546777652a77753784a7723c8d077231e6a771f39f876f0de3376f096c376ef06c676e1a5f076c379d576b871ac769ee490769e1cc8768e81ea76549099764e5f6176374491761a42bc7613d46a7605ae21756b3d6c75576ffc7554e386753f33837539d26974f8ca7a74d57dbf74ae2b347485a1e974789e64746a0e0a742e54c37408724473fa28f273f993ba73ea5b6e73e9209c73d644c773be3a8b73823427736647aa72f1b40272e9411572bb7e8b72b28339727718da726a4e01724693b772464c2172301b0f72286c4f721cd8337218e0f571d8f934
  | 7, 21 => 0x80b2da9b806266ad805e0fe97fe1a60d7fdec0a27fca544a7f75ea277f65878f7f6323277f24c13b7ef775487eeeae697edbceae7ed1cb467e912cbc7e4b58517e1a8a567e05acff7dfb85ac7de29e817dd765af7dd747b97dc60fd37db173387d99a3907d45c82b7cea112d7ce7e2b17cb560537ca8786f7c69c65e7c4bfba17c1abb197c170b2e7c08287b7bf0d3337bbbac317b86605a7b665f577aface357ae6a9707abf348a7aa157477a8ef3507a7f40357a5b787a7a2bf43679f05dc079e15a2879d3e13a79cce61979be6a9879a30aba79952bdb797abaaa79717a8d797004af796fc1e1796deb3979684f627961f72778e9916b78e4358b78b54ae2
  | 7, 22 => 0x8903714688f823fd88ede02888e50a9488d9be1688a4fc21884d6a8e8824c1658816e9498803a86a87e75edb87e13aa087de9c8a87b2ceb4877779c387648dca872dc005870803528703169686fcb5f186bb689486bad95e86b63847869b7594867726a18625e7dd861a00e985a623a08527bd3a85184ada84f50771849e475c8475b533846b9cfe84594c5e8450d9fa844c64498433dbed840799a683fe99eb83e740ff83c7f1fb83a2fded838341f4833df9038323a63b82fee33982de711782de0bf882d3eb9982c52c6282b3ae80829ec1d68267361782585f94821853fe81fd9d3781e62af8819be999818c8a24817f943c817be6a281303d8c8123ee88
  | 7, 23 => 0x947d9aae94302b6c942a4f2093f91dd793f42b8d93f094929365df5093602c46932ed1f79322c346931be89e92efcbe3927d83849222139b921c7d4492002a6a918c7c03915bff5891503a30913e5b3c90e225fa906d26119049058a9040bef49022657e90061e318fe77d2d8fb5d0938fa972eb8f80fc978f76ecae8f74f0a98ee425888ed973b68e9fcbf58e7679718e27cd4e8e2302ba8e1426838dd7584d8dc0b2f38d94f5ad8d5eaaf98d32e83b8d1d99c48d1b84e68c51c7138bc68b508b8fda438b4da15b8b3f92418b1fd6d78b080e6a8ab20f158aa44b2d8aa3b04f8a772a858a59424c8a4b2c5689ba9fdf89b9a4c58983c1878974814d894ebb5e
  | 7, 24 => 0x9e5adc459e519fea9e4b2ef19e418da49e1370af9debfd949d9a91c89d72dd149d65b4079d6568569d609f369d413caf9ce7c5ba9c9ccc9d9c625b659b74bd5f9b6cf8b59b5bed5b9b42e6359b34b1219b1664259af887159ae5da449aca79e39ab52eeb9a6914bc9a07492d99eaf18f99d6685399ce129a99c74fee99bed3f99978ab00994e76d09944066399265abf990f019198e2892c9848d5ba9848610497f3060497ec88bb97c54e4097a4f38797a4a4a19775269297708ba5974dbfb4973c231c96f60d79969aeb729630ff51960bb76c9608f40395a7bcd39595a4cf951cbb3294d7782194d4832a94b8834e94ae151694ad81c794a0b6d3949f308d
  | 7, 25 => 0xa7b45be4a748d152a6bd0c77a6910249a65c3616a61dcadfa6193286a5f12d82a5d7b751a5b36a13a5ae8250a57519cca54a6a95a5141b3ba4ed51b6a4c4fe3ba4ae7b11a494c22fa4943c01a44634c2a411e8baa40b50aca3f2435da3c1ab4ba39ec2eea390017ea3814b1aa37a73fba33926f8a32cb193a3219133a3098384a2f7e86ca2d3422fa2b3fd1fa296a4d8a26534afa2602c83a1f16defa1a0b745a1662bafa1537f86a13f99cfa0f696e5a0d05094a099d7c2a07b3991a041465da0178350a00b64c39fc0bc2f9fada3039fa7e8e29f7f6c789f7298a79f281e6a9f22e88e9f1c706f9efaea139ef41ebc9ed600aa9e93ebe99e64b9f29e5fc6b7
  | 7, 26 => 0xb4efd615b4a840e1b43f5990b435aab5b432738eb4309820b41b0a9db40478deb3e7728fb3b09514b36df0c6b30843b8b2dacd1bb285abbdb27560a3b24f00d3b1ff7463b1f9e3e0b1eb36f8b1bbd0a8b18c7b6cb18a5954b0e1dcffb0d5dbb4b08e74bcb077cf95b06379a0b02ed722b028f5a0b0231954b017831caf9cc68aae948155ae93ac3bae1bf85dae18ff3dae064aa9adf1a5e6ad58a5d0ad3bbe89ad096b8baca9b064ac9944f7ac7b9e87ac59c64aac54c35bac41cfbeabbd86cdab9f69a8ab55c58dab555734ab227451aae6feafaaacc2cbaa90e0daaa75a9a3aa43ea8eaa1f6e87aa090333a9647ee6a9501df1a8e78fc4a89eb231a828f69b
  | 7, 27 => 0xc219e413c20018d3c1f9e755c1ebf1e0c1a3757dc154e976c1041042c088640ac019afebc0171c7cbfa41077bf8705ebbf662c09beffe354befa2055bef0b2a0bece32d5bec33186bec0a575be51e5eebe4be64fbe3add0dbe269a7bbe110a0dbd9159b9bd7e86ebbd6a8f7fbd686373bd386403bd376e02bd2fc437bd1c3529bceb8a3dbcdd2ef2bcc91ac8bc87e6edbc7e8f37bc0c7999bc042ef7bba66d37bb80d0edbb4177cfba558546b9fe2647b9e4f0ccb9df77edb91d4ce9b90994d0b78864c3b7694f48b75d88c1b7186549b6f964b2b6be7634b69c07f9b691c424b66e795fb62922e8b6251136b623fb60b60f96a1b5e82352b593ef12b4fc8e64
  | 7, 28 => 0xcc6e82bfcc5ce581cc5be40acc577fb2cc1a159bcbedcfe9cbd798ffcbb9f257cb5221cfcb46a5f8cb2f7209cb22d64bcb20c46ecb099803cb09853fca8e6379c9f4ae78c9be5be9c9bdabcac9a3b4fac996b3b6c96f57afc8d8951dc82aa73ec7d22c68c7bdffc1c7b65101c7914283c75d9bc3c7327c7fc6d0b208c6a44c39c682e025c667cc40c63e6ab8c601cd67c5ff83fec5eadd1ec5c1d047c54fca04c5368674c52f7576c4e09fabc4a50f80c496691ec48fe98ec4038d0dc3e38b32c3e2d77bc3e02969c3b9c3cac398766ec3944fa3c3606443c3432490c31b6fd9c2db04abc2d42780c2b808bac2afde01c2a091e1c27c2edfc26131dec25c674a
  | 7, 29 => 0xde4eb049ddf8e307dd1abbaedd1a865bdb6940c7db4f33a9db43194adb29855cdaf2339cdaf07901da53f235da4ab022d9cc308ed9891486d96359b3d9612da7d8f65272d8811cb7d85d0165d84ccd00d803eed7d7f9e631d7a5749ed7948ba0d78c0afed7783301d76d9a26d7404b60d7272a2ed70a1d9bd70862e2d6c78025d68b73c0d5f3eb55d568b144d5583fe0d44635d3d4001a12d3a13996d3792a58d3039b18d2f75b26d2aeea40d29440d5d28d9f00d2440c1fd222b1abd1d3f658d17bf5cfd173caa4d0c5752fd028b587cfaaeb5dcf9551ebcf1f3ed4cf01a125cf010decce8ab657ce1ee8e6cddd1867cdb0a1f9cd4f96bbcd28ef85ccb4b64f
  | 7, 30 => 0xed3bc136ed2ae9e7eccef605ec8449e5ec04ee7febc0c7caeb6f4652eaf7f023eabec0cdea81aee3ea630ca9ea39f55de9f16a94e9500fafe93d2869e88e9a99e849f352e82d725ee7a75556e73f702ce7283c3de6d0b57ee65393cae5eea4cee5e351dce5cb74e9e5c2ba49e5b7261de55dcfb7e504ee61e4e88dfde491a641e4625a30e4489ffce3d420a8e3d3e65de35f42cae2e22383e2d81aade2aad18ce298b8f8e281e22ce280ec37e277b2dee232c2d0e20f79eae195a639e15042f8e1489438e1283faae1151f08e0b9173ae0800c8de01ebd33dfdba1afdf9dc7dcdf60a9c0df1659addeff409cdede789bdec1b6bdde86f571de7f46b1de74f913
  | 7, 31 => 0xfe2a185cfd7e81a8fcfeb677fcf063cefc84438afc50f767fc43d33dfc1a4b00fbe1c5f5fbe0f7e9fb4008c7fb195303fafc002efaea169efab495f5fa7d76fdfa3b31f7f9b99d75f9b835b8f96feb04f94691eaf8c7e701f8bf6874f8ba5c5ff8b72109f87e7dd9f7e68aa8f7a45692f6f01bfdf6334be5f5ab4c3ff58f108cf582e6acf5735d60f48476d3f3c06a7bf33384e5f31ff462f318916ef2f3ae00f2c41b18f2854adff20c2781f1d7f84cf1d45c2af1c51099f1b216c2f15a4793f0db47d2f053c1fdf02597d4effaa880efdd5beeefd4f348ef831902eec40f0ceebe9aeaeeb0d630ee9ef80aee622b56ee365bcfee02495bed7d44f8ed56b179
  | 7, 32 => 0xfff37a59ffcceadcff98826cff3e3073ff0db492fea58edc
  | 8, 0 => 0x11761aa81142fa411134c93410d1aa960fd4c3f50fc22fb60f8898390f3badb20edd17080e8414b20e783ebe0dfb96ef0db675560d9cbe430d9a92370d91ebc20d61f2fb0d52c9a60cf91d9f0cea20e10cc7aa850c167f100bd753a90bb2ffb10b989d440b41c7720afb5dd30acf09dd0ab7b9ae0ab0afbb0a71f9560a172c490878675807d82e3c07bd347d07af559e06ecbabd065223ce064612c7061ab28605c61dd605ad2f3405a3eb0a059e8b1705869eb105169eb004d0acec03e36454036df150033a727c02e9d44b02d5abde0296f579024a740d023f103c0198251c0188fb4b0129b75501283a1701013f360086a50c006499150027347900103def
  | 8, 1 => 0x203cd04e1fd3d3851fb72b911f608b651f3d31db1f3108e21ee4e3db1ebb13731eb3facb1e8eec381e7359ed1e1aa3ae1e17d8601e08e1531d73f5661d29fe0a1ca0b1831c53b96d1c1ffead1bea35011bde45011b8548e61b78d4bc1b325a461b2d157f1b1036f41a5d39541a2bfa9c1a0dc40d19f08aad19e3604919deb3e21979f417192a0dd61923eb0b1900f42918e3fb0a183e8305181aa94117d07b00175a929b1729918f170db67f15ff8a4715f86a801561a43a1528ba3c1415063f1413d60814121a0c13b5da6d136d10ac135211a21317dd2b12b8ab4112b8884a12ae5da3129997eb124e26351232479711ed84b711d7480611b4128d1187183a
  | 8, 2 => 0x2efbd9642eedfa852edbd6b52ea0b9112e9e70832e46479b2d770a592d6df75a2d014b912cf3c0ef2cf085992cae27f22ca821632bdd94e82ba0a43a2b48380c2b0f56702a7c85282a5e00e129e942c429c478db2964176b291abe562889888f284db2db2838c79a2775450f2774c460275958f22727707326e36c2426d2458e26aa53c326a4b5bf264ea12126396ad4262d41fb2609324125eb7b5225bece64259eb530255ffecb2485a934246ade962429651523fe6fae233e51982310763b23038dd422ea3ac022d85c9a22c7351322543c1c22521a042236825921e9d24d21a5f9682179389d20df43cc2081cc612064873a204aaf2d2046aaad203e530f
  | 8, 3 => 0x4025ca0a3ffca0873f49363a3e277fff3dff89d03df1aaf13dc32c533d8620523d0124c93cedcf813c9f3cdf3c9dc2fe3c39fd5e3bf3e2703bd0b7833bc2d8a43b3c318a3b23954e3afd7b253acd3e823a8b1a653a861c993a305add396f572d3950034038ad846e3899ed1837dd7e8037a1ed1c375fd1e83724f45b36e4026d36c744ae36b6da9236ad5160368990f73678c0eb363c57f436224d1b361b1af435d89aaa359aee6d357bcd57355e29ce354bc4fd3518dab13481847a34746a9f342cdee933d93c6b33ab0d08339be83032e7627a32e64fc5326a0621315024ba31381b073129ad3f3122199e30ccd1eb30bda81a2fc976f62fbf18df2fa1c82a
  | 8, 4 => 0x515c2919514f6454514aca6d51007c3a50c4b4ed5059633d4f9b055d4f8c57c24f717d1d4f490be64e7327324e1db72a4e00c0ea4de27c5e4de254b54dd111674dc27b5b4d2b306b4cfd734b4cd8ba054c4c79c44c1e35cd4c173de94bf147df4bc969994b62f61f4b40518f4afc5e1e4aee73794ac0774d4a6707154a0d197449d602e849148db048fa38cc48f889f848f0bd7d48ebd2aa48b0ac9d484e6acf475141bb472e33c146e1bded465e79d54609964845c07cca45179a8f44d9dfff44cd758b43cee64d43b4257143555fb0434ac032432891ef42b779a34223bdb941d9fb7841d622d341a8390641a4b5d640db2d8b4079af63405c8f3d40455b7a
  | 8, 5 => 0x6292bf226284e04362623a3562542af86129ea296001a2b65fbac6fd5f5d13a95f2a63495ec6f1c75ebcebc25e90082e5e22a7545e1657ce5e06e6065debf6475d9647d45d93d62e5d7bf2db5d6275f45d3a46645d2e415c5c9fbd605c91de815bff541c5b2acd595af03eb05a73054d5a7078f85a437adf59f223e559e5330159d66aa059d395c75992adb05943cbfb5923c1c65916f5625905159658a5f17758905d1357c3519856dbe56f568ff7f156240dff55df5df855ab6c465592bd7c558b8750557f4cd954ed1c7554b47b985316929452f2fea452acbe7d52943af5528ca242520a3fab51e81d5151d2062b51bf3f2b51bb2a0f51a4e007516924ff
  | 8, 6 => 0x77211a3f76f0de3376f0916b76eecc3f76db0b2e76bdf4b9764e5f61749b9886745a681c73a4532b73a1eeb773227b8e72739f547260e48f721cd83371be65bd70ffce1070c4152b707cee8d7005f1236fa6c90d6f3b46226ebe77696e38e6f66e1ad9ba6ddedbb86db8095f6d9b14bb6d483b2f6d2657c06cd622c66c8fa51c6c4b6e046b89f08a6b6909ce6b46b4d16b1be3666af785736a7ff6686a5eea176a510b386a4fc62d6a4f220869c031bf692e70ee6920920f68ff5c7d688d1b55683fb3fc67f1c0d36709aa6166fb4c91668c477066742ba76659a12a64ffcc4e64e30e6464cf00c564789948645092fc6347643b6336351163275f1562b43c17
  | 8, 7 => 0x8b308e208aef68758a8bfac78a18c28889beef4c897643b68968a0cb88f823fd88ede028886bb2a5881ad299876b320387080352869b7594868cb424867726a1862851b985f48e9f8549f6d285210b03850f030e8492c7cd83f048fb838341f4833df903830766bf82d3eb99828511a482739f2081b633a5806266ad7fe35f827fc0036d7fb9fc427f97da8d7f27d8097f1797dc7e1a8a567e05acff7dfd47397db1e1917d7d57bc7d776c2f7d33ff317d303bbe7cea112d7cd372a07c439fcf7ae97d0f7ab597257ab2c9087aa157477a85129f7a70b1287a2bfc5d79a4d76c7952d274791d9b417900675a785a178978493a7f77d135d07770373f7733bc53
  | 8, 8 => 0xabe5308aab681b8eaa8df529aa3f12b1aa38618daa2867c5aa21bb6da9cb11c2a9647ee6a8e78fc4a8d69abba80d4bfda8098f40a6563cc3a62fa927a4a02823a36baaf7a302d5f5a2f4f716a1f16defa1662bafa141bf77a0c045e2a00d2aa29ffd08839eab30d29e6bbe4b9d3508f49b34b1219ab47d5a9985b80798d8396998553ede97a5128c9721f5ed97012b84965f3458965531e6963c456d955a089894b8834e9396353d93602c46934043b892a6c201927d8384927a567e925c0be491bec62691b98d1291426eab906d26119011f58290061e318f78512d8e35cdb08d92f6958d7f04bb8d6fdaea8c8386ea8bedc1998bc68b508bbc73f08b8fda43
  | 8, 9 => 0xd3b34341d355d4ffd2f75b26d27a66b2d229a3e5d1d3f658d0a7e5c1d051c79bcf9551ebcf84bc20cf6e15b1ceecb93fceeb1ad8cecb96dfce6b8b90cd5fbf4fcc0b8b0bc9e65a89c9d88a90c7a9b843c5c226a0c4605fcec3935453c31b6fd9c30bd3fac2afde01c1c6e06ec1c5a5bebfa41077bf46884bbef5700abee065e9bd2744b8bc5e25f5bbec3344bad4da24bab08b31baa8a17cba2399e2b84d21e0b7610a65b713f0d0b6edc245b6be7634b69fded2b65f3e8fb59a84ddb315333eb2f03ccbb210ca3fb1b17014b12375bdb108215ab0f51e5bb0ec7e1fb0480e0daf01b67aaee65ee3aec64c0eae8d3699ae5c9576ae064aa9ad85a160ac23afed
  | 8, 10 => 0xff5a28fefe12eeb4fcf8d17ffabc44b5fab495f5faa130d0fa3b31f7f9b99d75f96feb04f8b72109f772bfb1f734b506f646c3bff637ead7f50771aef32a1730f2854adff11d8484f0f10dbef05fc8f2efeaeca8efdfd1c7ef0e3eb4ee6bbfe2eca193e2eb7a065aeaf7dac4ea72c195ea39f55de9d3bc26e8b03ee3e878be20e86f0f45e7a75556e5d4dd4ce575a6eae2f7dbbfe2f02cffe2cd10cbe25263cde07b344edfdba1afdf7fbf91dede789bde1b0bb2dd9de376dd547ea2dc240579d9eccea3d986de71d8f62b1fd8e7dfa1d87f9952d7d8277ed7c2c847d69e993fd6890d25d62ad27fd5d7c256d58853add56748abd3c1c38e
  | 9, 0 => 0xdd9de376bad4da24a6563cc3a1f16def5e22a75455df5df85059633d2eedfa851e7359ed1729918f
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0x300000544c9201000000000000000000000000100014910440301
  | 6, 0 => 0x50000010440202000000000e103000000000000c0000020480202000000380a201000000001210500000018022020000000000014000000290d201000000000000d0000000002103000000010d1070000000006103000000000000500000000121070000010440200000000000000d0000001909201000000000e107000000390920100000544c52010000000006106000000000a1070000000006108000000090520100000524c4200000000000a103000000000e103000000000000f00000038062010000000909201
  | 6, 1 => 0xe103000000000e10300000000c81030000000012104000000000a100000000000e108000000000000f0000000002103000001044020200000000c810600000544c920100000000000090000000000005000000000610500000000021050000000000005000000000610400000000411000000000006108000000000e1060000000002100000000010d1080000000006108000000000a1030000000000014000000000000b000000480a2010000000000005000000000a10000000544c920100000000851070000000012103
  | 6, 2 => 0xa103000000380a200000000000a104000000000000a0000054485201000000000e1040000000081107000000001210300000000021070000003802201000000000610000000000061040000000000000000000000e10700000038022010000003806201000000000a100000000000a104000000000a1060000000012104000005348420100000104402000000000104100000000000e10200000104402010000000085107000000000000c0000000000005000000000e10500000000121030000003802201000000010d108
  | 6, 3 => 0x1044020200000000121070000000081107000000000a106000000000210500000000411020000004802200000000000e103000000000a1070000000100103000000000610400000000061030000000000000000000280220000000504c8208000000000610500000000c41030000010440202000000000210300000304c02000000000000014000000380620000000000c810600000000401020000003802200000000010d10800000524402010000054402201000000000210500000000c8105000000000000a0000000012104
  | 6, 4 => 0x70000002806200000000010d101000000000000a000000000e10300000544c8206000000001210600000424c02020000010440201000000380620000000000000060000000000000000000000610300000000c9101000000000000a00000001001030000000000003000000380620000000544c8206000000001210400000424402020000000002103000000001210400000324c8200000000000000a000000480a200000000000210200000000021050000021484202000000000210500000000121030000000000014
  | 6, 5 => 0xe1070000000006107000000000000b00000544c8205000000000e1050000002802201000000000000a00000000121030000000012107000000001210600000048062000000000000010000000000a103000000000a1070000054440200000005444020100000000000000000054402201000000000e104000c9514c8301000000280620000000000c9101000000000e105000000000000a00000028022000000010440202000000180220100000038022000000054402201000000000a10300000018022000000000000010
  | 6, 6 => 0x544c8205000000000000a00000038022000000000002106000000000e1040000001802200000000010d10700000000121070000000000010000000000e1010000002905201000000000e10400000324c82010000050484201000000000a103000c9504c8301000000380220000000000121060000000000006000000000001400000320c420300000514802010000002905201000000000a10400000000c910a000000010c10000000000c9102000000000210700000524402010000002806201000000000a1040000000000010
  | 6, 7 => 0xa10600000214842000000000085107000000000e104000000190920100000000000070000005908200000000000e1050000000006103000000380a201000000000210700000104402000000000002103000000590920100000540c920000000324c8201000000000000600000544c9201000000000000a0000000012103000000000a10000000000000070000010440200000000000a10400000000c810500000544022010000001802201000000000000a0000002806202000000001210300000000061050000000002106
  | 6, 8 => 0xf0000000000009000000000210400000000021010000000000003000000000001000000000061050000054402201000000000610000000000c810700000000121070000000012104000000000001500000544c9201000000000000a00000514c82070000000002107000000000e10400000524c02000000003802202000000000e1070000000012104000000010d108000000000000a0000052440200000000000a10300000540c9200000000380a2010000050012201000000000610300000000021040000000000005
  | 6, 9 => 0x4806200000000380a2000000002806200000000000e104000000000000a000000000000a00000000811070000053440201000000000e104000000000000a0000000012107000000000a10000000000061050000000000005000000000210100000424c4202000000000000100000540c92000000000002104000000290d201000000480a200000000000e10300000000000140000000000006000000000a10000000544c520100000540c92000000054402201000000000610300000514c820100000000061030000003806201
  | 6, 10 => 0xe1030000000909201000000380a20000000000000070000010440200000000000000d000000000000a0000000006104000000000e1030000000000004000000380a20000000000c810700000544c820500000000021070000021484200000000000210500000324c820000000000c910a000000000210300000000000140000000002104000000000210400000424c42020000000000005000000000210800000324c82020000000002107000000000000900000000021040000000012108000000000e103000000000e103
  | 6, 11 => 0x210300000000021030000000002104000000000210800000000000140000001802201000000004010000000000021000000000012103000000000001400000018022010000000108100000000000e106000000380a20200000524c42010000000006103000000008510700000000000140000053105200000000000e10700000324c820000000000021050000000000010000000000610700000000c81060000043108200000000000e10400000000000030000000012103000000001210300000000121080000054402201
  | 6, 12 => 0x2103000000000000a00000000021030000004802200000000010d1070000000006101000000000e107000000000000a000000008110700000000000140000000012107000000000210300000000121050000000081107000000000e10400000000061010000000000014000000000000d000000010d1070000000006107000000000e10300000524c42000000000000005000000000000d00000434c12010000000000005000000000000a000000000000e000000010010300000540c920000000324c82020000001802200
  | 6, 13 => 0x540c920000000000061070000000905201000000000210300000324c8201000000000610200000324c82000000000000000000000000000300000000061050000000012104000000000e103000000001210500000000061070000001802200000000000000f00000000000090000000000007000000000000000000000000030000000000007000000000e107000000380a201000000380a200000000180220000000504c8201000000590520100000000121040000005905201
  | 7, 0 => 0x21000000000000007000000000a1010000000012105000000000e1000000000000000000000000210000000000c51010000000000000000000000610100000000c1100000000000e1080000003802201000000000000000000000021010000000000008000000000210100000000061020000000012107000000000000000000000061010000000000000000000000210600000000411020000000081102000000000210400000000061050000000002104000000000000400000000401010000000002103
  | 7, 1 => 0x50000000000005000000000001000000000121070000000000009000000001210400000000000030000002802200000000000610000000000021010000000000006000000000000300000524402000000000000004000000000000700000000000010000000000003000000000a100000000000000500000000c4100000000000e10000000304c02000000002806200000000000a1020000000002108000000000210600000001091010000000000003000000000a101000000000210100000000000060000000000007
  | 7, 2 => 0x324c8201000000000000300000000000040000000000007000000000000400000524c02000000000006101000000000000d000000000000300000000061060000000000006000000000e10100000000061020000000006104000000000210200000000000060000000002105000000000a1040000000002104000000000a10500000000000030000000000004000000000a108000000480620000000324c82000000000000014000000000000300000000000030000000000003000000008110000000000000030000000006106
  | 7, 3 => 0x70000000002100000000000a10300000000000050000000041102000000000e100000000000210500000000000080000000000003000000000000500000000121070000000002103000000000e1050000000002101000000000610600000000000000000004802200000000000000a0000000085101000000000a105000000000000a00000000c0100000000380620000000000000000000000006103000000001210500000000411020000000000001000000000210400000000411010000000000004000000380a201
  | 7, 4 => 0x500000324c82010000000000004000000000a103000000000a1000000000000005000000000210400000000021010000000012103000000000a10300000000061000000001802200000000000a10300000000021080000000006108000000000610400000000000070000000006103000000000001400000000c810500000000061000000010440201000000000a107000000000e105000000000000600000000c91010000000002104000000000000400000514c8201000000000000400000000061060000000000003
  | 7, 5 => 0x4110100000000000040000000000015000000000e10000000000c8105000000000000300000000c11020000000002100000000000a1080000000006102000000000e10400000000c8106000000000e1030000000006107000000000e107000000000e10100000000000070000000006100000000000000900000524c4201000000000a1010000000012101000000000000400000018022010000000000003000000000a1010000000012108000000000e106000000000a10800000038062010000000041100000000000e100
  | 7, 6 => 0x8000000000000a00000000000070000000002101000000004110100000000061000000001802200000000000000300000000c1101000000190c20000000000c8107000000000000000000000000060000000000000000000000000100000000c81050000000000010000000000000700000000061040000000000004000000000a1030000000000006000000000000800000000000060000000000004000000000a104000000000000000000000000030000000000004000000000210300000000000080000000002100
  | 7, 7 => 0x6103000000000a1000000000000006000000000000a00000304c020000000000021000000000000003000000000000600000000000020000002802200000000000000300000038062010000000002100000000000a1040000000000003000000000000800000000121030000000002101000000000e1060000000006103000000000000f0000000006108000000000000500000000000010000000041102000000000a1040000000000007000000000000500000000000070000000002103000000000a1010000000108100
  | 7, 8 => 0xc4102000000001210000000000000060000000000004000000380a2000000053440201000000000610200000314c4200000000480a200000000000a10100000000c9100000000380220000000000000030000004802200000000000a10300000000c1102000000000a1000000000006101000000000a10700000324c82010000000006101000000000a10000000028022000000000081107000000480a20000000000000070000000002100000000000000f0000000012103000000008410100000214842010000000000003
  | 7, 9 => 0xf00000000c810100000000021030000000000007000000004110200000000c1100000000000a1080000000000004000000000a1060000000002100000000000a104000000000a104000000000e1070000000002107000000000000400000000021060000001802200000000000001400000048022000000052440201000000000e100000000000e1080000000000003000000008510100000000061040000000000006000000000210000000504c820100000000021000000000012104000000000e1030000000006100
  | 7, 10 => 0x4000000000210100000524c0201000000000a101000000380620100000000121050000003806201000000000000300000304c0200000000000a1060000000000009000000000a104000000000001400000544c0201000000480a20100000000021000000000000014000000000001000000000021010000000000008000000000a1070000000109101000000000a10300000000021000000000002106000000000a1020000000000003000000010d10100000000c1101000000000000400000000000030000000040102
  | 7, 11 => 0x109101000000000e10100000000000080000000000011000000000610600000000c510000000000021050000000002101000000480220100000000000030000000000001000000000210000000000121070000000006101000000001210600000000021070000000000004000000000000700000000000000000000085101000000000e10000000000c110200000000000030000000002101000000001210400000000000040000000006105000000000a100000000000610000000000c810700000000061000000000002101
  | 7, 12 => 0x21484200000000000e1010000000000005000000000210100000000021020000000000001000000000610100000304c02010000000000006000000000610100000000061010000000000008000000000e10500000000061000000000006103000000480a201000000000a10800000000000040000000000003000000000a1030000000000000000000000000300000000c8106000000000210400000000000070000000000000000005444020100000000061070000000000007000000000210500000000121000000000000005
  | 7, 13 => 0x2806200000000000000700000000c910100000000061040000000085101000000000210700000000000070000000006101000000000610200000000801000000000000008000000000a10300000000c5102000000000000400000000000050000000000005000000000a1080000054440201000000000000a0000000040100000000000e103000000000000700000000061060000000000006000000000e10700000000411000000000000008000000000210100000000c11020000004802201000000000a10100000000c1100
  | 7, 14 => 0xa105000000000e101000000000a1020000000012107000000000a107000000000e10000000000000030000000006100000000000a105000000000000500000540c920000000000021020000000000005000000000000000000000021000000000105101000000000000700000028062000000000000006000000000000000000018022000000000000005000000000a102000000000210000000000c41000000000000001000000010510100000000c91010000000006104000000000210000000000061010000000085101
  | 7, 15 => 0xe1020000000002100000000000000700000000000040000000002101000000000a102000000000000f00000000000030000000000004000000010510100000000411000000000000006000000000210800000524c42010000000105101000000000000700000000000050000000006100000000000000700000000021030000000006100000000180220000000000000090000004806200000000010510100000000000050000000006103000000000610800000000061070000000041101000000000e1040000000000006
  | 7, 16 => 0x5000000000a107000000000a100000000000610300000000000060000000002100000000000e100000000000000800000001051010000000000006000000000610800000000000080000000006104000000000e103000000000210100000000c8103000000000610100000544c8201000000000000400000000000040000000000005000000000e106000000000e1050000000002104000000000000300000000c9100000000000a104000000000e107000000000210300000000c9101000000000000300000000c9102
  | 7, 17 => 0xa1030000000000004000000000e10800000000061000000053440200000000000610000000000c4100000000000000700000000061020000000000005000000000610100000000c11020000000109101000000000e1040000000000003000000000a101000000000a1020000000002103000000001210300000048062010000054484201000000000a10200000000c410300000000000090000000040102000000000610700000000000050000000006104000000000000400000000c91000000000006102
  | 7, 18 => 0x480e20100000000061000000000006102000000000a1010000000002102000000000000a0000000012108000000480e2010000003909201000000000000300000000000040000000000000000000000a1000000000000006000000000e10100000000401000000000006105000001044020000000000c91020000000105101000000000610500000000021030000000012103000000000a1050000000002102000000008110700000000000060000000000005000000000000a0000000012100000000000a106000000000e103
  | 7, 19 => 0x10d10100000304c02010000000105101000000000000300000000000070000000109101000000000a105000000000e10300000000021020000000000004000000000a104000000000a1050000000041100000000000000d0000000000005000000000a1060000000000003000000000210200000000c5102000000000000400000000000030000004806201000000000a10700000000061070000000012104000000000a100000000000000400000000000080000000002101000000000210100000000021000000000006108
  | 7, 20 => 0x40000000000005000000000000a000000000000700000000000030000000000007000000000000600000000000100000000000004000000000000100000104402000000002802201000000001210300000000c1102000000010510100000000021010000000000014000000000210200000000000030000000012100000000000000000000000c410300000000000080000000006103000000000000f000000000e100000000000210100000000c410000000000000060000000000008000000000000400000000c5100
  | 7, 21 => 0x14000000000e10600000000000010000000000009000000000e100000000004110000000000021070000000002104000000000001500000000000140000000002106000000000e106000000000a1000000000000003000000000a108000000001210400000000061070000003802200000000000a1000000000006107000000000e107000000000610100000000021010000000002101000000000a10100000000000100000000081101000000000a1080000000000004000000000001000000214842000000000040100
  | 7, 22 => 0x28022010000000109101000005244020000000000061010000000000009000000004010000000000000100000004806201000000000610600000000061050000053484201000000000000600000028062010000000006107000000000000a000000000000900000000000020000000006104000000000210200000000000100000000000006000000000a101000000010c100000000000000a000000000000600000304c02010000000000007000000000a101000000000000400000038022000000000000008000000000a103
  | 7, 23 => 0x21484200000000000610100000540c920000000000121010000000000014000000000210000000000000000000000000005000000000000d00000000000080000000006101000000000001000000324c8200000000000e10400000000000080000000109101000000000a1030000000006102000000000000800000000061030000000006103000000008110000000000000110000000000004000000000e101000000000a10600000000000000000000000003000000000e103000000000001300000000000070000000000003
  | 7, 24 => 0x1400000000000060000000002104000000000210100000000000090000000000009000000000000600000000061030000000081101000000000a1060000000006100000000000000300000000851000000000012108000000000e108000000000a102000000000610300000000061030000000000001000000000000300000000061010000000000003000000000000300000000061080000000012103000000000e107000000380a2010000000002100000000000a101000000001210400000524c02000000000002104
  | 7, 25 => 0x21020000000002107000000008110100000000021070000000012106000000000610000000000c9102000000000610600000524402000000000002101000000000000000000000411070000000006101000000000000000000304c02010000000012101000000000e10000000000121050000000000004000000000210700000524c42000000000002108000000000000300000000061010000000006102000000000000a000000010c1000000000000004000000000e101000000000610200000000411010000000000001
  | 7, 26 => 0xa10000000104402000000000012106000000000610500000000000000000000006107000000000000300000000c8105000000000e10100000524c02000000000002103000000000e106000000000e10000000000121010000000000008000000000e10100000000000040000000000003000004310820000000000000000000000000000000000000000300000000c110200000000000060000000006100000000000000a0000000000005000000000a1060000000012103000000000e10300000028022010000000006104
  | 7, 27 => 0x8000000000e100000000004010200000000121000000000002103000000000000100000000021070000000000003000000000210800000018022010000000040102000000000000d0000000000007000000000210500000000061010000000012108000000000a10000000000000060000000002103000000000000200000000121010000000000001000000000000800000000411000000000000006000000000610500000000c110200000000000040000000000004000000000a103000000000a101000000000a101
  | 7, 28 => 0x140000000000003000000000a100000000000a1030000000006100000000008010200000000000070000000041101000000000a10600000000021030000000006107000000000000600000000061000000000000007000000000610100000000021040000000002100000000380a2010000000006104000000000e101000000004110000000000061070000000000008000000000000000000000c510200000029052010000000006101000000190d2010000000006101000000000e10100000000000030000000006106
  | 7, 29 => 0x1051000000000084102000000000e10200000000000070000000000004000000000a1000000000006100000000380a201000000000a10100000214842000000000104100000000000000300000018022010000000000004000000000000400000000061030000000041100000000380220100000304c0200000000480a2000000000000007000000000210800000000c91020000003802201000000000e1000000000002104000000000610100000104402000000000000006000000000000600000000000050000000006101
  | 7, 30 => 0xa10100000000121000000000000003000005244020000000000000030000000006100000000000e1000000000012100000000280220000000000c810600000000c8100000000000000900000314c42010000000000013000000000a1040000000002100000000000210300000000000030000000000000000000000000a000000000e103000001044020100000000000000000000006100000000001210300000000411010000000006108000000000a100000000000e106000000000000300000000061070000000000001
  | 7, 31 => 0x50000000006106000000000000500000524c0200000000480a200000000000210100000314c4201000000008510200000000021030000000041100000000000001400000000c4100000000000000600000000000060000000000007000000004110200000000000080000000000003000000000000300000000000030000000000009000000000210600000000000070000000000003000000000000400000000000090000000000007000000000a105000000000000300000000121060000000002100000000000e106
  | 7, 32 => 0x40100000000000610100000000121030000000006108000000000000a000000000e100000000000a101000000001210800000524c420000000000c4100000000000210000000000061040000000000005000000000000000000000c410000000324c8201000000001210800000000000060000000041101000000000000300000000c0102000000000000300000000000150000000000000000000000e10800000018022010000000002104000000180220100000000841020000000002106000000000a1010000000006103
  | 7, 33 => 0x524402000000000006103000000000a1010000000000008000000480620000000000000000000000085102000000000a103000000000a10000000000c81050000000000005000000000610000000524c020100000000021080000000002108000000000000700000000000040000000000004000000000610100000000000030000000002103000000000001400000000c810200000000000030000000000003000000000e105000000000000300000000061010000000000006000000000610100000000061000000002806200
  | 7, 34 => 0xe10500000000c810300000000021030000000000005000000000e103000000000000800000000811010000000000000000000000000500000000121000000000002100000000000000e0000000000004000000000000600000000000050000000002106000000280620000000000061070000000000010000000380620100000000021040000000000003000000190520100000000000040000000002105000000000210500000000000060000000041101000000000a100000000001210300000000801000000000000003
  | 7, 35 => 0x1400000000000100000000006100000000000a10000000000061010000000006101000000000e101000000000000400000000000050000000006104000000000210600000000c81000000000000006000000000000300000000c91010000000002101000000000210000000000121060000000041101000000480620000000000021020000000000009000000000000300000540c92000000000000005000000000000a000000000610600000000000050000000105101000000000610100000000000080000000000007
  | 7, 36 => 0x60000002806200000000000000600000000000050000000000009000000000000500000524c4200000000480a2000000000012103000000000e100000000000e1040000000000009000000000a10000000000000110000000000006000000000001100000000021080000000012106000000000a1000000000000000000000000000300000534402010000000006106000003250520100000000021010000000002103000000380a20000000000000070000000006101000000000610000000000000040000000000014
  | 7, 37 => 0x61020000000002101000000000a101000000000210000000000000030000000000012000000000e107000000000a10400000000c8102000000000000300000000000060000000081101000000001210000000000061080000000006102000000000000a000000000e101000000008010200000000061010000000000006000000000000600000000c810700000000000070000000006103000000480e2000000000000005000000008110000000000c410000000000000070000000000000000000000a10700000000c8103
  | 7, 38 => 0x6101000000000000700000000000050000000000003000000000a108000000008510100000000000080000000000005000000000e10000000000c9102000000000000400000000000010000000002106000000000a101000000480a201000000000a1000000000041100000000000610000000000c810300000000c8100000000001210000000000061050000000002100000000000a103000000000a104000000000e10600000000000030000000006101000000000a1010000004806200000000000a1060000000000004
  | 7, 39 => 0x324c8200000000000e1040000000000004000000000000f000000000e100000000000000100000000061050000000000003000000000a101000000000210600000000061000000000000006000000000e102000000000a101000000000a1020000000000004000000000000400000038022010000000012105000000000e105000000000a107000000000610400000000000030000000909201000000000000a0000000012107000000000000a000000000e107000000000a10400000000061080000010440201000000000000d
  | 7, 40 => 0x210800000000021050000000006100000000000001000000524402010000000002108000000000610000000504c4201000000000a10000000000c81060000000000003000000000a10000000000000040000000000000000000000000700000000021080000000000007000000000210100000000c51020000000000004000000001210400000000061010000000041100000000000000300000000000030000000012103000000000a105000000000e10000000038022000000000002101000000000000d0000000006101
  | 7, 41 => 0x610000000524c02010000000105101000000000a1000000000000013000000000a10100000000000070000000002105000000000000d000000000000300000000121000000000000004000000000000600000000121010000000000005000000000210000000000c5100000004144120100000000c910100000000000080000002806200000000000000000000000061000000021484201000000000210300000000c91000000000000003000000000e1070000010440201000000000210000000000801000000000012104
  | 7, 42 => 0xf00000000061000000000000005000000000a1070000000000007000000000610000000000061060000000000005000000000a100000000000000800000000061000000000000000000000000e108000005244020100000000000010000000006107000000000a101000000010010400000000021030000000000014000000000e1030000004806200000000004110000000000411010000000000008000000000a107000000001210500000000c81000000000000004000000000000f00000000061000000000012105
  | 7, 43 => 0xa102000000000000300000000411020000000002103000000001210300000000000040000000006101000000000e1030000004806201000000000000300000000411010000000006107000000000210000000214842010000000041102000000008110100000000c51000000000085101000000000000300000524c02010000000002101000000000000000000000021070000000000003000000000000700000000c8106000000004010000000000000060000000105101000000000210400000000000030000000006103
  | 7, 44 => 0xa101000000000000a000000000a106000000000a100000000000210100000000061010000000002102000000000e1040000000000006000000480620100000000c8107000000000610100000000000030000000012101000000000210800000000000060000003908200000000000e1010000000012104000000000a102000005244020100000000000080000000002104000000000a1020000000002103000000000000400000000000050000000000008000000000a104000000000e103000000000a1010000000000007
  | 7, 45 => 0x800000000801000000000000004000000000a10200000000c1101000002048020100000000121040000000002101000000000610000000000000000000000006100000000000000800000028022010000000002101000000000610000000000000080000000084102000000000a1000000000000005000000380a20000000000000000000000006107000000000a1010000000002100000000000000300000524c020100000000000030000000002101000000000000300000000000050000000000006000000000000f
  | 7, 46 => 0xd000000000000700000000061010000000002105000000000210100000000021030000000002103000000000000d0000000002107000000000a10800000000061010000000000006000000010510100000000121040000000000008000000000610000000000061010000000000004000000000000300000000061030000000002105000000000000600000304c02010000000000014000000010c100000000000610500000324c82010000000012104000000000000300000000401010000000000004000000000e104
  | 7, 47 => 0x4000000000610200000000121080000000040100000000000210100000000c810300000534802000000000000006000000000000300000214842000000000002101000000000000600000000c010000000000000050000000000003000000000210100000000021030000000000005000000000000400000000021020000000000005000000000a101000000001210700000000c91010000000006101000000000000300000000000050000000041102000000480220100000000c810200000000121000000000000007
  | 7, 48 => 0x210800000000c810600000000000040000000002107000000000000d000000000a1070000000006103000000000000300000000061010000000041100000000000000700000000c1101000000000610200000000121010000000000007000000000001200000000c9101000000000210200000000021000000000006102000000000000300000000021020000000000006000000000610200000000000110000000000003000000000e10700000000000030000000002105000000000000700000000000060000000002104
  | 7, 49 => 0x40000000000005000000000000400000000000040000000000001000000001210500000000021080000000000006000000000e1030000000000006000000000001400000000000050000000002104000000000000800000000061020000000000007000000000000400000018022010000000040100000000008010000000540c9200000000000000700000000000040000000000008000000000e1020000000006104000000000a104000000004110200000000000010000000000006000000000a1050000000000000
  | 7, 50 => 0x12101000000000000500000000000030000000000003000000000210000000540c920000000001011000000000000007000000000000300000000021030000000012104000000000000500000000121070000000000003000000000e101000000000e1040000000006100000000001210600000018022010000000084102000000000000300000000c91010000000000000000000000000400000304c02000000000002101000000000610100000000000040000000002105000000000000700000524c42000000054041201
  | 7, 51 => 0x6102000000000000800000000000010000000085101000000000000100000000000050000000006100000000000e1040000000041101000000000000400000524c42000000000006107000000010d10100000000061070000000000004000000000610100000000021010000000002104000000000000900000000000040000000006107000000480a20000000000061070000000000003000000480220000000000121000000000000009000000000e10300000000c1101000000000210600000000000030000000000000
  | 7, 52 => 0x3000000090c20000000000c910000000000021000000000000003000000000000400000000000030000000006100000000000e1030000000000003000000000a105000000000e1040000000000014000000008110100000000021070000000040100000000000000300000000061050000000000003000000000a1060000000012107000000000000400000000c81000000000000000000000008510700000324c82010000000012107000000000210000000000c4100000000000000800000000061050000000006100
  | 7, 53 => 0x4110200000000c110100000018022000000000002102000000000000300000000061000000000000003000000000e106000000000001400000000411010000000002101000000001210500000540c920000000514c020100000000c81020000000000001000000000000700000000000030000000000008000000000e103000000000e100000000000a10600000000000030000000000003000000000e1030000003806201000000000e1060000000000006000000000210400000000021080000003806201000000000a104
  | 7, 54 => 0xc1101000000000000300000000021070000000000007000000010010300000000000010000000002106000000000210300000000c01020000000000003000000000610300000000000040000000000001000000000000a000000000000400000000000010000000041101000000000a10000000000000030000000002104000000000a105000000010010000000000021040000000002104000000000000300000524c420000000000000030000000000014000000000610000000000c51000000000012103000000000a100
  | 7, 55 => 0x90000000012108000000000000400000304c0200000000000e10600000000121040000000006106000000380a2000000000000007000000000000700000000c1101000000000000300000000000110000000006105000000000210000000000021010000000105101000000000e1000000000000008000000001210300000000021000000000000004000000000000400000000061080000000000007000000000e10100000000121060000000012105000000000000400000000c5101000000480a2010000000002104
  | 7, 56 => 0x2100000000480220000000000000070000000002107000000000a106000000000e108000000000e10100000000061000000000002100000000000a10000000000000010000000006106000000000e10100000000000050000000000009000000000000300000000121010000000006100000000000a10300000000c51010000000085101000000008110100000000c810100000000000030000000041101000000000a106000000000210200000000c81000000021484201000000001210300000000021010000000000003
  | 7, 57 => 0x12106000000000000000000000000030000000084101000000000a10000000048022010000000085101000000000000800000000021000000000006100000000000210200000000000060000000002102000000000e1030000000041101000000000000500000524c0201000000000e102000000000000300000000000050000000000008000000000000400000000021040000000109101000000380a20000000000000040000000000004000000000e10300000001091010000000000001000000000000b0000000000007
  | 7, 58 => 0x6108000000010910100000324c8200000000000610200000000c910100000000061010000000041100000000000000a0000000002100000000000000400000544402010000000000004000000000a103000000000610300000000061000000000081100000000000000900000048022010000000000003000000000000600000000000070000000006101000000000000400000000021010000000002105000000000000300000324c820000000000000050000000109101000000000210000000544402010000000000000
  | 7, 59 => 0x70000000002108000000000e10000000524c42010000000000004000000000210200000000000050000000006101000005444020100000000c810600000000c9101000000000210300000000c9101000000000610500000000000040000000002105000000000000300000000000040000000000007000000380a20000000000061030000000000007000000000610300000524c420100000001091010000000000003000000000000f00000000000010000000012103000000000000500000018022000000000000003
  | 7, 60 => 0x61010000000000003000000004110000000000000070000000012103000000000000500000524c020000000000021000000000002100000000000610000000000000090000000000009000000000a10200000000c91010000000000001000000000000900000000000140000000002106000000000000800000000061000000000000009000000000e1040000000002101000000000000300000000000090000000000004000000004110000000000021000000000000004000000000000000000000021000000000002103
  | 7, 61 => 0x61040000000000003000000004010200000000061000000000002101000000000000f000000000000300000000c910100000000411000000000002100000000000e102000000000210000000000021050000000000014000000001210100000000000130000000006102000000000000700000000000010000000002103000000000210100000000401000000000000004000000000000800000324c820000000000000040000000002101000000000210500000524c4201000000000610100000000000040000000006100
  | 7, 62 => 0xe104000000000000300000059052010000000000004000000000000000000000021030000000012101000000000610000000000c51010000000000000000000000000100000000000030000000006103000000000000100000000021030000000000001000000004110200000000061050000000002101000000000e1040000000002101000000000000100000000c9101000000000000700000000000010000000002103000000000210300000000411020000054440201000000000000300000000000000000000000004
  | 7, 63 => 0x80101000000000e107000000000210700000000000040000000905201000000000000500000000000080000000012107000000000210200000000c81000000000000000000000004110000000000121040000000000003000000000210000000000c810000000000000070000000000003000000380a20100000000000000000000041100000000000210100000000021050000000002101000000000210000000000121040000000006101000000000000a000000000e1040000000000004000000000a1070000010440200
  | 7, 64 => 0x480220000000000000040000010440201000000380a20100000000021000000000002101
  | 8, 0 => 0x4110000000000000090000000000003000000000610000000000c910100000000c4101000000000000600000000000060000000000003000000001210100000000000030000000000008000000000000700000000000080000000000003000000008510100000000c410000000000000050000000000005000000010c100000000008410000000000000050000000105101000000000a10000000000000000000000000000000000000000300000000000010000000000010000000000000800000000121010000000000001
  | 8, 1 => 0x5000000000000100000000c91000000000000010000000000000500000000411000000000000002000000000000400000000000020000000000003000000000000700000000000010000000000005000000000000600000000000050000000000002000000000a1010000000000007000000000000400000000000050000000000003000000000000700000000000020000000000004000000000000600000000061000000000000007000000000000400000000c4100000000000000500000000000060000000000008
  | 8, 2 => 0x20000000000005000000000000700000000c51000000000000000000000008110100000000c01010000000040100000000000000300000000000000000000000004000000000000600000000000010000000000006000000000000800000000000010000000000002000000000000700000000c0101000000000000200000000801000000000000004000000000000000000000811010000000000003000000000000000000000c110100000000000080000000000011000000000210000000001081000000000000004
  | 8, 3 => 0x4110000000000000010000000000008000000000000000000000000080000000000003000000000000100000000000000000000000007000000000e10000000000000000000000000004000000000000100000000000010000000000007000000010d101000000000000600000000000060000000002101000000000000600000000000070000000000007000000000000300000000c410000000000000060000000000005000000000000100000000851000000000000001000000000000500000000000000000000000004
  | 8, 4 => 0x8410000000000c810100000000000070000000000000000000000000300000000000030000000000003000000010c1000000000084100000000000000900000000000010000000000010000000010410000000000000080000000109101000000000a10100000000000030000000000003000000000000700000000000000000000000006000000000000f00000000c810100000000021010000000000007000000000610100000000811010000000000004000000000000300000000000020000000000001
  | 8, 5 => 0x300000000000000000000100100000000000610100000000c5101000000000000100000000000000000000040101000000000000100000000000010000000000000000000000000100000000000070000000000005000000000000700000001041000000000000013000000000000300000000000000000000002101000000000000400000000000060000000006101000000000a101000000000000300000000000050000000109101000000000210100000000000030000000041100000000010c10000000000c9101
  | 8, 6 => 0x6000000000000d00000000061010000000000001000000000000000000000c110000000000000030000000080100000000000000000000000000140000000000001000000000000100000000000030000000000005000000000000300000000000100000000012100000000000000500000000000040000000000006000000010010000000000000050000000000004000000000a1000000000000007000000000e1010000000000004000000000a1010000000105101000000008510100000000000030000000000004
  | 8, 7 => 0x1100000000000050000000000004000000000000000000000000030000000000000000000000000500000000c110000000000000030000000000001000000001210000000000c4101000000000000800000000000000000000000003000000010410000000000000010000000000003000000008410100000000c8100000000000000800000000000020000000000008000000000000100000000000040000000000008000000000a10000000000000020000000000003000000008010000000000000000000000006101
  | 8, 8 => 0x3000000000a10000000000000000000000000006000000000000600000000841000000000000004000000000210100000000000040000000041101000000000000000000000000000000000000003000000000000400000000000010000000000006000000000610000000000000060000000000005000000000000300000000000010000000000000000000000000000000000c410100000000000070000000000004000000004110100000000000080000000000003000000000001000000000061000000000000008
  | 8, 9 => 0x40100000000010d101000000000000700000000000050000000000010000000000000100000000000040000000000001000000004110100000000000090000000000000000000000000700000000c110000000000000000000000000003000000000000600000000000060000000000000000000000000300000000000060000000000007000000000000600000000061000000000012100000000010d101000000000210000000000000000000000000002000000000000000000000c910000000000c4101000000000e100
  | 8, 10 => 0xc510000000000000000000000000000000000000000100000000000030000000000007000000000000600000000401000000000101101000000000000200000000000030000000000001000000001210100000000000010000000000003000000000000200000000c1100000000000000200000000811010000000000004000000004010000000000000080000000002100000000000000500000000c510000000000c9100000000000000500000000000010000000012101000000000000000000001001000000000000005
  | 8, 11 => 0x500000000c9100000000000000300000000000020000000002100000000000000000000000000010000000105101000000010c100000000010110100000000000000000000000002000000000000000000001011010000000000005000000000000100000000c810000000000000040000000000008000000000000f000000000000700000000000010000000000003000000000610000000000000030000000000002000000000000700000000000000000000000003000000000000000000000000000000000000005
  | 8, 12 => 0x400000000000030000000000008000000000000800000000000050000000000001000000000a101000000000000300000000c510000000000000050000000000001000000000000600000000000030000000040100000000000a101000000000000200000000000040000000000002000000000000100000000000040000000000002000000010c100000000000000000000000c010100000001051010000000000007000000000000300000000811010000000000003000000000000400000000021000000000000001
  | 8, 13 => 0x100000000000040000000080100000000010c100000000000000400000000000030000000000007000000000a10100000001091010000000000000000000004010100000000c81010000000000000000000000001400000000021010000000000007000000000000400000000000020000000000001000000000a1010000000080100000000000000900000000000020000000000003000000000e10000000000000060000000002101000000000000700000000000060000000000000000000000e1000000000000001
  | 8, 14 => 0xc01010000000000004000000000000000000000000040000000006101000000000000700000000000080000000006101000000000000500000000000030000000000004000000008110000000000000030000000000003000000000000800000000000030000000000009000000000001000000000061010000000000003000000000000000000000000060000000000007000000000e10100000001051010000000000004000000000a1010000000000014000000000a101000000000000700000000000070000000000003
  | 8, 15 => 0x100100000000000000300000000401010000000002101000000000000300000000c9101000000000000f00000000000040000000000004000000000000000000000000020000000080100000000000a10000000000021000000000000000000000000000300000000000020000000000014000000000000100000000000040000000000006000000000210100000000c910100000000061010000000000004000000000000d000000000e1010000000000004000000000e101000000000000900000000000030000000000007
  | 8, 16 => 0x40101000000004110100000000c81000000000000006000000000000300000000000010000000000000000000000000600000000000030000000006100000000000000600000000411010000000000005000000000000500000001001000000000002101000000000000600000000c910100000000c5101000000000000800000000401010000000000003000000000000400000000c41010000000000005000000000a100000000000000000000000000040000000000003000000000610100000000c51010000000006101
  | 8, 17 => 0x500000000000070000000000003000000000000000000000000140000000101101000000000000300000000000050000000002100000000000000800000000801010000000000004000000000000f0000000000001000000010d10100000000000060000000000004000000000000d0000000100100000000000000100000000000030000000081100000000000000500000000000050000000081100000000000000300000000c810000000000000070000000000004000000000001300000000c51010000000000005
  | 8, 18 => 0x40000000000001000000000000100000000000000000000000004000000000001000000000c9100000000000000300000000000010000000104100000000000000000000000000010000000080101000000000610000000000811010000000000000000000008010000000000000010000000000007000000000000400000000000040000000105101000000000e100000000000a100000000008510000000000c8100000000000000100000001011010000000080101000000000000300000000000010000000041100
  | 8, 19 => 0x800000000000010000000000004000000000000f00000000000010000000000008000000000000300000000c81010000000006101000000000000d000000000000400000000411000000000000003000000000000600000000c810000000000000070000000000005000000000000100000000000000000000104100000000000000200000000000010000000000001000000000000400000000000000000000000005000000000000100000000000040000000000007000000000000000000000000020000000000000
  | 8, 20 => 0x100000000006100000000000000200000000000010000000000000000000000000800000000000000000000002100000000010c10000000000000000000000000007000000000210100000000c4101000000000000400000000c8101000000000000000000000c51010000000040101000000000000400000000000060000000041101000000000000100000000000040000000012100000000000000600000000000000000000000005000000000210100000000c810100000000c910100000000000040000000000001
  | 8, 21 => 0x200000000000050000000000004000000000000000000000021000000000012100000000000000700000000000030000000000000000000000210000000000000020000000006100000000000000500000000c5100000000004010000000000000010000000000000000000000a1000000000000004000000000000700000000061000000000000003000000000210000000000c910000000000000000000000006100000000000000400000001041000000000002100000000000a100
  | 9, 0 => 0x10000000000001000000000000100000000000010000000000001000000000000000000000000000000000000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 13 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_31 roots_31 8 s ws hint
  | 1 => checkCutEntry dom_47_16 roots_47_16 8 s ws hint
  | 2 => checkCutEntry dom_15_16 roots_15_16 7 s ws hint
  | 3 => checkCutEntry dom_61 roots_61 7 s ws hint
  | 4 => checkCutEntry dom_62 roots_62 7 s ws hint
  | 5 => checkCutEntry dom_55 roots_55 7 s ws hint
  | 6 => checkCutEntry dom_59 roots_59 7 s ws hint
  | 7 => checkCutEntry dom_55_8 roots_55_8 7 s ws hint
  | 8 => checkCutEntry dom_59_4 roots_59_4 7 s ws hint
  | 9 => checkCutEntry dom_31_32 roots_31_32 6 s ws hint
  | 10 => checkCutEntry dom_47 roots_47 6 s ws hint
  | 11 => checkCutEntry dom_15_48 roots_15_48 5 s ws hint
  | 12 => checkCutEntry dom_23_8 roots_23_8 5 s ws hint
  | 13 => checkCutEntry dom_39 roots_39 5 s ws hint
  | 14 => checkCutEntry dom_27_4 roots_27_4 5 s ws hint
  | 15 => checkCutEntry dom_43 roots_43 5 s ws hint
  | 16 => checkCutEntry dom_51_12 roots_51_12 5 s ws hint
  | 17 => checkCutEntry dom_29 roots_29 5 s ws hint
  | 18 => checkCutEntry dom_45_16 roots_45_16 5 s ws hint
  | 19 => checkCutEntry dom_30 roots_30 5 s ws hint
  | 20 => checkCutEntry dom_30_32 roots_30_32 5 s ws hint
  | 21 => checkCutEntry dom_23 roots_23 5 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_61 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_62 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31_32 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_48 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_43 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_51_12 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_29 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_45_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_30 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_30_32 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_63 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
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
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 7 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 7 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 7 → Z 5 i = true := z5_0
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
private theorem z6_96 : ∀ i, 96 ≤ i → i < 109 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 13 96 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 109 → Z 6 i = true := (range_split (range_split (range_split z6_0 z6_16) (range_split z6_32 z6_48)) (range_split (range_split z6_64 z6_80) z6_96))
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
private theorem z7_336 : ∀ i, 336 ≤ i → i < 343 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 336 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 343 → Z 7 i = true := (range_split (range_split (range_split (range_split (range_split z7_0 z7_16) (range_split z7_32 z7_48)) (range_split (range_split z7_64 z7_80) (range_split z7_96 z7_112))) (range_split (range_split (range_split z7_128 z7_144) (range_split z7_160 z7_176)) (range_split (range_split z7_192 z7_208) (range_split z7_224 z7_240)))) (range_split (range_split (range_split z7_256 z7_272) (range_split z7_288 z7_304)) (range_split z7_320 z7_336)))
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
private theorem z8_176 : ∀ i, 176 ≤ i → i < 180 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 4 176 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 180 → Z 8 i = true := (range_split (range_split (range_split (range_split z8_0 z8_16) (range_split z8_32 z8_48)) (range_split (range_split z8_64 z8_80) (range_split z8_96 z8_112))) (range_split (range_split z8_128 z8_144) (range_split z8_160 z8_176)))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_0 : ∀ i, 0 ≤ i → i < 16 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_16 : ∀ i, 16 ≤ i → i < 23 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 7 16 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 23 → Z 9 i = true := (range_split z9_0 z9_16)
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

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 14]⟩], 16⟩

theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by
  simp [wit, PEqualNP.MetaComplexity.Monotone2]

theorem wit_sz : wit.size ≤ 11 := by decide

set_option maxRecDepth 40000 in
theorem wit_ev : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276652168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_63.testBit r.val = (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276652168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) (pt6 r.val) := by decide +kernel

theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276652168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 11 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276652168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_63 11 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_40527_aux

theorem PEqualNP.Outside.L_meta_40527 :
  ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276652168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276652168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  exact ⟨PEqualNP.Outside.L_meta_40527_aux.wit, PEqualNP.Outside.L_meta_40527_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_40527_aux.wit_sz (PEqualNP.Outside.L_meta_40527_aux.lower s hs), PEqualNP.Outside.L_meta_40527_aux.wit_ev⟩
