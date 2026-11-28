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

namespace PEqualNP.Outside.L_meta_41076_aux

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
  forceN ((((w &&& 4294967295) ^^^ seed) * 2654435761) &&& 4294967295) fun a =>
  forceN (((a ^^^ (a >>> 16)) + ((((w >>> 32) &&& 4294967295) ^^^ (seed + 1)) * 2246822519)) &&& 4294967295) fun x =>
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
def goal_all : Nat := 0xfeeaece0faeae000
def dom_63 : Nat := 0xffffffffffffffff
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]
def dom_x0_0_x1_1_x4_0 : Nat := 0x444400004444
def roots_x0_0_x1_1_x4_0 : List Nat := [0x404000004040, 0x440000004400, 0x444400000000]
def dom_x0_0_x1_1 : Nat := 0x4444444444444444
def roots_x0_0_x1_1 : List Nat := [0x4040404040404040, 0x4400440044004400, 0x4444000044440000, 0x4444444400000000]
def dom_x0_1_x1_1_x4_0 : Nat := 0x888800008888
def roots_x0_1_x1_1_x4_0 : List Nat := [0x808000008080, 0x880000008800, 0x888800000000]
def dom_x0_1_x1_1 : Nat := 0x8888888888888888
def roots_x0_1_x1_1 : List Nat := [0x8080808080808080, 0x8800880088008800, 0x8888000088880000, 0x8888888800000000]
def dom_x1_1 : Nat := 0xcccccccccccccccc
def roots_x1_1 : List Nat := [0x8888888888888888, 0xc0c0c0c0c0c0c0c0, 0xcc00cc00cc00cc00, 0xcccc0000cccc0000, 0xcccccccc00000000]
def dom_x0_0_x2_1_x5_0 : Nat := 0x50505050
def roots_x0_0_x2_1_x5_0 : List Nat := [0x40404040, 0x50005000, 0x50500000]
def dom_x0_0_x2_1 : Nat := 0x5050505050505050
def roots_x0_0_x2_1 : List Nat := [0x4040404040404040, 0x5000500050005000, 0x5050000050500000, 0x5050505000000000]
def dom_x0_0_x4_0 : Nat := 0x555500005555
def roots_x0_0_x4_0 : List Nat := [0x444400004444, 0x505000005050, 0x550000005500, 0x555500000000]
def dom_x0_0_x5_0 : Nat := 0x55555555
def roots_x0_0_x5_0 : List Nat := [0x44444444, 0x50505050, 0x55005500, 0x55550000]
def dom_x0_0_x4_1_x5_1 : Nat := 0x5555000000000000
def roots_x0_0_x4_1_x5_1 : List Nat := [0x4444000000000000, 0x5050000000000000, 0x5500000000000000]
def dom_x0_0_x4_1 : Nat := 0x5555000055550000
def roots_x0_0_x4_1 : List Nat := [0x4444000044440000, 0x5050000050500000, 0x5500000055000000, 0x5555000000000000]
def dom_x0_0_x5_1 : Nat := 0x5555555500000000
def roots_x0_0_x5_1 : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]
def dom_x0_0 : Nat := 0x5555555555555555
def roots_x0_0 : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]
def dom_x1_0_x2_1_x5_0 : Nat := 0x30303030
def roots_x1_0_x2_1_x5_0 : List Nat := [0x20202020, 0x30003000, 0x30300000]
def dom_x1_0_x2_1 : Nat := 0x3030303030303030
def roots_x1_0_x2_1 : List Nat := [0x2020202020202020, 0x3000300030003000, 0x3030000030300000, 0x3030303000000000]
def dom_x0_1_x4_0 : Nat := 0xaaaa0000aaaa
def roots_x0_1_x4_0 : List Nat := [0x888800008888, 0xa0a00000a0a0, 0xaa000000aa00, 0xaaaa00000000]
def dom_x4_0 : Nat := 0xffff0000ffff
def roots_x4_0 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]
def dom_x2_1 : Nat := 0xf0f0f0f0f0f0f0f0
def roots_x2_1 : List Nat := [0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000]
def dom_x2_1_x5_0 : Nat := 0xf0f0f0f0
def roots_x2_1_x5_0 : List Nat := [0xa0a0a0a0, 0xc0c0c0c0, 0xf000f000, 0xf0f00000]
def dom_x1_0_x5_0 : Nat := 0x33333333
def roots_x1_0_x5_0 : List Nat := [0x22222222, 0x30303030, 0x33003300, 0x33330000]
def dom_x1_0_x3_1_x5_0 : Nat := 0x33003300
def roots_x1_0_x3_1_x5_0 : List Nat := [0x22002200, 0x30003000, 0x33000000]
def dom_x3_1_x5_0 : Nat := 0xff00ff00
def roots_x3_1_x5_0 : List Nat := [0xaa00aa00, 0xcc00cc00, 0xf000f000, 0xff000000]
def dom_x5_0 : Nat := 0xffffffff
def roots_x5_0 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
def dom_x1_0_x3_1_x5_1 : Nat := 0x3300330000000000
def roots_x1_0_x3_1_x5_1 : List Nat := [0x2200220000000000, 0x3000300000000000, 0x3300000000000000]
def dom_x3_1_x5_1 : Nat := 0xff00ff0000000000
def roots_x3_1_x5_1 : List Nat := [0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000]
def dom_x3_1 : Nat := 0xff00ff00ff00ff00
def roots_x3_1 : List Nat := [0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000]
def dom_x1_0_x5_1 : Nat := 0x3333333300000000
def roots_x1_0_x5_1 : List Nat := [0x2222222200000000, 0x3030303000000000, 0x3300330000000000, 0x3333000000000000]
def dom_x4_1_x5_1 : Nat := 0xffff000000000000
def roots_x4_1_x5_1 : List Nat := [0xaaaa000000000000, 0xcccc000000000000, 0xf0f0000000000000, 0xff00000000000000]
def dom_x5_1 : Nat := 0xffffffff00000000
def roots_x5_1 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]
def dom_x1_0 : Nat := 0x3333333333333333
def roots_x1_0 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]
def dom_x0_1 : Nat := 0xaaaaaaaaaaaaaaaa
def roots_x0_1 : List Nat := [0x8888888888888888, 0xa0a0a0a0a0a0a0a0, 0xaa00aa00aa00aa00, 0xaaaa0000aaaa0000, 0xaaaaaaaa00000000]
def dom_x4_1 : Nat := 0xffff0000ffff0000
def roots_x4_1 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]

namespace S_x0_0_x1_1_x4_0
def pairsG : List (Nat × Nat) := [(6, 14), (6, 38), (10, 14), (10, 42), (34, 38), (34, 42)]
def r1sG : List Nat := [6, 6, 10, 10, 34, 34]
def r2sG : List Nat := [14, 38, 14, 42, 38, 42]
def mpG : Nat := 0x3f
def pool6G : List Nat := [11021459269134]
def xsM : List Nat := roots_x0_0_x1_1_x4_0.map (· &&& dom_x0_0_x1_1_x4_0)
def goalM : Nat := goal_all &&& dom_x0_0_x1_1_x4_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xc35445b7
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x44440000000000004400000044000000404000004040
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x0_0_x1_1_x4_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x0_0_x1_1_x4_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x0_0_x1_1_x4_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x0_0_x1_1_x4_0 goalM u ys) : RunD dom_x0_0_x1_1_x4_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x0_0_x1_1_x4_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x0_0_x1_1_x4_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x0_0_x1_1_x4_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x0_0_x1_1_x4_0 roots_x0_0_x1_1_x4_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x0_0_x1_1_x4_0 goal_all := by
    have h0 : isConstB dom_x0_0_x1_1_x4_0 goal_all = false := by decide +kernel
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
end S_x0_0_x1_1_x4_0
theorem low_x0_0_x1_1_x4_0 : Lower dom_x0_0_x1_1_x4_0 roots_x0_0_x1_1_x4_0 goal_all 4 := S_x0_0_x1_1_x4_0.noCircuit

theorem low_x0_0_x1_1 : Lower dom_x0_0_x1_1 roots_x0_0_x1_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x4444000044440000, 6, 22)] (by decide +kernel) (by decide +kernel) low_x0_0_x1_1_x4_0

namespace S_x0_1_x1_1_x4_0
def pairsG : List (Nat × Nat) := [(7, 15), (7, 39), (11, 15), (11, 43), (35, 39), (35, 43)]
def r1sG : List Nat := [7, 7, 11, 11, 35, 35]
def r2sG : List Nat := [15, 39, 15, 43, 39, 43]
def mpG : Nat := 0x3f
def pool6G : List Nat := [12125282707215]
def xsM : List Nat := roots_x0_1_x1_1_x4_0.map (· &&& dom_x0_1_x1_1_x4_0)
def goalM : Nat := goal_all &&& dom_x0_1_x1_1_x4_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xb2600146
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x88880000000000008800000088000000808000008080
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x0_1_x1_1_x4_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x0_1_x1_1_x4_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x0_1_x1_1_x4_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x0_1_x1_1_x4_0 goalM u ys) : RunD dom_x0_1_x1_1_x4_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x0_1_x1_1_x4_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x0_1_x1_1_x4_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x0_1_x1_1_x4_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x0_1_x1_1_x4_0 roots_x0_1_x1_1_x4_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x0_1_x1_1_x4_0 goal_all := by
    have h0 : isConstB dom_x0_1_x1_1_x4_0 goal_all = false := by decide +kernel
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
end S_x0_1_x1_1_x4_0
theorem low_x0_1_x1_1_x4_0 : Lower dom_x0_1_x1_1_x4_0 roots_x0_1_x1_1_x4_0 goal_all 4 := S_x0_1_x1_1_x4_0.noCircuit

theorem low_x0_1_x1_1 : Lower dom_x0_1_x1_1 roots_x0_1_x1_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x8888000088880000, 3, 19)] (by decide +kernel) (by decide +kernel) low_x0_1_x1_1_x4_0

namespace S_x1_1
def pairsG : List (Nat × Nat) := [(3, 19), (6, 14), (6, 22), (6, 38), (7, 15), (7, 23), (7, 39), (10, 14), (10, 42), (11, 15), (11, 27), (11, 43), (18, 19), (18, 22), (26, 27), (26, 30), (26, 58), (34, 38), (34, 42), (35, 39), (35, 43), (35, 51), (50, 51), (50, 54), (50, 58)]
def r1sG : List Nat := [3, 6, 6, 6, 7, 7, 7, 10, 10, 11, 11, 11, 18, 18, 26, 26, 26, 34, 34, 35, 35, 35, 50, 50, 50]
def r2sG : List Nat := [19, 14, 22, 38, 15, 23, 39, 14, 42, 15, 27, 43, 19, 22, 27, 30, 58, 38, 42, 39, 43, 51, 51, 54, 58]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [12125282641422, 28617552891414, 55006235857686, 28618208712206, 38513159048742]
def xsM : List Nat := roots_x1_1.map (· &&& dom_x1_1)
def goalM : Nat := goal_all &&& dom_x1_1
def NN : Nat → Nat
  | 5 => 3
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xe1f7ce9661abef16258ccac1
  | 6, 0, 0 => 0xbadd30c7
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xccccccccc0c0c0c0c0c0c0c000cc00cc00cc00cccccccccc00000000cccc0000cccc0000cc00cc00cc00cc0088888888888888880c0c0c0c0c0c0c0c
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x11a215ac7ac78d5
  | 6, 0, 0 => 0x46b15
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
  | 0 => 0x1ffff000000000000007e0000000001fe307f0000000001fe00000000000001c1f000000000000001cf800000000000380e710000000001ffff81
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0xf6b700000000008aa2fe0000000000ea306d0000000001ff09480000000001e1f425000000000115cf920000000000785e710000000001755d01
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
  | 0 => checkCutEntry dom_x0_0_x1_1 roots_x0_0_x1_1 5 s ws hint
  | 1 => checkCutEntry dom_x0_1_x1_1 roots_x0_1_x1_1 5 s ws hint
  | 2 => checkCutEntry dom_x0_0_x1_1_x4_0 roots_x0_0_x1_1_x4_0 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x1_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x1_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_1_x1_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x1_1_x4_0 _ hc
  · contradiction
def p0Subs : List Nat := [0, 1, 2]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x1_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq, Bool.or_eq_true] at h; rcases h with h1 | h0
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2
  · obtain ⟨k, _, hk⟩ := List.any_eq_true.1 h0; exact checkCutByIdx_sound hk
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x1_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x1_1 goalM u ys) : RunD dom_x1_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x1_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x1_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_x1_1 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x1_1 roots_x1_1 goal_all 7 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x1_1 goal_all := by
    have h0 : isConstB dom_x1_1 goal_all = false := by decide +kernel
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
end S_x1_1
theorem low_x1_1 : Lower dom_x1_1 roots_x1_1 goal_all 7 := S_x1_1.noCircuit

namespace S_x0_0_x2_1_x5_0
def pairsG : List (Nat × Nat) := [(6, 14), (6, 22), (12, 14), (12, 28), (20, 22), (20, 28)]
def r1sG : List Nat := [6, 6, 12, 12, 20, 20]
def r2sG : List Nat := [14, 22, 14, 28, 22, 28]
def mpG : Nat := 0x3f
def pool6G : List Nat := [13220246722062]
def xsM : List Nat := roots_x0_0_x2_1_x5_0.map (· &&& dom_x0_0_x2_1_x5_0)
def goalM : Nat := goal_all &&& dom_x0_0_x2_1_x5_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x5afaf8e6
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x5050000000000000500050000000000040404040
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x0_0_x2_1_x5_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x0_0_x2_1_x5_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x0_0_x2_1_x5_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x0_0_x2_1_x5_0 goalM u ys) : RunD dom_x0_0_x2_1_x5_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x0_0_x2_1_x5_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x0_0_x2_1_x5_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x0_0_x2_1_x5_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x0_0_x2_1_x5_0 roots_x0_0_x2_1_x5_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x0_0_x2_1_x5_0 goal_all := by
    have h0 : isConstB dom_x0_0_x2_1_x5_0 goal_all = false := by decide +kernel
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
end S_x0_0_x2_1_x5_0
theorem low_x0_0_x2_1_x5_0 : Lower dom_x0_0_x2_1_x5_0 roots_x0_0_x2_1_x5_0 goal_all 4 := S_x0_0_x2_1_x5_0.noCircuit

theorem low_x0_0_x2_1 : Lower dom_x0_0_x2_1 roots_x0_0_x2_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5050505000000000, 6, 38)] (by decide +kernel) (by decide +kernel) low_x0_0_x2_1_x5_0

theorem low_x0_0_x4_0 : Lower dom_x0_0_x4_0 roots_x0_0_x4_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x444400004444, 12, 14)] (by decide +kernel) (by decide +kernel) low_x0_0_x1_1_x4_0

theorem low_x0_0_x5_0 : Lower dom_x0_0_x5_0 roots_x0_0_x5_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x50505050, 10, 14)] (by decide +kernel) (by decide +kernel) low_x0_0_x2_1_x5_0

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
  | 3, 0, 0 => 0x8c12a2c1
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

theorem low_x0_0_x4_1 : Lower dom_x0_0_x4_1 roots_x0_0_x4_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555000000000000, 26, 58)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_1_x5_1

theorem low_x0_0_x5_1 : Lower dom_x0_0_x5_1 roots_x0_0_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555000000000000, 44, 60)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_1_x5_1

namespace S_x0_0
def pairsG : List (Nat × Nat) := [(6, 14), (6, 22), (6, 38), (10, 14), (10, 42), (12, 14), (12, 28), (18, 22), (20, 22), (20, 28), (24, 28), (26, 30), (26, 58), (34, 38), (34, 42), (36, 38), (40, 42), (44, 46), (44, 60), (50, 54), (50, 58), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [6, 6, 6, 10, 10, 12, 12, 18, 20, 20, 24, 26, 26, 34, 34, 36, 40, 44, 44, 50, 50, 52, 52, 56, 56]
def r2sG : List Nat := [14, 22, 38, 14, 42, 14, 28, 22, 22, 28, 28, 30, 58, 38, 42, 38, 42, 46, 60, 54, 58, 54, 60, 58, 60]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [57201114484246, 55001790156326, 57201115143190, 57363685314076, 48405155681806, 55001790158374, 48491123055630]
def xsM : List Nat := roots_x0_0.map (· &&& dom_x0_0)
def goalM : Nat := goal_all &&& dom_x0_0
def NN : Nat → Nat
  | 5 => 10
  | 6 => 12
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xe08254e2cad8283097330fd09167b64b8188e31e38cce0b036a510be3301872b2736786703511936
  | 6, 0, 0 => 0xe50c7e4adde7335583248dc87f81043573b5f5714fd096404d0b89982d01d1ec2a506aae27367867262306f31757a53a
  | 7, 0, 0 => 0x73b5f571
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x500050005000500044004400440044004040404040404040505000005050000000005555000055554444444400000000000000005555555555005500550055001111111111111111050505050505050555555555000000005555000055550000505050505050505044444444444444440055005500550055
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x4315053210854376554326053726854715a542b1054210a5432105321905
  | 6, 0, 0 => 0x437210604372650472b1504721a50437215037219543721d6043715543721c604321054372e160372185
  | 7, 0, 0 => 0x437215
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
  | 0 => 0x60060000000000000181800000000000000070000000000600300000000000007e07f00000000001860000000000000001fff0000000001871c780000000001e787600000000001997c980000000001ffe0000000000001f81f800000000000668367000000000018789f000000000078e387
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x1460e69000000000093583900000000002aa9af00000000016c0fc2000000000003e03d0000000000bbf0140000000000000feb0000000001d75e79000000000144064000000000009150100000000001fff0140000000001fc1fc200000000016eafef0000000000bbf9bf000000000028a186
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 15 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 15 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 15 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 15 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 15 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 5 0 (NN s)
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
  | 0 => checkCutEntry dom_x0_0_x1_1 roots_x0_0_x1_1 5 s ws hint
  | 1 => checkCutEntry dom_x0_0_x2_1 roots_x0_0_x2_1 5 s ws hint
  | 2 => checkCutEntry dom_x0_0_x4_0 roots_x0_0_x4_0 5 s ws hint
  | 3 => checkCutEntry dom_x0_0_x5_0 roots_x0_0_x5_0 5 s ws hint
  | 4 => checkCutEntry dom_x0_0_x1_1_x4_0 roots_x0_0_x1_1_x4_0 4 s ws hint
  | 5 => checkCutEntry dom_x0_0_x2_1_x5_0 roots_x0_0_x2_1_x5_0 4 s ws hint
  | 6 => checkCutEntry dom_x0_0_x4_1 roots_x0_0_x4_1 5 s ws hint
  | 7 => checkCutEntry dom_x0_0_x5_1 roots_x0_0_x5_1 5 s ws hint
  | 8 => checkCutEntry dom_x0_0_x4_1_x5_1 roots_x0_0_x4_1_x5_1 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x0_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x1_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x2_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x1_1_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x2_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1_x5_1 _ hc
  · contradiction
def p0Subs : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x0_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq, Bool.or_eq_true] at h; rcases h with h1 | h0
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2
  · obtain ⟨k, _, hk⟩ := List.any_eq_true.1 h0; exact checkCutByIdx_sound hk
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x0_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x0_0 goalM u ys) : RunD dom_x0_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x0_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 12 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 0 = true)
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
def RootG (s : Nat) : Bool := scr dom_x0_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_x0_0 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x0_0 roots_x0_0 goal_all 8 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x0_0 goal_all := by
    have h0 : isConstB dom_x0_0 goal_all = false := by decide +kernel
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
end S_x0_0
theorem low_x0_0 : Lower dom_x0_0 roots_x0_0 goal_all 8 := S_x0_0.noCircuit

namespace S_x1_0_x2_1_x5_0
def pairsG : List (Nat × Nat) := [(5, 13), (5, 21), (12, 13), (12, 28), (20, 21), (20, 28)]
def r1sG : List Nat := [5, 5, 12, 12, 20, 20]
def r2sG : List Nat := [13, 21, 13, 28, 21, 28]
def mpG : Nat := 0x3f
def pool6G : List Nat := [13215951754509]
def xsM : List Nat := roots_x1_0_x2_1_x5_0.map (· &&& dom_x1_0_x2_1_x5_0)
def goalM : Nat := goal_all &&& dom_x1_0_x2_1_x5_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x857159eb
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x3030000000000000300030000000000020202020
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x1_0_x2_1_x5_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x1_0_x2_1_x5_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x1_0_x2_1_x5_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x1_0_x2_1_x5_0 goalM u ys) : RunD dom_x1_0_x2_1_x5_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x1_0_x2_1_x5_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x1_0_x2_1_x5_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x1_0_x2_1_x5_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x1_0_x2_1_x5_0 roots_x1_0_x2_1_x5_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x1_0_x2_1_x5_0 goal_all := by
    have h0 : isConstB dom_x1_0_x2_1_x5_0 goal_all = false := by decide +kernel
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
end S_x1_0_x2_1_x5_0
theorem low_x1_0_x2_1_x5_0 : Lower dom_x1_0_x2_1_x5_0 roots_x1_0_x2_1_x5_0 goal_all 4 := S_x1_0_x2_1_x5_0.noCircuit

theorem low_x1_0_x2_1 : Lower dom_x1_0_x2_1 roots_x1_0_x2_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3030303000000000, 5, 37)] (by decide +kernel) (by decide +kernel) low_x1_0_x2_1_x5_0

theorem low_x0_1_x4_0 : Lower dom_x0_1_x4_0 roots_x0_1_x4_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x888800008888, 41, 43)] (by decide +kernel) (by decide +kernel) low_x0_1_x1_1_x4_0

namespace S_x4_0
def pairsG : List (Nat × Nat) := [(5, 13), (5, 37), (6, 14), (6, 38), (7, 15), (7, 39), (9, 13), (10, 14), (10, 42), (11, 15), (11, 43), (12, 13), (12, 14), (33, 37), (34, 38), (34, 42), (35, 39), (35, 43), (36, 37), (36, 38), (40, 42), (41, 43), (41, 45), (44, 45), (44, 46)]
def r1sG : List Nat := [5, 5, 6, 6, 7, 7, 9, 10, 10, 11, 11, 12, 12, 33, 34, 34, 35, 35, 36, 36, 40, 41, 41, 44, 44]
def r2sG : List Nat := [13, 37, 14, 38, 15, 39, 13, 14, 42, 15, 43, 13, 14, 37, 38, 42, 39, 43, 37, 38, 42, 43, 45, 45, 46]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [12125282641165, 12125282641422, 38513159048485, 48426446884110, 48529526105382]
def xsM : List Nat := roots_x4_0.map (· &&& dom_x4_0)
def goalM : Nat := goal_all &&& dom_x4_0
def NN : Nat → Nat
  | 5 => 3
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x6d85fe656cc90f8424327c2d
  | 6, 0, 0 => 0x261f8b17
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xffff0000f0f00000f0f0000000ff000000ff0000ffff000000000000ff000000ff000000cccc0000cccc0000aaaa0000aaaa00000f0f00000f0f
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xf23d6646ac6885
  | 6, 0, 0 => 0x47915
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
  | 0 => 0x1fff00000000018c183f00000000000fe03f0000000001ffe0000000000001f01fc0000000000003c7bc0000000000632673000000000073e7c0
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x1ad50000000001cd7aff00000000000d602a0000000001ffe52a0000000001f29fd500000000013bd7bc0000000000e72e730000000000328500
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
  | 0 => checkCutEntry dom_x0_0_x4_0 roots_x0_0_x4_0 5 s ws hint
  | 1 => checkCutEntry dom_x0_1_x4_0 roots_x0_1_x4_0 5 s ws hint
  | 2 => checkCutEntry dom_x0_0_x1_1_x4_0 roots_x0_0_x1_1_x4_0 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x4_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_1_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x1_1_x4_0 _ hc
  · contradiction
def p0Subs : List Nat := [0, 1, 2]
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

theorem low_x2_1 : Lower dom_x2_1 roots_x2_1 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa0a0a0a0a0a0a0a0, 12, 13)] (by decide +kernel) (by decide +kernel) low_x0_0_x2_1

theorem low_x2_1_x5_0 : Lower dom_x2_1_x5_0 roots_x2_1_x5_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa0a0a0a0, 12, 13)] (by decide +kernel) (by decide +kernel) low_x0_0_x2_1_x5_0

theorem low_x1_0_x5_0 : Lower dom_x1_0_x5_0 roots_x1_0_x5_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x30303030, 9, 13)] (by decide +kernel) (by decide +kernel) low_x1_0_x2_1_x5_0

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
  | 3, 0, 0 => 0x2849cc57
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

theorem low_x3_1_x5_0 : Lower dom_x3_1_x5_0 roots_x3_1_x5_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc00, 12, 14)] (by decide +kernel) (by decide +kernel) low_x1_0_x3_1_x5_0

namespace S_x5_0
def pairsG : List (Nat × Nat) := [(1, 17), (3, 19), (5, 13), (5, 21), (6, 14), (6, 22), (7, 15), (7, 23), (9, 13), (9, 25), (10, 14), (11, 15), (11, 27), (12, 13), (12, 14), (12, 28), (16, 17), (18, 19), (18, 22), (20, 21), (20, 22), (20, 28), (24, 25), (24, 28), (26, 27), (26, 30)]
def r1sG : List Nat := [1, 3, 5, 5, 6, 6, 7, 7, 9, 9, 10, 11, 11, 12, 12, 12, 16, 18, 18, 20, 20, 20, 24, 24, 26, 26]
def r2sG : List Nat := [17, 19, 13, 21, 14, 22, 15, 23, 13, 25, 14, 15, 27, 13, 14, 28, 17, 19, 22, 21, 22, 28, 25, 28, 27, 30]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [13241821498893, 28617552760086, 13224541688077, 13224541689358, 22020500491537]
def xsM : List Nat := roots_x5_0.map (· &&& dom_x5_0)
def goalM : Nat := goal_all &&& dom_x5_0
def NN : Nat → Nat
  | 5 => 1
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x2fa6b83f
  | 6, 0, 0 => 0xeba6a037
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xffff000000000000ff00ff0000000000f0f0f0f000000000cccccccc00000000aaaaaaaa000000000000ffff
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x46885
  | 6, 0, 0 => 0x58d15
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
  | 0 => 0x3ff00000000000003c0ff00000000000038e0fc0000000003061cf20000000000001bcf000000000000ffff
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x3ff92ab0000000003e0ff540000000002bcedfc0000000003165cf200000000014b3bcf0000000000006d54
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
  | 2 => checkCutEntry dom_x2_1_x5_0 roots_x2_1_x5_0 5 s ws hint
  | 3 => checkCutEntry dom_x3_1_x5_0 roots_x3_1_x5_0 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x5_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1_x5_0 _ hc
  · contradiction
def p0Subs : List Nat := [0, 1, 2, 3]
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

namespace S_x1_0_x3_1_x5_1
def pairsG : List (Nat × Nat) := [(41, 45), (41, 57), (44, 45), (44, 60), (56, 57), (56, 60)]
def r1sG : List Nat := [41, 41, 44, 44, 56, 56]
def r2sG : List Nat := [45, 57, 45, 60, 57, 60]
def mpG : Nat := 0x3f
def pool6G : List Nat := [48555548752173]
def xsM : List Nat := roots_x1_0_x3_1_x5_1.map (· &&& dom_x1_0_x3_1_x5_1)
def goalM : Nat := goal_all &&& dom_x1_0_x3_1_x5_1
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x23301cc
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x330000000000000030003000000000002200220000000000
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x1_0_x3_1_x5_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x1_0_x3_1_x5_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x1_0_x3_1_x5_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x1_0_x3_1_x5_1 goalM u ys) : RunD dom_x1_0_x3_1_x5_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x1_0_x3_1_x5_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x1_0_x3_1_x5_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x1_0_x3_1_x5_1 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x1_0_x3_1_x5_1 roots_x1_0_x3_1_x5_1 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x1_0_x3_1_x5_1 goal_all := by
    have h0 : isConstB dom_x1_0_x3_1_x5_1 goal_all = false := by decide +kernel
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
end S_x1_0_x3_1_x5_1
theorem low_x1_0_x3_1_x5_1 : Lower dom_x1_0_x3_1_x5_1 roots_x1_0_x3_1_x5_1 goal_all 4 := S_x1_0_x3_1_x5_1.noCircuit

theorem low_x3_1_x5_1 : Lower dom_x3_1_x5_1 roots_x3_1_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc0000000000, 40, 42)] (by decide +kernel) (by decide +kernel) low_x1_0_x3_1_x5_1

namespace S_x3_1
def pairsG : List (Nat × Nat) := [(9, 13), (9, 25), (10, 14), (10, 42), (11, 15), (11, 27), (11, 43), (12, 13), (12, 14), (12, 28), (24, 25), (24, 28), (26, 27), (26, 30), (26, 58), (40, 42), (41, 43), (41, 45), (41, 57), (44, 45), (44, 46), (44, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [9, 9, 10, 10, 11, 11, 11, 12, 12, 12, 24, 24, 26, 26, 26, 40, 41, 41, 41, 44, 44, 44, 56, 56, 56]
def r2sG : List Nat := [13, 25, 14, 42, 15, 27, 43, 13, 14, 28, 25, 28, 27, 30, 58, 42, 43, 45, 57, 45, 46, 60, 57, 58, 60]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [48555546646797, 48426446884110, 48490366962972, 48491123055630]
def xsM : List Nat := roots_x3_1.map (· &&& dom_x3_1)
def goalM : Nat := goal_all &&& dom_x3_1
def NN : Nat → Nat
  | 5 => 3
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xc3eb1704aa1ac62957e6ed87
  | 6, 0, 0 => 0x19b23d5e
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xff000000ff00aa00aa00aa00aa000f000f000f000f00ff00ff0000000000ff000000ff000000f000f000f000f000cc00cc00cc00cc005500550055005500
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x11a21633aac4775
  | 6, 0, 0 => 0x468e5
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
  | 0 => 0x3f83ff00000000000700730000000001c7fc7f0000000001ff80000000000001c07c000000000000380380000000000000707c0000000001f8ff8c
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x1b81dd00000000004f14f30000000000c5d46a0000000001ffc0480000000001e47e2200000000013a2b95000000000091f17c0000000001b0eb0c
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
  | 0 => checkCutEntry dom_x3_1_x5_0 roots_x3_1_x5_0 5 s ws hint
  | 1 => checkCutEntry dom_x1_0_x3_1_x5_0 roots_x1_0_x3_1_x5_0 4 s ws hint
  | 2 => checkCutEntry dom_x3_1_x5_1 roots_x3_1_x5_1 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x3_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x3_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1_x5_1 _ hc
  · contradiction
def p0Subs : List Nat := [0, 1, 2]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x3_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq, Bool.or_eq_true] at h; rcases h with h1 | h0
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2
  · obtain ⟨k, _, hk⟩ := List.any_eq_true.1 h0; exact checkCutByIdx_sound hk
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x3_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x3_1 goalM u ys) : RunD dom_x3_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x3_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x3_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_x3_1 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x3_1 roots_x3_1 goal_all 7 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x3_1 goal_all := by
    have h0 : isConstB dom_x3_1 goal_all = false := by decide +kernel
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
end S_x3_1
theorem low_x3_1 : Lower dom_x3_1 roots_x3_1 goal_all 7 := S_x3_1.noCircuit

theorem low_x1_0_x5_1 : Lower dom_x1_0_x5_1 roots_x1_0_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3300330000000000, 52, 60)] (by decide +kernel) (by decide +kernel) low_x1_0_x3_1_x5_1

theorem low_x4_1_x5_1 : Lower dom_x4_1_x5_1 roots_x4_1_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa000000000000, 48, 49)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_1_x5_1

namespace S_x5_1
def pairsG : List (Nat × Nat) := [(33, 37), (33, 49), (34, 38), (34, 42), (35, 39), (35, 43), (35, 51), (36, 37), (36, 38), (40, 42), (41, 43), (41, 45), (41, 57), (44, 45), (44, 46), (44, 60), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [33, 33, 34, 34, 35, 35, 35, 36, 36, 40, 41, 41, 41, 44, 44, 44, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [37, 49, 38, 42, 39, 43, 51, 37, 38, 42, 43, 45, 57, 45, 46, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [48529526105382, 57325670638897, 57364173630012, 48555548750117, 61796579419452, 55165503416870, 48529677559333, 48529711834666, 61762220139836]
def xsM : List Nat := roots_x5_1.map (· &&& dom_x5_1)
def goalM : Nat := goal_all &&& dom_x5_1
def NN : Nat → Nat
  | 5 => 11
  | 6 => 13
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xeef00bf2e299c4dae02b48d3d3d501bbc0d591f2b210ced39510e530766ac205734cb248419972c80decb8e1
  | 6, 0, 0 => 0xdfd23ee1ce9cdd61bcd30b3dbbfc5a0896ca434792e7e42d7a72457a6d3d4baa5b75988b52df1ca74cb0d56c0decb8e1019671c9
  | 7, 0, 0 => 0x7a72457a
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xf000f00000000000fcfcfcfc00000000fafafafa00000000eeeeeeee00000000fc00fc00000000000000ffff00000000fafa00000000000000ff00ff00000000f0f0f0f00000000055555555000000003333333300000000ffff000000000000ff00ff0000000000cccccccc00000000aaaaaaaa000000000f0f0f0f00000000
  | 1 => 0xff00000000000000f0f0000000000000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xc410294670954a4188c0520ce62a9c414294871190a4184a0522ce20a90410214693882a4188205
  | 6, 0, 0 => 0x438828520ce208188389c41620cf010588369c41620dc710580419c41520cef1058033882a520cec10580419c4650106208140419c255
  | 7, 0, 0 => 0x419c415
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 29
  | 6 => 34
  | 7 => 29
  | _ => 0
def stateM : Nat → Nat
  | 5 => 0x1fffffff
  | 6 => 0x3ffffffff
  | 7 => 0x1fffffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0xe00000000000007ee1fc000000000070fdf300000000000e1c7f000000000000e000000000000000ffff000000000070000000000000007f01ff000000000070e1800000000003ffe38c0000000003f1ff830000000003ff0000000000000380fe0000000000000e007c0000000000001c7300000000038f1e7f
  | 1 => 0x38000000000000000700000
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x240e80000000000037eeffd0000000002f7fdf70000000001bf7fff000000000348ee280000000000006fbd0000000002f7904200000000003701d7000000000274e99500000000036cc30c0000000002d1b8830000000003ff90420000000003c8fe2800000000012e477c0000000000933cf300000000018b166a
  | 1 => 0x3c890000000000002748000
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 18 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 18 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 18 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 18 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 18 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x1f) :: stateWiresD n (ids >>> 5)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x1f) :: stateWiresS n (ids >>> 5)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 5 0 (NN s)
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
  | 0 => checkCutEntry dom_x0_0_x5_1 roots_x0_0_x5_1 5 s ws hint
  | 1 => checkCutEntry dom_x1_0_x5_1 roots_x1_0_x5_1 5 s ws hint
  | 2 => checkCutEntry dom_x3_1_x5_1 roots_x3_1_x5_1 5 s ws hint
  | 3 => checkCutEntry dom_x4_1_x5_1 roots_x4_1_x5_1 5 s ws hint
  | 4 => checkCutEntry dom_x0_0_x4_1_x5_1 roots_x0_0_x4_1_x5_1 4 s ws hint
  | 5 => checkCutEntry dom_x1_0_x3_1_x5_1 roots_x1_0_x3_1_x5_1 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x5_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x3_1_x5_1 _ hc
  · contradiction
def p0Subs : List Nat := [0, 2, 1, 3, 4, 5]
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
private theorem z5 : ∀ i, 0 ≤ i → i < 11 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 11 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 13 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 13 0 = true)
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

namespace S_x1_0
def pairsG : List (Nat × Nat) := [(1, 17), (5, 13), (5, 21), (5, 37), (9, 13), (9, 25), (12, 13), (12, 28), (16, 17), (20, 21), (20, 28), (24, 25), (24, 28), (33, 37), (33, 49), (36, 37), (41, 45), (41, 57), (44, 45), (44, 60), (48, 49), (52, 53), (52, 60), (56, 57), (56, 60)]
def r1sG : List Nat := [1, 5, 5, 5, 9, 9, 12, 12, 16, 20, 20, 24, 24, 33, 33, 36, 41, 41, 44, 44, 48, 52, 52, 56, 56]
def r2sG : List Nat := [17, 13, 21, 37, 13, 25, 13, 28, 17, 21, 28, 25, 28, 37, 49, 37, 45, 57, 45, 60, 49, 53, 60, 57, 60]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [48555546644749, 48400861305869, 57196820110353, 57363668208924, 57351639666981]
def xsM : List Nat := roots_x1_0.map (· &&& dom_x1_0)
def goalM : Nat := goal_all &&& dom_x1_0
def NN : Nat → Nat
  | 5 => 2
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x8529ae5b08dee8a8
  | 6, 0, 0 => 0xb592d7db
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x2222222222222222000033330000333333333333000000003333000033330000330033003300330030303030303030301111111111111111
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x23442c4755
  | 6, 0, 0 => 0x468e5
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
  | 0 => 0x3603f00000000000fe0ff0000000001ffe0000000000001f01f0000000000018f18f000000000006c86ce0000000001fc9fc0
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0xb7eb7f000000000005a05a0000000001ffe0080000000001fa5fa50000000001cf1cf200000000016db6de0000000001481480
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 7 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 7 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 7 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 7 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 7 then wireAt i else 0
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
  | 0 => checkCutEntry dom_x1_0_x2_1 roots_x1_0_x2_1 5 s ws hint
  | 1 => checkCutEntry dom_x1_0_x5_0 roots_x1_0_x5_0 5 s ws hint
  | 2 => checkCutEntry dom_x1_0_x3_1_x5_0 roots_x1_0_x3_1_x5_0 4 s ws hint
  | 3 => checkCutEntry dom_x1_0_x5_1 roots_x1_0_x5_1 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x1_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x2_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x3_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x5_1 _ hc
  · contradiction
def p0Subs : List Nat := [0, 1, 3, 2]
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
private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
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
def RootG (s : Nat) : Bool := scr dom_x1_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_x1_0 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x1_0 roots_x1_0 goal_all 7 := by
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
theorem low_x1_0 : Lower dom_x1_0 roots_x1_0 goal_all 7 := S_x1_0.noCircuit

theorem low_x0_1 : Lower dom_x0_1 roots_x0_1 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x8888888888888888, 41, 43)] (by decide +kernel) (by decide +kernel) low_x0_1_x1_1

theorem low_x4_1 : Lower dom_x4_1 roots_x4_1 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa0000aaaa0000, 16, 17)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_1

namespace S_63
def pairsG : List (Nat × Nat) := [(1, 17), (3, 19), (5, 13), (5, 21), (5, 37), (6, 14), (6, 22), (6, 38), (7, 15), (7, 23), (7, 39), (9, 13), (9, 25), (10, 14), (10, 42), (11, 15), (11, 27), (11, 43), (12, 13), (12, 14), (12, 28), (16, 17), (18, 19), (18, 22), (20, 21), (20, 22), (20, 28), (24, 25), (24, 28), (26, 27), (26, 30), (26, 58), (33, 37), (33, 49), (34, 38), (34, 42), (35, 39), (35, 43), (35, 51), (36, 37), (36, 38), (40, 42), (41, 43), (41, 45), (41, 57), (44, 45), (44, 46), (44, 60), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 3, 5, 5, 5, 6, 6, 6, 7, 7, 7, 9, 9, 10, 10, 11, 11, 11, 12, 12, 12, 16, 18, 18, 20, 20, 20, 24, 24, 26, 26, 26, 33, 33, 34, 34, 35, 35, 35, 36, 36, 40, 41, 41, 41, 44, 44, 44, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [17, 19, 13, 21, 37, 14, 22, 38, 15, 23, 39, 13, 25, 14, 42, 15, 27, 43, 13, 14, 28, 17, 19, 22, 21, 22, 28, 25, 28, 27, 30, 58, 37, 49, 38, 42, 39, 43, 51, 37, 38, 42, 43, 45, 57, 45, 46, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x3ffffffffffffff
def pool6G : List Nat := [57205409451281, 38513159048485, 28618057388310, 48409450649102, 57205108379941, 38530271481130, 57287216077846, 57363701763356, 48529676833061, 57205360038166, 48409451240461, 48529526105382, 38513410709029, 57364173164828, 57351438339345, 12125534295565, 57205409451542, 48490869755164, 28617552760086, 57363702091292, 28617956790550, 12125534299661, 12125282641165, 48426193587725, 57286964421910, 48529273131301, 48491123055630, 57286964415766]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_all &&& dom_63
def NN : Nat → Nat
  | 5 => 12
  | 6 => 142
  | 7 => 613
  | 8 => 308
  | 9 => 31
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xfabac72bed2fcacfbe3be521b568ca57937264e07ad525066c4870745b030d833b15182c2dd6f21f1b7a2334088287c9
  | 6, 0, 0 => 0x72ae9de76fe6b8476e135d0c6d1b8e516c335b256a81188e6a4fbdba6a16df5467c261ef657e8ba965422c49617322f35f6782f5595c58c057a33a8f56dce6ea56d211ea51e628db5056b6ba4ff5b6a44f2e1aab4d9642e84cadbbc348bd220846e06bdc455436f24391a87641d82dfb407cd3cf3f414a253d20c7df3c50dff73a3ebcca37cae42b36a9a2b23653a2e93501407730bbc1c22f4cd5152b98b0e22a72db22298197b8280d10912602e17d25b941fa25967d6c22bc3fe41fa6552d1f75b24c1f6470c31e8b1d3e1e6d8f8d1d10b55f1c62eaa019e3facb164ffdd315ae827713a2e2790ce4df950ad7e62a03fc0f0203c5657e03ba0d1a03214aec
  | 6, 0, 1 => 0xea4ac4f7e90c8e30e6f6a3b6e48e7a1bdf479a4edee4a53ede9f565ddd07edd9d9f27b93d87b7b9ad7682fd9d4c4331ed3df8ec6d0d31662cf9b7c3bce79f2afcd5bf546caf7cb15c9de6a87c91fd48fc7490879c71ededdc6add4ffc3bb0dcabeb16106bd68eafab800c502b6c19b56b699b54db44499ceb3aecc95b324a800b2b7656db275aad9b0008743afbea2d9aedefdb7ab6fbc9ba8b4036ea6aa2fe9a24322d79ef2a2ff9d47edb4989b60859480177f9456a477928873b89287b582916f132a901291ec8ee810558cb683498c91bf8389ffa51f843d4abd81eb52be7e8cd9ba7d036509765798de764f1c6d74e9036d73a8bc2372ecc08a72d93e5f
  | 6, 0, 2 => 0xffb85fd6fe3a4b55fae0fcb3f90a3f8ff8167092f76193c7f676be07f3e318a7f17fbd4bf0e0eea2f06e0b5aed768aafed49ea9deae50236
  | 7, 0, 0 => 0x1c9454711c62eaa01c33eefe1c1928291ad0802419b6c5591956825f192439d718788e92182141dd17b8277b178270b11778fdec170efe2f16b5dda1164ffdd315a750a71299cfe711a07b4e1191d5ce117a58c31143415d0fe17bff0eddf50b0ebd8d6a0e1752730db856600da3dff10d6e0c770c7f0f820c73ee3b0bec4eb60bbf98790b93c10a0b3053740acf6a2c0a64e1b90a52d2db0a37b86309aab2f0099dcefe095e7bf508f19f45089d57d3080465a607af3f5d07a2cd180783f7450715498d06e0dea505e991b90529fa4f04a1e8fe047b1532047395a2045636c903fad7f6035c13aa0356ee77034b8f2801fec3c701818ed0012cad0b0019b8c6
  | 7, 0, 1 => 0x3650d29935581adb3542459f3408338433c0b67e339b6de133721971333165e032c76fd732ae6b9f329ce6903287c53e3260b0d9325d0d85317fcb25313c88583131359830da702d303aef642ff37a902fbc7ba42f9eb1222f2460382deb9a982db021812da64bb72d80c3d22c7578892c4dc40c2b5b714c2b34637e2b1e48cb2a7bf7562a4cfd1529fbba1a29ba9631299e12eb293cb14727d8adcb278270f427495f96267bd39d2621c4c426026ecc25ce08de25c3e24624527ff7244e3f2023bea9c5234f19092329c47a2328f98322d91c03212fb28d210b522120ea3d851fda0bbc1f6828c51d8beab91d5275941d4bf1bb1d21eafc1d0a570d1cb79b7c
  | 7, 0, 2 => 0x56a21c7b547d44db545c29f853cea40553890dd552c2c0a0526d9a575228404651419c6f513785fd512a7daf50c865845086ebaa4fe855494fdfa27f4f9eecaf4ebf55304e882a064e573acc4dd3eb7b4d2adf594c8d04e84c7cb5c14bceeb0249e7f20d4933dad848f25aa148dd246448a613ca476d95e94691fdef463b029f4613374e460fba1b45bbfe35459d63c4456319dd4544dd7d44130e1a43fce5de421a0a4d41c796a6409e00cd4073bd033eef1ec33e86703c3dc53c2e3d8e4b863d5dec943d26dfb13d020fd93c8249c83c50dff739ba7acf396d428b38dc31f638bf2ecf38b7f353389ab20b3845fc4937fea1603792b7f23713f2e436d00032
  | 7, 0, 3 => 0x6b9e45e86b96a74b6af71c9b6a9866b66a5f9e446a5b0bf069ef228269a1197568d45be9686f09c46848325868318afa6791937867880e646721459a668614a1667ff3466615a3146607e37965aaaf1364bd1b6963d7296f63a3badb638e58d6638da028635eceb86336188a630d45a062e524e362893f47610e58cd61080d1f60e42f31607327d4604805285fed9d5f5f4644f85edc890c5e57bee95e2165345e1cf0265e1a14cb5dce0c4a5d4be1eb5d4a14835d14d5085c5824aa5c51b4bd5b4327c359dedb8459b6e18d598e980a5989f9bf59799ede58fe5e6758913afe58567d215824cb3157db8061579ceee156db525156b94ef156aeea8756aaa9b0
  | 7, 0, 4 => 0x821de44181fb573f80f4350e8092368e801675d58000a0997fc2b71c7f1521377f0f67a27e53ca6f7e25ad557e0f5a8b7d3809da7ce6d6e37c19bc257c0af7747bf9cb407b9792677b027e5a7ab1d58a7a685fe47a6297347a5d0c1c7a0aafa37951d685793744fd7935b3b078f62cda7870a26578514c6d77c5563777b5086f77a1480d76d85f747617bae2758f5fa37584a59a754c2ce17528ba1e74f1a12574c037547419638c73c4f47472e218de72962e95725db598725b8fae712d802d70fd41a670d27af570c572a76fe8d4316f834a416f39e1a76edeb4586ead4a876e8983726e7080f16e5b1f256df22fc46deed46a6ca136c86c92e0136c8cc841
  | 7, 0, 5 => 0x9df311db9d7f5d6e9cddb1369cd2fed29ca7e2709ca201249c4680cc9c3713069b013f369a4cca8299f8011499bbbe1c99a188049982dfb6997db02a98e27f319809717396d35d19963393ff95bb394895842c659542dde7949b9cf29488a035940b1c0e93f84de193f40d0a93f311e893b1208d927ee9ed91f684a691e36bc891a2af889126e41b90df2355900b262a8f713f988ed53e0d8ed383578de0251b8da868fb8d9e33c08d8249758d31b8a38cc7b8e68cbae0b48c3a225b8bd6d9bb8bb213078a7556c58a335bae8a06821b8937bce188c8592288c2514088b1e7448828c8d987a541ad870f3af185a2d87184f1dfd183f3954e835c9aa882f9c3b0
  | 7, 0, 6 => 0xba3abfd9b96ba581b929c117b8c46823b84be1b4b7a391acb7842f4bb67eb1e8b6283af4b5a996c2b5562e40b5053f76b4eaab67b3a94b1fb3832b99b293feb6b23b047fb189e4a3b1658437b1446f9bb0d40f46b0b034ffb08217e5b0154e27aeee5540ae94ecadae5635d0adcba09aad12e612ad11cd92acccad9bacb976acac2817b2abc66819aba3ba95ab9db1ebab76f7d6ab52976aa9a17713a9131075a82cdb97a827c1daa7f89740a7a46f4aa7100fb7a6aa2fe9a60182bda590cdc8a3aac124a390703fa38e8a46a2e7b907a2e5eb9fa2453ec1a2067ec3a1964c37a1664887a0ed1e35a0180d7f9ff982e99fb16acd9f52b8a99e1a06709dfab078
  | 7, 0, 7 => 0xd84b58cbd7c7c7ffd7539bdad6fa86bad6c71384d69534b5d66397a8d616304bd542562fd4040d1ed3f700c5d3b24338d37cf759d323a151d2cd8fbfd1b4db32d1af2339d1580846d0abab7fd018f33dcfd46ca8cf1d6b2fceec12e2ce65deddce1af5a2cd8f687ccd669592ccbaa2f2ccb8d58acc546ba4cc04a432cb615d11cb451b79caf685ecc98f6c6ac9421defc92fc7a9c87b7b57c7972e5bc6e33866c6ab04afc673906cc64f7c78c5b24cf1c59c77b5c55f8e9bc44cb52ec3c2a4d9c2ca73d4c1f3b5e4c1dc5b5ec1b11346c134a243c131a89dc1129ee3c04dba9dc04daca6bf9f6024bf7e924ebf5bcdc0bc37c57fbc2283abbbe7a437bbc874d2
  | 7, 0, 8 => 0xedb5ea9aed853cd4ecec19c2ec0c7482ebab792feb9f992aeb4f5268eb413bf9eb3d6051eace37edea9f1848ea02da06e9d3d0f4e9bcbd99e8dd12e7e8af8fede89bfac4e84fc37ce816704fe8144a65e7cf1b35e75fb9b1e67e2d5ee676a51de6730c17e659902ce64260c6e605b5afe5df9629e5d5189ce5876b79e50cd1cee4e0203ae4976f0fe45fe2fee3d66f38e3a0da2be35d99d1e290a862e1e699d8e19bce85e191b813e0045351dfe8af95dfc00becdf6e3822df198746deda8ae6de00ed0fde002525dd85116fdd561584dce678bcdc13de25db6369cadb571064db569198db3c7535da696bccd98fe426d96c7a47d937567ad9069a79d85ded4d
  | 7, 0, 9 => 0xff756f46ff43dbfdff077c9dfef4ece4fe7b0bf7fe003672fde5f311fd52f07cfcc7f5a8fc94b559fb515f21fb4486effacd5d73f9a39b97f9076f3ff81e1b74f80eb781f7f8e245f78b0895f6b508dbf667724df4ecf506f3910cd3f36777b6f1f6e0d6f1c3b22bf1623f35f0cd59eaf0cad7eff03b8bbdef6f61a0eeaee791ee8e6a21ee28cb7cee1d6168edf99859edcb7b3f
  | 8, 0, 0 => 0x374ca990371b3fbf36ae22d134c68f8a33e715943366d85832a7cf853255b3a430ed8f323098ad6d2e60ed462dbd9e352db95d5e2d6c36d42c443a412b935f3d28736fa12764e2a726f708f726c17c56268d093a25ff72af25ce08de259c2a0f2577635b241ae38822fd0d35223cfbcd1f504cac1f1c08551edb62021d21eafc1be5022a1b0b998c192abff41928bdfb18ddfae018da718b187a7d1a18491349178270b1161b979115ea2dc015df0c79142db03813cffff71315d12e12c99a330f54aff70e8587a80ddeb3e00b69e2050b00d3fd0acf6a2c0ac291fa0a97cb4908729adb06d554670666871c063313e604ae569103bef7750156e3cc004b64f5
  | 8, 0, 1 => 0x667ff34665c9f48665bcd2fb64eeec5464dfafd264ae460163076e4362f517fd6240cbab60a888ba609018d86046708f5eb0dedf5ea189375da661335a6a02b35a65cb0959cdc471590a0aed58cd881857f8949f57df34d055e7d3ff558dc526553a094054ee602c528f7aa3522a7003521132084ed429274eaffbbb4db2c4844c8de4c04c0054d34bceeb024b85288b4a995f9a485a3d014774b70f46d836664691fdef45ed680645bbfe3542d860c9422923bc4205d0494169bf9e40fdd6303fcf5cc13d7b908d3d7077383d2456c23bcf8e9d3bcbcf173b2b98db3ab26e893a9c53d639bed33d39a60da2393b3931390d085a3909cf60384665c23756b8d6
  | 8, 0, 2 => 0x968d45fc9541f7f99516af759371a0599368ebeb9165d2a090b527f0907a592f8eb2455a8d8d65968cb614e58c64e1ee8c348f798b969fb78b89027f887437e587bee8ad8790cb938680c80c85723b128564e97e8502b0a584db14438464689c83c82a5a82a2633b8274e04182614b1881dbc0a381d99ab981cc023081a2729c810a65a080437db27eb74b1f7e9d06ce7e5cbf637e2b55927e1949c17d9bbf8c79fe9a177953f26f78a4ffe5789fdb3a77c63d6375fdfe5175d92e7975af1c437528ba1e750964267501c58973c08ca27355347a7210a91f7166433c708c63d86ff132df6d4247ad6cc9ecf66c92e0136a5967b868c9048168b16336682b2f31
  | 8, 0, 3 => 0xd01622edcf1d6b2fcf0795f3cd8606d2ccc58d3ccc3eff34ca9fc081ca66a7b3ca003fb8c9b8cae4c9640176c8e9b08cc77571d5c6dd499fc3ed52ebc34efe54c1628508c10eafeac1027068bf935932bf4be41fbd14695dbcee49d7bba622bdbaf502e1bad0a275baaf8dd9b99f5c10b711420fb67cebd0b6283af4b605ed0ab50ed8d3b31bd2b3b30c9551b265c412b147c105b07b2df5b0154e27af6ca0fbac52d745ac5109ddab65cba2a8bdd6e7a8a3455fa84a25ffa7dca2c7a6445fd6a5b19f0aa494ba80a3631f52a34cc39aa1c9b5faa1748fb1a15392e4a0da99e1a03e7b57a03173099eef4aa39ea5e2099d5e30269d1c3ecb98405c4b980df69f
  | 8, 0, 4 => 0xfe581344fd53a92afcfb68defcd295f4fc4e8f9bfc24d5ecfbc06c06facd5d73fab3f02bfa387828f9b2edb3f81a05cff67433def6170511f5087817f33eef32f327dbd7f1485bc0f0a0a2a5f07e9f45ef992c97ed864953ed84fd02eb97b9b2eb06ecc3eafcd651ea8db5d8e884a584e6f02fade5943b56e4dc43aae4c22ea2e2fb0264e2a274b8e132e63de00052f3df814e89ddc23632dc6a17cedc38adfddc226a26dac32684da390d57d9b24658d90d7775d8293d25d6880befd616304bd461a42ad2fa8aa8d251ec01d1024c99
  | 9, 0, 0 => 0xff82234ffe739655fa0bc0e3eeff5994e5943b56e27895b3df814e89dbbd0a3fd36b5df6d2cf1fb4d0e09013bf935932bbd0e250b4d0e9e0b20e639db147c105afaf7e14a8110047a494ba809ff8643a981d639891df56237cc052b875fdfe51556b7311553a09403a03cbab2f07484d2293dc3917f0a5e609b68333
  | 10, 0, 0 => 0xeeff5994
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xff00ff000000000f0f0f0f0f0f0f0f0eaeaeaeaeaeaeaea03ff03ff03ff03ffaaaaaaaaaaaaaaaa3333333333333333e0e0e0e0e0e0e0e000ff00ff00ff00ffff00ff00ff00ff00fafa0000fafa00001f1f1f1f1f1f1f1fffffffff00000000ffff0000ffff0000cccccccccccccccc55555555555555550ff00ff00ff00ff0
  | 1 => 0xffccffccffccffcccc00cc00cc00cc00fcfcfcfc00000000fcfcfcfcfcfcfcfcc0c0c0c0c0c0c0c0fff0fff000000000f000f000f000f0000f0f0f0f0f0f0f0ff0f00f0ff0f00f0ffffff000fffff000fff0fff0fff0fff0faaaaaaafaaaaaaafffffffff000f0000fff0fff0000000000000000ffffffff0000ffff0000ffff
  | 2 => 0xeee0eee0eee0eee0feeefeeef000f000eeeeeeee00000000eeeeeeeeeeeeeeeefafafafafafafafaccffccff00000000fffff0f0fffff0f0f0f00000f0f0000055555050555550500fff0fff0fff0fffccc0ccc0ccc0ccc0ffffff00ffffff00ff000000ff000000ffffccccffffcccccccc0000cccc0000f0c0f0c0f0c0f0c0
  | 3 => 0xffff0f0fffff0f0f0f0f00000f0f0000ff0fff0fff0fff0f0f000f000f000f00cfcfcfcfcfcfcfcf0c0c0c0c0c0c0c0cfc00fc00f000f00003ff03ff0fff0ffffcccf000fcccf000fcccfcccfcccfcccfcf0fcf0fcf0fcf00f3f0f3f0f3f0f3f1515151515151515fc00fc00fc00fc00ffff0505ffff05050000fafa0000fafa
  | 4 => 0xccffccffccffccffcccccccc00000000ff00cc00ff00cc00f0f0c0c0f0f0c0c0ff00ff0000000000f0f0f0f000000000ff00f000ff00f00000000f0f00000f0faaaaa0a0aaaaa0a0fff0fff0f0f0f0f0ffffc000ffffc000fff0fff0f000f000fcccccccfcccccccf0000000f0000000aaaaeeeeaaaaeeeeaaaaafafaaaaafaf
  | 5 => 0xfafffafffafffaffff00fa00ff00fa00fffffafafffffafa05ff05ff05ff05ff0505050505050505fa00fa00fa00fa00eeeeee00eeeeee00eeeee0e0eeeee0e0ee00ee00ee00ee0011ff11ff11ff11ffe000e000e000e000ffe0ffe0ffe0ffe0f0f0f000f0f0f000ffff000000000000ffff00ffffff00fff0fff0fff0fff0ff
  | 6 => 0xff000000ff000000f0f00000f0f0aaffaaffaaffaafffffff0f0ffff0000afafafafafafafafffffaaffffffaafff0f0a0a0f0f0a0a00000555500005555ff00aa00ff00aa00ffffafafffffafafffffaaaaffffaaaaffaaf0a0ffaaf0a00f5f0f5f0f5f0f5ff0a0f0a0f0a0f0a0ffaaffaaffaaffaafafafa00fafafa00
  | 7 => 0xf0f3f3f0f0f3f3ff000c000f000c000fff0ccc0fff0ccc0fcf0cc00fcf0cc00f0f0c000f0f0c000ffffcc00ffffcc00eeaaeeaaeeaaeeaae0a0e0a0e0a0e0a0ffccf0c0ffccf0c0ffc0c0c0ffc0c0c0ff00c000ff00c000ffffc0c0ffffc0c0ea00ea00ea00ea00fcfcfc00fcfcfc00fffffc00fffffc000000ffff00000000
  | 8 => 0xffff0f0fffff0000ff000f00ff000f00ffff0f00ffff0f00ffff0c0cffff0c0cffccccccff000000fcfcccccf0f00000fcccfcccf000f000ff00cc00ff000000f0f0c0c0f0f00000ffffccccffff0000fcfcfcfcf0f0f0f0eeeeeeeeaaaaaaaafcfcf0f0fcfcf0f0fc00f000fc00f000eeeeaaaaeeeeaaaa00ff33ff00ff33ff
  | 9 => 0xff00f000ff000000fafafafaaaaaaaaaf0ff00fff0ff00ff00ff0fff00ff0ffffffff0fffffff0fff000f000fffffffffff0f0f0fff0f0f0eaaaeaaaeaaaeaaac000c000c000c000fafaaaaafafaaaaafaaafaaafaaafaaa0000cccc0000ccccffffff00ffff0000ffaaaaaaffaaaaaaff0f0f0fff0f0f0f0f0f0f0f00000000
  | 10 => 0xffaaffaaaaaaaaaaf000f00000000000ff00f000f000f000f0f0fffff0f0f0f0f0f0fff0f0f0fff0f0f0f000f0f00000fffffffff0f0f0000f0f0fff0f0f0ffffffff0f0f0f0f0f0ffffaaaaaaaaaaaaf0f000f0f0f000f0a0f0a0f0a0f0a0f0fff0f0f0ff000000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x417020b085040706020551303020b0050406090208503020b001150416151402503020b1200504030b0a00504020b0010504030e0d0c50403020100503020b000f5
  | 6, 0, 0 => 0x42928024708600040319091e0b6001519020b101160004030e023308600044507360e0b60004030e02010c600042207210118600130307140e026001f0e1e0b101160004030e020b0060004070240181060004031514190260003020118081160004060e2c02086000e2a020b0810600030e010a081160004030e020b38600040e020b083060004030e250b266000424230b0a18600071d020b181060004020b18081060004030d021808600040e0b0a0810600130315020b26600040346020b26600040b0a180810600031f0e1e01116000003071d0e0d5001a0e19020b1060004033b0b3a08600030e2a0201086
  | 6, 0, 1 => 0x32d020b18086000432020b181060004073b0b3a10600031d0e02010860013033519020b600000403020b00500040e19250b1060004390e020b106000407024118106000428020b0848600030b0a180811600131519020b10600044619020b10600043d020b3c106000407010a18106002423020b1811600000403320e0d500042928020108600040e020b0c106000403192f020b60000040706090250003020b1218086000e2d020b0810600032a020b1808600042207370e0b600020b1808101160004030e1b0b0c6001303151902016000407250b18106000e0b0a08101160004320e1b0b1060004030b0a18086
  | 6, 0, 2 => 0x31d020b18086000403150b0a266000307010a18116000407020b183060004030e201e016000403072b0205600030e020b0c1160004070b0a1810600320e020b101160004220e210108600040335020b266000406020b180860000040717020b5001a070e02011060004060e0b0a086000415020b26106000429280b0a08600070201181011600031a2819020b6001d0e020b081060003440e19020b600070e010a101160004070d02181060003072e0e020b600041607430e0b6040307190d09027000403020b180c6000403020b26006001303360e1e0b60004032b090208600040315020126600070e250b10116
  | 6, 0, 3 => 0x71d0e1b0b10600043519020b1060004030e1e0b346000422210b180860004161542020b60004242302011860004031519010a600072d020b18106001a07020b181060004031f1e0118600040e0241081060004030e0227086001a070e0b0a1060004031c1b0108600070b0a181011600040e201e0b10600040201180810600060e020b08116002928020b081160004031c0e0d08600040e010a081060004030e0240086000403070233186000315020b2612600041519020110600040307320e0d600031a0e020b26600043f020b3e08600070e0d021011600031a070e010a600041607140e02600071c1b0b10116
  | 6, 0, 4 => 0xe02010810116000415190b0a1060004070e25011060003070e023311600041f1e0b181060004310e020b08600130307430e0b600040e0d020810600040319020b0060004031543190b600041c1b0b081060013030e19250b6000403010a18086000315020b26116
  | 7, 0, 0 => 0x4070e2c4e0b1070003070e0d020b11700040e026d0b081070004030e020b18087000407020b1810947000407020b189010700130307950e020b700040361070b0a18700040e021b0b081070000031a07020b1860003070e022101117000407060e020b087000429030e0b0a08700044b0e020b08107000403075e0e020b70004290728020b087000403020b183e087000003071d0e020160004030732020b18700030e19020b08117000403159519020b700040e4f020b081070004030781020b187000403070e020b8070004074d0e020b107000403a0070e020b7000416030e020b0870000031a070e0b0a600240307020b181170000041f0e1e0b10600042207020b1810700040307390e020b7
  | 7, 0, 1 => 0x46507020b18107000004020b1808106000403070e250b1070061070e020b10117000429074928020b7000003071d0e1b0b60004039e0e020b087000403073b0201187000004033519020b6000416070e42020b700040307aa0e020b7000429030e020b087000403070e19010a700043f03070e0b0a70004030e02010a0870000040e0b0a081060004030e021e010870004070e62020b1070004031c020b180870004510e020b08107000403070ea2020b700040307880e020b70003070e09020b117000403024e0b18087000422070e19210b700042903020b180870000041519020b10600043f03070b0a18700000403072b090260004034a020b18087000003072d020b1860003230e020b08117
  | 7, 0, 2 => 0x4034f020b1808700000403070e25016000403074d020b18700040307430e190b700046c070e28020b700030728020b1811700000424230e0b0a6000004031f1e0b18600030e2c020b081170000071d0e020b1060004070e020118107000403070e20020170000040e020b081060003070e4c020b1170004030769020b187000403072302011870003070e020b26117000004030e0d020860003070e280b0a1170004030e57020b08700040307020b186870004030e020b086f700030e020b08101170004030e280201087000004031c1b0b086000407500e020b1070004030719020118700046a030e020b087000403350e020b08700043f0307020b18700048c0307020b187000403950e020b087
  | 7, 0, 3 => 0x40e020b0a08107000403490e020b08700040e021e0b08107000403070e55020b700030e020b18081170004070e024e01107000474070e28020b70000031a0e19020b600048d0307020b187000445070e19020b70004037d070e020b7000403070e620b0a70000040706020b186000403070e58020b7000451030e0b0a0870004070e4a0201107000403026d0b1808700042b0e020b0810700040352020b180870013030e19020b087000403320e19020b7000403021b0b180870000030e0201081160000042423020b1860004034b020b180870000040315190b0a600031a070e28020b7000407a90e020b10700000407060e0b0a600047a0307020b1870000042907280b0a60004030e6d0b0a087
  | 7, 0, 4 => 0x3f0307020b18117000403070e010a187000004030e0b0a0860004070e20020b1070004660307020b1870004030779020b187000403070e190d02700031c0e020b0811700036107020b181170004038b070e020b7000403071c191b0b70029030e020b08117000407020b18106e70004033d070201187000403077c0e020b70004030e020ba10870004070e02010810700040719020b18107000407020b181048700046503070b0a187000004030b0a1808600047103320e020b7000403070201181070004070e0b0a106e70004073b020b1810700000422070e210160004030762020b187000307320e020b1170004030796020b18700045103020b180870004070e190b0a1070003070e81020b117
  | 7, 0, 5 => 0x3070e9a19020b700040307360e970b70004070e021b011070004034d0e19020b700049b030e020b08700042903070e010a70004074b0e02011070000030e2a020b086000474030e020b087000422030e0201087000403070e4a010a70004032b0e0b0a0870000043f07020b3e60003070e190201117001303150e19020b70004031f07020118700000e020b0810116001303070e020b267000403070e530201700048f0307020b1870004030e09020b08700040376070e020b7000003071d020b18600000403020b18086000004070e250b1060004071c0e1b0b1070004031519020b2670004030e0d020b0870004039207020b18700046c030e020b0870004070e19020b1070004030e022101087
  | 7, 0, 6 => 0x403070e024060004030e280b0a087000024230e020b1160004290e28020b0870004072c020b1810700040307140e1902700040307820e020b700043d07020b18107000403078e020b187000403070e020b3470022031a070e020b7000403070e010a087000415070e020110700040307190b0a1870003074d0e020b117000403020b0a18087000403021e0b180870000031f0e1e0b11600000403320e02016000451030e026d0b700220307020b18117000486030e020b08700040307750e020b700041607230e020b7000403070e020b9c70004070e2c1e0b107000403152819020b7000403020b26180870004032b020b18087000403020b183a0870003070e69020b117000307230e0201117
  | 7, 0, 7 => 0x4030720020b1870004030767020b1870003070e62020b11700000403071c1b0160004035f0e020b087000307960e020b1170051030e020b081170403070e190d020b80004075a0e020b10700040307490e02477000403070e0b0a6e7046c03070e19020b80004030e020b5b087000403078e0e020b70000040702011810600040328020b18087000403070e190b0a70000031519020b116000403500e02010870004070e0b0a18107000007060e020b11600040307230b0a1870000290728020b116000429032b020b08700030e026d0b0811700040307020118087000403020b183c0870004030e4c020b08700000403071c0e0d6000403990e020b087000004070e010a1060004030e020b26087
  | 7, 0, 8 => 0x3070e79020b1170004074a020b181070004034b0e020b267000403320e020b0870004070e0b0a107070004930307020b1870004070e020b1810700650307020b18117000003020b18081160004030e81020b087000403070e59020b7000407a80e020b1070013030e19021e0b7000429070e0b0a107000403074b0e010a7000004070e0241106000403026b0b180870004220e020b081070004070e4a0b0a1070000040307250b18600070e19020b1011700041f07020b18107006503070e0b0a1170000030e0b0a0811600000403070e02276000403070e87020b700040307020b186e70004070e53020b1070403070e1909020b80004030e020b3c0870004030719020b18700000403320e1b0b6
  | 7, 0, 9 => 0x407020b18106f700031f070e0201117000403150e020b26700a603070e53020b700040307490e020170004070e021e01107000004030e020b0c60004030e84020b087000403073519020b70000042207210b186000403072c1e0b1870004033d070b0a18700040315070e010a70004070e0b0a081070000030e2d020b0860004070e0b0a106f70004071c020b18107000407020b1810707000392070e020b117001303070e19020170004030e026b0b087000403078a0e020b700040307021b0118700040e020b0810947000004320e020b106000407024e0b181070065031a070e020b7000403070b0a1810700042907020b18107000429030720020b70003070e19020b1270004030ea2020b087
  | 7, 0, 10 => 0x70e2c020b1011700000431070e020b6000013031519020b6001303070e42020b70003070e190b0a117000403075a020b187000004034619020b6000403070e530b0a7000004070e0d0210600041603070e0b0a70004070e57020b1070004030e19020108700043f030e020b08700043f0307026b0b70004650e020b0810700040302210b18087000403830e020b087000403151942020b7000004071c1b0b1060004240307020118700032b0e020b08117000004033d020b3c6000403075a0e0b0a7000403070e1998027000422031519020b7000407350e020b1070000040307010a1860004500e020b08107000403070e020b05700042403070e010a700043f03020b18087000407020b1808107
  | 7, 0, 11 => 0x307670e020b11700000403073b0b3a60003070e192d020b7000415070e0b0a10700046c07230e020b7000403079f0e020b700030723020b1811700042403320e020b700047a030e020b0870013070e19020b107000407021b0b18107000004030e19250b60004034d0e020b08700000403390e020b60000070e02011011600030e28020b081170004074b020b1810700042203020b18087000307230e0b0a1170003070e02010811700030719020b18117000403070e7e020b7000403850e020b087000403070e0d73027000403070e28250b70004030e69020b087000403230e02010870004030753020b1870004160307020b1870004030e020b086870004074b0e0b0a107000403079d0e020b7
  | 7, 0, 12 => 0x465030e0b0a087000403070e020126700040350020b180870004030e020b263c7000403070e0b0a6f70003070e0b0a1011700042407020b181070004030e020108107000403360e191e0b7040354070e09020b80004030e192c1e0b7000403960e020b0870004030702010a187000004070b0a1810600040307021e01187000403500e0b0a0870004030e021e0b267000465031519020b7000424070e0b0a107000403070b0a1808700041507020b18107000003070e250b116000004060e020b086001f070e020b101170004030e2c4e0b0870000042928020b086000403320e020b0c7000403020b1890087000407490e020b1070000040332020b18600070e020b18101170003070e20020b117
  | 7, 0, 13 => 0x1303070e190b0a7000003070e010a116000004070e020b306000403070e020b7f7000403920e020b0870003072c020b181170004070e09020b10700033d07020b1811700000407020b1810600031a070e020b10700070e020b0810117000403070e0d090270004030e79020b08700000403070d021860004030757020b18700040307890e020b700046503020b1808700040307020b186f7000307020b181011700040307280201187000429030e0247087000022070e210b1160003070e2c1e0b117000004070e0b0a106000403071909020b700040e020b08106e700071c0e020b10117000403070e4c0201700042b060e020b0870004030795020b18700040e19020b081070003070e021b01117
  | 7, 0, 14 => 0x45103070e0b0a700040307026d0b18700042403070b0a1870004030e024e010870022030e020b08117000429030e020108700031f07020b181170004030e4a0201087000407020b0a18107000403070e73020b70003070e53020b1170004030749020b187000407021e0b18107000403070ea7020b7000403990719020b70000031a070e02016000407060e19020b70000040315020b26600044b0e19020b107000429072819020b70004072b020b181070003075a0e020b117000407020b183a10700040307320e020170013030719020b18700040307490e0b0a70000030702011811600000407060e2c02600040377070e020b70000031d0e020b08600031a070e2c020b70004030e020118087
  | 7, 0, 15 => 0x45d030e020b08700046c0307020b187000403070e020ba170004070e020b3c1070000040e02010810600040307022101187000403070e091e0b700000403070b0a1860015070e020b1011700000429072802476000403070e78020b700040307720e020b7000403230e0b0a08700040307320e1b0b700040319020b1808700046c03070e0b0a7000003320e020b1160004510307020b187000403070e020b63700000403070e023360004030e19021e01700040307490e020b700040e2c020b081070004033b020b1808700043f03070201187000407020b183c1070004070e4c020b1070004030e190b0a0870004150e19020b10700070e021b0b101170004031c0e02010870004070e020b26107
  | 7, 1, 0 => 0x4030e4f02010870065030e020b08117000403074d0e020170004032b0e2c020870003070e28020111700001a070e020b106000003071c1b0b116000004031f0e1e0160004740307020b187000422030702011870004031519020b107000407320e020b10700046503070e250b7000307950e020b117000007020b18101160004031c0e1b0b0870004030e020b086e70003500e020b081170004030709020b1870004030e1957020b70003071d0e19020b70004030e020b0848700040e020b1808107000307020b1808117000407026b0b18107000403670e020b087042403070e09020b800040323020b180870003070e02010a117000403070d020b1870000070e0b0a101160003070e021e01117
  | 7, 1, 1 => 0x43f07020b1810700040364070e020b7000424230e020b18700130307360e020b70000042907280201600041c0e020b08107000403070e0b0a267000416031519020b700040e020b0810707000403070e020b567000403520e02010870004030e021b010870004860307020b18700046107020b1810700040e024e0b081070004a4030e020b0870004030e0b0a0810700000424230e020160004290e020b081070004034b0e0201087000403070e020ba570004039107020b18700040e4a020b08107000403153619020b70000070e2d020b106000403070e020b0c700040315192c020b7000003070e0d021160003070e57020b117000403070e020b5c7000416070e28020b7000407065a0e020b7
  | 7, 1, 2 => 0x446070e020b107000004030e201e0b60003070e026d0b117000004030201180860003070e020b261270004030e0b0a18087000403076b0b0a187000403070e020b2670004a3030e020b08700070e020b0a101170004039d0e020b087000307490e020b11700070e021e0b101170004070e190201107000004030e010a08600040307600e020b70004032c020b1808700072b0e020b10117000403074c020b187000451030e020108700040e020b08106f700040307020b2618700040307280b0a18700040391070e020b700047a07230e020b700040e19021e0b107000403020b1808107000403070e2f020b700040307370e020b700000403151902016000004220e210b0860004030e2c1e0b087
  | 7, 1, 3 => 0x403070e7b020b70000040728020b486000003070b0a18116000407850e020b1070004035a0e020b087
  | 8, 0, 0 => 0x42203074b0e020b80004031c0e020b0870403070e28021e0b80004036107020b1870403070e19020b108000403070e84020b7046503070e024e0b80004030e024e0b087000429030e020b087046503070e4a020b80004030e4a020b087000003070e2d020b6000403070e026b0b70004070e020b1094700040361070e0b0a70000031a070e020b600040307320e020b700000307020b18116000403070e81020b7002403070e020b117046503070e020b1880004030e020b1808700040307026b0b187000422070e020b107000003070e0b0a116042203070e020b088000403070e020b3c7000004030e0201086000315070e020b117040307230e19020b8000403070e020b5b70004030728020b187
  | 8, 0, 1 => 0x46503074b0e020b80004034b0e020b0870403070e4a19020b800047a03070e020b70004030e4f020b087000403074d0e020b70003070e28020b117040307230e020b188000004031f0e1e0b60004220307020b18700040307850e020b7000403070e69020b700040307230e0201700040346070e020b7000403070e020b6870403070e19020b1880003070e020b0a1170003070e021e0b117000403070e190201704220315070e020b800043f03070e020b7000465070e020b1070000040e020b081060004030702210b18700040307830e020b7041603070e19020b80003072b0e020b117046503070e020b088040307360e19020b80403070e192c020b80004030e19021e0b700043f0307020b187
  | 8, 0, 2 => 0x4033d070e020b1880004650307020b18700000403020b18086000361070e020b11700042903070e024770004070e020b106e70403070e020b181080004072b060e020b70004070e19020b10700046503070e0b0a7000004030e0b0a086000403070e020110704650315070e020b8000403070e62020b700040307960e020b7000451030e020b087040307230e024e0b8040307950e19020b8040307230e4a020b8000004031519020b60403071c0e19020b800000407060e020b6000403070e2c4e0b7000004290728020b60004030e026d0b08700040307020b18907000403520e020b087046503070e021b0b80403070e19024e0b80004030e021b0b087042903070e19020b800000424230e020b6
  | 8, 0, 3 => 0x403070e190b0a7000403071c0e020170004030e020b0a0870403070e2c020b088046503070e021e0b80004030e021e0b087000403070e024e017002203070e020b11700042903070e02017000403070e4a02017040307230e021b0b80004032b0e020b0870403070e020b081080403074b230e020b804031f070e020b188040352070e19020b8042903070e2c020b80403070e19021b0b80004031f070e020170403070e4a2c020b80003070e02210b1170403074b0e19020b8000003071d0e020b6000403070e0201187000004030e020b0860403070e024e0b1080403070e4a020b1080403070e1902970b800040392070e020b700040307500e020b7000403070e79020b70403070e2c020b188
  | 8, 0, 4 => 0x403072b0e19020b80004070e4a020b10700049303070e020b7040315070e020b108006503070e020b1170000030e020b08116042903070e020b088000403072b0e2c0270403074b0e2c020b800000403070e250b600041f070e020b107000403071c0e1b0b7000403070e020b6e7000403070e19020b7000403070e020b4870403070e021b0b1080004070e020b18107000403070e20020b700040307670e020b70403074b0e020b1080004030723020b18700045d03070e020b70403070e020b18088000004070e02011060004030e28020b08700040307230e0b0a7000403070e02010870004030719020b1870429031f070e020b80403070e19ab020b80004070e2c020b107000403073b020b187
  | 8, 0, 5 => 0x4030702011860004030e02210b087000403070e0b0a18700042403070e020170004a303070e020b704290307490e020b80403070e2819020b800000403070e010a6000403072c020b1870004033d07020b18700040315070e020170004070e020b08107040307230e021e0b8042403070e2c020b80004070e020b106f700040307020b1810700000422070e210b6000403070e2c1e0b70403070e19020b0a80403070e19021e0b80004071c0e020b1070004070e020b10707040315070e2c020b800040352070e02017000403070e021b0170004070e024e0b1070004a403070e020b7000403070e0b0a107000429070e020b107000403074b0e020170403070e19020b2680403071c0e020b088
  | 8, 0, 6 => 0x403500e020b087000403079e0e020b7000424070e020b10700040307020b1808700042903070e020b7000403070e02010a7000004070e0b0a106000403070e021e017000403070e0b0a087000415070e020b107000403071c020b18700000403320e020b600040307024e0b187042403071c0e020b80004290307020b187000403074a020b187000307230e020b117000403070e020b1870004070e021b0b1070403072b5a0e020b800042903070e0b0a70004074b0e020b1070403070e021e0b10800040307020b183e7000422030e020b087000403070e4a0b0a70003070e19020b1170004031f07020b187000403070e53020b700041603070e020b7000403075a0e020b7042403070e020b188
  | 8, 0, 7 => 0x4070e020b0a10700040307490e020b70004070e021e0b1070003070e020b181170403070e28024e0b800040315070e0b0a70004072b0e020b1070403070e4a28020b80004035207020b187001303070e19020b700040307021b0b187000003070e0201116000403074b020b1870403072b0e020b08800040352070e0b0a70403070e1942020b8000403074b0e0b0a70003070e2c020b117042203070e19020b8000004070e020b1060403070e28020b18800000403070e0d026000403070e57020b7000465030e020b087000403070e020b6f70003070e020b10117000403070e280201700000403071c1b0b600040307350e020b700040307950e020b700000407020b181060403070e1902210b8
  | 8, 0, 8 => 0x42203070e020b1880403070e28021b0b8042403072b0e020b80403074b0e28020b800047403070e020b700042203070e02017000403072b0e0b0a70000070e020b10116000403070e09020b70000040307020b18604290361070e020b80003070e020b08117000403230e020b087000403070e0d020b700046c03070e020b7000403070e022101700000403070e0b0a60003071c0e020b117046503070e19020b80004030e19020b087043f03070e020b18800045103070e020b7002903070e020b117000403ac070e020b70004240307020b187040361070e020b1880403070e28020b08800000403070b0a186000403070e026d0b700042403070e0b0a70004031507020b18700031f070e020b117
  | 8, 0, 9 => 0x4030e2c020b08700042903072b020b700040307020b183c7000403070e4c020b700040399070e020b7000403150e19020b70003070e021b0b117000403070e020b267042203070e4a020b8000403070e280b0a7000429070e28020b70004030e020b08107040315070e28020b800040307020b0a18700040307021e0b18700048603070e020b7000461070e020b1070004034b0e19020b7000403072b020b18700040307020b183a7
  | 9, 0, 0 => 0x403070e020b0a70403070e021e0b70403072b0e020b7000403070e020b600040307020b186042403070e020b7000403070e0b0a6040315070e020b7040352070e020b70403070e021b0b70403074b0e020b70004070e020b1060403070e020b0870403071c0e020b70403070e024e0b7042903070e020b70403070e4a020b704031f070e020b70403070e020b187000403070e020160403070e2c020b70403070e020b107040307230e020b70403070e19020b7046503070e020b70004030e020b086042203070e020b70403070e02210b7040361070e020b70003070e020b1160403070e28020b7
  | 10, 0, 0 => 0x403070e020b6
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 44
  | 6 => 60
  | 7 => 68
  | 8 => 68
  | 9 => 60
  | 10 => 52
  | _ => 0
def stateM : Nat → Nat
  | 5 => 0xfffffffffff
  | 6 => 0xfffffffffffffff
  | 7 => 0xfffffffffffffffff
  | 8 => 0xfffffffffffffffff
  | 9 => 0xfffffffffffffff
  | 10 => 0xfffffffffffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x3f01f80000000000070e180071c07fc00001c7300039fff03ff1fff1fe01fff00001c7300039f1f03f1ff831f3c181d00000000000007fc007f01ff07e007ff0380fe00f81ff800007000000700000003fffffffffff80303ffffff0000000003ff0000ffe00000000e007ce0c3e7e203ffe38cfffc60e003f01f80ff03fffc
  | 1 => 0x38efe7cf8dfffe200000000e003e000007ee1fc00000000007ee1fce7dfe7fe00000000000007e003f0ff80000000000000e000001c0000038f1e7ff8e3f80300701e7f0703f80303ffe000fffc000003f0ff80ff1ffffc00001c7300039f1f03ffffff001c000003ff1fff0000000000000000ffffffff0000ffff001fffff
  | 2 => 0x1c00e003fffc000efc7f001c0000000e1c7f00000000000e1c7fe0c3ffff0070fdf3071f9fff007f01ff0000000003ffe180fffc07fc007000000700000003ffe180fffc00e003ff1fffffe3ffff00000000e003e7e003fffe00fffff80003800000f800000003ff007cffe3e7e2000e0000e0c000000000e000001c07e0
  | 3 => 0x3ff1e7fffe3f803038f0000f8e00000038ffe7ff8fff80303801e00f803f800038f1e7ff8e3ffe3000e007ce0c3e0020000e000001c000003ff1fffffe3ffff000ee000e0dc0000000ee07ce0dfe7e20070e180e71fe7fc03ff1fffffe3f81f03ffe38cfffc60000000e000e01fe00003ff020cffe060000000fdf3001f9fff
  | 4 => 0x7f01ffe7e3e7ff000e007c0000000003800000f803e00000700000070007e00380fe00000000000070e180000000000380e000f81c000000001e7f0003f803000000000000071c03f0ff80071c07fc03ff0000ffe0000003f0ff80001c0000000e007ce0c3e7e2000000000000000000001c7f0003ffff00001e7f0003ff1f
  | 5 => 0x7ffdff07ff9fff0380fc00f81f980003fffdf3ffff9fff03ff03ffffe067ff038f020cf8e060000000fc00001f9800000e1c00e0c3f800000e0000e0c007fc00001c00e003f80003ffe3ff1ffc07ff00000000000000000380fe00f81ffffc0070e000071c000003ff00000000000003ff01ffffe007ff007fe1ff07fc07ff
  | 6 => 0xfe00001ff8000000e180001c07fc007f1dff07e39fff03ffe180ffe00000038f1e7ff8e3ff1f03ff1dffffe39fff007000000700071c0000e38c001c60e003801c00f803980003ff1e7fffe3ff1f03ff1c73ffe39f1f0380e000f81c071c03ff1fffffe3f8e30000e000001c071c0380fe73f81fff1f0070fc00071f9800
  | 7 => 0x38ffffff8fff81f000000000000000003f00000ff03e7e000700000e703e000007000000700000003ff0000ffe3e00000001c73e003ff1f000000000000071c038ee000f8dc07e003800000f80007e003800000f800000003ff0000ffe007e000001c0000039800007ee000e7dfe00003ffe000ffffe0000000ffff00000000
  | 8 => 0x3ff1e7fffe0000003801e00f803f80003ff1e00ffe3f80003ff007cffe3e002038e007cf8000000007e007c07000000000ee07c001c000003800000f8000000007000000700000003ff007cffe00000007ee1fc071c07fc000e1c7f00039f1f007ee180e7dc07fc0000e000e01c0000000e1c73e0c39f1f007fffff07fc1fff
  | 9 => 0x380e000f80000000070fdf300039f1f007f01ff07e007ff007f1fff07e3ffff03ffe1fffffc07ff0000e000ffffffff03f0e180ff1c07fc00001c7300039f1f000000000000000000701c7307039f1f0000fc73001f9f1f0000007c0003e7e203fffe00ffe0000003801c73f8039f1f038f1e7ff8e3f803038f1e7f00000000
  | 10 => 0x380fe7300039f1f0000e000000000000380e000001c00000070ffff071c07fc0070ff80071ffffc0070e0000700000003ffffff071c0000038f1ffff8e3ffff03ffe180071c07fc03ff1c7300039f1f00700180070007fc00700180070007fc03f0e180f8000000
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x1bc17bd800244900274e995579caffc00b77df76befbfff00b711d70be016db00933cf329679f1f02d1b8831d34181d00346995438caffc003701d703e006db03c8fe28fc1ff92402f790427ff1124b03cb966abc73500303ffffff8002449003ff9042fff1124b012e477ce2cbe7e2036cc30cd69860e001bc17bdab8356d8
  | 1 => 0x3eeff7cfedfffe601084628e00be120037eeffd80024490037eeffdf7dfeffe002441144288a7e003fcffbd800244900240e800541ca924018b166aa8635003027486285792424803fff842fffdbb6f03fcffbdff9ffffc02d3bcf37d779f1f03ffffffd41eedb401bf17ff80024490000000007ffdbb6f00006fbd000eedb4
  | 2 => 0x1bc7fbdeb8ffffc03ffffffd41eedb401bf7fff8002449001bf7fffebefffff02f7fdf77fffbfff013f47ff8002449003fff9d7fffdbfff0274800057900248036cc104d69820e001bf17ffabe356db012c473ce28be7e003fffe6afffffb6f03c89000fc11100003ffd77efffbf7eb012e0040e2c102420264e914569cafe4
  | 3 => 0x3ff966afff3524b018b1042a861100303cbfe6afc7ff92701881628a803500001af577eeaebf7e3010a0668a04340020348ee28d41ee92400b711d72be116db036ee840f6ddab66036eef7cf6dfefe6037cefbdf79feffc019b16eba963501b03488208941040000348ee28f41fe92403ff924afff1524b00006db5000eadb4
  | 4 => 0x13f47ffe3ebe7fb012e477c8002448003c8d628fc1bf1200274c1145798a7e803c8fe28800240000274e9950000049003c8f800fc1db9240000062800024000009338d329659f1f03fcffbdd79eeffc03ffd042fff9b36b03fcffbdd41eedb4036ec77cf6dbe7e2024080005410000000937fff296fffbf00933efb2967df1f
  | 5 => 0x2f7fdf77fffbfff03c8fc20fc1fb92403fffdf7ffffbfff013f03df83e046db010802088000400002c0fc207c1fb92401bf7e6aebeffb6f01bf79d7ebedbfff01887e28e80ff924027781d717f006db00006800400ca92403fcffbdff9ffffc0274e800579cab6c03ff90428000000003ff91d7fff116db0277e9d757fcafff
  | 6 => 0x6e28000ee92400006995000cadb400b73df72be79fdf03fff9d7fff116db019b3efba967df1f03ffbdf7fff79fdf0274a89157948f5c0000430c000860a003c8bc20fc17990403ffbefbfff7df5f03ffbcf3fff79f5f03dbf8d3fd7dbf3f01af176eaae350c30250e891551caf3c03dbfefbfd7fff3f02f7fc627fffbb6f
  | 7 => 0x18b3eeba86758170240c0005418a12003fcd73cff9bf7e8037cc628f79be3680274c0005798a36803ffd66afffbf36b019b7efbe96fff3f00106891410caf3c03eef954feddbfe603ecd114fe99b7e003c8d000fc19b12003ffd156fff9b7eb00807c20680fb924037eee68f7dfeb6e03fffe6afffffb6f00006fbd00024490
  | 8 => 0x3ff966afff3524b03c89628fc13500003ff966afff3524b03ff966afff3524b03eed77cfc135480037ec77cd79246c8036eef7cd41eeda403c8d628fc1350000274c114579006c803ffd77efff356cb037eeffdd79eeffc01bf7fffa967df9f037ee9d5f7ddaffe0348e800f41da92401bf3cf3ebe79f5f003729d703e40edf
  | 9 => 0x3c8f800fc11100002f7fdf729679f9f027781d757f006db003707ff03e246db03fff9d7fffdbfff0240e8007ffdbb6f03fcf995ff9dbffc00937cf3696fbf3f000040004008a12002f7bcf37ff79f5f02d3fcf37d7fbf3f0000473c000ae5a003fffe6afff3524b03dbbcf3fd779f1f03cb966afc735003018b166a80024000
  | 10 => 0x3dbfefba967df1f0240e8000000000003c8f800d41ca9240274efbd579eeffc0274efbd579eeffc0274e8005790024803ffffffd79eeffc018b17ffa863549303fff9d7d79caffc03ffbcf3a9679f1f02748195579006d80034299503848fdc03fcf995fc111490
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 173 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem wd_0 : ∀ i, 0 ≤ i → i < 128 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem wd_128 : ∀ i, 128 ≤ i → i < 173 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 45 128 = true)
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 173 → wireDOK i = true := (range_split wd_0 wd_128)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 173 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 173 then wireAt i else 0
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
  | 5 => 14
  | 6 => 507
  | 7 => 2074
  | 8 => 345
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xfa90f0c4c92142c2c1ad59109dbd77f18fc268d97fc35e3c7be6055a5c0301a35a19fa315996866a4d66f3ac3fb00fa0395ec9d029b6a34a
  | 6, 0, 0 => 0x1d81b2001ca3a2361c10e90c1b33bc301b2db8df1af2b3361a14e5e518788e92186a3d78179d7b2f177cf42716fdc89215ea848115df0c7915b6260f13d10dfe135968a4134e25c512c99a33129450961261a41211f1543211e7a20710fcd26010cf35f01096048b0fef01900f960dc50f8d2d210e8587a80e45865c0db856600d6e0c770d5a28a30d467bd70ce939780c6359a20bde67650a9192a80a19173e09e30787096421e108fa838708dfec5a08c2d36f087fee6d08729adb0775b51706f75c6206d64cab063405ac063313e605c8862204f2824904c6785d03d01aba03c35f1402e68e1902aa1fe5026f0bc30221550b01e8d7be01a4a57800c12c5f
  | 6, 0, 1 => 0x42aa353b426f7868421feec141f837be3f6ab8653f45a4083d45347a3d2456c23cfeaab63bcbcf173adaf93a3ab26e893aa1d80a3a978ffa39afdadd39aa1ef9398141e2394f07e9394ef5d73756b8d636f6d4833696e6af3677262935de276a33fb1bb5333c1b1c3260b0d932601560324b7fca31db0c2531bbe12a318296ff30ed8f3230e6b16c30b69e3e3029873f2fa3d4942f6504052da64bb72d536e152d12c6cb2c4d82672c1a96c72b314b9f2b22a8332a7f87ff29fd548529d0fcde2904d510286fede727daaae5267bd39d25ce08de25814378248b8add2456e409234f190922818311221a63eb217a179c2140a5ac20e11235208acbdb20151c66
  | 6, 0, 2 => 0x5c45214e5bff65e95bbb2d5a5acc587759ede07959e4ab9059b6e18d597a06a55915cc735905aebb58486b77573ec9395701612656b7806255e7d3ff55e3ec9a553a0940539d103c53620a935354503952ff896951708c5650a5f05450a2cbfe5086ebaa50806a234f84d3574f79d9894f5a83914f3ec98c4f176df24ebf55304e3663434e22b7804ddf67e54d118c334c7ca8eb4c484ebf4be8775f4bceeb024bcb8f784badcd024ac0cd254a8fdf314a38d6824a2dc6a349e7f20d4998497d4966ecbc46fe9f664665e2f2460c36c945bbfe35456013a8453fb8e9451c3870444dbec24413c14943f1d901439fccf943829424437d69064358214742ba2627
  | 6, 0, 3 => 0x832c6aa282ff368e82fd501082dcd4b381eec8bf809c82647fd1d1f57f6df6c37e2b55927e2a5df07e27d36b7d1bd0f67ceda0887c8f07627c19bc257c12fd457bfacb9d7adecfc57988d5717953f26f7951d6857871fa43773d33c476caa53c759e3192753fabb074c03754749160a273e04a0973272880723199737135056b70a75ed9708c63d87044ac116f992ba16f5390286ead4a876e8983726e3c6d976de6b7566c9bb11a6bc21c2d6a22cbbd69d3cb7a69863ed46898de9c68400cfa6721459a667ce951662d0d2a654e08ff6535b5c9652c8946650a2dc764bd1b69626c10ad6253d3c761c16e9561af7522610e58cd5f189b885eb31ec05d51d110
  | 6, 0, 4 => 0xa3916ffba31cb31aa2cd276da2c75f9aa2067ec3a1bfbc20a0ed1e35a0a24794a037775ca031c9ca9f89b7959e92da489e546ba79d7985249c4f25b59bd57bd29b6b63729b4417a99a17d9e199e4565f9982dfb69976cac8996a0f2298d953e19876547a980cef3b97f6bfe4976c16bd96a6d259968d45fc9583c14292acaae39233fad7920d279191cc8e6b9126e41b9122fac29087acc1907a592f8fd4ad9e8f869baa8f0dbda68f085cec8e9883348e6d3b1c8e3bc4008da868fb8d1e2ab18cfb9a798c73b3dd8c3ffdb58bd671358afbeac48a04d4ab89ac63cc8974172987bee8ad87bbc5dd870f3af186c28627866a38fe84e8fdf783fe4113835496e5
  | 6, 0, 5 => 0xc1f3b5e4c1890036c15ab118c140e382c09ae832c03d3c8cc026380dc0256cb3bf935932bf8c5b38bf2aa141bf1fa773bed52879bdbb5a85bd6cf8e1bd14695dbc2283abba4ef104b99f5c10b929c117b83b6958b7cd708fb7c4cfa9b7a6ea88b694c7b0b6283af4b589334ab57890e8b51eb63ab459f37cb458ff93b3a94b1fb3782e48b2fdef31b29dc3f6b14b2561b0a5b82bb022a1b9b0154e27afddc2b5af9908dbaf37411eaf12d4d6adf91cebaddbe416acf78e29aca478a0a9c40857a94758c4a9250586a8bdd6e7a8a5dfeea7f6e6efa7efaae3a79c1640a7451882a6465b06a644b697a63cb499a5e241f6a5a85006a54e670aa4a3068aa42b4014
  | 6, 0, 6 => 0xdf8ea21bdf814e89df198746df0d9ccade3999fbdd929700dd46ceb2dcd6db01db79b540db457584db1f985edaea1147da4c1573d9069a79d8932228d85fcda4d77faa33d6f5010cd6e37d0ad6c71384d6bce295d687aaa4d66668dfd62fbca8d62383ddd622b73bd616304bd599eaffd5791daad563bdedd50cab91d3f9ff0fd3d79b1cd3b36f06d2274180d1b27d2dd180e121cfc4ea7bcf568aebcf483ae8cebe6972cdfac662cd77bd25ccef9d05cc8a5d3ecc557d16cbc760d3ca1023fbc9cd9f4ec992521fc8e9b08cc8c841bec74adca0c65d4e4cc6385980c447306bc37d61c1c33790f3c2fa1e23c2def8e5c2ba4776c2b554f1c2742c08c231182e
  | 6, 0, 7 => 0xff959867ff4d08e5ff077c9dfeb38b90fdf0016cfde6bd08fdbc4a2bfd05fad5fcf5e330fcc7f5a8fc78a37afb8e4ecdfb3fc388fb04bddffa9bb520f93a1c18f91b24d3f84c24aff82f39e7f79ebb9cf762d39af6b508dbf6b1b85bf661ca94f61be41df516b206f30c3217f1c23678f11bd619f06a3befeff23829ef11eb39ee8ba7d5edef1b85ede7e845ed9e4c1eed3dac49ec13b86fea48128fea2b21e7e9c92ce9e884a584e7cbd522e75b933ce63e1eb0e63b80a5e605b5afe5bdf683e5943b56e5208997e4be1e00e43525c2e42bf0d9e3cae15ce35d99d1e359bb7fe28e4feae148a66fe123f52e
  | 7, 0, 0 => 0x8729adb083d26bf083d0d0907eaa76e07c7a31e07c54ddf07a58cff0774f8470774a5330737dedd071edf2906f749cc06e57ca506d4891806d46df1067c0c5b0642ce05063313e6062fa7450619e31105df2e7505c2b37a059daf68059bbd0a055f9278055ef6a305028d9804e091b504acadca04a0ac360451f4ec041cb05b03f2e17703e6094503ce694603b5648e0367149d035bb98b03477751033bcf23030a3cae02ce4b6e02a392aa02917d28022c97c00206ca5101ed469801ec392301e8a27c01e76e9e01a9edce01a68be6017b1b03016a2c55014e30ba0124f21000a19559009ebe4c006b5bf8004e043b004c7978004b64f500379789001f71bf
  | 7, 0, 1 => 0x105120260ff627ad0fe72a990fc560cc0fa9c1e20f97b7810f95c23a0f780a210f6c66920f686dc40f5d56f70f4f9ce60f1cde3d0ef0b7720ee773870ed77b7b0ed6b6d80e9c34060e8587a80e821ebc0e31969b0e17cc080dfbeab70dfa6d1f0dddced70dda8feb0dd83aac0dc548f10da59a5d0d79d9290d4ea6490d32c3940cf109030cd585dc0c8fb1910c65ac0d0c4e5f240b92d3d10b8d8e810b6bffcc0b658ee80b5757610b03f0440adec1170ac291fa0aba4c6d0a89f4ba0a7d15dd0a3e33590a3a0d400a24328f09e988c809e33ae009c68f8a09b683330984a56c09747a0f09191f43090c697f0909f17008df5de008d77fe808cb083e088bb673
  | 7, 0, 2 => 0x18f6de0818b72fcd188a748a187b2f6d187af5e4184913491808ead417f0a5e617e6d79c17a2c75c1798c2df171ddab2170aadc016cb1ea8164a3fb1161e1f0415fa176615ea2dc015df0c7915d84d9915c726f3157b5a91156d2d4f155cb516154673b51530df23151dc3df146d255d142db0381419b33013eb160713cffff713c6527f13bdf11913b43d3113ab6cc3138cc5f613686f99134e25c5131c44351315d12e13100f2312badba512b5664212a44300128bb9891252e518124e460d123b44b511f7a2ff11d5297011c3bc8a1199046f116cc9b7114eed1311498a8f113f7b351139848a1127f8d911237ea41102841810d68feb10aa5bfc108067cb
  | 7, 0, 3 => 0x236c7b1223619af9235262422309b3c522fc30e222db09d522d2e89b228f5815225601032222b3e5220503cd21f55e4921e2144c21c6d87521b94fc021a7515b21826396213c2611211aa262210b631720fec43620eb73c8206024fc20549af6204966a320433a85203a6ecf1fce75a31f8871d91f12a9411edb62021ec085971ebf87551e8de2b11e21cd4d1dfbc0ce1de6c7d71cf843df1ce944151cde0b751cc486e21c4314361c303b841c0fc7181bdf86681bb3eba81ba8047d1b801a1c1b0b998c1aebd7691aea5eef1ac4c55a1aa960b31a6a09231a39a8121a1c3af51a10de0e19bc3e6419aa6ddc199722491977834219748627194744fd1928bdfb
  | 7, 0, 4 => 0x2bce4ac52bc11f412bb6de2e2b31f6b32accb66e2abf42042aabc3ea2a8fd3a02a70be412a5541652a42d0652a4104882a3f22e129b484e1298bc455297c38b6295bb09528e8c03a28d27d25288c943d288a8ef4287d375b28736fa128478b4b28371d17282b026028235c44280ccaa627f900ef27f5011927eccb5327ccd7922786f5df277bfd27276c1381274f12de2741b01f271e4fe426f708f726d65f9d26c27e6f26bdf513269e5e7d26923ec42689ec4726724f6326716cae2666c6702661d63426593852264d5b9c25fad02f259c2a0f257a111a2553493a2537c62924eb385a24bdc3e824690a892449a2a323cd564223b2424023891cfe236da21d
  | 7, 0, 5 => 0x348300e0343f9dab3423b89d341901f533e7159433e705b933abe67033a624a4339a3b9833493d6b333c1b1c3333a5b832fc17d232e53b5932dfa60432d06d4d32c778e432940219327a00333279aee0322bc1b331c2745a31667af231601f57315bfdca30e9e20b30e47f8730dfa33b30d54c9a30cf69a73098ad6d30896e223010929c2fd0f1b42fc771ae2fb879da2f755c332f55ca092f4775b82f2f932e2f1bdc2a2f08d6592f07484d2ef58bac2ee917cc2e8bac6a2e79c9f52e6269bb2e3def2d2dbd9e352da6e06d2da66f232d9337d72d46d8552ce42dc92ce19c092cd56b3c2cd24e8c2c764eea2c6eea002c59e72d2c1ac5352c00a1052be9541c
  | 7, 0, 6 => 0x3d8950fd3d468bef3d3014d43d2d59613d1ebcd63cce35373cbf1c9d3c469f8f3bdb341a3bcbcf173bc809173bbc103d3b7b0b8e3b5d973a3aeca3da3a9c53d63a57bf6c3a54f6eb3a03cbab39dc95ba39d0e21b39bed33d39b79a1f39b72fed39a60da23994496d396b351b394f07e939353a54390f7b1f3909cf6038d71f70388c9bad3889d6393873f497386d3698385294e0383b36073808a26337ace5cf37a90d6b37a3dfcc378f7ea9373cfc45370bd009370b3fcb3709185a36fe7c5d36ebeecb36bb486a36a5a2b8369f09dd36908f733677c0e4366d1e1b364de9bc363306f935efb7cc35c6e79835852c57354b2ed735427ffb34e168ad348cbf68
  | 7, 0, 7 => 0x4503285344fb624244c8b5784461f69143f56eff43e9341843e6c29f436b3a374356eee94329f17b432411f6430f111842d860c942ad8ab642a1145242938fae426c479d4252923d422a4d0d4205d04941ff6f1e41fe673e41cbbddd41a8e6a1417948cd416ff734416bacca4169bf9e4167b45a41629edc413a5f9b412f0ba04122ba3f40ef18be40e506b04085327d4080a6fe403d92f24021b381402052ea40114274400204ed3fdae0823fba24703fab50003fa7b8ac3fa7924a3f7813d53f4827213f3205d63f252da43f2366d13effa6b23edb7a123ead9e393e9fe9133e7bd8083e6ca6e33e60a7733e1b8f303def3e613dd6474b3dbb4e813d96b5c6
  | 7, 0, 8 => 0x4cd6a0334c9320e84c8adfa44c84f8184c6a0abf4c6848c84c0054d34bee965c4bd749734bb454674b9041a64b7b05914b643fc64b34b3524b21d40f4b139a5d4b0ad4724addccb94ad1ae214ab3f9994a995f9a4a4e99134a4dd1db4a4ca1ff4a06002c49dbf98049d5ca7749c6ea2f498bffe249738f1e494ab295493966f1493931a44905218948e1d37548a67c7b487d72e8487a89944825126e48050f7047f18e7a47e6f64647d7c52147ce4d7e478345ba4721ead7470d89b44701084b46e245c046d8366646ce08c64689db144684514b4671549546571df24644e889463e3ff7463d6c754639537545f42d4a45ed680645c8e532456818c445109973
  | 7, 0, 9 => 0x548c8e8e54634bdf53d2630953ca8d5d53bfc0b253b3f6ed53896338537e23f153770cf253563928533cefe2531c369552b5353352b10586528fd164527a9afc526575bc52626ddc522e62e85214f52b52119ab9521132085201832951f8cbd351ea364051940288518dc5f4517e7bcb513de1c050f578d050ee023f50d7d76250d274de509fc760509d90eb505623895039cf455018ecf94ffec99c4fe12bdb4fdb08704f68fb544f4bdfe24f3a76054f248afd4f20a1d04ee69c8c4eaffbbb4e79a1c14e796c1e4e7522cd4e505f124e4f9ac64e37ff3b4e1a14854df9e3134dc68d764db94bee4d78cf864d7443cc4d55c85e4d1f1c334cf3253c4cedb262
  | 7, 0, 10 => 0x5d7af3195d714fc65d34488c5d3140355d1b4eb85d17d8fd5d12ce075ca684dc5c08eaaf5be653d35b6ca1675b3ec2c55ae24ad15a81fa1b5a41a7395a0dea3c59f2b46459ca8b1159628b8359592a72594fa3ad5933582b58fd707658eff19558e4f7c758b8c81958ad24265833c2495823f8cb580e28b45802866957ed89d857e2de0f57ca187457a3f41d5776af1e5775212f57523998574e0c8b572a73a156eac42f56e561ab5692d9775682f8b6565d8326564be97b5633e4ee5623e9e255f2818a55e6fb3255aeccd255acdb4c55908d5f558dc52655589b72553f4a91553a094055338e9d55303af6552280e554f8683a54e623cf54b43a7854b26b93
  | 7, 0, 11 => 0x65bcd2fb6590eea5659010486567bbad655c10c06552782e6541a5e9653e05e0652cd7dd652448f56502d07664e1132b64c1bd3364ae805d641ce52d6414dd59641223ac63bbb2bd63bad008639797ea636ac6bb633c0dcb63398a676335fe6a632e3b8562b01f8f629759f4627a6fbd6240cbab623d5947620b4bc061d1c6c361536b42613cf91d6110af96610aec2c60df5bbd609a59bd6046708f602b884960246d2f601e3a2c601b9bf6600c8c116002d9b35fff37cb5fdd77de5fb812115fa184f75f6c173f5f64116c5f3ec1a35f105d435ece265e5eb6e06c5e9b93905e772fc55e5d91205e45feae5e26ca935db6d6205da4c1f05d8c47db5d84ab1d
  | 7, 0, 12 => 0x6d0f38c46cf113686cee87286cc9ecf66c9f2d636c90d9126c85336f6c7236b96c601a436c5800166c548b7c6c3a35996c31ab276c2d4cab6c224c846c033dc06bf50f6e6bd38ee96bcd41946bcce0f06bbc9d636b6b9a4c6b184a996af8c9c96ae9063d6a7d83ef6a6014506a482c5369e8c6d369bfb2446985003c6970bf6f69692d5e6961df276948595b6926f4da6924f41a68e5a78d68d8907268d4269c68b1633668583447682b2f31681867e067cc4dea67bc94e6678c8372677a69246775f6766764f75267635da867239c6366df6b7066b305f366a87eac667246a2666a9dba663e7516662748cc6612249866028f3465e222a165d5f79765c00f37
  | 7, 0, 13 => 0x74527bb4744f2f70744a1f4f7442d8ba7405513173b882b473a71b3473726f357365b9717355347a733b925573391b267334830e7330cfda73245830731f1b4c730ce2877250633372502a2b722a6e7b72251df87210a91f7207ba907202ea8271ff901071a491b17192070d71782f1b716e997f7122b633711970c3710bb69670b4b9d6708c63d87088f7377077f9c0706ff8f5705b19206ff132df6fdcdba46f6051bc6f4f00336f2fcc576f2a9fc76f0bd7b46ea561246e7f23a66e4c31696e2bfd176e2473a76e1db4816e0b865c6de7547d6ddf3ab76dba01ca6db5097d6db1a7736dafa7f36d8a32d26d77114c6d5105186d4247ad6d400c0b6d22ccfb
  | 7, 0, 14 => 0x7cc052b87c4b25f67c34c7127c24d5ec7be9c0d87bd60b217bbd202b7ba2da817b98cb277b85e1927b8148cb7b76566a7b5477c17b38a1bb7b02e70b7ae705f37ad1df4d7aceb00f7aaa70187aa023a97a76d4d479dfb04a79c9865a79c7315379b4d911795080da794df86178f583f878d2ed1e78a4ffe57899d705787b7d20786f0601786350007815d74f78127cdd780bc8f677db7f2f77db3701779ff70377899cbf774a58f5772c596d76e9018376befbff76bc8db17689c99976459ea87638b1a27621da4575fdfe5175e6de7375d6d40b75c31e5475bededa75688164754fc9217501c58974cc140a74cbb07774c86fab7497834b7473fbda74700960
  | 7, 0, 15 => 0x851351e58502b0a584e174a884cf0882846a691884248597841c14d084158e56837bd53d8358bc12833c4781833293e083324f9182fc31f082f8ac1e82e3c47c82d47f5f82c9216982c214e082b28e1982a2633b82614b188243b3af81f413f781c99ac581969e81817d9b1b8167f757813ed259812b7915809469cb8056eaa180437db2800a3ee67ff396887fe9c1207fc67d417faf35d37f9bf5977f636da77f4b1a627f44ece87f343a4f7ee5d9eb7ec6754f7ec2ac277eb7710b7eb5c45a7ea5708e7e9278507e7303227e2b55927dee6bfc7dd770217dc1bf8b7db6cc217d99aff67d805dd57d7e08967d6b16db7d68e8707d4b68477d2b55c57ce0823d
  | 7, 1, 0 => 0x8e194a048e11b86e8dbe983e8d8d65968d6b98918d5f6f4c8d3eb5618cfd2e1b8cf11eac8cebfa108cc598778caf50f58ca960d08c8d9d078c83d95f8c64e1ee8c260f548c2028678bf8ba958bdc94a28bc6ad0f8b58d3908b438d778b13e0a18afb51c08aab50fe8a993b7c8a93bec18a81b0a88a2f019d8a1878e789ebf36c899d218f8999d50c8992ff45898e35fb898afbfc896ba8df89508b2a89472ebf88c457d7887437e5885015c787ea3fa7878ff92d877a78c987718b85873e90c98718462e870bce5086f5893586bfb66f869c64288683275186396688861c7e1a860d3b9a85d96a0e85c3ecee859fe550857e1b838564e97e855aaed08521287b
  | 7, 1, 1 => 0x94815289946709029466a56f944d138d943d24c79430ce11941dccaa93e5144793b5eba193b50087939b7f5e9348259e931ec53193101ae8930c56d092f8302c92d6874d92d55f5692c36a6a92a1fecc9260fc67923e1f8292147ca192041fe491f2907191df562391c881cf91c5637391bf634591a7cab1918c63c0918c5a799187981d916cc7d39148360e910797519107661a90fc9af190d7529090c0704c90a6ab8e907a592f9079a3d5905dee4c9026721190012c808ffa68e08fef348d8fe9a8f78fdf91ec8f9749838f91161b8f71a1938f62c14b8f5ac8118f27d6fe8f02ef6c8ee689b18ed508c08eb2455a8e6f86db8e3a26c08e3635218e33b09b
  | 7, 1, 2 => 0x9ac7ad149a98656f9a9859c99a943f569a8e19009a8799c19a8174da9a43bade9a11c9cc9a03850e99e920e5998006f39973515999669b959962264b995336ef994267be9934706d9931b1fe9928e5db99253a54990f4d3c98e3794f98c478a69878dbe4986e8f2898510c4f98405c4b9800305f97e93a5397b3295397ac0d5c979acf039796ad769794a2ef9792d9f79780b3859779113f973d7dbb973aebfb97384e4c9721cb11971a52e796f4e0c896ef31db96c41dce96acf15696a547bf968d45fc9689d95b968496669670db1996659465961a6f3395f4027a95efc2b8958b46a59541f7f9950afcf994eabe1994ca0e3394b4eb3c94b4979a948273a8
  | 7, 1, 3 => 0xa1822aefa17f4196a1748fb1a0da99e1a0c66e0da0b720b5a0a105cda098eb13a08c56eba06176dba03e7b57a03ba547a0317309a02f760da02e2f04a020378a9ffda58b9ff8343d9ff1df999ff039bf9fee95f09fbc60939f7f378b9f6d3f989f4a2acb9f1b2a1d9f097fe49f03921c9ef6661c9ef05aaf9eef4aa39eb46aa69ea5e2099e96a0299e8bc8b19e7162a59e60f8799e549f359e40bca09e4065869e0f5d589dd56d0d9dafb4e29da28d5d9d4c3d0d9d4b3b199cf7feb19ce9e3a79cbfde239cbd32db9c7b39269c186cd29c13ec2f9be7c0979bc597ee9bc0931f9bbfcae49bbfc0fe9b90cfd89b86c07e9b6f3e229b5c14ea9b1141f19afb75d1
  | 7, 1, 4 => 0xa964a127a934ca04a9263fa4a90b69fea8f4d5d3a8e4d034a8e4a6a0a8d56183a8a3455fa89f5cdda862c48ea8500690a8110047a7d633f7a7a89771a6fd25f3a6fb7775a6c745a9a691bcb5a6500a0fa6445fd6a6421094a60b210aa5e71626a5df680ba5d45b80a5c81aa7a5c75f65a589fe7fa5405515a537202ca4f0a5fca4e84de5a4c75773a4ae46dda494ba80a48c0cb2a47b7271a473e546a433c8baa43176d4a428cecaa420e67da3c2a1afa3aed91ca37f20c3a3631f52a34bf28ea3181646a2dac139a2d973a2a2d1b9d3a2d01fa8a2cd4489a2cc83aea2b783b0a28b0943a288736ea2763b37a20635c1a2025d5da1b43f61a1a3bca5a199ad4b
  | 7, 1, 5 => 0xb190a4dfb18cf6bdb15a583db158780cb14eb48bb147c105b142447bb12758b8b0e32b06b0978fe9b094a0e5b0945291b0805584b07b2df5b0195b0bafafd4d5afaf7e14af87c055af511deaaf327da3aef06f0eae792b02ae4cb3d0ae21a5f2adfd1ee7adf3fcf7add14485ad55b4eead4bd754ad437083ad3b5923ad2dbfedad06daa8acd2dda9ac9d464cac740321ac52d745ac5109ddac27da11ac20dc44ac0e1dbeabdf5d4babc1044cab93af8dab6dd701ab662c93ab65cba2ab40ee92ab0392c9aae2c829aad7e7b0aacae70baa923e5aaa6ee76daa343074aa21e858aa16707aaa066e3ea9b9ce7fa9aac1c1a98b55c8a976b005a96d79d0a9689b7c
  | 7, 1, 6 => 0xb8b26dfdb8ae9e6fb878e8aab86e02edb84c4a65b83213a8b824c4bdb821d01bb7f9c4a4b7ce9b54b7c99c1bb7c64597b7af4ab4b7ace222b76b23b0b74f340cb74c752eb7470254b734c20cb72b7312b728e152b6e24499b6a12c76b68c167bb68a26d3b67cebd0b647e64eb608648ab5d83fcdb5d63960b591f83fb5793bfcb556c2dcb5456a70b5238438b4d8b370b4d0e9e0b4b8038ab4a5f1f1b4835f10b46eb107b454fe59b4549ac6b44d909fb43492bfb407b969b3d60919b3d44d90b3c7d433b38f0202b3300583b2ecdc34b2a67dc3b29791f4b265c412b25e5f62b2500118b24fee72b24a8eb9b21d840eb20e639db1bfd837b1ae1d88b1a46349
  | 7, 1, 7 => 0xbf63c02bbf605e05bf44ba99bf4349e2bf382022bf0bbb85bf05cb60befd167dbee60c36bed7be86bed147f6bec55acabeb088aebe5d4f2abe37d219be2e4b02be011283bdf77620bdf3a368bdcb3d81bda24004bd9fb0fdbd803234bd3e5fdfbd044ad2bcee49d7bcb41943bcac3712bc90c0a4bc5b0324bc5ad31bbc5a383dbc1b5157bc0fd8a9bbd0e250bbc8136fbbbb9ca0bba622bdbb9731b2bb8c28c9bb8b47b6bb2bc4d0bb20d37bbaeba03dbad0a275ba9bc06dba67eb26ba678793ba58198eba0450a3b9ffbf23b9e5f66bb9bf5ab4b9bc92e2b9b5e2abb9847949b96838e0b963bc1eb9501ba2b942f250b940a0a2b9305d15b8d76971b8c78aca
  | 7, 1, 8 => 0xc5dd9856c5c5f159c5c250d7c56a26f2c54b0cefc528c95dc526badec4f74707c4f69bf3c4e6f17ec4db4a0dc4d95c87c4c895a0c4bd66f7c4b5d2b9c49c3c34c49af72bc499cfc1c497e4b0c456be7bc44d8592c44147aac44137cfc4325c78c40edbd4c40919c9c3ed52ebc3b27a64c3a36f81c3470184c3380f69c2c4f678c2bb39e0c2a4404fc28d123bc26778a6c2461387c1f42b18c1f052b4c1ce0c23c1c0ad08c1bf2bdbc190042ac184418ec182726ac1628508c1528514c142f441c13eb19dc11a368ec0a4c34cc075b494c045954ac01c245bc012abf0c00e2ce1bffc6bd3bffbf173bfe9d026bfdfd4f0bfbebae3bf989a83bf935932bf898ae8
  | 7, 1, 9 => 0xcd3c884dcd0e8dbfccfe0817ccf4cfffcce8599bccb26ef1ccac7c24cca61987cc8bfc62cc3eff34cc2565b4cbfd2d53cbec55efcbd53da4cbd271facbc30625cb81317ecb7de521cb43e9a1cacc77c6cabbfc2bcaac01c0caa9cfdbca9fc081ca948c7aca8818bbca7dbd21ca65dc03ca21c8a1ca003fb8c9f10d7fc9d57bcfc9d37c31c9c56731c9b8cae4c9981195c9794b1fc976bd77c9640176c922bf5bc8e643ebc8ce26adc8cd45a9c83c6390c82ae006c82971d5c80717e5c8033f81c7fdb986c7c1673ac77571d5c76c30c1c76571e1c72f5efdc6eb1b4ac6dede38c6d8171fc6c75031c68d390fc6623aa1c62f1128c612d2bbc5f6fcb5c5f2c1bd
  | 7, 1, 10 => 0xd4544e47d4190236d3f617dbd370fe11d36b5df6d366268dd3370471d330856fd322d6fed31bb684d312ba80d307bcccd2fd705dd2fb4668d2fa8aa8d2d4096fd2cf1fb4d251ec01d24c54b9d23286ecd20d9ee2d1fcebc3d1e583b1d1c1e670d19491b1d18fd8eed1484d94d120ded2d10465b8d0e09013d0df6493d0d1205dd0bc24d7d0b1959ad0b109c5d0858540d08247e8d07b1f4bd03c767dd01b4a7cd01622edd0030342cfea3e97cfdf8375cfa7a5a9cf8c37eccf8345c8cf5ddffbcf35ac28cf2c8335cf100924cf0795f3ce442b27ce1502afce141fface08b058ce04edffcdfaaa70cd8606d2cd752687cd71a101cd679d87cd4a8fdacd45d9be
  | 7, 1, 11 => 0xdcc89ae5dc9a2c69dc8b08f7dc48c872dc2bb59cdc2b0159dc22420fdc1804a3dc0d1f05dbfdce00dbeb56ffdbd5ffcbdbbd0a3fdb852709db7ecb46db65ec16db62ed1adb56fb22db41f3cbdb411130db2d04aedab8c3dadaad8f87daa6d415da61419dda500c6eda460ee5da390d57d959200cd923b2f7d9169c22d90efb48d90d7775d8feb116d8ee1682d8cac204d8678b9ad85f4186d8465bc2d840e3bad808f7e5d7e675f1d7d0fd1bd7c0dd1bd7a300b0d75b3a61d74bcf57d747d71ad7423459d7283adcd6f87d55d6ea2904d6e40d2ad6d04fd6d6c96a4dd6a466f5d698720dd5e44300d5b7f282d5b4710fd5a19962d52c8a38d486e115d461a42a
  | 7, 1, 12 => 0xe67eee19e60f910de5fd4df7e5adc7b3e59a22b6e5997ca7e5943b56e58a6d0ce50c9da9e4e9d91be4c93f64e4c22ea2e4be8a28e48a170de4552f85e3e24157e32e3e5ce2ad1936e2aa535ce2a274b8e27895b3e25929fde2115dbde210bacde1ca5fc4e1b99a2ce19813d6e18278c8e169e7efe1687241e15a4ea9e1396393e136fcb9e12ca6f4e117bdd6e1082be5e100943ae0e0ce7ae0c8841de0b18480e090eb3be07b2a37e06d2b85e0662ce5e000e70adfd1871ddfc1d156dfa66769df868fdadf82a98edf814e89def9b0dcdedfaf91decd2106deb6a8dbde8a3303ddf2b66eddb68b26dd8508a1dd663279dd6059c6dd4d5752dd47e478dd3d44e7
  | 7, 1, 13 => 0xecd123afecc4d9bdec8aef01ec66227aec631cc5ec4d63e9ec4260fbec29a3caec24a381ec183774ec124d3bebdd2ef9ebd8302bebc6d37deb98224beb955e7ceb7bd90beb43cc1feb33d401eadc2c31ead5062deab0cd2cea9bd94fea97c532ea8db5d8ea8cd3ddea84a74eea82dc14ea681c52ea53d15aea503e02ea2b9a92ea1389cfea053820e9b35c88e98606ece9713d6be96b46c0e95aa6fbe950b034e945c68fe9145362e8c5c5a0e8ab9dbae88df45fe884a584e86c1eece8685acae8244a8ae8214b0ae8091deae7ebaedde7d9adc7e7d75888e7c466cde7bba539e7b84ac7e7a4b839e75f1e46e7399420e71b18b2e71914dae6f02fade68e1704
  | 7, 1, 14 => 0xf5eb20bbf5c24c04f57f37f8f55a7045f5087817f474d66cf4350afff422fc21f41d1798f415e4d3f415021ef406f78df3ed48f2f3c81542f3b330cdf3b20571f352edaef327dbd7f321a327f31e7ac6f2fedaeff2f18c0af2f0c491f2b64da9f262ca44f2207c43f1ed3813f1b3710ff19fb472f197e0bbf1485bc0f10f3cd9f0aab1fff0a0a2a5f07e9f45f066be27f03a0d1bf024906af0093fd3eff93542efd833eeefa6a8dfef996472ef98f3b9ef7a786def5f3232ef1083d3eeda0839ee8ba7d5ee808b20ee77bbe7ee3855dfee227f6eee13f946edfe9baaeda42584ed9439e6ed8be3d2ed7a456ded720b13ed49643ded349631ed275ae7ecde9f3d
  | 7, 1, 15 => 0xfceb0b28fcd839dffc7e3331fc551edffc4f2ebafc4bfa3efc21d1c1fc0d0f85fbd94c56fbd8edfafbc5f651fb19c03efafde212faadec30fa87c339fa638275fa5faa11fa53b8d2fa48847ffa387828fa24aabcfa19e45af9d4cf87f9aed299f9ac5005f9921879f971e035f9316793f92238e4f91176c9f9039bf1f8f1ef1af8eca66df8e9a39ff8bc6264f88b7bb8f87fb814f87d843ef84f8713f84f2c4df8449003f8336910f81a05cff7ebc58ef7e665d5f7d6512af7d1410cf7a7777ff782e5baf77d4ca6f775fc65f7494b61f7435c0ef7325e1bf6f63a51f6e672acf6b19c3af69db23af69da25ff64a3032f63029adf61c2ca0f6170511f5ffda11
  | 7, 2, 0 => 0xffa90661ff9df545ff82234fff6609caff5a72a7ff34a3adff176f7dff088f35feff933afea81174fe99c0fdfe8c579bfe7ad6aafe739655fe581344fe4d5cfcfe463010fe09da09fdf4be5efd810311fd80606ffd5427d0fd53a92afd51801efd48b93efcf95f79
  | 8, 0, 0 => 0x3e52d0123b34c7713ad68a4b3a8033753a1dbef63a1c5f433861a2a437a90d6b3539e07430e71b652fe9e3ab2fe7ff5f2fb879da2ed972652daa52e22bc11f412b8dd2232b792aef2b6360842b31f6b328c67460282125ee27f900ef251ca22b24eb385a24b6d68824368a0d225215782040143d1d53af701d36919d19bc3e6419ad68c215fa176614ccf9dc14823c45131f4f8c1302228312de71c31210c29210f99b2a108ae1ac1076a8040ffbb91e0fe91b5a0fe72a990ecd9dd70cfa623d0c3fce1c0c22e64f0a9899f809b4fac5098a0cfe0985b8e705b4bb76058e5e4e0522378c04ff35c004a62e7c03f2e17703d13a060334fbc401466c23003e590a
  | 8, 0, 1 => 0x6fa993546e4c31696e15510b6c9959c36c93356b6c5dc6bd6a89ba876a69a7bb6a275dca69ad2dc16916efa46910ef7f68d7357d68666c2467e7cb0c67d7439667ce92b267225fde66d93e1265ed79a06389c2176190853d60c73bd46081e9ba60507fe96000993c5f6d245d5e68564b5b9e0b385b6ca16757c86c81573ec35256c9d87e56618b4755d528fd534d92b7534768b952b8402b5212b21b507c6eeb4df9e3134da0f7e84c8514524c7181d24bf5ebc44b29cc9b4b12b9ab4ade3d70499655e64854b7324850336847e6f646478990d04689db1445f14ddf45af2d6b451a42544460ce244422b1fc42a4748a414287dc40982e5a403663d23ead9e39
  | 8, 0, 2 => 0x958b46a59562c537953566ac94b56620944d138d9257f85191c8cfc391316dea905d7ef59037996c8f4f5a7a8f44884c8e8cb7168e3a26c08bc6319f8b82116a8b57ffe18ac8d7538a75e276899b2a8e8895799e87d6c96187ced70687cea5d7873fae7886369415859fe550848218fa84158e5682f2eadf828f70e18224362d8187f7eb811474fa80f8f01f805efbc2805317747f99684a7f132b1a7e9816487e08edba7c3096787bd60b217b45ef2c7b1bd0817a8ca7f37a76d4d479531f0478ba657e7806243d77c22f61774a58f5769098c175f051ad75c9f62975c31e547569a1257445e99a743b34d67431b338729bd432721c2af071feda0a70276af5
  | 8, 0, 3 => 0xbb8c28c9bb7012e8bb038207b9ffbf23b8ffabb4b8708326b86f5b6ab84bdbbcb831e6bdb77a592cb63b7ad9b608648ab5793bfcb5456a70b49f1bfdb469fd04b32776f0b2442040b229c4cdb1b4f7b2b090567cafab3129af327da3ae43986eae3afb86ae3275b1ad4d904ead2c6e8cad262ec8ad20b424ab6e3959ab0edae3aac752a7aa16707aa9f273f7a95635b5a8c70d27a767a614a6facad7a663da61a648f59fa62afc61a57c8260a40383ada333da41a2d1b9d3a2804ecea2697368a03f3f639ff852fe9e4ffbbf9e3fe67b9cf5cccc9b6f3e229a11c9cc9811ee4a97ed931a976cf00a975154d8964f52ea961a6f33961045e195c9e79995c3f31a
  | 8, 0, 4 => 0xe7088a33e6d380e8e66c4bf1e5b3e6b0e536c5f0e525fa75e47dbc50e434f3cde2743fade1efa266e1ad9d15e03d9934e0155a24dfae70a6de63a60edde5965dddc02084dc72db0ada0093e9d967b24dd901b7dbd8f206efd876dc57d6093950d57a10c2d4faac56d4fa9690d48a317dd46b83c8d330856fd0459b76d003ae56cf8c37eccf6e0e8dcf335269ce38b857ce24c56fce246966cdac560dcaa9cfdbca883bb0c9e26274c9bceffdc8ce26adc86e161dc6e758f9c6a97e1dc5c5f159c5ab8fdac5491818c4e4ed42c4045873c34caa51c2f5cb79c2d28e99c2453233c2037a77c012abf0bfe76089bd9fb0fdbcf7064dbc5e37aebc1b5157bbae2c84
  | 8, 0, 5 => 0xfeb87767fe8600cffd3ae12afd124cd3fbc4fbadfa44fde0f9316793f88bc9acf67be793f615c1f0f3897d71f31e7ac6f2450b53f16a559cf0aab1ffeff93542ef5a367cee77bbe7ed8f0c5cec36be60ebc6d37deb7bd90bea97c532e8bca3e2e8ab2dda
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x104418003504120010094104c0400054842090000010440000000411080009410480c84050853010000010441800324c820c000001044180035041200000c41008040025041203
  | 6, 0, 0 => 0x100404002148420c00002048804000000a103000c5310804000000610b000c932083000018022010000a048830000000e10f0000021043c000000a100000c4048804000001210b00002048804000000210b0000021043c000000610300000048400000000a1010000021043c00000c81090000a038830000181220c0000003843c000000210b00115310830000000e1000000004840400000061000000004843c000008410f
  | 6, 0, 1 => 0xe04883000000411000000a038830000010910b0000a008804000080a20100000008400000008410f0000021043c00450852010000a048804000000e1000000e0488300000100101000c4048804000000a10f00006048804000001210c00114214804000000e10900000104400000000a10b0000000842c000000e1030001521083000038122010000004840c00450412010000003840000018122010000001840c000000e10b
  | 6, 0, 2 => 0x81200804000280e2010000003843c003100220100000008400000000610f0000001842c000001210900100028804000080e20c0000002842c003100a201000d5018804000000e1010000000842c000180a20c00000028404000000610000000038430000000e1000000a038804000000210b0004110080400000021000000002843c000000e10b0000002843c00250412030000a018804000000210f000d44148300015081201
  | 6, 0, 3 => 0x28400000000610b000d501880400214842010000002840400000121030000001842400214842010000001840000000c41010011421480400314c42010000021043c000000a10100000038400000000610f0000004843c000000a10c000d410480000324c8201000c4028804000181220100002038830000000e10900000028400000000610c000c4018804003100a20100054324830002504120100006028804000000e10b
  | 6, 0, 4 => 0x4843000000121090000a038804000000a10b0000003840c000000a10b0000e048830000180a20100095310830000008510c0000002842c000080a20100000008400000000a1030000003843c000000e10b00002038804000000610b00000104400003100a20100002028804000081220c00000028400000000e10b0000004842c000008010300000038400000000e10c0000a038830000000a100000000284240045484201
  | 6, 0, 5 => 0x10094104c0400000061000000000840c000001210000002038830000000e1030009410480400000411060000002840400000061030000003843c000000a10b00000038424000000610f00114104804000000e1090000002840400028122010000a048804000000a109000c4028804000000610b00000028404000180a2010000002840c000000610100002028830000180e20100054204804000000e10000000048424000381220c
  | 6, 0, 6 => 0x41043c000000e10100000028400000000a10b0000002840c000180e20c00000314404000008411800095310830000000a10000000018400001500e20100000038400000000610b000c4048804000081220c00006038804000000610f00000104418000080620c0008521080400350412000000001842c003101220100094104804000000210b0000004843c000000e10f00002038804000000a10300000048430000008410f
  | 6, 0, 7 => 0x843000028122010000003842400000121010000003842c000000210900006028804000001210b0000a048804000000e10f00014214804000000e10f00000048424000000e10300100028804000280e20c00000028400000001210b0000e048830000508520100000038400000000210b000c4028804000000a10f0000021043c00000061000000a038830002504120100006028804000000210f0000000842c000180e201
  | 6, 0, 8 => 0x4843000000121000000003842c003540620100002018804000000210b00000008404000000610000114204830000180a20c00109420830000001210c0010942083000000021000000003843c000000610b0000020040c000000e10f0008521083000000411080000a048830000008410f0000000843c8405085301000c1300804003540620100002018804000000a1000000a048830000181220c0000003840c000548420c
  | 6, 0, 9 => 0xe048804000000610f0000021043c000001210c000c402880400000021090000003840c000000210900000048424000181220c0000a038830000000610f00000038400000001210b0000004840000000411000000021046000000061030000041043c0000041103000d4214830000180e20c0000002843c000001210f0000004840c000000e10b0000000840c004000e20100002048830000000610100000008424000000e10c
  | 6, 0, 10 => 0x210424000000e10900000320424000000a10b0000004843c000000e10b00002038804003504120000000038400000000a10300000018400000001210c0000a04883000324c820c00000028400000000e1010000003843c00350412000009410480400000c810900115310804000000a10b0000004840000000401010000003843c000281220c0000a048804003100a2010000042442c000000e1030000000840c000000610f
  | 6, 0, 11 => 0x2842c000000210f00000048424000180e2010000000843c000001210900000028404000000610900000038404000000210f00002038830000280e20100000028404000381220100100018804000004010100000028400000010910b00041100804001500e2010000002840c000000a10b000c9320830003508520c00002018830000180e20100015210824003100220100000048424004548420c0000002840c000000610f
  | 6, 0, 12 => 0x18400000001210300000008400004548420c00000008400000000610100000028400000000610f0000003840c00324c820c0000004840c000008410f0000002840c000000210b000c9320830003100220100000104400000181220100000048404000000a10c0000002843c000000a10f00000028424000081220c0000021043c00000c410100000038424000000e103000c4018804000000610c000d42148300000012100
  | 6, 0, 13 => 0x2843c00000021010000a048830000080a20100006038804000000a103000c4008804000000a10300105410830000000a1000000002842400008062010000004842c000181220c00085210804004000a2010000001840c000000e100000c5310804000280e2010000002842c000001210f000c4018804000181220c0000002842c000000a10f0000201880400000061000000004843c000000610100000018424000000a10c
  | 6, 0, 14 => 0x38400000000e1000000004842c000000210000000018404000000a1010000002843c003101220120054204c04003508520c0000010440c000080a20c00006038804000000210f0000e048804000010410f00000028424000000a109000d4104800000548420c0000002842c000000610100006028804000000e109000020188300000006103000d5018804000000e10b000c401880400324c820c00000018424000000e10f
  | 6, 0, 15 => 0x841180000002840c000180a20c00006038830000004110000002038830000000210900000048430000000610000006028804003508520c0000003842c000280e2010000a03880400050852010000001840c000008410f000d410480000000c910c0000010040400000021000000202880400000121000000003840c00324c820c000c4048804003508520c
  | 7, 0, 0 => 0x28404000000610100000214404000000e10900000028430000000a10f00000200404000001210300000320404000010510c00000304430000001210f00000028430000000a1000000003840c000000a10900000048404000000210f00006038830002148420100100038804000010810c0000003840400000021010000000840c00314c420c0000032042400000c41010000e048830000000a1030000002840c000000a100
  | 7, 0, 1 => 0x1843000001041010000a03880400000c910c00000018430000000610c00000038404000008510c0008120080400000061010000002843c0000002109000c5310830000000e10b0000032043000008062010000003843c000000a10100000028400000000e1000000000840c000000a10c00000424430000000610c00000310404000010510c00000424430000000a10b0000002840c00450412010000003843c000010c101
  | 7, 0, 2 => 0x2840400324c820c00000028400000080e20c0000000843000000061000000002840000314c420c0000003843000001041010000000840c000000e10b00000018404000000210f00000324404000000210c00002028804000000e10300000424430000000e10900000008404000000e10000000310404000001210000000038404000000a10100002028804000000210100000214430000000a1010000002843c000008510c
  | 7, 0, 3 => 0x6028804000000610100000008404000000610c00000048404000000210300014214804000000a1000000032043000000061090000021043c000008410100000018404000000210c0000004842c000010510c00000028404000000e10c00000028430000000e1000000003843000000c410100000018400000000a10f000c9320804000000a10c00000028430000000610f0000001840400000021010010d430830000000e101
  | 7, 0, 4 => 0x4840c00000121090000002842c002148420100000018404000000e1090000004843000324c820c00000008404000000a1010000002843c00000121010000001842c000000e10b0000031040400000061000000021043c00324c820c0010d430830004508120c0000001843c000008410100000028404000080e20c0000002840400314c420100000038430003508520c00000310404000000610f00109420830000000e103
  | 7, 0, 5 => 0x41043c000000a10b00000028404000000e10c00006048830000000e10c0000000843c00000121010000004843c00324c820c0000001843c000381220c0000000842c000000610300114204830000000610f00000018404000000e10c00000400404000000a10c00000038404000000a10c00006038830000000e10f00000008400004250820c00000320430000281220100000018404000000a10100054324830000000e10f
  | 7, 0, 6 => 0x48400000281220c00000038424000000210b0000021043c000001210f0000001840c000000a10300000048404000080a20100000414430000081220100105410830000180e20c0000003843c000280e20c00000028400000000610c00000048400000001210f00000038424004504120100000320430000000210f00114204830000000a1010000003840400000061010000004842c000000210b0000003842c0000006101
  | 7, 0, 7 => 0x10440000000021010000001840000000c51010000002840c000001210f0000002840c00000021000000602880400018122010008521083000000121010000001840c000280e20c0000021043c000000e1030000003843c000000210100000018400000000610300000028430000010010100000038424000000610f00000018400000000e10000006038830000001210300000008400000000210c0000021043c00324c8201
  | 7, 0, 8 => 0x843c004000620100000038424000000610100000420430000000a10300000210404000000210f0000001842c000008410f0000000842c000001210900000210430000001210f0000004843c00450852010000040043c000000210c0000a03883000000c81010000001843c000548420c0000040043c000000a10000000038430004350c20c00000028400000001210100000008400000010010100000008430000000e10c
  | 7, 0, 9 => 0x4843c000000a1010000001842c000000e10c0000001842c000000210300000028404000001210b00000028404000000e10f0000004843c000000210f00000404430000000610c0000002843c000010010100000028400000000e1030000032042400000121030000002842c000000a10f00000018430000001210100000038404000080a2010000002843c000508520100000038404000000a1030000021043c0000002101
  | 7, 0, 10 => 0x214430000010810c00000018400000000e10c0000001840400000121010000004843c000181220c00000324430000280e20c0000030040400000c810c00000028404000001210c00000400404000000e1010000602880400000c410100000038424000000610100000008404000001210c0000a048804000000e10c0000002842c00000061030000004843c00450412010000002840400000061000000e048830000001210c
  | 7, 0, 11 => 0x18400000000e1030000002842c000000210c00000028400003100a2010000001842400000061010000003842c000000a10f00000018430000000610100000100404000000a10300000008404000000610000000008430000001210300000008430000000610b0011531083000000121010000002843c000010c10c00000038430000000e10b0000e048830000000a10b00000028400000000610100000018400000010810c
  | 7, 0, 12 => 0x2842c000008010100000038430000000e10b00000008430000000a1030000001840c000000a10100000028404000000e10f0000000843c000001210b00006038830000000e10c0000004840c000004110c0000001840400000061030000003842c00000c81010000031040400304c020100000038430000000210b0000002840400000121030000602880400000c810c00000008400000281220c00000038400000000e103
  | 7, 0, 13 => 0x10d43083000204802010008521083000038122010000a038830000000a1030000020040400001041010000004843000000c410100000018404001500e20100000038430000000610f00000430404000000a10100000008400000000e10c00000304404000000e1010000001843c000000a10c0000041043c000000e10f0000003843000000121010000a038804000000a10c0000001842c000000e10b0000002843c000000a10c
  | 7, 0, 14 => 0x38404000000a10300109420830000000e10300000008400000081220c0000004843c00000c81010000003840400000121010000002843c000010010100000018404000008410100000310404000000a10c0000002842c000000a10100000018404000000e10000094104804000000e10c00000048430000000610100006028830000000a10c00000048424000000a10300000048400000000610300000100404000000e10b
  | 7, 0, 15 => 0x320430000000610c00000200404000010c1010000004843c000000a1030009410480400000c810c000c9320830000000a10c00000048430000000a100000000384040002812201000000384300000006103000c9320830000001210100000038400000008410100000320404004508120c00000104430000000610f0000004840400000021000000021043c00000c410100000038424000008110100000038430000008410f
  | 7, 1, 0 => 0x843000150c920c00000028424000000a1030000000842c000001210f00000008404000000e1090000000842c00000021010000002843000000c810c0000001843c000000e10f0000000843c000000e10c0011420483000000c410100000028400000000e10c00002048830000000e10f00002038804000010010100000038424000000a1030000003842c000001210c00000008404004250820c0000003840000000c5101
  | 7, 1, 1 => 0x38404000000a10900000028400000008510c00006038804000080620c00000018404000180e20c00000018430000000610000000324430000000a10300000018400000008410100000038400000001210b0000204883000000021000000032043000000c41010000031440400000411090000000843c000000a10000000018430000000e10f000000084000000002100000000084000000100101000000084000000084101
  | 7, 1, 2 => 0x6038830000000a10300000038400000000610f00000028404000000a10c0000002840400104402010001421480400000c41010005432483000000121030000002843000000061030000000842c000008010100000018430000000610f000003144040000002101000c531080400000061010000000843c000000610100000204430000000e10000000314404000000210b0000002842c000010110c00000028404000000e10c
  | 7, 1, 3 => 0x28430000000610100054324830000000e1010000002842c000001210c0000000843c000000a10900000048400000004010100000018430000000610100000008430000001210f00000048430000000e10000000210404000001210c00000310430000001210c0000003840400000c81010000a038830000000210b00000028430000010c10c0000002842c000000210b00000038430000000e10100000008400000000610b
  | 7, 1, 4 => 0x28430000000e10c00000100404002504120100000018400000008510c00000008400000000e10f0000002842c000280e20c0000010040400000c41010000032443000000021000000a038804000000210c00105410830000010010f00000048400000000e10c0000003840c00000061010000004840c000000e10c00000028404000000a1030000002843c000000a1010000000840c000000e1000000000842c0002812201
  | 7, 1, 5 => 0x38404000010810c0000000842c001500e20100002048804000000e1030000002843c000000a10b00000028400000000210c00000038430000000210300000018400000000e10c0000002843c000000a1010000003840000000021010000003842c000080a20100000104430000000e1000000001842c000000210c00000038404000000210f00000018400000000a10000000048430000000a10f00000048430000001210c
  | 7, 1, 6 => 0x81200804000001210c00000008404000000e100000c9320804000281220100000028404000080620c0000002843c000010510c00000038400000000e10c00000048404000000210100000018404000000610f00000018404000180a20100000028430000000a1010000002842c000080e20100000028430000000610c00000048400000004110c000c1300804000000210900105410830000000610f00000028430000000610b
  | 7, 1, 7 => 0x2843c000000a1010000004840400000021090000041043c00001041010000004840c000008410100000048400000000610000000424430000180e20100054204804000000a10c00000104430000010410100114204830000000a10f0000002843c000000a10b00000038404000001210b00000008430000000e10300006048804000000a10c00000038430004504120100000314404004150420c000004004040000012101
  | 7, 1, 8 => 0x18400000000e10000000048404000000e10000000028430000000e10000000320430000001210c00000038404001044020100000018400000000e10b0000203880400324c82010000003842c000001210300000210404000004110000000028430000000610100000048400000001210c0000003843c000080620c0000041043c000080a20c0000001842c000000610100000048404000000610c0000003840c00000c110c
  | 7, 1, 9 => 0x3842c000004110c00000038430000000a10100000028404000000a10f00002028830000000610f00000038400000080620100000314404000000a10b00000310404000001210f00000048404000181220c00000028430000008510c00000100404000008410f00000400404000000a10c000c5310804000080620c0000004842c00000021090000032443000000061030000003843c000000a10f00114104804000000e100
  | 7, 1, 10 => 0x320424000000e1010000003840000000121030000003842c000000a1030000003840c000000610f00000310404000000e10b00000048404000001210300000028404000000e10c00000104404000000e10100000008430000001210100000104400000000e10b00000200404000180e2010000004843c000000e10f00000320430000000e10900085210804000008410100000008430000000610300094104804000000610f
  | 7, 1, 11 => 0x3840c000000e10b0000000843c00000121090000004843c00000021010000000840c000000e10100002038804000000a1030000000843c000000e10300000018430000000e1010000003843c000001210c00000038430000000610c0000004843000000021090000040040400000c510100000048404000000610c0000001840c000001210b00000038424000000e10f0000002840c00000061000000003842c000080a20c
  | 7, 1, 12 => 0xd4214830000000a10c00000028430000000a10300000028424000000610c00000404430000000210c00000028404000000e10100000028400000000e10000002048830000010c10c0000002843c00000121030000003840c000080a20100000210404000000e1000000001842c000000210100000048430000000e10c0000000842400000c810100000008430000000210c00000038430000080e20100000430430000000e10c
  | 7, 1, 13 => 0x320404000010010100006028804000000210f0000002842c000000610100000320430000081220c00000038404000010110c00000048430000000610100000038430000000a1000000004840c000000610000000210404002048020100006038804000000e10100000048404000001210f00000310404000080a20c00000028430000000610b00000200404000001210c00000008404000000e1000000004840c0000006100
  | 7, 1, 14 => 0x48430000000e10b00000018400000000e10000006048830000000210b00000028404000000a10b0000000840c00250412010000001840000000061010000e048804000000a10100000400404003508520c0000000840000000c010100000038404000000e10c00000028430000001210300000048424000000a1090000002840c000000e10c00000038430000000a10f00000008404000000a1010000001843c002148420c
  | 7, 1, 15 => 0x8430000001210c00000018404000080620100054324830000010910c00000008404000000e101000000184040000002101000d4214830000000a10100000008430000001210300000314404000000e10100000048430000000e10100000410430000000610c0000004843000000061030000002840c000000a10000000008430000004010100000038404000000a1010000002843c000000210c00000048404000000210b
  | 7, 2, 0 => 0x324404000000210c0000004843000001001010000021043c000000610100085210830000001210b000c5310804000000a10300000008404000008510c00000048430000000610b00000214430000000a10f0000002842c000000610000000324430000001210100002038804000004110c00000008430000000610000006048830000281220c0000002843c000000a10100000038430000000e10000000028404000000e109
  | 7, 2, 1 => 0x2842c000008410100000414430000000a10b00000038430000000210c00000048400000000610b00014214804000001210c00015210830000180e2010000001843c000008410f0000003840c000000e10b00000008424000281220c00000008430000008110c0000021043000000061010000000840c000000a10f0000020440400001081010000000843c000181220c000000184040000006101000000484240000080101
  | 7, 2, 2 => 0x15310830000001210b00000008430000000a1010000001842c000000210900000434430000000a1000000a048830000000210100000018400000000610b00041100804000001210f0000002843c000000a1000000001843c000000610100085210830000000e1000000001840000000061000000003842400000061000000004842c00000061000000002843000000061010000001842c000000210100000310404000381220c
  | 7, 2, 3 => 0x1840c000001210c0000004843000000061010000001842c000000610900085210830000000e10f0000001843c000000e10000000100404000000a10c00000008404000000a10b00015210830000000a1000000003843c004150420c00000008424000000e10300000018400000000610c0000004843c000180a20c0000001843c000000e1010000a048804000001210900000008430000004110300000008400000000e10b
  | 7, 2, 4 => 0x3840c000000e10c0000002842c000548420c00000048400000000610f0000e048804000001210c00000008404004000a2010000002842c000000a1010000000842c000000e1030000201883000000c510100000018404000000610000000048424000000a10b0000001843c000000e1010000004842c000010410f00000048430000000a10f00000008400000001210900000038404000004110c00000324430000000a10b
  | 7, 2, 5 => 0x1840c000080620100041100804000000a1030000000840400000121000000002840c000000a10900000048430000000e1010000031443000000121010000001840400008062010000a04883000314c420c00000038404000000210300000018404000000e10c0000001843c000008410c00000018430000001210c00000018430000001210100000028430000008410100000048424000004010100000400404000000210c
  | 7, 2, 6 => 0x18400000001210b0000002843000000c410100000008404000000610f00000430404000000e10000000210404000010010100000018424000000e10f00000028404000000610100000038404000000610000002028830000000610b0000003843000000c810c00000028430000000610000000048400000000a1000000003843c000000a10c0000201883000000021010000001843000304c02010000002843c0000006100
  | 7, 2, 7 => 0x28430000000210b00000048430000000a10300000048430000004110c00000018404000010910c00000038404000000210b00000028400000381220100000018430000000a10f00000038404000180e20100000008430000000610b0000003842c000000a1090000000843c004350c20c0000004843c000000a1000000003842c000000a1010000021440400000c010100000028430000000a10b000003204300000812201
  | 7, 2, 8 => 0xe048830000181220100000048430000000610100000210404000004110000000018404000000e10f00000310404000000a10000000038404000000a1090000043040400000121000000003843c000000a10100109420830000010c10c0000002840400000021010000002842c000001210c0000000843c00000121030000003840c000000210c00000028400000000e101000000384040000006101000020288300000006101
  | 7, 2, 9 => 0x38424000001210c00000404430004508520100000038430000000610100000018404000000a10c0000002843000000411000000000842c000000610100000204404000000210300000434430000000e1010000040040400000021000000002840400000801030000002843000000c810c0000002842c000000a1010000002840c000001210c00085210804000180a20c000c9320830000000210c001094208300000006109
  | 7, 2, 10 => 0xe04880400000c010100002018804000000e10b0000001842c000000e10b00000048404000010010100006028830000010010100000048424000001210c00000028404000010910c00000018400000000610100000028424000000210f00000048400000000210c0000001843000000121030000003843c00000c810c00000018404000000610900014214804004250820c00000038404000000a10f000000484300000006101
  | 7, 2, 11 => 0x48400000010110c0000004843000104402010000002843c00000c510100000048404000000e1000000004843000000121090000602883000000021030000000842c000000210100000028424000001210c00000410404000001210f00000028404000000610c000d4214830000000210f00000314404000180e20c0000041042c000001210c00000038404000000210c0000010440400000121000000002842c000010910c
  | 7, 2, 12 => 0x48424000000a10c00000314404000000610900000104404000000210100000038400000010410100000048430000000610c00000018430000000610f0000a038830000000e1000000000843c003508520c00000028430000000e1030000001840c000000a10c00000028430000000210b0000002842c00000121090000004840000000061010000000843c00000c410100000400404000001210b0000001843c000000a103
  | 7, 2, 13 => 0x18430000000a10c0000004840000000021090000003840c000008410f000c130080400000801010000004843000001001010000003842c000000a10900000324404000000210c00000310430000000210f00000038404000001210c000d540080400008122010000001843000001001010000000840400000411000000003842c000008410100006048830000000210100000048404000000a10c00000018400000000610c
  | 7, 2, 14 => 0x18404000280e20100000028404000001210100000018404000000a10100000048430000000a10c00000310430000181220c0000003840c000000a10900000048430000000210300000028430000000a10c00000038404000010010100000018430000000610f00000038404000008410f00000018400000010d10c00000048400000000210900006028830000000a1030000021043c00000021010000001843c000000e100
  | 7, 2, 15 => 0x20040400000061010000000842c00000061010000001842c00038122010000004843c00001001010000004843000000c01010000002843c000000a10c00000434404000000e10b00000104430003100220100000028424000000210300000410404000000210c00085210804000000a1010000001843c00018122010000002840000000801010000001840400000121090000000843000250412010000a048830000010110c
  | 7, 3, 0 => 0x18430003508520c00000038400000000e10f0000004843c00000021010000000840400000121000000001843c000001210000000038430000001210000114214804000000610c0000001843000000121000000a048830000000e10b00000028404000001210b0000003840c00000021010000002843000008062010000003842c000000a10f0000004842c000000a10f00000038430000001210c00000038404000000e10f
  | 7, 3, 1 => 0x28430000001210c00000018430000000e10f0000002842c004508520100000018404000010510100000310404000000a10300000048430000000e1030000002842c000001210000085210830000000610c0000003843c000000a1030000040040400000c910c000000184000000006100000c4018804000000e10c00000008404000000a10100000018430000080e2010000001843c000548420c0011521080400000c8101
  | 7, 3, 2 => 0x400404000180e20100000320430000000e10100000008404000001210b0000001843c000000610c00000048400000000a10c0000004842c000000210c00015210830000000210f0000001840400000061010000003842c000010810100000028430000010010100000028430002048020100000008404000001210b00000400404000000a10c00000018404000000e10000000018404000000210c00000008400000000a10b
  | 7, 3, 3 => 0x4110080400000c01010000001840400008122010000001843000000021000000004842c000000610100000324430000000610b00000310404000000210f00000038404000000a10c00000028404000081220100000018404000000e10000000210424000000610300000028400000000e10100000048430000000e10100000310404000000a1000000003843c000001210c00000018404000000a10c0000004842c000001210f
  | 7, 3, 4 => 0x31040400000401010000004843c00000061090000000843c000010c10c00000008430000000e10b0000003843c00000c410100000038404000000210900000048404000000610100000028404000000a10f00000028430000000610100000324430000000e10f00000048400000000e10f0000003843c00254c420c00000300404000010410c00000028430000008410c0000003843c000008510c0000002843c000000e10c
  | 7, 3, 5 => 0x38430000000e10f00000048404000000e10f0000043040400214842010000004840c000000e10100000018400000000e10b00000048424000181220100000048404000000a10c0000001842c000281220100000100404000000a10b00000018424000000e10b00000310404000000210f0000003843c000000a10900000028430000000a1030000001843000000401010000002843c00001081010000002840c000000610c
  | 7, 3, 6 => 0x2842c000001210900000400404000000e10c0000004842c000000a1090000003843c000000e10f00000048424003510520c00000028400000010410100000100404000000a10c00114214804000001210c0000000840c000000610000000038404000000e10f00000028430000001210100000028404000000e10100000028424000080e20c0000002840400001081010000010440c000001210b0000a038804000000a101
  | 7, 3, 7 => 0x2843c00000061090000002842c000180a20c00000048430000080e20c0000003842c000000a10f00000204430000080a20100000048424000010c10100000214404000000610c00000008400000000610000000008430000000610300000310404000001210100000414430000000210f00000008400000000610000000400404000000a10c00000008404000010910c000003144040025041201000c1300804000000a100
  | 7, 3, 8 => 0x38404000180a20c000d5018804000000610b0000001843c00000c410100000028400000080e20c00000214404000080e2010009430480400000061010000003840c00000c410100000048430002048020100000018430000000a10f0000000840400008122010000003842c000000610100000310404000010810c000c130080400000021000000a038804000001210c0000000840c000000610100000028430000000e101
  | 7, 3, 9 => 0x840000324c82010000002842c000001210c00000048430000000a10c00000018404000000610f0000604880400000c410100000018430000000e10c00000320424000010810100000008404000000a10100000028404000000a1090000021043c000004010100000324404000000210300000018430000180a2010000032043000150c920c0000002843000000021030000002840c000010810100014214804000000a10f
  | 7, 3, 10 => 0x10d43083000104402010000201880400000021010000002840400314c42010000003843000450852010000002840c000000610f0000021043c000010810100000018400000001210c00115210830000000610f00000028430000000a10000000038430000000610b00000048430000001210c0000003843c000000e10c0000003840c000000e1010000001840c000000210b0000002842c00314c420c00000100404000180e201
  | 7, 3, 11 => 0x2843c00000c410100054304804000010010100000018400000000e1000000004843c004504120100000400404000010810100000048400002148420100000104430000000a10c0000003843c000000a10100000028404000000210b0000004843c000000a10c0000032040400000c91010000001843c000000610c00000008404000000a10000000310404003540620100000018404000000610c0000a0388040000002100
  | 7, 3, 12 => 0x2843000000061010000001843c000000a10c00000038404004150420c0000001842c000000e10100000008404000081220c00000028400000000610100000048424000000a10b00000048404000000a10000000028404000000a10900000048404000000610f0000002840c000010d10c0000002842c000008010100000038430000000e10100000100404000000a1030000000840c000000210000000048404000000610c
  | 7, 3, 13 => 0x18404000000a1000000e048830000001210c0000001843c000080a2010000000843c00000021090000004843c000000610f0000001843c000000210100000038400000000a10b0000000843000000c110100000424430000000e10100000028404000000210100000210404000000a10c0000000842c000000e10b00000310404000000610b0000001840400000c410100000048404000000e10f000003204300000006101
  | 7, 3, 14 => 0x184240000012101000d520080400000121010000000840c000181220100000028430000001210b00000200404000000a10b0000003840c00000061010000001843c00000c110c00000310404000001210b00002038830000000a1010000042442c000510920c0000004840c00000021030000004840c0000002101000000284000000012100000c404880400000c41010000002840c000000a10b0000001843c000001210f
  | 7, 3, 15 => 0x1843c000000e10100000048404000280e2010000002843c00000c51010000e048804000000210f0000001842400324c82010000e048830000000e1000000004843000000c110100006028804000001210100000048404000000e10f0000003840000000061030000001840c000000610f00000028404000010010f0000000842c00314c42010000001843c000000610100000028430000000a1010000001843c0000108101
  | 7, 4, 0 => 0x200404000548420c0000000840400000061010000004840400314c420100000028400000000a1000000002842400000c41010000001840c000000a100000000384300000080101000000284040000002103000c5310830000000a1090000003843000000401010000001840c000000610c00000314404000000e100000000284300000006101
  | 8, 0, 0 => 0x424430000000610100000420430000010510c0000000840400000c81010000032440400000801010000004843000000c110100000314430000010510c00000420430000000210100000404430000000a10c00000210404000008510100000018430000010510c00000310430000010410c0000001843000000c010100000204430000010410c00000310430000000a10100000430404000004010100000420404000008110c
  | 8, 0, 1 => 0x204404000008410c0000001840400000841010000041043000000c410100000214430000000a10100000410430000010010100000404430000000210100000038430000008010100000304430000000a1010000004840400000c810100000404430000000e10c00000304430000000e10100000048430000010110c00000038430000008410100000038430000008110c0000042443000000c410100000214430000000a101
  | 8, 0, 2 => 0x204404000000e10100000038404000000610100000320404000010c10c0000002840400000c810c0000002843000000c110100000210404000010c10c00000320430000010810100000104404000010d10c00000038404000008010100000400404000000610c00000314404000000e10c0000041040400000c810c0000041443000000851010000032443000000c010100000320404000000e10100000414430000001210c
  | 8, 0, 3 => 0x8430000000e10100000104430000001210100000204404000001210c0000002840400000c110100000430430000010c10100000018404000004010100000028404000000e10100000018430000001210c00000104430000010810100000310430000010010100000104404000001210c00000400404000010110c0000003843000000c510100000300404000010410100000404430000000e10c00000310404000010c10c
  | 8, 0, 4 => 0x10040400000c810c0000042443000000c01010000002840400001081010000002843000000811010000031443000000c810c0000001840400000c810c00000018404000000a10c00000008430000004110100000324404000010c10100000314430000000e10100000400404000000210c00000314404000000210100000314430000000a10c00000420430000010410100000104430000010810c0000021440400000c5101
  | 8, 0, 5 => 0x48430000010810100000434430000008010100000018404000000a1010000003843000000c91010000032040400000c110100000214430000001210c00000018404000000210100000424430000000e10c00000104404000008510c00000214404000008410100000400404000010c10c00000314404000000a10c00000424430000010410100000028404000008510c00000038404000010c10c00000314430000010c101
  | 8, 0, 6 => 0x28430000000610100000430404000004010100000210430000010810100000324404000008410100000320404000000210c00000038404000000210100000104430000000210100000210430000010510c0000021440400000c410100000104430000000a10100000048430000000610c00000048430000001210c00000430404000010410c00000100404000000e10c00000038404000008410c000001044040000002101
  | 8, 0, 7 => 0x28430000000610c00000214430000000610c00000324404000010d10c00000310404000004110c00000018404000010910c00000324430000000210100000018430000000a10c0000031043000000811010000031443000000851010000043443000000c910c00000324430000000a10c0000001843000000c510c00000008404000001210100000210430000008010100000320404000000e10c00000324430000000210c
  | 8, 0, 8 => 0x18404000000a1010000001843000000c410100000310430000010510c00000310404000001210c0000010040400000c910100000204430000000a10c00000104404000000e10c00000048404000001210c0000040040400000c010100000314404000000210100000410404000008010100000008404000000e10100000038430000000a10c00000214430000000e10c00000434430000010910c000000184040000081101
  | 8, 0, 9 => 0x43040400000c910c00000100404000000610c00000104404000010c10c00000420404000010810c0000040040400000c910c0000031440400000c410100000410404000010810c00000320430000008410c00000300404000001210100000018430000010810c0000021043000000c410c00000204404000000210100000018430000008010100000018404000008110c00000310430000000e10100000304404000008110c
  | 8, 0, 10 => 0x10410c00000304404000010410c0000030443000000c110c0000004843000000061010000030443000000841010000032440400000c01010000000840400000c110c00000410404000000a10c00000038404000008510100000048404000010d10c00000028404000000a10c00000028404000000610c00000304404000010d10c
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 13 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x1_1 roots_x1_1 7 s ws hint
  | 1 => checkCutEntry dom_x0_0 roots_x0_0 8 s ws hint
  | 2 => checkCutEntry dom_x1_0_x2_1 roots_x1_0_x2_1 5 s ws hint
  | 3 => checkCutEntry dom_x4_0 roots_x4_0 7 s ws hint
  | 4 => checkCutEntry dom_x1_0_x2_1_x5_0 roots_x1_0_x2_1_x5_0 4 s ws hint
  | 5 => checkCutEntry dom_x0_1_x1_1 roots_x0_1_x1_1 5 s ws hint
  | 6 => checkCutEntry dom_x2_1 roots_x2_1 6 s ws hint
  | 7 => checkCutEntry dom_x0_1_x1_1_x4_0 roots_x0_1_x1_1_x4_0 4 s ws hint
  | 8 => checkCutEntry dom_x2_1_x5_0 roots_x2_1_x5_0 5 s ws hint
  | 9 => checkCutEntry dom_x5_0 roots_x5_0 7 s ws hint
  | 10 => checkCutEntry dom_x1_0_x3_1_x5_0 roots_x1_0_x3_1_x5_0 4 s ws hint
  | 11 => checkCutEntry dom_x3_1 roots_x3_1 7 s ws hint
  | 12 => checkCutEntry dom_x5_1 roots_x5_1 8 s ws hint
  | 13 => checkCutEntry dom_x0_0_x2_1 roots_x0_0_x2_1 5 s ws hint
  | 14 => checkCutEntry dom_x0_0_x1_1_x4_0 roots_x0_0_x1_1_x4_0 4 s ws hint
  | 15 => checkCutEntry dom_x1_0 roots_x1_0 7 s ws hint
  | 16 => checkCutEntry dom_x0_0_x2_1_x5_0 roots_x0_0_x2_1_x5_0 4 s ws hint
  | 17 => checkCutEntry dom_x0_0_x4_1_x5_1 roots_x0_0_x4_1_x5_1 4 s ws hint
  | 18 => checkCutEntry dom_x0_1 roots_x0_1 6 s ws hint
  | 19 => checkCutEntry dom_x0_0_x4_1 roots_x0_0_x4_1 5 s ws hint
  | 20 => checkCutEntry dom_x0_1_x4_0 roots_x0_1_x4_0 5 s ws hint
  | 21 => checkCutEntry dom_x4_1 roots_x4_1 6 s ws hint
  | 22 => checkCutEntry dom_x4_1_x5_1 roots_x4_1_x5_1 5 s ws hint
  | 23 => checkCutEntry dom_x1_0_x3_1_x5_1 roots_x1_0_x3_1_x5_1 4 s ws hint
  | 24 => checkCutEntry dom_x1_0_x5_0 roots_x1_0_x5_0 5 s ws hint
  | 25 => checkCutEntry dom_x1_0_x5_1 roots_x1_0_x5_1 5 s ws hint
  | 26 => checkCutEntry dom_x3_1_x5_0 roots_x3_1_x5_0 5 s ws hint
  | 27 => checkCutEntry dom_x0_0_x4_0 roots_x0_0_x4_0 5 s ws hint
  | 28 => checkCutEntry dom_x0_0_x5_0 roots_x0_0_x5_0 5 s ws hint
  | 29 => checkCutEntry dom_x3_1_x5_1 roots_x3_1_x5_1 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_63 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x2_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x2_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_1_x1_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_1_x1_1_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x3_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x2_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x1_1_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x2_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_1_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x3_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1_x5_1 _ hc
  · contradiction
def p0Subs : List Nat := [15, 11, 0, 3, 1, 12, 6, 9, 2, 18, 8, 21, 13, 20, 14, 5, 10, 19, 4, 16, 24, 26, 22, 27, 7, 29, 17, 28, 23, 25]
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
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 12 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 64 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 64 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_64 : ∀ i, 64 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 64 64 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_128 : ∀ i, 128 ≤ i → i < 142 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 14 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 142 → Z 6 i = true := (range_split z6_0 (range_split z6_64 z6_128))
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
private theorem z7_576 : ∀ i, 576 ≤ i → i < 613 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 37 576 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 613 → Z 7 i = true := (range_split (range_split (range_split z7_0 z7_64) (range_split z7_128 (range_split z7_192 z7_256))) (range_split (range_split z7_320 z7_384) (range_split z7_448 (range_split z7_512 z7_576))))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 64 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_64 : ∀ i, 64 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 64 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_128 : ∀ i, 128 ≤ i → i < 192 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_192 : ∀ i, 192 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 192 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_256 : ∀ i, 256 ≤ i → i < 308 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 52 256 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 308 → Z 8 i = true := (range_split (range_split z8_0 z8_64) (range_split z8_128 (range_split z8_192 z8_256)))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 31 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 31 0 = true)
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

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 11]⟩], 16⟩
theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by simp [wit, PEqualNP.MetaComplexity.Monotone2]
theorem wit_size : wit.size ≤ 11 := by decide
theorem wit_eval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = ((fun x : Fin 6 → Bool => Nat.testBit (4276808928 * 2 ^ 32 + 4209696768) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))) x := by decide +kernel
theorem hT6 : ∀ r : Fin 64, goal_all.testBit r.val = ((fun x : Fin 6 → Bool => Nat.testBit (4276808928 * 2 ^ 32 + 4209696768) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))) (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808928 * 2 ^ 32 + 4209696768) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 11 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (4276808928 * 2 ^ 32 + 4209696768) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_all 11 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_41076_aux

theorem PEqualNP.Outside.L_meta_41076 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808928 * 2 ^ 32 + 4209696768) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808928 * 2 ^ 32 + 4209696768) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s hs
  have hlb : 11 ≤ s := PEqualNP.Outside.L_meta_41076_aux.lower s hs
  exact ⟨PEqualNP.Outside.L_meta_41076_aux.wit, PEqualNP.Outside.L_meta_41076_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_41076_aux.wit_size hlb, PEqualNP.Outside.L_meta_41076_aux.wit_eval⟩
