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

namespace PEqualNP.Outside.L_meta_41524_aux

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
def goal_all : Nat := 0xfeeeeee8faa8aaa8
def dom_63 : Nat := 0xffffffffffffffff
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]
def dom_x0_0_x1_1 : Nat := 0x4444444444444444
def roots_x0_0_x1_1 : List Nat := [0x4040404040404040, 0x4400440044004400, 0x4444000044440000, 0x4444444400000000]
def dom_x0_0 : Nat := 0x5555555555555555
def roots_x0_0 : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]
def dom_x0_0_x5_1 : Nat := 0x5555555500000000
def roots_x0_0_x5_1 : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]
def dom_x1_0_x4_1_x5_0 : Nat := 0x33330000
def roots_x1_0_x4_1_x5_0 : List Nat := [0x22220000, 0x30300000, 0x33000000]
def dom_x1_0_x4_1 : Nat := 0x3333000033330000
def roots_x1_0_x4_1 : List Nat := [0x2222000022220000, 0x3030000030300000, 0x3300000033000000, 0x3333000000000000]
def dom_x2_0_x3_0_x4_1 : Nat := 0xf0000000f0000
def roots_x2_0_x3_0_x4_1 : List Nat := [0xa0000000a0000, 0xc0000000c0000, 0xf000000000000]
def dom_x2_0_x4_1 : Nat := 0xf0f00000f0f0000
def roots_x2_0_x4_1 : List Nat := [0xa0a00000a0a0000, 0xc0c00000c0c0000, 0xf0000000f000000, 0xf0f000000000000]
def dom_x3_0_x4_1 : Nat := 0xff000000ff0000
def roots_x3_0_x4_1 : List Nat := [0xaa000000aa0000, 0xcc000000cc0000, 0xf0000000f00000, 0xff000000000000]
def dom_x4_1_x5_0 : Nat := 0xffff0000
def roots_x4_1_x5_0 : List Nat := [0xaaaa0000, 0xcccc0000, 0xf0f00000, 0xff000000]
def dom_x4_1 : Nat := 0xffff0000ffff0000
def roots_x4_1 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]
def dom_x2_0_x3_0 : Nat := 0xf000f000f000f
def roots_x2_0_x3_0 : List Nat := [0xa000a000a000a, 0xc000c000c000c, 0xf0000000f0000, 0xf000f00000000]
def dom_x2_0_x4_0_x5_1 : Nat := 0xf0f00000000
def roots_x2_0_x4_0_x5_1 : List Nat := [0xa0a00000000, 0xc0c00000000, 0xf0000000000]
def dom_x2_0_x4_0 : Nat := 0xf0f00000f0f
def roots_x2_0_x4_0 : List Nat := [0xa0a00000a0a, 0xc0c00000c0c, 0xf0000000f00, 0xf0f00000000]
def dom_x2_0_x3_0_x5_1 : Nat := 0xf000f00000000
def roots_x2_0_x3_0_x5_1 : List Nat := [0xa000a00000000, 0xc000c00000000, 0xf000000000000]
def dom_x2_0_x5_1 : Nat := 0xf0f0f0f00000000
def roots_x2_0_x5_1 : List Nat := [0xa0a0a0a00000000, 0xc0c0c0c00000000, 0xf000f0000000000, 0xf0f000000000000]
def dom_x2_0 : Nat := 0xf0f0f0f0f0f0f0f
def roots_x2_0 : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]
def dom_x1_0_x5_1 : Nat := 0x3333333300000000
def roots_x1_0_x5_1 : List Nat := [0x2222222200000000, 0x3030303000000000, 0x3300330000000000, 0x3333000000000000]
def dom_x3_0_x4_0_x5_1 : Nat := 0xff00000000
def roots_x3_0_x4_0_x5_1 : List Nat := [0xaa00000000, 0xcc00000000, 0xf000000000]
def dom_x3_0_x5_1 : Nat := 0xff00ff00000000
def roots_x3_0_x5_1 : List Nat := [0xaa00aa00000000, 0xcc00cc00000000, 0xf000f000000000, 0xff000000000000]
def dom_x4_0_x5_1 : Nat := 0xffff00000000
def roots_x4_0_x5_1 : List Nat := [0xaaaa00000000, 0xcccc00000000, 0xf0f000000000, 0xff0000000000]
def dom_x5_1 : Nat := 0xffffffff00000000
def roots_x5_1 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]
def dom_x3_0_x4_0 : Nat := 0xff000000ff
def roots_x3_0_x4_0 : List Nat := [0xaa000000aa, 0xcc000000cc, 0xf0000000f0, 0xff00000000]
def dom_x3_0 : Nat := 0xff00ff00ff00ff
def roots_x3_0 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]
def dom_x1_1 : Nat := 0xcccccccccccccccc
def roots_x1_1 : List Nat := [0x8888888888888888, 0xc0c0c0c0c0c0c0c0, 0xcc00cc00cc00cc00, 0xcccc0000cccc0000, 0xcccccccc00000000]
def dom_x1_0_x5_0 : Nat := 0x33333333
def roots_x1_0_x5_0 : List Nat := [0x22222222, 0x30303030, 0x33003300, 0x33330000]
def dom_x5_0 : Nat := 0xffffffff
def roots_x5_0 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
def dom_x1_0 : Nat := 0x3333333333333333
def roots_x1_0 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]
def dom_x4_0 : Nat := 0xffff0000ffff
def roots_x4_0 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

namespace S_x0_0_x1_1
def pairsG : List (Nat × Nat) := [(6, 38), (10, 42), (14, 30), (14, 46), (18, 50), (22, 30), (22, 54), (26, 30), (26, 58), (34, 38), (34, 42), (34, 50)]
def r1sG : List Nat := [6, 10, 14, 14, 18, 22, 22, 26, 26, 34, 34, 34]
def r2sG : List Nat := [38, 42, 30, 46, 50, 30, 54, 30, 58, 38, 42, 50]
def mpG : Nat := 0xfff
def pool6G : List Nat := [28682364790302, 37478122004018, 37443896483370, 24249959066142, 37443963854374]
def xsM : List Nat := roots_x0_0_x1_1.map (· &&& dom_x0_0_x1_1)
def goalM : Nat := goal_all &&& dom_x0_0_x1_1
def NN : Nat → Nat
  | 4 => 5
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xb298f9eba410c76681c26c416dba44174e36025d
  | 5, 0, 0 => 0x6dba4417
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x444444440000444400004444004400440044004404040404040404044444444400000000444400004444000044004400440044004040404040404040
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x685468c4646468844474
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
  | 0 => 0x1ff0000000000000e0f0000000000000e710000000000000f920000000000000e0000000000000001f0000000000000018e000000000000006d
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0xa4000000000000060b0000000000000a510000000000000d120000000000000f5b00000000000009f400000000000005ae00000000000002ed
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x0_0_x1_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x0_0_x1_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x0_0_x1_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x0_0_x1_1 goalM u ys) : RunD dom_x0_0_x1_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x0_0_x1_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x0_0_x1_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 3 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_x0_0_x1_1 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x0_0_x1_1 roots_x0_0_x1_1 goal_all 6 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x0_0_x1_1 goal_all := by
    have h0 : isConstB dom_x0_0_x1_1 goal_all = false := by decide +kernel
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
end S_x0_0_x1_1
theorem low_x0_0_x1_1 : Lower dom_x0_0_x1_1 roots_x0_0_x1_1 goal_all 6 := S_x0_0_x1_1.noCircuit

theorem low_x0_0 : Lower dom_x0_0 roots_x0_0 goal_all 7 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x4444444444444444, 36, 38)] (by decide +kernel) (by decide +kernel) low_x0_0_x1_1

namespace S_x0_0_x5_1
def pairsG : List (Nat × Nat) := [(34, 38), (34, 42), (34, 50), (36, 38), (40, 42), (44, 46), (44, 60), (48, 50), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [34, 34, 34, 36, 40, 44, 44, 48, 52, 52, 56, 56]
def r2sG : List Nat := [38, 42, 50, 38, 42, 46, 60, 50, 54, 60, 58, 60]
def mpG : Nat := 0xfff
def pool6G : List Nat := [48525416870442, 48525483977254, 57321375671858, 57321576999462]
def xsM : List Nat := roots_x0_0_x5_1.map (· &&& dom_x0_0_x5_1)
def goalM : Nat := goal_all &&& dom_x0_0_x5_1
def NN : Nat → Nat
  | 4 => 5
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xff97843edbbf5600d28a1c4f87c099e55202ab87
  | 5, 0, 0 => 0x87c099e5
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x5555000000000055005500000000050505050000000011111111000000005555000000000000550055000000000050505050000000004444444400000000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x4474646468c468846854
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x0_0_x5_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x0_0_x5_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x0_0_x5_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x0_0_x5_1 goalM u ys) : RunD dom_x0_0_x5_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x0_0_x5_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x0_0_x5_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 3 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_x0_0_x5_1 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x0_0_x5_1 roots_x0_0_x5_1 goal_all 6 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x0_0_x5_1 goal_all := by
    have h0 : isConstB dom_x0_0_x5_1 goal_all = false := by decide +kernel
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
end S_x0_0_x5_1
theorem low_x0_0_x5_1 : Lower dom_x0_0_x5_1 roots_x0_0_x5_1 goal_all 6 := S_x0_0_x5_1.noCircuit

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
  | 3, 0, 0 => 0xd4e87cd
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

namespace S_x2_0_x3_0_x4_1
def pairsG : List (Nat × Nat) := [(17, 19), (17, 49), (18, 19), (18, 50), (48, 49), (48, 50)]
def r1sG : List Nat := [17, 17, 18, 18, 48, 48]
def r2sG : List Nat := [19, 49, 19, 50, 49, 50]
def mpG : Nat := 0x3f
def pool6G : List Nat := [19865032339731]
def xsM : List Nat := roots_x2_0_x3_0_x4_1.map (· &&& dom_x2_0_x3_0_x4_1)
def goalM : Nat := goal_all &&& dom_x2_0_x3_0_x4_1
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xb63c8384
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xf000000000000000c0000000c0000000a0000000a0000
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x2_0_x3_0_x4_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x2_0_x3_0_x4_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x2_0_x3_0_x4_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x2_0_x3_0_x4_1 goalM u ys) : RunD dom_x2_0_x3_0_x4_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x2_0_x3_0_x4_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x2_0_x3_0_x4_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x2_0_x3_0_x4_1 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x2_0_x3_0_x4_1 roots_x2_0_x3_0_x4_1 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x2_0_x3_0_x4_1 goal_all := by
    have h0 : isConstB dom_x2_0_x3_0_x4_1 goal_all = false := by decide +kernel
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
end S_x2_0_x3_0_x4_1
theorem low_x2_0_x3_0_x4_1 : Lower dom_x2_0_x3_0_x4_1 roots_x2_0_x3_0_x4_1 goal_all 4 := S_x2_0_x3_0_x4_1.noCircuit

theorem low_x2_0_x4_1 : Lower dom_x2_0_x4_1 roots_x2_0_x4_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0000000f000000, 17, 25)] (by decide +kernel) (by decide +kernel) low_x2_0_x3_0_x4_1

theorem low_x3_0_x4_1 : Lower dom_x3_0_x4_1 roots_x3_0_x4_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0000000f00000, 17, 21)] (by decide +kernel) (by decide +kernel) low_x2_0_x3_0_x4_1

theorem low_x4_1_x5_0 : Lower dom_x4_1_x5_0 roots_x4_1_x5_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccc0000, 17, 19)] (by decide +kernel) (by decide +kernel) low_x1_0_x4_1_x5_0

namespace S_x4_1
def pairsG : List (Nat × Nat) := [(17, 19), (17, 21), (17, 25), (17, 49), (18, 19), (18, 50), (20, 21), (20, 28), (22, 23), (22, 30), (22, 54), (24, 25), (24, 28), (26, 27), (26, 30), (26, 58), (48, 49), (48, 50), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [17, 17, 17, 17, 18, 18, 20, 20, 22, 22, 22, 24, 24, 26, 26, 26, 48, 48, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [19, 21, 25, 49, 19, 50, 21, 28, 23, 30, 54, 25, 28, 27, 30, 58, 49, 50, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0xffffff
def pool6G : List Nat := [24262708304149, 24263145959699, 61646105088817, 61646539855129, 28661259573523, 57248560453909, 28660687704857, 57247991468849, 24263145952531, 28661192399897, 24263212997653]
def xsM : List Nat := roots_x4_1.map (· &&& dom_x4_1)
def goalM : Nat := goal_all &&& dom_x4_1
def NN : Nat → Nat
  | 5 => 9
  | 6 => 15
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xfe65e7c7ea211090e826c8ece2cf961e9ef51cb35c1d51b03352bcc910f15dd30b9a2b05
  | 6, 0, 0 => 0xfe65e7c7c3d716c8ac7e513a94a7b7928246581d706228e7632de5a95f03924250048be04ee90e724797940042809bd142337a1424e2df9c03bd1a95
  | 7, 0, 0 => 0x632de5a9
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xffcc0000ffcc0000fcfc0000fcfc0000ffff0000aaaa0000ffaa0000ffaa0000fafa0000fafa0000eeee0000eeee0000aaaa0000aaaa000000000000ffff000000ff000000ff00000f0f00000f0f00003333000033330000ffff000000000000ff000000ff000000f0f00000f0f00000cccc0000cccc00005555000055550000
  | 1 => 0xffff0000ff000000ffff0000f0f00000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x4188205208203a8c293214620810a4184065209253a88293a1483494ca4188055
  | 6, 0, 0 => 0x418820523c620a5a2418829620c4148188358829601062495404188295230620a59a41882960104149d40310528520dc20a5883128296810620a5804185265
  | 7, 0, 0 => 0x4188295
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
  | 0 => 0xe0ff3000000000001ce7f00000000000ff000f0000000000e0f80f00000000001c07cf000000000000e73f000000000000000f000000000000ffff00000000001f07ff0000000000e3f83f0000000000ff18cf0000000000ff00000000000000e0f80000000000001c07c0000000000000e7300000000000fffff0
  | 1 => 0xfff8000000000000ff07c0
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0xfaffb50000000000def7f30000000000ffad7f0000000000f5fbdf0000000000bd7fdf00000000006fef7f000000000025295f0000000000007bd700000000000f057b000000000063a83d0000000000b518ce0000000000ff84280000000000f0fa8400000000009c57c200000000004ae7310000000000dad6a0
  | 1 => 0xfffeac0000000000ffd7ea
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
  | 0 => checkCutEntry dom_x1_0_x4_1 roots_x1_0_x4_1 5 s ws hint
  | 1 => checkCutEntry dom_x2_0_x4_1 roots_x2_0_x4_1 5 s ws hint
  | 2 => checkCutEntry dom_x3_0_x4_1 roots_x3_0_x4_1 5 s ws hint
  | 3 => checkCutEntry dom_x4_1_x5_0 roots_x4_1_x5_0 5 s ws hint
  | 4 => checkCutEntry dom_x1_0_x4_1_x5_0 roots_x1_0_x4_1_x5_0 4 s ws hint
  | 5 => checkCutEntry dom_x2_0_x3_0_x4_1 roots_x2_0_x3_0_x4_1 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x4_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x4_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x3_0_x4_1 _ hc
  · contradiction
def p0Subs : List Nat := [0, 1, 2, 3, 4, 5]
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
private theorem z5 : ∀ i, 0 ≤ i → i < 9 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 15 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 15 0 = true)
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
def RootG (s : Nat) : Bool := scr dom_x4_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_x4_1 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x4_1 roots_x4_1 goal_all 8 := by
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
theorem low_x4_1 : Lower dom_x4_1 roots_x4_1 goal_all 8 := S_x4_1.noCircuit

theorem low_x2_0_x3_0 : Lower dom_x2_0_x3_0 roots_x2_0_x3_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0000000f0000, 33, 49)] (by decide +kernel) (by decide +kernel) low_x2_0_x3_0_x4_1

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
  | 3, 0, 0 => 0xf00cd17a
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

theorem low_x2_0_x4_0 : Lower dom_x2_0_x4_0 roots_x2_0_x4_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f00000000, 10, 42)] (by decide +kernel) (by decide +kernel) low_x2_0_x4_0_x5_1

namespace S_x2_0_x3_0_x5_1
def pairsG : List (Nat × Nat) := [(33, 35), (33, 49), (34, 35), (34, 50), (48, 49), (48, 50)]
def r1sG : List Nat := [33, 33, 34, 34, 48, 48]
def r2sG : List Nat := [35, 49, 35, 50, 49, 50]
def mpG : Nat := 0x3f
def pool6G : List Nat := [37525937860899]
def xsM : List Nat := roots_x2_0_x3_0_x5_1.map (· &&& dom_x2_0_x3_0_x5_1)
def goalM : Nat := goal_all &&& dom_x2_0_x3_0_x5_1
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xf4dbc64d
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xf000000000000000c000c00000000000a000a00000000
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x2_0_x3_0_x5_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x2_0_x3_0_x5_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x2_0_x3_0_x5_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x2_0_x3_0_x5_1 goalM u ys) : RunD dom_x2_0_x3_0_x5_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x2_0_x3_0_x5_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x2_0_x3_0_x5_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x2_0_x3_0_x5_1 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x2_0_x3_0_x5_1 roots_x2_0_x3_0_x5_1 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x2_0_x3_0_x5_1 goal_all := by
    have h0 : isConstB dom_x2_0_x3_0_x5_1 goal_all = false := by decide +kernel
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
end S_x2_0_x3_0_x5_1
theorem low_x2_0_x3_0_x5_1 : Lower dom_x2_0_x3_0_x5_1 roots_x2_0_x3_0_x5_1 goal_all 4 := S_x2_0_x3_0_x5_1.noCircuit

theorem low_x2_0_x5_1 : Lower dom_x2_0_x5_1 roots_x2_0_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f0000000000, 33, 41)] (by decide +kernel) (by decide +kernel) low_x2_0_x3_0_x5_1

namespace S_x2_0
def pairsG : List (Nat × Nat) := [(1, 3), (1, 9), (2, 3), (8, 9), (10, 11), (10, 42), (17, 19), (17, 25), (17, 49), (18, 19), (18, 50), (24, 25), (26, 27), (26, 58), (33, 35), (33, 41), (33, 49), (34, 35), (34, 42), (34, 50), (40, 41), (40, 42), (48, 49), (48, 50), (56, 57), (56, 58)]
def r1sG : List Nat := [1, 1, 2, 8, 10, 10, 17, 17, 17, 18, 18, 24, 26, 26, 33, 33, 33, 34, 34, 34, 40, 40, 48, 48, 56, 56]
def r2sG : List Nat := [3, 9, 3, 9, 11, 42, 19, 25, 49, 19, 50, 25, 27, 58, 35, 41, 49, 35, 42, 50, 41, 42, 49, 50, 57, 58]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [28661259045123, 37526072078595, 37495352920362, 28660889944841, 61646104560433]
def xsM : List Nat := roots_x2_0.map (· &&& dom_x2_0)
def goalM : Nat := goal_all &&& dom_x2_0
def NN : Nat → Nat
  | 5 => 2
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x861e300b441a1221
  | 6, 0, 0 => 0x1bba847f
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xa0a0a0a0a0a0a0a03030303030303030f0f0f0f000000000f0f00000f0f00000f000f000f000f000c0c0c0c0c0c0c0c0505050505050505
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x235aac6885
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
  | 0 => 0x1c1c30000000003f1c9cb0000000003ffc0000000000003c03fc0000000000330383800000000000e36340000000003fe3e3c
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x153dbdf000000000151898a0000000003ffe5200000000003c93fc0000000000334b8ba0000000002ae76750000000002ac2420
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
  | 0 => checkCutEntry dom_x2_0_x3_0 roots_x2_0_x3_0 5 s ws hint
  | 1 => checkCutEntry dom_x2_0_x4_0 roots_x2_0_x4_0 5 s ws hint
  | 2 => checkCutEntry dom_x2_0_x5_1 roots_x2_0_x5_1 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x2_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x3_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x5_1 _ hc
  · contradiction
def p0Subs : List Nat := [0, 1, 2]
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
  | 4, 0, 0 => 0xcba65d238e1981d253d9707a4a55c3be49ebd58e
  | 5, 0, 0 => 0xcba65d23
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x3333000000000033003300000000030303030000000011111111000000003333000000000000330033000000000030303030000000002222222200000000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x6884646468c468544474
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
  | 3, 0, 0 => 0x9de85d1
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
    [(0xf000f000000000, 33, 37)] (by decide +kernel) (by decide +kernel) low_x2_0_x3_0_x5_1

theorem low_x4_0_x5_1 : Lower dom_x4_0_x5_1 roots_x4_0_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f000000000, 33, 37)] (by decide +kernel) (by decide +kernel) low_x2_0_x4_0_x5_1

namespace S_x5_1
def pairsG : List (Nat × Nat) := [(33, 35), (33, 37), (33, 41), (33, 49), (34, 35), (34, 38), (34, 42), (34, 50), (36, 37), (36, 38), (40, 41), (40, 42), (44, 45), (44, 46), (44, 60), (48, 49), (48, 50), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [33, 33, 33, 33, 34, 34, 34, 34, 36, 36, 40, 40, 44, 44, 44, 48, 48, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [35, 37, 41, 49, 35, 38, 42, 50, 37, 38, 41, 42, 45, 46, 60, 49, 50, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x7fffff
def pool6G : List Nat := [57321190400818, 57317282031909, 48525416867370, 37525869962531, 61715127215409, 48520818729769, 57364140075324, 57321576999462, 48525096854314, 61719422182962, 48520818467621, 48521121899817, 61796545799484, 61762186585404, 37526071552291, 57364156392252, 57364139549500, 57317080704305, 48521189009701, 48525483977254, 57321375671858, 57364156916540, 57364140073788, 61762202641212, 61762185798460]
def xsM : List Nat := roots_x5_1.map (· &&& dom_x5_1)
def goalM : Nat := goal_all &&& dom_x5_1
def NN : Nat → Nat
  | 5 => 40
  | 6 => 120
  | 7 => 22
  | 8 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xfa70de97e1a0c381dbd08516d387ae8ed2af586ccaaa9cc6c12e9be4bc1d45aab4d854ccb3a13c0dad7b6eaca93982a6a74d2771a557238c9d0110119977c73e994c9fbe93498003932d159d931421e480098c2578702cbf7614384175c4d8d97241e58468c950ba674f75225c32c3ce5553501154500559482f1c6047f9be41458b423a3934fb2228e22d42272781e11dd5247f1bdb5cce184e2f610efe49cb
  | 6, 0, 0 => 0x80db32257f5598407bfdbdb877cd965874eb9e7373eb373e73b42cef734cb2486b0151c266f74eae66f66b306526741f614f62fc60670bb5602f0c905d6d03e25b75988b588e766b55c109b04d91a9594cb90be74b10cb4048d7a1af47a343a546d1247345aa22d743f7378c432086574062528b3f7bdb9c3ed13e643e6571533bf7557b38de808636e36bba35b989b333e26fb830ccfd722db4287d2a44b6ae2836818e2662579422083a53217144781f921e771dee6f961d643c5c1735f52117243b15153ae05514e360f414164a8d12c024d312202cdf110d8300108a7607102518130decb8e10b0596c10adf3bc50a0e6b1008e426f9047929e9042e5a89
  | 6, 0, 1 => 0xfeaf4fa9fca8d26dfc2a3caefa1a63fbf847dd94f6cef830f46177f9f0fee0eeeef00bf2ee8fbd7ae659900ee299c4dae02b48d3dfd23ee1dceb1cc1d871d896d728c01fd6edd6b0d50e977fd4e75974d3d501bbd29b63a0cc1b917ecbffe9fbca151442c705c93cc672b7f2c40e0021c29c3869c2747e1dc10af011c0d591f2bfc4d822b83f160eb645f151b3afbafeb210ced3ab7183aea845b151a78f2494a3fad4b5a0db6d53a00355929f9f91659e00a53a953fe26a9510e5309481be69946931359448852093f20552906626068f119b2f8e3ae9fa8d3d6f7383eed29a
  | 7, 0, 0 => 0xe1712b0cdfd23ee1ce9cdd61c1b37560bcd30b3dbbfc5a0896ca434792e7e42d7a72457a778b235a6d3d4baa669ff0945b75988b52df1ca74fc9aa614cb0d56c44f7652f3fe19ced38a0abd32f21c5020decb8e1019671c9
  | 8, 0, 0 => 0x7a72457a
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xeeeeeeee00000000ffffff0000000000ff00000000000000fffff0f000000000f0f0000000000000fff0fff000000000f000f00000000000cccccccc000000000000ffff00000000f0f0f0f00000000000ff00ff00000000ffff000000000000ff00ff0000000000555555550000000033333333000000000f0f0f0f00000000
  | 1 => 0xfefefefe000000001111111100000000fffffff000000000ffcccccc00000000ffaaaaaa00000000fcfccccc00000000fafaaaaa00000000fcccfccc00000000faaafaaa00000000aaaaaaaa00000000ffffcccc00000000ffffaaaa00000000ffccffcc00000000ffaaffaa00000000fcfcfcfc00000000fafafafa00000000
  | 2 => 0x333300000000ffffffcc000000000033003300000000fffffcfc00000000fffcfffc0000000003030303000000000000555500000000ffffffaa000000000055005500000000fffffafa00000000fffafffa000000000505050500000000ffffeeee00000000ffeeffee00000000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x3182047500429721653032cf21667440d0216600c0cb20257440d1216600c0da216538d18f21661036863d6600e34620250042982165006202147500c0d9216510a24f216600358100751036063d66004289202574448621660040c2040500c0cb58157550c62166008580147500e34658150065811475004202005500418204551035c63c8600428958157540c6216601550318f500e6c621651036463c86
  | 5, 0, 1 => 0x458100550044d218f511c0c63d660040d140f57444c6216600e7062165003202007511b0c63c86
  | 6, 0, 0 => 0x54428318859c05440c62026015503188598c1120c6216700318f2161d8028318858760000c62021d40103408580610a0c63c859c0103448580600428318809801037c6216600448318f218010340658163840c63c859c03840c620260040c621695803940c6216602c103188598011b0c621660040c6216a18010318808763040c63c859c01230c621660140c62161d800040c8580500448321601803040c620260040c621689803140c6216650428318859c01290c62166
  | 6, 0, 1 => 0x40d718859808440c6216601510318f59800d018858760044c321601800d118858760040c6216ad80004216005500429218859801036462166000106581154010344620263840d018859c0103606216600e112188598e10344621670000c62161d4048318858760040c658101807440c6216600e54318859801200c621660040c6581158054318858760044c621615840c624f21670040cd196058010318b581600c543188598010318920260040d018f21809040c62166
  | 6, 0, 2 => 0xe1131885980103196047600470318859809840c6216601410321601804c3188587600038d1885940006216147500c10319605801063c8585601410319605801130c62026000106202154010a0d021660040d118f598010a0d121660040c62167980103188080600010a248594c1130c6216700c10621615840cd18f21670001035810140504188585610318b3c859c03040d021660040c620215803040d121660040cd188098010318b20260040c62169d801036862166
  | 6, 0, 3 => 0x44831960580113486216600440621615805440c8580600444621615801130c63d660040c62560580a840c621660000c85801d4010345021660040cf216018000319604750001032020140004188585500448621615803840c8580601410318f218010a0c658160003032c8594010a4c6216600010318205401031885ad600e10319605805441885856
  | 7, 0, 0 => 0x1130c62166004188585510318858061031885856103346216610318b2166103406216610344621660040c621651120c6216610318921665440c62166003188587510318f216610a0c621660040c620253840c6216610318858763040c621665040c621660040c858050040c65815
  | 8, 0, 0 => 0x40c62165
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 40
  | 6 => 46
  | 7 => 40
  | 8 => 34
  | _ => 0
def stateM : Nat → Nat
  | 5 => 0xffffffffff
  | 6 => 0x3fffffffffff
  | 7 => 0xffffffffff
  | 8 => 0x3ffffffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0xff00000000007ffc00000000000070000000000000007ff30000000000000e000000000000007e7f00000000000000700000000000000000f00000000000007fff00000000000e730000000000000f83ff00000000007f80000000000000707c0000000000007ffff000000000007fff0f0000000000718cff
  | 1 => 0xe73ff00000000007fff0000000000007fff0000000000007000f0000000000070000f00000000000e00f000000000000e000f00000000000070f0000000000000700f000000000000000f00000000007f80f000000000007f800f0000000000707cf00000000000707c0f00000000000e73f000000000000e730f
  | 2 => 0x7f0f00000000007ffcf000000000000f830f00000000007ff3f000000000007e7ff00000000000718c0f0000000000007ff000000000007ffc0f00000000000f83f000000000007ff30f00000000007e7f0f0000000000718cf000000000007f80ff0000000000707cff
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x37bfff00000000007ffccc000000000078400000000000007ff3aa00000000004e400000000000007e7f6600000000004870000000000000252af10000000000003f7700000000004e732200000000000783bb00000000007fc0880000000000787c4400000000006d6ae000000000005ad50e0000000000318cdd
  | 1 => 0x7fffff000000000048400000000000007fffee00000000007d6af100000000007ad51f00000000006f6af100000000005ed51f00000000006d7af100000000005af51f000000000012951f00000000007feaf900000000007fd59f00000000007d7ef500000000007afd5f00000000006f7bf300000000005ef73f
  | 2 => 0x150600000000007ffefd000000000002810a00000000007ffbfb00000000007f7ff7000000000010840c0000000000002a6000000000007ffddf00000000000502a000000000007ff7bf00000000007eff7f00000000002108c000000000007fffff00000000007fffff
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 46 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 46 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 46 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 46 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 46 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x3f) :: stateWiresD n (ids >>> 6)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x3f) :: stateWiresS n (ids >>> 6)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 8 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 5 => 39
  | 6 => 42
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xfed14f59f44c9fa2e299c4dae02b48d3dfd23ee1d9420580d2a68bdbc8726d50c090a064b210ced3a6c3bff89510e5307f26650e7a74a90378a945f87307c0ba6e93468e6bafe5e466f66b3066b179a26465049f5b75988b5ab3420852651e3e4f9c5bd24f88c51e4ccf13a6460ed72640c401ff3f8522662db4287d244aa43e1d065548194996980decb8e101ffe574019671c900c873f000c105db
  | 6, 0, 0 => 0xfad285b7e7b8db90e5be38d9e276aae3d6f975bad5bed513c1cbcee4bc0e692cba4b0dfcb2877f28a6313810a5a8cee3a2ebedad9d3070139835592f96e40bc493b154e48df3ef2c8d7a20148835f569846d05287eb55cf57bdfae516a1adf2f6953e05a5e1a048d5b9c9b595a1b7b69581fef394fa79069435149513ff1406a314770702a057539218d16691eab60c211d6c66a109124e30f54ae8e099748d6043addcb00105ed2
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x38404000000e10100000028404000000610100000018400000000a10100000038400000000a10100000018404000000210100000008400000000a1000000000840400000021010000003840400000061010000001840400000c910500000038400000000a10100000008404000000210000000008400000000e10100000028404000000e101000000184000000006101000000184000000002101000000284000000006100
  | 5, 0, 1 => 0xa10000000038404000000e10000000018404000000a10100000038400000000a100
  | 6, 0, 0 => 0x8404000000e10000000008404000000e10100000018400000000210000000028404000000a10000000038400000000610100000028404000000210000000008404000000a10000000038400000000e10100000028400000000a10100000018400000000610100000008404000000610000000028404000000a10000000028404000000e10100000028400000000610100000038404000000e10000000008404000000e101
  | 6, 0, 1 => 0x8400000000610100000038400000000a10100000008400000000e101000000184040000006100000000184000000006101
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 7 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x1_0_x5_1 roots_x1_0_x5_1 6 s ws hint
  | 1 => checkCutEntry dom_x0_0_x5_1 roots_x0_0_x5_1 6 s ws hint
  | 2 => checkCutEntry dom_x2_0_x3_0_x5_1 roots_x2_0_x3_0_x5_1 4 s ws hint
  | 3 => checkCutEntry dom_x2_0_x4_0_x5_1 roots_x2_0_x4_0_x5_1 4 s ws hint
  | 4 => checkCutEntry dom_x3_0_x4_0_x5_1 roots_x3_0_x4_0_x5_1 4 s ws hint
  | 5 => checkCutEntry dom_x2_0_x5_1 roots_x2_0_x5_1 5 s ws hint
  | 6 => checkCutEntry dom_x3_0_x5_1 roots_x3_0_x5_1 5 s ws hint
  | 7 => checkCutEntry dom_x4_0_x5_1 roots_x4_0_x5_1 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x5_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x3_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x4_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x4_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_0_x5_1 _ hc
  · contradiction
def p0Subs : List Nat := [1, 0, 5, 6, 7, 2, 3, 4]
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
private theorem z5 : ∀ i, 0 ≤ i → i < 40 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 40 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 64 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 64 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_64 : ∀ i, 64 ≤ i → i < 120 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 56 64 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 120 → Z 6 i = true := (range_split z6_0 z6_64)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 22 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 22 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 8) : ∀ i < NN s, Z s i = true := by
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
def RootG (s : Nat) : Bool := scr dom_x5_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD dom_x5_1 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x5_1 roots_x5_1 goal_all 9 := by
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
theorem low_x5_1 : Lower dom_x5_1 roots_x5_1 goal_all 9 := S_x5_1.noCircuit

theorem low_x3_0_x4_0 : Lower dom_x3_0_x4_0 roots_x3_0_x4_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff00000000, 6, 38)] (by decide +kernel) (by decide +kernel) low_x3_0_x4_0_x5_1

namespace S_x3_0
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (2, 3), (4, 5), (6, 7), (6, 38), (17, 19), (17, 21), (17, 49), (18, 19), (18, 50), (20, 21), (22, 23), (22, 54), (33, 35), (33, 37), (33, 49), (34, 35), (34, 38), (34, 50), (36, 37), (36, 38), (48, 49), (48, 50), (52, 53), (52, 54)]
def r1sG : List Nat := [1, 1, 2, 4, 6, 6, 17, 17, 17, 18, 18, 20, 22, 22, 33, 33, 33, 34, 34, 34, 36, 36, 48, 48, 52, 52]
def r2sG : List Nat := [3, 5, 3, 5, 7, 38, 19, 21, 49, 19, 50, 21, 23, 54, 35, 37, 49, 35, 38, 50, 37, 38, 49, 50, 53, 54]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [24263145161987, 37526004969731, 37478173050150, 24262843171589, 57247990678321]
def xsM : List Nat := roots_x3_0.map (· &&& dom_x3_0)
def goalM : Nat := goal_all &&& dom_x3_0
def NN : Nat → Nat
  | 5 => 2
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xf783194cf5469f52
  | 6, 0, 0 => 0x689b949e
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xaa00aa00aa00aa003300330033003300ff00ff0000000000ff000000ff000000f000f000f000f000cc00cc00cc00cc0055005500550055
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x23442c6b55
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
  | 0 => 0x1c1c30000000003f1c9cb0000000003ffc0000000000003c03fc0000000000330383800000000000e36340000000003fe3e3c
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x153dbdf000000000151898a0000000003ffe5200000000003c93fc0000000000334b8ba0000000002ae76750000000002ac2420
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
  | 0 => checkCutEntry dom_x2_0_x3_0 roots_x2_0_x3_0 5 s ws hint
  | 1 => checkCutEntry dom_x3_0_x4_0 roots_x3_0_x4_0 5 s ws hint
  | 2 => checkCutEntry dom_x3_0_x5_1 roots_x3_0_x5_1 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x3_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x3_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x5_1 _ hc
  · contradiction
def p0Subs : List Nat := [0, 1, 2]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x3_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq, Bool.or_eq_true] at h; rcases h with h1 | h0
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2
  · obtain ⟨k, _, hk⟩ := List.any_eq_true.1 h0; exact checkCutByIdx_sound hk
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x3_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x3_0 goalM u ys) : RunD dom_x3_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x3_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x3_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_x3_0 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x3_0 roots_x3_0 goal_all 7 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x3_0 goal_all := by
    have h0 : isConstB dom_x3_0 goal_all = false := by decide +kernel
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
end S_x3_0
theorem low_x3_0 : Lower dom_x3_0 roots_x3_0 goal_all 7 := S_x3_0.noCircuit

theorem low_x1_1 : Lower dom_x1_1 roots_x1_1 goal_all 7 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x8888888888888888, 2, 3)] (by decide +kernel) (by decide +kernel) low_x0_0_x1_1

theorem low_x1_0_x5_0 : Lower dom_x1_0_x5_0 roots_x1_0_x5_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x33330000, 12, 28)] (by decide +kernel) (by decide +kernel) low_x1_0_x4_1_x5_0

theorem low_x5_0 : Lower dom_x5_0 roots_x5_0 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccccccc, 1, 3)] (by decide +kernel) (by decide +kernel) low_x1_0_x5_0

theorem low_x1_0 : Lower dom_x1_0 roots_x1_0 goal_all 7 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3333333300000000, 17, 49)] (by decide +kernel) (by decide +kernel) low_x1_0_x5_1

theorem low_x4_0 : Lower dom_x4_0 roots_x4_0 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f00000f0f0, 1, 5)] (by decide +kernel) (by decide +kernel) low_x2_0_x4_0

namespace S_63
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (2, 3), (4, 5), (6, 7), (6, 38), (8, 9), (10, 11), (10, 42), (12, 13), (12, 28), (14, 15), (14, 30), (14, 46), (17, 19), (17, 21), (17, 25), (17, 49), (18, 19), (18, 50), (20, 21), (20, 28), (22, 23), (22, 30), (22, 54), (24, 25), (24, 28), (26, 27), (26, 30), (26, 58), (33, 35), (33, 37), (33, 41), (33, 49), (34, 35), (34, 38), (34, 42), (34, 50), (36, 37), (36, 38), (40, 41), (40, 42), (44, 45), (44, 46), (44, 60), (48, 49), (48, 50), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 1, 2, 4, 6, 6, 8, 10, 10, 12, 12, 14, 14, 14, 17, 17, 17, 17, 18, 18, 20, 20, 22, 22, 22, 24, 24, 26, 26, 26, 33, 33, 33, 33, 34, 34, 34, 34, 36, 36, 40, 40, 44, 44, 44, 48, 48, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [3, 5, 9, 3, 5, 7, 38, 9, 11, 42, 13, 28, 15, 30, 46, 19, 21, 25, 49, 19, 50, 21, 28, 23, 30, 54, 25, 28, 27, 30, 58, 35, 37, 41, 49, 35, 38, 42, 50, 37, 38, 41, 42, 45, 46, 60, 49, 50, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x3fffffffffffff
def pool6G : List Nat := [57269382349606, 36357135539249, 24262708300037, 36344753947907, 37443813312810, 61715125110065, 18752198149385, 48525094486822, 37443813311782, 24249959066140, 57247856460593, 36344586437385, 28648005576220, 18752400130821, 37457284695299, 37478122003506, 57286828033308, 57317078598961, 28661259045123, 18752384075036]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_all &&& dom_63
def NN : Nat → Nat
  | 5 => 6
  | 6 => 52
  | 7 => 337
  | 8 => 189
  | 9 => 25
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xaf4f9a20902ced2a6fc6afd166725c8e40717a6a25d39d38
  | 6, 0, 0 => 0xfeb5e66dfe3a4b55f75d7d64ed49ea9de2589710e13403a5de9f565dde630c01de3999fbdd07edd9d63cbe1ad24bf9ddd1f077c4cd5bf546caa554dbc7490879c2fa1e23c2da67e1c24abd26bf98ed8cbecda52bbeb16106b86229dda4990acfa371fd719c15311c926c70f273e04a0972ae9de76fdd7acc6e25393665fa4e0c6535b5c9640409a757f16d3457a33a8f5627736d535450394e3743df4ddf67e54cb90f734cadbbc345dbb12e426f786831bbe12a304f14c8302691492e9c4ee7196a04a016968f590ce4df9502e68e19
  | 7, 0, 0 => 0x31ebb49331c7e23a30e9e20b30da702d30a189c8309636182f14154d2e6269bb2e3def2d2e3bf71a2db3dda72da64bb72c9265d02a9092672a70be412a1620a729091e6027f5a9a9278270f426c143782621c4c425d01169244e3f202256010320ea3d851fda0bbc1f43fb591e3b52531c62eaa01b62ace41974862718fa379218b72fcd184ae75918164b9d17f1a2311778fdec164ffdd314d76ef613ab6cc312a4430011b9feb711a07b4e114eed13113f7b35105120260db856600da59a5d0c73ee3b0b25a16c09aab2f0083d0d090818ba1d05a2377804e091b5047395a204715e4903ce6946031d2a34030a3cae02a810d4029cbd2401a68be601818ed0
  | 7, 0, 1 => 0x638f9daa635eceb8610e58cd607327d45fbb6eb25f9291ab5f4644f85f3ec1a35d4be1eb5d4a14835d34488c5cbf6e775c51b4bd5b3ec2c559b3be7a59628b8358fd7076587b153956eac42f56db525156b94ef1568d87445466cd9854634bdf545c29f851f8cbd351ed837351d3a487517e7bcb50d7d76250c865844f7036e84ef312784da7207d4b6d3cb64ad565b248dd246448a613ca485a77c0463b029f4617ab04460fba1b45a948c64544dd7d4331be4c429326fd401b2a2c3f6ab8653f02434f3d5dec943cc0ab5f3c921f153c50dff73b258eff3a3a9d4539c7968b3808a26337ace5cf37a71558378f8dfc3713f2e43650d29935c6e7983279aee0
  | 7, 0, 2 => 0x8e03a2108caf50f58bd6d9bb8bb213078b8f1d578a335bae885cfdb787b0e5e28710eb6e870f3af1834af6a78056eaa18000a0997faf35d37f76a1447f636da77eb558bd7e2c51dd7da344417d4b68477d3809da7ce6d6e37c250fd57c19bc257bf9cb407b98cb277aaa70187aa023a9799bd48379781f2b795080da794eb3727938e77b77899cbf76d3e98a76b48ade764a2c0275fb7dd37419638c73adf45e71834b80716e1eda70dbd44d70a3347070474b396f656c4a6f39e1a76f339b6f6f26f11f6dfd6ac26ba2f5686a731c0b6a1cc4e16a0d41a0680a4cb5679193786775f6766721459a6663ef9e65aaaf13652076d564cc77b263d7296f63b2af77
  | 7, 0, 3 => 0xc6ab04afc6909219c6296abbc5f2c1bdc2d3e0f6c23b1996c134a243c1129ee3bfd17d54bf382022bf10d6aebd83e085bbc874d2bb21b576b9ec36acb988964bb6284596b4c5a9cdb3e034f9b3367456b2f3d0cab24fee72b210f6c5b0b73cb2adf47384ad479a41ad3b5923ab3182cea9c40857a8e4d034a7a46f4aa6fee0c5a6aa2fe9a60182bda57edef1a4d1b1bfa420e67da3ab594da3a0059da2e7b907a199ad4ba17f4196a177a9eba0a105cda020378a9ff1df999f4f95969f097fe49e0f5d589d3243619ce904e69cddb1369cd2fed29cbd32db9bce10d39ac7ad14993ca8c99794a2ef96ef31db95664e6e94ca0e33918943fa915c8ed69107661a
  | 7, 0, 4 => 0xf2f0c491f2b64da9f262ca44f1d8d8c1f1b6bd88ee9eae52ee1d6168ed7d5dd3ecd08490ec91594aec8e34b6eb9f992aea503e02ea02da06e9bcbd99e9720ccae86cbf5ae7ce2a3fe7a4b839e6f2dcb7e67e5fc7e67cba08e6730c17e64260c6e3f541b8e3e24157e3a9d0cce2bbe8e5e2b09535e210bacde19494d1e122979ae1082be5e0227f12dfb2ced7df98cd72dedfaf91dd2f1882db56fb22d9e07a80d8c1fd0ad83809a3d7a24347d6c71384d69534b5d68d98cdd6706e01d5fc455ad53b3e9fd31b58b1d263d936d1eae36ad0ba710eceec12e2cca61987cba637d4cb81317ecb7fc115cb746d65ca21c8a1c9f91273c9981195c80717e5c720e726
  | 7, 0, 5 => 0xfead9bdffe99c0fdfcc7f5a8fc551edffbfd277efb515f21f87fb814f85cf202f7ebc58ef78b0895f759030cf6b508dbf5a6fe98f4ecf506f4c69bf9f3691f48f303d164
  | 8, 0, 0 => 0x558dc526534768b9521132084fa88ab34f1467044eaffbbb4db2c4844c8514524bceeb024786ad6e4691fdef45bbfe354291e30441f7b9eb4169bf9e414287dc3d4b05d83d2456c23a8033753a13af9c3909cf6037a90d6b3773b4b430ed8f322db95d5e2da043882d2eb55a2bc11f4127c8f26426f708f725de5cbc25ce08de259c2a0f2577635b22224e0b20792b7d1f1c08551e6988d21e0aaeb41bc4f8f81b0b998c1a394cee19bc3e641928bdfb192433571710b89b15ea602915df0c791315d12e0f518ce40edffeb60e4baff30e17cc080ddeb3e00c634b1b0acf6a2c097ffda4088d6a600663a259063313e6056845bc03f2e17702e72a530156e3cc
  | 8, 0, 1 => 0xab65cba2ab04cb89aa45b81faa16707aaa0c240ba8bab3d4a3631f52a34cc39aa18e9a8ba0ffc12da0da99e1a0857125a03f3f639ed16cac9ea5e209968d45fc961a6f339541f7f99516af7594ceb0f293ea65129257f851907a592f8eb2455a8d431c738cb614e58c64e1ee88ce8be587ccba078680c80c858b90348564e97e84db144384158e5683c82a5a81a2729c805317747bd60b217b1bd0817ad93d1878a4ffe5785d381d759a52ee7528ba1e7355347a71feda0a708c63d86ff132df6e4c31696d4247ad6cc9ecf66916efa468b16336687b7b81667ff34665bcd2fb64eeec54629bcaf26055e26d6046708f5dce6a1d5da661335982210955b6d0b0
  | 8, 0, 2 => 0xfe581344fcfb68defc4e8f9bfa387828f9316793f90411f7f6170511f5087817f327dbd7f0a0a2a5f08636f0f07e9f45ec3fd3faeb7bd90bead5062dea8db5d8e6c9718ee5f62735e2a274b8e03d9934e00052f3dd0b2dded93008b9d8293d25d616304bd4eadf53d38ce6dfd330856fd251ec01d1723623d01622edcf8c37eccf5ddffbcf0795f3ceb62b2dce520fbcce38b857ce04edffcc53ac0bcc3eff34ca9fc081c6dd499fc4360e95c2c829e6c018fa19bc1b5157baaf8dd9b99f5c10b711420fb67cebd0b6283af4b517843bb2d48d37b265c412b2442040b1db9bf1b0154e27af6ca0fbac52d745ac5109ddac3b3de6
  | 9, 0, 0 => 0xff82234ffe739655fa0bc0e3e5943b56df814e89dbbd0a3fd2cf1fb4c5866f95bf935932bbd0e250b4d0e9e0b3818eb8a8110047a494ba809ff8643a9db831cb981d63988541295f7cc052b875fdfe51553a09402f07484d2293dc3909b68333029c85d1
  | 10, 0, 0 => 0xeeff5994
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xfff0fff0fff0fff0f000f000f000f000aaaaaaaaaaaaaaaa3333333333333333f0f0f0f0f0f0f0f0aa55aa55aa55aa550f0f0f0f0f0f0f0fff00ff00ff00ff000000ffff0000ffffa5a5a5a5a5a5a5a500ff00ff00ff00ffffffffff00000000ffff0000ffff0000f00ff00ff00ff00fcccccccccccccccc5555555555555555
  | 1 => 0xff88ff88ff88ff880077007700770077f8f8f8f8f8f8f8f8fff8fff8fff8fff8f800f800f800f800070707070707070700cc00cc00cc00cc0c0c0c0c0c0c0c0cffee0000ff000000fefe0000f0f00000eeeeeeee0000000011111111ffffffffeeeeeeeeeeeeeeee8888888888888888faaafaaafaaafaaa000f000f000f000f
  | 2 => 0xf5f5f0f0f5f5f0f05500550055005500f5f0f5f0f5f0f5f05050505050505050ff50ff50ff50ff500555055505550555fafaaaaafafaaaaaffaaffaaffaaffaaaa00aa00aa00aa000055005500550055ffaaaaaaffaaaaaafafafafafafafafaa0a0a0a0a0a0a0a00505050505050505f888f888f888f888f080f080f080f080
  | 3 => 0xfff0ff00fff0ff00fff00000fff0000055505550555055500f0f00000f0f00000f000f000f000f00cccc0000cccc0000ffccff00ffccff00fcfcf0f0fcfcf0f0cc00cc00cc00cc00fcf0fcf0fcf0fcf0c0c0c0c0c0c0c0c0ffc0ffc0ffc0ffc0ff000000ff000000f0f00000f0f000005555000055550000ff55ff00ff55ff00
  | 4 => 0xfefafefafefafefa8888ffff8888ffffff888888ff888888f8f88888f8f88888ff880000ff880000f8f80000f8f8000000ee00ee00ee00ee0e0e0e0e0e0e0e0effeeffeeff00ff00fefefefef0f0f0f0ffaa0000ffaa0000fafa0000fafa0000fffafffafffafffafff0f0f0fff0f0f000ff000000ff000000f000f000f000f0
  | 5 => 0xf0f5f0f5f0f5f0f5fffaffaafffaffaaf0a0f0a0f0a0f0a00f0a0f0a0f0a0f0affeeffaaffeeffaaffeaffeaffeaffeaa0a0ffffa0a0ffffffa0ffa0ffa0ffa0005f005f005f005fececececececececfffafafafffafafa00fa00fa00fa00fa0005000500050005ff05ff05ff05ff05fa00fa00fa00fa00fefefafafefefafa
  | 6 => 0xeeaaeeaaeeaaeeaa11551155115511550f0c0f0c0f0c0f0cffccffccffccffcceaeaeaeaeaeaeaea151515151515151500fc00fc00fc00fcfcfcfcfcfcfcfcfcaaaa0000aaaa0000ffaaff00ffaaff00fffafff0fffafff0fafaf0f0fafaf0f0aa00ffffaa00fffffaf0faf0faf0faf0050f050f050f050feecceecceecceecc
  | 7 => 0xaafaaafaaafaaafaf0fcf0fcf0fcf0fcaaeeaaeeaaeeaaeef0faf0faf0faf0fa0505555505055555fffaaaaafffaaaaafffcfffcfffcfffc00aa00aa00aa00aaafaaafaaafaaafaaff0cff0cff0cff0caeaeaeaeaeaeaeae0a0a0a0a0a0a0a0aff0aff0aff0aff0afffcfff0fffcfff0eeeeaaaaeeeeaaaa1111555511115555
  | 8 => 0xffcc0000ffcc0000fcfc0000fcfc0000cc88cc88cc88cc88c8c8c8c8c8c8c8c8eeee0000eeee00000055555500555555
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x403020d0c504080106075040302010050403010a095040b010a07504030106055
  | 6, 0, 0 => 0x40302010d5040f0e0100076040b01272607604031c0e010d60403280b010a60408012322076040311010d10604031312090560315010d090560004030b010a504030f110d0c6041f010d0907604030f0e13126030f0e15010d60403010d1a0560408000c090760403010d091e60308010d14096040f11010d076040b131205076041d010d050760b15010d0507604030f21010d604030e0d0c106040301232205617080b15010d6040b010d1e07604030f110100604031c1b010d604030f2829016040d0c090507604030e0100106
  | 6, 0, 1 => 0x4030f2524016040f0e0d0c0760308150d091860403000c0905604031c20010d604030b010a26604030f0e000c6040301270926604081312090760815010d09076030b150d0519604030f010d2a6040308010622604010009050760403082401066040b000c05076030b010d1405608160b15010d60408010d1a0760004030801065
  | 7, 0, 0 => 0x4034308010d09704030f08240d0c70403640b010d0570403080b010d6970403080b0e000c700040b0d0c0507604037e0b010d05704030f0e010d007040343080b0d0c70403081d1b010d7040368010d090570403080b01002670403240b01000570403010d120905700040f0e010d07600040308131209600030815010d0960403080b010d2a7040328080d0c097040b010d05780770403080b010d4870403082d0b0100704036c010d0905704030871010d09704030f2832010d704030f080b131270403083624010d7040325080b0100704030f081d010d7030f080b15010d704030f0e010d12700046c0b370d076
  | 7, 0, 1 => 0x40308290b0d0c70403080b321312704080b010d2607704240b010d050770403081d32010d703080b3215010d704030f08010d22704080b01002e0770403010d0905787040308010d096d704030801770d0970004030f0e0d0c604031f330b010d70004030b010d5760004032401230560004580b010d0760403081d4a010d704030f08320d0c70004036c370d09604030f0801002c704080b01000907704031f0b0e010d70403083301000970403010d000905704030b32010005700040368350d05604080b6f010d077040308330b000c70004010d09050760403280b01272670403080b010041704037308010d097
  | 7, 0, 2 => 0x4030f3324010d704030f0e010d0c70004080b600d07604037c0b010d05704030b6b010d05704032508010d0970403420824010d704030b013a0005704030b017f0d0570403080b000c09704036608010d0970403086f010d09704031c080b010d7040325080b0d0c704030b010d055470004030b560d05604037a080b010d704080b01000507704030f285d010d704030824010d1070004030d0c0905604031d0b010d0570403080b010d6e70403280b010005704033e080b0d0c704030b0100310570403080b010d6d704032508240b01704080b0e0d0c077040b010d0c050770403010d097405704030f0b0d0c057
  | 7, 0, 3 => 0x4031f0b20010d70403080100090570004080b000c07604030b320d0c05704030b017d0d0570004030b010d1e6040813010d0907704030b01002c0570403080b000c057040f080b010007704033f080b010070003080b010d1460403010d0c090570403080b01003c704030f280b0100704280b010d050770403080b0d0c41704030b130d05197040308010d09267040324010d090570403010d09180570403080b010d70704031f0b010d09704030801002e09704080b013500077040339080b010070004030e010d1060403080100093c704030b0100054070403080b0d0c2670403240b0d0c05704032808290b017
  | 7, 0, 4 => 0x4033f280b010d704030b010005267040365080b010d7040355080b010d70403085f0b010d704031f0b010d1e704030b71010d0570308460b15010d70403083824010d700040308600d0960403080b010d8070004080b010d5960403430f0e010d700041f0b010d076046c08010d0907704035e080b010d704030f0829010d7040339280b010d704031f0b010d05704030f2451010d704031c081d010d704035a080b010d7040308360b0100704030b010d22057040308110b0100700040801000907604032b080b0100704080b0d0c0907700040308010d616040343510b010d7040308330d0c097040330080b01007
  | 7, 0, 5 => 0x4030f24010d0570408010d00090770403013a0d090570403380b010d05704030f1f0b010d700040868350d0760403430b010d05704034d080b010d70408110b010d07700040308000c09604030f08010009704030b01000519704080b01370007704030b010005417040372080b010d7040328010d09057040308210b010d704030b010d056970004030f11010d60004030b131205604030f080b000c704080b0d0c050770004031d010d05600030b15010d056040868010d090770408240b01000770408010d12090770004280b0127076040308130d091870403080b010d4970403280b0d0c057040f280b010d077
  | 7, 0, 6 => 0x4080d0c0907604030801370009704081d0b010d077040308330b131270428080b0100077040308331d010d70308330b15010d70403080d0c090570403082401000970403080b01001070403080100091870004032801270960408010d0974077040b010d051907704030f28010d0970403080b01003d70403080b0e131270347080b15010d70403081d0e010d703080b0e15010d7040f080b0d0c07704033f080b0d0c7040345080b010070403080b0d0c3c704030f280b0d0c704033908010d097040334080b010070004031f010d0960004082401230760004080b010d6360403080d0c093c704030b0d0c05407
  | 7, 0, 7 => 0x408010d0c0907704030b010d052670403080b010d1e70403010d090519704030f080d0c097040308010d095c7040824010d090770408010d09180770403084f0b010d704030b0d0c05417040308440b010070403280b010d10704030b0100090570408240b0d0c07704030801750d09704031f0b32010d7040343085d010d7040308500b010d704030f330b0100704080b6b010d077040334280b010d70403080b010022704031f4b0b010d70403080b010d1a70403080100093b7040342080b0100704037608010d0970403080b32000c70004080b560d0760403080100092270403290b010d057040308110b0d0c7
  | 7, 0, 8 => 0x403080b0d0c107040352080b010d704030b010d0549704030f0864010d7046c0b010d05077040343280b01277040345080b0d0c70403080b010d54704030f08240100704030f250b010d70403081d010d1a700040b010005076040308013a00097040308240123227040308380b01007041f080b010d07704030f660b010d7040343080b010070403084c0b010d704080b010d220770004080b010d4e6040b13010d050770403080b13120970403080b010d5c70004030801232260403081d010d09703080b15010d097040328080100097040328010d093b704080b01002c0770403080100310970403080b010d7b7
  | 7, 0, 9 => 0x4030f0b01000570443080b010d077040308290b010070403080b0d0c22700040308010d1a600040862010d0760004030f0e010060403080d0c093b7040342080b0d0c7040324010d0540704035b080b010d704680b010d05077040b010d120507704030b013500057042808010d090770403080b010d53704030f0832010070004030b01272660004080b13120760403790f0e010d70004081d010d07604030f0b010d26700080b15010d07604030f0e13010d704030f0b01002e70403080b13120570428080b0d0c0770403081d010d05703080b15010d0570403010d67090570403082f0b01007040308240d0c097
  | 7, 0, 10 => 0x40308010d09487040308440b0d0c7000403010009056040b010d000507704031f08010d09704030b0d0c0905704033e080b01007040f0824010d077040308010d0922704080b0e01000770403430824012370004030b000c0560403080b010d6a7040313010d0905704030f2824010d704030f330b0d0c704031c1f0b010d7
  | 8, 0, 0 => 0x40308013a0d09700040308380b010d700040343080b010d7000403080b010d3170403080b0e13010d804032845080b010d8000004030862010d604030f080b013a0d8000403680b010d0570403080b32010d0c80004030b010d120570004032808010d09704030824440b010d800000403080b1312600000403081d010d6000003080b15010d600040328080b0d0c704030f28080b010d80403430f080b010d80004036c0b010d05700040308440b010d7000403080b71010d7040308240b010d2280004030b010d09057040308240b01370d8040308240b01820d8040328080b01350d8000004030b01000560004031f080b010d70004030b010d230570004030f330b010d7000403080b010d227
  | 8, 0, 1 => 0x403080b0100097040308330b010d00800040325080b010d700040385080b010d700040366080b010d7000403080b6f010d70403080b13010d0980403080b0e010d00800000403010d090560004033e080b010d70004080b0e010d077000004030b0d0c05604030833680b010d80004030f0b010d05700040308290b010d7040308330b010d128040328080b32010d8000004030f0e010d60403080b0e010d128040308240b013a0d80004030b01350d0570004030b010d057870004030f0832010d7000004036c0b370d600040308330b0100704032808240b010d804034308240b010d80004030b010d000570004030f0824010d7000403080b0e01007040308330b13010d80000040b010d05076
  | 8, 0, 2 => 0x4030f080b13010d80004080b010d12077000403080b0135007040308680b010d0580403080b010d1205800040308010d670970403080b010d0009800000403080b600d600046c080b010d077040328080b01830d8040328080b5d010d80004080b010d090770004030833010d09704030f080b010d678000004080b01000760004030b32010d0570004080b010d2307700040308330b0d0c7000403080b01000570403080b010d120980004080b13010d077000403080b010d417000403080b0e0d0c70004030b010d0c0570403080b13010d058040328080b013a0d8000403080b010d267000403240b010d057000403080b01002e704036c080b010d09800000403580b010d604034328080b010d8
  | 8, 0, 3 => 0x4030868010d09700040308240b01007000403080b010d3c700040308010d1209700000403280b012760004030f280b010d70004080b01350d07704030824510b010d804030f08680b010d800040339080b010d700040308010d093c70004030b010d0540704030f080b010d128000004031f0b010d60004036c08010d097000004030801000960004080b010d000770004030b013a0d057000403080b0d0c09704030f6c080b010d8040328080b010d2680403080b010d0005800000403080b000c60004030813010d097040308330b010d0c80004030f080b010070004080b010d05077000403280b010d05704030833240b010d80403080b0e010d0c80403790f080b010d8000408680b010d077
  | 8, 0, 4 => 0x403080b01003170004080b010d0c07700040308010d097470004030b010d051970004080b01370d0770004030b010d0541700040308840b010d70403080b32010d128000403080b81010d70403080b010d0c0580004030f080b0d0c7000408240b010d077040308240b010d0580000040308240123604036c080b32010d800040358080b010d700040308010d00097000403080b3201007000004030868350d600040308360b010d700040308110b010d700000408010d090760403080b010d0c0980403080b3213010d800040308010d0905704030f080b010d00800040308640b010d7000004080b0d0c076000403080b0137007000403080b0d0c05700040f080b010d0770004033f080b010d7
  | 8, 0, 5 => 0x4030b13010d05700040308010d093b700040342080b010d7000403080b320d0c700040308010d27097000403080b01002c700040308010d0c0970004030801370d097000428080b010d0770004030824010d097000403080b010d10700040308010d0918704030f080b010d0c80004030b010d6705700040345080b010d700040308240b0d0c704030f08240b010d800040334080b010d7000403080b6b010d70403080b32010d008000403080b013a00700040308620b010d700000403080b560d6040328080b010d09800000403080d0c096000403081d0b010d700040328080b010070004080b010d270770004030f08010d097
  | 9, 0, 0 => 0x403080b010d0c70403080b01370d7040308240b010d700040308010d096000403080b0d0c604030f080b010d70403080b01350d70403080b010d0070004080b010d0760403080b010d057040308680b010d70403080b010d12704036c080b010d70403080b010d097000403080b010060403080b010d2370403080b13010d70403080b010d677040308330b010d70403080b0e010d70004030b010d0560403080b013a0d7040328080b010d70403080b32010d70403080b010d277
  | 10, 0, 0 => 0x403080b010d6
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 44
  | 6 => 52
  | 7 => 60
  | 8 => 68
  | 9 => 60
  | 10 => 52
  | _ => 0
def stateM : Nat → Nat
  | 5 => 0xfffffffffff
  | 6 => 0xfffffffffffff
  | 7 => 0xfffffffffffffff
  | 8 => 0xfffffffffffffffff
  | 9 => 0xfffffffffffffff
  | 10 => 0xfffffffffffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x3f3f807fe07ff00000380000007c000000000780078007003fff878c678c970007398003e07c700007c1f803f800780038c67ffc1f838f00383e007c007f8000003fff80007fff0038c6787c1803880007c1ff83ff807f003fffff80000000003fc0007fff80000000f87f801ffc0f0000007873987368003ffff87ff87ff8
  | 1 => 0x383e007c007f800007c1ff83ff807f0007398003e07c70003f3f807fe07ff00000380000007c000038c67ffc1f838f00000078039800680000007870180308003800007c0000000007000003e000000000007f80000000003fff807fffffff0000007ff39ff36f0000000000000000000038078007fc070000c07f801f800f
  | 2 => 0x3ff9807ff87c7000383e007c007f80003f3f807fe07ff00007398003e07c70003f3f807fe07ff0003fc7f87ff803f80007000783e7800700383e07fc07ff8700000000000000000007c1f803f8007800380007fc0780070007398783e7fc7700000000000000000038c6787c1803880000380000007c000000380000007c00
  | 3 => 0x3f3e007fe07f80003f00007fe00000003f3f807fe07ff00038c0007c1f8000003806007c000380000000007398000000383e007f987f800007398073f87c7000000000700073000007398073e07f70000000000380706000383e007f807fe0003800007c0000000007000003e00000003fc0007ff80000003ffe007ff87f80
  | 4 => 0x73987f3e7ff7700003fff80007fff003800007c0000000007000003e00000003800007c0000000007000003e000000000007f839f806f0000007ff01f830f00383e7ffc007f80000739ff83e07c70003800007c0780000007000003e78000003f3f87ffe7fff7003f39807fe07c700007c00003ff80000007018003e00070
  | 5 => 0x7f9f803f87c78003f3e07ffe7ff870000380000007c0000380607fc07838700383e07ff9fff8700383e07ff87ffe700003fff80007fff00383e007c007f800007c1ff83ff807f0000007873987368003f3987ffe7fc770007018783e780770000c078001800080038fe787c187f880000380000007c0000073987f3fffc77
  | 6 => 0x7f007f307003ffff80ff80cf8003806787c18038800383e787f987fe8000000078387f067003ffff87c780f98000701f803f80078000739f873f87f78000000000007800000383e007c07ff80003f3f807fe7fff00007398003e7fc7000003fff80007fff0007398003e07c700038c67ffc1f838f0000007873987368
  | 7 => 0x7018783e78077000739f803f87c780000007f839f806f0007398783e7fc770038fff87c187ff8003f0007ffe78007003f3ff87ff87ff8000000078007800700380607fc07838700383e787c187f880000007ff01f830f000000078007800700383e07fc07ff87003f3f807ff87ff000000007f39f8007003ffff80c607ff8
  | 8 => 0x3800007f9800000007000073f800000000000070007300000000000380706000000000739f80000007fff803f87ff8
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x3f3fb37fe37ff60024380029407c0000094a8f94af95bf002d6a870c670c96002739912be17c72000a8b52161215c40018c66ed41e838d003c3e227d427f8400001fbb800057ff00118ce140b116320003c1dd82bd807b003fffffc2144240003fe0447fffa8000024f84ca95cfc0900129578f398f3690036b5706b506a40
  | 1 => 0x3c3e2afdcaffad0003c1d50235005200273999bbe9fd7b003f3fbbffebffff0024380039407d000018c66644160284000281588298806900108468d0188309003fe0447f562800003fe0446bf52800001bdfffc2144240002420003debbdbf001bdffff7bff7ff0000000890889129002d7a8fbdeffdbf0000c04c801c8009
  | 2 => 0x37b9d16bf17c720034342069406a0000373db16be17e72002631102b406840003e3f327f427fc40012857042100240002f6a8fbfefbdbf003d7eaffdefffbf00080a02140215840002815002100040003d6a8ffdefbdbf002f7b9fbfeffdff0001088100a11432001084604010020000243808b9c8fd290024380029c07c20
  | 3 => 0x3f3e227fe37f84003f20007fe32800003635306b406a400018c044541e80000018062254020384001280407398a000003ebe627fdaff840037b9d17bf9fc72001014207100730000373db17be17f720002111023807060003e3f327fc27fe4003c20007d422800002720002be128000036a0406b502800003ebe627f527f84
  | 4 => 0x3f7fbfffefffff00001fbb9088d7ff003c2008fdcab92900272008bbe9b929003c20007dcaa800002720003be9a8000003c1dd82bd807b0018c66ed41e838d003fffffff567fc4003fffffebf57e72003d60047defa800002f60043fefa800003f7fbfffefffff003f39917fe37c720003c04402bd80000003019102a10072
  | 5 => 0x27b9d12bf17c72003f7eafffefffbf0025388129e17c320018462ed40e838d003ffeefffffffbf003f7fbfffefffff00011fbb80a157ff003d3ea37de37fb60002c15c821c804900139df9f3b9f77b003f7b9fffeffdff0003419d82ad807b0000804000100000003cbe627d527f84002c3a023d427d84003ffbdffffffdff
  | 6 => 0x195eaff5aff7bf0026a1500a5008400018866ad41a838d003ebf7affdaffed000b5b9fb7aff5ff0034a46048500a00000381d982b9807b0037bdf9fbf9ff7b0009400414af8000003d7e267defff84003f7fb77feffff6002f79953feffc7200081fbb940257ff002f3b933fe37df60010c46cc01c8209001a9f7af79af7ed
  | 7 => 0xb4b9f96af95ff0027b9d9abf9fc7b000bcbdf96bf95ff0027799dabedfc7b0010957040104240003f6a8fffefbdbf003fbffbfffbffff0001408d80ad803b00194eafd4af97bf003cbe6afd5aff8d0019ceefd4bf97bf0008420e940e818d003c7e2efd4eff8d003fbff37ffbfff6001bcacff7bfb5bf0024353008404a40
  | 8 => 0x3ea0407fdaa8000037a0407bf9a80000101428f188f32900021118b388f169001bc04477bfa0000002957002104240
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 134 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem wd_0 : ∀ i, 0 ≤ i → i < 128 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem wd_128 : ∀ i, 128 ≤ i → i < 134 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 6 128 = true)
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 134 → wireDOK i = true := (range_split wd_0 wd_128)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 134 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 134 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 10 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 5 => 5
  | 6 => 349
  | 7 => 1688
  | 8 => 501
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xe88a39deb01ae2819f043cc098cec71e605f6fc1
  | 6, 0, 0 => 0x25ce08de25b941fa258143782267298021ea77ab219c3f162140a5ac2125742920ab026920a7cca8209b1c83205e76f020151c661fa6552d1f3345181e8383ac1e6d8f8d1e0aaeb41df5556b1c69ac4f1b12875c1af2b3361aa809da1a98159c198bce2d186ae64b183fdeb91822ff14178ffaa41710b89b170eadba16d97f5f166c2b1c1619817b15ea602915df0c79152a8e1214a16d661273a18d121267d611747d8c10bf76911096048b108b9c51105fbf620f6fac190e8fbece0e8ca3a90e846b1e0db8791d0bde67650a7b2baf096421e1067a072d063313e60542451303ba0d1a035fc48c0358500b02a0c6ee029029fd017ff6500140ced500c89ba2
  | 6, 0, 1 => 0x5381deb953620a9353076cf951e628db51bdf43650fd67db50b8131350a2cbfe5073bd46501bb186501702cb501486a04fe8a9b14f3ec98c4eb4f9e14e7868144d41636c4c960e714bceeb024a0415fe48cb580e47e91717465f591445d9e97145cc49e845bbfe35455436f243fe21e2438aedff42824ea042474c0041abf9e64181a0b04108e09f3f414a253e6bc86f3d2456c23cd4c1e73b2c665439c163c839afdadd387483b136a9a2b23696e6af3603f8f335ff9a2734854d42321e206a30ed8f323019bbdf2ffab45a2fad60c02f71836f2f6504052f4cd5152e8b19db2d1e1a7b2d12c6cb2c7ae9512ab692012a72db222a1620a729150737273ff6f2
  | 6, 0, 2 => 0x856c1d2c854c032884455e60837aa709820b38ef81b835c081b37bb481acc49e81082fa27fd1d1f57f83de047efabd587da344417adecfc57ad93d187ad3f2c6794a4e1777bed65a76caa53c769c7a8c762208cc753fabb0749160a2745e8908742fe16d73a80dc3736a224472ecc08a72d9e3f172319973708c63d870020e6e6f9b95056f70ecb46ea2ef386e51c5c36e135d0c6cb496226ca704ca6c9bb11a6b22189e69ff0406685c04b7673816326714a00d65422c49650a2dc762c3cd906261eed96192216e6125296560ee00b45fe7613f5f6817dd5e41bf6b5e366bbb5c8e08c95abd12fd5982210956979809561a9e0355f5156b55a26bca54d95dfe
  | 6, 0, 3 => 0xb66a2cacb6283af4b5b1e0a3b46fbcaeb324a800b27a9976b275aad9b262ce40b244a9c1b1a7ec62b12c2878b0f54e99b086ec07b0154e27b0008743afff32aaabdaf0a2aa0c240ba9ab78c9a7666e52a6949093a63cb499a58e092ea584c028a5165c27a4366edca42b1b2ca3916ffba2afc82ea058ea199fc5351c9f97b8f89f1751599ef2a2ff9ed16cac9d47c2759a5f6b2c9a06b0b2999480c29856b89c97776a6d9776cb51976c16bd968d45fc94c4f2cb936e57299287b58291cc8e6b916f132a9122fac2907a592f901291ec8e6b33ca8e11c3278d7aa69e8c43c79d8b76a08a8af46c7589ffa51f89fe5086898c950a8883ddfd86eee2d885e84363
  | 6, 0, 4 => 0xea8481a1ea2b21e7e8afc6e9e7dbb335e6ef58a1e564bf4ce48e7a1be45ba9efe304cca1e238b27de123f52ee075e39cdf20a347dee4a53edc773af4dc2d6e24db899d0ddb0f2b4dd9c02858d93008b9d8d1b871d8c2e7b9d87b7b9ad8501f34d7dde44fd7a8ce86d70054bcd6f5010cd6bce295d616304bd2b554a9d16defffd0d31662cfa6bb51cf9b7c3bcf568aebcf03b95acc76fd85cc557d16cc432444cbc7053ecb5b2681c992521fc8d9e910c5c61740c518337dc4360e95c1dad111c13c6603bf318047be815263be579ac0bdbb5a85bd77ad75bd6cf8e1bc032673bb9c57e7bb116305ba7a904cba750178ba253360b99f5c10b7cd708fb66d9f3d
  | 6, 0, 5 => 0xffb85fd6ff4cd5a8fcf5e330fc66475cfb3fc388f9ae1daff9abbd60f988a4baf8cbd015f8c483bcf882a188f7d3f690f7c3f3a6f76ed223f7429485f694b0c2f60f4435f5d04064f5cff07cf5a79d75f4727dd0f471cd17f3f8a6fdf1c88650f0adfd8cf063c30bef94b0a8ee9eae52eb085849
  | 7, 0, 0 => 0x9747a0f09639c48095848980943669209191f43090c697f0909f17008f19f4508d77fe808cb083e08c6500e083af9400827f4ee0807b452080465a607c7a31e07af3f5d07a58cff0737dedd0737146906e57ca506d48918067c0c5b066c22b50666871c06562966062fa745061c4c960616a90305fc7a3005f0e61d05e991b905df2e7505c2b37a053d862904afa52d047b15320478c9a70451f4ec0438b537035bb98b030aa55f02dcfe7302c66aa2029c85d10276b316023bda8f0221550b0206ca5101ec392301e76e9e01c2352301a9edce0156e3cc014e30ba0124f21000fc27a000f72f1500c21a28009ebe4c004c797800379789003360cb0025e5ef
  | 7, 0, 1 => 0x13bdf119138cc5f6138330ff137f022a1299cfe7127bbba911fdbf3c11f7a2ff1183ead311498a8f1139848a1127f8d91112e089110892ad10ee029d10d68feb10c19598107595fd106aa8190ff627ad0fba49230f780a210f54aff70f3a80ac0f1cde3d0ee773870eddf50b0ec5633b0e821ebc0e4a3f3c0e17cc080e1752730dfbeab70dfa6d1f0ddeb3e00dddced70dda8feb0dc548f10dbab7c40da3dff10d9246660d79d9290d5c359a0d32c3940cd585dc0c7f0f820c65ac0d0c587f990c02455b0b93c10a0b8d8e810b6bffcc0b3053740b03f0440adec1170acf6a2c0a89f4ba0a7d15dd0a64e1b90a52d2db0a3e335909c68f8a09b683330995e4c9
  | 7, 0, 2 => 0x200b758d1fa866a21f6828c51f5c0ca71f453c0f1f1020151f0851631ef133f11e8de2b11e0aaeb41dfbc0ce1df9c4691dde02fb1db939a71db5c7de1d8beab91d7905bf1d0a570d1ce944151cde0b751c912b121c4314361c1cf8501c1928291bca887a1bb3eba81bb335281b801a1c1b7d86141b65b7561b5c72701a3245891a1c3af519d0402319aa6ddc1991eef719778342196feb97192439d7189f06ef188a748a187b2f6d187af5e4181aad0c1808ead417f74fc517a2c75c1798c2df171ddab2170efe2f16b5dda1161e1f0415f6d6c415a750a7156d2d4f155cb5161559939415203c11150731c414fdf20f1470e2d8146d255d142db03813c6527f
  | 7, 0, 3 => 0x2843639b28371d17282b026028235c4427f5011927d8adcb27ccd79227cbd9f127c31747279d34b427495f962723c39926c27e6f269a15b026923ec42661d634264d5b9c264929b325ecb53025d05fa7257a111a2577635b2553493a253fdbed2537c629249a5ad224690a8924556093243d46db242588f223cd5642236da21d23619af9235fb8f5235262422329c47a2309b3c522fc30e222d2e89b22a531a62293dc392292aa1e228f581522818eb822272f442222b3e522224e0b220503cd21f55e4921e2144c21d410a221c6d87521905b2421826396211aa262210b63172100d6d220792b7d20549af6204966a3203c8a51203a6ecf2037d379202a21a8
  | 7, 0, 4 => 0x31a7daf1317fcb2531662a1e313c88583131359830e47f8730cf69a7303aef642fef5cf22fc771ae2f9eb1222f7a0e7c2f755c332f450b362f3377952f2f932e2f2460382f08d6592f07484d2ee917cc2ec732322e6b28b42e59920e2deb9a982dbd9e352db021812da6e06d2da66f232d9337d72d4b74a62d0e825a2ce42dc92cd56b3c2cd24e8c2ccf15c72c59e72d2c1ac5352c00a1052bd876a52bc11f412b86df172b5b714c2b42cd8c2b34637e2b1e48cb2accb66e2abf42042a916e272a7bf7562a48301e2a4104882a40c8322a3a36492a2802972a0d557d29bfb934299e0a8b2998e5e0298bc455297c38b6293350232921255d290ff31528731ec1
  | 7, 0, 5 => 0x3c071d803bf0a74b3b8961983b6357883b5d973a3aeca3da3a9aeb2f3a57bf6c3a4ac17939dc95ba39b72fed396d428b396b351b39353a54390f7b1f38dca1ad38dc31f638bf2ecf38b7f3533873f497386d3698383b360737bf1d6737a90d6b3792b7f2378f7ea9378317ee373f30bf373cfc45370bd0093709185a36ebeecb36d0003236bb486a369f09dd3698eff6365df424363306f936102bff35fbbb4b35427ffb3542459f353e5673351a2acb350e98fc34fab66d34e168ad348300e034694089340091a333e7a16e33c0b67e33abe670339b6de13388b7fc335a55be3333a5b832d06d4d32c76fd7329932ee3287c53e3276a5c1323533b631e88820
  | 7, 0, 6 => 0x45690ae9456818c445461e3344f2161544c8b57843fce5de43e9341843e7fc5e4356eee9432411f6430f111842fbe64a42d860c942ad8ab642938fae426c479d4263202542391a64422a4d0d42289881421a0a4d420d9c884205d04941e7255e41dfa1ef41b4174c41b1693b41a66aab4195b076416ff7344169bf9e4122ba3f40ef18be40a744f94085327d40114274400204ed3fdae0823fd964cf3fba24703fab50003fa4f5333f9c22363f561e1c3f4827213f3205d63f252da43eef1ec33edbac7b3e86703c3e7bd8083e65d4ab3dee256b3dd6474b3d3014d43d26dfb13d21a4893d1ebcd63d020fd93cce35373c92d92c3c8249c83c820d253c6ed1a4
  | 7, 0, 7 => 0x4e8d76614e7400e54e708ac44e68afad4e65034f4e5d34534e37ff3b4e1a14854e1549714db94bee4d7443cc4d2adf594d24a5bd4cfb5d284cf3253c4cec209a4c9af7d44c9320e84c8adfa44c6a0abf4c6848c84bee965c4bb454674b7b05914b643fc64b3538444b21d40f4b1404df4b139a5d4b0ad4724a8a6c324a5a36fc4a4dd1db4a2aab494a06002c49dbf98049c6ea2f4993bc25496a77cf494ab295493966f14933dad848a67c7b487d72e84825126e48186c23480b075147f18e7a47d982914786ad6e478345ba47475e20470a84e246fbfb0646ce08c646bd63254693a1d84684514b46503c394644e88945fbb87d45a2a97a459d63c4457f5ec6
  | 7, 0, 8 => 0x58f6d09b58d5ad6d58b8c81958ad242658a0f3e2587ce08e5833c249580e28b458053a1057de754257a31d79579ceee15775212f573d6a7c572a73a156e5d79556e561ab56aaa9b05692d977565c5e5b5633e4ee5623e9e255e6fb32558dc526557fdd00556b73115557adb2553a094055303af6550af717550652ba54b43a7854b26b9353ca8d5d5389c70f52c2c0a0527a9afc526d9a57526575bc5252e720521132085201832951419c6f513785fd512a7daf50d503fd50d274de50d12a8b50ba3eb650b65042509fc760509d90eb5086ebaa5084b7a75039cf454ffec99c4fe855494fa88ab34f9eecaf4f1f9f844f1467044ee69c8c4ed429274ebf5530
  | 7, 0, 9 => 0x61e076b561c8922461c319d9619305fd6157399f61536b426119d41d6110af96610aec2c61080d1f60eed24060e37e90609a59bd607b72e6606501066055e26d602b884960246d2f5fff37cb5fed9d5f5fdd77de5fb812115fb4b9305f85bc415f81912c5f6c173f5f6b8d2b5f45417a5f0a68f35edd83d15ece265e5eb6e06c5e9dd4c85e2165345de6c5325dce6a1d5da4c1f05d84ab1d5d7af3195d63dfcd5d3eb22d5d17d8fd5d14d5085d12ce075cbf4ad15cba73975c7f589f5c5ed6485c08eaaf5b9bdda45b4327c35b0f7b205ae8c3ce5ae24ad15a41a7395a0dea3c59f2b46459e8839259dedb8459a6b4df599c50055982210959592a725933582b
  | 7, 0, 10 => 0x6c85336f6c5800166c548b7c6c033dc06ba38b9e6b97e1ea6b6e117c6af8c9c96ae9063d6abc488b6a5b0bf06a482c5369e8c6d369bfb2446970bf6f69692d5e6961df276926f4da6924f41a6923304f690f20cb68e5a78d68d45be968b3ec9c68a58ae1687b7b81681867e067cc4dea678c8372678c33bf67239c63671781b167160b2466fcc9d466a87eac668614a1667246a2663e75166615a3146607e37965d5f79765cb891e65bcd2fb6590eea5657320766552782e64e1132b649897b2644d690f6431397963bbb2bd639797ea6353a1d063398a676336188a6335fe6a62f216bb62d647b962c1cfb56296fecc6293bb5062929e1462250a8b61fb1bb2
  | 7, 0, 11 => 0x76befbff76b4c528763e87187621da4575fdfe5175e6de7375bededa75a553d77584a59a75688164754fc9217528ba1e750cf168750964267501c58974e65d9174cbb07774c95a1f74c037547497834b747c9958744f2f70744a1f4f73f5677073b882b4739a6d9d73726f357365b971733e713673391b267330cfda7324583072d44b9c726c153e725b8fae71efa4917193c0cb7192070d716e997f7122b633710bb69670fd41a670d5c9e170c572a770b360da7088f7377077f9c06f834a416ead4a876e98bba36e829bc66e5279376e46f12e6e2bfd176e0b865c6ddf3ab76dafa7f36d8a32d26d22ccfb6d1b2e146d0f38c46cc9ecf66c9f2d636c90d912
  | 7, 0, 12 => 0x813ed259812e0dd0810f2d9380b2a32b80854292801076038004117e7ff396887f9bf5977f624f1e7f343a4f7ef522b97ea5708e7e9b7f2a7e9278507e7f11787e53ca6f7e5007e67e0f5a8b7df00d267d99aff67d805dd57d6b16db7d695f157d2b55c57ce6b9b97ce0823d7ccf3d847cc052b87c5679a67c4b25f67c34c7127c24d5ec7c1005487c0af7747ba2da817b9792677b815e127b8148cb7b38a1bb7b027e5a7af94a5e7ad9b7bd7a685fe47a5d0c1c7a0aafa379c7315379bd5325798bf5d9794fdd46794df861793744fd792983ae78f62cda7899d705787b7d20786e7c7b780bc8f67805b35677f9149677e2a06e77b2766677a1480d76d85f74
  | 7, 0, 13 => 0x8c2028678bbc312a8bb14f2f8b438d778b3dd07c8ac8d8178a993b7c8a93bec18a81b0a88a75c4ce8a2f019d8a06821b89f3993489e7fd19898608e2896ba8df89508b2a89472ebf8937bce188c2514088aa1da588a35ea7887437e58836e0328828c8d987e8e0f0877a78c98745189e870bce508704ce3486bfb66f869c64288697290686705671860d3b9a85efb3c185c3ecee85a2d87185753beb855aaed08541295f85178a21850b4b1784cf0882848a94a58476c8318429901583f3954e837bd53d835c9aa88358bc12833d710e833d437f833293e083324f9182ffcbae82e3c47c82d47f5f82736d5b826f9b8f82614b18821de44182113a50817d9b1b
  | 7, 0, 14 => 0x9516af7594eabe1994b7e3889493863b948273a89466a56f943d24c7942f48f3941dccaa93f40d0a93e73daf93e5144793b5eba193b36aa2938cd488931ec53193101ae8930586df92f8302c92cb4ffc92c36a6a9260fc67924aa8cb92041fe491f684a691f2907191a2af88918c5a799187981d916ef3a0916cc7d3915a87599148360e90c0704c90a6ab8e905dee4c905a01169029af998ffa68e08fef348d8fe9a8f78fdf91ec8f91161b8f71a1938f713f988f62c14b8f27d6fe8ed53e0d8eae1f4d8e78286d8e7669558e6f86db8e33b09b8e194a048d9e33c08d8249758d5f6f4c8d31b8a38d1ed3a98cfd2e1b8cebfa108cc7b8e68ca960d08c64e1ee
  | 7, 0, 15 => 0x9db831cb9d5e30269d4c3d0d9d11421a9cbfde239c8e83a89c74e3b19c4680cc9c13ec2f9c0a87af9bfff7699be7c0979bc0931f9bbfcae49bbfc0fe9b90cfd89b80928f9b78702a9b1141f19b0dd38c9ae89b769aaa0f7d9a98656f9a928b4499f8011499e02d39997db02a9973515999669b959962264b99585cc59954c735995336ef994267be9931b1fe9931a0a399253a5498ebf71898e27f3198cddf8998c478a6985e97bc98405c4b981d6398980971739800305f97ec74c49768e5319767d24c9759a8af973d7dbb971a52e796f883d496f4e0c896d35d1996c7df4696c654cb96c41dce9689d95b9670db19963393ff961a6f3395bb3948953ca632
  | 7, 1, 0 => 0xa8110047a7d633f7a72501eba7100fb7a6af3acfa691bcb5a684a1c7a6174514a5c75f65a590cdc8a589fe7fa5405515a5267037a50404d3a4f5a3c8a4e84de5a4c75773a494ba80a4869320a428cecaa3ca896aa390703fa36a4139a34bf28ea2f21d43a2d973a2a2cd4489a2cc83aea2763b37a251068ca237e894a20635c1a2025d5da1b43f61a1a3bca5a1964c37a1822aefa0ffc12da0faf9b1a0f23fe8a0ed1e35a0da99e1a08c56eba0857125a02e2f049ff982e99ff8643a9fee95f09fc926289f6d3f989f4a2acb9f1b2a1d9f03921c9ee60f5a9ec09f1d9eb47f2f9e98ed9d9e8551459e6d001c9e549f359e4065869e1a06709e0b60729dd56d0d
  | 7, 1, 1 => 0xb23b047fb21d840eb1db9bf1b1bfd837b1ae1d88b159e536b147c105b1446f9bb0e32b06b0be885bb094a0e5b0945291b07b2df5b03ebc32af9b2289af511deaaf27f62caeaaffc9ae9e89f6ae94ecadae7a0db7ae792b02ae5635d0ae45b6fdae21a5f2addf0384add14485ad8da066ad1de092ad18982fad06daa8acd55f77acccad9bacb976acac9d464cac81e873ac740321ac52d745ac3b3de6ac2817b2ac20dc44ac0e1dbeabc66819aba3ba95ab3f1928ab036524ab0094ebaae2c829aaabf859aa45b81faa343074aa2a7239a9e7e355a98b55c8a964a127a9260483a9131075a8e4a6a0a8e137d3a8a212f7a8767affa8500690a8407ff5a8187690
  | 7, 1, 2 => 0xbc38eed2bc1b5157bc0fd8a9bbd0e250bbbb9ca0bb6905cbbb536b52bb2bc4d0bb27b356bb20d37bbb113f38baeba03dbada1e4cba9bc06dba8234adba678793ba606cd7ba58198eb9f0b52ab9e5f66bb9bf5ab4b96ba581b9501ba2b901e6d0b8f8956cb8ca5cb8b8bf0908b8b26dfdb8845c83b84c4a65b7f766cab7af4ab4b7a391acb7842f4bb75f91c2b74f340cb74c752eb711420fb67cebd0b67579f2b647e64eb62a91bdb608648ab5a76137b5a6ef3fb591f83fb5562e40b4ebec1db4d8b370b4d0e9e0b497e3ffb4549ac6b43492bfb429e16cb407b969b3c7d433b3ae7953b3832b99b3818eb8b2ecdc34b2d0b010b2a67dc3b265c412b25e5f62
  | 7, 1, 3 => 0xc6623aa1c62f1128c5f6fcb5c5c59377c5866f95c526badec4e3991fc4db4a0dc4c90a9dc4b5d2b9c49af72bc497e4b0c470f588c44147aac40919c9c3dd79acc3b27a64c2c4f678c2bb39e0c28f65ccc28d123bc26778a6c237c534c1f052b4c1e7c8c6c18270c8c16ea0a3c13eb19dc0eaab43c045954ac01c245bc018fa19c00e2ce1c000c1b1bfee3a86bfdfd4f0bfbebae3bf95affbbf935932bf898ae8bf7e924ebf605e05bf44ba99bf4349e2bf0bbb85befd167dbedd1ea2bec55acabe4e7a3cbe33444bbe19cecfbe07fbc7be011283bdf77620bdddcd25bda23594bd9c0d1bbd803234bcee49d7bcca73a7bcb41943bcac3712bc5ad31bbc506207
  | 7, 1, 4 => 0xcf8c37eccf651ab6cf5ddffbcf4c853ecf3748bccf299811cf1d6b2fceb62b2dce8351bbce65deddce520fbcce1af5a2ce1502afce08b058ce04edffcd4a8fdacd0e8dbfccf7e781cce8599bcce28f39cccf954accbaa2f2ccb8d58acca944d8cc602b10cc546ba4cc4ad961cc04a432cbfd2d53cbfa840acbec55efcb615d11cb451b79caf685eccaefce9ecacc77c6cab5490aca8818bbca7dbd21ca68a6bcca555fc4ca385cdbc9f10d7fc9cbe633c9c4dd1dc98f6c6ac9794b1fc976bd77c965a8ffc9421defc8d30a3ac89c9e85c87b7b57c860ffd9c83eb8cfc829e141c82971d5c8033f81c7c2b8fec7972e5bc6f3220cc6e33866c69ffa27c68d390f
  | 7, 1, 5 => 0xd8f96a32d8f7562ad8f20b95d8ee1682d8cef8ded8cac204d8729e39d85ded4dd84b58cbd8465bc2d832c79ad82773ead808f7e5d7d0fd1bd7cf2dccd7c0dd1bd78613e0d7283adcd6fa86bad6ea2904d6e40d2ad6c96a4dd69a84a9d6692655d5e44300d5b5f79fd5442397d542562fd52c8a38d461a42ad45717f4d4190236d3f617dbd3cd8bc1d37cf759d37b29f1d3655dfad3561860d33d65d4d3370471d322d6fed307bcccd2fd705dd2fb4668d2cf1fb4d282ca97d24c54b9d239893ad214fac3d1fcebc3d1fbadccd1e583b1d1ac0026d1723623d170d1a3d16e5dbfd1580846d15619c6d10465b8d0d1205dd08247e8d01622edcff8574dcfea3e97
  | 7, 1, 6 => 0xe25929fde191b813e18278c8e1455695e1396393e136fcb9e12ca6f4e119b8bde100943ae0e0ce7ae0c8841de0b18480e090eb3be08e0c62e07b2a37e074c2dae072172de0662ce5e0531625e0045351e0028e61e000e70adfe8af95dfc1d156dfa59472df82a98edf814e89df6e3822df198746deda8ae6debad334deabcba6de72b37eddb68b26dd8508a1dd6059c6dd4d5752dd0b2ddedcc89ae5dc9a2c69dc82d4b3dc48c872dc2b0159dbfdce00dbeb56ffdbe00383dbdccd07dbbd0a3fdb8462c8db65ec16db571064db569198db4413d2dad170addacce843dab8c3dadaad8f87da6c954dda61419dda460ee5da3d2664d98fe426d959200cd9069a79
  | 7, 1, 7 => 0xeb3d6051ead5062deab7dde3ea9f1848ea9bd94fea7d6367ea69c5f5ea681c52ea34e2a8ea053820e9d5dec3e9b35c88e9713d6be9609396e9145362e90a466be8dd12e7e8ab9dbae8a21811e89bfac4e88df45fe8818e34e8685acae84fc37ce8495d18e838a758e82dfb2ce8214b0ae8144a65e8017a2ce7d9adc7e7c466cde75f1e46e7399420e71914dae6f02fade6c1e7b5e68e1704e67e2d5ee5f62735e5daae04e5bf9a30e59b8f43e5943b56e58a6d0ce54148c9e50c9da9e4e0203ae4d9c7aee4c93f64e4c1afd6e4467f62e3d0788de3a0da2be3923d94e373300fe3446298e33ee4d5e3348390e32e3e5ce32b1457e2ad1936e290a862e27895b3
  | 7, 1, 8 => 0xf55dde90f5304b86f5109622f474d66cf422fc21f415e4d3f415021ef4029c27f3ed48f2f3c81542f3c4153cf394049df3910cd3f335f6a3f321a327f2fedaeff2e394d3f29f7551f2049c15f1f6e0d6f1ed3813f1c3b22bf19db3b2f197e0bbf18f2935f10f3cd9f10d2b1bf0cd59eaf08f9d94f07e9f45f068d0c3eff14f81efd833eeefa6a8dfef996472ef98f3b9ef7f4eeaef7d8fc8ef4746cceeda0839eeaee791ee23909cedf99859edc98305edbbddceeda86f61ed8be3d2ed720b13ed5cbd68ed49643ded275ae7ed08a60eecd123afeca6cae1ec8c87a3ec7c632aec66227aec631cc5ebe24d9cebab792feb955e7ceb4f5268eb43cc1feb413bf9
  | 7, 1, 9 => 0xfcfb4ebefcf95f79fcf50d9efceb0b28fc9b980dfc7e3331fc621d98fc4f2ebafc4e8f9bfc3c1b9afc21d1c1fbd94c56fbd8edfafbc5f651fb7cbcfdfb585651fb4486effb433853fb3027b2fa87c339fa638275fa56648bfa53b8d2fa48847ffa24aabcfa19e45afa0bc0e3f9e9bd83f9d4cf87f9aed299f9ac5005f95347a7f91176c9f9076f3ff90411f7f8f1ef1af8e6b461f8891f4ef87d843ef84f2c4df81a05cff7f8e245f7e665d5f7cb96a8f7a7777ff782e5baf76bbee1f75af9f2f756fbeaf7435c0ef7325e1bf6f63a51f6e87c11f6b19c3af6a67826f676193af63029adf6170511f60b62f9f6099b33f5eb20bbf5ce3b03f5c1c01ef568463f
  | 7, 1, 10 => 0xffebe533ffcd33cdff8f76e1ff82234fff34a3adff176f7dff088f35ff077c9dfef2edb9fed64e70fecda4e8fec98830fe739655fe4d5cfcfe463010fe143688fe09da09fddc2ba5fd810311fd80606ffd5ed6d1fd333380fd284922fcfb68de
  | 8, 0, 0 => 0x28736fa127f900ef2764e2a726c17c5624eb385a24368a0d241ae38822fd0d3522521578223cfbcd2103e11d1facba191dd391cb1d36919d1d21eafc1cf7e4341be736751bd68aa41b3d035d19eda83518ddfae018491349178270b11663beb0160d185815fa176615ea2dc014ccf9dc13734caf10e87ecc108ae1ac1076a8040fe91b5a0fe72a990f0fe5d90e8587a80e7d19c40db2fc7a0cfa623d0c22e64f0b5757610b00d3fd0a9899f8098a0cfe0985b8e708cf1df808729adb085e0bf70774f84706ffe09b06d5546706647db7061dd98805b4bb760522378c04ff35c004ae569104a62e7c047512b804244b480334fbc40312123600830b55003e590a
  | 8, 0, 1 => 0x4b85288b4b4097c14b1f358a4af0fcd64a86956649b559a74978086c48b3455f4850336847e6f6464774b70f4689db1445f14ddf45ed680645af2d6b451032fa44ea24a9443acc4b4422b1fc4329f17b42d860c94285ef8f422923bc40fdd63040982e5a3fcf5cc13ead9e393d7077383b34c7713afd60273a1dbef63a1c5f4339bed33d39a60da2393b393139328fec390d085a3861a2a4384665c2371b3fbf36ae22d13640897a3539e074330261e132a7cf8531601f5730ba311c3098ad6d30896e2230781dde2fe7ff5f2fb879da2ed972652dec17522daa52e22ccad7332bf289122b8dd2232b31f6b32a85c0a02a719cf329dbefa629b484e128c67460
  | 8, 0, 2 => 0x6d984e506d6960e56b200a506b022d8e6a5967b86a275dca69ad2dc169a3424f69773a706948961c69089f4e68c9048168c124c768666c2467e7cb0c67ce92b267a3c4896760a4bb67225fde670fe02e66dd21f166d93e1265ee3ccc6544df0064dfafd263076e43627168a06240cbab612c571a60c73bd460a888ba6077da6060507fe96000993c5fbf99f95f6d245d5eb0dedf5ea189375e68564b5d17c0025b6ca1675b3916d25b2c6da15a6a02b35a65cb0959c066d358cd881857f8949f57df34d057df1f2357b0e66f573ec352568fc3fb56618b4755fe3f2654f2587952f9b84952b8402b507c6eeb4df9e3134da0f7e84c7181d24c0054d34bf5ebc4
  | 8, 0, 3 => 0x89f236c689797c2b8900bee288fff5b68895799e887437e587d6c96187ced70687cea5d78710b4f48675f0ff86369415859fe5508502b0a5848218fa8464689c8332bdd282f2eadf82a2633b828f70e182614b188224362d81d99ab9811474fa80437db27f99684a7f132b1a7edfec597e9d06ce7e2b55927e1949c17e08edba7d1d106e7ce5c2597c8967fa7c8106d07c3096787b45ef2c7a8ca7f37a76d4d479fe9a177947f9e27836a26577dff3e977c22f6177195151769098c175f051ad75c9f62975af1c43758caae575810e607569a1257445e99a743b34d67431b33873b01f3e73030669729bd432721c2af0708a3ac5704a027c6fa993546e15510b
  | 8, 0, 4 => 0xa6facad7a663da61a6445fd6a62afc61a5b19f0aa57c8260a494ba80a3eac9f2a333da41a2de6f97a29cd03ca2905892a2804ecea2621fdea1c9b5faa1748fb1a15392e4a03e7b57a03ce6b2a0317309a004e02f9eef4aa39ecc14489e4ffbbf9e0571b09db218cf9d2109df9cebbd729c7b39269c6d2ebf9b8a3c669b7e5d089b6f3e229a11c9cc99a4ffcd993cee42980df69f97ed931a976cf00a96b2205f964f52ea961045e195de29bd958b46a59562c53795379eaf95178725939a1fdb937f44349371a05992d6c71d91df562391c8cfc391316dea9057a0088f4f5a7a8ee05a298dffff528c7d04a98b969fb78b82116a8b73c1868af983f68ac8d753
  | 8, 0, 5 => 0xc3ed52ebc34caa51c2912d58c2037a77c1ca8ac0c182a05ec1628508c10eafeac1027068c0bbfdc6c03247cfc0290ea1c012abf0bfe76089bf23bad5bf21187bbe980561bd9fb0fdbd9e40bebd1acaecbc542854bbd0e250bba622bdbb8c28c9bb7012e8bb038207babbe563b9ffbf23b9b426dfb8ffabb4b864d278b84bdbbcb8161e07b73b2416b63b7ad9b5f44193b5a7056fb5793bfcb5456a70b4b05633b49f1bfdb32776f0b1b4f7b2b1146f26b090567cafab3129af4a1e6faf327da3ae43986eae3275b1ad4d904ead262ec8ad20b424ab6e3959ab0edae3aac752a7a9f273f7a8cea874a8c70d27a8a3455fa84a25ffa7dca2c7a794af40a767a614
  | 8, 0, 6 => 0xe1efa266e1ca5fc4e16359cee054ccd4dfae70a6df730953de77c545de63a60ede57fb7bdde5965dddc23632dd28f898dd1af66bdc72db0adc6a17cedc226a26dbecf762da0093e9d967b24dd90d7775d901b7dbd8f206efd8947344d876dc57d57a10c2d4fa9690d48a317dd46b83c8d3707bfcd2fa8aa8d24db4ebd1024c99d09ce63ed05e404ad003ae56cf36465ecf335269ced6b2e3ce24c56fce1e0ddbcd8606d2cd468893ccc58d3ccbb907bccaa9cfdbca66a7b3ca003fb8c9bceffdc8e9b08cc8ce26adc8833fa8c82adb97c77571d5c76c30c1c6e758f9c6a97e1dc6485bd3c5c5f159c5ab8fdac5866f95c573d8c8c4e4ed42c456be7bc3ff869d
  | 8, 0, 7 => 0xffd55bf7ff82234ffeb87767fe897d15fe8600cffd3ae12afd124cd3fbc4fbadfbc06c06fb5773bff93020eef8bf5267f88bc9acf81a05cff615c1f0f5ec4ba5f315725ef2fb5f6ef2450b53f2165256f1ecd274f1a3c596f0aab1ffeff93542efb76ccdef992c97ee77bbe7ee228795eda6d11ced84fd02ec36be60ec183774ebc6d37deb97b9b2eafcd651ea97c532e8bca3e2e884a584e7088a33e6d380e8e5b3e6b0e5a2e642e536c5f0e525fa75e4dc43aae4c22ea2e47dbc50e434f3cde3ee27b1e3e76ac8e34400b9e321d5afe2df9ab7
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x610200000008404c9054c8303000000284080000006101
  | 6, 0, 0 => 0x203880c000000610000095100820000004110800000028428000000a100048d5100c20000080a2030000202880cc0058c130810440048c20000000a1000000000842412254403080000003840006254c030800000038428000000e1010000603880c023548030800000038434000000e10000002038820000000a100000000284100025440203000000184001a3544030800000048428000080a20300016400800000010010d
  | 6, 0, 1 => 0xe048820020280e30800000008424000000610000000028428000000e10000000028424000000a1040000003841118058c030800100028800000000e100260d5104c20020180e30803895100c2000000061000000602880c00254c020800000028410002544020300000018404000000610106895100c20000000a10100000008410000000e10000000028410000000610004895300c200010440208324c8008c20000000a100
  | 6, 0, 2 => 0x28410000180a2030180e048c200000006100000c9320820000000a100000000284040000002104000000384280a35440308324c8048c20411000a30800000018400000000a104000000184280000006100000c5310820c1300123080000003842400000061010000a048820000000610d0000202880c000000610000000028400000000610100000018400000000a100314c4048c201235480308000000284008105880308
  | 6, 0, 3 => 0x68d5200c20812000e308048d5200c20000080e20300000028404000180a20320480038c20000280e203314c4028c20000000a100028d5200c20000000a10d00000018424000000e10a00000038400000000210400000048428000000e1000000a038820063548030821484038c2099450c030800000018400000000e10000000028410000180e2080280e048c20000000e10036514200c20000000e100000d510080c00000c9110
  | 6, 0, 4 => 0x38401180588030800000008400000000610000000038410000000610100000028434000000a10a00000028404000000610003855200c20000000e10400000028428060280e3080000001842400104402030011510082000450412030000002840441100123080000003843400104402030009510080c004504120300000028400000000e100000d5200820c932006308304c0028c20000180e20300000008404000000e109
  | 6, 0, 5 => 0x18400000000a10103895300c20000000a10000000028404000080e20300000038400000000610000000018400000000a10400000038428000000e10032415320c20c8058c930800055300820000000610000000018410000000210100000028434000000a10000000038400000000610a36095104c2012154c030800000028424000000a10030416300c2000000021040000000840c000000210900002048820000010010d
  | 6, 0, 6 => 0xe048820000080e203000d5100820c0058c130802855300c20000000a10100000038408123544030800000038400000000e10000000028404000080a20806895100c20000000e10000000038410000000e1090000603880c0000002101000020188200202812308000000284281a254c030800000028400000000e10a00000028400004000e20000806048c20000000e10a04895100c201a3544030810440028c20000000610d
  | 6, 0, 7 => 0x46095104c20000281220800000018400000000210421484048c20000000a10100000018410000000610300000018428000000e109000000284000040006200000c932080c000181220800806028c20000000610a0000003841000304c020800000038400000000210332415320c20411000e308204d5200c20000000610a03895100c20000000a10000000028428c13001230800000018400000000e10400000038424000000e100
  | 6, 0, 8 => 0x18404000000e1000180a048c20000000a10a00895300c20d9250403080000203880c994504030800000018400000000a109304c0028c20000000a10000000028424000280e20800081200820000000e10000000038434000280e20332415320c0c0a3544030820480048c20000000610000000008404000000210100000038400812001230800000038408000000e1000000000841000214842080000002842400324c8208
  | 6, 0, 9 => 0xd510080c000000e1040000002840000000061000000001840c00354402030000a03880c000000a100264d4100c20000000610d00000038434000000610000000028404000080a20300000008404000080620300000028400000000e1000000003841000154802080000201880d180584030800000008404000000610106514320c20000000a10900000038434000000e10a00000028410000180a20804855200c20000000e10a
  | 6, 0, 10 => 0x20381230800000038400000000610a00000038400000000e10900000018410000000e102460d5104c20000000e10000000038428000000e10000000038400000000e10900000018428000000a10010440038c20d94504030800000048428000000e100000000184008005881308000c932080c000000610420016204c20000000a10000000028400000000210004895300c20c1254c0308
  | 7, 0, 0 => 0x840c000000a108000d510080c00000061040000003842400055082080000001840c000000a1000010403882000000021030005443482000255002080000030042000254c02080000003840000154802080000003840c002040a20800000008434000000e10a0000603882000058812080008004882000000061090000000842000000021040001620082000314c42080000e048820000000a103000c93208200021484203
  | 7, 0, 1 => 0x3840000254402030011410480c003548020800040038820000000a10a00000008400004100220800002038820000180e2080000000840c00354802080000000840400000c91030000603880c00000061080000e048820000000e10d000000284240035440208000c5310820000381220800006028820000180e208000d402882000058c420800000028428000000a1030000003840c00254c020800081200820000000a109
  | 7, 0, 2 => 0x18428000000e10300015410820000000210300000028420000000610d00114038820000180a2030000020440c000080620800000028400000000e100000c9320820000280e2080000203882000420062080000030440c00054842080000002842800314c420800000038424000000210300000038410000280e2080004110080c00000021080000002840c0002812208000000284340001812208000004204200015480208
  | 7, 0, 3 => 0xa048820000080a2080000020040c00204062080000003841000324c82080000020440c00324c82080009530080c000080e2080000000840c000000e108000c1300820002550c20800000028410000000610d0011410480c000000210300000028420000000a10300000028400000000a10a000d421482000204802030000001840000354842080000a038820000000210300000038428000000610d00114204820000280e203
  | 7, 0, 4 => 0x8434000000a10000000028404002040a20800016324820001500a20800000008410000000e10400000028400000000e1080000604882000000c91030000201880c000000a103000c9320820003100a2080000e048820000000610300000018404000000610d00000018428000000210900006038820000000e10d000c5310820000550c208000c9430820001550820800055200820004000e2080001502882000450c1208
  | 7, 0, 5 => 0x8521080c00000c110300000038424000000e10000000038400003550420800006028820000000e1000000a04882000254c02080000000840c003100a2080000002842000154c02030000000840c000000210400000018400000000a10300000018424000000a103000d52008200000006101000951008200030412208000d520080c000180e208000c5048820000280e2080000000840c00000061030000003840c0035480208
  | 7, 0, 6 => 0x8428001000a2080000001842800420062080000000840c000000a1090000002840c00000c110300000304420000000e1080000000842800314c420300041100820003000a208000d5204820002148420800094008820004300620800094038820000280e208000c9320820000000e10d0000602880c004200620800095100820004500220800000018434000180a2080000031440c000180e208001142048200000002109
  | 7, 0, 7 => 0x840c000000e10000000018404000000a10d0010c028820000000610300000008400000000e10300000018428000180e208000410388200010012208000060388200000012108000c5048820000010010d0000a0388200025412208000d4028820000000a10000015210820002550420800000400434002550c2080000002842800000c91030000002842800304c020800095300820000000a10900000008428000000e108
  | 7, 0, 8 => 0xa038820000000610400000018400000000e1030000002840c0003812208000c9430820000080e20800000008428000000a1030000002840c000000610300000018424000000610400000008410003240e20800000028424000588120800084008820000180a20800080038820000180e208000000384200005884208000000284040000002104000000284340000100100000d520082000254c0208000953008200021412208
  | 7, 0, 9 => 0x95300820000180e2030000020440c000081220800000028424000381220800000018400000280e208000c9320820000180a2080000002841000354802080000001840000000811030000003840c000181220800002038820000280e20800000410420000000610100000018400000000e108000d5100820000000a10300094404820000280e20800041038820000000610d0000000840000000c810300000038420002000e208
  | 7, 0, 10 => 0x15410820000000610300000008424000080e20800000028404000000a1000000002840000008122080000a048820000000e1090000021040c000000e10800000038400000000a10300000038428000000610a0000030040c003548020800000038400000280e20800006028820000081220800000028410000080620300000018400000000610a0000002840c004500220800000018410000000210300000028400000000a104
  | 7, 0, 11 => 0xc1018820000000a10a000553008200035480208000000184340045002208000d5100820000000210a00094038820003001220800000038434000080a20300000038424000180e2030000003840c00000121080000001840c000000e1040000000840c000000e1080000003840c000000a1090000003840c000500e2080000a03880c000000210d0000032440c0010440208000c5038820000180e208001142048200000006100
  | 7, 0, 12 => 0x2840c000000a1000000003840c000000e10000041100820000000a10d0010c00882000000411080000000840400000c51030005520080c00000061090000a03880c000000a10000000018400000000a10300095100820000000210400006028820000000a103000d5200820000000610300085210820000000e1040005530080c000280e2080000002840c000000a10300000048420000180a2030000000840c0025504208
  | 7, 0, 13 => 0x28424000000610300000018400000000610000054304820002140e2080000002840c0021484208000c9320820000001210800000028428000000e10800002048820001000e2080000001840c00324c82080000020440c000008110300000038428000000a100000c102882000000c1103000943048200010440208000d5100820003140a208000d510080c000000210300055200820000000210a00015420820000000e100
  | 7, 0, 14 => 0x8434000000210300000018420002101220800000008428003250820800114008820000000210a00000008424000000e1040000002840c000000210900000008400000000e1030009400882000000021040000001840c00450c92080000001843400204802030000021440c00254c02080000003840c00000411030000003840c00008122080009510082000000411080000020440c000000a101000000384100035504208
  | 7, 0, 15 => 0x104028820002140a2080009530082000255042080000000842400254022080000001840000410022080000000840c000004110300002038820000000a1040004002882000354802030000002840000304c020300000028420003140a20800000028428000000a10300002018820000180e20800000018428000000a103000000184280000006103000000384280015109208000d5204820000081220800055300820000000a103
  | 7, 1, 0 => 0x2038820000000e10400015420820000080620300000038428000081220800000008410003040e20800015430820000280e2080000003840c000080e2030000201882000000021030000603882000154c0208000c920482000055042080000002840c00000061030000002840c000548420800000028400000000a100000c800882000450c52080000000840400000c9103000d54008200000002103000950388200003812208
  | 7, 1, 1 => 0x2840c000080a2030000000840c000000610a0000032440c000000e10000000028428000000a10d0000032440c000080e20800014324820000000a10400000018428000080a20800000038434000000e1000000a038820004300220800000008434000008110a0000e048820000000210800000400434000080a2080000003840c000010110800055300820000000e108000000284340035508208000003244200000002109
  | 7, 1, 2 => 0x32440c000000e1040009531082000350022080000602880c00000061030000003840000304c02030000001840c000000e10300000018410000000a10d0004110080c00154c02080008521080c0000002101000000284280045041208000000284240000006100000c130080c000000610a00000028434000000e103000000384280000006100000c531082000450c920800002028820003548020800000018424000000e10a
  | 7, 1, 3 => 0xd510082000450c5208000d5210820000000a1000000000840c00314c4208000d510080c000000210000000038428000000a1040009510080c004504120300014038820000000a103000c942082000058c120800002018820000000a10d00000008400000000e103000c0028820000000610d000d520082000304c0208000d5100820000000a1090000002842800154c020800000038400000000a10800000028404000000a108
  | 7, 1, 4 => 0x8120080c000000a10000000038434000000a10400002018820000080a208000c932082000000021090000003840c000008110a00006038820000000a1000000003840c002500220800000038410003548020800016214820000550c20800000028434000000a103000d5100820000000210800000028424000000e103000c5310820000000e1030005530080c00000811030000002842000000061030000010440c002100e208
  | 7, 1, 5 => 0x20288200000002101000c130080c000181220800000008404000000e103000000384280000806208000c903882000304c020800015420820000000610400000038434000000a10d00000038428000000610a00000038428000000e10a00000028420001500e2080009530080c000000e10a0000003842400000c91030000002840c004500e20800000038424000000610300000038410000000a10d000000184000000006101
  | 7, 1, 6 => 0x55430820001500e2080000201882000254c02080000031440c002040e2080000002840c000000610a00002028820000000a1040000031440c000181220800000018400000000e10a00114324820003201220800006038820000080e208000d510082000154c02030000030440c00000021080000032440c000000a1030008503882000324c82080000002840c00304c02080000e048820000080e2080000203880c000000a10d
  | 7, 1, 7 => 0x204882000314c42030000030440c000180e20800000320420000000e10a00000048420003541220800006048820000000e108000c900882000028122080000004842000250c5208000d440482000008062080000000842000354402080000a038820000000e10d0000032440c000000e10900000008434004500e20800000018410000004010300040048820000000e10a0000030440c000000e103000020488200001812208
  | 7, 1, 8 => 0x843400154802030000001840c00008122080000a048820000000e10800000048420000000a10a00015430820000080a2080000002840c000000a10400000008410000000e1030000202882000304c020800015320820003544020800000008434000281220800000008420000180a20300114314820000000610a00002028820003500a208000d54008200025440208000000284240045085208000153108200002812208
  | 7, 1, 9 => 0x28434000008510300000028404003544020800000018400000000e108000c1300820000000610a0000003840c00430062080000001842800000c11030000000842800058812080000010440c000080a2080000002840c002544020800000018410000000a10d00114028820000000e10800000028434000000e1090000001843400000061000008521082000000c91030000043042000254402030011410480c000280e208
  | 7, 1, 10 => 0x10440c00254c02080000604882000154c020800000028434000000e1090010c0288200000002109000004004200035481208000000184000000006104000c130082000254c020300000038400000080620300000018400000280e2030000201880c0035440208000c1300820000080e208000000084200000108108000000384000000012108000d5200820000008110300006048820000000a103001080388200005412208
  | 7, 1, 11 => 0xa048820000000210300016304820000000210300000028420003544020800000008434000181220800000008410003548420800100028820000080a20300114008820003548020800000038420000080a2030008521082000058c1208000810388200000006109000c0048820000550c2080000a048820000000e108000c932080c001548020800000018410002048020800000018428004500a208000d4008820000000a101
  | 7, 1, 12 => 0x8420000180e2030000a048820000000610300041100820000000e10000000028434000180e20800000018434000000610000000038428000000610a000c8018820000000610a00000018428000000a1090000603882000304c02080005530082000000061030000e048820000000a1090000001840c000000e10900000008420000000210900000028400000180e20800000048420000000e103000000184340003812208
  | 7, 1, 13 => 0x602882000324122080000003842000200122080000002840c000001210800000018424001548020300085210820000000210900081200820000000e10d00104028820000000a1000005402882000008062080000a038820001000e208000000284280000081103000c8008820000000a103000d510080c000180a20800006048820001500a2080004104882000000c110300015310820000000610a00114038820000000a109
  | 7, 1, 14 => 0xc5310820000000a10100002028820000000210300006028820000000a10300108038820003548520800000048420000180a203000d420482000000411080000a0488200010412208000c5310820000000a10a0000004842000314c420300080048820000000a104000d5028820002000e2080000a03880c002048020300006028820004200e20800000018428000000a1030010c018820000081220800002038820000000e100
  | 7, 1, 15 => 0x200420002510d20800000028434003040220800002028820000000e10000000028400004300a2080000002842000204802080000000840c000000610a0000003840c000000e10d00000028420000080620800085210820001548020300000028434000000a1080000003840c000008110a00000018434004508120800000038410001548020800002048820001000a2080000001842800028122080001541082000150c9208
  | 7, 2, 0 => 0x3840000000061000000202882000314122080000002842000355042080009530082000008122080000003840c004500a20800000038400002500e20800000038400000280e20800000008420000000210d00000018400000180e2080000003840c000000a100000000084340000085103000d520082000204802080000010440c000000210300000028400000000a103000000384280002812208000852108200000041108
  | 7, 2, 1 => 0x3144200000002103000c1300820000000210100014038820000000a100000000384200020480208000060288200000006109000c9320820000000210800000038400003544020800000038424000381220800100028820000000a108000d520080c000000a10a0005530082000324c820300000028424000000a10000000008428000000a10000000048420000000210d0000002842800355002080000020440c0000002103
  | 7, 2, 2 => 0x38424002100220800000008404000000e1000000003840c000180e208000d5420820000180e20300000400400000180a20800000008410000000a10900055300820000000a10d00000038400000000210d0000000840c004500a208000000384340000006100000d5100820000000e1000000a03882000154c02080000203880c0000006100000552008200020480208000d510082000000061000000002841000058c9208
  | 7, 2, 3 => 0xa03880c000008110300095400820003040e20800000018434003140e20800000424420000000210400000048420000000a1040000602882000000021030000201882000304c0208000d5200820000000610100055200820003000a2080000032440c000000e10300000008434000000210d00085048820000000a1040000603882000051092080000000840c000000a103000000084100021484203000400488200035002208
  | 7, 2, 4 => 0x41028820000000e10400000008424000000210d0000003840000254c420800015320820000000210a0000604882000000061000000201882000324022080008521080c000000610a0000e048820000000a100000c901882000000851080000002840000000061080000a03882000324412080000021440c000000a10800055200820000000a10900000100420000000a10800000018404000000a1080000a0388200032012208
  | 7, 2, 5 => 0xc5038820000080a2080000003840c000000e1080000000841000000c11030000030440c0001812208000c932080c000000e10300055200820003240a208000d510080c000000210300006028820000000a10800000400400000000e1000004110080c000000610d0000000840c00008062080000602882000154c02080009510082000254402030011410480c000000610800000028424000000e103000060288200020480203
  | 7, 2, 6 => 0x84040035480203000d520080c000000a10d00000038420003540220800000048420000000e10d00002028820000500a2080000001840400000021010000204882000000411080000020440c000000a1080000021440c004100e20800085038820000180a20800041028820000000210300000028400000004110a00055200820000000610d000d4104820001000e2080000002840c00304122080000a0488200020402208
  | 7, 2, 7 => 0x38428000000610000000008428000000a10a0000000842000000021040000001842400000121080000000840c00214842080000003843400001001000000031040c000000610a0000000842400104402030000002840400000c110300000018420000000610000000038428000000e10d000020488200000002100000d520082000254402030000000840c00028122080009530080c000000e103000000084000035480208
  | 7, 2, 8 => 0x1840c000000a10900041100820000000610300000028400000000a10a0000003843400204802080000002840000054c4208000d5410820004500a20800000038428000180a20300000008400002500e2080000030440c000080e20800095400820000000e1030000203880c00000c51030000000842000000c5103000000084340000006100000d5100820003140a20800002028820000080e2080000002840c0000006100
  | 7, 2, 9 => 0x1402882000450c9208000540388200020480208000d510082000254c0203000d4424820004500e20800000038420000000a10400114214820000080a2030000003843400254c420800114104820000180e20300054404820000000a10a0000001842000000c91030010800882000000061090000003841000154802030000032440c00210122080000001842800000061010000000843400058c020800000038400000000e104
  | 7, 2, 10 => 0x8100882000314c42030000001842400000c91030000032440c000000a1080000003840c004500a20800000018428001000a208000c1300820000000a108000002104200000006100000c8018820000000e10800085210820003100220800095100820000000e10d000c9304820004500220800000028404000500e2080000002840c000000e10000054038820000000610800000008434000181220800014214820000000e100
  | 7, 2, 11 => 0x95100820000500a20800002048820000004110800000038400000000e1080000002840c00310022080000003840c00000061030009510080c004504120300085048820000000a10a0005520082000104402080000000840c000000a10300000038424000000e10d00000028420000000a10000095100820000510d208000020388200015500208000060388200032412208000d5420820000540e20800085028820000000e10d
  | 7, 2, 12 => 0x10440c000000210a0000003840c00000021090000001840000254c02080000003840c003040620800000104428000180a20800002038820000000610100081048820000000e1030000000840c00000c910800015420820000000610a0000a038820000000e1040000002841000000c110300095400820000000210d00002018820002544020800000400400000000210000000018400000000a1090004110080c0001812208
  | 7, 2, 13 => 0x10c008820000080a2030010800882000154c020300000028434000000e1090000602882000254c020800000018434000000210400000028428000080e2080000032440c00204802080000604882000000411030011421482000000061000009530080c00324c820300095310820000000a10400000038424000001210800095100820002100e2080000001842000054c82080000a048820000000a104000953008200000081103
  | 7, 2, 14 => 0x1840c000080e208000c531082000250412080004110082000028122080000e048820003548420800000048420000000210300095100820000000a10800000018434000000a1030000202882000000021090000010442800000061080000003841000154802080000010440c00420022080011400882000000021080011430482000154c02080000030440c000000a1000000032440c003040a20800085210820000010d108
  | 7, 2, 15 => 0xe04882000450c120800002028820000080e20800000018434002048020800000048420000000a1030000001840c0021484208000d510080c00000021010000002841000000c81030000001843400354802080000e048820003500220800000028400000180e20300000018428000000210a00000018434000000210300000038434000080a2080000003840c000000a10a00002038820000000a104000000484200000006103
  | 7, 3, 0 => 0x840000008122080000002842800000021040000021440c001044020800000320420000000a10a0000a03880c000000a1000000003840c000000210300095300820000000e10300002048820000000a10300000028428000000210400081200820001044020800000028434000000610400000028400002048020800000400400000000610a0009510082000000021030000000842400000061040000000841000324c8203
  | 7, 3, 1 => 0x3840c0032406208000c130080c000000610100002028820000000610d0000001843400254c02080000031440c000000a1040000031440c00355002080008104882000314c42030000002840000000021040000032440c00000021030000000840c000080e20300000018400000000e103000c531082000310122080004110082000000061000000000840c000000610400000028400001500a208000951008200025504208
  | 7, 3, 2 => 0x203880c00018122080009400882000104402080009510082000254c020800014028820001500e2080000e048820003101220800000018434002544020800114038820000080e2080000002842800054c82030000001840000450852080000000840c004504120800000018424000000a10a00000028400000000210a0000002840c000180a2080000021440c000010c1080000001840000058c52080000000843400054c8208
  | 7, 3, 3 => 0x3840c000080a20300114304820000000610d0000003840c0030402208000d520080c000000a10d00095430820000000a104000c004882000204062080000010040c00038122080004110082000050c520800000018410003240a20800000008420000000a1040011400882000254402080000003843400018122080000001840c000000610d00000204420001500a20800100038820000010010d0000203880c0000002103
  | 7, 3, 4 => 0x9530082000000021090000002843400000061080000010040c000000a10a00000028428000180a2080000202882000354402080000002842800450c5208000003104200000002103000c5310820000008110300085028820002544020800054204820000000610300040048820000000a1040000021440c003500a208
  | 8, 0, 0 => 0x420420000000610800000314420000000a1080000031440c00000c01080000002842000000c910800000204420000000a1030000001842000000c41080000041042000000c01080000001842000000021080000021442000000c11080000003840c00000021030000020042000000061080000020442000001041080000032442000000c410800000304420000008010300000210420000000e108000001044200000081108
  | 8, 0, 1 => 0x1842000000121080000031042000000c910300000038420000000e1080000032040c000008110800000204420000000e1030000031042000000c11080000021040c00000851080000002840c00000021080000010042000001081080000021440c00000401030000032040c000000e1080000003840c00000811080000030440c000000a1080000003842000001081080000041042000001041080000000840c00000c5108
  | 8, 0, 2 => 0x28420000000e1080000021040c00000061080000032042000000851080000032040c000000e10800000320420000000e1080000041042000000c010800000420420000010c10800000200420000000a1030000042042000000c410800000018420000000e1080000031042000000021080000030442000000401080000000840c00000c01080000003842000000061030000020442000001001080000001842000000c1108
  | 8, 0, 3 => 0x30442000001081080000031442000000c51030000001840c00000061080000031040c000000e1030000040042000000061080000002840c000000e1080000040042000000061030000032042000000811030000010440c00000c410300000324420000000a1080000000840c00000021080000032440c000000e1030000020040c000010c10800000048420000010c108000002104200000041103000004104200000108108
  | 8, 0, 4 => 0x3842000000801030000040042000001041080000003840c000010c1080000020042000000841080000003842000001001080000010442000000c81080000010440c00000c91030000010442000001041080000032042000000851080000021440c000010c10800000100420000004010300000314420000010010800000304420000010c10800000320420000000a1080000030040c000010c1080000002840c00000c8108
  | 8, 0, 5 => 0x30440c00000801080000031442000000c01080000031440c000010c1080000040042000000c01080000032040c00000c01080000030040c00000c81080000031442000000021030000001842000000411080000002842000000401080000040042000000061030000002840c00000c41080000001840c000000a1080000031040c0000002108000002044200000002103000004304200000080108000000084200000081103
  | 8, 0, 6 => 0x20440c00000c010800000104420000000e1080000032042000000c81080000002842000000021080000010442000000841080000020042000000851080000031442000000851030000010042000000021080000010040c000008410300000200420000008510800000314420000000a108000004204200000040108000002004200000100108000001044200000108108000001044200000080103000000084200000041108
  | 8, 0, 7 => 0x31442000000401080000002842000000c110300000008420000000a10300000430420000000210300000028420000000610300000028420000000210800000038420000001210800000214420000000210800000100420000010c1080000004842000000c51080000001840c00000801080000000842000000c810800000048420000008010800000028420000000e1080000032440c000000e1080000003840c00000c5108
  | 8, 0, 8 => 0x1842000000121080000031440c00000851080000002840c00000401080000041042000000851080000003842000000841080000021042000000121080000010042000000021080000021040c00001001080000021042000000021030000000840c0000012108000000384200000080103000004004200000085108000004304200000040108000003144200000041103000000384200000100108000003044200000085108
  | 8, 0, 9 => 0x10040c00000c81080000002842000000021080000043042000000c01030000002842000000801080000010442000000401080000000842000000061080000021042000000061030000001840c00000121080000031040c000000e1030000003842000000061080000000842000000c81080000032442000000411080000032440c000000e1080000041042000000811030000003842000000c91080000031440c0000002108
  | 8, 0, 10 => 0x30042000000841080000032442000000c01030000040042000000061080000002842000000841080000031042000000c51080000032442000000c910800000324420000000a1080000003840c000000610800000314420000010010800000210420000010c1080000003842000000c910800000008420000000a10800000008420000008010800000210420000000a1080000021440c000000a1030000003840c0000002108
  | 8, 0, 11 => 0x1842000000c010800000018420000000e1080000001840c00000c41080000001842000000411080000032040c00000c41030000001842000000c910800000028420000008510800000310420000010c10800000100420000000e1080000032442000000811080000020440c000000e1080000003840c000000a1080000001842000000851080000020442000000061080000010042000000021030000000840c0000041108
  | 8, 0, 12 => 0x842000000021080000020442000000c910300000018420000008410300000310420000008010800000028420000008510800000420420000000210800000048420000010810800000028420000008110800000008420000000a1080000010442000000021080000002842000000411080000003842000000801080000021040c00000121080000030042000000021080000030440c00000c0103000003244200000080108
  | 8, 0, 13 => 0x32442000000c81080000001842000000c41080000042042000000801080000020442000000c81080000010042000000841080000021442000001041080000030042000000401080000032040c000000a10300000204420000000610800000420420000000a1030000021042000000c41080000030042000000c510800000018420000000a1080000020442000000c41080000030440c00000061030000030042000000c5108
  | 8, 0, 14 => 0x8420000000a1080000004842000001041080000002840c00000021080000042042000001001080000020440c000000e10800000304420000000a1080000042042000000021030000001842000000801030000004842000000c01080000032442000000061080000030442000000851080000043042000000c11030000003842000000c01080000042042000000061080000010042000000c11080000010440c00000c4108
  | 8, 0, 15 => 0x851030000001842000001041080000010440c00000401030000041042000000c11080000030442000000841080000021440c00000401030000002842000000c11080000003840c00000c01030000000842000000c51030000001840c00000c11080000041042000000c4103
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x0_0 roots_x0_0 7 s ws hint
  | 1 => checkCutEntry dom_x0_0_x1_1 roots_x0_0_x1_1 6 s ws hint
  | 2 => checkCutEntry dom_x0_0_x5_1 roots_x0_0_x5_1 6 s ws hint
  | 3 => checkCutEntry dom_x4_1 roots_x4_1 8 s ws hint
  | 4 => checkCutEntry dom_x2_0 roots_x2_0 7 s ws hint
  | 5 => checkCutEntry dom_x2_0_x3_0 roots_x2_0_x3_0 5 s ws hint
  | 6 => checkCutEntry dom_x2_0_x3_0_x4_1 roots_x2_0_x3_0_x4_1 4 s ws hint
  | 7 => checkCutEntry dom_x2_0_x3_0_x5_1 roots_x2_0_x3_0_x5_1 4 s ws hint
  | 8 => checkCutEntry dom_x5_1 roots_x5_1 9 s ws hint
  | 9 => checkCutEntry dom_x3_0 roots_x3_0 7 s ws hint
  | 10 => checkCutEntry dom_x1_1 roots_x1_1 7 s ws hint
  | 11 => checkCutEntry dom_x4_1_x5_0 roots_x4_1_x5_0 5 s ws hint
  | 12 => checkCutEntry dom_x5_0 roots_x5_0 6 s ws hint
  | 13 => checkCutEntry dom_x1_0 roots_x1_0 7 s ws hint
  | 14 => checkCutEntry dom_x2_0_x4_0 roots_x2_0_x4_0 5 s ws hint
  | 15 => checkCutEntry dom_x3_0_x4_0 roots_x3_0_x4_0 5 s ws hint
  | 16 => checkCutEntry dom_x4_0 roots_x4_0 6 s ws hint
  | 17 => checkCutEntry dom_x2_0_x4_1 roots_x2_0_x4_1 5 s ws hint
  | 18 => checkCutEntry dom_x3_0_x4_1 roots_x3_0_x4_1 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_63 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x1_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x3_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x3_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x3_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x4_1 _ hc
  · contradiction
def p0Subs : List Nat := [0, 4, 13, 9, 10, 3, 1, 5, 8, 14, 6, 16, 15, 12, 17, 18, 7, 11]
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
private theorem z5 : ∀ i, 0 ≤ i → i < 6 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 52 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 52 0 = true)
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
private theorem z7_320 : ∀ i, 320 ≤ i → i < 337 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 17 320 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 337 → Z 7 i = true := (range_split (range_split z7_0 (range_split z7_64 z7_128)) (range_split z7_192 (range_split z7_256 z7_320)))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 64 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_64 : ∀ i, 64 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 64 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_128 : ∀ i, 128 ≤ i → i < 189 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 61 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 189 → Z 8 i = true := (range_split z8_0 (range_split z8_64 z8_128))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 25 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 25 0 = true)
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

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 13]⟩], 16⟩
theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by simp [wit, PEqualNP.MetaComplexity.Monotone2]
theorem wit_size : wit.size ≤ 11 := by decide
theorem wit_eval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = ((fun x : Fin 6 → Bool => Nat.testBit (4277071592 * 2 ^ 32 + 4205357736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))) x := by decide +kernel
theorem hT6 : ∀ r : Fin 64, goal_all.testBit r.val = ((fun x : Fin 6 → Bool => Nat.testBit (4277071592 * 2 ^ 32 + 4205357736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))) (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071592 * 2 ^ 32 + 4205357736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 11 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (4277071592 * 2 ^ 32 + 4205357736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_all 11 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_41524_aux

theorem PEqualNP.Outside.L_meta_41524 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071592 * 2 ^ 32 + 4205357736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071592 * 2 ^ 32 + 4205357736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s hs
  have hlb : 11 ≤ s := PEqualNP.Outside.L_meta_41524_aux.lower s hs
  exact ⟨PEqualNP.Outside.L_meta_41524_aux.wit, PEqualNP.Outside.L_meta_41524_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_41524_aux.wit_size hlb, PEqualNP.Outside.L_meta_41524_aux.wit_eval⟩
