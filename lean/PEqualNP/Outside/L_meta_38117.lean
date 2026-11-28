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

namespace PEqualNP.Outside.L_meta_38117_aux

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

def bsr (read : Nat → Nat) (h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      (if read ((lo + hi) / 2) ≤ h then bsr read h f ((lo + hi) / 2) hi
       else bsr read h f lo ((lo + hi) / 2))
    else lo

def hw256 (seed w : Nat) : Nat :=
  let x := (((w &&& 4294967295) ^^^ seed) * 2654435761 +
            (((w >>> 32) &&& 4294967295) ^^^ seed) * 2246822519 +
            (((w >>> 64) &&& 4294967295) ^^^ seed) * 3266489917 +
            (((w >>> 96) &&& 4294967295) ^^^ seed) * 668265263 +
            (((w >>> 128) &&& 4294967295) ^^^ seed) * 374761393 +
            (((w >>> 160) &&& 4294967295) ^^^ seed) * 1274126177 +
            (((w >>> 192) &&& 4294967295) ^^^ seed) * 2869860233 +
            (((w >>> 224) &&& 4294967295) ^^^ seed) * 1640531527) &&& 4294967295
  let y := ((x ^^^ (x >>> 16)) * 2246822519) &&& 4294967295
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
         let h := hk seed cz
         !(foundH S N htAt idxH s h cz) && !(cutHitH s h cz))
      have hF (zs) (hz : RunD dm (T &&& dm) s zs) : F zs = true := by
        have hcz := hr hz
        have hcutf : cutHitH s (hk seed (ori zs)) (ori zs) = false := by
          cases h : cutHitH s (hk seed (ori zs)) (ori zs) with
          | false => rfl
          | true => exact absurd hcz (hcut h)
        simp only [F, coversP_ok hd pairs hpairs hz, scr_no pool hz, hcutf, Bool.not_false, Bool.true_and, Bool.and_true, foundH]
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
def goal_all : Nat := 0xfefefeeafeecfea8
def dom_63 : Nat := 0xffffffffffffffff
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]
def dom_x0_0_x2_1_x3_0 : Nat := 0x50005000500050
def roots_x0_0_x2_1_x3_0 : List Nat := [0x40004000400040, 0x50000000500000, 0x50005000000000]
def dom_x1_0_x3_0_x4_1 : Nat := 0x33000000330000
def roots_x1_0_x3_0_x4_1 : List Nat := [0x22000000220000, 0x30000000300000, 0x33000000000000]
def dom_x1_0_x4_1 : Nat := 0x3333000033330000
def roots_x1_0_x4_1 : List Nat := [0x2222000022220000, 0x3030000030300000, 0x3300000033000000, 0x3333000000000000]
def dom_x0_0_x3_0_x5_1 : Nat := 0x55005500000000
def roots_x0_0_x3_0_x5_1 : List Nat := [0x44004400000000, 0x50005000000000, 0x55000000000000]
def dom_x0_0_x5_1 : Nat := 0x5555555500000000
def roots_x0_0_x5_1 : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]
def dom_x1_0_x4_0_x5_0 : Nat := 0x3333
def roots_x1_0_x4_0_x5_0 : List Nat := [0x2222, 0x3030, 0x3300]
def dom_x3_0_x4_0 : Nat := 0xff000000ff
def roots_x3_0_x4_0 : List Nat := [0xaa000000aa, 0xcc000000cc, 0xf0000000f0, 0xff00000000]
def dom_x0_0_x3_0 : Nat := 0x55005500550055
def roots_x0_0_x3_0 : List Nat := [0x44004400440044, 0x50005000500050, 0x55000000550000, 0x55005500000000]
def dom_x3_0_x4_1 : Nat := 0xff000000ff0000
def roots_x3_0_x4_1 : List Nat := [0xaa000000aa0000, 0xcc000000cc0000, 0xf0000000f00000, 0xff000000000000]
def dom_x2_1_x3_0 : Nat := 0xf000f000f000f0
def roots_x2_1_x3_0 : List Nat := [0xa000a000a000a0, 0xc000c000c000c0, 0xf0000000f00000, 0xf000f000000000]
def dom_x1_0_x3_0 : Nat := 0x33003300330033
def roots_x1_0_x3_0 : List Nat := [0x22002200220022, 0x30003000300030, 0x33000000330000, 0x33003300000000]
def dom_x3_0_x5_1 : Nat := 0xff00ff00000000
def roots_x3_0_x5_1 : List Nat := [0xaa00aa00000000, 0xcc00cc00000000, 0xf000f000000000, 0xff000000000000]
def dom_x3_0 : Nat := 0xff00ff00ff00ff
def roots_x3_0 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]
def dom_x0_0_x2_1 : Nat := 0x5050505050505050
def roots_x0_0_x2_1 : List Nat := [0x4040404040404040, 0x5000500050005000, 0x5050000050500000, 0x5050505000000000]
def dom_x0_0_x4_0_x5_1 : Nat := 0x555500000000
def roots_x0_0_x4_0_x5_1 : List Nat := [0x444400000000, 0x505000000000, 0x550000000000]
def dom_x0_0_x4_0 : Nat := 0x555500005555
def roots_x0_0_x4_0 : List Nat := [0x444400004444, 0x505000005050, 0x550000005500, 0x555500000000]
def dom_x4_0_x5_0 : Nat := 0xffff
def roots_x4_0_x5_0 : List Nat := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]
def dom_x1_0_x4_0 : Nat := 0x333300003333
def roots_x1_0_x4_0 : List Nat := [0x222200002222, 0x303000003030, 0x330000003300, 0x333300000000]
def dom_x2_0_x4_0_x5_0 : Nat := 0xf0f
def roots_x2_0_x4_0_x5_0 : List Nat := [0xa0a, 0xc0c, 0xf00]
def dom_x4_0_x5_1 : Nat := 0xffff00000000
def roots_x4_0_x5_1 : List Nat := [0xaaaa00000000, 0xcccc00000000, 0xf0f000000000, 0xff0000000000]
def dom_x2_0_x4_0 : Nat := 0xf0f00000f0f
def roots_x2_0_x4_0 : List Nat := [0xa0a00000a0a, 0xc0c00000c0c, 0xf0000000f00, 0xf0f00000000]
def dom_x4_0 : Nat := 0xffff0000ffff
def roots_x4_0 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]
def dom_x0_0 : Nat := 0x5555555555555555
def roots_x0_0 : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]
def dom_x1_0 : Nat := 0x3333333333333333
def roots_x1_0 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]
def dom_x2_1 : Nat := 0xf0f0f0f0f0f0f0f0
def roots_x2_1 : List Nat := [0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000]
def dom_x2_0_x5_0 : Nat := 0xf0f0f0f
def roots_x2_0_x5_0 : List Nat := [0xa0a0a0a, 0xc0c0c0c, 0xf000f00, 0xf0f0000]
def dom_x1_0_x4_1_x5_0 : Nat := 0x33330000
def roots_x1_0_x4_1_x5_0 : List Nat := [0x22220000, 0x30300000, 0x33000000]
def dom_x4_1_x5_0 : Nat := 0xffff0000
def roots_x4_1_x5_0 : List Nat := [0xaaaa0000, 0xcccc0000, 0xf0f00000, 0xff000000]
def dom_x4_1 : Nat := 0xffff0000ffff0000
def roots_x4_1 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]
def dom_x5_1 : Nat := 0xffffffff00000000
def roots_x5_1 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]
def dom_x5_0 : Nat := 0xffffffff
def roots_x5_0 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
def dom_x2_0 : Nat := 0xf0f0f0f0f0f0f0f
def roots_x2_0 : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]

namespace S_x0_0_x2_1_x3_0
def pairsG : List (Nat × Nat) := [(6, 22), (6, 38), (20, 22), (20, 52), (36, 38), (36, 52)]
def r1sG : List Nat := [6, 6, 20, 20, 36, 36]
def r2sG : List Nat := [22, 38, 22, 52, 38, 52]
def mpG : Nat := 0x3f
def pool6G : List Nat := [22016609756694]
def xsM : List Nat := roots_x0_0_x2_1_x3_0.map (· &&& dom_x0_0_x2_1_x3_0)
def goalM : Nat := goal_all &&& dom_x0_0_x2_1_x3_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x11911f8f
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x5000500000000000500000005000000040004000400040
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x0_0_x2_1_x3_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x0_0_x2_1_x3_0 goalM u ys := by
  unfold cutHitH at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x0_0_x2_1_x3_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x0_0_x2_1_x3_0 goalM u ys) : RunD dom_x0_0_x2_1_x3_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x0_0_x2_1_x3_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x0_0_x2_1_x3_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x0_0_x2_1_x3_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x0_0_x2_1_x3_0 roots_x0_0_x2_1_x3_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x0_0_x2_1_x3_0 goal_all := by
    have h0 : isConstB dom_x0_0_x2_1_x3_0 goal_all = false := by decide +kernel
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
end S_x0_0_x2_1_x3_0
theorem low_x0_0_x2_1_x3_0 : Lower dom_x0_0_x2_1_x3_0 roots_x0_0_x2_1_x3_0 goal_all 4 := S_x0_0_x2_1_x3_0.noCircuit

namespace S_x1_0_x3_0_x4_1
def pairsG : List (Nat × Nat) := [(17, 21), (17, 49), (20, 21), (20, 52), (48, 49), (48, 52)]
def r1sG : List Nat := [17, 17, 20, 20, 48, 48]
def r2sG : List Nat := [21, 49, 21, 52, 49, 52]
def mpG : Nat := 0x3f
def pool6G : List Nat := [22064055726357]
def xsM : List Nat := roots_x1_0_x3_0_x4_1.map (· &&& dom_x1_0_x3_0_x4_1)
def goalM : Nat := goal_all &&& dom_x1_0_x3_0_x4_1
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x7f9f54c9
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x3300000000000000300000003000000022000000220000
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x1_0_x3_0_x4_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x1_0_x3_0_x4_1 goalM u ys := by
  unfold cutHitH at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x1_0_x3_0_x4_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x1_0_x3_0_x4_1 goalM u ys) : RunD dom_x1_0_x3_0_x4_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x1_0_x3_0_x4_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x1_0_x3_0_x4_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x1_0_x3_0_x4_1 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x1_0_x3_0_x4_1 roots_x1_0_x3_0_x4_1 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x1_0_x3_0_x4_1 goal_all := by
    have h0 : isConstB dom_x1_0_x3_0_x4_1 goal_all = false := by decide +kernel
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
end S_x1_0_x3_0_x4_1
theorem low_x1_0_x3_0_x4_1 : Lower dom_x1_0_x3_0_x4_1 roots_x1_0_x3_0_x4_1 goal_all 4 := S_x1_0_x3_0_x4_1.noCircuit

theorem low_x1_0_x4_1 : Lower dom_x1_0_x4_1 roots_x1_0_x4_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3300000033000000, 17, 25)] (by decide +kernel) (by decide +kernel) low_x1_0_x3_0_x4_1

namespace S_x0_0_x3_0_x5_1
def pairsG : List (Nat × Nat) := [(34, 38), (34, 50), (36, 38), (36, 52), (48, 50), (48, 52)]
def r1sG : List Nat := [34, 34, 36, 36, 48, 48]
def r2sG : List Nat := [38, 50, 38, 52, 50, 52]
def mpG : Nat := 0x3f
def pool6G : List Nat := [39729256215078]
def xsM : List Nat := roots_x0_0_x3_0_x5_1.map (· &&& dom_x0_0_x3_0_x5_1)
def goalM : Nat := goal_all &&& dom_x0_0_x3_0_x5_1
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xa1f74a59
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x5500000000000000500050000000000044004400000000
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x0_0_x3_0_x5_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x0_0_x3_0_x5_1 goalM u ys := by
  unfold cutHitH at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x0_0_x3_0_x5_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x0_0_x3_0_x5_1 goalM u ys) : RunD dom_x0_0_x3_0_x5_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x0_0_x3_0_x5_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x0_0_x3_0_x5_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x0_0_x3_0_x5_1 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x0_0_x3_0_x5_1 roots_x0_0_x3_0_x5_1 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x0_0_x3_0_x5_1 goal_all := by
    have h0 : isConstB dom_x0_0_x3_0_x5_1 goal_all = false := by decide +kernel
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
end S_x0_0_x3_0_x5_1
theorem low_x0_0_x3_0_x5_1 : Lower dom_x0_0_x3_0_x5_1 roots_x0_0_x3_0_x5_1 goal_all 4 := S_x0_0_x3_0_x5_1.noCircuit

theorem low_x0_0_x5_1 : Lower dom_x0_0_x5_1 roots_x0_0_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5500550000000000, 34, 42)] (by decide +kernel) (by decide +kernel) low_x0_0_x3_0_x5_1

namespace S_x1_0_x4_0_x5_0
def pairsG : List (Nat × Nat) := [(1, 5), (1, 9), (4, 5), (4, 12), (8, 9), (8, 12)]
def r1sG : List Nat := [1, 1, 4, 4, 8, 8]
def r2sG : List Nat := [5, 9, 5, 12, 9, 12]
def mpG : Nat := 0x3f
def pool6G : List Nat := [4402476484869]
def xsM : List Nat := roots_x1_0_x4_0_x5_0.map (· &&& dom_x1_0_x4_0_x5_0)
def goalM : Nat := goal_all &&& dom_x1_0_x4_0_x5_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xb9ef265f
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x330000000000000030300000000000002222
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x1_0_x4_0_x5_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x1_0_x4_0_x5_0 goalM u ys := by
  unfold cutHitH at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x1_0_x4_0_x5_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x1_0_x4_0_x5_0 goalM u ys) : RunD dom_x1_0_x4_0_x5_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x1_0_x4_0_x5_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x1_0_x4_0_x5_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x1_0_x4_0_x5_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x1_0_x4_0_x5_0 roots_x1_0_x4_0_x5_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x1_0_x4_0_x5_0 goal_all := by
    have h0 : isConstB dom_x1_0_x4_0_x5_0 goal_all = false := by decide +kernel
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
end S_x1_0_x4_0_x5_0
theorem low_x1_0_x4_0_x5_0 : Lower dom_x1_0_x4_0_x5_0 roots_x1_0_x4_0_x5_0 goal_all 4 := S_x1_0_x4_0_x5_0.noCircuit

namespace S_x3_0_x4_0
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 33), (2, 3), (4, 5), (6, 7), (6, 38), (32, 33), (34, 35), (34, 38), (36, 37), (36, 38)]
def r1sG : List Nat := [1, 1, 1, 2, 4, 6, 6, 32, 34, 34, 36, 36]
def r2sG : List Nat := [3, 5, 33, 3, 5, 7, 38, 33, 35, 38, 37, 38]
def mpG : Nat := 0xfff
def pool6G : List Nat := [6601937658117, 6601971205379, 37387793466145, 37388296783107]
def xsM : List Nat := roots_x3_0_x4_0.map (· &&& dom_x3_0_x4_0)
def goalM : Nat := goal_all &&& dom_x3_0_x4_0
def NN : Nat → Nat
  | 4 => 5
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xb6f5a4a5a71197399b5b931976e5fe7b3e9727f5
  | 5, 0, 0 => 0x76e5fe7b
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xff0000000f0000000f00000033000000330000005500000055000000ff00000000000000f0000000f0000000cc000000cc000000aa000000aa
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x6464685468c468844474
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x3_0_x4_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x3_0_x4_0 goalM u ys := by
  unfold cutHitH at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x3_0_x4_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x3_0_x4_0 goalM u ys) : RunD dom_x3_0_x4_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x3_0_x4_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x3_0_x4_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 3 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_x3_0_x4_0 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x3_0_x4_0 roots_x3_0_x4_0 goal_all 6 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x3_0_x4_0 goal_all := by
    have h0 : isConstB dom_x3_0_x4_0 goal_all = false := by decide +kernel
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
end S_x3_0_x4_0
theorem low_x3_0_x4_0 : Lower dom_x3_0_x4_0 roots_x3_0_x4_0 goal_all 6 := S_x3_0_x4_0.noCircuit

theorem low_x0_0_x3_0 : Lower dom_x0_0_x3_0 roots_x0_0_x3_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x50005000500050, 34, 38)] (by decide +kernel) (by decide +kernel) low_x0_0_x2_1_x3_0

theorem low_x3_0_x4_1 : Lower dom_x3_0_x4_1 roots_x3_0_x4_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc000000cc0000, 16, 18)] (by decide +kernel) (by decide +kernel) low_x1_0_x3_0_x4_1

theorem low_x2_1_x3_0 : Lower dom_x2_1_x3_0 roots_x2_1_x3_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa000a000a000a0, 4, 5)] (by decide +kernel) (by decide +kernel) low_x0_0_x2_1_x3_0

theorem low_x1_0_x3_0 : Lower dom_x1_0_x3_0 roots_x1_0_x3_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x33000000330000, 36, 52)] (by decide +kernel) (by decide +kernel) low_x1_0_x3_0_x4_1

theorem low_x3_0_x5_1 : Lower dom_x3_0_x5_1 roots_x3_0_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaa00aa00000000, 32, 33)] (by decide +kernel) (by decide +kernel) low_x0_0_x3_0_x5_1

namespace S_x3_0
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 33), (2, 3), (2, 18), (4, 5), (6, 7), (6, 22), (6, 38), (16, 18), (17, 19), (17, 21), (17, 49), (20, 21), (20, 22), (20, 52), (32, 33), (34, 35), (34, 38), (34, 50), (36, 37), (36, 38), (36, 52), (48, 49), (48, 50), (48, 52)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 4, 6, 6, 6, 16, 17, 17, 17, 20, 20, 20, 32, 34, 34, 34, 36, 36, 36, 48, 48, 48]
def r2sG : List Nat := [3, 5, 33, 3, 18, 5, 7, 22, 38, 18, 19, 21, 49, 21, 22, 52, 33, 35, 38, 50, 37, 38, 52, 49, 50, 52]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [22016609756690, 22064055722245, 52931749876276, 18717804201219, 37456512942881, 39728733029158, 52802935334418, 39608527360550, 37457217262083, 39668421104180, 52849911530785, 18718073947395, 37409452524838, 18718040400133, 39608475779878, 18718073954578, 39668421104133]
def xsM : List Nat := roots_x3_0.map (· &&& dom_x3_0)
def goalM : Nat := goal_all &&& dom_x3_0
def NN : Nat → Nat
  | 4 => 2
  | 5 => 59
  | 6 => 138
  | 7 => 27
  | 8 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x817f4853312c96e1
  | 5, 0, 0 => 0xfec9ef8afbc0e648fba6b2a3fabfc7acfa7f1917f75bdc30ed2df496ea623ca5ea5eaf99e9e6352ee8ff4a37e7d28a32e79e3ee7e6e89c7ce59b5ebbe5812b16e30ca29ee1626cf8d8a1bf30d5142777d3737451d14c2529cfa1ef83cc1ea279c57b7c1dc4bd00cdc1a046dbbbc0772cba5e2504b3b3cfdfaf5dab68a9fff9b7a9e08f78a542467ea26262059367956492dccc168f1cbef18e91f5a37d50f12268111a2b577036a251b693c44ca06d5d49841e57485596ea444f9c06424c02d74011f2943ff6164f2fc3c668294c3ae022b257692149f2241222951610f1d9f410d7a64f10a4a0a40c8ccfdc
  | 6, 0, 0 => 0x72908bda6ed249926d263ee76cf22bba6be2a74c6b56a6106a62794769788b9168111a2b67e3cb7067c3e0db66643a24659c91b363f25c0d63cc237f63069edd5996289b57adc6a056baafed568436f9566a035456438df5551d18f753a251f44f3d47dc4eae918e479e5ac544a985df416dcc4a40c6c3393f1df3553e5066413d7cca673d22f5d73afeb71c39f23b44355327d831d366d82d0dfcc727b801ee25cd91e9236d2b7b22afdb282182bb76216887d1183709d6180b7bd41617511113d1ffbe13a671bc11927a61114541111107b1130fe011240fa80a5c0f5ad10c0934404a04e4426f03de457102faf5b50211824901e5f4470176ab7100804d26
  | 6, 0, 1 => 0xed6b8494e55b1352df866f60de650322dd1e0fa6dc6253a6d891550bd887ca38d69c6f61d44682d9d3461684d32be2dfd2764d4dcf2e7da5cacb525aca141635c7af0354c635aae5c5095a34c1ead472c16b656abde63789bc45387bafbb20acab07f9e6aa84bb06a82ef62ba6bd2373a542467ea52812d9a3f876e6a3e41fb8a0dd3c669e3895129adf2fac93679564931a5c148f79c49e8f1cbef18f028b4c8ecf85a18cef5f28871c65e684d010b882112b2682092a6e8202ddc98118f0138092c707801eba697fb17ead7e36a1b87dc654b37d4fb6c17cf4d4877cd87af27cb2619479ebcb4579d197a07824b79974e14ff774c71c52737c8a9572c2b7ec
  | 6, 0, 2 => 0xff936efeff793b59ff3c613efc6186b5fc39995ffbafedf1fb295814fa7716b0fa5cabccedb8bde4
  | 7, 0, 0 => 0xfc6186b5fab4a6aef7570b67ede69525d8f9f269d1cd36f1bf98b147bef1a836a5e2e6eba3f876e69661eed3963660d182092a6e6e21827567d0cec255bbd1f444608fe23ed527902932dee327b801ee2659db28236d2b7b2352f7d611927a61114541110322b61c003c1023
  | 8, 0, 0 => 0xa5e2e6eb
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x1100110011001100ff00aa00ff00aa0000005500000055000000ff000000ff00550000005500000000000000ff00ff000f000f000f000f0055005500550055003300330033003300cc00cc00cc00cc00aa00aa00aa00aa000f000f00f000f000ff00ff0000000000ff000000ff000000f000f000f000f00099009900990099
  | 1 => 0xff00ff00aa00aa00aa00aa0000000000ff00aa0000000000f000a000f000a000ff00ff00a000a000ec00ec00ec00ec00130013001300130005000500ff00ff00fe00fe00cc00cc00fa00fa0000000000fa00fa00fa00fa00a000a000a000a000fa00fa00aa00aa00f000f00000000000ee00ee00ee00ee0088008800880088
  | 2 => 0xe000e000e000e000ff00cc00ff00cc0044004400440044000f000f00ff00ff00fc00fc00cc00cc00cc00cc0000000000ff00ff00cc00cc00fc00fc00fc00fc00c000c000c000c000ff00ff00f000f000fa00fa00f000f000ee00ee00cc00cc0011001100330033000f000f005f005f00fc00fc00ec00ec00f000f000a000a0
  | 3 => 0xcf00cf00cf00cf00ee00ee00aa00aa00f000f000c000c000ff00cc0000000000f000c000f000c000ea00ea00ea00ea00fc00fc0000000000330033000000000030003000300030002200220022002200ff00aa00ff000000ff00a000ff00a000ff00ff0088008800ff008800ff008800f800f800f800f800ee00ee00000000
  | 4 => 0xff000000ff00ff00f000f000ff00ff00cc00cc00ff00ff00f000f000f0000000ff00f000ff00f000ff00f00000000000ff00ff00ff000000ff00ff000f000f00ff000f00ff000f
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x418284406080804
  | 5, 0, 0 => 0x989060a3140022c04287506381130219802904a8289500981120a1d400304182a250008305122940031c0430f500080850e29400e024430a5000c1050e2540031c4430951c740920c1580030404407506089812219801b021828c500043051a294002509c28a5000c3051235418242803056000c088161d548250483056006c1010a1d402604182ac5000c1010a6540060a2460a5000c0861035400304042a350008287122940010a1c60a50038305122940030a1c48c5
  | 5, 0, 1 => 0xe021438a50008308122940010c2060a5000d2860a3140031c143895000c3081231418e02488866000ca86283141172c04305600080880e29400304942875000c0a40a314003040480f5000c09a0a31400304203895000c0880e314003401828c5007c0863c3140030454a075063891c0c1580031c044075000c1200a1d401f0404f07500580860a31530256483056000c7130219400202182985
  | 6, 0, 0 => 0xc12802143b0006b81060a25800304a09060ac0208304182896000c1010c147b0000a41015415400304ac0860ac00002021828a500080910c145300000c1060a2540030405f060ac0018222182896000c0910c1463000404305122980022a0430514c001ae04043086000c0860a24630006540860a31800006080850ea000031c043055000018e0244328006080c50c15800304048850ec0018e02443056060958124182ba906094010c15c002024830514c0018203183056000c1010a1c4b000608a810a1d800304043056ec0018202703056
  | 6, 0, 1 => 0xc10174182b004c0c1010a1d800304042876ec0000304543145000c70138182b0006043052831800006080a40aa000030404d055000018202203a80000d9010c154000063808610a0018202144076000018240182a80007c1010c7940033a080860ac00f8304042876000c1010a503b0006089810c1580031c0808610c014830418289600a41810c146300000c1012241400304042876cc00128021828a6000d4010c1463000008b010c15400304fc30512c014830404287600b81010c14530088080860a29800386080860ac0002604483055
  | 6, 0, 2 => 0x1860a24628006080bb0c158003040432a10c00002021438a500007010c14528006080860ae18000060828712a00003021438c5000018e0c144a800609c810c15802904049060ac001018c1828a600381010c14530006080920c15800304052060ac001820268305600981810c14630304049110c15c00304043080ec00002021840a5000c7020c144b00000c1250c15400006380850ea0018202193886000c11602182b00000c10610254000060430818a001810c1440c6007c1820c144b003e0c0860a318003040430558c00147021828a6
  | 6, 0, 3 => 0xc70124182b00840c1060a25800006d40860aa0000304c43055000c1010c216b031c080920c15c00304050060ac001820248308600001810c205a80006c1010c154003041828914c001810c1460a6000198202182a800638e810c15800006043051aa0018202fc30560000182509c2a80040432a0a298003800830512c001820ca82896000c1010a1c530090080860a298003021829e18c0018202c0305600080860a1c530006080853c1d8002021938514c001820c14389600001060a24528000043051829400304048860ac001820c9c2896
  | 6, 0, 4 => 0x3044830512c00181241828c6000c1015e182b00000c1010c21400378080860ac0000368043055000c1010a1dc30006080910c2180030405e860ac0018202482876
  | 7, 0, 0 => 0x30404308506080860a218f830404305606080860a5194830404305606094010c1581ae0404305607101010c1580030404305506080910c158182021828960608a810c1581820248305606080860a41a1030404305606080860a2981820219505606080860a7981820218287600080860a29418202193856000c1060a254003021828c5000c1010a1d40031c0430554c0c1010c15818e04043056
  | 8, 0, 0 => 0x304043055
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 32
  | 5 => 46
  | 6 => 53
  | 7 => 46
  | 8 => 39
  | _ => 0
def stateM : Nat → Nat
  | 4 => 0xffffffff
  | 5 => 0x3fffffffffff
  | 6 => 0x1fffffffffffff
  | 7 => 0x3fffffffffff
  | 8 => 0x7fffffffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x3f1e220000000000380fe0700000000007f01f800000000007f01ff000000000380e200000000000000ffff00000000038f1e1f0000000003ffe3f80000000003f1fe2700000000000e01d80000000000001c0700000000038fe1e00000000003ff0000000000000380fe00000000000070e1e00000000003f1e220
  | 1 => 0x3ff1c0700000000000000000000000003800000000000000000e0000000000003ff000000000000000e01d80000000003f1fe2700000000038fffff00000000007e01d80000000000700000000000000070fde700000000000000000000000000701c07000000000070000000000000000e1ddf0000000000000000
  | 2 => 0x1c000000000038effd800000000000e01d800000000038fffff00000000007e01d800000000000e00000000000003ff01d800000000007ee1f800000000000001c00000000003ffe1e0000000000070e1e000000000000e01d80000000003f1fe2700000000038fffff00000000007e01d80000000000700000
  | 3 => 0x38f1fdf00000000000e1c0700000000007001c000000000038e0000000000000000e1c00000000000001dc700000000007e00000000000003f10000000000000070e0200000000000001c07000000000380fe00000000000380fe000000000003ff0000000000000380fe00000000000070e1e000000000000e0000
  | 4 => 0x380ffff000000000070ffff00000000000effff000000000070e0000000000003f0ffe00000000003f000000000000003fffe000000000003ff1e1f00000000038ffe1f
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x24080000000000003dbfeff0000000000240100000000000037016f000000000348c2900000000000006efb00000000018b161d00000000036cc3900000000002d1b82600000000012e47d90000000000933c6f00000000018b78e60000000003ff91040000000003c8fe90000000000274e9e20000000002428449
  | 1 => 0x3ffbd6f00000000009310040000000003db9004000000000250e8e20000000003ffb96600000000013e6ffb0000000002c190040000000001086efb0000000003ffd7dd0000000002f791040000000002f7fdef00000000001028620000000002f7bd6f00000000027481000000000001bf7fff0000000000020449
  | 2 => 0x3469e20000000003eeffd900000000012c439000000000018b7eff00000000037ec7d900000000012e01000000000003ffd7dd00000000037eeffb00000000002441c00000000003fff9e60000000002f7f9e60000000001bf57dd000000000240a82200000000018b569d00000000037eeffb000000000274a962
  | 3 => 0x1af57dd0000000001bf3d6f000000000274c1c00000000003ee9100000000000264e9c00000000000b77def00000000037e81000000000002d19004000000000250a82200000000009138260000000003dbfe940000000003d8fef20000000003ff954d0000000003cafed9000000000276edeb0000000001bf1104
  | 4 => 0x3c8fefb000000000274effb00000000012e6ffb000000000274e9800000000003fcfff20000000003fc91000000000003ffff940000000003ff971d0000000003cbfe9d
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 73 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 73 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 73 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 73 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 73 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x7f) :: stateWiresD n (ids >>> 7)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x7f) :: stateWiresS n (ids >>> 7)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 9 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 5 => 31
  | 6 => 24
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xfdb93c9ffc6186b5f96e662cebcd630de91e897bdcab91a3d69c6f61d08b0252a5697d20a52812d9a11ea6ada0dd3c669a065f108f43f5938f028b4c864426f983e0d78381f950867a1301e779d197a05aedabc0506b58e149a574a348a8bb04418c2a6839207ca536ce09ea27b801ee23bd7c70236d2b7b11927a61
  | 6, 0, 0 => 0xdbfaeb30c5933e73941ee1eb90aa02728fd40b788c5f2bff8a68fb87861e25147df95a5e7a847ae5744373fa732590316edab9be68c866b2655387395f12804e5d0008a45246f92347cf14f83c031f5737b848e426f831bc25dd97ca10aca41e
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xe10100000008404000000a10100000018404000000a1010000002840400000021010000031040c000000e10100000038404000000a10100000028404000000e1010000001840400000061010000003840400000061010000002840400000021010000000840400000021010000031040c000000e10100000028404000000e1010000000840400000061010000003840400000c4103000000284040000006101
  | 6, 0, 0 => 0x18404000000210100000038404000000e10100000028404000000a10100000038404000000a10100000018404000000610100000018404000000e10100000028404000000210100000008404000000210100000018404000000e10100000008404000000e10100000028404000000a101000000184040000002101
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 6 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x0_0_x2_1_x3_0 roots_x0_0_x2_1_x3_0 4 s ws hint
  | 1 => checkCutEntry dom_x3_0_x4_0 roots_x3_0_x4_0 6 s ws hint
  | 2 => checkCutEntry dom_x0_0_x3_0_x5_1 roots_x0_0_x3_0_x5_1 4 s ws hint
  | 3 => checkCutEntry dom_x0_0_x3_0 roots_x0_0_x3_0 5 s ws hint
  | 4 => checkCutEntry dom_x1_0_x3_0_x4_1 roots_x1_0_x3_0_x4_1 4 s ws hint
  | 5 => checkCutEntry dom_x3_0_x4_1 roots_x3_0_x4_1 5 s ws hint
  | 6 => checkCutEntry dom_x2_1_x3_0 roots_x2_1_x3_0 5 s ws hint
  | 7 => checkCutEntry dom_x1_0_x3_0 roots_x1_0_x3_0 5 s ws hint
  | 8 => checkCutEntry dom_x3_0_x5_1 roots_x3_0_x5_1 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x3_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x2_1_x3_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x3_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x3_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x3_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_1_x3_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x3_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x5_1 _ hc
  · contradiction
def p0Subs : List Nat := [3, 1, 6, 0, 7, 8, 2, 5, 4]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x3_0 goalM u ys := by
  unfold cutHitH at h; rw [Bool.or_eq_true] at h; rcases h with h1 | h0
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
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 59 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 59 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 64 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 64 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_64 : ∀ i, 64 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 64 64 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_128 : ∀ i, 128 ≤ i → i < 138 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 10 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 138 → Z 6 i = true := (range_split z6_0 (range_split z6_64 z6_128))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 27 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 27 0 = true)
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
def RootG (s : Nat) : Bool := scr dom_x3_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD dom_x3_0 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x3_0 roots_x3_0 goal_all 9 := by
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
theorem low_x3_0 : Lower dom_x3_0 roots_x3_0 goal_all 9 := S_x3_0.noCircuit

theorem low_x0_0_x2_1 : Lower dom_x0_0_x2_1 roots_x0_0_x2_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5000500050005000, 4, 12)] (by decide +kernel) (by decide +kernel) low_x0_0_x2_1_x3_0

namespace S_x0_0_x4_0_x5_1
def pairsG : List (Nat × Nat) := [(34, 38), (34, 42), (36, 38), (36, 44), (40, 42), (40, 44)]
def r1sG : List Nat := [34, 34, 36, 36, 40, 40]
def r2sG : List Nat := [38, 42, 38, 44, 42, 44]
def mpG : Nat := 0x3f
def pool6G : List Nat := [39729121471014]
def xsM : List Nat := roots_x0_0_x4_0_x5_1.map (· &&& dom_x0_0_x4_0_x5_1)
def goalM : Nat := goal_all &&& dom_x0_0_x4_0_x5_1
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x66820991
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x55000000000000005050000000000000444400000000
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x0_0_x4_0_x5_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x0_0_x4_0_x5_1 goalM u ys := by
  unfold cutHitH at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x0_0_x4_0_x5_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x0_0_x4_0_x5_1 goalM u ys) : RunD dom_x0_0_x4_0_x5_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x0_0_x4_0_x5_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x0_0_x4_0_x5_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x0_0_x4_0_x5_1 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x0_0_x4_0_x5_1 roots_x0_0_x4_0_x5_1 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x0_0_x4_0_x5_1 goal_all := by
    have h0 : isConstB dom_x0_0_x4_0_x5_1 goal_all = false := by decide +kernel
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
end S_x0_0_x4_0_x5_1
theorem low_x0_0_x4_0_x5_1 : Lower dom_x0_0_x4_0_x5_1 roots_x0_0_x4_0_x5_1 goal_all 4 := S_x0_0_x4_0_x5_1.noCircuit

theorem low_x0_0_x4_0 : Lower dom_x0_0_x4_0 roots_x0_0_x4_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x555500000000, 6, 38)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_0_x5_1

theorem low_x4_0_x5_0 : Lower dom_x4_0_x5_0 roots_x4_0_x5_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccc, 1, 3)] (by decide +kernel) (by decide +kernel) low_x1_0_x4_0_x5_0

theorem low_x1_0_x4_0 : Lower dom_x1_0_x4_0 roots_x1_0_x4_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x333300000000, 1, 33)] (by decide +kernel) (by decide +kernel) low_x1_0_x4_0_x5_0

namespace S_x2_0_x4_0_x5_0
def pairsG : List (Nat × Nat) := [(1, 3), (1, 9), (2, 3), (2, 10), (8, 9), (8, 10)]
def r1sG : List Nat := [1, 1, 2, 2, 8, 8]
def r2sG : List Nat := [3, 9, 3, 10, 9, 10]
def mpG : Nat := 0x3f
def pool6G : List Nat := [2203453098243]
def xsM : List Nat := roots_x2_0_x4_0_x5_0.map (· &&& dom_x2_0_x4_0_x5_0)
def goalM : Nat := goal_all &&& dom_x2_0_x4_0_x5_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x183c7911
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xf000000000000000c0c0000000000000a0a
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x2_0_x4_0_x5_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x2_0_x4_0_x5_0 goalM u ys := by
  unfold cutHitH at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x2_0_x4_0_x5_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x2_0_x4_0_x5_0 goalM u ys) : RunD dom_x2_0_x4_0_x5_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x2_0_x4_0_x5_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x2_0_x4_0_x5_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x2_0_x4_0_x5_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x2_0_x4_0_x5_0 roots_x2_0_x4_0_x5_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x2_0_x4_0_x5_0 goal_all := by
    have h0 : isConstB dom_x2_0_x4_0_x5_0 goal_all = false := by decide +kernel
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
end S_x2_0_x4_0_x5_0
theorem low_x2_0_x4_0_x5_0 : Lower dom_x2_0_x4_0_x5_0 roots_x2_0_x4_0_x5_0 goal_all 4 := S_x2_0_x4_0_x5_0.noCircuit

theorem low_x4_0_x5_1 : Lower dom_x4_0_x5_1 roots_x4_0_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa00000000, 32, 33)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_0_x5_1

theorem low_x2_0_x4_0 : Lower dom_x2_0_x4_0 roots_x2_0_x4_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f00000000, 1, 33)] (by decide +kernel) (by decide +kernel) low_x2_0_x4_0_x5_0

namespace S_x4_0
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (1, 33), (2, 3), (2, 10), (4, 5), (4, 12), (6, 7), (6, 14), (6, 38), (8, 9), (8, 10), (8, 12), (32, 33), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (36, 44), (40, 41), (40, 42), (40, 44)]
def r1sG : List Nat := [1, 1, 1, 1, 2, 2, 4, 4, 6, 6, 6, 8, 8, 8, 32, 34, 34, 34, 36, 36, 36, 40, 40, 40]
def r2sG : List Nat := [3, 5, 9, 33, 3, 10, 5, 12, 7, 14, 38, 9, 10, 12, 33, 35, 38, 42, 37, 38, 44, 41, 42, 44]
def mpG : Nat := 0xffffff
def pool6G : List Nat := [39586816721697, 6601937658117, 43985332668937, 6601971205379, 37387793466145]
def xsM : List Nat := roots_x4_0.map (· &&& dom_x4_0)
def goalM : Nat := goal_all &&& dom_x4_0
def NN : Nat → Nat
  | 5 => 3
  | 6 => 7
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x98fa57c14617139e0f49110e
  | 6, 0, 0 => 0xd975ad84cec1e1d5cb56f506983672418151f4be7bde9db2058fe465
  | 7, 0, 0 => 0x3b576e79
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xffff0000fcfc0000fcfc0000fafa0000fafa0000eeee0000eeee0000aaaa0000aaaa0000cccc0000cccc00000f0f00000f0f0000ffff000000000000ff000000ff000000f0f00000f0f000005555000055550000333300003333
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x436155432105437055
  | 6, 0, 0 => 0x3267b5043675543a26764392676432867604327050432615
  | 7, 0, 0 => 0x432675
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
  | 0 => 0x3fff00000000001f87f000000000001c07cf000000000003873f000000000000000f00000000000387300000000000e3f83f0000000000ffc0000000000000e0380000000000001c07c00000000000fffff00000000000fc78cf
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x3bf70000000000dfb7f30000000000bdefdf00000000006fdf7f000000000024c95f00000000004b9731000000000062d83d0000000000ffc4080000000000f23aa400000000009d27c20000000000db36a00000000000b468ce
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
  | 5, 0, 0 => 0xd6ef288bcd9ab2e1a835d8cb840be4687c1ba1ea7167d63b1e8492180dbd2b1b
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x28400000000e10000000008400000000610000000038400000000a100000000184000000002100
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 4 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x3_0_x4_0 roots_x3_0_x4_0 6 s ws hint
  | 1 => checkCutEntry dom_x0_0_x4_0_x5_1 roots_x0_0_x4_0_x5_1 4 s ws hint
  | 2 => checkCutEntry dom_x0_0_x4_0 roots_x0_0_x4_0 5 s ws hint
  | 3 => checkCutEntry dom_x4_0_x5_0 roots_x4_0_x5_0 5 s ws hint
  | 4 => checkCutEntry dom_x1_0_x4_0_x5_0 roots_x1_0_x4_0_x5_0 4 s ws hint
  | 5 => checkCutEntry dom_x1_0_x4_0 roots_x1_0_x4_0 5 s ws hint
  | 6 => checkCutEntry dom_x2_0_x4_0_x5_0 roots_x2_0_x4_0_x5_0 4 s ws hint
  | 7 => checkCutEntry dom_x4_0_x5_1 roots_x4_0_x5_1 5 s ws hint
  | 8 => checkCutEntry dom_x2_0_x4_0 roots_x2_0_x4_0 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x4_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x4_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x4_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x4_0 _ hc
  · contradiction
def p0Subs : List Nat := [0, 2, 5, 3, 7, 8, 1, 4, 6]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x4_0 goalM u ys := by
  unfold cutHitH at h; rw [Bool.or_eq_true] at h; rcases h with h1 | h0
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
def RootG (s : Nat) : Bool := scr dom_x4_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_x4_0 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x4_0 roots_x4_0 goal_all 8 := by
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
theorem low_x4_0 : Lower dom_x4_0 roots_x4_0 goal_all 8 := S_x4_0.noCircuit

namespace S_x0_0
def pairsG : List (Nat × Nat) := [(2, 10), (2, 18), (4, 12), (6, 14), (6, 22), (6, 38), (8, 10), (8, 12), (16, 18), (20, 22), (20, 28), (20, 52), (24, 26), (24, 28), (34, 38), (34, 42), (34, 50), (36, 38), (36, 44), (36, 52), (40, 42), (40, 44), (48, 50), (48, 52), (56, 58), (56, 60)]
def r1sG : List Nat := [2, 2, 4, 6, 6, 6, 8, 8, 16, 20, 20, 20, 24, 24, 34, 34, 34, 36, 36, 36, 40, 40, 48, 48, 56, 56]
def r2sG : List Nat := [10, 18, 12, 14, 22, 38, 10, 12, 18, 22, 28, 52, 26, 28, 38, 42, 50, 38, 44, 52, 42, 44, 50, 52, 58, 60]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [61598757686282, 22016609756690, 61598993877516, 39729387801126]
def xsM : List Nat := roots_x0_0.map (· &&& dom_x0_0)
def goalM : Nat := goal_all &&& dom_x0_0
def NN : Nat → Nat
  | 5 => 1
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x9e7b792b
  | 6, 0, 0 => 0xc99170a
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x444444444444444455555555000000005555000055550000550055005500550050505050505050501111111111111111
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x46885
  | 6, 0, 0 => 0x468d5
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
  | 0 => 0x1c03b0000000003ffc0000000000003c03f0000000000033030c000000000000e0e3c0000000003fe3fc4
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x153d37b0000000003ffc8200000000003c93f12000000000334b4cd0000000002ae6ebc0000000002ac2c84
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
  | 0 => checkCutEntry dom_x0_0_x2_1 roots_x0_0_x2_1 5 s ws hint
  | 1 => checkCutEntry dom_x0_0_x3_0 roots_x0_0_x3_0 5 s ws hint
  | 2 => checkCutEntry dom_x0_0_x4_0 roots_x0_0_x4_0 5 s ws hint
  | 3 => checkCutEntry dom_x0_0_x5_1 roots_x0_0_x5_1 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x0_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x2_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x3_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x5_1 _ hc
  · contradiction
def p0Subs : List Nat := [0, 1, 2, 3]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x0_0 goalM u ys := by
  unfold cutHitH at h; rw [Bool.or_eq_true] at h; rcases h with h1 | h0
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
def RootG (s : Nat) : Bool := scr dom_x0_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_x0_0 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x0_0 roots_x0_0 goal_all 7 := by
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
theorem low_x0_0 : Lower dom_x0_0 roots_x0_0 goal_all 7 := S_x0_0.noCircuit

namespace S_x1_0
def pairsG : List (Nat × Nat) := [(1, 5), (1, 9), (1, 33), (4, 5), (4, 12), (8, 9), (8, 12), (17, 21), (17, 25), (17, 49), (20, 21), (20, 28), (20, 52), (24, 25), (24, 28), (32, 33), (36, 37), (36, 44), (36, 52), (40, 41), (40, 44), (48, 49), (48, 52), (56, 57), (56, 60)]
def r1sG : List Nat := [1, 1, 1, 4, 4, 8, 8, 17, 17, 17, 20, 20, 20, 24, 24, 32, 36, 36, 36, 40, 40, 48, 48, 56, 56]
def r2sG : List Nat := [5, 9, 33, 5, 12, 9, 12, 21, 25, 49, 21, 28, 52, 25, 28, 33, 37, 44, 52, 41, 44, 49, 52, 57, 60]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [22064187312389, 39655771997473, 61646271745033, 61658837878068]
def xsM : List Nat := roots_x1_0.map (· &&& dom_x1_0)
def goalM : Nat := goal_all &&& dom_x1_0
def NN : Nat → Nat
  | 5 => 2
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xe3c1d732e335c3d3
  | 6, 0, 0 => 0x653667d8
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x2222222222222222030303030303030333333333000000003333000033330000330033003300330030303030303030301111111111111111
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
  | 0 => 0x3870000000001f8e3e70000000001ff80000000000001e07f8000000000019860600000000000071c180000000001fffc78
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0xa9a7af0000000000a8a3260000000001ff92040000000001e47f8000000000019a69720000000001575cd90000000001565850
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
  | 0 => checkCutEntry dom_x1_0_x3_0 roots_x1_0_x3_0 5 s ws hint
  | 1 => checkCutEntry dom_x1_0_x4_1 roots_x1_0_x4_1 5 s ws hint
  | 2 => checkCutEntry dom_x1_0_x4_0 roots_x1_0_x4_0 5 s ws hint
  | 3 => checkCutEntry dom_x1_0_x4_0_x5_0 roots_x1_0_x4_0_x5_0 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x1_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x3_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x4_0_x5_0 _ hc
  · contradiction
def p0Subs : List Nat := [0, 2, 1, 3]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x1_0 goalM u ys := by
  unfold cutHitH at h; rw [Bool.or_eq_true] at h; rcases h with h1 | h0
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

theorem low_x2_1 : Lower dom_x2_1 roots_x2_1 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa0a0a0a0a0a0a0a0, 4, 5)] (by decide +kernel) (by decide +kernel) low_x0_0_x2_1

theorem low_x2_0_x5_0 : Lower dom_x2_0_x5_0 roots_x2_0_x5_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f0000, 2, 18)] (by decide +kernel) (by decide +kernel) low_x2_0_x4_0_x5_0

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
  let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x1_0_x4_1_x5_0 goalM u ys := by
  unfold cutHitH at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
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

theorem low_x4_1_x5_0 : Lower dom_x4_1_x5_0 roots_x4_1_x5_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccc0000, 16, 18)] (by decide +kernel) (by decide +kernel) low_x1_0_x4_1_x5_0

theorem low_x4_1 : Lower dom_x4_1 roots_x4_1 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccc0000cccc0000, 16, 18)] (by decide +kernel) (by decide +kernel) low_x1_0_x4_1

theorem low_x5_1 : Lower dom_x5_1 roots_x5_1 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaaaaaa00000000, 32, 33)] (by decide +kernel) (by decide +kernel) low_x0_0_x5_1

namespace S_x5_0
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (2, 3), (2, 10), (2, 18), (4, 5), (4, 12), (6, 7), (6, 14), (6, 22), (8, 9), (8, 10), (8, 12), (16, 18), (17, 19), (17, 21), (17, 25), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 2, 4, 4, 6, 6, 6, 8, 8, 8, 16, 17, 17, 17, 20, 20, 20, 24, 24, 24]
def r2sG : List Nat := [3, 5, 9, 3, 10, 18, 5, 12, 7, 14, 22, 9, 10, 12, 18, 19, 21, 25, 21, 22, 28, 25, 26, 28]
def mpG : Nat := 0xffffff
def pool6G : List Nat := [22063650441477, 18717804201219, 26461394830089, 26414334674188]
def xsM : List Nat := roots_x5_0.map (· &&& dom_x5_0)
def goalM : Nat := goal_all &&& dom_x5_0
def NN : Nat → Nat
  | 5 => 3
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xea902df214e17f6b09e2bbbd
  | 6, 0, 0 => 0x1f16380d
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xff00ff00000000ffaaffaa00000000aaaaaaaa00000000ffff000000000000ff00ff0000000000f0f0f0f000000000cccccccc0000000055555555
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x446f511a216668d6
  | 6, 0, 0 => 0x468d5
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
  | 0 => 0x1fc7ff0000000000e3b80700000000000380070000000000ffc0000000000000e0380000000000001c07c000000000000007380000000000fc7ff8
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0xdc56b0000000000f7bbdf000000000027894f0000000000ffc4200000000000f23a9400000000009d27c2000000000048d7390000000000d876b0
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
  | 0 => checkCutEntry dom_x2_0_x5_0 roots_x2_0_x5_0 5 s ws hint
  | 1 => checkCutEntry dom_x4_1_x5_0 roots_x4_1_x5_0 5 s ws hint
  | 2 => checkCutEntry dom_x1_0_x4_0_x5_0 roots_x1_0_x4_0_x5_0 4 s ws hint
  | 3 => checkCutEntry dom_x4_0_x5_0 roots_x4_0_x5_0 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x5_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x4_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_0_x5_0 _ hc
  · contradiction
def p0Subs : List Nat := [3, 0, 1, 2]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x5_0 goalM u ys := by
  unfold cutHitH at h; rw [Bool.or_eq_true] at h; rcases h with h1 | h0
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

theorem low_x2_0 : Lower dom_x2_0 roots_x2_0 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f00000f0f0000, 2, 18)] (by decide +kernel) (by decide +kernel) low_x2_0_x4_0

namespace S_63
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (1, 33), (2, 3), (2, 10), (2, 18), (4, 5), (4, 12), (6, 7), (6, 14), (6, 22), (6, 38), (8, 9), (8, 10), (8, 12), (16, 18), (17, 19), (17, 21), (17, 25), (17, 49), (20, 21), (20, 22), (20, 28), (20, 52), (24, 25), (24, 26), (24, 28), (32, 33), (34, 35), (34, 38), (34, 42), (34, 50), (36, 37), (36, 38), (36, 44), (36, 52), (40, 41), (40, 42), (40, 44), (48, 49), (48, 50), (48, 52), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 4, 6, 6, 6, 6, 8, 8, 8, 16, 17, 17, 17, 17, 20, 20, 20, 20, 24, 24, 24, 32, 34, 34, 34, 34, 36, 36, 36, 36, 40, 40, 40, 48, 48, 48, 56, 56, 56]
def r2sG : List Nat := [3, 5, 9, 33, 3, 10, 18, 5, 12, 7, 14, 22, 38, 9, 10, 12, 18, 19, 21, 25, 49, 21, 22, 28, 52, 25, 26, 28, 33, 35, 38, 42, 50, 37, 38, 44, 52, 41, 42, 44, 49, 50, 52, 57, 58, 60]
def mpG : Nat := 0x3fffffffffff
def pool6G : List Nat := [61658836305164, 39668421104180, 61718965846794, 61646004552993, 61599028356626, 61727842896396, 37469902087698, 37456512942881, 18718040400133, 39608527360550, 61727842898484, 61646001931529, 39655771997473, 22064189939973, 22016609756690, 61646236680969, 61658837878068, 37457349970179, 61599027432458, 37456512943393, 39729387801126, 61645766919433, 39655536198433, 22064187312389, 37409452524838, 22063348253452, 18717804201219, 61598757686282, 39656005960453, 39608475779878, 39656373357061, 39656373356805, 61598706762508, 22016608832517]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_all &&& dom_63
def NN : Nat → Nat
  | 4 => 7
  | 5 => 57
  | 6 => 192
  | 7 => 548
  | 8 => 283
  | 9 => 26
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xfd4459f0bef1bc99acf84d7a830f9e45519ee3282a6c6dc12898dfea
  | 5, 0, 0 => 0xfadf2db3ed3f395ae9568ffae776916bde61ae49d5dec37cc68802ecbfc235ebbac48acab91cf1c9b5899d3cb3b5d21fada2c201aa6ab691a9ba7ccea798be06a5e4c81ea0f9762ca09ced95a08a055b9c2a4660951747cf93ca83539334095491262c628883b7c672f18c8b701244706fcb19136f88bb0f6d26eedf6be2d3e0671d89a466cab041655776cb602b0ec35ebcbcd55e5780ec5c14bde7534e83744cd75e0040ba5b35402c17763ba8d18238b6d6a1323a9b822b16e2482328cd4e225871321ede97f31c9d6b1413e0cb46106a0443100e426105098c490467430003e55ce7
  | 6, 0, 0 => 0x59df37c55738c896545d9434512a565f511ce3a650e043ff502473694f2e193b4e72b9f34e1d92c44d0211904b6882954b4d31944b0c42ab48893a7a475dc18e46ce433745cce363457a83134459c9ea42ad9c653f6ae6d13d6089e83bcbb2e73b678d4235f2b5bf330c9dbb31800e8a2f9ad2e52f6753852d93ce0e2b4fa23d29204b7d2714f68726aab3b72538064a22fdda5c22f3643022b3ad672258be2f21cf34ce217c12aa1d4a39ee1c7212bd19a4c68718cb3b74184febc513e50f3d1161e45f10de11440fbbea030fbbcc4a0f4b7f560df3ceb30ca3b5de0ab1918c07cbaed307198c07068aa96304fbce7f04ebb28c03e931270368fe9300598859
  | 6, 0, 1 => 0xa407f263a3e4fa6ca3dc5717a21e100ba146a2149eb63d339e5b2cb99c8951439c482d749a2512c59a22b34199e0b1c199bd0b2a96ee98d9943ad31e904c22ee8fadd5768ee1fa168dfc1c578be05f688b674e728b27bfd48952c9e888931dff87f346a282950184823172d881d532ee808545537ff0d7507e1b40517d4c426e7b3832d67a5bc27979d79dec791351a67910fa09773edad675a76b8374297a2b7423dda97338c2127186a54670496a8b6f0d190b6ef0fd586e769cdd6d0b04896ba26c6a68f4465d68cf7c37680de50a67d016fb67ae2a06675059e166c4274166ad06a564e4815963fbd0df6386892060d5834a5f0d90dd5c4d69d75a956559
  | 6, 0, 2 => 0xfdf9659afdf66d6efc6e88affc20786bfb9cd9c2facd09bdf580d6edf2a57a16f221ca1bef4702d4eedb92cbed2150faec1818f6ebeabd24eb8fcdecea2ffbf7e9e68530e8e0fa4de8a8abede6439c7ee4811541e471dad3e39955eee37a1951e2d56012e22d262ade9a69cfdbe06c38dbcd1d99daadeaafd8ae62b1d8327f90d65b8e97d3737523d2524aa6d19faa06cf994254caeb9b70c6ecb9a1c68967bcc5b44f88c2b07e02c1f2a3d0c06caa72c021bcacbd92e1d4bb41cdfbb8d91b38b839177ab8336b67b7ae395cb434601db3011fb6b0e5bad3afdfc9a8ae200e62ada1614cacb1290ea9d70228a92cc8b6a919135da6946bc4a5c1ad00a53f8d20
  | 7, 0, 0 => 0x1ba9074c1aca7bc81a939d131a0397ba1996d3a0196c97d417d58bc317c5b6f0172afb1815e149c415a29c4115653d6814b726ea149a4ea1146dd67813fda563138bc72e1371087b1357233a1227f09d11e861ff11ac345010faeb32108dfb000f4449ac0ed4fd100e66c2330e5684bd0dbbbcde0d52fdb80a5667000a1c88f4097f42550979a5d30895d519086df8bb07cb813407c644650750f592071ebcc6070b6e2706fefd2b06a40df30694c23506499c2105f4b00505da15a005a7c7630532d23704e4e8ea04dbe27c0474d6a10462e1350446c582042142730414a87703f06d2503ebf0ec0370d01e02f2e5b2026aed28021f224600412c3d0010041b
  | 7, 0, 1 => 0x36445c913592eb5735747c4034824e4b3456a4b4340c055d33b8069c33b0f4e332681bf4322d29b131df196d319b7248311656bb3107d3ae2f3679eb2e9f17e82e1f778a2d81375d2d7eac952cfd4cb22cd48a3e2c1a27b72c002f4b2b9ea3c32a9e670e2a81106f2a6bb05329fbfd31297cc0d4289b697328641b182807443f27af507d2726dd47266a576826057a5825a1eb182579079a254f9c3424cb8b5524bc32c923efb98523e4b7822308cf9f22e9b86821d0d1c621a95e26213777172112506520e3556c20bd169c1ed593121eb4212a1eb1f0a11eb1c1a61ea7e76f1e674cef1df3a9141de8e6291d9ebe2f1d490ecc1c6686f61c023d801bb5a148
  | 7, 0, 2 => 0x5af33ad65aca5d735ab8a9c8598215f25916f36a5874c9ef580aba2258039e4a57f655b7573ab3ac562b742b5626438a557784d655073dee54f6b5bf529e82285271f78f52083abf51d54e5151750ba650fece0850fcb6f25047ce894f968dac4f09552f4eabf50f4e2ee3624d8edfa44cba213e4c9ad3b34c2e2dab4c272b804bafb81c4b07216947ef23c546a5aa93464f4da1459ded534566e491453591d244e31715445383ff43e3fd0e43e254544375d68c42b11f72423d3c4e4206f13841f44f3540e06b1a404296163e9a40983e6edb873e26d9273e0301fa3c5fea2a3bea33ee3ae45aa93add98ba3a6372fa39321f41387cf53237f2c06537bb2d5d
  | 7, 0, 3 => 0x75a2edc775300ff774fb6bb77480d24774391d8f72ab5f4f718e49e47174690b70a7275b6fec830e6f658ee36f43ea976ef35a186edf7c9c6e3b3ad06e3433cd6e07e4c16e0368886d8847ba6d043ea96c873f416c76c0d66c3e96666bb156c16b9ca6a46b58447069b46fdc69548d24689eda766864628b680afefb67e20fe067a812d06739e7116673126165ff6a2e65f0a6b0654799756525f48764ef0a7e64a6aa8e63965c28632c349263274522629b960b6226436761d9161e61c76273616dfee3605c2bfe5fe245c45fb3f3825f83829a5f16df6a5ef7a2cd5d97f1e35d73bb595d251b845c6954b95c57add25bf22aa55be7e2d45b7342755b0a17b2
  | 7, 0, 4 => 0x9553881e9522500394ad7817938b73e2934f2dc4934c359893209e1591f789a3912299f9906737e99022d1e78f037d7a8ed8dd848e9d7d068e26e5f78e1d627c8d9225708c839dfd8c5fd6378bc0d5c28bbc70aa8b19b7c88af4dc708aebbf738a304b448997b887895436e08802cfa28700b65a86de1e44865fd91e86453eb985b9eee28574e552856cdd14849ccafe845b963e84315af5827719248140854e811da4dd80fd97147fbd18fc7f7cb5047eb814087e5eb0787e151cff7e0956ae7c3f68397b9964a87b8acdea7b36f6787b1dd25f7a831aff7a5716df7a0eec327976ef1679485f6778cfe17b788c2ff57862d68977d25643764a93397607a4ff
  | 7, 0, 5 => 0xb5af7852b5416e40b53a41a8b4d870c0b3fa7eaeb3156a73b2a00218b2069b61b1918fb0afe9734cafe9653daf470c66af22a460ae49084eae43e66cadf5efeaadcd7a96ad433354ad13837cac8c31a1ac8550d0aaf7e2b6aa82d705a9cc52bea9744f92a91197bba7454648a6e4eccba6bbb42ea6768364a6080b8da4a14780a41588cca3798e69a27497a3a241eaf0a214873fa01eb4169f67cab99e56811f9e33d4ec9e3136e39dfc23f69dd647ab9d2176fd9cd5fbe69c7675b69c6f54319c6d66999b6f9ad19b4a782f9b3dde339b2dce579b27740c9a9a44729a2873fa9a06f67198a206619836ef2697ef9c39967c8c2e964c72dd95cdd5a695c7433b
  | 7, 0, 6 => 0xd2b65212d28c47b6d248728ed206ce76d1cce4d6d1a51e2fd16ca0bed12ac53fd0bd556cd02c02fdcfaccb24cdc18071ccde85f8cbf50b6acb8b3933cb69ce5ecb349801cb11b533cabf5ebccabe2c2bca54dc08c9f9bd60c9f97420c9f8ee7ac9f3d846c86265e5c8144c74c673f56fc62b88fcc4f09b0fc45b15b3c41d1613c406c3f6c3a85e1ec3248b03c32481ddc2daf057c2024609c171ea6abfc5b5b0bec1af2dbe302c54be0af635bd97d8e1bd56c4b9bd569d44bcf80b4bbc6f13e9bc4e049dbbf4c111bbecc5edbade97aeb9cd3fe6b9a8cac8b91f90c3b8ad8c6db853a286b82ebfcdb8097591b6fad8c9b6d1dad4b6af85aab62871f1b5e54624
  | 7, 0, 7 => 0xf0945cbfefeb2d83efa703a7ef901e62ef8454b0eea663e9ee8830ffee803053ee28865dedf34286ed84c96ced65bc25ed0fcc39ec20b13ceba52384eb222eefe9eb6b25e97deab7e8cf8ba4e8a7455ee85a7ff3e6e489dbe6801e89e59d96b3e54e6e14e53126b1e4ae95b3e483e165e3735aeee35521e4e2c10b79e2a3a791e1560784e10c9b80e0dc783ce0620ad5e04d6edde01f1c9bdf21d78fdf185981df0fbfd0de9849e3de8ede08de4dbcd2de164021dcc2d6ebdc8e32f7dc530cc6dc240b61db7cb9bbd9fde2d5d95b6233d825c4b2d7dd85d1d7a0e62ad79f9109d7120514d6d828a2d5b41e40d5a576d8d51552b6d4dfb9a3d4c9f929d39eec29
  | 7, 0, 8 => 0xff89b8c6ff8634b3ff57afedff3d1588fdfd4d15fdf3875ffdaefc54fd93ab53fd52bc6afd380cd7fd05efccfd03f230fca6220bfc8bca0cfc02cecffbd43f20fb88fb78fb3e6e67fb2e4632fb10699bfad792e2facfb439fa2886acf9f779d9f9b38880f9611aa0f914bcf6f895c760f7568747f713d73ff6b5bc52f62b4b74f5e05daef5373f08f490429ef0d999e6
  | 8, 0, 0 => 0x36aa157736209e1534bd92e333ac49493386ff0d33641e9c31c32ec330797d6f2ff00c9c2ea7d59d2c9d909e2ad2a9b42aa95048292e66d928910cf826c74c062566d73a24f1d90e249d63ef24923197225227cd2232fccd21f40ce01d0c61251b9b06e31ae554351ac2a53e1a28899f19e4b47719b15e6818b98c201723715416ed244d15303b88147ef837141f8fdd140ddc3213b478a2128177ed126ac74e11c9fc5910eee49c10dfc44d108cbea210739a890eccb7400e9e27910de1f81f0d2c2e290cd4669f0ba05b630b8bbf6b0b5d6d290af1fed60a5133e10a4a180909d69a710907828d0801277906e4120e0499b2c1025a06d301dd076b00f26ece
  | 8, 0, 1 => 0x76abcfae764d3db575a3370774e1c74f71e3fb2171a8d4f07162e77e6d7b8cdc6cd46e566afb3f026aeac5db6a75398c69da45856999900369415288679e3ab86722ad006640f86d64ede01564d6e24c644d152063d8096f608a602b6013f4555faaa4325ed2ab605b8a9b54592b668a58bcfd2356c7b29454bb11625360be5f5325690852eda10b52652dd550ba5f8b509cfade50429db54f4e6d214f2308104f1c75a54d8457f24c50a0f34c1021324bba97004a258bc549e5240847c09368477294e646f3f1d646e757da45d1eda14541e84844aae86242694ba6409f8ab43fd89f2f3eca17bc3eb72f933bcc4b8e3a4949613a2919be3797b31a376a4f69
  | 8, 0, 2 => 0xaabb0592a99d0106a9536d8da8fc3611a8aceb64a77db8c7a57263d1a3ac4ce7a32013a5a0c6aa12a039bc459e86591b9deb9d439ca6bdbc9c31e4e49bea8a5f9b2fddca9a31aaa699ca9ecb9972845b9946354f9941b91698c6984897e410729790a9e094ea215094dbd1b49492ddb29353153f93494f8992a88494915ed34090dec3a290943691902d5b0c8faa1b9f8f0950aa8ed4acb68e6a85208e349d828dbf9f568d8425078d4f66ca8cac4f718c27a7848c0b847c8b9a7c8c8b3625d88ac1d32889e60ac888a3b6dc872633628646d6de84fccbd184d2c17584135e9583b31a7d83490ab082fc96368077f7197db0481d7c3a52057a5ac63378ba6f2e
  | 8, 0, 3 => 0xe1f09bdde1edd638e183f5d5e17cf3aae042b81ddf1b03fddf0b1436dea4ce9ede53bb01dd44ebefdb27b5cbdae1e332dabcacbbd7c3a15ed676da41d6363344d358ca24d03a22d3cff609b7ce904c00cdef810bcd52d7cdcd10f587c9d81675c9ac6cdec972257ac9123a57c90dcec6c7abb727c6dc9e7ac66c1ee5c5825014c52d073fc3753fb4c2d474bfc18ac36bc11b76cfc060a091bfd6d0e9bf51c55bbbc01f92bb553d6fbab4727aba11faf3b9653685b8db3bf4b7794bf6b6ff2650b68d3f41b65b2236b5e0fc76b4659c05b3c7f7b0b19e29acb1838f47b15805aab141b29aaf99e6ccaf359018aeec9bcaae6ff2a8adb8d1c0ad7136f2aba7945f
  | 8, 0, 4 => 0xff0a3806fee14d72fdf4a2a0fa359d84f8ec2452f8350b36f7a272fef77c0b91f5380deef4c886ecf44d6af7f147f2cfeecba126ec9f0221ec907bd6eb7c0bb4eac36ef1ea5d0618e7f44a52e7baf5ffe78c552be72b167be6f82e66e6527f1ce45de151e3e1ec07e2182b15
  | 9, 0, 0 => 0xfe971ab2f92dd199ee12c54de5f2c308d43a869fc02871debde6d522bc1d1430ba47a138b749d50ab03b1c5fa0e187959437159c8f8b65ae62a89ff75d017f514e31041e46d9577144efaef6448b58423ef2c9303e51fe3b3d084ce7358f846f242a74e0196926bf
  | 10, 0, 0 => 0x69904ec9
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xffffffffffa0ffa0ffffffa0ffffffa0fafafafafafafafa33333333333333330000005500330077eeeeeeeeeeeeeeee0f0f0f0f0f0f0f0fffffffff00000000ffffffaaffccff88ffffffffff00ff00ffffff00ffffff009999999999999999ffffffffff88ff88ffffff88ffffff88f0f0f0f0f0f0f0f01111111111111111
  | 1 => 0x505050505050505ffffaaaacccc8888ffffffffcccc8888ffccff88ffccff88ffffaaaaffffaaaafcfcf8f8fcfcf8f8fcfca8a8fcfca8a800ff00ff00ff00ffff00ff00ff00ff0000000000ffffffff0000ffff0000ffff0077007700770077ffff0000ffff0000ff88ff88ff88ff88cccccccccccccccc0000005f0000005f
  | 2 => 0x5500ff00fffffffffff0f0f0f00505050555555555ffffffffffffaaaaffffffaaff00ff00eeeeeeeeaaaaaaaaffffffffcccccccc1111111155555555fcfcfcfcfcfcfcfc1515151515151515aaaaaaaaaaaaaaaaa5a5a5a5a5a5a5a5ffecffecffecffec005f005f005f005ffafafafa00000000ffa0ffa0ffa0ffa0
  | 3 => 0xeeeeaaaaeeeeaaaa8888888888888888e0e0e0e0e0e0e0e0ffffeeee000000000000fcfc0000fcfcc0c0c0c0c0c0c0c00000555500005555f0f0f0f00000000055555555555555555555000055550000cccccccc00000000000000ff003300ffcccccccc33333333c3c3c3c3c3c3c3c3f0f0f0f00f0f0f0faaaaaaaa55555555
  | 4 => 0x131313131313131300000000fafafafaffffffff05050505a0a0a0a0a0a0a0a0ffffccccffffccccc8c8c8c8c8c8c8c80000000077777777ffffffff88888888ffff8888ffff888800007777000077770707070707070707fafafafaaaaaaaaaf0f0f0f0a0a0a0a0fcfcececfcfcececfefefefefefefefecccc8888cccc8888
  | 5 => 0xffffaaaaffff00000055005500ff00ffffaaffaaff00ff00050505050f0f0f0f11111111333333330000000055555555ffffffffaaaaaaaaaaaaaaaa00000000ffffaaaa00000000cfcf8f8fcfcf8f8fffffeeeeffffeeeeeaeaeaeaeaeaeaea2222222222222222000000005f5f5f5fffffffffa0a0a0a0ffffa0a0ffffa0a0
  | 6 => 0xf5f50000f5f5ffff0000ffff33330000ffff0000ccccffffff00ffccff000000000033333333aaaafefeaaaafefe0303030303030303000000000f0f0f0fffffffff0f0f0f0f0f0f0f0f00000000ffff0a0affff0a0aafafafafafafafaf0a0a0a0a0a0a0a0affff0303ffff0303ffff2222ffff2222afafafaf0f0f0f0f
  | 7 => 0x333300003333f0f0c0c0f0f0c0c05555444455554444ffffc0c0ffffc0c0ffffffffffff0000fffff0f0fffff0f033333333000000003030303030303030555555550000000050505050505050504444444444444444ffff4444ffff44440f0f0f0f03030303ffff0000ffffaaaa00000000f3f3f3f3ffffffff0c0c0c0c
  | 8 => 0xfffffffffafafafa32323232323232328f8f8f8f8f8f8f8ff8f8f8f8f8f8f8f8fefefefeeeeeeeeefefefefe00000000eeeeeeee00000000f0f0a0a0f0f0a0a0ffffffffeeeeeeeef0f0f0f0f0f00000fffff0f0ffff0000fcfcfcfcccccccccffff0f0fffff0f0fcfcfcfcfcfcfcfcfffffccccffff0000f0f0f0f0c0c0c0c0
  | 9 => 0xeeeeeeeeccccccccccccccccddddddddfcfcfcfcececececfcfcfcfca8a8a8a83333333322222222f0f0f0f0f0f0a0a0fffffafa00000000fffffafafffffafaffffafafffffafaff0f0e0e0f0f0e0e000005f5f00005f5fffffececffffecececececececececec05050505fffffffffefefefecccccccccdcdcdcdcdcdcdcd
  | 10 => 0xffffffffffffccccfffffffffcfcfcfcfcfc0000fcfc000000000000f0f0f0f000000000aaaaaaaa3333333330303030f3f3f3f3f0f0f0f0bbbbbbbbaaaaaaaaffffffff30303030babababababababaffffffff22222222f2f2f2f2f2f2f2f2000055550000ffffffffffaaffffff00ffeeffeeffccffccfafafafaf0f0f0f0
  | 11 => 0xfffffcfcfffffcfccccccccc88888888ccccccccfcfcfcfcf0f0f0f0fcfcfcfcf0f0f0f0fafafafacccccccceeeeeeeefafafafafafaaaaa00000000cccccccccfcfcfcfccccccccffff0c0cffff0c0c0c0c0c0c0c0c0c0cffffffff0a0a0a0acecececececececefafafafaeaeaeaeaffff0000cccc0000fafaeaeafafaeaea
  | 12 => 0xfffffffffffffffff0f000000f0f00000f0ffcfcfcfcf0f0f0f0ffffffffc0c0c0c0fcfcfcfc00000000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x302010040605010440807010040f0d111040f0e0d0c408070a09408010a0b4
  | 5, 0, 0 => 0x80517010450813200c1f513200d0c165081201001550f0e01250c5081719010050820111f1552c0111252f51d1b170a095081b17272650807112509508130100145080111250b52e1b17112d5081732251551317332509508130104185291b1701285081b1c010051317010416508200d0c15513120a09165081e1701005291b172a09508131704095081b171a0050313120100513200d210c5000302010a4080e230d11513171130095000f0e0d114
  | 5, 0, 1 => 0x817010415508120a091551d1b1701005131701300c5131711241650802120100508200d11105000807010a408130d0c225081b1c0a0950f13200d0c5080d112215513120100165290135253451320111f165081317240c5061317010450f011125105081e170a095081711241552c2b1125095080e200d0c508131200095131731250c513173225165
  | 6, 0, 0 => 0x813120100500081312010a3d60000031312010a50000081320111f500081211250915600080e230111256001b170a1109166000013200d1116500000f0e011125500081b170a400960013171158095a6001317112545166001317273a3716600081317250c5c6007017112509156002e131744250c6004d131701250c600081317640c63600081b17413d1160008131760250c600086e171125096003c1b1701113760000081317322550008170d4c0c15600081317255b09600131711250949600590813172754600081b17270100600081317010a0460000296c01352550008171901250c600131701580c5a6
  | 6, 0, 1 => 0x8131711245001701370c15166000813200d010c6000817250c09396081b1701430a11700081b17011128600082001250c15600291b1735250960000081b1c010a5000855174025096000813200d114a6000813174c0c1f600671317250c66600081b17370c0960013170d4c0c1660000080e200d11500131721250c096000003020111255000013173111255000817114c1f156000817013e0015600002e1b1744115000817370c09156002e1317440a1160029086c11250960000081e17010a500081b172a1109600002c2b01112550008171125094660000081b171a0a500086217250c09600081719010a116
  | 6, 0, 2 => 0x1317370c0916600081701254f15600081312010a00600081b0111252f60008170a110939600290801112534600131711250971600171137091516600081320250c09600084b13200d11600000813010a1450029131744010a60008171125096d60008135d250c09600081b17010c006000008130d1122500131701250c4e600081323200d1160029081b17010060008170111373b600000f13200d1150013173525096b600085f17250c09629081b17010a3d7000813173e00096001b1701370c166081b1727010a3f70008171125096f600131211250916600081701116a25600081727542515600081b170c53096
  | 6, 0, 3 => 0x81b17014000600086517250c096003c1b17112509600080111255e15600081b1701112d600591317580c09600081317254f096001d1b171125096001b1727010a16600131727542516600081b17270a3d600085017250c096000013170111305000813200d110c600081b1742010a6002c57171125096002e131743250c60000081b172754500132001250c16600511701250c15600081b17110009600081b170d3d116002913170d012a60013171125094e600171125093916600000812010a155001317114c1f166001b17113709166001317013e001660000081719010a500081b17541109600081b175611256
  | 6, 0, 4 => 0x81e171125096000f132001250c600721711250916600080111252215600291317353709600131711257316600291317012528600170137360c16600086117250c096000013200d2111500131738250c68600001312010a1650008170a3e0915600081b170d4311600081701370c39600471711250916600481711250915600131701254f1660000291b17012a500000813170104500080e2001250c60013172101370c600511317250c09600082b1b112509600080e13200d11600081737360c09600172101113715600081301250c5e6002913172a2509600000813120a0950008173a2569156001b17011100166
  | 6, 0, 5 => 0x13170a3e091660008171125093b60008131727440a600001d1b17010a5000817011100396001b17250c0916600000807011125500081727010a39600081317010400600081b17441109600081b1c11250960017250c091516600081317272526600081b170a0c09600000813200d0c500131701250c52600081b1701112660013170d214c0c60000080212010a50029081b170a096000008200d111550008200111251060013173a2569166001711373609166002e131711252d6000013170133255000817112545156002e131738370c6000817273a3715600651711250916600081301250c226000817113709396
  | 7, 0, 0 => 0x1701113715166000008132001250c600131711253709167002e08131701370c70059131701250c16700081711250963157000813179f112509700002e131738250c600000817273a2515600081b17010a1109700000813200d011160008131725580c097000008a25d011125600081b1782112509700081b171125091670008b61317112509700ae08131701250c70008971b1711250970008131754112509700081b13170a11097000008170111256d6000008135d01250c6000813170d821125700081317270d250c700081b17113a25097002913173811250970000081711250939600000817011125956000008200111251560013170d2101250c70000087a17881125600002e17381125156
  | 7, 0, 1 => 0x813172701370c700081b170188250c700088313171137097000817013811371570000085f171125096007a1317011137167001317019311251670000081b1727010a600001b17011137166001b1701112509167000008131727542560029081317250c0970000081b17273a2560008172701113715700000813178225b5600081711250c09157001317010a11371670000081b170154116001b131711250916700081317112500097000813170d3d112570013170d011125927000894131701932570000131701370c16600131701250c0916700081317250c0963700000817010a113960029081711250915700002e1b173811256008713170189112570008131701bd11257002e1317380a11257
  | 7, 0, 2 => 0x81b1701381137700670813171137097000008132011250960000081727ad3a25600002c57170111256000813170d114a4c7000008178c1125156000813170d250c787005913171125091670008170d01250c15700081317012a1137700131727010a25167000817270111253b70029131701431125700081b1711250c097000008135d1125096000813170138370c700081317270a3d2570000081b170111006000813178b0111257001317015411251670008131701250caa700081b17010a3d117000029b117013525600000802120111256002959131701250c7000013170111254e6000813170111259b700001701112539166001317011125691670029081b17112509700081317018211377
  | 7, 0, 3 => 0x81b17017e11257003c1317010a11257006708131701250c7000813171125096b700000847171125096000059131701580c600131711253e09167000008131701254f60008131701250c8e70008131727441125700001d1b17011125600081b170d01250c70008551317112509700081701113775157000008501701250c600000817019325156004b13171125091670013178a010a112570000131711370916600005917011158156000813170d014c0c700081b170186112570013170111250016700081701113537367000874131701113770087081b17010a11700700813171125097002c081b17112509700081317013d1137700081701254c0c15700081727011125397000813170111252d7
  | 7, 0, 4 => 0x84b13170d114c700081317b71125097000813170d250c09700081b131701370c70008131701a6250c70013171125096316700131711250916b87000051131701250c600001317273a25166000813170d43112570013170d0111254e70000991b1701112560000082b1b011125600081b1701880a117000813170111377f7000008170137360c600002e131743112560008170d112509157000013200111251660029131701380a2570000291317012a25600005117011125156000813173811370970008131701370c787000000081312010a500295913171125097001317270d1125167001317112509b516700003c1b17011125600131701250c16ac700000817019f2515600081b17881125097
  | 7, 0, 5 => 0x81317a901250c70008174101112515700170d0111251516700081b170d010a117000813174401250c700081701113709157005908131701370c7008f08131701250c700081317b2011125700081b1711402509700000865171125096002908b117112509700000817010a3e15600081317113775097000008131711258d600000813179325096001317270111371670008174401112515700131711250c09167001317bc01112516700081317a401250c70000591317115809600081317250c096970008131701250c5a700081317019e11257000817010a250c157000047170111251660000481701112515600081317010a3e00700081317254c0c0970029131711250916700000850171125096
  | 7, 0, 6 => 0x7217011125166001317bb01112516700131701254c0c1670000501701112516600081b170196112570000080e2001112560000081b171a11256000029131701353760008131701250c1f700081b1317113709700001317210111376000013178c11251660008131701a8250c700005113171125096000813174101250c70013170d01250c16700084b131701370c700081701113a3715700081b1711352509700081b174401112570008131701370c09700000813173a25696000008171137360960008170111251f157000813170193254f7000008981788112560000031312011125600081b17010a250c700000813179f2509600081317014311377000008130111255e6000008611701250c6
  | 7, 0, 7 => 0x813174201112570000086217011125600590813171137097007b081317250c09700001317381125686000813170a250c0970000481317112509600081b17010a1100700081317011125267002e13170138250c7000813170d114c0c700081317250c79097000813170154113770013170111377516700081b170111257870008811317011137700081b1701113a377002913170138113770000081701113739600290813170a25097000813171125095a700001317019325166000817011125093970000081e1701112560008170a1125091570008131701250c9b7000813171125093970008131701370c16700000817250c09156001b170d01112516700084b1b170111377000813170164250c7
  | 7, 0, 8 => 0xf132001112560017010a1125151670008551b1711250970000081b17440111600081317113a370970000081b1c011125600001701250c151660000081b17010a0c60000081317a0250c60008131744010a11700081b17010a3f117002908131701370c70013170d11250916700084b131711370970008170111370c15700081b131727010a700081317011137007000029081b17010a600081317273d1125700081317841125097007b081b17112509700a708131701250c7002e081701250c15700000817a0112515600000813170a3e09600081b170a11250970000170111373616600087a1317250c097000813170137770c70059131701250c7970000081b17250c09600081317441125097
  | 7, 0, 9 => 0x813171137770970000081317273a376000813170182250c70008831317250c09700001317010a3e166000008170111253b6001b17010a11251672908131727010a25800084b13200111257081317910d011125800001b1701250c16600000817011125a3600131701bd112516700081b17019a1125700002e131738113760008178c0111251570008172701250c157001317010a250c1670059081317273a25700081b170111370c70008131727012500700590813170154117000008130111252260000ae13173811256000813179d0111257000813179c011125700081701381137367002e081b1701250c700081b13170111007000813232001112570008131782113709700081317113709167
  | 7, 0, 10 => 0x8131727010a8925800081b17012a1125700081317013d250c700081b571711250970008131711370c0970067081317250c09700001711250915166002e081317250c09700131701113a371670000081b170a11096005108131701250c70000000813200d115000008131701255b6000813170137760c70000131701112552600001317011125496002908131711370970013170111251f16700081b1701821125700081b172701250c700085513170111377000013170d21114c60008471317112509700081b83171125097000813170d012a11700131741011125167004b13170111371670000081317112545600081317413d1125700131701113709167000817012a112515700081701113776157
  | 7, 0, 11 => 0x8171901112561317910d21011125800001317272111256000813200111250c70008131701250cac700088513170111377000013170111585a6000813170d01370c70008131727250c097002e081b17010a117000883131701113770008131701901125700291317010a8925700081701250c78157008708131701250c7000813172743112570008170125370c15700081317b9011125700001b1711250916600081727ad01250c7000813170186113770008170d0111371570008172711250915729081317270d112580013170a11250916700081b17013d1125700000813011125146002e59131701250c70067081b17112509700001317250c09166002913174401112570000086e170111256
  | 7, 0, 12 => 0x813170d4c0c600004d131701112560000081317116463600081b1727010a11700b4081317112509700000813171160256007b2913171125097081b13170d010a1180008170d01112539700081317b3112509700081b1711250939700081b1738112509700084b1317019325700081701250c53157000008170d114c156000865131711250970008170111353715700081b1701250c7870013170111370c16700a508131701250c7000813172a112509700131701ba11251670008131701801137700081317b0011125700000812011125156002e131701250c16700001b17010a111660008131738250c0970000081b17010a40600081317017e11377002913170d01352570008131784010a257
  | 7, 0, 13 => 0x81701370c1560008131764250c09700081317250c78097001b17270111251670008131725370c0970000701317112509600081701250c09157590813170d010a118000029086c01112560000081317273d25600081701113a37367000813170111377d700514b131701112570013178c01112516700080e132001112570013172701250c16700870813171125097000008131711255c60008131727380a257000817112537091570048081317112509700081b1701113537700081b174201112570008131701370c0070059081701250c1570000081b17012a116000813170125760c7000813170188250c700002e13174411256000008170111254660017270111251516700081317381125697
  | 7, 0, 14 => 0x81317250c53097000813170193250c7000817015411251570000081b1701370c6000813171135370970008131744011137700131721010a1125700081b1701250c097000813170111254f7007b08131701370c70008170111256915700131701250c16ab700081b1741010a11700081317010a370c700081b1317250c09700000813121125096000013172101250c600081b17014311257000817019311251570008131701370c797000813171125097f708131701430a11258000813170111252870059081b1701250c7000813170d112578700002917013525156000817010a1137157002c081317112509700001721011125156000813170143250c70059081b170d0111700131701113776167
  | 7, 0, 15 => 0x5113170111250c70000081b17010c53600000817113709156002908131701250070008551b1701113770008131701113778700081b170154112570008131701250c687000817011125001570059081317250c09729081317010a3d258000817011137360c70029671317112509700131701250c781670013170125370c16700af081317112509700081317a001250c7000817010a11253970013170d01113716700001317bc112516600131727112509167005908171125091570000081701250c3960008131701250c6970008131784011137700081727010a25157000813170111258e70000291b17013525600000855170140256001727ad01112516700001b1721011125600087a131701370c7
  | 7, 1, 0 => 0x8131793112509700084b1b1711250970000081317114c1f6000067131711256660000081b1711370960000085d011125156000817270d1125157000013170135256b60000085f1701250c6000817112509b51570000081317013e00600081b17011125007007b081317113709700131711250916ab700131701250c5316700170d2101112515700002913173525096000013170d114c1660008131727381137700081317010a3d3e7000813170a113709700081317250c0966700001317211125096000813170111a625700084b1317250c09700087c131701113770000081317370c0960000131201112516600081711253e091570008131701250c0070059081b171125097002e0813170d250c7
  | 7, 1, 1 => 0x813a15d01112570059081b17010a1170008131782250c09700081317250c09167
  | 8, 0, 0 => 0x813170111251f700085f1317011125700087a1b170111257000813174101112570013170d01112516700084b13170111377081317011125370c8084b1317011125098000813170111370975908131701113a258087a1317010a1125800081317840111257007b081b1701112570000081317010a3e600081b17010a1125700087a131701250c70813170d2101112587b081317010a112580000081b1701250c6000813171135250970008131744011125759084b1317011125800590813170111377008f0813170111257007b08131701250c75908131701112509800081317010a250c7000048131701112560008131701250c7970029081317010a257000813170111255a7000817010a1125157
  | 8, 0, 1 => 0x2e081317010a112580813170111250c09800001701112515166002e08131701250c70000081b17010a1160000081317a011256002908131701113772908131701112509800084713170111257590813170111250c8002e081701112515700087a13171125097000813170111377770008131727013a2570000081b171125096007b081317112509700081317273811257000813170a112509708131727c001112580813170d01381125800087c13170111257002e13170138112570000081317250c0960008981317011125700081317011137167000008171125091560008551b17011125700081317011164257000813170111257870008131701113a3770013170111254c16708551317010a11258
  | 8, 0, 2 => 0x5908131701431125800081b170138112570067081317112509708131701113525378002e08131711250970051081317011125708131701380a1125800081317012a112570008131701113776700081b17270111257000813170138250c700c108131701112577b081317270111258081b13170d011125808131727010a1125800085013170111257000813178c011125700081317018211257000813172701250c70008831317112509700081701381125157007a131701112516700001b17011125166007b131701112516700081727011125157001317010a11251670813170d01114a2580000131701250c166002e081b17011125700081317011125c3700081b57170111257000813170111370c7
  | 8, 0, 3 => 0x8131701250c53700000813170d114c600081317011135377081b1317010a1125800081b131701250c7000008131201112560008981b170111257000813170111257f70813170d011125168002c08131701112570813170d01113a258002e131701112516700081317c20111257084b13170111254c8000813173811250970008131701250c787000813170125370c700081317011125ac7084b13170d011125808131741010a11258000813170d01113770008131727112509700870813170111257000817011125371570048081317011125700081727ad0111257590813170d0111258002e591317011125700001317112509166007b291317011125700081317013d1125700081b17011125397
  | 8, 0, 4 => 0x7b081317011137700131701112516ab700002913170135256084b1317010a1125800081317010a1137700081b131711250970000131721011125608131727013811258081317010a1125098000817011125151670813170111254c0c800084b131701250c759087a13170111258000008131701370c600081701113a251570008170111253e1570008131701250c0970059081b1701112570813170d0111250c80008131701431125759081317010a1125800000817011137156000813171164250970008131711253709700081701112509157005908131701250c7290813170d011125800af081317011125700131727011125167005908170111251570008131701112576700081317018811257
  | 8, 0, 5 => 0x2908131701250c700084b131711250970008170111250c15700000813171137096001b131701112516700081317011125007081317010a3d1125800290817011125157002e0813170d1125700081317011125687005908131711250970008131727010a2570013170111253716700081317019f1125700081317a00111257000813170125580c700081b170111251670008131701541125700081b1317010a1170008811317011125700081b1701113a257002913170138112570000081701112539600081317011125697081317010a112516800087a13170111377000817011125581570008131701250c1670008131701931125700084b1b1701112570000081b17011137600081b17011125097
  | 8, 0, 6 => 0x59081317270111258004b13170111251670000131701113716600131701112509167000813171125096370000081317273a256081317010a8911258002c081b170111257000008132001112562e084b13170111258002e08131701113770059131701112516700002e131738112560008131711255809700ae081317011125700081b170111250c7000008135d011125600081317270d1125700081317112509b570013170d210111257081b131727011125800081317821125097000813171125091670029081b17011125787081317010a1125800081317113a250970008131711253e0970000085f1701112560813170138112537829081317010a1125800081317011125c5700081317112509667
  | 8, 0, 7 => 0x8131701254c0c700081317017e1125700291317011125167000008501701112560813170d010a11258000813170d01114c72e0813170111250c800000813178c1125600088513170111257000813170d01250c7000883131701112570008170111254c15700131701112516b8700081317018611257081317270111251680008170d01112515700081317013811377002959131701112570008bf13170111257084b1317270111258000813172701113770008131711250c09700081b17018811257000813170111256b70000084717011125600131701113a25167590813170111be2580013170111253e167002908131711250970813170d0111352580008551317011125700c40813170111257
  | 8, 0, 8 => 0x813170111253970008131711254c0970000081701250c156000813170d112509700081b13170111377081317010a1125008081b13170111250980000511317011125600081b1701113525708131701113a25378000008170111373660000081317019f256084b13170111253782908131727011125800081b17011140257002908b117011125700131701112516ac7000813170111377570000081317019325600670813170111257000817011135251570013170111250c16700087a13172711257000059131701115860008131701801125700081b170d01112577b0813170d0111258
  | 9, 0, 0 => 0x813170138112570813172701112570013170111251662e0813170111257000813171125096087a1317011125700081b1701112567b0813170111257081317010a112570008131701250c60008170111251560813170111352570813170111254c70813170d01112570813170111250c729081317011125708131701112558708131701112516708131701113a2570813170111253e7084b13170111257000813170111376081317011125097590813170111257081b13170111257081317011125377
  | 10, 0, 0 => 0x813170111256
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 36
  | 5 => 44
  | 6 => 60
  | 7 => 68
  | 8 => 68
  | 9 => 60
  | 10 => 52
  | _ => 0
def stateM : Nat → Nat
  | 4 => 0xfffffffff
  | 5 => 0xfffffffffff
  | 6 => 0xfffffffffffffff
  | 7 => 0xfffffffffffffffff
  | 8 => 0xfffffffffffffffff
  | 9 => 0xfffffffffffffff
  | 10 => 0xfffffffffffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x3ffffe00e00000003fe00fffe0000000001e01fe1f8f00003ffe1fffe18f0000001ff1ff1fff00000001e01e1e7f00003fe1fe1fe07f00003ffff000000000003fe00e00e00000003ffffe00e00000003fe00fffe00000003ffe1fe1e18000003ffffe00e00000003fe00fffe0000000001e01e01f8000003ffe1fe1e180
  | 1 => 0x3fe1fe01e07000003f000000000000003ffff0000000000038e00e00e00000003f000fff000f0000001e01e01f800000000001e000000000071ff1ff1fff000038e00e00e000000000000fffffff000000fff000ffff0000071ff1ff1fff00003f000fff0000000038e00e00e00000000001e0001e700000001ff0001fff
  | 2 => 0x1ff1ff1fff00003ffff1e01f8000003fe1ffe1fff000003fffffff000f00003fe00e00e00000000001e01e000f00003ffff0001e7000003ffe1fe1fff00000001fe1e01ff000003fffffe1e1f000000000001e000f00003fe1fe01e070000038e1ee00fe700000071ff1ff1fff0000001e00000000000038e00e00e000
  | 3 => 0x1e000f00000000000000000000000000001e0000003f01e00000000000001fe0001ff00000000000001e00000000fff000fff00000001e0000000000003fffffe1fff000003f000fe1000000000001e00000000000001ff1ff1fff00000001efffe18f00003fe01e1ffe0f0000001e0e1fe07f000000000fe1fff0
  | 4 => 0x3ffe1fffe18f0000000001fe1f8f00003ffffe01e070000000000000000000003f01efff1e700000000000001e00000000000fffffff00003ffff000000000003f000fff0000000000fff000ffff00003fe1fe1fe07f0000001e001e000f0000001e0000000000000001e1e01e700000001fe1fe1fff0000000000000000
  | 5 => 0x3f000fff00000000071ff1ff1fff000038e00e00e00000003fe1fe1fe07f00003ffe1fffe18f000000000fe1fff000003ffff01e000f000000000000000000003f000000000000003fe1fe1fe07f00003f01efff1e7f00000000001e1e0f00000000001e000f000000000fffffff00003ffff000000000003f000fff0000
  | 6 => 0xfff000fff000003f000fffe18f000000fff0001e7000003fe00e00e000000000000fffe18f0000001fe01e1fff00003fe01e1fe00f000000000e1fe07f00003ffffe1fe07f00003fe1f000000000003f000fff000f00003fe1fe1fe07f00000000001e000f00003fe01fffe00f00003f000fff000f00003fe1fe1fe07f
  | 7 => 0xfe1000e18f0000000001e01e0000003f01efe11e7000003f000fff1e0000003fffffff000000003f1e0fff1f8000003ffe100000000000001e01e0018000003ffff00000000000001e01e01f8000000001e0001e7000003f01efff1e7000003fe1fe1fe00f00003f000fff000f000000000fffff8f00003ffff0000070
  | 8 => 0x3ffff1fe1f8f0000001e01fe018f00003fe1fe1fe07f0000001e01e01f800000001fe01e1e7f0000001fe000000000000001e00000000000000001e0000000003ffff01e1e7f0000001e01e0000000003f1e0fff00000000001fe0001e7000003fe1ffffe07f00003fe1fe1ffe7f00003f01efff00000000001e00001e00
  | 9 => 0x1e0001e7000000001efe1fff00000001fe0001e700000001fe000000000003ffe101e000f0000001e01e0000000003f1e0000000000003f1e0fff1f8f00003fe1ffffe07f0000000001e01e00000000fff000ffff00003f01efff1e7000000001e0001e7000003fe1ffffffff0000001fe0001e7000003fe1fe01fe70
  | 10 => 0x3fffffff1e7000003ffff1e01ff00000000001e000000000000001e01f8000000000001e000f00003ffe11e0018000003ffe11e01f8000003ffe101e000f00003ffff1e001800000001e01fe018f00003ffff01e000f0000001e01fe1f8f000000fff000ffff00003fe00fffe000000038e1ee00fe700000001e01e01f80
  | 11 => 0x3f1fefff1ff000000001e000000000000001e1e01ff00000001e01e01ff00000001e01fe1f8f00000001e01e1e7f0000001e01fe000f0000000000001e7000003fe1f0001e7000003f01efff007000000001e000007000003ffff01e000f00000001e01e1e7f0000001e001e1e0f00003f00000000000000000001fe1e0f
  | 12 => 0xffff00003fffffff1f80000000e1f000e07f0000001fe1e01f8000003ffff0001e000000001fe0000000
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x3fffffbcf7ae00003ffb8fffefe600002dbe7bfebf9f00002dba1bbca18e000000044024108200001b67f67f7eff00001b61b61b607d00003ffff110100800003ffbbfdbef7d00003fffff98f52c00003ff98fffed64000024982982831100003fffff9af73d00003ff9afffef750000249e49e49f820000249809808100
  | 1 => 0x12418401406000003f3335530a5900003ffff5531a5900003ae9aecbef7500003f333fff2adf0000369f6de79fd3000036132de70ad30000071771771adb000038e88e88e524000000000eefeff7000000eef000f7bf00000717517518ca00003f110fff0840000038e8ae8ae73500001245e4435e710000000470001019
  | 2 => 0x440671ad300003ffff9f49f8a000012418cc1cd6000003fffffff3adf00003ffbbf98e52c00001b67f23e329f00003ffff5535e79000024980dc1cd60000036dfede7dff3000036d98d81c16000000922323e229f00001243842542e200003aefeeeffff7000007157153185900002dbe71101008000038ea8eace7a6
  | 3 => 0x1b23367f2adf00000000200202110000000640641e8200003f77f1101008000000cee000d7b30000000440401e00000000ccc000d5200000249e41001000000036ddcdc1dd60000036110dc1084000001245e0001000000000067024129b00001245eaacb1860000092452583e0c0000249e470b7075000009223cd1cd68
  | 4 => 0x2db81b98a10c000000000aeeaf9700003ffff5115068000000020024028200003f55efff5e710000000460421e11000000000eedede600003ffff112121900003f112fff0a51000000eed000f5ae00001b619619606c00002dbe733e329f0000249e4124128200003657ede75ef300003fffffffffff0000120124430a51
  | 5 => 0x3f333fff08480000061541671ad3000039eabe98e52c00001241860b6075000024980baca186000000000cc1cd6000003ffff33e329f000009223010000800003f333110000800001b61b65b6a7d00003f77ffff7eff00000926727e3e9f00000922123c208e000000000ecbed7500003ffff134128a00003f130fff0ac2
  | 6 => 0xcec000d7a200003f110fffa9c6000000eef000563900003ff98fdbed64000000000aaca186000009eef23ef7bf000009201218200c00000000060b607500003ffff71b707d00001b61b010000800003f313fff285d00001b63b63f62ff00000920321a201d00003f311fff284c00003f331fff28ce00001b63b61b607d
  | 7 => 0xaa1000a18e0000241449e41e0000003655cdc15c6000003f154fff1e4000003fffffff184800003f9f4fff9fc200002dba111000080000249a09a48182000036ddc10010000000249c49c09d0000001245c4415c6000003f55cfff5c6000001b61b218200c00003f110fff2ad7000000000aecaf8600003ffff5135079
  | 8 => 0x3ffffbfebf9f00002dba1bbca18e00001b61b61b627d0000249e69e69f9300003ffff77f7eff00003ffff110100800001b67f01010080000241209e40a8200003ffff77f7eff0000249e49e4180000003f9f4fff1840000036dfe5435e7100003f71bfff687d00001b65f65b7e7d00003f55efff18400000249e41401e00
  | 9 => 0x1b67f4535e7900001245ecc3df71000036dfe5675ef3000036dfe126129300002dba133c208e0000249e49e41a8200003fbf7110100800003fbf7fffbfdf00003f73bfff6aff0000241649e41e82000000ecf000f53d00003f57efff5ef300001247e4675ef3000012418eefeff700003ffff5535e7900001245e4435e71
  | 10 => 0x3fffffff5e7900003ffffdf7dffb000036110de708400000000008e48f8200000000022e229700002dba19b4818a00002dbe59f49f8a00002dba333e229f00003ffff9b4918a00002dba3bbea39f00003ffff33c308e00002dbe5bfcbf8e000000ccc000f7b700003ffbbfffed6c00003beffedbff7d00002dbe79f49f8a
  | 11 => 0x3fdfefffdff300001245e002121100001245ece7dff30000249e4de7dff30000249e4beebf9700001245e66f7ef700002dbe7bfe3a9f0000000004434e7100001b65f4535e7900003f51afff487100001241a403407100003ffff31a301d00001b65f65b7e7d00002dbe737e3e9f00003f110553084000002d367bfe3e9f
  | 12 => 0xe7b700003fffffff9fca00000060b000603d000036dfe9e49f8200003ffff1501e08000036dfe1001000
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 198 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem wd_0 : ∀ i, 0 ≤ i → i < 128 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem wd_128 : ∀ i, 128 ≤ i → i < 198 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 70 128 = true)
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 198 → wireDOK i = true := (range_split wd_0 wd_128)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 198 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 198 then wireAt i else 0
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
  | 5 => 43
  | 6 => 1043
  | 7 => 2721
  | 8 => 563
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xaa92666ca6584ac05eac5b7e576aad824444ac6f
  | 5, 0, 0 => 0xfb260178f690e440f15b500ff0b463f8eb256ae5e8753c35e7c05221e5f7c8bbe3ede76fe051076edefc856bd8aae099d51f7487d40b7d95c44222a7bb6d0d4eb22ab1a2a72038759dd647ab946afc80938669a492b773a78d294e847f50159f7f3994cb7cfa7a277a034d717651e21f70bfc84b68d4d485606617e45f3756875e60fdcc5cabef0b51f056d74a123ca13bea33ee2cd46d6c263770d21becb1f11a8e92d51851cd331716b4c0
  | 6, 0, 0 => 0xe66c2330dc680660dc001ce0da39ff50d5091710cdbdf180cc182eb0cb46fd70c9f78540c57856d0ba05b630b5f40c90b5b7ff60b473ba10ae65ec809d9ee1709b51d2109a9f76109761ef1091f418209185426087fcca40872a4550863ad99085b5d060835a929081f5fc008004c8c07530442070631ea06e4120e0694e74a06678eeb065f141c061e3e79060d28c705fcea2e05ba855505a01b610555dc93052cb6390521707c04e2af1e04d8ddb90462e135041b54f603f8295d03e1a0a2038a94200370d01e0360c75a0342f9cf032e490f02d08e5102cb356c029b3eb60262e26f01ce043e01c1dc3b01b60b0f016c556800bf18a7002c2d7300172a34
  | 6, 0, 1 => 0x1ae554351aace10f1a8610df1a6da2f61a38bbea19f741441996d3a0198b6f951984e97b197e5ef619326ebe1927a14e18af80cd185d4a4f183d5a6b17b5e2591771ba8b1700043516e6d16616cab25b16b7bd0716ab8c8d165e940516597d231658cc621643a6de163ee168163694bf161bec261615b49115c8eab715bc7c0e15a29c411504458814498cb91385f3fe1371087b131893ac131418ed130ba19912e8889912e7df1812be333012aa21501280d9f312759921126d7e9d122141ae11d86e081148cbad1122c616109911fc1076ee2f1074cb80105a1a7f1046f7790f4527f60f27dc140f20166b0efd143c0ee9cb090eccb7400eba320c0eb869df
  | 6, 0, 2 => 0x2aed239d2aca1f1f2ab731fb2a836b2f2a2f0cca2a0c930729e0061229b8653129a7721529a4117329a32866299c322928fc70ce28f54f4928910cf82884ead128794e862866bf56284ff25e281d302627ad6f242760319a275b9205272b4f0726edd9d126ca9fac26c1d593267304fa26070cb525be2f82258dd42825615ce4254f9c34254c0e9b253e0ff124df4e522475975123f6e37f23ab086023a8da942374b28422f971c822f092d422ab36ea22903a962274ea1222508f1622007d3421f40ce021a84b1b21a3ed8120e8daf220e6e1ec20bd169c204f7fe91fe8d88b1fd528dc1f683b8c1f5ea4701e72edb71ce570331ca8ccff1baaea081b897892
  | 6, 0, 3 => 0x3a0fa16a3a0948e739fb5db839f7395239c1173939997e943978469c396b85ce396aa3ac393e622738341f1437e8f494377b8c3b3776c27437769ccb3753fe0536e7f2d936759b103660cb9f36379e0c36263f93356bb79a35263e8d35074ac834bd92e334bd11df3456a4b433b7593933a6ed973386ff0d3366371333641e9c32fc7e7c32e44c57328b0715325beb0131ad60fd3158ea47312b042b3127429830bbb4ab30b3da1730a9931f3041824e3034f1e72fcbc7242fbebee02f3679eb2ece18e22e9f17e82e65ae532df3cc712d9b40532d882c942d73ca7b2d0004652ca7cc942c5e54df2bf9805c2bedc5d12be951ef2bda7c9e2b7e444a2b352211
  | 6, 0, 4 => 0x48deb89248d7a10748887538488142a0486588bf48222d0d4727ecd74684bc8d46839b9e464ff956464d772445dda18d45b2bb4c4559780a453591d24515788f44cd8bf4448f70a9444eea2943f5f8ee43e4d1b5435b6db74357d5ec433ee71e42e73f7f42aee1174289d5e642694ba6422ec1864228310c4206f13841f8c8af41c7dbb341c03cc0417ecd764138704840c6187f4086ff474007a3c43fb9c1a73f46801f3f25fd303ec4765c3e9e661f3e9010eb3e4a58b53e0300bf3dd793813dd764b23d93ec903d4823bb3d27f5b33c69c2423c4ad0ab3c437d123bf368d73bcc4b8e3b5c06d43ac119a03aaaf6cd3a90c4fa3a57a61e3a40c5033a151ed1
  | 6, 0, 5 => 0x5853cf775797b04b576b9f39573ac34f57090ffe56b1c8ce565b5541564852af562b742b55df544f5572ca98556cfc86553fcbf054e860fd549d984f54924c595483357b54703f9a53ed5d7f5317e18b52fa2f8052b1841451f336b151f280be5176962751525a0750fc801050c7476b50a80ace508cbf0e50595528503fea47502e59364fdecd1d4fb16c0a4faa861b4f942bb74f85d0be4f44d6d04f263a924ed583854ed09ba44dc646bf4da292a64d9d00f34d947f0c4d702f384cff85024ce4dc694cd555c24cc83f594c9dcdca4c91dafa4bd291ea4b331d2f4b0b17e04b0113f54ae3c8134ac4b4ff4a81d1cd4a5bbf824a3bfd6949e282cf497e0663
  | 6, 0, 6 => 0x6bcb755f6bbf54336b2757176b226ffb6b19de816a53a82a6a415a4369db379369cea9f769b8f0ee6971a7ac68aa067967fafb3a679e856d66fae65966e077f8664a7a62657e37b6653d59ad65333af36424ceda63c52cec635e23ba632c3492632745226320d54d630d044962930e6e62763da06253501b61d6cef261a34b2b619b4dce612a8ebc60d14eed5fb68be25f3c4d2a5f3b171c5f38afbb5ef7a2cd5e10fa395dd02c2c5db3cc3b5dac2a085d900afd5d62b5595d251b845cd49d255cb1fe155cafc34b5c871fc55c7b46455c1eece45bf22aa55bbe37c15b977fd15b2bf4835a7b9e545a4f42775a134b9759a3c653591384d958bcfd23589d4bdb
  | 6, 0, 7 => 0x7baf0da07ac5db0d7ac0ddc17a95c6f27a34ebaf79fa3d2a79bf63cc79823fa37968525e7933afc278da1e4a78cfe17b785779a477ff60ed77a3a379777f69047715d45d76c4582a764d3db5764d32ff7615dcee759ba135758dfd7075300ff7744209607432fa2a73f65d6173ed37ae73092275730619a172f0ed4f72ce0cde72bc591a72b0ab2172adff15729fb2a471fd96c071e3266f71a8d4f0718e49e47170cea671648ea171382528713103a371174ea47109dc7d70c5cd5f70c44dfb70beabda7070b0596ff956066f76cbb56f4706916dfc6bd06ded31a56dce3ec56d49cca96d4541c66ce805ed6cb14bab6caf0d1f6c76c0d66c3ef3e26c20d330
  | 6, 0, 8 => 0x8a19a66b8a00502789edde5289d8b78289cbc50b89a0043a8989ed4889899951894db45b892fa138892c1d2388c93c068888c9e7887bb81988628bb688077b3c87c570538798e6a7875d8dfa8755af5186ef59c186d9503586d2b804862a0961859ab80e854f5c3c84fccbd184d9857284c18d20849ccafe8485fe98844d273d8395c0db83912f9c833bb76a8305193682102af581db6deb81ba835b81ab944881a6f558818f753d8143a45a8128988f811da4dd8108f5d580f8fe9e80b3e57b7fb610517f989fae7f5676647e5dc07f7e248d087df2e1307dc200827da27d9b7d1c60a77cbf4cce7c73d1eb7c71289b7c4f87b67c2cfebf7c12f7dd7c06f5ba
  | 6, 0, 9 => 0x9ad13d4c9a7ae0a59a41b7f699b24a8199affe63998c182b9956921498c6984898561b9f983178f597f7b5c797b37c3a979a3f309773e2ac96dc14bf96c3f57b965903f39651af8196053d6d95f6c76f95dc5f9a9562efe794991c6f9494550e94701a99940776da93a4b7de9391693f934c359892a88494912eb69790b22092902d5b0c8ff6cb368fe9c3bb8fe19ee48f78e0ca8f5d59028f2f69968ed1defe8e9116618e6a85208e5540368e54373c8e2226b78e05cc928dce9c0f8d76fa0e8d1551f88cc727558c95ff338c5f50cb8c0b847c8bcc2b7d8b9ab91c8aff68268afa9dd58acc12a58abef05a8ab27a538a5750d58a46a0ae8a35f35b8a34f76c
  | 6, 0, 10 => 0xaa2124dca9f6ce9fa9cf09e4a9bde0c1a9770155a94d3c18a8fc3611a88242d5a82d7ee4a82b5118a820bc30a77f4358a76c1020a7240888a6f50881a6f101bca6d2311aa61cceb8a5f7db34a5b9ed9ba58716d2a5838734a57f04dea57b9e64a5533d4ba5219aefa4d2536da4a14780a47b5aa6a44bb208a40e3209a3c7660ea3b7432aa3b0f630a2b03c00a2400dd1a231a742a2289759a1ca3707a1712555a13d2202a0f3d190a096bd149ff703939fd364a59fc3786f9f610cdc9ee922899e9375879e6e1c509e3455ef9e194a249df9a76a9d70b2ea9d13f6189be869a39ba30db99b8811659b83d2f69b67b3eb9b4865e59b153e9d9afb9c289aecbd4b
  | 6, 0, 11 => 0xbcb5f9c4bc7536e9bbf7cea5bbc01f92bbbc7503bba6b7e6bb251300ba170c41ba12cde6ba04a7adb99d485ab98347cab9653685b878c2fab782baebb77dcb7bb75a0230b6d1dad4b6a10310b68d3f41b67cc9c0b6580efab639a771b5cc74f3b5b72bf7b57273e1b53a41a8b4d4f304b4b4f0b8b4a95c2eb433f8c4b3883d11b3248b32b2f6302eb2df7ac8b2b91b29b28b7570b227e630b1d5974cb114bc38b0e0cb63b0bfdb12b088540fb073630ab06e9943b0512c3ab048b0feafc9c8ceafc84582af47fc14aeec9bcaaea8734cad4311b4ad419fdead35ffe6ac94db4cac420587ac11ca64ac108321abc6697eab30ec82ab2de287ab2b63e7aa22dafa
  | 6, 0, 12 => 0xcf1f0be2ceabe5f7ce8cec50ce7a4a4dcdcd756fcd64149fcd258c51cd16c9a2ccb8f717cc3dbb03cc2be02acb6380c0cb0513fbcaf4d69fcaecfae6caacd43fcaa823b6ca8c04abca7bf45cc9d24619c9ac6cdec91589c7c8802c98c86265e5c7f84d10c7207782c71ac861c6e981c6c6a6f670c6a43d0fc62b88fcc5e4d03dc478bb7dc466ba13c450d1f8c43f63d8c3cf0d4dc3c1d1d9c3bfd471c3a85e1ec36eb50fc2d474bfc25f196dc1dc6afec125c4ecc0dc9fccc0cd472fc0c9406ac0920075c072ccddc060a091c05fca4bc036effbbf983dc5bf47d025bf2b9455befb0668beaa921bbe61d6eabe556c3cbd5ddea2bd337361bd28650fbcc21d34
  | 6, 0, 13 => 0xdea4ce9ede3b5545de167681ddd3cfb3dd9b215ddd82b20add36a1ecdcc9e4eedc999a49dc305505dc240b61dbe22eafdb9b43b0db7868cbdb6e146fdb0b4b93dad7d7dfdac61e72dab4de7ada814efcda14dabcda10753bd9930d2bd961b0c2d90874f4d8ca3eecd8b45af8d8ad2698d88a24d6d830868ad7ef799cd7b49524d72c9c9ad681d093d67e8103d59b1271d57ef694d5742b36d523c2efd51552b6d471b2bad4463646d3a9189bd25101a8d21272d6d2097ea4d1fe53fdd1f9bc49d1eae136d1e302fcd1bb8cead1a51e2fd169122dd167d17dd15349d9d1477092d10da73dd061f1fed0522678cf54d149cf352890cf2ace27cf26ea8bcf25d8b5
  | 6, 0, 14 => 0xeee874d8eec41fbbeeac3e7fee588312ee568a0cee21d76eedbe6ae6edb336d0edb2683aed5744d5ed478fb4ecc271b8ec462292ec4582deec1a34a1ebcc6885ebb11d6bebb0ed36eb9cda82eb813c55eb7d9de5eb0d1e96ea28da72e9f1f3eae9f1943be9ab169ce94cb1b9e8d8a142e8bd2e21e87825bde8662453e80a176fe803160be7f44a52e7a5b41de7772d12e7378986e69135c5e6801e89e6527f1ce5f8651ee5e915fde5c53e3ee5a9227ae5a89ed1e5599b08e4dd52a9e462aeabe4474ac7e42be8b1e3da335be3259c4ce2f0245ee2c10b79e1fd7feee19b9584e17cf3aae16df81ce1576ba8e07a6978e074a129dff5b8f9df4b62c9df247d40
  | 6, 0, 15 => 0xfa0e42d2f9d184e0f9c70b72f914bcf6f8fcbbeef8bbd628f8a75d48f86a8a06f8674b99f805289ff7fc4f19f7fa0422f7f0b3bbf77c0b91f6ea2619f6e568f1f6d11c85f6823d1af62e19c2f5fc8dcff5f92689f5f72d83f5dedc51f570d73cf524d58ef521381ff5167eacf4fecc89f4c47380f4a34db3f4871b7df46e6ac0f456485ff44d6af7f3c57bc4f39c549ff36b4bd9f328fc61f2e76726f2cb481bf2856546f26fa829f1f1943ef1c7b84af1b05e43f177fd56f1750596f15faadaf147f2cff0f66ff4f0de4580f0ccfc0ff0c84254f0c5da8aeffc3e8eefeb2d83efbab07cefb8b958efb22faaefad403aef5f6455ef3cbe7aef03246beeff7228
  | 6, 1, 0 => 0xffb11508ff9cf290feabccaafe9162b6fe8acb86fe1444fcfdf4a2a0fddfd530fdb27209fd6fe6b3fd251713fc813e75fb9bcca1fb5429c4fb2c06dafad3ffe0fa331e36fa114ba6fa10411a
  | 7, 0, 0 => 0x6b6b959068d4b130674bcee062f6038062c153d0620bd3c0612866c0612365d06058e7305f6b71805dba0bf05d82c6c05cff7de05bf0a7e05b78e4a05b2eac505ab6a77059b03a4057823330564e0a305406a460533fba6050deacb04d064d104a90eb50499b2c104715e16044067d1043f644503afd08103af162503ad58cf03a7a7ad039a82b7038c1671037a645a0360aaa70342f9cf0331cac6031029e102e42d5302d338cd02a36d9d0288edb00265ec62025ebca5025a493c02463e47023d26a30229321f0224028a01dfe0b3016dcd980167dd250166af5f012d94cb0129179e0104396600d64fc3007d1f41004e8f92004aa5ad003a955e001528ba
  | 7, 0, 1 => 0xcbb9b490c95bc360c730d3f0c6522a70c4feadd0c3025590c2d1daa0c23ba7d0c11c00d0be71cd10bd8f1a00bb9a7120b951c780b6f2f220b66943c0b61c6690b5d6d290b36b2d90b1c6bf00b0ab8450ad79ab60acc9fe20aba57dc0a9cd3050a75aa570a51d1c70a4a18090a3a77c00a3643350a2c4ac90a2984140a2632930a200d4a0a110c4c0a0eeb570a01adfb09c8d28f09baeccb09bad19109980d66094c258b093a6687090422d808c04d1d089d8c4e088ec9d5088d0f520883b66b0868b13b084a24cd0828fed70814753607fba0f207e60fd707b3764507a1618d07983db6073325e006e4120e06e0c14b06e0a38906d1977a06d133fa06cc483f
  | 7, 0, 2 => 0x13a474e11332ca0113196f651317c8ac1300569312e220cf129b11251288b0461269ac3b123727b51205153611c9fc5911b2f3431194d57e1182c6e91174cb241168de381158bc8d113c00b61138b0dd10f31c5810ee709e10c9a57610c7913810ab151e109959ad108cbea2107e292e1056c74b104dd56b10391595101ba3370fcf05c80f8e768b0f5e8c8c0f51ae2d0f4801f60f27162b0f232de10f07ff480ee65f3a0ee047db0ebcc9260e7871670e68f5ce0e5d667f0e4468b30e41de8b0e3e77060e2d6bf20e00d3cc0dea00600de616750de050250dcca99c0d6a41550d4b6ee40d31c24d0d31a8270d2f75e70d1a20270d16ec7b0d0bf7290cfdf231
  | 7, 0, 3 => 0x194a9f681948027b193bf80a1937c60519324a89191c880718fa400b18f4e10a18bc18ae18b26e2218a40cb3189eabce18917f941877b407185ae160182077a41804d3f117fa190117e17fa417bc20f017b10efc1783d36c1769b970176707ad1766a58e175df26a1747ce401740cf13172babbb17173f3b16c7550716c4ecbb16a2410f16a0d74d1682538b166c05e0166b912e165fb78c164ec6c81635ced6162259c2161b607615ef008615bf0bfb159dc5ad159b56a61571fd28151f94c7151d51991515e26114eee25d14dedea314b7c4bd148f3e3a147d503d1439308014236703141f8fdd1410a82114028fce13f3fba013ec0a3313cc75ff13ac2e7a
  | 7, 0, 4 => 0x1da432d71d7fe65b1d64beba1d64551f1d5b21981d291e511d1ff9bc1d1e19bc1d1a31a91d0c61251d0839f91ceeaed11cd2ceee1cbc6c011cb356241ca8e5581c9476741c9375ba1c8311b51c59b8491c54452b1c1284641c0feb111c0377111beeb5211bd07d241bc1ec8f1b9b06e31b8f4bc21b6db4001b67bfdb1b5aa7ce1b43497f1b36af831b23c71b1b183c0a1b0c122d1b01564c1af080381adeceda1adb9ef91ac2a53e1a9a638c1a963ce71a8db47d1a804d981a76b50e1a6c12561a4174f91a3c6d051a28899f1a21454a1a0a201f19ed676819ea89b319e4b47719dbde1c19d6e25419b45c2419a396e71984a60c19729319196926bf195e4838
  | 7, 0, 5 => 0x237396c423725fb9236bcd4e23497e70233bab092331768c231e048e2305e8be22b12ef022b0f35f22a39c5a228741b9226d7d3c22670883225227cd22272e9b2222d26421f5914321d2836121c06e8b21a0749d218b094a218a645621701c68216f8e382161cccc214d3e85213b82992118d8ca210940e420e5768320c55f8720b14afe209ff89c20892a7820814bc4206d00e3205f78db2056771b204cfb9c202b40b21ff874121fec7aff1fd910571fcf4aa11fcef5c61fc882a41fc1b3651f904b671f8bbb851f2e7fac1ea89fbe1e99e7201e9742441e82e74f1e6e6ef41e4df89f1e2f7dc81e05f2111e0058df1df5c4f81de527be1de4ce581dd9276e
  | 7, 0, 6 => 0x292cb8d42929ecdb2920d6ee291bc8c3291ab76a290a690b290449ee28f2496d28c3a7c328b7dffc2898a3ce288b90f02889e91d287632fc287085772841347c283bdc1f27ff675027f211d527d6d48b27c003a927bf8f0327b5d8e22773e4862724f3bb271e4bdc270a00fb26d06c1026c840ca26b7a5be26b4857e26a6ede5266d2ce4265099e32613f6fd25f87f7325f197ff25cc306725c7bf3b25c7b42e25c57f8825b75869259918d0258f13452566d73a25613c15255cb14a254c93602537670e2514869d2513939f2512c07025029ba324fe889724ec528724d5ba0324a4de902491f55e246a0b8a2461748c2457de7a242a74e023e95a4623bfce22
  | 7, 0, 7 => 0x2f7aeeb72f6289282f2664432ef590472eee210f2ee6a1a12eb4f9a72e80ed852e5d03c12e2cb24b2e1d7b042e1d68462e1add622de9c0a22ddbe4da2dba570b2da2fbfc2d7abe332d4d2e3b2d4ca52a2d3564552d11b3fb2d0e39ee2d0c54cc2d0b08af2cd99b922cbfb75d2cba5f7d2cafca952ca409f32c9f503b2c60eef42c5458812c13df762bf9b1622bf3edcf2bdaea362bd981bf2b8b31f12b6d142c2b6692a32b3e9fc02b351a482b3290202b170a3d2b0c54332afbe5a92ae3339f2ada82fe2ad101ba2aca669f2abf74ef2aa950482a71985b2a5af2ea2a20277c29ea1d3829e3d32f29bfe79b2961a88329481b1b294551f0293e10b42935e746
  | 7, 0, 8 => 0x3545db6c353ffe893535d36d3532e67c34ea9d8534de448634d9b7d434b3dda734aeaf2434ae4d7b3497d1de348ee9a33457b94234206ca63403b3df33f9fbdb33f6a21133b2c29e33addc96339bda72338c9ad2338a1e193384501a33641e9c333fecef332b6cf03326806b33102a5c33036e7132dfb21b32ac8e81328aacd0327951d13276ea7c326b44773229f271320f02f83209779031f3ad7631eb022d3189073030fab30230f8d5e330d3ff1530c2219f30b5147d30b1a1813092a0e2308ead5a306b06c7305ce7b3303247ff302f8f99302a0ae330108d352ff39f242ff1bf382fd90f922fd2e75e2fbca8982fb4080e2fa60ebd2fa0d4092f9ebac6
  | 7, 0, 9 => 0x3b7204a93b6671ed3b58f2743b22fa393b0ed6ec3afd18923a94329b3a9050163a8927f03a5b83583a5731083a4a02173a446c543a281b973a1fbb533a12271c3a0ecb513a046aa139f7320a39df606639d772b739bb472c399d2fed3977cb6c3970fb693950403a3922fce73910511538f9f1d038f267cf38c12eb938a459d7389c6cc93897bfdb3895e653388eec623887ec9c382d8f773827611838168c59380acf4537ccd3f03795d5fb378255a2376a4f69374100aa37223166371be02136f8386a36f2504936cc8fb136727dff36607174364722363622fc1e35d968a535cc150935c6f3cf35bdc14735937adb358f846f358ad93f358231293574f688
  | 7, 0, 10 => 0x3fa8446b3f96f1e83f73c4e33f73be233f5b35893f4a96ab3f4469d73f34bff33f0d3cfb3efb5abd3ef57a873ef2c9303ec491353ec4651c3eb194723eadf8b13e7774b13e51fe3b3e435d163e4191e33e2a98cc3e299d2e3e294fff3e2424c43e224e9b3e098a5f3e066e433e0108f43dde00c23dc089333d90aa313d71fd593d6b71c53d5db2783d51cce33d4d12c53d4a73893d35d18c3d25e7c53d1bf2473d1bc8603d0d3c6a3d084ce73cfa499c3cd54ec73c83af333c7ebbf73c7bdb083c771e663c46c9e63c2865463c1fe1e43c1d557b3c15c93d3bed95723bed92613bd23dc43bc972183bbeecf43bbb8b303b9f4fa53b879d9d3b7aa4333b7296e2
  | 7, 0, 11 => 0x451126604508ab2444efaef644eecb5944ce231c44c798e444b0b53e449e090c448b58424488eff6446609b6441595d643ff470e43f8662a43f4158c43ec44e643e12dec43c11da543bdd24743bcd98743a70ae54398ddee43852168437f917b436fcda1434d0023433f339e4320af4b430c645b4306b86b42fc4e1d42f9159c42f1942f42e47aa142e11d4e42de074342b870d0429fbbee428023ed426f3ddc4266f78e424d62df4203720541f65a4241f305b641cae48541c281c6419fa1554197cdb14177097540fed52240fd5c8940eb971d40d9ec8640d3701140ccdda640bcbb6b40b04b7940a16ab94092dffa40811af040584744403aa2ec3faa646c
  | 7, 0, 12 => 0x4b85183a4b6d7f204b665da04b5a26174b550f714b36c4a04afb27574ae58e0c4ad05e494aac3dc34a9c955e4a8e4a264a6b23fb4a07ce4749f28eb049f1948249c137dd49994e35495faea7494a6572492a2f2d48c22d9b48b7e81148b2d4b0489f703e488d5190486b9cc54860e5784860daab485e935b485d290d4804f0f947cd22e347c09368478d5981473a6d92470552fe46f3f1d646dacf1f46da305e46da15bd46d9577146b90c1f46b099304697f60b466b79634660f1af465237e9464b49344646e00c463352ca462698db461fe4234600690545f4fb8345eb319d45d1eda145c4616d45bd00e645b5059c459a7aba456cd12f4561370c451526ee
  | 7, 0, 13 => 0x5147ebfe512b4a3e51111e3b50fc801050eb246750af34d550a4ce5f50a37433508313615081680750429db5503e3f22502c43f85028bc575013ea85500480924ffb3acc4fbfe4264f5a6fd74f2bc50d4f2308104f1c75a54efa29254ee29ddf4ee201a54edbdb8e4ec079ac4ebdb7684eafe4014eac70544eaa1ddc4e94fe3a4e4273d64e31041e4e2ff7f04e10be834deb64974de987784de119ad4dce8b244db517664dada4154da171e74d2885244d09c6d74cf9641a4ce69ba94cd683a94cd3f7294cb7f0c94cb2d9fd4ca9aba14ca3de694ca0b7c64c9d082d4c89535d4c25cfc94c1021324bf3646b4bef9b8c4bd7c0734bd380b74bd2582b4b9c124d
  | 7, 0, 14 => 0x56dcf45156abf8c15695158656713ef956661dac565e118d565a3d77563a3637563267f65617558855fd7d2155f8209255eaa36555e7a0d655d9162255ca84545593c9de558871705578dba6553eb09b550f9dbf550d954954f4926e54c74ec254bb1162548e179a548cc5b55485ce8054768c98546f02b95450ce925431b23f53fa4c3e53e709ff53dc75bd53b79f14539e250653756e9b5368b9a95360be5f535d66b75359b3fb5337d3cb530dd69552fe543752f219fd52bc8da352996d67528577355281bc6d5270f6e45270ec6c52652dd5523ac82c52277d2d52084b2c51ff9fc651e1ba9751db4f1a51c5f1d451c45c5651bb968e51698b0a515b0c33
  | 7, 0, 15 => 0x5dfd04b75daf6d415d4631575d017f515d00d2a15cc01deb5caba7035c90af7e5c8704475c8048ac5c7c04cf5c46243c5c1f581b5bdbb0b35bdb091e5b8aad865b758b0b5b6d297d5b1b4a615b10def85af64afc5af1ba895aef23a75a96d7c95a910ab55a757c235a656b815a5fdbb45a5f463859f01b3a59dd40be59d8d2e559d3587659cd3ac959cb464e59bf3e135996f09f5992e51b597460c859716586594ea2b95945debb594545ac5943b1655922191e5918aad958d6963f58d3150158c2ef595862b63e585896a65813abce57f1606e57db40a8579d4d4557986259578258d0574a3c075718cd2c5710d06857106ce85702d8b156f51c3656f3747f
  | 7, 1, 0 => 0x63de931563b72ebb63ae5c0963946322637bac956376351f6358a853633cbe4b632afeaa6324045f63134f7f62ddcc1362bc2e5c62b9dcc962b94e0c62b5130262adb27b62a89ff762a0e5156265485362415fa3623567bb6230a5c1622d0e09620ebf416205d88361a7f2f161a59074618f83aa61882e806175ee9a614251e660fd5a8260fba71a60e9aef260dd91ac60d6c195609d6ba2609ba710608a602b6088d7de6088c021607e89b7605adc25603fd0126013f4555ffed7895ff7d54a5fe54eea5fdec53c5fcd3a315fc8c0095fa624535fa1c3e15f6bdcae5f66e6445f32ed555f2bf4dd5f112ad15ed1d7c75eb355125eafa1875e88f3ec5e1f8913
  | 7, 1, 1 => 0x69183bbd690e091668ff83c268fcf56368e2355b68d267d368d1099568cd9ffa68c3f13e68bee2ec68badc8d68ae8ce6689adc6a68832f49685c37af68377a7467fda5b667d6a2c867d44f0c67cd191167cc5ab667bd3c8767adb0e367a26ce8679e3ab8679b211f677efbbb67796d5c6776708767729a9d676ae4a96767de4a67539f086742a7d36722ad0067068df5670425a966f87fdc66c18c796684cbfb66824f026658320f6653f8896653a3d9664bccff664adcf26640f86d6625159d661f734e65be5a3265b5e2c8655c4e5a6555e6036539ae46652e1b4b65039c1564ec986864e38e3a64ce7728647cb2b5645c98eb64499c76643bf4796438425e
  | 7, 1, 2 => 0x6e6656486e62b4746e19f6746e09f0ed6e02eec26df716036df0fec26ded31a56deaba066dc1dc046dbfad186da936f06da8abc16da0706f6d9110bf6d72199c6d4f0de56d4541c66d129f076d1012796cfba4ef6cfa59176cee2f236cdf4af96cca26066cb455396c6b07056c453e1d6c33681b6c0ecbaf6c0b2e346bee9c076bee0e686bcc8d236bc738476ba0ff156b86d8da6b7e56f36b78b4ba6b408f3a6b2ac9b66af2f3f26ae95ce96ada9cdf6ad9b6196ad97ffd6ad837d96ac103f16a8773836a80edbd6a7bb2e16a6ad72f6a161b4269d8a4a169cae70769c1909169bc6b26699d81266991695b6986998d69658e99693978f969273a416918e240
  | 7, 1, 3 => 0x747a456a74730a657440f1177440dbf174381a627412504373d7ecdf73c1a1c173b11193739605b4737e297e736b23c9735d3d7c735a8c39734c9f76730b3a757308071d72dcd27272d87a3472d5b0c472bc21e472a64171729b2e07726be43a723af4ec722f623072285f1a71fe46de71ebea7c71afb552717fa4aa717d774a7162e77e7141ec527108289170f6156570f10bda70e8ab9670e3dc6970db175f70cd5ae470ac39d17084376f70813c8d707543f17067e71f70596b3e704a65907039e208702759d96fef05cc6fdc58a56fc2e2136f9d17036f8fc5496f53468b6f1f7e7a6eac48236e81024f6e7696f56e74d7686e73d1506e6dbd796e69c746
  | 7, 1, 4 => 0x7bde17317bcd10707bca6adf7bac4d1a7ba3efb57b9672c97b52ee217b4f5d537b43b31d7b2c7ce27b103aa87ae4f7e17ac3e1087a5ac6337a451b037a18590079c53e6079ba847279732626795b686a795921fc792ffb85791676ee790cff8978d69b6378ba6f2e789ffcfc789e7b0c789d0a56785ddb12785978f0783fe09f78204d05780206cc77f91bf477dfd53c77dbdffd77c0a3b577b942fa776f6b4e776e799377496a09773d6e78773a9c7c771e700576e3013076cdf25376bbf7e376ad33d276abcfae769ada3276832976765f42f5763e9c90761777c475c3c696759208f275825b8b75715c627563827e751601bb74f972b174e4177e748913ee
  | 7, 1, 5 => 0x81e71ca881c08e9b81be0906819c32b2819b4b0881957b358175613f81573a698128f3f3810ceb778100a06180d3e75480d3660f80b9b8ab80b8c97c80b18522808514b7806c43f780458e7c803f3d538032d812803070bd80231ba07ff6ec087ff196777fa9ffa17fa56e0e7f6c93bd7f348d087f2619507f1dbf9e7f18940b7f0a5d3b7eee8de77e9e811e7e9642097e687d3c7e5cb7727e4c27237dfdf9327dec58af7ddb18c17dcdede77dc7732a7dbbec7d7d674d9d7d4b8dba7d4ae48d7d4a419d7d4548fb7d42df457cfc430d7cf9986b7ce68dd97cbd2ffa7ca027e27c9f7e7c7c9266867c8d51b07c85f1297c7fc2207c723b297c2e85b57c0c1826
  | 7, 1, 6 => 0x894e9e1a891c294589148cd388b4f3ae88a143d8888486d18869664f885bec338856635b8808037987c5705387a85dfc87a82a1f874a584a87410439873c288b873771588726336286bb989c869a8951868c39b5868b04e4865a602686519f6a864345b3860993d585ed815585d2e6f085c3ded685c0c0e685b1d8b3858b8dff85721f6a85037d4084f9b78a84f3169584eb872d84d2c17584b1beab8488c06e8458ec9584135e95840206a983f73f8a83e93e7583cbd3c083bf71ac83b31a7d8394a9d48384e7c18369a80983665084833c7e9483324e8f8315c732830f3b4183079e2782c9e5be82b6236a82b2a86082b0af5c828f2ba38236f38f81e87e93
  | 7, 1, 7 => 0x8e0f90388e032ec18de24ce58dd424298db72a9c8db48e2e8d9ceb668d9af2608d8425078d8031598d792ab98d7869e68d2a939d8ce045cb8cd297818ccd0a3a8cc44cce8cbb13f68cb905758c815e948c7cbb378c50b03d8c491a168c488a708c2048b48bffb89a8bfbe3e68be212a78bd6858c8bd60d088bc8a39f8ba622f48ba351498ba1dbf28b933bf28b90331e8b7b06cc8b793b1c8b69ff958b67488a8b55b5f88b4228558b34a47b8b33bd8c8b22ec5c8afce0bc8af69d508ac1d3288aaa79df8a9ff1b68a7d11458a7a9db88a7700498a35f35b8a31a9ec8a30541f8a1656d289dd480289c7447a89c21aea89bf6807899478738952d794894fa878
  | 7, 1, 8 => 0x934eabff9340ec7093384e8a9318279892e53e3792e07c9f92ddd80692be588f927712139274a528923619c09231eb73922be147920cbe9291f8b16591ecb7d991ea244691e1923691d7069f91b813ea91b41eab9180cfe5915ed3409143acf2912e86b9911fadd990ff85ea90dca57990a6310190943691908d554b90830544908180149061c1d39061903f905e9fa3905c681f9036c11c900e35ef9001ea248ff96af68fe2ac528facd3798f912a818f8b65ae8f2f8aec8f03ca238ef4719a8ef363738ef1cae28ee001eb8edc438c8ed225db8eb6e2ca8e6b87e68e6b60fe8e6a85208e6302838e61529c8e5725bd8e4b49138e3d634f8e3270a98e1f01db
  | 7, 1, 9 => 0x98bce30c9889b7f1986e80b79849c5b8984429e79839f57d9826567b9811f11d9811ba83980f33cf97e4107297e3684197d861f897d1cea797c4975d97bb039a97956ff4974a5a399737905a9723cc68971d87a996fe905796fce5c696d72ef996d0132196a90ab6967edfc89677bd2a965c958996305e109608812995dd264195da1b149583352e956f07ff956ace78955cb4e89556175c9553e2e295522fc3954c1bfa954a07bc951eb3b894ffe11f94f20c5594e8795694e2b7a694d07ba694aff83a949a11839492ddb29487229194726a869466b5f39437159c940baf2d93cf9b3b93a98caf939c8143939314a6938d511f936a0d269353153f934ff48a
  | 7, 1, 10 => 0x9e276e1e9e17be369deb9d439dd975b99dcf7e389dc17d239d72802a9d5d266f9d57fc609d4e037f9d3f16bb9d3e8f329d3df8079d1c0c8f9d14bd429d12b9ba9cf995a19cee05e09ce503cd9cb659e29ca8e6789ca6bdbc9ca607d99c926e6c9c6b6d939c0945a09c029e899bfb0ed09bea9eb89be91c129be3dfda9bc071759ba8ca2e9b9703f59b52b2589b4d69079b49f8709b3cd8b89b345e369b2fddca9b2df4969b2422a99b03d58e9b0132a19aeb76b19abb768e9ab8455a9aac9e129a67f3379a4707359a31aaa69a1dcd2a9a1cefb899d1a7bd9996391b99823e4f9944d26b992e20c898f5fe4c98e1de9b98df764f98c6cc9598c6984898c30bb0
  | 7, 1, 11 => 0xa4a77657a4897a7ca46a78e5a4626ff5a4456160a42ac53aa40e3209a3f6d802a3e70f89a3db5ae4a3b74bbea3b4a789a3a12717a39c9fa5a3731f65a34e91ada33be304a333f748a317fe4ba3086daba2878a77a26ac316a245ca46a241a4fda23ed8b4a23bc818a1c22db6a1b636a0a1a22f76a1554572a14a8c27a14a4ecda10eac17a104f34fa0f73e1fa0e5f819a0e4074da0e18795a0a58af5a09d03cba093d74aa0855b69a06bbb55a03a73baa02300249feaa7b29fe1d2839f8d4af99f6c35d39f63ccad9f5c29a69f219ef39f1dec7a9ed653409e7a94da9e7937709e6f30de9e68ddc59e5912e49e4ff7719e3bb3879e3660239e2ebe079e2dbe58
  | 7, 1, 12 => 0xac203c81ac12f907ac08012baba7945fab627818aa90bc90aa8ba3f5aa820f7faa6baa8ba9ffdafca9e94dbea9d8de5ca9c34916a9b4fe63a99fc019a9925c3da9536d8da930a090a929b3f7a8d0e661a8af8e51a86f31f2a862bd1da84a90f6a83da742a837e8f9a8255610a82101fba80b8a37a7de7870a7dcea2da7db6d6fa7a821cda7916477a78974f5a77db8c7a778c454a76b4f4da76199bca748a056a742c4d9a73369e3a721479da7153f15a7070867a7021b01a6bea662a6b0199ca6ae84b7a6a2fb5ea697cd48a66aaf8fa63f4fafa6375980a6365dcfa5ae4bb6a596fabaa5904268a57de989a5731149a54714f0a53f8738a4f612fca4d35194
  | 7, 1, 13 => 0xb2a312aab299699db28cc84eb275c1e6b274a0a9b2701879b26a3914b23ccd8fb238fd55b2110892b20e28b8b1ecd252b1ea3e9eb1b90588b1b43169b1a60c98b19e29acb1944398b1838f47b177d426b16daea2b165918ab1514e89b140fa6bb12db808b11cca9ab1022d5cb0e0351cb0c810ccb0b8d335b03e1077b03b1c5fafd5efccafa392a4af770d74af6de679af6a54ceaf3e8548af3327ccaf2bc6ccaf2022c0af0c0464aeec9bcaaee7910eaedd696eaed822e5aec114e0aeb8f7e5ae98bf4cae8056fcae7a07f8ae45eeb5ae15c46cae0bcf42adf473f8ada685f3ad74bff1ad57fe49ad1760b6ad09eef0acbf819aaca5b365ac7e3138ac64da7b
  | 7, 1, 14 => 0xb81c86e6b81852e2b802dc33b800ff14b7d88107b7c51bbdb7a8f6efb7794bf6b758a4ccb74e163fb749d50ab737b8cab732b815b73008afb72f4b60b6ff2650b6e02c80b6b74dc0b6b24b4fb6aacb56b6967739b63ff386b63e8ff7b63d2de1b6358400b5e1844eb5e0fc76b5d34d7eb5ca4c10b5c668b8b5b77e2ab5b461f1b5902909b554a760b53ea0b5b5170810b5151766b4f848e5b4d3a14db4aaf078b492876eb4881007b4826f84b47e588cb46b6fb3b4659c05b443860bb4265a72b4122ae2b401dacfb3d27f62b390f841b36a5ba6b3686ebfb3562109b34d471eb34b9406b342b37db320141eb31bd1c5b3124904b2f42647b2db01a9b2cbded0
  | 7, 1, 15 => 0xbde7efb4bde6d522bdbc8780bdb59ca2bdad5056bda5ba88bd7b2bf6bd5c6ceabd281e83bd26b484bcf03cf9bce0ee17bcd904bbbcbd54e4bc7607b4bc5ae0bebc4f4a74bc43a1fbbc1d1430bc1a299ebc0a4da8bbf2c6b6bbe6e79bbbc7133abbbb2494bb887e76bb7a6e24bb793359bb6714abbb5cd4dfbb49c479bb47860fbb35131dbaf14e5fbac6ac71baa1d6c5ba6ddb7aba47a138ba2fc850ba1aaad3ba084ee9b9fb3ed2b9f6f76eb9b4923ab9a82248b99fd817b98d4c4eb9858bbbb97b98a3b95c1f28b94caba9b9238bb6b911a0c1b9114bf3b8fa157bb8db78a7b8ad38fab8a1ca09b8997bc3b88ec8b7b87a7005b86dcafcb85605a0b83c6ce3
  | 7, 2, 0 => 0xc38d3d11c38bd864c37604d3c36d5f1bc35cbd48c35bf766c34bf7b5c33be1ccc3291744c3101f35c2f3dd45c2a65918c26e9b1ec264289fc22b236ac21450dec1fd94bec1e67121c1d10fbdc1a671b8c18ac36bc16eae9ec158b17ac1522c87c1438dfbc13044c8c124aa0ac11b76cfc10c93d2c0e46e0dc0df4715c0c437dac0c3705dc0a7fd53c091d8acc061f6c4c0452260c0324461c02871dec0222c96c015f1d7c00cfa25bfea19b4bfe69374bfcca165bfb0bb14bf9fe90cbf964610bf8928b0bf653cc4bf52f044bf5270e8bf51c55bbf2fb475bf1f539ebf12c69abf033fcebec15d88beac5dc1be9eafcfbe937088be4929dbbe3a591bbe159bfb
  | 7, 2, 1 => 0xcc2a050dcbcb633acb914436cb82d94acb7d4e04cb549467cb5012d4cb025607cac05273ca43b4e2ca06b25cca04774ec9fba24bc9c45eccc9b79dfec9afe55ec9ac6cdec99664fac9901028c974095fc93615f1c90b667ac8fd7c87c8f8b2c0c8dde1c9c87d6749c87c4895c861da35c85f00d7c8525effc85246a6c84dd6fcc7e69b45c7cdf583c7b58e37c7a0b93ec76aca4fc72a8082c722c4afc6d9a3e1c6cf4479c6af14d6c69e7be3c66c1ee5c629c73fc5f87b2fc5d82793c5c197f6c5974a78c58dfe2bc57b818dc55fe387c53b428bc532c1fdc5093225c4f17c22c4d489a9c4cf2a05c4bc0901c46975e9c41dae32c405f0aac3f04a81c3aa5cb7
  | 7, 2, 2 => 0xd257e8b9d24558f5d22f524ad22e444ed227a095d21dd0abd1d4b423d1c7e360d1bac628d1a41867d1967357d194a595d18f4277d1644545d130e37ad12654edd11f33d7d11c0b79d10ff778d0d31777d0cb6bfed06fa9abd062548ed055369fd01d5aded008a737d00843b7d0042302cff609b7cfe93710cfb93b24cfb83305cf73c5f6cf65523ecf64937bcf422f75cf409521cef553f0ceef46becee27a34cedaf033ce9c234ace84f52dce6b0b63ce43ae61ce07748ecd9bd94dcd66305ecd52d7cdcd3b7bfbcd330f57cd2585cccd18a10acd10f587ccffafb3cce6e03eccd81dcccccc8a9eccc52a17cc924b33cc8df8c6cc5e9a47cc5b0663cc54468c
  | 7, 2, 3 => 0xd80e38fad808765ed804a941d7f5b952d7e7ef97d7c3a15ed7c02e62d7899138d770178fd75e8d0fd734ab98d719f753d71460e3d6baf7edd6b7954cd6b0802ad6a95e7cd6a543cfd6a04de8d698d3ddd6951e9fd6827ea1d632e366d62c5f14d60e4952d5e8a824d5e6dcbdd5e404bfd5925408d57f7a4cd555b7f7d5512cccd5477b7ed5220327d509cd6ed4f171c4d4f0f799d4468e80d441c802d43a869fd40806fed3f88ffed3e45aa5d3d3e2c2d3cbe778d3c5c492d3a8e0f7d3a2fce4d3a103ded39e3e39d388e184d37fe0b5d379eceed36d52f2d35d4250d3598fafd3571d07d347bebcd338bdb8d330a51bd32d5babd31e59f0d2d79b92d2d4b27b
  | 7, 2, 4 => 0xde4f6a22de49630fde40e3d7de3e0348de25f21addde2f58ddb45ffadd31dd94dd2c73b5dd29ad5edd27bf43dd22f5f6dd1f7eb9dcf65b6edcc898cddcae849bdc79da45dc57a0d0dc507f22dc46d9ccdc15be7adc0d6e19dc018a2adbff3966dbaaaeb5dba90328dba270bddb9bc750db94eee6db3369b7db27b5cbdaf3b57ddadec81adabcacbbdab95c9ddaaf4034da803c01da70e2dada61dd2cda2fc246da2eb777da0a530ad9e0ee8ed9d5bdd0d9d3059ed9c9b650d9a4b253d98f9349d96b5e00d95402cdd93cbd2cd8f816a5d8efac19d8ed43cdd8e90a6ad8d69c0bd8c624d8d8c3bfbfd8a89667d89dfb22d8961c4ad869e4eed857c640d82ac424
  | 7, 2, 5 => 0xe38f2d78e37f5dabe34db855e34dadace3487461e3412cc1e33d926de32ad7e4e3247725e31ed1ebe31c0ee9e3106e12e30df211e2f85ad0e2f59de5e2d452cfe2d0f16ee2b96760e277a43ce27552aee23a18e3e2314fc8e2293bbfe1f74cd8e1f35799e1edd638e1e4d452e1df1b87e1d8c22ce1acba96e19b35e4e17cf3aae1785573e146d760e1410c7ae0addcd6e08ef68ee08c0277e0756c61e0528bf0e02e78d6e01d51f1dfeff946dfe6b977dfdfc5dedfdb1714dfce52b2dfb96348dfacc4d2df99d6a4df8942cadf739c23df3afb3adf382235df138139deeb28eddec9210cdec7c43cdea768b3dea4ce9edea259fcdea08b8ade996fb2de53bb01
  | 7, 2, 6 => 0xe9840b59e97f9331e975ef70e9566778e93d90ece935373ae915f6bce9060583e8e77ad7e8bab8e2e8b32ee1e8a202a5e88d9bf5e881f5cbe86ee786e85d33dbe80b65fce803d04be7f44a52e7e7ce24e7e3af24e7deeac6e7bc1e00e7baf5ffe731742de7311744e72b167be6ffbb90e6ed781be6e875efe6c9bcbee6b6f618e69b64dce698fc90e666e665e651e520e6334511e626c786e6195402e5fdd2f8e5f93c5de5f2c308e5e191b6e5b161a2e586e684e58377c9e56e18dee5465ba0e542f83be5423ef7e5419b8be529538ce521d0ffe4eabceae4dc164be4a8a4cbe4a63fcce46f7636e46f4b18e4634e0fe45de151e400b320e3e78eb3e3b25197
  | 7, 2, 7 => 0xf0296f4df0210b71f015890befed77cfefea5e8cefdf8af1efb87663efa50aa1efa3059bef95be8def57b8faef335fc1ef2c4c96eee2b68feed068a8ee91d2c2ee77e148ee340c20ee12c54dee04b134ee00b611eddbee4dedd9858fedc3c90ced7dc820ed7b3b92ed2d3eceed27dc13ed26731fed105b43ed08e3c9ecf958ccecf6989eece05157ecb91f5fec99ef6dec61ae47ec55144bec41d777ec309f4aec1d97a3ec0790f8ebe60585eb9e1ad9eb9e1840eb9304d6eb7e1f2aeb650627eb5bbcf8eb58a678eb406b8feb3c7bf6eadc660dead8cca8ead56621eac36ef1eaa78c21ea9c8c53ea5d0618e9e4b65be9e08265e9d791d3e9c1773de9aaf229
  | 7, 2, 8 => 0xf63f1f25f635a2a4f62fcd0bf5ed84a4f5dbf51af5c74da0f5c1194ff5b4f1e4f58eacb7f51b75b9f4c241aef4b303e2f4a423e9f48e01d5f48a3216f478ee65f44d6af7f443b5bbf42435d0f41c0488f40a6ed4f4081177f3f82decf3a8a818f38d6f6cf3733036f37209e4f367d1f7f2f21463f2ccc65bf2c6f385f2a2d6cff280ddebf242239cf23b1858f22de2fdf21bf636f1aa4a0df1784439f15bb8cef1480d4bf147f2cff1448c39f136cbbdf1327997f11de759f11cb99bf1167821f100029ef0d31038f0c49457f0baa007f0a863e1f0a4ef4bf091b573f08f38a7f07d827df0799319f05e0487f04f03a7f04df3e5f047ce9cf041e202f04110b8
  | 7, 2, 9 => 0xfcc3aa8ffcaa14ddfc8e6f52fc8be65dfc5b4afdfc34fec9fc019be2fbfa800afbc1bc8dfb98b5bbfb870272fb84f944fb2bfdb8fb16a3affaf397f8faef58b7faeb1bb2fab6ff8cfaa5118ffa9321d7fa4e962dfa25ad8bfa0187f4f9c44b15f9b62ee3f9b18f7af98072dbf964d1c6f96395eff956e2e6f9552142f94130b7f92dd199f9208f7cf880c6d4f833943df82ca004f82530ccf821a1bdf81aa65df81733abf7fee982f7ef4ae1f7c46fa3f7813a1af77c0b91f7712f20f768559bf75ba0adf72ec109f72c971cf7229d44f6fb34a4f6f4507cf6da13f8f6b4fa10f6b42a57f6a17f76f68e4a3df6825476f660409df64a1ac2f6436489f642186c
  | 7, 2, 10 => 0xffff0634fffea3a6ffc7aef9ffb39eb1ffaa18f5ff926020ff837588ff58e3f3ff46578cff22015dfefe038cfef8a7f1feb839bafe971ab2fe7e7e7afe770e46fe69f639fe3788f5fdeaed64fde8e296fd9d02e8fd90ee05fd8afa16fd7dbe82fd676c26fd536d0dfd50c364fd3c276cfd1304b1fd0dd52afcef1659fcecae0dfcdf1884
  | 8, 0, 0 => 0x194eea6e193f069f1917953718ed5c0818daafeb18097fbf17c028151742223f174164871703b38d169f5cd9167ebc1d15dadce1155b070714ffc7cb14f312d414c25be7147be17a147387c8144456111439cce4134220d9133606d912a155e412a036a6126f593f11f546a611b6e00f116093e11157a4901106cdc710bcd6ce10af5719106602d20f970d4b0f1c517e0ecd7e060e9187990e62c7b30db3a33c0d4c5b2b0d359d660cd29d6b0cc838990c5bdf350b198ec00b15b6280a9f6c0309efeca509dedc18085dcf4707f0d02407e6419707a3890607852a5a0769545207540f0806940e5505af33680544cdf604be9b5d03e57276020fff7e01c0cf2f
  | 8, 0, 1 => 0x3d0bb5b13d084ce73cc117773c79d3023c05e1c63b6b92a33a9cdd1a3a97ffb8392a12193889bf72386dc675382614fb37a8b67b36f7f7a036a016f7363bc04335db239335a8333934f9221f34bca48e33c0c90032db8bcc3265f79931b30d7c315f0dca3150d6fa313507a630a6803d30a331313069bd2d3002663c2f1583e82ee5f83b2eb8b4e82dbb214e2d6782ad2ceb381e2c33b3742b5379482b384c9528a5bcb427a4a978273fec70250036df23fc0e4422805bc72205790020bd10b42085ba6f204508b51feb40ca1f96edc61f505e561eb180c41da0f8bb1d22f2e51c1160c61c02e4e51b5f5bff1b28af1a1ae156291a44266019959b0d196926bf
  | 8, 0, 2 => 0x59428c4e58652e3d57c4634856cff38d56a65876567ab1f4567057c4562852a055b00d5b555e780a5514da2a545907f853fc1e2653d94335533db7de533d435d532b31af52c6dafb52b2351451bfab7251a2f1b550a840dd509f8ca35046c4424f01e97c4ef5be6c4eb1e7524dcff4e94d2e4be94cae6cf64c8d80f44b8b4c2a4b43cfa04b0d46544a6cd03a4a0c99e049d837ae490e14d748be36e948a30f48470ecdb246d9577146cd9c50465f78f8452bb7f643fdcee443cfd02243cb072843a4cbbe436b49e542ed440f42a809fe424b4c73414c6349412582f040f62fdf409e34a43fe16c1f3fd242ec3f521ef63f0ac68d3d9f9c853d9cd9ed3d41059b
  | 8, 0, 3 => 0x7985c0977937382478e4f5a2779b444e770282c076e1ad9c7673e45e7663a7c675b7bbb07584e2737530df3e749a204b7414985b72f58c2c7278be2071cfa26f70e422b07082196870227bd66f36b6b86ee55b736ea16f056e3ca8b56d42739e6bfb0bf96bf2d3266b58cb236b3d020a6af4746f6a314b076a0e5a8068866d45685bd80f67a3692b67851a7467360e8c6716b47367108e52664b1a33655e0be164bb1a686438425e63ff7f4763e020e463dabd576371691462a89ff7619f6a456131850560c081b760965ffb604bbc7e5fecffb25ebd6c475e6214035dfdbd4f5db7a25f5c6c86d75c0fa18f5bf8a09c5b919bb95b1760205a9a33625a910ab5
  | 8, 0, 4 => 0x93080b4c92e1305c9291ef96928a0576923c767591505196906c6bd9903af60b900cc7b68ffad9b98f66a91b8f0252678ea1b5b78e96f8e18e5c135a8e3118c78d29a2818cb80d3c8ca877188c5ba5cf8c53b6888b992cb38b1d15ca8ae474e18969c355895dd9a18911bc2488f2ca4188c8f86088c3fb8587abe572877f470c86bb2776868841c1861a5c8185e77d9d85b3ccb1857f3777855c728484d0ab2d84013fe7836a9b7e824f20f6824ebd7681a2fbbd816c4ed8813bcdaf8129707a8128f3f38124f5e78112770580067e947fbb0c1d7f82a65d7f1e4fa97e67abc27dd7bdf57d57e2b57c1b05047b4367897a98c0657a51c3047a076bf279fc07f6
  | 8, 0, 5 => 0xab75d046ab7128a0ab2b8525aa70fe3da92e1f67a8fdcabba8fa3d0ba8f48ae1a8dc75baa889de48a888922ba7de7870a7787976a7420870a708bb6da64e8b36a61c3eeda5ef21d7a54e664ba549f6c7a52b97c7a4c9dd97a451de4ea3d3d878a2729855a26835d3a203df1fa1eb8460a1ea2ffda1a94993a185d949a184c90da156df129f9b20929f36c9de9e9b8e0a9df24a1a9dd97e959dc6e8679d3b975e9cee05e09c6b500d9c26fc249c08a19f9bed4a379bca85189ba44aeb9b4c7f429b0132a19a8d182a9a80d3c49a02cdee98fd6fd798a7fe4397b3be83979476b8960bbbd995f9626495b97c50956af0e495546bd09477c98794213f909406f9df
  | 8, 0, 6 => 0xcad7f953cab0ad57ca5896e9ca1e5d15c9ad816cc98e47ffc92fe007c8bac5fac88323f1c7fd48dcc77d5d96c74aa3c2c6579413c638f60bc613a061c5eaeea0c5af49adc58557c3c5547d17c5164b1ec2621cf6c2157f87c1ad5ec7c1645d2cc088584ac026c9e4c02126d4c016ba9bbfa320febf75efa6be769f18be2c3e52bdb79b24bd541193baa031c9ba7a062eba53eca2ba421ab1b9fc0058b9c192a0b981579cb806c79fb800f691b7f96484b7ba7b55b7acf0edb6b375dab5f481dbb51da5ecb41a71fab1d8d9dfb1447d4bb0b06ff8af973d23af1d0a4eae5dd3faae08364cadcd7c31ada97aa9ad1f9a1cacab5189abf80939aba98afbab858806
  | 8, 0, 7 => 0xeb7d2b56eb5881baeb500845eb406b8feb1c83beeade399aea36d74ae9f6ba3be9877a69e8a9e5dbe6a45857e604fcffe5563db7e3cc9162e3a3bb46e33f4fa2e27df1c3e2760958e0b0bd65deae0fc1de2570bcddf5fcc6ddb2f137dbff73e2db747efcdab6ff36da067d68da025fd3d99ad6ebd7a32b09d7593a2fd753c3f4d7000549d69e5019d5be2d13d58f793dd519e096d5053b33d4b4a79ed45050ead3ba0645d35f5289d2e6725bd2c7c583d271ba71d23eabb7d175aa0ed111535ad0bc3a17d0ab1f49d09be3c2cf7791e2cf54f589cef2f817cedaf033ceca0d03ce63f497ce16f6e3cd9702facd7d2942cccd458fcc2257dbcb78c448cb41d630
  | 8, 0, 8 => 0xff652815ff123350fe5a0e72fdf7bd66fddc089cfc4e4806fc453af5fb8cf931fb1f7172fabb6945fab21684faa3a2ccf879cc89f8037aa5f7fa7a3ef7e5a0b6f6b00b97f6a010b9f63e7977f5b49804f542c7dcf4ed8e48f4da989ff4b6683ef452118af42e45c1f3f2f90df3c7c4c5f303e5cdf29f8f19f26d989ff1de1c4af1dccc71f1af9c79f179c596f13196a3f0715766f04782b3ef2e9b0feee28738ee18b783edb87e68edacebaced070007ed03ec8beccf062fecc677f9ec85e6b5ec6e9556ec663512ec4ae460
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xc91020000032440800000c91010000032440800000c9102
  | 5, 0, 0 => 0x324408001548020a26514304c3400000c91020010932483400000c91020000032440400200812040000032440400424c920d26514304c3400000c91020000020443800000c910115041304c1000000c910200000324404000010d11700000324408d5204803040000041042c000010d11700000324408002550c20d000002044380010041204104d5100c28000008110e30515100c1000424c920b00000434450000010410b
  | 5, 0, 1 => 0xc1454803040010932482c813548030a0000030443400424c920b204d5200c2914454c1304204d5200c2800000c91020000032440800424c920b
  | 6, 0, 0 => 0x30485210c10003548020a15055028c10000000e10d10440028c10120080630400000018460d40480230400914204c10c1054843040000001842c0e4544030400000414428000000210b0000000842c003548020a0000001842c0a058c13040000003842c000540e20400000018428c10180a3040000004846000000121180000000842c02028123040000042442cd90588530400000104429080590930421016214c1041058c1304
  | 6, 0, 1 => 0x10416304c10c11040630400000018434062550030436414018c10000000610b03841100c10000000e10b21415210c10c104802304000c1018810000180220a000d51008280a3550030400041100810000000611815041304c10000000611830485104c1000001011180000001842c000001210b0000000842c000001210b40500018c10004150420a414c1104c101a1548030421415210c100635500304001151008100e25500304
  | 6, 0, 2 => 0x21415210c10000001210b068d4214c10000001211830415210c10001548020a0000041042d05305043040000003842c004000a20441415410c10000000e10d0000021446012058c130430416104c10000000610d00000018434c14508130430415420c10000000210d0000041042c00001011180000000842c0000101118000d5200828000000e10b000d5400828060381230430402018c1000104402040000003842c000281220a
  | 6, 0, 3 => 0xa038811094200230400002018828000010410b00000204438000000210b028d5400c10000010410b01915200c10000001210d21484048c10000010410b00000048434000000210b06514210c10d42108530442115214c100e254403040000001842c000000610b0000001842c000000e10b36085210c10000081220a0000001842d092510130400000028460000000210b00000304434000000e10d0000000842c000000610a
  | 6, 0, 4 => 0x3895100c11014000a30400000018428000000e10d06895100c100a3550030430455008c1085058843040000004846000100412040000004842c120080a30400816304c1000000c910b0000003842c000010111800006028810852100230400000018460000000610b018d5200c10c10584130403855200c100e0180a30410440048c10000000610b00000018434143040630400000028434c101812304000003044341a35500304
  | 6, 0, 5 => 0x1842c00000c110d30441028c10000000611800000028428000000610d00105410828000000610b06855400c10000001210b03855400c101a4544030406915200c101a45440304000c1028810000000a118000020488280a454c43040000a008828004508120a45080204c10000000610b00000038434000000210b02855200c10000000a1180000001842800000c110d028d5100c10000080620a0000041042c1a15480304
  | 6, 0, 6 => 0x180a048c101a355003040000030443400000121180000001842c0e255003040000042442cd90590530400000008434000000610b0000001842c0a155003040000002842c000000210b0000001842c06354803040000004842c0e1548030400000018460000000e10d204d5200c29081550030400000204438000010410b0000a0488280625440304000000484340a03812304104d5100c28c10080a30400000204438000010d117
  | 6, 0, 7 => 0x4885210c1000000c910b00002018828000001210a03806048c10c1028123040000004846000305002040000001846105410023040000001842c000001210b00914204c10000080a20a04895100c1000000c110d0000001842c0a45480304000000484348421402304064d4214c1105055043040011430481000000c110d0000e048810000001210b028d5100c10d4018023040000041042c003044120421016214c100025500204
  | 6, 0, 8 => 0x4842c85450813040000003842c000001210b04855200c10000000611800000404460000001210b0000001842d00059013040000001842c003048020400000204438000000610b0000003842c0a3548030410041038c10000010d1170000001842d18204803040000004842cc115480304424c1420c10000000210b00006048810000000e10b0000004842c000000610b00000038434000001210b00000304434000000610d
  | 6, 0, 9 => 0x18434000000610b42016424c10003550020400000204438000000a10b10440038c10000000a118000d4414810000000610b30485104c100a4544030430402048c100a054c430401915200c10000000610b36416414c10c11041230402855200c10000010d117000000484341235440304160c1104c10c1214843040000042442c000080a20a00000434460003041220400000028428000081220a35006008c10c105484304
  | 6, 0, 10 => 0x46416204c10000000610b00000008434140540a30400000028460000000a11830416104c10000001210b25494304c10000000e10b10440028c100a15500304204d5200c28000001210b00000028428000001210b00000404460000010410b00000018428000000a10b0000004842cc14548030400000204438000001210d00115200828000000e10b204d5200c28000001210b0011520081000450c120d204d5200c28812000e304
  | 6, 0, 11 => 0x4895100c101a25500304000003044348545081304000000184340e0281230400000028460000280620a0000001842c000000210b000d520082806255003040000043445cc10550430401915100c1000000c110d0000004842c000280620a00000048434004250820a00000018435090550830400000018434000000210b068d5100c10000008110e01815038c1084058853043500a008c1081200063040000000842c003550020a
  | 6, 0, 12 => 0x3914204c1000000c110d018d5200c10000000a10b00806038c11084548530400816304c10d40280230400000304434000000210b00000008428000000e10b0000003842cd90588530425494304c10000010111821494104c10003550421800002048828000000a10a0000000842c0a15500304068d5200c100000101118048d5200c10000010910b0180a038c10002148420a0000004842c00000c110d0000a048810000000210b
  | 6, 0, 13 => 0x484340e2550030410440028c10004544020400085210828000000e10d00000304434003510520400000304434000000a10a21484008c10064508130430406028c10411001230446454028c10d90588530400000018434000000610b00006028828000001210d26454048c10000000e10b41504038c10024508130404895100c1000000c110d00000304434003544020a42508008c10413544030a10041028c101215480304
  | 6, 0, 14 => 0x4842c000000e10410415420c10850548430400114304810000000210b000001004100a4544030406855400c10000000210b0000004842c000001210b0000000842d053050430406915200c10000081220a06915100c10000000e10b15454304c11142008130430514204c10d40480230402815038c10000000210b414c1104c10063500230430402018c10000000610b00000430434121548030406895100c1000000c910d
  | 6, 0, 15 => 0x10041048c1006028123040000001842c00000c910203915200c10000000e10b0000001841000000c910b0000000842c000001210b00000304434d4048023040009510082800000c110d04806038c10000000210b03914204c10000000a11800081200810c10550830400000324408000000610b0000001842cd90588530403881200c10000001211830441028c10000000210a0000003843406058c130430441018c100625500304
  | 6, 1, 0 => 0x200428000001210a00806028c10000280220a00000018434000010410b00000048460000000610b00055200828000000610b01915200c10000000611801895400c10000000210b028d5100c101a355003040000040446000000c110d0000004842c000001210b01914204c111420081304028d5200c10980584030400000304434000000610a0000004842c143040630430406104c10020280e3040000001842c000000a10b
  | 6, 1, 1 => 0x45115028c100e0080630406915200c10c10080a304001014008281a2544030441016414c10854508130400000310434000000a118018d5400c10000000611810016104c1012104403040000000842c000000210b04815038c10000180a20a41504028c10812001230440016404c1000450c120d21484008c10000010111802914204c10c10480630400002038810000000611830514204c10c1055083040000001842c004504120a
  | 6, 1, 2 => 0x1054108100a058c130400000028428c11040a304068d5200c1000200812040000000842c1a155003040000001846000450812040000001842c000000e10b4140e410c10000008110e30441048c1000000851180000003842cc9250c130442508038c100e450813040000201881019351053040000001842c854508130400055400828000010d1180000001842c00000c110d000003044340000101118028d4008c108005881304
  | 6, 1, 3 => 0x48d5100c110905508304424c1420c10000000e10b00000028428000000210b0000000842c00058c120420480018c10000010111846416204c10000000e118048d5200c10140540a30446414214c10000000610b0000001842cd9059053040080e048c10813548030a104d5100c28000000210b0000004842c120280e3040000001842c00000c910d42508018c10852100e304000002144280030402204001152008280000002118
  | 6, 1, 4 => 0x18434c10081230400000018434c10480a30430414018c10850548430400000028460000181220a30485210c10541540a30400115100828c1054843040000001842c802040e30406895400c10000001211800000324408023544030402915200c10000000a1180000001842c000000210b00806048c10000001210d04806028c1006058c13040000004842c000001210b000000384340a4508130403915100c1041058c1304
  | 6, 1, 5 => 0x414c1104c10000000610d04816304c1000000c110d00000404460000000610b0000202881058304413040000004842c000001210d21085038c1000000c110d0000002842800000061180000001842c0e0080a30420081018c100a3550030400000018460000000a11800000404460000000e10b0000032440800000c110d0000001842c811548030430406028c10d90590530421494104c10c121441304048d4008c10000000a118
  | 6, 1, 6 => 0x30415420c10000000210d0000030443400150c120435084214c1114454c130403895100c10000000610b00000048434000010910b0000004841006450813040000602882859350803040000001842c000000a10b30441018c10002550c20d000d5400810812000e30430416104c1000450c120d30412104c10000010410b0000a048828002008120400000324404000004110a00000404460d4411053040000003842c000010910d
  | 6, 1, 7 => 0x855200c1000000121180000001842c0000080104018d5200c10000180a20a03855200c10000000e10b30415410c10020281230400000008461014000e304001094208100a058c13040000041042c000001210b4240e420c105830441304068d5100c1000001001040000001842c00001011180000000842cc12108530420480018c10000000210d21514204c10140540a3040000003842c81454803040000000842c000001210a
  | 6, 1, 8 => 0x3855400c10020180e30400081200810813548030a00000048434000001210b0000032442d190588130410416304c1000008122040000001843485250413040000000842c0a354403040000004842c0e0081230440500018c10000000211800085210810000080620a06855200c10000000e10b00000018434d44110530402915100c10c1018123040000a0488280e2148430400000018460c12144130442415420c101a25500304
  | 6, 1, 9 => 0x20480048c10000000a10b35006008c1109251013040000001842c0a4508130400000018434002550020a30441028c1002454803040000004842c000000210b00806028c1105055043040000004842c0e454803040000003842c000000e10b00041100828002048020a000d5100810000000a11800000404460c10550430400000404460c12144130435084214c10d8008063040000000842c000000610d42415420c10000000610b
  | 6, 1, 10 => 0x3842c000000210d46416204c10000000e11800006048828000000210b15454304c100e4508130400000404460000010d1170000040446012058c130430402018c10000010910d20016204c10000000e10b00000304435144540a30401915200c10000000610d21484048c10000000210b41016414c10000004110a00000304434000000210d10016104c10000080620a000d4214810000000610b41504028c10000010410b
  | 6, 1, 11 => 0x95100810000000210b0000001842c000008511820081048c11014000a3040000000842d182544130403895100c10003544020401914204c1114454c13043040a048c10000280220a42508018c1000000c910b0000003843400000c110d048d5100c10000000a11803915100c10000010910b0000001842c00000061180000000842c00000021180000001842c0a354803040011410482806058c130400006028828000000e10b
  | 6, 1, 12 => 0x1843400154802040000004842c000000610b0000a048828c11041230401816304c10004050020421085048c100e1548030400081200828000000610d00000008460583044130400806048c1040058413044040e400c1041058c130436002028c10d90501230400000214460c14508130410440038c101430406304000d5200810000000a1180080a038c10800588130400000028460000000e1180000002842c0a15480304
  | 6, 1, 13 => 0x100038810594508030402915200c10000000610b018d5400c10000000e10d0000001842840058413040000001842c000010410b0000003842d14454c13040000001842c000080a20a00000434450000000e10b06914204c10413544030a21016214c10d90500a3043500a008c10000000610d00000048434850548430426016400c1095250c130400000404460413544030a15055028c100a1550030400806028c10000000210b
  | 6, 1, 14 => 0x842c003500220400055200828000000a10a0000004842c00000c910b0000003842c000000e10b048d5200c10000281220a32494304c10000181220a00002018828000000210b41504008c11053044130400055400810000000e10b0000000842c000001210b068d5100c10000001210b04881200c101430406304000d5400810000000611800914204c10122544030420016204c100e1550030430402028c1000000c110d
  | 6, 1, 15 => 0x816304c1000000c110d0000000842c0a4508130404855200c10852100e30400105410828000000210d00000028460000000210b0000004842c003550020421494104c10004548020430415410c10000000e10b0000003842cc1058413040000043445c00304412040000001842c0040006204000060288280e454803040180a038c100a058c13040000041042c000000a10d000000184601a35480304000c1100810000008110e
  | 6, 2, 0 => 0x851180000004842c120080e30400000048460000000e10b02915100c10000180e2040000000842cd8008123040000004842c000000210b00002028828000000a10b0000003842c000000610b10416100c10000000610b0000003842c0020480204
  | 7, 0, 0 => 0x2028828000000610d0000001842c000080a20400000304410000540e2040001401881000018412040000001843400204802040010541081000350022040010140082800404c120400015420810000001210a0005542081000410022040010d304810000000610a000d51008280045081204000552008100042508204000000184340000100104000000384340010440204000c1104810000000e10b00000100428000080a204
  | 7, 0, 1 => 0x2842800000061040000202881000324c120400000104428000080e20400105008810002048020a000d5400810000080a20400016214810000000610b0009510481000355002040011520081000324062040000a048828003044120400095400810003140220400094304810000001210b00095100828000001210a000000284280045006204000000484280035085204000d5100810000001210b000002004280000012104
  | 7, 0, 2 => 0x4842800000c110d00000018434000081220400014434810000001211800081008810000010010a000c1104810000488120400000028410004040e20400016204810000000a10400109404810000281220a00016304810002510120400085210810000000e10b00109018810000008010a00095400810000000610b0000a0488280003812204001151008100025002204000d540081000038122040000a04881000000c110d
  | 7, 0, 3 => 0x101400828000280e204000553048100035500204000c9304810000180e20400000424428003548020400014048810003550020400015028810000080620400094018810000008410a00000008460002100220400015420810000010111800095104810002041220400085210810000000a10400055400810000081220400000018434000001210a00115204810000000210a00085048810002550020a0000004842c000001210a
  | 7, 0, 4 => 0x10101881000450812040010d008810000000610b0009541081000000121180000000842c004150820400000304434000000e10b000d520481000058c920400000028428001548020a00000018428000181220400095100810003508520400000214460000588120400012200810000181220400000104428000000611800002048810000000610b00054424810000080620400000204428000004110a0009401881000454c5204
  | 7, 0, 5 => 0x6028810002140a2040004104881000354802040000041042c000000610d00055200810000180a20a000c1204810000001210b00000028460000080a204000c1028810000000a10a00002038810003544020400000028428000540a20400000018428003550020a0000002842800454802040000001846000048022040000001842c000080a20400055420810004250820400000008428000000210d0000a0388100001812204
  | 7, 0, 6 => 0x41028810000008510a0000004842800404c1204000d52008280042508204000d5100810000000611800000404460000180a2040000000842c00000021180008503881000150022040000001842c004544020400000028410000000610b0010d04881000304122040000000842c0010412204000c1048810000008510a000d51008100025441204001094208280035484204000000284600005105204000c10088100025101204
  | 7, 0, 7 => 0x843400254c1204000004044600025440204000c50188100003812204000c9048810000000211800054204810004040a20400000018428000000610d00002018810004340a20400000008428002100e20400095400810000008010400115104810001000e20400055400828000000a10a00002028810000180e20400000404460000380220400006028810000008511800000048434002150820400000048434000001210d
  | 7, 0, 8 => 0x5502881000214062040000000842800150c120400085210828000001210d0011420481000214842040000002842800154c12040000021442800304412040000001842c00000c110d00000008428000000210b000c1028810004548020400015028810003540a2040000e0488100000812204000163048100025006204000c1018810004241220400000028410000010111800000304410004140e204000000084100000012118
  | 7, 0, 9 => 0x28410000081220a0010d008810000001210b00085210810000590920400000018434000000210b00014048810003548120400041100810000000610a00000404460000001210d00105410810003044120400006028828000000e10b000c90288100045002204000000084600002885204000d5200810000001210a00041028810000080620a00095100810000081220400041008810002500620400000028410003040a204
  | 7, 0, 10 => 0x2038810004200620400000304434004140620400000018460004548420400115100810000081220400006048810000000210d000001044280015480204000c5304810000081220400094008810000000e104000d54008100035002204000c1008810000000e10400104008810003544020a00000008434000010810a00109038810004508120a00000204428003540a20400115214810004548020a000c10288100021484204
  | 7, 0, 11 => 0x105008810000550420400094008810003048520400081200828000000a10a00085048810000000e104000000384100000002104000c90288100015480204000000084280000012104000d5210810000000e10400115200810000000e10b000000284280000002118000d51008100000040104000000284600032402204000d5100828004000e2040000000843400454c120400006048810000000e10d001014008100035440204
  | 7, 0, 12 => 0x9510081000304412040008120082800355042040000000841000304842040000000842c00415082040000001841000000061040000004841000415082040008542081000104022040010901881000058c1204000c1104810002550020400108104810003040620400114324810000010810a00109028810000000610d0000004841000454802040001621481000204802040000010042800000c1104000000084280030504204
  | 7, 0, 13 => 0x55400810000001210b0000a03881000254402040000201881000250412040000000842c000500620400000018434002550020400000210428000000210a0000003842c000001210d00100018810000001210a00000104428003040220400000214460000010810a00002018810000000a10a000c10488100030402204000d510081000414c12040000004842c0000006104000c10488100005484204001150288100035440204
  | 7, 0, 14 => 0x304410000000610b0010930481000354802040005540081000058c9204000c1048810000001210a00000104428000000a10a0000002842800028122040010d414810002144120400000008434000000e10d00000008460000281220400101400810000000210a00114008810000081220400000028460000080a20400012038810004150420400000018410000000a10a001143048100035480204000002044280000006104
  | 7, 0, 15 => 0x304410000000a10a0000000842800000121040000004842c000000210a000003044340000002118000c1008810000000a10a00016304810000000210a00101400810000008010a00000048460000000a11800000214428004250120400115100828000590920400055400810000000e10b00000304410000281220400085048810002544020400101028810000001210d00084038810000000e10b00000304434000181220a
  | 7, 1, 0 => 0x6008810000001210d00055200810000000210a00115200810000000610a00000048428000000a10400085038810000000611800012018810000000610d0011532081000355042040000030441000058402040000003842c004508120400000304410004140e20400006028810000000a118000d540081000018122040000001842c0020402204000003044100015480204000000184280042481204000000184280000012118
  | 7, 1, 1 => 0x38434000001210400041100828003041220400000018460001048520400115104810000001210a000020288100015480204000d4214810000001210b0000a038810000000210b00016104810004544020400012104810000000210b00000008410000010410b00000048410004548020400101038810002550020400115324810002148420400000028460000000210a0000003842c000000610b000000384100040412204
  | 7, 1, 2 => 0x810088100021406204000d520081000000c110d00115100810004500a20400085028810000000210d000161048100000101118000c1048810003540a20400002018810004140620400016314810000001211800000048434004200e204000c1028810000000210a00000038410000000210b000c5028810000180e2040010d048810001041220400095100810000000e10d00000404410004548020400002028810000000e104
  | 7, 1, 3 => 0x2018810000180a20400114204828000000610a0000001842c000380a2040000041042800250122040010942081000304842040000002846000000c110d00055400810003040620400002018810000000210b0000001842c003140620400016434810000000a10a000c9048810000000610400085028810000010910a000d5200810002544020a00095100810001550020400002018828000000210a00002028828001540a204
  | 7, 1, 4 => 0x101400810000000a11800016214810004050020a00000404460000000210a000c1104810000281220400105410828000540a20400000028410000000210b00085210810000000610400114204810003241220400000214428000380220400000200428002100a2040009510081000350022040000a03881000250062040000201882800058c120400055400810001000a204000951008100000101118000d40088100035500204
  | 7, 1, 5 => 0x414428000000210a0009404881000150c12040000002841000454c12040011520081000304852040005520081000434c1204000d520081000000c510400109048810003500220400000400428000001210d000d520081000000021040000041042c004150420400000018460002550420400000028428001540a2040000004842c00028122040000003842c004200620400105304810004548420400108028810004140a204
  | 7, 1, 6 => 0x30443400038842040008520481000058c52040000001842c001548020a0000e100810000000210a00054028810004240a204000c102881000018852040011520081000058c5204000c1104810002550020400000048428004544020400108104810004500a204001142048100000006118000154108100025002204000c10088100000002118000c5304810000000610b0000000843400000c1104000002144280045481204
  | 7, 1, 7 => 0x16304810000000610d0000021041000154802040000e048810000010111800002028810003050820400000100410002540620400000008410004540a2040011521481000008122040008510481000154c120400000008460000000a104000000384340000040104000020188100035440204000c1018810000000e1040009510082800405002040000030443400000c11040000001842c00304c92040000a0188100003812204
  | 7, 1, 8 => 0x48460003548020400094304810004240220400000028410001540a20400016304810000000210a00000038434000001210400000104428000000a10400101048810002504120400000410428003550020a001081048100005881204000c1018810000000a1040001541081000415012040000001842c0042508204000d5028810000000610a00006038810000000210a00085210810001548020400100028810000000210b
  | 7, 1, 9 => 0xd5200828000000210b000d4008810000001210a00095038810001500a20400014018810000000210a000d5100810000001210d00081200810000000610400115100810000181220400104008810000000e10400054434810003040a2040004110081000154c120400109420828000004110a0005402881000405052040000003842c000000210a00006038810001550020400000008428000010410a00006028828000001210a
  | 7, 1, 10 => 0x5540081000001001040000e048810000281220400000028460000480a2040008510481000058c120400016424828000000210a0001402881000154c820400094304810003044120400085210810002550020400015320810000001210b00000214428004250820400000100410000000610400000214428000000610b0000e400810004548420400055400828000080e20400115304810000008410a00000214460000000e10d
  | 7, 1, 11 => 0xd400881000000c11040000001842c000000610a00000200410002100a204000c1048810000000610b000d4214810000000610a00115200810000000210a0000041042c00008812040000020042800000c110d000c5048810001550020a00002048810003508520400015410810002500220400000028428000000610d0000001842c000000611800055400810000080e204000000284100045440204000940088100045480204
  | 7, 1, 12 => 0x104428000001210b00000038434000001210a000000284600021412204000c101881000058c12040000a048828000000610a0000001842c000000210b0000201881000354412040000003842c000081220a0000000842800424812040008521082800000021040011502881000454412040011520082800454c920400085048810000000610a000000284600035002204000020388100000006104000003044340045440204
  | 7, 1, 13 => 0x410428000000a10400041100810000500a204001142048100005905204000000284600015012204000d5100810003040620400081008810002101220400002028828004500220400101400810000000611800040048810002140a20400000404460000181220400000008428000180e2040011520081000454c520400094104810000000610b0000001842800000c110d00115200810003508520400115100810004140a204
  | 7, 1, 14 => 0x114204810002550020a0000000842c00450c520400094304810000000610d00000028410000004010a00094018810000000e10b00000018434001044020400015028810002008120400000048460000080620400002028828000080a20400000304410000000a10a0009404881000000021180000030441000404062040000000842c0041412204000c1028810000080e20400002028810000000610b000c5028810000001210d
  | 7, 1, 15 => 0x11510081000000c110d000000284280000105104000d5400810004150120400115304810000001210b000060288100000012104000d5214810000000e10d00000304434003041220400000400428002550420400094404810000180e20400000028460000000210d00105038810004200a20400006038810000000e10b000d4008810002140220400000008428000000a10400000008428000004110a0000000842c000180a204
  | 7, 2, 0 => 0x21042800314062040000030441000000121040000001842800038062040000001843400454412040000004841000000c110d00114204810000080620400115038810000080e20400000048410000000e10b0000001846000420022040000004842c002544020400108008810004241220400055200810000000e10d0000041042c00058c520400006028810000001210a00000400428000000e10b000020488100000806204
  | 7, 2, 1 => 0x115100810000008110a000000184340030406204000d5400828000008110a00041008810000000e10b00015028810003040a20400095304810001540a204000810388100045081204000c1018810000000a10a0000a0388100000006104000d5200810004148520400105410810000181220a00000304434000180e204000c1104810000000610b000d5100828000000210b0011510082800000c110d000842148100035105204
  | 7, 2, 2 => 0x104008810001501220400002018810000000210b00000008434000281220400000008428000008010a00000404460000000610d000d5400828004250820a00000018428000000a10a00094048810000000610a00114304810000000210b00085204810000280e2040000004842c000000610a0010d008810000000210b000d5400810000501220400041008810004150420400115100810002510d20400000420428000180e204
  | 7, 2, 3 => 0x55200810003500220400000028428000008410a00006048810000001210a00109304810000000e10b00101400810001044020a00000048434003548020a000c1018810000590520400014018810000004110a00081200810000000e104000812008100000085118000d5200828000000610d000d5028810001548020400094018810004540220400000028410004250820400101400810002048020a00000008434002000e204
  | 7, 2, 4 => 0x115210810000000a118000411008100020480204000d5200828000001210b00000018428000000210d00095100810000000610b0000004842c00058c1204000d5420810000000610d0000030443400150122040008404881000351052040000004842c00250c120400109008810001540a20400081018810000000211800006028810000000e10b00000028410000540e2040000041042c0032402204000940188100030406204
  | 7, 2, 5 => 0x4842c0000040104000c11048100041412204000d5200810002550020400000028410000000a10a001010388100035504204000c1008810000588520400014018810003550020a00105420810000000a10a00085210828000000610a00000304434000001210b00000008434000000a10a000000084280000006118000000484100035402204000060288100010440204000162148100000012118000940088100025412204
  | 7, 2, 6 => 0x95304810000008010a000000284600015500204000c1048810000081220400094414810000001210b000c5048810000000210b000000484100025500204001054108100030481204000c1028810000000a10a00100018810002148420a00002028810000000210b00002048828000000e10b000c1104810000000a10a00114104810000000a1040001521081000200062040008521081000250c520400081200828002544020a
  | 7, 2, 7 => 0x55200810000000610b00115028810004500220400000048410004100e20400000404460000000e10b00006048810001000e204000c9214810000001210d00085008810000004110a00000048410000010410b000c1028810000488520400101400810002144120400000018460000000210400002048828001550020400002048810000281220400115314810000280e20400000048428000081220a00000304438000000a10a
  | 7, 2, 8 => 0x105104810003510520400000018460000280e2040000001843400354402040005520082800424812040000041046000250122040000003842c004540a2040000004842800150022040000001842c000000610b00002038810000500620400000100428000540a20400006048810000010410b00101400828000080a2040011530481000000c1104000d4008810000280e20400016424810004040620400000008410004040a204
  | 7, 2, 9 => 0x4842c0005841204000c1008810000000210a0008103881000404c120400094404810003044120400094414810002550020400002028810000084120400095008810002500220400000424428001548020a0000a048810000010111800000100428003548020400000404460003500220400054304810000180a2040009440481000250c120400115200810000001210a0000041042c000280e20400000018410000000210a
  | 7, 2, 10 => 0x105018810000180a20400000008428000000610b0000040446000314062040000000842c0030441204000c5028810002550020400055400810000000a10a00002018810000000e10b00002028810002100e20400085008810000000610b00016104810003041220400000008434001000e20400000104410000080620a00006028828003544020400000048428000381220400094104810000180a204000000084280030485204
  | 7, 2, 11 => 0x81214810000590d204000c1410810000000610b00000008428000001210d000c142081000000121040000a038810001550020a000d5400810000000a10a000d400881000104022040004110081000050c9204000c1028810000000a10a00000018434000008510a00002018810000001210d00000048428004500a20400114204810003040a20400000424428000180a2040000e048810000281220a0000a038810000180e204
  | 7, 2, 12 => 0xc10088100015480204000c5304810000000210a00105410828000540a204000000484340020480204000c1008810000080a20400115200810000000610b00084028810000000210400081200810000280e20400006048810001000a20400000048410000000610d00000028428000000610a00000028428003040a2040000003842c00404022040000000843400204062040001203881000434022040000003843400058c1204
  | 7, 2, 13 => 0x18428000000611800000404428004508120400000400410000001210400000028428000000210b0010d018810004544020400000048428000008510a00000048460000001210a00115200828000000610b00000008434002510120400081028810003240220400100038810004508120a00014028810000000a10400006048810003040a20400055028810000281220400000048460000501220400000008460003040a204
  | 7, 2, 14 => 0x1842c00000021180009510082800058c1204000c1104810004250820400109420828002000a20400000048428000010810a00000018428000000e10d000d541081000254c4204000c1210810000180a20400085204810003044120400095400810000180e20400016304810000000a10a000c1048810001500a2040000000842c000010010a00002048810000004010a0001201881000058852040000a0388100030481204
  | 7, 2, 15 => 0x95400828000000a10a0009540081000000801040000004842c00425082040000001842c00400062040000e048810000388120400000104428001040e20400100028810003041220400000018460000000610b000c1018810003240220400095100810000550820400000028428004548020400085210828004508120a0008520481000351052040001542081000054842040000e048810000000a10400115214810001500a204
  | 7, 3, 0 => 0xc1104810000010110e000060288100025500204000c104881000214412040000002846000350022040000032041000000c110d00000028460003548020400000204410000000210b0010900881000000c11040010d304810000501220400105104810000008410a00000304434000000611800095100828000008010a0011420481000059012040010104881000155002040000004842c000001211800000104428000000210a
  | 7, 3, 1 => 0x3842c004050020a00002038810000480220400006048810000008510a0000004843400000851180001642481000214842040000e048810000000a1180000e200810004148520400000404460000000611800101028810000000e10d00000008428000381220400000048434000000a10a000c1028810000008010a000152108100045006204000c110481000255002040000004842c000501220400000028428004100e204
  | 7, 3, 2 => 0xa0488100021441204000d4008810000500a20400105038810000000210a00000404460000000610a00000018460000081220400095410810004508520400041100810000081220400055200828004248120400085210810000000e1040000604881000104062040000000846000405002040000020041000354842040000030443400000121180000001842c000000610d000d54008100045440204000552008100002812204
  | 7, 3, 3 => 0x842800001011180000004842c000010810a0000000842800150c1204000c1018810003544020a00104028810000000e10b000162148100005508204000411008280000002118000c5048810001548020a00040028810001040e2040000041042c00008122040000004842c003040a20400000018428004040220400115204810004544020a00015018810000181220a0010d018810000000e10b00055200810000000610b
  | 7, 3, 4 => 0x18410000590920400041100810003140a20400000304434000000610b00000404428003041220400000400410003044120400006038810000381220400000008434003544120400000018460000080a204000c9018810000080620400015210810000001210d0010920481000454c92040009400881000304122040000604881000058412040000e048810003044020400000304434000181220400016304810000000a10a
  | 7, 3, 5 => 0x1641481000000c110d0000204881000304122040000004842c00210122040000041442800100122040011402881000000121180000000842c000001210d00000008460000000e10b0000004842800155082040010d304810003501220400000038434002048020a00000404460001550020400114204810000001211800105018810000280e20400000048428004140a2040000003842c0000101118000943048100035440204
  | 7, 3, 6 => 0x5540082800324c1204000c1018810001000a204000c10088100000104104000951048100035500204000810488100002812204000c101881000314022040000002842800254c1204000c104881000000c110d00000400410003041220400055400810000590d2040000000842c000390420400016104810000010810a00002038810004150420400041018810000080a2040000001842c001550020a000c1410810000001210a
  | 7, 3, 7 => 0xd5100810004150120400115200828000180e204000d5214810000000210b00000048428000000210a00000214428000010410b00000018428002140220400000018460000080a20a00016204810001540a2040011531481000028122040000602881000414c1204000c1400810000000a10a00000304410000001210a00085008810000008010a00081038810003550020400006028810000010111800000420428002100a204
  | 7, 3, 8 => 0x108008810001500a20400105008810000584120400000018460000280e2040000000843400154c12040011520082800008122040000004842c000000610a0000001842c00058c120400094038810000480a20400015028810000000610b0000a03881000250062040000002842800210022040000001843400000121040000003841000454802040000201881000304412040010d0288100020012204000c1104810000000a10a
  | 7, 3, 9 => 0x1842c002510d20400000018428004500a2040011420481000000c110d00100028810000000210b00055008810004544020a0000021446000000c110d00000028460003040a20400105410810003548120400006038810004250820a001152148100020406204000c1018810000000610a00000048434000080620a00000400410000588420400000028428000081220400085204810003500620400114204810000001210a
  | 7, 3, 10 => 0xa048810000000e10b000d50288100030481204000000184280040412204000000184340000002118000000084340015012204000d5400810000000210a00000028460003548420400109420810004250820400000304434004250820400006028810000000e10b000004044600045081204000d5018810000180a2040000004842c0021481204001151008100035485204000000084100000006104000000484280042402204
  | 7, 3, 11 => 0xd5420810000001211800055400810004540620400002018828000288120400000038434000000a118000163048100021484204000c1018810002150820400000018428000180a20a00108214810000010110a0005502881000204062040000a048810001040a20400040048810000001210a00000414428000008511800000414428000000210400115304810002048020400000008410002544020400000008410000000e104
  | 7, 3, 12 => 0x6038810000000210b0000e018810003040a2040000004842c004544020400114204828003044120400000420428002550020400104028810000010110a000000184340045081204000c1028810000000610a0001630481000250c520400115100828003548020400081200810000281220a000d5028810004340a2040000001843400000c110400000028428000000210a00055200810002544020400000304434000500a204
  | 7, 3, 13 => 0xd5104810000500a204000000084600004802204000954008100025440204000000284600045485204000c9028810000000610b00000018410000080a20400115324810002048020400114008810003040620400114018810000480a2040000000842c004544020a0010541082800200062040000001842800250c52040000a04881000038122040005402881000414122040000004846000054c42040000a0488100021484204
  | 7, 3, 14 => 0x1842800250122040008400881000405002040000000842c00000411040000001842c000004110a00055200810000001210a00000048434003040620400000018460002544020400095104810000000610d00081048810004140a204000d5400810004240e20400000008428000010410b00000008434000000610a00094414810003141220400000028410000000610a0010003881000404c1204000000284280003841204
  | 7, 3, 15 => 0xc102881000000c110400115310810000000211800080038810000000210a00055420828003040a204000d54008100000101118000060488100010440204000000184600032485204000d5100810000588120400000404460001548020400000434410000010111800115028810000000211800000008428002048020400041100828000590520400006048810000000210b000000184280035440204000410288100032485204
  | 7, 4, 0 => 0x8410000000a10a00000028460000000210a00000404460004240620400000324410001500220400000304434003044120400095400810003040a20400000018434003541220400085008810000540a20400100018810000008010a0000001842c002500620400115304810000000210a0010d04881000250122040000602881000250c1204000540088100004884204000411008280041402204000121008100020480204
  | 7, 4, 1 => 0xc1048810000000210400000404460000000e10b00000008434001550020400000104428003040620400095400828001541220400000410428000010510a0000202881000414852040000000842800000c110d000000484280020081204000c131481000354852040000a048810000000e10b0000001842800251012040000e048810003040220400000048434000500a204000c5008810000000610d0000004842c0020480204
  | 7, 4, 2 => 0x810388100030484204000060388100042508204000d542081000028122040000041442800254412040010930481000058c920400002018810003544120400054324810000001210b0000003842c002040a20400055400810000010810a00000414428000000a10a00002028828000000211800108008810003548120400094008810000000a10a00080018810000000a11800114304810000000a10a00002018810000000210d
  | 7, 4, 3 => 0x2038810004548020400006048828000000a10a0000001842800000c110400041048810000000210b001054108100021085204000004304340002802204000002004100000012118000c1048810000000210a000d5100810000000a10400115200810002510d20400000018428000001210d00114204810000000a10a000c1104810000000210b00015048810000180a204000d54008100030441204000060488100000101118
  | 7, 4, 4 => 0x2038810000080a20a000d4008810000010110a000002104280020406204000c1048810000180a20a000d4028810002148420400081028810000000210b00000048434000000610a000d520081000204802040000602881000304022040008103881000434122040000021442800250c120400000028460000000210b000d5028810000000210a00002038810002000e2040010d414810002140e20400000028428003544020a
  | 7, 4, 5 => 0xd5028810000000610b0000e028810000001210a00041100810000000210b00000008434004200e2040000602882800405092040000000841000425082040010803881000000c410d000c9048810000001210b00000008428000001211800002048810000000611800081200810000000210d00000008428002544020400054008810000180e204000060288100035508204000d5214810001501220400000048434000008410a
  | 7, 4, 6 => 0x10d414810001041220400000414428000590d20400000008434003548020400081018810000000a1040000004842c002544020400114204810000080620400000008428002048020400000008410000000610b0008001881000250c52040000001842800000c110d0005502881000214062040000001842800058c120400000018428002048020400002018810002000a204000d5200810000000a10a00109420810000008110a
  | 7, 4, 7 => 0x143148100000002104000000084280041504204000d5100810002510d204000c1048810000000210a00000404460000000610b000c1048810000000210b00055038810000000a10a00041038810004141220400105104810003040a20400000028410000000a1180009510481000008062040011420481000059012040009441481000155002040000004842c0000002118000c1204810000000a10a00000400428000001210d
  | 7, 4, 8 => 0xc120481000150122040010942081000054c420400000048428003040220400000008428002510d2040000002842800304852040000a048810003040220400085210810000000a11800055200810000180a20400115028810000000e10d00104038810004544020400000038434000000e10d0011401881000420062040000001842c0000002104000c9214810004200620400115210810000000610b000000284280000006118
  | 7, 4, 9 => 0x105214810000000a10a00054304810000004010a0010d018810000001210a000c1018810000008110a000d4414810000000e10d00000028428004240a204000c1008810003550020a0011520081000354402040010002881000048062040004101881000008122040000203881000150022040000001842c004240e204000000484600005504204000940088100042041204000000084280045440204000d5028810000001210b
  | 7, 4, 10 => 0x95400810000000210b00094104810000010110a00016304810000001210a00000104428002550020a00014018810000010410a0009404881000058c120400105304810004100a20400109420828000000610a000154208100020412204000000184340030508204000c1420810000001210a00002048828004540a204000c9214810000010410b000000484280025440204000002104280040402204001152048100035508204
  | 7, 4, 11 => 0x2028810000010110a0000010442800435052040001630481000450c120400016304810002550020a00002018810003544020400041100810000008110a0010901881000155002040000041042800058c920400000048428000000611800000210428000080e204000060488100032406204000d5200828000080e2040000000843400250c52040011502881000454402040000003842c002000a204000c11048100035480204
  | 7, 4, 12 => 0x842c00000c110d00000200410001550820400000048428000000a10a000020288100035002204000142148100000109104000000184340042501204000c101881000450812040000001842c002140e2040000a048810000010510a00015410810004250820400000008428000001210b0005542081000054842040000a03881000028122040005542081000304412040009441481000000c110d001090388100000085118
  | 7, 4, 13 => 0x2018810003550020400000304410000010111800002048828000080e2040011420482800008062040000000842c000181220a0000004842800154c0204000c1200810000281220a00095104810002041220400000400410003140220400055200810000000a11800000400428000000210a00000200428004540a2040010541082800450812040000604881000000c110d00000008460003050420400085210828000080620a
  | 7, 4, 14 => 0x48428002544020400114028810000080e2040005502881000214062040000000842800454402040000004842c000381220400081028810000000610a00000018410000181220a0000002842800450812040000001842c003508520400002038810000588120400115200828004150420a00000304434002501220400006048828003040220400054008810002544120400006048810000000610b000c100881000424c1204
  | 7, 4, 15 => 0x2028810003040220400000100428000004110a0000204881000058c1204000d5200810000180e204000c1008810003544120400000048428002140e2040000004842c000000e10d00000304434004050020400015028810002500620400000048410002550020400084008810000000610400115304810000000a11800000008434000001210b00000008428004150420400000048428004544120400080048810000280e204
  | 7, 5, 0 => 0x8428000001210b0000030441000250c520400006038810000010010a000000184280035481204000d5200810001550020400000048428000001210b00081028810000000e10400000104428000000e10b0001640481000204022040000202881000058c120400000414428000001210b000800288100025500204000c1048810000000a10a00085028810000000a11800000028428000000a10a00000048434000000210b
  | 7, 5, 1 => 0x16304810000004110a00055200810000000210400041100810004200a20400016304810000000e10400108028810000000a118000c1018810004040e2040000001842800405002040009400881000000c1104000d4008810000000210a00094018810000001210a00105104810000180a20400109420810000080620400016404810000080a204000000084280001812204000c1214810000004010400094048810001040e204
  | 7, 5, 2 => 0x214410000000e10d00015028810001540a20400000018410000000210b00000048428000000210a00095100810000010111800041038810000000a10a00115304810004548020400081200810000000e10400014424810000548420400040104810000388520400109048810000001210a0011401881000355002040000041442800354842040000003842c0042508204000954108100045006204000060288100021406204
  | 7, 5, 3 => 0x18410000000a10a00000304434000390820400000018428000000610a0010100881000454812040010101881000250c12040010d018810002001220400085420810004340a20400085210810003548020400000210428001040a204000c1028810000000610a0000002842800000021180001631481000000021180008542081000104062040000004842c0041504204000d5400810004144120400000008434001040a204
  | 7, 5, 4 => 0x109028810003040620400000304434000000a118000c9018810001550020400085210810000001210b000c902881000104062040011400881000450c12040000042041000038122040000001841000304062040000001842c000000610a00095304810000000210b00000104428000001211800085210810000081220400000018434003040620400104028810001510120400015420810000000610d000000184340030485204
  | 7, 5, 5 => 0x1210a
  | 8, 0, 0 => 0x204410000000210400000018428000000a1040000002841000000c910400000018410000000e10400000304410000000e10400000420410000010510a0000042442800000021040000041441000000c91040000041442800001011040000030441000000c910400000100410000010110400000048410000008510400000038410000010d10400000304410000000210400000104410000010d104000001044100000006104
  | 8, 0, 1 => 0x48410000008410400000434410000001210400000100410000010810400000104410000004110400000324410000008410400000100410000000e10400000304410000008010400000304410000004110a00000018410000001210a0000003841000000061040000010442800000c510400000434410000000210400000214410000000610a00000018428000010910400000104410000000a104000003144100000006104
  | 8, 0, 2 => 0x28428000000a10400000424410000010410400000100410000004110400000028410000001210400000048410000000210400000404410000010810a00000200428000010010400000410410000008010400000424410000010010400000420410000008510a00000204428000000a1040000032441000000c910400000204410000000a104000003044100000012104000003044100000006104000004344100000002104
  | 8, 0, 3 => 0x424410000000a10400000038410000008110a00000048410000004110400000434410000010410400000420410000001210400000018410000008510400000028428000000610400000210410000004010400000048410000000210a00000204410000000610400000214410000000210400000304410000000a10400000038410000010510400000028410000010410a000003144100000109104000000084100000105104
  | 8, 0, 4 => 0x28410000001210400000304410000004110a00000410410000010810400000048428000010d10400000018428000001210400000104410000010810400000048410000008010a00000018410000010110400000214410000010910400000424410000000a1040000020041000000c910400000200428000008510400000424428000010010400000008428000008110a00000304410000008110400000304410000010d104
  | 8, 0, 5 => 0x42042800000c510400000008410000000610400000214410000000a10400000400410000008510400000420410000000a10400000048410000000610400000008410000008510a00000304410000000610a00000210410000004010400000304410000010510a00000404428000010410a00000104410000008510400000404410000010410400000414410000010410a0000031441000000c9104000000084100000012104
  | 8, 0, 6 => 0x104410000010010400000038410000004110a00000424410000000610a00000200410000000610400000008428000000610a00000028428000000210400000204410000000a10a00000018410000008110400000008410000000a1040000000841000000121040000002841000000c110400000210410000004010400000018410000010010400000420410000010110a00000420410000008110400000324410000000210a
  | 8, 0, 7 => 0x314410000010910400000008410000000a1040000020041000000021040000041441000000021040000042442800000c510400000410410000010010a0000000842800001041040000042441000001001040000001841000000021040000040441000000121040000001841000000c110400000324410000001210a0000030441000000c110400000210428000010510400000100428000010d104000001044280000080104
  | 8, 0, 8 => 0x314410000008110400000008410000008010400000214410000000210400000200428000000a10400000028428000010510a00000038410000000a1040000030441000000121040000020441000001041040000002842800000c11040000020441000001011040000042041000000841040000010041000000851040000004842800001011040000001841000000c110400000048410000008510400000404410000000e104
  | 8, 0, 9 => 0x404410000010910a00000410410000010110400000324410000001210400000434410000010110a0000010441000000c110400000210410000004010400000048410000004110400000420428000010d10400000434410000008410400000404410000004110400000100410000000610400000420410000010810400000314410000000610400000018428000008510a00000008410000010010400000204428000000a104
  | 8, 0, 10 => 0x104410000008410a00000100428000008510400000048410000001210a0000020441000000061040000004842800000c510400000048410000008410400000314410000000210400000100410000000210400000048428000000210400000028410000000a1040000000842800001001040000002842800001051040000031441000001001040000042442800000021040000042441000000c9104000000284100000109104
  | 8, 0, 11 => 0x28410000000610400000400410000000610400000008428000008110400000018410000008510a00000400428000000a10400000214410000000610a00000414410000008510400000304410000000a10400000214428000000210400000304410000010010400000400428000010510400000048410000001210400000200410000008410400000100410000000e10400000210410000008010400000100410000001210a
  | 8, 0, 12 => 0x400410000000610a0000020042800001051040000041041000001091040000041441000000061040000030441000001091040000040441000000c910400000210410000010510a00000404410000008110a0000000841000001051040000032441000000411040000030441000000c110400000410410000010810a00000404410000010d10400000200410000000610400000420410000004110400000400410000010810a
  | 8, 0, 13 => 0x8410000004010400000434410000008110400000038410000000a10400000008428000000a10400000104410000001210400000008410000010410a00000008428000010510400000210410000000a10400000100410000000610400000404428000008510a0000004841000001011040000031441000000841040000004841000000121040000001841000000c510400000018410000000210400000038410000000a104
  | 8, 0, 14 => 0x210428000001210a00000424428000010d10400000200410000008110400000210428000004010a0000010441000000121040000042041000001051040000004841000000c110400000210410000004010400000018410000010810400000420428000010510400000400410000008510400000028428000008010400000324410000000210a0000010042800000851040000002842800000c1104000003144100000085104
  | 8, 0, 15 => 0x8410000010410400000200410000000210a00000028410000008510400000204428000000a10a00000414410000010410400000204410000008410400000404428000000610400000404410000001210400000404428000000a10400000104428000008010400000414410000010010a000000184280000080104000004104100000100104000000084100000081104000003244100000109104000003044100000081104
  | 8, 1, 0 => 0x48428000000a10400000048410000004110400000210428000004010a00000424410000010810400000048428000008410400000100410000000610a00000210428000000610400000200410000004010a00000200410000010d10400000420410000000610400000200428000000210a00000008410000000a10400000314410000008110400000028428000010510a0000020441000000c11040000000841000000c5104
  | 8, 1, 1 => 0x10910400000018410000010410400000400428000010410400000048410000010010400000410428000010010a00000324410000000e1040000002842800000c110400000038410000010410400000410428000010d1040000004842800000c1104
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 13 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x0_0_x2_1_x3_0 roots_x0_0_x2_1_x3_0 4 s ws hint
  | 1 => checkCutEntry dom_x1_0_x4_1 roots_x1_0_x4_1 5 s ws hint
  | 2 => checkCutEntry dom_x0_0_x5_1 roots_x0_0_x5_1 5 s ws hint
  | 3 => checkCutEntry dom_x1_0_x4_0_x5_0 roots_x1_0_x4_0_x5_0 4 s ws hint
  | 4 => checkCutEntry dom_x3_0 roots_x3_0 9 s ws hint
  | 5 => checkCutEntry dom_x0_0_x2_1 roots_x0_0_x2_1 5 s ws hint
  | 6 => checkCutEntry dom_x0_0_x3_0 roots_x0_0_x3_0 5 s ws hint
  | 7 => checkCutEntry dom_x1_0_x3_0_x4_1 roots_x1_0_x3_0_x4_1 4 s ws hint
  | 8 => checkCutEntry dom_x0_0_x3_0_x5_1 roots_x0_0_x3_0_x5_1 4 s ws hint
  | 9 => checkCutEntry dom_x0_0_x4_0_x5_1 roots_x0_0_x4_0_x5_1 4 s ws hint
  | 10 => checkCutEntry dom_x4_0 roots_x4_0 8 s ws hint
  | 11 => checkCutEntry dom_x0_0 roots_x0_0 7 s ws hint
  | 12 => checkCutEntry dom_x0_0_x4_0 roots_x0_0_x4_0 5 s ws hint
  | 13 => checkCutEntry dom_x1_0 roots_x1_0 7 s ws hint
  | 14 => checkCutEntry dom_x2_1 roots_x2_1 6 s ws hint
  | 15 => checkCutEntry dom_x2_0_x5_0 roots_x2_0_x5_0 5 s ws hint
  | 16 => checkCutEntry dom_x2_0_x4_0_x5_0 roots_x2_0_x4_0_x5_0 4 s ws hint
  | 17 => checkCutEntry dom_x2_1_x3_0 roots_x2_1_x3_0 5 s ws hint
  | 18 => checkCutEntry dom_x1_0_x4_1_x5_0 roots_x1_0_x4_1_x5_0 4 s ws hint
  | 19 => checkCutEntry dom_x4_1_x5_0 roots_x4_1_x5_0 5 s ws hint
  | 20 => checkCutEntry dom_x4_1 roots_x4_1 6 s ws hint
  | 21 => checkCutEntry dom_x3_0_x5_1 roots_x3_0_x5_1 5 s ws hint
  | 22 => checkCutEntry dom_x4_0_x5_1 roots_x4_0_x5_1 5 s ws hint
  | 23 => checkCutEntry dom_x5_1 roots_x5_1 6 s ws hint
  | 24 => checkCutEntry dom_x5_0 roots_x5_0 7 s ws hint
  | 25 => checkCutEntry dom_x1_0_x4_0 roots_x1_0_x4_0 5 s ws hint
  | 26 => checkCutEntry dom_x2_0 roots_x2_0 6 s ws hint
  | 27 => checkCutEntry dom_x2_0_x4_0 roots_x2_0_x4_0 5 s ws hint
  | 28 => checkCutEntry dom_x3_0_x4_1 roots_x3_0_x4_1 5 s ws hint
  | 29 => checkCutEntry dom_x4_0_x5_0 roots_x4_0_x5_0 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_63 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x2_1_x3_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x4_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x2_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x3_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x3_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x3_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x4_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_1_x3_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x4_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_0_x5_0 _ hc
  · contradiction
def p0Subs : List Nat := [11, 5, 13, 24, 14, 10, 2, 20, 23, 26, 1, 4, 3, 12, 15, 18, 9, 19, 0, 6, 27, 22, 16, 8, 17, 21, 25, 28, 7, 29]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_63 goalM u ys := by
  unfold cutHitH at h; rw [Bool.or_eq_true] at h; rcases h with h1 | h0
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
private theorem z4 : ∀ i, 0 ≤ i → i < 7 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 57 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 57 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 64 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 64 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_64 : ∀ i, 64 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 64 64 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_128 : ∀ i, 128 ≤ i → i < 192 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 64 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 192 → Z 6 i = true := (range_split z6_0 (range_split z6_64 z6_128))
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
private theorem z7_512 : ∀ i, 512 ≤ i → i < 548 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 36 512 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 548 → Z 7 i = true := (range_split (range_split (range_split z7_0 z7_64) (range_split z7_128 z7_192)) (range_split (range_split z7_256 z7_320) (range_split z7_384 (range_split z7_448 z7_512))))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 64 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_64 : ∀ i, 64 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 64 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_128 : ∀ i, 128 ≤ i → i < 192 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_192 : ∀ i, 192 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 192 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_256 : ∀ i, 256 ≤ i → i < 283 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 27 256 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 283 → Z 8 i = true := (range_split (range_split z8_0 z8_64) (range_split z8_128 (range_split z8_192 z8_256)))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 26 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 26 0 = true)
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

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 13]⟩], 16⟩
theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by simp [wit, PEqualNP.MetaComplexity.Monotone2]
theorem wit_size : wit.size ≤ 11 := by decide
theorem wit_eval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = ((fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4276944552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))) x := by decide +kernel
theorem hT6 : ∀ r : Fin 64, goal_all.testBit r.val = ((fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4276944552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))) (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4276944552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 11 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4276944552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_all 11 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_38117_aux

theorem PEqualNP.Outside.L_meta_38117 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4276944552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4276944552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s hs
  have hlb : 11 ≤ s := PEqualNP.Outside.L_meta_38117_aux.lower s hs
  exact ⟨PEqualNP.Outside.L_meta_38117_aux.wit, PEqualNP.Outside.L_meta_38117_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_38117_aux.wit_size hlb, PEqualNP.Outside.L_meta_38117_aux.wit_eval⟩
