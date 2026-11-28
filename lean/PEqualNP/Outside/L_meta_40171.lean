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

namespace PEqualNP.Outside.L_meta_40171_aux

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
def goal_all : Nat := 0xfeeaeaeaeec0e8c0
def dom_63 : Nat := 0xffffffffffffffff
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]
def dom_x1_0_x3_1 : Nat := 0x3300330033003300
def roots_x1_0_x3_1 : List Nat := [0x2200220022002200, 0x3000300030003000, 0x3300000033000000, 0x3300330000000000]
def dom_x1_0_x2_1_x4_1 : Nat := 0x3030000030300000
def roots_x1_0_x2_1_x4_1 : List Nat := [0x2020000020200000, 0x3000000030000000, 0x3030000000000000]
def dom_x1_0_x4_1 : Nat := 0x3333000033330000
def roots_x1_0_x4_1 : List Nat := [0x2222000022220000, 0x3030000030300000, 0x3300000033000000, 0x3333000000000000]
def dom_x1_0_x2_1 : Nat := 0x3030303030303030
def roots_x1_0_x2_1 : List Nat := [0x2020202020202020, 0x3000300030003000, 0x3030000030300000, 0x3030303000000000]
def dom_x1_0 : Nat := 0x3333333333333333
def roots_x1_0 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]
def dom_x2_0_x3_1_x5_0 : Nat := 0xf000f00
def roots_x2_0_x3_1_x5_0 : List Nat := [0xa000a00, 0xc000c00, 0xf000000]
def dom_x2_0_x3_1 : Nat := 0xf000f000f000f00
def roots_x2_0_x3_1 : List Nat := [0xa000a000a000a00, 0xc000c000c000c00, 0xf0000000f000000, 0xf000f0000000000]
def dom_x2_0_x5_0 : Nat := 0xf0f0f0f
def roots_x2_0_x5_0 : List Nat := [0xa0a0a0a, 0xc0c0c0c, 0xf000f00, 0xf0f0000]
def dom_x2_0 : Nat := 0xf0f0f0f0f0f0f0f
def roots_x2_0 : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]
def dom_x0_1_x4_0_x5_0 : Nat := 0xaaaa
def roots_x0_1_x4_0_x5_0 : List Nat := [0x8888, 0xa0a0, 0xaa00]
def dom_x0_1_x4_0 : Nat := 0xaaaa0000aaaa
def roots_x0_1_x4_0 : List Nat := [0x888800008888, 0xa0a00000a0a0, 0xaa000000aa00, 0xaaaa00000000]
def dom_x0_1_x5_0 : Nat := 0xaaaaaaaa
def roots_x0_1_x5_0 : List Nat := [0x88888888, 0xa0a0a0a0, 0xaa00aa00, 0xaaaa0000]
def dom_x0_0_x3_1_x5_1 : Nat := 0x5500550000000000
def roots_x0_0_x3_1_x5_1 : List Nat := [0x4400440000000000, 0x5000500000000000, 0x5500000000000000]
def dom_x0_0_x5_1 : Nat := 0x5555555500000000
def roots_x0_0_x5_1 : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]
def dom_x5_1 : Nat := 0xffffffff00000000
def roots_x5_1 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]
def dom_x3_1_x5_0 : Nat := 0xff00ff00
def roots_x3_1_x5_0 : List Nat := [0xaa00aa00, 0xcc00cc00, 0xf000f000, 0xff000000]
def dom_x4_0_x5_0 : Nat := 0xffff
def roots_x4_0_x5_0 : List Nat := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]
def dom_x5_0 : Nat := 0xffffffff
def roots_x5_0 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
def dom_x0_0_x3_1 : Nat := 0x5500550055005500
def roots_x0_0_x3_1 : List Nat := [0x4400440044004400, 0x5000500050005000, 0x5500000055000000, 0x5500550000000000]
def dom_x3_1_x4_0_x5_0 : Nat := 0xff00
def roots_x3_1_x4_0_x5_0 : List Nat := [0xaa00, 0xcc00, 0xf000]
def dom_x3_1_x5_1 : Nat := 0xff00ff0000000000
def roots_x3_1_x5_1 : List Nat := [0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000]
def dom_x3_1_x4_0 : Nat := 0xff000000ff00
def roots_x3_1_x4_0 : List Nat := [0xaa000000aa00, 0xcc000000cc00, 0xf0000000f000, 0xff0000000000]
def dom_x3_1 : Nat := 0xff00ff00ff00ff00
def roots_x3_1 : List Nat := [0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000]
def dom_x0_0 : Nat := 0x5555555555555555
def roots_x0_0 : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]
def dom_x2_1_x4_1 : Nat := 0xf0f00000f0f00000
def roots_x2_1_x4_1 : List Nat := [0xa0a00000a0a00000, 0xc0c00000c0c00000, 0xf0000000f0000000, 0xf0f0000000000000]
def dom_x0_0_x4_1_x5_1 : Nat := 0x5555000000000000
def roots_x0_0_x4_1_x5_1 : List Nat := [0x4444000000000000, 0x5050000000000000, 0x5500000000000000]
def dom_x0_0_x4_1 : Nat := 0x5555000055550000
def roots_x0_0_x4_1 : List Nat := [0x4444000044440000, 0x5050000050500000, 0x5500000055000000, 0x5555000000000000]
def dom_x4_1_x5_1 : Nat := 0xffff000000000000
def roots_x4_1_x5_1 : List Nat := [0xaaaa000000000000, 0xcccc000000000000, 0xf0f0000000000000, 0xff00000000000000]
def dom_x4_1 : Nat := 0xffff0000ffff0000
def roots_x4_1 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]
def dom_x0_1 : Nat := 0xaaaaaaaaaaaaaaaa
def roots_x0_1 : List Nat := [0x8888888888888888, 0xa0a0a0a0a0a0a0a0, 0xaa00aa00aa00aa00, 0xaaaa0000aaaa0000, 0xaaaaaaaa00000000]
def dom_x2_1 : Nat := 0xf0f0f0f0f0f0f0f0
def roots_x2_1 : List Nat := [0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000]
def dom_x4_0 : Nat := 0xffff0000ffff
def roots_x4_0 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

namespace S_x1_0_x3_1
def pairsG : List (Nat × Nat) := [(9, 13), (9, 25), (9, 41), (12, 13), (24, 25), (28, 29), (28, 60), (40, 41), (44, 45), (44, 60), (56, 57), (56, 60)]
def r1sG : List Nat := [9, 9, 9, 12, 24, 28, 28, 40, 44, 44, 56, 56]
def r2sG : List Nat := [13, 25, 41, 13, 25, 29, 60, 41, 45, 60, 57, 60]
def mpG : Nat := 0xfff
def pool6G : List Nat := [30825722423577, 30825923746061, 48417640025385, 48418109790477]
def xsM : List Nat := roots_x1_0_x3_1.map (· &&& dom_x1_0_x3_1)
def goalM : Nat := goal_all &&& dom_x1_0_x3_1
def NN : Nat → Nat
  | 4 => 5
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x897c9ebd40b0c94c391caec018eb3e570e64878d
  | 5, 0, 0 => 0x391caec0
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x330033000000330000003300030003000300030011001100110011003300330000000000330000003300000030003000300030002200220022002200
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x646468c4688468544474
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x1_0_x3_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x1_0_x3_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x1_0_x3_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x1_0_x3_1 goalM u ys) : RunD dom_x1_0_x3_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x1_0_x3_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x1_0_x3_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 3 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_x1_0_x3_1 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x1_0_x3_1 roots_x1_0_x3_1 goal_all 6 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x1_0_x3_1 goal_all := by
    have h0 : isConstB dom_x1_0_x3_1 goal_all = false := by decide +kernel
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
end S_x1_0_x3_1
theorem low_x1_0_x3_1 : Lower dom_x1_0_x3_1 roots_x1_0_x3_1 goal_all 6 := S_x1_0_x3_1.noCircuit

namespace S_x1_0_x2_1_x4_1
def pairsG : List (Nat × Nat) := [(21, 29), (21, 53), (28, 29), (28, 60), (52, 53), (52, 60)]
def r1sG : List Nat := [21, 21, 28, 28, 52, 52]
def r2sG : List Nat := [29, 53, 29, 60, 53, 60]
def mpG : Nat := 0x3f
def pool6G : List Nat := [30877396251933]
def xsM : List Nat := roots_x1_0_x2_1_x4_1.map (· &&& dom_x1_0_x2_1_x4_1)
def goalM : Nat := goal_all &&& dom_x1_0_x2_1_x4_1
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x355300cd
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x303000000000000030000000300000002020000020200000
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x1_0_x2_1_x4_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x1_0_x2_1_x4_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x1_0_x2_1_x4_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x1_0_x2_1_x4_1 goalM u ys) : RunD dom_x1_0_x2_1_x4_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x1_0_x2_1_x4_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x1_0_x2_1_x4_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x1_0_x2_1_x4_1 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x1_0_x2_1_x4_1 roots_x1_0_x2_1_x4_1 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x1_0_x2_1_x4_1 goal_all := by
    have h0 : isConstB dom_x1_0_x2_1_x4_1 goal_all = false := by decide +kernel
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
end S_x1_0_x2_1_x4_1
theorem low_x1_0_x2_1_x4_1 : Lower dom_x1_0_x2_1_x4_1 roots_x1_0_x2_1_x4_1 goal_all 4 := S_x1_0_x2_1_x4_1.noCircuit

theorem low_x1_0_x4_1 : Lower dom_x1_0_x4_1 roots_x1_0_x4_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3030000030300000, 56, 60)] (by decide +kernel) (by decide +kernel) low_x1_0_x2_1_x4_1

theorem low_x1_0_x2_1 : Lower dom_x1_0_x2_1 roots_x1_0_x2_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3030000030300000, 44, 60)] (by decide +kernel) (by decide +kernel) low_x1_0_x2_1_x4_1

namespace S_x1_0
def pairsG : List (Nat × Nat) := [(1, 33), (5, 13), (5, 37), (9, 13), (9, 25), (9, 41), (12, 13), (17, 25), (17, 49), (21, 29), (21, 53), (24, 25), (28, 29), (28, 60), (32, 33), (36, 37), (40, 41), (44, 45), (44, 60), (48, 49), (52, 53), (52, 60), (56, 57), (56, 60)]
def r1sG : List Nat := [1, 5, 5, 9, 9, 9, 12, 17, 17, 21, 21, 24, 28, 28, 32, 36, 40, 44, 44, 48, 52, 52, 56, 56]
def r2sG : List Nat := [33, 13, 37, 13, 25, 41, 13, 25, 49, 29, 53, 25, 29, 60, 33, 37, 41, 45, 60, 49, 53, 60, 57, 60]
def mpG : Nat := 0xffffff
def pool6G : List Nat := [48418109790477, 30877396246809, 30825923748109, 30825722421529, 30825722416409, 48469582291213, 61761782353212, 61663721824537]
def xsM : List Nat := roots_x1_0.map (· &&& dom_x1_0)
def goalM : Nat := goal_all &&& dom_x1_0
def NN : Nat → Nat
  | 4 => 1
  | 5 => 9
  | 6 => 12
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x856bff8f
  | 5, 0, 0 => 0xfb3479b7f19a254dd875bf28c00cee72b95e25d4777f3f6a76a78ec06c40da6049821fd1
  | 6, 0, 0 => 0xf21b9f42e6572a32cf315099a7e868eaa56c26968f767d968529ae5b79eb495156e853bf487a19a52c3b143008dee8a8
  | 7, 0, 0 => 0xb592d7db
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x2222000022220000202020202020202033330000222200003030303020202020222222222222222233333333222222220000000033333333000033330000333333333333000000003300330033003300111111111111111103030303030303033333000033330000330033002200220030303030303030302222222200000000
  | 1 => 0x33330000000000003030303000000000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x188204
  | 5, 0, 0 => 0x60ad09538c415a9cc12a15433040a71998b5198254a9da60ad4665912a7198a45
  | 6, 0, 0 => 0x38cc15a58e33056e638cc182d80330569538cc15bd8e38982b601c6609540719964538cc15818e330565651c660ad807305685
  | 7, 0, 0 => 0x71982b5
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 24
  | 5 => 29
  | 6 => 34
  | 7 => 29
  | _ => 0
def stateM : Nat → Nat
  | 4 => 0xffffff
  | 5 => 0x1fffffff
  | 6 => 0x3ffffffff
  | 7 => 0x1fffffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x78000000000000006060000000000f80780000000000036860600000000000007bf0000000000ffc7bf0000000000003fff000000000007c07f0000000000ffc0000000000000c738780000000000fff8400000000000c949b90000000000f83f800000000000c70038000000000036b6460000000000000000
  | 1 => 0xf800000000000000368000
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x581f90000000000012964e0000000000fc3f900000000000b6b64e00000000005bdfff0000000000ffffff0000000000001ada000000000003c06f0000000000ffe5250000000000e73afa0000000000a4200000000000004949b10000000000fc3f900000000000e73afa0000000000b6b64e00000000005bc525
  | 1 => 0xfc25000000000000b6a404
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
  | 5 => 12
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xffa48c68e21b298dd6dcc483bc5910039eae0caa999a55748e5bf06a8c270b327bef521b65d063da1a636ef104d9e41c
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x28400000000210000000018400000000e10000000038400000000210000000018400000000610000000008400000000a10000000028400000000e100
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 5 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x1_0_x3_1 roots_x1_0_x3_1 6 s ws hint
  | 1 => checkCutEntry dom_x1_0_x4_1 roots_x1_0_x4_1 5 s ws hint
  | 2 => checkCutEntry dom_x1_0_x2_1 roots_x1_0_x2_1 5 s ws hint
  | 3 => checkCutEntry dom_x1_0_x2_1_x4_1 roots_x1_0_x2_1_x4_1 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x1_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x2_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x2_1_x4_1 _ hc
  · contradiction
def p0Subs : List Nat := [0, 2, 1, 3]
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
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 9 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 9 0 = true)
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

namespace S_x2_0_x3_1_x5_0
def pairsG : List (Nat × Nat) := [(9, 11), (9, 25), (10, 11), (10, 26), (24, 25), (24, 26)]
def r1sG : List Nat := [9, 9, 10, 10, 24, 24]
def r2sG : List Nat := [11, 25, 11, 26, 25, 26]
def mpG : Nat := 0x3f
def pool6G : List Nat := [11034175346955]
def xsM : List Nat := roots_x2_0_x3_1_x5_0.map (· &&& dom_x2_0_x3_1_x5_0)
def goalM : Nat := goal_all &&& dom_x2_0_x3_1_x5_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x62a6bbc9
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xf000000000000000c000c00000000000a000a00
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x2_0_x3_1_x5_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x2_0_x3_1_x5_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x2_0_x3_1_x5_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x2_0_x3_1_x5_0 goalM u ys) : RunD dom_x2_0_x3_1_x5_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x2_0_x3_1_x5_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x2_0_x3_1_x5_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x2_0_x3_1_x5_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x2_0_x3_1_x5_0 roots_x2_0_x3_1_x5_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x2_0_x3_1_x5_0 goal_all := by
    have h0 : isConstB dom_x2_0_x3_1_x5_0 goal_all = false := by decide +kernel
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
end S_x2_0_x3_1_x5_0
theorem low_x2_0_x3_1_x5_0 : Lower dom_x2_0_x3_1_x5_0 roots_x2_0_x3_1_x5_0 goal_all 4 := S_x2_0_x3_1_x5_0.noCircuit

theorem low_x2_0_x3_1 : Lower dom_x2_0_x3_1 roots_x2_0_x3_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f0000000000, 9, 41)] (by decide +kernel) (by decide +kernel) low_x2_0_x3_1_x5_0

theorem low_x2_0_x5_0 : Lower dom_x2_0_x5_0 roots_x2_0_x5_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f00, 3, 11)] (by decide +kernel) (by decide +kernel) low_x2_0_x3_1_x5_0

namespace S_x2_0
def pairsG : List (Nat × Nat) := [(1, 33), (3, 11), (3, 35), (9, 11), (9, 25), (9, 41), (10, 11), (10, 26), (17, 25), (17, 49), (18, 26), (19, 27), (19, 51), (24, 25), (24, 26), (32, 33), (34, 35), (40, 41), (42, 43), (42, 58), (48, 49), (50, 51), (50, 58), (56, 57), (56, 58)]
def r1sG : List Nat := [1, 3, 3, 9, 9, 9, 10, 10, 17, 17, 18, 19, 19, 24, 24, 32, 34, 40, 42, 42, 48, 50, 50, 56, 56]
def r2sG : List Nat := [33, 11, 35, 11, 25, 41, 11, 26, 25, 49, 26, 27, 51, 25, 26, 33, 35, 41, 43, 58, 49, 51, 58, 57, 58]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [46219084306699, 46261933775371, 61612012673561, 61753192418074, 61655096564249]
def xsM : List Nat := roots_x2_0.map (· &&& dom_x2_0)
def goalM : Nat := goal_all &&& dom_x2_0
def NN : Nat → Nat
  | 5 => 3
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xe74dfad9861e300b441a1221
  | 6, 0, 0 => 0x1bba847f
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xf0f00000f0f0a0a0a0a0a0a0a0a03030303030303030f0f0f0f000000000f0f00000f0f00000f000f000f000f000c0c0c0c0c0c0c0c0505050505050505
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x111dd635aac6885
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
  | 0 => 0xf80ff0000000000001b3f000000000192e3390000000001ff80000000000001f07f0000000000018e60f800000000006d1cc60000000001ffe4c0
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x7806f0000000000b7bb7f000000000092a3310000000001ff92250000000001f87f900000000001ce6dfa00000000016d5cce0000000001484480
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
  | 0 => checkCutEntry dom_x2_0_x3_1 roots_x2_0_x3_1 5 s ws hint
  | 1 => checkCutEntry dom_x2_0_x5_0 roots_x2_0_x5_0 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x2_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x5_0 _ hc
  · contradiction
def p0Subs : List Nat := [0, 1]
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

namespace S_x0_1_x4_0_x5_0
def pairsG : List (Nat × Nat) := [(3, 7), (3, 11), (5, 7), (5, 13), (9, 11), (9, 13)]
def r1sG : List Nat := [3, 3, 5, 5, 9, 9]
def r2sG : List Nat := [7, 11, 7, 13, 11, 13]
def mpG : Nat := 0x3f
def pool6G : List Nat := [5510594890503]
def xsM : List Nat := roots_x0_1_x4_0_x5_0.map (· &&& dom_x0_1_x4_0_x5_0)
def goalM : Nat := goal_all &&& dom_x0_1_x4_0_x5_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x96de1621
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xaa00000000000000a0a00000000000008888
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x0_1_x4_0_x5_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x0_1_x4_0_x5_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x0_1_x4_0_x5_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x0_1_x4_0_x5_0 goalM u ys) : RunD dom_x0_1_x4_0_x5_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x0_1_x4_0_x5_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x0_1_x4_0_x5_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x0_1_x4_0_x5_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x0_1_x4_0_x5_0 roots_x0_1_x4_0_x5_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x0_1_x4_0_x5_0 goal_all := by
    have h0 : isConstB dom_x0_1_x4_0_x5_0 goal_all = false := by decide +kernel
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
end S_x0_1_x4_0_x5_0
theorem low_x0_1_x4_0_x5_0 : Lower dom_x0_1_x4_0_x5_0 roots_x0_1_x4_0_x5_0 goal_all 4 := S_x0_1_x4_0_x5_0.noCircuit

theorem low_x0_1_x4_0 : Lower dom_x0_1_x4_0 roots_x0_1_x4_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa00000000, 1, 33)] (by decide +kernel) (by decide +kernel) low_x0_1_x4_0_x5_0

theorem low_x0_1_x5_0 : Lower dom_x0_1_x5_0 roots_x0_1_x5_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa0000, 9, 25)] (by decide +kernel) (by decide +kernel) low_x0_1_x4_0_x5_0

namespace S_x0_0_x3_1_x5_1
def pairsG : List (Nat × Nat) := [(42, 46), (42, 58), (44, 46), (44, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [42, 42, 44, 44, 56, 56]
def r2sG : List Nat := [46, 58, 46, 60, 58, 60]
def mpG : Nat := 0x3f
def pool6G : List Nat := [48559843719726]
def xsM : List Nat := roots_x0_0_x3_1_x5_1.map (· &&& dom_x0_0_x3_1_x5_1)
def goalM : Nat := goal_all &&& dom_x0_0_x3_1_x5_1
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xc244b53a
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x550000000000000050005000000000004400440000000000
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x0_0_x3_1_x5_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x0_0_x3_1_x5_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x0_0_x3_1_x5_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x0_0_x3_1_x5_1 goalM u ys) : RunD dom_x0_0_x3_1_x5_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x0_0_x3_1_x5_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x0_0_x3_1_x5_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x0_0_x3_1_x5_1 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x0_0_x3_1_x5_1 roots_x0_0_x3_1_x5_1 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x0_0_x3_1_x5_1 goal_all := by
    have h0 : isConstB dom_x0_0_x3_1_x5_1 goal_all = false := by decide +kernel
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
end S_x0_0_x3_1_x5_1
theorem low_x0_0_x3_1_x5_1 : Lower dom_x0_0_x3_1_x5_1 roots_x0_0_x3_1_x5_1 goal_all 4 := S_x0_0_x3_1_x5_1.noCircuit

theorem low_x0_0_x5_1 : Lower dom_x0_0_x5_1 roots_x0_0_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5500550000000000, 50, 58)] (by decide +kernel) (by decide +kernel) low_x0_0_x3_1_x5_1

theorem low_x5_1 : Lower dom_x5_1 roots_x5_1 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaaaaaa00000000, 32, 33)] (by decide +kernel) (by decide +kernel) low_x0_0_x5_1

theorem low_x3_1_x5_0 : Lower dom_x3_1_x5_0 roots_x3_1_x5_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f000, 9, 13)] (by decide +kernel) (by decide +kernel) low_x2_0_x3_1_x5_0

theorem low_x4_0_x5_0 : Lower dom_x4_0_x5_0 roots_x4_0_x5_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa, 10, 11)] (by decide +kernel) (by decide +kernel) low_x0_1_x4_0_x5_0

namespace S_x5_0
def pairsG : List (Nat × Nat) := [(2, 6), (3, 7), (3, 11), (4, 6), (5, 7), (5, 13), (9, 11), (9, 13), (9, 25), (10, 11), (10, 14), (10, 26), (12, 13), (12, 14), (17, 25), (18, 22), (18, 26), (19, 23), (19, 27), (20, 22), (21, 23), (21, 29), (24, 25), (24, 26), (28, 29), (28, 30)]
def r1sG : List Nat := [2, 3, 3, 4, 5, 5, 9, 9, 9, 10, 10, 10, 12, 12, 17, 18, 18, 19, 19, 20, 21, 21, 24, 24, 28, 28]
def r2sG : List Nat := [6, 7, 11, 6, 7, 13, 11, 13, 25, 11, 14, 26, 13, 14, 25, 22, 26, 23, 27, 22, 23, 29, 25, 26, 29, 30]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [23132845705990, 30829427100422, 23128718378509, 20929728808459, 30825149762329]
def xsM : List Nat := roots_x5_0.map (· &&& dom_x5_0)
def goalM : Nat := goal_all &&& dom_x5_0
def NN : Nat → Nat
  | 5 => 1
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xbe519f46
  | 6, 0, 0 => 0xeba6a037
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xcccccccc00000000ffff000000000000ff00ff0000000000f0f0f0f000000000aaaaaaaa0000000033333333
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
  | 0 => 0x78e070000000003ffc0000000000003c03fc0000000000338303800000000003641f60000000003f871f8
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x29fae5f0000000003ffc9000000000003e57fe400000000033ab4bb00000000017653f600000000016051a0
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
  | 0 => checkCutEntry dom_x0_1_x5_0 roots_x0_1_x5_0 5 s ws hint
  | 1 => checkCutEntry dom_x3_1_x5_0 roots_x3_1_x5_0 5 s ws hint
  | 2 => checkCutEntry dom_x2_0_x5_0 roots_x2_0_x5_0 5 s ws hint
  | 3 => checkCutEntry dom_x4_0_x5_0 roots_x4_0_x5_0 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x5_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_0_x5_0 _ hc
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

theorem low_x0_0_x3_1 : Lower dom_x0_0_x3_1 roots_x0_0_x3_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5500550000000000, 28, 60)] (by decide +kernel) (by decide +kernel) low_x0_0_x3_1_x5_1

namespace S_x3_1_x4_0_x5_0
def pairsG : List (Nat × Nat) := [(9, 11), (9, 13), (10, 11), (10, 14), (12, 13), (12, 14)]
def r1sG : List Nat := [9, 9, 10, 10, 12, 12]
def r2sG : List Nat := [11, 13, 11, 14, 13, 14]
def mpG : Nat := 0x3f
def pool6G : List Nat := [11033973230859]
def xsM : List Nat := roots_x3_1_x4_0_x5_0.map (· &&& dom_x3_1_x4_0_x5_0)
def goalM : Nat := goal_all &&& dom_x3_1_x4_0_x5_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x5b72f794
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xf000000000000000cc00000000000000aa00
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x3_1_x4_0_x5_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x3_1_x4_0_x5_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x3_1_x4_0_x5_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x3_1_x4_0_x5_0 goalM u ys) : RunD dom_x3_1_x4_0_x5_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x3_1_x4_0_x5_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x3_1_x4_0_x5_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x3_1_x4_0_x5_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x3_1_x4_0_x5_0 roots_x3_1_x4_0_x5_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x3_1_x4_0_x5_0 goal_all := by
    have h0 : isConstB dom_x3_1_x4_0_x5_0 goal_all = false := by decide +kernel
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
end S_x3_1_x4_0_x5_0
theorem low_x3_1_x4_0_x5_0 : Lower dom_x3_1_x4_0_x5_0 roots_x3_1_x4_0_x5_0 goal_all 4 := S_x3_1_x4_0_x5_0.noCircuit

theorem low_x3_1_x5_1 : Lower dom_x3_1_x5_1 roots_x3_1_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaa00aa0000000000, 40, 41)] (by decide +kernel) (by decide +kernel) low_x0_0_x3_1_x5_1

theorem low_x3_1_x4_0 : Lower dom_x3_1_x4_0 roots_x3_1_x4_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff0000000000, 9, 41)] (by decide +kernel) (by decide +kernel) low_x3_1_x4_0_x5_0

namespace S_x3_1
def pairsG : List (Nat × Nat) := [(9, 11), (9, 13), (9, 25), (9, 41), (10, 11), (10, 14), (10, 26), (12, 13), (12, 14), (24, 25), (24, 26), (28, 29), (28, 30), (28, 60), (40, 41), (42, 43), (42, 46), (42, 58), (44, 45), (44, 46), (44, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [9, 9, 9, 9, 10, 10, 10, 12, 12, 24, 24, 28, 28, 28, 40, 42, 42, 42, 44, 44, 44, 56, 56, 56]
def r2sG : List Nat := [11, 13, 25, 41, 11, 14, 26, 13, 14, 25, 26, 29, 30, 60, 41, 43, 46, 58, 45, 46, 60, 57, 58, 60]
def mpG : Nat := 0xffffff
def pool6G : List Nat := [61611779558697, 30825722416409, 46218613755147, 48417640025385, 46219086535182, 30825923746061, 46218883960331]
def xsM : List Nat := roots_x3_1.map (· &&& dom_x3_1)
def goalM : Nat := goal_all &&& dom_x3_1
def NN : Nat → Nat
  | 5 => 3
  | 6 => 7
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xe84f765254539fcf021fc72d
  | 6, 0, 0 => 0xf9d04ef9c3eb1704c2f34015aa1ac6299fb4a95357e6ed872cb293d4
  | 7, 0, 0 => 0x19b23d5e
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xff00ff00ff00f000ff00f000ff00aa00ff00aa00fa00fa00fa00fa00aa00aa00aa00aa00f000f000f000f0000000ff000000ff00ff00ff0000000000ff000000ff000000cc00cc00cc00cc0055005500550055000f000f000f000f00
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x427055432105462155
  | 6, 0, 0 => 0x4a362760436215438627604327054936276046275503627b5
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
  | 5, 0, 0 => 0xf2501703c71bbd50bfe2cb5fabaa253d91d9d4625e5440804483efa53fa5fbc0
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x28400000000e10000000038400000000210000000018400000000210000000018400000000a100
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 4 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x1_0_x3_1 roots_x1_0_x3_1 6 s ws hint
  | 1 => checkCutEntry dom_x0_0_x3_1_x5_1 roots_x0_0_x3_1_x5_1 4 s ws hint
  | 2 => checkCutEntry dom_x0_0_x3_1 roots_x0_0_x3_1 5 s ws hint
  | 3 => checkCutEntry dom_x3_1_x5_0 roots_x3_1_x5_0 5 s ws hint
  | 4 => checkCutEntry dom_x2_0_x3_1_x5_0 roots_x2_0_x3_1_x5_0 4 s ws hint
  | 5 => checkCutEntry dom_x2_0_x3_1 roots_x2_0_x3_1 5 s ws hint
  | 6 => checkCutEntry dom_x3_1_x4_0_x5_0 roots_x3_1_x4_0_x5_0 4 s ws hint
  | 7 => checkCutEntry dom_x3_1_x5_1 roots_x3_1_x5_1 5 s ws hint
  | 8 => checkCutEntry dom_x3_1_x4_0 roots_x3_1_x4_0 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x3_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x3_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x3_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1_x4_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1_x4_0 _ hc
  · contradiction
def p0Subs : List Nat := [0, 2, 5, 3, 7, 8, 1, 4, 6]
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
def RootG (s : Nat) : Bool := scr dom_x3_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_x3_1 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x3_1 roots_x3_1 goal_all 8 := by
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
theorem low_x3_1 : Lower dom_x3_1 roots_x3_1 goal_all 8 := S_x3_1.noCircuit

theorem low_x0_0 : Lower dom_x0_0 roots_x0_0 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5500550055005500, 18, 26)] (by decide +kernel) (by decide +kernel) low_x0_0_x3_1

theorem low_x2_1_x4_1 : Lower dom_x2_1_x4_1 roots_x2_1_x4_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c00000c0c00000, 20, 22)] (by decide +kernel) (by decide +kernel) low_x1_0_x2_1_x4_1

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
    [(0x5555000000000000, 28, 60)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_1_x5_1

theorem low_x4_1_x5_1 : Lower dom_x4_1_x5_1 roots_x4_1_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa000000000000, 48, 49)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_1_x5_1

namespace S_x4_1
def pairsG : List (Nat × Nat) := [(17, 25), (17, 49), (18, 22), (18, 26), (19, 23), (19, 27), (19, 51), (20, 22), (21, 23), (21, 29), (21, 53), (24, 25), (24, 26), (28, 29), (28, 30), (28, 60), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [17, 17, 18, 18, 19, 19, 19, 20, 21, 21, 21, 24, 24, 28, 28, 28, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [25, 49, 22, 26, 23, 27, 51, 22, 23, 29, 53, 25, 26, 29, 30, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [30868283921946, 61654729234737, 61693232223804, 30877396250905, 23172292024854, 61796309866044, 30868772035097, 57295185713468, 55096716826138]
def xsM : List Nat := roots_x4_1.map (· &&& dom_x4_1)
def goalM : Nat := goal_all &&& dom_x4_1
def NN : Nat → Nat
  | 5 => 11
  | 6 => 13
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xef78435eea211090e826c8ec9ef51cb37306ea4b5c1d51b054cbd73e4ee90e7245ef9d803352bcc90b9a2b05
  | 6, 0, 0 => 0xfe65e7c7dcaa0796c3d716c8b07ee5aca58eab6ca4b7fa37706228e7632de5a95f0392424ee90e724797940042337a1403bd1a95
  | 7, 0, 0 => 0x632de5a9
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xf0000000f0000000ffcc0000ffcc0000ffaa0000ffaa0000eeee0000eeee0000f0c00000f0c0000000000000ffff0000ffaa0000000000000f0f00000f0f0000ff000000ff00000055550000555500003333000033330000ffff000000000000f0f00000f0f00000cccc0000cccc0000aaaa0000aaaa000000ff000000ff0000
  | 1 => 0xff00000000000000f0f0000000000000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x10414014831180a71050a521c4642a4e31054830940a7184aa520c410290eb1054620814a438cc55
  | 6, 0, 0 => 0x438c46521c6208188e38c41621c6f10588788c41621c7010580438c255010e310548d38c416010620814071882a521c6c105804388285
  | 7, 0, 0 => 0x438c415
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
  | 0 => 0xe00000000000038ef87c000000000380ff7300000000000e077f000000000000e000000000000000ffff000000000380000000000000038f187f000000000380f8000000000003fff88c0000000003f1ff830000000003ff0000000000000070e78000000000000e007c000000000000077300000000007f07ff
  | 1 => 0x38000000000000000700000
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x240e2000000000003eefbfd0000000003dbff7b0000000001bf7fff000000000264e3940000000000007bbd0000000003db844200000000018b186b0000000003c8fa2900000000036cd08c0000000002d1ae030000000003ff8442000000000274e79400000000012e51fc0000000000932f7300000000003705d6
  | 1 => 0x3c880000000000002748400
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
  | 0 => checkCutEntry dom_x0_0_x4_1 roots_x0_0_x4_1 5 s ws hint
  | 1 => checkCutEntry dom_x1_0_x4_1 roots_x1_0_x4_1 5 s ws hint
  | 2 => checkCutEntry dom_x2_1_x4_1 roots_x2_1_x4_1 5 s ws hint
  | 3 => checkCutEntry dom_x4_1_x5_1 roots_x4_1_x5_1 5 s ws hint
  | 4 => checkCutEntry dom_x0_0_x4_1_x5_1 roots_x0_0_x4_1_x5_1 4 s ws hint
  | 5 => checkCutEntry dom_x1_0_x2_1_x4_1 roots_x1_0_x2_1_x4_1 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x4_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_1_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x2_1_x4_1 _ hc
  · contradiction
def p0Subs : List Nat := [0, 2, 1, 3, 4, 5]
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

theorem low_x0_1 : Lower dom_x0_1 roots_x0_1 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa0000aaaa0000, 9, 25)] (by decide +kernel) (by decide +kernel) low_x0_1_x4_0

theorem low_x2_1 : Lower dom_x2_1 roots_x2_1 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c0c0c0c0c0c0c0, 4, 6)] (by decide +kernel) (by decide +kernel) low_x1_0_x2_1

theorem low_x4_0 : Lower dom_x4_0 roots_x4_0 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa0000aaaa, 10, 11)] (by decide +kernel) (by decide +kernel) low_x0_1_x4_0

namespace S_63
def pairsG : List (Nat × Nat) := [(1, 33), (2, 6), (3, 7), (3, 11), (3, 35), (4, 6), (5, 7), (5, 13), (5, 37), (9, 11), (9, 13), (9, 25), (9, 41), (10, 11), (10, 14), (10, 26), (12, 13), (12, 14), (17, 25), (17, 49), (18, 22), (18, 26), (19, 23), (19, 27), (19, 51), (20, 22), (21, 23), (21, 29), (21, 53), (24, 25), (24, 26), (28, 29), (28, 30), (28, 60), (32, 33), (34, 35), (34, 38), (36, 37), (36, 38), (40, 41), (42, 43), (42, 46), (42, 58), (44, 45), (44, 46), (44, 60), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 2, 3, 3, 3, 4, 5, 5, 5, 9, 9, 9, 9, 10, 10, 10, 12, 12, 17, 17, 18, 18, 19, 19, 19, 20, 21, 21, 21, 24, 24, 28, 28, 28, 32, 34, 34, 36, 36, 40, 42, 42, 42, 44, 44, 44, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [33, 6, 7, 11, 35, 6, 7, 13, 37, 11, 13, 25, 41, 11, 14, 26, 13, 14, 25, 49, 22, 26, 23, 27, 51, 22, 23, 29, 53, 25, 26, 29, 30, 60, 33, 35, 38, 37, 38, 41, 43, 46, 58, 45, 46, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0xffffffffffffff
def pool6G : List Nat := [23128718378509, 46300489582106, 61611779558689, 61612012210969, 48498923870524, 20929728808459, 48559052098310, 61693231171132, 61762336065084, 46261969101067, 30868806305306, 48418109790477, 23128719296013, 46261933775371, 46299900087066, 30825722421529, 57257152485894, 23171500411654, 46218882123275, 48559843711494, 46300690913798, 61796308944444, 30877396246797, 30825722416409, 30825923748109, 61693063400764]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_all &&& dom_63
def NN : Nat → Nat
  | 5 => 11
  | 6 => 148
  | 7 => 530
  | 8 => 288
  | 9 => 27
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xf4b0da97f25afebee3617c9dc90c8068b86def53801336c669110f0a56e6e3a150d3f6d425d39d380a857359
  | 6, 0, 0 => 0x71c5a25170fded6b70edea3b702cffbd6bd66cb66b9af01d6ae2b6ec65422c4961252965605201df5e5c74465dd4b0405d0b51cc5ca69ee65addd7df5ac7b4dc595b092657a33a8f52d46e9e52324af34a2bb09f455436f24329583b42843724413228e640edc7c73fac5b103f414a253ebf80263e917fab3d579cd03b37b34f3ab33bbf3744b0033497ba6b31bbe12a2e3fbd0d2d7b3cc42cdb77262b3513a329a7f8f92940fea126c88a5925b941fa23950c2c1fa6552d1e1dc6c21af2b3361a037e641949ac73176d88ef15c85f47152bddc0148cb2f013d9cf82115a9c220ce4df9508614ebc076c525f05c12441042ee5a201d909c901a93e9701581f81
  | 6, 0, 1 => 0xdfa8ea5cdf1216c1dee03be5dda94fdcdda07463dc0c3701d07fa395d01e5b9ccf9b7c3bcd5bf546ca0b6ecfc9c5a3edc936240ec7490879c110b93dbf98ed8cbf7e924ebefdc92abe99ef23ba7c78d0b94e3b15b694c7b0b35c4c80b28189f7b1390d52b086d7bab0008743ab262085a8d50878a86d5fd0a7e99f86a1791af79fd2b7749b662e2a98990cff97c68475970f279d93d5341b927d020e901291ec8f9141d18e1cf7af8d241f6c8b9357cf8b6ffe258b126ef189ffa51f880a0ae285806b02837a0994830d2b877af38e817ab880477a54ae6579adbf3b79a1804378fe180777d88f1e7700d70874e0a1b47441c198738e9376727c2d4871c79616
  | 6, 0, 2 => 0xffb85fd6ff08955cfe82d1cafdd93ee2fdb6871efd23ec0dfb9651cafb4532b4fb04bddff8f5a88ff7a39a51f5c4111ff3e0083ff2a7fa80efb12452ed49ea9de70ddb49e525038ee3b36130e0faee7c
  | 7, 0, 0 => 0x1c62eaa01c4314361c0fc7181bb3eba81b7734231a489ada1991eef71956825f187af5e418164b9d1803e25c1778fdec170e0d3f16ecc36a16ea5d6a164ffdd3154673b5153f2f4c14b81fcf13d02b00138cc5f6137f022a1269e19511cc6cfa11a07b4e113f7b351102c15910fb20720fb0b31b0f1cde3d0e8587a80d79d9290d77f8140d1009e00ca1f7180c8fb1910b145cd50ac33dbf096edf460909f17008d42a660873b39a07edf008076e6ac507445d200721a55c0715498d067c0c5b066c22b505fc7a3005e991b905c2b37a059bbd0a0593b91304b2bb55041b0ffd039a271f03752aea035e134a035bf2790355613e030b35d00226058b001f71bf
  | 7, 0, 1 => 0x3cf947cf3c50dff73bf0a74b3b8fa0e83ab31eae3a3cef3338bf09ac3845fc4937ace5cf374b07543713f2e4367ed00b365df4243646956435c6e798342a0266337ffdba337e2fdc33131737326ab65b31381a8730da702d30133fa22f2460382f00e81a2ec732322ccf15c72c00a1052a70be412a5e32b72a2802972a04636628b4456527eec4ce2788e50027495f96274531e626bc28fa2621c4c4253fdbed24de2991244e3f2023cd56422329c47a22fc30e2225601032222b3e5222229d1221d02bd21c0fa83216edd2d213ef0b920ea3d8520d8a72d205b87a7203a6ecf1fece27b1fc265421f337d851e8de2b11e3b52531d4c39401ce944151cc675ae
  | 7, 0, 2 => 0x607327d4604dea565f6b8d2b5f4644f85f3ec1a35ece265e5d1b4eb85c80ce835c5ed6485c4f96145ba66f3c5b77c737574e0c8b573a942156db52515559be46552ef96054634bdf524b3b035202422f5201832951d3a487512a7daf50c8658450b033f1508baba8505f14db4ffb6df54fe855494f8214564ebf55304e505f124e0f8ab64df9e3134d89c7244c9af7d44bef55624bd31c844a9d47244a4c280e4a27418d49af22f3494ab295493966f148e20fe348a613ca483158e447fc9de947e917174789b9c646c2bb0e46880b07460fba1b45867d3e43fce5de429326fd424abb9841aeefda40d3f27040aacd643fab50003f3331663e7bd8083def3e61
  | 7, 0, 3 => 0x7fab0ac87f624f1e7e7f11787e31c26d7b5477c17b3c87557b38a1bb7af94a5e7a60c1f7787b7d20786e7c7b77db7f2f77904d8a76eb2f6576e9018376813e0a7621da457574bb5674e65d9174e408bb74c03754749160a2725b8fae717d60bd710bb69670ee382f70d8429870c572a770a33470701466cf6f834a416ead4a876de7547d6d8a9bea6d77114c6d675f566d5098246c85336f6c5800166c24a9f16b6e117c6af8c9c96a9f8b4569692d5e68e5a78d68d45be968bc967467919378676a88366721459a66dac7d566b6c59b667246a264c9defb6432d31a63d7296f632e3b8562d4a6976293bb50627f6546625279a961c9fe1861b055fe610e58cd
  | 7, 0, 4 => 0x9eb46aa69e1a06709d57546c9cbfde239c4680cc9bc597ee9b86c07e9b0a59899aee0930997db02a993732659932a5f99931b1fe98097173978815ed968d45fc963393ff94fe760d94ca0e33931ec531928b369291f684a6918b2c7e916ef3a0912af3d290a6ab8e9079a3d58f713f988ed53e0d8ebb40d88e70429b8e33b09b8e0438848d8249758d3eb5618d146b1e8caf50f58c9d2b3f8bda57218b3dd07c8b01341f8a93bec189fdcdad8937bce189339dea892bca4688c25140885d55ce872e13de870f3af186af0245869c642885c76a5485b93d1f855ef63d84ac9afd845eacbf83eae0e083bfcca3837bd53d830c9e818143ad5c80854292806bf546
  | 7, 0, 5 => 0xbc7c78ffbc5b0324bc5ad31bbc1b5157bbc874d2baa42b90ba8234adb9f22e22b96ba581b8531383b7f766cab7a391acb767aa91b75f91c2b755c7a3b72b7312b66a2cacb5ad745bb4b8038ab4a5f1f1b4a5d9b2b43492bfb3832b99b2a67dc3b1fc71dfb1cd1cbeb094a0e5b0417b40af511deaaf50c27faf34800eae69ee0fae586d90ae5635d0ae21a5f2adf47384add784b2ad479a41ac9d464cac85d81cac159ed8ab3182ceaafe6657aae43935aa2a7239aa29e825a8e4d034a8570142a84580c3a7a46f4aa7448f80a73bcfb0a6fee0c5a6aa2fe9a602b20ba5d26ec4a4c75773a417856ca39dc7a8a36a4139a199ad4ba131a2b3a07a45dba04512f1
  | 7, 0, 6 => 0xd486e115d462db7ed45717f4d3561860d2fb4668d282ca97d26ae18dd1ea6736d1484d94d08ec448d072ee42d047281aceec12e2cd432b93cce8599bccd29adbcc57f4c0cc4ad961cc04a432cbaaa06ecb88a40ecb81317ecb5c26cccb114a14ca91da70ca8818bbca343b4dc9fa83dbc9cbe633c9c56731c9c4dd1dc8e9b08cc868e768c80717e5c8050d61c6f3220cc6e33866c6bfae0ec68d390fc612d2bbc5f6fcb5c549f7d0c499cfc1c47eeda3c3e7970ec3cb5e30c3b27a64c2da578bc2b95953c28f65ccc25e9274c1f42b18c16c44c9c142f441c131a89dc12684b5c0e0353fc04dba9dc004e2c5bf7e924ebe949cf0be07fbc7bdf623f5bd2f950e
  | 7, 0, 7 => 0xf5eb20bbf5d7c7b6f4ecf506f474d66cf3b0323af3967e69f38c9ae1f078f987efe28683efd833eeee9021cced275ae7ed1e7f6eeb9f992aeace37edeab7dde3ea9f1848e9b35c88e98606ece8474abfe8214b0ae805e227e7a7ac33e68e1704e659902ce5df9629e5d5189ce5adc7b3e537ed27e50c9da9e4c93f64e3d66f38e2ba2e19e210bacde0c8841de0b4d820e07b2a37dfe8af95df425275df198746def9b0dcde712d15de6a884ede50b430ddf04437dd7d14e9dd57107fdd561584dd3069d4dbfdce00db6369cadb4f9afcdb2839b2dacce843daa6d415da460ee5d98979dad96b25aed943aef8d9069a79d85e4048d7fd5403d75b3a61d6c71384
  | 7, 0, 8 => 0xff2f2f5dff077c9dfef2edb9fea743f1fe082330fdf64b7bfd5427d0fcc7f5a8fc551edffbc5f651fb515f21f9a39b97f8e000ecf8de9276f87d843ef78b0895f6b508dbf676193a
  | 8, 0, 0 => 0x3ceb1bf83ad68a4b39bed33d39a60da238325070363a340532a7cf853255b3a42fb879da2e4947cf2db95d5e2d6c36d42c674f202bc11f412b8dd2232b8820fb2b792aef2b31f6b329c6a5e527f900ef26f708f725ce08de22fd0d3520792b7d1ff1e5c11f1c08551e233e0d1d53af701d36919d1cf7e4341b0b998c199cbae61887fc7b17f0a5e61745ae2915fa176615ea2dc01519c8151511c41e14fdf20f12d9fd8411032f2c102d7a0f0fe91b5a0fe72a990f54aff70f2dd1b80e8587a80e17cc080da8ed200d862e3b0d7456860cfa623d0cd232db0c3fce1c0acf6a2c08729adb085e0bf70666871c063313e603f2e1770156e3cc009544c0003e590a
  | 8, 0, 1 => 0x7a8dd4717a76d4d476f5ba2875f051ad75c31e547528ba1e740aa9837355347a72d44b9c7290125870a2ce7c708c63d87045e6136ff132df6e4c31696e15510b6d4247ad6c9959c36bfed98e6bf7c76a6b247a4768b16336667ff346660c53db65c9f48664d69a68644d690f60a888ba6046708f6009b6b35dce6a1d5b6d606d5b6ca1675a1b522f59ca331959840b37592d2dfe577aa8f45765015156f4e56256061612558dc52653925fcb52b8402b52113208512cfae54eb13c714e5d34534df9e3134db2c4844c8514524bceeb024b12b9ab49166e3e481d6bbc47e6f64646d63bcf4691fdef45cb505b45bbfe3543a80d714291e3044169bf9e40b62592
  | 8, 0, 2 => 0xb0154e27ae773e1bae3275b1acd55f77abba8fd5ab65cba2ab04cb89aac752a7aa45b81fa65501e5a62afc61a5b19f0aa34cc39aa29cd03ca1748fb1a1093789a0da99e1a03173099ff8643a9eef4aa39af64abc9ada11de9a11c9cc99e4c213993cee429851a7ef98405c4b97db60d996b2205f968d45fc961a6f3395c9e799958b46a59545755f9516af759368ebeb907a592f900e39b18f4f5a7a8ee05a298eb2455a8e3a26c08ce6f37b8b57ffe18a0f88bf87598a3a859fe5508564e97e84f2c6618464689c82f2eadf8274e04181e69b5e81d99ab980fb6bc8806c433a80564da380437db27e4f26f97e2b55927d9bbf8c7c3096787bd60b217b1bd081
  | 8, 0, 3 => 0xde63a60eddc23632dd0b2ddedcc1369edc6664a6dbede8d5dbd5ffcbdada31d7d9b24658d8f7562ad63db919d616304bd5b5f79fd5264043d3fcf8aed365a219d330856fd1723623d05e404acff8574dcf8c37ecce520fbcce04edffcd8606d2cd468893cbfa840aca9fc081ca003fb8c8e9b08cc86e161dc77571d5c6d3d2aec6a97e1dc5c5f159c5866f95c52b7f66c4f74707c4360e95c3ed52ebc34caa51c1628508c10eafeac012abf0bd9fb0fdbcee49d7bc1b5157bb8c28c9baaf8dd9b9ffbf23b89f9e4cb831e6bdb7d50c4db7c38bceb67cebd0b6283af4b608648ab580bd16b5793bfcb3959077b31bd2b3b1db9bf1b0b45387b0afadbeb0a6edee
  | 8, 0, 4 => 0xff563ef9fe581344fcfb68defcf7b91ffc4e8f9bfa387828fa0bc0e3f9316793f930dd7ff90411f7f7c555caf4b5f832f4474a6ff31e7ac6f0a85a1bf0a0a2a5eff93542ee77bbe7ede89359ecd51b8aebc6d37deb7bd90bea8db5d8e9c419f0e884a584e7dc4b53e5943b56e536c5f0e411f253e3e0e689e1687241e0c6589f
  | 9, 0, 0 => 0xfa0bc0e3f531f1bbeeff5994e5943b56df814e89d36b5df6d0e09013c97dca2ec5866f95c4f74707bf935932b4d0e9e0afaf7e14aa7455c7a494ba809ff8643a9db831cb981d63988541295f7cc052b875fdfe5157650151553a09401f6535a417f0a5e609b68333029c85d1
  | 10, 0, 0 => 0xeeff5994
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xaaaaaaaa55555555ff00ff00aa00aa00ffaaaaaaff000000aa00aa00aa00aa00ffffffffaa00aa00aaaaaaaa000000003333333333333333ffaaaaaa00000000ff000000ff000000f0f0f0f0f0f0f0f055ff55ff55ff55ffffffffff00000000ffff0000ffff0000cccccccccccccccca5a5a5a5a5a5a5a500ff00ff00ff00ff
  | 1 => 0xfffffffff0f0f0f0f0f0f0f0000000000000ffff0000ffffffffffff555555555555555500000000f5f5f5f5f5f5f5f55050505050505050555555555555555500000000fffffffff00f0f0ff00f0f0faaaaaaaaaaaaaaaa1133333311333333ffaaaaaaffaaaaaaeecccccceecccccc0f0f0f0f0f0f0f0fff00ff00ff00ff00
  | 2 => 0xffff0000eeee0000ff00ff00ee00ee00fcccfcccfcccfcccee00ee00ee00ee0011ff11ff11ff11ff01ff01ff01ff01ffeeeeeeeeeeeeeeeeaaaaaaaa88888888050505050f0f0f0ffafafafaf0f0f0f0eeeeeeeecccccccc1111111133333333fafafafa00000000ffffffff05050505fc00fc00fc00fc0000ffffff00ffffff
  | 3 => 0xff00aa00ff00aa00fcfcfcfcfcfcfcfcffffffffaa000000fff0f0f0fff0f0f0faf0faf0faf0faf0eecceecceecceecc005f5f5f005f5f5fa0a0ffffa0a0ffffffa0a0a0ffa0a0a0ec00ec00ec00ec0005ff05ff05ff05ff00000000fafafafafa00fa00fa00fa000505050505050505fafafafafafafafaa0a0a0a0a0a0a0a0
  | 4 => 0xffffffff0f00000003ff03ff03ff03ffffff00000000000000000000ff00ff00ffffffffff000000ff00000000000000f0000000f0000000faf0f0f0faf0f0f0aa000000aa000000aaaaffff0000ffffaaffaaff00ff00ff0000000055555555ffffffffaaaaaaaaaaaa0000aaaa0000eeeecccceeeeccccffccccccffcccccc
  | 5 => 0xf0f0f0f000000000f0f00000f0f00000f000f000f000f00ffffffffcccccccc0303030303030303ff00ff0000000000f0f00000f0f00000f000f000f000f00055550000555500005500550055005500dcdcdcdcdcdcdcdcdddddddddddddddd000f0f0f000f0f0ffcccccccfccccccc050f0f0f050f0f0ff0f0f0f00f0f0f0f
  | 6 => 0xffffffffa0a0a0a01313131313131313feccfeccfeccfeccaaaaaaaaa0a0a0a0fafafafac8c8c8c8ffffffffeeeeeeeeeeee0000eeee0000fefefefefefefefefefe0000fefe0000fe00fe00fe00fe0011111111111111110a0a0a0a0a0a0a0afafaf0f0fafaf0f0ececececececececfcfcfcfcccccccccfcfcccccfcfccccc
  | 7 => 0xff00ff00f000f000fffffffff000f000faaafaaafaaafaaaee00ee00cc00cc00fefefefefcfcfcfcccccccccddddddddfcfcfcfca8a8a8a8ffff0000aaaa0000faaaf000faaaf000ffffffffaaaa0000fa00f000fa00f000ee00cc00ee00cc0011113333111133335555ffff5555fffffaf0faf0aa00aa001133113311331133
  | 8 => 0xf0000000f000000afafafafaaaaaaaaffffffff0f0f0000afafaaaaafafaaaaffffffff0a0a0a0a0000000033333333ffff0000cccc0000ff00ff00cc00cc00fffcfcfcfffcfcfca8a8a8a8a8a8a8a800000000ffff000000000000f0f0f0f000000000aaaaaaaaffffaaaaaaaaaaaaffaaffaaaaaaaaaafafafafaaaaaaaaa
  | 9 => 0xff00cc00cc00cc00ff00aa00aa00aa00ffcccccccccccccc00f0f0f000f0f0f00033333300333333fc00fc00cc00cc000303030333333333fa00fa00aa00aa00000000000f0f0f0feeeeeeeeececececfc00cc00fc00cc00fafaaaaafafaaaaafa00aa00fa00aa000333033303330333ffffccccccccccccffccffcccccccccc
  | 10 => 0xfffff0f0f0f0f0f0fff0fff0f0f0f0f0ffff0000f0f00000fffffffff0f00000f0f0f0f0c0c0c0c0fcfcfcfc00000000fffffffffcfcfcfcfcfc0000fcfc0000f0f0f0f0a0a0a0a0fffffffffafafafafafa0000fafa0000e0e0e0e0e0e0e0e0f0f0f0f0fffff0f0ccccccccffffccccccccccccfcfcfcfc
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xb07060a095040d060c0950807060205504131006145041016021550e07060a095041310121150310020f1150310060f095040302010050807060c095
  | 6, 0, 0 => 0x40706021535600031006150934600040321063a156000403023032006000403061524006004b4d10061509600040e0702151160003100e060a0960004100246151160004070615094c600040e0706150960003021811001760004100646150960003061809001760004102515111d60004033130090060000080706020c50004100706151460004070215051160004032e021511600040721060218600043c1306020c60004210602152060004070615050960004150911001d60004072c0215116004303060a0900600100723061509600000b0706020a50000040d06020c5000410021811206000310230218116
  | 6, 0, 1 => 0x4310060a091d6000323060218006000706150c09176000410073130096001f031e1509006043c073e02150c700040d1006150960003150911001760004100615380960000031006020f5000413070602056000403100615146043c3f0602150c700431007060a096043c400602150c70004072102151160022031002181160004101809111d6000407060a0c0960007061509174c600040310021827600021511001d1760004100602153960004100718091160004101509112060004131006410260004070602152b600061509001d17600043c105202156000407150c091160003100215113460004070602154e6
  | 6, 0, 2 => 0xb0310060a096000b040706150960004100615241d6004303100a09116000403102928116043c073b02150c700041310061202600100218111d17600000e0706020a5001c0310021b11600072106021517600041307020c116004b104a06150960004401306020c600100618091d176001c0310061b09600041307060c096000410070615246000810070615096001007021811176000003105002155000413100247116000437100615096001002151120176000403100618246004310020a111d6000702150c111760010070618091760004131006470960010061509201760000041310061250004030602152a6
  | 6, 0, 3 => 0x4032d062c156000310060a0944600041049021553600031031300917600040733061509600040706360215600040602150520600040313020c11600101509111d1760004021811001d600040313060c096000403064515096004f100702151160004061809001d6001f10071e1509600000403100201500031002181117600042f100215116000403101524116001007150911176000410071215116001f03101e18096000403101a1909600043c072102156003d10070215116000323061509006000310180911176003d1007061509600043c104915096000410070215516000403261509006000b04070215116
  | 6, 0, 4 => 0x60218001d176000407020c18116000403102518116000403101215116000402150c112060004100726150960004100618092060003102306180960004310230001d6000407060c18096000406150c09206003d03100215116000410074815096000403102618096003d03100615096000403180911006000413100242116000310020a11446000407330215116000413100642096
  | 7, 0, 0 => 0x403109e06021570004070602150c117000004100726021560004036106021500700000410060218206000003102306021860043041007021511700040310061547097000410060215302070000040706020c18600000403100625186000403106b0602157000004031006121560000040602150c2060004030215115e00700040310150a09117000403061e15090070003103b06021517700040310210215117006a040310021511700001f03101e150960004031006156c097000403107906021570004131007021511700044013100602157000403100602159270000041007480215600430410070615097000407063a02150c7000310233306021570000040310260218600049103060215007
  | 7, 0, 1 => 0x4021511001d60004030615180900700031006150c09177001f0403061509007000403100674021570004030706150c0970003103102151117700040380060215007004304100615091d700040363060215007000403100602157370004031006581809700040310021557117000437100706021570000430306020a006000004061509001d6000403100602185b700001007230602156005c031002151117700040310028e15117001c0403100218117000310310615091770000041007062515600000407062c021560004033e021511007000403310602180070004100706021811700040310061557097000410060215112070004031002154711700000310021511176001c0403100618097
  | 7, 0, 2 => 0x4031006157209700040310062502187000004100625151d6000306290215001770004031006120215700040310064218097000410060218111d700033c1006021517700044010070215117000403100702181170004034010060218700031006591509177000403100215112070004030215181100700031002150c1117700031006620215177000403100215118a7000004102602151d6000403102d0629157000410073e060218700040306590218007000004070602150560004030702150c117000403061509001770004103e060215207000410070602155b7000004032e0602156004304100215111d7000403100706180970004073e0602150c700040310061509207000403103e0625157
  | 7, 0, 3 => 0x4b4d1006021560000040315091100600040306410215007000004031031026c6000003100e06020a600040310021511837000004070602154c6000310210602151770004030602185700700041007021542117000410065815091d7000403072106021570004103e0602181d70000040e0706021560004030215116400700040310061509837000403100215281170004031006257c157000004100602461560004100706250215700041007061542097000431060215001d7001f041006021520700000306021800176000003103123023060004031002157211700040310024218117005c04060215001d700000403310230006000010230602151d60004034d0615090070004073e210602157
  | 7, 0, 4 => 0x40702150c1160043040310021511700000403102515116000b04031002151170000041007061809600040310063a0218700000410061509206000003102306150960004100729021511700041007061530097000403102d06021870004031033060218700040310028c1511700040313100215117000403100602156e70000040706150c09600000403104802156000410062502151d700000310060215346000b0403100615097000403100618091170004073b0602150c700033e06021500177000403131006150970004031071060215700000403102615096000410070602159b7000403103e063a15700040310290218117000403100630180970043040310150911700031060060215177
  | 7, 0, 5 => 0x40306591509007005c041006021520700040306620215007000410290215111d700040306021819007000410061530091d700031006150917837001c0403100615097000403103e0218117000410070215115e700041007061e150970004033710060215700040310610602187004010070602151770004033102151100700049110070602157000403107b0625157000403100218561170004031006a10215700000410070218116005c0403021511007000403100218115e700040310061e18097000403310615090070000041002151120600041007061509117000003102302151160004031006251524700031006580218177000403100696021570000060215001d17600040310061856097
  | 7, 0, 6 => 0x40310062c021870004031025021511700040310313302307000310230602150c700041007630602157001f040310021811700040310154209117000043100706020a6000410063a02151d700040310061809177005c031002150a117000403401002151170004102d0602151d7000410330602151d700043c100706021870004030602153200700043c10060215207000004100218111d6000410073e021511700031006a00215177001f040310061809700043c070602150c700000407210602156000403100715091170003100215111783700040310630602187001c0403100215117000403109a06021570000040706020a0c600041007610602157000007060215174c6000004100618091d6
  | 7, 0, 7 => 0x41007310230600044d10070615097000310060218111770004100752060215700001f031e021500600031006a10215177000403600602150070004034d1002181170000040d10060215600040310021565117000403105a0218117000310061509178470004100702151811700430310021511177000410610602151d7004303103e06020a700040306150a09007000410070615091770004034d100618097005c04031029151170000030215110017600000403660602156000403105a06180970004100706151809700040310021811177001f041007061509700430310061509177000410061e15091d700000410060215386000003101e02159760010065802151d17700000306150900176
  | 7, 0, 8 => 0x403103b0602187000410062c02151d70003100602155b17700043c13100602157000410021518111d70004031098060215700040310021511447008b0403100215117000410070215116470004100615091d1770004820310021511700033106021500177000410880602151d70000043710060215600040310330615097004b0410070615097000403100636021570000040310180911600040310064102187000410061518091d7000403100615094470000043c105902156000403100602159b7000310a206021517700001007060218176000482031006150970000041310060247600040310540218117000010060215201760000431006020a1d6000403100218116470000070602150c176
  | 7, 0, 9 => 0x310061542091770010060215111d17700040310061556097005c0403100218117000310070215111770003401006021517700040310310618097000403106d060215700004b104a06021560000100602181d1760010073e060215177000004031002152760004031002181b1170004105a0215111d700001c031006021b60000040310021811600031007061509177000004130706020c6000004103102301d60004031006181b097000008100706021560004105a0615091d700000410071509116000403103a0215117000410070641021570004100215111d1770004910310021511700031006581509177000403103302151170003103e060218177004b0410070215117004304060215001d7
  | 7, 0, 10 => 0x43c1007021511700103e0602151d17700430403061509007000403100218115d700043c401006021570004033c1006021870004031015180911700040310067a0215700041007310215117000403100659180970004031093060215700000b0407060215600040310020c1811700040310066202187000403100218113270004031006150985700043c10070615097000403940602150070000430310020a116005c0410070215117000403107d0615097000004101509111d60004100731061509700005c031026021560003100215421117700040310060c180970004031080061509700040310021556117000403103102181170000430310060a0960000040310062928600040310950602157
  | 7, 0, 11 => 0x40310061505097000403210602150c7005c04100215111d7000403100215181170004030602181100700003d100706021560004034d101509117040310610602150c8000003100618091760000043c104902156000403105a15091170003102902151117700000403260215006000403100602185d7006f040310061509700031006153009177000004106706021560004100706591509700000403103130096000490100602151d70004100706620215700430403021511007000403102c0215117008d04031002151170004100e0602151d70000220310060215600040310150911177000403107506021570004030629021800700000b031006020a60004031088021511700040310021511857
  | 7, 0, 12 => 0x42f100602156000403100218571170000040310061524600040310020a18117000403061e02180070043031006150a0970004031002158611700001f03101e02186000403106006021870004107f0602151d7000403106902151170004100706154709700001007061509176000310063a021517700041006150c091d700000403101a0219600000410070612156000403100215051170004100748060215700040310061857097000403103106540270003102d060215177000310330602151770004031026060218700040310060a1809700040310210602187000003230602150060000031002181117600043c10073e02157000310061509111775c043c1007060215800000403062515006
  | 7, 0, 13 => 0x406021530001d7000403100615094c70003103e02151117700760403100215117004b04031002151170004031054021511700040378100215117000403100e06150970003100615091785700001f10071e021560004100760060215700040381100215117000406290215001d700760403100615097004b04031006150970043031002150a11700040378100615097000403104102151170004033e0602180070004031077060215700040310067c02157000004031002303260004100706150a09700033123060215007000410070215471170004030602155b00700040381100615097000010070215111760003100215115e17700041002150c111d7000410066202151d700000310060218176
  | 7, 0, 14 => 0x410070612021570004030215421100700040368060215007003c100706021517700041006150a091d7000410210602151d7000440100706021870000100215111d1760003100615180917700041007021511207001f0310061509177000410070602155370004401006021520700043f070602150c7000410074a061509700040306582c021570004030625021500700040306154209007000406021511001d7000440070602150c700040310660602157000310630602151770004039010021511700040310311530097000004031306020c600040310060215707000004030602451560000100615091d17600041007061509207000403100e021511700031002151117857000004060218001d6
  | 7, 0, 15 => 0x403101a0218117000403100602159970004032902151100700040306153009007000410070215118f7000403109f0602157000403891002151170000041310060242600048710070602157000403101a06180970000031006020a446000003103102301760000040733060215600043e060215001d7000403100602152b7000403100218115f70004034d06021800700040310150c091170004031006181909700041007064915097000403060215650070004031006021524700049d1007060215700041002150a111d7000403100602154e7000310062c02151770004031006021535700001f101e02151d6000403107f061509700031002151811177007e040310061509700040331062902007
  | 7, 1, 0 => 0x3d031006021560000031015091117600430403100218117000310064102151770004131007061509700040310060a0c097000310061509174c700000403021811006000406021518001d7001f04060215001d7000403061509110070004820306021500700430403100618097000410060215209c700031002151164177000410065802181d70000040306180900600040310065502187
  | 8, 0, 0 => 0x403100602154770000031006021517600a504031006021570004031002150a117000403061e021500700001f03101e02156000403100602156c70004031060060215700430410070602157001f0403103102157000403102606021575c0403100659021580004031006150a09700040310210602157006a04031006021570000031002151117600040310a40602157040310310602150c8000413100706021570004031006020a0c743040310060215118000310060215174c704031006580215428000403060215110070000031006150917600430403100602187000403100602155d7000004030602180060004030602153000700040310060215327040340100706021585c040310310602158
  | 8, 0, 1 => 0x4031006021528704031006021542118000403100215115f70004034d06021500700040310060215727000403100602421870003100659021517704031007060215118000403060215001770004401007060215700040310070602187000403ad10060215700040310060215207000403060215180070003100602150c177000403100602158a704031007060215308001f0403060215007000403070602150c7004304100602151d700040310065802187000004060215001d600031031060215177000403100602155770004031006021597704031006582902158005c0310060215177040310065902150c8430403103e0602158001c04031006021870004033e060215007001f5c03100602157
  | 8, 0, 2 => 0x5c0403060215007000004100602152060000031023060215600ab040310060215700041007060215307000004070602150c60043040310060215700000403100625156000b040310060215700040310060218117000410070629021571f040310070602158000403131006021570000040310260215600040310060230187000403101a0602157004304031002151170403100629021511804031006580215188000004030215110060403103e06021542800040310062902187040310630602154280043040310061509704031006290215308000410065802151d75c04031006aa021580000040306150900600040310060215837040310073e06021580004031094060215700041007060215427
  | 8, 0, 3 => 0x403106806021570004031006021817700040310062502157001f040310060218700040310061542097000410060215111d7005c03100602150a7000403100702151170004034010060215700a804031006021574304031006a602158000004100602181d6000410073e060215700040306590215007000410060215301d71f0403100629021580004031007061509700031006021517837001c04031006021570403100641021542800041007061e02157000410062902151d70004031006581509704031006292c02158000403103e060218700031031230602157000403100602155b700040310061e0218700040331060215007000410070602151170004031006021856700000410070602186
  | 8, 0, 4 => 0x1f04100602151d7000403100602154470004031006150911700048203100602157000004031006180960403100629a3021580403103e06021517800044d100706021570004031029021511700040310061530097000403100654021870403103e06021518804033c10070602158000310060215178470004030602150a0070004103e0602151d7000410070602151770004034d1006021875c0403100706021580004ae0310060215700040310060215657000403105a060218700041007060215187001f041007060215700430310060215177000410061e02151d7005c040310062915700000306021500176000403103106290275c0403100658021580004031002154211704031006021518118
  | 8, 0, 5 => 0x4100615091d6040310063a02150c80003100602154217700040310060215567040310062902150c8000403103e0215117000403103106021875c040310060215118000403100602155e700040310610602157005c04031006021870003100706021517704031031330602158000403100602181b70004105a0602151d700000410070215116000403100215115e700040310061e1509700000403100602186000310065802151770000041007061509600040310063a021570004100602151d1770004910310060215704034d103e0602158000403102d060215700040310330602157004b04100706021570403105a3e060215800000403100218116000410060215181d70403103e060215868
  | 8, 0, 6 => 0x31006021530177005c04100602151d70004031006021518700041007065902157001f0403100602157000004031031023060004034d100615097040310061e02150c8000403105a061509700031006290215177000403100215111770043040306021500700040310062c0215700040310021518117001f04031002151170004031006590218700040310061509177000403108806021570403100602150c1180004031006021585700043c10070602157000403107d0602157000004100215111d60004031006151809700041007310602157001f04031006150970004031006020c1870004031080060215700040310630602157000403ac100602157000043031006020a6005c0410070602157
  | 8, 0, 7 => 0x430403100658021580003103e060215177000403103b060215700760403100602157004b04031006021570004031006540215700040378100602157000410070602150a70004038110060215700040310060215647004303100602150a700000403101509116000403100641021570403103e21060215800041007060215477000010070602151760004100602150c1d7000403100602185770004031006020a187000403100602158670004031002151164700040310a7060215700040310066902157000310060215111770403103ea9060215800040310060215057000410310602151d70004034d100215117000003100602181760403103e0602150c8000403105a0215117006f0403100602157
  | 8, 0, 8 => 0x403101a060218700040306290215007000403100215115d7000403891006021570004033c10060215700040310065915097000403103106021570004031002150c117000403100662021570004031006021819700041007064902157000403107f0602157007e04031006021570004031006150c0970403103b0602150c8000403103102151170004100602150a1d700031006021518177001f0310060215177000410074a0602157005c04031002151170004030602154200700040310310615097000403103102153070000100602151d17600041007060215207000004031002151160403103e0602150a800040390100602157000403100602154c7000403100e060215700031006021517857
  | 9, 0, 0 => 0x403103106021575c040310060215700040310060215600040310021511600040310061509604034d1006021570403105a06021570403100602151770403100602151871f04031006021570004100602151d60403103e0602157040310061e021570004100706021560403100602151170004031006021860403100602153070403100629021570403100602154270403100706021570403100658021574304031006021570004030602150060403100602150a70003100602151760403100659021570403100602150c7
  | 10, 0, 0 => 0x403100602156
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
  | 0 => 0x3e233e02200e03f8000001e0000e00003e00000000000000000001e0000fffffc00001e00000000000000000000fc78e7fe0f1fe100e000000000000000e00003e0000000001c38639e0301e000ffffffffffe1ff00fffffc0000000000ffc003fffc00000003871801f0e01e00e3c79c7c30e1c2001fc07c1ffc01ff
  | 1 => 0xffffff9e0301e0001c38600000000000003ffc0003ffff00ffffffe233e02200fffffc0000000000fffffffe33e1e2001c38638203002000ffffffe233e02200000003ffffffff0003c79f81fcfe1f000000001dcc1fdd00fc78e7fe0f1fe100e00003fdcc1fdd0003871801f0e01e00e3c79c61fcfe1f00e03f83e003fe00
  | 2 => 0xffc0001dfc000000e03f800000fe000003bf1b81f3e01e000007000000fe0000fff8ffffff01ff00ffc0fc7ffc01ff000387181dfcffdf0000000001c0001c00e3c79c61fcfe1f001c38639e0301e00003871801f0e01e00fc78e7fe0f1fe1001c38600000000000fffffc6030e00200003f038003e000001ffffc1fffffff
  | 3 => 0xe00003e0001e00001fbf7b9ff3e1fe00fffffc0000000000fc3863fe0301e0001c38639e031fe00003871801f0fe1e001ffffc03fffe3f00003ffc1c03ffff00e00003fc0001c0000007000000e00000ffc7fc7ffce1ff000000039fcf1ffd0000380380031e0000e3c79c6030e002001c38639fcf1ffd000000001c0001c0
  | 4 => 0xfffffc6000000000ffc0fc7ffc1fff00ffc0000000000000000003e003fe0000ffffffe000000000e00000000000000000000380000000001c38639e0301e0000000000000000000003ffc0003ffff001fc07c1ffc01ff00000003e233e02200fffffc1dcc1fdd000000001dcc0000000387181dfce01e00e3871be1f0e01e
  | 5 => 0xe3c79c0000000000e3c00061fc000000e007806000fe0000fffffc01f0e01e00e04084600c1e0100e03f8000000000001c00039e000000000038038003000000ffc003e230000000e03f83e003e000001fbf7b83f3e03e00ffffffe3f3e03e0003c79c01fcfe1f0003871b81f0e01e00e3c79c61fcfe1f001c386061fcfe1f
  | 6 => 0xfffffc1c0001c000fc78e7e20f1e210003bf1b81f3fe1e000000001c0001c0001c386001c0001c00fffffc1dfcffdf000380001dfc0000001fbf7b9fffffff001f80039ffc000000003f038003fe0000fc78e7e20300200000000001cc1e1d001c38639fcf01e0000387181df0e1de001fbf7801f0e01e001f871b9ff0e01e
  | 7 => 0xe03f838003000000ffffff80030000000038039dcf1fdd000007000000e000001fbf7b9ff3e1fe0003871be3f3e03e001fbf781dc001dc00ffc0001dcc0000000038039dcf000000fffffc1dcc00000000380380030000000007000000e00000fc78e7e2031fe100ffffffe233ffff001c386000001e0000fc78e7fe0f01e1
  | 8 => 0xe000006000000000e3c79c1dcc1fdd00fffffc61fc000000e3c0007dfc1fdd00fffffc01cc1e1d00000003fe0f1fe100ffc00001f0000000e03f800000e00000ffbf7bfff3e1fe000000001dc001dc00000003fffc0000000000039e0301e0000000001dcc1fdd00ffc0001dcc1fdd00e03f801dcc1fdd001c38601dcc1fdd
  | 9 => 0xe007000000e00000e0000000001e0000e3871801f0e01e001c38601e0301e0001c78e41e0f1fe100003f000000e00000e04087fe0f1fe10000380000001e000000000061fcfe1f000387181df0e1de000007038000e000001c00039fcc1fdd0000000380001e0000fc40e47e0c1fe100ffc71801f0e01e00e3bf9801f0e01e
  | 10 => 0xfff8639e0301e000fc3fe39e0301e000ffc0039e00000000ffffff9e000000001c386000000000001fbf780000000000ffffff9ff3e1fe001f80039ff00000001c38601c0001c000ffffff9fcf1ffd001c00039fcc0000000000001c0001c0001c3863ffff01e00003871bfffce01e0003871b9ff3e1fe
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x24c9ad533ad13300f23f82a8853e8800f6edaff9ac991100200980a8853e8800fffffeb98d3f990024c9ac1108111100b468a6b80d1d8100f6edae1108111100f22403e8a48800009d3a739e5345e600dff67f577ac17700fffffe1108111100ffe403fffc8800004b975947f2e27e00460c20dc6185c4000dc07c17580177
  | 1 => 0xffffff9f5b55f7009d3a721000010000001bfc000377ff00ffffff533ad13300db36520000000000df3e73de73c5e6009932530212402200db36534232c02200000001eef7eeee0090e18f890832190024c9acbdcd3fdd009468a61009158100f6edaffdedbfdd006b9759eff6ea7e0062c58c61acba1900f23f83e8a7fe88
  | 2 => 0xffe403fffc880000f23f83e8a7fe8800dbbf5bcff3e6fe00621f81e8a7fe88009de07e17580177000dc07c17580177006fdffdffffffff0024c9ac15c8335d0042040060a4aa0800bdfbff9f5b55f7006fdffd57faf37f00902002a8050c8000bdfbfe1108111100fffffe5128911100d23f03c8a3e688000ddbfc175b77ff
  | 3 => 0xf22d83e8a5be8800dfbf7bdff3e7fe00fffffeb98c191100ff3e73fef7cde600bd3bf3bed77fee006b9fd9eff7fefe0009d3dc031a723b00041bfc9c4377ff00f62c23fce58dc400421f01c8a3e688004fc47c5778817700000001aed76eee00b03b83a8877e88004204004020800000bdfbffbfdf7fff000408209c4105c4
  | 4 => 0xfffffe71ac9911002dc0fc375c197700ffe4021108000000000001e8a7ee8800fffffff9ac991100f2240200000000009020038800000000bd3a73bed74de600200000a88408000024dbfc110b77ff002dc9fc17581177000000014232c02200fffffebdcd3fdd0024c000bdcc0800006fd759fffeea7e00fbb75beff6ea7e
  | 5 => 0x62c58c010810110062c40061ac88000062058060a4ba0800ffffff57faf37f00204084200c180100f23f8200001000009d20039e50000000903a038803448000db24034230800000d236034022c00000dbb75b47f2e27e00dbb75b47f2e27e0000c18c0108321900dbb75bcff2e27e0042c58c4128b219009d3a7270a4ab08
  | 6 => 0xfffffe9d4915d500b06086200c180100fbbfdbeff7fefe0024c9ac9d4915d500bdfbff17da737f00ffffffffffffff006fc401fffc880000ffffffffffffff00ffe403fffc880000f23f83e8a7fe8800902002000000000020c18c218c3a1900bdfa73bfdf4de6004f9f79dff3e7fe00dfbf7b57f2e37e00dfb75bdff2e27e
  | 7 => 0xf23f838803548000ffffff990b559100b4fbafbdcf7fdd00621f8140a2f20800ffffffdffbf7ff004b975947f2e27e00dfbf7a9dc127dc00ffe402bdcc080000b4fa03bdcf4c8000fffffebdcc191100b03a03a8874c8000621701e8a6ea08009028a60001158100db3fff4233f7ff00bd3bf2b8853f880094602610080101
  | 8 => 0x62040060a488000066cdacbdcd3fdd00fffffe71ac99110066cdacfdedbfdd00fffffe318c3b1900000000a8050c8000ffe40357f8800000f23f8340a2f20800ffbf7bfff7effe000489289dc127dc00000001eef48800000000018e5344e600000000acc52ecc00ffedaebdcd3fdd00f6ffaebdcd3fdd00bdfbfebdcd3fdd
  | 9 => 0xf2370340a2e20800f22d82a8853e8800fbb75b47f2e27e000d1a70165345e6000448a41009158100d23f0340a2e20800204084a80d1c8100b03b82a8853e880000000060a4aa08006fdffddffbf7ff00d23703c8a2e20800bde9afbfdd3fdd00b02983a8853e88002440a4300c190100fff75b57fae27e00fbbfdb47f2f27e
  | 10 => 0xfffe739f5b45e600ff3ff39e5355e600ffe4039f58000000ffffff9f581111009d3a731652416600dfbf7a1100011000ffffffdffbf7ff00dfa403dff08000009d3a729c4105c400ffffffbfdf7fff00bde003bfdc0800000d1a719e5345e6009d3a73fef7cde6004b9759eff6ea7e004b9759cff3e6fe
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 175 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem wd_0 : ∀ i, 0 ≤ i → i < 128 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem wd_128 : ∀ i, 128 ≤ i → i < 175 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 47 128 = true)
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 175 → wireDOK i = true := (range_split wd_0 wd_128)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 175 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 175 then wireAt i else 0
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
  | 5 => 29
  | 6 => 589
  | 7 => 2250
  | 8 => 402
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xf786cd9ff1bee322ebcd4035e9efea94e5ba5368d8b6dcf4d41b51d2ccd24605cb370802b752a1ffb3d5e20a91f2919c7701a58a714bff296c247170665c86f35f7dae01592f289b567e7da84006257f30d6be852aca561b244f25ce19fa4ff018a841b216fbcae110fc0a0109535e96026401b9
  | 6, 0, 0 => 0x1d81b2001b3c9c941a174f681a14e5e519988118187d16b5180152bc17f0a5e617d2438017cc11df17c1ebe717464e4d170eadba163fc5a7158b722b1566718f153dcc6c1519c81514d6fd901404629b13b3f324139e13b8135968a412a960a4121267d611f97611119a5242117e63d0114905c3102cd8da0fe48c6c0fb5727a0f3a1b4e0f2adf9f0f1deafe0ec374710e8587a80d467bd70bff7b090b08b4e00ac33dbf09e0271d090afe3108b86e9b08729adb08439d1a082f340407445d20066807c6065a428e063313e604ffce3b04f5c81304a9595104510578035f4404035e134a03132982024e61ef0234fb4a021c4737017ff6500128b8dc00551af9
  | 6, 0, 1 => 0x3696e6af3677262936344bbe36321d73360aca1735c206a13593436a3549cd763491099b345d16ec32d1736f328177663243d93d323ee5d931ca69c43164ffec311ff4ee30df3c5a30c61fd030622d693035338730215ef12f46bbda2f2460382ef6c5642ed2d5962e8b19db2e5598682df076192dab67df2c0bc0272bb077e22b1751dd2b0d08212ab692012a2246ba29e37fda29bcf0fd2991d48728f408ff28898d04283f6a3c2801c4742767152426394f172633bb23260d62e925ce08de259e3a8324bb54ab2490d772242aa86123e6e87423d0930d237ee7ba234f1909224e350d2232841622238267221aab7020dedb3c1ee05f901e8dc32f1e6d8f8d
  | 6, 0, 2 => 0x5425afd05373df75534063a752ee48045241ef005202422f51e628db51cefb51512cfae550c9fa1d50bdc31d50a2cbfe509e91be507a3152503143444ef3f3604e1924c54df12d004ddf67e54d89c7244bceeb024b3122304ad6a7414ab246d54aabe3f64a8fdf314a4c280e49c9f37f496e258f48cb580e489c303747f45c5d47ecdf1247e917174601d1f545d9e97145bbfe354588d52244d52e8143e88e404382942442886e9b41aeefda411e661940014b533fc5bf033f75e8553f6da6c93d146e793cc9d2003c1116213c0e93da3c0e2ec23bf445043b68a4c73b5b2de73b4d423b3b2c66543ab31eae39c163c838bf09ac376d387836c973f436a9a2b2
  | 6, 0, 3 => 0x6fbfac806e51c5c36db419bd6d7f0ccc6cf0df106b60f5cc6b22189e6adfcf8d6ac5beb26aa03c2c69ff04066998c2f66901454a686fe2d9686734a767f6361967aa7ebd6738f6ec673816326721459a6714a00d6701efa266cf440666c2a48165bca57265a7926f6569df09654e08ff6513559763ec173963b5648063386b0e6277a2c26227358061fa7e5261b055fe6162e1b45fd6f0065f23c9295e627f475e1e9add5dc3e61f5d6e1a9c5cd2b11c5c98a9f65c3f1af15c0463895bdd43db5b9346c25b6d606d5a1b522f59ca331958b23402585c6480577aa8f456f4e56256dce6ea56b3a933569798095685bd295685ad9a55c8aff654e4c26e54b4c80f
  | 6, 0, 4 => 0x8f9a02ed8efd00728e40ef1e8e3807538e1e008b8d7aa69e8c8bd4088b43c5fb8afbeac48a24058b8a1bf12189bd1d528983c22f892bca4689021a1088251a86880b13be870f3af1869ce49a859d226f84e8fdf784e39a56845eacbf83bfcca381b835c0809a57747fd1d1f57fc0ac087edfe9387e2b55927e039f467d9517757c26173b7b79def87b4fb03a7ad8f3527a4107f7797837fc7917febb78d467eb78a4914177927972776cd09d7767d3b1767b1376760010787513da2c74d2b7c574c037547498f076749160a273f16f8473e04a0973a8bc2372dca6c472a12ecc72624b8c71f17c8671887344717579e1714f0c817135056b708c63d870732d12
  | 6, 0, 5 => 0xaae43935aab6846daab4d42eaa595a1aaa1d7978a95e76b3a7ddb0e3a7a608b6a7448f80a6ec21a1a6e17d0ea66be917a64dda14a63cb499a3520e49a333f77ba2a8aa7ca26210f3a226f95fa192eb4ea1093789a0edce5a9ff8643a9ed54a0f9e2bfccf9e05a4959d5943639ce0bfff9b9568059b6479ac9b0308ba9af64abc9af403229aee09309a876be99a2e490199a21096997db02a98c25d4298bce0ab9746569696ef1d12968d45fc965463b994fe760d94f8972094cc47c094747f1c9389b308934f4be99287054b92485c0d920d2791920ad07791a8c5f3916f132a9122fac290dc304590d04cb990c02cef90b7ddef907a592f9036f2589031ee2c
  | 6, 0, 6 => 0xc4801afac4360e95c431ba92c37f6552c2b95953c2935ce8c223f24bc1297554c0d9f649c0be6b72c074ca6ec004e2c5bff3e190bf7329dabf7034c2beb16106be511fa3bddfbaf1bd66b44bbc01bf86bbb11754baa42b90ba61dda1b9a84a45b9a80cbbb96ba581b8eadc5db8531383b83cf1dbb7f98cffb797c174b7244a60b6f7ed88b6eae39db6e97f2eb6c19b56b6283af4b60f042eb608e4fcb5eed2b9b5bc09eab5a9ee5cb59e2a87b564e8f1b4fdd74ab324a800b22a050eb2255685b12194b1b0d7f6d0b0afadbeb0646677b0154e27affc1761af93fa6eae23c6c3addbe416adb8f583ad99d61fad85de96acfd4defac8c280eac79c95faae9e01b
  | 6, 0, 7 => 0xdee4a53ede9f565dde3999fbddb99ffddd929700dd358d4ddc2d6e24dc0933a3dbda9941daea1147da5501eada1de6ddd97cb2c4d92afae5d8d1b871d7d85cbed77faa33d6eeac03d6a7650dd616304bd5253991d511e5c9d50c1e7cd47493d7d41a35bfd3d58587d3936b1ad365a219d31a133fd25f599dd1d1b1d3d0df7a90d0d31662cfc32efbcfbfdca7cfa1f550cf568aebcf4f0260ce524b42cdf4a4fbcdab1c21cda6eadacd34cb17cd13e886cc6860d8cbc7053ecb90a2accab4f72eca480577c9fa83dbc992521fc985e45ac91a9690c8e9b08cc82c96b4c7982f54c74adca0c6d1583fc655740bc6116671c5ca0232c56cddc4c52129fac51c2ccd
  | 6, 0, 8 => 0xf76ed223f681dfc8f6281ae1f5c8f14af52fd18af4c36b61f4a487fbf4166d44f366bb19f3261b24f2d134fef2a5b19cf19b55fef0f659b3f06ef2fbf06e0b5aef6679f2ef452d54ef3cea48ef1ce4bdee5e2a16edca1a3bed6d2ea7ed22c06eebf3eccbeb28025ceaf45351ea995c6bea8b727cea329cb6e9fa7c4fe9b81452e980b4f0e9474e2de939392ae8b69696e884a584e86b6ebee7dbb335e7b72d6ee6be1fffe6b644fee620e160e620dc5be5fdcd2fe5e7d7ace5e5ba74e5943b56e58a167ee4b721c5e390825fe3714eade3487a1ae2b4f325e2a3a9c9e1c8c668e09b71a3e058f6e3df4b618adf3de7b2df198746df06686fdefa314edef769d9
  | 6, 0, 9 => 0xffa38cbeff89ad14ff077c9dfeece16efe3a4b55fe029cebfce87415fcc7f5a8fb3a01a3f9ab63fef8c5e63ef7d3f690f7c5dc2a
  | 7, 0, 0 => 0x7e7cc3007c54ddf07af3f5d07a58cff07893d0c0777e528077551060774f8470760f7ce074d54be0743e7350737dedd0717e18d070cd64e06fa24be06f4682806ce33a30666871c06647db70633812b063313e6061c4c9605df2e75059a9b09057fe7040529fa4f0505111504fa5c8f04f3a90a04afa52d04ae569104a51fe10489544c047b1532043dfd4e0438b537041cb05b03cb7e2903800384035bb98b033d2064033bcf23030aa55f02f807ca029c85d102917d28024e07b60206ca5101fec3c701ec392301a9edce016a2c5501626439014e30ba013b914201317fca0130fa680124f2100114c18a00f72f1500d9f06100b2528100379789000d71aa
  | 7, 0, 1 => 0xf018eb40ef0b7720eddf50b0ed7415d0ec5633b0ea533020e9c34060e4a3f3c0e17cc080e1752730dd83aac0dcd0eb20db911f10db856600da59a5d0da3dff10d9246660d8ad1f50d862e3b0d4ea6490d3627210d32c3940cf8018b0cd232db0cba76dd0c7f0f820c4e5f240bec4eb60b8d8e810b69e2050b3053740b2e440e0b1d86e60b1a6bef0aeba37c0ad264b60acf6a2c0acf08c90ab80cae0aab49810a64e1b90a3ea1980a3a0d400a30404f0a1eafdb09e33ae009d62c9209b6833309aab2f009a98b08099dcefe0988b3e109747a0f094077ba09403d9209191f43090c697f08f19f4508c6500e0893043408830b5008729adb083d0d09080465a6
  | 7, 0, 2 => 0x170efe2f16e19d9a16ca50b116b5dda1166b69471650114f15fa176615d84d9915c667dc15af3009156ed308156d2d4f14fdf20f14c583ac147f072014521e1f143c04ee142322271404a56e13ee22a313bdf11913ab6cc313891184138330ff13756256136d90d2133d7a46132cf8e213100f2312dbd9cc12d9fd8412a44300128c11a11289bf3c127d79e41228f0ad11fdbf3c11c1e546119a5242117b124510d68feb107595fd105120261045a0e0102cb7d210068c150ff627ad0febbbd80fe17bff0fc560cc0fa9c1e20fa417e00fa016b80f97b7810f780a210f69177a0f686dc40f61488e0f5f94050f54aff70f4544c00f3a80ac0f2dd1b80f2197c9
  | 7, 0, 3 => 0x1dde5da61dbcafca1dbaecd11db5c7de1db1ce391d8beab91d8428691d7779101d6ab1761d2a5c381d29b90f1d21eafc1d0931f61d06cf9b1cf843df1cde0b751cc939d11cc486e21cb79b7c1c9756be1c63b9a01c1928291c129a8a1c0a15f01bfcde181bd08aa81bbb6cc21b801a1c1b7d86141b771a861aebd7691aea5eef1ac4c55a1a89b2fd1a7a57991a41a0c21a13a90e1a03ef6b19dd3a1b19d0402319c31065199cbae6199bfe5119930f07196feb9719436650193d4cd31928bdfb192439d7190ee20018fa379218ea819418b72fcd189f06ef187819b0183679a61808ead417f0a5e617d4d21317cfe3431798c2df174358ea171ddab2171bc73b
  | 7, 0, 4 => 0x2516223e24ebe0d324bd924f249b5ca6248e04d624473a2b2434c45623c66e1e23bea9c523a02b6423619af92352624223317b5a2328f9832309b3c52303bfa722fe2d4522e5fd2122db09d522d2e89b22a531a622a43a052293dc39228f58152284dc61220818b6220503cd21f4ef7921e2144c21a18b1721758804213c2611210b6317210b522120fec43620ee76c220de29ff20dac52720792b7d20764d7c205d250f204d4779204966a31fef95911fda0bbc1fce75a31faae3e51f6535a41f5c0ca71f507a471f4f43ba1f0a2ad11f0851631eda4df81ecb3cc41e9d87531e7c6a761e787f8a1e6a14301e6733e61e4c683d1dfe83a11dfe3b7a1df9c469
  | 7, 0, 5 => 0x2d6c36d42d4b74a62d0b49a22d06a7892ce19c092cd24e8c2c59e72d2c1ac5352c03b6d42bff46732be9541c2bc11f412b8dd2232b662f122b35ce122b34637e2b31f6b32b1e8f872b1e48cb2af23f092abf42042aade4d82aa228122a7bf7562a4104882a180ad529cc814929b3667a29a27822299e0a8b2998e5e0297263fa2971218a293cb1472923a8d928f8e9ee28736fa1284c956e2843639b283ee929282b0260281c5a692807dc4627f900ef27f5011927d8adcb27ccd79227cbd9f1279d34b42764e2a7272bd80e26f708f726ecdaeb26a6147c269bbbd526724f6326716cae2667fbbc265938522610fb7c259c91d0259c2a0f257b0961253dfff0
  | 7, 0, 6 => 0x350afbf135050c0234fcc10534fab66d34bcf6153483698b3475d36a346940893423f6ed3423b89d341901f53414d76d33b3de4c33abe670339b6de13366d858335ff7c2335a55be334e9e183333a5b832dfa60432d0d1a432c778e432c76fd732a7cf85329827de32940219328be19b327a00333276a5c1323533b6323189e431f9198e317fcb2531662a1e31313598312e73113098ad6d3076c1bc2fb879da2fb055c52f9eb1222f755c332f61fdbf2f55ca092f32ac792f2f932e2f14e5f92f08d6592efc3d862ee917cc2e9635332e4947cf2e3def2d2e01bef52deb9a982db95d5e2db021812da6e06d2da66f232da64bb72d9337d72d7296672d6d10ed
  | 7, 0, 7 => 0x3d5dec943d4e96ec3d436a713d26dfb13d1efc8a3d1ebcd63d0a06bc3d07d3283d020fd93cf5f1c03cf2f7563ceb1bf83cce35373ccaa2d03cc14c493c8249c83c820d253c5afe723c071d803bfc88ae3b7b0b8e3b4a6f143b3588023b1de8be3aeca3da3ac4ab823a6fc2fb3a57bf6c3a54f6eb3a37a85a3a3459f239dc95ba39d1bb9639a051c5399863333994496d396d428b396b351b38dc31f638d876eb38bf2ecf388cfc463873f497386d36983853cc1837e4a27d3792b7f2378f7ea9374c6156370bd009370b3fcb36ebeecb36bb486a3665a2d83650d299364de9bc364a88ff363a340535fbbb4b35efb7cc35e8ec4c35427ffb353b3391350e98fc
  | 7, 0, 8 => 0x43bbcef543b2960d43684b3a4356eee94345dd8a43310032430f11184307b1bf42d860c942cfbda542c9f63242c60ab342ad8ab642a739ed42a1145242938fae4252923d42391a64422a4d0d421a0a4d420d9c88420b7036416ff7344169bf9e413a5f9b412e27994122ba3f411dbffc4114e18340ef18be40e506b040a6a9cc4085327d4073bd03405336a0403b3cd0402052ea40114274400204ed3fecf6043fdae0823f98b8343f965bf93f75e8553f5b723c3f3d268d3eef1ec33eeb63b83edb7a123eab89f23e86703c3e6ca6e33e65d4ab3e5dba0e3e5a19393deb184f3deaab903dd6474b3dc868bd3da8e2283d9b44b43d99f9393d8950fd3d6a38ea
  | 7, 0, 9 => 0x4b139a5d4a6fcc964a6e21814a5a36fc4a4ca1ff4a2aab494a1b963549dbf98049c6ea2f4991f19349633728493931a44937960e4933dad8493049d949166e3e49153a3549119e30490261c948d8f78048ae4aba48a67c7b486ba47c482b111848186c2347f18e7a47e6f64647d7c52147a6de7547a321ed476d95e94760553447475e20470a84e246d902da46cf27fc46bd63254687e3c446571df2464e299d463b029f4613374e45fbb87d45f42d4a45a948c64588d5224574248b45690ae9455025de45461e334538ef404533275544fb624244e1b40644d3b0f944b9bc4944a9c6b244a6370444a5eedd44932a8144185ada441454c043f56eff43e93418
  | 7, 0, 10 => 0x519eacd0518dc5f4517e7bcb5154fd10513de1c0513785fd510eadad509d90eb5086ebaa4fe12bdb4fc20fc04fa88ab34f9eecaf4f7e558c4f7664314f7636814f7203ae4f248afd4f20a1d04f0f1c0e4ef710314eea32dd4ee69c8c4eb13c714ea461854e9499964e8d76614e79a1c14e5061c24e4f9ac64e4bc3504e1f4e0c4e1a14854e16faff4e1549714ddc84ac4dd3eb7b4db94bee4dacf1bf4d948e4e4d7443cc4d55c85e4d436f384d3b1b904d2adf594cf3253c4cedb2624cc5254b4ca9d7894c8adfa44c7b2d784c6a0abf4c6848c84c620f5f4c0054d34bf528d94bee965c4bebe8c14bd749734bceeb024bc64fed4b85288b4b7b05914b643fc6
  | 7, 0, 11 => 0x58053a1057f8949f57f4821b57eec11057de754257ddaa8357ca1874579ceee1577d401857650151573d6a7c572a73a15717156e570f5c8956e43a5556b94ef15692d977564f0e11564be97b56298ade5606161255fe3f2655f89c0955e6dc5555aeccd2558dc526557fdd00556b7311553a094055338e9d55268b875521b6ce54f8683a54cf5e0454b43a78548cbc44548c8e8e54796d4d545c29f85428dc8453d77a3d53cac47953ca8d5d53c6a42253b5587e53b52331538faa4d538855f6536ad34653501ffc532a2e0f531ddda1530fcb365308dfdf52c2c0a052bec6fb52a5d133528c5cdc526575bc52626ddc52506be15226d6935214f52b51ea3640
  | 7, 0, 12 => 0x6046708f602b884960246d2f601e3a2c6009b6b36002d9b35fff37cb5ff9e8985fed9d5f5fdd77de5fa184f75f6c173f5f5b33575f33ce345e772fc55e536bca5e46b6065e2165345e0005765dce6a1d5dad411b5da4c1f05d90e8175d4be1eb5d4a14835d481a365d3eb22d5d34488c5d1f3be55d17d8fd5d14d5085d12ce075cd861e65c9a51265c51b4bd5c43718e5c4329675c2099495b6d606d5b55547e5b0f7b205af0a7de5ae24ad15a81fa1b5a6446d65a41a7395a1ade3c5a0dea3c5a005aaf59f2b46459ca8b11599c50055989f9bf59840b37595a8f0059592a72595129d05933582b590a0aed58e154bf58d5ad6d58d1b3c8589606125823f8cb
  | 7, 0, 13 => 0x6607e37966028f3465fb6fbc65e222a165c9f48665bcd2fb65901048658b6cad6552782e6546bb016541a5e9653e05e06531c8d86516237164e1132b64cc77b2648ec3c1648c9e78647a995e6418419263fceb8963bbb2bd63b2af7763a3badb638da0286385fc7a6378f347635eceb86356409163519efa6348cf846336188a6335fe6a6312074d63076e4362f517fd62d0b61c62cbf52a62b01f8f629759f462929e1462893f47627073a8625f19346247b3976240cbab62250a8b620b5c0b61fb1bb261d1c6c361cf7d9a61b95c0961afc4a06157399f61543d9e6110af96610aec2c61080d1f60dde6c760c7db0860a888ba60a137a6609a59bd60480528
  | 7, 0, 14 => 0x6db1a7736dafa7f36d5105186d0f38c46cee87286cc9ecf66cbcbd386ca136c86c9f2d636c224c846c1c94436c033dc06bf50f6e6bf02a286bc9ad1b6badd3526b6144e56b0fc9666ae19d2e6abc488b6aa779d66a9e1bea6a9866b66a78c1b16a5f9e446a4cfcd46a482c536a23f33f6a11d88469ef228269ee273569d6142b69c1547169ab1cff698f8ef06961df276948595b693e6fda691bdb3f68d4269c68abcb9f68a58ae1689c18f7688a0486684bdc96684a5baa682b2f3167fd72af67cc4dea67c7d37867c40bc3679eea8b678f49dc678c83726777af1d67239c6367160b2466fcc9d4668614a16683d716666922236663ef9e663e75166615a314
  | 7, 0, 15 => 0x74cc140a74cbb07774815cb87473fbda747009607460d31c744f2f70742a20e474149a7f73c0dde773b882b473af063273726f35736a22447365b9717355347a73391b267334830e73290475730ce287730af06872f8152f72901258728d3e7e728a34eb726890537214cbea7202ea8271f1e80371a542d471964d6f7192070d717cc4ed716e997f714b8953711970c3711204bf70fd41a670fc53a370e1532a70de390770ba66a3708ebaa1708c63d8708681326ff61c576fddb4576fa993546fa7aaad6fa1f7d76f7b27666f39e1a76f3940146f2a9fc76f0a8caa6edeb4586ec6c98c6ea561246e7c85646e77d66b6e1db4816ddf3ab76ddac0456db87e6c
  | 7, 1, 0 => 0x7b02e70b7ae2129e7adccfcd7ad9b7bd7ad1df4d7aaa70187aa023a97a8dd4717a76d4d47a685fe47a5dda987a5d0c1c7a3757fd7a36d3a57a0aafa379c7315379be408e79b4d911794df861793744fd792983ae7914ad3079105e9278f62cda787c964778653b67786350007863460a7815d74f780bc8f67805b35677e53fb277bdc693779ff703778f771377899cbf7767d58c775392ad76f5ba2876d85f7476d6aa437669ff1476459ea875fdfe5175e6de7375e5643075d6d40b75b870d975b02e45758f5fa37584a59a7569e25475641c4f754c2ce1753448e87531e2e27528ba1e7514584375096426750704c17501c58974f1a12574e6752b74e47166
  | 7, 1, 1 => 0x8289e6848274e041826f9b8f82614b18821de441821be89081fb573f81dad6b581d99ab981ce6e3e81c99ac581485325813ed259810f2d9381034bdb80fb6bc880d6ca6d806c433a8056eaa18047166e8000a0997ff396887fc1b1617faf35d37f9bf5977f59cf707f343a4f7ec6754f7ec2ac277eb7710b7e5cbf637e31e3f17e2b55927e0f5a8b7df00d267defa3347dee6bfc7dd770217d9bbf8c7d99aff67d86e1f57d81367a7d7e08967d68e8707d5c8dc27d4b68477d47b5487d3809da7d2b55c57cf38eb07ce6d6e37ce30f2e7cd7813b7cc052b87c24d5ec7c0af7747be9c0d87bd60b217bd3bdd07ba2da817b9ae1b07b9792677b85e1927b66874b
  | 7, 1, 2 => 0x8a2f019d8a06821b89ebf36c89e12c9389e0cd3289a499b08999d50c896ba8df896902de891cb00588db7cda88d39ce488ccd74e88c8592288b843b9888ef62a887437e588690beb885015c787e0850487c50fea87b3fb67877a78c9876f803d87598a3a8745189e873c904e872027968715de87870bce5087097c0b86e8f91e865a28498639668885e80fda85a2d871857e1b83855aaed08541295f8521287b851351e58511735c84f2c66184d8fda984cf088284c17d8a846889c08464689c844322e084236453841c14d084121b4d83f3954e83c82a5a8365566b835c9aa88358bc12834af6a783324f91832fb02282f9c3b082ea6e0882e12cf482b9ea81
  | 7, 1, 3 => 0x91f2907191d9f9ca91c881cf91c70ff491c61f5d9154b9239134e99e911c7b83910797519107661a90ce1e1490b5581590acf9b7907a592f906eac279029af999026721190012c808ff1da1c8fef348d8fdf91ec8f8f43728f62c14b8f0840ad8f01e3128ed508c08eb2455a8eae1f4d8e7ffa808e6f86db8deb17e08dc6e8348dc52fd98dafd4d48dae411e8d9e33c08d8d65968d6be5b08d6b98918d5eb5be8d31b8a38cfd2e1b8ced27908cebfa108ce6f37b8cc7b8e68cb614e58c7748cc8c64e1ee8c62eb518c5be8ec8bf8ba958bd6d9bb8b5c06d38b438d778b3217fd8a993b7c8a9267628a8968078a81b0a88a66b7088a4d79d98a45d5f28a335bae
  | 7, 1, 4 => 0x97b8dab597b1803697ac0d5c97a325919796ad7697891ec9978297ad976832839761de27973f14ea973aebfb971a52e7970aeaed96fcd41b96f4e0c896d6f6da96d35d1996d1492f96c7df4696c654cb96c41dce96acf156968b472b9674ac22961a6f3395bb394895ae098a959c229b958b46a595842c65957b8792954faf1a9528b0229527428b9516af7595152d0994c2e5889483f77b948273a894815289947f73de946709029466a56f943d24c7941dccaa9415c69993f40d0a93e73daf93b5eba193a6e6809371a0599368ebeb93101ae892f8302c92db658f92d90a4b92d6c71d92c36a6a92a5e56092a1fecc9260fc679241af6c922bf0e392041fe4
  | 7, 1, 5 => 0x9ea5e2099e98ed9d9e8551459e3e66dc9e0f5d589e0b60729db831cb9db23ddd9d9059379d6d5e699d4c3d0d9d3f5bf79d201a1f9cdd6e749cd2fed29cbd32db9c4863a29c44f3639c316cfc9bfc3cba9be7c0979bc0931f9bbfcae49b90cfd89b80928f9b754f269b01f5719ada11de9a9859c99a943f569a8e19009a8799c19a2340e89a11c9cc99f8011499e4c21399d221d299a210969984e8f9998006f39973515999669b959962264b994267be993595cb9931a0a39928e5db98f82d9f98ebf71898e3794f98c478a6989adfa698802a11986e8f2898633758985e97bc9851a7ef98405c4b982476499817f8559800305f97e93a5397e7d73d97db60d9
  | 7, 1, 6 => 0xa5b19f0aa590cdc8a589fe7fa51fc446a5095371a5000233a4e84de5a4cea530a4ae46dda494ba80a48c0cb2a428e9dda420e67da399673fa34bf28ea2f21d43a2e7b907a2e5eb9fa2e3f152a2d973a2a2d4b5e4a2cd4489a2cc83aea2b783b0a29cd03ca288736ea27f1b0ba2652be0a237e894a22d71c3a227fee9a20635c1a1f95779a1cc6112a1a3bca5a1964c37a191278ca177a9eba16cc099a15bc9d1a13d31d6a128e2e3a1093789a0ed1e35a0da99e1a0b0be07a0a105cda03e37faa03ba547a0372ad5a02e2f04a01d46149ff8643a9ff1df999f86ee869f6268639f55e2bc9f4b173e9f31f90c9f17b54f9f03921c9ef6661c9eef4aa39ee60f5a
  | 7, 1, 7 => 0xad55b4eead55363cad48753bad1de092ad18c1c9ad06daa8acfa6444acd55f77acccad9bacb976acaca81907ac69ff69ac61a46fac52d745ac4f0f90ac3fd422ac2817b2ac27da11ac1fae32ac1143a1abf39b78abc66819aba3ba95ab93af8dab92179dab52976aab0edae3ab0262caaae2c829aacae70baac69e07aac3b6a8aaabf859aa7455c7aa45b81faa343074aa16707aa9689b7ca964a127a9592a70a934ca04a9219341a9131075a8a3455fa88d3ca9a862c48ea8500690a81f7c07a7d633f7a7100fb7a6f0d53ea6c461a1a691bcb5a6782e47a671d284a649f73da62afc61a61537b4a60cc165a60182bda5f84e67a5d45b80a5d367e0a5c75f65
  | 7, 1, 8 => 0xb5793bfcb55eb9b6b5562e40b546d898b5456a70b5188b5ab4a663c6b47a4ed1b454fe59b4549ac6b407b969b3e9bd6bb3d44d90b3959077b2ecdc34b2ad7fa9b293dab7b265c412b25e5f62b2500118b23b047fb21d840eb2131f3ab205cbd4b1db9bf1b1bb24ceb1ae1d88b190a4dfb18c0144b1658437b15a583db147c105b1446f9bb0de901eb0b45387b09aef0eb07d744ab07b2df5b02af465b017a4f0afbc46a2afaf7e14af89fe51af87c055af7bf3c0af6ca0fbaf091573aee02b81aecad907ae94ecadae9376f9ae9131a2ae7a963cae7a0db7ae792b02ae661bd6ae45b6fdae3275b1ae1985b0adf3fcf7ade9ebafadd14485ad8da066ad703ecc
  | 7, 1, 9 => 0xbc37165bbc0fd8a9bbef2a91bbc8136fbbc06128bbbb9ca0bb9731b2bb2bc4d0bb2baadebb245f63bb20d37bbaf71f82baf502e1badbd6c1bad0a275baaf8dd9ba9bc06dba67eb26ba678793b9ffbf23b9ebdc06b9cd0f77b9bf5ab4b9a4cadcb96838e0b964f444b963bc1eb9501ba2b949b22fb9363165b8f5ff44b8b26dfdb8a6c784b89f9e4cb87ec56ab8706511b86e02edb84c4a65b84be1b4b7f9c4a4b7d50c4db7d1a67bb7c38bceb7af4ab4b7ace222b7991462b7842f4bb7599b1db74c752eb7470254b7356839b728e152b72413c1b6af7cedb6a12c76b67eb1e8b67cebd0b647e64eb62a91bdb6283af4b608e4fcb608648ab5a76137b580bd16
  | 7, 1, 10 => 0xc2bb39e0c28d123bc26778a6c237c534c228d3afc1db834fc1bf2bdbc1a81019c16ea0a3c15e9b0ec1528514c13eb19dc1327779c1129ee3c10eafeac08f689ec0876bacc07b1aa1c07a4c42c05601dbc0364c96c023ea7fc02352c4c01c245bc012abf0bfe9d026bfe050b1bf935932bf7a226cbf67ddaabf605e05bf4349e2bf382022bf301bf1bf17d198bf150c9abed404b1beca58e7bec55acabeb088aebea0f363be9f069bbe86e2f4be816572be753832be716ffcbe4e7a3cbe33444bbe011283bdf77620bde6c271bd9fb0fdbd865601bd60fedfbd3e5fdfbd3dffacbd20eee5bcffced9bcee49d7bcb41943bca1d41bbc62ecabbc506207bc40c5be
  | 7, 1, 11 => 0xc922bf5bc8e952b9c8d70231c8ae6820c87b7b57c87781b2c8472f0ec83c6390c82f7310c820d0acc7fdb986c7f52eb4c7eefad9c7cde774c7c1673ac7972e5bc77571d5c76c30c1c76571e1c76117a8c6ef51ddc6e38824c6dede38c6cc5394c6ab04afc6a97e1dc644665fc637ec94c6378e2dc62f1128c60d8b1dc5f2c1bdc5ddaf2fc5c990d2c5a0224fc59c77b5c5866f95c56cddc4c56c8578c56292dcc54b0cefc526badec51c3592c4f74707c4d95c87c4c90a9dc4c895a0c4c34daac4bd66f7c4ba5df5c4a2ed94c49c3c34c49af72bc4608a74c44cb52ec4325c78c40edbd4c40919c9c3be9199c3b222f2c327768ac2e9f47ac2d3e0f6c2c4f678
  | 7, 1, 12 => 0xd0cdef19d0c01760d05e404ad03c767dd01622edcff8574dcfecc3c7cfdf8375cfa2ac6bcf5a9d44cf4c853ecf1d6b2fcef134e5ced7684cce96563ece8acd61ce65deddce520fbcce442b27ce2b6ec8ce1af5a2ce1502afce04edffcd8bb8bdcd8606d2cd4a8fdacd3c884dcce28f39ccbaa2f2ccb8d58accac7c24cca61987cc7d8ee0cc6fddcacc546ba4cc526cfccc4676f8cbfd2d53cbd53da4cbd26a4bcbc30625cbb741e5cb8e1c8ecb615d11cb60b80bcb4861a8cacc77c6cac9ac2acac9a72ecabb024ccab5490aca9fc081ca8a3c6fca81b63eca7dbd21ca65dc03ca5b44d8ca21c8a1ca003fb8c98f6c6ac97dca2ec976bd77c9421defc92fc7a9
  | 7, 1, 13 => 0xd823c9f5d808f7e5d7f89236d7d8795ad7d0fd1bd788012fd78613e0d747d71ad71780fcd7120918d6f11cd2d6ab48ecd6aae2e7d69534b5d68095bfd6791ee0d616304bd5f9171fd5f313c6d5e44300d5b5f79fd5442397d542562fd5405be2d52c8a38d4b8d850d49dba2ed493e748d4002735d3fcf8aed3aa4b56d397741cd38ce6dfd3855a4ed37cf759d36b5df6d366268dd365a219d32a59add323a151d31b58b1d307bcccd2fd705dd2c8e568d2b8551dd2b7b812d285b4ced26aec66d25fb16cd24c54b9d238faf7d22635e6d214fac3d1fcebc3d1c3e57cd1b4db32d19491b1d1723623d15f29f3d15619c6d152d0acd1024c99d0e6ecb9d0e09013
  | 7, 1, 14 => 0xe0531625e000e70ae00052f3dfc72249dfb2e678df98cd72df82a98edf814082df3de7b2df15e160deda8ae6ded4018ddeabcba6de7c18c2de36b6c2de2b8ab6de002525ddf87e56ddc23632ddb68b26dd8508a1dd47e478dd24f5e5dd0b2ddedd04099fdcdb82a4dcc1369edc72db0adc48c872dbede8d5dbeb56ffdbd5ffcbdbbd0a3fdb852709db62ed1adb571064db569198db2d04aedaad8f87da89d89bda5b7502da390d57da00fb54d9f4bb38d9f4b273d9cfdc70d9b24658d99bfd39d98fe426d96c7a47d93b31f4d92afae5d91252f6d90efb48d90d7775d8feb116d8d1265dd8cce369d896e72fd8729e39d8671faed85ded4dd84b58cbd8465bc2
  | 7, 1, 15 => 0xe8495d18e838a758e8327cb3e8244a8ae8144a65e8091deae7ebaedde7dc4b53e7cd86a1e7bba539e7a4b839e789efd1e75f1e46e7361b74e7338c83e702ce56e6fdb53ee6f02fade6a6f2e6e67eee19e64260c6e60f910de5943b56e591f1ade54946c4e54148c9e535c32be5298114e514fc23e4ffa8dee4e6ee5ae4e0203ae4c22ea2e4c1afd6e4976f0fe4552f85e4443063e411f253e3e86bd4e3e0e689e3a9d0cce35d12d2e32e3e5ce2d9dedae290a862e26c052ae25929fde225ba8be2115dbde1eb50d1e1e668e1e1b33bc2e19813d6e191b813e18278c8e1687241e136fcb9e12ca6f4e119f6ece1112642e0e0ce7ae0c8d7d6e0c6589fe0903d64
  | 7, 2, 0 => 0xee016744edc98305edbc78bfeda7a798ed95711eed79ae14ed720b13ed49643ded08a60eecf4239fecec19c2ecde9f3decd51b8aecd123afecc3f223eca6cae1ec8f44b8ec4042f6ec2f2d4fec0da9a0ebfe6a55ebc6d37debab792feb955e7ceb689266eb4f5268eb3d6051eb2d760deafcd651eafc90c9eafae91fea9bd94fea8db5d8ea827697ea681c52ea53d15aea503e02ea34e2a8ea053820ea02da06e9fd320fe9ed1452e9d98517e9bcbd99e9b2d274e9a00863e9713d6be95aa6fbe92b5b16e91bfc19e9145362e90a466be8e13307e8dd12e7e8bc6b04e8ab9dbae8a905f0e8a21811e89bfac4e88df45fe886fc4de884a584e8685acae84fc37c
  | 7, 2, 1 => 0xf7a7777ff78e05a8f782e5baf759030cf7325e1bf6e672acf6b19c3af690cfa1f674c83ff6170511f5bd1192f58211a2f578c7def56a5c67f55a7045f5304b86f51b09d5f5087817f4b5f832f4474a6ff422fc21f41d1798f415e4d3f415021ef40cf774f3b56d3ff39b1c2df33fa6a2f2f18c0af2b64da9f2868994f2554dc8f2049c15f1f6e0d6f1bf72fff1bf6a05f19fb472f197e0bbf15017aff146d173f1440f1df121c55af120ad05f10d2b1bf0cd59eaf0b79c77f0aab1fff0a20346f091c2daf07e9f45f066be27efa6a8dfef98f3b9ef7a786def5f3232ef1083d3eedbd48beedb9e17eeda0839eeaee791ee866c17ee5a378cee1d6168ee0a4d88
  | 7, 2, 2 => 0xfe7ad6aafe4d5cfcfe3c8b0ffe1ff7d9fe161085fe143688fe09da09fdf4be5efdaccb97fd80606ffd6bdaa3fd48b93efd284922fcfb68defcfb4ebefcf95f79fcf7b91ffcd295f4fcaa2fa8fca323ccfc7e3331fc46322dfbebd6fafbd94c56fbcc093cfbc06c06fbb41fd5fb954f1dfb585651fb4486effb433853fb2a913dfb0db467fafde212fa87c339fa5ceb48fa5aa583fa48847ffa24aabcfa15d03dfa0bc0e3f9d4e1f1f9d4cf87f95347a7f94f8c9cf9316793f930dd7ff91fc747f91176c9f9076f3ff90411f7f8eca66df8bf1bb4f88b7bb8f8863f15f872a538f84f2c4df81e1b74f81a05cff813c029f811fd64f7f8e245f7ca913af7c555ca
  | 7, 2, 3 => 0xffecfe06ffd6a4ecffb44ec2ffafc6adff1c357afeff933afe9eedaefe9aefc8fe8c579bfe7b0bf7
  | 8, 0, 0 => 0x2ed972652da043882d2eb55a2bf289122b6360842a7bac4d28c6746028736fa12764e2a72716306b259c2a0f24eb385a24368a0d241ae38823071c8f226abd701d21eafc1be736751be5022a1b3d035d1a740b5a1a394cee19bc3e6419ad68c2192abff41928bdfb18ddfae018491349178270b1174358ea16d503ed161b979114ccf9dc14823c4513cffff713734caf131f4f8c1315d12e12de71c31210c29210e87ecc10c72c17108ae1ac1076a8040ffbb91e0f611f320ce278c60c22e64f0b69e2050b00d3fd0a8e8a9e0985b8e7097ffda4088d6a6006ffe09b06647db7058e5e4e0522378c04ff35c004ae569104244b480334fbc402e5179c00486864
  | 8, 0, 1 => 0x62f517fd627b77fa6240cbab623a66ef60c73bd46098819e609018d86077da606000993c5f6d245d5e9f6fd55da661335b9e0b385b55547e5a65cb0959cdc471590a0aed57f8949f57b0e66f56c9d87e52f9b849528f7aa3522a70035212b21b4ebb441c4da0f7e84c8de4c04c7da6ae4c0054d34b85288b4ade3d7049c35e8349be71ec485033684774b70f4639537545ed680645af2d6b451032fa44ea24a94422b1fc42d860c942a4748a414287dc40982e5a3fcf5cc13e52d0123d4b05d83b34c7713afd60273a8033753a13af9c39f81e62390d085a3909cf60384665c2374ca99035bb4c4c33ef9a3f335b92863098ad6d309620c52fe9e3ab2fe7ff5f
  | 8, 0, 2 => 0x8895799e887437e5886480a08806511087ced706873fae788680c80c85d14f2185723b1284db1443848218fa84158e5683c82a5a82a2633b828f70e182614b1881ce6e3e81a2729c818d0e418187f7eb7f60ad2e7e9816487e5cbf637e08edba7d8cc9437d1d106e7c8106d078ba657e78a4ffe5771951517445e99a7431b33873c08ca272be881d71feda0a71f7e5857166433c708ebaa1704a027c6fa993546ef68aeb6ed1d2506d835fd06d6960e56cc9ecf66c5dc6bd6a89ba876a69a7bb69c0e3786916efa46910ef7f69089f4e68c124c768666c2467e7cb0c67d7439667ce92b267a3c48966dd21f166d93e1265bcd2fb64eeec54647a995e63076e43
  | 8, 0, 3 => 0xa8cea874a8c70d27a8a3455fa84a25ffa7dca2c7a57c8260a3631f52a333da41a328ba33a2697368a1e30abda1c9b5faa18e9a8ba091bf2da03e7b57a03ce6b29ea5e2099cebbd729c6d2ebf9b171ca19acd454799ca9344992ef9489811ee4a980df69f97ed931a976cf00a967a67ff964f52ea961cc5fc95c3f31a95714dc79562c5379541f7f995379eaf94b5662094a8762193ef9a1c937f44349371a0599328f78492d6c71d9257f85191c8cfc391526b2b91316dea9057a0088e441be78dffff528d8d65968d431c738cb614e58c8cd4378c7d04a98c64e1ee8c348f798bc6319f8b969fb78b4119808af983f68a75e2768a08a4b989797c2b89528f76
  | 8, 0, 4 => 0xc9bceffdc9640176c8d07d32c8ae6820c71ebaf5c6f26785c6e49a15c6dd499fc5ab8fdac5491818c4e4ed42c4e320d5c2c829e6c28a9299c2453233c2037a77c1027068c03247cfc0290ea1bfe76089bf23bad5be8df607bdd11acebd1acaecbcf7064dbcc84171bc542854bba622bdbaf71f82bad0a275bac5f4bdb9e89288b8ffabb4b8f51c8fb8d5ac04b8708326b864d278b819de68b77a592cb73b2416b63b7ad9b605ed0ab5f44193b5456a70b517843bb4b05633b408f741b31d6796b265c412b2442040b1b4f7b2b07b2df5afab3129af7f1e6faf6ca0fbaf327da3ae3afb86ad4d904ead2c6e8cac52d745ac5109ddab0edae3aa16707aa95635b5
  | 8, 0, 5 => 0xef1664beee3c737bed864953ed84fd02ec36be60eafcd651ea97c532ea7c4480e8bca3e2e8ab2ddae8656c85e7a1d500e6c9718ee66c4bf1e55636cfe4c22ea2e49ca939e3ee27b1e3e76ac8e34400b9e2df9ab7e2743fade1efa266e1ad9d15e16359cee054ccd4e00052f3de81d49fdddb8703ddc02084dc72db0adc6a17cedc226a26daffafefda390d57da0093e9d90d7775d8f206efd876dc57d8293d25d698dcd4d6880befd6093950d57a10c2d4faac56d49440d7d46b83c8d38ce6dfd3444ba7d2fa8aa8d251ec01d24db4ebd14cb470d1024c99d09ce63ed01622edd00dbdb0cf5ddffbcf0795f3ce38b857ccc58d3ccc3eff34cbb1e63dcaa9cfdb
  | 8, 0, 6 => 0xfe897d15fd2fbf52fd124cd3fbc06c06fb5773bffab3f02bfa44fde0f91af23af88bc9acf81a05cff67433def6170511f5087817f327dbd7f0aab1fff07e9f45efb76ccdef992c97
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x3010c206000c0430818000000a1090010c300818c80510930030455300c24003010c2060000030042000000c810a0000032042800000c010832084048c00003010c20600000430414003010c206000c043081800430c02060010140082400000c810b32016210c0000430c02060010c300818000010c10532084008c0084058c830030455300c2400430c0206000c8210800003010c206
  | 6, 0, 0 => 0x28418000000610600000028424004250820e00006048800000181220e00002018838000000a1090000000841800000c810a000d4204800000181220e0000004840000058842000000a04883800154c020900000028438000180a20e00002028800000000a10e0000001842400000c81000010140082400000061060009530082400000c1109000c8200800000000e10600006048838000080a20e0010d430824000000610e
  | 6, 0, 1 => 0xa038800000010c105000000284180000806200000c820080000254c020e0000043041400000121000000000840000000c810a0000001840400000c010600002048824000080a2090010140082400000c81000000002841800415042000011420482400000061060000000841800018122000000a04883800000c810b0000202883800000c01080000e04882400000c0106000000084180000806209000003044380025101200
  | 6, 0, 2 => 0x841800450812000000002840400018122090000a04883800000c810a0000002841800154c02090010140080000304c0209000c821080000000c810a000003204280000002109000c8008800000280e2000000040042400058c8200000c8018800002048020900094104800000181220e00000018418000000a10000000320400000000e106000003004180032080200001153008240035500209000c9320824000180a209
  | 6, 0, 3 => 0x6048800000080e20e0000002841800000c810a0000602882400000c81010000043041800000021010010c300818000000610600000430414000010c1060010140082400430c02060010502882400000c810b0000002842400000021060000032042800405002090000a04882400000061060000040040400008122090008120082400320842000000000840400320022000010c30081800354802090000032040000000c810a
  | 6, 0, 4 => 0x1841800254c020900006038838000000e10100000028400000000a10900000430414002048020900006028800000001210100055400800003010c206000c800880000000c810100109320800004350c2090008404880000000061090000043041800320802000000003841800000c810100000048404000010c106000c8210800000080e20000101400824000080a20900000048424000000e100001094208240003812209
  | 6, 0, 5 => 0x6048838004508120e00105038824000000e106000c1300838000080a2090000203883800058c820000055400800000181220900000008418000280e20e0005540083800000121060000004840400424c82000008400880000154c02090000a038800000000a1060000602880000000c810000095400838000001210600000038418000180e20e0011410480000000c810b0000032443800028122000000204882400000c810b
  | 6, 0, 6 => 0x43041800000c81000000032040400000121090000000841800000c01060011530082400000c810100000048424000010c1050000001840000324c82090000002842400001011090000004841800000c810b0000040040000320022000001632080000450412000000032040400450c1209000c820080000001001000000a04882400304c020900006048824003510920000000008418000180a209000000384040032084200
  | 6, 0, 7 => 0x32042800000021010008403880000154c020900000008418000080a20900006038824000180e20e0010140082400000061060000202882400254c0209000c821080000355002090000604882400000021060000032042800154c020900000038404000080a20e0000202880000210022000000000840400000c0106000d421480000000c010e00115300824000080620900094104800000080620900101400824000000a10e
  | 6, 0, 8 => 0x105038824004508120900101400800000000210e00000320400000281220e00000038418000001210600055400824000000a10e0000043041800254c020900000028418000180e20e0000203882400000061010000a048824000010c10500094104800003200620000006028800000000a10100095400824000000e106001094208240035500209000c800880000430c020600002038824000280e20900002038800000080e20e
  | 6, 0, 9 => 0x300420000000210100002018800000281220900002028824000000a1010000004841800430c02060000a038824000080620e00114304824000000e106000004304180035480209000c8210800000181220900002018824000080620000084038800003200620000006038824000000e1060000204882400304c02090000203883800450c12090000002840400000c81010000003841800028122000000040040400000c810b
  | 6, 0, 10 => 0x38418004350c20900000028424004140a20900002038824000081220e00000018418003200620000002018838000000a1090000201880000155002000000030442400304c02090010942082400000061090000204880000454c020e00000018424000001210900006048800000010010100114204824000180e20e00006028824000510920000000320428000080620e00000008418000000210000002028838000000e106
  | 6, 0, 11 => 0x404424000010d10e000d5400824004050020e000c1300838000010c10600095300824000180e20900000028418003504120000101400824000000a109000c8048800000281220000000430418004350c20900000300418000001210e0010502882400058c8200000c8018800004050020900000008400000000a1060000004842400320122000000202883800000c01060000030041800154c020e0005520082400000c8100
  | 6, 0, 12 => 0x32042c000280e20900055400824000280e20e00006038800000280e20e000002104000000806209000c043081800008062000000201883800000c81000000001840400038122000000201882400000c810100095400824000180e2090010140080000000c810a00000038400000180e20e0000203882400254c020900006038800000280e2090000000840400000c01060000001843800000c810100000018418000180a209
  | 6, 0, 13 => 0x10c300818001044020000000038400000181220900055300824000081220e00000028418002108020000101400824000080620e00000028438004508120900000314438000181220e00000320428000080e20900000028418002048020e000d5200824000080a2090000202883800454c02090000001843800000c810a000552008240000812200000d440480000324c8209000020288240032012200000004304180032006200
  | 6, 0, 14 => 0x202880000454c020e00006028838000000210600006028800000010c10500000430418000000e10e00000028418000180a20900000038404000000a1000000002841800000021010010c30081800000061090010c30081800028122090000a04882400304c020e000c8018800000081220000000430418000000610600000028400000080a20e000000184180021012200000003204040000002109000000184240021002200
  | 6, 0, 15 => 0x202882400008062090000603880000000021090000a03882400000061060000201883800254c020e00000430414000180a20e00055400800000010c10600114204824002500e2000000201882400154c020e0000603882400304c020e0005540082400000061000010c30081800355002090000032040400000c010600000430418000010c105000000284240032012200000163208000040500209000000084240025500209
  | 6, 1, 0 => 0xc8048800000381220900000048418000000a10e0000e048800000381220e00002028824000000610e0000043041400405002090000003841800000021060000043041800000c010600081200824000000610000055400824002100e20040094404c0000000121060000002841800000c8101001143048000000806209000d5400824000000e10600000048404000280e2090000a04883800000c810a00084048800000010c106
  | 6, 1, 1 => 0x2018800000080a2090010140082400000c81010000a03882400000121060000032042c00000121060000032042800430c020600000048438000000a10600000018424000000610600002018824000280e200000d5200824003544020000000048418000180e20900002048824000000a10e000000484040000006101000c93208240005884200000943148000000812209000000284040000006100000c130082400000c810b
  | 6, 1, 2 => 0x181220900000430414000181220000094304800000180e20900055400824000000610600002028824000180a20e0005540082400450c120900000038404000180a209
  | 7, 0, 0 => 0x28424000000e10900041100800000000a10100000404438000010c10600000320404000000a10000000008418000001210e00000008438000000e10900000200400000001210000000008424000000e10e0000a048824000000a1060000002840000000c410000000018438000000e1010000000840400000c8100000000184240000006109000001044240000002101000000084000000002106000000284240000002109
  | 7, 0, 1 => 0x320400000181220e00000038424000000e10000000320400000000610600000028438000010410000000404424004250820e00000028424000000a1090000042042400000c01000000004842400000c510e00000008438000000a1090000000843800000c810a00000008424000000a10e00000008438000001210e00000310400000001210900000400424000008510e00000300424000000610100000048424000000610e
  | 7, 0, 2 => 0x32040000001081000000004840000000c010e00000028424000001210e00000028438000000210e00006038800002550020900000038438000010510900000414400000000610e0000000840000000c410000006028824000000e1060000a038800000000210600000038400000001210900000430418000000a10000000028400000081220000000008438004250820900000400404000001210000000038424000180e20e
  | 7, 0, 3 => 0x100400000000210e00006028800004050020900000008438000001210000000038438000000610000000204438000280e20e0000a048838000001210e00000430418000000e10900000018400000180a20e00000204438000000a10600000304424000010910900000028400000000e10000000420424000001210900000434424000000a101000020488240000012109000000284000000012109000000384240000100109
  | 7, 0, 4 => 0x434424000000e10600000430424000010510900000204438000000610900000048438000010110900000018400000000210e0000602880000000401000000003840400155002090000002843800000c910900000048404000000610e00000048400000010810900000404438000000210600000104424000008010000000018404000000210100000400404000008410000000434438002048020e000004044000000012109
  | 7, 0, 5 => 0x18438000010510900000048424000080a20000000048404000010810000000028418000000a10e00000430418001550020000000008438000180e20e0000031040000000851090000000842400000c810000055400800000008410000000430418000081220e00000048418000000210900006048824000008010e00095400838003201220000000430418000000e109000000084240045081209000004044240000006109
  | 7, 0, 6 => 0x4840000320802000000040040400000021060000043041800001001000000032040400000021090000030043800001051000000a048824000000a10e00006048800000000210900055400838000000a10900000008404000010010e00000028424000001210600000028424000000e10100000414424000001210e00000008400000001210000000028424000004110900000018400000001210e00000038424004050020e
  | 7, 0, 7 => 0x843800000c810000000038424000000210e0000043041800000021010010942082400000c01090000020042400058c820000000320404000000a10e00000048400000000e10000000048400000000a10e00000320400000001210e0000020442400000c0106000000384380003812209001142048380000012100000c820080000000c810900000204424000280e20e000000084380000100100000000184240000012109
  | 7, 0, 8 => 0x18404000381220e00000028424001550020e00095400838000000210000000008438000000210100115200824000001210600000018400003200220000000028400000001210e0000000842400001001000000003840400001001010010503882400000061060000604880000001051090000032040000058c8200000c80088000000085109000000484380000081109001141048000025500209000003244240001812200
  | 7, 0, 9 => 0x48424000010910900000400424000010910900105410800000000a1090000040040400155002090000004840400000c810100000008400000000610000000424438000004110900000008438000010110900000028438000000610900000048400000000a10e00000304438000001210e0000020440000000021010000032040000000c010e00000404400000000610900000018418000000a106000000084180000006101
  | 7, 0, 10 => 0x38400000001210100000048418000000a10900000048400000000e10600000008438000000210900000018424000000610000000028424000010110e00000028418000000610900000008400000000e10e00000018424000001210000000300438000000210900000038424001550020e00114204824000001210000000048400000000210000000008424000000e109001054108000000006100000000084240000101109
  | 7, 0, 11 => 0x42442400000c810e00000320404000000a10600000038418000000610100000038438000000a10e0000000842400255002090000e04882400000021090000004842400000c810900094018800000000610e00000424424000000210e00000018424000008010900000008404000008010000081200838000000a10900000008400000010910e00000038438000001210100000038438000080e209000000084000000012109
  | 7, 0, 12 => 0x32042c000000610900000204438000000a10900000048404000000610000000304424000001210900000008438000180a20000000018400000010810900002048838000001210e00000018438000001210100000028404000000e1010000202880000000c810000000320400000000a10900000320428000000a10900000008424000000a1090000003841800000061000000001842400000061010000032042c0000100100
  | 7, 0, 13 => 0x1841800000c410000055400800000000a10e0000032040000000851090000032042800000c010e00000210400000000a1090000000843800000c81000000004840400000061060000203880000000c810000000430424000080620e00000048438000000610000000008400000001210600002048800000000a10e0000004843800000c010600000048424000000210600000008418000000210e00000008424000010c106
  | 7, 0, 14 => 0x48438000001210900000008400000001210900002028838000000e10900000018438000000610600000038404000000610100000028404000000e1090000000841800000c81010000002842400000021000000041040000000061090000003843800000061000000603882400000c01060000a038800000000210900115300824000000210e00000008438000001210e00000048400000000a10e00000320404000080e200
  | 7, 0, 15 => 0x20388240000002109000c8048800000000e10100000048404000000a10900000048400000010c10600000028438000010c1060000043040000001001000000a03882400450812090000e048800000180a20e00000008438000010d10900006048824000000e10900000038418003208020000000414424000000a1060000000841800001001000000032040000000021000000002840400000c0109000003004240000012106
  | 7, 1, 0 => 0x38438000381220e00000300418000000610600000304424000000e10100000048400000010110900000028400000010410000000018424000000610900000200400003200220000000028438000000a1060000003841800000c810100002028824000001210100000028438000000a1090000004840400058c820000095400824000000610e000004004240000006109000004144240045041200000004144240000012109
  | 7, 1, 1 => 0x28424001550020900000314438000010510900000204424000000210600000214424000000610000000008438000010c1060000000841800000061060000a048800000004110e00000434424000000610e00000048438000008110e0000003840400028122090000030443800000c810000000008400000008110e0000a04880000000c810000002038824002504120000000400424000000a10e000004144380000012100
  | 7, 1, 2 => 0x8120083800000c410000000038424000008510e00000300400004508120900000018438000000a10600002028800000281220e00000204438000000e10900000028424000000a10900000400424000000a1090010502882400000021010000000842400000c01000000004840000000c810b0000032040000000c81010000042442400255002090000032442400000021060000043041800000c810000000048400000000a10e
  | 7, 1, 3 => 0x48424000010c10900055400824000000a10e00000414424000000210e00000048424000000e10000000008424003510120000000410400000000210000000320404000000e10000000048424000000210000000008418000000610600000028424000000a10600109420824000000a10e0000000843800000021090000003843800000021090000040440000000121010000040040400001011090000003843800000c8100
  | 7, 1, 4 => 0x8400000000e10900000008438000381220e00000028438000004110e00000430418000000e10900000008424000000a10900114204824000000e10e00000028404000000a10000000028400000000210e00000038438000000a10000000430418000000a10e00000008400000000610000000028438000001210e0000002840000000c810000006048824000000a109000840088000000012109000000284380000006100
  | 7, 1, 5 => 0x48404000000a10900000008424000000210900000038418000080e20e00000404438000000e1000000002843800000c01000000032040400000c810000002028824000001210e00000304438000000a10900000018400000000a10600000018418000010c10600000008404000000610100000008424000000210100000048404000008410000006048800000000610e0000032040000000c010e000000084380000105100
  | 7, 1, 6 => 0x8438000000610000000008424000000e10e0000002843800000121000000203880000000801090000000840000000021000000003840400000851090000020442400000c810000101400838000004010000000434424000000210e00000104424000010c10900000430424000010910e000020188380000006106000000484000000085109000000084040003812200000940188000000012106000000484180002812209
  | 7, 1, 7 => 0x324438000001210000000008400000001210600000038418000000210900000038438000000a10900000320404000010110000000008404000000e10000000434424000010510000000320400000180a2000000000840000000411090000000840000001011000000040442400001081000000032040000000411090000004840000000021010000003843800000c110000000028400000000a106000004144240041504200
  | 7, 1, 8 => 0x48424000000210900006028800002550020900000324424000008410000000008424000001210900002018800000010910900000018400000010910900000048424000000a10000000028424000000e10e00000204424000000e1000000001841800008062000000a048838000010910e00000008438000000610900000104424000000e10000000008400000000a10900002028838000000a10600000320400000001210e
  | 7, 1, 9 => 0x204424000080620e00000028400004250820e00000028424000001210000000018404001550020000000038438000000a10600000028424000000a1090000021040000000061090000004843800000c810000000320400000280e2090000032042400000021090000032042c000000610000016320800000080620900002038824000000210600000018438000000210900000414424000000e10e00000018404000000a100
  | 7, 1, 10 => 0x38424000010510000000008400000001210000000314438000001210600000028418000000e1060000001843800000c91090000032040000000c810000000320400000000210e0000010443800155002090000a04880000000121000000021040000000c810100055400800000000210e00000320400000080620900000038400000000a1090000030041800000c8100000000084040015500200000000484240000012109
  | 7, 1, 11 => 0x84240000012101000c8200800000000610900000008400000000a10000000048400003200620000000008404000000a10900000048404000008110900000038424000001210100000038404000008110900101400800000010010000000008400003200620000000404438000000a10000000008424000001210e0000004842400000c810000000048418000080a20900000320400000000a10e00000008400000000a109
  | 7, 1, 12 => 0x10140082400000c810900016320800000000e10900000048400004504120000000018400000000e10000101400800000000a10e00016320800000001210100114104800000000210900000018400003208020000000018438000000610900000430418000001210e00000404424000000e10900000400400000080a20900081200838000000a101000000284040000002109000004004000000002109000020288380000012109
  | 7, 1, 13 => 0x210400000000e10600000008424000000e10900000028400000000210900000324424000000a10900002038838000000210600000104400000000e10000000028424003200220000002048838000010c106000840388000000041100000c800880000001081090000001843800058c820000000008400000010510e000002044240045041200000000184040000104100001014008380000012109000c8008800000004110e
  | 7, 1, 14 => 0x304438000000a10e00000048438000000e10900000008424000000a10100000048404000010110e00000008400000000a10e00000008424000000210e00000434438000010110e00000214424000000210e0000003842400000c010600000048424000280e20900000018438000381220900000008424000181220e00055300824000001210900000414438000000a10100000104400000000a10e00000028424000000e109
  | 7, 1, 15 => 0x842400000021090000040040400000c810000000414424000000210e0000003842400454c020e0000041442400000c110900000018404000010010900000038400000000210900000038400000000a10900000038438000001210000000008418000001210900000008418004050020e00000414400004150420000000008438000000210000000018418000000610600000204424000001210000000018400000000e106
  | 7, 2, 0 => 0x842400000021060000003840000000021090000004842400000c810100000400400000000e10100000008418000000e1090000004843800000841000000003840000001051090000001842400000121090000043040000000851090000001843800000c010600000048400000000a10e0000032040400405002000000002843800000c81000000021040000000c910e00000304424000281220e000000484380000105109
  | 7, 2, 1 => 0x48438000000210000000424424000000a10e00000320438000180e20000000038424000004110000000008418000000a10100000038438000080620000000300400000010810e0000a038800000000210100000204424000000a10e00000008400000180e20000000008424000010110900000008438000180a20e00000300424000000210600006048800000004110900000028418000000a106000000484240000012109
  | 7, 2, 2 => 0x48424000180a20900000028400000000a10600000048404000001210e00000104400000000a1060000043041800405002090000e048838000000210000000320400000000a1000008120082400008062090000001840000000021090000603882400000121060000001842400000c810000000008400000000610e00000028424000000a10e000d4104800000080e20900000304424000000a10e0010942083800000c8101
  | 7, 2, 3 => 0x324424000010910e00000204438000000e10000000028438000010c10600002048824000000210100000008424000001210000000008438000010910e00000028400000080e2000000032042800000021090000040040000001091090000202880000000c010600002038800000000610000000324424000000210900000038438000010010900000018400000001210e000003004240000002100000000484380000101109
  | 7, 2, 4 => 0x404424000000210600000404424000000e10900000038438000000210900000300400000000a10100000008404000590520900000048424003200620000000018404002550020900000430418000000210e00000320404003200220000000018418004250820e00002018824000000210000000404438000280e20e00002018838000080a2090000000840400000021090000a038824000000a109000004304180000006106
  | 7, 2, 5 => 0x28418000080a20900000104424000010510e00101400824000008510900000008418000080a20e00000320424000000610000000008424000008410000000028418000000a10900041100800000001210000000028438000001210e0000010440000000c810a00000210400000000610900000018424000000210900000048404001044020000000210400000010810000000400404000000610000000414424000001210e
  | 7, 2, 6 => 0x104400000000e10900000320404000000610e00000028424000081220000000404424004508120900000008424000000610900114204824000000e10900000008400000000e10e00000008424000001210900000038424000010910e00000038424000081220000006028800000008010000000008438000081220e0000000840000000c910900055400824000000210100000430400000008010000094404800000000e100
  | 7, 2, 7 => 0x18400000000210e00000048424000004110e00000038438000010c10900055400800000001210100081200824000000610900000404438000010c10600000038424000000210000000324438000000e10900000008400000001210000000320424000000a1000000001840000000c81010000002842400000c810000000008424000000610000000018400000281220000000018404000000610900114204838000000a109
  | 7, 2, 8 => 0x840400001011090000001840000000c81000000003841800000c510900000028424000000610e00101400800000000e10900000038424000000610900000048400000010c10600000008424002048020e00000018400000010910900000008424000010110e00000028424000000a10000000320400000000610e00000008438000000210100000048418000000e109000000284380015480209000000084380000006100
  | 7, 2, 9 => 0x84240000002100000000084000000012109000000484240000002109000c8200800000000210e00000200438000010010000000048418000000a1090000004843800001001000000002840400001041000000a0388380000012109000812008380000006101000000284040000002100000004044380032012200000000084380000812209000000484380000002100000004244380000012101000002144240020480209
  | 7, 2, 10 => 0x16320800000001210e00006038800000010c10000114104800000000210e00000300400000081220900000018400000000610000000038404000080e20000000424424000000210e00000424424000000210900000028438000000610e00000038424000081220e00000204424000001210100000104438000180a20e000002104000000081109000003204040000081109000000484180000002101000c8048800000010d109
  | 7, 2, 11 => 0x18400000004110e00000008438000000a10e00000210400000010c1000000010040000000401000000001840000405002090000002840000001081090000021040000001011090000603882400000061090000001840000000c810900095400838000000210600000018400000000e10e00000038400000080620900000420400003200220000000048438000008010000000100400000000a10e000000184240000012101
  | 7, 2, 12 => 0x5540083800001051090000202882400038122090000004840000008062000000032040400320802000000004843800000c810000000028424000000e10e00000028438000010910e00000028424000000210e00000048438000001210900000038424000000210600000008400000280e20000000414424004150420000000048424000000210e00000008418000010010900000008400000000a10e00000048424000008510e
  | 7, 2, 13 => 0x48424000000610900000404424000000e10e00000204424000000210000000038438004508120e00000038404000000610000000204424004050020900002038824000010510900000028404000000210900006028824000280e20900000028418000000a10000000320404000000e10100000008400000001210100000008418000000210e0000030043800000c81010000020443800000c810000000320400000000210e
  | 7, 2, 14 => 0x843800000c810000000028438000000e10000000018400000000a10e00000038418000010810e00000048418000010810000002038838000000610000000400400000000210900000008404004050020e00000008438000080620000000300424000000210e00000028400000010c10600000008438000004110e00000008400000010010900000018424000080620000000430418000001210600000028404000180a20e
  | 7, 2, 15 => 0x8418000010110e00000320400000000210900000430418000381220000000434438000000210900000038424000081220000000300438000010110e00000214424000000a1000000004840000000c810100006038838000001210100000028424000001210e000c8018800000000210100000028424000381220000000414424000181220e00000008424000001210e00000008400000000210600000430418000000e106
  | 7, 3, 0 => 0x84040000012109000004244380000006109000c80188000000002100000004244240000006109000004244240000104100000c8018800000001210000000320400000000210000000320400000000210000000300424000000e10e00000018424000000e10600000214438000000210000000008400000010110900000028404000001210e00000424438000001210e00000320400000000210e000000284380000080100
  | 7, 3, 1 => 0x41440000000c81000000e048824000001210900000028438000008110900000028424000001210e00000018424000000610900000214438000000610e00000214424000000210900000028424000000a10000000018418000000a1090000003840400000121000000a038838000008110e0000001843800000c1109000002044380000002101000000184000000012100000c8018800000281220e0000004843800000c5100
  | 7, 3, 2 => 0x28418000010810000000038418000000a10900000008418000000e10e00000304424004250820e00000048438000010c10600000324424002048020900000008400002550020e00000038404000010110900000038400000000e100000c8048800000000610600000038424000008110e00000018438000281220900000204424000000e10000000028424000000a10e000002104000000002100000020488240000081109
  | 7, 3, 3 => 0x320404000000e10e00041100800000081220e00000320404000000210100000048418000180e2090000031442400000c81000000003843800000c810000000038424000000210900000048438000000210e00000008424000000a10900000028424000001210000000430400000004110900000008438000008510e00000048400000010c100000000084180000006101000000384240000002101000003204000000006109
  | 7, 3, 4 => 0x18424000000210e00000028400000000210000000310400000000e10600000028424000010d10000000424438000010c1090000030040000000c810b00000310400000010010100000214438000281220000000028418000000210e00000300438000010110900000400438001550020e00000048404000010810000000210400000004010000000200400000000a10e000004144000000812209000000084180000101109
  | 7, 3, 5 => 0x18404000000e10900000038400000001210600000320400000000a10900000048424000000210900000008438000000210000000018438000280e20900101400800000180e2000000004840000000c810000000038438000010010000000100400000000e1090011420483800405002000000004842400000061090000002841800000121090000032042c000000e100000000384380000080109000000284180000806200
  | 7, 3, 6 => 0x55300838000004010000000008424000180e20000000008400000000210900000048424000010010900000028424000000210100000008438000010510000000038418000080e2000000002842400000c810900000048438000008010000000028404000000610100000038400000001210000000324424000000e10e0000201882400000021090008404880000000c810100000048438000010c1060000602882400000c110e
  | 7, 3, 7 => 0x18418000010010900000018418000000210000002038838000000e10600000048424000081220e00000434424000004110000000038424000001210000000008418000000210900000404424000281220900000028424000010010000000028438000000210000000048404000000610100000048424000010c1060000603880000000121010000002842400000c010000000320404000000a10900000048438000180a200
  | 7, 3, 8 => 0x43041800000021000000e048800000000210e00000048404000000210000000028418000010110e00000048400000008510e00000008418000000e10100000324424000001210e00000018438000008510900000304438000181220e00002028800000008110e00000038424000000a10600000038400000001210600000008438000080a20900000028438000180a20900000048400000001210900002028800000381220e
  | 7, 3, 9 => 0xa048838000010010900000008418000000210e0000003840000000401000000004840000000021010000032040400000c01000008120082400000c910900000048438000000210e0000004840000000061090000002840400000c410000000048400004250820900002028838000000e10000000300400000010510e00000048404000000a1000000020040000000c910e00000018424000000e109000000484240000006100
  | 7, 3, 10 => 0x8424000010810000000018424000010c1000000030042400000121090000032040000000841000000000842400018122000000004842400000c510900000048438001044020000000320400000010010900000018438000000610100000008424000001210900000410400000000210000000320428000000610e00006048800000000210e00000420424000000e101000000484380000012100000000384240000108100
  | 7, 3, 11 => 0x6048838000001210600000320428004144120900000028404000000210100000008438000000e1000000040442400000061090000001843800001051000005530080000008062000000021442400000c810000000018400000001210e00000400438000080e20e0000030040000018122090000e04882400000121000000004842400104402000000002842400001081000000204882400000c010900041100800000000e109
  | 7, 3, 12 => 0x214400000000610600000008424000281220900000038404000010c10000000008400000004110e00000320404000001210e00000008424000008510e00000210400000001210900000404424004150420000000028424000081220000000404438000000610e0000030041800000c51090000002842400000121060000003840400000c410000000028438000000a10e00000200400000081220000000038438000000e100
  | 7, 3, 13 => 0x95300838000000a10100000008400000000610e0000030041800254c020900000028400000000210600000028438000000210000000028400000000610e0000020443800000121090000a048838000010910e00000048424002550020e00000048400000000210000000038438000000610000000028424000008110900000028438004508120e00000404438000001210000000018400000000210000000048418000010110e
  | 7, 3, 14 => 0x48424000000e1010000e048838000000610e001014008240000108100000c80488000000012109000060388240000002109000000084240032012200000000484000000002109000000084180000006106000000184380042508209000c8048800000000210100000028418000080a20e00000008404000010110900000038424000180a2090000003842400320062000000000840400001001010000004843800000c8100
  | 7, 3, 15 => 0x38400000000a10600000320400000000a10e00000008424000281220000000018424000000e10900000038418000000e10600000038400000001210600000018438000000210900000320400000001210900000038424000004010000000424424000000210e00000104424000008010900000018400000008510e00000048424000000a10e0000030042400000c8100000002144380000080100000000284380000002109
  | 7, 4, 0 => 0x104400000001210e0000002843800000061060000a038800000000610e00000400400000080a20000000430418004250820900000008400000280e20900000100400000001210900000028404000000e10e0000000843800000c010e00000018400000001210900000424424000280e20000000008404000000210600000038424000000210900006038838000000a10900000048424000001210e000000184000000002109
  | 7, 4, 1 => 0x400404000000210e00000320428004504120000000038418000010c10000000028438000000210100000414400000010510e00000028424000000610600000430424000000a1000000004842400000061090000004840000000c010600000320404000000a10e00000320404000000610000000008438000000210900000048438000000610100000038438000001210900000008400000010110e000000084240000006100
  | 7, 4, 2 => 0x8438000000210900000048404000004110000002048800000000e10000000008400000000210900000018404000001210900000414424000000210e00000018404004050020000000028424000010c10e00000008404000000610000000028418000000210e00000008404000000e10100000028424000001210e00000320400000010510e00000028400000280e20e0000043041800000c8101000000084240000002101
  | 7, 4, 3 => 0x48424001550020900000008424002048020900002038824000080620e0000002840000000c110900000430418000000610000000300400000000210600000320400000010910900000048438000181220900000430424000000610000000424424000010910900000008418000001210000000018400000000610000095400838000008110e0000e048824000000e10900000028418000000e109000003204000001812200
  | 7, 4, 4 => 0x320404000000e10900000028404000010510e00000300438000000e10000000018424000010910000000104400001550020e00000038418000000210e00000008418000000a10900000100400000010410000002038838000381220000000008404000000610600000018404000001210900000320404000000e1060000a04880000000c81090000003842400000c81000000010442400038122000008120082400000c8109
  | 7, 4, 5 => 0x28400000000210e00000430418000000210900000434424000008110e00000028418000001210900000200424000000610e00000008400000000610000000214424000000a10900000038424000080a20e0000043040000000c41000011420483800000c810000002048824000000e1090000604882400000061060000032040000000121000010140083800000c11090000020040000000061010000a0488240000012101
  | 7, 4, 6 => 0x8424000008410000105008824000010110000000048418000000a10600000430418000000e109000002144240000081109
  | 8, 0, 0 => 0x320424000001210e00000038400000010c10000000200400000000610900000400424000008010000000420400000010110e00000008438000010110900000424438000010110000000048424000010010900000048424000000a10e00000104400000001210000000104400000004110000000430424000000210e000000084000000081109000004144000000012109000002004380000100100000004204000000105109
  | 8, 0, 1 => 0x400400000008110900000204424000000210e00000424438000010010900000414424000001210000000048400000010110e00000018400000000e10e0000040442400000c810e00000048424000010510000000028438000010110000000430438000008510e0000040440000000c410000000028400000010110e00000310400000000a10900000320438000000a10000000038438000001210e00000400438000010810e
  | 8, 0, 2 => 0x31040000000c010000000028438000000e1090000001843800000c810e00000204438000004110e00000404424000000210e0000020040000000c81000000020043800000c81000000030042400000c810900000404400000004110e0000021040000000411000000041040000000841000000002840000000c810e0000043043800000c4100000004244380000012100000000284380000101109000000484380000100100
  | 8, 0, 3 => 0x48438000010110900000008438000004010000000100400000010c10e00000320400000008110e00000200438000010010000000214424000000a10900000414438000001210900000104438000008410000000008424000001210000000214438000008010900000400424000010810e0000021040000000c01090000041442400000c010e0000002842400000801000000002843800000121090000040442400000c0100
  | 8, 0, 4 => 0x430438000010410000000300424000010810e00000028424000000210900000200438000000210e00000320400000008010900000320400000008010e00000008424000001210e00000200424000010010e0000043042400000061000000030040000000c010e00000420424000000210e00000404400000010910e000001044380000006100000000284380000101100000000284000000041109000000084000000002100
  | 8, 0, 5 => 0x8400000000a10e00000018400000010510000000008438000010910e00000210400000010010e00000210400000004110900000214438000000e10000000008400000000e10000000048424000000610e00000048400000008510900000430400000004010000000420438000000210900000048438000010910900000400424000008110e0000042042400000c010900000038424000008510e000000284380000104100
  | 8, 0, 6 => 0x420400000000a1000000000843800000c010000000424438000010810000000410400000000210900000430438000000210e0000000842400001091090000002842400000801090000030042400000c810000000048400000000a10900000320400000000210900000048400000010c1090000003842400000c810000000048438000004110900000320400000010110900000200424000000210000000414400000010510e
  | 8, 0, 7 => 0x20042400001051000000001840000000851090000002843800000c010e00000038400000004110900000420424000010110e00000420438000000610e00000214424000010c10e00000038438000010c10900000028424000008110e00000420424000004110900000210400000010910900000048438000010510e00000028424000010c10000000404400000010c100000000484240000002109000003004000000040100
  | 8, 0, 8 => 0x842400000c810000000300424000010910900000008438000010810900000414438000010c10000000048424000008410000000300438000000a10e00000018400000010810000000018400000008110900000028424000000210900000424424000000210000000028424000000610000000008400000000610e000001004000000012100000001004000000006109000000384240000002109000000184000000002100
  | 8, 0, 9 => 0x20443800000061000000004843800000021000000020040000000c81090000043042400000811090000020040000000c010000000300438000010510e0000032042400001051090000040043800001051090000032043800001041000000043042400000851090000041040000000411000000040443800000411000000004842400000c810000000204438000000e10e00000320400000001210e0000042042400000c8100
  | 8, 0, 10 => 0x28438000001210000000048438000001210000000028424000001210000000400424000000a1090000030040000000c81090000000840000001051000000000840000000121090000041440000000021090000040040000000061090000002842400000c010e00000200424000001210900000008424000000e10000000424424000000a1000000003840000000c410000000310400000000610900000104424000000e109
  | 8, 0, 11 => 0x400438000000210000000310400000008110900000400424000000210e0000001842400000c810000000200438000010510900000214424000001210e00000204424000008010000000300424000001210900000018400000010c10000000400400000010810900000430400000010010000000414424000010010e00000420400000010810000000008400000010c1090000010440000000401000000004840000000c810e
  | 8, 0, 12 => 0x10443800000c810900000048424000001210000000214438000010810e00000404438000000210900000424424000000e10e00000320424000000610000000018400000000e10900000028424000000610000000410400000000a10e
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 13 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x1_0 roots_x1_0 8 s ws hint
  | 1 => checkCutEntry dom_x2_0 roots_x2_0 7 s ws hint
  | 2 => checkCutEntry dom_x1_0_x2_1 roots_x1_0_x2_1 5 s ws hint
  | 3 => checkCutEntry dom_x0_1_x4_0 roots_x0_1_x4_0 5 s ws hint
  | 4 => checkCutEntry dom_x0_1_x5_0 roots_x0_1_x5_0 5 s ws hint
  | 5 => checkCutEntry dom_x5_1 roots_x5_1 6 s ws hint
  | 6 => checkCutEntry dom_x5_0 roots_x5_0 7 s ws hint
  | 7 => checkCutEntry dom_x2_0_x3_1_x5_0 roots_x2_0_x3_1_x5_0 4 s ws hint
  | 8 => checkCutEntry dom_x4_0_x5_0 roots_x4_0_x5_0 5 s ws hint
  | 9 => checkCutEntry dom_x3_1 roots_x3_1 8 s ws hint
  | 10 => checkCutEntry dom_x0_0 roots_x0_0 6 s ws hint
  | 11 => checkCutEntry dom_x0_0_x5_1 roots_x0_0_x5_1 5 s ws hint
  | 12 => checkCutEntry dom_x3_1_x5_1 roots_x3_1_x5_1 5 s ws hint
  | 13 => checkCutEntry dom_x2_1_x4_1 roots_x2_1_x4_1 5 s ws hint
  | 14 => checkCutEntry dom_x4_1 roots_x4_1 8 s ws hint
  | 15 => checkCutEntry dom_x0_0_x3_1 roots_x0_0_x3_1 5 s ws hint
  | 16 => checkCutEntry dom_x0_0_x4_1 roots_x0_0_x4_1 5 s ws hint
  | 17 => checkCutEntry dom_x0_0_x3_1_x5_1 roots_x0_0_x3_1_x5_1 4 s ws hint
  | 18 => checkCutEntry dom_x0_0_x4_1_x5_1 roots_x0_0_x4_1_x5_1 4 s ws hint
  | 19 => checkCutEntry dom_x0_1_x4_0_x5_0 roots_x0_1_x4_0_x5_0 4 s ws hint
  | 20 => checkCutEntry dom_x0_1 roots_x0_1 6 s ws hint
  | 21 => checkCutEntry dom_x2_1 roots_x2_1 6 s ws hint
  | 22 => checkCutEntry dom_x4_0 roots_x4_0 6 s ws hint
  | 23 => checkCutEntry dom_x3_1_x4_0 roots_x3_1_x4_0 5 s ws hint
  | 24 => checkCutEntry dom_x1_0_x2_1_x4_1 roots_x1_0_x2_1_x4_1 4 s ws hint
  | 25 => checkCutEntry dom_x3_1_x4_0_x5_0 roots_x3_1_x4_0_x5_0 4 s ws hint
  | 26 => checkCutEntry dom_x4_1_x5_1 roots_x4_1_x5_1 5 s ws hint
  | 27 => checkCutEntry dom_x2_0_x5_0 roots_x2_0_x5_0 5 s ws hint
  | 28 => checkCutEntry dom_x2_0_x3_1 roots_x2_0_x3_1 5 s ws hint
  | 29 => checkCutEntry dom_x3_1_x5_0 roots_x3_1_x5_0 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_63 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x2_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_1_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x3_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_1_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x3_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_1_x4_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x2_1_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1_x4_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1_x5_0 _ hc
  · contradiction
def p0Subs : List Nat := [6, 1, 9, 0, 14, 3, 20, 10, 22, 21, 11, 15, 5, 12, 4, 2, 7, 8, 16, 27, 17, 13, 19, 26, 18, 23, 24, 25, 29, 28]
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
private theorem z5 : ∀ i, 0 ≤ i → i < 11 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 11 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 64 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 64 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_64 : ∀ i, 64 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 64 64 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_128 : ∀ i, 128 ≤ i → i < 148 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 20 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 148 → Z 6 i = true := (range_split z6_0 (range_split z6_64 z6_128))
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
private theorem z7_512 : ∀ i, 512 ≤ i → i < 530 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 18 512 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 530 → Z 7 i = true := (range_split (range_split (range_split z7_0 z7_64) (range_split z7_128 z7_192)) (range_split (range_split z7_256 z7_320) (range_split z7_384 (range_split z7_448 z7_512))))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 64 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_64 : ∀ i, 64 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 64 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_128 : ∀ i, 128 ≤ i → i < 192 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_192 : ∀ i, 192 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 192 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_256 : ∀ i, 256 ≤ i → i < 288 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 32 256 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 288 → Z 8 i = true := (range_split (range_split z8_0 z8_64) (range_split z8_128 (range_split z8_192 z8_256)))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 27 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 27 0 = true)
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

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 13]⟩], 16⟩
theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by simp [wit, PEqualNP.MetaComplexity.Monotone2]
theorem wit_size : wit.size ≤ 11 := by decide
theorem wit_eval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = ((fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4005619904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))) x := by decide +kernel
theorem hT6 : ∀ r : Fin 64, goal_all.testBit r.val = ((fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4005619904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))) (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4005619904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 11 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4005619904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_all 11 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_40171_aux

theorem PEqualNP.Outside.L_meta_40171 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4005619904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4005619904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s hs
  have hlb : 11 ≤ s := PEqualNP.Outside.L_meta_40171_aux.lower s hs
  exact ⟨PEqualNP.Outside.L_meta_40171_aux.wit, PEqualNP.Outside.L_meta_40171_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_40171_aux.wit_size hlb, PEqualNP.Outside.L_meta_40171_aux.wit_eval⟩
