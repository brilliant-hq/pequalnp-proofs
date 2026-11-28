import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50586

open PEqualNP.CircuitLowerBounds

def full : Nat := 63
def tA : Nat := 13
def tB : Nat := 33
def tC : Nat := 40
def bank0 : List Nat := [62, 60, 56, 48, 32, 0, 63]

def okGate (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

def gmask (m : List Nat) (g : Gate) : Nat :=
  match g.op, g.inputs with
  | GateOp.and, [] => full
  | GateOp.and, [i] => m.getD i 0
  | GateOp.and, i :: j :: _ => m.getD i 0 &&& m.getD j 0
  | GateOp.or, [] => 0
  | GateOp.or, [i] => m.getD i 0
  | GateOp.or, i :: j :: _ => m.getD i 0 ||| m.getD j 0
  | GateOp.not, [] => full
  | GateOp.not, i :: _ => full ^^^ m.getD i 0
  | _, _ => 0

def mwires (gs : List Gate) (m : List Nat) : List Nat :=
  gs.foldl (fun m g => m ++ [gmask m g]) m

def notcnt (gs : List Gate) : Nat := PEqualNP.NotBracket.notCount ⟨gs, 0⟩

def Has3 (bank : List Nat) : Prop := tA ∈ bank ∧ tB ∈ bank ∧ tC ∈ bank

def missing (bank : List Nat) : Nat :=
  (if tA ∈ bank then 0 else 1) + (if tB ∈ bank then 0 else 1) + (if tC ∈ bank then 0 else 1)

def Sol : Nat → Nat → List Nat → Prop
  | 0, _, bank => Has3 bank
  | f + 1, n, bank => Has3 bank ∨
      (∃ a ∈ bank, ∃ b ∈ bank, (a &&& b) ∉ bank ∧ Sol f n (bank ++ [a &&& b])) ∨
      (∃ a ∈ bank, ∃ b ∈ bank, (a ||| b) ∉ bank ∧ Sol f n (bank ++ [a ||| b])) ∨
      (∃ a ∈ bank, (full ^^^ a) ∉ bank ∧ 0 < n ∧ Sol f (n - 1) (bank ++ [full ^^^ a]))

def force {α : Type} (w : Nat) (cont : Nat → α) : α :=
  Nat.rec (cont 0) (fun k _ => cont (k + 1)) w

theorem force_eq {α : Type} (w : Nat) (cont : Nat → α) : force w cont = cont w := by
  cases w <;> rfl

def bitsOf (bank : List Nat) : Nat := bank.foldl (fun s x => s ||| (1 <<< x)) 0

theorem bits_fold (bank : List Nat) (s x : Nat) :
    (bank.foldl (fun s x => s ||| (1 <<< x)) s).testBit x = (s.testBit x || decide (x ∈ bank)) := by
  induction bank generalizing s with
  | nil => simp
  | cons y ys ih =>
    rw [List.foldl_cons, ih]
    by_cases h : x = y
    · subst h; simp [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow_self]
    · have h2 : y ≠ x := fun e => h e.symm
      simp [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, h, h2]

theorem bits_mem (bank : List Nat) (x : Nat) : (bitsOf bank).testBit x = true ↔ x ∈ bank := by
  unfold bitsOf
  rw [bits_fold]
  simp

theorem bits_not (bank : List Nat) (x : Nat) (h : x ∉ bank) : (bitsOf bank).testBit x = false := by
  cases e : (bitsOf bank).testBit x
  · rfl
  · exact absurd ((bits_mem bank x).mp e) h

theorem bits_append (bank : List Nat) (m : Nat) : bitsOf (bank ++ [m]) = bitsOf bank ||| (1 <<< m) := by
  simp [bitsOf, List.foldl_append]

def missS (S : Nat) : Nat :=
  (if S.testBit tA then 0 else 1) + (if S.testBit tB then 0 else 1) + (if S.testBit tC then 0 else 1)

theorem missS_eq (bank : List Nat) : missS (bitsOf bank) = missing bank := by
  unfold missS missing
  by_cases hA : tA ∈ bank <;> by_cases hB : tB ∈ bank <;> by_cases hC : tC ∈ bank <;>
    simp [hA, hB, hC, (bits_mem bank tA).mpr, (bits_mem bank tB).mpr, (bits_mem bank tC).mpr, bits_not]

def pairsAny : List Nat → (Nat → Nat → Bool) → Bool
  | [], _ => false
  | a :: t, f => t.any (f a) || pairsAny t f

theorem pairsAny_of (f : Nat → Nat → Bool) (sym : ∀ a b, f a b = f b a) :
    ∀ (l : List Nat) (a b : Nat), a ∈ l → b ∈ l → a ≠ b → f a b = true → pairsAny l f = true := by
  intro l
  induction l with
  | nil => intro a b ha; simp at ha
  | cons x t ih =>
    intro a b ha hb hab hf
    rcases List.mem_cons.mp ha with rfl | ha2
    · have hb2 : b ∈ t := by
        rcases List.mem_cons.mp hb with e | h
        · exact absurd e.symm hab
        · exact h
      simp only [pairsAny, Bool.or_eq_true, List.any_eq_true]
      exact Or.inl ⟨b, hb2, hf⟩
    · rcases List.mem_cons.mp hb with rfl | hb2
      · simp only [pairsAny, Bool.or_eq_true, List.any_eq_true]
        exact Or.inl ⟨a, ha2, by rw [sym]; exact hf⟩
      · simp only [pairsAny, Bool.or_eq_true]
        exact Or.inr (ih a b ha2 hb2 hab hf)

def pairF (S : Nat) (k : Nat → Bool) (a b : Nat) : Bool :=
  force (a &&& b) (fun m => !S.testBit m && k m) || force (a ||| b) (fun m => !S.testBit m && k m)

theorem pairF_sym (S : Nat) (k : Nat → Bool) (a b : Nat) : pairF S k a b = pairF S k b a := by
  unfold pairF
  rw [Nat.land_comm a b, Nat.lor_comm a b]

def chk : Nat → Nat → List Nat → Nat → Bool
  | 0, _, _, S => S.testBit tA && S.testBit tB && S.testBit tC
  | f + 1, n, bank, S =>
      (S.testBit tA && S.testBit tB && S.testBit tC) ||
      (Nat.ble (missS S) (f + 1) &&
        (pairsAny bank (pairF S (fun m => force (S ||| (1 <<< m)) (fun S2 => chk f n (bank ++ [m]) S2))) ||
         (Nat.blt 0 n && bank.any fun a =>
            force (full ^^^ a) (fun m => !S.testBit m &&
              force (S ||| (1 <<< m)) (fun S2 => chk f (n - 1) (bank ++ [m]) S2)))))

theorem sol_equiv : ∀ (f n : Nat) (b1 b2 : List Nat), (∀ x, x ∈ b1 ↔ x ∈ b2) → Sol f n b1 → Sol f n b2 := by
  intro f
  induction f with
  | zero =>
    intro n b1 b2 eq h
    exact ⟨(eq _).mp h.1, (eq _).mp h.2.1, (eq _).mp h.2.2⟩
  | succ f ih =>
    intro n b1 b2 eq h
    have app : ∀ m, ∀ x, x ∈ b1 ++ [m] ↔ x ∈ b2 ++ [m] := by
      intro m x
      simp only [List.mem_append, List.mem_singleton, eq x]
    rcases h with h | ⟨a, ha, b, hb, hn, h⟩ | ⟨a, ha, b, hb, hn, h⟩ | ⟨a, ha, hn, hp, h⟩
    · exact Or.inl ⟨(eq _).mp h.1, (eq _).mp h.2.1, (eq _).mp h.2.2⟩
    · exact Or.inr (Or.inl ⟨a, (eq _).mp ha, b, (eq _).mp hb, fun c => hn ((eq _).mpr c), ih _ _ _ (app _) h⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨a, (eq _).mp ha, b, (eq _).mp hb, fun c => hn ((eq _).mpr c), ih _ _ _ (app _) h⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨a, (eq _).mp ha, fun c => hn ((eq _).mpr c), hp, ih _ _ _ (app _) h⟩))

theorem sol_fuel : ∀ (f n : Nat) (bank : List Nat), Sol f n bank → Sol (f + 1) n bank := by
  intro f
  induction f with
  | zero => intro n bank h; exact Or.inl h
  | succ f ih =>
    intro n bank h
    rcases h with h | ⟨a, ha, b, hb, hn, h⟩ | ⟨a, ha, b, hb, hn, h⟩ | ⟨a, ha, hn, hp, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨a, ha, b, hb, hn, ih _ _ h⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨a, ha, b, hb, hn, ih _ _ h⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨a, ha, hn, hp, ih _ _ h⟩))

theorem sol_nots : ∀ (f n : Nat) (bank : List Nat), Sol f n bank → Sol f (n + 1) bank := by
  intro f
  induction f with
  | zero => intro n bank h; exact h
  | succ f ih =>
    intro n bank h
    rcases h with h | ⟨a, ha, b, hb, hn, h⟩ | ⟨a, ha, b, hb, hn, h⟩ | ⟨a, ha, hn, hp, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨a, ha, b, hb, hn, ih _ _ h⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨a, ha, b, hb, hn, ih _ _ h⟩))
    · refine Or.inr (Or.inr (Or.inr ⟨a, ha, hn, Nat.succ_pos _, ?_⟩))
      have e : n + 1 - 1 = (n - 1) + 1 := by omega
      rw [e]
      exact ih _ _ h

theorem sol_weaken {f n f2 n2 : Nat} {bank : List Nat} (h : Sol f n bank) (hf : f ≤ f2) (hn : n ≤ n2) :
    Sol f2 n2 bank := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hf
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hf hn
  induction k with
  | zero =>
    induction l with
    | zero => exact h
    | succ l ih => exact sol_nots _ _ _ ih
  | succ k ih => exact sol_fuel _ _ _ ih

theorem miss_step (bank : List Nat) (m : Nat) : missing bank ≤ missing (bank ++ [m]) + 1 := by
  have key : ∀ x : Nat, (if x ∈ bank then 0 else 1) ≤ (if x ∈ bank ++ [m] then 0 else 1) + (if x = m then 1 else 0) := by
    intro x
    by_cases h1 : x ∈ bank <;> by_cases h2 : x = m <;> simp [h1, h2] <;> split_ifs <;> omega
  have d : (if tA = m then 1 else 0) + (if tB = m then 1 else 0) + (if tC = m then 1 else 0) ≤ 1 := by
    unfold tA tB tC
    split_ifs <;> omega
  have k1 := key tA
  have k2 := key tB
  have k3 := key tC
  unfold missing
  omega

theorem sol_missing : ∀ (f n : Nat) (bank : List Nat), Sol f n bank → missing bank ≤ f := by
  intro f
  induction f with
  | zero =>
    intro n bank h
    simp [missing, h.1, h.2.1, h.2.2]
  | succ f ih =>
    intro n bank h
    rcases h with h | ⟨a, _, b, _, _, h⟩ | ⟨a, _, b, _, _, h⟩ | ⟨a, _, _, _, h⟩
    · simp [missing, h.1, h.2.1, h.2.2]
    · have := ih _ _ h; have := miss_step bank (a &&& b); omega
    · have := ih _ _ h; have := miss_step bank (a ||| b); omega
    · have := ih _ _ h; have := miss_step bank (full ^^^ a); omega

theorem has3_bits (bank : List Nat) (h : Has3 bank) :
    ((bitsOf bank).testBit tA && (bitsOf bank).testBit tB && (bitsOf bank).testBit tC) = true := by
  simp [(bits_mem bank tA).mpr h.1, (bits_mem bank tB).mpr h.2.1, (bits_mem bank tC).mpr h.2.2]

theorem chk_sound : ∀ (f n : Nat) (bank : List Nat), Sol f n bank → chk f n bank (bitsOf bank) = true := by
  intro f
  induction f with
  | zero =>
    intro n bank h
    exact has3_bits bank h
  | succ f ih =>
    intro n bank h
    have hm : Nat.ble (missS (bitsOf bank)) (f + 1) = true := by
      rw [missS_eq]; exact Nat.ble_eq_true_of_le (sol_missing _ _ _ h)
    have kk : ∀ (n2 m : Nat), Sol f n2 (bank ++ [m]) →
        chk f n2 (bank ++ [m]) (bitsOf bank ||| (1 <<< m)) = true := by
      intro n2 m hs
      rw [← bits_append]
      exact ih _ _ hs
    rcases h with h | ⟨a, ha, b, hb, hin, h⟩ | ⟨a, ha, b, hb, hin, h⟩ | ⟨a, ha, hin, hn, h⟩
    · simp only [chk, has3_bits bank h, Bool.true_or]
    · have hab : a ≠ b := by
        intro e; subst e; rw [Nat.and_self] at hin; exact hin ha
      have pf : pairF (bitsOf bank) (fun m => force (bitsOf bank ||| (1 <<< m)) (fun S2 => chk f n (bank ++ [m]) S2)) a b = true := by
        unfold pairF
        simp [force_eq, bits_not bank _ hin, kk n _ h]
      have pa := pairsAny_of _ (pairF_sym _ _) bank a b ha hb hab pf
      simp only [chk, hm, pa, Bool.true_and, Bool.true_or, Bool.or_true]
    · have hab : a ≠ b := by
        intro e; subst e; rw [Nat.or_self] at hin; exact hin ha
      have pf : pairF (bitsOf bank) (fun m => force (bitsOf bank ||| (1 <<< m)) (fun S2 => chk f n (bank ++ [m]) S2)) a b = true := by
        unfold pairF
        simp [force_eq, bits_not bank _ hin, kk n _ h]
      have pa := pairsAny_of _ (pairF_sym _ _) bank a b ha hb hab pf
      simp only [chk, hm, pa, Bool.true_and, Bool.true_or, Bool.or_true]
    · have e : (bank.any fun a =>
          force (full ^^^ a) (fun m => !(bitsOf bank).testBit m &&
            force (bitsOf bank ||| (1 <<< m)) (fun S2 => chk f (n - 1) (bank ++ [m]) S2))) = true := by
        rw [List.any_eq_true]
        refine ⟨a, ha, ?_⟩
        simp [force_eq, bits_not bank _ hin, kk (n - 1) _ h]
      have hb : Nat.blt 0 n = true := by
        rw [Nat.blt_eq]; exact hn
      simp only [chk, hm, e, hb, Bool.true_and, Bool.or_true]

theorem getD_mem (m : List Nat) (h0 : 0 ∈ m) (i : Nat) : m.getD i 0 ∈ m := by
  by_cases hi : i < m.length
  · rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  · rw [List.getD_eq_default _ _ (by omega)]; exact h0

theorem mwires_cons (g : Gate) (gs : List Gate) (m : List Nat) :
    mwires (g :: gs) m = mwires gs (m ++ [gmask m g]) := rfl

theorem mwires_sub : ∀ (gs : List Gate) (m : List Nat), ∀ x ∈ m, x ∈ mwires gs m := by
  intro gs
  induction gs with
  | nil => intro m x hx; exact hx
  | cons g gs ih =>
    intro m x hx
    rw [mwires_cons]
    exact ih _ _ (List.mem_append_left _ hx)

theorem notcnt_le (g : Gate) (gs : List Gate) : notcnt gs ≤ notcnt (g :: gs) := by
  simp only [notcnt, PEqualNP.NotBracket.notCount, List.filter_cons]
  split <;> simp

theorem bridge : ∀ (gs : List Gate) (m : List Nat), (∀ g ∈ gs, okGate g) → 0 ∈ m → full ∈ m →
    Has3 (mwires gs m) → Sol gs.length (notcnt gs) m := by
  intro gs
  induction gs with
  | nil => intro m _ _ _ h; exact h
  | cons g gs ih =>
    intro m hok h0 hf h
    rw [mwires_cons] at h
    have tail := ih (m ++ [gmask m g]) (fun g2 hg2 => hok g2 (List.mem_cons_of_mem _ hg2))
      (List.mem_append_left _ h0) (List.mem_append_left _ hf) h
    by_cases hx : gmask m g ∈ m
    · have s1 : Sol gs.length (notcnt gs) m := sol_equiv _ _ _ _ (by
        intro x
        simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro (h1 | h1)
          · exact h1
          · rw [h1]; exact hx
        · intro h1; exact Or.inl h1) tail
      exact sol_weaken (sol_fuel _ _ _ s1) (Nat.le_refl _) (notcnt_le g gs)
    · obtain ⟨hop, hlen⟩ := hok g List.mem_cons_self
      obtain ⟨op, inputs⟩ := g
      simp only at hop hlen
      rcases hop with rfl | rfl | rfl
      · have nc : notcnt (⟨GateOp.and, inputs⟩ :: gs) = notcnt gs := by
          simp [notcnt, PEqualNP.NotBracket.notCount]
        rw [nc]
        match inputs, hlen with
        | [], _ => exact absurd hf (by simpa [gmask] using hx)
        | [i], _ => exact absurd (getD_mem m h0 i) (by simpa [gmask] using hx)
        | [i, j], _ =>
          refine Or.inr (Or.inl ⟨m.getD i 0, getD_mem m h0 i, m.getD j 0, getD_mem m h0 j, ?_, ?_⟩)
          · simpa [gmask] using hx
          · simpa [gmask] using tail
        | _ :: _ :: _ :: _, hl => simp at hl
      · have nc : notcnt (⟨GateOp.or, inputs⟩ :: gs) = notcnt gs := by
          simp [notcnt, PEqualNP.NotBracket.notCount]
        rw [nc]
        match inputs, hlen with
        | [], _ => exact absurd h0 (by simpa [gmask] using hx)
        | [i], _ => exact absurd (getD_mem m h0 i) (by simpa [gmask] using hx)
        | [i, j], _ =>
          refine Or.inr (Or.inr (Or.inl ⟨m.getD i 0, getD_mem m h0 i, m.getD j 0, getD_mem m h0 j, ?_, ?_⟩))
          · simpa [gmask] using hx
          · simpa [gmask] using tail
        | _ :: _ :: _ :: _, hl => simp at hl
      · have nc : notcnt (⟨GateOp.not, inputs⟩ :: gs) = notcnt gs + 1 := by
          simp [notcnt, PEqualNP.NotBracket.notCount]
        rw [nc]
        match inputs, hlen with
        | [], _ => exact absurd hf (by simpa [gmask] using hx)
        | i :: rest, _ =>
          refine Or.inr (Or.inr (Or.inr ⟨m.getD i 0, getD_mem m h0 i, ?_, Nat.succ_pos _, ?_⟩))
          · simpa [gmask] using hx
          · simpa [gmask] using tail

theorem full_bit (t : Nat) (ht : t < 6) : full.testBit t = true := by
  unfold full
  interval_cases t <;> decide

theorem gate_sim (t : Nat) (ht : t < 6) (w : List Bool) (m : List Nat)
    (inv0 : ∀ j, w.getD j false = (m.getD j 0).testBit t) (g : Gate) (hok : okGate g) :
    g.op.eval (g.inputs.map fun i => w.getD i false) = (gmask m g).testBit t := by
  obtain ⟨hop, hlen⟩ := hok
  obtain ⟨op, inputs⟩ := g
  simp only at hop hlen
  have inv : ∀ j : Nat, w[j]?.getD false = (m[j]?.getD 0).testBit t := by
    intro j; simpa using inv0 j
  rcases hop with rfl | rfl | rfl
  · match inputs, hlen with
    | [], _ => simp [GateOp.eval, gmask, full_bit t ht]
    | [i], _ => simp [GateOp.eval, gmask, inv]
    | [i, j], _ => simp [GateOp.eval, gmask, inv, Nat.testBit_and]
    | _ :: _ :: _ :: _, hl => simp at hl
  · match inputs, hlen with
    | [], _ => simp [GateOp.eval, gmask]
    | [i], _ => simp [GateOp.eval, gmask, inv]
    | [i, j], _ => simp [GateOp.eval, gmask, inv, Nat.testBit_or]
    | _ :: _ :: _ :: _, hl => simp at hl
  · match inputs, hlen with
    | [], _ => simp [GateOp.eval, gmask, full_bit t ht]
    | i :: rest, _ => simp [GateOp.eval, gmask, inv, Nat.testBit_xor, full_bit t ht]

theorem wires_sim (t : Nat) (ht : t < 6) : ∀ (gs : List Gate) (w : List Bool) (m : List Nat),
    (∀ g ∈ gs, okGate g) → w.length = m.length → (∀ j, w.getD j false = (m.getD j 0).testBit t) →
    ∀ j, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD j false =
      ((mwires gs m).getD j 0).testBit t := by
  intro gs
  induction gs with
  | nil => intro w m _ _ inv j; exact inv j
  | cons g gs ih =>
    intro w m hok hlen inv j
    rw [mwires_cons, List.foldl_cons]
    apply ih _ _ (fun g2 hg2 => hok g2 (List.mem_cons_of_mem _ hg2))
    · simp [hlen]
    · intro k
      have hg := gate_sim t ht w m inv g (hok g List.mem_cons_self)
      rcases Nat.lt_trichotomy k w.length with hk | hk | hk
      · rw [List.getD_append _ _ _ _ hk, List.getD_append _ _ _ _ (hlen ▸ hk)]
        exact inv k
      · have e1 : (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD k false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          rw [List.getD_append_right _ _ _ _ (by omega)]; simp [hk]
        have e2 : (m ++ [gmask m g]).getD k 0 = gmask m g := by
          rw [List.getD_append_right _ _ _ _ (by omega)]; simp [hk, hlen]
        rw [e1, e2, hg]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
        simp

theorem bounded : ∀ (gs : List Gate) (m : List Nat), (∀ g ∈ gs, okGate g) → (∀ x ∈ m, x < 2 ^ 6) →
    ∀ x ∈ mwires gs m, x < 2 ^ 6 := by
  intro gs
  induction gs with
  | nil => intro m _ hb x hx; exact hb x hx
  | cons g gs ih =>
    intro m hok hb x hx
    rw [mwires_cons] at hx
    refine ih _ (fun g2 hg2 => hok g2 (List.mem_cons_of_mem _ hg2)) ?_ x hx
    intro y hy
    rcases List.mem_append.mp hy with h1 | h1
    · exact hb y h1
    · rw [List.mem_singleton.mp h1]
      have gd : ∀ i, m.getD i 0 < 2 ^ 6 := by
        intro i
        by_cases hi : i < m.length
        · rw [List.getD_eq_getElem _ _ hi]; exact hb _ (List.getElem_mem hi)
        · rw [List.getD_eq_default _ _ (by omega)]; decide
      obtain ⟨hop, hlen⟩ := hok g List.mem_cons_self
      obtain ⟨op, inputs⟩ := g
      simp only at hop hlen
      have hfull : full < 2 ^ 6 := by decide
      rcases hop with rfl | rfl | rfl
      · match inputs, hlen with
        | [], _ => simpa [gmask] using hfull
        | [i], _ => simpa [gmask] using gd i
        | [i, j], _ => simpa [gmask] using Nat.and_lt_two_pow _ (gd j)
        | _ :: _ :: _ :: _, hl => simp at hl
      · match inputs, hlen with
        | [], _ => simp [gmask]
        | [i], _ => simpa [gmask] using gd i
        | [i, j], _ => simpa [gmask] using Nat.or_lt_two_pow (gd i) (gd j)
        | _ :: _ :: _ :: _, hl => simp at hl
      · match inputs, hlen with
        | [], _ => simpa [gmask] using hfull
        | i :: rest, _ => simpa [gmask] using Nat.xor_lt_two_pow hfull (gd i)

theorem eq_of_bits (x c : Nat) (hx : x < 2 ^ 6) (hc : c < 2 ^ 6)
    (h : ∀ t : Fin 6, x.testBit t.val = c.testBit t.val) : x = c := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 6
  · exact h ⟨i, hi⟩
  · have p : 2 ^ 6 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx p), Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc p)]

theorem base (t : Fin 6) : ∀ j, ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true]).getD j false =
    (bank0.getD j 0).testBit t.val := by
  intro j
  by_cases hj : j < 7
  · interval_cases j <;> fin_cases t <;> decide
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp [bank0]; omega)]
    simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem none : chk 6 2 bank0 (bitsOf bank0) = false := by decide +kernel

end PEqualNP.Outside.L_meta_50586

theorem PEqualNP.Outside.L_meta_50586 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (13 : Nat).testBit t.val ∧
    w.getD q.val false = (33 : Nat).testBit t.val ∧
    w.getD r.val false = (40 : Nat).testBit t.val)) := by
  rintro ⟨D, p, q, r, hfan, _, hnot, hsize, hval⟩
  have hok : ∀ g ∈ D.gates, PEqualNP.Outside.L_meta_50586.okGate g := by
    intro g hg
    obtain ⟨h1, h2⟩ := hfan g hg
    refine ⟨?_, h2⟩
    simpa using h1
  have sim : ∀ (t : Fin 6) (j : Nat), (D.wires ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true])).getD j false =
      ((PEqualNP.Outside.L_meta_50586.mwires D.gates PEqualNP.Outside.L_meta_50586.bank0).getD j 0).testBit t.val := by
    intro t j
    exact PEqualNP.Outside.L_meta_50586.wires_sim t.val t.isLt D.gates _ _ hok (by simp [PEqualNP.Outside.L_meta_50586.bank0])
      (PEqualNP.Outside.L_meta_50586.base t) j
  have hb := PEqualNP.Outside.L_meta_50586.bounded D.gates PEqualNP.Outside.L_meta_50586.bank0 hok (by decide)
  have h0 : (0 : Nat) ∈ PEqualNP.Outside.L_meta_50586.mwires D.gates PEqualNP.Outside.L_meta_50586.bank0 :=
    PEqualNP.Outside.L_meta_50586.mwires_sub _ _ _ (by decide)
  have key : ∀ (i : Nat) (c : Nat), c < 2 ^ 6 →
      (∀ t : Fin 6, (D.wires ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true])).getD i false = c.testBit t.val) →
      c ∈ PEqualNP.Outside.L_meta_50586.mwires D.gates PEqualNP.Outside.L_meta_50586.bank0 := by
    intro i c hc h
    have hm := PEqualNP.Outside.L_meta_50586.getD_mem _ h0 i
    have e := PEqualNP.Outside.L_meta_50586.eq_of_bits _ c (hb _ hm) hc (fun t => by rw [← sim t i]; exact h t)
    rw [← e]; exact hm
  have h3 : PEqualNP.Outside.L_meta_50586.Has3 (PEqualNP.Outside.L_meta_50586.mwires D.gates PEqualNP.Outside.L_meta_50586.bank0) :=
    ⟨key p.val 13 (by decide) (fun t => (hval t).1), key q.val 33 (by decide) (fun t => (hval t).2.1),
      key r.val 40 (by decide) (fun t => (hval t).2.2)⟩
  have s := PEqualNP.Outside.L_meta_50586.bridge D.gates PEqualNP.Outside.L_meta_50586.bank0 hok (by decide) (by decide) h3
  have s2 := PEqualNP.Outside.L_meta_50586.sol_weaken s hsize (show PEqualNP.Outside.L_meta_50586.notcnt D.gates ≤ 2 from hnot)
  have c := PEqualNP.Outside.L_meta_50586.chk_sound _ _ _ s2
  rw [PEqualNP.Outside.L_meta_50586.none] at c
  exact Bool.noConfusion c
