import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50372

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

def xs (t : Fin 6) : List Bool :=
  (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true]

def pack6 (f : Fin 6 → Bool) : Nat :=
  (if f 0 then 1 else 0) +
  2 * ((if f 1 then 1 else 0) +
  2 * ((if f 2 then 1 else 0) +
  2 * ((if f 3 then 1 else 0) +
  2 * ((if f 4 then 1 else 0) +
  2 * (if f 5 then 1 else 0)))))

lemma testBit_bit0 (b : Bool) (n : Nat) :
    ((if b then 1 else 0) + 2 * n).testBit 0 = b := by
  cases b <;> simp [Nat.testBit_zero]

lemma testBit_bitS (b : Bool) (n k : Nat) :
    ((if b then 1 else 0) + 2 * n).testBit (k + 1) = n.testBit k := by
  rw [Nat.testBit_succ]
  cases b <;> simp [Nat.add_mul_div_left]

lemma pack6_testBit (f : Fin 6 → Bool) (t : Fin 6) :
    (pack6 f).testBit t.val = f t := by
  fin_cases t
  · exact testBit_bit0 _ _
  · rw [pack6, testBit_bitS]; exact testBit_bit0 _ _
  · rw [pack6, testBit_bitS, testBit_bitS]; exact testBit_bit0 _ _
  · rw [pack6, testBit_bitS, testBit_bitS, testBit_bitS]; exact testBit_bit0 _ _
  · rw [pack6, testBit_bitS, testBit_bitS, testBit_bitS, testBit_bitS]; exact testBit_bit0 _ _
  · rw [pack6, testBit_bitS, testBit_bitS, testBit_bitS, testBit_bitS, testBit_bitS]
    change (if f 5 then 1 else 0).testBit 0 = f 5
    cases f 5 <;> rfl

lemma pack6_lt (f : Fin 6 → Bool) : pack6 f < 64 := by
  unfold pack6
  have h0 : (if f 0 then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have h1 : (if f 1 then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have h2 : (if f 2 then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have h3 : (if f 3 then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have h4 : (if f 4 then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have h5 : (if f 5 then 1 else 0) ≤ 1 := by split_ifs <;> omega
  omega

lemma testBit_ge6 {v i : Nat} (hv : v < 64) (hi : ¬ i < 6) : v.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : 6 ≤ i)))

lemma pack6_eq_of_testBit (f : Fin 6 → Bool) (v : Nat) (hv : v < 64)
    (h : ∀ t : Fin 6, f t = v.testBit t.val) : pack6 f = v := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 6
  · rw [pack6_testBit f ⟨i, hi⟩, h ⟨i, hi⟩]
  · rw [testBit_ge6 (pack6_lt f) hi, testBit_ge6 hv hi]

lemma pack6_and (f g : Fin 6 → Bool) :
    pack6 (fun t => f t && g t) = Nat.land (pack6 f) (pack6 g) := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (pack6 (fun t => f t && g t)).testBit i = (pack6 f &&& pack6 g).testBit i
  rw [Nat.testBit_and]
  by_cases hi : i < 6
  · rw [pack6_testBit _ ⟨i, hi⟩, pack6_testBit _ ⟨i, hi⟩, pack6_testBit _ ⟨i, hi⟩]
  · rw [testBit_ge6 (pack6_lt _) hi, testBit_ge6 (pack6_lt _) hi, Bool.false_and]

lemma pack6_or (f g : Fin 6 → Bool) :
    pack6 (fun t => f t || g t) = Nat.lor (pack6 f) (pack6 g) := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (pack6 (fun t => f t || g t)).testBit i = (pack6 f ||| pack6 g).testBit i
  rw [Nat.testBit_or]
  by_cases hi : i < 6
  · rw [pack6_testBit _ ⟨i, hi⟩, pack6_testBit _ ⟨i, hi⟩, pack6_testBit _ ⟨i, hi⟩]
  · rw [testBit_ge6 (pack6_lt _) hi, testBit_ge6 (pack6_lt _) hi, testBit_ge6 (pack6_lt _) hi, Bool.false_or]

lemma pack6_not (f : Fin 6 → Bool) :
    pack6 (fun t => !f t) = Nat.xor (pack6 f) 63 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (pack6 (fun t => !f t)).testBit i = (pack6 f ^^^ 63).testBit i
  rw [Nat.testBit_xor]
  by_cases hi : i < 6
  · rw [pack6_testBit _ ⟨i, hi⟩, pack6_testBit _ ⟨i, hi⟩]
    have h63 : (63 : Nat).testBit i = true := by
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [h63]
    cases f ⟨i, hi⟩ <;> rfl
  · rw [testBit_ge6 (pack6_lt _) hi, testBit_ge6 (pack6_lt _) hi, testBit_ge6 (by omega : 63 < 64) hi]
    rfl

lemma pack6_false : pack6 (fun _ => false) = 0 := rfl

lemma pack6_true : pack6 (fun _ => true) = 63 := rfl

def hasBit (m v : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight m v) 1) 1

def setBit (m v : Nat) : Nat :=
  Nat.lor m (Nat.shiftLeft 1 v)

lemma hasBit_eq_testBit (m v : Nat) : hasBit m v = m.testBit v := by
  unfold hasBit
  change (((m >>> v) &&& 1) == 1) = m.testBit v
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  cases Nat.mod_two_eq_zero_or_one (m / 2 ^ v) with
  | inl h => simp [h]
  | inr h => simp [h]

lemma hasBit_setBit (m v x : Nat) :
    hasBit (setBit m v) x = (hasBit m x || decide (x = v)) := by
  rw [hasBit_eq_testBit, hasBit_eq_testBit]
  unfold setBit
  change (m ||| (1 <<< v)).testBit x = (m.testBit x || decide (x = v))
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : x = v
  · subst h; simp
  · have hne : v ≠ x := Ne.symm h
    simp [h, hne]

def pairAny (ws : List Nat) (p : Nat → Nat → Bool) : Bool :=
  match ws with
  | [] => false
  | a :: rest => rest.any (fun b => p a b) || pairAny rest p

lemma pairAny_true_of_mem {ws : List Nat} {p : Nat → Nat → Bool}
    (hp : ∀ a b, p a b = p b a) {a b : Nat} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b)
    (h : p a b = true) : pairAny ws p = true := by
  induction ws with
  | nil => simp at ha
  | cons x rest ih =>
    simp only [pairAny, Bool.or_eq_true]
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact (hne rfl).elim
      · exact Or.inl (List.any_eq_true.mpr ⟨b, hb', h⟩)
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inl (List.any_eq_true.mpr ⟨a, ha', hp b a ▸ h⟩)
      · exact Or.inr (ih ha' hb')

def remTargets (m : Nat) : Nat :=
  (if hasBit m 2 then 0 else 1) +
  (if hasBit m 8 then 0 else 1) +
  (if hasBit m 42 then 0 else 1)

def canReach (steps nots : Nat) (ws : List Nat) (m : Nat) : Bool :=
  let rem := remTargets m
  if rem == 0 then true
  else if steps < rem then false
  else
    match steps with
    | 0 => false
    | s + 1 =>
      let notOk :=
        if nots == 0 then false
        else ws.any fun w =>
          let v := Nat.xor w 63
          if hasBit m v then false
          else canReach s (nots - 1) (v :: ws) (setBit m v)
      let binOk :=
        pairAny ws fun a b =>
          (let va := Nat.land a b
           if hasBit m va then false else canReach s nots (va :: ws) (setBit m va)) ||
          (let vo := Nat.lor a b
           if hasBit m vo then false else canReach s nots (vo :: ws) (setBit m vo))
      notOk || binOk

lemma canReach_mono_step (s : Nat) :
    ∀ n ws m, canReach s n ws m = true → canReach (s + 1) n ws m = true := by
  induction s with
  | zero =>
    intro n ws m h
    unfold canReach at h
    unfold canReach
    by_cases hr : (remTargets m == 0) = true
    · simp [hr]
    · simp only [hr, Bool.false_eq_true, ↓reduceIte] at h
      split_ifs at h
      all_goals simp at h
  | succ s ih =>
    intro n ws m h
    unfold canReach at h
    unfold canReach
    by_cases hr : (remTargets m == 0) = true
    · simp [hr]
    · simp only [hr, Bool.false_eq_true, ↓reduceIte] at h ⊢
      by_cases hlt : s + 1 < remTargets m
      · simp [hlt] at h
      · have hlt2 : ¬ (s + 2 < remTargets m) := by omega
        simp only [hlt, ↓reduceIte] at h
        simp only [hlt2, ↓reduceIte]
        rw [Bool.or_eq_true] at h ⊢
        rcases h with hnot | hbin
        · left
          by_cases hn : (n == 0) = true
          · simp [hn] at hnot
          · simp only [hn, Bool.false_eq_true, ↓reduceIte] at hnot ⊢
            rw [List.any_eq_true] at hnot ⊢
            obtain ⟨w, hw, hres⟩ := hnot
            refine ⟨w, hw, ?_⟩
            cases hb : hasBit m (Nat.xor w 63)
            · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hres ⊢
              exact ih _ _ _ hres
            · simp only [hb, ↓reduceIte] at hres
              cases hres
        · right
          have hpair : ∀ (l : List Nat) (p1 p2 : Nat → Nat → Bool),
              (∀ a b, p1 a b = true → p2 a b = true) →
              pairAny l p1 = true → pairAny l p2 = true := by
            intro l p1 p2 himp
            induction l with
            | nil => intro h0; simp [pairAny] at h0
            | cons x r ihr =>
              intro h0
              simp only [pairAny, Bool.or_eq_true] at h0 ⊢
              rcases h0 with h1 | h2
              · left
                rw [List.any_eq_true] at h1 ⊢
                obtain ⟨b, hb, hp⟩ := h1
                exact ⟨b, hb, himp x b hp⟩
              · right
                exact ihr h2
          refine hpair ws _ _ (fun a b hab => ?_) hbin
          rw [Bool.or_eq_true] at hab ⊢
          rcases hab with ha | ho
          · left
            cases hb : hasBit m (Nat.land a b)
            · simp only [hb, Bool.false_eq_true, ↓reduceIte] at ha ⊢
              exact ih _ _ _ ha
            · simp only [hb, ↓reduceIte] at ha
              cases ha
          · right
            cases hb : hasBit m (Nat.lor a b)
            · simp only [hb, Bool.false_eq_true, ↓reduceIte] at ho ⊢
              exact ih _ _ _ ho
            · simp only [hb, ↓reduceIte] at ho
              cases ho

lemma canReach_mono_not (s : Nat) :
    ∀ n ws m, canReach s n ws m = true → canReach s (n + 1) ws m = true := by
  induction s with
  | zero =>
    intro n ws m h
    unfold canReach at h ⊢
    exact h
  | succ s ih =>
    intro n ws m h
    unfold canReach at h ⊢
    by_cases hr : (remTargets m == 0) = true
    · simp [hr]
    · simp only [hr, Bool.false_eq_true, ↓reduceIte] at h ⊢
      by_cases hlt : s + 1 < remTargets m
      · simp [hlt] at h
      · simp only [hlt, ↓reduceIte] at h ⊢
        rw [Bool.or_eq_true] at h ⊢
        rcases h with hnot | hbin
        · left
          by_cases hn : (n == 0) = true
          · simp [hn] at hnot
          · have hn1 : (n + 1 == 0) = false := by simp
            simp only [hn, Bool.false_eq_true, ↓reduceIte] at hnot
            simp only [hn1, Bool.false_eq_true, ↓reduceIte]
            rw [List.any_eq_true] at hnot ⊢
            obtain ⟨w, hw, hres⟩ := hnot
            refine ⟨w, hw, ?_⟩
            cases hb : hasBit m (Nat.xor w 63)
            · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hres ⊢
              have hpos : n - 1 + 1 = n := by
                have : n ≠ 0 := by intro heq; subst heq; simp at hn
                omega
              have hsub : n + 1 - 1 = n - 1 + 1 := by omega
              rw [hsub]
              exact ih (n - 1) _ _ hres
            · simp only [hb, ↓reduceIte] at hres
              cases hres
        · right
          have hpair : ∀ (l : List Nat) (p1 p2 : Nat → Nat → Bool),
              (∀ a b, p1 a b = true → p2 a b = true) →
              pairAny l p1 = true → pairAny l p2 = true := by
            intro l p1 p2 himp
            induction l with
            | nil => intro h0; simp [pairAny] at h0
            | cons x r ihr =>
              intro h0
              simp only [pairAny, Bool.or_eq_true] at h0 ⊢
              rcases h0 with h1 | h2
              · left
                rw [List.any_eq_true] at h1 ⊢
                obtain ⟨b, hb, hp⟩ := h1
                exact ⟨b, hb, himp x b hp⟩
              · right
                exact ihr h2
          refine hpair ws _ _ (fun a b hab => ?_) hbin
          rw [Bool.or_eq_true] at hab ⊢
          rcases hab with ha | ho
          · left
            cases hb : hasBit m (Nat.land a b)
            · simp only [hb, Bool.false_eq_true, ↓reduceIte] at ha ⊢
              exact ih n _ _ ha
            · simp only [hb, ↓reduceIte] at ha
              cases ha
          · right
            cases hb : hasBit m (Nat.lor a b)
            · simp only [hb, Bool.false_eq_true, ↓reduceIte] at ho ⊢
              exact ih n _ _ ho
            · simp only [hb, ↓reduceIte] at ho
              cases ho

lemma canReach_mono {s1 s2 n1 n2 : Nat} {ws : List Nat} {m : Nat}
    (hs : s1 ≤ s2) (hn : n1 ≤ n2) (h : canReach s1 n1 ws m = true) :
    canReach s2 n2 ws m = true := by
  have h1 : canReach s2 n1 ws m = true := by
    induction hs with
    | refl => exact h
    | step _ ih => exact canReach_mono_step _ _ _ _ ih
  induction hn with
  | refl => exact h1
  | step _ ih => exact canReach_mono_not _ _ _ _ ih

lemma canReach_done {s n : Nat} {ws : List Nat} {m : Nat}
    (h2 : hasBit m 2 = true) (h8 : hasBit m 8 = true) (h42 : hasBit m 42 = true) :
    canReach s n ws m = true := by
  unfold canReach
  have hr : remTargets m = 0 := by simp [remTargets, h2, h8, h42]
  simp [hr]

lemma remTargets_setBit_le (m v : Nat) :
    remTargets m ≤ remTargets (setBit m v) + 1 := by
  unfold remTargets
  rw [hasBit_setBit, hasBit_setBit, hasBit_setBit]
  by_cases h2 : hasBit m 2 = true <;> by_cases h8 : hasBit m 8 = true <;>
    by_cases h42 : hasBit m 42 = true <;>
    by_cases e2 : 2 = v <;> by_cases e8 : 8 = v <;>
    by_cases e42 : 42 = v <;> simp_all <;> omega

lemma remTargets_le_of_canReach {s n : Nat} {ws : List Nat} {m : Nat}
    (h : canReach s n ws m = true) : remTargets m ≤ s := by
  by_contra hgt
  push Not at hgt
  unfold canReach at h
  by_cases hr : (remTargets m == 0) = true
  · simp at hr; omega
  · simp only [hr, Bool.false_eq_true, ↓reduceIte] at h
    simp [hgt] at h

lemma canReach_of_not {s n : Nat} {ws : List Nat} {m w : Nat}
    (hw : w ∈ ws) (hnew : hasBit m (Nat.xor w 63) = false)
    (hsub : canReach s n (Nat.xor w 63 :: ws) (setBit m (Nat.xor w 63)) = true) :
    canReach (s + 1) (n + 1) ws m = true := by
  unfold canReach
  by_cases hr : (remTargets m == 0) = true
  · simp [hr]
  · simp only [hr, Bool.false_eq_true, ↓reduceIte]
    have hrem : remTargets m ≤ s + 1 :=
      le_trans (remTargets_setBit_le m (Nat.xor w 63)) (Nat.add_le_add_right (remTargets_le_of_canReach hsub) 1)
    have hlt : ¬ (s + 1 < remTargets m) := by omega
    simp only [hlt, ↓reduceIte, Bool.or_eq_true]
    left
    have hn1 : (n + 1 == 0) = false := by simp
    simp only [hn1, Bool.false_eq_true, ↓reduceIte]
    rw [List.any_eq_true]
    refine ⟨w, hw, ?_⟩
    simp only [hnew, Bool.false_eq_true, ↓reduceIte]
    exact hsub

lemma canReach_of_and {s n : Nat} {ws : List Nat} {m a b : Nat}
    (ha : a ∈ ws) (hb : b ∈ ws) (hab : hasBit m a = true)
    (hnew : hasBit m (Nat.land a b) = false)
    (hsub : canReach s n (Nat.land a b :: ws) (setBit m (Nat.land a b)) = true) :
    canReach (s + 1) n ws m = true := by
  have hne : a ≠ b := by
    intro heq; subst heq
    have hself : Nat.land a a = a := Nat.and_self a
    rw [hself, hab] at hnew
    cases hnew
  unfold canReach
  by_cases hr : (remTargets m == 0) = true
  · simp [hr]
  · simp only [hr, Bool.false_eq_true, ↓reduceIte]
    have hrem : remTargets m ≤ s + 1 :=
      le_trans (remTargets_setBit_le m (Nat.land a b)) (Nat.add_le_add_right (remTargets_le_of_canReach hsub) 1)
    have hlt : ¬ (s + 1 < remTargets m) := by omega
    simp only [hlt, ↓reduceIte, Bool.or_eq_true]
    right
    refine pairAny_true_of_mem ?_ ha hb hne ?_
    · intro x y
      have h1 : Nat.land x y = Nat.land y x := Nat.and_comm x y
      have h2 : Nat.lor x y = Nat.lor y x := Nat.or_comm x y
      simp only [h1, h2]
    · simp only [Bool.or_eq_true]
      left
      simp only [hnew, Bool.false_eq_true, ↓reduceIte]
      exact hsub

lemma canReach_of_or {s n : Nat} {ws : List Nat} {m a b : Nat}
    (ha : a ∈ ws) (hb : b ∈ ws) (hab : hasBit m a = true)
    (hnew : hasBit m (Nat.lor a b) = false)
    (hsub : canReach s n (Nat.lor a b :: ws) (setBit m (Nat.lor a b)) = true) :
    canReach (s + 1) n ws m = true := by
  have hne : a ≠ b := by
    intro heq; subst heq
    have hself : Nat.lor a a = a := Nat.or_self a
    rw [hself, hab] at hnew
    cases hnew
  unfold canReach
  by_cases hr : (remTargets m == 0) = true
  · simp [hr]
  · simp only [hr, Bool.false_eq_true, ↓reduceIte]
    have hrem : remTargets m ≤ s + 1 :=
      le_trans (remTargets_setBit_le m (Nat.lor a b)) (Nat.add_le_add_right (remTargets_le_of_canReach hsub) 1)
    have hlt : ¬ (s + 1 < remTargets m) := by omega
    simp only [hlt, ↓reduceIte, Bool.or_eq_true]
    right
    refine pairAny_true_of_mem ?_ ha hb hne ?_
    · intro x y
      have h1 : Nat.land x y = Nat.land y x := Nat.and_comm x y
      have h2 : Nat.lor x y = Nat.lor y x := Nat.or_comm x y
      simp only [h1, h2]
    · simp only [Bool.or_eq_true]
      right
      simp only [hnew, Bool.false_eq_true, ↓reduceIte]
      exact hsub

def stepWires (w : Fin 6 → List Bool) (g : Gate) : Fin 6 → List Bool :=
  fun t => w t ++ [g.op.eval (g.inputs.map fun i => (w t).getD i false)]

def runWires (gs : List Gate) (w : Fin 6 → List Bool) : Fin 6 → List Bool :=
  gs.foldl stepWires w

lemma runWires_eq_foldl (gs : List Gate) (w : Fin 6 → List Bool) (t : Fin 6) :
    runWires gs w t = gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) (w t) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => exact ih (stepWires w g)

def Covered (ws : List Nat) (m : Nat) (w : Fin 6 → List Bool) : Prop :=
  (∀ v, v ∈ ws ↔ hasBit m v = true) ∧
  hasBit m 0 = true ∧
  hasBit m 63 = true ∧
  (∀ k, hasBit m (pack6 (fun t => (w t).getD k false)) = true)

def SameLen (w : Fin 6 → List Bool) (L : Nat) : Prop :=
  ∀ t : Fin 6, (w t).length = L

lemma sameLen_step (w : Fin 6 → List Bool) (L : Nat) (h : SameLen w L) (g : Gate) :
    SameLen (stepWires w g) (L + 1) := by
  intro t
  simp [stepWires, h t]

lemma covered_append {ws : List Nat} {m : Nat} {w : Fin 6 → List Bool} {L : Nat} {f : Fin 6 → Bool}
    (hl : SameLen w L) (hc : Covered ws m w) (v : Nat) (hv : pack6 f = v) :
    (hasBit m v = true → Covered ws m (fun t => w t ++ [f t])) ∧
    (hasBit m v = false → Covered (v :: ws) (setBit m v) (fun t => w t ++ [f t])) := by
  constructor
  · intro hold
    refine ⟨hc.1, hc.2.1, hc.2.2.1, fun k => ?_⟩
    rcases lt_trichotomy k L with hk | rfl | hk
    · have heq : (fun t : Fin 6 => (w t ++ [f t]).getD k false) = (fun t => (w t).getD k false) := by
        funext t
        have hlt : k < (w t).length := by rw [hl t]; exact hk
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [heq]; exact hc.2.2.2 k
    · have heq : (fun t : Fin 6 => (w t ++ [f t]).getD k false) = f := by
        funext t
        have hlt : (w t).length = k := hl t
        rw [← hlt]
        simp [List.getD_eq_getElem?_getD]
      rw [heq, hv]; exact hold
    · have heq : (fun t : Fin 6 => (w t ++ [f t]).getD k false) = (fun _ => false) := by
        funext t
        have hle : (w t ++ [f t]).length ≤ k := by simp [hl t]; omega
        exact List.getD_eq_default _ _ hle
      rw [heq, pack6_false]; exact hc.2.1
  · intro _
    refine ⟨fun x => ?_, ?_, ?_, fun k => ?_⟩
    · rw [List.mem_cons, hc.1, hasBit_setBit, Bool.or_eq_true, decide_eq_true_eq]
      exact or_comm
    · rw [hasBit_setBit, hc.2.1]; rfl
    · rw [hasBit_setBit, hc.2.2.1]; rfl
    · rcases lt_trichotomy k L with hk | rfl | hk
      · have heq : (fun t : Fin 6 => (w t ++ [f t]).getD k false) = (fun t => (w t).getD k false) := by
          funext t
          have hlt : k < (w t).length := by rw [hl t]; exact hk
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
        rw [heq, hasBit_setBit, hc.2.2.2 k]; rfl
      · have heq : (fun t : Fin 6 => (w t ++ [f t]).getD k false) = f := by
          funext t
          have hlt : (w t).length = k := hl t
          rw [← hlt]
          simp [List.getD_eq_getElem?_getD]
        rw [heq, hv, hasBit_setBit]; simp
      · have heq : (fun t : Fin 6 => (w t ++ [f t]).getD k false) = (fun _ => false) := by
          funext t
          have hle : (w t ++ [f t]).length ≤ k := by simp [hl t]; omega
          exact List.getD_eq_default _ _ hle
        rw [heq, pack6_false, hasBit_setBit, hc.2.1]; rfl

def notCnt (gs : List Gate) : Nat :=
  notCount ⟨gs, 0⟩

lemma runWires_sound (gs : List Gate) :
    ∀ (s n L : Nat) (ws : List Nat) (m : Nat) (w : Fin 6 → List Bool),
      gs.length ≤ s →
      notCnt gs ≤ n →
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
      SameLen w L →
      Covered ws m w →
      (∃ p q r : Nat,
        pack6 (fun t => (runWires gs w t).getD p false) = 2 ∧
        pack6 (fun t => (runWires gs w t).getD q false) = 8 ∧
        pack6 (fun t => (runWires gs w t).getD r false) = 42) →
      canReach s n ws m = true := by
  induction gs with
  | nil =>
    intro s n L ws m w _ _ _ _ hc ⟨p, q, r, hp, hq, hr⟩
    have h2 : hasBit m 2 = true := hp ▸ hc.2.2.2 p
    have h8 : hasBit m 8 = true := hq ▸ hc.2.2.2 q
    have h42 : hasBit m 42 = true := hr ▸ hc.2.2.2 r
    exact canReach_done h2 h8 h42
  | cons g rest ih =>
    intro s n L ws m w hs hn hfit hl hc hres
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by simp at hs; omega⟩
    have hs' : rest.length ≤ s' := by simp at hs; omega
    have hfit_g := hfit g List.mem_cons_self
    have hfit_r : ∀ g' ∈ rest, (g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hfit g' (List.mem_cons_of_mem _ hg')
    have hl' : SameLen (stepWires w g) (L + 1) := sameLen_step w L hl g
    let f : Fin 6 → Bool := fun t => g.op.eval (g.inputs.map fun i => (w t).getD i false)
    have hstep_eq : stepWires w g = (fun t => w t ++ [f t]) := rfl
    have hcov := covered_append hl hc (pack6 f) rfl
    rcases hfit_g.1 with hop | hop | hop
    · have hn' : notCnt rest ≤ n := by
        unfold notCnt notCount at hn ⊢
        simp [hop] at hn
        exact hn
      rcases hinputs : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
      · have hf : pack6 f = 63 := by
          have : f = fun _ => true := by funext t; simp [f, hop, hinputs, GateOp.eval]
          rw [this, pack6_true]
        have hold : hasBit m (pack6 f) = true := hf ▸ hc.2.2.1
        have hc' : Covered ws m (stepWires w g) := hstep_eq ▸ hcov.1 hold
        exact canReach_mono_step s' n ws m (ih s' n (L + 1) ws m (stepWires w g) hs' hn' hfit_r hl' hc' hres)
      · have hf : pack6 f = pack6 (fun t => (w t).getD i false) := by
          congr 1; funext t; simp [f, hop, hinputs, GateOp.eval]
        have hold : hasBit m (pack6 f) = true := hf ▸ hc.2.2.2 i
        have hc' : Covered ws m (stepWires w g) := hstep_eq ▸ hcov.1 hold
        exact canReach_mono_step s' n ws m (ih s' n (L + 1) ws m (stepWires w g) hs' hn' hfit_r hl' hc' hres)
      · let a := pack6 (fun t => (w t).getD i false)
        let b := pack6 (fun t => (w t).getD j false)
        have hf : pack6 f = Nat.land a b := by
          have heq : f = fun t => (w t).getD i false && (w t).getD j false := by
            funext t; simp [f, hop, hinputs, GateOp.eval]
          rw [heq]; exact pack6_and _ _
        cases hb : hasBit m (pack6 f)
        · have hc' : Covered (pack6 f :: ws) (setBit m (pack6 f)) (stepWires w g) := hstep_eq ▸ hcov.2 hb
          have hsub := ih s' n (L + 1) (pack6 f :: ws) (setBit m (pack6 f)) (stepWires w g) hs' hn' hfit_r hl' hc' hres
          rw [hf] at hb hsub
          exact canReach_of_and ((hc.1 a).mpr (hc.2.2.2 i)) ((hc.1 b).mpr (hc.2.2.2 j)) (hc.2.2.2 i) hb hsub
        · have hc' : Covered ws m (stepWires w g) := hstep_eq ▸ hcov.1 hb
          exact canReach_mono_step s' n ws m (ih s' n (L + 1) ws m (stepWires w g) hs' hn' hfit_r hl' hc' hres)
      · have hlen := hfit_g.2; rw [hinputs] at hlen; simp at hlen
    · have hn' : notCnt rest ≤ n := by
        unfold notCnt notCount at hn ⊢
        simp [hop] at hn
        exact hn
      rcases hinputs : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
      · have hf : pack6 f = 0 := by
          have : f = fun _ => false := by funext t; simp [f, hop, hinputs, GateOp.eval]
          rw [this, pack6_false]
        have hold : hasBit m (pack6 f) = true := hf ▸ hc.2.1
        have hc' : Covered ws m (stepWires w g) := hstep_eq ▸ hcov.1 hold
        exact canReach_mono_step s' n ws m (ih s' n (L + 1) ws m (stepWires w g) hs' hn' hfit_r hl' hc' hres)
      · have hf : pack6 f = pack6 (fun t => (w t).getD i false) := by
          congr 1; funext t; simp [f, hop, hinputs, GateOp.eval]
        have hold : hasBit m (pack6 f) = true := hf ▸ hc.2.2.2 i
        have hc' : Covered ws m (stepWires w g) := hstep_eq ▸ hcov.1 hold
        exact canReach_mono_step s' n ws m (ih s' n (L + 1) ws m (stepWires w g) hs' hn' hfit_r hl' hc' hres)
      · let a := pack6 (fun t => (w t).getD i false)
        let b := pack6 (fun t => (w t).getD j false)
        have hf : pack6 f = Nat.lor a b := by
          have heq : f = fun t => (w t).getD i false || (w t).getD j false := by
            funext t; simp [f, hop, hinputs, GateOp.eval]
          rw [heq]; exact pack6_or _ _
        cases hb : hasBit m (pack6 f)
        · have hc' : Covered (pack6 f :: ws) (setBit m (pack6 f)) (stepWires w g) := hstep_eq ▸ hcov.2 hb
          have hsub := ih s' n (L + 1) (pack6 f :: ws) (setBit m (pack6 f)) (stepWires w g) hs' hn' hfit_r hl' hc' hres
          rw [hf] at hb hsub
          exact canReach_of_or ((hc.1 a).mpr (hc.2.2.2 i)) ((hc.1 b).mpr (hc.2.2.2 j)) (hc.2.2.2 i) hb hsub
        · have hc' : Covered ws m (stepWires w g) := hstep_eq ▸ hcov.1 hb
          exact canReach_mono_step s' n ws m (ih s' n (L + 1) ws m (stepWires w g) hs' hn' hfit_r hl' hc' hres)
      · have hlen := hfit_g.2; rw [hinputs] at hlen; simp at hlen
    · have hnpos : notCnt rest + 1 ≤ n := by
        unfold notCnt notCount at hn ⊢
        simp [hop] at hn ⊢
        omega
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have hn' : notCnt rest ≤ n' := by omega
      rcases hinputs : g.inputs with _ | ⟨i, _⟩
      · have hf : pack6 f = 63 := by
          have : f = fun _ => true := by funext t; simp [f, hop, hinputs, GateOp.eval]
          rw [this, pack6_true]
        have hold : hasBit m (pack6 f) = true := hf ▸ hc.2.2.1
        have hc' : Covered ws m (stepWires w g) := hstep_eq ▸ hcov.1 hold
        exact canReach_mono (by omega) (by omega) (ih s' n' (L + 1) ws m (stepWires w g) hs' hn' hfit_r hl' hc' hres)
      · let a := pack6 (fun t => (w t).getD i false)
        have hf : pack6 f = Nat.xor a 63 := by
          have heq : f = fun t => !((w t).getD i false) := by
            funext t; simp [f, hop, hinputs, GateOp.eval]
          rw [heq]; exact pack6_not _
        cases hb : hasBit m (pack6 f)
        · have hc' : Covered (pack6 f :: ws) (setBit m (pack6 f)) (stepWires w g) := hstep_eq ▸ hcov.2 hb
          have hsub := ih s' n' (L + 1) (pack6 f :: ws) (setBit m (pack6 f)) (stepWires w g) hs' hn' hfit_r hl' hc' hres
          rw [hf] at hb hsub
          exact canReach_of_not ((hc.1 a).mpr (hc.2.2.2 i)) hb hsub
        · have hc' : Covered ws m (stepWires w g) := hstep_eq ▸ hcov.1 hb
          exact canReach_mono (by omega) (by omega) (ih s' n' (L + 1) ws m (stepWires w g) hs' hn' hfit_r hl' hc' hres)

def initWs : List Nat := [62, 60, 56, 48, 32, 0, 63]

def initMask : Nat := 0xD101000100000001

lemma init_sameLen : SameLen xs 7 := by
  intro t; simp [xs]

lemma init_covered : Covered initWs initMask xs := by
  refine ⟨fun v => ?_, by decide, by decide, fun k => ?_⟩
  · by_cases hv : v < 64
    · have hfin : (⟨v, hv⟩ : Fin 64).val ∈ initWs ↔ hasBit initMask (⟨v, hv⟩ : Fin 64).val = true := by
        revert hv
        have hall : ∀ u : Fin 64, (u.val ∈ initWs ↔ hasBit initMask u.val = true) := by decide
        intro hv
        exact hall ⟨v, hv⟩
      exact hfin
    · have h1 : v ∉ initWs := by
        intro hm
        simp [initWs] at hm
        omega
      have h2 : hasBit initMask v = false := by
        rw [hasBit_eq_testBit]
        apply Nat.testBit_lt_two_pow
        have hlt : initMask < 2 ^ 64 := by decide
        exact lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) (by omega))
      simp [h1, h2]
  · by_cases hk : k < 7
    · have hall : ∀ j : Fin 7, hasBit initMask (pack6 (fun t => (xs t).getD j.val false)) = true := by decide
      exact hall ⟨k, hk⟩
    · have heq : (fun t : Fin 6 => (xs t).getD k false) = fun _ => false := by
        funext t
        have hle : (xs t).length ≤ k := by simp [xs]; omega
        exact List.getD_eq_default _ _ hle
      rw [heq, pack6_false]
      decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma search_false : canReach 5 2 initWs initMask = false := by
  decide +kernel

end PEqualNP.Outside.L_meta_50372

theorem PEqualNP.Outside.L_meta_50372 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (2 : Nat).testBit t.val ∧
    w.getD q.val false = (8 : Nat).testBit t.val ∧
    w.getD r.val false = (42 : Nat).testBit t.val)) := by
  rintro ⟨D, p, q, r, hfan, _, hnot, hsz, hval⟩
  have hfit : ∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    exact ⟨by simpa using hop, hlen⟩
  have hrun : ∀ t : Fin 6, PEqualNP.Outside.L_meta_50372.runWires D.gates PEqualNP.Outside.L_meta_50372.xs t = D.wires (PEqualNP.Outside.L_meta_50372.xs t) :=
    fun t => PEqualNP.Outside.L_meta_50372.runWires_eq_foldl D.gates PEqualNP.Outside.L_meta_50372.xs t
  have hp : PEqualNP.Outside.L_meta_50372.pack6 (fun t => (PEqualNP.Outside.L_meta_50372.runWires D.gates PEqualNP.Outside.L_meta_50372.xs t).getD p.val false) = 2 := by
    apply PEqualNP.Outside.L_meta_50372.pack6_eq_of_testBit _ 2 (by omega)
    intro t; rw [hrun t]; exact (hval t).1
  have hq : PEqualNP.Outside.L_meta_50372.pack6 (fun t => (PEqualNP.Outside.L_meta_50372.runWires D.gates PEqualNP.Outside.L_meta_50372.xs t).getD q.val false) = 8 := by
    apply PEqualNP.Outside.L_meta_50372.pack6_eq_of_testBit _ 8 (by omega)
    intro t; rw [hrun t]; exact (hval t).2.1
  have hr : PEqualNP.Outside.L_meta_50372.pack6 (fun t => (PEqualNP.Outside.L_meta_50372.runWires D.gates PEqualNP.Outside.L_meta_50372.xs t).getD r.val false) = 42 := by
    apply PEqualNP.Outside.L_meta_50372.pack6_eq_of_testBit _ 42 (by omega)
    intro t; rw [hrun t]; exact (hval t).2.2
  have htrue := PEqualNP.Outside.L_meta_50372.runWires_sound D.gates 5 2 7
    PEqualNP.Outside.L_meta_50372.initWs PEqualNP.Outside.L_meta_50372.initMask PEqualNP.Outside.L_meta_50372.xs
    hsz hnot hfit PEqualNP.Outside.L_meta_50372.init_sameLen PEqualNP.Outside.L_meta_50372.init_covered
    ⟨p.val, q.val, r.val, hp, hq, hr⟩
  rw [PEqualNP.Outside.L_meta_50372.search_false] at htrue
  cases htrue
