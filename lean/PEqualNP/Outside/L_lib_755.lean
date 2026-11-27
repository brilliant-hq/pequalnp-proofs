import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_755_aux

open Fin.NatCast Fin.CommRing

def ones : List Bool → ℕ
  | [] => 0
  | x :: l => (if x = true then 1 else 0) + ones l

def c01 : List Bool → ℕ
  | x :: y :: l => (if x = false ∧ y = true then 1 else 0) + c01 (y :: l)
  | _ => 0

def c100 : List Bool → ℕ
  | x :: y :: z :: l => (if x = true ∧ y = false ∧ z = false then 1 else 0) + c100 (y :: z :: l)
  | _ => 0

def allL : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n+1 => (allL n).image (List.cons true) ∪ (allL n).image (List.cons false)

lemma mem_allL : ∀ n (l : List Bool), l ∈ allL n ↔ l.length = n
  | 0, l => by cases l <;> simp [allL]
  | n+1, l => by
    cases l with
    | nil => simp [allL]
    | cons x l => cases x <;> simp [allL, mem_allL n]

lemma sum_allL_succ (n : ℕ) (F : List Bool → ℕ) :
    ∑ l ∈ allL (n+1), F l = ∑ l ∈ allL n, (F (true :: l) + F (false :: l)) := by
  rw [allL, Finset.sum_union, Finset.sum_image, Finset.sum_image, Finset.sum_add_distrib]
  · intro x _ y _ h; simpa using h
  · intro x _ y _ h; simpa using h
  · rw [Finset.disjoint_left]
    intro l h1 h2
    simp only [Finset.mem_image] at h1 h2
    obtain ⟨x, _, rfl⟩ := h1
    obtain ⟨y, _, h⟩ := h2
    simp at h

def iA (a r t : ℕ) (l : List Bool) : ℕ :=
  if l.head? = some true ∧ l.getLast? = some false ∧ ones l = a ∧ c01 l = r ∧ c100 l = t then 1 else 0
def iB (a r t : ℕ) (l : List Bool) : ℕ :=
  if l.head? = some false ∧ l.tail.head? ≠ some false ∧ l.getLast? = some false ∧ ones l = a ∧
    c01 l = r ∧ c100 l = t then 1 else 0
def iC (a r t : ℕ) (l : List Bool) : ℕ :=
  if l.head? = some false ∧ l.tail.head? = some false ∧ l.getLast? = some false ∧ ones l = a ∧
    c01 l = r ∧ c100 l = t then 1 else 0
def iE (a r t : ℕ) (l : List Bool) : ℕ :=
  if l = [] ∧ a = 0 ∧ r = 0 ∧ t = 0 then 1 else 0

lemma tA_true (a r t : ℕ) (l : List Bool) : iA a r t (true :: l) =
    if a = 0 then 0 else iA (a-1) r t l + iB (a-1) r t l + (if t = 0 then 0 else iC (a-1) r (t-1) l) := by
  rcases l with _ | ⟨y, _ | ⟨z, l⟩⟩
  · simp [iA, iB, iC]
  · rcases a with _ | _ | a <;> cases y <;> simp [iA, iB, iC, ones, c01, c100]
  · cases y <;> cases z <;> simp [iA, iB, iC, ones, c01, c100] <;> split_ifs <;> simp_all <;> omega

lemma tA_false (a r t : ℕ) (l : List Bool) : iA a r t (false :: l) = 0 := by simp [iA]
lemma tB_true (a r t : ℕ) (l : List Bool) : iB a r t (true :: l) = 0 := by simp [iB]
lemma tC_true (a r t : ℕ) (l : List Bool) : iC a r t (true :: l) = 0 := by simp [iC]

lemma tB_false (a r t : ℕ) (l : List Bool) : iB a r t (false :: l) =
    iE a r t l + (if r = 0 then 0 else iA a (r-1) t l) := by
  rcases l with _ | ⟨y, _ | ⟨z, l⟩⟩
  · simp [iA, iB, iE, ones, c01, c100]; split_ifs <;> simp_all <;> omega
  · cases y <;> simp [iA, iB, iE, ones, c01, c100] <;> split_ifs <;> simp_all <;> omega
  · cases y <;> cases z <;> simp [iA, iB, iE, ones, c01, c100] <;> split_ifs <;> simp_all <;> omega

lemma tC_false (a r t : ℕ) (l : List Bool) : iC a r t (false :: l) = iB a r t l + iC a r t l := by
  rcases l with _ | ⟨y, _ | ⟨z, l⟩⟩
  · simp [iB, iC]
  · cases y <;> simp [iB, iC, ones, c01, c100] <;> split_ifs <;> simp_all <;> omega
  · cases y <;> cases z <;> simp [iB, iC, ones, c01, c100] <;> split_ifs <;> simp_all <;> omega

def cA (n a r t : ℕ) : ℕ := ∑ l ∈ allL n, iA a r t l
def cB (n a r t : ℕ) : ℕ := ∑ l ∈ allL n, iB a r t l
def cC (n a r t : ℕ) : ℕ := ∑ l ∈ allL n, iC a r t l

lemma sumE (n a r t : ℕ) : ∑ l ∈ allL n, iE a r t l = if n = 0 ∧ a = 0 ∧ r = 0 ∧ t = 0 then 1 else 0 := by
  cases n with
  | zero => rw [allL, Finset.sum_singleton]; simp [iE]
  | succ n =>
    rw [Finset.sum_eq_zero]
    · simp
    · intro l hl
      rw [mem_allL] at hl
      have : l ≠ [] := by rintro rfl; simp at hl
      simp [iE, this]

lemma cA_succ (n a r t : ℕ) : cA (n+1) a r t =
    if a = 0 then 0 else cA n (a-1) r t + cB n (a-1) r t + (if t = 0 then 0 else cC n (a-1) r (t-1)) := by
  simp only [cA, cB, cC, sum_allL_succ, tA_true, tA_false, add_zero]
  split_ifs <;> simp [Finset.sum_add_distrib]

lemma cB_succ (n a r t : ℕ) : cB (n+1) a r t =
    (if n = 0 ∧ a = 0 ∧ r = 0 ∧ t = 0 then 1 else 0) + (if r = 0 then 0 else cA n a (r-1) t) := by
  simp only [cA, cB, sum_allL_succ, tB_true, tB_false, zero_add, Finset.sum_add_distrib, sumE]
  split_ifs <;> simp

lemma cC_succ (n a r t : ℕ) : cC (n+1) a r t = cB n a r t + cC n a r t := by
  simp only [cB, cC, sum_allL_succ, tC_true, tC_false, zero_add, Finset.sum_add_distrib]

def Y (b r t : ℕ) : ℕ :=
  if t = 0 then (if b = r then 1 else 0) else if r + t ≤ b then r.choose t * (b-r-1).choose (t-1) else 0
def Z (b r t : ℕ) : ℕ := if r + t + 2 ≤ b then r.choose t * (b-r-2).choose t else 0
def Acl (n a r t : ℕ) : ℕ := if a = 0 then 0 else (a-1).choose r * Y (n-a) (r+1) t
def Bcl (n a r t : ℕ) : ℕ :=
  (if n = 1 ∧ a = 0 ∧ r = 0 ∧ t = 0 then 1 else 0) + (if r = 0 then 0 else Acl (n-1) a (r-1) t)
def Ccl (n a r t : ℕ) : ℕ :=
  (if 2 ≤ n ∧ a = 0 ∧ r = 0 ∧ t = 0 then 1 else 0) +
    (if r = 0 ∨ a = 0 then 0 else (a-1).choose (r-1) * Z (n-a) r t)

lemma Y_rec (b r t : ℕ) (hr : 1 ≤ r) :
    Y b (r+1) t = Y (b-1) r t + (if t = 0 then 0 else Z b r (t-1)) := by
  rcases t with _ | s
  · simp only [Y, if_true]; split_ifs <;> simp_all <;> omega
  · simp only [Y, Z, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    by_cases h : r + s + 2 ≤ b
    · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
      have e1 : b - (r+1) - 1 = b - r - 2 := by omega
      have e2 : b - 1 - r - 1 = b - r - 2 := by omega
      rw [e1, e2, Nat.choose_succ_succ', add_mul, add_comm]
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

lemma Z_rec (b r t : ℕ) (hr : 1 ≤ r) : Z (b+1) r t = Y (b-1) r t + Z b r t := by
  rcases t with _ | s
  · simp only [Z, Y, if_true, Nat.choose_zero_right, mul_one, add_zero]; split_ifs <;> simp_all <;> omega
  · simp only [Y, Z, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    by_cases h : r + s + 2 ≤ b
    · obtain ⟨c, rfl⟩ : ∃ c, b = r + 2 + c := ⟨b - r - 2, by omega⟩
      have e1 : r + 2 + c + 1 - r - 2 = c + 1 := by omega
      have e2 : r + 2 + c - 1 - r - 1 = c := by omega
      have e3 : r + 2 + c - r - 2 = c := by omega
      rw [if_pos (by omega), if_pos (by omega), e1, e2, e3, Nat.choose_succ_succ', mul_add]
      by_cases h2 : r + (s + 1) + 2 ≤ r + 2 + c
      · rw [if_pos h2]
      · rw [if_neg h2, Nat.choose_eq_zero_of_lt (by omega : c < s + 1)]; simp
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

lemma I1 (n a r t : ℕ) (ha : a ≠ 0) : Acl (n+1) a r t =
    Acl n (a-1) r t + Bcl n (a-1) r t + (if t = 0 then 0 else Ccl n (a-1) r (t-1)) := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  simp only [Acl, Bcl, Ccl, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
  have eb : n + 1 - (a' + 1) = n - a' := by omega
  rw [eb]
  rcases a' with _ | a''
  · simp only [if_true, zero_add, Nat.sub_zero]
    rcases r with _ | r
    · rcases t with _ | t
      · simp [Y]
      · rcases t with _ | t
        · simp [Y]
        · simp [Y, Nat.choose_eq_zero_of_lt]
    · simp [Nat.choose_eq_zero_of_lt]
  · simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, and_false, false_and, or_false]
    rcases r with _ | r
    · simp
    · simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, zero_add]
      have e : n - 1 - (a'' + 1) = n - (a'' + 1) - 1 := by omega
      rw [e, Y_rec _ _ _ (by omega), Nat.choose_succ_succ']
      split_ifs <;> ring

lemma I3 (n a r t : ℕ) : Ccl (n+1) a r t = Bcl n a r t + Ccl n a r t := by
  rcases r with _ | r
  · simp only [Ccl, Bcl, true_or, if_true, add_zero]; split_ifs <;> simp_all <;> omega
  · simp only [Ccl, Bcl, Acl, Nat.succ_ne_zero, false_or, and_false, false_and, if_false, zero_add,
      Nat.add_sub_cancel]
    split_ifs with ha
    · rfl
    · by_cases h : a ≤ n
      · have e1 : n + 1 - a = (n - a) + 1 := by omega
        have e2 : n - 1 - a = (n - a) - 1 := by omega
        rw [e1, e2, Z_rec _ _ _ (by omega), mul_add]
      · have e1 : n + 1 - a = 0 := by omega
        have e2 : n - 1 - a = 0 := by omega
        have e3 : n - a = 0 := by omega
        rw [e1, e2, e3]; simp [Y, Z]

lemma counts_eq : ∀ n a r t, cA n a r t = Acl n a r t ∧ cB n a r t = Bcl n a r t ∧ cC n a r t = Ccl n a r t
  | 0, a, r, t => by
    refine ⟨?_, ?_, ?_⟩
    · simp only [cA, allL, Finset.sum_singleton, iA, Acl, Y]
      simp
    · simp only [cB, allL, Finset.sum_singleton, iB, Bcl, Acl, Y]
      simp
    · simp [cC, allL, iC, Ccl, Z]
  | n+1, a, r, t => by
    have ih := counts_eq n
    refine ⟨?_, ?_, ?_⟩
    · rw [cA_succ]
      split_ifs with ha ht
      · simp [Acl, ha]
      · rw [I1 _ _ _ _ ha, if_pos ht, (ih _ _ _).1, (ih _ _ _).2.1]
      · rw [I1 _ _ _ _ ha, if_neg ht, (ih _ _ _).1, (ih _ _ _).2.1, (ih _ _ _).2.2]
    · rw [cB_succ, Bcl]
      congr 1
      · simp
      · split_ifs
        · rfl
        · rw [(ih _ _ _).1]; simp
    · rw [cC_succ, I3, (ih _ _ _).2.1, (ih _ _ _).2.2]

section cyc
variable {k : ℕ} [NeZero k]

lemma z2 (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have : ∀ y : Fin 2, y = 0 ∨ y = 1 := by decide
  exact this x

lemma card_shift (p : Fin k → Prop) [DecidablePred p] (s : Fin k) :
    (Finset.univ.filter (fun i => p (i + s))).card = (Finset.univ.filter p).card := by
  apply Finset.card_nbij' (fun i => i + s) (fun i => i - s)
  · intro i hi; simpa using hi
  · intro i hi; simpa using hi
  · intro i _; simp
  · intro i _; simp

def wt (m : Fin k → ZMod 2) : ℕ := (Finset.univ.filter fun i => m i = 1).card
def G (m : Fin k → ZMod 2) : ℕ := (Finset.univ.filter fun i => m i = 0 ∧ m (i+1) = 1).card
def T (m : Fin k → ZMod 2) : ℕ :=
  (Finset.univ.filter fun i => m i = 1 ∧ m (i+1) = 0 ∧ m (i+1+1) = 0).card
def fib (m : Fin k → ZMod 2) : Finset (Fin k → ZMod 2) :=
  Finset.univ.filter (fun u => ∀ i, m i * u (i+1) = u i * m (i+1))

def Sset (m : Fin k → ZMod 2) : Finset (Fin k) :=
  Finset.univ.filter (fun j => m j = 0 ∧ ¬(m (j-1) = 1 ∧ m (j+1) = 0))

lemma card_Sset (m : Fin k → ZMod 2) :
    (Sset m).card = (Finset.univ.filter fun j => m j = 0).card - T m := by
  have hsub : Finset.univ.filter (fun j => m (j-1) = 1 ∧ m j = 0 ∧ m (j+1) = 0) ⊆
      Finset.univ.filter (fun j => m j = 0) := by
    intro j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto
  have hT : (Finset.univ.filter (fun j => m (j-1) = 1 ∧ m j = 0 ∧ m (j+1) = 0)).card = T m := by
    rw [← card_shift _ 1, T]; congr 1; ext i; simp
  rw [← hT, ← Finset.card_sdiff_of_subset hsub, Sset]
  congr 1; ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
  tauto

lemma walk_exists (m : Fin k → ZMod 2) (z : Fin k) (hz : m z = 0) (i : Fin k) :
    ∃ n : ℕ, m (i - (n : Fin k)) = 0 := ⟨(i - z).val, by simp [hz]⟩

lemma fib_card (m : Fin k → ZMod 2) (z : Fin k) (hz : m z = 0) :
    (fib m).card = 2 ^ (Sset m).card := by
  classical
  have key : (2:ℕ) ^ (Sset m).card = (Finset.univ : Finset (↥(Sset m) → ZMod 2)).card := by
    rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_coe]
  rw [key]
  have F1 : ∀ u ∈ fib m, ∀ i, m i = 1 → m (i+1) = 1 → u (i+1) = u i := by
    intro u hu i h1 h2
    have := (Finset.mem_filter.1 hu).2 i; rw [h1, h2] at this; simpa using this
  have F2 : ∀ u ∈ fib m, ∀ i, m i = 1 → m (i+1) = 0 → u (i+1) = 0 := by
    intro u hu i h1 h2
    have := (Finset.mem_filter.1 hu).2 i; rw [h1, h2] at this; simpa using this
  have F3 : ∀ u ∈ fib m, ∀ i, m i = 0 → m (i+1) = 1 → u i = 0 := by
    intro u hu i h1 h2
    have := (Finset.mem_filter.1 hu).2 i; rw [h1, h2] at this; simpa using this.symm
  refine Finset.card_bij (fun u _ => fun j => if m (j.1+1) = 1 then u (j.1+1) else u j.1)
    (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro u hu v hv huv
    have hρ : ∀ j (hj : j ∈ Sset m), (if m (j+1) = 1 then u (j+1) else u j) =
        (if m (j+1) = 1 then v (j+1) else v j) := fun j hj => congr_fun huv ⟨j, hj⟩
    have hzero : ∀ i, m i = 0 → u i = v i := by
      intro i hi
      rcases z2 (m (i+1)) with h1 | h1
      · rcases z2 (m (i-1)) with h2 | h2
        · have hS : i ∈ Sset m := by simp [Sset, hi, h2]
          have := hρ i hS; simpa [h1] using this
        · have e1 := F2 u hu (i-1) h2 (by simpa using hi)
          have e2 := F2 v hv (i-1) h2 (by simpa using hi)
          simp at e1 e2; rw [e1, e2]
      · rw [F3 u hu i hi h1, F3 v hv i hi h1]
    have hwalk : ∀ n : ℕ, ∀ i, m i = 1 → m (i - (n : Fin k)) = 0 → u i = v i := by
      intro n
      induction n with
      | zero => intro i h1 h0; simp [h1] at h0
      | succ n ih =>
        intro i h1 h0
        rcases z2 (m (i-1)) with h2 | h2
        · have hS : i - 1 ∈ Sset m := by simp [Sset, h2, h1]
          have := hρ (i-1) hS; simpa [h1] using this
        · have e1 := F1 u hu (i-1) h2 (by simpa using h1)
          have e2 := F1 v hv (i-1) h2 (by simpa using h1)
          simp at e1 e2
          rw [e1, e2]
          apply ih (i-1) h2
          rw [← h0]; congr 1; push_cast; ring
    funext i
    rcases z2 (m i) with h | h
    · exact hzero i h
    · obtain ⟨n, hn⟩ := walk_exists m z hz i
      exact hwalk n i h hn
  · intro g _
    let g' : Fin k → ZMod 2 := fun j => if h : j ∈ Sset m then g ⟨j, h⟩ else 0
    have hex := walk_exists m z hz
    let nf : Fin k → ℕ := fun i => Nat.find (hex i)
    have nf_succ : ∀ i, m (i+1) = 1 → nf (i+1) = nf i + 1 := by
      intro i h1
      show Nat.find (hex (i+1)) = Nat.find (hex i) + 1
      rw [Nat.find_eq_iff]
      constructor
      · have := Nat.find_spec (hex i)
        convert this using 2; push_cast; ring
      · intro j hj
        rcases j with _ | j
        · simp [h1]
        · have := Nat.find_min (hex i) (show j < Nat.find (hex i) by omega)
          intro h'; apply this; convert h' using 2; push_cast; ring
    let u : Fin k → ZMod 2 := fun i =>
      if m i = 1 then g' (i - (nf i : Fin k)) else if m (i-1) = 0 ∧ m (i+1) = 0 then g' i else 0
    refine ⟨u, ?_, ?_⟩
    · simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and]
      intro i
      rcases z2 (m i) with h1 | h1 <;> rcases z2 (m (i+1)) with h2 | h2
      · simp [h1, h2]
      · simp [u, h1, h2]
      · simp [u, h1, h2]
      · rw [h1, h2, one_mul, mul_one]
        simp only [u, h1, h2, if_true]
        rw [nf_succ i h2]; congr 1; push_cast; ring
    · funext ⟨j, hj⟩
      have hj' := hj
      simp only [Sset, Finset.mem_filter, Finset.mem_univ, true_and] at hj'
      rcases z2 (m (j+1)) with h1 | h1
      · have h2 : m (j-1) = 0 := by
          rcases z2 (m (j-1)) with h | h
          · exact h
          · exact absurd ⟨h, h1⟩ hj'.2
        simp [u, h1, h2, hj'.1, g', hj]
      · have hn : nf (j+1) = 1 := by
          show Nat.find (hex (j+1)) = 1
          rw [Nat.find_eq_iff]
          refine ⟨by simpa using hj'.1, ?_⟩
          intro n hn; interval_cases n; simp [h1]
        simp [u, h1, hn, g', hj]

end cyc

lemma ones_eq : ∀ l : List Bool, ones l = ∑ i ∈ Finset.range l.length, if l[i]? = some true then 1 else 0
  | [] => by simp [ones]
  | x :: l => by
    rw [ones, ones_eq l, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

lemma c01_eq : ∀ l : List Bool, c01 l =
    ∑ i ∈ Finset.range l.length, if l[i]? = some false ∧ l[i+1]? = some true then 1 else 0
  | [] => by simp [c01]
  | [x] => by simp [c01]
  | x :: y :: l => by
    rw [c01, c01_eq (y :: l), List.length_cons (a := x), Finset.sum_range_succ', add_comm]
    congr 1
    simp

lemma c100_eq : ∀ l : List Bool, c100 l =
    ∑ i ∈ Finset.range l.length,
      if l[i]? = some true ∧ l[i+1]? = some false ∧ l[i+2]? = some false then 1 else 0
  | [] => by simp [c100]
  | [x] => by simp [c100]
  | [x, y] => by simp [c100, Finset.sum_range_succ]
  | x :: y :: z :: l => by
    rw [c100, c100_eq (y :: z :: l), List.length_cons (a := x), Finset.sum_range_succ', add_comm]
    congr 1
    simp

section cyc3
variable {k : ℕ} [NeZero k]

lemma dz (x : ZMod 2) : (decide (x = 1) = false ↔ x = 0) := by
  rcases z2 x with h | h <;> simp [h]
lemma nz (x : ZMod 2) : (¬ x = 1 ↔ x = 0) := by
  rcases z2 x with h | h <;> simp [h]
lemma dz' (x : ZMod 2) : (decide (x = 1) = true ↔ x = 1) := by simp

lemma val_succ_of_ne (j : Fin k) (hj : j ≠ -1) : (j+1).val = j.val + 1 := by
  have hv : (j+1).val = (j.val + 1) % k := by
    rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  rcases Nat.lt_or_ge (j.val + 1) k with h | h
  · rw [hv, Nat.mod_eq_of_lt h]
  · exfalso; apply hj
    have hk : j.val + 1 = k := by have := j.isLt; omega
    have : j + 1 = 0 := by ext; rw [hv, hk, Nat.mod_self]; simp
    exact eq_neg_of_add_eq_zero_left this

lemma val_neg_one (hk : 2 ≤ k) : ((-1 : Fin k).val) + 1 = k := by
  have hv : ((-1 : Fin k)+1).val = ((-1 : Fin k).val + 1) % k := by
    rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  rw [neg_add_cancel, Fin.val_zero] at hv
  have := (-1 : Fin k).isLt
  rcases Nat.lt_or_ge ((-1 : Fin k).val + 1) k with h | h
  · rw [Nat.mod_eq_of_lt h] at hv; omega
  · omega

def Lw (m : Fin k → ZMod 2) : List Bool := List.ofFn (fun i => decide (m i = 1))

lemma Lw_get (m : Fin k → ZMod 2) (j : Fin k) : (Lw m)[j.val]? = some (decide (m j = 1)) := by
  simp [Lw, List.getElem?_ofFn, j.isLt]

lemma Lw_none (m : Fin k → ZMod 2) (j : ℕ) (hj : k ≤ j) : (Lw m)[j]? = none := by
  simp [Lw, List.getElem?_ofFn]; omega

lemma Lw_len (m : Fin k → ZMod 2) : (Lw m).length = k := by simp [Lw]

lemma Lw_head (m : Fin k → ZMod 2) : (Lw m).head? = some (decide (m 0 = 1)) := by
  rw [List.head?_eq_getElem?, ← Fin.val_zero k, Lw_get]

lemma Lw_last (hk : 2 ≤ k) (m : Fin k → ZMod 2) :
    (Lw m).getLast? = some (decide (m (-1) = 1)) := by
  rw [List.getLast?_eq_getElem?, Lw_len, ← Lw_get]; congr 1; have := val_neg_one (k := k) hk; omega

lemma Lw_ones (m : Fin k → ZMod 2) : ones (Lw m) = wt m := by
  rw [ones_eq, Lw_len, ← Fin.sum_univ_eq_sum_range (fun i => if (Lw m)[i]? = some true then 1 else 0),
    wt, Finset.card_filter]
  apply Finset.sum_congr rfl; intro i _; simp [Lw_get]

lemma Lw_c01 (hk : 2 ≤ k) (m : Fin k → ZMod 2) (h0 : m 0 = 1) (h1 : m (-1) = 0) :
    c01 (Lw m) + 1 = G m := by
  rw [c01_eq, Lw_len, ← Fin.sum_univ_eq_sum_range
    (fun i => if (Lw m)[i]? = some false ∧ (Lw m)[i+1]? = some true then 1 else 0), G, Finset.card_filter]
  have key : ∀ i : Fin k, (if m i = 0 ∧ m (i+1) = 1 then 1 else 0) =
      (if (Lw m)[i.val]? = some false ∧ (Lw m)[i.val+1]? = some true then 1 else 0) +
        (if i = -1 then 1 else 0) := by
    intro i
    by_cases hi : i = -1
    · subst hi
      have e : (-1 : Fin k).val + 1 = k := val_neg_one hk
      rw [Lw_none m ((-1 : Fin k).val + 1) (by omega), neg_add_cancel, h0, h1]; simp
    · rw [← val_succ_of_ne i hi, Lw_get, Lw_get]; simp [hi, dz, nz]
  symm
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

lemma Lw_c100 (hk : 2 ≤ k) (m : Fin k → ZMod 2) (h0 : m 0 = 1) (h1 : m (-1) = 0) :
    c100 (Lw m) = T m := by
  rw [c100_eq, Lw_len, ← Fin.sum_univ_eq_sum_range
    (fun i => if (Lw m)[i]? = some true ∧ (Lw m)[i+1]? = some false ∧ (Lw m)[i+2]? = some false
      then 1 else 0), T, Finset.card_filter]
  apply Finset.sum_congr rfl; intro i _
  by_cases hi : i = -1
  · subst hi; rw [Lw_get, h1]; simp
  · by_cases hi2 : i + 1 = -1
    · have e1 := val_succ_of_ne i hi
      have e : (-1 : Fin k).val + 1 = k := val_neg_one hk
      rw [hi2] at e1
      rw [Lw_none m (i.val + 2) (by omega), hi2, neg_add_cancel, h0]; simp
    · have e1 := val_succ_of_ne i hi
      have e2 := val_succ_of_ne (i+1) hi2
      rw [show i.val + 2 = (i+1+1).val by omega, ← e1, Lw_get, Lw_get, Lw_get]
      simp [dz, nz]

def rot (s : Fin k) (m : Fin k → ZMod 2) : Fin k → ZMod 2 := fun i => m (i + s)

lemma wt_rot (s : Fin k) (m : Fin k → ZMod 2) : wt (rot s m) = wt m :=
  card_shift (fun i => m i = 1) s

lemma G_rot (s : Fin k) (m : Fin k → ZMod 2) : G (rot s m) = G m := by
  unfold G rot
  rw [← card_shift (fun i => m i = 0 ∧ m (i+1) = 1) s]
  congr 1; ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [show i + 1 + s = i + s + 1 by ring]

lemma T_rot (s : Fin k) (m : Fin k → ZMod 2) : T (rot s m) = T m := by
  unfold T rot
  rw [← card_shift (fun i => m i = 1 ∧ m (i+1) = 0 ∧ m (i+1+1) = 0) s]
  congr 1; ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [show i + 1 + s = i + s + 1 by ring, show i + 1 + 1 + s = i + s + 1 + 1 by ring]

def N0 (a r t : ℕ) : Finset (Fin k → ZMod 2) :=
  Finset.univ.filter fun m => m 0 = 1 ∧ m (-1) = 0 ∧ wt m = a ∧ G m = r ∧ T m = t

def cnt (a r t : ℕ) : Finset (Fin k → ZMod 2) :=
  Finset.univ.filter fun m => wt m = a ∧ G m = r ∧ T m = t

lemma rot_count (a r t : ℕ) : r * (cnt (k := k) a r t).card = k * (N0 (k := k) a r t).card := by
  classical
  let P := (Finset.univ : Finset ((Fin k → ZMod 2) × Fin k)).filter
    (fun p => (wt p.1 = a ∧ G p.1 = r ∧ T p.1 = t) ∧ p.1 p.2 = 0 ∧ p.1 (p.2+1) = 1)
  have h1 : P.card = r * (cnt (k := k) a r t).card := by
    rw [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
    have : ∀ m : Fin k → ZMod 2, (∑ i : Fin k,
        if (wt m = a ∧ G m = r ∧ T m = t) ∧ m i = 0 ∧ m (i+1) = 1 then 1 else 0) =
        if (wt m = a ∧ G m = r ∧ T m = t) then r else 0 := by
      intro m
      split_ifs with h
      · rw [← h.2.1, G, Finset.card_filter]; simp [h]
      · simp [h]
    simp_rw [this]
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm, cnt]
  have h2 : P.card = (N0 (k := k) a r t ×ˢ (Finset.univ : Finset (Fin k))).card := by
    apply Finset.card_nbij' (fun p => (rot (p.2+1) p.1, p.2)) (fun q => (rot (-(q.2+1)) q.1, q.2))
    · intro p hp
      simp only [P, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp
      simp only [N0, Finset.coe_product, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_prod,
        Set.mem_setOf_eq, Finset.coe_univ, Set.mem_univ, and_true, wt_rot, G_rot, T_rot]
      refine ⟨?_, ?_, hp.1⟩
      · simp [rot, hp.2.2]
      · simp only [rot]; rw [show (-1 : Fin k) + (p.2 + 1) = p.2 by ring]; exact hp.2.1
    · intro q hq
      simp only [N0, Finset.coe_product, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_prod,
        Set.mem_setOf_eq, Finset.coe_univ, Set.mem_univ, and_true] at hq
      simp only [P, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, wt_rot, G_rot,
        T_rot]
      refine ⟨hq.2.2, ?_, ?_⟩
      · simp only [rot]; rw [show q.2 + -(q.2 + 1) = -1 by ring]; exact hq.2.1
      · simp only [rot]; rw [show q.2 + 1 + -(q.2 + 1) = 0 by ring]; exact hq.1
    · intro p _; refine Prod.ext ?_ rfl; funext i; simp only [rot]; congr 1; ring
    · intro q _; refine Prod.ext ?_ rfl; funext i; simp only [rot]; congr 1; ring
  rw [← h1, h2, Finset.card_product, Finset.card_univ, Fintype.card_fin, mul_comm]

lemma bridge (hk : 2 ≤ k) (a r t : ℕ) :
    (N0 (k := k) a (r+1) t).card = cA k a r t := by
  classical
  rw [cA]
  have : ∀ l, iA a r t l = if (l.head? = some true ∧ l.getLast? = some false ∧ ones l = a ∧
      c01 l = r ∧ c100 l = t) then 1 else 0 := fun l => rfl
  simp_rw [this]
  rw [← Finset.card_filter]
  apply Finset.card_bij (fun m _ => Lw m)
  · intro m hm
    simp only [N0, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    obtain ⟨h0, h1, hw, hg, ht⟩ := hm
    rw [Finset.mem_filter, mem_allL]
    refine ⟨Lw_len m, by rw [Lw_head, h0]; simp, by rw [Lw_last hk, h1]; simp, by rw [Lw_ones, hw],
      by have := Lw_c01 hk m h0 h1; omega, by rw [Lw_c100 hk m h0 h1, ht]⟩
  · intro m _ m' _ h
    funext i
    have := congrArg (fun l : List Bool => l[i.val]?) h
    simp only [Lw_get, Option.some.injEq] at this
    rcases z2 (m i) with h1 | h1 <;> rcases z2 (m' i) with h2 | h2 <;> simp_all
  · intro l hl
    simp only [Finset.mem_filter, mem_allL] at hl
    obtain ⟨hlen, hh, hl', ho, hc, ht⟩ := hl
    let m : Fin k → ZMod 2 := fun i => if l.getD i.val false = true then 1 else 0
    have hLm : Lw m = l := by
      apply List.ext_getElem
      · rw [Lw_len, hlen]
      · intro n h1 h2
        simp only [Lw, List.getElem_ofFn, m]
        rcases Bool.eq_false_or_eq_true (l[n]) with h | h <;> simp [h, List.getElem?_eq_getElem h2]
    have h0 : m 0 = 1 := by
      have := Lw_head m; rw [hLm, hh] at this
      simp only [Option.some.injEq] at this
      exact (dz' _).1 this.symm
    have h1 : m (-1) = 0 := by
      have := Lw_last hk m; rw [hLm, hl'] at this
      simp only [Option.some.injEq] at this
      exact (dz _).1 this.symm
    refine ⟨m, ?_, hLm⟩
    simp only [N0, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨h0, h1, ?_, ?_, ?_⟩
    · rw [← Lw_ones, hLm, ho]
    · rw [← Lw_c01 hk m h0 h1, hLm, hc]
    · rw [← Lw_c100 hk m h0 h1, hLm, ht]

end cyc3

section mainsec
variable {k : ℕ} [NeZero k]

lemma pow2_inj {x y : ℕ} : (2:ℕ)^x = 2^y ↔ x = y :=
  ⟨fun h => Nat.pow_right_injective (le_refl 2) h, fun h => h ▸ rfl⟩

lemma G_pos (m : Fin k → ZMod 2) (z o : Fin k) (hz : m z = 0) (ho : m o = 1) : 1 ≤ G m := by
  by_contra h
  have h0 : G m = 0 := by omega
  rw [G, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
  have step : ∀ i, m i = 0 → m (i+1) = 0 := by
    intro i hi
    rcases z2 (m (i+1)) with h' | h'
    · exact h'
    · exact absurd ⟨hi, h'⟩ (h0 (Finset.mem_univ _))
  have hall : ∀ n : ℕ, m (z + (n : Fin k)) = 0 := by
    intro n; induction n with
    | zero => simpa using hz
    | succ n ih => rw [Nat.cast_succ, ← add_assoc]; exact step _ ih
  have := hall (o - z).val
  simp [ho] at this

lemma zeros_card (m : Fin k → ZMod 2) :
    (Finset.univ.filter fun j => m j = 0).card = k - wt m := by
  have := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun j => m j = 1)
  rw [Finset.card_univ, Fintype.card_fin] at this
  have e : (Finset.univ.filter fun j => ¬ m j = 1) = Finset.univ.filter fun j => m j = 0 := by
    ext j; simp [nz]
  rw [e] at this; unfold wt; omega

lemma Ycl_zero (b r t : ℕ) (hr : 1 ≤ r) (h : b < r ∨ r < t) : Y b r t = 0 := by
  unfold Y
  split_ifs with h1 h2 h3 <;> try rfl
  · omega
  · rw [Nat.choose_eq_zero_of_lt (by omega : r < t)]; simp

theorem mid (hk2 : 2 ≤ k) (a f : ℕ) (ha0 : 0 < a) (hak : a < k) :
    (Finset.univ.filter fun m : Fin k → ZMod 2 => wt m = a ∧ (fib m).card = 2^f).card =
      ∑ r ∈ Finset.Icc 1 (min a (k-a)), ∑ t ∈ Finset.Icc 0 r,
        if r+t ≤ k-a ∧ f = k-a-t then
          (k * Nat.choose (a-1) (r-1) * Nat.choose r t * (if t = 0 then (if r = k-a then 1 else 0)
            else Nat.choose (k-a-r-1) (t-1))) / r
        else 0 := by
  classical
  set b := k - a with hb

  have hS : (Finset.univ.filter fun m : Fin k → ZMod 2 => wt m = a ∧ (fib m).card = 2^f) =
      Finset.univ.filter fun m : Fin k → ZMod 2 => wt m = a ∧ b - T m = f := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    all_goals rintro ⟨hw, h⟩
    all_goals refine ⟨hw, ?_⟩
    all_goals
      have hz : ∃ z, m z = 0 := by
        by_contra hc
        push_neg at hc
        have : wt m = (Finset.univ : Finset (Fin k)).card := by
          rw [wt, Finset.card_filter_eq_iff]; intro x _
          rcases z2 (m x) with h' | h'
          · exact absurd h' (hc x)
          · exact h'
        rw [Finset.card_univ, Fintype.card_fin] at this; omega
      obtain ⟨z, hz⟩ := hz
      have hf := fib_card m z hz
      rw [card_Sset, zeros_card, hw] at hf
    · rw [hf] at h; exact pow2_inj.1 h
    · rw [hf, h]
  rw [hS]

  have hGle : ∀ m : Fin k → ZMod 2, G m ≤ k := fun m => by
    have := Finset.card_filter_le (Finset.univ : Finset (Fin k)) (fun i => m i = 0 ∧ m (i+1) = 1)
    rw [Finset.card_univ, Fintype.card_fin] at this; exact this
  have hTle : ∀ m : Fin k → ZMod 2, T m ≤ k := fun m => by
    have := Finset.card_filter_le (Finset.univ : Finset (Fin k))
      (fun i => m i = 1 ∧ m (i+1) = 0 ∧ m (i+1+1) = 0)
    rw [Finset.card_univ, Fintype.card_fin] at this; exact this
  rw [Finset.card_eq_sum_card_fiberwise (f := G) (t := Finset.range (k+1))
    (fun m _ => by simp only [Finset.coe_range, Set.mem_Iio]; have := hGle m; omega)]
  have inner : ∀ r, (Finset.filter (fun m => G m = r)
      (Finset.univ.filter fun m : Fin k → ZMod 2 => wt m = a ∧ b - T m = f)).card =
      ∑ t ∈ Finset.range (k+1), if f = b - t then (cnt (k := k) a r t).card else 0 := by
    intro r
    rw [Finset.card_eq_sum_card_fiberwise (f := T) (t := Finset.range (k+1))
      (fun m _ => by simp only [Finset.coe_range, Set.mem_Iio]; have := hTle m; omega)]
    apply Finset.sum_congr rfl; intro t _
    split_ifs with hf
    · congr 1; ext m; simp only [cnt, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨⟨h1, _⟩, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨⟨h1, by omega⟩, h2⟩, h3⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro m hm hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      omega
  simp_rw [inner]

  have hcnt : ∀ r t, 1 ≤ r → (cnt (k := k) a r t).card = k * ((a-1).choose (r-1) * Y b r t) / r := by
    intro r t hr
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have h1 := rot_count (k := k) a (r'+1) t
    rw [bridge hk2, (counts_eq _ _ _ _).1, Acl, if_neg (by omega)] at h1
    simp only [Nat.add_sub_cancel]
    symm; apply Nat.div_eq_of_eq_mul_left (by omega); rw [← h1]; ring
  have hcnt0 : ∀ t, (cnt (k := k) a 0 t).card = 0 := by
    intro t
    rw [Finset.card_eq_zero, cnt, Finset.filter_eq_empty_iff]
    rintro m - ⟨hw, hg, -⟩
    obtain ⟨o, ho⟩ : ∃ o, m o = 1 := by
      have : 0 < wt m := by omega
      obtain ⟨o, ho⟩ := Finset.card_pos.1 this
      exact ⟨o, (Finset.mem_filter.1 ho).2⟩
    obtain ⟨z, hz⟩ : ∃ z, m z = 0 := by
      by_contra hc
      push_neg at hc
      have : wt m = (Finset.univ : Finset (Fin k)).card := by
        rw [wt, Finset.card_filter_eq_iff]; intro x _
        rcases z2 (m x) with h' | h'
        · exact absurd h' (hc x)
        · exact h'
      rw [Finset.card_univ, Fintype.card_fin] at this; omega
    have := G_pos m z o hz ho; omega
  let Φ : ℕ → ℕ → ℕ := fun r t => if f = b - t then k * ((a-1).choose (r-1) * Y b r t) / r else 0
  have hPhi0 : ∀ r t, 1 ≤ r → (a < r ∨ b < r ∨ r < t) → Φ r t = 0 := by
    intro r t hr h
    simp only [Φ]
    split_ifs
    · rcases h with h | h
      · rw [Nat.choose_eq_zero_of_lt (by omega : a - 1 < r - 1)]; simp
      · rw [Ycl_zero b r t hr h]; simp
    · rfl

  have hterm : ∀ r t, 1 ≤ r → (if r+t ≤ b ∧ f = b-t then
          (k * Nat.choose (a-1) (r-1) * Nat.choose r t * (if t = 0 then (if r = b then 1 else 0)
            else Nat.choose (b-r-1) (t-1))) / r
        else 0) = Φ r t := by
    intro r t hr
    simp only [Φ]
    by_cases hf : f = b - t
    · by_cases h : r + t ≤ b
      · rw [if_pos ⟨h, hf⟩, if_pos hf]
        congr 1
        unfold Y
        rcases Nat.eq_zero_or_pos t with rfl | ht
        · simp only [if_true, Nat.choose_zero_right, mul_one]
          by_cases hrb : r = b
          · rw [if_pos hrb, if_pos hrb.symm]; ring
          · rw [if_neg hrb, if_neg (Ne.symm hrb)]; ring
        · rw [if_neg (by omega), if_neg (by omega), if_pos h]; ring
      · have hY : Y b r t = 0 := by unfold Y; split_ifs <;> first | rfl | omega
        rw [if_neg (fun h' => h h'.1), if_pos hf, hY]
        simp
    · rw [if_neg (fun h' => hf h'.2), if_neg hf]
  rw [Finset.sum_congr rfl (fun r hr => Finset.sum_congr rfl
    (fun t _ => hterm r t (Finset.mem_Icc.1 hr).1))]
  have e1 : ∀ r ∈ Finset.Icc 1 (min a b), ∑ t ∈ Finset.Icc 0 r, Φ r t =
      ∑ t ∈ Finset.range (k+1), Φ r t := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    apply Finset.sum_subset
    · intro t ht; simp only [Finset.mem_Icc, Finset.mem_range] at ht ⊢; omega
    · intro t _ ht
      simp only [Finset.mem_Icc, not_and, not_le] at ht
      exact hPhi0 r t hr.1 (Or.inr (Or.inr (ht (Nat.zero_le _))))
  rw [Finset.sum_congr rfl e1]
  calc ∑ r ∈ Finset.range (k+1), ∑ t ∈ Finset.range (k+1), (if f = b - t then (cnt (k := k) a r t).card else 0)
      = ∑ r ∈ Finset.range (k+1), (if r = 0 then 0 else ∑ t ∈ Finset.range (k+1), Φ r t) := by
        apply Finset.sum_congr rfl; intro r _
        split_ifs with hr0
        · subst hr0; simp [hcnt0]
        · apply Finset.sum_congr rfl; intro t _
          simp only [Φ]; rw [hcnt r t (by omega)]
    _ = ∑ r ∈ Finset.Icc 1 (min a b), (if r = 0 then 0 else ∑ t ∈ Finset.range (k+1), Φ r t) := by
        symm; apply Finset.sum_subset
        · intro r hr; simp only [Finset.mem_Icc, Finset.mem_range] at hr ⊢; omega
        · intro r _ hr
          split_ifs with hr0
          · rfl
          · apply Finset.sum_eq_zero; intro t _
            simp only [Finset.mem_Icc, not_and, not_le] at hr
            apply hPhi0 r t (by omega)
            have := hr (by omega); omega
    _ = _ := by
        apply Finset.sum_congr rfl; intro r hr
        rw [if_neg (by simp only [Finset.mem_Icc] at hr; omega)]

end mainsec

section fin
variable {k : ℕ} [NeZero k]

lemma wt_zero_iff (m : Fin k → ZMod 2) : wt m = 0 ↔ m = 0 := by
  rw [wt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h; funext i; exact (nz _).1 (h (Finset.mem_univ i))
  · rintro rfl i _; simp

lemma wt_k_iff (m : Fin k → ZMod 2) : wt m = k ↔ m = fun _ => 1 := by
  have e := Finset.card_filter_eq_iff (s := (Finset.univ : Finset (Fin k))) (p := fun i => m i = 1)
  rw [Finset.card_univ, Fintype.card_fin] at e
  rw [wt, e]
  constructor
  · intro h; funext i; exact h i (Finset.mem_univ i)
  · rintro rfl i _; rfl

lemma fib_zero_card : (fib (0 : Fin k → ZMod 2)).card = 2 ^ k := by
  have : fib (0 : Fin k → ZMod 2) = Finset.univ := by
    apply Finset.filter_true_of_mem; intro u _ i; simp
  rw [this, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]

lemma fib_one_card : (fib (fun _ : Fin k => (1 : ZMod 2))).card = 2 := by
  have : fib (fun _ : Fin k => (1 : ZMod 2)) = {fun _ => 0, fun _ => 1} := by
    ext u
    simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and, one_mul, mul_one,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      have hall : ∀ n : ℕ, u (n : Fin k) = u 0 := by
        intro n; induction n with
        | zero => simp
        | succ n ih => rw [Nat.cast_succ, h, ih]
      have hc : u = fun _ => u 0 := by
        funext j; have := hall j.val; simpa using this
      rcases z2 (u 0) with h0 | h0
      · left; rw [hc, h0]
      · right; rw [hc, h0]
    · rintro (rfl | rfl) <;> intro i <;> rfl
  rw [this, Finset.card_pair]
  intro h; have := congr_fun h 0; exact absurd this (by decide)

theorem main_thm (a f : ℕ) (hak : a ≤ k) :
    (Finset.univ.filter fun m : Fin k → ZMod 2 => wt m = a ∧ (fib m).card = 2^f).card =
      if a = 0 then (if f = k then 1 else 0)
      else if a = k then (if f = 1 then 1 else 0)
      else ∑ r ∈ Finset.Icc 1 (min a (k-a)), ∑ t ∈ Finset.Icc 0 r,
        if r+t ≤ k-a ∧ f = k-a-t then
          (k * Nat.choose (a-1) (r-1) * Nat.choose r t * (if t = 0 then (if r = k-a then 1 else 0)
            else Nat.choose (k-a-r-1) (t-1))) / r
        else 0 := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  split_ifs with h0 hf h1 hf1
  · subst h0; subst hf
    rw [Finset.card_eq_one]; refine ⟨0, ?_⟩
    ext m; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, wt_zero_iff]
    constructor
    · exact fun h => h.1
    · rintro rfl; exact ⟨rfl, fib_zero_card⟩
  · subst h0
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro m - ⟨hw, hc⟩
    rw [wt_zero_iff] at hw; subst hw
    rw [fib_zero_card] at hc; exact hf (pow2_inj.1 hc).symm
  · subst h1; subst hf1
    rw [Finset.card_eq_one]; refine ⟨fun _ => 1, ?_⟩
    ext m; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, wt_k_iff]
    constructor
    · exact fun h => h.1
    · rintro rfl; exact ⟨rfl, by rw [fib_one_card]; rfl⟩
  · subst h1
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro m - ⟨hw, hc⟩
    rw [wt_k_iff] at hw; subst hw
    rw [fib_one_card] at hc
    exact hf1 (pow2_inj.1 (by rw [← hc]; rfl)).symm
  · exact mid (by omega) a f (by omega) (by omega)

end fin

end PEqualNP.Outside.L_lib_755_aux

open PEqualNP.Outside.L_lib_755_aux

theorem PEqualNP.Outside.L_lib_755 : (∀ (k : ℕ) (hk : 0 < k) (a f : ℕ), a ≤ k →
  let F := ZMod 2
  let W := Fin k → F
  let next := fun (i : Fin k) => (⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩ : Fin k)
  let fiber := fun (m : W) => (Finset.univ : Finset W).filter (fun u =>
    ∀ i, m i * u (next i) = u i * m (next i))
  let words := (Finset.univ : Finset W).filter (fun m =>
    (Finset.univ.filter (fun i : Fin k => m i = 1)).card = a ∧ (fiber m).card = 2^f)
  let b := k-a
  words.card =
    if a = 0 then (if f = k then 1 else 0)
    else if a = k then (if f = 1 then 1 else 0)
    else ∑ r ∈ Finset.Icc 1 (min a b), ∑ t ∈ Finset.Icc 0 r,
      if r+t ≤ b ∧ f = b-t then
        let extras := if t = 0 then (if r = b then 1 else 0)
          else Nat.choose (b-r-1) (t-1)
        (k * Nat.choose (a-1) (r-1) * Nat.choose r t * extras) / r
      else 0) := by
  intro k hk a f hak
  have : NeZero k := ⟨by omega⟩
  have hn : ∀ i : Fin k, (⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩ : Fin k) = i + 1 := by
    intro i; ext; rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  intro F W next fiber words b
  have hfib : ∀ m : W, fiber m = fib m := by
    intro m; ext u; simp only [fiber, fib, next, hn, Finset.mem_filter]; try rfl
  have hw : words = Finset.univ.filter fun m : Fin k → ZMod 2 => wt m = a ∧ (fib m).card = 2^f := by
    ext m; simp only [words, hfib, wt, Finset.mem_filter]
    exact ⟨fun h => Finset.mem_filter.2 h, fun h => Finset.mem_filter.1 h⟩
  rw [hw, main_thm a f hak]
