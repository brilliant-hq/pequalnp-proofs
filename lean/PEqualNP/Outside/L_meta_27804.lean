import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27804

namespace Helpers

open PEqualNP PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem final_gates (v : List Bool) (k o0 o1 : ℕ) (hk : k < v.length) (h0 : o0 < v.length)
    (h1 : o1 < v.length) :
    (wiresFrom [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [v.length, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [v.length + 1, v.length + 2]⟩] v).getD (v.length + 3) false
      = ((!(v.getD k false) && v.getD o0 false) || (v.getD k false && v.getD o1 false)) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length → (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [wiresFrom, GateOp.eval, A _ _ hk, A _ _ h0, A _ _ h1]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem shannon (k : ℕ) : ∀ (f : (Fin k → Bool) → Bool) (m : ℕ), k ≤ m →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length + 4 ≤ 5 * 2 ^ k ∧
      out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = f (fun i : Fin k => w.getD i false) := by
  induction k with
  | zero =>
    intro f m _
    refine ⟨[⟨if f (fun i => i.elim0) = true then GateOp.and else GateOp.or, []⟩], m, ?_, by simp,
      by simp, ?_⟩
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      refine ⟨?_, by simp⟩
      by_cases h : f (fun i => i.elim0) = true <;> simp [h]
    · intro w hw
      have hf : (fun i : Fin 0 => w.getD i false) = (fun i => i.elim0) := Subsingleton.elim _ _
      rw [hf]
      by_cases h : f (fun i => i.elim0) = true <;>
        simp [wiresFrom, h, ← hw, GateOp.eval]
  | succ k ih =>
    intro f m hm
    obtain ⟨gs0, o0, ok0, len0, ho0, ev0⟩ :=
      ih (fun y => f (Fin.snoc y false)) m (by omega)
    obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ :=
      ih (fun y => f (Fin.snoc y true)) (m + gs0.length) (by omega)
    let M := m + gs0.length + gs1.length
    refine ⟨gs0 ++ gs1 ++ [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [M, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [M + 1, M + 2]⟩], M + 3, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with (hg | hg) | hg | hg | hg | hg
      · exact ok0 g hg
      · exact ok1 g hg
      all_goals (subst hg; simp [Ok])
    · simp only [List.length_append, List.length_cons, List.length_nil]
      rw [pow_succ]; omega
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro w hw
      rw [wiresFrom_append, wiresFrom_append]
      set w1 := wiresFrom gs0 w with hw1
      set w2 := wiresFrom gs1 w1 with hw2
      have l1 : w1.length = m + gs0.length := by rw [hw1, length_wiresFrom, hw]
      have l2 : w2.length = M := by rw [hw2, length_wiresFrom, l1]
      have e0 : w2.getD o0 false = f (Fin.snoc (fun i : Fin k => w.getD i false) false) := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega)]; exact ev0 w hw
      have e1 : w2.getD o1 false = f (Fin.snoc (fun i : Fin k => w.getD i false) true) := by
        rw [ev1 w1 l1]
        congr 2; funext i
        exact getD_wiresFrom _ _ _ (by have := i.isLt; omega)
      have ek : w2.getD k false = w.getD k false := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega), hw1, getD_wiresFrom _ _ _ (by omega)]
      have hx : (fun i : Fin (k + 1) => w.getD i false)
          = Fin.snoc (fun i : Fin k => w.getD i false) (w.getD k false) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      rw [hx]
      have hk2 : k < w2.length := by omega
      have h02 : o0 < w2.length := by omega
      have h12 : o1 < w2.length := by omega
      rw [show M = w2.length from l2.symm, final_gates w2 k o0 o1 hk2 h02 h12, ek, e0, e1]
      cases w.getD k false <;> simp

end Helpers

namespace TableSearch

open PEqualNP PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

def gt (M : ℕ) : GateOp → List ℕ → ℕ
  | GateOp.and, [] => M
  | GateOp.and, [a] => a
  | GateOp.and, a :: b :: _ => a &&& b
  | GateOp.or, [] => 0
  | GateOp.or, [a] => a
  | GateOp.or, a :: b :: _ => a ||| b
  | GateOp.not, [] => M
  | GateOp.not, a :: _ => M ^^^ a
  | _, _ => 0

def tstep (M : ℕ) (T : List ℕ) (g : Gate) : List ℕ :=
  T ++ [gt M g.op (g.inputs.map fun i => T.getD i 0)]

def tabs (M : ℕ) (T0 : List ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (tstep M) T0

def GOk (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

theorem gt_testBit (M p : ℕ) (hM : M.testBit p = true) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (l : List ℕ)
    (hl : l.length ≤ 2) :
    (gt M op l).testBit p = op.eval (l.map fun t => t.testBit p) := by
  match l, hl with
  | [], _ => rcases hop with h | h | h <;> subst h <;> simp [gt, GateOp.eval, hM]
  | [a], _ => rcases hop with h | h | h <;> subst h <;> simp [gt, GateOp.eval, Nat.testBit_xor, hM]
  | [a, b], _ =>
    rcases hop with h | h | h <;> subst h <;>
      simp [gt, GateOp.eval, Nat.testBit_xor, Nat.testBit_land, Nat.testBit_lor, hM]

theorem getD_map_testBit (T : List ℕ) (p i : ℕ) :
    (T.map fun t => t.testBit p).getD i false = (T.getD i 0).testBit p := by
  rw [show false = (0 : ℕ).testBit p by simp, List.getD_map]

theorem wires_tabs (M p : ℕ) (hM : M.testBit p = true) :
    ∀ (gs : List Gate) (T0 : List ℕ), (∀ g ∈ gs, GOk g) →
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (T0.map fun t => t.testBit p)
        = (tabs M T0 gs).map fun t => t.testBit p := by
  intro gs
  induction gs with
  | nil => intro T0 _; rfl
  | cons g gs ih =>
    intro T0 hok
    have hg := hok g (by simp)
    have e : (T0.map fun t => t.testBit p) ++
        [g.op.eval (g.inputs.map fun i => (T0.map fun t => t.testBit p).getD i false)]
        = (tstep M T0 g).map fun t => t.testBit p := by
      simp only [tstep, List.map_append, List.map_cons, List.map_nil]
      congr 2
      rw [gt_testBit M p hM g.op hg.1 _ (by simpa using hg.2), List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact getD_map_testBit T0 p i
    simp only [List.foldl_cons]
    rw [e]
    exact ih _ (fun g' hg' => hok g' (by simp [hg']))

def cands (M : ℕ) (S : List ℕ) : List ℕ :=
  M :: 0 :: ((0 :: S).map (fun a => M ^^^ a) ++ (0 :: S) ++
    ((0 :: S).flatMap fun a => (0 :: S).map fun b => a &&& b) ++
    ((0 :: S).flatMap fun a => (0 :: S).map fun b => a ||| b))

def nub : List ℕ → List ℕ
  | [] => []
  | a :: l => if (nub l).contains a then nub l else a :: nub l

theorem mem_nub (x : ℕ) : ∀ l : List ℕ, x ∈ nub l ↔ x ∈ l := by
  intro l
  induction l with
  | nil => simp [nub]
  | cons a l ih =>
    simp only [nub]
    split
    · rename_i h
      simp only [List.contains_iff_mem] at h
      rw [ih, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | h') <;> [exact (ih.1 h); exact h']
    · simp [ih]

def next (M : ℕ) (S : List ℕ) : List ℕ :=
  nub ((cands M S).filter fun t => !(S.contains t))

def reach (M : ℕ) (good : ℕ → Bool) : ℕ → List ℕ → Bool
  | 0, S => (0 :: S).any good
  | k + 1, S => (0 :: S).any good || (next M S).any fun t => reach M good k (S ++ [t])

theorem cands_mono (M : ℕ) (S S' : List ℕ) (h : ∀ x, x ∈ S → x ∈ S') (t : ℕ)
    (ht : t ∈ cands M S) : t ∈ cands M S' := by
  have h0 : ∀ x, x ∈ (0 :: S) → x ∈ (0 :: S') := by
    intro x hx
    rcases List.mem_cons.1 hx with hx | hx
    · simp [hx]
    · exact List.mem_cons_of_mem _ (h x hx)
  simp only [cands, List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap] at ht
  simp only [cands, List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap]
  rcases ht with ht | ht | ((⟨a, ha, e⟩ | ht) | ⟨a, ha, b, hb, e⟩) | ⟨a, ha, b, hb, e⟩
  · exact Or.inl ht
  · exact Or.inr (Or.inl ht)
  · refine Or.inr (Or.inr (Or.inl (Or.inl (Or.inl ⟨a, ?_, e⟩))))
    have := h0 a (by simpa using ha); simpa using this
  · refine Or.inr (Or.inr (Or.inl (Or.inl (Or.inr ?_))))
    have := h0 t (by simpa using ht); simpa using this
  · refine Or.inr (Or.inr (Or.inl (Or.inr ⟨a, ?_, b, ?_, e⟩)))
    · have := h0 a (by simpa using ha); simpa using this
    · have := h0 b (by simpa using hb); simpa using this
  · refine Or.inr (Or.inr (Or.inr ⟨a, ?_, b, ?_, e⟩))
    · have := h0 a (by simpa using ha); simpa using this
    · have := h0 b (by simpa using hb); simpa using this

theorem mem_next (M : ℕ) (S : List ℕ) (t : ℕ) : t ∈ next M S ↔ t ∈ cands M S ∧ t ∉ S := by
  simp [next, mem_nub]

theorem any_congr_mem (l l' : List ℕ) (f f' : ℕ → Bool) (hl : ∀ x, x ∈ l ↔ x ∈ l')
    (hf : ∀ x, f x = f' x) : l.any f = l'.any f' := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨x, hx, e⟩; exact ⟨x, (hl x).1 hx, by rw [← hf]; exact e⟩
  · rintro ⟨x, hx, e⟩; exact ⟨x, (hl x).2 hx, by rw [hf]; exact e⟩

theorem reach_congr (M : ℕ) (good : ℕ → Bool) : ∀ (k : ℕ) (S S' : List ℕ),
    (∀ x, x ∈ S ↔ x ∈ S') → reach M good k S = reach M good k S' := by
  intro k
  induction k with
  | zero =>
    intro S S' h
    simp only [reach]
    exact any_congr_mem _ _ _ _ (by intro x; simp [h]) (fun _ => rfl)
  | succ k ih =>
    intro S S' h
    simp only [reach]
    congr 1
    · exact any_congr_mem _ _ _ _ (by intro x; simp [h]) (fun _ => rfl)
    · apply any_congr_mem
      · intro x
        rw [mem_next, mem_next]
        exact ⟨fun ⟨a, b⟩ => ⟨cands_mono M S S' (fun y => (h y).1) x a, by rwa [← h]⟩,
          fun ⟨a, b⟩ => ⟨cands_mono M S' S (fun y => (h y).2) x a, by rwa [h]⟩⟩
      · intro t
        exact ih _ _ (by intro x; simp [h])

theorem reach_of_zero (M : ℕ) (good : ℕ → Bool) (S : List ℕ) (h : reach M good 0 S = true) :
    ∀ k, reach M good k S = true := by
  intro k
  cases k with
  | zero => exact h
  | succ k => simp only [reach] at h ⊢; simp [h]

theorem reach_succ (M : ℕ) (good : ℕ → Bool) (k : ℕ) (S : List ℕ) :
    reach M good (k + 1) S
      = ((0 :: S).any good || (next M S).any fun t => reach M good k (S ++ [t])) := rfl

theorem reach_mono (M : ℕ) (good : ℕ → Bool) : ∀ (k : ℕ) (S : List ℕ),
    reach M good k S = true → reach M good (k + 1) S = true := by
  intro k
  induction k with
  | zero => intro S h; exact reach_of_zero M good S h 1
  | succ k ih =>
    intro S h
    rw [reach_succ M good k S] at h
    rw [reach_succ M good (k + 1) S]
    simp only [Bool.or_eq_true, List.any_eq_true] at h ⊢
    rcases h with h | ⟨t, ht, e⟩
    · exact Or.inl h
    · exact Or.inr ⟨t, ht, ih _ e⟩

theorem getD_mem_zero (S : List ℕ) (o : ℕ) : S.getD o 0 ∈ (0 :: S) := by
  rw [List.getD_eq_getElem?_getD]
  cases hs : S[o]? with
  | none => simp
  | some v => exact List.mem_cons_of_mem _ (List.mem_of_getElem? hs)

theorem mem_cands_not (M : ℕ) (S : List ℕ) (a : ℕ) (ha : a ∈ (0 :: S)) :
    M ^^^ a ∈ cands M S :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem ha)))))

theorem mem_cands_copy (M : ℕ) (S : List ℕ) (a : ℕ) (ha : a ∈ (0 :: S)) : a ∈ cands M S :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _ ha))))

theorem mem_cands_and (M : ℕ) (S : List ℕ) (a b : ℕ) (ha : a ∈ (0 :: S)) (hb : b ∈ (0 :: S)) :
    a &&& b ∈ cands M S :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_flatMap.2 ⟨a, ha, List.mem_map_of_mem hb⟩))))

theorem mem_cands_or (M : ℕ) (S : List ℕ) (a b : ℕ) (ha : a ∈ (0 :: S)) (hb : b ∈ (0 :: S)) :
    a ||| b ∈ cands M S :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _
    (List.mem_flatMap.2 ⟨a, ha, List.mem_map_of_mem hb⟩)))

theorem gt_mem (M : ℕ) (S : List ℕ) (g : Gate) (hg : GOk g) :
    gt M g.op (g.inputs.map fun i => S.getD i 0) ∈ cands M S := by
  obtain ⟨hop, hl⟩ := hg
  have hm : ∀ i, S.getD i 0 ∈ (0 :: S) := getD_mem_zero S
  generalize g.inputs = ins at hl ⊢
  match ins, hl with
  | [], _ =>
    rcases hop with h | h | h <;> rw [h] <;> simp [gt, cands]
  | [i], _ =>
    rcases hop with h | h | h <;> rw [h] <;> simp only [gt, List.map_cons, List.map_nil]
    · exact mem_cands_copy M S _ (hm i)
    · exact mem_cands_copy M S _ (hm i)
    · exact mem_cands_not M S _ (hm i)
  | [i, j], _ =>
    rcases hop with h | h | h <;> rw [h] <;> simp only [gt, List.map_cons, List.map_nil]
    · exact mem_cands_and M S _ _ (hm i) (hm j)
    · exact mem_cands_or M S _ _ (hm i) (hm j)
    · exact mem_cands_not M S _ (hm i)

theorem reach_sound (M : ℕ) (good : ℕ → Bool) : ∀ (gs : List Gate) (k : ℕ) (S : List ℕ)
    (o : ℕ), gs.length ≤ k → (∀ g ∈ gs, GOk g) → good ((tabs M S gs).getD o 0) = true →
    reach M good k S = true := by
  intro gs
  induction gs with
  | nil =>
    intro k S o _ _ hgood
    apply reach_of_zero
    simp only [reach, List.any_eq_true]
    exact ⟨_, getD_mem_zero S o, hgood⟩
  | cons g gs ih =>
    intro k S o hk hok hgood
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    have hg := hok g (by simp)
    set t := gt M g.op (g.inputs.map fun i => S.getD i 0) with ht
    have h1 : reach M good k' (S ++ [t]) = true :=
      ih k' (S ++ [t]) o (by simpa using hk) (fun g' hg' => hok g' (by simp [hg'])) hgood
    by_cases hin : t ∈ S
    · have e : reach M good k' (S ++ [t]) = reach M good k' S :=
        reach_congr M good k' _ _ (by intro x; simp only [List.mem_append, List.mem_singleton]
                                      constructor
                                      · rintro (h | rfl) <;> assumption
                                      · exact Or.inl)
      exact reach_mono M good k' S (e ▸ h1)
    · simp only [reach, Bool.or_eq_true, List.any_eq_true]
      exact Or.inr ⟨t, (mem_next M S t).2 ⟨gt_mem M S g hg, hin⟩, h1⟩

theorem mod_eq_of_testBit (B t tgt : ℕ) (htgt : tgt < 2 ^ B)
    (h : ∀ p, p < B → t.testBit p = tgt.testBit p) : t % 2 ^ B = tgt := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow]
  by_cases hi : i < B
  · simp [hi, h i hi]
  · simp only [hi, decide_false, Bool.false_and]
    symm
    apply Nat.testBit_eq_false_of_lt
    exact lt_of_lt_of_le htgt (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem lower_of_search (n B : ℕ) (f : (Fin n → Bool) → Bool) (T0 : List ℕ) (tgt k : ℕ)
    (htgt : tgt < 2 ^ B)
    (hpt : ∀ p, p < B → ∃ x : Fin n → Bool, List.ofFn x = T0.map (fun t => t.testBit p) ∧
      f x = tgt.testBit p)
    (hsearch : reach (2 ^ B - 1) (fun t => t % 2 ^ B == tgt) k T0 = false) :
    ¬ HasCircuitSize n f k := by
  rintro ⟨C, hC, hsize, hev⟩
  have hok : ∀ g ∈ C.gates, GOk g := by
    intro g hg
    obtain ⟨h1, h2⟩ := hC g hg
    refine ⟨?_, h2⟩
    simpa [Set.mem_insert_iff] using h1
  have hgood : (fun t => t % 2 ^ B == tgt) ((tabs (2 ^ B - 1) T0 C.gates).getD C.output 0)
      = true := by
    simp only [beq_iff_eq]
    apply mod_eq_of_testBit B _ tgt htgt
    intro p hp
    obtain ⟨x, hx, hfx⟩ := hpt p hp
    have hM : (2 ^ B - 1).testBit p = true := by
      rw [Nat.testBit_two_pow_sub_one]; simpa using hp
    have := hev x
    rw [hfx] at this
    rw [← this, Circuit.eval, Circuit.wires, hx, wires_tabs _ p hM _ _ hok,
      getD_map_testBit]
  have := reach_sound (2 ^ B - 1) (fun t => t % 2 ^ B == tgt) C.gates k T0 C.output hsize hok hgood
  rw [hsearch] at this
  exact absurd this (by decide)

end TableSearch

namespace ExactMaj3

open PEqualNP PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds TableSearch

def maj3 : (Fin 3 → Bool) → Bool :=
  fun x : Fin 3 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2)

def maj3Circuit : Circuit :=
  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [4, 2]⟩, ⟨GateOp.or, [3, 5]⟩], 6⟩

theorem maj3_upper : HasCircuitSize 3 maj3 4 := by
  refine ⟨maj3Circuit, ?_, by decide, ?_⟩
  · intro g hg
    simp only [maj3Circuit, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp
  · decide

theorem maj3_search : reach (2 ^ 8 - 1) (fun t => t % 2 ^ 8 == 232) 3 [170, 204, 240] = false := by
  decide +kernel

theorem maj3_lower : ¬ HasCircuitSize 3 maj3 3 := by
  apply lower_of_search 3 8 maj3 [170, 204, 240] 232 3 (by norm_num) _ maj3_search
  have key : ∀ p, p < 8 → (List.ofFn fun i : Fin 3 => p.testBit i)
      = [170, 204, 240].map (fun t : ℕ => t.testBit p) ∧
      maj3 (fun i => p.testBit i) = Nat.testBit 232 p := by decide
  exact fun p hp => ⟨_, key p hp⟩

theorem hasCircuitSize_mono {n : ℕ} {f : (Fin n → Bool) → Bool} {s t : ℕ} (hst : s ≤ t)
    (h : HasCircuitSize n f s) : HasCircuitSize n f t := by
  obtain ⟨C, h1, h2, h3⟩ := h
  exact ⟨C, h1, le_trans h2 hst, h3⟩

theorem maj3_size (s : ℕ) : HasCircuitSize 3 maj3 s ↔ 4 ≤ s := by
  constructor
  · intro h
    by_contra hs
    exact maj3_lower (hasCircuitSize_mono (by omega) h)
  · intro h
    exact hasCircuitSize_mono h maj3_upper

end ExactMaj3

theorem L100 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2)) s ↔ 4 ≤ s :=
  ExactMaj3.maj3_size

namespace RepReads

open PEqualNP PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Helpers
open PEqualNP.Represents

theorem wiresFrom_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wiresFrom (gs ++ [g]) x = wiresFrom gs x ++
      [g.op.eval (g.inputs.map fun i => (wiresFrom gs x).getD i false)] := by
  rw [wiresFrom_append]; rfl

theorem getD_snoc (V : List Bool) (e : Bool) (i : ℕ) :
    (V ++ [e]).getD i false = if i = V.length then e else V.getD i false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem needed (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ N : Finset ℕ, ∃ N' : Finset ℕ, N'.card ≤ N.card + gs.length ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
        (∀ i ∈ N', x.getD i false = y.getD i false) →
        ∀ i ∈ N, (wiresFrom gs x).getD i false = (wiresFrom gs y).getD i false := by
  induction gs using List.reverseRecOn with
  | nil => intro N; exact ⟨N, by simp, fun x y _ _ h => h⟩
  | append_singleton gs g ih =>
    intro N
    have hgs : ∀ g ∈ gs, g.inputs.length ≤ 2 := fun g' h => hg g' (List.mem_append_left _ h)
    have hg2 : g.inputs.length ≤ 2 := hg g (by simp)
    by_cases hm : n + gs.length ∈ N
    · obtain ⟨N', hc, hN⟩ := ih hgs (N.erase (n + gs.length) ∪ g.inputs.toFinset)
      refine ⟨N', ?_, fun x y hx hy h i hi => ?_⟩
      · have h1 := Finset.card_union_le (N.erase (n + gs.length)) g.inputs.toFinset
        have h2 := Finset.card_erase_of_mem hm
        have h3 := List.toFinset_card_le g.inputs
        have h4 : 0 < N.card := Finset.card_pos.2 ⟨_, hm⟩
        rw [List.length_append, List.length_singleton]
        omega
      · have H := hN x y hx hy h
        rw [wiresFrom_snoc, wiresFrom_snoc, getD_snoc, getD_snoc, length_wiresFrom,
          length_wiresFrom, hx, hy]
        split_ifs with hk
        · congr 1
          apply List.map_congr_left
          intro a ha
          exact H a (Finset.mem_union_right _ (List.mem_toFinset.2 ha))
        · exact H i (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hk, hi⟩))
    · obtain ⟨N', hc, hN⟩ := ih hgs N
      refine ⟨N', ?_, fun x y hx hy h i hi => ?_⟩
      · rw [List.length_append, List.length_singleton]; omega
      · rw [wiresFrom_snoc, wiresFrom_snoc, getD_snoc, getD_snoc, length_wiresFrom,
          length_wiresFrom, hx, hy]
        have hk : i ≠ n + gs.length := fun h => hm (h ▸ hi)
        rw [if_neg hk, if_neg hk]
        exact hN x y hx hy h i hi

theorem op_mono (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (S T : ℕ → Bool) (h : ∀ i, S i = true → T i = true)
    (he : g.op.eval (g.inputs.map S) = true) : g.op.eval (g.inputs.map T) = true := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop <;> rw [hop] at he ⊢
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id] at he ⊢
    exact fun i hi => h i (he i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at he ⊢
    obtain ⟨i, hi, hv⟩ := he
    exact ⟨i, hi, h i hv⟩

theorem mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (x y : List Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (wiresFrom gs x).getD i false = true → (wiresFrom gs y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => exact h
  | append_singleton gs g ih =>
    have H := ih fun g' h' => hg g' (List.mem_append_left _ h')
    intro i
    rw [wiresFrom_snoc, wiresFrom_snoc, getD_snoc, getD_snoc, length_wiresFrom, length_wiresFrom,
      hl]
    split_ifs with hk
    · exact op_mono g (hg g (by simp)) _ _ H
    · exact H i

def inp (N : ℕ) (P : Finset ℕ) : List Bool := List.ofFn fun i : Fin N => decide ((i : ℕ) ∈ P)

theorem inp_getD (N : ℕ) (P : Finset ℕ) (i : ℕ) :
    (inp N P).getD i false = decide (i < N ∧ i ∈ P) := by
  unfold inp
  by_cases h : i < N <;> simp [List.getD_eq_getElem?_getD, h]

theorem oneEach_eq {n m : ℕ} (u : Fin n) (v : Fin m) :
    oneEach u v = inp (n + m) {(u : ℕ), n + (v : ℕ)} := by
  have hu := u.2
  have hv := v.2
  apply List.ext_getElem
  · simp [oneEach, inp]
  · intro i h1 h2
    simp only [oneEach, inp, List.length_append, List.length_ofFn] at h1 h2 ⊢
    by_cases hi : i < n
    · rw [List.getElem_append_left (by simpa using hi)]
      simp only [List.getElem_ofFn, Fin.ext_iff, Finset.mem_insert, Finset.mem_singleton,
        decide_eq_decide]
      omega
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.getElem_ofFn, List.length_ofFn, Fin.ext_iff, Finset.mem_insert,
        Finset.mem_singleton, decide_eq_decide]
      omega

def forcedL {n m : ℕ} (A : Fin n → Fin m → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun u => ∃ v, A u v = true ∧ ∃ u', A u' v = false

def forcedR {n m : ℕ} (A : Fin n → Fin m → Bool) : Finset (Fin m) :=
  Finset.univ.filter fun v => ∃ u, A u v = true ∧ ∃ w, A u w = false

theorem reads_le {n m s : ℕ} (A : Fin n → Fin m → Bool) (h : RepSizeAtMost A s) :
    (forcedL A).card + (forcedR A).card ≤ s + 1 := by
  obtain ⟨C, hC, hs, hR⟩ := h
  obtain ⟨S, hcard, hS⟩ := needed (n + m) C.gates (fun g hg => (hC g hg).2) {C.output}
  have hop : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) :=
    fun g hg => (hC g hg).1
  have hev : ∀ P, C.eval (inp (n + m) P) =
      (wiresFrom C.gates (inp (n + m) P)).getD C.output false := fun P => rfl

  have hoff : ∀ P w, w ∉ S → C.eval (inp (n + m) P) = C.eval (inp (n + m) (P.erase w)) := by
    intro P w hw
    rw [hev, hev]
    refine hS _ _ (by simp [inp]) (by simp [inp]) (fun i hi => ?_) _ (Finset.mem_singleton_self _)
    rw [inp_getD, inp_getD, decide_eq_decide, Finset.mem_erase]
    have : i ≠ w := fun e => hw (e ▸ hi)
    tauto
  have hmono : ∀ P Q : Finset ℕ, P ⊆ Q → C.eval (inp (n + m) P) = true →
      C.eval (inp (n + m) Q) = true := by
    intro P Q hPQ
    rw [hev, hev]
    refine mono C.gates hop _ _ (by simp [inp]) (fun i => ?_) _
    rw [inp_getD, inp_getD, decide_eq_true_eq, decide_eq_true_eq]
    exact fun ⟨a, b⟩ => ⟨a, hPQ b⟩
  have hA : ∀ (u : Fin n) (v : Fin m), C.eval (inp (n + m) {(u : ℕ), n + (v : ℕ)}) = A u v := by
    intro u v
    rw [← oneEach_eq]; exact hR u v
  have hL : ∀ u ∈ forcedL A, (u : ℕ) ∈ S := by
    intro u hu
    obtain ⟨v, h1, u', h2⟩ := (Finset.mem_filter.1 hu).2
    by_contra hw
    have e := hoff {(u : ℕ), n + (v : ℕ)} u hw
    rw [hA, h1] at e
    have := hmono _ {(u' : ℕ), n + (v : ℕ)} (fun i hi => by
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
      tauto) e.symm
    rw [hA, h2] at this
    exact Bool.noConfusion this
  have hRr : ∀ v ∈ forcedR A, n + (v : ℕ) ∈ S := by
    intro v hv
    obtain ⟨u, h1, w, h2⟩ := (Finset.mem_filter.1 hv).2
    by_contra hw
    have e := hoff {(u : ℕ), n + (v : ℕ)} (n + v) hw
    rw [hA, h1] at e
    have := hmono _ {(u : ℕ), n + (w : ℕ)} (fun i hi => by
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
      tauto) e.symm
    rw [hA, h2] at this
    exact Bool.noConfusion this
  have hsub : (forcedL A).image (fun u : Fin n => (u : ℕ)) ∪
      (forcedR A).image (fun v : Fin m => n + (v : ℕ)) ⊆ S := by
    intro i hi
    rcases Finset.mem_union.1 hi with hi | hi
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hi; exact hL u hu
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hi; exact hRr v hv
  have hdis : Disjoint ((forcedL A).image (fun u : Fin n => (u : ℕ)))
      ((forcedR A).image (fun v : Fin m => n + (v : ℕ))) := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨v, _, hv⟩ := Finset.mem_image.1 h2
    have := u.2
    omega
  have hcc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis,
    Finset.card_image_of_injective _ (fun a b h => Fin.ext h),
    Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa using h))] at hcc
  rw [Finset.card_singleton] at hcard
  have : C.gates.length ≤ s := hs
  omega

end RepReads

namespace RepInduced

open PEqualNP PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Helpers
open PEqualNP.Represents RepReads

open scoped Classical

section kill
variable (N : ℕ) (Z : Finset ℕ) (gs : List Gate)

def gat (j : ℕ) : Gate := gs.getD j ⟨.and, []⟩

noncomputable def st : ℕ → List Gate × (ℕ → Option ℕ)
  | 0 => ([], fun w => if w < N ∧ w ∉ Z then some w else none)
  | j + 1 =>
    let p := st j
    let g := gat gs j
    if ∃ i ∈ g.inputs, p.2 i = none then
      (p.1, Function.update p.2 (N + j)
        (if g.op = GateOp.and then none else (g.inputs.filterMap p.2).head?))
    else (p.1 ++ [⟨g.op, g.inputs.map fun i => (p.2 i).getD 0⟩],
      Function.update p.2 (N + j) (some (N + p.1.length)))

def Dead (j : ℕ) : Prop := ∃ i ∈ (gat gs j).inputs, (st N Z gs j).2 i = none

theorem st_dead {j : ℕ} (h : Dead N Z gs j) : st N Z gs (j + 1) =
    ((st N Z gs j).1, Function.update (st N Z gs j).2 (N + j)
      (if (gat gs j).op = GateOp.and then none
        else ((gat gs j).inputs.filterMap (st N Z gs j).2).head?)) := by
  rw [st]; exact if_pos h

theorem st_keep {j : ℕ} (h : ¬ Dead N Z gs j) : st N Z gs (j + 1) =
    ((st N Z gs j).1 ++ [⟨(gat gs j).op, (gat gs j).inputs.map fun i =>
      ((st N Z gs j).2 i).getD 0⟩],
      Function.update (st N Z gs j).2 (N + j) (some (N + (st N Z gs j).1.length))) := by
  rw [st]; exact if_neg h

theorem st_ne {j w : ℕ} (h : w ≠ N + j) : (st N Z gs (j + 1)).2 w = (st N Z gs j).2 w := by
  by_cases hd : Dead N Z gs j
  · rw [st_dead N Z gs hd]; exact Function.update_of_ne h _ _
  · rw [st_keep N Z gs hd]; exact Function.update_of_ne h _ _

theorem st_late (j : ℕ) : ∀ w, N + j ≤ w → (st N Z gs j).2 w = none := by
  induction j with
  | zero => intro w h; simp [st, show ¬ w < N by omega]
  | succ j ih => intro w h; rw [st_ne N Z gs (by omega)]; exact ih w (by omega)

theorem st_final {j k w : ℕ} (hjk : j ≤ k) (h : w < N + j) :
    (st N Z gs k).2 w = (st N Z gs j).2 w := by
  induction k, hjk using Nat.le_induction with
  | base => rfl
  | succ k hk ih => rw [st_ne N Z gs (by omega)]; exact ih

theorem st_off {j k w : ℕ} (hjk : j ≤ k) (h : (st N Z gs k).2 w = none) :
    (st N Z gs j).2 w = none := by
  by_cases hw : w < N + j
  · rw [← st_final N Z gs hjk hw]; exact h
  · exact st_late N Z gs j w (by omega)

theorem st_len (j : ℕ) : (st N Z gs j).1.length +
    ((Finset.range j).filter fun i => Dead N Z gs i).card = j := by
  induction j with
  | zero => simp [st]
  | succ j ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hd : Dead N Z gs j
    · rw [if_pos hd, Finset.card_insert_of_notMem (by simp), st_dead N Z gs hd]
      show (st N Z gs j).1.length + _ = _
      omega
    · rw [if_neg hd, st_keep N Z gs hd]
      simp only [List.length_append, List.length_singleton]
      omega

theorem st_lt (j : ℕ) : ∀ w a, (st N Z gs j).2 w = some a → a < N + (st N Z gs j).1.length := by
  induction j with
  | zero =>
    intro w a h
    simp only [st] at h
    split_ifs at h with hw
    · simp only [Option.some.injEq] at h
      simp [st]; omega
  | succ j ih =>
    intro w a h
    by_cases hd : Dead N Z gs j
    · rw [st_dead N Z gs hd] at h ⊢
      by_cases hw : w = N + j
      · subst hw
        simp only [Function.update_self] at h
        split_ifs at h
        have hm := List.mem_of_mem_head? (Option.mem_def.2 h)
        obtain ⟨i, _, hi⟩ := List.mem_filterMap.1 hm
        exact ih i a hi
      · simp only [Function.update_of_ne hw] at h
        exact ih w a h
    · rw [st_keep N Z gs hd] at h ⊢
      simp only [List.length_append, List.length_singleton]
      by_cases hw : w = N + j
      · subst hw
        simp only [Function.update_self, Option.some.injEq] at h
        omega
      · simp only [Function.update_of_ne hw] at h
        have := ih w a h
        omega

variable (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)

include hgs in
theorem gat_ok (j : ℕ) : ((gat gs j).op = GateOp.and ∨ (gat gs j).op = GateOp.or) ∧
    (gat gs j).inputs.length ≤ 2 := by
  by_cases h : j < gs.length
  · have := hgs (gat gs j) (by rw [gat, List.getD_eq_getElem _ _ h]; exact List.getElem_mem h)
    simpa using this
  · rw [gat, List.getD_eq_default _ _ (by omega)]; simp

include hgs in
theorem st_ok (j : ℕ) : ∀ g ∈ (st N Z gs j).1,
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction j with
  | zero => simp [st]
  | succ j ih =>
    by_cases hd : Dead N Z gs j
    · rw [st_dead N Z gs hd]; exact ih
    · rw [st_keep N Z gs hd]
      intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact ih g hg
      · rw [List.mem_singleton.1 hg]
        have := gat_ok gs hgs j
        simpa using this

theorem take_succ (j : ℕ) (hj : j < gs.length) : gs.take (j + 1) = gs.take j ++ [gat gs j] := by
  rw [List.take_succ_eq_append_getElem hj, gat, List.getD_eq_getElem _ _ hj]

include hgs in

theorem st_val (P : Finset ℕ) (j : ℕ) (hj : j ≤ gs.length) : ∀ w,
    ((st N Z gs j).2 w = none → (wiresFrom (gs.take j) (inp N (P \ Z))).getD w false = false) ∧
    ∀ a, (st N Z gs j).2 w = some a → (wiresFrom (st N Z gs j).1 (inp N P)).getD a false =
      (wiresFrom (gs.take j) (inp N (P \ Z))).getD w false := by
  induction j with
  | zero =>
    intro w
    simp only [st, List.take_zero, wiresFrom, List.foldl_nil, inp_getD, Finset.mem_sdiff]
    constructor
    · intro h
      split_ifs at h with hw
      simp only [decide_eq_false_iff_not]; tauto
    · intro a h
      split_ifs at h with hw
      simp only [Option.some.injEq] at h
      subst h
      rw [decide_eq_decide]; tauto
  | succ j ih =>
    have H := ih (by omega)
    have hl1 : (wiresFrom (gs.take j) (inp N (P \ Z))).length = N + j := by
      rw [length_wiresFrom, List.length_take]; simp [inp]; omega
    have hl2 : (wiresFrom (st N Z gs j).1 (inp N P)).length = N + (st N Z gs j).1.length := by
      rw [length_wiresFrom]; simp [inp]
    have hok := gat_ok gs hgs j
    rw [take_succ gs j (by omega), wiresFrom_snoc]
    set V := wiresFrom (gs.take j) (inp N (P \ Z)) with hV
    intro w
    rw [getD_snoc, hl1]
    by_cases hd : Dead N Z gs j
    · rw [st_dead N Z gs hd]
      by_cases hw : w = N + j
      · subst hw
        simp only [Function.update_self, if_true]
        obtain ⟨i, hi, hoff⟩ := hd
        have hi0 := (H i).1 hoff
        rcases hok.1 with hop | hop
        · simp only [hop, if_true]
          refine ⟨fun _ => ?_, fun a h => by simp at h⟩
          rw [← Bool.not_eq_true, GateOp.eval, List.all_eq_true]
          intro h
          have := h _ (List.mem_map.2 ⟨i, hi, rfl⟩)
          rw [hi0] at this; simp at this
        · simp only [hop, reduceCtorEq, if_false]

          have hlen := hok.2
          constructor
          · intro h
            rw [List.head?_eq_none_iff, List.filterMap_eq_nil_iff] at h
            rw [← Bool.not_eq_true, GateOp.eval, List.any_eq_true]
            rintro ⟨b, hb, hb1⟩
            obtain ⟨i', hi', rfl⟩ := List.mem_map.1 hb
            have := (H i').1 (h i' hi')
            rw [this] at hb1; simp at hb1
          · intro a h
            obtain ⟨i', hi', hia⟩ := List.mem_filterMap.1 (List.mem_of_mem_head? (Option.mem_def.2 h))
            rw [(H i').2 a hia, GateOp.eval]
            have hne : i ≠ i' := by rintro rfl; rw [hoff] at hia; simp at hia

            have hall : ∀ b ∈ (gat gs j).inputs, b = i ∨ b = i' := by
              intro b hb
              by_contra hn
              push Not at hn
              have h3 : ({i, i', b} : Finset ℕ) ⊆ (gat gs j).inputs.toFinset := by
                intro c hc
                simp only [Finset.mem_insert, Finset.mem_singleton] at hc
                rcases hc with rfl | rfl | rfl <;> simpa
              have := Finset.card_le_card h3
              rw [Finset.card_eq_three.2 ⟨i, i', b, hne, fun e => hn.1 e.symm, fun e => hn.2 e.symm,
                rfl⟩] at this
              have := List.toFinset_card_le (gat gs j).inputs
              omega
            apply Bool.eq_iff_iff.2
            rw [List.any_eq_true]
            constructor
            · intro hv; exact ⟨_, List.mem_map.2 ⟨i', hi', rfl⟩, hv⟩
            · rintro ⟨b, hb, hb1⟩
              obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
              rcases hall c hc with rfl | rfl
              · rw [hi0] at hb1; simp at hb1
              · exact hb1
      · simp only [Function.update_of_ne hw, if_neg hw]
        exact H w
    · rw [st_keep N Z gs hd]
      by_cases hw : w = N + j
      · subst hw
        simp only [Function.update_self, if_true]
        refine ⟨fun h => by simp at h, fun a h => ?_⟩
        simp only [Option.some.injEq] at h
        subst h
        rw [wiresFrom_snoc, getD_snoc, hl2, if_pos rfl]
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        obtain ⟨b, hb⟩ : ∃ b, (st N Z gs j).2 i = some b := by
          cases h : (st N Z gs j).2 i with
          | none => exact absurd ⟨i, hi, h⟩ hd
          | some b => exact ⟨b, rfl⟩
        simp only [Function.comp_apply, hb, Option.getD_some]
        exact (H i).2 b hb
      · simp only [Function.update_of_ne hw, if_neg hw]
        refine ⟨(H w).1, fun a h => ?_⟩
        have hlt := st_lt N Z gs j w a h
        rw [wiresFrom_snoc, getD_snoc, hl2, if_neg (by omega)]
        exact (H w).2 a h

def Live (o : ℕ) : ℕ → Prop :=
  Relation.ReflTransGen (fun g w => ∃ j < gs.length, g = N + j ∧ w ∈ (gat gs j).inputs) o

theorem live_dep (o : ℕ) (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (h : ∀ i, Live N gs o i → x.getD i false = y.getD i false) (j : ℕ) (hj : j ≤ gs.length) :
    ∀ w, Live N gs o w →
      (wiresFrom (gs.take j) x).getD w false = (wiresFrom (gs.take j) y).getD w false := by
  induction j with
  | zero => intro w hw; simpa [wiresFrom] using h w hw
  | succ j ih =>
    intro w hw
    have H := ih (by omega)
    rw [take_succ gs j (by omega), wiresFrom_snoc, wiresFrom_snoc, getD_snoc, getD_snoc,
      length_wiresFrom, length_wiresFrom, hx, hy, List.length_take, Nat.min_eq_left (by omega)]
    split_ifs with hwj
    · congr 1
      apply List.map_congr_left
      intro a ha
      exact H a (hw.tail ⟨j, by omega, hwj, ha⟩)
    · exact H w hw

include hgs in

theorem kill_count (o : ℕ) (Z0 : Finset ℕ) (hZ0 : ∀ i ∈ Z0, i < N ∧ i ∈ Z ∧ Live N gs o i)
    (ho : (st N Z gs gs.length).2 o ≠ none) :
    Z0.card ≤ ((Finset.range gs.length).filter fun i => Dead N Z gs i).card := by
  set k := gs.length with hk
  let K := (Finset.range k).filter fun j => Dead N Z gs j ∧ Live N gs o (N + j)
  let Y := (Finset.range k).filter fun j => (st N Z gs k).2 (N + j) = none ∧ Live N gs o (N + j)
  let Q : Finset (Σ _ : ℕ, ℕ) := K.sigma fun j =>
    (gat gs j).inputs.toFinset.filter fun i => (st N Z gs j).2 i = none
  let W := Z0 ∪ Y.image fun j => N + j
  have hYK : Y ⊆ K := by
    intro j hj
    obtain ⟨hjk, hz, hl⟩ := Finset.mem_filter.1 hj
    refine Finset.mem_filter.2 ⟨hjk, ?_, hl⟩
    by_contra hd
    have hjk' := Finset.mem_range.1 hjk
    rw [st_final N Z gs (show j + 1 ≤ k by omega) (by omega), st_keep N Z gs hd] at hz
    simp at hz
  have hW : W ⊆ Q.image fun q => q.2 := by
    intro w hw
    have hw2 : (st N Z gs k).2 w = none ∧ Live N gs o w := by
      rcases Finset.mem_union.1 hw with h | h
      · obtain ⟨h1, h2, h3⟩ := hZ0 w h
        refine ⟨?_, h3⟩
        rw [st_final N Z gs (Nat.zero_le k) (by omega)]
        simp [st, h2]
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 h
        exact (Finset.mem_filter.1 hj).2
    have hne : w ≠ o := fun e => ho (e ▸ hw2.1)
    rcases Relation.ReflTransGen.cases_tail hw2.2 with e | ⟨g, hg, j, hj, rfl, hi⟩
    · exact absurd e hne
    · have hoff := st_off N Z gs (show j ≤ k by omega) hw2.1
      refine Finset.mem_image.2 ⟨⟨j, w⟩, Finset.mem_sigma.2 ⟨?_, ?_⟩, rfl⟩
      · exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, ⟨w, hi, hoff⟩, hg⟩
      · exact Finset.mem_filter.2 ⟨List.mem_toFinset.2 hi, hoff⟩
  have hWc : W.card = Z0.card + Y.card := by
    have : Disjoint Z0 (Y.image fun j => N + j) := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 h2
      have := (hZ0 _ h1).1
      omega
    show (Z0 ∪ Y.image fun j => N + j).card = _
    rw [Finset.card_union_of_disjoint this,
      Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  have hQ : Q.card ≤ K.card + Y.card := by
    show (K.sigma _).card ≤ _
    rw [Finset.card_sigma]
    calc ∑ j ∈ K, ((gat gs j).inputs.toFinset.filter fun i => (st N Z gs j).2 i = none).card
        ≤ ∑ j ∈ K, (1 + if j ∈ Y then 1 else 0) := by
          apply Finset.sum_le_sum
          intro j hj
          obtain ⟨hjk, hd, hl⟩ := Finset.mem_filter.1 hj
          have hjk' := Finset.mem_range.1 hjk
          have hok := gat_ok gs hgs j
          have hc := List.toFinset_card_le (gat gs j).inputs
          have hf := Finset.card_filter_le (gat gs j).inputs.toFinset
            fun i => (st N Z gs j).2 i = none
          split_ifs with hY
          · omega
          ·
            have hsome : (st N Z gs k).2 (N + j) ≠ none := fun e =>
              hY (Finset.mem_filter.2 ⟨hjk, e, hl⟩)
            rw [st_final N Z gs (show j + 1 ≤ k by omega) (by omega), st_dead N Z gs hd] at hsome
            simp only [Function.update_self] at hsome
            obtain ⟨i, hi, hia⟩ : ∃ i ∈ (gat gs j).inputs, (st N Z gs j).2 i ≠ none := by
              by_contra hn
              push Not at hn
              apply hsome
              split_ifs
              · rfl
              · rw [List.head?_eq_none_iff, List.filterMap_eq_nil_iff]; exact hn
            have hlt : ((gat gs j).inputs.toFinset.filter fun i => (st N Z gs j).2 i = none).card <
                (gat gs j).inputs.toFinset.card :=
              Finset.card_lt_card (Finset.filter_ssubset.2 ⟨i, List.mem_toFinset.2 hi, hia⟩)
            omega
      _ = K.card + Y.card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, Finset.sum_ite_mem,
            Finset.inter_eq_right.2 hYK, Finset.sum_const, smul_eq_mul, mul_one]
  have h1 := Finset.card_le_card hW
  have h2 := Finset.card_image_le (s := Q) (f := fun q => q.2)
  have h3 : K.card ≤ ((Finset.range k).filter fun i => Dead N Z gs i).card :=
    Finset.card_le_card fun j hj => by
      obtain ⟨a, b, _⟩ := Finset.mem_filter.1 hj
      exact Finset.mem_filter.2 ⟨a, b⟩
  omega

include hgs in

theorem kill (o : ℕ) (Z0 : Finset ℕ) (hZ0 : ∀ i ∈ Z0, i < N ∧ i ∈ Z ∧ Live N gs o i)
    (P0 : Finset ℕ) (hP0 : Circuit.eval ⟨gs, o⟩ (inp N (P0 \ Z)) = true) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + Z0.card ≤ gs.length ∧
      ∀ P, D.eval (inp N P) = Circuit.eval ⟨gs, o⟩ (inp N (P \ Z)) := by
  have hv : ∀ P, _ := fun P => st_val N Z gs hgs P gs.length le_rfl o
  simp only [List.take_length] at hv
  have ho : (st N Z gs gs.length).2 o ≠ none := by
    intro e
    have := (hv P0).1 e
    rw [show Circuit.eval ⟨gs, o⟩ (inp N (P0 \ Z)) =
      (wiresFrom gs (inp N (P0 \ Z))).getD o false from rfl, this] at hP0
    exact Bool.noConfusion hP0
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 ho
  refine ⟨⟨(st N Z gs gs.length).1, a⟩, st_ok N Z gs hgs _, ?_, fun P => (hv P).2 a ha⟩
  have h1 := kill_count N Z gs hgs o Z0 hZ0 ho
  have h2 := st_len N Z gs gs.length
  show (st N Z gs gs.length).1.length + Z0.card ≤ gs.length
  omega

end kill

theorem induced : ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (R : Finset (Fin n)) (K : Finset (Fin m)), (∀ u ∈ R, ∃ v ∈ K, A u v = false) → (∀ v ∈ K, ∃ u ∈ R, A u v = false) → (∃ u ∈ R, ∃ v ∈ K, A u v = true) → PEqualNP.Represents.RepSizeAtMost A s → ∃ s' : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v => A u v && decide (u ∈ R) && decide (v ∈ K)) s' ∧ s' + ((Finset.univ.filter (fun a : Fin n => ∃ b : Fin m, A a b = true ∧ ∃ a' : Fin n, A a' b = false)).card + (Finset.univ.filter (fun b : Fin m => ∃ a : Fin n, A a b = true ∧ ∃ b' : Fin m, A a b' = false)).card) ≤ s + ((R.filter (fun a => ∃ b ∈ K, A a b = true)).card + (K.filter (fun b => ∃ a ∈ R, A a b = true)).card) := by
  intro n m s A R K hR hK ⟨u0, hu0, v0, hv0, h0⟩ ⟨⟨gs, o⟩, hC, hs, hrep⟩
  let BL := R.filter fun a => ∃ b ∈ K, A a b = true
  let BR := K.filter fun b => ∃ a ∈ R, A a b = true
  let Z : Finset ℕ := (Finset.univ.filter fun a : Fin n => a ∉ BL).image (fun a : Fin n => (a : ℕ)) ∪
    (Finset.univ.filter fun b : Fin m => b ∉ BR).image (fun b : Fin m => n + (b : ℕ))
  have hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := hC
  have hop : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := fun g hg => (hC g hg).1
  have hZl : ∀ a : Fin n, (a : ℕ) ∈ Z ↔ a ∉ BL := by
    intro a
    simp only [Z, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨x, hx, e⟩ | ⟨x, _, e⟩)
      · rwa [← Fin.ext e]
      · have := a.2; omega
    · exact fun h => Or.inl ⟨a, h, rfl⟩
  have hZr : ∀ b : Fin m, n + (b : ℕ) ∈ Z ↔ b ∉ BR := by
    intro b
    simp only [Z, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨x, _, e⟩ | ⟨x, hx, e⟩)
      · have := x.2; omega
      · rwa [← Fin.ext (show (x : ℕ) = b by omega)]
    · exact fun h => Or.inr ⟨b, h, rfl⟩
  have hmono : ∀ P Q : Finset ℕ, P ⊆ Q → Circuit.eval ⟨gs, o⟩ (inp (n + m) P) = true →
      Circuit.eval ⟨gs, o⟩ (inp (n + m) Q) = true := by
    intro P Q hPQ
    refine mono gs hop _ _ (by simp [inp]) (fun i => ?_) _
    rw [inp_getD, inp_getD, decide_eq_true_eq, decide_eq_true_eq]
    exact fun ⟨a, b⟩ => ⟨a, hPQ b⟩
  have hA : ∀ (u : Fin n) (v : Fin m),
      Circuit.eval ⟨gs, o⟩ (inp (n + m) {(u : ℕ), n + (v : ℕ)}) = A u v := by
    intro u v; rw [← oneEach_eq]; exact hrep u v
  have hoff : ∀ P w, ¬ Live (n + m) gs o w →
      Circuit.eval ⟨gs, o⟩ (inp (n + m) P) = Circuit.eval ⟨gs, o⟩ (inp (n + m) (P.erase w)) := by
    intro P w hw
    have := live_dep (n + m) gs o (inp (n + m) P) (inp (n + m) (P.erase w)) (by simp [inp])
      (by simp [inp]) (fun i hi => by
        rw [inp_getD, inp_getD, decide_eq_decide, Finset.mem_erase]
        have : i ≠ w := fun e => hw (e ▸ hi)
        tauto) gs.length le_rfl o Relation.ReflTransGen.refl
    rw [List.take_length] at this
    exact this
  have hL : ∀ u ∈ forcedL A, Live (n + m) gs o (u : ℕ) := by
    intro u hu
    obtain ⟨v, h1, u', h2⟩ := (Finset.mem_filter.1 hu).2
    by_contra hw
    have e := hoff {(u : ℕ), n + (v : ℕ)} u hw
    rw [hA, h1] at e
    have := hmono _ {(u' : ℕ), n + (v : ℕ)} (fun i hi => by
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
      tauto) e.symm
    rw [hA, h2] at this
    exact Bool.noConfusion this
  have hRr : ∀ v ∈ forcedR A, Live (n + m) gs o (n + (v : ℕ)) := by
    intro v hv
    obtain ⟨u, h1, w, h2⟩ := (Finset.mem_filter.1 hv).2
    by_contra hw
    have e := hoff {(u : ℕ), n + (v : ℕ)} (n + v) hw
    rw [hA, h1] at e
    have := hmono _ {(u : ℕ), n + (w : ℕ)} (fun i hi => by
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
      tauto) e.symm
    rw [hA, h2] at this
    exact Bool.noConfusion this
  have hBL : BL ⊆ forcedL A := by
    intro a ha
    obtain ⟨_, b, hb, hab⟩ := Finset.mem_filter.1 ha
    obtain ⟨a', _, ha'⟩ := hK b hb
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, b, hab, a', ha'⟩
  have hBR : BR ⊆ forcedR A := by
    intro b hb
    obtain ⟨_, a, ha, hab⟩ := Finset.mem_filter.1 hb
    obtain ⟨b', _, hb'⟩ := hR a ha
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, a, hab, b', hb'⟩
  let Z0 : Finset ℕ := (forcedL A \ BL).image (fun a : Fin n => (a : ℕ)) ∪
    (forcedR A \ BR).image (fun b : Fin m => n + (b : ℕ))
  have hZ0 : ∀ i ∈ Z0, i < n + m ∧ i ∈ Z ∧ Live (n + m) gs o i := by
    intro i hi
    rcases Finset.mem_union.1 hi with hi | hi
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hi
      obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 ha
      exact ⟨by have := a.2; omega, (hZl a).2 h2, hL a h1⟩
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hi
      obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hb
      exact ⟨by have := b.2; omega, (hZr b).2 h2, hRr b h1⟩
  have hZ0c : Z0.card = (forcedL A \ BL).card + (forcedR A \ BR).card := by
    have hdis : Disjoint ((forcedL A \ BL).image (fun a : Fin n => (a : ℕ)))
        ((forcedR A \ BR).image (fun b : Fin m => n + (b : ℕ))) := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 h1
      obtain ⟨v, _, hv⟩ := Finset.mem_image.1 h2
      have := u.2
      omega
    show (_ ∪ _ : Finset ℕ).card = _
    rw [Finset.card_union_of_disjoint hdis,
      Finset.card_image_of_injective _ (fun a b h => Fin.ext h),
      Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa using h))]

  have hval : ∀ (u : Fin n) (v : Fin m),
      Circuit.eval ⟨gs, o⟩ (inp (n + m) (({(u : ℕ), n + (v : ℕ)} : Finset ℕ) \ Z)) =
        (A u v && decide (u ∈ R) && decide (v ∈ K)) := by
    intro u v
    by_cases hu : u ∈ BL
    · by_cases hv : v ∈ BR
      · have hu' := (Finset.mem_filter.1 hu).1
        have hv' := (Finset.mem_filter.1 hv).1
        rw [show ({(u : ℕ), n + (v : ℕ)} : Finset ℕ) \ Z = {(u : ℕ), n + (v : ℕ)} from by
          rw [Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_left]
          intro i hi
          rcases Finset.mem_insert.1 hi with rfl | hi
          · rw [hZl]; exact fun h => h hu
          · rw [Finset.mem_singleton.1 hi, hZr]; exact fun h => h hv, hA]
        simp [hu', hv']
      ·
        have hu' := (Finset.mem_filter.1 hu).1
        obtain ⟨b, hb, hab⟩ := hR u hu'
        have e1 : (A u v && decide (u ∈ R) && decide (v ∈ K)) = false := by
          by_contra hne
          simp only [Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hne
          exact hv (Finset.mem_filter.2 ⟨hne.2, u, hne.1.2, hne.1.1⟩)
        rw [e1]
        by_contra hne
        rw [Bool.not_eq_false] at hne
        have := hmono _ {(u : ℕ), n + (b : ℕ)} (fun i hi => by
          obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hi
          rcases Finset.mem_insert.1 h1 with rfl | h1
          · simp
          · rw [Finset.mem_singleton.1 h1] at h2; exact absurd ((hZr v).2 hv) h2) hne
        rw [hA, hab] at this
        exact Bool.noConfusion this
    ·
      have e1 : (A u v && decide (u ∈ R) && decide (v ∈ K)) = false := by
        by_contra hne
        simp only [Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hne
        exact hu (Finset.mem_filter.2 ⟨hne.1.2, v, hne.2, hne.1.1⟩)
      rw [e1]
      by_contra hne
      rw [Bool.not_eq_false] at hne
      obtain ⟨b, hb, a, hab⟩ : ∃ b : Fin m, (n + (v : ℕ) ∉ Z → b = v) ∧ ∃ a : Fin n, A a b = false := by
        by_cases hv : v ∈ BR
        · obtain ⟨a, _, ha⟩ := hK v (Finset.mem_filter.1 hv).1
          exact ⟨v, fun _ => rfl, a, ha⟩
        · obtain ⟨a, _, ha⟩ := hK v0 hv0
          exact ⟨v0, fun h => absurd ((hZr v).2 hv) h, a, ha⟩
      have := hmono _ {(a : ℕ), n + (b : ℕ)} (fun i hi => by
        obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hi
        rcases Finset.mem_insert.1 h1 with rfl | h1
        · exact absurd ((hZl u).2 hu) h2
        · rw [Finset.mem_singleton.1 h1] at h2 ⊢
          rw [hb h2]; simp) hne
      rw [hA, hab] at this
      exact Bool.noConfusion this
  obtain ⟨D, hD1, hD2, hD3⟩ := kill (n + m) Z gs hgs o Z0 hZ0 {(u0 : ℕ), n + (v0 : ℕ)}
    (by rw [hval]; simp [h0, hu0, hv0])
  refine ⟨D.size, ⟨D, hD1, le_rfl, fun u v => ?_⟩, ?_⟩
  · rw [oneEach_eq, hD3, hval]
  · have c1 := Finset.card_sdiff_add_card_eq_card hBL
    have c2 := Finset.card_sdiff_add_card_eq_card hBR
    have hs' : gs.length ≤ s := hs
    have e1 : (Finset.univ.filter (fun a : Fin n => ∃ b : Fin m, A a b = true ∧
      ∃ a' : Fin n, A a' b = false)).card = (forcedL A).card := by unfold forcedL; congr
    have e2 : (Finset.univ.filter (fun b : Fin m => ∃ a : Fin n, A a b = true ∧
      ∃ b' : Fin m, A a b' = false)).card = (forcedR A).card := by unfold forcedR; congr
    have e3 : (R.filter (fun a => ∃ b ∈ K, A a b = true)).card = BL.card := by congr
    have e4 : (K.filter (fun b => ∃ a ∈ R, A a b = true)).card = BR.card := by congr
    rw [e1, e2]
    try rw [e3, e4]
    omega

end RepInduced

namespace S18508

abbrev Gates := ℕ → Bool × ℕ × ℕ

def bin (op a b : Bool) := if op then a && b else a || b

def val (S : Finset ℕ) (g : Gates) (x : ℕ → Bool) (w : ℕ) : Bool :=
  if w ∈ S then bin (g w).1
    (if (g w).2.1 < w then val S g x (g w).2.1 else false)
    (if (g w).2.2 < w then val S g x (g w).2.2 else false)
  else x w
termination_by w

def Good (H : ℕ) (S : Finset ℕ) (g : Gates) : Prop :=
  ∀ w ∈ S, H ≤ w ∧ (g w).2.1 < w ∧ (g w).2.2 < w

theorem vin {S : Finset ℕ} {g : Gates} {x : ℕ → Bool} {w H : ℕ} (h : Good H S g) (hw : w ∈ S) :
    val S g x w = bin (g w).1 (val S g x (g w).2.1) (val S g x (g w).2.2) := by
  rw [val, ite_eq_left hw, ite_eq_left (h w hw).2.1, ite_eq_left (h w hw).2.2]

theorem vout {S : Finset ℕ} {g : Gates} {x : ℕ → Bool} {w : ℕ} (hw : w ∉ S) : val S g x w = x w := by
  rw [val, ite_eq_right hw]

def lport (i : ℕ) := 2 * i + 2

def rport (i : ℕ) := 2 * i + 3

def point (M : Finset ℕ) (u v w : ℕ) : Bool :=
  decide (w = 0 ∨ w = lport u ∨ w = rport v ∨ (u ∉ M ∧ w = rport u) ∨ (v ∉ M ∧ w = lport v))

def Solves (K M S : Finset ℕ) (g : Gates) (o : ℕ) : Prop :=
  ∀ u ∈ K, ∀ v ∈ K, val S g (point M u v) o = decide (u ≠ v)

def Dark (K S : Finset ℕ) (g : Gates) (w : ℕ) : Prop :=
  ∀ i ∈ K, val S g (point ∅ i i) w = false

def Normal (K S : Finset ℕ) (g : Gates) : Prop :=
  ∀ w ∈ S, Dark K S g (g w).2.1 ∨ Dark K S g (g w).2.2 → Dark K S g w

def Alias (K M S : Finset ℕ) (g : Gates) (w : ℕ) : Prop :=
  ∃ t < w, ∀ u ∈ K, ∀ v ∈ K, val S g (point M u v) w = val S g (point M u v) t

theorem nrDiag (M : Finset ℕ) (i : ℕ) : point M i i = point ∅ i i := by
  funext w
  unfold point
  congr 1
  apply propext
  tauto

def nrAlias (t b w : ℕ) := if w = t then b else w

theorem nrAliasLe {b t : ℕ} (hb : b < t) (w : ℕ) : nrAlias t b w ≤ w := by
  by_cases hw : w = t <;> simp [nrAlias, hw, hb.le]

def nrSet (S : Finset ℕ) (t f : ℕ) := insert f (S.erase t)

def nrGate (g : Gates) (t b d o f : ℕ) : Gates := fun w =>
  if w = f then (false, d, nrAlias t b o)
  else ((g w).1, nrAlias t b (g w).2.1, nrAlias t b (g w).2.2)

theorem nrEval {H t b d o f : ℕ} {S : Finset ℕ} {g : Gates}
    (hg : Good H S g) (hT : Good H (nrSet S t f) (nrGate g t b d o f)) (hb : b < t)
    (hv : ∀ x, val S g x t = (val S g x d || val S g x b)) (x : ℕ → Bool) (w : ℕ) :
    w < f → (w < t ∨ val S g x d = false) →
      val (nrSet S t f) (nrGate g t b d o f) x (nrAlias t b w) = val S g x w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwf hx
    by_cases hwt : w = t
    · subst w
      have hd : val S g x d = false := hx.resolve_left (Nat.lt_irrefl _)
      have hB := ih b hb (hb.trans hwf) (Or.inl hb)
      simpa [nrAlias, hb.ne, hv x, hd] using hB
    · rw [show nrAlias t b w = w by simp [nrAlias, hwt]]
      by_cases hw : w ∈ S
      · have hnew : w ∈ nrSet S t f := Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hwt, hw⟩)
        rw [vin hT hnew, vin hg hw]
        simp only [nrGate, ite_eq_right hwf.ne]
        have hrec (c : ℕ) (hc : c < w) := ih c hc (hc.trans hwf) (hx.imp_left (fun h => hc.trans h))
        rw [hrec _ (hg w hw).2.1, hrec _ (hg w hw).2.2]
      · have hnew : w ∉ nrSet S t f := by simp [nrSet, hwf.ne, hw]
        rw [vout hnew, vout hw]

theorem nrChoice {K S : Finset ℕ} {g : Gates} {H t : ℕ} (hg : Good H S g) (ht : t ∈ S)
    (hc : Dark K S g (g t).2.1 ∨ Dark K S g (g t).2.2) (hn : ¬Dark K S g t) :
    ∃ d b : ℕ, d < t ∧ b < t ∧ Dark K S g d ∧
      ∀ x, val S g x t = (val S g x d || val S g x b) := by
  have hop : (g t).1 = false := by
    cases hh : (g t).1 with
    | false => rfl
    | true =>
      exfalso
      apply hn
      intro i hi
      rw [vin hg ht, hh]
      rcases hc with hd | hd <;> simp [bin, hd i hi]
  rcases hc with hd | hd
  · refine ⟨(g t).2.1, (g t).2.2, (hg t ht).2.1, (hg t ht).2.2, hd, ?_⟩
    intro x
    rw [vin hg ht, hop]
    rfl
  · refine ⟨(g t).2.2, (g t).2.1, (hg t ht).2.2, (hg t ht).2.1, hd, ?_⟩
    intro x
    rw [vin hg ht, hop]
    exact Bool.or_comm _ _

noncomputable def nrLit (K S : Finset ℕ) (g : Gates) : Finset ℕ := by
  classical
  exact S.filter (fun w => ¬Dark K S g w)

theorem nrStep {K M S : Finset ℕ} {g : Gates} {H o : ℕ}
    (hg : Good H S g) (hs : Solves K M S g o) (hn : ¬Normal K S g) :
    ∃ T : Finset ℕ, ∃ h : Gates, ∃ p : ℕ, Good H T h ∧ Solves K M T h p ∧
      T.card ≤ S.card ∧ (nrLit K T h).card < (nrLit K S g).card := by
  classical
  unfold Normal at hn
  push Not at hn
  obtain ⟨t, ht, hc, hnt⟩ := hn
  obtain ⟨d, b, hdt, hbt, hdark, hv⟩ := nrChoice hg ht hc hnt
  let f := S.sup id + o + H + 1
  have hf (w : ℕ) (hw : w ∈ S) : w < f := by
    have hh : id w ≤ S.sup id := Finset.le_sup hw
    change w ≤ S.sup id at hh
    dsimp [f]
    omega
  have hof : o < f := by dsimp [f]; omega
  have hHf : H ≤ f := by dsimp [f]; omega
  have hdf : d < f := hdt.trans (hf t ht)
  let T := nrSet S t f
  let h := nrGate g t b d o f
  have hT : Good H T h := by
    intro w hw
    change w ∈ insert f (S.erase t) at hw
    rcases Finset.mem_insert.mp hw with he | he
    · subst w
      simpa [h, nrGate] using And.intro hHf (And.intro hdf ((nrAliasLe hbt o).trans_lt hof))
    · have hws := (Finset.mem_erase.mp he).2
      have hwf := (hf w hws).ne
      obtain ⟨hH, ha, hb⟩ := hg w hws
      simpa [h, nrGate, hwf] using And.intro hH (And.intro ((nrAliasLe hbt _).trans_lt ha) ((nrAliasLe hbt _).trans_lt hb))
  have heq (x : ℕ → Bool) (w : ℕ) (hwf : w < f) (hx : w < t ∨ val S g x d = false) :
      val T h x (nrAlias t b w) = val S g x w :=
    nrEval hg hT hbt hv x w hwf hx
  have hdeq (x : ℕ → Bool) : val T h x d = val S g x d := by
    simpa only [nrAlias, ite_eq_right hdt.ne] using heq x d hdf (Or.inl hdt)
  have hfT : f ∈ T := Finset.mem_insert_self _ _
  have hfeq (x : ℕ → Bool) : val T h x f = (val S g x d || val T h x (nrAlias t b o)) := by
    rw [vin hT hfT]
    simp [h, nrGate, bin, hdeq]
  have hsol : Solves K M T h f := by
    intro u hu v hw
    let x := point M u v
    change val T h x f = _
    rw [hfeq]
    cases hdx : val S g x d with
    | false =>
      rw [Bool.false_or, heq x o hof (Or.inr hdx)]
      exact hs u hu v hw
    | true =>
      have huv : u ≠ v := by
        intro he
        have hx : x = point ∅ u u := by change point M u v = _; rw [← he, nrDiag]
        rw [hx, hdark u hu] at hdx
        contradiction
      simp [huv]
  have hfdark : Dark K T h f := by
    intro i hi
    simpa only [nrDiag M i, ne_self_iff_false, decide_false] using hsol i hi i hi
  have hsub : nrLit K T h ⊆ (nrLit K S g).erase t := by
    intro w hw
    obtain ⟨hwT, hnw⟩ := Finset.mem_filter.mp hw
    rcases Finset.mem_insert.mp hwT with he | he
    · exact (hnw (he ▸ hfdark)).elim
    · obtain ⟨hwt, hws⟩ := Finset.mem_erase.mp he
      apply Finset.mem_erase.mpr
      refine ⟨hwt, Finset.mem_filter.mpr ⟨hws, ?_⟩⟩
      intro hd
      apply hnw
      intro i hi
      have hval := heq (point ∅ i i) w (hf w hws) (Or.inr (hdark i hi))
      simpa only [nrAlias, ite_eq_right hwt, hd i hi] using hval
  have hcs : T.card ≤ S.card := by
    exact (Finset.card_insert_le f (S.erase t)).trans (Finset.card_erase_add_one ht).le
  have htLit : t ∈ nrLit K S g := Finset.mem_filter.mpr ⟨ht, hnt⟩
  exact ⟨T, h, f, hT, hsol, hcs, (Finset.card_le_card hsub).trans_lt (Finset.card_erase_lt_of_mem htLit)⟩

theorem nrNormalize {n : ℕ} {K M S : Finset ℕ} {g : Gates} {o : ℕ}
    (hg : Good (2*n+2) S g) (hs : Solves K M S g o) :
    ∃ T : Finset ℕ, ∃ h : Gates, ∃ p : ℕ,
      Good (2*n+2) T h ∧ Solves K M T h p ∧ Normal K T h ∧ T.card ≤ S.card := by
  classical
  generalize hq : (nrLit K S g).card = q
  induction q using Nat.strong_induction_on generalizing S g o with
  | ind q ih =>
    by_cases hn : Normal K S g
    · exact ⟨S, g, o, hg, hs, hn, le_rfl⟩
    · obtain ⟨T, h, p, hT, hsol, hle, hlt⟩ := nrStep hg hs hn
      obtain ⟨U, k, a, hU, hsol', hnorm, hle'⟩ := ih _ (hlt.trans_le hq.le) hT hsol rfl
      exact ⟨U, k, a, hU, hsol', hnorm, hle'.trans hle⟩

def crPort (b : Bool) (i : ℕ) := if b then rport i else lport i

def crOriented (M : Finset ℕ) (b : Bool) (u v : ℕ) := if b then point M v u else point M u v

def crSide (M : Finset ℕ) (b : Bool) (u w : ℕ) := w = crPort b u ∨ (u ∉ M ∧ w = crPort (!b) u)

theorem crHit {M : Finset ℕ} {b : Bool} {u v w : ℕ} : crOriented M b u v w = true ↔ w = 0 ∨ crSide M b u w ∨ crSide M (!b) v w := by
  cases b <;> simp [crOriented, point, crSide, crPort] <;> tauto

theorem crEq {b c : Bool} {i j : ℕ} : crPort b i = crPort c j ↔ b = c ∧ i = j := by
  cases b <;> cases c <;> simp [crPort, lport, rport] <;> omega

theorem crNeZero (b : Bool) (i : ℕ) : crPort b i ≠ 0 := by cases b <;> simp [crPort, lport, rport]

theorem crDiag {i w : ℕ} {b : Bool} : point ∅ i i w = true ↔ w = 0 ∨ w = crPort b i ∨ w = crPort (!b) i := by
  cases b <;> simp [point, crPort] <;> tauto

theorem crDiagM {M : Finset ℕ} {i : ℕ} : point M i i = point ∅ i i := by
  funext w
  apply Bool.eq_iff_iff.mpr
  simp [point]; tauto

theorem crSolve {K M S : Finset ℕ} {g : Gates} {o : ℕ} (hs : Solves K M S g o) {b : Bool} {i j : ℕ} (hi : i ∈ K) (hj : j ∈ K) (hij : i ≠ j) : val S g (crOriented M b i j) o = true := by
  cases b <;> simp [crOriented, hs i hi j hj, hs j hj i hi, hij, Ne.symm hij]

theorem crDout {K M S : Finset ℕ} {g : Gates} {o : ℕ} (hs : Solves K M S g o) {i : ℕ} (hi : i ∈ K) : val S g (point ∅ i i) o = false := by simpa [crDiagM] using hs i hi i hi

theorem crAgainst {M : Finset ℕ} {b : Bool} {i j w : ℕ} (hi : i ∈ M) (hw : w ≠ crPort b i) (hx : crOriented M b i j w = true) : point ∅ j j w = true := by
  apply (crDiag (b := b)).2
  rw [crHit] at hx
  simp [crSide, hi, hw] at hx
  tauto

theorem crOff {M : Finset ℕ} {b : Bool} {i j : ℕ} (hi : i ∈ M) (hij : i ≠ j) : crOriented M b i j (crPort (!b) i) = false := by
  apply Bool.eq_false_iff.mpr
  simp [crHit, crSide, crEq, crNeZero, hi, hij]

theorem crGone {M : Finset ℕ} {b : Bool} {i u v : ℕ} (hu : u ≠ i) (hv : v ≠ i) : point M u v (crPort b i) = false := by
  cases b <;> simp [crPort, point, lport, rport] <;> omega

theorem crDiagPort (b : Bool) (i : ℕ) : point ∅ i i (crPort b i) = true := (crDiag (b := b)).2 (Or.inr (Or.inl rfl))

theorem crMerge {M : Finset ℕ} {b : Bool} {i u v : ℕ} (hp : point (M.erase i) u v (crPort b i) = true) {w : ℕ} (hw : point ∅ i i w = true) : point (M.erase i) u v w = true := by
  have h : u = i ∨ v = i := by by_contra! h; simp [crGone h.1 h.2] at hp
  rcases h with rfl | rfl <;> rcases (crDiag (b := false)).1 hw with rfl | rfl | rfl <;> simp [point, crPort]

def crReads (g : Gates) (t p : ℕ) := (g t).2.1 = p ∨ (g t).2.2 = p

theorem crView {g : Gates} {t p : ℕ} (h : crReads g t p) : ∃ W, ((g t).2.1 = p ∧ (g t).2.2 = W) ∨ ((g t).2.1 = W ∧ (g t).2.2 = p) := by
  rcases h with h | h
  · exact ⟨_, Or.inl ⟨h, rfl⟩⟩
  · exact ⟨_, Or.inr ⟨rfl, h⟩⟩

theorem crEval {H S g t p W} (hg : Good H S g) (ht : t ∈ S) (hf : ((g t).2.1 = p ∧ (g t).2.2 = W) ∨ ((g t).2.1 = W ∧ (g t).2.2 = p)) (x : ℕ → Bool) : val S g x t = bin (g t).1 (val S g x p) (val S g x W) := by
  rw [vin hg ht]; rcases hf with h | h <;> rw [h.1, h.2]
  cases (g t).1 <;> simp [bin, Bool.and_comm, Bool.or_comm]

theorem crLess {H S g t p W} (hg : Good H S g) (ht : t ∈ S) (hf : ((g t).2.1 = p ∧ (g t).2.2 = W) ∨ ((g t).2.1 = W ∧ (g t).2.2 = p)) : p < t ∧ W < t := by
  obtain ⟨_, ha, hb⟩ := hg t ht
  rcases hf with h | h <;> grind

theorem crCut {H S g} (hg : Good H S g) {x y : ℕ → Bool} {B : ℕ → Prop} {d : ℕ}
    (hraw : ∀ w, ¬B w → w ∉ S → x w = true → y w = true)
    (hgate : ∀ w ∈ S, w ≤ d → ¬B w → (B (g w).2.1 ∨ B (g w).2.2) → val S g x w = true → val S g y w = true)
    {w : ℕ} (hd : w ≤ d) (hw : ¬B w) (hx : val S g x w = true) : val S g y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hS : w ∈ S
    · by_cases ha : B (g w).2.1 ∨ B (g w).2.2
      · exact hgate w hS hd hw ha hx
      · push Not at ha
        obtain ⟨_, hl, hr⟩ := hg w hS
        have l := ih _ hl (by omega) ha.1
        have r := ih _ hr (by omega) ha.2
        rw [vin hg hS] at hx ⊢
        cases ho : (g w).1 <;> simp [bin, ho] at hx ⊢ <;> tauto
    · rw [vout hS] at hx ⊢; exact hraw _ hw hS hx

theorem crMono {H S g} (hg : Good H S g) {x y : ℕ → Bool} (h : ∀ w, x w = true → y w = true) {w : ℕ} (hx : val S g x w = true) : val S g y w = true :=
  crCut (B := fun _ => False) hg (fun w _ _ => h w) (by simp) (Nat.le_refl _) (by simp) hx

theorem crRaw {n S g i} (hg : Good (2*n+2) S g) (hi : i ∈ Finset.range n) (b : Bool) : crPort b i ∉ S := by
  intro h; have hz := (hg _ h).1; have := Finset.mem_range.mp hi
  cases b <;> simp [crPort, lport, rport] at hz <;> omega

theorem crZero {n S g} (hg : Good (2*n+2) S g) : 0 ∉ S := by intro h; have := (hg _ h).1; omega

theorem crTwo {K : Finset ℕ} {i : ℕ} (hi : i ∈ K) (h3 : 3 ≤ K.card) : ∃ j ∈ K, ∃ k ∈ K, j ≠ i ∧ k ≠ i ∧ j ≠ k := by
  have hc : 1 < (K.erase i).card := by rw [Finset.card_erase_of_mem hi]; omega
  obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp hc
  exact ⟨j, (Finset.mem_erase.mp hj).2, k, (Finset.mem_erase.mp hk).2, (Finset.mem_erase.mp hj).1, (Finset.mem_erase.mp hk).1, hjk⟩

theorem crOutput {K M S g o i j} (hs : Solves K M S g o) (hi : i ∈ K) (hj : j ∈ K) (hij : i ≠ j) : o ∈ S := by
  by_contra ho
  have hx := crSolve (b := false) hs hi hj hij
  rw [vout ho, crHit] at hx
  have a := crDout hs hi; have b := crDout hs hj
  rw [vout ho] at a b
  have aux (u : ℕ) (hu : point ∅ u u o = false) : ¬ (o = 0 ∨ o = crPort false u ∨ o = crPort true u) := fun h => by have := (crDiag (b := false)).2 h; simp_all
  have := aux i a; have := aux j b
  simp [crSide] at hx; tauto

theorem crSeen {n K M S g o i j} (hg : Good (2*n+2) S g) (hs : Solves K M S g o) (hi : i ∈ M) (him : i ∈ K) (hin : i ∈ Finset.range n) (hj : j ∈ K) (hij : i ≠ j) (b : Bool) : ∃ t ∈ S, crReads g t (crPort b i) := by
  by_contra! h
  have hout := crOutput hs him hj hij
  have ho : o ≠ crPort b i := fun e => crRaw hg hin b (e ▸ hout)
  have hz := crCut (B := fun w => w = crPort b i) hg (fun _ hw _ => crAgainst hi hw) (fun w hw _ _ hr => False.elim (h w hw hr)) (Nat.le_refl o) ho (crSolve (b := b) hs him hj hij)
  simp [crDout hs hj] at hz

theorem crKilled {n K M S g w p} (hg : Good (2*n+2) S g) (hw : w ∈ S) (hr : crReads g w p) (hz : ∀ u ∈ K, ∀ v ∈ K, val S g (point M u v) p = false) : Alias K M S g w := by
  obtain ⟨W, hf⟩ := crView hr
  obtain ⟨hp, hW⟩ := crLess hg hw hf
  cases he : (g w).1
  · refine ⟨W, hW, fun u hu v hv => ?_⟩; simp [crEval hg hw hf, hz u hu v hv, he, bin]
  · refine ⟨p, hp, fun u hu v hv => ?_⟩; simp [crEval hg hw hf, hz u hu v hv, he, bin]

theorem crDeadPort {n S g i w} {K M : Finset ℕ} (hg : Good (2*n+2) S g) (hin : i ∈ Finset.range n) (hw : w ∈ S) {b : Bool} (hr : crReads g w (crPort b i)) : Alias (K.erase i) (M.erase i) S g w := by
  apply crKilled hg hw hr
  intro u hu v hv; exact (vout (crRaw hg hin b)).trans (crGone (Finset.mem_erase.mp hu).1 (Finset.mem_erase.mp hv).1)

theorem crFour {S : Finset ℕ} {A : ℕ → Prop} {a b c d : ℕ} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (aa : A a) (ab : A b) (ac : A c) (ad : A d) : ∃ F : Finset ℕ, F ⊆ S ∧ 4 ≤ F.card ∧ ∀ w ∈ F, A w := by
  refine ⟨{a,b,c,d}, ?_, ?_, ?_⟩
  · intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl <;> assumption
  · simp [hab, hac, had, hbc, hbd, hcd]
  · intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl <;> assumption

theorem crSame {H K M S g t p W} (hg : Good H S g) (ht : t ∈ S) (hf : ((g t).2.1 = p ∧ (g t).2.2 = W) ∨ ((g t).2.1 = W ∧ (g t).2.2 = p)) (heq : ∀ u ∈ K, ∀ v ∈ K, val S g (point M u v) p = val S g (point M u v) W) : Alias K M S g t := by
  refine ⟨W, (crLess hg ht hf).2, fun u hu v hv => ?_⟩
  rw [crEval hg ht hf, heq u hu v hv]; cases (g t).1 <;> simp [bin]

theorem crPair {n K S g t i} {M : Finset ℕ} (hg : Good (2*n+2) S g) (hin : i ∈ Finset.range n) (ht : t ∈ S) (hL : crReads g t (crPort false i)) (hR : crReads g t (crPort true i)) : Alias K (M.erase i) S g t := by
  obtain ⟨W, hf⟩ := crView hL
  have he : W = crPort true i := by unfold crReads at hR; rcases hf with h | h <;> simp [h.1, h.2, crEq] at hR <;> exact hR
  subst W
  apply crSame hg ht hf
  intro u hu v hv; rw [vout (crRaw hg hin false), vout (crRaw hg hin true)]
  apply Bool.eq_iff_iff.mpr; constructor <;> intro h <;> exact crMerge h (crDiagPort _ i)

theorem crForce {n K M S g o i b t} (hg : Good (2*n+2) S g) (hs : Solves K M S g o) (hi : i ∈ M) (him : i ∈ K) (hin : i ∈ Finset.range n) (honly : ∀ w ∈ S, crReads g w (crPort b i) → w = t) {j} (hj : j ∈ K) (hij : i ≠ j) : val S g (crOriented M b i j) t = true ∧ val S g (point ∅ j j) t = false := by
  have ho : o ≠ crPort b i := fun e => crRaw hg hin b (e ▸ crOutput hs him hj hij)
  have hh : ¬(val S g (crOriented M b i j) t = true → val S g (point ∅ j j) t = true) := by
    intro h
    have hz := crCut (B := fun w => w = crPort b i) hg (fun _ hw _ => crAgainst hi hw) (fun w hw _ _ hr => honly w hw hr ▸ h) (Nat.le_refl o) ho (crSolve (b := b) hs him hj hij)
    simp [crDout hs hj] at hz
  simpa using hh

theorem crRest {n M S g t W i b j} (hg : Good (2*n+2) S g) (hi : i ∈ M) (honly : ∀ w ∈ S, crReads g w (crPort b i) → w = t) (hlt : W < t) (hne : W ≠ crPort b i) (hx : val S g (crOriented M b i j) W = true) (k : ℕ) : val S g (crOriented (M.erase i) b k j) W = true := by
  apply crCut (B := fun w => w = crPort b i) hg _ _ (Nat.le_refl W) hne hx
  · intro w hw _ hp
    rw [crHit] at hp ⊢
    simp [crSide, hi, hw] at hp
    simp [crSide]
    grind
  · intro w hw hle _ hr
    have := honly w hw hr; omega

theorem crNotBoth {g : Gates} {S : Finset ℕ} {i w : ℕ} (h : ¬∃ w ∈ S, crReads g w (crPort false i) ∧ crReads g w (crPort true i)) (hw : w ∈ S) {b : Bool} (hp : crReads g w (crPort b i)) : ¬crReads g w (crPort (!b) i) := by
  intro hq; apply h; refine ⟨w, hw, ?_⟩; cases b <;> simp_all

theorem crAndHard {n K M S g o i b t W} (hK : K ⊆ Finset.range n) (hi : i ∈ M) (him : i ∈ K) (h3 : 3 ≤ K.card)
    (hg : Good (2*n+2) S g) (hs : Solves K M S g o) (hn : Normal K S g)
    (ht : t ∈ S) (hp : crReads g t (crPort b i)) (honly : ∀ w ∈ S, crReads g w (crPort b i) → w = t)
    (hnq : ¬crReads g t (crPort (!b) i))
    (hf : ((g t).2.1 = crPort b i ∧ (g t).2.2 = W) ∨ ((g t).2.1 = W ∧ (g t).2.2 = crPort b i))
    (hop : (g t).1 = true) (hW : W ≠ crPort b i) (hd : val S g (point ∅ i i) W = false) :
    ∃ F : Finset ℕ, F ⊆ S ∧ 4 ≤ F.card ∧ ∀ w ∈ F, Alias (K.erase i) (M.erase i) S g w := by
  have hin := hK him
  have hlt := (crLess hg ht hf).2
  have raw := crRaw hg hin b
  have qraw := crRaw hg hin (!b)
  obtain ⟨j, hj, k, hk, hji, hki, hjk⟩ := crTwo him h3
  have hpos (a : ℕ) (ha : a ∈ K) (hia : i ≠ a) : val S g (crOriented M b i a) W = true := by
    have h := (crForce hg hs hi him hin honly ha hia).1
    rw [crEval hg ht hf, hop] at h; exact (Bool.and_eq_true_iff.mp h).2
  have hgate : W ∈ S := by
    by_contra h
    have a := hpos j hj hji.symm; have c := hpos k hk hki.symm
    rw [vout h] at a c hd
    have hjd := (crDiag (b := b)).1 (crAgainst hi hW a)
    have hkd := (crDiag (b := b)).1 (crAgainst hi hW c)
    have h0 : W ≠ 0 := fun e => by simp [e, point] at hd
    rcases hjd with z | z | z <;> rcases hkd with y | y | y <;> first | exact h0 z | exact h0 y | exact hjk (crEq.mp (z.symm.trans y)).2
  have hOne (u : ℕ) (hu : u ∈ K.erase i) (v : ℕ) (hv : v ∈ K.erase i) : val S g (point (M.erase i) u v) W = true := by
    obtain ⟨hu', huK⟩ := Finset.mem_erase.mp hu
    obtain ⟨hv', hvK⟩ := Finset.mem_erase.mp hv
    cases b
    · exact crRest hg hi honly hlt hW (hpos v hvK hv'.symm) u
    · exact crRest hg hi honly hlt hW (hpos u huK hu'.symm) v
  have hAW : Alias (K.erase i) (M.erase i) S g W := by
    refine ⟨0, ?_, fun u hu v hv => ?_⟩
    · have := (hg W hgate).1; omega
    · simp [vout (crZero hg), point, hOne u hu v hv]
  have hDark : Dark K S g t := by
    intro a ha; rw [crEval hg ht hf, hop, vout raw]
    by_cases he : a = i
    · subst a; simp [hd, bin]
    · simp [crGone he he, bin]
  have hDead (u : ℕ) (hu : u ∈ K.erase i) (v : ℕ) (hv : v ∈ K.erase i) : val S g (point (M.erase i) u v) t = false := by
    simp [crEval hg ht hf, hop, bin, vout raw, crGone (Finset.mem_erase.mp hu).1 (Finset.mem_erase.mp hv).1]
  have hWq : ¬crReads g W (crPort (!b) i) := by
    intro h; obtain ⟨V, hv⟩ := crView h
    cases he : (g W).1
    · simp [crEval hg hgate hv, he, bin, vout qraw, crDiagPort] at hd
    · have hz := hpos j hj hji.symm
      simp [crEval hg hgate hv, he, bin, vout qraw, crOff hi hji.symm] at hz
  have ho : o ≠ t := by
    intro e; have hz := hs j hj k hk
    simp [e, hjk, crEval hg ht hf, hop, bin, vout raw, crGone hji hki] at hz
  have hor : o ≠ crPort b i := fun e => raw (e ▸ crOutput hs hj hk hjk)
  have hr : ∃ a ∈ S, crReads g a t ∧ ¬crReads g a (crPort (!b) i) := by
    by_contra! h
    have hnDark (a : ℕ) (ha : a ∈ S) (hat : crReads g a t) : Dark K S g a := by
      apply hn a ha; rcases hat with e | e
      · exact Or.inl (e ▸ hDark)
      · exact Or.inr (e ▸ hDark)
    have hz := crCut (B := fun w => w = crPort b i ∨ w = t) hg
      (fun _ hw _ => crAgainst hi (fun e => hw (Or.inl e)))
      (d := o) (x := crOriented M b i j) (y := point ∅ j j) (by
        intro a ha _ hao hr hx
        have hat : crReads g a t := by
          by_contra H
          have har : crReads g a (crPort b i) := by unfold crReads at H ⊢; tauto
          exact hao (Or.inr (honly a ha har))
        have haq := h a ha hat
        obtain ⟨V, hv⟩ := crView haq
        cases he : (g a).1
        · have hdi := hnDark a ha hat i him
          simp [crEval hg ha hv, he, bin, vout qraw, crDiagPort] at hdi
        · simp [crEval hg ha hv, he, bin, vout qraw, crOff hi hji.symm] at hx)
      (Nat.le_refl _) (not_or_intro hor ho) (crSolve (b := b) hs him hj hji.symm)
    simp [crDout hs hj] at hz
  obtain ⟨a, ha, hat, haq⟩ := hr
  obtain ⟨d, hdS, hdq⟩ := crSeen hg hs hi him hin hj hji.symm (!b)
  have hta : t < a := by obtain ⟨V, hv⟩ := crView hat; exact (crLess hg ha hv).1
  exact crFour hgate ht ha hdS (by omega) (by omega) (fun e => hWq (e ▸ hdq)) (by omega) (fun e => hnq (e ▸ hdq)) (fun e => haq (e ▸ hdq)) hAW (crDeadPort hg hin ht hp) (crKilled hg ha hat hDead) (crDeadPort hg hin hdS hdq)

theorem crUnique {n K M S g o i b t} (hK : K ⊆ Finset.range n) (hi : i ∈ M) (him : i ∈ K) (h3 : 3 ≤ K.card)
    (hg : Good (2*n+2) S g) (hs : Solves K M S g o) (hn : Normal K S g)
    (ht : t ∈ S) (hp : crReads g t (crPort b i)) (honly : ∀ w ∈ S, crReads g w (crPort b i) → w = t)
    (hnq : ¬crReads g t (crPort (!b) i)) :
    (∃ w ∈ S, Alias K (M.erase i) S g w) ∨ ∃ F : Finset ℕ, F ⊆ S ∧ 4 ≤ F.card ∧ ∀ w ∈ F, Alias (K.erase i) (M.erase i) S g w := by
  obtain ⟨W, hf⟩ := crView hp
  have hin := hK him
  have raw := crRaw hg hin b
  by_cases he : W = crPort b i
  · exact Or.inl ⟨t, ht, crSame hg ht hf (fun _ _ _ _ => congrArg _ he.symm)⟩
  have hsoft (hd : val S g (point ∅ i i) W = true) (u v : ℕ) (h : val S g (point (M.erase i) u v) (crPort b i) = true) : val S g (point (M.erase i) u v) W = true := by
    rw [vout raw] at h; exact crMono hg (fun _ => crMerge h) hd
  cases hop : (g t).1
  · have hnd : ¬Dark K S g W := by
      intro hd
      have hh : Dark K S g t := by
        apply hn t ht; rcases hf with h | h
        · exact Or.inr (h.2 ▸ hd)
        · exact Or.inl (h.1 ▸ hd)
      have h := hh i him
      simp [crEval hg ht hf, hop, bin, vout raw, crDiagPort] at h
    unfold Dark at hnd; push Not at hnd
    obtain ⟨a, ha, hwa⟩ := hnd
    have e : a = i := by
      by_contra h
      have hz := (crForce hg hs hi him hin honly ha (Ne.symm h)).2
      simp [crEval hg ht hf, hop, bin, hwa] at hz
    subst a
    refine Or.inl ⟨t, ht, W, (crLess hg ht hf).2, fun u hu v hv => ?_⟩
    rw [crEval hg ht hf, hop]
    have h := hsoft (by simpa using hwa) u v
    cases e : val S g (point (M.erase i) u v) (crPort b i) <;> simp_all [bin]
  · cases hd : val S g (point ∅ i i) W
    · exact Or.inr (crAndHard hK hi him h3 hg hs hn ht hp honly hnq hf hop he hd)
    · refine Or.inl ⟨t, ht, crPort b i, (crLess hg ht hf).1, fun u hu v hv => ?_⟩
      rw [crEval hg ht hf, hop]
      have h := hsoft hd u v
      cases e : val S g (point (M.erase i) u v) (crPort b i) <;> simp_all [bin]

theorem crStep {n : ℕ} {K M S : Finset ℕ} {g : Gates} {o i : ℕ} (hK : K ⊆ Finset.range n) (hM : M ⊆ K) (hi : i ∈ M) (h3 : 3 ≤ K.card) (hg : Good (2*n+2) S g) (hs : Solves K M S g o) (hn : Normal K S g) : (∃ w ∈ S, Alias K (M.erase i) S g w) ∨ ∃ F : Finset ℕ, F ⊆ S ∧ 4 ≤ F.card ∧ ∀ w ∈ F, Alias (K.erase i) (M.erase i) S g w := by
  have him := hM hi
  have hin := hK him
  by_cases hp : ∃ w ∈ S, crReads g w (crPort false i) ∧ crReads g w (crPort true i)
  · obtain ⟨w, hw, hl, hr⟩ := hp
    exact Or.inl ⟨w, hw, crPair hg hin hw hl hr⟩
  obtain ⟨j, hj, _, _, hji, _, _⟩ := crTwo him h3
  obtain ⟨a, ha, al⟩ := crSeen hg hs hi him hin hj hji.symm false
  obtain ⟨c, hc, cr⟩ := crSeen hg hs hi him hin hj hji.symm true
  by_cases au : ∀ w ∈ S, crReads g w (crPort false i) → w = a
  · exact crUnique hK hi him h3 hg hs hn ha al au (crNotBoth hp ha al)
  by_cases cu : ∀ w ∈ S, crReads g w (crPort true i) → w = c
  · exact crUnique hK hi him h3 hg hs hn hc cr cu (crNotBoth hp hc cr)
  push Not at au cu
  obtain ⟨b, hb, bl, hba⟩ := au
  obtain ⟨d, hd, dr, hdc⟩ := cu
  have dis : ∀ x ∈ S, crReads g x (crPort false i) → ∀ y, crReads g y (crPort true i) → x ≠ y := by
    intro x hx hl y hr e; subst y; exact hp ⟨_, hx, hl, hr⟩
  exact Or.inr (crFour ha hb hc hd hba.symm (dis a ha al c cr) (dis a ha al d dr) (dis b hb bl c cr) (dis b hb bl d dr) hdc.symm (crDeadPort hg hin ha al) (crDeadPort hg hin hb bl) (crDeadPort hg hin hc cr) (crDeadPort hg hin hd dr))

def bypass (F : Finset ℕ) (r : ℕ → ℕ) (w : ℕ) : ℕ :=
  if w ∈ F ∧ r w < w then bypass F r (r w) else w
termination_by w

theorem bypass_le (F : Finset ℕ) (r : ℕ → ℕ) (w : ℕ) : bypass F r w ≤ w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rw [bypass]
    split_ifs with hw
    · exact (ih _ hw.2).trans hw.2.le
    · rfl

theorem prune {H : ℕ} {K M S F : Finset ℕ} {g : Gates} {o : ℕ}
    (hg : Good H S g) (hs : Solves K M S g o) (_hF : F ⊆ S) (ha : ∀ w ∈ F, Alias K M S g w) :
    ∃ h : Gates, ∃ p : ℕ, Good H (S \ F) h ∧ Solves K M (S \ F) h p := by
  classical
  let r (w : ℕ) := if hw : w ∈ F then (ha w hw).choose else w
  have hr w (hw : w ∈ F) : r w < w ∧ ∀ u ∈ K, ∀ v ∈ K,
      val S g (point M u v) w = val S g (point M u v) (r w) := by
    simpa only [r, dite_eq_left hw] using (ha w hw).choose_spec
  let d := bypass F r
  let h (w : ℕ) := ((g w).1, d (g w).2.1, d (g w).2.2)
  have hh : Good H (S \ F) h := by
    intro w hw
    have hw' := hg w (Finset.mem_sdiff.mp hw).1
    exact ⟨hw'.1, (bypass_le ..).trans_lt hw'.2.1, (bypass_le ..).trans_lt hw'.2.2⟩
  refine ⟨h, d o, hh, ?_⟩
  intro u hu v hv
  suffices ∀ w, val (S \ F) h (point M u v) (d w) = val S g (point M u v) w by
    rw [this, hs u hu v hv]
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hf : w ∈ F
    · have he : d w = d (r w) := by rw [show d w = bypass F r w from rfl, bypass, ite_eq_left ⟨hf, (hr w hf).1⟩]
      rw [he, ih _ (hr w hf).1, (hr w hf).2 u hu v hv]
    · have he : d w = w := by rw [show d w = bypass F r w from rfl, bypass, ite_eq_right (fun h => hf h.1)]
      rw [he]
      by_cases hw : w ∈ S
      · rw [vin hh (Finset.mem_sdiff.mpr ⟨hw, hf⟩), vin hg hw]
        change bin _ (val _ _ _ (d _)) (val _ _ _ (d _)) = _
        rw [ih _ (hg w hw).2.1, ih _ (hg w hw).2.2]
      · rw [vout hw, vout (fun (e : w ∈ S \ F) => hw (Finset.mem_sdiff.mp e).1)]

theorem bin_mono {op a b c d : Bool} (ha : a = true → c = true) (hb : b = true → d = true) :
    bin op a b = true → bin op c d = true := by
  cases op <;> simp [bin] <;> tauto

theorem val_mono {H S g} (hg : Good H S g) {x y : ℕ → Bool} (hxy : ∀ w, x w = true → y w = true) :
    ∀ w, val S g x w = true → val S g y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w ∈ S
    · rw [vin hg hw, vin hg hw]
      exact bin_mono (ih _ (hg w hw).2.1) (ih _ (hg w hw).2.2)
    · simpa only [vout hw] using hxy w

theorem point_grow {M : Finset ℕ} {i u v w : ℕ} (ht : point M u v w = true) :
    point (M.erase i) u v w = true := by
  simp [point] at ht ⊢
  tauto

theorem point_diag (M : Finset ℕ) (i w : ℕ) : point M i i w = point ∅ i i w := by
  unfold point
  rw [decide_eq_decide]
  simp only [Finset.notMem_empty]
  tauto

theorem merge_solves {H K M S g o} (hg : Good H S g) (hs : Solves K M S g o) (i : ℕ) :
    Solves K (M.erase i) S g o := by
  intro u hu v hv
  have h0 := hs u hu v hv
  by_cases huv : u = v
  · subst v
    simpa only [funext (point_diag M u), funext (point_diag (M.erase i) u)] using h0
  · simpa only [decide_eq_true huv] using val_mono hg (fun _ => point_grow) o (by simpa [huv] using h0)

theorem delete_solves {H K M S g o} (hg : Good H S g) (hs : Solves K M S g o) (i : ℕ) :
    Solves (K.erase i) (M.erase i) S g o := by
  intro u hu v hv
  exact merge_solves hg hs i u (Finset.mem_of_mem_erase hu) v (Finset.mem_of_mem_erase hv)

def plug (g : Gates) (z : ℕ) (t : Bool × ℕ × ℕ) : Gates := fun w => if w = z then t else g w

theorem plug_good {S H g} (hg : Good H S g) {z a b : ℕ} (hz : z ∉ S)
    (hzH : H ≤ z) (ha : a < z) (hb : b < z) (op : Bool) :
    Good H (insert z S) (plug g z (op, a, b)) := by
  intro w hw
  rcases Finset.mem_insert.mp hw with rfl | hw
  · simpa [plug] using And.intro hzH (And.intro ha hb)
  · have hne : w ≠ z := fun e => hz (e ▸ hw)
    simpa [plug, hne] using hg w hw

theorem plug_old {S H g} (hg : Good H S g) {z a b : ℕ} {op : Bool}
    (hg' : Good H (insert z S) (plug g z (op,a,b))) (x : ℕ → Bool) (w : ℕ) (hw : w < z) :
    val (insert z S) (plug g z (op,a,b)) x w = val S g x w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    have hn := Nat.ne_of_lt hw
    by_cases h : w ∈ S
    · rw [vin hg' (Finset.mem_insert_of_mem h), vin hg h]
      simp only [plug, ite_eq_right hn]
      rw [ih _ (hg w h).2.1 ((hg w h).2.1.trans hw), ih _ (hg w h).2.2 ((hg w h).2.2.trans hw)]
    · rw [vout h, vout (by simp [hn,h] : w ∉ insert z S)]

theorem plug_new {S H g} (hg : Good H S g) {z a b : ℕ} {op : Bool} (ha : a < z) (hb : b < z)
    (hg' : Good H (insert z S) (plug g z (op,a,b))) (x : ℕ → Bool) :
    val (insert z S) (plug g z (op,a,b)) x z = bin op (val S g x a) (val S g x b) := by
  rw [vin hg' (Finset.mem_insert_self ..)]
  simp only [plug, ite_true]
  rw [plug_old hg hg' x a ha, plug_old hg hg' x b hb]

theorem point_full (u v w : ℕ) : point ∅ u v w = true ↔
    w = 0 ∨ w = lport u ∨ w = rport u ∨ w = lport v ∨ w = rport v := by
  simp only [point, decide_eq_true_eq, Finset.notMem_empty]
  tauto

theorem left_full (u v i : ℕ) : point ∅ u v (lport i) = true ↔ i = u ∨ i = v := by
  rw [point_full]
  unfold lport rport
  omega

def moved (H i j w : ℕ) := if w < H then
    if w = lport i ∨ w = rport i then 1 else if w = lport j ∨ w = rport j then H else w
  else w+1

theorem move_lt {H i j w k : ℕ} (_hH : 2 ≤ H) (hk : H ≤ k) (hw : w < k) : moved H i j w < k+1 := by
  unfold moved
  split_ifs <;> omega

theorem extend {n : ℕ} {K S : Finset ℕ} {i j o : ℕ} {g : Gates} (hK : K ⊆ Finset.range n)
    (hi : i ∈ K) (hj : j ∈ K) (hij : i ≠ j) (hg : Good (2*n+2) S g) (hs : Solves (K.erase i) ∅ S g o) :
    ∃ T : Finset ℕ, ∃ h : Gates, ∃ p : ℕ, Good (2*n+2) T h ∧ Solves K ∅ T h p ∧ T.card ≤ S.card + 3 := by
  classical
  let H := 2*n+2
  have li : lport i < H := by have := Finset.mem_range.mp (hK hi); dsimp [lport,H]; omega
  have lj : lport j < H := by have := Finset.mem_range.mp (hK hj); dsimp [lport,H]; omega
  let m := moved H i j
  let T := insert H (S.image Nat.succ)
  let h : Gates := fun w => if w = H then (false,lport i,lport j) else
    ((g (w-1)).1,m (g (w-1)).2.1,m (g (w-1)).2.2)
  have hp (w : ℕ) (hw : w < H) : w ∉ T := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with e | hh
    · omega
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hh
    have : H ≤ k := (hg k hk).1
    omega
  have hT : Good H T h := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simpa [h] using And.intro (le_refl H) (And.intro li lj)
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hkg,ha,hb⟩ := hg k hk
    change H ≤ k at hkg
    have hne : k.succ ≠ H := by omega
    simp only [h, ite_eq_right hne, Nat.succ_sub_one]
    exact ⟨by omega, move_lt (by dsimp [H]; omega) hkg ha, move_lt (by dsimp [H]; omega) hkg hb⟩
  let f (k : ℕ) := if k = i then j else k
  have fm {k : ℕ} (hk : k ∈ K) : f k ∈ K.erase i := by
    by_cases e : k = i <;> simp [f,e,Finset.mem_erase,hij.symm,hj,hk]
  have sim (u v : ℕ) (hu : u ∈ K) (hv : v ∈ K) (w : ℕ) :
      val T h (point ∅ u v) (m w) = val S g (point ∅ (f u) (f v)) w := by
    have un := Finset.mem_range.mp (hK hu)
    have vn := Finset.mem_range.mp (hK hv)
    have fun' := Finset.mem_range.mp (hK (Finset.mem_of_mem_erase (fm hu)))
    have fvn := Finset.mem_range.mp (hK (Finset.mem_of_mem_erase (fm hv)))
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hw : w ∈ S
      · obtain ⟨hkg,ha,hb⟩ := hg w hw
        change H ≤ w at hkg
        have hm : m w = w+1 := by simp [m,moved, Nat.not_lt.mpr hkg]
        have hws : w+1 ∈ T := Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w,hw,rfl⟩)
        have hne : w+1 ≠ H := by omega
        rw [hm,vin hT hws,vin hg hw]
        simp only [h,ite_eq_right hne,Nat.add_sub_cancel]
        rw [ih _ ha, ih _ hb]
      · rw [vout hw]
        by_cases hx : w < H
        · by_cases h1 : w = lport i ∨ w = rport i
          · have hm : m w = 1 := by simp [m,moved,hx,h1]
            rw [hm,vout (hp _ (by dsimp [H]; omega)),Bool.eq_iff_iff,point_full,point_full]
            have hfi := (Finset.mem_erase.mp (fm hu)).1
            have hfj := (Finset.mem_erase.mp (fm hv)).1
            unfold lport rport at *
            omega
          · by_cases h2 : w = lport j ∨ w = rport j
            · have hm : m w = H := by simp [m,moved,hx,h1,h2]
              rw [hm,vin hT (Finset.mem_insert_self ..)]
              simp only [h,ite_eq_left rfl,bin,Bool.false_eq_true,ite_false]
              rw [vout (hp _ li),vout (hp _ lj),Bool.eq_iff_iff,Bool.or_eq_true,left_full,left_full,point_full]
              dsimp [f,lport,rport] at *
              split_ifs <;> omega
            · have hm : m w = w := by simp [m,moved,hx,h1,h2]
              rw [hm,vout (hp _ hx),Bool.eq_iff_iff,point_full,point_full]
              unfold f
              split_ifs <;> grind
        · have hm : m w = w+1 := by simp [m,moved,hx]
          have ht : w+1 ∉ T := by
            intro he
            rcases Finset.mem_insert.mp he with he | he
            · omega
            obtain ⟨k,hk,hke⟩ := Finset.mem_image.mp he
            exact hw (Nat.succ.inj hke ▸ hk)
          rw [hm,vout ht,Bool.eq_iff_iff,point_full,point_full]
          dsimp [H,lport,rport] at *
          omega
  let z := max (max (T.sup id) H) (m o) + 1
  have zS : z ∉ T := fun hz => by have hle : z ≤ T.sup id := Finset.le_sup (f := id) hz; dsimp [z] at hle; omega
  have zH : H < z := by dsimp [z]; omega
  have zo : m o < z := by dsimp [z]; omega
  let h1 := plug h z (true,lport i,lport j)
  have hg1 : Good H (insert z T) h1 := plug_good hT zS zH.le (li.trans zH) (lj.trans zH) true
  have z1S : z+1 ∉ insert z T := by
    simp only [Finset.mem_insert,not_or]
    refine ⟨by omega, fun hz => ?_⟩
    have hle : z+1 ≤ T.sup id := Finset.le_sup (f := id) hz
    dsimp [z] at hle
    omega
  let h2 := plug h1 (z+1) (false,z,m o)
  have hg2 : Good H (insert (z+1) (insert z T)) h2 := plug_good hg1 z1S (by omega) (by omega) (by omega) false
  refine ⟨_,h2,z+1,hg2,?_,?_⟩
  · intro u hu v hv
    rw [plug_new hg1 (by omega) (by omega) hg2, plug_new hT (li.trans zH) (lj.trans zH) hg1,
      vout (hp _ li),vout (hp _ lj),plug_old hT hg1 _ _ zo,sim u v hu hv,hs _ (fm hu) _ (fm hv)]
    rw [Bool.eq_iff_iff]
    simp only [bin,ite_true,Bool.false_eq_true,ite_false,Bool.or_eq_true,Bool.and_eq_true,left_full,decide_eq_true_eq]
    dsimp [f]
    split_ifs <;> omega
  · have ht := Finset.card_insert_le H (S.image Nat.succ)
    have ht' := Finset.card_image_le (s := S) (f := Nat.succ)
    rw [Finset.card_insert_of_notMem z1S, Finset.card_insert_of_notMem zS]
    change (insert H (S.image Nat.succ)).card + 1 + 1 ≤ _
    omega

theorem frontier {H S g} (hg : Good H S g) (k : ℕ) (T : Finset ℕ) (hT : ∀ w ∈ T, w ∈ S → w < k) :
    ∃ U : Finset ℕ, U.card ≤ T.card + ((Finset.range k).filter (· ∈ S)).card ∧
      ∀ x y : ℕ → Bool, (∀ w ∈ U, x w = true → y w = true) →
        ∀ w ∈ T, val S g x w = true → val S g y w = true := by
  classical
  induction k generalizing T with
  | zero =>
    refine ⟨T,by simp,?_⟩
    intro x y hxy w hw
    have hn : w ∉ S := fun e => Nat.not_lt_zero _ (hT w hw e)
    simpa only [vout hn] using hxy w hw
  | succ k ih =>
    have step : ((Finset.range k).filter (· ∈ S)).card ≤ ((Finset.range (k+1)).filter (· ∈ S)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))
    by_cases h : k ∈ T ∧ k ∈ S
    · obtain ⟨hkt,hks⟩ := h
      let a := (g k).2.1
      let b := (g k).2.2
      let T' := insert a (insert b (T.erase k))
      have ha : a < k := (hg k hks).2.1
      have hb : b < k := (hg k hks).2.2
      obtain ⟨U,hU,hs⟩ := ih T' (by
        intro w hw hwS
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact ha
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact hb
        have h' := Finset.mem_erase.mp hw
        have := hT w h'.2 hwS
        omega)
      refine ⟨U,?_,?_⟩
      · have c1 := Finset.card_insert_le a (insert b (T.erase k))
        have c2 := Finset.card_insert_le b (T.erase k)
        have c3 := Finset.card_erase_add_one hkt
        change U.card ≤ (insert a (insert b (T.erase k))).card + _ at hU
        rw [Finset.range_add_one,Finset.filter_insert]
        have eh : k ∉ (Finset.range k).filter (· ∈ S) := by simp
        rw [ite_eq_left hks,Finset.card_insert_of_notMem eh]
        omega
      · intro x y hxy w hw
        by_cases he : w = k
        · subst w
          rw [vin hg hks,vin hg hks]
          exact bin_mono (hs x y hxy a (Finset.mem_insert_self ..))
            (hs x y hxy b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..)))
        · exact hs x y hxy w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨he,hw⟩)))
    · obtain ⟨U,hU,hs⟩ := ih T (by
        intro w hw hws
        have := hT w hw hws
        have hne : w ≠ k := fun e => h ⟨e ▸ hw, e ▸ hws⟩
        omega)
      exact ⟨U,by omega,hs⟩

theorem input_bound {H : ℕ} {K M S : Finset ℕ} {g : Gates} {o : ℕ} (hk : 2 ≤ K.card)
    (hm : M ⊆ K) (hg : Good H S g) (hs : Solves K M S g o) :
    K.card + M.card ≤ S.card + 1 := by
  classical
  obtain ⟨U,hu,hsup⟩ := frontier hg (o+1) {o} (by simp)
  have cc : U.card ≤ S.card+1 := by
    have : ((Finset.range (o+1)).filter (· ∈ S)).card ≤ S.card :=
      Finset.card_le_card fun k h => (Finset.mem_filter.mp h).2
    simp only [Finset.card_singleton] at hu
    omega
  have wit (i j : ℕ) (hi : i ∈ K) (hj : j ∈ K) (hne : i ≠ j) :
      (∃ w ∈ U, w = lport i ∨ (i ∉ M ∧ w = rport i)) ∧
      (∃ w ∈ U, w = rport i ∨ (i ∉ M ∧ w = lport i)) := by
    have left_bad (a b : ℕ) (ha : a ∈ K) (hb : b ∈ K) (hab : a ≠ b) :
        ∃ w ∈ U, point M a b w = true ∧ point M j j w = false := by
      by_contra! hn
      have ff := hsup (point M a b) (point M j j) (by
        intro w hw ht
        simpa using hn w hw ht) o (Finset.mem_singleton_self o) (by rw [hs a ha b hb]; simp [hab])
      simp [hs j hj j hj] at ff
    constructor
    · obtain ⟨w,hw,h1,h2⟩ := left_bad i j hi hj hne
      refine ⟨w,hw,?_⟩
      simp [point] at h1 h2
      tauto
    · obtain ⟨w,hw,h1,h2⟩ := left_bad j i hj hi hne.symm
      refine ⟨w,hw,?_⟩
      simp [point] at h1 h2
      tauto
  let f (i : ℕ) := if lport i ∈ U then lport i else rport i
  have grab (i : ℕ) (hi : i ∈ K) : f i ∈ U ∧ (i ∈ M → lport i ∈ U ∧ rport i ∈ U) := by
    obtain ⟨j,hj⟩ := Finset.card_pos.mp (show 0 < (K.erase i).card by have := Finset.card_erase_add_one hi; omega)
    obtain ⟨h1,h2⟩ := wit i j hi (Finset.mem_of_mem_erase hj) (Finset.mem_erase.mp hj).1.symm
    obtain ⟨a,ha,ha'⟩ := h1
    obtain ⟨b,hb,hb'⟩ := h2
    dsimp only [f]
    split_ifs <;> grind
  have fits : K.image f ∪ M.image rport ⊆ U := by
    intro w hw
    rcases Finset.mem_union.mp hw with hl | hr
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hl
      exact (grab i hi).1
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hr
      exact ((grab i (hm hi)).2 hi).2
  have dis : Disjoint (K.image f) (M.image rport) := by
    rw [Finset.disjoint_left]
    rintro _ hw hl
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hl
    have hj' := ((grab j (hm hj)).2 hj).1
    dsimp only [f] at he
    split_ifs at he with h
    · unfold lport rport at he
      omega
    · have : j = i := by unfold rport at he; omega
      subst j
      exact h hj'
  have inj : Function.Injective f := by
    intro i j he
    dsimp only [f] at he
    split_ifs at he <;> unfold lport rport at * <;> omega
  have inj' : Function.Injective rport := by intro i j he; unfold rport at he; omega
  have ct := Finset.card_le_card fits
  rw [Finset.card_union_of_disjoint dis, Finset.card_image_of_injective _ inj,Finset.card_image_of_injective _ inj'] at ct
  omega

theorem base_two {n : ℕ} {K M S : Finset ℕ} {g : Gates} {o : ℕ}
    (hK : K ⊆ Finset.range n) (hm : M ⊆ K) (hk : K.card = 2)
    (hg : Good (2*n+2) S g) (hs : Solves K M S g o) :
    ∃ T : Finset ℕ, ∃ h : Gates, ∃ p : ℕ, Good (2*n+2) T h ∧ Solves K ∅ T h p ∧ T.card + M.card ≤ S.card := by
  have cb := input_bound (by omega : 2 ≤ K.card) hm hg hs
  obtain ⟨i,j,hij,hpair⟩ := Finset.card_eq_two.mp hk
  have hi : i < n := Finset.mem_range.mp (hK (by simp [hpair]))
  have hj : j < n := Finset.mem_range.mp (hK (by simp [hpair]))
  let H := 2*n+2
  let h : Gates := fun _ => (true,lport i,lport j)
  have li : lport i < H := by dsimp [lport,H]; omega
  have lj : lport j < H := by dsimp [lport,H]; omega
  have hgood : Good H {H} h := by
    intro w hw
    obtain rfl := Finset.mem_singleton.mp hw
    exact ⟨le_rfl,li,lj⟩
  refine ⟨{H},h,H,hgood,?_,by simp only [Finset.card_singleton]; omega⟩
  intro u hu v hv
  rw [vin hgood (Finset.mem_singleton_self H)]
  change bin true (val {H} h _ (lport i)) (val {H} h _ (lport j)) = _
  rw [vout (by simpa using li.ne : lport i ∉ ({H} : Finset ℕ)), vout (by simpa using lj.ne : lport j ∉ ({H} : Finset ℕ)),Bool.eq_iff_iff]
  simp only [bin,ite_true,Bool.and_eq_true,left_full,decide_eq_true_eq]
  simp only [hpair,Finset.mem_insert,Finset.mem_singleton] at hu hv
  omega

theorem discount {n : ℕ} {K M S : Finset ℕ} {g : Gates} {o : ℕ}
    (hK : K ⊆ Finset.range n) (hm : M ⊆ K) (hk : 2 ≤ K.card)
    (hg : Good (2*n+2) S g) (hs : Solves K M S g o) :
    ∃ T : Finset ℕ, ∃ h : Gates, ∃ p : ℕ, Good (2*n+2) T h ∧ Solves K ∅ T h p ∧ T.card + M.card ≤ S.card := by
  classical
  generalize hc : M.card = c
  induction c using Nat.strong_induction_on generalizing K M S g o with
  | ind c ih =>
    by_cases h0 : M = ∅
    · subst M
      exact ⟨S,g,o,hg,hs,by simp [← hc]⟩
    by_cases hk2 : K.card = 2
    · simpa only [← hc] using base_two hK hm hk2 hg hs
    have hk3 : 3 ≤ K.card := by omega
    obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr h0
    have cm := Finset.card_erase_add_one hi
    have ck := Finset.card_erase_add_one (hm hi)
    have clt : (M.erase i).card < c := by omega
    obtain ⟨N,d,q,hd,hq,hn,cs⟩ := nrNormalize hg hs
    rcases crStep hK hm hi hk3 hd hq hn with ⟨w,hw,ha⟩ | ⟨F,hF,cf,ha⟩
    · have hf : {w} ⊆ N := Finset.singleton_subset_iff.mpr hw
      obtain ⟨d',q',hd',hq'⟩ := prune hd (merge_solves hd hq i) hf (by simpa using ha)
      obtain ⟨T,h,p,ht,hp,ct⟩ := ih _ clt hK ((Finset.erase_subset i M).trans hm) hk hd' hq' rfl
      have ce := Finset.card_sdiff_add_card_eq_card hf
      simp only [Finset.card_singleton] at ce
      exact ⟨T,h,p,ht,hp,by omega⟩
    · obtain ⟨d',q',hd',hq'⟩ := prune hd (delete_solves hd hq i) hF ha
      have hkm : K.erase i ⊆ Finset.range n := (Finset.erase_subset i K).trans hK
      have hmm : M.erase i ⊆ K.erase i := Finset.erase_subset_erase i hm
      obtain ⟨T,h,p,ht,hp,ct⟩ := ih _ clt hkm hmm (by omega) hd' hq' rfl
      obtain ⟨j,hj⟩ := Finset.card_pos.mp (show 0 < (K.erase i).card by omega)
      obtain ⟨T',h',p',ht',hp',ct'⟩ := extend hK (hm hi) (Finset.mem_of_mem_erase hj) (Finset.mem_erase.mp hj).1.symm ht hp
      have ce := Finset.card_sdiff_add_card_eq_card hF
      exact ⟨T',h',p',ht',hp',by omega⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ioRun (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem ioSnoc (gs : List Gate) (g : Gate) (x : List Bool) :
    ioRun (gs ++ [g]) x = ioRun gs x ++ [g.op.eval (g.inputs.map fun i => (ioRun gs x).getD i false)] := by
  simp [ioRun, List.foldl_append]

theorem ioLen (gs : List Gate) (x : List Bool) : (ioRun gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [ioRun]
  | append_singleton gs g ih => rw [ioSnoc]; simp [ih]; omega

theorem ioGet (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem ioLast (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem ioPrefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (ioRun (gs ++ hs) x).getD i false = (ioRun gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, ioSnoc, ioGet _ _ _ (by rw [ioLen, List.length_append]; omega), ih]

theorem ioInput (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (ioRun gs x).getD i false = x.getD i false := by
  simpa [ioRun] using ioPrefix [] gs x i (by simpa using hi)

theorem ioGate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (ioRun gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (ioRun gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen := ioLen gs x
    have same (k : ℕ) (hk : k ≤ gs.length) (l : List ℕ) :
        (l.map fun i => if i < x.length + k then (ioRun (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (ioRun gs x).getD i false else false := by
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact ioPrefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), ioPrefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, ioSnoc, ← hlen, ioLast]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)

def ioWire (n j i : ℕ) := if i < n then lport i else if i < 2*n then rport (i-n)
  else if i < 2*n+j then i+2 else 1

theorem ioWireLt (n j i : ℕ) : ioWire n j i < 2*n+2+j := by
  unfold ioWire lport rport; split_ifs <;> omega

def ioArg (n j k : ℕ) (b : Bool) (l : List ℕ) :=
  (l[k]?.map (ioWire n j)).getD (if b then 0 else 1)

theorem ioArgLt (n j k : ℕ) (b : Bool) (l : List ℕ) : ioArg n j k b l < 2*n+2+j := by
  unfold ioArg
  cases l[k]? with
  | none => cases b <;> simp; omega
  | some i => exact ioWireLt n j i

def ioPairGate (n j : ℕ) (q : Gate) : Bool × ℕ × ℕ :=
  let b := match q.op with | .and => true | _ => false
  (b, ioArg n j 0 b q.inputs, ioArg n j 1 b q.inputs)

theorem ioPairEval (n j : ℕ) (q : Gate) (V R : ℕ → Bool) (h0 : V 0 = true) (h1 : V 1 = false)
    (hv : ∀ i, V (ioWire n j i) = R i) (hop : q.op = GateOp.and ∨ q.op = GateOp.or)
    (hq : q.inputs.length ≤ 2) :
    bin (ioPairGate n j q).1 (V (ioPairGate n j q).2.1) (V (ioPairGate n j q).2.2) = q.op.eval (q.inputs.map R) := by
  rcases q with ⟨op,l⟩
  change op = _ ∨ op = _ at hop
  change l.length ≤ 2 at hq
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩ <;> rcases hop with rfl | rfl <;>
    simp_all [ioPairGate, ioArg, bin, GateOp.eval]

theorem ioFrom {n s : ℕ} (hn : 2 ≤ n)
    (hr : RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) s) :
    ∃ S : Finset ℕ, ∃ g : Gates, ∃ o : ℕ, Good (2*n+2) S g ∧
      Solves (Finset.range n) (Finset.range n) S g o ∧ S.card ≤ s := by
  obtain ⟨C, hC, hc, hrep⟩ := hr
  let H := 2*n+2
  let S := Finset.Ico H (H + C.gates.length)
  let g : Gates := fun w => if h : w-H < C.gates.length then ioPairGate n (w-H) C.gates[w-H] else (false,0,0)
  have good : Good H S g := by
    intro w hw
    obtain ⟨ha,hb⟩ := Finset.mem_Ico.mp hw
    have hj : w-H < C.gates.length := by omega
    simp only [g, dite_eq_left hj, ioPairGate]
    have h : 2*n+2+(w-H) = w := by dsimp [H] at ha ⊢; omega
    exact ⟨ha, (ioArgLt _ _ _ _ _).trans_le h.le, (ioArgLt _ _ _ _ _).trans_le h.le⟩
  refine ⟨S, g, ioWire n C.gates.length C.output, good, ?_, by simpa [S, Circuit.size] using hc⟩
  intro u hu v hv
  have hu' := Finset.mem_range.mp hu
  have hv' := Finset.mem_range.mp hv
  let U : Fin n := ⟨u,hu'⟩
  let V : Fin n := ⟨v,hv'⟩
  let x := oneEach U V
  let p := point (Finset.range n) u v
  have px (w : ℕ) : p w = decide (w = 0 ∨ w = lport u ∨ w = rport v) := by simp [p,point,hu,hv]
  have xl : x.length = 2*n := by simp [x,oneEach]; omega
  have lower (w : ℕ) (hw : w < H) : val S g p w = p w := vout (by simp [S, not_le.mpr hw])
  have h0 : val S g p 0 = true := by rw [lower 0 (by dsimp [H]; omega),px]; simp
  have h1 : val S g p 1 = false := by rw [lower 1 (by dsimp [H]; omega),px]; simp [lport,rport]
  have simw : ∀ w, val S g p (ioWire n C.gates.length w) = (ioRun C.gates x).getD w false := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hin : w < 2*n
      · have hwin : w < x.length := by omega
        rw [ioInput C.gates x w hwin]
        simp only [x,oneEach] at hwin ⊢
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hwin]
        simp only [Option.getD_some]
        by_cases hl : w < n
        · rw [ioWire, ite_eq_left hl, lower _ (by dsimp [H,lport]; omega), px]
          have hw' : w < (List.ofFn fun i : Fin n => decide (i=U)).length := by simpa using hl
          rw [List.getElem_append_left hw']
          simp only [List.getElem_ofFn]
          rw [decide_eq_decide]
          simp only [lport,rport,Fin.ext_iff,U]
          omega
        · rw [ioWire, ite_eq_right hl, ite_eq_left hin, lower _ (by dsimp [H,rport]; omega), px]
          have hw' : ¬ w < (List.ofFn fun i : Fin n => decide (i=U)).length := by simpa using hl
          rw [List.getElem_append_right (Nat.le_of_not_gt hw')]
          simp only [List.getElem_ofFn]
          rw [decide_eq_decide]
          simp only [List.length_ofFn,lport,rport,Fin.ext_iff,V]
          omega
      · by_cases hw : w < 2*n+C.gates.length
        · let j := w-2*n
          have hj : j < C.gates.length := by dsimp [j]; omega
          have hwj : 2*n+j = w := by dsimp [j]; omega
          have hsub : w+2-H = j := by dsimp [H,j]; omega
          have hgp : g (w+2) = ioPairGate n j C.gates[j] := by simp [g,hsub,hj]
          have hwm : w+2 ∈ S := by simp [S,H]; omega
          rw [ioWire, ite_eq_right (by omega), ite_eq_right hin, ite_eq_left hw, vin good hwm, hgp]
          have hg := ioGate C.gates x j hj
          rw [xl, hwj] at hg
          rw [hg]
          apply ioPairEval _ _ _ _ _ h0 h1 _ (by simpa using (hC _ (List.getElem_mem hj)).1) (hC _ (List.getElem_mem hj)).2
          intro i
          split_ifs with h
          · rw [← ih i h]; congr 1; unfold ioWire; split_ifs <;> omega
          · have e : ioWire n j i = 1 := by unfold ioWire; split_ifs <;> omega
            rw [e,h1]
        · rw [ioWire, ite_eq_right (by omega), ite_eq_right hin, ite_eq_right hw, h1,
            List.getD_eq_default _ _ (by rw [ioLen,xl]; omega)]
  rw [simw]
  change C.eval (oneEach U V) = _
  simpa [U,V,Fin.ext_iff] using hrep U V

def ioRv (x : List Bool) : Bool ⊕ ℕ → Bool
  | .inl b => b
  | .inr i => x.getD i false

def ioSeed (n w : ℕ) : Bool ⊕ ℕ :=
  if w = 0 then .inl true else if 2 ≤ w ∧ (w-2)/2 < n then .inr ((w-2)/2) else .inl false

def ioBits {n : ℕ} (x : Fin n → Bool) (w : ℕ) := ioRv (List.ofFn x) (ioSeed n w)

def ioOK (q : Gate) := (q.op = GateOp.and ∨ q.op = GateOp.or) ∧ q.inputs.length ≤ 2

theorem ioEmit (n : ℕ) (hs : List Gate) (op : Bool) (a b : Bool ⊕ ℕ) :
    ∃ (e : List Gate) (r : Bool ⊕ ℕ), (∀ q ∈ e, ioOK q) ∧ e.length ≤ 1 ∧
      ((∀ t, a = .inr t → t < n+hs.length) → (∀ t, b = .inr t → t < n+hs.length) →
        ∀ t, r = .inr t → t < n+hs.length+e.length) ∧
      ∀ x : Fin n → Bool, ioRv (ioRun (hs++e) (List.ofFn x)) r =
        bin op (ioRv (ioRun hs (List.ofFn x)) a) (ioRv (ioRun hs (List.ofFn x)) b) := by
  rcases a with c | i
  · refine ⟨[], if c = op then b else .inl c, by simp, by simp, ?_, ?_⟩
    · cases op <;> cases c <;> simp
    · cases op <;> cases c <;> simp [ioRv,bin]
  · rcases b with d | j
    · refine ⟨[], if d = op then .inr i else .inl d, by simp, by simp, ?_, ?_⟩
      · cases op <;> cases d <;> simp
      · cases op <;> cases d <;> simp [ioRv,bin]
    · let q : Gate := ⟨if op then GateOp.and else GateOp.or, [i,j]⟩
      refine ⟨[q], .inr (n+hs.length), by cases op <;> simp [q,ioOK], by simp, by simp, ?_⟩
      intro x
      have hl : (ioRun hs (List.ofFn x)).length = n+hs.length := by simp [ioLen]
      simp only [ioRv]
      rw [ioSnoc, ← hl, ioLast]
      cases op <;> simp [q,bin,GateOp.eval]

theorem ioCompile {n H : ℕ} {S : Finset ℕ} {g : Gates} (hg : Good H S g) (k : ℕ) :
    ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ q ∈ hs, ioOK q) ∧
      hs.length ≤ (S.filter (· < k)).card ∧
      (∀ w < k, ∀ t, m w = .inr t → t < n+hs.length) ∧
      ∀ w < k, ∀ x : Fin n → Bool, ioRv (ioRun hs (List.ofFn x)) (m w) = val S g (ioBits x) w := by
  induction k with
  | zero => exact ⟨[], fun _ => .inl false, by simp, by simp, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨hs,m,hok,hlen,hb,he⟩ := ih
    have step : ∃ (e : List Gate) (r : Bool ⊕ ℕ), (∀ q ∈ e, ioOK q) ∧
        hs.length+e.length ≤ (S.filter (· < k+1)).card ∧
        (∀ t, r = .inr t → t < n+hs.length+e.length) ∧
        ∀ x : Fin n → Bool, ioRv (ioRun (hs++e) (List.ofFn x)) r = val S g (ioBits x) k := by
      by_cases hk : k ∈ S
      · have ha := (hg k hk).2
        obtain ⟨e,r,h1,h2,h3,h4⟩ := ioEmit n hs (g k).1 (m (g k).2.1) (m (g k).2.2)
        have hf : S.filter (· < k+1) = insert k (S.filter (· < k)) := by
          ext i
          by_cases heq : i = k
          · subst i; simp [hk]
          · simp only [Finset.mem_filter, Finset.mem_insert, heq, false_or]
            rw [show i < k+1 ↔ i < k by omega]
        refine ⟨e,r,h1,?_, h3 (hb _ ha.1) (hb _ ha.2), ?_⟩
        · rw [hf,Finset.card_insert_of_notMem (by simp)]; omega
        · intro x; rw [h4,he _ ha.1,he _ ha.2,vin hg hk]
      · refine ⟨[], ioSeed n k, by simp, ?_, ?_, ?_⟩
        · simp only [List.length_nil,Nat.add_zero]
          apply hlen.trans (Finset.card_le_card ?_)
          intro i hi
          obtain ⟨him,hik⟩ := Finset.mem_filter.mp hi
          exact Finset.mem_filter.mpr ⟨him, by omega⟩
        · intro t ht
          unfold ioSeed at ht
          split_ifs at ht with h z
          cases ht; simp; omega
        · intro x
          rw [List.append_nil,vout hk]
          unfold ioBits ioSeed
          split_ifs with h z
          · rfl
          · exact ioInput _ _ _ (by simpa using z.2)
          · rfl
    obtain ⟨e,r,hq,hl,hr,hev⟩ := step
    refine ⟨hs++e,Function.update m k r,fun q h => (List.mem_append.mp h).elim (hok q) (hq q),
      by simpa using hl, ?_, ?_⟩
    · intro w hw t ht
      by_cases h : w = k
      · subst w; simpa [Function.update_self,List.length_append,Nat.add_assoc] using hr t (by simpa using ht)
      · rw [Function.update_of_ne h] at ht
        have := hb w (by omega) t ht
        rw [List.length_append]; omega
    · intro w hw x
      by_cases h : w = k
      · subst w; simpa using hev x
      · rw [Function.update_of_ne h, ← he w (by omega) x]
        cases hmw : m w with
        | inl b => rfl
        | inr t => exact ioPrefix _ _ _ _ (by simpa using hb w (by omega) t hmw)

theorem ioMonobin {a b c d : Bool} (op : Bool) (h1 : a ≤ c) (h2 : b ≤ d) :
    bin op a b ≤ bin op c d := by
  cases op <;> cases a <;> cases b <;> cases c <;> cases d <;> simp_all [bin]

theorem ioMono {H : ℕ} {S : Finset ℕ} {g : Gates} (hg : Good H S g) {a b : ℕ → Bool}
    (h : ∀ i, a i ≤ b i) (w : ℕ) : val S g a w ≤ val S g b w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w ∈ S
    · rw [vin hg hw,vin hg hw]
      exact ioMonobin _ (ih _ (hg _ hw).2.1) (ih _ (hg _ hw).2.2)
    · simpa [vout hw] using h w

def ioPt {n : ℕ} (a b i : Fin n) := decide (i=a ∨ i=b)

theorem ioPairBits {n : ℕ} (a b : Fin n) : ioBits (ioPt a b) = point ∅ a b := by
  funext w
  unfold ioBits ioSeed
  split_ifs with h h
  · simp [ioRv,point,h]
  · have hi : (w-2)/2 < (List.ofFn (ioPt a b)).length := by simpa using h.2
    simp only [ioRv,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some,
      List.getElem_ofFn,ioPt,Fin.ext_iff,point,Finset.notMem_empty,not_false_eq_true,true_and,decide_eq_decide,lport,rport]
    omega
  · simp only [ioRv,point,lport,rport,Finset.notMem_empty,not_false_eq_true,true_and]
    symm
    apply decide_eq_false
    have := a.isLt; have := b.isLt; omega

theorem ioBitsMono {n : ℕ} {x y : Fin n → Bool} (h : ∀ i, x i ≤ y i) (w : ℕ) : ioBits x w ≤ ioBits y w := by
  unfold ioBits ioSeed
  split_ifs with h0 hi
  · exact le_rfl
  · have h₁ : (w-2)/2 < (List.ofFn x).length := by simpa using hi.2
    have h₂ : (w-2)/2 < (List.ofFn y).length := by simpa using hi.2
    simpa only [ioRv,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h₁,List.getElem?_eq_getElem h₂,
      Option.getD_some,List.getElem_ofFn] using h ⟨(w-2)/2,hi.2⟩
  · exact le_rfl

theorem ioTo {n : ℕ} (hn : 2 ≤ n) {S : Finset ℕ} {g : Gates} {o : ℕ}
    (hg : Good (2*n+2) S g) (hs : Solves (Finset.range n) ∅ S g o) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ S.card ∧
      (∀ x : Fin n → Bool, (List.ofFn x).count true = 2 → C.eval (List.ofFn x) = true) ∧
      (∀ x : Fin n → Bool, (List.ofFn x).count true ≤ 1 → C.eval (List.ofFn x) = false) := by
  classical
  have pair (a b : Fin n) : val S g (ioBits (ioPt a b)) o = decide (a ≠ b) := by
    rw [ioPairBits]
    simpa [Fin.ext_iff] using hs a (Finset.mem_range.mpr a.isLt) b (Finset.mem_range.mpr b.isLt)
  obtain ⟨qs,m,hok,hlen,_,he⟩ := ioCompile (n:=n) hg (o+1)
  have ev := he o (by omega)
  let a : Fin n := ⟨0,by omega⟩
  let b : Fin n := ⟨1,by omega⟩
  have ab : a ≠ b := by simp [a,b]
  cases hm : m o with
  | inl c =>
    have v0 := ev (ioPt a a)
    have v1 := ev (ioPt a b)
    simp [hm,ioRv,pair,ab] at v0 v1
    simp_all
  | inr t =>
    let C : Circuit := ⟨qs,t⟩
    have hval (x : Fin n → Bool) : C.eval (List.ofFn x) = val S g (ioBits x) o := by
      simpa [hm,ioRv,C,Circuit.eval,Circuit.wires,ioRun] using ev x
    refine ⟨C,fun q hq => ⟨by simpa using (hok q hq).1,(hok q hq).2⟩,
      hlen.trans (Finset.card_le_card (Finset.filter_subset _ _)), ?_, ?_⟩
    · intro x hx
      rw [List.count_ofFn] at hx
      obtain ⟨i,j,hij,heq⟩ := Finset.card_eq_two.mp hx
      have ex : x = ioPt i j := by
        funext k
        have hk := Finset.ext_iff.mp heq k
        simp at hk
        cases hb : x k <;> simp_all [ioPt]
      rw [ex,hval,pair]; simp [hij]
    · intro x hx
      rw [List.count_ofFn] at hx
      let _ : Nonempty (Fin n) := ⟨a⟩
      obtain ⟨i,hi⟩ := Finset.card_le_one_iff_subset_singleton.mp hx
      have bound (j : Fin n) : x j ≤ ioPt i i j := by
        cases hj : x j
        · simp
        · have eq : j = i := by simpa using hi (Finset.mem_filter.mpr ⟨Finset.mem_univ j,hj⟩)
          simp [ioPt,eq]
      have h := ioMono hg (ioBitsMono bound) o
      rw [pair] at h
      rw [hval]
      exact le_antisymm (by simpa using h) (Bool.false_le _)

end S18508

theorem S18508 : ∀ n s : ℕ, 2 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size + n ≤ s ∧ (∀ x : Fin n → Bool, (List.ofFn x).count true = 2 → C.eval (List.ofFn x) = true) ∧ (∀ x : Fin n → Bool, (List.ofFn x).count true ≤ 1 → C.eval (List.ofFn x) = false) := by
  intro n s hn hr
  obtain ⟨S,g,o,hg,hs,cs⟩ := S18508.ioFrom hn hr
  obtain ⟨T,h,p,ht,hp,ct⟩ := S18508.discount (n := n)
    (K := Finset.range n) (M := Finset.range n) (fun _ h => h) (fun _ h => h) (by simpa using hn) hg hs
  obtain ⟨C,hC,hsize,hpos,hneg⟩ := S18508.ioTo hn ht hp
  simp only [Finset.card_range] at ct
  exact ⟨C,hC,by omega,hpos,hneg⟩

namespace S30581

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Represents (oneEach Represents RepSizeAtMost)

def edge (x y : Nat) : Bool :=
  (64478 : Nat).testBit (4 * min x 3 + min y 3)

private theorem edge_spec (x y : Nat) : edge x y = !decide (x = y ∧ x < 3) := by
  have small : ∀ a b : Fin 4, (64478 : Nat).testBit (4*a.val+b.val) =
      !decide (a.val = b.val ∧ a.val < 3) := by decide
  unfold edge
  rw [small ⟨min x 3, by omega⟩ ⟨min y 3, by omega⟩]
  have h : (min x 3 = min y 3 ∧ min x 3 < 3) ↔ (x=y ∧ x<3) := by omega
  simp only [h]

private def low {n : Nat} (h : 3 ≤ n) : Finset (Fin n) :=
  Finset.univ.map (Fin.castLEEmb h)

private theorem mem_low {n : Nat} (h : 3 ≤ n) (i : Fin n) : i ∈ low h ↔ i.val < 3 := by
  simp only [low, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a,rfl⟩
    exact a.isLt
  · intro hi
    exact ⟨⟨i.val,hi⟩,rfl⟩

private theorem card_low {n : Nat} (h : 3 ≤ n) : (low h).card = 3 := by simp [low]

private theorem adjacent_low {m : Nat} (h : 3 ≤ m) (x : Nat) :
    ∃ j : Fin m, j.val < 3 ∧ edge x j.val = true := by
  by_cases hx : x = 0
  · exact ⟨⟨1,by omega⟩, by change 1 < 3; decide, by simp [edge_spec,hx]⟩
  · exact ⟨⟨0,by omega⟩, by change 0 < 3; decide, by simp [edge_spec,hx]⟩

private theorem edge_symm (x y : Nat) : edge x y = edge y x := by
  rw [edge_spec,edge_spec]
  by_cases h : x=y
  · subst y; rfl
  · simp [h,Ne.symm h]

abbrev InducedBound : Prop :=
∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (R : Finset (Fin n)) (K : Finset (Fin m)), (∀ u ∈ R, ∃ v ∈ K, A u v = false) → (∀ v ∈ K, ∃ u ∈ R, A u v = false) → (∃ u ∈ R, ∃ v ∈ K, A u v = true) → PEqualNP.Represents.RepSizeAtMost A s → ∃ s' : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v => A u v && decide (u ∈ R) && decide (v ∈ K)) s' ∧ s' + ((Finset.univ.filter (fun a : Fin n => ∃ b : Fin m, A a b = true ∧ ∃ a' : Fin n, A a' b = false)).card + (Finset.univ.filter (fun b : Fin m => ∃ a : Fin n, A a b = true ∧ ∃ b' : Fin m, A a b' = false)).card) ≤ s + ((R.filter (fun a => ∃ b ∈ K, A a b = true)).card + (K.filter (fun b => ∃ a ∈ R, A a b = true)).card)

theorem saved (induced : InducedBound) (n m s : Nat) (hn : 3 ≤ n) (hm : 3 ≤ m)
    (source : Represents.RepSizeAtMost (fun (i : Fin n) (j : Fin m) => edge i.val j.val) s) :
    ∃ t : Nat, Represents.RepSizeAtMost
        (fun (i : Fin n) (j : Fin m) => edge i.val j.val && decide (i.val < 3) && decide (j.val < 3)) t ∧
      t + (n+m) ≤ s + 6 := by
  let A := fun (i : Fin n) (j : Fin m) => edge i.val j.val
  have missR (i : Fin n) (hi : i ∈ low hn) : ∃ j ∈ low hm, A i j = false := by
    have h := (mem_low hn i).mp hi
    exact ⟨⟨i.val,by omega⟩, (mem_low hm _).mpr h, by simp [A,edge_spec,h]⟩
  have missK (j : Fin m) (hj : j ∈ low hm) : ∃ i ∈ low hn, A i j = false := by
    have h := (mem_low hm j).mp hj
    exact ⟨⟨j.val,by omega⟩, (mem_low hn _).mpr h, by simp [A,edge_spec,h]⟩
  have hit : ∃ i ∈ low hn, ∃ j ∈ low hm, A i j = true := by
    exact ⟨⟨0,by omega⟩, (mem_low hn _).mpr (by change 0 < 3; decide), ⟨1,by omega⟩,
      (mem_low hm _).mpr (by change 1 < 3; decide), by change edge 0 1 = true; decide⟩
  have activeR (a : Fin n) : ∃ b : Fin m, A a b = true ∧ ∃ a' : Fin n, A a' b = false := by
    obtain ⟨b,hb,ab⟩ := adjacent_low hm a.val
    obtain ⟨a',_,zero⟩ := missK b ((mem_low hm _).mpr hb)
    exact ⟨b,ab,a',zero⟩
  have activeK (b : Fin m) : ∃ a : Fin n, A a b = true ∧ ∃ b' : Fin m, A a b' = false := by
    obtain ⟨a,ha,ba⟩ := adjacent_low hn b.val
    obtain ⟨b',_,zero⟩ := missR a ((mem_low hn _).mpr ha)
    exact ⟨a, (edge_symm _ _).trans ba,b',zero⟩
  obtain ⟨t,rep,budget⟩ := induced n m s A (low hn) (low hm) missR missK hit source
  have r := Finset.card_filter_le (low hn) (fun a => ∃ b ∈ low hm, A a b = true)
  have c := Finset.card_filter_le (low hm) (fun b => ∃ a ∈ low hn, A a b = true)
  simp [activeR,activeK] at budget
  rw [card_low] at r c
  exact ⟨t,by simpa only [A,mem_low] using rep,by omega⟩

private def wire (n m a b dead w : Nat) : Nat :=
  if w < n then (if w < a then w else dead)
  else if w < n + m then (if w - n < b then a + (w - n) else dead)
  else a + b + (w - (n + m))

private def rename (r : Nat → Nat) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

private def prefixStep (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map fun k => ws.getD k false)]

private theorem lengthInput {a b : Nat} (u : Fin a) (v : Fin b) : (oneEach u v).length = a + b := by
  simp [oneEach]

private theorem readInput {a b : Nat} (u : Fin a) (v : Fin b) (i : Nat) :
    (oneEach u v).getD i false = decide (i = u.val ∨ i = a + v.val) := by
  have hu := u.isLt
  have hv := v.isLt
  unfold oneEach
  by_cases hi : i < a
  · rw [List.getD_append _ _ _ _ (by simpa using hi)]
    simp [List.getD_eq_getElem?_getD, hi, Fin.ext_iff, show i ≠ a + v.val by omega]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega), List.length_ofFn]
    by_cases hj : i - a < b
    · simp [List.getD_eq_getElem?_getD, hj, Fin.ext_iff, show i ≠ u.val by omega,
        show i - a = v.val ↔ i = a + v.val by omega]
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp [show i ≠ u.val by omega, show i ≠ a + v.val by omega]

private theorem readPrefix {n m a b N : Nat} (ha : a ≤ n) (hb : b ≤ m)
    (u : Fin a) (v : Fin b) (tail : List Bool) (ht : tail.length ≤ N) (w : Nat) :
    (oneEach u v ++ tail).getD (wire n m a b (a + b + N) w) false =
    (oneEach (Fin.castLE ha u) (Fin.castLE hb v) ++ tail).getD w false := by
  have hu := u.isLt
  have hv := v.isLt
  by_cases raw : w < n + m
  · conv_rhs => rw [List.getD_append _ _ _ _ (by rwa [lengthInput]), readInput]
    simp only [Fin.val_castLE]
    by_cases left : w < n
    · by_cases kept : w < a
      · simp only [wire, if_pos left, if_pos kept]
        rw [List.getD_append _ _ _ _ (by rw [lengthInput]; omega), readInput]
        simp [show w ≠ a + v.val by omega, show w ≠ n + v.val by omega]
      · simp only [wire, if_pos left, if_neg kept]
        rw [List.getD_eq_default _ _ (by rw [List.length_append, lengthInput]; omega)]
        simp [show w ≠ u.val by omega, show w ≠ n + v.val by omega]
    · by_cases kept : w - n < b
      · simp only [wire, if_neg left, if_pos raw, if_pos kept]
        rw [List.getD_append _ _ _ _ (by rw [lengthInput]; omega), readInput]
        simp [show a + (w - n) ≠ u.val by omega, show w ≠ u.val by omega,
          show a + (w - n) = a + v.val ↔ w = n + v.val by omega] <;> omega
      · simp only [wire, if_neg left, if_pos raw, if_neg kept]
        rw [List.getD_eq_default _ _ (by rw [List.length_append, lengthInput]; omega)]
        simp [show w ≠ u.val by omega, show w ≠ n + v.val by omega]
  · simp only [wire, if_neg (show ¬ w < n by omega), if_neg raw]
    rw [List.getD_append_right _ _ _ _ (by rw [lengthInput]; omega),
      List.getD_append_right _ _ _ _ (by rw [lengthInput]; omega), lengthInput, lengthInput]
    congr 1
    omega

private theorem simulation {n m a b N : Nat} (ha : a ≤ n) (hb : b ≤ m)
    (u : Fin a) (v : Fin b) (gs : List Gate) (tail : List Bool) (h : tail.length + gs.length ≤ N) :
    let r := wire n m a b (a + b + N)
    ∃ out : List Bool, out.length ≤ N ∧
      (gs.map (rename r)).foldl prefixStep (oneEach u v ++ tail) = oneEach u v ++ out ∧
      gs.foldl prefixStep (oneEach (Fin.castLE ha u) (Fin.castLE hb v) ++ tail) =
        oneEach (Fin.castLE ha u) (Fin.castLE hb v) ++ out := by
  induction gs generalizing tail with
  | nil => exact ⟨tail, by simpa using h, rfl, rfl⟩
  | cons g rest ih =>
    let old := oneEach (Fin.castLE ha u) (Fin.castLE hb v) ++ tail
    let bit := g.op.eval (g.inputs.map fun k => old.getD k false)
    have ht : tail.length ≤ N := by omega
    have same : (rename (wire n m a b (a + b + N)) g).op.eval
        ((rename (wire n m a b (a + b + N)) g).inputs.map fun k =>
          (oneEach u v ++ tail).getD k false) = bit := by
      simp only [rename, List.map_map, Function.comp_def, readPrefix ha hb u v tail ht, bit, old]
    have bound : (tail ++ [bit]).length + rest.length ≤ N := by
      simp only [List.length_cons] at h
      simp; omega
    simpa only [List.map_cons, List.foldl_cons, prefixStep, same, List.append_assoc, bit, old]
      using ih (tail ++ [bit]) bound

theorem restrictPrefix {n m a b s : Nat} (ha : a ≤ n) (hb : b ≤ m)
    (A : Fin n → Fin m → Bool) (h : RepSizeAtMost A s) :
    RepSizeAtMost (fun i j => A (Fin.castLE ha i) (Fin.castLE hb j)) s := by
  obtain ⟨C, mono, size, rep⟩ := h
  let r := wire n m a b (a + b + C.size)
  let D : Circuit := ⟨C.gates.map (rename r), r C.output⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
    simpa [rename] using mono f hf
  · simpa [D, Circuit.size] using size
  · intro u v
    obtain ⟨out, len, hnew, hold⟩ :=
      simulation (N := C.size) ha hb u v C.gates [] (by simp [Circuit.size])
    simp only [List.append_nil] at hnew hold
    have val := rep (Fin.castLE ha u) (Fin.castLE hb v)
    change (C.gates.foldl prefixStep _).getD C.output false = _ at val
    change ((C.gates.map (rename r)).foldl prefixStep _).getD (r C.output) false = _
    rw [hnew, readPrefix ha hb u v out len, ← hold, val]

private def step (v : List Bool) (g : Gate) : List Bool :=
  v ++ [g.op.eval (g.inputs.map fun k => v.getD k false)]

private def core (n total : Nat) : List Gate :=
  [⟨.or, [0,n]⟩, ⟨.or, [1,n+1]⟩, ⟨.or, [2,n+2]⟩,
   ⟨.and, [total,total+1]⟩, ⟨.or, [total,total+1]⟩,
   ⟨.and, [total+4,total+2]⟩, ⟨.or, [total+3,total+5]⟩]

private def bits (xs : List Bool) (n : Nat) : List Bool :=
  let p := xs.getD 0 false || xs.getD n false
  let q := xs.getD 1 false || xs.getD (n+1) false
  let r := xs.getD 2 false || xs.getD (n+2) false
  [p,q,r,p && q,p || q,(p || q) && r,(p && q) || ((p || q) && r)]

private theorem core_run (xs : List Bool) (n : Nat) (h : n+2 < xs.length) :
    (core n xs.length).foldl step xs = xs ++ bits xs n := by
  have raw (ls : List Bool) (j : Nat) (hj : j < xs.length) :
      (xs ++ ls).getD j false = xs.getD j false := List.getD_append _ _ _ _ hj
  have added (ls : List Bool) (j : Nat) :
      (xs ++ ls).getD (xs.length+j) false = ls.getD j false := by
    rw [List.getD_append_right _ _ _ _ (by omega)]
    congr 1
    omega
  have first (ls : List Bool) :
      (xs ++ ls).getD xs.length false = ls.getD 0 false := by simpa using added ls 0
  simp (disch := omega) only [core, step, bits, GateOp.eval, List.foldl_cons, List.foldl_nil,
    List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
    id_eq, Bool.or_false, Bool.and_true, List.append_assoc, List.cons_append, List.nil_append,
    added, first, raw, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceAdd]

private def chain (last : Nat) : List Nat → List Gate
  | [] => []
  | w :: ws => ⟨.or,[last,w]⟩ :: chain (last+1) ws

private theorem chain_len (last : Nat) (ws : List Nat) : (chain last ws).length = ws.length := by
  induction ws generalizing last with
  | nil => rfl
  | cons _ _ ih => simp [chain, ih]

private theorem chain_pos (last : Nat) (ws : List Nat) :
    ∀ g ∈ chain last ws, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  induction ws generalizing last with
  | nil => simp [chain]
  | cons w ws ih =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl | keep
    · simp
    · exact ih (last+1) g keep

private theorem anyAgree (xs : List Nat) (p q : Nat → Bool)
    (agree : ∀ k ∈ xs, p k = q k) : xs.any p = xs.any q := by
  induction xs with
  | nil => rfl
  | cons k rest ih =>
    rw [List.any_cons, List.any_cons, agree k (by simp), ih (fun t ht => agree t (by simp [ht]))]

private theorem chain_run (xs : List Bool) (last : Nat) (ws : List Nat)
    (len : xs.length = last+1) (early : ∀ w ∈ ws, w < xs.length) :
    ((chain last ws).foldl step xs).getD (last+ws.length) false =
      (xs.getD last false || ws.any (fun w => xs.getD w false)) := by
  induction ws generalizing xs last with
  | nil => simp [chain]
  | cons w ws ih =>
    let v := xs.getD last false || xs.getD w false
    have e : ∀ k ∈ ws, k < xs.length := fun k hk => early k (List.mem_cons_of_mem _ hk)
    have eq : step xs ⟨GateOp.or,[last,w]⟩ = xs ++ [v] := by simp [step, v, GateOp.eval]
    have lastVal : (xs ++ [v]).getD (last+1) false = v := by
      rw [← len, List.getD_append_right _ _ _ _ (by omega), Nat.sub_self]
      rfl
    have other : ws.any (fun k => (xs ++ [v]).getD k false) = ws.any (fun k => xs.getD k false) := by
      apply anyAgree
      intro k hk
      exact List.getD_append _ _ _ _ (e k hk)
    simp only [chain,List.foldl_cons,List.length_cons,List.any_cons,eq]
    rw [show last+(ws.length+1) = (last+1)+ws.length by omega,
      ih (xs ++ [v]) (last+1) (by simp [len]) (by intro k hk; specialize e k hk; simp; omega),
      lastVal,other]
    exact Bool.or_assoc _ _ _

private def extras (n m : Nat) : List Nat :=
  ((List.range (n-3)).map (fun t => 3+t)) ++ ((List.range (m-3)).map (fun t => n+3+t))

private theorem extras_mem (n m k : Nat) :
    k ∈ extras n m ↔ (3 ≤ k ∧ k < n) ∨ (n+3 ≤ k ∧ k < n+m) := by
  simp only [extras, List.mem_append, List.mem_map, List.mem_range]
  constructor
  · rintro (⟨t,ht,rfl⟩ | ⟨t,ht,rfl⟩)
    · left; omega
    · right; omega
  · rintro (h | h)
    · left; exact ⟨k-3,by omega,by omega⟩
    · right; exact ⟨k-(n+3),by omega,by omega⟩

private theorem rawBit {n m : Nat} (i : Fin n) (j : Fin m) (w : Nat) :
    (Represents.oneEach i j).getD w false = decide (w = i.val ∨ w = n+j.val) := by
  unfold Represents.oneEach
  by_cases lw : w < n
  · rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using lw)]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using lw)]
    simp only [List.getElem_ofFn, Fin.ext_iff, decide_eq_decide]
    omega
  · rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
    simp only [List.length_ofFn]
    by_cases rw' : w-n < m
    · rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using rw')]
      simp only [List.getElem_ofFn, Fin.ext_iff, decide_eq_decide]
      omega
    · rw [List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega)]
      have neither : ¬(w=i.val ∨ w=n+j.val) := by omega
      simp [neither]

private def flag (a b k : Nat) : Bool := decide (a=k) || decide (b=k)

private def vote (a b c : Bool) : Bool := (a && b) || ((a || b) && c)

private theorem graphFormula (a b : Nat) :
    (vote (flag a b 0) (flag a b 1) (flag a b 2) || decide (3 ≤ a ∨ 3 ≤ b)) =
    (64478 : Nat).testBit (4 * min a 3 + min b 3) := by
  have control : ∀ i j : Fin 4,
      (vote (flag i.val j.val 0) (flag i.val j.val 1) (flag i.val j.val 2) ||
        decide (3 ≤ i.val ∨ 3 ≤ j.val)) = (64478 : Nat).testBit (4*i.val+j.val) := by decide
  have low (x k : Nat) (h : k < 3) : (min x 3 = k) ↔ x=k := by omega
  have high (x : Nat) : 3 ≤ min x 3 ↔ 3 ≤ x := by omega
  simpa (disch := decide) only [flag, low, high] using
    control ⟨min a 3,by omega⟩ ⟨min b 3,by omega⟩

private theorem extraValue {n m : Nat} (i : Fin n) (j : Fin m) :
    (extras n m).any (fun w => (Represents.oneEach i j).getD w false) =
      decide (3 ≤ i.val ∨ 3 ≤ j.val) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, extras_mem, rawBit, decide_eq_true_eq]
  constructor
  · rintro ⟨w, h, h'⟩
    omega
  · rintro (hi | hj)
    · exact ⟨i.val, Or.inl ⟨hi,i.isLt⟩, Or.inl rfl⟩
    · exact ⟨n+j.val, Or.inr ⟨by omega,by omega⟩, Or.inr rfl⟩

private theorem coreValue {n m : Nat} (hn : 3 ≤ n) (hm : 3 ≤ m) (i : Fin n) (j : Fin m) :
    (bits (Represents.oneEach i j) n).getD 6 false =
      vote (flag i.val j.val 0) (flag i.val j.val 1) (flag i.val j.val 2) := by
  have left (k : Nat) (hk : k < 3) :
      (Represents.oneEach i j).getD k false = decide (i.val=k) := by
    rw [rawBit, decide_eq_decide]; omega
  have right (k : Nat) (hk : k < 3) :
      (Represents.oneEach i j).getD (n+k) false = decide (j.val=k) := by
    rw [rawBit, decide_eq_decide]; omega
  have right0 := right 0 (by decide)
  rw [Nat.add_zero] at right0
  simp (disch := decide) only [bits, List.getD_cons_succ, List.getD_cons_zero,
    left, right, right0, vote, flag]

theorem threeHoleUpper :
∀ (n m : Nat), 3 ≤ n → 3 ≤ m →
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = n + m + 1 ∧
      PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin m) =>
        (64478 : Nat).testBit (4 * min u.val 3 + min v.val 3)) C := by
  intro n m hn hm
  let N := n+m
  let rest := extras n m
  let C : Circuit := ⟨core n N ++ chain (N+6) rest, N+6+rest.length⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · intro g hg
    change g ∈ core n N ++ chain (N+6) rest at hg
    rcases List.mem_append.mp hg with hc | he
    · simp only [core, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using chain_pos (N+6) rest g he
  · change (core n N ++ chain (N+6) rest).length = n+m+1
    simp only [List.length_append, chain_len, rest, extras, List.length_map,List.length_range]
    change 7 + ((n-3)+(m-3)) = n+m+1
    omega
  · intro i j
    let xs := Represents.oneEach i j
    have len : xs.length = N := by simp [xs, N, Represents.oneEach]
    have bLen : (bits xs n).length = 7 := rfl
    have short : ∀ w ∈ rest, w < xs.length := by
      intro w hw
      rcases (extras_mem n m w).mp hw with h | h <;> dsimp [N] at len <;> omega
    have init : (core n N).foldl step xs = xs ++ bits xs n := by
      rw [← len]; exact core_run xs n (by dsimp [N] at len; omega)
    have past : (xs ++ bits xs n).getD (N+6) false = (bits xs n).getD 6 false := by
      rw [List.getD_append_right _ _ _ _ (by omega),len]
      congr 1
      omega
    have same : rest.any (fun w => (xs ++ bits xs n).getD w false) =
        rest.any (fun w => xs.getD w false) := by
      apply anyAgree
      intro w hw
      exact List.getD_append _ _ _ _ (short w hw)
    change ((core n N ++ chain (N+6) rest).foldl step xs).getD (N+6+rest.length) false = _
    rw [List.foldl_append,init,chain_run _ _ _ (by simp [len,bLen])
      (by intro w hw; specialize short w hw; simp [bLen]; omega),past,same,
      coreValue hn hm i j,extraValue i j]
    exact graphFormula i.val j.val

def val (n : ℕ) (gs : List Gate) (X : Finset (Fin n)) (k : ℕ) : Bool :=
  if h : k < n then decide (⟨k, h⟩ ∈ X)
  else if h2 : k - n < gs.length then
    (gs[k - n]).op.eval
      ((gs[k - n]).inputs.map (fun j => if hj : j < k then val n gs X j else false))
  else false
termination_by k
decreasing_by exact hj

theorem val_input {n : ℕ} {gs : List Gate} {X : Finset (Fin n)} {k : ℕ} (h : k < n) :
    val n gs X k = decide (⟨k, h⟩ ∈ X) := by
  rw [val]; simp [h]

theorem val_gate {n : ℕ} {gs : List Gate} {X : Finset (Fin n)} {k : ℕ} (h : ¬ k < n)
    (h2 : k - n < gs.length) :
    val n gs X k = (gs[k - n]).op.eval
      ((gs[k - n]).inputs.map (fun j => if j < k then val n gs X j else false)) := by
  rw [val]; simp only [h, h2, dite_false, dite_true]
  congr 2

theorem val_past {n : ℕ} {gs : List Gate} {X : Finset (Fin n)} {k : ℕ}
    (h : n + gs.length ≤ k) : val n gs X k = false := by
  rw [val]
  have h1 : ¬ k < n := by omega
  have h2 : ¬ k - n < gs.length := by omega
  simp [h1, h2]

theorem foldl_take {n : ℕ} (gs : List Gate) (X : Finset (Fin n)) :
    ∀ j, j ≤ gs.length →
    (gs.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (List.ofFn (fun v : Fin n => decide (v ∈ X)))
      = List.ofFn (fun k : Fin (n + j) => val n gs X k) := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [List.take_zero, List.foldl_nil]
    apply List.ext_getElem
    · simp
    · intro k h1 h2
      simp only [List.length_ofFn] at h1
      simp [val_input h1]
  | succ j ih =>
    intro hj
    have hj' : j < gs.length := by omega
    rw [List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some, List.foldl_append,
      ih (by omega)]
    simp only [List.foldl_cons, List.foldl_nil]
    apply List.ext_getElem
    · simp
    · intro k h1 h2
      simp only [List.length_append, List.length_ofFn, List.length_singleton] at h1
      by_cases hk : k < n + j
      · rw [List.getElem_append_left (by simpa using hk)]
        simp only [List.getElem_ofFn]
      · have hk' : k = n + j := by omega
        subst hk'
        rw [List.getElem_append_right (by simp)]
        simp only [List.length_ofFn, Nat.sub_self, List.getElem_singleton, List.getElem_ofFn]
        rw [val_gate (by omega) (by omega)]
        have : n + j - n = j := by omega
        simp only [this]
        congr 2
        funext i
        by_cases hi : i < n + j
        · simp [List.getD_eq_getElem?_getD, hi]
        · simp [List.getD_eq_getElem?_getD, hi]

theorem eval_eq {n : ℕ} (gs : List Gate) (X : Finset (Fin n)) (o : ℕ) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn fun v : Fin n => decide (v ∈ X)) = val n gs X o := by
  unfold Circuit.eval Circuit.wires
  simp only
  have := foldl_take gs X gs.length le_rfl
  rw [List.take_length] at this
  rw [this]
  by_cases ho : o < n + gs.length
  · simp [List.getD_eq_getElem?_getD, ho]
  · rw [val_past (by omega)]
    simp [List.getD_eq_getElem?_getD, ho]

theorem op_eval_mono {op : GateOp} (hop : op = .and ∨ op = .or) (l : List ℕ) (f f' : ℕ → Bool)
    (hff : ∀ a ∈ l, f a = true → f' a = true) (h : op.eval (l.map f) = true) :
    op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id] at h ⊢
    intro a ha; exact hff a ha (h a ha)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at h ⊢
    obtain ⟨a, ha, hfa⟩ := h
    exact ⟨a, ha, hff a ha hfa⟩

theorem val_mono {n : ℕ} {gs : List Gate} (hgs : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    {X X' : Finset (Fin n)} (hXX : X ⊆ X') :
    ∀ k, val n gs X k = true → val n gs X' k = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases h : k < n
    · rw [val_input h] at hk ⊢
      simp only [decide_eq_true_eq] at hk ⊢
      exact hXX hk
    · by_cases h2 : k - n < gs.length
      · rw [val_gate h h2] at hk ⊢
        refine op_eval_mono (hgs _ (List.getElem_mem _)) _ _ _ ?_ hk
        intro a _ ha
        by_cases hak : a < k
        · simp only [hak, ite_true] at ha ⊢
          exact ih a hak ha
        · simp [hak] at ha
      · rw [val_past (by omega)] at hk
        exact absurd hk (by simp)

abbrev MajorityFloor : Prop :=
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2)) s ↔ 4 ≤ s

abbrev CrownReduction : Prop :=
∀ n s : ℕ, 2 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size + n ≤ s ∧ (∀ x : Fin n → Bool, (List.ofFn x).count true = 2 → C.eval (List.ofFn x) = true) ∧ (∀ x : Fin n → Bool, (List.ofFn x).count true ≤ 1 → C.eval (List.ofFn x) = false)

theorem crownFloor (majority : MajorityFloor) (reduceCrown : CrownReduction) :
    ¬ Represents.RepSizeAtMost (fun i j : Fin 3 => decide (i ≠ j)) 6 := by
  intro rep
  obtain ⟨C, pos, size, two, low⟩ := reduceCrown 3 6 (by decide) rep
  have ops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa using (pos g hg).1
  have fan : FanInTwo C := by
    intro g hg
    refine ⟨?_, (pos g hg).2⟩
    rcases ops g hg with e | e <;> simp [e]
  let pair : Finset (Fin 3) := {0, 1}
  have atPair := two (fun i => decide (i ∈ pair)) (by decide)
  rw [eval_eq C.gates pair C.output] at atPair
  have atTop := val_mono ops (Finset.subset_univ pair) C.output atPair
  rw [← eval_eq C.gates Finset.univ C.output] at atTop
  have small : HasCircuitSize 3 (fun x : Fin 3 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2)) 3 := by
    refine ⟨C, fan, by omega, ?_⟩
    intro x
    have table : ∀ y : Fin 3 → Bool,
        let maj := (y 0 && y 1) || (y 1 && y 2) || (y 0 && y 2)
        ((List.ofFn y).count true ≤ 1 ∧ maj = false) ∨
        ((List.ofFn y).count true = 2 ∧ maj = true) ∨
        (y = (fun i => decide (i ∈ (Finset.univ : Finset (Fin 3)))) ∧ maj = true) := by decide
    rcases table x with ⟨h,e⟩ | ⟨h,e⟩ | ⟨h,e⟩
    · exact (low x h).trans e.symm
    · exact (two x h).trans e.symm
    · rw [h]; exact atTop.trans (h ▸ e).symm
  have := (majority 3).mp small
  omega

theorem exactFromThree (induced : InducedBound) (majority : MajorityFloor)
    (reduceCrown : CrownReduction) (n m : ℕ) (hn : 3 ≤ n) (hm : 3 ≤ m) :
    let A := fun (i : Fin n) (j : Fin m) => edge i.val j.val
    Represents.RepSizeAtMost A (n+m+1) ∧ ¬ Represents.RepSizeAtMost A (n+m) := by
  obtain ⟨C, pos, price, rep⟩ := threeHoleUpper n m hn hm
  refine ⟨⟨C,pos,price.le,rep⟩,?_⟩
  intro small
  obtain ⟨t, ⟨D, dp, ds, dr⟩, cost⟩ := saved induced n m (n+m) hn hm small
  have copy := restrictPrefix hn hm _ (s := 6) ⟨D,dp,by omega,dr⟩
  have eqn : ∀ i j : Fin 3, (edge i.val j.val && decide (i.val < 3) && decide (j.val < 3)) = decide (i ≠ j) := by decide
  apply crownFloor majority reduceCrown
  simpa only [Fin.coe_castLE, eqn] using copy

theorem exactThreeLinesFromReceipts
    (induced : InducedBound)
    (majority : MajorityFloor)
    (reduceCrown : CrownReduction) :
∀ (n m : Nat), 3 ≤ n → 3 ≤ m →
  let A := fun (u : Fin n) (v : Fin m) =>
    (64478 : Nat).testBit (4 * min u.val 3 + min v.val 3)
  PEqualNP.Represents.RepSizeAtMost A (n + m + 1) ∧
    ¬ PEqualNP.Represents.RepSizeAtMost A (n + m)
 := by
  intro n m hn hm
  exact exactFromThree induced majority reduceCrown n m hn hm

end S30581

theorem S30581 :
  ∀ (n m : Nat), 3 ≤ n → 3 ≤ m →
    let A := fun (u : Fin n) (v : Fin m) =>
      (64478 : Nat).testBit (4 * min u.val 3 + min v.val 3)
    PEqualNP.Represents.RepSizeAtMost A (n + m + 1) ∧
      ¬ PEqualNP.Represents.RepSizeAtMost A (n + m) :=
  S30581.exactThreeLinesFromReceipts
    RepInduced.induced
    L100
    S18508

end PEqualNP.Outside.L_meta_27804

theorem PEqualNP.Outside.L_meta_27804 :
(∀ (n m : Nat), 4 ≤ n → 4 ≤ m →
  let A := fun (u : Fin n) (v : Fin m) =>
    (64478 : Nat).testBit (4 * min u.val 3 + min v.val 3)
  PEqualNP.Represents.RepSizeAtMost A (n + m + 1) ∧
    ¬ PEqualNP.Represents.RepSizeAtMost A (n + m)) := by
  intro n m hn hm
  exact PEqualNP.Outside.L_meta_27804.S30581 n m (by omega) (by omega)
