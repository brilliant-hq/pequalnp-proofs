import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_42686_aux

-- Row, parity, and gate construction helpers adapted from lean/PEqualNP/Outside/L_meta_42687.lean at 036ab8b318851b49a3c9d09ef7f5972dd8c3d253.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
def nonlinear (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def valid (w : Nat) (C : Circuit) : Prop :=
  ReadsBack w C ∧ ∀ g ∈ C.gates, g.inputs.length ≤ 2

def depthList (w : Nat) (gs : List Gate) : List Nat :=
  gs.foldl (fun (ds : List Nat) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate w 0)
def xorList (l : List Bool) : Bool :=
  l.foldl xor false

def xorFin {m : Nat} (f : Fin m → Bool) : Bool :=
  (List.finRange m).foldl (fun a i => xor a (f i)) false

lemma foldl_xor_init (l : List Bool) (a : Bool) :
    l.foldl xor a = xor a (l.foldl xor false) := by
  induction l generalizing a with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldl_cons, List.foldl_cons, Bool.false_xor, ih, ih b]
    cases a <;> cases b <;> cases bs.foldl xor false <;> rfl

lemma foldl_map_xor_init {α : Type} (l : List α) (f : α → Bool) (a : Bool) :
    l.foldl (fun s x => xor s (f x)) a = xor a (l.foldl (fun s x => xor s (f x)) false) := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, List.foldl_cons, Bool.false_xor, ih, ih (f x)]
    cases a <;> cases f x <;> cases xs.foldl (fun s y => xor s (f y)) false <;> rfl

lemma foldl_map_xor_append {α : Type} (l1 l2 : List α) (f : α → Bool) :
    (l1 ++ l2).foldl (fun s x => xor s (f x)) false =
      xor (l1.foldl (fun s x => xor s (f x)) false)
          (l2.foldl (fun s x => xor s (f x)) false) := by
  rw [List.foldl_append, foldl_map_xor_init]

lemma foldl_map_xor_xor {α : Type} (l : List α) (f g : α → Bool) :
    l.foldl (fun s x => xor s (xor (f x) (g x))) false =
      xor (l.foldl (fun s x => xor s (f x)) false)
          (l.foldl (fun s x => xor s (g x)) false) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, Bool.false_xor]
    rw [foldl_map_xor_init xs (fun y => xor (f y) (g y)), foldl_map_xor_init xs f,
      foldl_map_xor_init xs g, ih]
    cases f x <;> cases g x <;>
      cases xs.foldl (fun s y => xor s (f y)) false <;>
      cases xs.foldl (fun s y => xor s (g y)) false <;> rfl

lemma foldl_map_xor_false {α : Type} (l : List α) :
    l.foldl (fun s (_ : α) => xor s false) false = false := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, Bool.false_xor, ih]

lemma foldl_map_xor_and_left {α : Type} (l : List α) (c : Bool) (f : α → Bool) :
    l.foldl (fun s x => xor s (c && f x)) false =
      (c && l.foldl (fun s x => xor s (f x)) false) := by
  cases c
  · exact foldl_map_xor_false l
  · simp

lemma foldl_map_xor_and_right {α : Type} (l : List α) (f : α → Bool) (c : Bool) :
    l.foldl (fun s x => xor s (f x && c)) false =
      (l.foldl (fun s x => xor s (f x)) false && c) := by
  cases c
  · simp only [Bool.and_false]; exact foldl_map_xor_false l
  · simp

lemma foldl_map_xor_congr {α : Type} (l : List α) (f g : α → Bool)
    (h : ∀ x ∈ l, f x = g x) :
    l.foldl (fun s x => xor s (f x)) false = l.foldl (fun s x => xor s (g x)) false := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, Bool.false_xor]
    rw [h x List.mem_cons_self, foldl_map_xor_init xs f, foldl_map_xor_init xs g,
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

lemma foldl_map_xor_eq_false {α : Type} (l : List α) (f : α → Bool)
    (h : ∀ x ∈ l, f x = false) :
    l.foldl (fun s x => xor s (f x)) false = false := by
  rw [foldl_map_xor_congr l f (fun _ => false) h, foldl_map_xor_false]

lemma foldl_map_xor_single {α : Type} [DecidableEq α] (l : List α) (hl : l.Nodup)
    (a : α) (ha : a ∈ l) (c : Bool) :
    l.foldl (fun s x => xor s (if x = a then c else false)) false = c := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    rw [List.foldl_cons, foldl_map_xor_init]
    rcases List.mem_cons.mp ha with rfl | hmem
    · simp only [ite_true, Bool.false_xor]
      rw [foldl_map_xor_eq_false xs _ (fun y hy => by
        have hne : y ≠ a := fun he => hl.1 (he ▸ hy)
        simp [hne])]
      simp
    · have hne : x ≠ a := fun he => hl.1 (he ▸ hmem)
      simp only [hne, ite_false, Bool.false_xor]
      exact ih hl.2 hmem

lemma xorFin_xor {m : Nat} (f g : Fin m → Bool) :
    xorFin (fun i => xor (f i) (g i)) = xor (xorFin f) (xorFin g) :=
  foldl_map_xor_xor _ f g

lemma xorFin_false {m : Nat} : xorFin (fun _ : Fin m => false) = false :=
  foldl_map_xor_false _

lemma xorFin_congr {m : Nat} (f g : Fin m → Bool) (h : ∀ i, f i = g i) :
    xorFin f = xorFin g :=
  foldl_map_xor_congr _ f g (fun i _ => h i)

lemma xorFin_cast {m1 m2 : Nat} (h : m1 = m2) (f : Fin m1 → Bool) (g : Fin m2 → Bool)
    (hfg : ∀ i (hi1 : i < m1) (hi2 : i < m2), f ⟨i, hi1⟩ = g ⟨i, hi2⟩) :
    xorFin f = xorFin g := by
  subst h
  exact xorFin_congr f g (fun i => hfg i.val i.isLt i.isLt)

lemma xorFin_eq_false {m : Nat} (f : Fin m → Bool) (h : ∀ i, f i = false) :
    xorFin f = false :=
  foldl_map_xor_eq_false _ f (fun i _ => h i)

lemma xorFin_and_left {m : Nat} (c : Bool) (f : Fin m → Bool) :
    xorFin (fun i => c && f i) = (c && xorFin f) :=
  foldl_map_xor_and_left _ c f

lemma xorFin_and_right {m : Nat} (f : Fin m → Bool) (c : Bool) :
    xorFin (fun i => f i && c) = (xorFin f && c) :=
  foldl_map_xor_and_right _ f c

lemma xorFin_single {m : Nat} (j : Fin m) (c : Bool) :
    xorFin (fun i : Fin m => if i = j then c else false) = c :=
  foldl_map_xor_single (List.finRange m) (List.nodup_finRange m) j (List.mem_finRange j) c

lemma xorFin_single' {m : Nat} (j : Fin m) (f : Fin m → Bool) (h : ∀ i, i ≠ j → f i = false) :
    xorFin f = f j := by
  have heq : xorFin f = xorFin (fun i => if i = j then f j else false) :=
    xorFin_congr f _ (fun i => by by_cases hij : i = j <;> simp [hij, h])
  rw [heq, xorFin_single]

lemma xorFin_succ {m : Nat} (f : Fin (m + 1) → Bool) :
    xorFin f = xor (xorFin (fun i : Fin m => f i.castSucc)) (f (Fin.last m)) := by
  unfold xorFin
  have hfr : List.finRange (m + 1) =
      (List.finRange m).map Fin.castSucc ++ [Fin.last m] := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      by_cases hi : i < m
      · rw [List.getElem_append_left (by simp [hi])]
        apply Fin.ext
        simp
      · have hie : i = m := by simp at h1; omega
        subst hie
        rw [List.getElem_append_right (by simp)]
        simp [Fin.ext_iff]
  rw [hfr, foldl_map_xor_append]
  have h1 : ((List.finRange m).map Fin.castSucc).foldl (fun s x => xor s (f x)) false =
      (List.finRange m).foldl (fun s i => xor s (f i.castSucc)) false := by
    rw [List.foldl_map]
  rw [h1]
  simp

lemma xorFin_head_tail {m : Nat} (g : Fin (m + 1) → Bool) :
    xorFin g = xor (g ⟨0, Nat.zero_lt_succ m⟩) (xorFin (fun j : Fin m => g j.succ)) := by
  unfold xorFin
  have hfr : List.finRange (m + 1) = ⟨0, Nat.zero_lt_succ m⟩ :: (List.finRange m).map Fin.succ := by
    apply List.ext_getElem
    · simp
    · intro idx _ _; cases idx <;> apply Fin.ext <;> simp
  rw [hfr, List.foldl_cons, foldl_map_xor_init, List.foldl_map, Bool.false_xor]

lemma xorFin_const (m : Nat) (c : Bool) :
    xorFin (fun _ : Fin m => c) = (c && decide (m % 2 = 1)) := by
  induction m with
  | zero => simp [xorFin]
  | succ m ih =>
    rw [xorFin_succ, ih]
    cases c
    · rfl
    · simp only [Bool.true_and]
      by_cases hm : m % 2 = 1
      · have hm1 : (m + 1) % 2 ≠ 1 := by omega
        simp [hm, hm1]
      · have hm1 : (m + 1) % 2 = 1 := by omega
        simp [hm, hm1]

lemma xorFin_first {m : Nat} (hm : 1 ≤ m) (f : Fin m → Bool) :
    xorFin f = xor (f ⟨0, by omega⟩) (xorFin (fun j : Fin (m - 1) => f ⟨j.val + 1, by omega⟩)) := by
  have he : m = (m - 1) + 1 := by omega
  rw [xorFin_cast he f (fun j : Fin ((m - 1) + 1) => f ⟨j.val, by omega⟩) (fun _ _ _ => rfl),
    xorFin_head_tail]
  apply congrArg (xor _)
  apply xorFin_congr; intro j; exact congrArg f (Fin.ext (by simp only [Fin.val_succ]))

lemma xorFin_last {m : Nat} (hm : 1 ≤ m) (f : Fin m → Bool) :
    xorFin f = xor (xorFin (fun j : Fin (m - 1) => f ⟨j.val, by omega⟩)) (f ⟨m - 1, by omega⟩) := by
  have he : m = (m - 1) + 1 := by omega
  rw [xorFin_cast he f (fun j : Fin ((m - 1) + 1) => f ⟨j.val, by omega⟩) (fun _ _ _ => rfl),
    xorFin_succ]
  rfl

lemma xorFin_ends {m : Nat} (hm : 2 ≤ m) (f : Fin m → Bool) :
    xorFin f = xor (f ⟨0, by omega⟩)
                   (xor (xorFin (fun j : Fin (m - 2) => f ⟨j.val + 1, by omega⟩))
                        (f ⟨m - 1, by omega⟩)) := by
  rw [xorFin_first (by omega) f, xorFin_last (by omega)]
  apply congrArg (xor _)
  have h1 : xorFin (fun j : Fin (m - 1 - 1) => f ⟨j.val + 1, by omega⟩) =
      xorFin (fun j : Fin (m - 2) => f ⟨j.val + 1, by omega⟩) :=
    xorFin_cast (by omega) _ _ (fun _ _ _ => rfl)
  have h2 : f ⟨m - 1 - 1 + 1, by omega⟩ = f ⟨m - 1, by omega⟩ :=
    congrArg f (Fin.ext (by dsimp only; omega))
  rw [h1, h2]

lemma xorFin_swap {a b : Nat} (f : Fin a → Fin b → Bool) :
    xorFin (fun i => xorFin (f i)) = xorFin (fun j => xorFin (fun i => f i j)) := by
  induction a with
  | zero =>
    have h1 : xorFin (fun i : Fin 0 => xorFin (f i)) = false := rfl
    have h2 : xorFin (fun j : Fin b => xorFin (fun i : Fin 0 => f i j)) = false :=
      xorFin_eq_false _ (fun _ => rfl)
    rw [h1, h2]
  | succ a ih =>
    rw [xorFin_succ]
    rw [ih (fun i j => f i.castSucc j)]
    rw [← xorFin_xor]
    apply xorFin_congr
    intro j
    rw [xorFin_succ]

lemma xorFin_prod {a b : Nat} (hbpos : 0 < b) (f : Fin a → Fin b → Bool) :
    xorFin (fun p : Fin (a * b) =>
      f ⟨p.val / b, Nat.div_lt_of_lt_mul (Nat.mul_comm a b ▸ p.isLt)⟩
        ⟨p.val % b, Nat.mod_lt _ hbpos⟩) =
      xorFin (fun i : Fin a => xorFin (f i)) := by
  induction a with
  | zero =>
    exact (xorFin_cast (Nat.zero_mul b) _ (fun _ : Fin 0 => false) (fun _ hi _ => by omega)).trans rfl
  | succ a ih =>
    rw [xorFin_succ]
    have hmul : (a + 1) * b = a * b + b := Nat.succ_mul a b
    have hbmul : b * (a + 1) = a * b + b := by rw [Nat.mul_comm, Nat.succ_mul]
    have hsplit : ∀ (N M : Nat) (g : Fin (N + M) → Bool),
        xorFin g = xor (xorFin (fun i : Fin N => g ⟨i.val, by omega⟩))
                       (xorFin (fun j : Fin M => g ⟨N + j.val, by omega⟩)) := by
      intro N M g
      induction M with
      | zero =>
        simp only [Nat.add_zero]
        have h0 : xorFin (fun j : Fin 0 => g ⟨N + j.val, by omega⟩) = false := rfl
        rw [h0, Bool.xor_false]
        exact xorFin_congr _ _ (fun i => rfl)
      | succ M ihM =>
        rw [xorFin_succ (fun j : Fin (M + 1) => g ⟨N + j.val, by omega⟩)]
        have hgoal := xorFin_succ (fun x : Fin (N + M + 1) => g ⟨x.val, by omega⟩)
        have hcast : xorFin g = xorFin (fun x : Fin (N + M + 1) => g ⟨x.val, by omega⟩) :=
          xorFin_congr _ _ (fun i => rfl)
        rw [hcast, hgoal]
        have hih := ihM (fun x : Fin (N + M) => g ⟨x.val, by omega⟩)
        have hcs : xorFin (fun i : Fin (N + M) => g ⟨i.castSucc.val, by omega⟩) =
            xorFin (fun i : Fin (N + M) => g ⟨i.val, by omega⟩) :=
          xorFin_congr _ _ (fun _ => rfl)
        rw [hcs, hih]
        simp only [Fin.last, Bool.xor_assoc]
        rfl
    have hcast2 : xorFin (fun p : Fin ((a + 1) * b) =>
        f ⟨p.val / b, Nat.div_lt_of_lt_mul (Nat.mul_comm (a + 1) b ▸ p.isLt)⟩
          ⟨p.val % b, Nat.mod_lt _ hbpos⟩) =
      xorFin (fun p : Fin (a * b + b) =>
        f ⟨p.val / b, Nat.div_lt_of_lt_mul (show p.val < b * (a + 1) by omega)⟩
          ⟨p.val % b, Nat.mod_lt _ hbpos⟩) :=
      xorFin_cast hmul _ _ (fun _ _ _ => rfl)
    rw [hcast2, hsplit (a * b) b]
    congr 1
    · rw [← ih (fun i j => f i.castSucc j)]
      apply xorFin_congr
      intro p
      rfl
    · apply xorFin_congr
      intro j
      have hdiv : (a * b + j.val) / b = a := by
        rw [Nat.mul_comm, Nat.mul_add_div hbpos, Nat.div_eq_of_lt j.isLt, Nat.add_zero]
      have hmod : (a * b + j.val) % b = j.val := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]
      congr 1
      · exact Fin.ext hdiv
      · exact Fin.ext hmod

lemma xorFin_finset_card {k : Nat} (S : Finset (Fin k)) (f : Fin k → Bool) :
    decide ((S.filter (fun i => f i = true)).card % 2 = 1) =
      xorFin (fun i : Fin k => decide (i ∈ S) && f i) := by
  induction S using Finset.induction_on with
  | empty =>
    simp [xorFin_false]
  | @insert a s ha ih =>
    have h1 : ((insert a s).filter (fun i => f i = true)).card =
        (s.filter (fun i => f i = true)).card + (f a).toNat := by
      rw [Finset.filter_insert]
      cases hfa : f a
      · simp
      · simp only [ite_true, Bool.toNat_true]
        rw [Finset.card_insert_of_notMem (by simp [ha])]
    have h2 : decide (((s.filter (fun i => f i = true)).card + (f a).toNat) % 2 = 1) =
        xor (decide ((s.filter (fun i => f i = true)).card % 2 = 1)) (f a) := by
      cases hfa : f a
      · simp [Bool.toNat]
      · simp only [Bool.toNat, Bool.xor_true]
        by_cases hc : (s.filter (fun i => f i = true)).card % 2 = 1
        · have hc1 : ((s.filter (fun i => f i = true)).card + 1) % 2 ≠ 1 := by omega
          simp [hc, hc1]
        · have hc1 : ((s.filter (fun i => f i = true)).card + 1) % 2 = 1 := by omega
          simp [hc, hc1]
    have h3 : xorFin (fun i : Fin k => decide (i ∈ insert a s) && f i) =
        xor (xorFin (fun i : Fin k => decide (i ∈ s) && f i))
            (xorFin (fun i : Fin k => if i = a then f a else false)) := by
      rw [← xorFin_xor]
      apply xorFin_congr
      intro i
      by_cases hia : i = a
      · subst hia; simp [ha]
      · simp [hia]
    rw [h1, h2, ih, h3, xorFin_single]

def dot {N : Nat} (u v : Fin N → Bool) : Bool :=
  xorFin (fun i => u i && v i)

lemma dot_xor_left {N : Nat} (u1 u2 v : Fin N → Bool) :
    dot (fun i => xor (u1 i) (u2 i)) v = xor (dot u1 v) (dot u2 v) := by
  unfold dot
  rw [← xorFin_xor]
  apply xorFin_congr
  intro i
  dsimp only
  cases u1 i <;> cases u2 i <;> cases v i <;> rfl

lemma dot_xor_right {N : Nat} (u v1 v2 : Fin N → Bool) :
    dot u (fun i => xor (v1 i) (v2 i)) = xor (dot u v1) (dot u v2) := by
  unfold dot
  rw [← xorFin_xor]
  apply xorFin_congr
  intro i
  dsimp only
  cases u i <;> cases v1 i <;> cases v2 i <;> rfl

lemma dot_zero_right {N : Nat} (u : Fin N → Bool) :
    dot u (fun _ => false) = false := by
  unfold dot
  exact xorFin_eq_false _ (fun i => by simp)

def eVec {N : Nat} (p : Fin N) : Fin N → Bool :=
  fun i => decide (i = p)

lemma dot_eVec {N : Nat} (u : Fin N → Bool) (p : Fin N) :
    dot u (eVec p) = u p := by
  unfold dot eVec
  rw [xorFin_single' p]
  · simp
  · intro i hi; simp [hi]

def IsAffine {N : Nat} (f : (Fin N → Bool) → Bool) : Prop :=
  ∃ (c : Bool) (w : Fin N → Bool), ∀ y, f y = xor c (dot w y)

def pol {N : Nat} (f : (Fin N → Bool) → Bool) (a b : Fin N → Bool) : Bool :=
  xor (xor (f (fun i => xor (a i) (b i))) (f a))
      (xor (f b) (f (fun _ => false)))

def rank2 {N : Nat} (L R : Fin N → Bool) (a b : Fin N → Bool) : Bool :=
  xor (dot L a && dot R b) (dot R a && dot L b)

lemma isAffine_const {N : Nat} (c : Bool) : IsAffine (fun _ : Fin N → Bool => c) :=
  ⟨c, fun _ => false, fun y => by simp [dot, xorFin_false]⟩

lemma isAffine_coord {N : Nat} (p : Fin N) : IsAffine (fun y : Fin N → Bool => y p) :=
  ⟨false, eVec p, fun y => by
    simp only [Bool.false_xor, dot, eVec]
    rw [xorFin_single' p]
    · simp
    · intro i hi; simp [hi]⟩

lemma isAffine_xor {N : Nat} {f g : (Fin N → Bool) → Bool}
    (hf : IsAffine f) (hg : IsAffine g) :
    IsAffine (fun y => xor (f y) (g y)) := by
  rcases hf with ⟨cf, wf, hfe⟩
  rcases hg with ⟨cg, wg, hge⟩
  refine ⟨xor cf cg, fun i => xor (wf i) (wg i), fun y => ?_⟩
  dsimp only
  rw [hfe y, hge y, dot_xor_left]
  cases cf <;> cases cg <;> cases dot wf y <;> cases dot wg y <;> rfl

lemma isAffine_and_const {N : Nat} (c : Bool) {f : (Fin N → Bool) → Bool}
    (hf : IsAffine f) : IsAffine (fun y => c && f y) := by
  cases c
  · simpa using isAffine_const false
  · simpa using hf

lemma isAffine_not {N : Nat} {f : (Fin N → Bool) → Bool}
    (hf : IsAffine f) : IsAffine (fun y => !(f y)) := by
  have h := isAffine_xor (isAffine_const true) hf
  simpa only [Bool.true_xor] using h

lemma isAffine_xorFin {N m : Nat} (F : Fin m → (Fin N → Bool) → Bool)
    (hF : ∀ i, IsAffine (F i)) : IsAffine (fun y => xorFin (fun i => F i y)) := by
  induction m with
  | zero => exact isAffine_const false
  | succ m ih =>
    have h1 := ih (fun i => F i.castSucc) (fun i => hF i.castSucc)
    have h2 := hF (Fin.last m)
    have h3 := isAffine_xor h1 h2
    have heq : (fun y => xorFin (fun i => F i y)) =
        (fun y => xor (xorFin (fun i : Fin m => F i.castSucc y)) (F (Fin.last m) y)) := by
      funext y; exact xorFin_succ (fun i => F i y)
    rw [heq]; exact h3

lemma isAffine_comp {N M : Nat} {f : (Fin M → Bool) → Bool} {g : (Fin N → Bool) → (Fin M → Bool)}
    (hf : IsAffine f) (hg : ∀ i, IsAffine (fun y => g y i)) :
    IsAffine (fun y => f (g y)) := by
  rcases hf with ⟨c, w, hfe⟩
  have heq : (fun y => f (g y)) = (fun y => xor c (xorFin (fun i => w i && g y i))) := by
    funext y; exact hfe (g y)
  rw [heq]
  exact isAffine_xor (isAffine_const c) (isAffine_xorFin _ (fun i => isAffine_and_const (w i) (hg i)))

lemma pol_xor {N : Nat} (f g : (Fin N → Bool) → Bool) (a b : Fin N → Bool) :
    pol (fun y => xor (f y) (g y)) a b = xor (pol f a b) (pol g a b) := by
  unfold pol; dsimp only
  cases f (fun i => xor (a i) (b i)) <;> cases g (fun i => xor (a i) (b i)) <;>
    cases f a <;> cases g a <;> cases f b <;> cases g b <;>
    cases f (fun _ => false) <;> cases g (fun _ => false) <;> rfl

lemma pol_and_const {N : Nat} (c : Bool) (f : (Fin N → Bool) → Bool) (a b : Fin N → Bool) :
    pol (fun y => c && f y) a b = (c && pol f a b) := by
  cases c <;> simp [pol]

lemma pol_const {N : Nat} (c : Bool) (a b : Fin N → Bool) :
    pol (fun _ : Fin N → Bool => c) a b = false := by
  unfold pol; dsimp only; cases c <;> rfl

lemma pol_affine {N : Nat} {f : (Fin N → Bool) → Bool} (hf : IsAffine f)
    (a b : Fin N → Bool) : pol f a b = false := by
  rcases hf with ⟨c, w, hfe⟩
  unfold pol
  simp only [hfe, dot_xor_right, dot_zero_right]
  cases c <;> cases dot w a <;> cases dot w b <;> rfl

lemma pol_and_affine {N : Nat} {f g : (Fin N → Bool) → Bool}
    {cf cg : Bool} {lf lg : Fin N → Bool}
    (hf : ∀ y, f y = xor cf (dot lf y)) (hg : ∀ y, g y = xor cg (dot lg y))
    (a b : Fin N → Bool) :
    pol (fun y => f y && g y) a b = rank2 lf lg a b := by
  unfold pol rank2
  simp only [hf, hg, dot_xor_right, dot_zero_right]
  cases cf <;> cases cg <;> cases dot lf a <;> cases dot lf b <;>
    cases dot lg a <;> cases dot lg b <;> rfl

lemma gate_eval_1 (op : GateOp) (a : Bool) :
    op.eval [a] = xor (op.eval [false]) (xor (op.eval [false]) (op.eval [true]) && a) := by
  cases a <;> cases op.eval [false] <;> cases op.eval [true] <;> rfl

lemma gate_eval_2 (op : GateOp) (a b : Bool) :
    op.eval [a, b] =
      xor (op.eval [false, false])
        (xor (xor (op.eval [false, false]) (op.eval [true, false]) && a)
          (xor (xor (op.eval [false, false]) (op.eval [false, true]) && b)
            (xor (xor (op.eval [false, false]) (op.eval [false, true]))
                 (xor (op.eval [true, false]) (op.eval [true, true])) && (a && b)))) := by
  cases a <;> cases b <;>
    cases op.eval [false, false] <;> cases op.eval [false, true] <;>
    cases op.eval [true, false] <;> cases op.eval [true, true] <;> rfl

lemma depthList_length (w : Nat) (gs : List Gate) :
    (depthList w gs).length = w + gs.length := by
  unfold depthList
  suffices ∀ (gs : List Gate) (acc : List Nat),
      (gs.foldl (fun (ds : List Nat) g =>
        ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat]) acc).length =
      acc.length + gs.length by
    simpa [List.length_replicate] using this gs (List.replicate w 0)
  intro gs
  induction gs with
  | nil => intro acc; simp
  | cons g gs ih =>
    intro acc
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma wires_length (gs : List Gate) (x : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length =
      x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldr_max_le_iff (l : List Nat) (k : Nat) :
    l.foldr max 0 ≤ k ↔ ∀ x ∈ l, x ≤ k := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons, Nat.max_le, ih, List.mem_cons, forall_eq_or_imp]

lemma depthList_getD_le_depth (w : Nat) (gs : List Gate) (i : Nat) :
    (depthList w gs).getD i 0 ≤ (depthList w gs).foldr max 0 := by
  by_cases hi : i < (depthList w gs).length
  · rw [List.getD_eq_getElem _ _ hi]
    exact (foldr_max_le_iff _ _).mp (le_refl _) _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
    omega

lemma getD_append_lt {α : Type} (l : List α) (v d : α) {i : Nat} (hi : i < l.length) :
    (l ++ [v]).getD i d = l.getD i d := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi,
    List.getElem_append_left hi]

lemma getD_append_eq {α : Type} (l : List α) (v d : α) :
    (l ++ [v]).getD l.length d = v := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]
  simp

lemma ite_pos {α : Type} {P : Prop} [Decidable P] {a b : α} (h : P) :
    (if P then a else b) = a := by simp [h]

lemma ite_neg {α : Type} {P : Prop} [Decidable P] {a b : α} (h : ¬P) :
    (if P then a else b) = b := by simp [h]

lemma dite_pos {α : Type} {P : Prop} [Decidable P] {a : P → α} {b : ¬P → α} (h : P) :
    (if hp : P then a hp else b hp) = a h := by simp [h]

lemma dite_neg {α : Type} {P : Prop} [Decidable P] {a : P → α} {b : ¬P → α} (h : ¬P) :
    (if hp : P then a hp else b hp) = b h := by simp [h]

lemma hk_of {r k : Nat} (hr : 2 ≤ r) (hk3 : k = 3 * r) : 0 < k := by omega

section RowAlg

variable {r k : Nat} (hk : 0 < k)

def ix (i : Nat) : Fin k := ⟨i % k, Nat.mod_lt _ hk⟩
def add (u v : Fin k → Bool) (i : Fin k) : Bool := xor (u i) (v i)
def mix (w : Fin k → Bool) (i : Fin k) : Bool :=
  xor (w (ix hk (i.val + k - 1))) (xor (w i) (w (ix hk (i.val + 1))))
def rot (x : Fin k → Bool) (i : Fin k) : Bool := x (ix hk (i.val + k - 1))
def chi (w : Fin k → Bool) (i : Fin k) : Bool :=
  xor (w i) (!(w (ix hk (i.val + 1))) && w (ix hk (i.val + 2)))
def row (u x : Fin k → Bool) : Fin k → Bool :=
  add (chi hk (mix hk (add u (rot hk x)))) x
def vMask : Fin k → Bool := fun i => decide (i.val ≠ 1)
def diffFn (u x : Fin k → Bool) : Fin k → Bool :=
  add (row hk u x) (row hk (add u vMask) x)
def neededSet (r k : Nat) : Finset (Fin k) :=
  Finset.univ.filter (fun i : Fin k =>
    if i.val = 0 ∨ i.val = k - 1 then r % 2 = 0
    else i.val = 1 ∨ i.val = k - 2 ∨ i.val % 3 ≠ 1)

lemma ix_eq_of_lt {i : Nat} (hi : i < k) : ix hk i = ⟨i, hi⟩ :=
  Fin.ext (Nat.mod_eq_of_lt hi)

lemma ix_mod_eq {a b : Nat} (h : a % k = b % k) : ix hk a = ix hk b :=
  Fin.ext h

lemma mix_add (w1 w2 : Fin k → Bool) :
    mix hk (add w1 w2) = add (mix hk w1) (mix hk w2) := by
  funext i; unfold mix add; dsimp only
  cases w1 (ix hk (i.val + k - 1)) <;> cases w2 (ix hk (i.val + k - 1)) <;>
    cases w1 i <;> cases w2 i <;>
    cases w1 (ix hk (i.val + 1)) <;> cases w2 (ix hk (i.val + 1)) <;> rfl

lemma mix_vMask (hr : 2 ≤ r) (hk3 : k = 3 * r) (i : Fin k) :
    mix hk vMask i = decide (3 ≤ i.val) := by
  unfold mix vMask
  have h1 : (ix hk (i.val + k - 1)).val = if i.val = 0 then k - 1 else i.val - 1 := by
    dsimp only [ix]; split_ifs with h0
    · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    · rw [show i.val + k - 1 = (i.val - 1) + k by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
  have h2 : (ix hk (i.val + 1)).val = if i.val = k - 1 then 0 else i.val + 1 := by
    dsimp only [ix]; split_ifs with hlast
    · rw [show i.val + 1 = k by omega, Nat.mod_self]
    · rw [Nat.mod_eq_of_lt (by omega)]
  rw [h1, h2]
  by_cases hi0 : i.val = 0
  · have hn1 : k - 1 ≠ 1 := by omega
    have hn2 : ¬(0 = k - 1) := by omega
    simp [hi0, hn1, hn2]
  · by_cases hi1 : i.val = 1
    · have hn2 : ¬(1 = k - 1) := by omega
      simp [hi1, hn2]
    · by_cases hi2 : i.val = 2
      · have hn2 : ¬(2 = k - 1) := by omega
        simp [hi2, hn2]
      · by_cases hil : i.val = k - 1
        · have hn0 : k - 1 ≠ 0 := by omega
          have hn1 : k - 1 ≠ 1 := by omega
          have hge3 : 3 ≤ k - 1 := by omega
          have hm1 : k - 1 - 1 ≠ 1 := by omega
          simp [hil, hn0, hn1, hge3, hm1]
        · have hge3 : 3 ≤ i.val := by omega
          have hne1 : i.val - 1 ≠ 1 := by omega
          simp [hi0, hi1, hil, hge3, hne1]

lemma diffFn_eq (hr : 2 ≤ r) (hk3 : k = 3 * r) (u x : Fin k → Bool) (i : Fin k) :
    let w := mix hk (add u (rot hk x))
    diffFn hk u x i =
      if i.val = 0 then false
      else if i.val = 1 then !(w (ix hk 2))
      else if i.val = 2 then xor (w (ix hk 3)) (w (ix hk 4))
      else if i.val < k - 2 then !(xor (w (ix hk (i.val + 1))) (w (ix hk (i.val + 2))))
      else if i.val = k - 2 then !(w (ix hk 0))
      else true := by
  intro w
  have h1 : add (add u vMask) (rot hk x) = add (add u (rot hk x)) vMask := by
    funext j; unfold add; cases u j <;> cases vMask j <;> cases rot hk x j <;> rfl
  have h2 : diffFn hk u x i = xor (chi hk w i) (chi hk (add w (mix hk vMask)) i) := by
    unfold diffFn row
    rw [h1, mix_add hk (add u (rot hk x)) vMask]
    change xor (xor (chi hk w i) (x i)) (xor (chi hk (add w (mix hk vMask)) i) (x i)) =
      xor (chi hk w i) (chi hk (add w (mix hk vMask)) i)
    cases chi hk w i <;> cases chi hk (add w (mix hk vMask)) i <;> cases x i <;> rfl
  rw [h2]
  unfold chi add
  rw [mix_vMask hk hr hk3, mix_vMask hk hr hk3, mix_vMask hk hr hk3]
  have hp1 : (ix hk (i.val + 1)).val = if i.val = k - 1 then 0 else i.val + 1 := by
    dsimp only [ix]; split_ifs with hl
    · rw [show i.val + 1 = k by omega, Nat.mod_self]
    · rw [Nat.mod_eq_of_lt (by omega)]
  have hp2 : (ix hk (i.val + 2)).val =
      if i.val = k - 2 then 0 else if i.val = k - 1 then 1 else i.val + 2 := by
    dsimp only [ix]; split_ifs with h1 h2
    · rw [show i.val + 2 = k by omega, Nat.mod_self]
    · rw [show i.val + 2 = 1 + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · rw [Nat.mod_eq_of_lt (by omega)]
  by_cases hi0 : i.val = 0
  · have h1v : (ix hk (i.val + 1)).val = 1 := by rw [hp1]; split_ifs <;> omega
    have h2v : (ix hk (i.val + 2)).val = 2 := by rw [hp2]; split_ifs <;> omega
    rw [h1v, h2v, hi0]
    simp only [ite_true]
    have hd0 : decide (3 ≤ 0) = false := rfl
    have hd1 : decide (3 ≤ 1) = false := rfl
    have hd2 : decide (3 ≤ 2) = false := rfl
    rw [hd0, hd1, hd2]
    cases w i <;> cases w (ix hk (0 + 1)) <;> cases w (ix hk (0 + 2)) <;> rfl
  · by_cases hi1 : i.val = 1
    · have h1v : (ix hk (i.val + 1)).val = 2 := by rw [hp1]; split_ifs <;> omega
      have h2v : (ix hk (i.val + 2)).val = 3 := by rw [hp2]; split_ifs <;> omega
      have heq1 : ix hk (i.val + 1) = ix hk 2 := by rw [hi1]
      rw [h1v, h2v, heq1, ite_neg hi0, ite_pos hi1, hi1]
      have hd0 : decide (3 ≤ 1) = false := rfl
      have hd1 : decide (3 ≤ 2) = false := rfl
      have hd2 : decide (3 ≤ 3) = true := rfl
      rw [hd0, hd1, hd2]
      cases w i <;> cases w (ix hk 2) <;> cases w (ix hk (1 + 2)) <;> rfl
    · by_cases hi2 : i.val = 2
      · have h1v : (ix hk (i.val + 1)).val = 3 := by rw [hp1]; split_ifs <;> omega
        have h2v : (ix hk (i.val + 2)).val = 4 := by rw [hp2]; split_ifs <;> omega
        have heq1 : ix hk (i.val + 1) = ix hk 3 := by rw [hi2]
        have heq2 : ix hk (i.val + 2) = ix hk 4 := by rw [hi2]
        rw [h1v, h2v, heq1, heq2, ite_neg hi0, ite_neg hi1, ite_pos hi2, hi2]
        have hd0 : decide (3 ≤ 2) = false := rfl
        have hd1 : decide (3 ≤ 3) = true := rfl
        have hd2 : decide (3 ≤ 4) = true := rfl
        rw [hd0, hd1, hd2]
        cases w i <;> cases w (ix hk 3) <;> cases w (ix hk 4) <;> rfl
      · by_cases hilt : i.val < k - 2
        · have hge3 : 3 ≤ i.val := by omega
          have h1v : 3 ≤ (ix hk (i.val + 1)).val := by rw [hp1]; split_ifs <;> omega
          have h2v : 3 ≤ (ix hk (i.val + 2)).val := by rw [hp2]; split_ifs <;> omega
          rw [ite_neg hi0, ite_neg hi1, ite_neg hi2, ite_pos hilt,
            decide_eq_true hge3, decide_eq_true h1v, decide_eq_true h2v]
          cases w i <;> cases w (ix hk (i.val + 1)) <;> cases w (ix hk (i.val + 2)) <;> rfl
        · by_cases hik2 : i.val = k - 2
          · have hge3 : 3 ≤ i.val := by omega
            have h1v : 3 ≤ (ix hk (i.val + 1)).val := by rw [hp1]; split_ifs <;> omega
            have h2v : ¬(3 ≤ (ix hk (i.val + 2)).val) := by rw [hp2]; split_ifs; omega
            have heq2 : ix hk (i.val + 2) = ix hk 0 := ix_mod_eq hk (by rw [hik2, show k - 2 + 2 = k by omega, Nat.mod_self, Nat.zero_mod])
            rw [ite_neg hi0, ite_neg hi1, ite_neg hi2, ite_neg hilt, ite_pos hik2,
              decide_eq_true hge3, decide_eq_true h1v, decide_eq_false h2v, heq2]
            cases w i <;> cases w (ix hk (i.val + 1)) <;> cases w (ix hk 0) <;> rfl
          · have hik1 : i.val = k - 1 := by omega
            have hge3 : 3 ≤ i.val := by omega
            have h1v : ¬(3 ≤ (ix hk (i.val + 1)).val) := by rw [hp1]; split_ifs; omega
            have h2v : ¬(3 ≤ (ix hk (i.val + 2)).val) := by rw [hp2]; split_ifs; omega
            rw [ite_neg hi0, ite_neg hi1, ite_neg hi2, ite_neg hilt, ite_neg hik2,
              decide_eq_true hge3, decide_eq_false h1v, decide_eq_false h2v]
            cases w i <;> cases w (ix hk (i.val + 1)) <;> cases w (ix hk (i.val + 2)) <;> rfl

def resSum (r : Nat) (hk3 : k = 3 * r) (w : Fin k → Bool) (c : Nat) (hc : c < 3) : Bool :=
  xorFin (fun j : Fin r => w ⟨3 * j.val + c, by omega⟩)

lemma resSum_mix (hr : 2 ≤ r) (hk3 : k = 3 * r) (z : Fin k → Bool) :
    resSum r hk3 (mix hk z) 0 (by omega) = xorFin z ∧
    resSum r hk3 (mix hk z) 1 (by omega) = xorFin z ∧
    resSum r hk3 (mix hk z) 2 (by omega) = xorFin z := by
  have hmod : ∀ (c : Nat) (hc : c < 3),
      resSum r hk3 (mix hk z) c hc = xorFin z := by
    intro c hc
    unfold resSum mix
    rw [xorFin_xor, xorFin_xor]

    have hpart : ∀ (f : Fin k → Bool),
        xorFin f = xor (xorFin (fun j : Fin r => f ⟨3 * j.val, by omega⟩))
                       (xor (xorFin (fun j : Fin r => f ⟨3 * j.val + 1, by omega⟩))
                            (xorFin (fun j : Fin r => f ⟨3 * j.val + 2, by omega⟩))) := by
      intro f
      have h1 : xorFin f = xorFin (fun p : Fin (r * 3) => f ⟨p.val, by omega⟩) :=
        xorFin_cast (by rw [hk3, Nat.mul_comm]) _ _ (fun _ _ _ => rfl)
      rw [h1]
      have h2 := xorFin_prod (a := r) (b := 3) (by omega) (fun j (q : Fin 3) => f ⟨3 * j.val + q.val, by omega⟩)
      have h3 : xorFin (fun p : Fin (r * 3) => f ⟨p.val, by omega⟩) =
          xorFin (fun p : Fin (r * 3) =>
            f ⟨3 * (p.val / 3) + p.val % 3, by omega⟩) :=
        xorFin_congr _ _ (fun p => by congr 1; apply Fin.ext; dsimp; omega)
      have hfin3 : ∀ (g : Fin 3 → Bool),
          xorFin g = xor (g ⟨0, by omega⟩) (xor (g ⟨1, by omega⟩) (g ⟨2, by omega⟩)) := by
        intro g; unfold xorFin
        have : List.finRange 3 = [0, 1, 2] := rfl
        rw [this]; simp
      rw [h3, show xorFin (fun p : Fin (r * 3) => f ⟨3 * (p.val / 3) + p.val % 3, by omega⟩) =
            xorFin (fun p : Fin (r * 3) =>
              (fun (j : Fin r) (q : Fin 3) => f ⟨3 * j.val + q.val, by omega⟩)
                ⟨p.val / 3, Nat.div_lt_of_lt_mul (Nat.mul_comm r 3 ▸ p.isLt)⟩
                ⟨p.val % 3, Nat.mod_lt _ (by omega)⟩) from xorFin_congr _ _ (fun _ => rfl), h2]
      simp_rw [hfin3, xorFin_xor]
      rfl
    rw [hpart z]

    have hrot_succ : ∀ (m : Nat) (g : Fin (m + 1) → Bool),
        xorFin g = xor (g ⟨0, by omega⟩) (xorFin (fun j : Fin m => g j.succ)) := by
      intro m g; unfold xorFin
      have hfr : List.finRange (m + 1) = ⟨0, by omega⟩ :: (List.finRange m).map Fin.succ := by
        apply List.ext_getElem
        · simp
        · intro idx _ _
          cases idx <;> apply Fin.ext <;> simp
      rw [hfr, List.foldl_cons, foldl_map_xor_init, List.foldl_map, Bool.false_xor]
    have hshift_prev : ∀ (c : Nat) (hc : c < 3),
        xorFin (fun j : Fin r => z (ix hk (3 * j.val + c + k - 1))) =
          xorFin (fun j : Fin r => z ⟨3 * j.val + (c + 2) % 3, by omega⟩) := by
      intro c hc
      by_cases hc0 : c = 0
      · subst hc0
        have hrot : ∀ (g : Fin r → Bool),
            xorFin (fun j : Fin r => g ⟨(j.val + r - 1) % r, Nat.mod_lt _ (by omega)⟩) = xorFin g := by
          intro g
          cases r with
          | zero => omega
          | succ r' =>
            rw [hrot_succ r', xorFin_succ g, Bool.xor_comm]
            congr 1
            · apply xorFin_congr; intro j; congr 1; apply Fin.ext
              simp only [Fin.val_succ, Fin.val_castSucc]
              rw [show j.val + 1 + (r' + 1) - 1 = j.val + (r' + 1) by omega,
                Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            · congr 1; apply Fin.ext; simp only [Fin.last]
              rw [Nat.zero_add, Nat.add_sub_cancel, Nat.mod_eq_of_lt (by omega)]
        have hmatch := hrot (fun j : Fin r => z ⟨3 * j.val + 2, by omega⟩)
        rw [← hmatch]
        apply xorFin_congr; intro j; congr 1; apply Fin.ext; dsimp [ix]
        by_cases hj0 : j.val = 0
        · rw [hj0]; simp only [Nat.mul_zero, Nat.zero_add]
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
        · rw [show 3 * j.val + k - 1 = (3 * j.val - 1) + k by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega), show j.val + r - 1 = (j.val - 1) + r by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
      · apply xorFin_congr; intro j; congr 1; apply Fin.ext; dsimp [ix]
        rw [show 3 * j.val + c + k - 1 = (3 * j.val + (c - 1)) + k by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]
        omega
    have hshift_next : ∀ (c : Nat) (hc : c < 3),
        xorFin (fun j : Fin r => z (ix hk (3 * j.val + c + 1))) =
          xorFin (fun j : Fin r => z ⟨3 * j.val + (c + 1) % 3, by omega⟩) := by
      intro c hc
      by_cases hc2 : c = 2
      · subst hc2
        have hrot : ∀ (g : Fin r → Bool),
            xorFin (fun j : Fin r => g ⟨(j.val + 1) % r, Nat.mod_lt _ (by omega)⟩) = xorFin g := by
          intro g
          cases r with
          | zero => omega
          | succ r' =>
            rw [xorFin_succ (fun j : Fin (r' + 1) => g ⟨(j.val + 1) % (r' + 1), Nat.mod_lt _ (by omega)⟩),
              hrot_succ r' g, Bool.xor_comm]
            congr 1
            · congr 1; apply Fin.ext; simp only [Fin.last]; rw [Nat.mod_self]
            · apply xorFin_congr; intro j; congr 1; apply Fin.ext
              simp only [Fin.val_castSucc, Fin.val_succ]
              rw [Nat.mod_eq_of_lt (by omega)]
        have hmatch := hrot (fun j : Fin r => z ⟨3 * j.val, by omega⟩)
        have hrhs : xorFin (fun j : Fin r => z ⟨3 * j.val + (2 + 1) % 3, by omega⟩) =
            xorFin (fun j : Fin r => z ⟨3 * j.val, by omega⟩) :=
          xorFin_congr _ _ (fun j => rfl)
        rw [hrhs, ← hmatch]
        apply xorFin_congr; intro j; congr 1; apply Fin.ext; dsimp [ix]
        by_cases hjl : j.val = r - 1
        · rw [hjl, show 3 * (r - 1) + 2 + 1 = k by omega, Nat.mod_self,
            show r - 1 + 1 = r by omega, Nat.mod_self]
        · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
      · apply xorFin_congr; intro j; congr 1; apply Fin.ext; dsimp [ix]
        rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [hshift_prev c hc, hshift_next c hc]
    interval_cases c
    · simp only [Nat.zero_add]
      cases xorFin (fun j : Fin r => z ⟨3 * j.val, by omega⟩) <;>
        cases xorFin (fun j : Fin r => z ⟨3 * j.val + 1, by omega⟩) <;>
        cases xorFin (fun j : Fin r => z ⟨3 * j.val + 2, by omega⟩) <;> rfl
    · cases xorFin (fun j : Fin r => z ⟨3 * j.val, by omega⟩) <;>
        cases xorFin (fun j : Fin r => z ⟨3 * j.val + 1, by omega⟩) <;>
        cases xorFin (fun j : Fin r => z ⟨3 * j.val + 2, by omega⟩) <;> rfl
    · cases xorFin (fun j : Fin r => z ⟨3 * j.val, by omega⟩) <;>
        cases xorFin (fun j : Fin r => z ⟨3 * j.val + 1, by omega⟩) <;>
        cases xorFin (fun j : Fin r => z ⟨3 * j.val + 2, by omega⟩) <;> rfl
  exact ⟨hmod 0 (by omega), hmod 1 (by omega), hmod 2 (by omega)⟩

def zPair (w : Fin k → Bool) (z0 z1 : Bool) : Nat → Bool × Bool
  | 0 => (z0, z1)
  | j + 1 =>
    let p := zPair w z0 z1 j
    (p.2, xor p.1 (xor p.2 (if h : j + 1 < k then w ⟨j + 1, h⟩ else false)))

def zOf (w : Fin k → Bool) (z0 z1 : Bool) (i : Fin k) : Bool :=
  (zPair w z0 z1 i.val).1

lemma zPair_snd (w : Fin k → Bool) (z0 z1 : Bool) (j : Nat) :
    (zPair w z0 z1 (j + 1)).1 = (zPair w z0 z1 j).2 := rfl

lemma zPair_rec (w : Fin k → Bool) (z0 z1 : Bool) (j : Nat) (hj : j + 1 < k) :
    (zPair w z0 z1 (j + 2)).1 =
      xor (zPair w z0 z1 j).1 (xor (zPair w z0 z1 (j + 1)).1 (w ⟨j + 1, hj⟩)) := by
  simp only [zPair, hj, dite_true]

lemma zPair_rec_at (w : Fin k → Bool) (z0 z1 : Bool) (j j1 j2 : Nat)
    (h1 : j1 = j + 1) (h2 : j2 = j + 2) (hj1 : j1 < k) :
    (zPair w z0 z1 j2).1 =
      xor (zPair w z0 z1 j).1 (xor (zPair w z0 z1 j1).1 (w ⟨j1, hj1⟩)) := by
  subst h1; subst h2; exact zPair_rec w z0 z1 j hj1

lemma zPair_xor (w1 w2 : Fin k → Bool) (z0a z1a z0b z1b : Bool) (j : Nat) :
    zPair (add w1 w2) (xor z0a z0b) (xor z1a z1b) j =
      (xor (zPair w1 z0a z1a j).1 (zPair w2 z0b z1b j).1,
       xor (zPair w1 z0a z1a j).2 (zPair w2 z0b z1b j).2) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [zPair, ih]
    refine Prod.ext rfl ?_
    by_cases h : j + 1 < k
    · simp only [h, dite_true, add]
      cases (zPair w1 z0a z1a j).1 <;> cases (zPair w2 z0b z1b j).1 <;>
        cases (zPair w1 z0a z1a j).2 <;> cases (zPair w2 z0b z1b j).2 <;>
        cases w1 ⟨j + 1, h⟩ <;> cases w2 ⟨j + 1, h⟩ <;> rfl
    · simp only [h, dite_false]
      cases (zPair w1 z0a z1a j).1 <;> cases (zPair w2 z0b z1b j).1 <;>
        cases (zPair w1 z0a z1a j).2 <;> cases (zPair w2 z0b z1b j).2 <;> rfl

lemma zOf_xor (w1 w2 : Fin k → Bool) (z0a z1a z0b z1b : Bool) (i : Fin k) :
    zOf (add w1 w2) (xor z0a z0b) (xor z1a z1b) i =
      xor (zOf w1 z0a z1a i) (zOf w2 z0b z1b i) := by
  unfold zOf; rw [zPair_xor]

lemma zPair_zero (z0 z1 : Bool) (j : Nat) :
    zPair (k := k) (fun _ => false) z0 z1 j =
      (if j % 3 = 0 then z0 else if j % 3 = 1 then z1 else xor z0 z1,
       if (j + 1) % 3 = 0 then z0 else if (j + 1) % 3 = 1 then z1 else xor z0 z1) := by
  induction j with
  | zero => simp [zPair]
  | succ j ih =>
    simp only [zPair, ih, dite_eq_ite, ite_self]
    refine Prod.ext rfl ?_
    have hmod : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases hmod with h | h | h
    · have h1 : (j + 1) % 3 = 1 := by omega
      have h2 : (j + 1 + 1) % 3 = 2 := by omega
      simp [h, h1, h2]
    · have h1 : (j + 1) % 3 = 2 := by omega
      have h2 : (j + 1 + 1) % 3 = 0 := by omega
      simp [h, h1, h2]; cases z0 <;> cases z1 <;> rfl
    · have h1 : (j + 1) % 3 = 0 := by omega
      have h2 : (j + 1 + 1) % 3 = 1 := by omega
      simp [h, h1, h2]; cases z0 <;> cases z1 <;> rfl

lemma zPair_mask3 (j : Nat) (hj : j < k) :
    zPair (fun i : Fin k => decide (3 ≤ i.val)) false false j =
      (decide (4 ≤ j ∧ j % 3 = 1), decide (4 ≤ j + 1 ∧ (j + 1) % 3 = 1)) := by
  induction j with
  | zero => simp [zPair]
  | succ j ih =>
    simp only [zPair, ih (by omega), hj, dite_true]
    refine Prod.ext rfl ?_
    by_cases h0 : j = 0
    · subst h0; simp
    · by_cases h1 : j = 1
      · subst h1; simp
      · by_cases h2 : j = 2
        · subst h2; simp
        · have hge3 : 3 ≤ j + 1 := by omega
          have hge4 : 4 ≤ j + 1 := by omega
          have hge4' : 4 ≤ j + 1 + 1 := by omega
          by_cases hj3 : j = 3
          · subst hj3; simp
          · have hj4 : 4 ≤ j := by omega
            simp only [hj4, hge3, hge4, hge4', true_and, decide_true]
            have hm : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
            rcases hm with h | h | h
            · have h1' : (j + 1) % 3 = 1 := by omega
              have h2' : (j + 1 + 1) % 3 = 2 := by omega
              simp [h, h1', h2']
            · have h1' : (j + 1) % 3 = 2 := by omega
              have h2' : (j + 1 + 1) % 3 = 0 := by omega
              simp [h, h1', h2']
            · have h1' : (j + 1) % 3 = 0 := by omega
              have h2' : (j + 1 + 1) % 3 = 1 := by omega
              simp [h, h1', h2']

lemma zPair_3m (w : Fin k → Bool) (z0 z1 : Bool) (m : Nat) (hm : 3 * m + 1 < k) :
    (zPair w z0 z1 (3 * m)).1 =
      xor z0 (xorFin (fun j : Fin m => xor (w ⟨3 * j.val + 1, by omega⟩) (w ⟨3 * j.val + 2, by omega⟩))) ∧
    (zPair w z0 z1 (3 * m)).2 =
      xor z1 (xorFin (fun j : Fin m => xor (w ⟨3 * j.val + 2, by omega⟩) (w ⟨3 * j.val + 3, by omega⟩))) := by
  induction m with
  | zero => simp [zPair, xorFin]
  | succ m ih =>
    rcases ih (by omega) with ⟨h1, h2⟩
    have ha : 3 * m + 1 < k := by omega
    have hb : 3 * m + 2 < k := by omega
    have hc : 3 * m + 3 < k := by omega
    have hstep1 : (zPair w z0 z1 (3 * m + 1)).1 = (zPair w z0 z1 (3 * m)).2 := rfl
    have hstep2 : (zPair w z0 z1 (3 * m + 2)).1 =
        xor (zPair w z0 z1 (3 * m)).1 (xor (zPair w z0 z1 (3 * m)).2 (w ⟨3 * m + 1, ha⟩)) := by
      simp only [zPair, ha, dite_true]
    have hstep3 : (zPair w z0 z1 (3 * m + 3)).1 =
        xor (zPair w z0 z1 (3 * m)).1 (xor (w ⟨3 * m + 1, ha⟩) (w ⟨3 * m + 2, hb⟩)) := by
      have ht := zPair_rec_at w z0 z1 (3 * m + 1) (3 * m + 2) (3 * m + 3) (by omega) (by omega) hb
      rw [ht, hstep1, hstep2]
      cases (zPair w z0 z1 (3 * m)).1 <;> cases (zPair w z0 z1 (3 * m)).2 <;>
        cases w ⟨3 * m + 1, ha⟩ <;> cases w ⟨3 * m + 2, hb⟩ <;> rfl
    have hstep4 : (zPair w z0 z1 (3 * m + 3)).2 =
        xor (zPair w z0 z1 (3 * m)).2 (xor (w ⟨3 * m + 2, hb⟩) (w ⟨3 * m + 3, hc⟩)) := by
      have ht := zPair_rec_at w z0 z1 (3 * m + 2) (3 * m + 3) (3 * m + 4) (by omega) (by omega) hc
      change (zPair w z0 z1 (3 * m + 4)).1 = _
      rw [ht, hstep2, hstep3]
      cases (zPair w z0 z1 (3 * m)).1 <;> cases (zPair w z0 z1 (3 * m)).2 <;>
        cases w ⟨3 * m + 1, ha⟩ <;> cases w ⟨3 * m + 2, hb⟩ <;> cases w ⟨3 * m + 3, hc⟩ <;> rfl
    rw [show 3 * (m + 1) = 3 * m + 3 by omega, hstep3, hstep4, h1, h2]
    constructor
    · rw [xorFin_succ]; simp only [Fin.val_castSucc, Fin.last, Bool.xor_assoc]
    · rw [xorFin_succ]; simp only [Fin.val_castSucc, Fin.last, Bool.xor_assoc]

lemma mix_zOf (hr : 2 ≤ r) (hk3 : k = 3 * r) (w : Fin k → Bool) (z0 z1 : Bool)
    (hs01 : resSum r hk3 w 0 (by omega) = resSum r hk3 w 1 (by omega))
    (hs02 : resSum r hk3 w 0 (by omega) = resSum r hk3 w 2 (by omega)) :
    mix hk (zOf w z0 z1) = w := by
  have hr' : r = (r - 1) + 1 := by omega
  have hsum_last : ∀ (c : Nat) (hc : c < 3),
      xorFin (fun j : Fin (r - 1) => w ⟨3 * j.val + c, by omega⟩) =
        xor (resSum r hk3 w c hc) (w ⟨3 * (r - 1) + c, by omega⟩) := by
    intro c hc
    unfold resSum
    have heq : xorFin (fun j : Fin r => w ⟨3 * j.val + c, by omega⟩) =
        xorFin (fun j : Fin ((r - 1) + 1) => w ⟨3 * j.val + c, by omega⟩) :=
      xorFin_cast hr' _ _ (fun _ _ _ => rfl)
    rw [heq, xorFin_succ]
    have hcs : xorFin (fun j : Fin (r - 1) => w ⟨3 * j.castSucc.val + c, by omega⟩) =
        xorFin (fun j : Fin (r - 1) => w ⟨3 * j.val + c, by omega⟩) :=
      xorFin_congr _ _ (fun _ => rfl)
    rw [hcs]
    simp only [Fin.last]
    cases xorFin (fun j : Fin (r - 1) => w ⟨3 * j.val + c, by omega⟩) <;>
      cases w ⟨3 * (r - 1) + c, by omega⟩ <;> rfl
  have hsum0 : xorFin (fun j : Fin (r - 1) => w ⟨3 * j.val + 3, by omega⟩) =
      xor (resSum r hk3 w 0 (by omega)) (w ⟨0, by omega⟩) := by
    unfold resSum
    have heq : xorFin (fun j : Fin r => w ⟨3 * j.val + 0, by omega⟩) =
        xor (w ⟨0, by omega⟩) (xorFin (fun j : Fin (r - 1) => w ⟨3 * j.val + 3, by omega⟩)) := by
      have hc : xorFin (fun j : Fin r => w ⟨3 * j.val + 0, by omega⟩) =
          xorFin (fun j : Fin ((r - 1) + 1) => w ⟨3 * j.val, by omega⟩) :=
        xorFin_cast hr' _ _ (fun _ _ _ => rfl)
      rw [hc]; unfold xorFin
      have hfr : List.finRange ((r - 1) + 1) = ⟨0, by omega⟩ :: (List.finRange (r - 1)).map Fin.succ := by
        apply List.ext_getElem
        · simp
        · intro idx _ _; cases idx <;> apply Fin.ext <;> simp
      rw [hfr, List.foldl_cons, foldl_map_xor_init, List.foldl_map, Bool.false_xor]
      congr 1
    rw [heq]
    cases w ⟨0, by omega⟩ <;> cases xorFin (fun j : Fin (r - 1) => w ⟨3 * j.val + 3, by omega⟩) <;> rfl
  funext i
  by_cases hi0 : i.val = 0
  · have h3m := zPair_3m w z0 z1 (r - 1) (by omega)
    have hzk1 := zPair_rec_at w z0 z1 (3 * (r - 1)) (3 * (r - 1) + 1) (k - 1) (by omega) (by omega) (by omega)
    rw [zPair_snd, h3m.1, h3m.2, xorFin_xor, xorFin_xor, hsum_last 1 (by omega), hsum0, hs01] at hzk1
    unfold mix zOf
    have hprev : ix hk (i.val + k - 1) = ⟨k - 1, by omega⟩ := by
      rw [hi0, Nat.zero_add]; exact ix_eq_of_lt hk (by omega)
    have hnext : ix hk (i.val + 1) = ⟨1, by omega⟩ := by
      rw [hi0]; exact ix_eq_of_lt hk (by omega)
    have hwi : w i = w ⟨0, hk⟩ := congrArg w (Fin.ext hi0)
    have hzi : (zPair w z0 z1 i.val).1 = z0 := by rw [hi0]; rfl
    rw [hprev, hnext, hwi, hzi]
    dsimp only
    rw [hzk1]
    have hz1 : (zPair w z0 z1 1).1 = z1 := rfl
    rw [hz1]
    cases z0 <;> cases z1 <;> cases resSum r hk3 w 1 (by omega) <;>
      cases xorFin (fun j : Fin (r - 1) => w ⟨3 * j.val + 2, by omega⟩) <;>
      cases w ⟨3 * (r - 1) + 1, by omega⟩ <;> cases w ⟨0, hk⟩ <;> rfl
  · by_cases hil : i.val = k - 1
    · have h3m := zPair_3m w z0 z1 (r - 1) (by omega)
      have hzk2 : (zPair w z0 z1 (k - 2)).1 = (zPair w z0 z1 (3 * (r - 1))).2 := by
        rw [show k - 2 = 3 * (r - 1) + 1 by omega]; rfl
      have hzk1 := zPair_rec_at w z0 z1 (3 * (r - 1)) (3 * (r - 1) + 1) (k - 1) (by omega) (by omega) (by omega)
      rw [zPair_snd, h3m.1, h3m.2, xorFin_xor, xorFin_xor, hsum_last 1 (by omega), hsum_last 2 (by omega)] at hzk1
      rw [h3m.2, xorFin_xor, hsum_last 2 (by omega)] at hzk2
      unfold mix zOf
      have hprev : ix hk (i.val + k - 1) = ⟨k - 2, by omega⟩ := by
        rw [hil]; exact (ix_mod_eq hk (by rw [show k - 1 + k - 1 = (k - 2) + k by omega, Nat.add_mod_right])).trans (ix_eq_of_lt hk (by omega))
      have hnext : ix hk (i.val + 1) = ⟨0, hk⟩ := by
        rw [hil]; exact (ix_mod_eq hk (by rw [show k - 1 + 1 = k by omega, Nat.mod_self, Nat.zero_mod])).trans (ix_eq_of_lt hk hk)
      have hwi : w i = w ⟨3 * (r - 1) + 2, by omega⟩ := congrArg w (Fin.ext (by dsimp; omega))
      have hzi : (zPair w z0 z1 i.val).1 = (zPair w z0 z1 (k - 1)).1 := by rw [hil]
      rw [hprev, hnext, hwi, hzi]
      dsimp only
      rw [hzk2, hzk1, ← hs01, hs02]
      have hz0 : (zPair w z0 z1 0).1 = z0 := rfl
      rw [hz0]
      cases z0 <;> cases z1 <;> cases resSum r hk3 w 2 (by omega) <;>
        cases w ⟨3 * (r - 1) + 1, by omega⟩ <;> cases w ⟨3 * (r - 1) + 2, by omega⟩ <;>
        cases xorFin (fun j : Fin (r - 1) => w ⟨3 * j.val + 3, by omega⟩) <;> rfl
    · unfold mix zOf
      have hprev : ix hk (i.val + k - 1) = ⟨i.val - 1, by omega⟩ :=
        (ix_mod_eq hk (by rw [show i.val + k - 1 = (i.val - 1) + k by omega, Nat.add_mod_right])).trans (ix_eq_of_lt hk (by omega))
      have hnext : ix hk (i.val + 1) = ⟨i.val + 1, by omega⟩ := ix_eq_of_lt hk (by omega)
      rw [hprev, hnext]
      dsimp only
      have ht := zPair_rec_at w z0 z1 (i.val - 1) i.val (i.val + 1) (by omega) (by omega) i.isLt
      rw [ht]
      cases (zPair w z0 z1 (i.val - 1)).1 <;> cases (zPair w z0 z1 i.val).1 <;>
        cases w i <;> rfl

lemma zOf_mix (hr : 2 ≤ r) (hk3 : k = 3 * r) (z : Fin k → Bool) :
    zOf (mix hk z) (z ⟨0, hk⟩) (z ⟨1, by omega⟩) = z := by
  have haux : ∀ j (hj : j + 1 < k),
      zPair (mix hk z) (z ⟨0, hk⟩) (z ⟨1, by omega⟩) j = (z ⟨j, by omega⟩, z ⟨j + 1, hj⟩) := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      have hj1 : j + 1 < k := by omega
      simp only [zPair, ih hj1, hj1, dite_true]
      refine Prod.ext rfl ?_
      unfold mix
      have hprev : ix hk (j + 1 + k - 1) = ⟨j, by omega⟩ :=
        (ix_mod_eq hk (by rw [show j + 1 + k - 1 = j + k by omega, Nat.add_mod_right])).trans (ix_eq_of_lt hk (by omega))
      have hnext : ix hk (j + 1 + 1) = ⟨j + 2, by omega⟩ := ix_eq_of_lt hk (by omega)
      dsimp only
      rw [hprev, hnext]
      cases z ⟨j, by omega⟩ <;> cases z ⟨j + 1, hj1⟩ <;> cases z ⟨j + 2, hj⟩ <;> rfl
  funext i
  unfold zOf
  by_cases hi : i.val + 1 < k
  · rw [haux i.val hi]
  · have hil : i.val = k - 1 := by omega
    have h1 := haux (k - 2) (by omega)
    rw [hil, show k - 1 = (k - 2) + 1 by omega, zPair_snd, h1]
    exact congrArg z (Fin.ext (by dsimp only; omega))

def tWalk (d : Fin k → Bool) : Nat → Bool
  | 0 => false
  | 1 => if h : 2 < k then d ⟨2, h⟩ else false
  | j + 2 =>
    xor (tWalk d (j + 1)) (if h : j + 3 < k then !(d ⟨j + 3, h⟩) else false)

def tRaw (hr : 2 ≤ r) (hk3 : k = 3 * r) (d : Fin k → Bool) (i : Fin k) : Bool :=
  if i.val = 0 then !(d ⟨k - 2, by omega⟩)
  else if i.val = 1 then false
  else if i.val = 2 then !(d ⟨1, by omega⟩)
  else tWalk d (i.val - 3)

def tOfD (hr : 2 ≤ r) (hk3 : k = 3 * r) (d : Fin k → Bool) (i : Fin k) : Bool :=
  if i.val = 1 then
    xor (tRaw hr hk3 d ⟨0, hk_of hr hk3⟩)
      (xorFin (fun j : Fin (r - 1) =>
        xor (tRaw hr hk3 d ⟨3 * (j.val + 1), by omega⟩)
            (tRaw hr hk3 d ⟨3 * (j.val + 1) + 1, by omega⟩)))
  else tRaw hr hk3 d i

lemma xorFin_split3 (_hr : 2 ≤ r) (hk3 : k = 3 * r) (f : Fin k → Bool) :
    xorFin f = xor (xorFin (fun j : Fin r => f ⟨3 * j.val, by omega⟩))
                   (xor (xorFin (fun j : Fin r => f ⟨3 * j.val + 1, by omega⟩))
                        (xorFin (fun j : Fin r => f ⟨3 * j.val + 2, by omega⟩))) := by
  have h1 : xorFin f = xorFin (fun p : Fin (r * 3) => f ⟨p.val, by omega⟩) :=
    xorFin_cast (by rw [hk3, Nat.mul_comm]) _ _ (fun _ _ _ => rfl)
  rw [h1]
  have h2 := xorFin_prod (a := r) (b := 3) (by omega) (fun j (q : Fin 3) => f ⟨3 * j.val + q.val, by omega⟩)
  have h3 : xorFin (fun p : Fin (r * 3) => f ⟨p.val, by omega⟩) =
      xorFin (fun p : Fin (r * 3) =>
        (fun (j : Fin r) (q : Fin 3) => f ⟨3 * j.val + q.val, by omega⟩)
          ⟨p.val / 3, Nat.div_lt_of_lt_mul (Nat.mul_comm r 3 ▸ p.isLt)⟩
          ⟨p.val % 3, Nat.mod_lt _ (by omega)⟩) :=
    xorFin_congr _ _ (fun p => by congr 1; apply Fin.ext; dsimp; omega)
  have hfin3 : ∀ (g : Fin 3 → Bool),
      xorFin g = xor (g ⟨0, by omega⟩) (xor (g ⟨1, by omega⟩) (g ⟨2, by omega⟩)) := by
    intro g; unfold xorFin
    have : List.finRange 3 = [0, 1, 2] := rfl
    rw [this]; simp
  rw [h3, h2]
  simp_rw [hfin3, xorFin_xor]
  rfl

lemma tWalk_diff (hr : 2 ≤ r) (hk3 : k = 3 * r) (u x : Fin k → Bool) :
    let w := mix hk (add u (rot hk x))
    let b := w ⟨3, by omega⟩
    ∀ j (hj : j + 3 < k), tWalk (diffFn hk u x) j = xor b (w ⟨j + 3, hj⟩) := by
  intro w b j
  induction j with
  | zero => intro _; simp [tWalk, b]
  | succ j ih =>
    cases j with
    | zero =>
      intro hj
      have h2lt : 2 < k := by omega
      simp only [tWalk, h2lt, dite_true]
      have hd := diffFn_eq hk hr hk3 u x ⟨2, h2lt⟩
      dsimp only at hd
      rw [hd]
      have h3 : ix hk 3 = ⟨3, by omega⟩ := ix_eq_of_lt hk (by omega)
      have h4 : ix hk 4 = ⟨4, hj⟩ := ix_eq_of_lt hk hj
      simp only [ite_true, h3, h4]
      rfl
    | succ j =>
      intro hj
      have hj3 : j + 3 < k := by omega
      have hprev := ih (by omega)
      simp only [tWalk, hj3, dite_true]
      have hd := diffFn_eq hk hr hk3 u x ⟨j + 3, hj3⟩
      dsimp only at hd
      have hn0 : j + 3 ≠ 0 := by omega
      have hn1 : j + 3 ≠ 1 := by omega
      have hn2 : j + 3 ≠ 2 := by omega
      have hlt : j + 3 < k - 2 := by omega
      rw [hd, ite_neg hn0, ite_neg hn1, ite_neg hn2, ite_pos hlt]
      have hp1 : ix hk (j + 3 + 1) = ⟨j + 1 + 3, by omega⟩ := ix_eq_of_lt hk (by omega)
      have hp2 : ix hk (j + 3 + 2) = ⟨j + 2 + 3, hj⟩ := ix_eq_of_lt hk hj
      rw [hprev, hp1, hp2]
      dsimp only [w]
      cases b <;> cases mix hk (add u (rot hk x)) ⟨j + 1 + 3, by omega⟩ <;>
        cases mix hk (add u (rot hk x)) ⟨j + 2 + 3, hj⟩ <;> rfl

lemma tOfD_diff (hr : 2 ≤ r) (hk3 : k = 3 * r) (u x : Fin k → Bool) :
    let w := mix hk (add u (rot hk x))
    let b := w ⟨3, by omega⟩
    let t := tOfD hr hk3 (diffFn hk u x)
    t ⟨3, by omega⟩ = false ∧
    w = add t (fun i => b && decide (3 ≤ i.val)) ∧
    resSum r hk3 t 0 (by omega) = resSum r hk3 t 1 (by omega) ∧
    resSum r hk3 t 0 (by omega) = resSum r hk3 t 2 (by omega) := by
  intro w b t
  have ht0 : tRaw hr hk3 (diffFn hk u x) ⟨0, hk⟩ = w ⟨0, hk⟩ := by
    unfold tRaw; simp only [ite_true]
    have hd := diffFn_eq hk hr hk3 u x ⟨k - 2, by omega⟩
    dsimp only at hd
    have hn0 : k - 2 ≠ 0 := by omega
    have hn1 : k - 2 ≠ 1 := by omega
    have hn2 : k - 2 ≠ 2 := by omega
    have hnlt : ¬(k - 2 < k - 2) := by omega
    rw [hd, ite_neg hn0, ite_neg hn1, ite_neg hn2, ite_neg hnlt, ite_pos rfl,
      ix_eq_of_lt hk hk, Bool.not_not]
  have ht2 : tRaw hr hk3 (diffFn hk u x) ⟨2, by omega⟩ = w ⟨2, by omega⟩ := by
    unfold tRaw
    have hn0 : (2 : Nat) ≠ 0 := by omega
    have hn1 : (2 : Nat) ≠ 1 := by omega
    rw [ite_neg hn0, ite_neg hn1, ite_pos rfl]
    have hd := diffFn_eq hk hr hk3 u x ⟨1, by omega⟩
    dsimp only at hd
    have h1n0 : (1 : Nat) ≠ 0 := by omega
    rw [hd, ite_neg h1n0, ite_pos rfl, ix_eq_of_lt hk (by omega), Bool.not_not]
  have htge3 : ∀ i : Fin k, 3 ≤ i.val → tRaw hr hk3 (diffFn hk u x) i = xor b (w i) := by
    intro i hi
    unfold tRaw
    have hn0 : i.val ≠ 0 := by omega
    have hn1 : i.val ≠ 1 := by omega
    have hn2 : i.val ≠ 2 := by omega
    rw [ite_neg hn0, ite_neg hn1, ite_neg hn2]
    have hw := tWalk_diff hk hr hk3 u x (i.val - 3) (by omega)
    rw [hw]
    congr 1; exact congrArg w (Fin.ext (by dsimp only; omega))
  have hres := resSum_mix hk hr hk3 (add u (rot hk x))
  have hres_split : ∀ (f : Fin k → Bool) (c : Nat) (hc : c < 3),
      resSum r hk3 f c hc = xor (f ⟨c, by omega⟩) (xorFin (fun j : Fin (r - 1) => f ⟨3 * (j.val + 1) + c, by omega⟩)) := by
    intro f c hc
    unfold resSum
    rw [xorFin_first (by omega)]
    dsimp only
    congr 1
    exact congrArg f (Fin.ext (by dsimp only; omega))
  have ht1 : t ⟨1, by omega⟩ = w ⟨1, by omega⟩ := by
    unfold t tOfD
    simp only [ite_true]
    rw [ht0]
    have hs01 : resSum r hk3 w 0 (by omega) = resSum r hk3 w 1 (by omega) := hres.1.trans hres.2.1.symm
    rw [hres_split w 0 (by omega), hres_split w 1 (by omega)] at hs01
    have hpair : xorFin (fun j : Fin (r - 1) =>
        xor (tRaw hr hk3 (diffFn hk u x) ⟨3 * (j.val + 1), by omega⟩)
            (tRaw hr hk3 (diffFn hk u x) ⟨3 * (j.val + 1) + 1, by omega⟩)) =
      xor (xorFin (fun j : Fin (r - 1) => w ⟨3 * (j.val + 1), by omega⟩))
          (xorFin (fun j : Fin (r - 1) => w ⟨3 * (j.val + 1) + 1, by omega⟩)) := by
      rw [← xorFin_xor]
      apply xorFin_congr; intro j
      rw [htge3 ⟨3 * (j.val + 1), by omega⟩ (by dsimp only; omega),
        htge3 ⟨3 * (j.val + 1) + 1, by omega⟩ (by dsimp only; omega)]
      cases b <;> cases w ⟨3 * (j.val + 1), by omega⟩ <;> cases w ⟨3 * (j.val + 1) + 1, by omega⟩ <;> rfl
    rw [hpair]
    have h00 : xorFin (fun j : Fin (r - 1) => w ⟨3 * (j.val + 1) + 0, by omega⟩) =
        xorFin (fun j : Fin (r - 1) => w ⟨3 * (j.val + 1), by omega⟩) :=
      xorFin_congr _ _ (fun _ => rfl)
    rw [h00] at hs01
    cases h0 : w ⟨0, hk⟩ <;> cases h1 : w ⟨1, by omega⟩ <;>
      cases h2 : xorFin (fun j : Fin (r - 1) => w ⟨3 * (j.val + 1), by omega⟩) <;>
      cases h3 : xorFin (fun j : Fin (r - 1) => w ⟨3 * (j.val + 1) + 1, by omega⟩) <;>
      simp [h0, h1, h2, h3] at hs01 ⊢
  have hw_eq : w = add t (fun i => b && decide (3 ≤ i.val)) := by
    funext i; unfold add
    by_cases hi0 : i.val = 0
    · have hie : i = ⟨0, hk⟩ := Fin.ext hi0
      rw [hie]; dsimp only
      have ht0' : t ⟨0, hk⟩ = w ⟨0, hk⟩ := by
        unfold t tOfD; rw [ite_neg (by omega)]; exact ht0
      rw [ht0']; simp
    · by_cases hi1 : i.val = 1
      · have hie : i = ⟨1, by omega⟩ := Fin.ext hi1
        rw [hie]; dsimp only; rw [ht1]; simp
      · by_cases hi2 : i.val = 2
        · have hie : i = ⟨2, by omega⟩ := Fin.ext hi2
          rw [hie]; dsimp only
          have ht2' : t ⟨2, by omega⟩ = w ⟨2, by omega⟩ := by
            unfold t tOfD; rw [ite_neg (by omega)]; exact ht2
          rw [ht2']; simp
        · have hge3 : 3 ≤ i.val := by omega
          have hte : t i = xor b (w i) := by
            unfold t tOfD; rw [ite_neg hi1]; exact htge3 i hge3
          dsimp only; rw [hte, decide_eq_true hge3, Bool.and_true]
          cases b <;> cases w i <;> rfl
  have ht3 : t ⟨3, by omega⟩ = false := by
    unfold t tOfD
    have hn1 : (3 : Nat) ≠ 1 := by omega
    rw [ite_neg hn1, htge3 ⟨3, by omega⟩ (by dsimp only; omega)]
    exact Bool.xor_self b
  have hres_t : ∀ (c : Nat) (hc : c < 3),
      resSum r hk3 w c hc = xor (resSum r hk3 t c hc) (b && decide ((r - 1) % 2 = 1)) := by
    intro c hc
    rw [hw_eq, hres_split _ c hc, hres_split t c hc]
    unfold add; dsimp only
    have hlt3 : ¬(3 ≤ c) := by omega
    rw [decide_eq_false hlt3, Bool.and_false, Bool.xor_false, xorFin_xor]
    have hmask : xorFin (fun j : Fin (r - 1) => b && decide (3 ≤ 3 * (j.val + 1) + c)) =
        (b && decide ((r - 1) % 2 = 1)) := by
      have h1 : xorFin (fun j : Fin (r - 1) => b && decide (3 ≤ 3 * (j.val + 1) + c)) =
          xorFin (fun _ : Fin (r - 1) => b) :=
        xorFin_congr _ _ (fun j => by rw [decide_eq_true (by omega), Bool.and_true])
      rw [h1, xorFin_const]
    rw [hmask, Bool.xor_assoc]
  have hs01_t : resSum r hk3 t 0 (by omega) = resSum r hk3 t 1 (by omega) := by
    have h0 := hres_t 0 (by omega); have h1 := hres_t 1 (by omega)
    have heq : resSum r hk3 w 0 (by omega) = resSum r hk3 w 1 (by omega) := hres.1.trans hres.2.1.symm
    rw [h0, h1] at heq
    cases ha : resSum r hk3 t 0 (by omega) <;> cases hb : resSum r hk3 t 1 (by omega) <;>
      cases hc : (b && decide ((r - 1) % 2 = 1)) <;> simp [ha, hb, hc] at heq ⊢
  have hs02_t : resSum r hk3 t 0 (by omega) = resSum r hk3 t 2 (by omega) := by
    have h0 := hres_t 0 (by omega); have h2 := hres_t 2 (by omega)
    have heq : resSum r hk3 w 0 (by omega) = resSum r hk3 w 2 (by omega) := hres.1.trans hres.2.2.symm
    rw [h0, h2] at heq
    cases ha : resSum r hk3 t 0 (by omega) <;> cases hb : resSum r hk3 t 2 (by omega) <;>
      cases hc : (b && decide ((r - 1) % 2 = 1)) <;> simp [ha, hb, hc] at heq ⊢
  exact ⟨ht3, hw_eq, hs01_t, hs02_t⟩

def Q0 (hr : 2 ≤ r) (hk3 : k = 3 * r) (t : Fin k → Bool) : Bool :=
  !(t ⟨1, by omega⟩) && t ⟨2, by omega⟩

def Qk (hr : 2 ≤ r) (hk3 : k = 3 * r) (t : Fin k → Bool) : Bool :=
  !(t ⟨0, hk_of hr hk3⟩) && t ⟨1, by omega⟩

def Qp (r : Nat) (t : Fin k → Bool) : Bool :=
  xorFin (fun i : Fin k => decide (i ∈ neededSet r k) && (!(t (ix hk (i.val + 1))) && t (ix hk (i.val + 2))))

def QpMid (hr : 2 ≤ r) (hk3 : k = 3 * r) (t : Fin k → Bool) : Bool :=
  xor (xor (t ⟨4, by omega⟩) (!(t ⟨4, by omega⟩) && t ⟨5, by omega⟩))
    (xor (!(t ⟨k - 1, by omega⟩) && t ⟨0, hk⟩)
      (xorFin (fun j : Fin (r - 2) =>
        xor (t ⟨3 * (j.val + 2) + 1, by omega⟩ &&
              !(xor (t ⟨3 * (j.val + 2), by omega⟩) (t ⟨3 * (j.val + 2) + 2, by omega⟩)))
            (t ⟨3 * (j.val + 2) + 2, by omega⟩))))

def linP (r : Nat) (u t : Fin k → Bool) : Bool :=
  xorFin (fun i : Fin k =>
    decide (i ∈ neededSet r k) &&
      xor (t i) (xor (zOf t false false (ix hk (i.val + 1))) (u (ix hk (i.val + 1)))))

lemma mem_neededSet_iff (r : Nat) (i : Fin k) :
    i ∈ neededSet r k ↔
      (if i.val = 0 ∨ i.val = k - 1 then r % 2 = 0
       else i.val = 1 ∨ i.val = k - 2 ∨ i.val % 3 ≠ 1) := by
  simp [neededSet]

lemma neededSet_c0 (hr : 2 ≤ r) (hk3 : k = 3 * r) (j : Fin r) :
    decide (⟨3 * j.val, by omega⟩ ∈ neededSet r k) =
      if j.val = 0 then decide (r % 2 = 0) else true := by
  by_cases hj : j.val = 0
  · simp [hj, mem_neededSet_iff]
  · rw [ite_neg hj]
    apply decide_eq_true; rw [mem_neededSet_iff]; dsimp only
    have hn : ¬(3 * j.val = 0 ∨ 3 * j.val = k - 1) := by omega
    rw [ite_neg hn]
    right; right; omega

lemma neededSet_c1 (hr : 2 ≤ r) (hk3 : k = 3 * r) (j : Fin r) :
    decide (⟨3 * j.val + 1, by omega⟩ ∈ neededSet r k) =
      decide (j.val = 0 ∨ j.val = r - 1) := by
  by_cases hj : j.val = 0 ∨ j.val = r - 1
  · rw [decide_eq_true hj]; apply decide_eq_true; rw [mem_neededSet_iff]; dsimp only
    have hn : ¬(3 * j.val + 1 = 0 ∨ 3 * j.val + 1 = k - 1) := by omega
    rw [ite_neg hn]
    rcases hj with h0 | hl
    · left; omega
    · right; left; omega
  · rw [decide_eq_false hj]; apply decide_eq_false; rw [mem_neededSet_iff]; dsimp only
    have hn : ¬(3 * j.val + 1 = 0 ∨ 3 * j.val + 1 = k - 1) := by omega
    rw [ite_neg hn]
    omega

lemma neededSet_c2 (hr : 2 ≤ r) (hk3 : k = 3 * r) (j : Fin r) :
    decide (⟨3 * j.val + 2, by omega⟩ ∈ neededSet r k) =
      if j.val = r - 1 then decide (r % 2 = 0) else true := by
  by_cases hj : j.val = r - 1
  · rw [ite_pos hj]
    have h1 : 3 * j.val + 2 = k - 1 := by omega
    simp [mem_neededSet_iff, h1]
  · rw [ite_neg hj]
    apply decide_eq_true; rw [mem_neededSet_iff]; dsimp only
    have hn : ¬(3 * j.val + 2 = 0 ∨ 3 * j.val + 2 = k - 1) := by omega
    rw [ite_neg hn]
    right; right; omega

lemma neededSet_res_even (hr : 2 ≤ r) (hk3 : k = 3 * r) (c : Nat) (hc : c < 3) :
    xorFin (fun j : Fin r => decide (⟨3 * j.val + c, by omega⟩ ∈ neededSet r k)) = false := by
  interval_cases c
  · rw [xorFin_first (by omega)]
    dsimp only
    have h0 : decide (⟨3 * 0 + 0, by omega⟩ ∈ neededSet r k) = decide (r % 2 = 0) := by
      have hc0 := neededSet_c0 hr hk3 ⟨0, by omega⟩; simpa using hc0
    have ht : xorFin (fun j : Fin (r - 1) => decide (⟨3 * (j.val + 1) + 0, by omega⟩ ∈ neededSet r k)) =
        decide ((r - 1) % 2 = 1) := by
      have h1 : xorFin (fun j : Fin (r - 1) => decide (⟨3 * (j.val + 1) + 0, by omega⟩ ∈ neededSet r k)) =
          xorFin (fun _ : Fin (r - 1) => true) :=
        xorFin_congr _ _ (fun j => by
          have hc0 := neededSet_c0 hr hk3 ⟨j.val + 1, by omega⟩
          simpa using hc0)
      rw [h1, xorFin_const, Bool.true_and]
    rw [h0, ht]
    by_cases he : r % 2 = 0
    · have ho : (r - 1) % 2 = 1 := by omega
      rw [decide_eq_true he, decide_eq_true ho]; rfl
    · have ho : ¬((r - 1) % 2 = 1) := by omega
      rw [decide_eq_false he, decide_eq_false ho]; rfl
  · rw [xorFin_ends hr]
    dsimp only
    have h0 : decide (⟨3 * 0 + 1, by omega⟩ ∈ neededSet r k) = true := by
      rw [neededSet_c1 hr hk3 ⟨0, by omega⟩]; simp
    have hl : decide (⟨3 * (r - 1) + 1, by omega⟩ ∈ neededSet r k) = true := by
      rw [neededSet_c1 hr hk3 ⟨r - 1, by omega⟩]; simp
    have hm : xorFin (fun j : Fin (r - 2) => decide (⟨3 * (j.val + 1) + 1, by omega⟩ ∈ neededSet r k)) = false :=
      xorFin_eq_false _ (fun j => by
        rw [neededSet_c1 hr hk3 ⟨j.val + 1, by omega⟩]
        apply decide_eq_false; dsimp only; omega)
    rw [h0, hl, hm]; rfl
  · rw [xorFin_last (by omega)]
    dsimp only
    have hl : decide (⟨3 * (r - 1) + 2, by omega⟩ ∈ neededSet r k) = decide (r % 2 = 0) := by
      have hc2 := neededSet_c2 hr hk3 ⟨r - 1, by omega⟩
      simpa using hc2
    have hm : xorFin (fun j : Fin (r - 1) => decide (⟨3 * j.val + 2, by omega⟩ ∈ neededSet r k)) =
        decide ((r - 1) % 2 = 1) := by
      have h1 : xorFin (fun j : Fin (r - 1) => decide (⟨3 * j.val + 2, by omega⟩ ∈ neededSet r k)) =
          xorFin (fun _ : Fin (r - 1) => true) :=
        xorFin_congr _ _ (fun j => by
          have hc2 := neededSet_c2 hr hk3 ⟨j.val, by omega⟩
          have hne : j.val ≠ r - 1 := by omega
          simpa [hne] using hc2)
      rw [h1, xorFin_const, Bool.true_and]
    rw [hl, hm]
    by_cases he : r % 2 = 0
    · have ho : (r - 1) % 2 = 1 := by omega
      rw [decide_eq_true he, decide_eq_true ho]; rfl
    · have ho : ¬((r - 1) % 2 = 1) := by omega
      rw [decide_eq_false he, decide_eq_false ho]; rfl

lemma neededSet_zZero_cancel (hr : 2 ≤ r) (hk3 : k = 3 * r) (z0 z1 : Bool) :
    xorFin (fun i : Fin k => decide (i ∈ neededSet r k) &&
      zOf (fun _ => false) z0 z1 (ix hk (i.val + 1))) = false := by
  rw [xorFin_split3 hr hk3]
  have hcls : ∀ (c : Nat) (hc : c < 3) (v : Bool),
      (∀ j : Fin r, zOf (fun _ => false) z0 z1 (ix hk (3 * j.val + c + 1)) = v) →
      xorFin (fun j : Fin r => decide (⟨3 * j.val + c, by omega⟩ ∈ neededSet r k) &&
        zOf (fun _ => false) z0 z1 (ix hk (3 * j.val + c + 1))) = false := by
    intro c hc v hv
    have h1 : xorFin (fun j : Fin r => decide (⟨3 * j.val + c, by omega⟩ ∈ neededSet r k) &&
          zOf (fun _ => false) z0 z1 (ix hk (3 * j.val + c + 1))) =
        xorFin (fun j : Fin r => decide (⟨3 * j.val + c, by omega⟩ ∈ neededSet r k) && v) :=
      xorFin_congr _ _ (fun j => by rw [hv j])
    rw [h1, xorFin_and_right, neededSet_res_even hr hk3 c hc, Bool.false_and]
  have hv0 : ∀ j : Fin r, zOf (fun _ => false) z0 z1 (ix hk (3 * j.val + 0 + 1)) = z1 := by
    intro j; unfold zOf; rw [zPair_zero]; dsimp only [ix]
    have hlt : 3 * j.val + 0 + 1 < k := by omega
    have hm1 : (3 * j.val + 0 + 1) % 3 = 1 := by omega
    simp only [Nat.mod_eq_of_lt hlt, hm1]; rfl
  have hv1 : ∀ j : Fin r, zOf (fun _ => false) z0 z1 (ix hk (3 * j.val + 1 + 1)) = xor z0 z1 := by
    intro j; unfold zOf; rw [zPair_zero]; dsimp only [ix]
    have hlt : 3 * j.val + 1 + 1 < k := by omega
    have hm2 : (3 * j.val + 1 + 1) % 3 = 2 := by omega
    simp only [Nat.mod_eq_of_lt hlt, hm2]; rfl
  have hv2 : ∀ j : Fin r, zOf (fun _ => false) z0 z1 (ix hk (3 * j.val + 2 + 1)) = z0 := by
    intro j; unfold zOf; rw [zPair_zero]; dsimp only [ix]
    have hm0 : ((3 * j.val + 2 + 1) % k) % 3 = 0 := by
      by_cases hjl : j.val = r - 1
      · rw [show 3 * j.val + 2 + 1 = k by omega, Nat.mod_self]
      · have hlt : 3 * j.val + 2 + 1 < k := by omega
        rw [Nat.mod_eq_of_lt hlt]; omega
    simp only [hm0]; rfl
  have hc0 : xorFin (fun j : Fin r => decide (⟨3 * j.val, by omega⟩ ∈ neededSet r k) &&
      zOf (fun _ => false) z0 z1 (ix hk (3 * j.val + 1))) = false := hcls 0 (by omega) z1 hv0
  have hc1 := hcls 1 (by omega) (xor z0 z1) hv1
  have hc2 := hcls 2 (by omega) z0 hv2
  dsimp only at hc0 hc1 hc2 ⊢
  rw [hc0, hc1, hc2]; rfl

lemma neededSet_lin_b_zero (hr : 2 ≤ r) (hk3 : k = 3 * r) :
    xorFin (fun i : Fin k => decide (i ∈ neededSet r k) &&
      xor (decide (3 ≤ i.val))
          (zOf (fun p : Fin k => decide (3 ≤ p.val)) false false (ix hk (i.val + 1)))) = false := by
  rw [xorFin_split3 hr hk3]
  have hzmask : ∀ p : Fin k,
      zOf (fun q : Fin k => decide (3 ≤ q.val)) false false p =
        decide (4 ≤ p.val ∧ p.val % 3 = 1) := fun p => by
    unfold zOf; rw [zPair_mask3 p.val p.isLt]
  have hc0 : xorFin (fun j : Fin r => decide (⟨3 * j.val, by omega⟩ ∈ neededSet r k) &&
      xor (decide (3 ≤ 3 * j.val))
          (zOf (fun p : Fin k => decide (3 ≤ p.val)) false false (ix hk (3 * j.val + 1)))) = false := by
    apply xorFin_eq_false; intro j
    rw [hzmask]; dsimp only [ix]
    have hlt : 3 * j.val + 1 < k := by omega
    simp only [Nat.mod_eq_of_lt hlt]
    by_cases hj : j.val = 0
    · simp [hj]
    · have h1 : 3 ≤ 3 * j.val := by omega
      have h2 : 4 ≤ 3 * j.val + 1 ∧ (3 * j.val + 1) % 3 = 1 := by omega
      rw [decide_eq_true h1, decide_eq_true h2]; simp
  have hc1 : xorFin (fun j : Fin r => decide (⟨3 * j.val + 1, by omega⟩ ∈ neededSet r k) &&
      xor (decide (3 ≤ 3 * j.val + 1))
          (zOf (fun p : Fin k => decide (3 ≤ p.val)) false false (ix hk (3 * j.val + 1 + 1)))) = true := by
    rw [xorFin_ends hr]; dsimp only
    have h0 : (decide (⟨3 * 0 + 1, by omega⟩ ∈ neededSet r k) &&
        xor (decide (3 ≤ 3 * 0 + 1))
            (zOf (fun p : Fin k => decide (3 ≤ p.val)) false false (ix hk (3 * 0 + 1 + 1)))) = false := by
      rw [hzmask]; dsimp only [ix]
      have hlt : 3 * 0 + 1 + 1 < k := by omega
      simp only [Nat.mod_eq_of_lt hlt]; simp
    have hl : (decide (⟨3 * (r - 1) + 1, by omega⟩ ∈ neededSet r k) &&
        xor (decide (3 ≤ 3 * (r - 1) + 1))
            (zOf (fun p : Fin k => decide (3 ≤ p.val)) false false (ix hk (3 * (r - 1) + 1 + 1)))) = true := by
      rw [neededSet_c1 hr hk3 ⟨r - 1, by omega⟩, hzmask]; dsimp only [ix]
      have hlt : 3 * (r - 1) + 1 + 1 < k := by omega
      simp only [Nat.mod_eq_of_lt hlt]
      have h1 : 3 ≤ 3 * (r - 1) + 1 := by omega
      have h2 : ¬(4 ≤ 3 * (r - 1) + 1 + 1 ∧ (3 * (r - 1) + 1 + 1) % 3 = 1) := by omega
      rw [decide_eq_true (Or.inr True.intro), decide_eq_true h1, decide_eq_false h2]; rfl
    have hm : xorFin (fun j : Fin (r - 2) =>
        decide (⟨3 * (j.val + 1) + 1, by omega⟩ ∈ neededSet r k) &&
          xor (decide (3 ≤ 3 * (j.val + 1) + 1))
              (zOf (fun p : Fin k => decide (3 ≤ p.val)) false false (ix hk (3 * (j.val + 1) + 1 + 1)))) = false := by
      apply xorFin_eq_false; intro j
      rw [neededSet_c1 hr hk3 ⟨j.val + 1, by omega⟩]
      have hn : ¬(j.val + 1 = 0 ∨ j.val + 1 = r - 1) := by omega
      rw [decide_eq_false hn, Bool.false_and]
    rw [h0, hl, hm]; rfl
  have hc2 : xorFin (fun j : Fin r => decide (⟨3 * j.val + 2, by omega⟩ ∈ neededSet r k) &&
      xor (decide (3 ≤ 3 * j.val + 2))
          (zOf (fun p : Fin k => decide (3 ≤ p.val)) false false (ix hk (3 * j.val + 2 + 1)))) = true := by
    rw [xorFin_ends hr]; dsimp only
    have h0 : (decide (⟨3 * 0 + 2, by omega⟩ ∈ neededSet r k) &&
        xor (decide (3 ≤ 3 * 0 + 2))
            (zOf (fun p : Fin k => decide (3 ≤ p.val)) false false (ix hk (3 * 0 + 2 + 1)))) = false := by
      rw [hzmask]; dsimp only [ix]
      have hlt : 3 * 0 + 2 + 1 < k := by omega
      simp only [Nat.mod_eq_of_lt hlt]; simp
    have hl : (decide (⟨3 * (r - 1) + 2, by omega⟩ ∈ neededSet r k) &&
        xor (decide (3 ≤ 3 * (r - 1) + 2))
            (zOf (fun p : Fin k => decide (3 ≤ p.val)) false false (ix hk (3 * (r - 1) + 2 + 1)))) =
        decide (r % 2 = 0) := by
      have hn := neededSet_c2 hr hk3 ⟨r - 1, by omega⟩
      dsimp only at hn; rw [ite_pos rfl] at hn
      rw [hn, hzmask]; dsimp only [ix]
      have heq : 3 * (r - 1) + 2 + 1 = k := by omega
      simp only [heq, Nat.mod_self]
      have h1 : 3 ≤ 3 * (r - 1) + 2 := by omega
      simp [h1]
    have hm : xorFin (fun j : Fin (r - 2) =>
        decide (⟨3 * (j.val + 1) + 2, by omega⟩ ∈ neededSet r k) &&
          xor (decide (3 ≤ 3 * (j.val + 1) + 2))
              (zOf (fun p : Fin k => decide (3 ≤ p.val)) false false (ix hk (3 * (j.val + 1) + 2 + 1)))) =
        decide ((r - 2) % 2 = 1) := by
      have h1 : xorFin (fun j : Fin (r - 2) =>
            decide (⟨3 * (j.val + 1) + 2, by omega⟩ ∈ neededSet r k) &&
              xor (decide (3 ≤ 3 * (j.val + 1) + 2))
                  (zOf (fun p : Fin k => decide (3 ≤ p.val)) false false (ix hk (3 * (j.val + 1) + 2 + 1)))) =
          xorFin (fun _ : Fin (r - 2) => true) := by
        apply xorFin_congr; intro j
        have hn := neededSet_c2 hr hk3 ⟨j.val + 1, by omega⟩
        dsimp only at hn; rw [ite_neg (by omega)] at hn
        rw [hn, hzmask]; dsimp only [ix]
        have hlt : 3 * (j.val + 1) + 2 + 1 < k := by omega
        simp only [Nat.mod_eq_of_lt hlt]
        have h3 : 3 ≤ 3 * (j.val + 1) + 2 := by omega
        have hm0 : ¬(4 ≤ 3 * (j.val + 1) + 2 + 1 ∧ (3 * (j.val + 1) + 2 + 1) % 3 = 1) := by omega
        rw [decide_eq_true h3, decide_eq_false hm0]; rfl
      rw [h1, xorFin_const, Bool.true_and]
    rw [h0, hl, hm]
    by_cases he : r % 2 = 0
    · have hm0 : ¬((r - 2) % 2 = 1) := by omega
      rw [decide_eq_true he, decide_eq_false hm0]; rfl
    · have hm1 : (r - 2) % 2 = 1 := by omega
      rw [decide_eq_false he, decide_eq_true hm1]; rfl
  dsimp only at hc0 hc1 hc2 ⊢
  rw [hc0, hc1, hc2]; rfl

lemma neededSet_quad_b_one (hr : 2 ≤ r) (hk3 : k = 3 * r) (t : Fin k → Bool) (b : Bool)
    (hs02 : resSum r hk3 t 0 (by omega) = resSum r hk3 t 2 (by omega)) :
    let w := add t (fun i => b && decide (3 ≤ i.val))
    xorFin (fun i : Fin k => decide (i ∈ neededSet r k) &&
      (!(w (ix hk (i.val + 1))) && w (ix hk (i.val + 2)))) =
    xor b (Qp hk r t) := by
  intro w
  unfold Qp
  suffices hdiff : xorFin (fun i : Fin k => decide (i ∈ neededSet r k) &&
      xor (!(w (ix hk (i.val + 1))) && w (ix hk (i.val + 2)))
          (!(t (ix hk (i.val + 1))) && t (ix hk (i.val + 2)))) = b by
    have h1 : xor (xorFin (fun i : Fin k => decide (i ∈ neededSet r k) &&
            (!(w (ix hk (i.val + 1))) && w (ix hk (i.val + 2)))))
          (xorFin (fun i : Fin k => decide (i ∈ neededSet r k) &&
            (!(t (ix hk (i.val + 1))) && t (ix hk (i.val + 2))))) = b := by
      rw [← xorFin_xor]
      rw [← hdiff]
      apply xorFin_congr; intro i
      cases decide (i ∈ neededSet r k) <;> cases (!(w (ix hk (i.val + 1))) && w (ix hk (i.val + 2))) <;>
        cases (!(t (ix hk (i.val + 1))) && t (ix hk (i.val + 2))) <;> rfl
    cases ha : xorFin (fun i : Fin k => decide (i ∈ neededSet r k) &&
            (!(w (ix hk (i.val + 1))) && w (ix hk (i.val + 2)))) <;>
      cases hc : xorFin (fun i : Fin k => decide (i ∈ neededSet r k) &&
            (!(t (ix hk (i.val + 1))) && t (ix hk (i.val + 2)))) <;>
      cases b <;> simp [ha, hc] at h1 ⊢
  have hterm : ∀ i : Fin k,
      xor (!(w (ix hk (i.val + 1))) && w (ix hk (i.val + 2)))
          (!(t (ix hk (i.val + 1))) && t (ix hk (i.val + 2))) =
      (b && (if i.val = 0 then false
             else if i.val = 1 then !(t ⟨2, by omega⟩)
             else if i.val < k - 2 then xor (t (ix hk (i.val + 1))) (t (ix hk (i.val + 2)))
             else if i.val = k - 2 then t ⟨0, hk⟩
             else false)) := by
    intro i; unfold w add
    by_cases hi0 : i.val = 0
    · have h1 : ix hk (i.val + 1) = ⟨1, by omega⟩ := by rw [hi0]; exact ix_eq_of_lt hk (by omega)
      have h2 : ix hk (i.val + 2) = ⟨2, by omega⟩ := by rw [hi0]; exact ix_eq_of_lt hk (by omega)
      rw [h1, h2, ite_pos hi0]; simp
    · by_cases hi1 : i.val = 1
      · have h1 : ix hk (i.val + 1) = ⟨2, by omega⟩ := by rw [hi1]; exact ix_eq_of_lt hk (by omega)
        have h2 : ix hk (i.val + 2) = ⟨3, by omega⟩ := by rw [hi1]; exact ix_eq_of_lt hk (by omega)
        rw [ite_neg hi0, ite_pos hi1]
        simp only [h1, h2]
        cases b <;> cases t ⟨2, by omega⟩ <;> cases t ⟨3, by omega⟩ <;> rfl
      · by_cases hilt : i.val < k - 2
        · have h1 : (ix hk (i.val + 1)).val = i.val + 1 := by dsimp [ix]; rw [Nat.mod_eq_of_lt (by omega)]
          have h2 : (ix hk (i.val + 2)).val = i.val + 2 := by dsimp [ix]; rw [Nat.mod_eq_of_lt (by omega)]
          rw [ite_neg hi0, ite_neg hi1, ite_pos hilt]
          simp only [h1, h2, decide_eq_true (by omega : 3 ≤ i.val + 1), decide_eq_true (by omega : 3 ≤ i.val + 2)]
          cases b <;> cases t (ix hk (i.val + 1)) <;> cases t (ix hk (i.val + 2)) <;> rfl
        · by_cases hik2 : i.val = k - 2
          · have h1 : ix hk (i.val + 1) = ⟨k - 1, by omega⟩ := by
              rw [hik2, show k - 2 + 1 = k - 1 by omega]; exact ix_eq_of_lt hk (by omega)
            have h2 : ix hk (i.val + 2) = ⟨0, hk⟩ :=
              (ix_mod_eq hk (by rw [hik2, show k - 2 + 2 = k by omega, Nat.mod_self, Nat.zero_mod])).trans (ix_eq_of_lt hk hk)
            rw [ite_neg hi0, ite_neg hi1, ite_neg hilt, ite_pos hik2]
            simp only [h1, h2, decide_eq_true (by omega : 3 ≤ k - 1)]
            cases b <;> cases t ⟨k - 1, by omega⟩ <;> cases t ⟨0, hk⟩ <;> rfl
          · have hik1 : i.val = k - 1 := by omega
            have h1 : ix hk (i.val + 1) = ⟨0, hk⟩ :=
              (ix_mod_eq hk (by rw [hik1, show k - 1 + 1 = k by omega, Nat.mod_self, Nat.zero_mod])).trans (ix_eq_of_lt hk hk)
            have h2 : ix hk (i.val + 2) = ⟨1, by omega⟩ :=
              (ix_mod_eq hk (by rw [hik1, show k - 1 + 2 = 1 + k by omega, Nat.add_mod_right])).trans (ix_eq_of_lt hk (by omega))
            rw [ite_neg hi0, ite_neg hi1, ite_neg hilt, ite_neg hik2]
            simp only [h1, h2]; simp
  have hfac : xorFin (fun i : Fin k => decide (i ∈ neededSet r k) &&
        xor (!(w (ix hk (i.val + 1))) && w (ix hk (i.val + 2)))
            (!(t (ix hk (i.val + 1))) && t (ix hk (i.val + 2)))) =
      (b && xorFin (fun i : Fin k => decide (i ∈ neededSet r k) &&
        (if i.val = 0 then false
         else if i.val = 1 then !(t ⟨2, by omega⟩)
         else if i.val < k - 2 then xor (t (ix hk (i.val + 1))) (t (ix hk (i.val + 2)))
         else if i.val = k - 2 then t ⟨0, hk⟩
         else false))) := by
    rw [← xorFin_and_left b]
    apply xorFin_congr; intro i; rw [hterm i]
    cases decide (i ∈ neededSet r k) <;> cases b <;> rfl
  rw [hfac]
  suffices hone : xorFin (fun i : Fin k => decide (i ∈ neededSet r k) &&
      (if i.val = 0 then false
       else if i.val = 1 then !(t ⟨2, by omega⟩)
       else if i.val < k - 2 then xor (t (ix hk (i.val + 1))) (t (ix hk (i.val + 2)))
       else if i.val = k - 2 then t ⟨0, hk⟩
       else false)) = true by
    rw [hone, Bool.and_true]
  rw [xorFin_split3 hr hk3]

  have hc0 : xorFin (fun j : Fin r => decide (⟨3 * j.val, by omega⟩ ∈ neededSet r k) &&
      (if 3 * j.val = 0 then false
       else if 3 * j.val = 1 then !(t ⟨2, by omega⟩)
       else if 3 * j.val < k - 2 then xor (t (ix hk (3 * j.val + 1))) (t (ix hk (3 * j.val + 2)))
       else if 3 * j.val = k - 2 then t ⟨0, hk⟩
       else false)) =
    xorFin (fun j : Fin (r - 1) =>
      xor (t ⟨3 * (j.val + 1) + 1, by omega⟩) (t ⟨3 * (j.val + 1) + 2, by omega⟩)) := by
    rw [xorFin_first (by omega)]
    simp only [Nat.mul_zero, ite_true, Bool.and_false, Bool.false_xor]
    apply xorFin_congr; intro j
    have hn := neededSet_c0 hr hk3 ⟨j.val + 1, by omega⟩
    dsimp only at hn; rw [ite_neg (by omega)] at hn
    rw [hn, Bool.true_and,
      ite_neg (by omega), ite_neg (by omega), ite_pos (by omega : 3 * (j.val + 1) < k - 2),
      ix_eq_of_lt hk (by omega), ix_eq_of_lt hk (by omega)]

  have hc1 : xorFin (fun j : Fin r => decide (⟨3 * j.val + 1, by omega⟩ ∈ neededSet r k) &&
      (if 3 * j.val + 1 = 0 then false
       else if 3 * j.val + 1 = 1 then !(t ⟨2, by omega⟩)
       else if 3 * j.val + 1 < k - 2 then xor (t (ix hk (3 * j.val + 1 + 1))) (t (ix hk (3 * j.val + 1 + 2)))
       else if 3 * j.val + 1 = k - 2 then t ⟨0, hk⟩
       else false)) =
    xor (!(t ⟨2, by omega⟩)) (t ⟨0, hk⟩) := by
    rw [xorFin_ends hr]; dsimp only
    have h0 : decide (⟨3 * 0 + 1, by omega⟩ ∈ neededSet r k) = true := by
      rw [neededSet_c1 hr hk3 ⟨0, by omega⟩]; simp
    have hl : decide (⟨3 * (r - 1) + 1, by omega⟩ ∈ neededSet r k) = true := by
      rw [neededSet_c1 hr hk3 ⟨r - 1, by omega⟩]; simp
    have hm : xorFin (fun j : Fin (r - 2) => decide (⟨3 * (j.val + 1) + 1, by omega⟩ ∈ neededSet r k) &&
        (if 3 * (j.val + 1) + 1 = 0 then false
         else if 3 * (j.val + 1) + 1 = 1 then !(t ⟨2, by omega⟩)
         else if 3 * (j.val + 1) + 1 < k - 2 then xor (t (ix hk (3 * (j.val + 1) + 1 + 1))) (t (ix hk (3 * (j.val + 1) + 1 + 2)))
         else if 3 * (j.val + 1) + 1 = k - 2 then t ⟨0, hk⟩
         else false)) = false := by
      apply xorFin_eq_false; intro j
      rw [neededSet_c1 hr hk3 ⟨j.val + 1, by omega⟩]
      have hn : ¬(j.val + 1 = 0 ∨ j.val + 1 = r - 1) := by omega
      rw [decide_eq_false hn, Bool.false_and]
    rw [h0, hl, hm, Bool.true_and, Bool.true_and, Bool.false_xor]
    have h00 : (3 * 0 + 1 : Nat) ≠ 0 := by omega
    have h01 : (3 * 0 + 1 : Nat) = 1 := by omega
    have hl0 : 3 * (r - 1) + 1 ≠ 0 := by omega
    have hl1 : 3 * (r - 1) + 1 ≠ 1 := by omega
    have hll : ¬(3 * (r - 1) + 1 < k - 2) := by omega
    have hlk : 3 * (r - 1) + 1 = k - 2 := by omega
    rw [ite_neg h00, ite_pos h01, ite_neg hl0, ite_neg hl1, ite_neg hll, ite_pos hlk]

  have hc2 : xorFin (fun j : Fin r => decide (⟨3 * j.val + 2, by omega⟩ ∈ neededSet r k) &&
      (if 3 * j.val + 2 = 0 then false
       else if 3 * j.val + 2 = 1 then !(t ⟨2, by omega⟩)
       else if 3 * j.val + 2 < k - 2 then xor (t (ix hk (3 * j.val + 2 + 1))) (t (ix hk (3 * j.val + 2 + 2)))
       else if 3 * j.val + 2 = k - 2 then t ⟨0, hk⟩
       else false)) =
    xorFin (fun j : Fin (r - 1) =>
      xor (t ⟨3 * (j.val + 1), by omega⟩) (t ⟨3 * (j.val + 1) + 1, by omega⟩)) := by
    rw [xorFin_last (by omega)]; dsimp only
    have hlast : (if 3 * (r - 1) + 2 = 0 then false
       else if 3 * (r - 1) + 2 = 1 then !(t ⟨2, by omega⟩)
       else if 3 * (r - 1) + 2 < k - 2 then xor (t (ix hk (3 * (r - 1) + 2 + 1))) (t (ix hk (3 * (r - 1) + 2 + 2)))
       else if 3 * (r - 1) + 2 = k - 2 then t ⟨0, hk⟩
       else false) = false := by
      rw [ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_neg (by omega)]
    rw [hlast, Bool.and_false, Bool.xor_false]
    apply xorFin_congr; intro j
    have hn := neededSet_c2 hr hk3 ⟨j.val, by omega⟩
    dsimp only at hn; rw [ite_neg (by omega)] at hn
    rw [hn, Bool.true_and,
      ite_neg (by omega), ite_neg (by omega), ite_pos (by omega : 3 * j.val + 2 < k - 2),
      ix_eq_of_lt hk (by omega), ix_eq_of_lt hk (by omega)]
    exact congrArg₂ xor (congrArg t (Fin.ext (by dsimp only; omega))) (congrArg t (Fin.ext (by dsimp only; omega)))
  dsimp only at hc0 hc1 hc2 ⊢
  rw [hc0, hc1, hc2]

  have hpair : xor (xorFin (fun j : Fin (r - 1) =>
        xor (t ⟨3 * (j.val + 1) + 1, by omega⟩) (t ⟨3 * (j.val + 1) + 2, by omega⟩)))
      (xorFin (fun j : Fin (r - 1) =>
        xor (t ⟨3 * (j.val + 1), by omega⟩) (t ⟨3 * (j.val + 1) + 1, by omega⟩))) =
    xor (xor (resSum r hk3 t 0 (by omega)) (t ⟨0, hk⟩))
        (xor (resSum r hk3 t 2 (by omega)) (t ⟨2, by omega⟩)) := by
    have htele : xor (xorFin (fun j : Fin (r - 1) =>
          xor (t ⟨3 * (j.val + 1) + 1, by omega⟩) (t ⟨3 * (j.val + 1) + 2, by omega⟩)))
        (xorFin (fun j : Fin (r - 1) =>
          xor (t ⟨3 * (j.val + 1), by omega⟩) (t ⟨3 * (j.val + 1) + 1, by omega⟩))) =
      xor (xorFin (fun j : Fin (r - 1) => t ⟨3 * (j.val + 1), by omega⟩))
          (xorFin (fun j : Fin (r - 1) => t ⟨3 * (j.val + 1) + 2, by omega⟩)) := by
      rw [← xorFin_xor, ← xorFin_xor]
      apply xorFin_congr; intro j
      cases t ⟨3 * (j.val + 1), by omega⟩ <;> cases t ⟨3 * (j.val + 1) + 1, by omega⟩ <;>
        cases t ⟨3 * (j.val + 1) + 2, by omega⟩ <;> rfl
    have hs0 : resSum r hk3 t 0 (by omega) =
        xor (t ⟨0, hk⟩) (xorFin (fun j : Fin (r - 1) => t ⟨3 * (j.val + 1), by omega⟩)) := by
      unfold resSum; rw [xorFin_first (by omega)]; rfl
    have hs2 : resSum r hk3 t 2 (by omega) =
        xor (t ⟨2, by omega⟩) (xorFin (fun j : Fin (r - 1) => t ⟨3 * (j.val + 1) + 2, by omega⟩)) := by
      unfold resSum; rw [xorFin_first (by omega)]; rfl
    rw [htele, hs0, hs2]
    cases t ⟨0, hk⟩ <;> cases t ⟨2, by omega⟩ <;>
      cases xorFin (fun j : Fin (r - 1) => t ⟨3 * (j.val + 1), by omega⟩) <;>
      cases xorFin (fun j : Fin (r - 1) => t ⟨3 * (j.val + 1) + 2, by omega⟩) <;> rfl
  have hcomm : xor (xorFin (fun j : Fin (r - 1) =>
        xor (t ⟨3 * (j.val + 1) + 1, by omega⟩) (t ⟨3 * (j.val + 1) + 2, by omega⟩)))
      (xor (xor (!(t ⟨2, by omega⟩)) (t ⟨0, hk⟩))
           (xorFin (fun j : Fin (r - 1) =>
             xor (t ⟨3 * (j.val + 1), by omega⟩) (t ⟨3 * (j.val + 1) + 1, by omega⟩)))) =
    xor (xor (!(t ⟨2, by omega⟩)) (t ⟨0, hk⟩))
        (xor (xorFin (fun j : Fin (r - 1) =>
          xor (t ⟨3 * (j.val + 1) + 1, by omega⟩) (t ⟨3 * (j.val + 1) + 2, by omega⟩)))
        (xorFin (fun j : Fin (r - 1) =>
          xor (t ⟨3 * (j.val + 1), by omega⟩) (t ⟨3 * (j.val + 1) + 1, by omega⟩)))) := by
    cases xorFin (fun j : Fin (r - 1) => xor (t ⟨3 * (j.val + 1) + 1, by omega⟩) (t ⟨3 * (j.val + 1) + 2, by omega⟩)) <;>
      cases xor (!(t ⟨2, by omega⟩)) (t ⟨0, hk⟩) <;>
      cases xorFin (fun j : Fin (r - 1) => xor (t ⟨3 * (j.val + 1), by omega⟩) (t ⟨3 * (j.val + 1) + 1, by omega⟩)) <;> rfl
  rw [hcomm, hpair, hs02]
  cases resSum r hk3 t 2 (by omega) <;> cases t ⟨0, hk⟩ <;> cases t ⟨2, by omega⟩ <;> rfl

lemma row_recovery (hr : 2 ≤ r) (hk3 : k = 3 * r) (u t : Fin k → Bool) (b z0 z1 : Bool)
    (hs01 : resSum r hk3 t 0 (by omega) = resSum r hk3 t 1 (by omega))
    (hs02 : resSum r hk3 t 0 (by omega) = resSum r hk3 t 2 (by omega)) :
    let w := add t (fun i => b && decide (3 ≤ i.val))
    let z := zOf w z0 z1
    let x := fun i : Fin k => xor (z (ix hk (i.val + 1))) (u (ix hk (i.val + 1)))
    mix hk (add u (rot hk x)) = w ∧
    x ⟨0, hk⟩ = xor z1 (u ⟨1, by omega⟩) ∧
    x ⟨k - 1, by omega⟩ = xor z0 (u ⟨0, hk⟩) ∧
    row hk u x ⟨0, hk⟩ = xor (xor (t ⟨0, hk⟩) (Q0 hr hk3 t)) (x ⟨0, hk⟩) ∧
    row hk u x ⟨k - 1, by omega⟩ = xor (xor (xor b (t ⟨k - 1, by omega⟩)) (Qk hr hk3 t)) (x ⟨k - 1, by omega⟩) ∧
    decide (((neededSet r k).filter (fun i => row hk u x i = true)).card % 2 = 1) =
      xor b (xor (Qp hk r t) (linP hk r u t)) := by
  intro w z x
  have hrot_x : add u (rot hk x) = z := by
    funext i; unfold add rot x
    have hidx : ix hk ((ix hk (i.val + k - 1)).val + 1) = i := by
      have hinner : (ix hk (i.val + k - 1)).val = if i.val = 0 then k - 1 else i.val - 1 := by
        dsimp only [ix]; split_ifs with h0
        · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
        · rw [show i.val + k - 1 = (i.val - 1) + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      apply Fin.ext
      change ((ix hk (i.val + k - 1)).val + 1) % k = i.val
      rw [hinner]; split_ifs with h0
      · rw [show k - 1 + 1 = k by omega, Nat.mod_self]; omega
      · rw [show i.val - 1 + 1 = i.val by omega, Nat.mod_eq_of_lt i.isLt]
    rw [hidx]
    cases u i <;> cases z i <;> rfl
  have hres_w : resSum r hk3 w 0 (by omega) = resSum r hk3 w 1 (by omega) ∧
      resSum r hk3 w 0 (by omega) = resSum r hk3 w 2 (by omega) := by
    have hres_c : ∀ (c : Nat) (hc : c < 3),
        resSum r hk3 w c hc = xor (resSum r hk3 t c hc) (b && decide ((r - 1) % 2 = 1)) := by
      intro c hc; unfold resSum
      rw [xorFin_first (by omega) (fun j : Fin r => w ⟨3 * j.val + c, by omega⟩),
        xorFin_first (by omega) (fun j : Fin r => t ⟨3 * j.val + c, by omega⟩)]
      unfold w add; dsimp only
      simp only [Nat.mul_zero, Nat.zero_add]
      rw [decide_eq_false (by omega : ¬(3 ≤ c)), Bool.and_false, Bool.xor_false, xorFin_xor]
      have hm : xorFin (fun j : Fin (r - 1) => b && decide (3 ≤ 3 * (j.val + 1) + c)) =
          (b && decide ((r - 1) % 2 = 1)) := by
        have h1 : xorFin (fun j : Fin (r - 1) => b && decide (3 ≤ 3 * (j.val + 1) + c)) =
            xorFin (fun _ : Fin (r - 1) => b) :=
          xorFin_congr _ _ (fun j => by rw [decide_eq_true (by omega), Bool.and_true])
        rw [h1, xorFin_const]
      rw [hm, Bool.xor_assoc]
    have h0 := hres_c 0 (by omega)
    have h1 := hres_c 1 (by omega)
    have h2 := hres_c 2 (by omega)
    rw [h0, h1, h2]
    exact ⟨by rw [hs01], by rw [hs02]⟩
  have hmix : mix hk (add u (rot hk x)) = w := by
    rw [hrot_x]; exact mix_zOf hk hr hk3 w z0 z1 hres_w.1 hres_w.2
  have hx0 : x ⟨0, hk⟩ = xor z1 (u ⟨1, by omega⟩) := by
    unfold x; dsimp only; rw [ix_eq_of_lt hk (by omega)]; rfl
  have hxk : x ⟨k - 1, by omega⟩ = xor z0 (u ⟨0, hk⟩) := by
    unfold x; dsimp only
    rw [(ix_mod_eq hk (by rw [show k - 1 + 1 = k by omega, Nat.mod_self, Nat.zero_mod])).trans (ix_eq_of_lt hk hk)]
    rfl
  have hrow0 : row hk u x ⟨0, hk⟩ = xor (xor (t ⟨0, hk⟩) (Q0 hr hk3 t)) (x ⟨0, hk⟩) := by
    unfold row; rw [hmix]; unfold add chi Q0; dsimp only
    rw [ix_eq_of_lt hk (by omega), ix_eq_of_lt hk (by omega)]
    unfold w add; dsimp only
    rw [show decide (3 ≤ 0) = false from rfl, show decide (3 ≤ 1) = false from rfl,
      show decide (3 ≤ 2) = false from rfl]
    simp
  have hrowk : row hk u x ⟨k - 1, by omega⟩ =
      xor (xor (xor b (t ⟨k - 1, by omega⟩)) (Qk hr hk3 t)) (x ⟨k - 1, by omega⟩) := by
    unfold row; rw [hmix]; unfold add chi Qk; dsimp only
    have h1 : ix hk (k - 1 + 1) = ⟨0, hk⟩ :=
      (ix_mod_eq hk (by rw [show k - 1 + 1 = k by omega, Nat.mod_self, Nat.zero_mod])).trans (ix_eq_of_lt hk hk)
    have h2 : ix hk (k - 1 + 2) = ⟨1, by omega⟩ :=
      (ix_mod_eq hk (by rw [show k - 1 + 2 = 1 + k by omega, Nat.add_mod_right])).trans (ix_eq_of_lt hk (by omega))
    rw [h1, h2]; unfold w add; dsimp only
    rw [decide_eq_true (by omega : 3 ≤ k - 1), show decide (3 ≤ 0) = false from rfl,
      show decide (3 ≤ 1) = false from rfl]
    simp only [Bool.and_true, Bool.and_false, Bool.xor_false]
    cases b <;> cases t ⟨k - 1, by omega⟩ <;> cases (!(t ⟨0, hk⟩) && t ⟨1, by omega⟩) <;>
      cases x ⟨k - 1, by omega⟩ <;> rfl
  have hpar : decide (((neededSet r k).filter (fun i => row hk u x i = true)).card % 2 = 1) =
      xor b (xor (Qp hk r t) (linP hk r u t)) := by
    rw [xorFin_finset_card]
    have hrow_eq : ∀ i : Fin k, row hk u x i =
        xor (xor (t i) (xor (zOf t false false (ix hk (i.val + 1))) (u (ix hk (i.val + 1)))))
          (xor (b && xor (decide (3 ≤ i.val))
                         (zOf (fun p : Fin k => decide (3 ≤ p.val)) false false (ix hk (i.val + 1))))
            (xor (zOf (fun _ => false) z0 z1 (ix hk (i.val + 1)))
                 (!(w (ix hk (i.val + 1))) && w (ix hk (i.val + 2))))) := by
      intro i; unfold row; rw [hmix]; unfold add chi
      have hz_decomp : ∀ q : Fin k, z q =
          xor (zOf t false false q)
            (xor (b && zOf (fun p : Fin k => decide (3 ≤ p.val)) false false q)
                 (zOf (fun _ => false) z0 z1 q)) := by
        intro q; unfold z w
        have h1 : add t (fun p : Fin k => b && decide (3 ≤ p.val)) =
            add (add t (fun p : Fin k => b && decide (3 ≤ p.val))) (fun _ => false) := by
          funext p; unfold add; simp
        have h2 : zOf (add t (fun p : Fin k => b && decide (3 ≤ p.val))) z0 z1 q =
            xor (zOf (add t (fun p : Fin k => b && decide (3 ≤ p.val))) false false q)
                (zOf (fun _ => false) z0 z1 q) := by
          have hz := zOf_xor (add t (fun p : Fin k => b && decide (3 ≤ p.val))) (fun _ => false) false false z0 z1 q
          simp only [Bool.false_xor] at hz
          rw [← h1] at hz; exact hz
        have h3 : zOf (add t (fun p : Fin k => b && decide (3 ≤ p.val))) false false q =
            xor (zOf t false false q) (b && zOf (fun p : Fin k => decide (3 ≤ p.val)) false false q) := by
          have hz := zOf_xor t (fun p : Fin k => b && decide (3 ≤ p.val)) false false false false q
          simp only [Bool.false_xor] at hz
          rw [hz]; congr 1
          cases b
          · simp only [Bool.false_and]
            unfold zOf; rw [zPair_zero]; simp
          · simp only [Bool.true_and]
        rw [h2, h3, Bool.xor_assoc]
      unfold x; rw [hz_decomp]
      change xor (xor (xor (t i) (b && decide (3 ≤ i.val))) (!(w (ix hk (i.val + 1))) && w (ix hk (i.val + 2)))) _ = _
      cases t i <;> cases b <;> cases decide (3 ≤ i.val) <;>
        cases (!(w (ix hk (i.val + 1))) && w (ix hk (i.val + 2))) <;>
        cases zOf t false false (ix hk (i.val + 1)) <;>
        cases zOf (fun p : Fin k => decide (3 ≤ p.val)) false false (ix hk (i.val + 1)) <;>
        cases zOf (fun _ => false) z0 z1 (ix hk (i.val + 1)) <;>
        cases u (ix hk (i.val + 1)) <;> rfl
    have hsplit : xorFin (fun i : Fin k => decide (i ∈ neededSet r k) && row hk u x i) =
        xor (linP hk r u t)
          (xor (b && xorFin (fun i : Fin k => decide (i ∈ neededSet r k) &&
                  xor (decide (3 ≤ i.val))
                      (zOf (fun p : Fin k => decide (3 ≤ p.val)) false false (ix hk (i.val + 1)))))
            (xor (xorFin (fun i : Fin k => decide (i ∈ neededSet r k) &&
                    zOf (fun _ => false) z0 z1 (ix hk (i.val + 1))))
                 (xorFin (fun i : Fin k => decide (i ∈ neededSet r k) &&
                    (!(w (ix hk (i.val + 1))) && w (ix hk (i.val + 2))))))) := by
      unfold linP
      rw [← xorFin_and_left, ← xorFin_xor, ← xorFin_xor, ← xorFin_xor]
      apply xorFin_congr; intro i; rw [hrow_eq i]
      cases decide (i ∈ neededSet r k) <;> cases b <;>
        cases xor (t i) (xor (zOf t false false (ix hk (i.val + 1))) (u (ix hk (i.val + 1)))) <;>
        cases xor (decide (3 ≤ i.val)) (zOf (fun p : Fin k => decide (3 ≤ p.val)) false false (ix hk (i.val + 1))) <;>
        cases zOf (fun _ => false) z0 z1 (ix hk (i.val + 1)) <;>
        cases (!(w (ix hk (i.val + 1))) && w (ix hk (i.val + 2))) <;> rfl
    rw [hsplit, neededSet_lin_b_zero hk hr hk3, neededSet_zZero_cancel hk hr hk3,
      neededSet_quad_b_one hk hr hk3 t b hs02]
    simp only [Bool.and_false, Bool.false_xor]
    cases b <;> cases Qp hk r t <;> cases linP hk r u t <;> rfl
  exact ⟨hmix, hx0, hxk, hrow0, hrowk, hpar⟩

lemma recovery_from_record (hr : 2 ≤ r) (hk3 : k = 3 * r) (u x : Fin k → Bool) :
    let t := tOfD hr hk3 (diffFn hk u x)
    let bp := decide (((neededSet r k).filter (fun i => row hk u x i = true)).card % 2 = 1)
    let b0 := row hk u x ⟨0, hk⟩
    let bk := row hk u x ⟨k - 1, by omega⟩
    let b := xor bp (xor (Qp hk r t) (linP hk r u t))
    let x0 := xor b0 (xor (t ⟨0, hk⟩) (Q0 hr hk3 t))
    let xk := xor bk (xor b (xor (t ⟨k - 1, by omega⟩) (Qk hr hk3 t)))
    let w := add t (fun i => b && decide (3 ≤ i.val))
    let z := zOf w (xor xk (u ⟨0, hk⟩)) (xor x0 (u ⟨1, by omega⟩))
    ∀ i : Fin k, x i = xor (z (ix hk (i.val + 1))) (u (ix hk (i.val + 1))) := by
  intro t bp b0 bk b x0 xk w z
  let z_true := add u (rot hk x)
  let w_true := mix hk z_true
  let b_true := w_true ⟨3, by omega⟩
  have htd := tOfD_diff hk hr hk3 u x
  have hzt : z_true = zOf w_true (z_true ⟨0, hk⟩) (z_true ⟨1, by omega⟩) :=
    (zOf_mix hk hr hk3 z_true).symm
  have hx_eq : x = fun i : Fin k => xor (z_true (ix hk (i.val + 1))) (u (ix hk (i.val + 1))) := by
    funext i; unfold z_true add rot
    have hidx : ix hk ((ix hk (i.val + 1)).val + k - 1) = i := by
      have hinner : (ix hk (i.val + 1)).val = if i.val = k - 1 then 0 else i.val + 1 := by
        dsimp only [ix]; split_ifs with hl
        · rw [show i.val + 1 = k by omega, Nat.mod_self]
        · rw [Nat.mod_eq_of_lt (by omega)]
      apply Fin.ext
      change ((ix hk (i.val + 1)).val + k - 1) % k = i.val
      rw [hinner]; split_ifs with hl
      · rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]; omega
      · rw [show i.val + 1 + k - 1 = i.val + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
    rw [hidx]; cases u (ix hk (i.val + 1)) <;> cases x i <;> rfl
  have hrec := row_recovery hk hr hk3 u t b_true (z_true ⟨0, hk⟩) (z_true ⟨1, by omega⟩) htd.2.2.1 htd.2.2.2
  have hw_eq : add t (fun i => b_true && decide (3 ≤ i.val)) = w_true := htd.2.1.symm
  have hx_eq2 : (fun i : Fin k => xor (zOf (add t (fun i => b_true && decide (3 ≤ i.val)))
      (z_true ⟨0, hk⟩) (z_true ⟨1, by omega⟩) (ix hk (i.val + 1))) (u (ix hk (i.val + 1)))) = x := by
    rw [hw_eq, ← hzt]; exact hx_eq.symm
  have hrec_x : x ⟨0, hk⟩ = xor (z_true ⟨1, by omega⟩) (u ⟨1, by omega⟩) ∧
      x ⟨k - 1, by omega⟩ = xor (z_true ⟨0, hk⟩) (u ⟨0, hk⟩) ∧
      row hk u x ⟨0, hk⟩ = xor (xor (t ⟨0, hk⟩) (Q0 hr hk3 t)) (x ⟨0, hk⟩) ∧
      row hk u x ⟨k - 1, by omega⟩ = xor (xor (xor b_true (t ⟨k - 1, by omega⟩)) (Qk hr hk3 t)) (x ⟨k - 1, by omega⟩) ∧
      decide (((neededSet r k).filter (fun i => row hk u x i = true)).card % 2 = 1) =
        xor b_true (xor (Qp hk r t) (linP hk r u t)) := by
    dsimp only at hrec
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [← congrFun hx_eq2 ⟨0, hk⟩]; exact hrec.2.1
    · rw [← congrFun hx_eq2 ⟨k - 1, by omega⟩]; exact hrec.2.2.1
    · rw [← hx_eq2]; exact hrec.2.2.2.1
    · rw [← hx_eq2]; exact hrec.2.2.2.2.1
    · rw [← hx_eq2]; exact hrec.2.2.2.2.2
  have hb_eq : b = b_true := by
    change xor bp (xor (Qp hk r t) (linP hk r u t)) = b_true
    rw [show bp = xor b_true (xor (Qp hk r t) (linP hk r u t)) from hrec_x.2.2.2.2]
    cases b_true <;> cases Qp hk r t <;> cases linP hk r u t <;> rfl
  have hx0_eq : x0 = x ⟨0, hk⟩ := by
    change xor b0 (xor (t ⟨0, hk⟩) (Q0 hr hk3 t)) = x ⟨0, hk⟩
    rw [show b0 = xor (xor (t ⟨0, hk⟩) (Q0 hr hk3 t)) (x ⟨0, hk⟩) from hrec_x.2.2.1]
    cases xor (t ⟨0, hk⟩) (Q0 hr hk3 t) <;> cases x ⟨0, hk⟩ <;> rfl
  have hxk_eq : xk = x ⟨k - 1, by omega⟩ := by
    change xor bk (xor b (xor (t ⟨k - 1, by omega⟩) (Qk hr hk3 t))) = x ⟨k - 1, by omega⟩
    rw [hb_eq, show bk = xor (xor (xor b_true (t ⟨k - 1, by omega⟩)) (Qk hr hk3 t)) (x ⟨k - 1, by omega⟩) from hrec_x.2.2.2.1]
    cases b_true <;> cases t ⟨k - 1, by omega⟩ <;> cases Qk hr hk3 t <;> cases x ⟨k - 1, by omega⟩ <;> rfl
  have hz0_eq : xor xk (u ⟨0, hk⟩) = z_true ⟨0, hk⟩ := by
    rw [hxk_eq, hrec_x.2.1]; cases z_true ⟨0, hk⟩ <;> cases u ⟨0, hk⟩ <;> rfl
  have hz1_eq : xor x0 (u ⟨1, by omega⟩) = z_true ⟨1, by omega⟩ := by
    rw [hx0_eq, hrec_x.1]; cases z_true ⟨1, by omega⟩ <;> cases u ⟨1, by omega⟩ <;> rfl
  have hz_eq : z = z_true := by
    unfold z w; rw [hb_eq, hz0_eq, hz1_eq, hw_eq, ← hzt]
  intro i; rw [hz_eq]; exact congrFun hx_eq i

lemma Qp_eq_QpMid (hr : 2 ≤ r) (hk3 : k = 3 * r) (t : Fin k → Bool) (ht3 : t ⟨3, by omega⟩ = false) :
    Qp hk r t =
      xor (if r % 2 = 0 then xor (Q0 hr hk3 t) (Qk hr hk3 t) else false)
          (QpMid hk hr hk3 t) := by
  unfold Qp QpMid Q0 Qk
  rw [xorFin_split3 hr hk3]

  have hc0 : xorFin (fun j : Fin r => decide (⟨3 * j.val, by omega⟩ ∈ neededSet r k) &&
      (!(t (ix hk (3 * j.val + 1))) && t (ix hk (3 * j.val + 2)))) =
    xor (if r % 2 = 0 then !(t ⟨1, by omega⟩) && t ⟨2, by omega⟩ else false)
      (xor (!(t ⟨4, by omega⟩) && t ⟨5, by omega⟩)
        (xorFin (fun j : Fin (r - 2) =>
          !(t ⟨3 * (j.val + 2) + 1, by omega⟩) && t ⟨3 * (j.val + 2) + 2, by omega⟩))) := by
    rw [xorFin_first (by omega), xorFin_first (by omega)]; dsimp only
    have h0 : (decide (⟨3 * 0, by omega⟩ ∈ neededSet r k) &&
        (!(t (ix hk (3 * 0 + 1))) && t (ix hk (3 * 0 + 2)))) =
        if r % 2 = 0 then !(t ⟨1, by omega⟩) && t ⟨2, by omega⟩ else false := by
      rw [neededSet_c0 hr hk3 ⟨0, by omega⟩, ix_eq_of_lt hk (by omega), ix_eq_of_lt hk (by omega)]
      dsimp only; rw [ite_pos rfl]
      by_cases h : r % 2 = 0 <;> simp [h]
    have h1 : (decide (⟨3 * (0 + 1), by omega⟩ ∈ neededSet r k) &&
        (!(t (ix hk (3 * (0 + 1) + 1))) && t (ix hk (3 * (0 + 1) + 2)))) =
        (!(t ⟨4, by omega⟩) && t ⟨5, by omega⟩) := by
      have hn := neededSet_c0 hr hk3 ⟨1, by omega⟩
      dsimp only at hn; rw [ite_neg (by omega)] at hn
      rw [hn, Bool.true_and, ix_eq_of_lt hk (by omega), ix_eq_of_lt hk (by omega)]
    have hrest : xorFin (fun j : Fin (r - 1 - 1) =>
          decide (⟨3 * (j.val + 1 + 1), by omega⟩ ∈ neededSet r k) &&
            (!(t (ix hk (3 * (j.val + 1 + 1) + 1))) && t (ix hk (3 * (j.val + 1 + 1) + 2)))) =
        xorFin (fun j : Fin (r - 2) =>
          !(t ⟨3 * (j.val + 2) + 1, by omega⟩) && t ⟨3 * (j.val + 2) + 2, by omega⟩) := by
      refine xorFin_cast (by omega) _ _ (fun idx hi1 hi2 => ?_)
      have hn := neededSet_c0 hr hk3 ⟨idx + 2, by omega⟩
      dsimp only at hn; rw [ite_neg (by omega)] at hn
      rw [hn, Bool.true_and, ix_eq_of_lt hk (by omega), ix_eq_of_lt hk (by omega)]
    rw [h0, h1, hrest]

  have hc1 : xorFin (fun j : Fin r => decide (⟨3 * j.val + 1, by omega⟩ ∈ neededSet r k) &&
      (!(t (ix hk (3 * j.val + 1 + 1))) && t (ix hk (3 * j.val + 1 + 2)))) =
    (!(t ⟨k - 1, by omega⟩) && t ⟨0, hk⟩) := by
    rw [xorFin_ends hr]; dsimp only
    have h0 : (decide (⟨3 * 0 + 1, by omega⟩ ∈ neededSet r k) &&
        (!(t (ix hk (3 * 0 + 1 + 1))) && t (ix hk (3 * 0 + 1 + 2)))) = false := by
      rw [ix_eq_of_lt hk (by omega : 3 * 0 + 1 + 2 < k),
        show (⟨3 * 0 + 1 + 2, by omega⟩ : Fin k) = ⟨3, by omega⟩ from rfl, ht3]
      simp
    have hl : (decide (⟨3 * (r - 1) + 1, by omega⟩ ∈ neededSet r k) &&
        (!(t (ix hk (3 * (r - 1) + 1 + 1))) && t (ix hk (3 * (r - 1) + 1 + 2)))) =
        (!(t ⟨k - 1, by omega⟩) && t ⟨0, hk⟩) := by
      have hn := neededSet_c1 hr hk3 ⟨r - 1, by omega⟩
      dsimp only at hn; rw [decide_eq_true (Or.inr rfl)] at hn
      have hp1 : ix hk (3 * (r - 1) + 1 + 1) = ⟨k - 1, by omega⟩ :=
        (ix_mod_eq hk (by rw [show 3 * (r - 1) + 1 + 1 = k - 1 by omega])).trans (ix_eq_of_lt hk (by omega))
      have hp2 : ix hk (3 * (r - 1) + 1 + 2) = ⟨0, hk⟩ :=
        (ix_mod_eq hk (by rw [show 3 * (r - 1) + 1 + 2 = k by omega, Nat.mod_self, Nat.zero_mod])).trans (ix_eq_of_lt hk hk)
      rw [hn, Bool.true_and, hp1, hp2]
    have hm : xorFin (fun j : Fin (r - 2) => decide (⟨3 * (j.val + 1) + 1, by omega⟩ ∈ neededSet r k) &&
        (!(t (ix hk (3 * (j.val + 1) + 1 + 1))) && t (ix hk (3 * (j.val + 1) + 1 + 2)))) = false := by
      apply xorFin_eq_false; intro j
      rw [neededSet_c1 hr hk3 ⟨j.val + 1, by omega⟩]
      have hn : ¬(j.val + 1 = 0 ∨ j.val + 1 = r - 1) := by omega
      rw [decide_eq_false hn, Bool.false_and]
    rw [h0, hl, hm]; simp

  have hc2 : xorFin (fun j : Fin r => decide (⟨3 * j.val + 2, by omega⟩ ∈ neededSet r k) &&
      (!(t (ix hk (3 * j.val + 2 + 1))) && t (ix hk (3 * j.val + 2 + 2)))) =
    xor (t ⟨4, by omega⟩)
      (xor (xorFin (fun j : Fin (r - 2) =>
          !(t ⟨3 * (j.val + 2), by omega⟩) && t ⟨3 * (j.val + 2) + 1, by omega⟩))
        (if r % 2 = 0 then !(t ⟨0, hk⟩) && t ⟨1, by omega⟩ else false)) := by
    rw [xorFin_ends hr]; dsimp only
    have h0 : (decide (⟨3 * 0 + 2, by omega⟩ ∈ neededSet r k) &&
        (!(t (ix hk (3 * 0 + 2 + 1))) && t (ix hk (3 * 0 + 2 + 2)))) = t ⟨4, by omega⟩ := by
      have hn := neededSet_c2 hr hk3 ⟨0, by omega⟩
      dsimp only at hn; rw [ite_neg (by omega)] at hn
      rw [hn, Bool.true_and, ix_eq_of_lt hk (by omega : 3 * 0 + 2 + 1 < k),
        ix_eq_of_lt hk (by omega : 3 * 0 + 2 + 2 < k),
        show (⟨3 * 0 + 2 + 1, by omega⟩ : Fin k) = ⟨3, by omega⟩ from rfl, ht3]
      simp
    have hl : (decide (⟨3 * (r - 1) + 2, by omega⟩ ∈ neededSet r k) &&
        (!(t (ix hk (3 * (r - 1) + 2 + 1))) && t (ix hk (3 * (r - 1) + 2 + 2)))) =
        if r % 2 = 0 then !(t ⟨0, hk⟩) && t ⟨1, by omega⟩ else false := by
      have hn := neededSet_c2 hr hk3 ⟨r - 1, by omega⟩
      dsimp only at hn; rw [ite_pos rfl] at hn
      have hp1 : ix hk (3 * (r - 1) + 2 + 1) = ⟨0, hk⟩ :=
        (ix_mod_eq hk (by rw [show 3 * (r - 1) + 2 + 1 = k by omega, Nat.mod_self, Nat.zero_mod])).trans (ix_eq_of_lt hk hk)
      have hp2 : ix hk (3 * (r - 1) + 2 + 2) = ⟨1, by omega⟩ :=
        (ix_mod_eq hk (by rw [show 3 * (r - 1) + 2 + 2 = 1 + k by omega, Nat.add_mod_right])).trans (ix_eq_of_lt hk (by omega))
      rw [hn, hp1, hp2]; by_cases h : r % 2 = 0 <;> simp [h]
    have hm : xorFin (fun j : Fin (r - 2) => decide (⟨3 * (j.val + 1) + 2, by omega⟩ ∈ neededSet r k) &&
        (!(t (ix hk (3 * (j.val + 1) + 2 + 1))) && t (ix hk (3 * (j.val + 1) + 2 + 2)))) =
      xorFin (fun j : Fin (r - 2) =>
        !(t ⟨3 * (j.val + 2), by omega⟩) && t ⟨3 * (j.val + 2) + 1, by omega⟩) := by
      apply xorFin_congr; intro j
      have hn := neededSet_c2 hr hk3 ⟨j.val + 1, by omega⟩
      dsimp only at hn; rw [ite_neg (by omega)] at hn
      rw [hn, Bool.true_and, ix_eq_of_lt hk (by omega), ix_eq_of_lt hk (by omega)]
      exact congrArg₂ (fun a b => !a && b) (congrArg t (Fin.ext (by dsimp only; omega))) (congrArg t (Fin.ext (by dsimp only; omega)))
    rw [h0, hl, hm]
  dsimp only at hc0 hc1 hc2 ⊢
  rw [hc0, hc1, hc2]
  have hpair : xor (xorFin (fun j : Fin (r - 2) =>
        !(t ⟨3 * (j.val + 2) + 1, by omega⟩) && t ⟨3 * (j.val + 2) + 2, by omega⟩))
      (xorFin (fun j : Fin (r - 2) =>
        !(t ⟨3 * (j.val + 2), by omega⟩) && t ⟨3 * (j.val + 2) + 1, by omega⟩)) =
    xorFin (fun j : Fin (r - 2) =>
      xor (t ⟨3 * (j.val + 2) + 1, by omega⟩ &&
            !(xor (t ⟨3 * (j.val + 2), by omega⟩) (t ⟨3 * (j.val + 2) + 2, by omega⟩)))
          (t ⟨3 * (j.val + 2) + 2, by omega⟩)) := by
    rw [← xorFin_xor]; apply xorFin_congr; intro j
    cases t ⟨3 * (j.val + 2), by omega⟩ <;> cases t ⟨3 * (j.val + 2) + 1, by omega⟩ <;>
      cases t ⟨3 * (j.val + 2) + 2, by omega⟩ <;> rfl
  rw [← hpair]
  by_cases he : r % 2 = 0
  · simp only [he, ite_true]
    cases (!(t ⟨1, by omega⟩) && t ⟨2, by omega⟩) <;>
      cases (!(t ⟨0, hk⟩) && t ⟨1, by omega⟩) <;>
      cases (!(t ⟨4, by omega⟩) && t ⟨5, by omega⟩) <;>
      cases t ⟨4, by omega⟩ <;>
      cases (!(t ⟨k - 1, by omega⟩) && t ⟨0, hk⟩) <;>
      cases xorFin (fun j : Fin (r - 2) => !(t ⟨3 * (j.val + 2) + 1, by omega⟩) && t ⟨3 * (j.val + 2) + 2, by omega⟩) <;>
      cases xorFin (fun j : Fin (r - 2) => !(t ⟨3 * (j.val + 2), by omega⟩) && t ⟨3 * (j.val + 2) + 1, by omega⟩) <;> rfl
  · simp only [he, ite_false]
    cases (!(t ⟨4, by omega⟩) && t ⟨5, by omega⟩) <;>
      cases t ⟨4, by omega⟩ <;>
      cases (!(t ⟨k - 1, by omega⟩) && t ⟨0, hk⟩) <;>
      cases xorFin (fun j : Fin (r - 2) => !(t ⟨3 * (j.val + 2) + 1, by omega⟩) && t ⟨3 * (j.val + 2) + 2, by omega⟩) <;>
      cases xorFin (fun j : Fin (r - 2) => !(t ⟨3 * (j.val + 2), by omega⟩) && t ⟨3 * (j.val + 2) + 1, by omega⟩) <;> rfl

lemma Qp_r2 (hr2 : r = 2) (hk3 : k = 3 * r) (t : Fin k → Bool)
    (ht3 : t ⟨3, by omega⟩ = false)
    (hs01 : resSum r hk3 t 0 (by omega) = resSum r hk3 t 1 (by omega))
    (hs02 : resSum r hk3 t 0 (by omega) = resSum r hk3 t 2 (by omega)) :
    Qp hk r t = t ⟨0, hk⟩ := by
  subst hr2; subst hk3
  rw [Qp_eq_QpMid hk (by omega) rfl t ht3]
  unfold resSum at hs01 hs02
  have hfr2 : ∀ g : Fin 2 → Bool, xorFin g = xor (g ⟨0, by omega⟩) (g ⟨1, by omega⟩) := by
    intro g; unfold xorFin; have : List.finRange 2 = [0, 1] := rfl; rw [this]; simp
  rw [hfr2, hfr2] at hs01 hs02
  dsimp only at hs01 hs02
  rw [ht3, Bool.xor_false] at hs01 hs02
  change t ⟨0, hk⟩ = xor (t ⟨1, by omega⟩) (t ⟨4, by omega⟩) at hs01
  change t ⟨0, hk⟩ = xor (t ⟨2, by omega⟩) (t ⟨5, by omega⟩) at hs02
  unfold Q0 Qk QpMid
  have h0 : ∀ f : Fin (2 - 2) → Bool, xorFin f = false := fun _ => rfl
  rw [h0]
  have heven : (if 2 % 2 = 0 then xor (!(t ⟨1, by omega⟩) && t ⟨2, by omega⟩) (!(t ⟨0, hk⟩) && t ⟨1, by omega⟩) else false) =
      xor (!(t ⟨1, by omega⟩) && t ⟨2, by omega⟩) (!(t ⟨0, hk⟩) && t ⟨1, by omega⟩) := rfl
  rw [heven]
  cases h0' : t ⟨0, hk⟩ <;> cases h1' : t ⟨1, by omega⟩ <;> cases h2' : t ⟨2, by omega⟩ <;>
    cases h4' : t ⟨4, by omega⟩ <;> cases h5' : t ⟨5, by omega⟩ <;>
    rw [h0', h1', h4'] at hs01 <;> rw [h0', h2', h5'] at hs02 <;>
    cases hs01 <;> cases hs02 <;> rfl

lemma Qp_r3 (hr3 : r = 3) (hk3 : k = 3 * r) (t : Fin k → Bool)
    (ht3 : t ⟨3, by omega⟩ = false)
    (hs01 : resSum r hk3 t 0 (by omega) = resSum r hk3 t 1 (by omega))
    (hs02 : resSum r hk3 t 0 (by omega) = resSum r hk3 t 2 (by omega)) :
    Qp hk r t =
      xor (Q0 (by omega : 2 ≤ r) hk3 t)
        (xor ((xor (t ⟨5, by omega⟩) (xor (t ⟨6, by omega⟩) (t ⟨7, by omega⟩))) &&
              (xor (t ⟨0, hk⟩) (xor (t ⟨4, by omega⟩) (t ⟨7, by omega⟩))))
          (xor ((xor (t ⟨4, by omega⟩) (t ⟨6, by omega⟩)) &&
                (xor (t ⟨2, by omega⟩) (xor (t ⟨6, by omega⟩) (t ⟨7, by omega⟩))))
            (xor (t ⟨0, hk⟩) (t ⟨4, by omega⟩)))) := by
  subst hr3; subst hk3
  rw [Qp_eq_QpMid hk (by omega) rfl t ht3]
  unfold resSum at hs01 hs02
  have hfr3 : ∀ g : Fin 3 → Bool, xorFin g = xor (g ⟨0, by omega⟩) (xor (g ⟨1, by omega⟩) (g ⟨2, by omega⟩)) := by
    intro g; unfold xorFin; have : List.finRange 3 = [0, 1, 2] := rfl; rw [this]; simp
  rw [hfr3, hfr3] at hs01 hs02
  dsimp only at hs01 hs02
  rw [ht3, Bool.false_xor] at hs01 hs02
  change xor (t ⟨0, hk⟩) (t ⟨6, by omega⟩) = xor (t ⟨1, by omega⟩) (xor (t ⟨4, by omega⟩) (t ⟨7, by omega⟩)) at hs01
  change xor (t ⟨0, hk⟩) (t ⟨6, by omega⟩) = xor (t ⟨2, by omega⟩) (xor (t ⟨5, by omega⟩) (t ⟨8, by omega⟩)) at hs02
  unfold Q0 QpMid
  have hfr1 : ∀ g : Fin 1 → Bool, xorFin g = g ⟨0, by omega⟩ := by
    intro g; unfold xorFin; have : List.finRange 1 = [0] := rfl; rw [this]; simp
  rw [hfr1]
  have hodd : (if 3 % 2 = 0 then xor (!(t ⟨1, by omega⟩) && t ⟨2, by omega⟩) (Qk (by omega) rfl t) else false) = false := rfl
  rw [hodd, Bool.false_xor]
  dsimp only
  have ht1 : t ⟨1, by omega⟩ = xor (xor (t ⟨0, hk⟩) (t ⟨6, by omega⟩)) (xor (t ⟨4, by omega⟩) (t ⟨7, by omega⟩)) := by
    cases h0' : t ⟨0, hk⟩ <;> cases h1' : t ⟨1, by omega⟩ <;> cases h4' : t ⟨4, by omega⟩ <;>
      cases h6' : t ⟨6, by omega⟩ <;> cases h7' : t ⟨7, by omega⟩ <;>
      rw [h0', h1', h4', h6', h7'] at hs01 <;> cases hs01 <;> rfl
  have ht8 : t ⟨8, by omega⟩ = xor (xor (t ⟨0, hk⟩) (t ⟨6, by omega⟩)) (xor (t ⟨2, by omega⟩) (t ⟨5, by omega⟩)) := by
    cases h0' : t ⟨0, hk⟩ <;> cases h2' : t ⟨2, by omega⟩ <;> cases h5' : t ⟨5, by omega⟩ <;>
      cases h6' : t ⟨6, by omega⟩ <;> cases h8' : t ⟨8, by omega⟩ <;>
      rw [h0', h2', h5', h6', h8'] at hs02 <;> cases hs02 <;> rfl
  rw [ht1, ht8]
  cases t ⟨0, hk⟩ <;> cases t ⟨2, by omega⟩ <;> cases t ⟨4, by omega⟩ <;>
    cases t ⟨5, by omega⟩ <;> cases t ⟨6, by omega⟩ <;> cases t ⟨7, by omega⟩ <;> rfl

lemma isAffine_tWalk (j : Nat) : IsAffine (fun d : Fin k → Bool => tWalk d j) := by
  induction j with
  | zero => exact isAffine_const false
  | succ j ih =>
    cases j with
    | zero =>
      by_cases h : 2 < k
      · simpa [tWalk, h] using isAffine_coord (N := k) ⟨2, h⟩
      · simpa [tWalk, h] using isAffine_const (N := k) false
    | succ j =>
      have hterm : IsAffine (fun d : Fin k → Bool => if h : j + 3 < k then !(d ⟨j + 3, h⟩) else false) := by
        by_cases h : j + 3 < k
        · simpa [h] using isAffine_not (isAffine_coord (N := k) ⟨j + 3, h⟩)
        · simpa [h] using isAffine_const (N := k) false
      exact isAffine_xor ih hterm

lemma isAffine_tRaw (hr : 2 ≤ r) (hk3 : k = 3 * r) (i : Fin k) :
    IsAffine (fun d : Fin k → Bool => tRaw hr hk3 d i) := by
  unfold tRaw
  split_ifs
  · exact isAffine_not (isAffine_coord _)
  · exact isAffine_const false
  · exact isAffine_not (isAffine_coord _)
  · exact isAffine_tWalk (i.val - 3)

lemma isAffine_tOfD (hr : 2 ≤ r) (hk3 : k = 3 * r) (i : Fin k) :
    IsAffine (fun d : Fin k → Bool => tOfD hr hk3 d i) := by
  unfold tOfD
  split_ifs
  · exact isAffine_xor (isAffine_tRaw hr hk3 _)
      (isAffine_xorFin _ (fun j => isAffine_xor (isAffine_tRaw hr hk3 _) (isAffine_tRaw hr hk3 _)))
  · exact isAffine_tRaw hr hk3 i

lemma isAffine_zPair {N : Nat} (W : (Fin N → Bool) → Fin k → Bool)
    (Z0 Z1 : (Fin N → Bool) → Bool)
    (hW : ∀ i, IsAffine (fun y => W y i)) (hZ0 : IsAffine Z0) (hZ1 : IsAffine Z1) (j : Nat) :
    IsAffine (fun y => (zPair (W y) (Z0 y) (Z1 y) j).1) ∧
    IsAffine (fun y => (zPair (W y) (Z0 y) (Z1 y) j).2) := by
  induction j with
  | zero => exact ⟨hZ0, hZ1⟩
  | succ j ih =>
    refine ⟨ih.2, ?_⟩
    have hwj : IsAffine (fun y => if h : j + 1 < k then W y ⟨j + 1, h⟩ else false) := by
      by_cases h : j + 1 < k
      · simpa [h] using hW ⟨j + 1, h⟩
      · simpa [h] using isAffine_const false
    exact isAffine_xor ih.1 (isAffine_xor ih.2 hwj)

lemma isAffine_zOf {N : Nat} (W : (Fin N → Bool) → Fin k → Bool)
    (Z0 Z1 : (Fin N → Bool) → Bool)
    (hW : ∀ i, IsAffine (fun y => W y i)) (hZ0 : IsAffine Z0) (hZ1 : IsAffine Z1) (i : Fin k) :
    IsAffine (fun y => zOf (W y) (Z0 y) (Z1 y) i) :=
  (isAffine_zPair W Z0 Z1 hW hZ0 hZ1 i.val).1

lemma isAffine_linP {N : Nat} (u : Fin k → Bool) (T : (Fin N → Bool) → Fin k → Bool)
    (hT : ∀ i, IsAffine (fun y => T y i)) :
    IsAffine (fun y => linP hk r u (T y)) := by
  unfold linP
  apply isAffine_xorFin; intro i
  apply isAffine_and_const
  exact isAffine_xor (hT i) (isAffine_xor
    (isAffine_zOf T (fun _ => false) (fun _ => false) hT (isAffine_const false) (isAffine_const false) _)
    (isAffine_const _))

end RowAlg

lemma xorFin_add_split {N M : Nat} (g : Fin (N + M) → Bool) :
    xorFin g = xor (xorFin (fun i : Fin N => g ⟨i.val, by omega⟩))
                   (xorFin (fun j : Fin M => g ⟨N + j.val, by omega⟩)) := by
  induction M with
  | zero =>
    simp only [Nat.add_zero]
    have h0 : xorFin (fun j : Fin 0 => g ⟨N + j.val, by omega⟩) = false := rfl
    rw [h0, Bool.xor_false]
    exact xorFin_congr _ _ (fun _ => rfl)
  | succ M ih =>
    rw [xorFin_succ (fun j : Fin (M + 1) => g ⟨N + j.val, by omega⟩)]
    have hgoal := xorFin_succ (fun x : Fin (N + M + 1) => g ⟨x.val, by omega⟩)
    have hcast : xorFin g = xorFin (fun x : Fin (N + M + 1) => g ⟨x.val, by omega⟩) :=
      xorFin_congr _ _ (fun _ => rfl)
    rw [hcast, hgoal]
    have hih := ih (fun x : Fin (N + M) => g ⟨x.val, by omega⟩)
    have hcs : xorFin (fun i : Fin (N + M) => g ⟨i.castSucc.val, by omega⟩) =
        xorFin (fun i : Fin (N + M) => g ⟨i.val, by omega⟩) :=
      xorFin_congr _ _ (fun _ => rfl)
    rw [hcs, hih]
    simp only [Fin.last, Bool.xor_assoc]
    rfl

lemma flatten_ofFn_length {n L : Nat} (f : Fin n → List Bool) (hlen : ∀ j, (f j).length = L) :
    (List.ofFn f).flatten.length = n * L := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, hlen 0,
      ih (fun j => f j.succ) (fun j => hlen j.succ), Nat.succ_mul, Nat.add_comm]

lemma flatten_ofFn_getD {n L : Nat} (f : Fin n → List Bool) (hlen : ∀ j, (f j).length = L)
    (j : Fin n) (p : Fin L) :
    (List.ofFn f).flatten.getD (j.val * L + p.val) false = (f j).getD p.val false := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    rw [List.ofFn_succ, List.flatten_cons]
    cases j using Fin.cases with
    | zero =>
      simp only [Fin.val_zero, Nat.zero_mul, Nat.zero_add]
      have hlt : p.val < (f 0).length := by rw [hlen 0]; exact p.isLt
      rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
        List.getElem_append_left hlt, List.getD_eq_getElem _ _ hlt]
    | succ j' =>
      simp only [Fin.val_succ]
      have hidx : (j'.val + 1) * L + p.val = (f 0).length + (j'.val * L + p.val) := by
        rw [hlen 0, Nat.succ_mul]; omega
      have hlt2 : j'.val * L + p.val < (List.ofFn (fun i : Fin n => f i.succ)).flatten.length := by
        rw [flatten_ofFn_length _ (fun i => hlen i.succ)]
        have : (j'.val + 1) * L ≤ n * L := Nat.mul_le_mul_right L j'.isLt
        rw [Nat.succ_mul] at this; omega
      rw [hidx, List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
        List.getElem_append_right (Nat.le_add_right _ _)]
      simp only [Nat.add_sub_cancel_left]
      rw [← List.getD_eq_getElem _ _ hlt2]
      exact ih (fun i => f i.succ) (fun i => hlen i.succ) j'

def recordFn {k : Nat} (hk : 0 < k) (r : Nat) (u x : Fin k → Bool) : List Bool :=
  List.ofFn (diffFn hk u x) ++
    [decide (((neededSet r k).filter (fun i => row hk u x i = true)).card % 2 = 1),
     row hk u x (ix hk 0), row hk u x (ix hk (k - 1))]

lemma recordFn_length {k : Nat} (hk : 0 < k) (r : Nat) (u x : Fin k → Bool) :
    (recordFn hk r u x).length = k + 3 := by
  simp [recordFn]

lemma recordFn_getD_lt {k : Nat} (hk : 0 < k) (r : Nat) (u x : Fin k → Bool)
    (p : Nat) (hp : p < k) :
    (recordFn hk r u x).getD p false = diffFn hk u x ⟨p, hp⟩ := by
  unfold recordFn
  have hl : (List.ofFn (diffFn hk u x)).length = k := List.length_ofFn
  rw [List.getD_eq_getElem _ _ (by rw [List.length_append, hl]; simp; omega),
    List.getElem_append_left (by omega), List.getElem_ofFn]

lemma recordFn_getD_k {k : Nat} (hk : 0 < k) (r : Nat) (u x : Fin k → Bool) :
    (recordFn hk r u x).getD k false =
      decide (((neededSet r k).filter (fun i => row hk u x i = true)).card % 2 = 1) := by
  unfold recordFn
  have hl : (List.ofFn (diffFn hk u x)).length = k := List.length_ofFn
  rw [List.getD_eq_getElem _ _ (by rw [List.length_append, hl]; simp),
    List.getElem_append_right (by omega)]
  simp [hl]

lemma recordFn_getD_k1 {k : Nat} (hk : 0 < k) (r : Nat) (u x : Fin k → Bool) :
    (recordFn hk r u x).getD (k + 1) false = row hk u x ⟨0, hk⟩ := by
  unfold recordFn
  have hl : (List.ofFn (diffFn hk u x)).length = k := List.length_ofFn
  rw [List.getD_eq_getElem _ _ (by rw [List.length_append, hl]; simp),
    List.getElem_append_right (by omega)]
  simp only [hl, Nat.add_sub_cancel_left, List.getElem_cons_succ, List.getElem_cons_zero]
  rw [ix_eq_of_lt hk hk]

lemma recordFn_getD_k2 {k : Nat} (hk : 0 < k) (r : Nat) (u x : Fin k → Bool) :
    (recordFn hk r u x).getD (k + 2) false = row hk u x ⟨k - 1, by omega⟩ := by
  unfold recordFn
  have hl : (List.ofFn (diffFn hk u x)).length = k := List.length_ofFn
  rw [List.getD_eq_getElem _ _ (by rw [List.length_append, hl]; simp),
    List.getElem_append_right (by omega)]
  simp only [hl, Nat.add_sub_cancel_left, List.getElem_cons_succ, List.getElem_cons_zero]
  rw [ix_eq_of_lt hk (by omega)]

def wOfY {r k : Nat} (hr : 2 ≤ r) (hk3 : k = 3 * r) (y : Fin (k - 3) → Bool) (i : Fin k) : Bool :=
  if i.val = 0 then y ⟨0, by omega⟩
  else if i.val = 1 then
    xor (y ⟨0, by omega⟩) (xor (y ⟨2, by omega⟩)
      (xorFin (fun j : Fin (r - 2) => xor (y ⟨3 * j.val + 4, by omega⟩) (y ⟨3 * j.val + 5, by omega⟩))))
  else if i.val = 2 then y ⟨1, by omega⟩
  else if i.val = 3 then false
  else if hi : i.val < k - 1 then y ⟨i.val - 2, by omega⟩
  else
    xor (y ⟨0, by omega⟩) (xor (y ⟨1, by omega⟩)
      (xorFin (fun j : Fin (r - 2) => xor (y ⟨3 * j.val + 4, by omega⟩) (y ⟨3 * j.val + 3, by omega⟩))))

lemma wOfY_zero {r k : Nat} (hr : 2 ≤ r) (hk3 : k = 3 * r) (i : Fin k) :
    wOfY hr hk3 (fun _ => false) i = false := by
  unfold wOfY
  split_ifs <;> simp [xorFin_false]

lemma wOfY_xor {r k : Nat} (hr : 2 ≤ r) (hk3 : k = 3 * r) (a b : Fin (k - 3) → Bool) (i : Fin k) :
    wOfY hr hk3 (fun p => xor (a p) (b p)) i = xor (wOfY hr hk3 a i) (wOfY hr hk3 b i) := by
  unfold wOfY
  split_ifs
  · rfl
  · dsimp only
    have hx : xorFin (fun j : Fin (r - 2) =>
        xor (xor (a ⟨3 * j.val + 4, by omega⟩) (b ⟨3 * j.val + 4, by omega⟩))
            (xor (a ⟨3 * j.val + 5, by omega⟩) (b ⟨3 * j.val + 5, by omega⟩))) =
      xor (xorFin (fun j : Fin (r - 2) => xor (a ⟨3 * j.val + 4, by omega⟩) (a ⟨3 * j.val + 5, by omega⟩)))
          (xorFin (fun j : Fin (r - 2) => xor (b ⟨3 * j.val + 4, by omega⟩) (b ⟨3 * j.val + 5, by omega⟩))) := by
      rw [← xorFin_xor]; apply xorFin_congr; intro j
      cases a ⟨3 * j.val + 4, by omega⟩ <;> cases b ⟨3 * j.val + 4, by omega⟩ <;>
        cases a ⟨3 * j.val + 5, by omega⟩ <;> cases b ⟨3 * j.val + 5, by omega⟩ <;> rfl
    rw [hx]
    cases a ⟨0, by omega⟩ <;> cases b ⟨0, by omega⟩ <;>
      cases a ⟨2, by omega⟩ <;> cases b ⟨2, by omega⟩ <;>
      cases xorFin (fun j : Fin (r - 2) => xor (a ⟨3 * j.val + 4, by omega⟩) (a ⟨3 * j.val + 5, by omega⟩)) <;>
      cases xorFin (fun j : Fin (r - 2) => xor (b ⟨3 * j.val + 4, by omega⟩) (b ⟨3 * j.val + 5, by omega⟩)) <;> rfl
  · rfl
  · rfl
  · rfl
  · dsimp only
    have hx : xorFin (fun j : Fin (r - 2) =>
        xor (xor (a ⟨3 * j.val + 4, by omega⟩) (b ⟨3 * j.val + 4, by omega⟩))
            (xor (a ⟨3 * j.val + 3, by omega⟩) (b ⟨3 * j.val + 3, by omega⟩))) =
      xor (xorFin (fun j : Fin (r - 2) => xor (a ⟨3 * j.val + 4, by omega⟩) (a ⟨3 * j.val + 3, by omega⟩)))
          (xorFin (fun j : Fin (r - 2) => xor (b ⟨3 * j.val + 4, by omega⟩) (b ⟨3 * j.val + 3, by omega⟩))) := by
      rw [← xorFin_xor]; apply xorFin_congr; intro j
      cases a ⟨3 * j.val + 4, by omega⟩ <;> cases b ⟨3 * j.val + 4, by omega⟩ <;>
        cases a ⟨3 * j.val + 3, by omega⟩ <;> cases b ⟨3 * j.val + 3, by omega⟩ <;> rfl
    rw [hx]
    cases a ⟨0, by omega⟩ <;> cases b ⟨0, by omega⟩ <;>
      cases a ⟨1, by omega⟩ <;> cases b ⟨1, by omega⟩ <;>
      cases xorFin (fun j : Fin (r - 2) => xor (a ⟨3 * j.val + 4, by omega⟩) (a ⟨3 * j.val + 3, by omega⟩)) <;>
      cases xorFin (fun j : Fin (r - 2) => xor (b ⟨3 * j.val + 4, by omega⟩) (b ⟨3 * j.val + 3, by omega⟩)) <;> rfl

lemma isAffine_wOfY {r k : Nat} (hr : 2 ≤ r) (hk3 : k = 3 * r) (i : Fin k) :
    IsAffine (fun y : Fin (k - 3) → Bool => wOfY hr hk3 y i) := by
  unfold wOfY
  split_ifs
  · exact isAffine_coord _
  · exact isAffine_xor (isAffine_coord _) (isAffine_xor (isAffine_coord _)
      (isAffine_xorFin _ (fun j => isAffine_xor (isAffine_coord _) (isAffine_coord _))))
  · exact isAffine_coord _
  · exact isAffine_const false
  · exact isAffine_coord _
  · exact isAffine_xor (isAffine_coord _) (isAffine_xor (isAffine_coord _)
      (isAffine_xorFin _ (fun j => isAffine_xor (isAffine_coord _) (isAffine_coord _))))

lemma wOfY_3 {r k : Nat} (hr : 2 ≤ r) (hk3 : k = 3 * r) (y : Fin (k - 3) → Bool) :
    wOfY hr hk3 y ⟨3, by omega⟩ = false := by
  unfold wOfY; simp

lemma wOfY_resSum {r k : Nat} (hr : 2 ≤ r) (hk3 : k = 3 * r) (y : Fin (k - 3) → Bool) :
    resSum r hk3 (wOfY hr hk3 y) 0 (by omega) = resSum r hk3 (wOfY hr hk3 y) 1 (by omega) ∧
    resSum r hk3 (wOfY hr hk3 y) 0 (by omega) = resSum r hk3 (wOfY hr hk3 y) 2 (by omega) := by
  have hs0 : resSum r hk3 (wOfY hr hk3 y) 0 (by omega) =
      xor (y ⟨0, by omega⟩) (xorFin (fun j : Fin (r - 2) => y ⟨3 * j.val + 4, by omega⟩)) := by
    unfold resSum
    rw [xorFin_first (by omega), xorFin_first (by omega)]; dsimp only
    have h0 : wOfY hr hk3 y ⟨3 * 0 + 0, by omega⟩ = y ⟨0, by omega⟩ := by unfold wOfY; simp
    have h3 : wOfY hr hk3 y ⟨3 * (0 + 1) + 0, by omega⟩ = false := by unfold wOfY; simp
    have hrest : xorFin (fun j : Fin (r - 1 - 1) => wOfY hr hk3 y ⟨3 * (j.val + 1 + 1) + 0, by omega⟩) =
        xorFin (fun j : Fin (r - 2) => y ⟨3 * j.val + 4, by omega⟩) := by
      refine xorFin_cast (by omega) _ _ (fun idx hi1 hi2 => ?_)
      unfold wOfY; dsimp only
      rw [ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_neg (by omega),
        dite_pos (by omega)]
      exact congrArg y (Fin.ext (by dsimp only; omega))
    rw [h0, h3, hrest, Bool.false_xor]
  have hs1 : resSum r hk3 (wOfY hr hk3 y) 1 (by omega) =
      xor (y ⟨0, by omega⟩) (xorFin (fun j : Fin (r - 2) => y ⟨3 * j.val + 4, by omega⟩)) := by
    unfold resSum
    rw [xorFin_first (by omega), xorFin_first (by omega)]; dsimp only
    have h1 : wOfY hr hk3 y ⟨3 * 0 + 1, by omega⟩ =
        xor (y ⟨0, by omega⟩) (xor (y ⟨2, by omega⟩)
          (xorFin (fun j : Fin (r - 2) => xor (y ⟨3 * j.val + 4, by omega⟩) (y ⟨3 * j.val + 5, by omega⟩)))) := by
      unfold wOfY; simp
    have h4 : wOfY hr hk3 y ⟨3 * (0 + 1) + 1, by omega⟩ = y ⟨2, by omega⟩ := by
      unfold wOfY; dsimp only
      rw [ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_neg (by omega),
        dite_pos (by omega)]
    have hrest : xorFin (fun j : Fin (r - 1 - 1) => wOfY hr hk3 y ⟨3 * (j.val + 1 + 1) + 1, by omega⟩) =
        xorFin (fun j : Fin (r - 2) => y ⟨3 * j.val + 5, by omega⟩) := by
      refine xorFin_cast (by omega) _ _ (fun idx hi1 hi2 => ?_)
      unfold wOfY; dsimp only
      rw [ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_neg (by omega),
        dite_pos (by omega)]
      exact congrArg y (Fin.ext (by dsimp only; omega))
    rw [h1, h4, hrest, xorFin_xor]
    cases y ⟨0, by omega⟩ <;> cases y ⟨2, by omega⟩ <;>
      cases xorFin (fun j : Fin (r - 2) => y ⟨3 * j.val + 4, by omega⟩) <;>
      cases xorFin (fun j : Fin (r - 2) => y ⟨3 * j.val + 5, by omega⟩) <;> rfl
  have hs2 : resSum r hk3 (wOfY hr hk3 y) 2 (by omega) =
      xor (y ⟨0, by omega⟩) (xorFin (fun j : Fin (r - 2) => y ⟨3 * j.val + 4, by omega⟩)) := by
    unfold resSum
    rw [xorFin_ends hr]; dsimp only
    have h2 : wOfY hr hk3 y ⟨3 * 0 + 2, by omega⟩ = y ⟨1, by omega⟩ := by unfold wOfY; simp
    have hlast : wOfY hr hk3 y ⟨3 * (r - 1) + 2, by omega⟩ =
        xor (y ⟨0, by omega⟩) (xor (y ⟨1, by omega⟩)
          (xorFin (fun j : Fin (r - 2) => xor (y ⟨3 * j.val + 4, by omega⟩) (y ⟨3 * j.val + 3, by omega⟩)))) := by
      unfold wOfY; dsimp only
      rw [ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_neg (by omega),
        dite_neg (by omega)]
    have hmid : xorFin (fun j : Fin (r - 2) => wOfY hr hk3 y ⟨3 * (j.val + 1) + 2, by omega⟩) =
        xorFin (fun j : Fin (r - 2) => y ⟨3 * j.val + 3, by omega⟩) := by
      apply xorFin_congr; intro j
      unfold wOfY; dsimp only
      rw [ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_neg (by omega),
        dite_pos (by omega)]
      exact congrArg y (Fin.ext (by dsimp only; omega))
    rw [h2, hlast, hmid, xorFin_xor]
    cases y ⟨0, by omega⟩ <;> cases y ⟨1, by omega⟩ <;>
      cases xorFin (fun j : Fin (r - 2) => y ⟨3 * j.val + 4, by omega⟩) <;>
      cases xorFin (fun j : Fin (r - 2) => y ⟨3 * j.val + 3, by omega⟩) <;> rfl
  rw [hs0, hs1, hs2]; exact ⟨rfl, rfl⟩

def Bpair {N : Nat} (f g : (Fin N → Bool) → Bool) (a b : Fin N → Bool) : Bool :=
  xor (f a && g b) (f b && g a)

lemma pol_and_lin {N : Nat} (f g : (Fin N → Bool) → Bool)
    (hf : ∀ a b, f (fun i => xor (a i) (b i)) = xor (f a) (f b)) (hf0 : f (fun _ => false) = false)
    (hg : ∀ a b, g (fun i => xor (a i) (b i)) = xor (g a) (g b)) (hg0 : g (fun _ => false) = false)
    (a b : Fin N → Bool) :
    pol (fun y => f y && g y) a b = Bpair f g a b := by
  unfold pol Bpair; dsimp only
  rw [hf, hg, hf0, hg0]
  cases f a <;> cases f b <;> cases g a <;> cases g b <;> rfl

lemma pol_not_and_lin {N : Nat} (f g : (Fin N → Bool) → Bool)
    (hf : ∀ a b, f (fun i => xor (a i) (b i)) = xor (f a) (f b)) (hf0 : f (fun _ => false) = false)
    (hg : ∀ a b, g (fun i => xor (a i) (b i)) = xor (g a) (g b)) (hg0 : g (fun _ => false) = false)
    (a b : Fin N → Bool) :
    pol (fun y => !(f y) && g y) a b = Bpair f g a b := by
  unfold pol Bpair; dsimp only
  rw [hf, hg, hf0, hg0]
  cases f a <;> cases f b <;> cases g a <;> cases g b <;> rfl

lemma pol_and_not_lin {N : Nat} (f g : (Fin N → Bool) → Bool)
    (hf : ∀ a b, f (fun i => xor (a i) (b i)) = xor (f a) (f b)) (hf0 : f (fun _ => false) = false)
    (hg : ∀ a b, g (fun i => xor (a i) (b i)) = xor (g a) (g b)) (hg0 : g (fun _ => false) = false)
    (a b : Fin N → Bool) :
    pol (fun y => f y && !(g y)) a b = Bpair f g a b := by
  unfold pol Bpair; dsimp only
  rw [hf, hg, hf0, hg0]
  cases f a <;> cases f b <;> cases g a <;> cases g b <;> rfl

lemma pol_xorFin {N m : Nat} (F : Fin m → (Fin N → Bool) → Bool) (a b : Fin N → Bool) :
    pol (fun y => xorFin (fun i => F i y)) a b = xorFin (fun i => pol (F i) a b) := by
  induction m with
  | zero => exact pol_const false a b
  | succ m ih =>
    have heq : (fun y => xorFin (fun i : Fin (m + 1) => F i y)) =
        (fun y => xor (xorFin (fun i : Fin m => F i.castSucc y)) (F (Fin.last m) y)) := by
      funext y; exact xorFin_succ (fun i => F i y)
    rw [heq, pol_xor, ih (fun i => F i.castSucc), xorFin_succ]

def w1Bit (p : Nat) : Bool := decide (p = 0 ∨ p = 2 ∨ (4 ≤ p ∧ p % 3 ≠ 0))
def wk1Bit (m p : Nat) : Bool := decide (p = 0 ∨ p = 1 ∨ (3 ≤ p ∧ p < m - 1 ∧ p % 3 ≠ 2))
def dTermBit (r m j q : Nat) : Bool :=
  xor (decide (q = 3 * j + 4)) (if j + 1 = r - 2 then wk1Bit m q else decide (q = 3 * j + 6))
def BmBit (r m p q : Nat) : Bool :=
  xor (xor (decide (p = 2) && decide (q = 3)) (decide (q = 2) && decide (p = 3)))
    (xor (xor (wk1Bit m p && decide (q = 0)) (wk1Bit m q && decide (p = 0)))
      (xor (if 5 ≤ p ∧ p % 3 = 2 then dTermBit r m ((p - 5) / 3) q else false)
           (if 5 ≤ q ∧ q % 3 = 2 then dTermBit r m ((q - 5) / 3) p else false)))
def B0Bit (p q : Nat) : Bool :=
  xor (w1Bit p && decide (q = 1)) (w1Bit q && decide (p = 1))
def BkBit (p q : Nat) : Bool :=
  xor (decide (p = 0) && w1Bit q) (decide (q = 0) && w1Bit p)
def CBit (r m : Nat) (a0 b0 : Bool) (p q : Nat) : Bool :=
  xor (BmBit r m p q) (xor (a0 && B0Bit p q) (b0 && BkBit p q))

lemma CBit_symm (r m : Nat) (a0 b0 : Bool) (p q : Nat) :
    CBit r m a0 b0 p q = CBit r m a0 b0 q p := by
  unfold CBit BmBit B0Bit BkBit
  cases (decide (p = 2) && decide (q = 3)) <;> cases (decide (q = 2) && decide (p = 3)) <;>
    cases (wk1Bit m p && decide (q = 0)) <;> cases (wk1Bit m q && decide (p = 0)) <;>
    cases (if 5 ≤ p ∧ p % 3 = 2 then dTermBit r m ((p - 5) / 3) q else false) <;>
    cases (if 5 ≤ q ∧ q % 3 = 2 then dTermBit r m ((q - 5) / 3) p else false) <;>
    cases a0 <;> cases b0 <;>
    cases (w1Bit p && decide (q = 1)) <;> cases (w1Bit q && decide (p = 1)) <;>
    cases (decide (p = 0) && w1Bit q) <;> cases (decide (q = 0) && w1Bit p) <;> rfl

lemma wOfY_eVec_0 {r k : Nat} (hr : 2 ≤ r) (hk3 : k = 3 * r) (p : Fin (k - 3)) :
    wOfY hr hk3 (eVec p) ⟨0, by omega⟩ = decide (p.val = 0) := by
  unfold wOfY eVec; simp [Fin.ext_iff, eq_comm]

lemma decide_eq_decide_of_iff {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    decide P = decide Q := by
  by_cases hp : P
  · rw [decide_eq_true hp, decide_eq_true (h.mp hp)]
  · rw [decide_eq_false hp, decide_eq_false (fun hq => hp (h.mpr hq))]

lemma wOfY_eVec_2 {r k : Nat} (hr : 2 ≤ r) (hk3 : k = 3 * r) (p : Fin (k - 3)) :
    wOfY hr hk3 (eVec p) ⟨2, by omega⟩ = decide (p.val = 1) := by
  unfold wOfY eVec; simp [Fin.ext_iff, eq_comm]

lemma wOfY_eVec_mid {r k : Nat} (hr : 2 ≤ r) (hk3 : k = 3 * r) (p : Fin (k - 3))
    (i : Nat) (hi4 : 4 ≤ i) (hil : i < k - 1) :
    wOfY hr hk3 (eVec p) ⟨i, by omega⟩ = decide (p.val = i - 2) := by
  unfold wOfY eVec; dsimp only
  rw [ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), dite_pos hil]
  simp [Fin.ext_iff, eq_comm]

lemma wOfY_eVec_1 {r k : Nat} (hr : 2 ≤ r) (hk3 : k = 3 * r) (p : Fin (k - 3)) :
    wOfY hr hk3 (eVec p) ⟨1, by omega⟩ = w1Bit p.val := by
  unfold wOfY w1Bit eVec; dsimp only
  rw [ite_neg (by omega), ite_pos rfl]
  have hsum : xorFin (fun j : Fin (r - 2) =>
      xor (decide (⟨3 * j.val + 4, by omega⟩ = p)) (decide (⟨3 * j.val + 5, by omega⟩ = p))) =
      decide (4 ≤ p.val ∧ p.val % 3 ≠ 0) := by
    by_cases hp : 4 ≤ p.val ∧ p.val % 3 ≠ 0
    · rw [decide_eq_true hp]
      let j0 : Fin (r - 2) := ⟨(p.val - 4) / 3, by omega⟩
      rw [xorFin_single' j0]
      · by_cases hm : p.val % 3 = 1
        · have h1 : (⟨3 * j0.val + 4, by omega⟩ : Fin (k - 3)) = p := Fin.ext (by dsimp [j0]; omega)
          have h2 : (⟨3 * j0.val + 5, by omega⟩ : Fin (k - 3)) ≠ p := fun h => by
            have := congrArg Fin.val h; dsimp [j0] at this; omega
          simp [h1, h2]
        · have h1 : (⟨3 * j0.val + 4, by omega⟩ : Fin (k - 3)) ≠ p := fun h => by
            have := congrArg Fin.val h; dsimp [j0] at this; omega
          have h2 : (⟨3 * j0.val + 5, by omega⟩ : Fin (k - 3)) = p := Fin.ext (by dsimp [j0]; omega)
          simp [h1, h2]
      · intro j hj
        have hne1 : (⟨3 * j.val + 4, by omega⟩ : Fin (k - 3)) ≠ p := fun h => by
          have hv := congrArg Fin.val h; dsimp only at hv
          exact hj (Fin.ext (by dsimp [j0]; omega))
        have hne2 : (⟨3 * j.val + 5, by omega⟩ : Fin (k - 3)) ≠ p := fun h => by
          have hv := congrArg Fin.val h; dsimp only at hv
          exact hj (Fin.ext (by dsimp [j0]; omega))
        simp [hne1, hne2]
    · rw [decide_eq_false hp]
      apply xorFin_eq_false; intro j
      have hne1 : (⟨3 * j.val + 4, by omega⟩ : Fin (k - 3)) ≠ p := fun h => by
        have hv := congrArg Fin.val h; dsimp only at hv; omega
      have hne2 : (⟨3 * j.val + 5, by omega⟩ : Fin (k - 3)) ≠ p := fun h => by
        have hv := congrArg Fin.val h; dsimp only at hv; omega
      simp [hne1, hne2]
  rw [hsum]
  have h0 : decide (⟨0, by omega⟩ = p) = decide (p.val = 0) := by simp [Fin.ext_iff, eq_comm]
  have h2 : decide (⟨2, by omega⟩ = p) = decide (p.val = 2) := by simp [Fin.ext_iff, eq_comm]
  rw [h0, h2]
  by_cases hp0 : p.val = 0
  · simp [hp0]
  · by_cases hp2 : p.val = 2
    · simp [hp2]
    · by_cases hpm : 4 ≤ p.val ∧ p.val % 3 ≠ 0
      · simp [hp0, hp2, hpm]
      · simp [hp0, hp2, hpm]

lemma wOfY_eVec_k1 {r k : Nat} (hr : 2 ≤ r) (hk3 : k = 3 * r) (p : Fin (k - 3)) :
    wOfY hr hk3 (eVec p) ⟨k - 1, by omega⟩ = wk1Bit (k - 3) p.val := by
  unfold wOfY wk1Bit eVec; dsimp only
  rw [ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), dite_neg (by omega)]
  have hsum : xorFin (fun j : Fin (r - 2) =>
      xor (decide (⟨3 * j.val + 4, by omega⟩ = p)) (decide (⟨3 * j.val + 3, by omega⟩ = p))) =
      decide (3 ≤ p.val ∧ p.val < k - 3 - 1 ∧ p.val % 3 ≠ 2) := by
    by_cases hp : 3 ≤ p.val ∧ p.val < k - 3 - 1 ∧ p.val % 3 ≠ 2
    · rw [decide_eq_true hp]
      let j0 : Fin (r - 2) := ⟨(p.val - 3) / 3, by omega⟩
      rw [xorFin_single' j0]
      · by_cases hm : p.val % 3 = 0
        · have h1 : (⟨3 * j0.val + 4, by omega⟩ : Fin (k - 3)) ≠ p := fun h => by
            have := congrArg Fin.val h; dsimp [j0] at this; omega
          have h2 : (⟨3 * j0.val + 3, by omega⟩ : Fin (k - 3)) = p := Fin.ext (by dsimp [j0]; omega)
          simp [h1, h2]
        · have h1 : (⟨3 * j0.val + 4, by omega⟩ : Fin (k - 3)) = p := Fin.ext (by dsimp [j0]; omega)
          have h2 : (⟨3 * j0.val + 3, by omega⟩ : Fin (k - 3)) ≠ p := fun h => by
            have := congrArg Fin.val h; dsimp [j0] at this; omega
          simp [h1, h2]
      · intro j hj
        have hne1 : (⟨3 * j.val + 4, by omega⟩ : Fin (k - 3)) ≠ p := fun h => by
          have hv := congrArg Fin.val h; dsimp only at hv
          exact hj (Fin.ext (by dsimp [j0]; omega))
        have hne2 : (⟨3 * j.val + 3, by omega⟩ : Fin (k - 3)) ≠ p := fun h => by
          have hv := congrArg Fin.val h; dsimp only at hv
          exact hj (Fin.ext (by dsimp [j0]; omega))
        simp [hne1, hne2]
    · rw [decide_eq_false hp]
      apply xorFin_eq_false; intro j
      have hne1 : (⟨3 * j.val + 4, by omega⟩ : Fin (k - 3)) ≠ p := fun h => by
        have hv := congrArg Fin.val h; dsimp only at hv; omega
      have hne2 : (⟨3 * j.val + 3, by omega⟩ : Fin (k - 3)) ≠ p := fun h => by
        have hv := congrArg Fin.val h; dsimp only at hv; omega
      simp [hne1, hne2]
  rw [hsum]
  have h0 : decide (⟨0, by omega⟩ = p) = decide (p.val = 0) := by simp [Fin.ext_iff, eq_comm]
  have h1 : decide (⟨1, by omega⟩ = p) = decide (p.val = 1) := by simp [Fin.ext_iff, eq_comm]
  rw [h0, h1]
  by_cases hp0 : p.val = 0
  · simp [hp0]
  · by_cases hp1 : p.val = 1
    · simp [hp1]
    · by_cases hpm : 3 ≤ p.val ∧ p.val < k - 3 - 1 ∧ p.val % 3 ≠ 2
      · simp [hp0, hp1, hpm]
      · simp [hp0, hp1, hpm]

lemma pol_Q0_eVec {r k : Nat} (hr : 2 ≤ r) (hk3 : k = 3 * r) (p q : Fin (k - 3)) :
    pol (fun y => Q0 hr hk3 (wOfY hr hk3 y)) (eVec p) (eVec q) = B0Bit p.val q.val := by
  unfold Q0 B0Bit
  rw [pol_not_and_lin (fun y => wOfY hr hk3 y ⟨1, by omega⟩) (fun y => wOfY hr hk3 y ⟨2, by omega⟩)
    (fun a b => wOfY_xor hr hk3 a b _) (wOfY_zero hr hk3 _)
    (fun a b => wOfY_xor hr hk3 a b _) (wOfY_zero hr hk3 _)]
  unfold Bpair; dsimp only
  rw [wOfY_eVec_1, wOfY_eVec_1, wOfY_eVec_2, wOfY_eVec_2]

lemma pol_Qk_eVec {r k : Nat} (hr : 2 ≤ r) (hk3 : k = 3 * r) (p q : Fin (k - 3)) :
    pol (fun y => Qk hr hk3 (wOfY hr hk3 y)) (eVec p) (eVec q) = BkBit p.val q.val := by
  unfold Qk BkBit
  rw [pol_not_and_lin (fun y => wOfY hr hk3 y ⟨0, by omega⟩) (fun y => wOfY hr hk3 y ⟨1, by omega⟩)
    (fun a b => wOfY_xor hr hk3 a b _) (wOfY_zero hr hk3 _)
    (fun a b => wOfY_xor hr hk3 a b _) (wOfY_zero hr hk3 _)]
  unfold Bpair; dsimp only
  rw [wOfY_eVec_0, wOfY_eVec_0, wOfY_eVec_1, wOfY_eVec_1]

lemma pol_QpMid_eVec {r k : Nat} (hk : 0 < k) (hr3 : 3 ≤ r) (hk3 : k = 3 * r) (p q : Fin (k - 3)) :
    pol (fun y => QpMid hk (by omega) hk3 (wOfY (by omega) hk3 y)) (eVec p) (eVec q) =
      BmBit r (k - 3) p.val q.val := by
  have hr : 2 ≤ r := by omega
  unfold QpMid BmBit
  rw [pol_xor, pol_xor, pol_xor, pol_xorFin]
  rw [pol_affine (isAffine_wOfY hr hk3 _), Bool.false_xor]
  rw [pol_not_and_lin (fun y => wOfY hr hk3 y ⟨4, by omega⟩) (fun y => wOfY hr hk3 y ⟨5, by omega⟩)
    (fun a b => wOfY_xor hr hk3 a b _) (wOfY_zero hr hk3 _)
    (fun a b => wOfY_xor hr hk3 a b _) (wOfY_zero hr hk3 _)]
  rw [pol_not_and_lin (fun y => wOfY hr hk3 y ⟨k - 1, by omega⟩) (fun y => wOfY hr hk3 y ⟨0, hk⟩)
    (fun a b => wOfY_xor hr hk3 a b _) (wOfY_zero hr hk3 _)
    (fun a b => wOfY_xor hr hk3 a b _) (wOfY_zero hr hk3 _)]
  have h1 : Bpair (fun y => wOfY hr hk3 y ⟨4, by omega⟩) (fun y => wOfY hr hk3 y ⟨5, by omega⟩) (eVec p) (eVec q) =
      xor (decide (p.val = 2) && decide (q.val = 3)) (decide (q.val = 2) && decide (p.val = 3)) := by
    unfold Bpair; dsimp only
    rw [wOfY_eVec_mid hr hk3 p 4 (by omega) (by omega), wOfY_eVec_mid hr hk3 q 4 (by omega) (by omega),
      wOfY_eVec_mid hr hk3 p 5 (by omega) (by omega), wOfY_eVec_mid hr hk3 q 5 (by omega) (by omega)]
  have h2 : Bpair (fun y => wOfY hr hk3 y ⟨k - 1, by omega⟩) (fun y => wOfY hr hk3 y ⟨0, hk⟩) (eVec p) (eVec q) =
      xor (wk1Bit (k - 3) p.val && decide (q.val = 0)) (wk1Bit (k - 3) q.val && decide (p.val = 0)) := by
    unfold Bpair; dsimp only
    rw [wOfY_eVec_k1, wOfY_eVec_k1, wOfY_eVec_0, wOfY_eVec_0]
  have h3 : xorFin (fun j : Fin (r - 2) =>
      pol (fun y => xor (wOfY hr hk3 y ⟨3 * (j.val + 2) + 1, by omega⟩ &&
                          !(xor (wOfY hr hk3 y ⟨3 * (j.val + 2), by omega⟩) (wOfY hr hk3 y ⟨3 * (j.val + 2) + 2, by omega⟩)))
                        (wOfY hr hk3 y ⟨3 * (j.val + 2) + 2, by omega⟩)) (eVec p) (eVec q)) =
      xor (if 5 ≤ p.val ∧ p.val % 3 = 2 then dTermBit r (k - 3) ((p.val - 5) / 3) q.val else false)
          (if 5 ≤ q.val ∧ q.val % 3 = 2 then dTermBit r (k - 3) ((q.val - 5) / 3) p.val else false) := by
    have hstep : ∀ j : Fin (r - 2),
        pol (fun y => xor (wOfY hr hk3 y ⟨3 * (j.val + 2) + 1, by omega⟩ &&
                            !(xor (wOfY hr hk3 y ⟨3 * (j.val + 2), by omega⟩) (wOfY hr hk3 y ⟨3 * (j.val + 2) + 2, by omega⟩)))
                          (wOfY hr hk3 y ⟨3 * (j.val + 2) + 2, by omega⟩)) (eVec p) (eVec q) =
        xor (decide (p.val = 3 * j.val + 5) && dTermBit r (k - 3) j.val q.val)
            (decide (q.val = 3 * j.val + 5) && dTermBit r (k - 3) j.val p.val) := by
      intro j
      rw [pol_xor, pol_affine (isAffine_wOfY hr hk3 _), Bool.xor_false]
      rw [pol_and_not_lin (fun y => wOfY hr hk3 y ⟨3 * (j.val + 2) + 1, by omega⟩)
        (fun y => xor (wOfY hr hk3 y ⟨3 * (j.val + 2), by omega⟩) (wOfY hr hk3 y ⟨3 * (j.val + 2) + 2, by omega⟩))
        (fun a b => wOfY_xor hr hk3 a b _) (wOfY_zero hr hk3 _)
        (fun a b => by rw [wOfY_xor, wOfY_xor]; cases wOfY hr hk3 a _ <;> cases wOfY hr hk3 b _ <;> cases wOfY hr hk3 a _ <;> cases wOfY hr hk3 b _ <;> rfl)
        (by rw [wOfY_zero, wOfY_zero]; rfl)]
      unfold Bpair dTermBit; dsimp only
      have ha : ∀ x : Fin (k - 3), wOfY hr hk3 (eVec x) ⟨3 * (j.val + 2) + 1, by omega⟩ = decide (x.val = 3 * j.val + 5) := fun x => by
        rw [wOfY_eVec_mid hr hk3 x (3 * (j.val + 2) + 1) (by omega) (by omega)]
        exact congrArg (fun n => decide (x.val = n)) (by omega)
      have hb : ∀ x : Fin (k - 3), xor (wOfY hr hk3 (eVec x) ⟨3 * (j.val + 2), by omega⟩)
          (wOfY hr hk3 (eVec x) ⟨3 * (j.val + 2) + 2, by omega⟩) =
          xor (decide (x.val = 3 * j.val + 4))
              (if j.val + 1 = r - 2 then wk1Bit (k - 3) x.val else decide (x.val = 3 * j.val + 6)) := fun x => by
        congr 1
        · rw [wOfY_eVec_mid hr hk3 x (3 * (j.val + 2)) (by omega) (by omega)]
          exact congrArg (fun n => decide (x.val = n)) (by omega)
        · by_cases hjl : j.val + 1 = r - 2
          · rw [ite_pos hjl]
            have heq : (⟨3 * (j.val + 2) + 2, by omega⟩ : Fin k) = ⟨k - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
            rw [heq, wOfY_eVec_k1]
          · rw [ite_neg hjl, wOfY_eVec_mid hr hk3 x (3 * (j.val + 2) + 2) (by omega) (by omega)]
            exact congrArg (fun n => decide (x.val = n)) (by omega)
      rw [ha p, ha q, hb p, hb q]
    rw [xorFin_congr _ _ hstep, xorFin_xor]
    have hside : ∀ x y' : Fin (k - 3),
        xorFin (fun j : Fin (r - 2) => decide (x.val = 3 * j.val + 5) && dTermBit r (k - 3) j.val y'.val) =
        if 5 ≤ x.val ∧ x.val % 3 = 2 then dTermBit r (k - 3) ((x.val - 5) / 3) y'.val else false := by
      intro x y'
      by_cases hx : 5 ≤ x.val ∧ x.val % 3 = 2
      · rw [ite_pos hx]
        let j0 : Fin (r - 2) := ⟨(x.val - 5) / 3, by omega⟩
        rw [xorFin_single' j0]
        · have heq : x.val = 3 * j0.val + 5 := by dsimp [j0]; omega
          rw [decide_eq_true heq, Bool.true_and]
        · intro j hj
          have hne : x.val ≠ 3 * j.val + 5 := fun h => hj (Fin.ext (by dsimp [j0]; omega))
          rw [decide_eq_false hne, Bool.false_and]
      · rw [ite_neg hx]
        apply xorFin_eq_false; intro j
        have hne : x.val ≠ 3 * j.val + 5 := by omega
        rw [decide_eq_false hne, Bool.false_and]
    rw [hside p q, hside q p]
  rw [h1, h2, h3]

def coreIdx (p : Nat) : Nat :=
  if p = 0 then 2
  else if p = 1 then 3
  else 3 * (p / 2 + 1) - 2 + p % 2

def partner (p : Nat) : Nat :=
  if p % 2 = 0 then p + 1 else p - 1

def extraIdx (m : Nat) (a0 b0 : Bool) (e : Fin 4) : Nat :=
  match e.val with
  | 0 => 0
  | 1 => 1
  | 2 => if a0 = false ∧ b0 = false then m - 2 else m - 3
  | _ => if a0 = false then m - 1 else m - 2

def basisIdx4 (r m : Nat) (a0 b0 : Bool) (i : Fin (2 * r)) : Nat :=
  if h : i.val < 2 * r - 4 then coreIdx i.val
  else extraIdx m a0 b0 ⟨i.val - (2 * r - 4), by omega⟩

lemma coreIdx_lt {r m : Nat} (hr4 : 4 ≤ r) (hm : m = 3 * r - 3) (p : Nat) (hp : p < 2 * r - 4) :
    coreIdx p < m := by
  unfold coreIdx; split_ifs <;> omega

lemma coreIdx_mod {r m : Nat} (hr4 : 4 ≤ r) (hm : m = 3 * r - 3) (p : Nat) (hp : p < 2 * r - 4) :
    2 ≤ coreIdx p ∧ coreIdx p ≤ m - 4 ∧
    (p = 0 → coreIdx p = 2) ∧ (p = 1 → coreIdx p = 3) ∧
    (2 ≤ p → 4 ≤ coreIdx p ∧ coreIdx p % 3 = 1 + p % 2) := by
  unfold coreIdx; split_ifs <;> refine ⟨by omega, by omega, by omega, by omega, fun _ => ⟨by omega, by omega⟩⟩

lemma CBit_core_core {r m : Nat} (hr4 : 4 ≤ r) (hm : m = 3 * r - 3) (a0 b0 : Bool)
    (p q : Nat) (hp : p < 2 * r - 4) (hq : q < 2 * r - 4) :
    CBit r m a0 b0 (coreIdx p) (coreIdx q) = decide (p = partner q) := by
  have hcp := coreIdx_mod hr4 hm p hp
  have hcq := coreIdx_mod hr4 hm q hq
  unfold CBit BmBit B0Bit BkBit dTermBit partner
  have hnp0 : coreIdx p ≠ 0 := by omega
  have hnp1 : coreIdx p ≠ 1 := by omega
  have hnq0 : coreIdx q ≠ 0 := by omega
  have hnq1 : coreIdx q ≠ 1 := by omega
  simp only [hnp0, hnp1, hnq0, hnq1, decide_false, Bool.and_false, Bool.false_and, Bool.xor_false, Bool.false_xor]
  by_cases hp0 : p = 0
  · subst hp0
    have hcp2 : coreIdx 0 = 2 := rfl
    rw [hcp2]
    have hnq2 : ¬(5 ≤ 2 ∧ 2 % 3 = 2) := by omega
    rw [ite_neg hnq2, Bool.false_xor]
    by_cases hq1 : q = 1
    · subst hq1; simp [coreIdx]
    · have hcq3 : coreIdx q ≠ 3 := by unfold coreIdx at *; split_ifs at * <;> omega
      have htermq : (if 5 ≤ coreIdx q ∧ coreIdx q % 3 = 2 then
          xor (decide (2 = 3 * ((coreIdx q - 5) / 3) + 4))
            (if (coreIdx q - 5) / 3 + 1 = r - 2 then wk1Bit m 2 else decide (2 = 3 * ((coreIdx q - 5) / 3) + 6))
          else false) = false := by
        (split_ifs with h1 h2 <;> simp); omega
      rw [htermq]; simp only [hcq3, decide_false, show decide (2 = 3) = false from rfl, Bool.and_false, Bool.xor_false]
      apply Eq.symm; apply decide_eq_false; intro h
      by_cases hqe : q % 2 = 0
      · rw [ite_pos hqe] at h; omega
      · rw [ite_neg hqe] at h; omega
  · by_cases hp1 : p = 1
    · subst hp1
      have hcp3 : coreIdx 1 = 3 := rfl
      rw [hcp3]
      have hnq3 : ¬(5 ≤ 3 ∧ 3 % 3 = 2) := by omega
      rw [ite_neg hnq3, Bool.false_xor]
      by_cases hq0 : q = 0
      · subst hq0; simp [coreIdx]
      · have hcq2 : coreIdx q ≠ 2 := by unfold coreIdx at *; split_ifs at * <;> omega
        have htermq : (if 5 ≤ coreIdx q ∧ coreIdx q % 3 = 2 then
            xor (decide (3 = 3 * ((coreIdx q - 5) / 3) + 4))
              (if (coreIdx q - 5) / 3 + 1 = r - 2 then wk1Bit m 3 else decide (3 = 3 * ((coreIdx q - 5) / 3) + 6))
            else false) = false := by
          (split_ifs with h1 h2 <;> simp); omega
        rw [htermq]; simp only [hcq2, decide_false, Bool.false_and, Bool.xor_false]
        apply Eq.symm; apply decide_eq_false; split_ifs <;> omega
    · by_cases hq0 : q = 0
      · subst hq0
        have hcq2 : coreIdx 0 = 2 := rfl
        rw [hcq2]
        have hcp3 : coreIdx p ≠ 3 := by unfold coreIdx at *; split_ifs at * <;> omega
        have htermp : (if 5 ≤ coreIdx p ∧ coreIdx p % 3 = 2 then
            xor (decide (2 = 3 * ((coreIdx p - 5) / 3) + 4))
              (if (coreIdx p - 5) / 3 + 1 = r - 2 then wk1Bit m 2 else decide (2 = 3 * ((coreIdx p - 5) / 3) + 6))
            else false) = false := by
          (split_ifs with h1 h2 <;> simp); omega
        rw [htermp]; simp [hcp3, hp1]
      · by_cases hq1 : q = 1
        · subst hq1
          have hcq3 : coreIdx 1 = 3 := rfl
          rw [hcq3]
          have hcp2 : coreIdx p ≠ 2 := by unfold coreIdx at *; split_ifs at * <;> omega
          have htermp : (if 5 ≤ coreIdx p ∧ coreIdx p % 3 = 2 then
              xor (decide (3 = 3 * ((coreIdx p - 5) / 3) + 4))
                (if (coreIdx p - 5) / 3 + 1 = r - 2 then wk1Bit m 3 else decide (3 = 3 * ((coreIdx p - 5) / 3) + 6))
              else false) = false := by
            (split_ifs with h1 h2 <;> simp); omega
          rw [htermp]; simp [hcp2, hp0]
        ·
          have hp2 : 2 ≤ p := by omega
          have hq2 : 2 ≤ q := by omega
          have hcp_ne2 : coreIdx p ≠ 2 := by omega
          have hcp_ne3 : coreIdx p ≠ 3 := by omega
          have hcq_ne2 : coreIdx q ≠ 2 := by omega
          have hcq_ne3 : coreIdx q ≠ 3 := by omega
          simp only [hcp_ne2, hcp_ne3, hcq_ne2, hcq_ne3, decide_false, Bool.false_and, Bool.xor_false, Bool.false_xor]
          have hcp_ge : 4 ≤ coreIdx p ∧ coreIdx p % 3 = 1 + p % 2 := hcp.2.2.2.2 hp2
          have hcq_ge : 4 ≤ coreIdx q ∧ coreIdx q % 3 = 1 + q % 2 := hcq.2.2.2.2 hq2
          have hcp_lt : (coreIdx p - 5) / 3 + 1 < r - 2 := by unfold coreIdx at *; split_ifs at *; omega
          have hcq_lt : (coreIdx q - 5) / 3 + 1 < r - 2 := by unfold coreIdx at *; split_ifs at *; omega
          by_cases hpe : p % 2 = 0 <;> by_cases hqe : q % 2 = 0
          · have hnp : ¬(5 ≤ coreIdx p ∧ coreIdx p % 3 = 2) := by omega
            have hnq : ¬(5 ≤ coreIdx q ∧ coreIdx q % 3 = 2) := by omega
            rw [ite_neg hnp, ite_neg hnq]
            apply Eq.symm; apply decide_eq_false; split_ifs; omega
          · have hnp : ¬(5 ≤ coreIdx p ∧ coreIdx p % 3 = 2) := by omega
            have hq5 : 5 ≤ coreIdx q ∧ coreIdx q % 3 = 2 := by omega
            rw [ite_neg hnp, ite_pos hq5, Bool.false_xor, ite_neg (by omega)]
            have hne6 : coreIdx p ≠ 3 * ((coreIdx q - 5) / 3) + 6 := by omega
            rw [decide_eq_false hne6, Bool.xor_false, ite_neg hqe]
            exact decide_eq_decide_of_iff (by unfold coreIdx at *; split_ifs at *; omega)
          · have hp5 : 5 ≤ coreIdx p ∧ coreIdx p % 3 = 2 := by omega
            have hnq : ¬(5 ≤ coreIdx q ∧ coreIdx q % 3 = 2) := by omega
            rw [ite_pos hp5, ite_neg hnq, Bool.xor_false, ite_neg (by omega)]
            have hne6 : coreIdx q ≠ 3 * ((coreIdx p - 5) / 3) + 6 := by omega
            rw [decide_eq_false hne6, Bool.xor_false, ite_pos hqe]
            exact decide_eq_decide_of_iff (by unfold coreIdx at *; split_ifs at *; omega)
          · have hp5 : 5 ≤ coreIdx p ∧ coreIdx p % 3 = 2 := by omega
            have hq5 : 5 ≤ coreIdx q ∧ coreIdx q % 3 = 2 := by omega
            rw [ite_pos hp5, ite_pos hq5, ite_neg (by omega), ite_neg (by omega)]
            have h1 : coreIdx q ≠ 3 * ((coreIdx p - 5) / 3) + 4 := by omega
            have h2 : coreIdx q ≠ 3 * ((coreIdx p - 5) / 3) + 6 := by omega
            have h3 : coreIdx p ≠ 3 * ((coreIdx q - 5) / 3) + 4 := by omega
            have h4 : coreIdx p ≠ 3 * ((coreIdx q - 5) / 3) + 6 := by omega
            rw [decide_eq_false h1, decide_eq_false h2, decide_eq_false h3, decide_eq_false h4]
            apply Eq.symm; apply decide_eq_false; split_ifs; omega

lemma CBit_m2_core {r m : Nat} (hr4 : 4 ≤ r) (hm : m = 3 * r - 3) (a0 b0 : Bool)
    (p : Nat) (hp : p < 2 * r - 4) :
    CBit r m a0 b0 (m - 2) (coreIdx p) = false := by
  have hcp := coreIdx_mod hr4 hm p hp
  unfold CBit BmBit B0Bit BkBit dTermBit
  have h0 : m - 2 ≠ 0 := by omega
  have h1 : m - 2 ≠ 1 := by omega
  have h2 : m - 2 ≠ 2 := by omega
  have h3 : m - 2 ≠ 3 := by omega
  have h5 : ¬(5 ≤ m - 2 ∧ (m - 2) % 3 = 2) := by omega
  have hp0 : coreIdx p ≠ 0 := by omega
  have hp1 : coreIdx p ≠ 1 := by omega
  simp only [h0, h1, h2, h3, hp0, hp1, decide_false, Bool.and_false, Bool.false_and, Bool.xor_false, Bool.false_xor]
  rw [ite_neg h5, Bool.false_xor]
  split_ifs with hq5 hql
  · exfalso; unfold coreIdx at *; split_ifs at * <;> omega
  · have ha : m - 2 ≠ 3 * ((coreIdx p - 5) / 3) + 4 := by omega
    have hb : m - 2 ≠ 3 * ((coreIdx p - 5) / 3) + 6 := by omega
    simp [ha, hb]
  · rfl

lemma CBit_one_core {r m : Nat} (hr4 : 4 ≤ r) (hm : m = 3 * r - 3) (b0 : Bool)
    (p : Nat) (hp : p < 2 * r - 4) :
    CBit r m false b0 1 (coreIdx p) = false := by
  have hcp := coreIdx_mod hr4 hm p hp
  unfold CBit BmBit B0Bit BkBit dTermBit
  have hp0 : coreIdx p ≠ 0 := by omega
  simp only [hp0, decide_false, Bool.and_false, Bool.false_and, Bool.xor_false, Bool.false_xor]
  rw [ite_neg (by omega : ¬(5 ≤ 1 ∧ 1 % 3 = 2)), Bool.false_xor]
  split_ifs with hq5 hql
  · exfalso; unfold coreIdx at *; split_ifs at * <;> omega
  · have ha : (1 : Nat) ≠ 3 * ((coreIdx p - 5) / 3) + 4 := by omega
    have hb : (1 : Nat) ≠ 3 * ((coreIdx p - 5) / 3) + 6 := by omega
    rw [decide_eq_false ha, decide_eq_false hb]; simp
  · simp

lemma CBit_m3_core {r m : Nat} (hr4 : 4 ≤ r) (hm : m = 3 * r - 3) (a0 b0 : Bool)
    (p : Nat) (hp : p < 2 * r - 4) :
    CBit r m a0 b0 (m - 3) (coreIdx p) = decide (p = 2 * r - 5) := by
  have hcp := coreIdx_mod hr4 hm p hp
  unfold CBit BmBit B0Bit BkBit dTermBit
  have h0 : m - 3 ≠ 0 := by omega
  have h1 : m - 3 ≠ 1 := by omega
  have h2 : m - 3 ≠ 2 := by omega
  have h3 : m - 3 ≠ 3 := by omega
  have h5 : ¬(5 ≤ m - 3 ∧ (m - 3) % 3 = 2) := by omega
  have hp0 : coreIdx p ≠ 0 := by omega
  have hp1 : coreIdx p ≠ 1 := by omega
  simp only [h0, h1, h2, h3, hp0, hp1, decide_false, Bool.and_false, Bool.false_and, Bool.xor_false, Bool.false_xor]
  rw [ite_neg h5, Bool.false_xor]
  split_ifs with hq5 hql
  · exfalso; unfold coreIdx at *; split_ifs at * <;> omega
  · have ha : m - 3 ≠ 3 * ((coreIdx p - 5) / 3) + 4 := by omega
    rw [decide_eq_false ha, Bool.false_xor]
    have hcp_val : coreIdx p = 3 * (p / 2) + 2 := by
      unfold coreIdx at *; split_ifs at * <;> omega
    have hp_odd : p % 2 = 1 := by
      unfold coreIdx at *; split_ifs at * <;> omega
    rw [hcp_val]
    exact decide_eq_decide_of_iff (by omega)
  · apply Eq.symm; apply decide_eq_false
    intro heq; subst heq; unfold coreIdx at hq5; split_ifs at hq5 <;> omega

lemma CBit_last_even {r m : Nat} (hr4 : 4 ≤ r) (hm : m = 3 * r - 3) (a0 b0 : Bool) :
    CBit r m a0 b0 0 (coreIdx (2 * r - 6)) = !b0 ∧
    CBit r m a0 b0 1 (coreIdx (2 * r - 6)) = a0 ∧
    CBit r m a0 b0 (m - 1) (coreIdx (2 * r - 6)) = true := by
  have hce : coreIdx (2 * r - 6) = m - 5 := by
    unfold coreIdx; rw [ite_neg (by omega), ite_neg (by omega)]; omega
  rw [hce]
  have hw1 : w1Bit (m - 5) = true := by unfold w1Bit; apply decide_eq_true; right; right; omega
  have hwk1 : wk1Bit m (m - 5) = true := by unfold wk1Bit; apply decide_eq_true; right; right; omega
  have hnot5 : ¬(5 ≤ m - 5 ∧ (m - 5) % 3 = 2) := by omega
  refine ⟨?_, ?_, ?_⟩
  · unfold CBit BmBit B0Bit BkBit; rw [hw1, hwk1, ite_neg hnot5]
    have h2 : m - 5 ≠ 2 := by omega
    have h3 : m - 5 ≠ 3 := by omega
    have h0 : m - 5 ≠ 0 := by omega
    have h1 : m - 5 ≠ 1 := by omega
    simp [h0, h1, h2, h3]
  · unfold CBit BmBit B0Bit BkBit; rw [hw1, ite_neg hnot5]
    have h2 : m - 5 ≠ 2 := by omega
    have h3 : m - 5 ≠ 3 := by omega
    have h0 : m - 5 ≠ 0 := by omega
    have h1 : m - 5 ≠ 1 := by omega
    simp [h0, h1, h2, h3]
  · unfold CBit BmBit B0Bit BkBit dTermBit; rw [ite_neg hnot5]
    have hm1_5 : 5 ≤ m - 1 ∧ (m - 1) % 3 = 2 := by omega
    rw [ite_pos hm1_5]
    have hdiv : (m - 1 - 5) / 3 + 1 = r - 2 := by omega
    rw [ite_pos hdiv, hwk1]
    have hne : m - 5 ≠ 3 * ((m - 1 - 5) / 3) + 4 := by omega
    have h0 : m - 1 ≠ 0 := by omega
    have h1 : m - 1 ≠ 1 := by omega
    have h2 : m - 1 ≠ 2 := by omega
    have h3 : m - 1 ≠ 3 := by omega
    have hp0 : m - 5 ≠ 0 := by omega
    have hp1 : m - 5 ≠ 1 := by omega
    simp [h0, h1, h2, h3, hp0, hp1, hne]

lemma CBit_extra_vals {r m : Nat} (hr4 : 4 ≤ r) (hm : m = 3 * r - 3) (a0 b0 : Bool) :
    CBit r m a0 b0 1 (m - 2) = a0 ∧
    CBit r m a0 b0 1 (m - 1) = !a0 ∧
    CBit r m a0 b0 (m - 2) 0 = !b0 ∧
    CBit r m a0 b0 (m - 2) (m - 1) = false ∧
    CBit r m a0 b0 1 (m - 3) = false ∧
    CBit r m a0 b0 (m - 3) 0 = true ∧
    CBit r m a0 b0 (m - 3) (m - 1) = true ∧
    CBit r m a0 b0 (m - 2) (m - 3) = false := by
  have hw1_m2 : w1Bit (m - 2) = true := by unfold w1Bit; apply decide_eq_true; right; right; omega
  have hw1_m3 : w1Bit (m - 3) = false := by unfold w1Bit; apply decide_eq_false; omega
  have hw1_m1 : w1Bit (m - 1) = true := by unfold w1Bit; apply decide_eq_true; right; right; omega
  have hwk1_1 : wk1Bit m 1 = true := by unfold wk1Bit; apply decide_eq_true; right; left; rfl
  have hwk1_m2 : wk1Bit m (m - 2) = true := by unfold wk1Bit; apply decide_eq_true; right; right; omega
  have hwk1_m3 : wk1Bit m (m - 3) = true := by unfold wk1Bit; apply decide_eq_true; right; right; omega
  have hnot_m2 : ¬(5 ≤ m - 2 ∧ (m - 2) % 3 = 2) := by omega
  have hnot_m3 : ¬(5 ≤ m - 3 ∧ (m - 3) % 3 = 2) := by omega
  have hyes_m1 : 5 ≤ m - 1 ∧ (m - 1) % 3 = 2 := by omega
  have hdiv_m1 : (m - 1 - 5) / 3 + 1 = r - 2 := by omega
  have h3d4 : 3 * ((m - 1 - 5) / 3) + 4 = m - 2 := by omega
  have hm2_0 : m - 2 ≠ 0 := by omega
  have hm2_1 : m - 2 ≠ 1 := by omega
  have hm2_2 : m - 2 ≠ 2 := by omega
  have hm2_3 : m - 2 ≠ 3 := by omega
  have hm3_0 : m - 3 ≠ 0 := by omega
  have hm3_1 : m - 3 ≠ 1 := by omega
  have hm3_2 : m - 3 ≠ 2 := by omega
  have hm3_3 : m - 3 ≠ 3 := by omega
  have hm1_0 : m - 1 ≠ 0 := by omega
  have hm1_1 : m - 1 ≠ 1 := by omega
  have hm1_2 : m - 1 ≠ 2 := by omega
  have hm1_3 : m - 1 ≠ 3 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold CBit BmBit B0Bit BkBit; rw [hw1_m2, ite_neg hnot_m2]
    simp [hm2_0, hm2_1, hm2_2, hm2_3]
  · unfold CBit BmBit B0Bit BkBit dTermBit; rw [hw1_m1, ite_pos hyes_m1, ite_pos hdiv_m1, hwk1_1, h3d4]
    have h1n : (1 : Nat) ≠ m - 2 := by omega
    simp [hm1_0, hm1_1, hm1_2, hm1_3, h1n]
  · unfold CBit BmBit B0Bit BkBit; rw [hw1_m2, hwk1_m2, ite_neg hnot_m2]
    simp [hm2_0, hm2_1, hm2_2, hm2_3]
  · unfold CBit BmBit B0Bit BkBit dTermBit; rw [ite_neg hnot_m2, ite_pos hyes_m1, ite_pos hdiv_m1, hwk1_m2, h3d4]
    simp [hm2_0, hm2_1, hm2_2, hm2_3, hm1_0, hm1_1, hm1_2, hm1_3]
  · unfold CBit BmBit B0Bit BkBit; rw [hw1_m3, ite_neg hnot_m3]
    simp [hm3_0, hm3_1, hm3_2, hm3_3]
  · unfold CBit BmBit B0Bit BkBit; rw [hw1_m3, hwk1_m3, ite_neg hnot_m3]
    simp [hm3_0, hm3_1, hm3_2, hm3_3]
  · unfold CBit BmBit B0Bit BkBit dTermBit; rw [ite_neg hnot_m3, ite_pos hyes_m1, ite_pos hdiv_m1, hwk1_m3, h3d4]
    have hne : m - 3 ≠ m - 2 := by omega
    simp [hm3_0, hm3_1, hm3_2, hm3_3, hm1_0, hm1_1, hm1_2, hm1_3, hne]
  · unfold CBit BmBit B0Bit BkBit; rw [ite_neg hnot_m2, ite_neg hnot_m3]
    simp [hm2_0, hm2_1, hm2_2, hm2_3, hm3_0, hm3_1, hm3_2, hm3_3]

lemma inv_CBit_r4 {r m : Nat} (hr4 : 4 ≤ r) (hm : m = 3 * r - 3) (a0 b0 : Bool)
    (c : Fin (2 * r) → Bool)
    (hzero : ∀ q : Fin (2 * r),
      xorFin (fun i : Fin (2 * r) => c i && CBit r m a0 b0 (basisIdx4 r m a0 b0 i) (basisIdx4 r m a0 b0 q)) = false) :
    ∀ i : Fin (2 * r), c i = false := by
  let L := 2 * r - 4
  have h2r : 2 * r = L + 4 := by omega
  let cc : Fin L → Bool := fun p => c ⟨p.val, by omega⟩
  let ce : Fin 4 → Bool := fun e => c ⟨L + e.val, by omega⟩
  have hsplit : ∀ (q : Fin (2 * r)),
      xor (xorFin (fun p : Fin L => cc p && CBit r m a0 b0 (coreIdx p.val) (basisIdx4 r m a0 b0 q)))
          (xorFin (fun e : Fin 4 => ce e && CBit r m a0 b0 (extraIdx m a0 b0 e) (basisIdx4 r m a0 b0 q))) = false := by
    intro q
    have hq := hzero q
    rw [xorFin_cast h2r _ (fun i : Fin (L + 4) => c ⟨i.val, by omega⟩ &&
        CBit r m a0 b0 (basisIdx4 r m a0 b0 ⟨i.val, by omega⟩) (basisIdx4 r m a0 b0 q)) (fun _ _ _ => rfl),
      xorFin_add_split] at hq
    rw [← hq]; congr 1
    · apply xorFin_congr; intro p
      have hbp : basisIdx4 r m a0 b0 ⟨p.val, by omega⟩ = coreIdx p.val := by
        unfold basisIdx4; dsimp only; rw [dite_pos p.isLt]
      rw [hbp]
    · apply xorFin_congr; intro e
      have hbe : basisIdx4 r m a0 b0 ⟨L + e.val, by omega⟩ = extraIdx m a0 b0 e := by
        unfold basisIdx4; dsimp only; rw [dite_neg (by omega)]
        exact congrArg (extraIdx m a0 b0) (Fin.ext (by dsimp only; omega))
      rw [hbe]
  have hpart_lt : ∀ p : Fin L, partner p.val < L := fun p => by unfold partner; split_ifs <;> omega
  have hpart_inv : ∀ p : Fin L, partner (partner p.val) = p.val := fun p => by unfold partner; split_ifs <;> omega

  have hcc : ∀ p : Fin L,
      cc p = xorFin (fun e : Fin 4 => ce e && CBit r m a0 b0 (extraIdx m a0 b0 e) (coreIdx (partner p.val))) := by
    intro p
    let q : Fin (2 * r) := ⟨partner p.val, by have := hpart_lt p; omega⟩
    have hq := hsplit q
    have hbq : basisIdx4 r m a0 b0 q = coreIdx (partner p.val) := by
      unfold basisIdx4; dsimp only [q]; rw [dite_pos (hpart_lt p)]
    rw [hbq] at hq
    have hcore : xorFin (fun i : Fin L => cc i && CBit r m a0 b0 (coreIdx i.val) (coreIdx (partner p.val))) = cc p := by
      rw [xorFin_single' p]
      · rw [CBit_core_core hr4 hm a0 b0 p.val (partner p.val) p.isLt (hpart_lt p), hpart_inv p]; simp
      · intro i hi
        rw [CBit_core_core hr4 hm a0 b0 i.val (partner p.val) i.isLt (hpart_lt p), hpart_inv p]
        have hne : i.val ≠ p.val := fun h => hi (Fin.ext h)
        simp [hne]
    rw [hcore] at hq
    cases ha : cc p <;> cases hb : xorFin (fun e : Fin 4 => ce e && CBit r m a0 b0 (extraIdx m a0 b0 e) (coreIdx (partner p.val))) <;>
      rw [ha, hb] at hq <;> simp at hq ⊢

  let S : Fin 4 → Fin 4 → Bool := fun e j =>
    xor (CBit r m a0 b0 (extraIdx m a0 b0 e) (extraIdx m a0 b0 j))
        (xorFin (fun p : Fin L =>
          CBit r m a0 b0 (extraIdx m a0 b0 e) (coreIdx (partner p.val)) &&
          CBit r m a0 b0 (coreIdx p.val) (extraIdx m a0 b0 j)))
  have hschur : ∀ j : Fin 4, xorFin (fun e : Fin 4 => ce e && S e j) = false := by
    intro j
    let q : Fin (2 * r) := ⟨L + j.val, by omega⟩
    have hq := hsplit q
    have hbq : basisIdx4 r m a0 b0 q = extraIdx m a0 b0 j := by
      unfold basisIdx4; dsimp only [q]; rw [dite_neg (by omega)]
      have hj_eq : (⟨L + j.val - L, by omega⟩ : Fin 4) = j := Fin.ext (by dsimp only; omega)
      rw [hj_eq]
    rw [hbq] at hq
    have hsub : xorFin (fun p : Fin L => cc p && CBit r m a0 b0 (coreIdx p.val) (extraIdx m a0 b0 j)) =
        xorFin (fun e : Fin 4 => ce e &&
          xorFin (fun p : Fin L =>
            CBit r m a0 b0 (extraIdx m a0 b0 e) (coreIdx (partner p.val)) &&
            CBit r m a0 b0 (coreIdx p.val) (extraIdx m a0 b0 j))) := by
      have h1 : xorFin (fun p : Fin L => cc p && CBit r m a0 b0 (coreIdx p.val) (extraIdx m a0 b0 j)) =
          xorFin (fun p : Fin L => xorFin (fun e : Fin 4 =>
            ce e && (CBit r m a0 b0 (extraIdx m a0 b0 e) (coreIdx (partner p.val)) &&
                     CBit r m a0 b0 (coreIdx p.val) (extraIdx m a0 b0 j)))) := by
        apply xorFin_congr; intro p; rw [hcc p, ← xorFin_and_right]
        apply xorFin_congr; intro e; simp [Bool.and_assoc]
      rw [h1, xorFin_swap]
      apply xorFin_congr; intro e; rw [xorFin_and_left]
    rw [hsub, ← xorFin_xor] at hq
    rw [← hq]; apply xorFin_congr; intro e; unfold S
    cases ce e <;> cases CBit r m a0 b0 (extraIdx m a0 b0 e) (extraIdx m a0 b0 j) <;>
      cases xorFin (fun p : Fin L => CBit r m a0 b0 (extraIdx m a0 b0 e) (coreIdx (partner p.val)) &&
        CBit r m a0 b0 (coreIdx p.val) (extraIdx m a0 b0 j)) <;> rfl
  have hfr4 : ∀ g : Fin 4 → Bool,
      xorFin g = xor (g ⟨0, by omega⟩) (xor (g ⟨1, by omega⟩) (xor (g ⟨2, by omega⟩) (g ⟨3, by omega⟩))) := by
    intro g; unfold xorFin
    have : List.finRange 4 = [0, 1, 2, 3] := rfl
    rw [this]; simp

  have hS_zeroR : ∀ (e j : Fin 4),
      (∀ p : Fin L, CBit r m a0 b0 (extraIdx m a0 b0 j) (coreIdx p.val) = false) →
      S e j = CBit r m a0 b0 (extraIdx m a0 b0 e) (extraIdx m a0 b0 j) := by
    intro e j hz; unfold S
    have h0 : xorFin (fun p : Fin L => CBit r m a0 b0 (extraIdx m a0 b0 e) (coreIdx (partner p.val)) &&
        CBit r m a0 b0 (coreIdx p.val) (extraIdx m a0 b0 j)) = false :=
      xorFin_eq_false _ (fun p => by rw [CBit_symm r m a0 b0 (coreIdx p.val), hz p, Bool.and_false])
    rw [h0, Bool.xor_false]
  have hS_zeroL : ∀ (e j : Fin 4),
      (∀ p : Fin L, CBit r m a0 b0 (extraIdx m a0 b0 e) (coreIdx p.val) = false) →
      S e j = CBit r m a0 b0 (extraIdx m a0 b0 e) (extraIdx m a0 b0 j) := by
    intro e j hz; unfold S
    have h0 : xorFin (fun p : Fin L => CBit r m a0 b0 (extraIdx m a0 b0 e) (coreIdx (partner p.val)) &&
        CBit r m a0 b0 (coreIdx p.val) (extraIdx m a0 b0 j)) = false :=
      xorFin_eq_false _ (fun p => by rw [hz ⟨partner p.val, hpart_lt p⟩, Bool.false_and])
    rw [h0, Bool.xor_false]
  have hS_m3R : ∀ (e j : Fin 4), extraIdx m a0 b0 j = m - 3 →
      S e j = xor (CBit r m a0 b0 (extraIdx m a0 b0 e) (m - 3))
                  (CBit r m a0 b0 (extraIdx m a0 b0 e) (coreIdx (2 * r - 6))) := by
    intro e j hj; unfold S; rw [hj]; congr 1
    let p0 : Fin L := ⟨2 * r - 5, by omega⟩
    rw [xorFin_single' p0]
    · rw [CBit_symm r m a0 b0 (coreIdx p0.val), CBit_m3_core hr4 hm a0 b0 p0.val p0.isLt]
      have hp0_eq : p0.val = 2 * r - 5 := rfl
      have hpart0 : partner p0.val = 2 * r - 6 := by unfold partner; dsimp [p0]; rw [ite_neg (by omega)]; omega
      rw [hp0_eq, hpart0]; simp
    · intro p hp
      rw [CBit_symm r m a0 b0 (coreIdx p.val), CBit_m3_core hr4 hm a0 b0 p.val p.isLt]
      have hne : p.val ≠ 2 * r - 5 := fun h => hp (Fin.ext h)
      simp [hne]
  have hS_m3L : ∀ (e j : Fin 4), extraIdx m a0 b0 e = m - 3 →
      S e j = xor (CBit r m a0 b0 (m - 3) (extraIdx m a0 b0 j))
                  (CBit r m a0 b0 (coreIdx (2 * r - 6)) (extraIdx m a0 b0 j)) := by
    intro e j he; unfold S; rw [he]; congr 1
    let p0 : Fin L := ⟨2 * r - 6, by omega⟩
    rw [xorFin_single' p0]
    · have hpart0 : partner p0.val = 2 * r - 5 := by unfold partner; dsimp [p0]; rw [ite_pos (by omega)]; omega
      rw [hpart0, CBit_m3_core hr4 hm a0 b0 (2 * r - 5) (by omega)]; simp [p0]
    · intro p hp
      rw [CBit_m3_core hr4 hm a0 b0 (partner p.val) (hpart_lt p)]
      have hne : partner p.val ≠ 2 * r - 5 := fun h => hp (Fin.ext (by
        have := hpart_inv p; rw [h] at this; unfold partner at this
        rw [ite_neg (by omega)] at this; dsimp [p0]; omega))
      simp [hne]
  have hself : ∀ x, CBit r m a0 b0 x x = false := fun x => by
    unfold CBit BmBit B0Bit BkBit
    cases (decide (x = 2) && decide (x = 3)) <;> cases (wk1Bit m x && decide (x = 0)) <;>
      cases (if 5 ≤ x ∧ x % 3 = 2 then dTermBit r m ((x - 5) / 3) x else false) <;>
      cases a0 <;> cases b0 <;> cases (w1Bit x && decide (x = 1)) <;>
      cases (decide (x = 0) && w1Bit x) <;> rfl
  have hex := CBit_extra_vals hr4 hm a0 b0
  have hle := CBit_last_even hr4 hm a0 b0
  have hm2z : ∀ p : Fin L, CBit r m a0 b0 (m - 2) (coreIdx p.val) = false := fun p => CBit_m2_core hr4 hm a0 b0 p.val p.isLt

  have hce0 : ∀ e : Fin 4, ce e = false := by
    have eq0 := hschur ⟨0, by omega⟩; rw [hfr4] at eq0
    have eq1 := hschur ⟨1, by omega⟩; rw [hfr4] at eq1
    have eq2 := hschur ⟨2, by omega⟩; rw [hfr4] at eq2
    have eq3 := hschur ⟨3, by omega⟩; rw [hfr4] at eq3
    cases a0 <;> cases b0
    ·
      have h1z : ∀ p : Fin L, CBit r m false false 1 (coreIdx p.val) = false := fun p => CBit_one_core hr4 hm false p.val p.isLt
      have hs02 : S ⟨0, by omega⟩ ⟨2, by omega⟩ = true := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using hm2z)]; simp [extraIdx]; rw [CBit_symm]; exact hex.2.2.1
      have hs12 : S ⟨1, by omega⟩ ⟨2, by omega⟩ = false := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using hm2z)]; exact hex.1
      have hs22 : S ⟨2, by omega⟩ ⟨2, by omega⟩ = false := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using hm2z)]; exact hself _
      have hs32 : S ⟨3, by omega⟩ ⟨2, by omega⟩ = false := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using hm2z)]; simp [extraIdx]; rw [CBit_symm]; exact hex.2.2.2.1
      rw [hs02, hs12, hs22, hs32] at eq2
      have hce_0 : ce ⟨0, by omega⟩ = false := by simpa using eq2
      have hs11 : S ⟨1, by omega⟩ ⟨1, by omega⟩ = false := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using h1z)]; exact hself _
      have hs21 : S ⟨2, by omega⟩ ⟨1, by omega⟩ = false := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using h1z)]; simp [extraIdx]; rw [CBit_symm]; exact hex.1
      have hs31 : S ⟨3, by omega⟩ ⟨1, by omega⟩ = true := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using h1z)]; simp [extraIdx]; rw [CBit_symm]; exact hex.2.1
      rw [hce_0, hs11, hs21, hs31] at eq1
      have hce_3 : ce ⟨3, by omega⟩ = false := by simpa using eq1
      have hs13 : S ⟨1, by omega⟩ ⟨3, by omega⟩ = true := by
        rw [hS_zeroL _ _ (by simpa [extraIdx] using h1z)]; exact hex.2.1
      have hs23 : S ⟨2, by omega⟩ ⟨3, by omega⟩ = false := by
        rw [hS_zeroL _ _ (by simpa [extraIdx] using hm2z)]; exact hex.2.2.2.1
      rw [hce_0, hce_3, hs13, hs23] at eq3
      have hce_1 : ce ⟨1, by omega⟩ = false := by simpa using eq3
      have hs20 : S ⟨2, by omega⟩ ⟨0, by omega⟩ = true := by
        rw [hS_zeroL _ _ (by simpa [extraIdx] using hm2z)]; exact hex.2.2.1
      rw [hce_0, hce_1, hce_3, hs20] at eq0
      have hce_2 : ce ⟨2, by omega⟩ = false := by simpa using eq0
      intro e; fin_cases e <;> assumption
    ·
      have h1z : ∀ p : Fin L, CBit r m false true 1 (coreIdx p.val) = false := fun p => CBit_one_core hr4 hm true p.val p.isLt
      have hs02 : S ⟨0, by omega⟩ ⟨2, by omega⟩ = true := by
        rw [hS_m3R _ _ rfl]; simp [extraIdx]; rw [CBit_symm r m false true 0 (m - 3), hex.2.2.2.2.2.1, hle.1]; decide
      have hs12 : S ⟨1, by omega⟩ ⟨2, by omega⟩ = false := by
        rw [hS_zeroL _ _ (by simpa [extraIdx] using h1z)]; exact hex.2.2.2.2.1
      have hs22 : S ⟨2, by omega⟩ ⟨2, by omega⟩ = false := by
        rw [hS_m3R _ _ rfl]; simp [extraIdx]; rw [hself, CBit_m3_core hr4 hm false true (2 * r - 6) (by omega), decide_eq_false (by omega)]
      have hs32 : S ⟨3, by omega⟩ ⟨2, by omega⟩ = false := by
        rw [hS_m3R _ _ rfl]; simp [extraIdx]; rw [CBit_symm r m false true (m - 1) (m - 3), hex.2.2.2.2.2.2.1, hle.2.2]
      rw [hs02, hs12, hs22, hs32] at eq2
      have hce_0 : ce ⟨0, by omega⟩ = false := by simpa using eq2
      have hs11 : S ⟨1, by omega⟩ ⟨1, by omega⟩ = false := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using h1z)]; exact hself _
      have hs21 : S ⟨2, by omega⟩ ⟨1, by omega⟩ = false := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using h1z)]; simp [extraIdx]; rw [CBit_symm]; exact hex.2.2.2.2.1
      have hs31 : S ⟨3, by omega⟩ ⟨1, by omega⟩ = true := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using h1z)]; simp [extraIdx]; rw [CBit_symm]; exact hex.2.1
      rw [hce_0, hs11, hs21, hs31] at eq1
      have hce_3 : ce ⟨3, by omega⟩ = false := by simpa using eq1
      have hs13 : S ⟨1, by omega⟩ ⟨3, by omega⟩ = true := by
        rw [hS_zeroL _ _ (by simpa [extraIdx] using h1z)]; exact hex.2.1
      have hs23 : S ⟨2, by omega⟩ ⟨3, by omega⟩ = false := by
        rw [hS_m3L _ _ rfl]; simp [extraIdx]; rw [hex.2.2.2.2.2.2.1, CBit_symm r m false true (coreIdx _), hle.2.2]
      rw [hce_0, hce_3, hs13, hs23] at eq3
      have hce_1 : ce ⟨1, by omega⟩ = false := by simpa using eq3
      have hs20 : S ⟨2, by omega⟩ ⟨0, by omega⟩ = true := by
        rw [hS_m3L _ _ rfl]; simp [extraIdx]; rw [hex.2.2.2.2.2.1, CBit_symm r m false true (coreIdx _), hle.1]; decide
      rw [hce_0, hce_1, hce_3, hs20] at eq0
      have hce_2 : ce ⟨2, by omega⟩ = false := by simpa using eq0
      intro e; fin_cases e <;> assumption
    ·
      have hs03 : S ⟨0, by omega⟩ ⟨3, by omega⟩ = true := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using hm2z)]; simp [extraIdx]; rw [CBit_symm]; exact hex.2.2.1
      have hs13 : S ⟨1, by omega⟩ ⟨3, by omega⟩ = true := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using hm2z)]; exact hex.1
      have hs23 : S ⟨2, by omega⟩ ⟨3, by omega⟩ = false := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using hm2z)]; simp [extraIdx]; rw [CBit_symm]; exact hex.2.2.2.2.2.2.2
      have hs33 : S ⟨3, by omega⟩ ⟨3, by omega⟩ = false := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using hm2z)]; exact hself _
      rw [hs03, hs13, hs23, hs33] at eq3
      have hs02 : S ⟨0, by omega⟩ ⟨2, by omega⟩ = false := by
        rw [hS_m3R _ _ rfl]; simp [extraIdx]; rw [CBit_symm r m true false 0 (m - 3), hex.2.2.2.2.2.1, hle.1]; rfl
      have hs12 : S ⟨1, by omega⟩ ⟨2, by omega⟩ = true := by
        rw [hS_m3R _ _ rfl]; simp [extraIdx]; rw [hex.2.2.2.2.1, hle.2.1]; decide
      have hs22 : S ⟨2, by omega⟩ ⟨2, by omega⟩ = false := by
        rw [hS_m3R _ _ rfl]; simp [extraIdx]; rw [hself, CBit_m3_core hr4 hm true false (2 * r - 6) (by omega), decide_eq_false (by omega)]
      have hs32 : S ⟨3, by omega⟩ ⟨2, by omega⟩ = false := by
        rw [hS_zeroL _ _ (by simpa [extraIdx] using hm2z)]; exact hex.2.2.2.2.2.2.2
      rw [hs02, hs12, hs22, hs32] at eq2
      have hce_1 : ce ⟨1, by omega⟩ = false := by simpa using eq2
      have hce_0 : ce ⟨0, by omega⟩ = false := by rw [hce_1] at eq3; simpa using eq3
      have hs20 : S ⟨2, by omega⟩ ⟨0, by omega⟩ = false := by
        rw [hS_m3L _ _ rfl]; simp [extraIdx]; rw [hex.2.2.2.2.2.1, CBit_symm r m true false (coreIdx _), hle.1]; rfl
      have hs30 : S ⟨3, by omega⟩ ⟨0, by omega⟩ = true := by
        rw [hS_zeroL _ _ (by simpa [extraIdx] using hm2z)]; exact hex.2.2.1
      rw [hce_0, hce_1, hs20, hs30] at eq0
      have hce_3 : ce ⟨3, by omega⟩ = false := by simpa using eq0
      have hs21 : S ⟨2, by omega⟩ ⟨1, by omega⟩ = true := by
        rw [hS_m3L _ _ rfl]; simp [extraIdx]
        rw [CBit_symm r m true false (m - 3) 1, hex.2.2.2.2.1, CBit_symm r m true false (coreIdx _) 1, hle.2.1]; decide
      rw [hce_0, hce_1, hce_3, hs21] at eq1
      have hce_2 : ce ⟨2, by omega⟩ = false := by simpa using eq1
      intro e; fin_cases e <;> assumption
    ·
      have hs03 : S ⟨0, by omega⟩ ⟨3, by omega⟩ = false := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using hm2z)]; simp [extraIdx]; rw [CBit_symm]; exact hex.2.2.1
      have hs13 : S ⟨1, by omega⟩ ⟨3, by omega⟩ = true := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using hm2z)]; exact hex.1
      have hs23 : S ⟨2, by omega⟩ ⟨3, by omega⟩ = false := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using hm2z)]; simp [extraIdx]; rw [CBit_symm]; exact hex.2.2.2.2.2.2.2
      have hs33 : S ⟨3, by omega⟩ ⟨3, by omega⟩ = false := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using hm2z)]; exact hself _
      rw [hs03, hs13, hs23, hs33] at eq3
      have hce_1 : ce ⟨1, by omega⟩ = false := by simpa using eq3
      have hs02 : S ⟨0, by omega⟩ ⟨2, by omega⟩ = true := by
        rw [hS_m3R _ _ rfl]; simp [extraIdx]; rw [CBit_symm r m true true 0 (m - 3), hex.2.2.2.2.2.1, hle.1]; decide
      have hs22 : S ⟨2, by omega⟩ ⟨2, by omega⟩ = false := by
        rw [hS_m3R _ _ rfl]; simp [extraIdx]; rw [hself, CBit_m3_core hr4 hm true true (2 * r - 6) (by omega), decide_eq_false (by omega)]
      have hs32 : S ⟨3, by omega⟩ ⟨2, by omega⟩ = false := by
        rw [hS_zeroL _ _ (by simpa [extraIdx] using hm2z)]; exact hex.2.2.2.2.2.2.2
      rw [hce_1, hs02, hs22, hs32] at eq2
      have hce_0 : ce ⟨0, by omega⟩ = false := by simpa using eq2
      have hs20 : S ⟨2, by omega⟩ ⟨0, by omega⟩ = true := by
        rw [hS_m3L _ _ rfl]; simp [extraIdx]; rw [hex.2.2.2.2.2.1, CBit_symm r m true true (coreIdx _), hle.1]; decide
      have hs30 : S ⟨3, by omega⟩ ⟨0, by omega⟩ = false := by
        rw [hS_zeroL _ _ (by simpa [extraIdx] using hm2z)]; exact hex.2.2.1
      rw [hce_0, hce_1, hs20, hs30] at eq0
      have hce_2 : ce ⟨2, by omega⟩ = false := by simpa using eq0
      have hs31 : S ⟨3, by omega⟩ ⟨1, by omega⟩ = true := by
        rw [hS_zeroL _ _ (by simpa [extraIdx] using hm2z)]; simp [extraIdx]; rw [CBit_symm]; exact hex.1
      rw [hce_0, hce_1, hce_2, hs31] at eq1
      have hce_3 : ce ⟨3, by omega⟩ = false := by simpa using eq1
      intro e; fin_cases e <;> assumption
  intro i
  by_cases hi : i.val < L
  · have hcp := hcc ⟨i.val, hi⟩
    have h0 : xorFin (fun e : Fin 4 => ce e && CBit r m a0 b0 (extraIdx m a0 b0 e) (coreIdx (partner i.val))) = false :=
      xorFin_eq_false _ (fun e => by rw [hce0 e, Bool.false_and])
    simpa [cc, h0] using hcp
  · have h := hce0 ⟨i.val - L, by omega⟩
    have heq : (⟨L + (i.val - L), by omega⟩ : Fin (2 * r)) = i := Fin.ext (by dsimp only; omega)
    simpa [ce, heq] using h

def Good (width : Nat) (gs : List Gate) : Prop :=
  ReadsBack width ⟨gs, 0⟩ ∧
  (∀ g ∈ gs, g.inputs.length ≤ 2) ∧
  (depthList width gs).foldr max 0 ≤ 1

def WireSpec (width : Nat) (gs : List Gate) (w : Nat) (d0 : Bool) (f : List Bool → Bool) : Prop :=
  w < width + gs.length ∧
  (d0 = true → (depthList width gs).getD w 0 = 0) ∧
  ∀ inp : List Bool, inp.length = width → (Circuit.wires ⟨gs, 0⟩ inp).getD w false = f inp

lemma good_nil (width : Nat) : Good width [] := by
  refine ⟨fun j hj => by simp at hj, (fun _ hg => by cases hg), ?_⟩
  rw [foldr_max_le_iff]; intro x hx
  have hmem : x ∈ List.replicate width 0 := hx
  rw [List.mem_replicate] at hmem; omega

lemma wireSpec_input (width : Nat) (w : Nat) (hw : w < width) :
    WireSpec width [] w true (fun inp => inp.getD w false) := by
  refine ⟨by simp [hw], fun _ => ?_, fun inp _ => rfl⟩
  unfold depthList
  rw [List.foldl_nil, List.getD_eq_getElem _ _ (by simp [hw]), List.getElem_replicate]

lemma append_gate {width : Nat} (gs : List Gate) (hgood : Good width gs) (g : Gate)
    (hfan : g.inputs.length ≤ 2)
    (hrb : ∀ i ∈ g.inputs, i < width + gs.length)
    (hdg : (g.inputs.map (fun a => (depthList width gs).getD a 0)).foldr max 0 + (nonlinear g).toNat ≤ 1) :
    Good width (gs ++ [g]) ∧
    (gs ++ [g]).countP nonlinear = gs.countP nonlinear + (nonlinear g).toNat ∧
    (∀ w d0 f, WireSpec width gs w d0 f → WireSpec width (gs ++ [g]) w d0 f) ∧
    WireSpec width (gs ++ [g]) (width + gs.length)
      (decide ((g.inputs.map (fun a => (depthList width gs).getD a 0)).foldr max 0 + (nonlinear g).toNat = 0))
      (fun inp => g.op.eval (g.inputs.map fun a => (Circuit.wires ⟨gs, 0⟩ inp).getD a false)) := by
  have hds_step : depthList width (gs ++ [g]) =
      depthList width gs ++ [(g.inputs.map (fun a => (depthList width gs).getD a 0)).foldr max 0 + (nonlinear g).toNat] := by
    unfold depthList; rw [List.foldl_append]; rfl
  have hds_len : (depthList width gs).length = width + gs.length := depthList_length width gs
  have hw_step : ∀ inp, Circuit.wires ⟨gs ++ [g], 0⟩ inp =
      Circuit.wires ⟨gs, 0⟩ inp ++ [g.op.eval (g.inputs.map fun a => (Circuit.wires ⟨gs, 0⟩ inp).getD a false)] := by
    intro inp; unfold Circuit.wires; rw [List.foldl_append]; rfl
  have hw_len : ∀ inp, inp.length = width → (Circuit.wires ⟨gs, 0⟩ inp).length = width + gs.length := by
    intro inp hlen; unfold Circuit.wires; rw [wires_length, hlen]
  have hgood' : Good width (gs ++ [g]) := by
    refine ⟨?_, ?_, ?_⟩
    · intro j hj i hi
      change j < (gs ++ [g]).length at hj
      simp only [List.length_append, List.length_cons, List.length_nil] at hj
      by_cases hlt : j < gs.length
      · have hga : gateAt ⟨gs ++ [g], 0⟩ j = gateAt ⟨gs, 0⟩ j := by
          unfold gateAt; exact getD_append_lt gs g _ hlt
        rw [hga] at hi; exact hgood.1 j hlt i hi
      · have hjeq : j = gs.length := by omega
        subst hjeq
        have hga : gateAt ⟨gs ++ [g], 0⟩ gs.length = g := by unfold gateAt; exact getD_append_eq gs g _
        rw [hga] at hi; exact hrb i hi
    · intro g' hg'
      rcases List.mem_append.mp hg' with hg1 | hg2
      · exact hgood.2.1 g' hg1
      · simp only [List.mem_singleton] at hg2; subst hg2; exact hfan
    · rw [foldr_max_le_iff]; intro x hx
      rw [hds_step] at hx
      rcases List.mem_append.mp hx with hx1 | hx2
      · exact (foldr_max_le_iff _ _).mp hgood.2.2 x hx1
      · simp only [List.mem_singleton] at hx2; subst hx2; exact hdg
  have hcnt : (gs ++ [g]).countP nonlinear = gs.countP nonlinear + (nonlinear g).toNat := by
    rw [List.countP_append, List.countP_cons, List.countP_nil]
    cases nonlinear g <;> simp [Bool.toNat]
  have hpres : ∀ w d0 f, WireSpec width gs w d0 f → WireSpec width (gs ++ [g]) w d0 f := by
    intro w d0 f hw
    have hwlt : w < width + gs.length := hw.1
    refine ⟨by simp only [List.length_append, List.length_cons, List.length_nil]; omega, fun hd0 => ?_, fun inp hlen => ?_⟩
    · rw [hds_step, getD_append_lt _ _ _ (by omega)]; exact hw.2.1 hd0
    · rw [hw_step, getD_append_lt _ _ _ (by rw [hw_len inp hlen]; exact hw.1)]; exact hw.2.2 inp hlen
  have hnew : WireSpec width (gs ++ [g]) (width + gs.length)
      (decide ((g.inputs.map (fun a => (depthList width gs).getD a 0)).foldr max 0 + (nonlinear g).toNat = 0))
      (fun inp => g.op.eval (g.inputs.map fun a => (Circuit.wires ⟨gs, 0⟩ inp).getD a false)) := by
    refine ⟨by simp, fun hd0 => ?_, fun inp hlen => ?_⟩
    · rw [hds_step, ← hds_len, getD_append_eq]; exact of_decide_eq_true hd0
    · rw [hw_step, ← hw_len inp hlen, getD_append_eq]
  exact ⟨hgood', hcnt, hpres, hnew⟩

lemma addConst {width : Nat} (gs : List Gate) (hgood : Good width gs) (c : Bool) :
    ∃ (gs' : List Gate) (w : Nat),
      Good width gs' ∧ gs'.countP nonlinear = gs.countP nonlinear ∧
      (∀ w0 d0 f0, WireSpec width gs w0 d0 f0 → WireSpec width gs' w0 d0 f0) ∧
      WireSpec width gs' w true (fun _ => c) := by
  let g : Gate := if c then ⟨GateOp.and, []⟩ else ⟨GateOp.or, []⟩
  have hnl : nonlinear g = false := by cases c <;> rfl
  have hinp : g.inputs = [] := by cases c <;> rfl
  have hstep := append_gate gs hgood g (by rw [hinp]; simp) (by rw [hinp]; intro _ h; cases h)
    (by rw [hinp, hnl]; simp)
  refine ⟨gs ++ [g], width + gs.length, hstep.1, by rw [hstep.2.1, hnl]; rfl, hstep.2.2.1, ?_⟩
  have hspec := hstep.2.2.2
  have hd : decide ((g.inputs.map (fun a => (depthList width gs).getD a 0)).foldr max 0 + (nonlinear g).toNat = 0) = true := by
    rw [hinp, hnl]; rfl
  have heval : (fun inp => g.op.eval (g.inputs.map fun a => (Circuit.wires ⟨gs, 0⟩ inp).getD a false)) = (fun _ => c) := by
    funext inp; cases c <;> rfl
  rw [hd, heval] at hspec; exact hspec

lemma addNot {width : Nat} (gs : List Gate) (hgood : Good width gs)
    {a : Nat} {d0 : Bool} {fa : List Bool → Bool} (ha : WireSpec width gs a d0 fa) :
    ∃ (gs' : List Gate) (w : Nat),
      Good width gs' ∧ gs'.countP nonlinear = gs.countP nonlinear ∧
      (∀ w0 d0' f0, WireSpec width gs w0 d0' f0 → WireSpec width gs' w0 d0' f0) ∧
      WireSpec width gs' w d0 (fun inp => !(fa inp)) := by
  let g : Gate := ⟨GateOp.not, [a]⟩
  have hnl : nonlinear g = false := rfl
  have hda_le : (depthList width gs).getD a 0 ≤ 1 :=
    le_trans (depthList_getD_le_depth width gs a) hgood.2.2
  have hstep := append_gate gs hgood g (by simp [g]) (by intro i hi; simp [g] at hi; subst hi; exact ha.1)
    (by simp only [g, hnl, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.max_zero, Bool.toNat_false, Nat.add_zero]; exact hda_le)
  refine ⟨gs ++ [g], width + gs.length, hstep.1, by rw [hstep.2.1, hnl]; rfl, hstep.2.2.1, ?_⟩
  refine ⟨hstep.2.2.2.1, fun hd0 => ?_, fun inp hlen => ?_⟩
  · have hda0 : (depthList width gs).getD a 0 = 0 := ha.2.1 hd0
    exact hstep.2.2.2.2.1 (by simp only [g, hnl, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.max_zero, Bool.toNat_false, Nat.add_zero, hda0]; rfl)
  · rw [hstep.2.2.2.2.2 inp hlen]; simp only [g, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, ha.2.2 inp hlen]

lemma addXor {width : Nat} (gs : List Gate) (hgood : Good width gs)
    {a b : Nat} {d0a d0b : Bool} {fa fb : List Bool → Bool}
    (ha : WireSpec width gs a d0a fa) (hb : WireSpec width gs b d0b fb) :
    ∃ (gs' : List Gate) (w : Nat),
      Good width gs' ∧ gs'.countP nonlinear = gs.countP nonlinear ∧
      (∀ w0 d0' f0, WireSpec width gs w0 d0' f0 → WireSpec width gs' w0 d0' f0) ∧
      WireSpec width gs' w (d0a && d0b) (fun inp => xor (fa inp) (fb inp)) := by
  let g1 : Gate := ⟨GateOp.mod 2, [a, b]⟩
  have hnl1 : nonlinear g1 = false := rfl
  have hda_le : (depthList width gs).getD a 0 ≤ 1 := le_trans (depthList_getD_le_depth width gs a) hgood.2.2
  have hdb_le : (depthList width gs).getD b 0 ≤ 1 := le_trans (depthList_getD_le_depth width gs b) hgood.2.2
  have hstep1 := append_gate gs hgood g1 (by simp [g1])
    (by intro i hi; simp [g1] at hi; rcases hi with rfl | rfl; exact ha.1; exact hb.1)
    (by simp only [g1, hnl1, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.max_zero, Bool.toNat_false, Nat.add_zero, Nat.max_le]; exact ⟨hda_le, hdb_le⟩)
  have hxnor : WireSpec width (gs ++ [g1]) (width + gs.length) (d0a && d0b) (fun inp => !(xor (fa inp) (fb inp))) := by
    refine ⟨hstep1.2.2.2.1, fun hd => ?_, fun inp hlen => ?_⟩
    · simp only [Bool.and_eq_true] at hd
      have hda0 := ha.2.1 hd.1; have hdb0 := hb.2.1 hd.2
      exact hstep1.2.2.2.2.1 (by simp only [g1, hnl1, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.max_zero, Bool.toNat_false, Nat.add_zero, hda0, hdb0]; rfl)
    · rw [hstep1.2.2.2.2.2 inp hlen]
      simp only [g1, List.map_cons, List.map_nil, ha.2.2 inp hlen, hb.2.2 inp hlen]
      cases fa inp <;> cases fb inp <;> rfl
  rcases addNot (gs ++ [g1]) hstep1.1 hxnor with ⟨gs2, w2, hg2, hc2, hp2, hw2⟩
  refine ⟨gs2, w2, hg2, by rw [hc2, hstep1.2.1, hnl1]; rfl, fun w0 d0' f0 h0 => hp2 w0 d0' f0 (hstep1.2.2.1 w0 d0' f0 h0), ?_⟩
  have heq : (fun inp => !(!(xor (fa inp) (fb inp)))) = (fun inp => xor (fa inp) (fb inp)) := by
    funext inp; exact Bool.not_not _
  rw [heq] at hw2; exact hw2

lemma addAnd0 {width : Nat} (gs : List Gate) (hgood : Good width gs)
    {a b : Nat} {fa fb : List Bool → Bool}
    (ha : WireSpec width gs a true fa) (hb : WireSpec width gs b true fb) :
    ∃ (gs' : List Gate) (w : Nat),
      Good width gs' ∧ gs'.countP nonlinear = gs.countP nonlinear + 1 ∧
      (∀ w0 d0' f0, WireSpec width gs w0 d0' f0 → WireSpec width gs' w0 d0' f0) ∧
      WireSpec width gs' w false (fun inp => fa inp && fb inp) := by
  let g : Gate := ⟨GateOp.and, [a, b]⟩
  have hnl : nonlinear g = true := rfl
  have hda0 := ha.2.1 rfl; have hdb0 := hb.2.1 rfl
  have hstep := append_gate gs hgood g (by simp [g])
    (by intro i hi; simp [g] at hi; rcases hi with rfl | rfl; exact ha.1; exact hb.1)
    (by simp only [g, hnl, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.max_zero, Bool.toNat_true, hda0, hdb0]; omega)
  refine ⟨gs ++ [g], width + gs.length, hstep.1, by rw [hstep.2.1, hnl]; rfl, hstep.2.2.1, ?_⟩
  refine ⟨hstep.2.2.2.1, (fun h => by cases h), fun inp hlen => ?_⟩
  rw [hstep.2.2.2.2.2 inp hlen]
  simp only [g, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true,
    ha.2.2 inp hlen, hb.2.2 inp hlen]

lemma addAffine {width M : Nat} (gs : List Gate) (hgood : Good width gs)
    (d0 : Bool) (ws : Fin M → Nat) (vals : Fin M → List Bool → Bool)
    (hws : ∀ p, WireSpec width gs (ws p) d0 (vals p))
    (c : Bool) (coeff : Fin M → Bool) :
    ∃ (gs' : List Gate) (w : Nat),
      Good width gs' ∧ gs'.countP nonlinear = gs.countP nonlinear ∧
      (∀ w0 d0' f0, WireSpec width gs w0 d0' f0 → WireSpec width gs' w0 d0' f0) ∧
      WireSpec width gs' w d0 (fun inp => xor c (xorFin (fun p => coeff p && vals p inp))) := by
  induction M generalizing gs with
  | zero =>
    rcases addConst gs hgood c with ⟨gs1, w1, hg1, hc1, hp1, hw1⟩
    refine ⟨gs1, w1, hg1, hc1, hp1, ?_⟩
    refine ⟨hw1.1, fun _ => hw1.2.1 rfl, fun inp hlen => ?_⟩
    rw [hw1.2.2 inp hlen]; exact (Bool.xor_false c).symm
  | succ M ih =>
    rcases ih gs hgood (fun p => ws p.castSucc) (fun p => vals p.castSucc)
      (fun p => hws p.castSucc) (fun p => coeff p.castSucc) with ⟨gs1, w1, hg1, hc1, hp1, hw1⟩
    cases hcl : coeff (Fin.last M)
    · refine ⟨gs1, w1, hg1, hc1, hp1, ?_⟩
      refine ⟨hw1.1, hw1.2.1, fun inp hlen => ?_⟩
      rw [hw1.2.2 inp hlen]; dsimp only; rw [xorFin_succ, hcl, Bool.false_and, Bool.xor_false]
    · have hw_last : WireSpec width gs1 (ws (Fin.last M)) d0 (vals (Fin.last M)) := hp1 _ _ _ (hws (Fin.last M))
      rcases addXor gs1 hg1 hw1 hw_last with ⟨gs2, w2, hg2, hc2, hp2, hw2⟩
      have hd0_eq : (d0 && d0) = d0 := by cases d0 <;> rfl
      rw [hd0_eq] at hw2
      refine ⟨gs2, w2, hg2, by rw [hc2, hc1], fun w0 d0' f0 h0 => hp2 _ _ _ (hp1 _ _ _ h0), ?_⟩
      refine ⟨hw2.1, hw2.2.1, fun inp hlen => ?_⟩
      rw [hw2.2.2 inp hlen]; dsimp only; rw [xorFin_succ, hcl, Bool.true_and, Bool.xor_assoc]

lemma addAffineFn {width M : Nat} (gs : List Gate) (hgood : Good width gs)
    (d0 : Bool) (ws : Fin M → Nat) (vals : Fin M → List Bool → Bool)
    (hws : ∀ p, WireSpec width gs (ws p) d0 (vals p))
    (f : (Fin M → Bool) → Bool) (hf : IsAffine f) :
    ∃ (gs' : List Gate) (w : Nat),
      Good width gs' ∧ gs'.countP nonlinear = gs.countP nonlinear ∧
      (∀ w0 d0' f0, WireSpec width gs w0 d0' f0 → WireSpec width gs' w0 d0' f0) ∧
      WireSpec width gs' w d0 (fun inp => f (fun p => vals p inp)) := by
  rcases hf with ⟨c, coeff, hfe⟩
  rcases addAffine gs hgood d0 ws vals hws c coeff with ⟨gs1, w1, hg1, hc1, hp1, hw1⟩
  refine ⟨gs1, w1, hg1, hc1, hp1, ?_⟩
  have heq : (fun inp => xor c (xorFin (fun p => coeff p && vals p inp))) =
      (fun inp => f (fun p => vals p inp)) := by funext inp; exact (hfe _).symm
  rw [heq] at hw1; exact hw1

lemma addAffineVec {width M K : Nat} (gs : List Gate) (hgood : Good width gs)
    (d0 : Bool) (ws : Fin M → Nat) (vals : Fin M → List Bool → Bool)
    (hws : ∀ p, WireSpec width gs (ws p) d0 (vals p))
    (fs : Fin K → (Fin M → Bool) → Bool) (hfs : ∀ i, IsAffine (fs i)) :
    ∃ (gs' : List Gate) (outs : Fin K → Nat),
      Good width gs' ∧ gs'.countP nonlinear = gs.countP nonlinear ∧
      (∀ w0 d0' f0, WireSpec width gs w0 d0' f0 → WireSpec width gs' w0 d0' f0) ∧
      ∀ i : Fin K, WireSpec width gs' (outs i) d0 (fun inp => fs i (fun p => vals p inp)) := by
  induction K generalizing gs with
  | zero => exact ⟨gs, fun i => i.elim0, hgood, rfl, fun _ _ _ h => h, fun i => i.elim0⟩
  | succ K ih =>
    rcases ih gs hgood hws (fun i => fs i.castSucc) (fun i => hfs i.castSucc) with
      ⟨gs1, outs1, hg1, hc1, hp1, houts1⟩
    rcases addAffineFn gs1 hg1 d0 ws vals (fun p => hp1 _ _ _ (hws p)) (fs (Fin.last K)) (hfs (Fin.last K)) with
      ⟨gs2, w2, hg2, hc2, hp2, hw2⟩
    refine ⟨gs2, fun i => if hi : i.val < K then outs1 ⟨i.val, hi⟩ else w2, hg2, by rw [hc2, hc1],
      fun w0 d0' f0 h0 => hp2 _ _ _ (hp1 _ _ _ h0), fun i => ?_⟩
    by_cases hi : i.val < K
    · dsimp only; rw [dite_pos hi]
      have hie : (⟨i.val, hi⟩ : Fin K).castSucc = i := Fin.ext rfl
      have hfe : (fun inp => fs (⟨i.val, hi⟩ : Fin K).castSucc (fun p => vals p inp)) =
          (fun inp => fs i (fun p => vals p inp)) := by rw [hie]
      rw [← hfe]; exact hp2 _ _ _ (houts1 ⟨i.val, hi⟩)
    · dsimp only; rw [dite_neg hi]
      have hie : Fin.last K = i := Fin.ext (by simp [Fin.last]; omega)
      rw [← hie]; exact hw2

lemma addAndVec {width M S : Nat} (gs : List Gate) (hgood : Good width gs)
    (ws : Fin M → Nat) (vals : Fin M → List Bool → Bool)
    (hws : ∀ p, WireSpec width gs (ws p) true (vals p))
    (A B : Fin S → (Fin M → Bool) → Bool) (hA : ∀ s, IsAffine (A s)) (hB : ∀ s, IsAffine (B s)) :
    ∃ (gs' : List Gate) (prods : Fin S → Nat),
      Good width gs' ∧ gs'.countP nonlinear = gs.countP nonlinear + S ∧
      (∀ w0 d0' f0, WireSpec width gs w0 d0' f0 → WireSpec width gs' w0 d0' f0) ∧
      ∀ s : Fin S, WireSpec width gs' (prods s) false (fun inp => A s (fun p => vals p inp) && B s (fun p => vals p inp)) := by
  induction S generalizing gs with
  | zero => exact ⟨gs, fun s => s.elim0, hgood, rfl, fun _ _ _ h => h, fun s => s.elim0⟩
  | succ S ih =>
    rcases ih gs hgood hws (fun s => A s.castSucc) (fun s => B s.castSucc)
      (fun s => hA s.castSucc) (fun s => hB s.castSucc) with ⟨gs1, p1, hg1, hc1, hp1, hsp1⟩
    rcases addAffineFn gs1 hg1 true ws vals (fun p => hp1 _ _ _ (hws p)) (A (Fin.last S)) (hA (Fin.last S)) with
      ⟨gs2, wa, hg2, hc2, hp2, hwa⟩
    rcases addAffineFn gs2 hg2 true ws vals (fun p => hp2 _ _ _ (hp1 _ _ _ (hws p))) (B (Fin.last S)) (hB (Fin.last S)) with
      ⟨gs3, wb, hg3, hc3, hp3, hwb⟩
    rcases addAnd0 gs3 hg3 (hp3 _ _ _ hwa) hwb with ⟨gs4, wp, hg4, hc4, hp4, hwp⟩
    have hp_all : ∀ w0 d0' f0, WireSpec width gs w0 d0' f0 → WireSpec width gs4 w0 d0' f0 :=
      fun w0 d0' f0 h0 => hp4 _ _ _ (hp3 _ _ _ (hp2 _ _ _ (hp1 _ _ _ h0)))
    refine ⟨gs4, fun s => if hs : s.val < S then p1 ⟨s.val, hs⟩ else wp, hg4,
      by rw [hc4, hc3, hc2, hc1]; omega, hp_all, fun s => ?_⟩
    by_cases hs : s.val < S
    · dsimp only; rw [dite_pos hs]
      have hse : (⟨s.val, hs⟩ : Fin S).castSucc = s := Fin.ext rfl
      have hfe : (fun inp => A (⟨s.val, hs⟩ : Fin S).castSucc (fun p => vals p inp) &&
            B (⟨s.val, hs⟩ : Fin S).castSucc (fun p => vals p inp)) =
          (fun inp => A s (fun p => vals p inp) && B s (fun p => vals p inp)) := by rw [hse]
      rw [← hfe]; exact hp4 _ _ _ (hp3 _ _ _ (hp2 _ _ _ (hsp1 ⟨s.val, hs⟩)))
    · dsimp only; rw [dite_neg hs]
      have hse : Fin.last S = s := Fin.ext (by simp [Fin.last]; omega)
      rw [← hse]; exact hwp


def ySite {r k : Nat} (hr : 2 ≤ r) (hk3 : k = 3*r) (p : Fin (k-3)) : Fin k :=
  ⟨if p.val = 0 then 0 else if p.val = 1 then 2 else p.val + 2, by split_ifs <;> omega⟩

lemma wOfY_site {r k : Nat} (hr : 2 ≤ r) (hk3 : k = 3*r) (y : Fin (k-3) → Bool) (p : Fin (k-3)) :
    wOfY hr hk3 y (ySite hr hk3 p) = y p := by
  by_cases h0 : p.val = 0
  · have h : ySite hr hk3 p = ⟨0, by omega⟩ := Fin.ext (by simp [ySite,h0])
    rw [h]
    unfold wOfY
    simp only [if_pos rfl]
    exact congrArg y (Fin.ext h0.symm)
  · by_cases h1 : p.val = 1
    · have h : ySite hr hk3 p = ⟨2, by omega⟩ := Fin.ext (by simp [ySite,h0,h1])
      rw [h]
      unfold wOfY
      simp only [Fin.val_mk, if_neg (by decide : (2 : Nat) ≠ 0), if_neg (by decide : (2 : Nat) ≠ 1), if_pos rfl]
      exact congrArg y (Fin.ext h1.symm)
    · have h : ySite hr hk3 p = ⟨p.val+2, by omega⟩ := Fin.ext (by simp [ySite,h0,h1])
      rw [h]
      unfold wOfY
      dsimp only
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), dif_pos (by omega)]
      exact congrArg y (Fin.ext (by dsimp only; omega))

lemma wOfY_recovers {r k : Nat} (hr : 2 ≤ r) (hk3 : k = 3*r) (w : Fin k → Bool)
    (h3 : w ⟨3, by omega⟩ = false)
    (h01 : resSum r hk3 w 0 (by omega) = resSum r hk3 w 1 (by omega))
    (h02 : resSum r hk3 w 0 (by omega) = resSum r hk3 w 2 (by omega)) :
    wOfY hr hk3 (fun p => w (ySite hr hk3 p)) = w := by
  let w' := wOfY hr hk3 (fun p => w (ySite hr hk3 p))
  have heq : ∀ i : Fin k, i.val ≠ 1 → i.val ≠ k-1 → w' i = w i := by
    intro i h1 hl
    by_cases h3i : i.val = 3
    · have he : i = ⟨3, by omega⟩ := Fin.ext h3i
      rw [he, h3]
      exact wOfY_3 hr hk3 _
    have hsite : ∃ p : Fin (k-3), ySite hr hk3 p = i := by
      by_cases h0 : i.val = 0
      · refine ⟨⟨0, by omega⟩, Fin.ext ?_⟩
        simpa [ySite] using h0.symm
      · by_cases h2 : i.val = 2
        · refine ⟨⟨1, by omega⟩, Fin.ext ?_⟩
          simpa [ySite] using h2.symm
        · have hp : i.val - 2 < k-3 := by omega
          refine ⟨⟨i.val-2, hp⟩, Fin.ext ?_⟩
          have hp0 : i.val-2 ≠ 0 := by omega
          have hp1 : i.val-2 ≠ 1 := by omega
          simpa [ySite, hp0, hp1] using (show i.val-2+2 = i.val by omega)
    rcases hsite with ⟨p, rfl⟩
    exact wOfY_site hr hk3 _ p
  have hres := wOfY_resSum hr hk3 (fun p => w (ySite hr hk3 p))
  change resSum r hk3 w' 0 (by omega) = _ ∧ resSum r hk3 w' 0 (by omega) = _ at hres
  have hz : resSum r hk3 w' 0 (by omega) = resSum r hk3 w 0 (by omega) := by
    apply xorFin_congr
    intro j
    apply heq <;> dsimp only <;> omega
  have h1 : w' ⟨1, by omega⟩ = w ⟨1, by omega⟩ := by
    have h : resSum r hk3 w' 1 (by omega) = resSum r hk3 w 1 (by omega) := hres.1.symm.trans (hz.trans h01)
    unfold resSum at h
    rw [xorFin_first (by omega) (fun j => w' ⟨3*j.val+1, by omega⟩),
      xorFin_first (by omega) (fun j => w ⟨3*j.val+1, by omega⟩)] at h
    dsimp only [Nat.mul_zero, Nat.zero_add] at h
    have hp : xorFin (fun j : Fin (r-1) => w' ⟨3 * (j.val+1) + 1, by omega⟩) =
        xorFin (fun j : Fin (r-1) => w ⟨3 * (j.val+1) + 1, by omega⟩) := by
      apply xorFin_congr; intro j; apply heq <;> dsimp only <;> omega
    rw [hp] at h
    exact (by decide : ∀ a b c : Bool, xor a c = xor b c → a = b) _ _ _ h
  have hl : w' ⟨k-1, by omega⟩ = w ⟨k-1, by omega⟩ := by
    have h : resSum r hk3 w' 2 (by omega) = resSum r hk3 w 2 (by omega) := hres.2.symm.trans (hz.trans h02)
    unfold resSum at h
    rw [xorFin_last (by omega) (fun j => w' ⟨3*j.val+2, by omega⟩),
      xorFin_last (by omega) (fun j => w ⟨3*j.val+2, by omega⟩)] at h
    have hp : xorFin (fun j : Fin (r-1) => w' ⟨3 * j.val + 2, by omega⟩) =
        xorFin (fun j : Fin (r-1) => w ⟨3 * j.val + 2, by omega⟩) := by
      apply xorFin_congr; intro j; apply heq <;> dsimp only <;> omega
    have hi : (⟨3 * (r-1) + 2, by omega⟩ : Fin k) = ⟨k-1, by omega⟩ := Fin.ext (by dsimp only; omega)
    rw [hp, hi] at h
    exact (by decide : ∀ a b c : Bool, xor c a = xor c b → a = b) _ _ _ h
  funext i
  by_cases hi : i.val = 1
  · simpa only [show i = ⟨1, by omega⟩ from Fin.ext hi] using h1
  by_cases hil : i.val = k-1
  · simpa only [show i = ⟨k-1, by omega⟩ from Fin.ext hil] using hl
  exact heq i hi hil

abbrev KeyCoords (k : Nat) := (Fin (k-3) → Bool) × Bool × Bool × Bool

def keyEncode {r k : Nat} (hk : 0 < k) (hr : 2 ≤ r) (hk3 : k = 3*r)
    (u x : Fin k → Bool) : KeyCoords k :=
  let d := diffFn hk u x
  let t := tOfD hr hk3 d
  (fun p => t (ySite hr hk3 p),
    decide (((neededSet r k).filter (fun i => row hk u x i = true)).card % 2 = 1),
    row hk u x ⟨0, hk⟩, row hk u x ⟨k-1, by omega⟩)

def keyDecode {r k : Nat} (hk : 0 < k) (hr : 2 ≤ r) (hk3 : k = 3*r)
    (u : Fin k → Bool) (a : KeyCoords k) : Fin k → Bool :=
  let w0 := wOfY hr hk3 a.1
  let b := xor a.2.1 (xor (Qp hk r w0) (linP hk r u w0))
  let x0 := xor a.2.2.1 (xor (w0 ⟨0, hk⟩) (Q0 hr hk3 w0))
  let xk := xor a.2.2.2 (xor b (xor (w0 ⟨k-1, by omega⟩) (Qk hr hk3 w0)))
  let w := add w0 (fun i => b && decide (3 ≤ i.val))
  let z := zOf w (xor xk (u ⟨0, hk⟩)) (xor x0 (u ⟨1, by omega⟩))
  fun i => xor (z (ix hk (i.val+1))) (u (ix hk (i.val+1)))

lemma keyDecode_encode {r k : Nat} (hk : 0 < k) (hr : 2 ≤ r) (hk3 : k = 3*r)
    (u x : Fin k → Bool) : keyDecode hk hr hk3 u (keyEncode hk hr hk3 u x) = x := by
  have h := tOfD_diff hk hr hk3 u x
  dsimp only at h
  have hw := wOfY_recovers hr hk3 _ h.1 h.2.2.1 h.2.2.2
  unfold keyDecode keyEncode
  dsimp only
  rw [hw]
  exact (funext (recovery_from_record hk hr hk3 u x)).symm

lemma mix_ix3_decode {r k : Nat} (hk : 0 < k) (hr : 2 ≤ r) (hk3 : k = 3*r)
    (u : Fin k → Bool) (a : KeyCoords k) :
    mix hk (rot hk (keyDecode hk hr hk3 u a)) (ix hk 3) =
      xor (Qp hk r (wOfY hr hk3 a.1))
        (xor a.2.1 (xor (linP hk r u (wOfY hr hk3 a.1)) (mix hk u (ix hk 3)))) := by
  have hs := wOfY_resSum hr hk3 a.1
  have hrec := (row_recovery hk hr hk3 u (wOfY hr hk3 a.1)
    (xor a.2.1 (xor (Qp hk r (wOfY hr hk3 a.1)) (linP hk r u (wOfY hr hk3 a.1))))
    (xor (xor a.2.2.2 (xor (xor a.2.1 (xor (Qp hk r (wOfY hr hk3 a.1)) (linP hk r u (wOfY hr hk3 a.1))))
      (xor (wOfY hr hk3 a.1 ⟨k-1, by omega⟩) (Qk hr hk3 (wOfY hr hk3 a.1))))) (u ⟨0, hk⟩))
    (xor (xor a.2.2.1 (xor (wOfY hr hk3 a.1 ⟨0, hk⟩) (Q0 hr hk3 (wOfY hr hk3 a.1)))) (u ⟨1, by omega⟩)) hs.1 hs.2).1
  change mix hk (add u (rot hk (keyDecode hk hr hk3 u a))) =
    add (wOfY hr hk3 a.1) (fun i => xor a.2.1 (xor (Qp hk r (wOfY hr hk3 a.1)) (linP hk r u (wOfY hr hk3 a.1))) && decide (3 ≤ i.val)) at hrec
  rw [mix_add hk] at hrec
  have h := congrFun hrec (ix hk 3)
  have hix : ix hk 3 = ⟨3, by omega⟩ := ix_eq_of_lt hk (by omega)
  dsimp only [add] at h
  rw [show wOfY hr hk3 a.1 (ix hk 3) = false by rw [hix]; exact wOfY_3 hr hk3 _,
    show decide (3 ≤ (ix hk 3).val) = true by rw [hix]; rfl] at h
  simp only [Bool.and_true, Bool.false_xor] at h
  exact (by decide : ∀ q p l z f : Bool, xor z f = xor p (xor q l) → f = xor q (xor p (xor l z))) _ _ _ _ _ h

noncomputable def keyEquiv {r k : Nat} (hk : 0 < k) (hr : 2 ≤ r) (hk3 : k = 3*r)
    (u : Fin k → Bool) : (Fin k → Bool) ≃ KeyCoords k := by
  classical
  have hi : Function.Injective (keyEncode hk hr hk3 u) :=
    (show Function.LeftInverse (keyDecode hk hr hk3 u) (keyEncode hk hr hk3 u) from keyDecode_encode hk hr hk3 u).injective
  have hc : Fintype.card (Fin k → Bool) = Fintype.card (KeyCoords k) := by
    simp only [KeyCoords, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Fintype.card_prod]
    rw [show k = (k-3)+3 by omega, pow_add]
    congr 1
  exact Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card _).2 ⟨hi, hc⟩)


abbrev bits (d : Nat) := Fin d → Bool

def splitKey {k : Nat} (hk : 3 ≤ k) (y : bits k) : KeyCoords k :=
  (fun p => y ⟨p.val, by omega⟩, y ⟨k-3, by omega⟩, y ⟨k-2, by omega⟩, y ⟨k-1, by omega⟩)

noncomputable def splitKeyEquiv {k : Nat} (hk : 3 ≤ k) : bits k ≃ KeyCoords k := by
  classical
  apply Equiv.ofBijective (splitKey hk)
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro a b e
    funext i
    by_cases hi : i.val < k-3
    · exact congrFun (congrArg Prod.fst e) ⟨i.val, hi⟩
    · by_cases h0 : i.val = k-3
      · have he : i = ⟨k-3, by omega⟩ := Fin.ext h0
        rw [he]
        exact congrArg (fun q : KeyCoords k => q.2.1) e
      · by_cases h1 : i.val = k-2
        · have he : i = ⟨k-2, by omega⟩ := Fin.ext h1
          rw [he]
          exact congrArg (fun q : KeyCoords k => q.2.2.1) e
        · have he : i = ⟨k-1, by omega⟩ := Fin.ext (show i.val = k-1 by omega)
          rw [he]
          exact congrArg (fun q : KeyCoords k => q.2.2.2) e
  · simp only [KeyCoords, bits, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Fintype.card_prod]
    rw [show k = (k-3)+3 by omega, pow_add]
    congr 1

noncomputable def inputChart {r k n : Nat} (hk : 0 < k) (hr : 2 ≤ r) (hk3 : k = 3*r)
    (u : Fin k → Bool) : bits (n*k) ≃ (Fin n → bits k) where
  toFun Y j := (keyEquiv hk hr hk3 u).symm (splitKey (by omega) (fun i => Y (finProdFinEquiv (j,i))))
  invFun x a := (splitKeyEquiv (by omega)).symm (keyEquiv hk hr hk3 u (x (finProdFinEquiv.symm a).1)) (finProdFinEquiv.symm a).2
  left_inv Y := by
    funext a
    obtain ⟨⟨j,i⟩, rfl⟩ := finProdFinEquiv.surjective a
    simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    exact congrFun ((splitKeyEquiv (by omega : 3 ≤ k)).symm_apply_apply (fun i => Y (finProdFinEquiv (j,i)))) i
  right_inv x := by
    funext j
    simp only [Equiv.symm_apply_apply]
    exact congrArg (keyEquiv hk hr hk3 u).symm ((splitKeyEquiv (by omega : 3 ≤ k)).apply_symm_apply (keyEquiv hk hr hk3 u (x j))) |>.trans
      ((keyEquiv hk hr hk3 u).symm_apply_apply (x j))

def normDiff {k : Nat} (hk : 0 < k) (w : bits k) (i : Fin k) : Bool :=
  if i.val = 0 then false
  else if i.val = 1 then !(w (ix hk 2))
  else if i.val = 2 then xor (w (ix hk 3)) (w (ix hk 4))
  else if i.val < k - 2 then !(xor (w (ix hk (i.val + 1))) (w (ix hk (i.val + 2))))
  else if i.val = k - 2 then !(w (ix hk 0))
  else true

lemma diff_norm {r k : Nat} (hk : 0 < k) (hr : 2 ≤ r) (hk3 : k = 3*r) (u x : bits k) (i : Fin k) :
    diffFn hk u x i = normDiff hk (wOfY hr hk3 (keyEncode hk hr hk3 u x).1) i := by
  have h := tOfD_diff hk hr hk3 u x
  dsimp only at h
  have hw := wOfY_recovers hr hk3 _ h.1 h.2.2.1 h.2.2.2
  unfold keyEncode
  dsimp only
  rw [hw]
  rw [diffFn_eq hk hr hk3, h.2.1]
  unfold normDiff
  split_ifs with h0 h1 h2 hlt hkl
  · rfl
  · rw [ix_eq_of_lt hk (by omega : 2 < k)]; simp [add]
  · rw [ix_eq_of_lt hk (by omega : 3 < k), ix_eq_of_lt hk (by omega : 4 < k)]
    simp only [add, decide_true, Bool.and_true]
    exact (by decide : ∀ a b c : Bool, xor (xor a c) (xor b c) = xor a b) _ _ _
  · rw [ix_eq_of_lt hk (by omega : i.val+1 < k), ix_eq_of_lt hk (by omega : i.val+2 < k)]
    simp only [add, decide_eq_true (by omega : 3 ≤ i.val+1), decide_eq_true (by omega : 3 ≤ i.val+2), Bool.and_true]
    exact congrArg (!·) ((by decide : ∀ a b c : Bool, xor (xor a c) (xor b c) = xor a b) _ _ _)
  · rw [ix_eq_of_lt hk hk]; simp [add]
  · rfl

lemma normDiff_aff {k d : Nat} (hk : 0 < k) (W : bits d → bits k)
    (hW : ∀ i, IsAffine (fun Y => W Y i)) (i : Fin k) : IsAffine (fun Y => normDiff hk (W Y) i) := by
  unfold normDiff
  split_ifs
  · exact isAffine_const false
  · exact isAffine_not (hW _)
  · exact isAffine_xor (hW _) (hW _)
  · exact isAffine_not (isAffine_xor (hW _) (hW _))
  · exact isAffine_not (hW _)
  · exact isAffine_const true

def dataRows {k n : Nat} (hk : 0 < k) (r : Nat) (u : bits k) (x : Fin n → bits k) : List Bool :=
  (List.ofFn (fun j : Fin n => recordFn hk r u (x j))).flatten

lemma dataRows_len {k n : Nat} (hk : 0 < k) (r : Nat) (u : bits k) (x : Fin n → bits k) :
    (dataRows hk r u x).length = n*(k+3) :=
  flatten_ofFn_length _ (fun j => recordFn_length hk r u (x j))

lemma dataRows_get {k n : Nat} (hk : 0 < k) (r : Nat) (u : bits k) (x : Fin n → bits k)
    (j : Fin n) (p : Fin (k+3)) : (dataRows hk r u x).getD (finProdFinEquiv (j,p)).val false =
      (recordFn hk r u (x j)).getD p.val false := by
  have h : (finProdFinEquiv (j,p)).val = j.val * (k+3) + p.val := by change _ + _ = _; ac_rfl
  rw [h]
  exact flatten_ofFn_getD _ (fun j => recordFn_length hk r u (x j)) j p

def coordBlock {k n : Nat} (h : 3 ≤ k) (Y : bits (n*k)) (j : Fin n) : KeyCoords k :=
  splitKey h (fun i => Y (finProdFinEquiv (j,i)))

lemma inputChart_encode {r k n : Nat} (hk : 0 < k) (hr : 2 ≤ r) (hk3 : k = 3*r) (u : bits k)
    (Y : bits (n*k)) (j : Fin n) :
    keyEncode hk hr hk3 u (inputChart hk hr hk3 u Y j) = coordBlock (by omega) Y j :=
  (keyEquiv hk hr hk3 u).apply_symm_apply _

lemma dataRows_aff {r k n : Nat} (hk : 0 < k) (hr : 2 ≤ r) (hk3 : k = 3*r) (u : bits k) (i : Nat) :
    IsAffine (fun Y : bits (n*k) => (dataRows hk r u (inputChart hk hr hk3 u Y)).getD i false) := by
  by_cases hi : i < n*(k+3)
  · let p : Fin n × Fin (k+3) := finProdFinEquiv.symm ⟨i,hi⟩
    have he : (finProdFinEquiv p).val = i := congrArg Fin.val (finProdFinEquiv.apply_symm_apply ⟨i,hi⟩)
    have hget : (fun Y : bits (n*k) => (dataRows hk r u (inputChart hk hr hk3 u Y)).getD i false) =
        (fun Y : bits (n*k) => (recordFn hk r u (inputChart hk hr hk3 u Y p.1)).getD p.2.val false) := by
      funext Y
      exact he ▸ dataRows_get hk r u (inputChart hk hr hk3 u Y) p.1 p.2
    rw [hget]
    by_cases hp : p.2.val < k
    · have he' : (fun Y : bits (n*k) => (recordFn hk r u (inputChart hk hr hk3 u Y p.1)).getD p.2.val false) =
          (fun Y : bits (n*k) => normDiff hk (wOfY hr hk3 (coordBlock (by omega) Y p.1).1) ⟨p.2.val,hp⟩) := by
        funext Y
        rw [recordFn_getD_lt _ _ _ _ _ hp, diff_norm hk hr hk3, inputChart_encode hk hr hk3]
      rw [he']
      apply normDiff_aff
      intro a
      exact isAffine_comp (isAffine_wOfY hr hk3 a) (fun q => isAffine_coord _)
    · by_cases h0 : p.2.val = k
      · have hf (Y : bits (n*k)) :
            (recordFn hk r u (inputChart hk hr hk3 u Y p.1)).getD p.2.val false =
              (coordBlock (by omega) Y p.1).2.1 := by
          rw [h0, recordFn_getD_k]
          exact congrArg (fun a : KeyCoords k => a.2.1) (inputChart_encode hk hr hk3 u Y p.1)
        rw [funext hf]
        exact isAffine_coord _
      · by_cases h1 : p.2.val = k+1
        · have hf (Y : bits (n*k)) :
              (recordFn hk r u (inputChart hk hr hk3 u Y p.1)).getD p.2.val false =
                (coordBlock (by omega) Y p.1).2.2.1 := by
            rw [h1, recordFn_getD_k1]
            exact congrArg (fun a : KeyCoords k => a.2.2.1) (inputChart_encode hk hr hk3 u Y p.1)
          rw [funext hf]
          exact isAffine_coord _
        · have h2 : p.2.val = k+2 := by omega
          have hf (Y : bits (n*k)) :
              (recordFn hk r u (inputChart hk hr hk3 u Y p.1)).getD p.2.val false =
                (coordBlock (by omega) Y p.1).2.2.2 := by
            rw [h2, recordFn_getD_k2]
            exact congrArg (fun a : KeyCoords k => a.2.2.2) (inputChart_encode hk hr hk3 u Y p.1)
          rw [funext hf]
          exact isAffine_coord _
  · have h : (fun Y : bits (n*k) => (dataRows hk r u (inputChart hk hr hk3 u Y)).getD i false) = fun _ => false := by
      funext Y
      apply List.getD_eq_default
      rw [dataRows_len]
      omega
    rw [h]
    exact isAffine_const false
-- The basis minor for r ≥ 4 is the one from L_meta_42687.lean at
-- 036ab8b318851b49a3c9d09ef7f5972dd8c3d253. The parity mask at r = 3
-- has a separate full-size minor, since the mask is odd there.

lemma pol_Qp_eVec {r k : Nat} (hk : 0 < k) (hr3 : 3 ≤ r) (hk3 : k = 3 * r)
    (p q : Fin (k - 3)) :
    pol (fun y => Qp hk r (wOfY (by omega) hk3 y)) (eVec p) (eVec q) =
      CBit r (k - 3) (decide (r % 2 = 0)) (decide (r % 2 = 0)) p.val q.val := by
  have hr : 2 ≤ r := by omega
  by_cases he : r % 2 = 0
  · have h : (fun y => Qp hk r (wOfY hr hk3 y)) =
        (fun y => xor (xor (Q0 hr hk3 (wOfY hr hk3 y)) (Qk hr hk3 (wOfY hr hk3 y)))
          (QpMid hk hr hk3 (wOfY hr hk3 y))) := funext fun y => by
        simpa only [if_pos he] using Qp_eq_QpMid hk hr hk3 _ (wOfY_3 hr hk3 y)
    rw [h, pol_xor, pol_xor, pol_Q0_eVec, pol_Qk_eVec, pol_QpMid_eVec hk hr3 hk3]
    rw [CBit, decide_eq_true he, Bool.true_and, Bool.true_and, Bool.xor_comm (xor (B0Bit p.val q.val) (BkBit p.val q.val))]
  · have h : (fun y => Qp hk r (wOfY hr hk3 y)) =
        (fun y => QpMid hk hr hk3 (wOfY hr hk3 y)) := funext fun y => by
        simpa only [if_neg he, Bool.false_xor] using Qp_eq_QpMid hk hr hk3 _ (wOfY_3 hr hk3 y)
    rw [h, pol_QpMid_eVec hk hr3 hk3]
    simp [CBit, he]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
lemma inv_CBit_r3_odd : ∀ (c : Fin 6 → Bool),
    (∀ q : Fin 6, xorFin (fun i : Fin 6 => c i && CBit 3 6 false false i.val q.val) = false) →
    ∀ i : Fin 6, c i = false := by
  decide

lemma qpPolarMinor {r k : Nat} (hk : 0 < k) (hr3 : 3 ≤ r) (hk3 : k = 3 * r) :
    ∃ p : Fin (2 * r) → Fin (k - 3), ∀ c : Fin (2 * r) → Bool,
      (∀ j : Fin (2 * r), xorFin (fun i => c i &&
        pol (fun y => Qp hk r (wOfY (by omega) hk3 y)) (eVec (p i)) (eVec (p j))) = false) →
      ∀ i, c i = false := by
  by_cases h3 : r = 3
  · subst r; subst k
    refine ⟨id, fun c hc => inv_CBit_r3_odd c (fun j => ?_)⟩
    have h := hc j
    simp only [pol_Qp_eVec (r := 3) (k := 9) hk (by omega) rfl, id_eq] at h
    exact h
  · have hr4 : 4 ≤ r := by omega
    let δ := decide (r % 2 = 0)
    have hm : k - 3 = 3 * r - 3 := by omega
    have hp (i : Fin (2 * r)) : basisIdx4 r (k - 3) δ δ i < k - 3 := by
      unfold basisIdx4
      split_ifs with h
      · exact coreIdx_lt hr4 hm _ h
      · have he (e : Fin 4) : extraIdx (k - 3) δ δ e < k - 3 := by
          fin_cases e
          · simp [extraIdx]; omega
          · simp [extraIdx]; omega
          · simp [extraIdx]; split_ifs <;> omega
          · simp [extraIdx]; split_ifs <;> omega
        exact he _
    refine ⟨fun i => ⟨basisIdx4 r (k - 3) δ δ i, hp i⟩, fun c hc => ?_⟩
    apply inv_CBit_r4 hr4 hm δ δ c
    intro j
    simpa only [pol_Qp_eVec hk hr3 hk3] using hc j

private lemma qp_split_two {r : Nat} (hr : 2 ≤ r) (f : Fin r → Bool) :
    xorFin f = xor (f ⟨0, by omega⟩) (xor (f ⟨1, by omega⟩)
      (xorFin (fun j : Fin (r - 2) => f ⟨j.val + 2, by omega⟩))) := by
  rw [xorFin_first (by omega), xorFin_first (by omega)]
  refine congrArg (fun b => xor (f ⟨0, by omega⟩) (xor (f ⟨1, by omega⟩) b)) ?_
  refine xorFin_cast (by omega) _ _ (fun i hi h'i => ?_)
  exact congrArg f (Fin.ext (show i + 1 + 1 = i + 2 from by omega))

private lemma qp_d_relation {r k : Nat} (hr : 2 ≤ r) (hk3 : k = 3 * r)
    (y : Fin (k - 3) → Bool) :
    let w := wOfY hr hk3 y
    xor (w ⟨0, by omega⟩) (w ⟨2, by omega⟩) = xor (w ⟨5, by omega⟩)
      (xorFin (fun j : Fin (r - 2) => xor (w ⟨3 * (j.val + 2), by omega⟩)
        (w ⟨3 * (j.val + 2) + 2, by omega⟩))) := by
  dsimp only
  let w := wOfY hr hk3 y
  let u : Fin (r - 2) → Bool := fun j => w ⟨3 * (j.val + 2), by omega⟩
  let v : Fin (r - 2) → Bool := fun j => w ⟨3 * (j.val + 2) + 2, by omega⟩
  have hh := (wOfY_resSum hr hk3 y).2
  unfold resSum at hh
  simp only [qp_split_two hr] at hh
  change xor (w ⟨0, by omega⟩) (xor (w ⟨3, by omega⟩) (xorFin u)) =
    xor (w ⟨2, by omega⟩) (xor (w ⟨5, by omega⟩) (xorFin v)) at hh
  have hw : w ⟨3, by omega⟩ = false := wOfY_3 hr hk3 y
  rw [hw, Bool.false_xor] at hh
  change xor (w ⟨0, by omega⟩) (w ⟨2, by omega⟩) =
    xor (w ⟨5, by omega⟩) (xorFin (fun j => xor (u j) (v j)))
  rw [xorFin_xor]
  have balance (a b t u v : Bool) (h : xor a u = xor b (xor t v)) :
      xor a b = xor t (xor u v) := by
    cases a <;> cases b <;> cases t <;> cases u <;> cases v <;> simp_all
  exact balance _ _ _ _ _ hh

private lemma qp_xor_and (a b c : Bool) : (xor a b && c) = xor (a && c) (b && c) := by
  cases a <;> cases b <;> cases c <;> rfl

private lemma qp_pair_tail {m : Nat} (x d z : Fin m → Bool) (c : Bool) :
    xorFin (fun j => xor (x j && !(d j)) (z j)) =
      xor (xorFin (fun j => xor (x j) (z j)))
        (xor (xorFin (fun j => xor (x j) c && d j)) (c && xorFin d)) := by
  have h (j : Fin m) : xor (x j && !(d j)) (z j) =
       xor (xor (x j) (z j)) (xor (xor (x j) c && d j) (c && d j)) := by
    cases x j <;> cases d j <;> cases z j <;> cases c <;> rfl
  rw [xorFin_congr _ _ h, xorFin_xor (fun j => xor (x j) (z j)),
    xorFin_xor (fun j => xor (x j) c && d j), xorFin_and_left]

set_option maxHeartbeats 1000000 in
private lemma qp_pair_head (δ a b x v s t T P : Bool)
    (h : xor a b = xor v T) :
    xor (δ && xor (!s && b) (!a && s))
      (xor (xor x (!x && v)) (xor (!t && a) (xor P (δ && (s && T))))) =
    xor (xor (xor x v) (xor a (xor P (δ && xor b s))))
      (xor (xor x (δ && s) && v) (t && a)) := by
  cases δ <;> cases a <;> cases b <;> cases x <;> cases v <;> cases s <;> cases t <;>
    cases T <;> cases P <;> simp_all

lemma qpPairs {r k : Nat} (hk : 0 < k) (hr : 2 ≤ r) (hk3 : k = 3 * r) :
    ∃ (L R : Fin r → (Fin (k - 3) → Bool) → Bool) (A : (Fin (k - 3) → Bool) → Bool),
      (∀ i, IsAffine (L i)) ∧ (∀ i, IsAffine (R i)) ∧ IsAffine A ∧
      (∀ i, L i (fun _ => false) = false) ∧ (∀ i, R i (fun _ => false) = false) ∧
      ∀ y, Qp hk r (wOfY hr hk3 y) = xor (A y) (xorFin (fun i => L i y && R i y)) := by
  let Y := Fin (k - 3) → Bool
  let w : Fin k → Y → Bool := fun i y => wOfY hr hk3 y i
  let δ := decide (r % 2 = 0)
  let c : Y → Bool := fun y => δ && w ⟨1, by omega⟩ y
  let x : Fin (r - 2) → Y → Bool := fun j => w ⟨3 * (j.val + 2) + 1, by omega⟩
  let z : Fin (r - 2) → Y → Bool := fun j => w ⟨3 * (j.val + 2) + 2, by omega⟩
  let d : Fin (r - 2) → Y → Bool := fun j y => xor (w ⟨3 * (j.val + 2), by omega⟩ y) (z j y)
  let L : Fin r → Y → Bool := fun i =>
    if h₀ : i.val = 0 then fun y => xor (w ⟨4, by omega⟩ y) (c y)
    else if h₁ : i.val = 1 then w ⟨k - 1, by omega⟩
    else fun y => xor (x ⟨i.val - 2, by omega⟩ y) (c y)
  let R : Fin r → Y → Bool := fun i =>
    if h₀ : i.val = 0 then w ⟨5, by omega⟩
    else if h₁ : i.val = 1 then w ⟨0, hk⟩
    else d ⟨i.val - 2, by omega⟩
  let P : Y → Bool := fun y => xorFin (fun j => xor (x j y) (z j y))
  let A : Y → Bool := fun y => xor (xor (w ⟨4, by omega⟩ y) (w ⟨5, by omega⟩ y))
    (xor (w ⟨0, hk⟩ y) (xor (P y) (δ && xor (w ⟨2, by omega⟩ y) (w ⟨1, by omega⟩ y))))
  have hw (i : Fin k) : IsAffine (w i) := isAffine_wOfY hr hk3 i
  have hc : IsAffine c := isAffine_and_const δ (hw _)
  refine ⟨L, R, A, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; unfold L; split_ifs
    · exact isAffine_xor (hw _) hc
    · exact hw _
    · exact isAffine_xor (hw _) hc
  · intro i; unfold R; split_ifs
    · exact hw _
    · exact hw _
    · exact isAffine_xor (hw _) (hw _)
  · exact isAffine_xor (isAffine_xor (hw _) (hw _)) (isAffine_xor (hw _)
      (isAffine_xor (isAffine_xorFin _ (fun j => isAffine_xor (hw _) (hw _)))
        (isAffine_and_const δ (isAffine_xor (hw _) (hw _)))))
  · intro i; unfold L; split_ifs <;> simp [c, w, x, wOfY_zero]
  · intro i; unfold R; split_ifs <;> simp [d, z, w, wOfY_zero]
  · intro y
    have hprod : xorFin (fun i => L i y && R i y) =
        xor (xor (w ⟨4, by omega⟩ y) (c y) && w ⟨5, by omega⟩ y)
          (xor (w ⟨k - 1, by omega⟩ y && w ⟨0, hk⟩ y)
            (xorFin (fun j => xor (x j y) (c y) && d j y))) := by
      rw [qp_split_two hr]
      simp only [L, R, Fin.val_mk, dite_pos rfl, dite_neg (by decide : (1 : Nat) ≠ 0)]
      refine congrArg (fun b => xor (xor (w ⟨4, by omega⟩ y) (c y) && w ⟨5, by omega⟩ y)
        (xor (w ⟨k - 1, by omega⟩ y && w ⟨0, hk⟩ y) b)) ?_
      apply xorFin_congr; intro j
      rw [dite_neg (by omega), dite_neg (by omega), dite_neg (by omega), dite_neg (by omega)]
      have hj : (⟨j.val + 2 - 2, by omega⟩ : Fin (r - 2)) = j := Fin.ext (by simp)
      rw [hj]
    rw [Qp_eq_QpMid hk hr hk3 _ (wOfY_3 hr hk3 y), hprod]
    unfold QpMid Q0 Qk
    have hmask (b : Bool) : (if r % 2 = 0 then b else false) = (δ && b) := by
      by_cases he : r % 2 = 0 <;> simp [δ, he]
    rw [hmask]
    change xor (δ && xor (!(w ⟨1, by omega⟩ y) && w ⟨2, by omega⟩ y)
        (!(w ⟨0, hk⟩ y) && w ⟨1, by omega⟩ y))
      (xor (xor (w ⟨4, by omega⟩ y) (!(w ⟨4, by omega⟩ y) && w ⟨5, by omega⟩ y))
        (xor (!(w ⟨k - 1, by omega⟩ y) && w ⟨0, hk⟩ y)
          (xorFin (fun j => xor (x j y && !(d j y)) (z j y))))) = _
    rw [qp_pair_tail (fun j => x j y) (fun j => d j y) (fun j => z j y) (c y)]
    let U := xorFin (fun j => xor (x j y) (c y) && d j y)
    have hh := qp_pair_head δ (w ⟨0, hk⟩ y) (w ⟨2, by omega⟩ y) (w ⟨4, by omega⟩ y)
      (w ⟨5, by omega⟩ y) (w ⟨1, by omega⟩ y) (w ⟨k - 1, by omega⟩ y)
      (xorFin (fun j => d j y)) (P y) (qp_d_relation hr hk3 y)
    have hmove (a b c d e f : Bool) :
        xor a (xor b (xor c (xor d (xor e f)))) =
          xor (xor a (xor b (xor c (xor d f)))) e := by
      cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl
    rw [hmove]
    change xor _ U = xor (A y) (xor _ (xor _ U))
    simp only [c, Bool.and_assoc]
    rw [hh]
    change xor (xor (A y) _) U = _
    simp only [Bool.xor_assoc]

private lemma qp_affine_add {N : Nat} {f : (Fin N → Bool) → Bool}
    (hf : IsAffine f) (hf0 : f (fun _ => false) = false) (u v : Fin N → Bool) :
    f (fun i => xor (u i) (v i)) = xor (f u) (f v) := by
  obtain ⟨c, w, hw⟩ := hf
  rw [hw, dot_zero_right, Bool.xor_false] at hf0
  simp only [hw, hf0, Bool.false_xor, dot_xor_right]

private lemma qp_linear_weighted {N m : Nat} (f : (Fin N → Bool) → Bool)
    (hadd : ∀ u v, f (fun i => xor (u i) (v i)) = xor (f u) (f v))
    (h0 : f (fun _ => false) = false) (c : Fin m → Bool) (x : Fin m → Fin N → Bool) :
    f (fun p => xorFin (fun i => c i && x i p)) = xorFin (fun i => c i && f (x i)) := by
  induction m with
  | zero => exact h0
  | succ m ih =>
    have hs : (fun p => xorFin (fun i => c i && x i p)) =
        (fun p => xor (xorFin (fun i : Fin m => c i.castSucc && x i.castSucc p))
          (c (Fin.last m) && x (Fin.last m) p)) := funext fun p => xorFin_succ _
    rw [hs, hadd, ih (fun i => c i.castSucc) (fun i => x i.castSucc), xorFin_succ]
    congr 1
    cases c (Fin.last m) <;> simp [h0]

private lemma qp_minor_surjective {N m : Nat}
    (F A : (Fin N → Bool) → Bool) (L R : Fin m → (Fin N → Bool) → Bool)
    (hA : IsAffine A) (hL : ∀ i, IsAffine (L i)) (hR : ∀ i, IsAffine (R i))
    (hL0 : ∀ i, L i (fun _ => false) = false) (hR0 : ∀ i, R i (fun _ => false) = false)
    (hF : ∀ y, F y = xor (A y) (xorFin (fun i => L i y && R i y)))
    (p : Fin (2 * m) → Fin N)
    (hminor : ∀ c : Fin (2 * m) → Bool,
      (∀ j : Fin (2 * m), xorFin (fun i => c i && pol F (eVec (p i)) (eVec (p j))) = false) →
      ∀ i, c i = false) :
    Function.Surjective (fun y i => (L i y, R i y)) := by
  have hLadd (i : Fin m) := qp_affine_add (hL i) (hL0 i)
  have hRadd (i : Fin m) := qp_affine_add (hR i) (hR0 i)
  have hpol (a b : Fin N → Bool) :
      pol F a b = xorFin (fun i => Bpair (L i) (R i) a b) := by
    rw [show F = (fun y => xor (A y) (xorFin (fun i => L i y && R i y))) from funext hF,
      pol_xor, pol_affine hA, Bool.false_xor, pol_xorFin (fun i y => L i y && R i y)]
    apply xorFin_congr; intro i
    exact pol_and_lin (L i) (R i) (hLadd i) (hL0 i) (hRadd i) (hR0 i) a b
  have hadd (v a b : Fin N → Bool) :
      pol F (fun i => xor (a i) (b i)) v = xor (pol F a v) (pol F b v) := by
    rw [hpol, hpol, hpol, ← xorFin_xor]
    apply xorFin_congr; intro i
    unfold Bpair
    rw [hLadd i a b, hRadd i a b]
    cases L i a <;> cases L i b <;> cases R i a <;> cases R i b <;>
      cases L i v <;> cases R i v <;> rfl
  have hzero (v : Fin N → Bool) : pol F (fun _ => false) v = false := by
    rw [hpol]
    exact xorFin_eq_false _ (fun i => by simp [Bpair, hL0, hR0])
  let ζ (c : Fin (2 * m) → Bool) (j : Fin N) := xorFin (fun i => c i && eVec (p i) j)
  have hweight (c : Fin (2 * m) → Bool) (j : Fin (2 * m)) :
      pol F (ζ c) (eVec (p j)) = xorFin (fun i => c i && pol F (eVec (p i)) (eVec (p j))) :=
    qp_linear_weighted (fun a => pol F a (eVec (p j)))
      (hadd (eVec (p j))) (hzero (eVec (p j))) c (fun i => eVec (p i))
  let g (c : Fin (2 * m) → Bool) (i : Fin m) := (L i (ζ c), R i (ζ c))
  have hg : Function.Injective g := by
    intro a b hab
    have heval (j : Fin (2 * m)) : pol F (ζ a) (eVec (p j)) = pol F (ζ b) (eVec (p j)) := by
      rw [hpol, hpol]
      apply xorFin_congr; intro i
      have hi : (L i (ζ a), R i (ζ a)) = (L i (ζ b), R i (ζ b)) := congrFun hab i
      have hl : L i (ζ a) = L i (ζ b) := (Prod.mk.inj hi).1
      have hr : R i (ζ a) = R i (ζ b) := (Prod.mk.inj hi).2
      rw [Bpair,Bpair,hl,hr]
    have hc := hminor (fun i => xor (a i) (b i)) (fun j => by
      simp only [qp_xor_and, xorFin_xor, ← hweight a j, ← hweight b j, heval j, Bool.xor_self])
    funext i
    exact (by decide : ∀ a b : Bool, xor a b = false → a = b) _ _ (hc i)
  have he : Fintype.card (Fin (2 * m) → Bool) = Fintype.card (Fin m → Bool × Bool) := by
    rw [Fintype.card_pi_const, Fintype.card_pi_const, Fintype.card_prod,
      Fintype.card_bool, Nat.pow_mul]
  have hgs := (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq he)).mp hg
  intro z
  obtain ⟨c, hc⟩ := hgs z
  exact ⟨ζ c, hc⟩

theorem qpNormal {r k : Nat} (hk : 0 < k) (hr : 2 ≤ r) (hk3 : k = 3 * r) :
    ∃ (L R : Fin (if r = 2 then 0 else r) → (Fin (k - 3) → Bool) → Bool)
      (A : (Fin (k - 3) → Bool) → Bool),
      (∀ i, IsAffine (L i)) ∧ (∀ i, IsAffine (R i)) ∧ IsAffine A ∧
      Function.Surjective (fun y i => (L i y, R i y)) ∧
      ∀ y, Qp hk r (wOfY hr hk3 y) = xor (A y) (xorFin (fun i => L i y && R i y)) := by
  by_cases h2 : r = 2
  · rw [if_pos h2]
    refine ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun y => wOfY hr hk3 y ⟨0, hk⟩,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i, isAffine_wOfY hr hk3 _, ?_, ?_⟩
    · intro z; exact ⟨fun _ => false, funext fun i => Fin.elim0 i⟩
    · intro y
      change Qp hk r (wOfY hr hk3 y) = xor (wOfY hr hk3 y ⟨0, hk⟩) false
      rw [Bool.xor_false]
      exact Qp_r2 hk h2 hk3 _ (wOfY_3 hr hk3 y) (wOfY_resSum hr hk3 y).1 (wOfY_resSum hr hk3 y).2
  · rw [if_neg h2]
    obtain ⟨p, hp⟩ := qpPolarMinor hk (by omega) hk3
    obtain ⟨L, R, A, hL, hR, hA, hL0, hR0, hF⟩ := qpPairs hk hr hk3
    exact ⟨L, R, A, hL, hR, hA, qp_minor_surjective _ A L R hA hL hR hL0 hR0 hF p hp, hF⟩

namespace BiasBound

open PEqualNP.CircuitLowerBounds
open scoped BigOperators

abbrev F := ZMod 2

variable {V : Type*} [AddCommGroup V] [Module F V]

def toF (b : Bool) : F := if b then 1 else 0
def ofF (a : F) : Bool := decide (a = 1)

@[local simp] theorem toF_false : toF false = 0 := rfl
@[local simp] theorem toF_true : toF true = 1 := rfl
@[local simp] theorem toF_xor (a b : Bool) : toF (xor a b) = toF a + toF b :=
  (by decide : ∀ a b : Bool, toF (xor a b) = toF a + toF b) a b
@[local simp] theorem toF_and (a b : Bool) : toF (a && b) = toF a * toF b :=
  (by decide : ∀ a b : Bool, toF (a && b) = toF a * toF b) a b
@[local simp] theorem ofF_zero : ofF 0 = false := rfl
@[local simp] theorem ofF_add (a b : F) : ofF (a+b) = xor (ofF a) (ofF b) :=
  (by decide : ∀ a b : F, ofF (a+b) = xor (ofF a) (ofF b)) a b
@[local simp] theorem toF_ofF (a : F) : toF (ofF a) = a :=
  (by decide : ∀ a : F, toF (ofF a) = a) a
@[local simp] theorem ofF_toF (a : Bool) : ofF (toF a) = a :=
  (by decide : ∀ a : Bool, ofF (toF a) = a) a

private theorem zero_or_one (a : F) : a = 0 ∨ a = 1 :=
  (by decide : ∀ a : F, a = 0 ∨ a = 1) a
private theorem twice (a : F) : a + a = 0 :=
  (by decide : ∀ a : F, a+a=0) a

def AffineBit (f : V → Bool) : Prop :=
  ∃ (L : V →ₗ[F] F) (c : F), ∀ x, toF (f x) = L x + c

theorem affineBit_of_isAffine {d : Nat} {f : (Fin d → Bool) → Bool}
    (hf : IsAffine f) : AffineBit (fun x : Fin d → F => f (fun i => ofF (x i))) := by
  obtain ⟨c, w, h⟩ := hf
  let L : (Fin d → F) →ₗ[F] F :=
    { toFun := fun x => toF (dot w (fun i => ofF (x i)))
      map_add' := by
        intro x y
        change toF (dot w (fun i => ofF (x i + y i))) = _
        simp only [ofF_add, dot_xor_right, toF_xor]
      map_smul' := by
        intro a x
        rcases zero_or_one a with rfl | rfl
        · change toF (dot w (fun i => ofF ((0 : F) • x i))) = (0 : F) • _
          simp [dot_zero_right]
        · simp }
  refine ⟨L, toF c, fun x => ?_⟩
  change toF (f (fun i => ofF (x i))) = toF (dot w (fun i => ofF (x i))) + toF c
  rw [h, toF_xor, add_comm]

private theorem affine_const (b : Bool) : AffineBit (fun _ : V => b) :=
  ⟨0, toF b, fun x => by simp⟩

private theorem affine_xor {p q : V → Bool} (hp : AffineBit p) (hq : AffineBit q) :
    AffineBit (fun x => xor (p x) (q x)) := by
  obtain ⟨L, c, hL⟩ := hp
  obtain ⟨M, e, hM⟩ := hq
  refine ⟨L+M, c+e, fun x => ?_⟩
  rw [toF_xor, hL, hM, LinearMap.add_apply]
  abel

private theorem affine_scale (b : Bool) {p : V → Bool} (hp : AffineBit p) :
    AffineBit (fun x => b && p x) := by
  cases b
  · simpa using (affine_const (V := V) false)
  · simpa using hp

private theorem affine_unary (u : Bool → Bool) {p : V → Bool} (hp : AffineBit p) :
    AffineBit (fun x => u (p x)) := by
  have he (a : Bool) : u a = xor (u false) (xor (u false) (u true) && a) := by
    cases a <;> cases u false <;> cases u true <;> rfl
  rw [show (fun x => u (p x)) = (fun x => xor (u false) (xor (u false) (u true) && p x)) from
    funext (fun x => he (p x))]
  exact affine_xor (affine_const _) (affine_scale _ hp)

private theorem polar_xor_affine {q p : V → Bool} {B : LinearMap.BilinForm F V}
    (hq : ∀ x y, toF (q (x+y)) + toF (q x) + toF (q y) + toF (q 0) = B x y)
    (hp : AffineBit p) (x y : V) :
    toF (xor (q (x+y)) (p (x+y))) + toF (xor (q x) (p x)) +
      toF (xor (q y) (p y)) + toF (xor (q 0) (p 0)) = B x y := by
  obtain ⟨L, c, hL⟩ := hp
  simp only [toF_xor, hL, map_add, map_zero, zero_add]
  linear_combination hq x y + twice (L x) + twice (L y) + 2 * twice c

-- Character orthogonality and the square identity follow the pinned
-- lean/PEqualNP/Outside/L_pcx_441.lean, 036ab8b318851b49a3c9d09ef7f5972dd8c3d253.
private def sign (z : F) : ℤ := if z = 0 then 1 else -1

private theorem sign_add (x y : F) : sign (x+y) = sign x * sign y :=
  (by decide : ∀ x y : F, sign (x+y) = sign x * sign y) x y

private theorem sum_translate {A : Type*} [AddCommGroup A] [Fintype A]
    (g : A → ℤ) (r : A) : (∑ x, g (x+r)) = ∑ x, g x :=
  Fintype.sum_equiv (Equiv.addRight r) _ _ fun _ => rfl

private theorem char_sum {A : Type*} [AddCommGroup A] [Fintype A]
    (l : A →+ F) : (∑ x, sign (l x)) = if l = 0 then (Fintype.card A : ℤ) else 0 := by
  classical
  by_cases hz : l = 0
  · simp [hz, sign]
  · obtain ⟨r, hr⟩ : ∃ r, l r ≠ 0 := by
      by_contra! h
      exact hz (AddMonoidHom.ext h)
    have h := sum_translate (fun x => sign (l x)) r
    simp only [l.map_add, sign_add, (zero_or_one (l r)).resolve_left hr,
      show sign 1 = -1 by decide, ← Finset.sum_mul] at h
    rw [ite_eq_right hz]
    linarith

private theorem rearrange (a b c d z : F) (h : a+b+c+d=z) : a+b = c+d+z :=
  (by decide : ∀ a b c d z : F, a+b+c+d=z → a+b=c+d+z) a b c d z h

private theorem asAdd_zero (l : V →ₗ[F] F) : l.toAddMonoidHom = 0 ↔ l = 0 := by
  constructor
  · intro h
    exact LinearMap.ext (fun x => DFunLike.congr_fun h x)
  · rintro rfl
    rfl

open Classical in
private theorem square [Fintype V] (q : V → F) (B : LinearMap.BilinForm F V)
    (hq : ∀ x r, q (x+r)+q x+q r+q 0 = B x r) :
    (∑ x, sign (q x)) ^ 2 =
      (Fintype.card V : ℤ) * ∑ r, if B r = 0 then sign (q r+q 0) else 0 := by
  classical
  rw [pow_two]
  calc
    _ = ∑ x : V, ∑ y : V, sign (q x) * sign (q y) := by
      simp only [Finset.mul_sum, mul_comm]
    _ = ∑ x : V, ∑ r : V, sign (q x) * sign (q (r+x)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact (sum_translate (fun y => sign (q x) * sign (q y)) x).symm
    _ = ∑ r : V, ∑ x : V, sign (q r+q 0)*sign ((B r).toAddMonoidHom x) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro x _
      rw [← sign_add, ← sign_add, add_comm (q x)]
      apply congrArg sign
      apply rearrange
      change q (r+x) + q x + q r + q 0 = B r x
      simpa only [add_right_comm (q (r+x)) (q r) (q x)] using hq r x
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [← Finset.mul_sum, char_sum]
      simp only [asAdd_zero]
      split <;> ring

private theorem card_pow (A : Type*) [AddCommGroup A] [Module F A] [Fintype A] :
    Fintype.card A = 2 ^ Module.finrank F A := by
  rw [Module.card_eq_pow_finrank (K := F), ZMod.card]

private theorem quadratic_sum_le [Fintype V] (q : V → F) (B : LinearMap.BilinForm F V)
    (hq : ∀ x y, q (x+y)+q x+q y+q 0 = B x y)
    {m : ℕ} (hr : 2*m ≤ Module.finrank F B.range) :
    (∑ x, sign (q x)) ≤ (2 : ℤ)^(Module.finrank F V-m) := by
  classical
  letI : Fintype B.ker := Fintype.ofFinite _
  have hdim := B.finrank_range_add_finrank_ker
  have hs : (∑ r : V, if B r = 0 then sign (q r+q 0) else 0) ≤ (Fintype.card B.ker : ℤ) := by
    calc
      _ ≤ ∑ r : V, if B r = 0 then (1 : ℤ) else 0 := by
        apply Finset.sum_le_sum
        intro r _
        by_cases h : B r = 0
        · simp only [h, ite_true, sign]
          split <;> norm_num
        · simp [h]
      _ = ∑ _ : B.ker, (1 : ℤ) := by
        rw [← Finset.sum_filter]
        exact Finset.sum_subtype _ (fun r => by simp [LinearMap.mem_ker]) _
      _ = _ := by simp
  apply le_of_sq_le_sq _ (by positivity)
  calc
    _ = (Fintype.card V : ℤ) * ∑ r : V, if B r = 0 then sign (q r+q 0) else 0 := square q B hq
    _ ≤ (Fintype.card V : ℤ) * (Fintype.card B.ker : ℤ) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (2 : ℤ)^(Module.finrank F V + Module.finrank F B.ker) := by
      simp only [card_pow V, card_pow B.ker, pow_add, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ ((2 : ℤ)^(Module.finrank F V-m))^2 := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ (by decide) (by omega)

private def vote (p q : Bool) : ℤ := if p = q then 1 else -1

private theorem vote_sign (p q : Bool) : vote p q = sign (toF p + toF q) :=
  (by decide : ∀ p q : Bool, vote p q = sign (toF p + toF q)) p q

private def value (g : Gate) (β : Option Bool) (w : List Bool) : Bool :=
  g.op.eval (match g.inputs with
    | [] => []
    | i :: is => β.getD (w.getD i false) :: is.map (fun j => w.getD j false))

private def step (g : Gate) (β : Option Bool) (w : List Bool) : List Bool :=
  w ++ [value g β w]

private theorem step_none (g : Gate) (w : List Bool) :
    step g none w = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := by
  unfold step value
  cases g.inputs <;> rfl

private theorem step_force (g : Gate) (w : List Bool) :
    step g (some (w.getD (g.inputs.headD 0) false)) w = step g none w := by
  unfold step value
  cases g.inputs <;> rfl

private theorem value_affine (g : Gate) (β : Option Bool) (w : V → List Bool)
    (hfan : g.inputs.length ≤ 2) (hfree : β ≠ none ∨ nonlinear g = false)
    (hw : ∀ i, AffineBit (fun x => (w x).getD i false)) :
    AffineBit (fun x => value g β (w x)) := by
  obtain ⟨op, is⟩ := g
  cases is with
  | nil => exact affine_const (V := V) (op.eval [])
  | cons i is =>
    cases is with
    | nil =>
      cases β with
      | none => exact affine_unary (fun b => op.eval [b]) (hw i)
      | some b => exact affine_const (V := V) (op.eval [b])
    | cons j is =>
      cases is with
      | nil =>
        cases β with
        | some b => exact affine_unary (fun a => op.eval [b, a]) (hw j)
        | none =>
          have hn := hfree.resolve_left (by simp)
          have hh : (xor (xor (op.eval [false, false]) (op.eval [false, true]))
            (xor (op.eval [true, false]) (op.eval [true, true]))) = false := by
            simpa [nonlinear] using hn
          have he (a b : Bool) : op.eval [a,b] = xor (op.eval [false,false])
              (xor (xor (op.eval [false,false]) (op.eval [true,false]) && a)
                (xor (op.eval [false,false]) (op.eval [false,true]) && b)) := by
            rw [gate_eval_2 op a b, hh] <;> simp
          change AffineBit (fun x => op.eval [(w x).getD i false, (w x).getD j false])
          have heq : (fun x => op.eval [(w x).getD i false, (w x).getD j false]) =
              (fun x => xor (op.eval [false,false])
                (xor (xor (op.eval [false,false]) (op.eval [true,false]) && (w x).getD i false)
                  (xor (op.eval [false,false]) (op.eval [false,true]) && (w x).getD j false))) :=
            funext (fun x => he _ _)
          rw [heq]
          exact affine_xor (affine_const _) (affine_xor (affine_scale _ (hw i)) (affine_scale _ (hw j)))
      | cons k ks =>
        simp only [List.length_cons] at hfan
        omega

private theorem step_affine (g : Gate) (β : Option Bool) (w : V → List Bool) {width : Nat}
    (hlen : ∀ x, (w x).length = width)
    (hw : ∀ i, AffineBit (fun x => (w x).getD i false))
    (hv : AffineBit (fun x => value g β (w x))) (i : Nat) :
    AffineBit (fun x => (step g β (w x)).getD i false) := by
  by_cases hi : i < width
  · have he : (fun x => (step g β (w x)).getD i false) = (fun x => (w x).getD i false) :=
      funext (fun x => by
        unfold step
        exact getD_append_lt _ _ _ (by rw [hlen x]; exact hi))
    rw [he]
    exact hw i
  by_cases hj : i = width
  · subst i
    have he : (fun x => (step g β (w x)).getD width false) = (fun x => value g β (w x)) :=
      funext (fun x => by
        unfold step
        rw [← hlen x]
        exact getD_append_eq _ _ _)
    rw [he]
    exact hv
  · have he : (fun x => (step g β (w x)).getD i false) = (fun _ => false) := funext (fun x => by
      apply List.getD_eq_default
      simp only [step, List.length_append, List.length_cons, List.length_nil, hlen x]
      omega)
    rw [he]
    exact affine_const false

private def run (gs : List Gate) (w : List Bool) (o : Nat) : Bool :=
  ((Circuit.mk gs 0).wires w).getD o false

private theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) (o : Nat) :
    run (g :: gs) w o = run gs (step g none w) o := by
  rw [step_none] <;> rfl

private theorem vote_branch (a p₀ p₁ q : Bool) :
    2 * vote (if a then p₁ else p₀) q =
      vote p₀ q + vote p₁ q + vote p₀ (xor q (xor a false)) + vote p₁ (xor q (xor a true)) :=
  (by decide : ∀ a p₀ p₁ q : Bool, 2 * vote (if a then p₁ else p₀) q =
    vote p₀ q + vote p₁ q + vote p₀ (xor q (xor a false)) + vote p₁ (xor q (xor a true))) a p₀ p₁ q

-- Force the first operand of a nonlinear gate, and expand the indicator of that branch
-- into its constant and affine characters. This keeps the original polar in both branches.
private theorem run_sum_le [Fintype V] (gs : List Gate) (o : Nat)
    (hfan : ∀ g ∈ gs, g.inputs.length ≤ 2) (B : LinearMap.BilinForm F V)
    {m : ℕ} (hr : 2*m ≤ Module.finrank F B.range)
    (w : V → List Bool) (q : V → Bool) {width : Nat}
    (hlen : ∀ x, (w x).length = width)
    (hw : ∀ i, AffineBit (fun x => (w x).getD i false))
    (hq : ∀ x y, toF (q (x+y)) + toF (q x) + toF (q y) + toF (q 0) = B x y) :
    (∑ x, vote (run gs (w x) o) (q x)) ≤ (2 : ℤ)^(Module.finrank F V-m) * 2^(gs.countP nonlinear) := by
  induction gs generalizing w q width with
  | nil =>
    let p : V → Bool := fun x => (w x).getD o false
    have he (x : V) : vote (run [] (w x) o) (q x) = sign (toF (xor (q x) (p x))) := by
      change vote (p x) (q x) = _
      rw [vote_sign, toF_xor, add_comm]
    simp only [he, List.countP_nil, pow_zero, mul_one]
    exact quadratic_sum_le (fun x => toF (xor (q x) (p x))) B
      (polar_xor_affine hq (hw o)) hr
  | cons g gs ih =>
    let R : ℤ := (2 : ℤ)^(Module.finrank F V-m) * 2^(gs.countP nonlinear)
    have hfan' : ∀ h ∈ gs, h.inputs.length ≤ 2 := fun h hh => hfan h (List.mem_cons_of_mem _ hh)
    have leaf (β : Option Bool) (hb : β ≠ none ∨ nonlinear g = false) :
        ∀ q' : V → Bool,
          (∀ x y, toF (q' (x+y)) + toF (q' x) + toF (q' y) + toF (q' 0) = B x y) →
          (∑ x, vote (run gs (step g β (w x)) o) (q' x)) ≤ R := by
      intro q' hq'
      exact ih hfan' (fun x => step g β (w x)) q'
        (width := width + 1) (fun x => by simp [step, hlen x])
        (step_affine g β w hlen hw (value_affine g β w (hfan g (by simp)) hb hw)) hq'
    cases hg : nonlinear g with
    | false =>
      have hcount : (g :: gs).countP nonlinear = gs.countP nonlinear := by
        simp [List.countP_cons, hg]
      simpa only [run_cons, hcount, R] using leaf none (Or.inr hg) q hq
    | true =>
      let a : V → Bool := fun x => (w x).getD (g.inputs.headD 0) false
      let p (b : Bool) (x : V) : Bool := run gs (step g (some b) (w x)) o
      let qb (b : Bool) (x : V) : Bool := xor (q x) (xor (a x) b)
      have hp (b : Bool) : AffineBit (fun x => xor (a x) b) :=
        affine_xor (hw _) (affine_const b)
      have hqb (b : Bool) (x y : V) :
          toF (qb b (x+y)) + toF (qb b x) + toF (qb b y) + toF (qb b 0) = B x y :=
        polar_xor_affine (q := q) (p := fun z => xor (a z) b) (B := B) hq (hp b) x y
      have hsome (b : Bool) : some b ≠ none ∨ nonlinear g = false :=
        Or.inl (by intro h; cases h)
      have hl (b : Bool) : (∑ x, vote (p b x) (q x)) ≤ R :=
        leaf (some b) (hsome b) q hq
      have hl' (b : Bool) : (∑ x, vote (p b x) (qb b x)) ≤ R :=
        leaf (some b) (hsome b) (qb b) (hqb b)
      have he (x : V) : run (g :: gs) (w x) o = (if a x then p true x else p false x) := by
        rw [run_cons, ← step_force]
        change p (a x) x = _
        cases a x <;> rfl
      have hsum : 2 * (∑ x, vote (run (g :: gs) (w x) o) (q x)) =
          (∑ x, vote (p false x) (q x)) + (∑ x, vote (p true x) (q x)) +
          (∑ x, vote (p false x) (qb false x)) + (∑ x, vote (p true x) (qb true x)) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun x _ => by rw [he]; exact vote_branch _ _ _ _)
      have hb : (2 : ℤ)^(Module.finrank F V-m) * 2^((g :: gs).countP nonlinear) = R * 2 := by
        simp [List.countP_cons, hg, pow_succ, R, mul_assoc]
      rw [hb]
      linarith [hl false, hl true, hl' false, hl' true]

private theorem sum_vote [Fintype V] (p q : V → Bool) :
    (∑ x, vote (p x) (q x)) =
      2 * ((Finset.univ.filter fun x => p x = q x).card : ℤ) - Fintype.card V := by
  classical
  have he (x : V) : vote (p x) (q x) = (if p x = q x then (2 : ℤ) else 0) - 1 := by
    by_cases e : p x = q x <;> simp [vote, e]
  simp only [he, Finset.sum_sub_distrib, ← Finset.sum_filter, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] <;> ring

/-- Affine input wires and a rank lower bound for the target's polar suffice. The circuit
need not be reads-back: nonexistent wires already have the default value `false`. -/
theorem circuit_agreement_le [Fintype V] {width m t : Nat} (C : Circuit) (o : Nat)
    (φ : V → List Bool) (q : V → Bool) (B : LinearMap.BilinForm F V)
    (hlen : ∀ x, (φ x).length = width)
    (haff : ∀ i, AffineBit (fun x => (φ x).getD i false))
    (hpoly : ∀ x y, toF (q (x+y)) + toF (q x) + toF (q y) + toF (q 0) = B x y)
    (hr : 2*m ≤ Module.finrank F B.range)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (ht : C.gates.countP nonlinear ≤ t) :
    2 * (Finset.univ.filter (fun x => (C.wires (φ x)).getD o false = q x)).card ≤
      2^(Module.finrank F V) + 2^(Module.finrank F V-(m-t)) := by
  classical
  have hd : m ≤ Module.finrank F V := le_trans (by omega : m ≤ 2*m) (hr.trans B.finrank_range_le)
  by_cases hm : m ≤ t
  · have hc := Finset.card_le_card (Finset.filter_subset
      (fun x => (C.wires (φ x)).getD o false = q x) Finset.univ)
    rw [Finset.card_univ, card_pow V] at hc
    rw [Nat.sub_eq_zero_of_le hm, Nat.sub_zero]
    omega
  have h := run_sum_le C.gates o hfan B hr φ q hlen haff hpoly
  rw [sum_vote] at h
  have he : Module.finrank F V-m+t = Module.finrank F V-(m-t) := by omega
  have h' := h.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) ht) (by positivity))
  rw [← pow_add, he, card_pow V] at h'
  change 2 * ((Finset.univ.filter fun x => (C.wires (φ x)).getD o false = q x).card : ℤ) -
    ((2 : Nat)^Module.finrank F V : ℤ) ≤ (2 : ℤ)^_ at h'
  zify
  simp only [Nat.cast_pow, Nat.cast_ofNat] at h' ⊢
  linarith only [h']

end BiasBound

namespace PairCalc
open BiasBound
open scoped BigOperators

abbrev fieldBits (d : Nat) := Fin d → F

def bitChart (d : Nat) : fieldBits d ≃ bits d where
  toFun x i := ofF (x i)
  invFun x i := toF (x i)
  left_inv x := funext fun i => toF_ofF (x i)
  right_inv x := funext fun i => ofF_toF (x i)

lemma toF_xorFin {m : Nat} (f : Fin m → Bool) : toF (xorFin f) = ∑ i, toF (f i) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [xorFin_succ, toF_xor, ih, Fin.sum_univ_castSucc]

variable {V : Type*} [AddCommGroup V] [Module F V]

def pairLinear {m : Nat} (L R : Fin m → V →ₗ[F] F) : V →ₗ[F] (Fin m → F × F) where
  toFun x i := (L i x, R i x)
  map_add' x y := by funext i; exact Prod.ext (map_add _ _ _) (map_add _ _ _)
  map_smul' c x := by funext i; exact Prod.ext (map_smul _ _ _) (map_smul _ _ _)

def pairPolar {m : Nat} (L R : Fin m → V →ₗ[F] F) : LinearMap.BilinForm F V :=
  ∑ i, ((L i).smulRight (R i) + (R i).smulRight (L i))

lemma pairPolar_apply {m : Nat} (L R : Fin m → V →ₗ[F] F) (x y : V) :
    pairPolar L R x y = ∑ i, (L i x * R i y + R i x * L i y) := by
  simp [pairPolar, LinearMap.sum_apply, LinearMap.smulRight_apply, smul_eq_mul]

lemma pairPolar_rank [Module.Finite F V] {m : Nat} (L R : Fin m → V →ₗ[F] F)
    (hs : Function.Surjective (pairLinear L R)) :
    Module.finrank F (pairPolar L R).range = 2*m := by
  classical
  let G := pairLinear L R
  let B := pairPolar L R
  have hk : B.ker = G.ker := by
    ext x
    constructor
    · intro hx
      apply LinearMap.mem_ker.mpr
      have hx' := LinearMap.mem_ker.mp hx
      funext i
      obtain ⟨u, hu⟩ := hs (Pi.single i (0,1))
      obtain ⟨v, hv⟩ := hs (Pi.single i (1,0))
      have hBu : B x u = 0 := DFunLike.congr_fun hx' u
      have hBv : B x v = 0 := DFunLike.congr_fun hx' v
      have hCu : B x u = L i x := by
        rw [pairPolar_apply]
        change (∑ j, (L j x * (G u j).2 + R j x * (G u j).1)) = _
        rw [hu]
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj; simp [Pi.single_apply,hj]
        · simp
      have hCv : B x v = R i x := by
        rw [pairPolar_apply]
        change (∑ j, (L j x * (G v j).2 + R j x * (G v j).1)) = _
        rw [hv]
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj; simp [Pi.single_apply,hj]
        · simp
      exact Prod.ext (hCu.symm.trans hBu) (hCv.symm.trans hBv)
    · intro hx
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext
      intro y
      rw [pairPolar_apply]
      apply Finset.sum_eq_zero
      intro i _
      have hi := congrFun (LinearMap.mem_ker.mp hx) i
      have hL : L i x = 0 := congrArg Prod.fst hi
      have hR : R i x = 0 := congrArg Prod.snd hi
      simp [hL,hR]
  have hdim : Module.finrank F G.range = 2*m := by
    rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_pi_fintype]
    simp [Module.finrank_prod, Nat.mul_comm]
  have hG := G.finrank_range_add_finrank_ker
  have hB := B.finrank_range_add_finrank_ker
  change Module.finrank F B.range = 2*m
  rw [hk] at hB
  omega

lemma affine_pairs {m d : Nat} (L R : Fin m → bits d → Bool)
    (hL : ∀ i, IsAffine (L i)) (hR : ∀ i, IsAffine (R i))
    (hs : Function.Surjective (fun x i => (L i x,R i x))) :
    ∃ (l r : Fin m → fieldBits d →ₗ[F] F) (a b : Fin m → F),
      (∀ i x, toF (L i (bitChart d x)) = l i x + a i) ∧
      (∀ i x, toF (R i (bitChart d x)) = r i x + b i) ∧
      Function.Surjective (pairLinear l r) := by
  choose l a hl using fun i => affineBit_of_isAffine (hL i)
  choose r b hr using fun i => affineBit_of_isAffine (hR i)
  refine ⟨l,r,a,b, hl,hr,?_⟩
  intro z
  obtain ⟨Y,hY⟩ := hs (fun i => (ofF ((z i).1 + a i),ofF ((z i).2+b i)))
  refine ⟨(bitChart d).symm Y, ?_⟩
  funext i
  have e := congrFun hY i
  have e1 := congrArg (toF ∘ Prod.fst) e
  have e2 := congrArg (toF ∘ Prod.snd) e
  have hh1 := hl i ((bitChart d).symm Y)
  have hh2 := hr i ((bitChart d).symm Y)
  change toF (L i (bitChart d ((bitChart d).symm Y))) = _ at hh1
  change toF (R i (bitChart d ((bitChart d).symm Y))) = _ at hh2
  rw [Equiv.apply_symm_apply] at hh1 hh2
  simp only [Function.comp_apply, toF_ofF, hh1] at e1
  simp only [Function.comp_apply, toF_ofF, hh2] at e2
  exact Prod.ext (add_right_cancel e1) (add_right_cancel e2)

lemma polar_affine_pairs {m d : Nat} (q A : bits d → Bool) (L R : Fin m → bits d → Bool)
    (hA : IsAffine A) (hL : ∀ i, IsAffine (L i)) (hR : ∀ i, IsAffine (R i))
    (hs : Function.Surjective (fun x i => (L i x,R i x)))
    (hq : ∀ x, q x = xor (A x) (xorFin (fun i => L i x && R i x))) :
    ∃ B : LinearMap.BilinForm F (fieldBits d),
      Module.finrank F B.range = 2*m ∧
      ∀ x y, toF (q (bitChart d (x+y))) + toF (q (bitChart d x)) +
        toF (q (bitChart d y)) + toF (q (bitChart d 0)) = B x y := by
  obtain ⟨l,r,a,b,hl,hr,hg⟩ := affine_pairs L R hL hR hs
  obtain ⟨D,c,hD⟩ := affineBit_of_isAffine hA
  change ∀ x, toF (A (bitChart d x)) = D x+c at hD
  refine ⟨pairPolar l r, pairPolar_rank l r hg, ?_⟩
  intro x y
  have hf (z : fieldBits d) : toF (q (bitChart d z)) =
      D z+c + ∑ i, (l i z+a i)*(r i z+b i) := by
    simp only [hq, toF_xor, hD, toF_xorFin, toF_and, hl, hr]
  rw [hf,hf,hf,hf,pairPolar_apply]
  have halg : ∀ a b c d e f : F,
      (a+c+e)*(b+d+f) + (a+e)*(b+f) + (c+e)*(d+f) + e*f = a*d+b*c := by decide +kernel
  have hlinear : ∀ a b c : F, (a+b+c)+(a+c)+(b+c)+c=0 := by decide
  simp only [map_add,map_zero]
  calc
    _ = ((D x+D y+c)+(D x+c)+(D y+c)+c) +
        ∑ i, ((l i x+l i y+a i)*(r i x+r i y+b i)+(l i x+a i)*(r i x+b i)+
          (l i y+a i)*(r i y+b i)+a i*b i) := by simp only [Finset.sum_add_distrib]; ring
    _ = _ := by simp only [hlinear, zero_add, halg]

-- The product character and fiber splitting below are adapted from
-- lean/PEqualNP/Outside/L_pcx_441.lean at 036ab8b318851b49a3c9d09ef7f5972dd8c3d253.
private def character (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

private theorem character_add (x y : ZMod 2) :
    character (x + y) = character x * character y := by
  have all : ∀ a b : ZMod 2, character (a + b) = character a * character b := by decide
  exact all x y


private theorem character_sum {I : Type*} (s : Finset I) (f : I → F) :
    character (∑ i ∈ s, f i) = ∏ i ∈ s, character (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [character]
  | insert a rest fresh ih =>
    rw [Finset.sum_insert fresh,Finset.prod_insert fresh,character_add,ih]

private theorem one_pair : (∑ q : F × F, character (q.1 * q.2)) = 2 := by decide

private theorem subset_bias {A : Type*} [Fintype A] (r k : ℕ) (S : Finset (Fin r)) (q : A → F)
    (coords : A ≃ (Fin r → F × F) × (Fin k → F))
    (form : ∀ x, q x = ∑ i ∈ S, ((coords x).1 i).1 * ((coords x).1 i).2) :
    (2 : ℤ)^S.card * (∑ x, character (q x)) = 2 ^ (2*r + k) := by
  classical
  let w (i : Fin r) (z : F × F) : ℤ := if i ∈ S then character (z.1 * z.2) else 1
  let a (i : Fin r) : ℤ := if i ∈ S then 2 else 1
  have count : (∏ i, a i) = (2 : ℤ)^S.card := by
    unfold a
    rw [Finset.prod_ite_mem_eq,Finset.prod_const]
  have term (z : Fin r → F × F) : character (∑ i ∈ S, (z i).1 * (z i).2) = ∏ i, w i (z i) := by
    rw [character_sum]
    unfold w
    rw [Finset.prod_ite_mem_eq]
  have product : (∏ i, a i * ∑ z, w i z) = (4 : ℤ)^r := by
    have pointwise (i : Fin r) : a i * (∑ z, w i z) = 4 := by
      by_cases h : i ∈ S
      · simp [a,w,h,one_pair]
      · simp [a,w,h,Fintype.card_prod,ZMod.card]
    simp only [pointwise,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have selected : (2 : ℤ)^S.card * (∑ z : Fin r → F × F, ∏ i, w i (z i)) = 4^r := by
    rw [← count, ← Fintype.prod_sum w, ← Finset.prod_mul_distrib]
    exact product
  have all : (∑ x, character (q x)) =
      ∑ p : (Fin r → F × F) × (Fin k → F), ∏ i, w i (p.1 i) := by
    apply Fintype.sum_equiv coords
    intro x
    rw [form,term]
  rw [all,Fintype.sum_prod_type]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Finset.mul_sum]
  have free : (Fintype.card (Fin k → F) : ℤ) = 2^k := by
    simp [Fintype.card_fun,ZMod.card]
  rw [free]
  calc
    _ = (2 : ℤ)^k * ((2 : ℤ)^S.card * (∑ z : Fin r → F × F, ∏ i, w i (z i))) := by ring
    _ = (2 : ℤ)^(2*r+k) := by rw [selected,pow_add,pow_mul]; norm_num [mul_comm]

private noncomputable def split_fibers {A T : Type*} [AddCommGroup A] [Module F A] [AddCommGroup T] [Module F T] (G : A →ₗ[F] T)
    (surj : Function.Surjective G) : A ≃ T × LinearMap.ker G where
  toFun x := (G x,⟨x - (surj (G x)).choose, by
    rw [LinearMap.mem_ker,map_sub,(surj (G x)).choose_spec,sub_self]⟩)
  invFun y := y.2.val + (surj y.1).choose
  left_inv x := sub_add_cancel _ _
  right_inv := by
    rintro ⟨y,z⟩
    have h : G (z.val + (surj y).choose) = y := by
      rw [map_add,(surj y).choose_spec,LinearMap.mem_ker.mp z.property,zero_add]
    apply Prod.ext h
    apply Subtype.ext
    change z.val + (surj y).choose -
      (surj (G (z.val + (surj y).choose))).choose = z.val
    rw [h,add_sub_cancel_right]

lemma paired_count {m d s : Nat} (hs : s ≤ m) (q A : bits d → Bool) (L R : Fin m → bits d → Bool)
    (hL : ∀ i, IsAffine (L i)) (hR : ∀ i, IsAffine (R i))
    (hS : Function.Surjective (fun x i => (L i x,R i x)))
    (hq : ∀ x, q x = xor (A x) (xorFin (fun i => L i x && R i x))) :
    let p := fun x => xor (A x) (xorFin (fun i : Fin s => L (Fin.castLE hs i) x && R (Fin.castLE hs i) x))
    2*(Finset.univ.filter (fun x => p x = q x)).card = 2^d + 2^(d-(m-s)) := by
  classical
  intro p
  obtain ⟨l,r,a,b,hl,hr,hG⟩ := affine_pairs L R hL hR hS
  let G := pairLinear l r
  obtain ⟨z,hz⟩ := hG (fun i => (a i,b i))
  let k := Module.finrank F G.ker
  let E := (Equiv.addRight z).trans ((split_fibers G hG).trans
      ((Equiv.refl _).prodCongr (Module.finBasis F G.ker).equivFun.toEquiv))
  let S : Finset (Fin m) := (Finset.univ.map (Fin.castLEEmb hs))ᶜ
  have hc : S.card = m-s := by simp [S, Finset.card_compl]
  have hd : d = 2*m+k := by
    have H := Fintype.card_congr E
    simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,ZMod.card] at H
    have hm : (4 : Nat)^m = 2^(2*m) := by rw [pow_mul]; rfl
    rw [hm, ← pow_add] at H
    exact (pow_right_injective₀ (by decide : (0 : Nat) < 2) (by decide : (2 : Nat) ≠ 1)) H
  have hcoords (x : fieldBits d) (i : Fin m) :
      (toF (L i (bitChart d x)),toF (R i (bitChart d x))) = (E x).1 i := by
    rw [hl, hr]
    change (l i x+a i,r i x+b i) = G (x+z) i
    rw [map_add, Pi.add_apply]
    exact congrArg (fun v => (G x i)+v) (congrFun hz i).symm
  have hform (x : fieldBits d) : toF (p (bitChart d x)) + toF (q (bitChart d x)) =
      ∑ i ∈ S, ((E x).1 i).1 * ((E x).1 i).2 := by
    simp only [p, hq, toF_xor, toF_xorFin, toF_and]
    let incl : Fin s ↪ Fin m := Fin.castLEEmb hs
    let U : Finset (Fin m) := Finset.univ.map incl
    let term (i : Fin m) := toF (L i (bitChart d x)) * toF (R i (bitChart d x))
    have hpre : (∑ i : Fin s, term (Fin.castLE hs i)) = ∑ i ∈ U, term i := by simp [U,incl]
    have hsplit : (∑ i, term i) = (∑ i ∈ U, term i) + ∑ i ∈ S, term i := by
      have hdis : Disjoint U Uᶜ := Finset.disjoint_left.mpr (by simp)
      change _ = _ + ∑ i ∈ Uᶜ, term i
      rw [← Finset.sum_union hdis, Finset.union_compl]
    rw [hpre,hsplit]
    have hcancel : ∀ a b c : F, (a+b)+(a+(b+c))=c := by decide
    rw [hcancel]
    exact Finset.sum_congr rfl (fun i _ => by unfold term; rw [← hcoords])
  have hsum := subset_bias m k S (fun x => toF (p (bitChart d x)) + toF (q (bitChart d x))) E hform
  rw [hc, ← hd] at hsum
  have he (a b : Bool) : character (toF a + toF b) = BiasBound.vote a b := by cases a <;> cases b <;> decide
  simp only [he] at hsum
  rw [BiasBound.sum_vote] at hsum
  have hcardEq : (Finset.univ.filter (fun z : fieldBits d => p (bitChart d z) = q (bitChart d z))).card =
      (Finset.univ.filter (fun x => p x = q x)).card :=
    Finset.card_equiv (bitChart d) (fun _ => by simp)
  rw [hcardEq] at hsum
  have hcard : (Fintype.card (fieldBits d) : ℤ) = (2 : ℤ)^d := by simp [fieldBits,ZMod.card]
  rw [hcard] at hsum
  have hp : (2 : ℤ)^(m-s) * 2^(d-(m-s)) = 2^d := by rw [← pow_add, show m-s+(d-(m-s)) = d by omega]
  have heq : 2*((Finset.univ.filter (fun x => p x = q x)).card : ℤ) - 2^d = 2^(d-(m-s)) :=
    mul_left_cancel₀ (by positivity : (2 : ℤ)^(m-s) ≠ 0) (hsum.trans hp.symm)
  have heq' := (sub_eq_iff_eq_add.mp heq)
  exact_mod_cast heq'.trans (add_comm _ _)

end PairCalc

def targets {k n : Nat} (hk : 0 < k) (x : Fin n → bits k) : Bool :=
  xorFin (fun j => mix hk (rot hk (x j)) (ix hk 3))

def rawBlock {r k n : Nat} (hr : 2 ≤ r) (hk3 : k = 3*r) (v : bits (n*(k+3))) (j : Fin n) : KeyCoords k :=
  let bit (i : Nat) (hi : i < k+3) := v (finProdFinEquiv (j,⟨i,hi⟩))
  let d : bits k := fun i => bit i.val (by omega)
  (fun p => tOfD hr hk3 d (ySite hr hk3 p), bit k (by omega), bit (k+1) (by omega), bit (k+2) (by omega))

lemma rawBlock_eq {r k n : Nat} (hk : 0 < k) (hr : 2 ≤ r) (hk3 : k = 3*r) (u : bits k)
    (x : Fin n → bits k) (j : Fin n) :
    rawBlock hr hk3 (fun p => (dataRows hk r u x).getD p.val false) j = keyEncode hk hr hk3 u (x j) := by
  unfold rawBlock keyEncode
  dsimp only
  have hd : (fun i : Fin k => (dataRows hk r u x).getD (finProdFinEquiv (j,(⟨i.val, by omega⟩ : Fin (k+3)))).val false) =
      diffFn hk u (x j) := by
    funext i
    rw [dataRows_get, recordFn_getD_lt _ _ _ _ _ i.isLt]
  rw [hd]
  simp only [dataRows_get, recordFn_getD_k, recordFn_getD_k1, recordFn_getD_k2]

lemma rawBlock_aff {r k n : Nat} (hr : 2 ≤ r) (hk3 : k = 3*r) (j : Fin n) :
    (∀ p, IsAffine (fun v : bits (n*(k+3)) => (rawBlock hr hk3 v j).1 p)) ∧
    IsAffine (fun v : bits (n*(k+3)) => (rawBlock hr hk3 v j).2.1) :=
  ⟨fun p => isAffine_comp (isAffine_tOfD hr hk3 (ySite hr hk3 p)) (fun _ => isAffine_coord _), isAffine_coord _⟩

lemma coordBlock_aff {k n : Nat} (h : 3 ≤ k) (j : Fin n) :
    (∀ p, IsAffine (fun Y : bits (n*k) => (coordBlock h Y j).1 p)) ∧
    IsAffine (fun Y : bits (n*k) => (coordBlock h Y j).2.1) :=
  ⟨fun _ => isAffine_coord _, isAffine_coord _⟩

lemma coordBlock_surj {k n : Nat} (h : 3 ≤ k) :
    Function.Surjective (fun Y : bits (n*k) => fun j : Fin n => coordBlock h Y j) := by
  intro a
  let bs (j : Fin n) : bits k := (splitKeyEquiv h).symm (a j)
  refine ⟨fun i => bs (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2, ?_⟩
  funext j
  have h' : splitKey h (fun i => bs j i) = a j := (splitKeyEquiv h).apply_symm_apply (a j)
  simpa only [coordBlock, Equiv.symm_apply_apply] using h'

lemma mix_ix3_encode {r k : Nat} (hk : 0 < k) (hr : 2 ≤ r) (hk3 : k = 3*r) (u x : bits k) :
    mix hk (rot hk x) (ix hk 3) =
      xor (Qp hk r (wOfY hr hk3 (keyEncode hk hr hk3 u x).1))
        (xor (keyEncode hk hr hk3 u x).2.1
          (xor (linP hk r u (wOfY hr hk3 (keyEncode hk hr hk3 u x).1)) (mix hk u (ix hk 3)))) := by
  simpa only [keyDecode_encode] using mix_ix3_decode hk hr hk3 u (keyEncode hk hr hk3 u x)

def allLeft {k n b d : Nat} (P : bits d → Fin n → KeyCoords k)
    (L : Fin b → bits (k-3) → Bool) (i : Fin (n*b)) (v : bits d) : Bool :=
  L (finProdFinEquiv.symm i).2 (P v (finProdFinEquiv.symm i).1).1

def allAff {r k n d : Nat} (hk : 0 < k) (hr : 2 ≤ r) (hk3 : k = 3*r) (u : bits k)
    (P : bits d → Fin n → KeyCoords k) (A : bits (k-3) → Bool) (v : bits d) : Bool :=
  xorFin (fun j => xor (A (P v j).1) (xor (P v j).2.1
    (xor (linP hk r u (wOfY hr hk3 (P v j).1)) (mix hk u (ix hk 3)))))

lemma allLeft_aff {k n b d : Nat} (P : bits d → Fin n → KeyCoords k)
    (L : Fin b → bits (k-3) → Bool) (hL : ∀ i, IsAffine (L i))
    (hP : ∀ j p, IsAffine (fun v => (P v j).1 p)) (i : Fin (n*b)) : IsAffine (allLeft P L i) := by
  unfold allLeft
  exact isAffine_comp (hL _) (hP _)

lemma allAff_aff {r k n d : Nat} (hk : 0 < k) (hr : 2 ≤ r) (hk3 : k = 3*r) (u : bits k)
    (P : bits d → Fin n → KeyCoords k) (A : bits (k-3) → Bool) (hA : IsAffine A)
    (hP : ∀ j p, IsAffine (fun v => (P v j).1 p)) (hPp : ∀ j, IsAffine (fun v => (P v j).2.1)) :
    IsAffine (allAff hk hr hk3 u P A) := by
  apply isAffine_xorFin
  intro j
  exact isAffine_xor (isAffine_comp hA (hP j)) (isAffine_xor (hPp j)
    (isAffine_xor (isAffine_linP (r := r) hk u _ (fun i => isAffine_comp (isAffine_wOfY hr hk3 i) (hP j)))
      (isAffine_const _)))

lemma xorFin_finProd {n b : Nat} (f : Fin n → Fin b → Bool) :
    xorFin (fun i : Fin (n*b) => f (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) =
      xorFin (fun j => xorFin (f j)) := by
  by_cases hb : b = 0
  · subst b
    have h : n*0 = 0 := Nat.mul_zero n
    have h' : xorFin (fun i : Fin (n*0) => f (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) = false :=
      (xorFin_cast h _ (fun _ => false) (fun _ _ h0 => Fin.elim0 ⟨_,h0⟩)).trans rfl
    rw [h']
    symm
    exact xorFin_eq_false _ (fun _ => rfl)
  exact xorFin_prod (Nat.pos_of_ne_zero hb) f

lemma targets_shape {r k n b d : Nat} (hk : 0 < k) (hr : 2 ≤ r) (hk3 : k = 3*r) (u : bits k)
    (P : bits d → Fin n → KeyCoords k) (L R : Fin b → bits (k-3) → Bool) (A : bits (k-3) → Bool)
    (hn : ∀ y, Qp hk r (wOfY hr hk3 y) = xor (A y) (xorFin (fun i => L i y && R i y)))
    (v : bits d) (x : Fin n → bits k) (hx : ∀ j, P v j = keyEncode hk hr hk3 u (x j)) :
    targets hk x = xor (allAff hk hr hk3 u P A v) (xorFin (fun i => allLeft P L i v && allLeft P R i v)) := by
  unfold targets allAff allLeft
  rw [xorFin_finProd (fun j i => L i (P v j).1 && R i (P v j).1), ← xorFin_xor]
  apply xorFin_congr
  intro j
  rw [hx j, mix_ix3_encode hk hr hk3 u (x j), hn]
  exact (by decide : ∀ a b c : Bool, xor (xor a b) c = xor (xor a c) b) _ _ _

lemma allPairs_surj {k n b d : Nat} (P : bits d → Fin n → KeyCoords k)
    (hP : Function.Surjective P) (L R : Fin b → bits (k-3) → Bool)
    (hS : Function.Surjective (fun y a => (L a y,R a y))) :
    Function.Surjective (fun v i => (allLeft P L i v, allLeft P R i v)) := by
  intro z
  choose y hy using fun j : Fin n => hS (fun i => z (finProdFinEquiv (j,i)))
  obtain ⟨Y,hY⟩ := hP (fun j => (y j,false,false,false))
  refine ⟨Y,?_⟩
  funext i
  obtain ⟨⟨j,a⟩,rfl⟩ := finProdFinEquiv.surjective i
  simpa only [allLeft, finProdFinEquiv.symm_apply_apply, hY] using congrFun (hy j) a

lemma build_predictor {width s : Nat} (A : bits width → Bool) (L R : Fin s → bits width → Bool)
    (hA : IsAffine A) (hL : ∀ i, IsAffine (L i)) (hR : ∀ i, IsAffine (R i)) :
    ∃ C : Circuit, ∃ o : Nat, valid width C ∧ C.gates.countP nonlinear = s ∧ o < width+C.gates.length ∧
      ∀ inp : List Bool, inp.length = width →
        (C.wires inp).getD o false =
          xor (A (fun i => inp.getD i.val false))
            (xorFin (fun i => L i (fun j => inp.getD j.val false) && R i (fun j => inp.getD j.val false))) := by
  let vals (i : Fin width) (inp : List Bool) := inp.getD i.val false
  have hws : ∀ i : Fin width, WireSpec width [] i.val true (vals i) :=
    fun i => wireSpec_input width i.val i.isLt
  obtain ⟨gs, ps, hg, hc, hp, hps⟩ :=
    addAndVec [] (good_nil width) (fun i : Fin width => i.val) vals hws L R hL hR
  obtain ⟨gs', a, hg', hc', hp', ha⟩ :=
    addAffineFn gs hg true (fun i : Fin width => i.val) vals (fun i => hp _ _ _ (hws i)) A hA
  let ws : Fin (s+1) → Nat := Fin.cons a ps
  let fs : Fin (s+1) → List Bool → Bool := Fin.cons (fun inp => A (fun i => vals i inp))
    (fun i inp => L i (fun j => vals j inp) && R i (fun j => vals j inp))
  have hsf : ∀ i, WireSpec width gs' (ws i) false (fs i) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨ha.1, (fun e => by cases e), ha.2.2⟩
    · exact hp' _ _ _ (hps j)
  obtain ⟨gs'', o, hg'', hc'', _, ho⟩ := addAffine gs' hg' false ws fs hsf false (fun _ => true)
  refine ⟨⟨gs'',0⟩, o, ⟨hg''.1,hg''.2.1⟩, by simp [hc'',hc',hc], ho.1, ?_⟩
  intro inp hinp
  rw [ho.2.2 inp hinp]
  simp only [Bool.true_and,Bool.false_xor,xorFin_head_tail,fs,Fin.cons_succ,vals] <;> rfl

lemma filter_equiv {α β : Type*} [Fintype α] [Fintype β] (E : α ≃ β) (p : β → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun x => p (E x))).card = (Finset.univ.filter p).card :=
  Finset.card_equiv E (fun _ => by simp)

open PairCalc BiasBound in
lemma exact_count {r k : Nat} (hk : 0 < k) (hr : 2 ≤ r) (hk3 : k = 3*r) (u : bits k) (n t c : Nat) :
    let m := if r = 2 then 0 else n*r
    let width := n*(k+3)
    (∃ (C : Circuit) (o : Nat), valid width C ∧ C.gates.countP nonlinear ≤ t ∧ o < width+C.gates.length ∧
        c ≤ (Finset.univ.filter (fun x : Fin n → bits k => (C.wires (dataRows hk r u x)).getD o false = targets hk x)).card) ↔
      2*c ≤ 2^(n*k) + 2^(n*k-(m-t)) := by
  classical
  intro m width
  let b := if r = 2 then 0 else r
  have hm : n*b = m := by simp [m,b,mul_ite]
  obtain ⟨L,R,A,hL,hR,hA,hs,hshape⟩ := qpNormal hk hr hk3
  let P (Y : bits (n*k)) (j : Fin n) := coordBlock (by omega : 3 ≤ k) Y j
  let Ec : bits (n*k) ≃ (Fin n → bits k) := inputChart hk hr hk3 u
  let q := fun Y : bits (n*k) => targets hk (Ec Y)
  let Lj : Fin (n*b) → bits (n*k) → Bool := allLeft P L
  let Rj : Fin (n*b) → bits (n*k) → Bool := allLeft P R
  let Aj := allAff hk hr hk3 u P A
  have hLj : ∀ i, IsAffine (Lj i) := allLeft_aff P L hL (fun j => (coordBlock_aff (by omega) j).1)
  have hRj : ∀ i, IsAffine (Rj i) := allLeft_aff P R hR (fun j => (coordBlock_aff (by omega) j).1)
  have hAj : IsAffine Aj := allAff_aff hk hr hk3 u P A hA
    (fun j => (coordBlock_aff (by omega) j).1) (fun j => (coordBlock_aff (by omega) j).2)
  have hS : Function.Surjective (fun Y i => (Lj i Y,Rj i Y)) := allPairs_surj P (coordBlock_surj _) L R hs
  have hq : ∀ Y, q Y = xor (Aj Y) (xorFin (fun i => Lj i Y && Rj i Y)) := fun Y =>
    targets_shape hk hr hk3 u P L R A hshape Y (Ec Y) (fun j => (inputChart_encode hk hr hk3 u Y j).symm)
  constructor
  · rintro ⟨C,o,hvalid,hcnt,_,hag⟩
    obtain ⟨B,hB,hpoly⟩ := polar_affine_pairs q Aj Lj Rj hAj hLj hRj hS hq
    let E := (bitChart (n*k)).trans Ec
    let φ (z : fieldBits (n*k)) := dataRows hk r u (E z)
    have hle := circuit_agreement_le (width := width) (m := n*b) (t := t) C o φ
      (fun z => q (bitChart (n*k) z)) B (fun _ => dataRows_len hk r u _) (fun i =>
        affineBit_of_isAffine (dataRows_aff hk hr hk3 u i)) hpoly hB.ge hvalid.2 hcnt
    change 2 * (Finset.univ.filter (fun z => (C.wires (dataRows hk r u (E z))).getD o false = targets hk (E z))).card ≤ _ at hle
    rw [filter_equiv E (fun x => (C.wires (dataRows hk r u x)).getD o false = targets hk x)] at hle
    have hdim : Module.finrank F (fieldBits (n*k)) = n*k := by
      simpa only [Fintype.card_fin] using (Module.finrank_pi (ι := Fin (n*k)) F)
    rw [hdim, hm] at hle
    exact (Nat.mul_le_mul_left _ hag).trans hle
  · intro hc
    let s := min (n*b) t
    have hs' : s ≤ n*b := min_le_left _ _
    let H (v : bits width) (j : Fin n) := rawBlock hr hk3 v j
    let A' := allAff hk hr hk3 u H A
    let L' (i : Fin s) := allLeft H L (Fin.castLE hs' i)
    let R' (i : Fin s) := allLeft H R (Fin.castLE hs' i)
    have hH (j : Fin n) := rawBlock_aff (n := n) hr hk3 j
    have hA' := allAff_aff hk hr hk3 u H A hA (fun j => (hH j).1) (fun j => (hH j).2)
    obtain ⟨C,o,hvalid,hcount,ho,hwire⟩ := build_predictor A' L' R' hA'
      (fun i => allLeft_aff H L hL (fun j => (hH j).1) _) (fun i => allLeft_aff H R hR (fun j => (hH j).1) _)
    refine ⟨C,o,hvalid,by rw [hcount]; exact min_le_right _ _,ho,?_⟩
    have hEq (Y : bits (n*k)) :
        (C.wires (dataRows hk r u (Ec Y))).getD o false =
          xor (Aj Y) (xorFin (fun i : Fin s => Lj (Fin.castLE hs' i) Y && Rj (Fin.castLE hs' i) Y)) := by
      have hrow : H (fun p => (dataRows hk r u (Ec Y)).getD p.val false) = P Y := by
        funext j
        exact (rawBlock_eq hk hr hk3 u (Ec Y) j).trans (inputChart_encode hk hr hk3 u Y j)
      rw [hwire _ (dataRows_len hk r u _)]
      simp only [A',L',R',Aj,Lj,Rj,allAff,allLeft,hrow]
    have he := paired_count hs' q Aj Lj Rj hLj hRj hS hq
    have hh : (Finset.univ.filter (fun Y : bits (n*k) =>
          (C.wires (dataRows hk r u (Ec Y))).getD o false = targets hk (Ec Y))).card = _ :=
      filter_equiv Ec (fun x => (C.wires (dataRows hk r u x)).getD o false = targets hk x)
    have hEq' : (fun Y : bits (n*k) =>
        (C.wires (dataRows hk r u (Ec Y))).getD o false = targets hk (Ec Y)) =
        (fun Y => xor (Aj Y) (xorFin (fun i : Fin s => Lj (Fin.castLE hs' i) Y && Rj (Fin.castLE hs' i) Y)) = q Y) := by
      funext Y
      rw [hEq]
    simp only [hEq'] at hh
    dsimp only at he
    rw [hh, show n*b-s = m-t by dsimp [s]; omega] at he
    omega

end PEqualNP.Outside.L_meta_42686_aux

theorem PEqualNP.Outside.L_meta_42686 :
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
        (xor (g.op.eval [true,false]) (g.op.eval [true,true]))
let valid := fun (w : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  PEqualNP.MetaComplexity.NestedCover.ReadsBack w C ∧
  ∀ g ∈ C.gates, g.inputs.length ≤ 2
∀ (r k : Nat) (hk : 0 < k), 2 ≤ r → k = 3*r →
  let W := Fin k → Bool
  let ix := fun (i : Nat) => (⟨i % k, Nat.mod_lt _ hk⟩ : Fin k)
  let add := fun (u v : W) (i : Fin k) => xor (u i) (v i)
  let mix := fun (w : W) (i : Fin k) => xor (w (ix (i.val+k-1))) (xor (w i) (w (ix (i.val+1))))
  let rot := fun (x : W) (i : Fin k) => x (ix (i.val+k-1))
  let chi := fun (w : W) (i : Fin k) => xor (w i) (!(w (ix (i.val+1))) && w (ix (i.val+2)))
  let row := fun (u x : W) => add (chi (mix (add u (rot x)))) x
  let v : W := fun i => decide (i.val ≠ 1)
  ∀ u : W,
    let base := row u
    let diff := fun x : W => add (base x) (row (add u v) x)
    let needed : Finset (Fin k) := Finset.univ.filter (fun i =>
      if i.val = 0 ∨ i.val = k-1 then r % 2 = 0
      else i.val = 1 ∨ i.val = k-2 ∨ i.val % 3 ≠ 1)
    let record := fun (x : W) => List.ofFn (diff x) ++
      [decide ((needed.filter (fun i => base x i)).card % 2 = 1), base x (ix 0), base x (ix (k-1))]
    ∀ (n t : Nat),
      let width := n*(k+3)
      let U := Fin n → W
      let data := fun (x : U) => (List.ofFn (fun j : Fin n => record (x j))).flatten
      let target := fun (x : U) => (List.ofFn (fun j : Fin n => mix (rot (x j)) (ix 3))).foldl xor false
      let keys : Finset U := Finset.univ
      let m := if r = 2 then 0 else n*r
      ∀ c : Nat,
        (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Nat),
          valid width C ∧ C.gates.countP nonlinear ≤ t ∧ o < width+C.gates.length ∧
          c ≤ (keys.filter (fun x => (C.wires (data x)).getD o false = target x)).card) ↔
        2*c ≤ 2^(n*k) + 2^(n*k-(m-t))
:= by
  intro nonlinear valid r k hk hr hk3 W ix add mix rot chi row v u base diff needed record n t width U data target keys m c
  have ht : target = PEqualNP.Outside.L_meta_42686_aux.targets hk := by
    funext x
    change (List.ofFn _).foldl xor false = _
    simp only [PEqualNP.Outside.L_meta_42686_aux.targets, PEqualNP.Outside.L_meta_42686_aux.xorFin,
      List.ofFn_eq_map, List.foldl_map] <;> rfl
  rw [ht]
  exact PEqualNP.Outside.L_meta_42686_aux.exact_count hk hr hk3 u n t c
