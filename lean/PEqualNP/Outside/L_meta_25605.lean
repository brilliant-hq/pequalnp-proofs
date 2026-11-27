import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25605

def mixF (x : Int → Bool) (z : Int) : Bool := xor (xor (x (z-1)) (x z)) (x (z+1))

def evolveF (x injection : Int → Bool) (z : Int) : Bool :=
  xor (xor (mixF x z) (!(mixF x (z+1)) && mixF x (z+2))) (injection z)

abbrev ev5 (t0 t1 t2 t3 t4 k : Bool) : Bool :=
  xor (xor (xor (xor t0 t1) t2) (!(xor (xor t1 t2) t3) && xor (xor t2 t3) t4)) k

theorem ev_eq (x inj : Int → Bool) (z : Int) :
    evolveF x inj z = ev5 (x (z-1)) (x z) (x (z+1)) (x (z+2)) (x (z+3)) (inj z) := by
  have h1 : z + 1 - 1 = z := by ring
  have h2 : z + 1 + 1 = z + 2 := by ring
  have h3 : z + 2 - 1 = z + 1 := by ring
  have h4 : z + 2 + 1 = z + 3 := by ring
  simp only [evolveF, mixF, ev5, h1, h2, h3, h4]

theorem evolve_congr {x x' inj : Int → Bool} {z : Int}
    (h : ∀ s, z - 1 ≤ s → s ≤ z + 3 → x s = x' s) :
    evolveF x inj z = evolveF x' inj z := by
  rw [ev_eq, ev_eq, h (z-1) (by omega) (by omega), h z (by omega) (by omega),
    h (z+1) (by omega) (by omega), h (z+2) (by omega) (by omega),
    h (z+3) (by omega) (by omega)]

theorem evolve_prefix {x x' inj : Int → Bool} {e : Int} (h : ∀ s ≤ e, x s = x' s) :
    ∀ z ≤ e - 3, evolveF x inj z = evolveF x' inj z :=
  fun z hz => evolve_congr (fun s _ h2 => h s (by omega))

theorem evolve_right {x x' inj : Int → Bool} {q : Int} (h : ∀ s > q, x s = x' s)
    (hq : x q ≠ x' q) :
    (∀ s > q + 1, evolveF x inj s = evolveF x' inj s) ∧
      evolveF x inj (q+1) ≠ evolveF x' inj (q+1) := by
  refine ⟨fun s hs => evolve_congr (fun t h1 _ => h t (by omega)), ?_⟩
  rw [ev_eq, ev_eq, show q + 1 - 1 = q by ring, h (q+1) (by omega), h (q+1+1) (by omega),
    h (q+1+2) (by omega), h (q+1+3) (by omega)]
  revert hq
  cases x q <;> cases x' q <;> simp

def blockF (width : Nat) (tape : Int → Bool) (edge : Int) : Nat :=
  (List.range width).foldl (fun (number bitIndex : Nat) =>
    number ||| ((tape (edge+1+(bitIndex : Int))).toNat <<< bitIndex)) 0

def tailsF (w admit : Nat) : List Nat :=
  (List.range (2 ^ (2*w+5))).filter (fun pattern => admit.testBit (pattern % 2^w))

def trialF (x : Int → Bool) (b : Int) (completionCode : Nat) (site : Int) : Bool :=
  if site ≤ b then x site else completionCode.testBit (site-b-1).toNat

def fixedF (w : Nat) (b : Int) (x inj : Int → Bool) (admit : Nat) (offset : Nat) : Bool :=
  (tailsF w admit).all (fun comparisonCode =>
    evolveF (trialF x b comparisonCode) inj (b-2+(offset : Int)) ==
      evolveF x inj (b-2+(offset : Int)))

def edgeF (w : Nat) (b : Int) (x inj : Int → Bool) (admit : Nat) : Int :=
  b-3+(((List.range (w+5)).takeWhile (fixedF w b x inj admit)).length : Int)

def advF (w : Nat) (b : Int) (x inj : Int → Bool) (admit : Nat) : Int × Nat :=
  (edgeF w b x inj admit, (tailsF w admit).foldl (fun acc outputCode =>
    acc ||| ((1 : Nat) <<< blockF w (evolveF (trialF x b outputCode) inj)
      (edgeF w b x inj admit))) 0)

def fitsF (width : Nat) (edge : Int) (sample : Int → Bool) (mask : Nat) (tape : Int → Bool) :
    Prop :=
  (∀ pos ≤ edge, tape pos = sample pos) ∧ mask.testBit (blockF width tape edge) = true

def runF (inj : Nat → Int → Bool) (length : Nat) (seed : Int → Bool) : Int → Bool :=
  (List.range length).foldl (fun st tick => evolveF st (inj tick)) seed

def padF (u mask w : Nat) : Nat := (List.range (2^w)).foldl (fun (acc pat : Nat) =>
    if mask.testBit (pat % (2^u)) then acc ||| ((1 : Nat) <<< pat) else acc) 0

def trackF (inj : Nat → Int → Bool) (x : Int → Bool) (b : Int) (P : Nat) (w len : Nat) :
    (Int → Bool) × Int × Nat :=
  (List.range len).foldl (fun (st : (Int → Bool) × Int × Nat) tick =>
      let nxt := advF w st.2.1 st.1 (inj tick) st.2.2
      (evolveF st.1 (inj tick), nxt.1, nxt.2)) (x, b, P)

def realF (inj : Nat → Int → Bool) (u : Nat) (b : Int) (x : Int → Bool) (mask : Nat)
    (length : Nat) (edge : Int) : Prop :=
  (∀ seed, fitsF u b x mask seed → ∀ z ≤ edge, runF inj length seed z = runF inj length x z) ∧
  (∃ seed, fitsF u b x mask seed ∧ runF inj length seed (edge+1) ≠ runF inj length x (edge+1))

/-! ## basic facts -/

theorem run_zero (inj : Nat → Int → Bool) (s : Int → Bool) : runF inj 0 s = s := rfl

theorem run_succ (inj : Nat → Int → Bool) (k : Nat) (s : Int → Bool) :
    runF inj (k+1) s = evolveF (runF inj k s) (inj k) := by
  simp only [runF, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem track_succ (inj : Nat → Int → Bool) (x : Int → Bool) (b : Int) (P w k : Nat) :
    trackF inj x b P w (k+1) =
      (evolveF (trackF inj x b P w k).1 (inj k),
        edgeF w (trackF inj x b P w k).2.1 (trackF inj x b P w k).1 (inj k)
          (trackF inj x b P w k).2.2,
        (advF w (trackF inj x b P w k).2.1 (trackF inj x b P w k).1 (inj k)
          (trackF inj x b P w k).2.2).2) := by
  simp only [trackF, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

theorem track_zero (inj : Nat → Int → Bool) (x : Int → Bool) (b : Int) (P w : Nat) :
    trackF inj x b P w 0 = (x, b, P) := rfl

theorem track_fst (inj : Nat → Int → Bool) (x : Int → Bool) (b : Int) (P w : Nat) :
    ∀ k, (trackF inj x b P w k).1 = runF inj k x
  | 0 => rfl
  | k+1 => by rw [track_succ, run_succ, track_fst inj x b P w k]

theorem fixed_iff (w : Nat) (b : Int) (x inj : Int → Bool) (A o : Nat) :
    fixedF w b x inj A o = true ↔ ∀ p, p < 2 ^ (2*w+5) → A.testBit (p % 2^w) = true →
      evolveF (trialF x b p) inj (b-2+(o:Int)) = evolveF x inj (b-2+(o:Int)) := by
  simp only [fixedF, tailsF, List.all_eq_true, List.mem_filter, List.mem_range, beq_iff_eq,
    and_imp]

theorem fold_bit (l : List Nat) (f : Nat → Nat) (acc n : Nat) :
    (l.foldl (fun a p => a ||| ((1 : Nat) <<< f p)) acc).testBit n =
      (acc.testBit n || l.any (fun p => decide (f p = n))) := by
  induction l generalizing acc with
  | nil => simp
  | cons p t ih =>
    rw [List.foldl_cons, ih, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow,
      List.any_cons, Bool.or_assoc]

theorem snd_bit (w : Nat) (b : Int) (x inj : Int → Bool) (A n : Nat) :
    (advF w b x inj A).2.testBit n = true ↔ ∃ p, p < 2 ^ (2*w+5) ∧ A.testBit (p % 2^w) = true ∧
      blockF w (evolveF (trialF x b p) inj) (edgeF w b x inj A) = n := by
  simp only [advF, fold_bit, Nat.zero_testBit, Bool.false_or, List.any_eq_true,
    decide_eq_true_eq, tailsF, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨p, ⟨h1, h2⟩, h3⟩
    exact ⟨p, h1, h2, h3⟩
  · rintro ⟨p, h1, h2, h3⟩
    exact ⟨p, ⟨h1, h2⟩, h3⟩

theorem block_succ (w : Nat) (t : Int → Bool) (e : Int) :
    blockF (w+1) t e = blockF w t e ||| ((t (e+1+(w:Int))).toNat <<< w) := by
  simp only [blockF, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem block_bit (w : Nat) (t : Int → Bool) (e : Int) (i : Nat) :
    (blockF w t e).testBit i = (decide (i < w) && t (e+1+(i:Int))) := by
  induction w with
  | zero => simp [blockF]
  | succ w ih =>
    rw [block_succ, Nat.testBit_or, ih]
    rcases lt_trichotomy i w with h | rfl | h
    · cases t (e+1+(w:Int)) <;> simp [Nat.testBit_shiftLeft, h, show i < w + 1 by omega] <;> omega
    · cases t (e+1+(i:Int)) <;> simp [Nat.testBit_shiftLeft]
    · cases t (e+1+(w:Int)) <;>
        simp [Nat.one_shiftLeft, Nat.testBit_two_pow, show ¬ i < w by omega,
          show ¬ i < w + 1 by omega, show w ≠ i by omega]

theorem block_lt (w : Nat) (t : Int → Bool) (e : Int) : blockF w t e < 2 ^ w := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [block_bit]
  simp [show ¬ i < w by omega]

theorem block_congr {w : Nat} {t t' : Int → Bool} {e : Int}
    (h : ∀ s, e + 1 ≤ s → s ≤ e + w → t s = t' s) : blockF w t e = blockF w t' e := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [block_bit, block_bit]
  by_cases hi : i < w
  · rw [h (e+1+(i:Int)) (by omega) (by omega)]
  · simp [hi]

theorem block_mod {u w : Nat} (h : u ≤ w) (t : Int → Bool) (e : Int) :
    blockF w t e % 2 ^ u = blockF u t e := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, block_bit, block_bit]
  by_cases hi : i < u
  · simp [hi, show i < w by omega]
  · simp [hi]

theorem trial_block (w : Nat) (x : Int → Bool) (b : Int) (p : Nat) :
    blockF w (trialF x b p) b = p % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, block_bit]
  by_cases hi : i < w
  · simp only [hi, decide_true, Bool.true_and, trialF]
    rw [if_neg (by omega), show (b + 1 + (i:Int) - b - 1).toNat = i by omega]
  · simp [hi]

theorem trial_fits {w : Nat} {x : Int → Bool} {b : Int} {M p : Nat}
    (h : M.testBit (p % 2 ^ w) = true) : fitsF w b x M (trialF x b p) :=
  ⟨fun pos hp => by simp [trialF, hp], by rw [trial_block]; exact h⟩

theorem tw_props (f : Nat → Bool) : ∀ (N s : Nat),
    ((List.range' s N).takeWhile f).length ≤ N ∧
    (∀ o < ((List.range' s N).takeWhile f).length, f (s+o) = true) ∧
    (((List.range' s N).takeWhile f).length < N →
      f (s + ((List.range' s N).takeWhile f).length) = false)
  | 0, s => by simp
  | N+1, s => by
    rw [List.range'_succ, List.takeWhile_cons]
    cases h : f s
    · simp [h]
    · simp only [if_true, List.length_cons]
      obtain ⟨a, b, c⟩ := tw_props f N (s+1)
      refine ⟨by omega, ?_, ?_⟩
      · intro o ho
        rcases o with _ | o
        · simpa using h
        · have := b o (by omega)
          rwa [show s + 1 + o = s + (o+1) by omega] at this
      · intro hl
        have := c (by omega)
        rwa [show s + 1 + ((List.range' (s + 1) N).takeWhile f).length =
          s + (((List.range' (s + 1) N).takeWhile f).length + 1) by omega] at this

theorem tw_range (f : Nat → Bool) (N : Nat) :
    ((List.range N).takeWhile f).length ≤ N ∧
    (∀ o < ((List.range N).takeWhile f).length, f o = true) ∧
    (((List.range N).takeWhile f).length < N → f ((List.range N).takeWhile f).length = false) := by
  have := tw_props f N 0
  simp only [Nat.zero_add] at this
  rw [List.range_eq_range']
  exact this

/-! ## one round -/

theorem edge_bounds (w : Nat) (b : Int) (x inj : Int → Bool) (M : Nat) :
    b - 3 ≤ edgeF w b x inj M ∧ edgeF w b x inj M ≤ b + w + 2 := by
  have := (tw_range (fixedF w b x inj M) (w+5)).1
  unfold edgeF
  omega

theorem prefix_trial {w : Nat} {b : Int} {x inj : Int → Bool} {M p : Nat}
    (hp : p < 2 ^ (2*w+5)) (hM : M.testBit (p % 2^w) = true) :
    ∀ j ≤ edgeF w b x inj M, evolveF (trialF x b p) inj j = evolveF x inj j := by
  intro j hj
  by_cases h3 : j ≤ b - 3
  · exact evolve_prefix (e := b) (fun s hs => by simp [trialF, hs]) j h3
  · obtain ⟨-, h2, -⟩ := tw_range (fixedF w b x inj M) (w+5)
    have hj' : j ≤ b - 3 + (((List.range (w+5)).takeWhile (fixedF w b x inj M)).length : Int) :=
      hj
    have := (fixed_iff w b x inj M (j - b + 2).toNat).1 (h2 _ (by omega)) p hp hM
    rwa [show b - 2 + (((j - b + 2).toNat : Nat) : Int) = j by omega] at this

theorem stepA {w : Nat} {b : Int} {x inj : Int → Bool} {M : Nat} {y : Int → Bool}
    (hy : fitsF w b x M y) :
    fitsF w (edgeF w b x inj M) (evolveF x inj) (advF w b x inj M).2 (evolveF y inj) := by
  set p := blockF (2*w+5) y b with hpdef
  have hp : p < 2 ^ (2*w+5) := block_lt _ _ _
  have ht : ∀ j ≤ b + (2*w+5 : Nat), trialF x b p j = y j := by
    intro j hj
    by_cases hb : j ≤ b
    · simp [trialF, hb, hy.1 j hb]
    · simp only [trialF, hb, if_false, hpdef, block_bit]
      rw [decide_eq_true (show (j - b - 1).toNat < 2*w+5 by omega), Bool.true_and,
        show b + 1 + (((j - b - 1).toNat : Nat) : Int) = j by omega]
  have hpm : p % 2^w = blockF w y b := by
    rw [hpdef, block_mod (by omega)]
  have hM : M.testBit (p % 2^w) = true := by rw [hpm]; exact hy.2
  have hE : ∀ j ≤ b + 2*w + 2, evolveF y inj j = evolveF (trialF x b p) inj j :=
    fun j hj => evolve_congr (fun s _ h2 => (ht s (by omega)).symm)
  have hb := edge_bounds w b x inj M
  refine ⟨fun pos hpos => ?_, ?_⟩
  · rw [hE pos (by omega)]
    exact prefix_trial hp hM pos hpos
  · rw [snd_bit]
    refine ⟨p, hp, hM, block_congr (fun s _ h2 => (hE s (by omega)).symm)⟩

theorem stepB {w : Nat} {b : Int} {x inj : Int → Bool} {M : Nat} {y' : Int → Bool}
    (hy : fitsF w (edgeF w b x inj M) (evolveF x inj) (advF w b x inj M).2 y') :
    ∃ y, fitsF w b x M y ∧ ∀ j ≤ edgeF w b x inj M + w, evolveF y inj j = y' j := by
  obtain ⟨p, hp, hM, hblk⟩ := (snd_bit w b x inj M _).1 hy.2
  refine ⟨trialF x b p, trial_fits hM, fun j hj => ?_⟩
  by_cases hj' : j ≤ edgeF w b x inj M
  · rw [prefix_trial hp hM j hj', hy.1 j hj']
  · have := congrArg (fun n => n.testBit (j - edgeF w b x inj M - 1).toNat) hblk
    simp only [block_bit] at this
    rw [decide_eq_true (show (j - edgeF w b x inj M - 1).toNat < w by omega), Bool.true_and,
      show edgeF w b x inj M + 1 + (((j - edgeF w b x inj M - 1).toNat : Nat) : Int) = j by
        omega] at this
    exact this

theorem stepE {w : Nat} {b : Int} {x inj : Int → Bool} {M : Nat}
    (h : edgeF w b x inj M < b + w + 2) :
    ∃ y, fitsF w b x M y ∧
      evolveF y inj (edgeF w b x inj M + 1) ≠ evolveF x inj (edgeF w b x inj M + 1) := by
  obtain ⟨-, -, h3⟩ := tw_range (fixedF w b x inj M) (w+5)
  have hl : ((List.range (w+5)).takeWhile (fixedF w b x inj M)).length < w + 5 := by
    unfold edgeF at h; omega
  have hf := h3 hl
  rw [← Bool.not_eq_true, fixed_iff] at hf
  push_neg at hf
  obtain ⟨p, hp, hM, hne⟩ := hf
  refine ⟨trialF x b p, trial_fits hM, ?_⟩
  have : edgeF w b x inj M + 1 =
      b - 2 + ((((List.range (w+5)).takeWhile (fixedF w b x inj M)).length : Nat) : Int) := by
    unfold edgeF; omega
  rw [this]
  exact hne

/-! ## padding -/

theorem fold_if_bit (l : List Nat) (c : Nat → Bool) (acc n : Nat) :
    (l.foldl (fun a p => if c p = true then a ||| ((1 : Nat) <<< p) else a) acc).testBit n =
      (acc.testBit n || l.any (fun p => c p && decide (p = n))) := by
  induction l generalizing acc with
  | nil => simp
  | cons p t ih =>
    rw [List.foldl_cons, ih, List.any_cons]
    cases hc : c p
    · simp
    · rw [if_pos rfl, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
      simp only [Bool.true_and, Bool.or_assoc]

theorem pad_bit (u mask w q : Nat) :
    (padF u mask w).testBit q = true ↔ q < 2 ^ w ∧ mask.testBit (q % 2^u) = true := by
  unfold padF
  rw [fold_if_bit]
  simp only [Nat.zero_testBit, Bool.false_or, List.any_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨p, hp, hc, rfl⟩
    exact ⟨hp, hc⟩
  · rintro ⟨hq, hc⟩
    exact ⟨q, hq, hc, rfl⟩

theorem pad_fits {u w : Nat} (h : u ≤ w) (b : Int) (x : Int → Bool) (mask : Nat)
    (y : Int → Bool) : fitsF w b x (padF u mask w) y ↔ fitsF u b x mask y := by
  unfold fitsF
  rw [pad_bit, block_mod h]
  simp [block_lt]

/-! ## the flipped seed -/

theorem flip_run (inj : Nat → Int → Bool) (y y' : Int → Bool) (q : Int)
    (h : ∀ s > q, y s = y' s) (hq : y q ≠ y' q) : ∀ k : Nat,
    (∀ s > q + k, runF inj k y s = runF inj k y' s) ∧
      runF inj k y (q + k) ≠ runF inj k y' (q + k)
  | 0 => by simpa using ⟨h, hq⟩
  | k+1 => by
    obtain ⟨a, c⟩ := flip_run inj y y' q h hq k
    have := evolve_right (inj := inj k) a c
    rw [run_succ, run_succ]
    push_cast
    rw [show q + ((k:Int) + 1) = q + k + 1 by ring]
    exact ⟨fun s hs => this.1 s (by omega), this.2⟩

theorem agree_bound (inj : Nat → Int → Bool) (u : Nat) (b : Int) (x : Int → Bool) (mask : Nat)
    (hm : mask.testBit (blockF u x b) = true) (k : Nat) (f : Int)
    (h : ∀ seed, fitsF u b x mask seed → ∀ z ≤ f, runF inj k seed z = runF inj k x z) :
    f ≤ b + u + k := by
  by_contra hc
  let xf : Int → Bool := fun j => if j = b + u + 1 then !x j else x j
  have hfit : fitsF u b x mask xf := by
    refine ⟨fun pos hp => by simp [xf, show pos ≠ b + u + 1 by omega], ?_⟩
    rw [block_congr (t' := x) (fun s _ h2 => by simp [xf, show s ≠ b + u + 1 by omega])]
    exact hm
  have hr := (flip_run inj xf x (b+u+1) (fun s hs => by simp [xf, show s ≠ b + u + 1 by omega])
    (by simp [xf]) k).2
  exact hr (h xf hfit _ (by omega))

theorem real_le (inj : Nat → Int → Bool) (u : Nat) (b : Int) (x : Int → Bool) (mask : Nat)
    (k : Nat) (e f : Int) (he : realF inj u b x mask k e)
    (h : ∀ seed, fitsF u b x mask seed → ∀ z ≤ f, runF inj k seed z = runF inj k x z) :
    f ≤ e := by
  by_contra hc
  obtain ⟨s, hs, hne⟩ := he.2
  exact hne (h s hs _ (by omega))

theorem real_unique (inj : Nat → Int → Bool) (u : Nat) (b : Int) (x : Int → Bool) (mask : Nat)
    (k : Nat) (e f : Int) (he : realF inj u b x mask k e) (hf : realF inj u b x mask k f) :
    e = f :=
  le_antisymm (real_le inj u b x mask k f e hf he.1) (real_le inj u b x mask k e f he hf.1)


/-! ## the tracked rounds -/

def St (inj : Nat → Int → Bool) (u : Nat) (b : Int) (x : Int → Bool) (mask w k : Nat) :
    (Int → Bool) × Int × Nat :=
  trackF inj x b (padF u mask w) w k

section rounds
variable (inj : Nat → Int → Bool) (u : Nat) (b : Int) (x : Int → Bool) (mask w : Nat)

theorem tr1 (k : Nat) : (St inj u b x mask w (k+1)).1 =
    evolveF (St inj u b x mask w k).1 (inj k) := by
  unfold St; rw [track_succ]

theorem tr2 (k : Nat) : (St inj u b x mask w (k+1)).2.1 =
    edgeF w (St inj u b x mask w k).2.1 (St inj u b x mask w k).1 (inj k)
      (St inj u b x mask w k).2.2 := by
  unfold St; rw [track_succ]

theorem tr3 (k : Nat) : (St inj u b x mask w (k+1)).2.2 =
    (advF w (St inj u b x mask w k).2.1 (St inj u b x mask w k).1 (inj k)
      (St inj u b x mask w k).2.2).2 := by
  unfold St; rw [track_succ]

theorem St_fst (k : Nat) : (St inj u b x mask w k).1 = runF inj k x := track_fst _ _ _ _ _ k

theorem St1 : (St inj u b x mask w 1).2.1 = edgeF w b x (inj 0) (padF u mask w) := tr2 _ _ _ _ _ _ 0

theorem inv1 (hw : u ≤ w) : ∀ k seed, fitsF u b x mask seed →
    fitsF w (St inj u b x mask w k).2.1 (St inj u b x mask w k).1 (St inj u b x mask w k).2.2
      (runF inj k seed)
  | 0, seed, hs => (pad_fits hw b x mask seed).2 hs
  | k+1, seed, hs => by
    rw [tr1, tr2, tr3, run_succ]
    exact stepA (inv1 hw k seed hs)

theorem inv4 : ∀ k : Nat, (St inj u b x mask w 1).2.1 - 3 * (k : Int) ≤
    (St inj u b x mask w (k+1)).2.1
  | 0 => by simp
  | k+1 => by
    have h := inv4 k
    have hb := edge_bounds w (St inj u b x mask w (k+1)).2.1 (St inj u b x mask w (k+1)).1
      (inj (k+1)) (St inj u b x mask w (k+1)).2.2
    rw [tr2 _ _ _ _ _ _ (k+1)]
    push_cast
    omega

theorem inv3 (hw : u ≤ w) : ∀ k y,
    fitsF w (St inj u b x mask w (k+1)).2.1 (St inj u b x mask w (k+1)).1
      (St inj u b x mask w (k+1)).2.2 y →
    ∃ seed, fitsF u b x mask seed ∧
      ∀ j ≤ (St inj u b x mask w 1).2.1 + w - 3 * (k : Int), runF inj (k+1) seed j = y j
  | 0, y', hy' => by
    rw [tr1, tr2, tr3] at hy'
    obtain ⟨y, hy, hyy⟩ := stepB hy'
    refine ⟨y, (pad_fits hw b x mask y).1 hy, fun j hj => ?_⟩
    rw [run_succ, run_zero]
    rw [St1] at hj
    exact hyy j (by simp only [Nat.cast_zero, mul_zero, sub_zero] at hj; exact hj)
  | k+1, y', hy' => by
    rw [tr1 _ _ _ _ _ _ (k+1), tr2 _ _ _ _ _ _ (k+1), tr3 _ _ _ _ _ _ (k+1)] at hy'
    obtain ⟨y, hy, hyy⟩ := stepB hy'
    obtain ⟨seed, hs, hseed⟩ := inv3 hw k y hy
    refine ⟨seed, hs, fun j hj => ?_⟩
    have h4 := inv4 inj u b x mask w (k+1)
    rw [tr2 _ _ _ _ _ _ (k+1)] at h4
    push_cast at hj h4
    rw [run_succ, evolve_prefix (e := (St inj u b x mask w 1).2.1 + w - 3 * (k : Int)) hseed j
      (by omega)]
    exact hyy j (by omega)

theorem part1 (hw : u ≤ w) (k : Nat) : ∀ seed, fitsF u b x mask seed →
    ∀ z ≤ (St inj u b x mask w k).2.1, runF inj k seed z = runF inj k x z := by
  intro seed hs z hz
  rw [← St_fst inj u b x mask w k]
  exact (inv1 inj u b x mask w hw k seed hs).1 z hz

theorem real_first (hw : u ≤ w) (hm : mask.testBit (blockF u x b) = true) :
    realF inj u b x mask 1 (St inj u b x mask w 1).2.1 := by
  have p1 := part1 inj u b x mask w hw 1
  refine ⟨p1, ?_⟩
  have hb := edge_bounds w b x (inj 0) (padF u mask w)
  rw [St1] at p1 ⊢
  by_cases h : edgeF w b x (inj 0) (padF u mask w) < b + w + 2
  · obtain ⟨y, hy, hne⟩ := stepE h
    refine ⟨y, (pad_fits hw b x mask y).1 hy, ?_⟩
    rw [run_succ, run_succ, run_zero, run_zero]
    exact hne
  · exfalso
    have := agree_bound inj u b x mask hm 1 _ p1
    push_cast at this
    omega

theorem real_final (hw : u ≤ w) (hm : mask.testBit (blockF u x b) = true) : ∀ k : Nat,
    (St inj u b x mask w (k+1)).2.1 + 1 + 3 * (k : Int) ≤ (St inj u b x mask w 1).2.1 + w →
    realF inj u b x mask (k+1) (St inj u b x mask w (k+1)).2.1
  | 0 => fun _ => real_first inj u b x mask w hw hm
  | k+1 => fun hle => by
    refine ⟨part1 inj u b x mask w hw (k+1+1), ?_⟩
    have hb := edge_bounds w (St inj u b x mask w (k+1)).2.1 (St inj u b x mask w (k+1)).1
      (inj (k+1)) (St inj u b x mask w (k+1)).2.2
    have h4 := inv4 inj u b x mask w k
    have e2 := tr2 inj u b x mask w (k+1)
    by_cases h : edgeF w (St inj u b x mask w (k+1)).2.1 (St inj u b x mask w (k+1)).1
      (inj (k+1)) (St inj u b x mask w (k+1)).2.2 < (St inj u b x mask w (k+1)).2.1 + w + 2
    · obtain ⟨y, hy, hne⟩ := stepE h
      have hy2 := stepA (inj := inj (k+1)) hy
      rw [← tr1, ← tr2, ← tr3] at hy2
      obtain ⟨seed, hs, hseed⟩ := inv3 inj u b x mask w hw (k+1) _ hy2
      refine ⟨seed, hs, ?_⟩
      push_cast at hle
      rw [hseed _ (by omega), ← St_fst, tr1, e2]
      exact hne
    · exfalso
      push_cast at hle
      omega

end rounds

theorem main (u n v : Nat) (b : Int) (x : Int → Bool) (mask : Nat) (inj : Nat → Int → Bool)
    (hn : 0 < n) (hm : mask.testBit (blockF u x b) = true) :
    ∃ E₁ E : Int, realF inj u b x mask 1 E₁ ∧ realF inj u b x mask n E ∧
      E ≤ b+(u : Int)+(n : Int) ∧
      0 ≤ E-E₁+3*((n-1 : Nat) : Int) ∧
      (∀ w : Nat, u ≤ w →
        (St inj u b x mask w 1).2.1 = E₁ ∧ (St inj u b x mask w n).2.1 ≤ E ∧
        (∀ z : Int, z+3*((n-1 : Nat) : Int) ≤ (St inj u b x mask w 1).2.1+(w : Int) →
          ∀ observed : Int → Bool,
            (∃ y, fitsF w (St inj u b x mask w n).2.1 (St inj u b x mask w n).1
              (St inj u b x mask w n).2.2 y ∧ ∀ j ≤ z, y j = observed j) ↔
            (∃ seed, fitsF u b x mask seed ∧ ∀ j ≤ z, runF inj n seed j = observed j)) ∧
        ((St inj u b x mask w n).2.1+((max 1 v : Nat) : Int)+3*((n-1 : Nat) : Int) ≤
            (St inj u b x mask w 1).2.1+(w : Int) ↔
          E-E₁+3*((n-1 : Nat) : Int)+((max 1 v : Nat) : Int) ≤ (w : Int)) ∧
        ((St inj u b x mask w n).2.1+((max 1 v : Nat) : Int)+3*((n-1 : Nat) : Int) ≤
            (St inj u b x mask w 1).2.1+(w : Int) →
          (St inj u b x mask w n).2.1 = E ∧
          ∀ val : Fin (2^v),
            (∃ word : Fin (2^w), (St inj u b x mask w n).2.2.testBit word.val = true ∧
              word.val % (2^v) = val.val) ↔
            (∃ seed, fitsF u b x mask seed ∧ blockF v (runF inj n seed) E = val.val))) ∧
      E-E₁+3*((n-1 : Nat) : Int)+((max 1 v : Nat) : Int) ≤
        (u : Int)+4*(n : Int)+((max 1 v : Nat) : Int) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [show k + 1 - 1 = k by omega]
  have ht1 : 1 ≤ max 1 v ∧ v ≤ max 1 v := ⟨le_max_left _ _, le_max_right _ _⟩
  have hbW := edge_bounds (u + 4*(k+1) + 1) b x (inj 0) (padF u mask (u + 4*(k+1) + 1))
  have hbu := edge_bounds u b x (inj 0) (padF u mask u)
  rw [← St1] at hbW hbu
  have hFW := agree_bound inj u b x mask hm (k+1) _
    (part1 inj u b x mask (u + 4*(k+1) + 1) (by omega) (k+1))
  have hRW := real_final inj u b x mask (u + 4*(k+1) + 1) (by omega) hm k (by push_cast at hFW ⊢; omega)
  have hE := agree_bound inj u b x mask hm (k+1) _ hRW.1
  have hFu := real_le inj u b x mask (k+1) _ _ hRW (part1 inj u b x mask u le_rfl (k+1))
  have h4u := inv4 inj u b x mask u k
  refine ⟨(St inj u b x mask u 1).2.1, (St inj u b x mask (u + 4*(k+1) + 1) (k+1)).2.1,
    real_first inj u b x mask u le_rfl hm, hRW, hE, by omega, ?_, by push_cast at hE ⊢; omega⟩
  intro w hw
  have hf := real_unique inj u b x mask 1 _ _ (real_first inj u b x mask w hw hm)
    (real_first inj u b x mask u le_rfl hm)
  have hFE := real_le inj u b x mask (k+1) _ _ hRW (part1 inj u b x mask w hw (k+1))
  have h4 := inv4 inj u b x mask w k
  have hpass : (St inj u b x mask w (k+1)).2.1+((max 1 v : Nat) : Int)+3*(k : Int) ≤
      (St inj u b x mask w 1).2.1+(w : Int) →
      (St inj u b x mask w (k+1)).2.1 = (St inj u b x mask (u + 4*(k+1) + 1) (k+1)).2.1 :=
    fun hp => real_unique inj u b x mask (k+1) _ _
      (real_final inj u b x mask w hw hm k (by omega)) hRW
  refine ⟨hf, hFE, ?_, ?_, ?_⟩
  · intro z hz obs
    constructor
    · rintro ⟨y, hy, hyo⟩
      obtain ⟨seed, hs, hseed⟩ := inv3 inj u b x mask w hw k y hy
      exact ⟨seed, hs, fun j hj => (hseed j (by omega)).trans (hyo j hj)⟩
    · rintro ⟨seed, hs, hso⟩
      exact ⟨_, inv1 inj u b x mask w hw (k+1) seed hs, hso⟩
  · constructor
    · intro hp
      have := hpass hp
      omega
    · intro hp
      omega
  · intro hp
    have hvw : v ≤ w := by omega
    refine ⟨hpass hp, fun val => ?_⟩
    constructor
    · rintro ⟨word, hw1, hw2⟩
      have hyfit : fitsF w (St inj u b x mask w (k+1)).2.1 (St inj u b x mask w (k+1)).1
          (St inj u b x mask w (k+1)).2.2
          (trialF (St inj u b x mask w (k+1)).1 (St inj u b x mask w (k+1)).2.1 word.val) :=
        trial_fits (by rw [Nat.mod_eq_of_lt word.isLt]; exact hw1)
      obtain ⟨seed, hs, hseed⟩ := inv3 inj u b x mask w hw k _ hyfit
      refine ⟨seed, hs, ?_⟩
      rw [← hpass hp, block_congr (t' := trialF (St inj u b x mask w (k+1)).1
        (St inj u b x mask w (k+1)).2.1 word.val) (fun s _ h2 => hseed s (by omega)),
        trial_block, hw2]
    · rintro ⟨seed, hs, hb⟩
      have hy := inv1 inj u b x mask w hw (k+1) seed hs
      refine ⟨⟨blockF w (runF inj (k+1) seed) (St inj u b x mask w (k+1)).2.1, block_lt _ _ _⟩,
        hy.2, ?_⟩
      simp only
      rw [block_mod hvw, hpass hp, hb]

end PEqualNP.Outside.L_meta_25605

open PEqualNP.Outside.L_meta_25605 in
theorem PEqualNP.Outside.L_meta_25605 :
    let mix := fun (x : Int → Bool) (z : Int) => xor (xor (x (z-1)) (x z)) (x (z+1))
    let evolve := fun (x injection : Int → Bool) (z : Int) =>
      xor (xor (mix x z) (!(mix x (z+1)) && mix x (z+2))) (injection z)
    let block := fun (width : Nat) (tape : Int → Bool) (edge : Int) =>
      (List.range width).foldl (fun (number bitIndex : Nat) =>
        number ||| ((tape (edge+1+(bitIndex : Int))).toNat <<< bitIndex)) 0
    let fits := fun (width : Nat) (edge : Int) (sample : Int → Bool) (mask : Nat) (tape : Int → Bool) =>
      (∀ pos ≤ edge, tape pos = sample pos) ∧ mask.testBit (block width tape edge) = true
    let advance := fun (w : Nat) (b : Int) (x inj : Int → Bool) (admit : Nat) =>
      let tails := (List.range (2 ^ (2*w+5))).filter (fun pattern => admit.testBit (pattern % 2^w))
      let trial := fun (completionCode : Nat) (site : Int) =>
        if site ≤ b then x site else completionCode.testBit (site-b-1).toNat
      let reference := evolve x inj
      let fixed := fun (offset : Nat) =>
        let site := b-2+(offset : Int)
        tails.all (fun comparisonCode => evolve (trial comparisonCode) inj site == reference site)
      let newEdge := b-3+(((List.range (w+5)).takeWhile fixed).length : Int)
      let newMask := tails.foldl (fun acc outputCode =>
        acc ||| ((1 : Nat) <<< block w (evolve (trial outputCode) inj) newEdge)) 0
      (newEdge, newMask)
    ∀ (u n v : Nat) (b : Int) (x : Int → Bool) (mask : Nat)
        (inj : Nat → Int → Bool), 0 < n → mask.testBit (block u x b) = true →
      let run := fun (length : Nat) (seed : Int → Bool) =>
        (List.range length).foldl (fun st tick => evolve st (inj tick)) seed
      let realEdge := fun (length : Nat) (edge : Int) =>
        (∀ seed, fits u b x mask seed → ∀ z ≤ edge, run length seed z = run length x z) ∧
        (∃ seed, fits u b x mask seed ∧ run length seed (edge+1) ≠ run length x (edge+1))
      let pad := fun (w : Nat) => (List.range (2^w)).foldl (fun (acc pat : Nat) =>
        if mask.testBit (pat % (2^u)) then acc ||| ((1 : Nat) <<< pat) else acc) 0
      let track := fun (w len : Nat) =>
        (List.range len).foldl (fun (st : (Int → Bool) × Int × Nat) tick =>
          let nxt := advance w st.2.1 st.1 (inj tick) st.2.2
          (evolve st.1 (inj tick), nxt.1, nxt.2)) (x, b, pad w)
      let t := max 1 v
      ∃ E₁ E : Int, realEdge 1 E₁ ∧ realEdge n E ∧ E ≤ b+(u : Int)+(n : Int) ∧
        let G := E-E₁+3*((n-1 : Nat) : Int)
        0 ≤ G ∧
        (∀ w : Nat, u ≤ w →
          let first := (track w 1).2.1
          let final := track w n
          let F := final.2.1
          let pass := F+(t : Int)+3*((n-1 : Nat) : Int) ≤ first+(w : Int)
          first = E₁ ∧ F ≤ E ∧
          (∀ z : Int, z+3*((n-1 : Nat) : Int) ≤ first+(w : Int) →
            ∀ observed : Int → Bool,
              (∃ y, fits w F final.1 final.2.2 y ∧ ∀ j ≤ z, y j = observed j) ↔
              (∃ seed, fits u b x mask seed ∧ ∀ j ≤ z, run n seed j = observed j)) ∧
          (pass ↔ G+(t : Int) ≤ (w : Int)) ∧
          (pass → F = E ∧
            ∀ val : Fin (2^v),
              (∃ word : Fin (2^w), final.2.2.testBit word.val = true ∧
                word.val % (2^v) = val.val) ↔
              (∃ seed, fits u b x mask seed ∧ block v (run n seed) E = val.val))) ∧
        G+(t : Int) ≤ (u : Int)+4*(n : Int)+(t : Int) := by
  intro mix evolve block fits advance u n v b x mask inj hn hm run realEdge pad track t
  exact main u n v b x mask inj hn hm
