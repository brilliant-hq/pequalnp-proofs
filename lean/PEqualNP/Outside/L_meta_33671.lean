import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33671

def Reg {N : ℕ} (t : ℕ) (G : Fin N → Fin N → Bool) : Prop :=
  (∀ x, (Finset.univ.filter (fun y => G x y)).card = t) ∧
  (∀ y, (Finset.univ.filter (fun x => G x y)).card = t)

def bit (b : Bool) : ℝ := if b then 1 else 0

def score {N : ℕ} (W : Fin N → Fin N → ℝ) (G : Fin N → Fin N → Bool) : ℝ :=
  ∑ x, ∑ y, W x y * bit (G x y)

theorem countPerm {ι : Type} [Fintype ι] (p : ι → Prop) [DecidablePred p] (e : Equiv.Perm ι) :
    (Finset.univ.filter (fun x => p (e x))).card = (Finset.univ.filter p).card := by
  simpa only [Finset.card_filter] using Equiv.sum_comp e (fun x => if p x then (1 : ℕ) else 0)

theorem countLt {N : ℕ} (v : Fin N) : (Finset.univ.filter (· < v)).card = v.val := by
  convert Fin.card_Iio v using 2
  ext
  simp

def swTest {n : ℕ} (v i : Fin (n+2)) (b : Bool) (j x y : Fin (n+2)) : Bool :=
  let x' := Equiv.swap i 1 (if b then Equiv.swap 0 i x else x)
  let y' := Equiv.swap v 1 (y-j)
  decide (y' - x' < v)

theorem countSw {n : ℕ} (v i : Fin (n+2)) (b : Bool) (j : Fin (n+2)) :
    Reg v.val (swTest v i b j) := by
  let r : Equiv.Perm (Fin (n+2)) := (if b then Equiv.swap 0 i else Equiv.refl _).trans (Equiv.swap i 1)
  let c := (Equiv.subRight j).trans (Equiv.swap v 1)
  have he x y : swTest v i b j x y = decide (c y - r x < v) := by cases b <;> rfl
  constructor
  · intro x
    simp only [he, decide_eq_true_eq]
    exact (countPerm (· < v) (c.trans (Equiv.subRight (r x)))).trans (countLt v)
  · intro y
    simp only [he, decide_eq_true_eq]
    exact (countPerm (· < v) (r.trans (Equiv.subLeft (c y)))).trans (countLt v)

theorem swBalance {n : ℕ} (v i : Fin (n+2)) (b : Bool) (x y : Fin (n+2)) :
    ∑ j, bit (swTest v i b j x y) = v.val := by
  let u := Equiv.swap i 1 (if b then Equiv.swap 0 i x else x)
  let e := ((Equiv.subLeft y).trans (Equiv.swap v 1)).trans (Equiv.subRight u)
  change (∑ j, if decide (e j < v) then (1 : ℝ) else 0) = _
  simp only [decide_eq_true_eq, Finset.sum_boole, countPerm (· < v) e, countLt]

theorem swScoreSum {n : ℕ} (v i : Fin (n+2)) (b : Bool) (W : Fin (n+2) → Fin (n+2) → ℝ) :
    ∑ j, score W (swTest v i b j) = (∑ x, ∑ y, W x y) * v.val := by
  unfold score
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun j y => _ * bit (swTest v i b j _ y)), ← Finset.mul_sum, swBalance, Finset.sum_mul]

theorem deltaBand {n : ℕ} (v z : Fin (n+2)) (hv : v ≠ 0) :
    bit (decide (z < v)) - bit (decide (z - 1 < v)) =
      (if z = 0 then 1 else 0) - (if z = v then 1 else 0) := by
  have hv' := Fin.pos_iff_ne_zero.mpr hv
  by_cases hz : z = 0
  · subst z
    have h : ¬ ((0:Fin (n+2))-1 < v) := by
      simp only [zero_sub, Fin.lt_def, Fin.val_neg, one_ne_zero, ite_false, Fin.val_one]
      omega
    simp only [bit, decide_eq_true_eq, ite_eq_left hv', ite_eq_right h, ite_true,
      ite_eq_right (Ne.symm hv)]
  · have h : z - 1 < v ↔ z ≤ v := by
      simp only [Fin.lt_def, Fin.le_def, Fin.val_sub_one_of_ne_zero hz]
      have := (Fin.pos_iff_ne_zero.mpr hz : 0 < z)
      omega
    rcases lt_trichotomy z v with he | he | he
    · simp [bit, h, he, hz, he.le, he.ne]
    · subst z; simp [bit, hv, h]
    · simp [bit, h, he.not_ge, he.not_gt, hz, he.ne']

theorem swScoreDiff {n : ℕ} (v i : Fin (n+2)) (hv : v ≠ 0) (hi : i ≠ 0)
    (W : Fin (n+2) → Fin (n+2) → ℝ) (j : Fin (n+2)) :
    score W (swTest v i false j) - score W (swTest v i true j) =
    (W i (j+1) - W 0 (j+1)) - (W i j - W 0 j) := by
  let z := fun y : Fin (n+2) => Equiv.swap v 1 (y-j)
  have h0 : Equiv.swap v 1 0 = 0 := Equiv.swap_apply_of_ne_of_ne hv.symm zero_ne_one
  have z0 y : z y = 0 ↔ y = j := by
    change Equiv.swap v 1 (y-j) = 0 ↔ _
    rw [← h0, EmbeddingLike.apply_eq_iff_eq, sub_eq_zero]
  have zv y : z y = v ↔ y = j+1 := by
    change Equiv.swap v 1 (y-j) = v ↔ _
    conv_lhs => rhs; rw [← Equiv.swap_apply_right v 1]
    rw [EmbeddingLike.apply_eq_iff_eq, sub_eq_iff_eq_add, add_comm (1 : Fin (n+2)) j]
  let d := fun y : Fin (n+2) => (if y=j then (1:ℝ) else 0) - (if y=j+1 then 1 else 0)
  have hd y : bit (decide (z y < v)) - bit (decide (z y - 1 < v)) = d y := by
    simpa only [z0, zv, d] using deltaBand v (z y) hv
  have diff x y : bit (swTest v i false j x y) - bit (swTest v i true j x y) =
      (if x=0 then d y else 0) - (if x=i then d y else 0) := by
    have hr : Equiv.swap i 1 0 = 0 := Equiv.swap_apply_of_ne_of_ne hi.symm zero_ne_one
    by_cases hx : x=0
    · subst x; simpa [swTest, hr, hi.symm, z] using hd y
    by_cases hxi : x=i
    · subst x; simpa [swTest, hr, hi, z] using congrArg Neg.neg (hd y)
    · simp [swTest, Equiv.swap_apply_of_ne_of_ne hx hxi, hx, hxi]
  unfold score
  simp_rw [← Finset.sum_sub_distrib, ← mul_sub, diff, mul_sub, Finset.sum_sub_distrib]
  simp [d, mul_ite, mul_sub, Finset.sum_sub_distrib]
  ring

open Fin.NatCast in
theorem cycleUp {N : ℕ} [NeZero N] (f p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hf : ∀ i, f (i+1) - f i ≤ p i) (y z : Fin N) :
    f y - f z ≤ ∑ i, p i := by
  let e (k : ℕ) : Fin N := (k : Fin N) + z
  have hk (k : ℕ) : e (k+1) = e k + 1 := by simp [e, add_right_comm]
  have hy : e (y-z).val = y := by simp [e]
  have hz : e 0 = z := by simp [e]
  calc
    f y - f z = ∑ k ∈ Finset.range (y-z).val, (f (e (k+1)) - f (e k)) := by
      rw [Finset.sum_range_sub (fun k => f (e k)), hy, hz]
    _ ≤ ∑ k ∈ Finset.range (y-z).val, p (e k) :=
      Finset.sum_le_sum fun k _ => by rw [hk]; exact hf (e k)
    _ ≤ ∑ k ∈ Finset.range N, p (e k) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (y-z).isLt.le) (fun a _ _ => hp _)
    _ = ∑ i, p i := by
      rw [← Fin.sum_univ_eq_sum_range]
      simpa [e] using Equiv.sum_comp (Equiv.addRight z) p

theorem switchOsc {n : ℕ} (v i : Fin (n+2)) (hv : v ≠ 0) (hi : i ≠ 0)
    (W : Fin (n+2) → Fin (n+2) → ℝ) (B : ℝ)
    (ht : ∀ b j, score W (swTest v i b j) ≤ B) (y z : Fin (n+2)) :
    (W i y - W 0 y) - (W i z - W 0 z) ≤
      (n+2 : ℝ)*B - (∑ x, ∑ j, W x j) * v.val := by
  let p := fun j => B - score W (swTest v i true j)
  calc
    _ ≤ ∑ j, p j := by
      apply cycleUp (fun y => W i y - W 0 y)
      · exact fun j => sub_nonneg.mpr (ht true j)
      · intro j
        rw [← swScoreDiff v i hv hi]
        exact sub_le_sub_right (ht false j) _
    _ = _ := by simp [p, Finset.sum_sub_distrib, swScoreSum]

theorem rowDeviation {N t : ℕ} (u : Fin N → Bool) (hu : (Finset.univ.filter (fun y => u y)).card = t)
    (f : Fin N → ℝ) (R : ℝ) (hR : ∀ y z, f y - f z ≤ R) :
    (∑ y, f y * ((N : ℝ) * bit (u y) - t)) ≤ (t : ℝ) * (N-t : ℕ) * R := by
  classical
  let U := Finset.univ.filter (fun y => u y)
  have hU : U.card = t := hu
  have hV : Uᶜ.card = N-t := by simp [Finset.card_compl, hU]
  have hNt : t ≤ N := by simpa only [hU, Fintype.card_fin] using Finset.card_le_univ U
  have part := Finset.sum_add_sum_compl U f
  have sel : (∑ y, f y * bit (u y)) = ∑ y ∈ U, f y := by
    simp [bit, U, Finset.sum_filter, mul_ite]
  have h := Finset.sum_le_sum (s := U) (fun y _ =>
    Finset.sum_le_sum (s := Uᶜ) (fun z _ => hR y z))
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hV, hU, ← Finset.mul_sum] at h
  simp_rw [mul_sub, ← mul_left_comm (N : ℝ), Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, sel]
  push_cast [Nat.cast_sub hNt] at *
  nlinarith

theorem scoreDeviation {n : ℕ} (v : Fin (n+2)) (hv : v ≠ 0)
    (W : Fin (n+2) → Fin (n+2) → ℝ) (B : ℝ)
    (ht : ∀ i ≠ 0, ∀ b j, score W (swTest v i b j) ≤ B)
    (G : Fin (n+2) → Fin (n+2) → Bool) (hG : Reg v.val G) :
    (n+2 : ℝ)*score W G - (∑ x, ∑ j, W x j)*v.val ≤
      (n+1 : ℝ)*v.val*(n+2-v.val : ℕ)*((n+2 : ℝ)*B - (∑ x, ∑ j, W x j)*v.val) := by
  let k (x y : Fin (n+2)) := (n+2 : ℝ)*bit (G x y) - v.val
  have col y : ∑ x, k x y = 0 := by
    simp only [k, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp [bit, Finset.sum_boole, hG.2 y]
  have cancel : ∑ x, ∑ y, W 0 y * k x y = 0 := by
    rw [Finset.sum_comm]; simp [← Finset.mul_sum, col]
  have equ : (n+2 : ℝ)*score W G - (∑ x, ∑ y, W x y)*v.val =
      ∑ x, ∑ y, (W x y - W 0 y)*k x y := by
    simp_rw [sub_mul, Finset.sum_sub_distrib, cancel, sub_zero, k, mul_sub, Finset.sum_sub_distrib]
    unfold score
    simp_rw [Finset.mul_sum, Finset.sum_mul, mul_left_comm (n+2 : ℝ)]
  rw [equ, Fin.sum_univ_succ]
  simp only [sub_self, zero_mul, Finset.sum_const_zero, zero_add]
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (n+1)))) (fun i _ =>
    rowDeviation (G i.succ) (hG.1 i.succ) (fun y => W i.succ y - W 0 y) _
      (switchOsc v i.succ hv (Fin.succ_ne_zero _) W B (ht _ (Fin.succ_ne_zero _))))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  push_cast at h
  simpa [k, mul_assoc] using h

theorem scoreCertificate (N t : ℕ) (ht0 : 0 < t) (ht : t < N) :
    ∃ test : Fin (2*N*(N-1)) → Fin N → Fin N → Bool, (∀ j, Reg t (test j)) ∧
      ∀ (W : Fin N → Fin N → ℝ) (B : ℝ), (∀ j, score W (test j) ≤ B) →
        (∑ x, ∑ y, W x y)*t ≤ N*B ∧
        ∀ G, Reg t G → N*score W G - (∑ x, ∑ y, W x y)*t ≤
          (((N-1)*t*(N-t) : ℕ) : ℝ)*(N*B - (∑ x, ∑ y, W x y)*t) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n+2 := ⟨N-2, by omega⟩
  let v : Fin (n+2) := ⟨t, ht⟩
  have hv : v ≠ 0 := by exact Fin.ne_of_val_ne (by simpa [v] using ht0.ne')
  let e := Fintype.equivFinOfCardEq (α := Bool × Fin (n+1) × Fin (n+2))
    (n := 2*(n+2)*(n+2-1)) (by simp; ring)
  let T := fun (k : Bool × Fin (n+1) × Fin (n+2)) => swTest v k.2.1.succ k.1 k.2.2
  refine ⟨fun j => T (e.symm j), fun j => countSw _ _ _ _, ?_⟩
  intro W B h
  have hh (i : Fin (n+1)) b j : score W (swTest v i.succ b j) ≤ B := by
    simpa [T] using h (e (b,i,j))
  constructor
  · have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hh 0 false j)
    simpa [swScoreSum, v] using hs
  · intro G hG
    have hs := scoreDeviation v hv W B (by
      intro i; refine Fin.cases ?_ (fun i _ => hh i) i; simp) G hG
    simpa [v] using hs

def cellCount {N : ℕ} (G : Fin N → Fin N → Bool) :=
  ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => G z.1 z.2)).card

def mismatch {N : ℕ} (G T : Fin N → Fin N → Bool) :=
  ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => G z.1 z.2 ≠ T z.1 z.2)).card

theorem cellCount_sum {N : ℕ} (G : Fin N → Fin N → Bool) :
    (cellCount G : ℝ) = ∑ x, ∑ y, bit (G x y) := by
  unfold cellCount
  rw [← Finset.sum_boole, Fintype.sum_prod_type]
  rfl

theorem mismatch_score {N : ℕ} (G T : Fin N → Fin N → Bool) :
    (mismatch G T : ℝ) = cellCount G + score (fun x y => 1-2*bit (G x y)) T := by
  unfold mismatch score
  rw [← Finset.sum_boole, Fintype.sum_prod_type, cellCount_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  dsimp only
  cases G x y <;> cases T x y <;> norm_num [bit]

theorem weightedLoss {M N : ℕ} (D : Fin M → Fin N → Fin N → Bool) (w : Fin M → ℝ)
    (hw : ∑ i, w i = 1) :
    let E := ∑ i, w i * cellCount (D i)
    let W := fun x y => ∑ i, w i * (1-2*bit (D i x y))
    (∑ x, ∑ y, W x y) = (N : ℝ)^2 - 2*E ∧
    ∀ T, (∑ i, w i * mismatch (D i) T) = E + score W T := by
  dsimp only
  constructor
  · simp_rw [Finset.sum_comm (f := fun (y : Fin N) (i : Fin M) => w i * (1-2*bit (D i _ y))),
      ← Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, ← cellCount_sum]
    simp [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ← mul_left_comm (2 : ℝ),
      ← Finset.mul_sum, hw, sq]
  · intro T
    simp_rw [mismatch_score, mul_add, Finset.sum_add_distrib]
    congr 1
    unfold score
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    simp [mul_assoc]

theorem lossCertificate (N t : ℕ) (hNt : N < 2*t) (ht : t < N) :
    ∃ test : Fin (2*N*(N-1)) → Fin N → Fin N → Bool, (∀ j, Reg t (test j)) ∧
      ∀ (A M : ℕ) (D : Fin M → Fin N → Fin N → Bool) (w : Fin M → ℝ) (h : ℝ),
        (∀ i, cellCount (D i) ≤ A ∧ 0 ≤ w i) → (∑ i, w i) = 1 →
        let a := 2*t-N
        let V := ((N*t : ℕ) : ℝ) - (a : ℝ)*A/N
        let err := fun T => ∑ i, w i * mismatch (D i) T
        (∀ j, err (test j) ≤ V+h) →
          (∀ T, Reg t T → err T ≤ V+(((N-1)*t*(N-t) : ℕ) : ℝ)*h) ∧
          (a : ℝ)*(A - ∑ i, w i * cellCount (D i)) ≤ N*h := by
  have ht0 : 0 < t := by omega
  obtain ⟨test, hr, hc⟩ := scoreCertificate N t ht0 ht
  refine ⟨test, hr, ?_⟩
  intro A M D w h hD hw
  dsimp only
  intro htests
  let a : ℝ := (2*t-N : ℕ)
  let V : ℝ := ((N*t : ℕ) : ℝ) - a*A/N
  let E := ∑ i, w i * cellCount (D i)
  let W := fun x y => ∑ i, w i * (1-2*bit (D i x y))
  let K : ℝ := ((N-1)*t*(N-t) : ℕ)
  have ha : a = 2*t - N := by simp [a, Nat.cast_sub hNt.le]
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hN : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hV : N*V = N*(N*t) - a*A := by dsimp [V]; push_cast; field_simp
  have hK : 1 ≤ K := by
    change (1 : ℝ) ≤ (((N-1)*t*(N-t) : ℕ) : ℝ)
    exact_mod_cast Nat.succ_le_of_lt (Nat.mul_pos (Nat.mul_pos (by omega) ht0) (by omega))
  obtain ⟨sumW, herr⟩ := weightedLoss D w hw
  change (∑ x, ∑ y, W x y) = _ - 2*E at sumW
  change ∀ T, _ = E + score W T at herr
  have hE : E ≤ A := calc
    _ ≤ ∑ i, w i * A := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hD i).1) (hD i).2
    _ = _ := by rw [← Finset.sum_mul, hw, one_mul]
  have hpass j : score W (test j) ≤ V+h-E := by
    have hh := htests j
    rw [herr] at hh
    change E + _ ≤ V+h at hh
    linarith
  obtain ⟨hmean, hall⟩ := hc W (V+h-E) hpass
  rw [sumW] at hmean
  have hm : a*(A-E) ≤ N*h := by rw [ha] at hV ⊢; nlinarith
  refine ⟨?_, hm⟩
  intro G hG
  rw [herr]
  change E + score W G ≤ V+K*h
  have hh := hall G hG
  rw [sumW] at hh
  change _ ≤ K * _ at hh
  apply le_of_mul_le_mul_left _ hN
  have hKE := mul_nonneg (sub_nonneg.mpr hK) (mul_nonneg ha0 (sub_nonneg.mpr hE))
  rw [ha] at hKE hV
  nlinarith [congrArg (K * ·) hV]

open PEqualNP.CircuitLowerBounds

def ok (g : Gate) : Prop :=
  g.inputs.length ≤ 2 ∧ (g.op = .or ∨ g.op = .and ∨ (g.op = .not ∧ g.inputs.length = 1))

def agree (S : Finset ℕ) (v z : ℕ → Bool) : Prop := ∀ i ∈ S, v i = z i

def fires (g : Gate) (v : ℕ → Bool) := g.op.eval (g.inputs.map v)

theorem gateCert (g : Gate) (hg : ok g) (z : ℕ → Bool) :
    ∃ S : Finset ℕ, S.card ≤ 2 ∧ ∀ v,
      (agree S v z → fires g v = fires g z) ∧
      (S.card = 2 → fires g v = fires g z → agree S v z) := by
  obtain ⟨op, l⟩ := g
  rcases l with _ | ⟨x, l⟩
  · exact ⟨∅, by simp, fun _ => ⟨fun _ => rfl, by simp⟩⟩
  rcases l with _ | ⟨y, l⟩
  · refine ⟨{x}, by simp, fun v => ⟨?_, by simp⟩⟩
    intro h
    simp [fires, h x (by simp)]
  have hlen := hg.1
  change ([x,y] ++ l).length ≤ 2 at hlen
  have hl : l = [] := by simpa using hlen
  subst l
  have hop := hg.2
  change op = .or ∨ op = .and ∨ op = .not ∧ [x,y].length = 1 at hop
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at hop
  rcases hop with rfl | rfl | ⟨_, h⟩
  all_goals try contradiction
  all_goals
    cases hx : z x <;> cases hy : z y
    all_goals first
      | (refine ⟨{x}, by simp, fun v => ⟨?_, by simp⟩⟩; solve | simp +contextual [agree, fires, GateOp.eval, hx, hy])
      | (refine ⟨{y}, by simp, fun v => ⟨?_, by simp⟩⟩; solve | simp +contextual [agree, fires, GateOp.eval, hx, hy])
      | refine ⟨{x,y}, (Finset.card_insert_le ..).trans (by simp), fun v => ?_⟩
        cases h1 : v x <;> cases h2 : v y <;> simp [agree, fires, GateOp.eval, hx, hy, h1, h2]

def readWire (w : List Bool) (i : ℕ) := w.getD i false

def stepWire (w : List Bool) (g : Gate) := w ++ [fires g (readWire w)]

theorem stepRead (g : Gate) (w : List Bool) (i : ℕ) :
    readWire (stepWire w g) i = if i = w.length then fires g (readWire w) else readWire w i := by
  by_cases h : i < w.length
  · rw [ite_eq_right h.ne]; exact List.getD_append _ _ _ _ h
  by_cases he : i = w.length
  · subst i; simp [readWire, stepWire]
  · have h' : (stepWire w g).length ≤ i := by simp [stepWire]; omega
    simp only [readWire, List.getD_eq_default _ _ h', ite_eq_right he,
      List.getD_eq_default _ _ (Nat.le_of_not_gt h)]

theorem stepCert (g : Gate) (hg : ok g) (z : List Bool) (T : Finset ℕ) :
    ∃ S : Finset ℕ, S.card ≤ T.card + 1 ∧ ∀ w : List Bool, w.length = z.length →
      (agree S (readWire w) (readWire z) →
        agree T (readWire (stepWire w g)) (readWire (stepWire z g))) ∧
      (S.card = T.card+1 → agree T (readWire (stepWire w g)) (readWire (stepWire z g)) →
        agree S (readWire w) (readWire z)) := by
  by_cases hn : z.length ∈ T
  · obtain ⟨F, hF, hval⟩ := gateCert g hg (readWire z)
    let S := T.erase z.length ∪ F
    have hcard : S.card ≤ (T.card-1) + F.card := by
      simpa only [Finset.card_erase_of_mem hn] using Finset.card_union_le (T.erase z.length) F
    have hpos := Finset.card_pos.mpr ⟨_, hn⟩
    refine ⟨S, by omega, fun w hw => ⟨?_, ?_⟩⟩
    · intro hh k hk
      simp only [stepRead, hw]
      split_ifs with he
      · exact (hval _).1 (fun i hi => hh i (Finset.mem_union_right _ hi))
      · exact hh k (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he, hk⟩))
    · intro eq hh k hk
      rcases Finset.mem_union.mp hk with hk | hk
      · obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hk
        simpa [stepRead, hw, hne] using hh k hmem
      · apply (hval _).2 (by omega) _ k hk
        simpa [stepRead, hw] using hh _ hn
  · refine ⟨T, by omega, fun w hw => ⟨?_, by omega⟩⟩
    intro h k hk
    have hne : k ≠ z.length := fun e => hn (e ▸ hk)
    simpa [stepRead, hw, hne] using h k hk

theorem gatesCert (gs : List Gate) (hg : ∀ g ∈ gs, ok g) (z : List Bool) (T : Finset ℕ) :
    ∃ S : Finset ℕ, S.card ≤ T.card + gs.length ∧ ∀ w : List Bool, w.length = z.length →
      (agree S (readWire w) (readWire z) →
        agree T (readWire (gs.foldl stepWire w)) (readWire (gs.foldl stepWire z))) ∧
      (S.card = T.card+gs.length → agree T (readWire (gs.foldl stepWire w))
        (readWire (gs.foldl stepWire z)) → agree S (readWire w) (readWire z)) := by
  induction gs generalizing z with
  | nil => exact ⟨T, by simp, fun _ _ => ⟨id, fun _ => id⟩⟩
  | cons g gs ih =>
    obtain ⟨P, hP, hp⟩ := ih (fun a ha => hg a (by simp [ha])) (stepWire z g)
    obtain ⟨S, hS, hs⟩ := stepCert g (hg _ (by simp)) z P
    simp only [List.length_cons, List.foldl_cons]
    refine ⟨S, by omega, fun w hw => ?_⟩
    have hh := hp (stepWire w g) (by simp [stepWire, hw])
    exact ⟨hh.1 ∘ (hs w hw).1, fun hc ha =>
      (hs w hw).2 (by omega) (hh.2 (by omega) ha)⟩

def lineGraph {N : ℕ} (R S : Finset (Fin N)) (x y : Fin N) := decide (x ∈ R ∨ y ∈ S)

theorem lineCount {N : ℕ} (R S : Finset (Fin N)) :
    cellCount (lineGraph R S) + R.card*S.card = (R.card+S.card)*N := by
  let U := (Finset.univ : Finset (Fin N))
  have eq : ((Finset.univ : Finset (Fin N × Fin N)).filter fun p => lineGraph R S p.1 p.2) =
      (R ×ˢ U) ∪ (U ×ˢ S) := by ext p; simp [lineGraph, U]
  have hi : (R ×ˢ U) ∩ (U ×ˢ S) = R ×ˢ S := by ext p; simp [U]
  unfold cellCount
  rw [eq]
  simpa [hi, U, Nat.add_mul, Nat.mul_comm N] using Finset.card_union_add_card_inter (R ×ˢ U) (U ×ˢ S)

theorem countMono {N : ℕ} {G H : Fin N → Fin N → Bool} (h : ∀ x y, G x y → H x y) :
    cellCount G ≤ cellCount H := by
  unfold cellCount
  apply Finset.card_le_card
  exact fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h p.1 p.2 (Finset.mem_filter.mp hp).2⟩

theorem countNeg {N : ℕ} (G : Fin N → Fin N → Bool) :
    cellCount (fun x y => !G x y) + cellCount G = N*N := by
  unfold cellCount
  let F := (Finset.univ : Finset (Fin N × Fin N)).filter fun p => G p.1 p.2
  have eq : (Finset.univ.filter fun p : Fin N × Fin N => (!G p.1 p.2) = true) = Fᶜ := by
    ext p; cases h : G p.1 p.2 <;> simp [F, h]
  rw [eq]; change Fᶜ.card + F.card = _
  simp

theorem splitWires {N : ℕ} (F : Finset ℕ) :
    let R := Finset.univ.filter fun x : Fin N => x.val ∈ F
    let S := Finset.univ.filter fun y : Fin N => N+y.val ∈ F
    R.card + S.card ≤ F.card := by
  intro R S
  let A := R.image Fin.val
  let B := S.image fun y => N+y.val
  have hd : Disjoint A B := by
    rw [Finset.disjoint_left]; intro a ha hb
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, h⟩ := Finset.mem_image.mp hb
    omega
  have h : A ∪ B ⊆ F := by
    intro a ha; rcases Finset.mem_union.mp ha with ha|ha <;>
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha <;> exact (Finset.mem_filter.mp hi).2
  have hA : A.card = R.card := Finset.card_image_of_injective _ Fin.val_injective
  have hB : B.card = S.card := Finset.card_image_of_injective _ (fun _ _ he => Fin.ext (Nat.add_left_cancel he))
  simpa only [Finset.card_union_of_disjoint hd, hA, hB] using Finset.card_le_card h

open PEqualNP.Represents

theorem oneRead {N : ℕ} (x y : Fin N) (i : ℕ) :
    readWire (oneEach x y) i = decide (i=x.val ∨ i=N+y.val) := by
  simp only [readWire, oneEach]
  by_cases hi : i < N
  · rw [List.getD_append _ _ _ _ (by simpa)]
    rw [List.getD_eq_getElem _ _ (by simpa), List.getElem_ofFn]
    simp [Fin.ext_iff, show i ≠ N+y.val by omega]
  · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hi), List.length_ofFn]
    by_cases hj : i-N < N
    · rw [List.getD_eq_getElem _ _ (by simpa), List.getElem_ofFn]
      simp [Fin.ext_iff, show i ≠ x.val by omega, show i-N = y.val ↔ i=N+y.val by omega]
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hj)]
      simp [show i ≠ x.val by omega, show i ≠ N+y.val by omega]

def table {N : ℕ} (C : Circuit) (x y : Fin N) := C.eval (oneEach x y)

theorem areaGap {N g : ℕ} (C : Circuit) (hg : ∀ a ∈ C.gates, ok a) (hs : C.size ≤ g)
    (hN : 2*g+1 < N) (hA : cellCount (table (N := N) C) < (g+1)*N) :
    cellCount (table (N := N) C) ≤ g*N ∨ ∃ R S : Finset (Fin N), R.card+S.card = g+1 ∧
      ∀ x y, table C x y = lineGraph R S x y := by
  let z := List.replicate (N+N) false
  let G := table (N := N) C
  obtain ⟨F, hF, hh⟩ := gatesCert C.gates hg z {C.output}
  simp only [Finset.card_singleton] at hF hh
  change C.gates.length ≤ g at hs
  let R := Finset.univ.filter fun x : Fin N => x.val ∈ F
  let S := Finset.univ.filter fun y : Fin N => N+y.val ∈ F
  have hrs : R.card + S.card ≤ F.card := splitWires F
  have hl := lineCount R S
  have hw (x y : Fin N) : agree F (readWire (oneEach x y)) (readWire z) ↔ x ∉ R ∧ y ∉ S := by
    simp only [agree, oneRead]
    simp [readWire, z, List.getElem?_getD_replicate_default_eq, R, S]
    grind only
  have hxy (x y : Fin N) := hh (oneEach x y) (by simp [z, oneEach])
  simp only [agree, Finset.mem_singleton, forall_eq] at hxy
  change ∀ x y : Fin N, (agree F (readWire (oneEach x y)) (readWire z) → G x y = C.eval z) ∧
    (F.card = 1 + C.gates.length → G x y = C.eval z → agree F (readWire (oneEach x y)) (readWire z)) at hxy
  simp_rw [hw] at hxy
  cases he : C.eval z with
  | true =>
    have h := countMono (G := fun x y => !lineGraph R S x y) (H := G) (by
      intro x y; simp [lineGraph]; intro hx hy; exact (hxy x y).1 ⟨hx, hy⟩ |>.trans he)
    have hn := countNeg (lineGraph R S)
    change cellCount G < _ at hA
    have hbound := Nat.mul_le_mul_right N (show R.card+S.card ≤ g+1 by omega)
    have hmin := Nat.mul_le_mul_right N (show 2*(g+1) ≤ N by omega)
    rw [Nat.mul_assoc] at hmin
    omega
  | false =>
    have sub : ∀ x y, G x y → lineGraph R S x y := by
      intro x y h
      by_contra! h'
      have hm : x ∉ R ∧ y ∉ S := by simpa [lineGraph] using h'
      have hh' := (hxy x y).1 hm
      simp [h, he] at hh'
    by_cases hc : R.card+S.card ≤ g
    · left
      exact (countMono sub).trans (by have := Nat.mul_le_mul_right N hc; omega)
    · right
      refine ⟨R,S, by omega, fun x y => ?_⟩
      cases h : G x y with
      | true => exact h.trans (sub x y h).symm
      | false =>
        have hm := (hxy x y).2 (by omega) (h.trans he.symm)
        change G x y = _
        simp [h, lineGraph, hm.1, hm.2]

def isLines {N : ℕ} (g : ℕ) (C : Circuit) := ∃ R S : Finset (Fin N),
  R.card+S.card = g+1 ∧ ∀ x y, table C x y = lineGraph R S x y

theorem massGap {N g r s M : ℕ} (hr : 0 < r) (hrs : r ≤ s) (hprod : r*s < N)
    (hN : 2*g+1 < N) (D : Fin M → Circuit) (w : Fin M → ℝ) (hw : ∑ i, w i = 1)
    (hD : ∀ i, (∀ a ∈ (D i).gates, ok a) ∧ (D i).size ≤ g ∧
      cellCount (table (N := N) (D i)) ≤ (g+1)*N-r*s ∧ 0 ≤ w i) :
    ((N-r*s : ℕ) : ℝ)*(∑ i, @ite ℝ (isLines (N := N) g (D i)) (Classical.propDecidable _) 0 (w i)) ≤
      (((g+1)*N-r*s : ℕ) : ℝ) - ∑ i, w i * cellCount (table (N := N) (D i)) := by
  classical
  let A := (g+1)*N-r*s
  have hfloor : N ≤ (g+1)*N := by rw [Nat.add_mul]; omega
  have hrpos := Nat.mul_pos hr (hr.trans_le hrs)
  have hpoint i : ((N-r*s : ℕ) : ℝ)*(if isLines (N := N) g (D i) then 0 else w i) ≤
      w i * A - w i * cellCount (table (N := N) (D i)) := by
    obtain ⟨ho,hs,ha,hw⟩ := hD i
    rw [← mul_sub]
    by_cases hl : isLines (N := N) g (D i)
    · simp only [ite_eq_left hl, mul_zero]
      exact mul_nonneg hw (sub_nonneg.mpr (Nat.cast_le.mpr ha))
    · simp only [ite_eq_right hl, mul_comm _ (w i)]
      apply mul_le_mul_of_nonneg_left _ hw
      have hc := (areaGap (D i) ho hs hN (lt_of_le_of_lt ha (by omega))).resolve_right hl
      have hh : N-r*s + cellCount (table (N := N) (D i)) ≤ A := by
        dsimp [A]; rw [Nat.add_mul, Nat.one_mul]; omega
      exact le_sub_iff_add_le.mpr (by exact_mod_cast hh)
  simpa only [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul, hw, one_mul, A] using
    Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)

open PEqualNP.MetaComplexity.NestedCover

theorem readOld (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    readWire (gs.foldl stepWire w) i = readWire w i := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih, stepRead, ite_eq_right hi.ne]
    simp [stepWire]; omega

theorem wireLength (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih, stepWire]; omega

theorem makeOr (n a : ℕ) (l : List ℕ) (ha : a < n) (hl : ∀ i ∈ l, i < n) :
    ∃ C : Circuit, ReadsBack n C ∧ C.output < n+C.size ∧
      (∀ g ∈ C.gates, g.op = .or ∧ g.inputs.length = 2) ∧ C.size = l.length ∧
      ∀ w : List Bool, w.length = n → C.eval w = (a::l).any (readWire w) := by
  induction l using List.reverseRecOn with
  | nil =>
    exact ⟨⟨[],a⟩, by simp [ReadsBack], by simpa [Circuit.size] using ha, by simp,
      rfl, by simp [Circuit.eval, Circuit.wires, readWire]⟩
  | append_singleton l i ih =>
    have hi := hl i (by simp)
    obtain ⟨C, hc, hout, hg, hs, hev⟩ := ih (fun j hj => hl j (by simp [hj]))
    let gate : Gate := ⟨.or, [C.output,i]⟩
    let C' : Circuit := ⟨C.gates ++ [gate], n+C.size⟩
    refine ⟨C', ?_, by simp [C', Circuit.size], ?_, by simp [C', Circuit.size] at hs ⊢; omega, ?_⟩
    · intro j hj
      change j < (C.gates ++ [gate]).length at hj
      simp only [List.length_append, List.length_singleton] at hj
      by_cases hj' : j < C.gates.length
      · simpa only [gateAt, C', List.getD_append _ _ _ _ hj'] using hc j hj'
      · have he : j = C.gates.length := by omega
        subst j
        simp [C', gateAt, gate, Circuit.size] at hout ⊢
        omega
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hg a ha
      · obtain rfl := List.mem_singleton.mp ha
        exact ⟨rfl,rfl⟩
    · intro w hw
      let W := C.gates.foldl stepWire w
      have hlen : W.length = n+C.size := by simp [W, wireLength, hw, Circuit.size]
      change readWire ((C.gates ++ [gate]).foldl stepWire w) (n+C.size) = _
      rw [List.foldl_append]; change readWire (stepWire W gate) (n+C.size) = _
      rw [stepRead, ite_eq_left hlen.symm]
      have he : readWire W C.output = _ := hev w hw
      have ho : readWire W i = readWire w i := readOld _ _ _ (by omega)
      simp [fires, gate, GateOp.eval, he, ho, Bool.or_assoc]

theorem realizeLines {N : ℕ} (R S : Finset (Fin N)) (hp : 0 < R.card+S.card) :
    ∃ C : Circuit, ReadsBack (N+N) C ∧ C.output < N+N+C.size ∧
      (∀ g ∈ C.gates, g.op = .or ∧ g.inputs.length = 2) ∧
      C.size+1 = R.card+S.card ∧ table C = lineGraph R S := by
  let l := R.toList.map Fin.val ++ S.toList.map (fun y => N+y.val)
  have hc : l.length = R.card+S.card := by simp [l]
  have hm (i : ℕ) : i ∈ l ↔ (∃ x ∈ R, x.val = i) ∨ (∃ y ∈ S, N+y.val = i) := by simp [l]
  have hl (i : ℕ) (hi : i ∈ l) : i < N+N := by
    rcases (hm i).mp hi with ⟨x,_,rfl⟩|⟨y,_,rfl⟩ <;> omega
  rcases he : l with _ | ⟨a,k⟩
  · simp [he] at hc; omega
  · have ha := hl a (by simp [he])
    obtain ⟨C, hv, ho, hg, hs, ht⟩ := makeOr (N+N) a k ha (fun i hi => hl i (by simp [he,hi]))
    refine ⟨C, hv, ho, hg, by simpa [he,hs] using hc, ?_⟩
    funext x y
    change C.eval (oneEach x y) = _
    rw [ht _ (by simp [oneEach]), ← he, Bool.eq_iff_iff]
    simp only [List.any_eq_true, oneRead, decide_eq_true_eq, lineGraph]
    simp_rw [hm]
    constructor
    · rintro ⟨i, (⟨p,hp,rfl⟩|⟨p,hp,rfl⟩), (h|h)⟩
      · exact Or.inl (Fin.ext h ▸ hp)
      · omega
      · omega
      · exact Or.inr (Fin.ext (Nat.add_left_cancel h) ▸ hp)
    · rintro (hx|hy)
      · exact ⟨_, Or.inl ⟨_,hx,rfl⟩, Or.inl rfl⟩
      · exact ⟨_, Or.inr ⟨_,hy,rfl⟩, Or.inr rfl⟩

abbrev Slice (N r : ℕ) := {R : Finset (Fin N) // R.card = r}

def ind {N r : ℕ} (R : Slice N r) (x : Fin N) : ℤ := if x ∈ R.val then 1 else 0

def ibit (b : Bool) : ℤ := if b then 1 else 0

def rect {N r s : ℕ} (T : Fin N → Fin N → Bool) (R : Slice N r) (S : Slice N s) : ℤ :=
  ∑ x, ∑ y, ind R x * ind S y * ibit (T x y)

theorem sliceExists {N r : ℕ} (h : r ≤ N) : Nonempty (Slice N r) := by
  obtain ⟨R, _, hr⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin N))) (by simpa using h)
  exact ⟨R,hr⟩

theorem adjacentSlices {N r : ℕ} (h0 : 0 < r) (hr : r < N) (i a : Fin N) :
    ∃ U V : Slice N r, ∀ x, ind U x - ind V x =
      (if x=i then 1 else 0) - (if x=a then 1 else 0) := by
  by_cases h : i=a
  · obtain ⟨U⟩ := sliceExists hr.le
    exact ⟨U,U,fun x => by simp [h]⟩
  let B := ((Finset.univ : Finset (Fin N)).erase i).erase a
  have hc : r-1 ≤ B.card := by
    have ha : a ∈ (Finset.univ : Finset (Fin N)).erase i := by simp [Ne.symm h]
    simp only [B, Finset.card_erase_of_mem ha, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨C,hC,he⟩ := Finset.exists_subset_card_eq hc
  have hi : i ∉ C := fun hi => by simpa [B] using hC hi
  have ha : a ∉ C := fun ha => by simpa [B] using hC ha
  refine ⟨⟨insert i C, by rw [Finset.card_insert_of_notMem hi, he]; omega⟩,
    ⟨insert a C, by rw [Finset.card_insert_of_notMem ha, he]; omega⟩, fun x => ?_⟩
  by_cases hx : x ∈ C
  · have hxi : x ≠ i := by rintro rfl; contradiction
    have hxa : x ≠ a := by rintro rfl; contradiction
    simp [ind, hx, hxi, hxa]
  · simp [ind, hx]

theorem contrastWeights {N r : ℕ} (h0 : 0 < r) (hr : r < N) (i : Fin N) :
    ∃ w : Slice N r → ℤ, (∑ R, w R) = 0 ∧ ∀ x, (∑ R, w R * ind R x) =
      (N : ℤ)*(if x=i then 1 else 0)-1 := by
  classical
  choose U V h using adjacentSlices h0 hr i
  let w (R : Slice N r) := ∑ a, ((if U a=R then (1:ℤ) else 0) - (if V a=R then 1 else 0))
  refine ⟨w, ?_, fun x => ?_⟩
  · unfold w; rw [Finset.sum_comm]; simp [Finset.sum_sub_distrib]
  · simp_rw [w, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, h]
    simp

theorem rectFactor {N r s : ℕ} (T : Fin N → Fin N → Bool) (u : Slice N r → ℤ)
    (v : Slice N s → ℤ) :
    (∑ R, ∑ S, (u R * v S) * rect T R S) =
      ∑ x, ∑ y, (∑ R, u R * ind R x)*(∑ S, v S * ind S y)*ibit (T x y) := by
  unfold rect
  let f (p : Slice N r × Slice N s) (q : Fin N × Fin N) :=
    u p.1 * v p.2 * (ind p.1 q.1 * ind p.2 q.2 * ibit (T q.1 q.2))
  have he := Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := f)
  simp only [Fintype.sum_prod_type, f] at he
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [he]
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro y _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro S _
  apply Finset.sum_congr rfl; intro R _
  ring

theorem rowBits {N t : ℕ} {T : Fin N → Fin N → Bool} (hr : Reg t T) (x : Fin N) :
    (∑ y, ibit (T x y)) = t := by simp [ibit, Finset.sum_boole, hr.1]

theorem colBits {N t : ℕ} {T : Fin N → Fin N → Bool} (hr : Reg t T) (y : Fin N) :
    (∑ x, ibit (T x y)) = t := by simp [ibit, Finset.sum_boole, hr.2]

theorem pointContrast {N t : ℕ} {T : Fin N → Fin N → Bool} (ht : Reg t T) (i j : Fin N) :
    (∑ x, ∑ y, ((N : ℤ)*(if x=i then 1 else 0)-1)*
      ((N : ℤ)*(if y=j then 1 else 0)-1)*ibit (T x y)) =
        N*((N : ℤ)*ibit (T i j)-t) := by
  have hrow x : (∑ y, (((N : ℤ)*(if y=j then 1 else 0)-1)*ibit (T x y))) =
      N*ibit (T x j)-t := by
    simp [sub_mul, ite_mul, Finset.sum_sub_distrib, rowBits ht]
  simp_rw [mul_assoc, ← Finset.mul_sum, hrow, sub_mul, Finset.sum_sub_distrib]
  simp [ite_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, colBits ht]

theorem signedKernel {ι : Type} [Fintype ι] [Nonempty ι] {m : ℕ} (v : Fin m → ι → ℤ)
    (hm : m ≤ Fintype.card ι) :
    ∃ k : ι → ℤ, k ≠ 0 ∧ ∀ j, ∑ i, k i*v j i ≤ 0 := by
  classical
  cases m with
  | zero => exact ⟨1, one_ne_zero, fun j => j.elim0⟩
  | succ p =>
    let A : Matrix (Fin p) ι ℤ := fun j i => v j.succ i - v 0 i
    have hn : ¬ Function.Injective A.mulVecLin := by
      intro hi
      have hh := LinearMap.finrank_le_finrank_of_injective hi
      simp only [Module.finrank_pi, Fintype.card_fin] at hh; omega
    obtain ⟨k, hk, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (mt LinearMap.ker_eq_bot.mp hn)
    have he (j : Fin p) : (∑ i, k i*v j.succ i) = ∑ i, k i*v 0 i := by
      have h := congrFun (LinearMap.mem_ker.mp hk) j
      change (∑ i, (v j.succ i - v 0 i)*k i) = 0 at h
      simpa only [sub_mul, mul_sub, Finset.sum_sub_distrib, sub_eq_zero, mul_comm] using h
    have hall j : (∑ i, k i*v j i) = ∑ i, k i*v 0 i := by
      exact Fin.cases rfl he j
    by_cases h : ∑ i, k i*v 0 i ≤ 0
    · exact ⟨k,hne,fun j => (hall j).le.trans h⟩
    · refine ⟨-k, neg_ne_zero.mpr hne, fun j => ?_⟩
      simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, hall j, neg_nonpos]
      exact le_of_not_ge h

def pointSum {n t : ℕ} (k : Fin n × Fin n → ℤ) (T : Fin (n+1) → Fin (n+1) → Bool) :=
  ∑ p, k p * ((n+1 : ℤ)*ibit (T p.1.succ p.2.succ)-t)

theorem positivePoint {n t : ℕ} (ht : 0 < t) (hN : t < n+2)
    (k : Fin (n+1) × Fin (n+1) → ℤ) (hk : k ≠ 0) :
    ∃ T, Reg t T ∧ 0 < pointSum (t := t) k T := by
  let W : Fin (n+2) → Fin (n+2) → ℝ := Fin.cases 0 fun i => Fin.cases 0 fun j => (k (i,j) : ℝ)
  let v : Fin (n+2) := ⟨t,hN⟩
  have hv : v ≠ 0 := Fin.ne_of_val_ne ht.ne'
  have hid (G : Fin (n+2) → Fin (n+2) → Bool) :
      (pointSum (t := t) k G : ℝ) =
      (n+2 : ℝ)*score W G - (∑ x, ∑ y, W x y)*v.val := by
    simp only [pointSum, Fintype.sum_prod_type, Int.cast_sum, Int.cast_mul, Int.cast_sub,
      Int.cast_add, Int.cast_one, Int.cast_natCast, score, Fin.sum_univ_succ (n := n+1)]
    simp [W,v, ibit, bit, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul,
      add_assoc]
    norm_num [mul_comm]
  by_contra! hf
  let B : ℝ := (∑ x, ∑ y, W x y)*v.val/(n+2)
  have hB : (n+2 : ℝ)*B = (∑ x, ∑ y, W x y)*v.val := by dsimp [B]; field_simp
  have hp i b j : score W (swTest v i b j) ≤ B := by
    have h := hf _ (countSw v i b j)
    have h' : (pointSum (t := t) k (swTest v i b j) : ℝ) ≤ 0 := by exact_mod_cast h
    rw [hid] at h'
    apply le_of_mul_le_mul_left _ (show 0 < (n+2 : ℝ) by positivity)
    linarith
  apply hk
  funext ⟨i,j⟩
  have h1 := switchOsc v i.succ hv (Fin.succ_ne_zero _) W B (hp _) j.succ 0
  have h2 := switchOsc v i.succ hv (Fin.succ_ne_zero _) W B (hp _) 0 j.succ
  simp [W,hB] at h1 h2
  exact le_antisymm h1 h2

def pay {N r s : ℕ} (t : ℕ) (T : Fin N → Fin N → Bool) (p : Slice N r × Slice N s) : ℤ :=
  N*rect T p.1 p.2 - (r*s*t : ℕ)

theorem signedPerturb {n t r s m : ℕ} (ht : 0 < t) (htN : t < n+2)
    (hr : 0 < r) (hrN : r < n+2) (hs : 0 < s) (hsN : s < n+2)
    (Q : Fin m → Fin (n+2) → Fin (n+2) → Bool) (hm : m ≤ (n+1)^2)
    (hQ : ∀ j, Reg t (Q j)) :
    ∃ w : Slice (n+2) r × Slice (n+2) s → ℤ, (∑ p, w p) = 0 ∧
      (∀ j, ∑ p, w p * pay t (Q j) p ≤ 0) ∧
      ∃ T, Reg t T ∧ 0 < ∑ p, w p * pay t T p := by
  classical
  choose u uz uh using contrastWeights hr hrN
  choose v vz vh using contrastWeights hs hsN
  let I := Fin (n+1) × Fin (n+1)
  let e (i : I) (p : Slice (n+2) r × Slice (n+2) s) := u i.1.succ p.1*v i.2.succ p.2
  have ez i : ∑ p, e i p = 0 := by simp [e, Fintype.sum_prod_type, ← Finset.mul_sum, vz]
  have er (T) (hT : Reg t T) (i : I) :
      (∑ p, e i p*rect T p.1 p.2) = (n+2 : ℤ)*((n+2 : ℤ)*ibit (T i.1.succ i.2.succ)-t) := by
    simp only [Fintype.sum_prod_type, e, rectFactor, uh, vh]
    simpa using pointContrast hT i.1.succ i.2.succ
  obtain ⟨k,hk,hsep⟩ := signedKernel (ι := I)
    (fun j i => (n+2 : ℤ)*ibit (Q j i.1.succ i.2.succ)-t) (by simpa [I,sq] using hm)
  let w p := ∑ i, k i * e i p
  have wz : ∑ p, w p = 0 := by unfold w; rw [Finset.sum_comm]; simp [← Finset.mul_sum, ez]
  have he (T) (hT : Reg t T) : (∑ p, w p*pay t T p) = (n+2 : ℤ)^2 * pointSum (t := t) k T := by
    simp only [pay, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, wz, zero_mul, sub_zero]
    simp only [mul_left_comm (w _), ← Finset.mul_sum]
    simp_rw [w, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, er T hT]
    simp only [pointSum, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc, sq, mul_assoc]
    norm_num only at *
    simp_rw [mul_left_comm (k _) (n+2 : ℤ), ← Finset.mul_sum]
    rfl
  refine ⟨w,wz,fun j => ?_,?_⟩
  · rw [he _ (hQ j)]
    apply mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) 
    simpa [pointSum, add_assoc] using hsep j
  · obtain ⟨T,hT,h⟩ := positivePoint ht htN k hk
    exact ⟨T,hT,by rw [he T hT]; exact mul_pos (by positivity) h⟩

theorem indSum {N r : ℕ} (R : Slice N r) : ∑ x, ind R x = r := by
  simp [ind, R.property]

theorem rectTranspose {N r s : ℕ} (T : Fin N → Fin N → Bool) (R : Slice N r) (S : Slice N s) :
    rect (fun y x => T x y) S R = rect T R S := by
  unfold rect; rw [Finset.sum_comm]; simp [mul_comm]

theorem blockPay {N t r s p k : ℕ} (T : Fin N → Fin N → Bool) (hT : Reg t T)
    (B : Fin p → Slice N r) (hB : ∀x,(Finset.univ.filter fun j => x ∈ (B j).val).card=k)
    (h : N*k = p*r) (S : Slice N s) : (∑ j, pay t T (B j,S)) = 0 := by
  have hc x : (∑ j, ind (B j) x) = k := by simp [ind, Finset.sum_boole, hB]
  have he : (∑ j, rect T (B j) S) = (k : ℤ)*s*t := by
    unfold rect
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (f := fun (j : Fin p) (y : Fin N) => _ * ind S y * ibit (T _ y)),
      ← Finset.sum_mul, hc]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, colBits hT, ← Finset.sum_mul, indSum]
  simp only [pay, Finset.sum_sub_distrib, ← Finset.mul_sum, he, Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ, Fintype.card_fin, Nat.cast_mul]
  have hh : (N : ℤ)*k = p*r := by exact_mod_cast h
  linear_combination s*t*hh

def freqs {ι : Type} [DecidableEq ι] {p : ℕ} (B : Fin p → ι) (z : ι) :=
  (Finset.univ.filter fun j => B j = z).card

theorem freqSum {ι : Type} [Fintype ι] [DecidableEq ι] {p : ℕ} (B : Fin p → ι) :
    ∑ z, freqs B z = p := by
  simp only [freqs, Finset.card_filter]
  rw [Finset.sum_comm]; simp

theorem freqScore {ι : Type} [Fintype ι] [DecidableEq ι] {p : ℕ} (B : Fin p → ι) (f : ι → ℤ) :
    (∑ z, (freqs B z : ℤ)*f z) = ∑ j, f (B j) := by
  simp only [freqs, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]; simp

theorem lineLoss {N t r s : ℕ} (R : Slice N r) (S : Slice N s) (T : Fin N → Fin N → Bool)
    (ht : Reg t T) :
    (mismatch (lineGraph R.val S.val) T : ℤ) =
      cellCount (lineGraph R.val S.val) + (N : ℤ)*t - 2*(r+s : ℤ)*t + 2*rect T R S := by
  have pair (x y : Fin N) : (if lineGraph R.val S.val x y ≠ T x y then (1:ℤ) else 0) =
      ibit (lineGraph R.val S.val x y) + ibit (T x y) -
      2*(ind R x*ibit (T x y) + ind S y*ibit (T x y)) + 2*(ind R x*ind S y*ibit (T x y)) := by
    by_cases hx : x ∈ R.val <;> by_cases hy : y ∈ S.val <;> cases h : T x y <;>
      norm_num [lineGraph, hx,hy,ibit,ind]
  have rows : (∑ x, ∑ y, ind R x*ibit (T x y)) = (r : ℤ)*t := by
    simp only [← Finset.mul_sum, rowBits ht, ← Finset.sum_mul, indSum]
  have cols : (∑ x, ∑ y, ind S y*ibit (T x y)) = (s : ℤ)*t := by
    rw [Finset.sum_comm]; simp only [← Finset.mul_sum, colBits ht, ← Finset.sum_mul, indSum]
  simp only [mismatch, cellCount, ← Finset.sum_boole, Fintype.sum_prod_type]
  simp only [pair, ← Finset.mul_sum (a := (2:ℤ)), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    rect, rows, cols, rowBits ht, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold ibit
  ring

theorem lossPay {N t g r s : ℕ} (hNt : N < 2*t) (hlt : t<N) (hgr : r+s=g+1)
    (R : Slice N r) (S : Slice N s) (T : Fin N → Fin N → Bool) (hT : Reg t T) :
    let A := (g+1)*N-r*s
    let V := ((N*t : ℕ) : ℝ) - ((2*t-N : ℕ):ℝ)*A/N
    (N : ℝ)*((mismatch (lineGraph R.val S.val) T : ℝ)-V) = 2*(pay t T (R,S) : ℝ) := by
  dsimp only
  have hc := lineCount R.val S.val
  rw [R.property,S.property,hgr] at hc
  have hA : (g+1)*N-r*s = cellCount (lineGraph R.val S.val) := by omega
  have he := lineLoss R S T hT
  have he' := congrArg (fun z : ℤ => (z:ℝ)) he
  push_cast at he'
  have hc' : (cellCount (lineGraph R.val S.val) : ℝ) + (r:ℝ)*s = (r+s:ℝ)*N := by
    rw [← hgr] at hc
    exact_mod_cast hc
  rw [hA]
  push_cast [pay, Nat.cast_sub hNt.le]
  field_simp [show (N : ℝ) ≠ 0 by exact_mod_cast (show N ≠ 0 by omega)]
  nlinarith [congrArg (fun z : ℝ => z*t) hc']

private lemma blockTransport {α : Type*} [Fintype α] (s t : Finset α)
    (h : s.card = t.card) : ∃ e : Equiv.Perm α, s.map e.toEmbedding = t := by
  classical
  let ep : {x // x ∈ s} ≃ {x // x ∈ t} := Finset.equivOfCardEq h
  let en : {x // x ∉ s} ≃ {x // x ∉ t} := Fintype.equivOfCardEq
    (Fintype.card_compl_eq_card_compl (fun x => x ∈ s) (fun x => x ∈ t)
      (Fintype.card_congr ep))
  let e : Equiv.Perm α := Equiv.subtypeCongr ep en
  refine ⟨e, Finset.eq_of_subset_of_card_le ?_ (by simp [h])⟩
  intro b hb
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
  change e a ∈ t
  have he : e a = (ep ⟨a, ha⟩ : α) := by
    simp [e, Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_pos ha]
  rw [he]
  exact (ep ⟨a, ha⟩).property

lemma balancedBlocks {N r : ℕ} (hr : 0 < r) (hrN : r < N) (R : Finset (Fin N))
    (hR : R.card = r) :
    let p := N / N.gcd r
    let k := r / N.gcd r
    ∃ B : Fin p → Finset (Fin N), (∀ j, (B j).card = r) ∧
      (∀ x, (Finset.univ.filter fun j => x ∈ B j).card = k) ∧ ∃ j, B j = R := by
  classical
  let d := N.gcd r
  let p := N / d
  let k := r / d
  have hpd : p * d = N := Nat.div_mul_cancel (Nat.gcd_dvd_left N r)
  have hkd : k * d = r := Nat.div_mul_cancel (Nat.gcd_dvd_right N r)
  have hd : 0 < d := Nat.gcd_pos_of_pos_left r (hr.trans hrN)
  have hkp : k < p := (Nat.mul_lt_mul_right hd).mp (by simpa only [hkd, hpd] using hrN)
  let _ : NeZero p := NeZero.of_pos (Nat.zero_lt_of_lt hkp)
  let c : Fin p := ⟨k, hkp⟩
  let u : Fin N ≃ Fin p × Fin d := (finCongr hpd.symm).trans finProdFinEquiv.symm
  let A (j : Fin p) : Finset (Fin N) := Finset.univ.filter fun x => (u x).1 - j < c
  have hA (j : Fin p) : (A j).card = r := by
    calc
      (A j).card = ((Finset.Iio c) ×ˢ (Finset.univ : Finset (Fin d))).card := by
        apply Finset.card_equiv (u.trans ((Equiv.subRight j).prodCongr (Equiv.refl (Fin d))))
        intro x
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
          Finset.mem_Iio, and_true]; rfl
      _ = r := by simpa only [Finset.card_product, Finset.card_univ, Fintype.card_fin,
        Fin.card_Iio] using hkd
  have hcount (x : Fin N) : (Finset.univ.filter fun j => x ∈ A j).card = k := by
    calc
      (Finset.univ.filter fun j => x ∈ A j).card = (Finset.Iio c).card := by
        apply Finset.card_equiv (Equiv.subLeft (u x).1)
        intro j
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio,
          Equiv.subLeft_apply]
      _ = k := Fin.card_Iio c
  obtain ⟨e, he⟩ := blockTransport (A 0) R ((hA 0).trans hR.symm)
  refine ⟨fun j => (A j).map e.toEmbedding, ?_, ?_, 0, he⟩
  · intro j
    simpa only [Finset.card_map] using hA j
  · intro x
    simpa only [Finset.mem_map_equiv] using hcount (e.symm x)

theorem padCounts {ι κ : Type} [Fintype ι] [Nonempty ι]
    (p q : ℕ) (f : κ → ι → ℤ)
    (b u v : ι → ℕ) (hb : ∀ i, 0 < b i) (hd : p ∣ ∑ i, b i)
    (hu : (∑ i, u i) = p) (hv : (∑ i, v i) = q)
    (bz : ∀ j, (∑ i, (b i : ℤ) * f j i) = 0)
    (uz : ∀ j, (∑ i, (u i : ℤ) * f j i) = 0)
    (vz : ∀ j, (∑ i, (v i : ℤ) * f j i) = 0)
    (w : ι → ℤ) (wz : (∑ i, w i) = 0) :
    ∃ a : ι → ℕ, 0 < ∑ i, a i ∧
      ((∃ h : ℕ, Nat.gcd p q = 2 ^ h) → ∃ h : ℕ, (∑ i, a i) = 2 ^ h) ∧
      ∀ j, (∑ i, (a i : ℤ) * f j i) = ∑ i, w i * f j i := by
  classical
  let K : ℕ := 1 + ∑ i, (w i).natAbs
  have hk (i : ι) : (w i).natAbs < K := by
    have hs : (w i).natAbs ≤ ∑ j, (w j).natAbs :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (w j).natAbs) (Finset.mem_univ i)
    dsimp only [K]
    omega
  have hpos (i : ι) : 0 < (K : ℤ) * b i + w i := by
    have hab : -(w i) ≤ ((w i).natAbs : ℤ) := by
      rw [Int.natCast_natAbs]
      exact neg_le_abs _
    have hbound : ((w i).natAbs : ℤ) < K := by exact_mod_cast hk i
    have hb' : (1 : ℤ) ≤ b i := by exact_mod_cast (show 1 ≤ b i from hb i)
    have hm : (K : ℤ) ≤ (K : ℤ) * b i := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hb' (Nat.cast_nonneg K : 0 ≤ (K : ℤ))
    omega
  let a₀ (i : ι) : ℕ := ((K : ℤ) * b i + w i).toNat
  have ha₀ (i : ι) : (a₀ i : ℤ) = (K : ℤ) * b i + w i :=
    Int.natCast_toNat_eq_self.mpr (hpos i).le
  let base : ℕ := ∑ i, a₀ i
  have hbase : base = K * ∑ i, b i := by
    change (∑ i, a₀ i) = _
    apply Nat.cast_injective (R := ℤ)
    simp only [Nat.cast_sum, Nat.cast_mul, ha₀, Finset.sum_add_distrib, ← Finset.mul_sum, wz, add_zero]
  have hbp : 0 < base := by
    let i : ι := Classical.choice inferInstance
    have hs : b i ≤ ∑ j, b j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (b j)) (Finset.mem_univ i)
    rw [hbase]
    exact Nat.mul_pos (by dsimp only [K]; omega) (lt_of_lt_of_le (hb i) hs)
  have hdBase : p.gcd q ∣ base := by
    rw [hbase]
    exact (Nat.gcd_dvd_left p q).trans (hd.mul_left K)
  have hz₀ (j : κ) : (∑ i, (a₀ i : ℤ) * f j i) = ∑ i, w i * f j i := by
    simp only [ha₀, add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum, bz,
      mul_zero, zero_add]
  by_cases H : ∃ h : ℕ, p.gcd q = 2 ^ h
  · obtain ⟨h, hh⟩ := H
    let t := h + base + p * q + 1
    let target : ℕ := 2 ^ t
    have hroom : base + p * q ≤ target := by
      have hpow : t < 2 ^ t := Nat.lt_pow_self (by decide : 1 < 2)
      exact le_trans (show base + p * q ≤ t by dsimp only [t]; omega) hpow.le
    have htarget : p.gcd q ∣ target := by
      rw [hh]
      exact pow_dvd_pow 2 (show h ≤ t by dsimp only [t]; omega)
    have hpred : p.pred * q.pred ≤ p * q := Nat.mul_le_mul (Nat.pred_le _) (Nat.pred_le _)
    obtain ⟨m, n, hmn⟩ := Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le p q (target - base)
      (Nat.dvd_sub htarget hdBase) (by omega)
    let a (i : ι) := a₀ i + m * u i + n * v i
    have htotal : (∑ i, a i) = target := by
      simp only [a, Finset.sum_add_distrib, ← Finset.mul_sum, hu, hv]
      change base + m * p + n * q = target
      omega
    refine ⟨a, ?_, fun _ => ⟨t, htotal⟩, ?_⟩
    · rw [htotal]
      exact pow_pos (by decide : 0 < 2) _
    · intro j
      simp only [a, Nat.cast_add, Nat.cast_mul, add_mul, mul_assoc, Finset.sum_add_distrib,
        ← Finset.mul_sum, hz₀, uz, vz, mul_zero, add_zero]
  · exact ⟨a₀, hbp, fun h => (H h).elim, hz₀⟩

theorem listOfCounts {ι : Type} [Fintype ι] (a : ι → ℕ) :
    ∃ L : Fin (∑ i, a i) → ι,
      ∀ f : ι → ℝ, (∑ i, f (L i)) = ∑ i, (a i : ℝ) * f i := by
  classical
  let e : (Σ i, Fin (a i)) ≃ Fin (∑ i, a i) := Fintype.equivFinOfCardEq (by simp)
  refine ⟨fun i => (e.symm i).1, ?_⟩
  intro f
  calc
    _ = ∑ x : (Σ i, Fin (a i)), f x.1 := e.symm.sum_comp (fun x => f x.1)
    _ = _ := by simp [Fintype.sum_sigma, nsmul_eq_mul]

theorem rowNeutral {N t r s : ℕ} (hr : 0<r) (hrN : r<N) (z : Slice N r × Slice N s) :
    ∃ b : Slice N r × Slice N s → ℕ, 0 < b z ∧ (∑ i, b i) = N/N.gcd r ∧
      ∀ T, Reg t T → (∑ i, (b i : ℤ)*pay t T i) = 0 := by
  classical
  obtain ⟨B,hc,hb,j,hj⟩ := balancedBlocks hr hrN z.1.val z.1.property
  let B' i : Slice N r := ⟨B i,hc i⟩
  let L i := (B' i,z.2)
  have hL : L j = z := Prod.ext (Subtype.ext hj) rfl
  refine ⟨freqs L, Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hL⟩⟩,
    freqSum L,fun T ht => ?_⟩
  rw [freqScore]
  apply blockPay T ht B' hb _ z.2
  have h₁ := Nat.div_mul_cancel (Nat.gcd_dvd_left N r)
  have h₂ := Nat.div_mul_cancel (Nat.gcd_dvd_right N r)
  calc N * (r / N.gcd r) = (N/N.gcd r*(N.gcd r))*(r/N.gcd r) := by rw [h₁]
       _ = N/N.gcd r*((r/N.gcd r)*(N.gcd r)) := by ring
       _ = _ := by rw [h₂]

theorem colNeutral {N t r s : ℕ} (hs : 0<s) (hsN : s<N) (z : Slice N r × Slice N s) :
    ∃ b : Slice N r × Slice N s → ℕ, (∑ i, b i) = N/N.gcd s ∧
      ∀ T, Reg t T → (∑ i, (b i : ℤ)*pay t T i) = 0 := by
  obtain ⟨v,_,hv,he⟩ := rowNeutral (t := t) hs hsN z.swap
  refine ⟨fun p => v p.swap, (Equiv.prodComm _ _).sum_comp v |>.trans hv, fun T ht => ?_⟩
  have h := he (fun y x => T x y) ⟨ht.2,ht.1⟩
  have hh := (Equiv.prodComm (Slice N r) (Slice N s)).sum_comp (fun p => (v p : ℤ)*pay t (fun y x => T x y) p)
  simpa only [Equiv.prodComm_apply, pay, Prod.fst_swap, Prod.snd_swap, rectTranspose, Nat.mul_comm s r] using hh.trans h

theorem rectLower {N t r s m : ℕ} (ht : 0<t) (htN : t<N) (hr : 0<r) (hrN : r<N)
    (hs : 0<s) (hsN : s<N) (Q : Fin m → Fin N → Fin N → Bool) (hm : m ≤ (N-1)^2) (hQ : ∀j, Reg t (Q j)) :
    ∃ (M : ℕ) (L : Fin M → Slice N r × Slice N s), 0 < M ∧
      ((∃ u : ℕ, (N/N.gcd r).gcd (N/N.gcd s) = 2^u) → ∃ u : ℕ, M=2^u) ∧
      (∀ j, ∑ i, (pay t (Q j) (L i) : ℝ) ≤ 0) ∧
      ∃ T, Reg t T ∧ 0 < ∑ i, (pay t T (L i) : ℝ) := by
  classical
  obtain ⟨w,hw,hsep,T,hT,hpos⟩ : ∃ w : Slice N r × Slice N s → ℤ, (∑p,w p)=0 ∧
      (∀j, ∑p,w p*pay t (Q j) p ≤ 0) ∧ ∃T,Reg t T ∧ 0 < ∑p,w p*pay t T p := by
    obtain ⟨n,rfl⟩ : ∃ n, N=n+2 := ⟨N-2,by omega⟩
    exact signedPerturb ht htN hr hrN hs hsN Q (by simpa using hm) hQ
  let I := Slice N r × Slice N s
  let _ : Nonempty I := ⟨Classical.choice (sliceExists hrN.le), Classical.choice (sliceExists hsN.le)⟩
  let z : I := Classical.choice inferInstance
  choose U Upos Ulen Uzero using rowNeutral (t := t) (s := s) hr hrN
  obtain ⟨v,vlen,vzero⟩ := colNeutral (t := t) hs hsN z
  let b (i : I) := ∑ j, U j i
  have bpos i : 0 < b i := (Upos i).trans_le (Finset.single_le_sum (fun j _ => Nat.zero_le (U j i)) (Finset.mem_univ i))
  have bd : N/N.gcd r ∣ ∑ i, b i := by
    unfold b; rw [Finset.sum_comm]; apply Finset.dvd_sum
    intro i _; exact (Ulen i).symm ▸ dvd_refl _
  let f (T : {T : Fin N → Fin N → Bool // Reg t T}) (i : I) := pay t T.val i
  have bz T : (∑i,(b i : ℤ)*f T i)=0 := by
    simp only [b, Nat.cast_sum, Finset.sum_mul]; rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun i _ => Uzero i T.val T.property
  obtain ⟨a,apos,adyad,ae⟩ := padCounts (N/N.gcd r) (N/N.gcd s) f b (U z) v bpos bd (Ulen z) vlen bz
    (fun T => Uzero z T.val T.property) (fun T => vzero T.val T.property) w hw
  obtain ⟨L,hL⟩ := listOfCounts a
  have eqP (G) (hG : Reg t G) : (∑i,(pay t G (L i) : ℝ)) = ((∑p,w p*pay t G p : ℤ) : ℝ) := by
    rw [hL (fun p => (pay t G p : ℝ))]
    have h := ae ⟨G,hG⟩
    dsimp only [f] at h
    push_cast; exact_mod_cast h
  refine ⟨_,L,apos,adyad,fun j => ?_,T,hT,?_⟩
  · rw [eqP _ (hQ j)]; exact_mod_cast hsep j
  · rw [eqP _ hT]; exact_mod_cast hpos

def fitsC (N g A : ℕ) (C : Circuit) := ReadsBack (N+N) C ∧ C.output < N+N+C.size ∧
  (∀ gate ∈ C.gates, ok gate) ∧ C.size ≤ g ∧ cellCount (table (N := N) C) ≤ A

theorem lowerResult {N t g r s m : ℕ} (hNt : N < 2*t) (ht : t<N) (hr : 0<r)
    (hrs : r ≤ s) (hgr : r+s=g+1) (hprod : r*s<N) (Q : Fin m → Fin N → Fin N → Bool)
    (hm : m≤(N-1)^2) (hQ : ∀j,Reg t (Q j)) :
    let A := (g+1)*N-r*s
    let V := ((N*t : ℕ) : ℝ) - ((2*t-N : ℕ):ℝ)*A/N
    ∃ (M : ℕ) (D : Fin M → Circuit), 0<M ∧
      ((∃ u : ℕ, (N/N.gcd r).gcd (N/N.gcd s)=2^u) → ∃u : ℕ, M=2^u) ∧
      (∀ i, fitsC N g A (D i) ∧ cellCount (table (N := N) (D i)) = A ∧ ∀ gate ∈ (D i).gates, gate.op = .or) ∧
      (∀ j, (∑ i, (mismatch (table (D i)) (Q j) : ℝ)) ≤ (M : ℝ)*V) ∧
      ∃ T : Fin N → Fin N → Bool, Reg t T ∧ (M : ℝ)*V < ∑ i, (mismatch (table (D i)) T : ℝ) := by
  classical
  dsimp only
  let A := (g+1)*N-r*s
  let V := ((N*t : ℕ) : ℝ) - ((2*t-N : ℕ):ℝ)*A/N
  have hs : s<N := (Nat.le_mul_of_pos_left s hr).trans_lt hprod
  obtain ⟨M,L,hM,hdy,hsep,T,hT,hpos⟩ := rectLower (by omega) ht hr (hrs.trans_lt hs) (hr.trans_le hrs) hs Q hm hQ
  have hp i : 0 < (L i).1.val.card + (L i).2.val.card := by rw [(L i).1.property,(L i).2.property]; omega
  choose D back out gates size tab using fun i => realizeLines _ _ (hp i)
  have ha i : cellCount (table (N := N) (D i)) = A := by
    rw [tab]; have h := lineCount (L i).1.val (L i).2.val
    rw [(L i).1.property, (L i).2.property,hgr] at h; dsimp [A]; omega
  have he (G) (hG : Reg t G) : (N : ℝ)*((∑ i, (mismatch (table (D i)) G : ℝ))-M*V) =
      2*∑ i, (pay t G (L i) : ℝ) := by
    have H := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => lossPay hNt ht hgr (L i).1 (L i).2 G hG)
    simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at H
    simpa only [tab,V,A,mul_sub] using H
  refine ⟨M,D,hM,hdy,fun i => ?_,fun j => ?_,T,hT,?_⟩
  · have sz := size i; rw [(L i).1.property,(L i).2.property,hgr] at sz
    exact ⟨⟨back i,out i, fun a ha => ⟨(gates i a ha).2.le, Or.inl (gates i a ha).1⟩, by omega, (ha i).le⟩,
      ha i,fun a ha => (gates i a ha).1⟩
  · have h := he _ (hQ j); have hh := hsep j
    change _ ≤ (M : ℝ)*V
    exact sub_nonpos.mp (nonpos_of_mul_nonpos_right (by linarith : (N : ℝ)*_ ≤ 0) (by exact_mod_cast (show 0<N by omega)))
  · have h := he _ hT
    change (M : ℝ)*V < _
    exact sub_pos.mp (pos_of_mul_pos_right (by linarith : (0 : ℝ)<(N : ℝ)*_) (Nat.cast_nonneg _))

end PEqualNP.Outside.L_meta_33671

theorem PEqualNP.Outside.L_meta_33671 : ∀ N t : ℕ, N < 2*t → t < N →
  let X := Fin N
  let L := 2*N*(N-1)
  let graph := X → X → Bool
  let reg := fun (T : graph) =>
    (∀ x, (Finset.univ.filter (fun y => T x y)).card = t) ∧
    (∀ y, (Finset.univ.filter (fun x => T x y)).card = t)
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let tab := fun (C : Circ) (x y : X) => C.eval (PEqualNP.Represents.oneEach x y)
  let area := fun (C : Circ) => ((Finset.univ : Finset (X × X)).filter (fun z => tab C z.1 z.2)).card
  let loss := fun (C : Circ) (T : graph) => ((Finset.univ : Finset (X × X)).filter
    (fun z => tab C z.1 z.2 ≠ T z.1 z.2)).card
  ∃ test : Fin L → graph, (∀ i, reg (test i)) ∧
    ∀ (g r s : ℕ), 0 < r → r ≤ s → r+s = g+1 → r*s < N → 2*g+1 < N →
      let A := (g+1)*N-r*s
      let a := 2*t-N
      let V := ((N*t : ℕ) : ℝ) - (a : ℝ)*(A : ℝ)/(N : ℝ)
      let fits := fun (C : Circ) =>
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C ∧ C.output < N+N+C.size ∧
        (∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
          (gate.op = .or ∨ gate.op = .and ∨ (gate.op = .not ∧ gate.inputs.length = 1))) ∧
        C.size ≤ g ∧ area C ≤ A
      let lines := fun (C : Circ) => ∃ R S : Finset X, R.card+S.card = g+1 ∧
        ∀ x y, tab C x y = decide (x ∈ R ∨ y ∈ S)
      let c := Nat.gcd (N / Nat.gcd N r) (N / Nat.gcd N s)
      (∀ (M : ℕ) (D : Fin M → Circ) (w : Fin M → ℝ) (h : ℝ),
        (∀ i, fits (D i) ∧ 0 ≤ w i) → (∑ i, w i) = 1 → 0 ≤ h →
        let err := fun T => ∑ i, w i*(loss (D i) T : ℝ)
        (∀ j, err (test j) ≤ V+h) →
          (∀ T, reg T → err T ≤ V+(((N-1)*t*(N-t) : ℕ) : ℝ)*h) ∧
          (a : ℝ)*((N-r*s : ℕ) : ℝ)*
            (∑ i, @ite ℝ (lines (D i)) (Classical.propDecidable _) 0 (w i)) ≤ (N : ℝ)*h) ∧
      ∀ (m : ℕ) (Q : Fin m → graph), m ≤ (N-1)^2 → (∀ j, reg (Q j)) →
        ∃ (M : ℕ) (D : Fin M → Circ), 0 < M ∧
          ((∃ u : ℕ, c = 2^u) → ∃ u : ℕ, M = 2^u) ∧
          (∀ i, fits (D i) ∧ area (D i) = A ∧ ∀ gate ∈ (D i).gates, gate.op = .or) ∧
          (∀ j, (∑ i, (loss (D i) (Q j) : ℝ)) ≤ (M : ℝ)*V) ∧
          ∃ T, reg T ∧ (M : ℝ)*V < ∑ i, (loss (D i) T : ℝ) := by
  classical
  intro N t hNt ht
  dsimp only
  obtain ⟨test,hrTest,hcert⟩ := PEqualNP.Outside.L_meta_33671.lossCertificate N t hNt ht
  refine ⟨test,hrTest,?_⟩
  intro g r s hr hrs hgr hp hN
  constructor
  · intro M D w h hD hw _ hpass
    obtain ⟨hAll,hArea⟩ := hcert ((g+1)*N-r*s) M (fun i => PEqualNP.Outside.L_meta_33671.table (D i)) w h
      (fun i => ⟨(hD i).1.2.2.2.2, (hD i).2⟩) hw hpass
    refine ⟨hAll,?_⟩
    have gap := PEqualNP.Outside.L_meta_33671.massGap hr hrs hp hN D w hw (fun i =>
      ⟨(hD i).1.2.2.1, (hD i).1.2.2.2.1, (hD i).1.2.2.2.2, (hD i).2⟩)
    rw [mul_assoc]
    exact (mul_le_mul_of_nonneg_left gap (Nat.cast_nonneg (2*t-N))).trans hArea
  · intro m Q hm hQ
    exact PEqualNP.Outside.L_meta_33671.lowerResult hNt ht hr hrs hgr hp Q hm hQ
