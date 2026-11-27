import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25888_aux

def q (M0 M1 M2 : ZMod 2) : ZMod 2 := M0 + (1 + M1) * M2

theorem q_deriv : ∀ X0 X1 X2 Y0 Y1 Y2 Z0 Z1 Z2 A0 A1 A2 : ZMod 2,
    q (X0+Y0+Z0+A0) (X1+Y1+Z1+A1) (X2+Y2+Z2+A2) - q (X0+Y0+Z0) (X1+Y1+Z1) (X2+Y2+Z2) =
      (q (X0+A0) (X1+A1) (X2+A2) - q X0 X1 X2) + (q (Y0+A0) (Y1+A1) (Y2+A2) - q Y0 Y1 Y2) +
      (q (Z0+A0) (Z1+A1) (Z2+A2) - q Z0 Z1 Z2) := by
  unfold q; decide

abbrev W (k : ℕ) := Fin k → ZMod 2

def ix (k : ℕ) (hk : 0 < k) (t : ℕ) : Fin k := ⟨t % k, Nat.mod_lt _ hk⟩

def rot (k : ℕ) (hk : 0 < k) (amount : ℕ) (x : W k) : W k := fun j => x (ix k hk (j.val + k - amount % k))

def mm (k : ℕ) (hk : 0 < k) (gap : ℕ) (x : W k) (j : Fin k) : ZMod 2 :=
  x j + x (ix k hk (j.val + gap)) + x (ix k hk (j.val + k - gap % k))

def layer (k : ℕ) (hk : 0 < k) (gap : ℕ) (x : W k) : W k :=
  fun j => mm k hk gap x j + (1 + mm k hk gap x (ix k hk (j.val + 1))) * mm k hk gap x (ix k hk (j.val + 2))

theorem mm_add (k : ℕ) (hk : 0 < k) (gap : ℕ) (x y : W k) (j : Fin k) :
    mm k hk gap (x + y) j = mm k hk gap x j + mm k hk gap y j := by
  simp only [mm, Pi.add_apply]; ring

theorem layer_deriv (k : ℕ) (hk : 0 < k) (gap : ℕ) (a x y z : W k) :
    layer k hk gap (x + y + z + a) - layer k hk gap (x + y + z) =
      (layer k hk gap (x + a) - layer k hk gap x) + (layer k hk gap (y + a) - layer k hk gap y) +
      (layer k hk gap (z + a) - layer k hk gap z) := by
  funext j
  simp only [layer, Pi.add_apply, Pi.sub_apply, mm_add]
  exact q_deriv _ _ _ _ _ _ _ _ _ _ _ _

theorem two_eq_zero (k : ℕ) (x : W k) : x + x = 0 := by
  funext j; show x j + x j = 0; exact CharTwo.add_self_eq_zero (x j)

theorem rot_add (k : ℕ) (hk : 0 < k) (a : ℕ) (x y : W k) : rot k hk a (x + y) = rot k hk a x + rot k hk a y := by
  funext j; rfl

def stateF (k : ℕ) (hk : 0 < k) (r gap initial : ℕ) (inject : ℕ → ℕ) (data : W k × (Fin r → W k)) (key : W k)
    (time : Fin (r + 1)) : W k :=
  ((List.finRange r).take time.val).foldl
    (fun v tick => layer k hk gap v + rot k hk (inject tick.val) key + data.2 tick) (rot k hk initial key + data.1)

theorem stateF_zero (k : ℕ) (hk : 0 < k) (r gap initial : ℕ) (inject : ℕ → ℕ) (data : W k × (Fin r → W k))
    (key : W k) : stateF k hk r gap initial inject data key 0 = rot k hk initial key + data.1 := by
  simp [stateF]

theorem stateF_succ (k : ℕ) (hk : 0 < k) (r gap initial : ℕ) (inject : ℕ → ℕ) (data : W k × (Fin r → W k))
    (key : W k) (t : Fin r) : stateF k hk r gap initial inject data key t.succ =
      layer k hk gap (stateF k hk r gap initial inject data key t.castSucc) + rot k hk (inject t.val) key + data.2 t := by
  unfold stateF
  simp only [Fin.val_succ, Fin.coe_castSucc]
  rw [List.take_succ, List.foldl_append]
  have : (List.finRange r)[t.val]? = some t := by simp
  rw [this]; simp

def Sol (k : ℕ) (hk : 0 < k) (r s gap : ℕ) (inject : ℕ → ℕ) (delta : Fin s → W k) (path : Fin (r + 1) → Fin s → W k)
    (t : Fin r) (p : Fin s) (v : W k) : Prop :=
  layer k hk gap (v + path t.castSucc p) - layer k hk gap v + rot k hk (inject t.val) (delta p) = path t.succ p

instance (k : ℕ) (hk : 0 < k) (r s gap : ℕ) (inject : ℕ → ℕ) (delta : Fin s → W k) (path : Fin (r + 1) → Fin s → W k)
    (t : Fin r) (p : Fin s) : DecidablePred (Sol k hk r s gap inject delta path t p) := by
  intro v; unfold Sol; infer_instance

def okF (k : ℕ) (hk : 0 < k) (r s gap initial : ℕ) (inject : ℕ → ℕ) (delta : Fin s → W k)
    (path : Fin (r + 1) → Fin s → W k) (raw : W k) (data : W k × (Fin r → W k)) (h : Fin (r + 1))
    (keep : Finset (Fin s)) : Prop :=
  ∀ t : Fin (r + 1), t ≤ h → ∀ p ∈ keep,
    stateF k hk r gap initial inject data (raw + delta p) t - stateF k hk r gap initial inject data raw t = path t p

theorem diff_succ (k : ℕ) (hk : 0 < k) (r gap initial : ℕ) (inject : ℕ → ℕ) (data : W k × (Fin r → W k))
    (raw d : W k) (t : Fin r) :
    stateF k hk r gap initial inject data (raw + d) t.succ - stateF k hk r gap initial inject data raw t.succ =
      layer k hk gap (stateF k hk r gap initial inject data raw t.castSucc +
        (stateF k hk r gap initial inject data (raw + d) t.castSucc - stateF k hk r gap initial inject data raw t.castSucc)) -
      layer k hk gap (stateF k hk r gap initial inject data raw t.castSucc) + rot k hk (inject t.val) d := by
  rw [stateF_succ, stateF_succ, rot_add, add_sub_cancel]
  abel

theorem ok_iff (k : ℕ) (hk : 0 < k) (r s gap initial : ℕ) (inject : ℕ → ℕ) (delta : Fin s → W k)
    (path : Fin (r + 1) → Fin s → W k) (raw : W k) (data : W k × (Fin r → W k)) (h : Fin (r + 1))
    (K : Finset (Fin s)) :
    okF k hk r s gap initial inject delta path raw data h K ↔
      ∀ p ∈ K, rot k hk initial (delta p) = path 0 p ∧
        ∀ t : Fin r, t.castSucc < h → Sol k hk r s gap inject delta path t p
          (stateF k hk r gap initial inject data raw t.castSucc) := by
  have d0 : ∀ p, stateF k hk r gap initial inject data (raw + delta p) 0 - stateF k hk r gap initial inject data raw 0 =
      rot k hk initial (delta p) := by
    intro p; rw [stateF_zero, stateF_zero, rot_add]; abel
  constructor
  · intro hok p hp
    refine ⟨by rw [← d0 p]; exact hok 0 (Fin.zero_le _) p hp, fun t ht => ?_⟩
    have h1 := hok t.castSucc (le_of_lt ht) p hp
    have h2 := hok t.succ (Fin.castSucc_lt_iff_succ_le.1 ht) p hp
    unfold Sol
    rw [diff_succ, h1] at h2
    exact h2
  · intro hK t ht p hp
    obtain ⟨hinit, hloc⟩ := hK p hp
    induction t using Fin.induction with
    | zero => rw [d0 p]; exact hinit
    | succ i ih =>
      have hi : i.castSucc < h := Fin.castSucc_lt_iff_succ_le.2 ht
      rw [diff_succ, ih (le_of_lt hi)]
      exact hloc i hi

def AffC {k : ℕ} (A : Finset (W k)) : Prop := ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z ∈ A

theorem sol_affc (k : ℕ) (hk : 0 < k) (r s gap : ℕ) (inject : ℕ → ℕ) (delta : Fin s → W k)
    (path : Fin (r + 1) → Fin s → W k) (t : Fin r) (p : Fin s) :
    AffC ((Finset.univ : Finset (W k)).filter (Sol k hk r s gap inject delta path t p)) := by
  intro x hx y hy z hz
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sol] at hx hy hz ⊢
  set c := rot k hk (inject t.val) (delta p)
  set T := path t.succ p
  have hx' : layer k hk gap (x + path t.castSucc p) - layer k hk gap x = T + c := by
    rw [← hx]; rw [add_assoc, two_eq_zero, add_zero]
  have hy' : layer k hk gap (y + path t.castSucc p) - layer k hk gap y = T + c := by
    rw [← hy]; rw [add_assoc, two_eq_zero, add_zero]
  have hz' : layer k hk gap (z + path t.castSucc p) - layer k hk gap z = T + c := by
    rw [← hz]; rw [add_assoc, two_eq_zero, add_zero]
  have hd2 := layer_deriv k hk gap (path t.castSucc p) x y z
  rw [hx', hy', hz'] at hd2
  rw [hd2]
  have : T + c + (T + c) = 0 := two_eq_zero k _
  rw [this, zero_add, add_assoc, two_eq_zero, add_zero]

theorem halve {k : ℕ} {A A' : Finset (W k)} (hA : AffC A) (hA' : AffC A') (hsub : A' ⊆ A) (hne : A' ≠ A)
    (hn : A'.Nonempty) : 2 * A'.card ≤ A.card := by
  obtain ⟨a, ha⟩ := hn
  obtain ⟨b, hbA, hbA'⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.2 ⟨hsub, hne⟩)
  have hmap : A'.image (fun x => x + a + b) ⊆ A \ A' := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hw
    rw [Finset.mem_sdiff]
    refine ⟨hA x (hsub hx) a (hsub ha) b hbA, fun h => hbA' ?_⟩
    have := hA' _ h x hx a ha
    have e : x + a + b + x + a = b := by
      calc x + a + b + x + a = b + (x + x) + (a + a) := by abel
        _ = b := by rw [two_eq_zero, two_eq_zero, add_zero, add_zero]
    rwa [e] at this
  have hinj : Function.Injective (fun x : W k => x + a + b) := by
    intro x y h; simpa using h
  have := Finset.card_le_card hmap
  rw [Finset.card_image_of_injective _ hinj, Finset.card_sdiff_of_subset hsub] at this
  have := Finset.card_le_card hsub
  omega

def Inter {k : ℕ} {ι : Type} (Sl : ι → W k → Prop) [∀ i, DecidablePred (Sl i)] (B : Finset ι) : Finset (W k) :=
  (Finset.univ : Finset (W k)).filter (fun v => ∀ i ∈ B, Sl i v)

theorem inter_affc {k : ℕ} {ι : Type} (Sl : ι → W k → Prop) [∀ i, DecidablePred (Sl i)]
    (hS : ∀ i, AffC ((Finset.univ : Finset (W k)).filter (Sl i))) (B : Finset ι) : AffC (Inter Sl B) := by
  intro x hx y hy z hz
  simp only [Inter, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy hz ⊢
  intro i hi
  have := hS i x (by simp [hx i hi]) y (by simp [hy i hi]) z (by simp [hz i hi])
  simpa using this

theorem card_univ_W (k : ℕ) : (Finset.univ : Finset (W k)).card = 2 ^ k := by
  simp [Finset.card_univ, ZMod.card]

theorem greedy {k : ℕ} {ι : Type} [DecidableEq ι] (Sl : ι → W k → Prop) [∀ i, DecidablePred (Sl i)]
    (hS : ∀ i, AffC ((Finset.univ : Finset (W k)).filter (Sl i))) (P : Finset ι) :
    ∃ B ⊆ P, Inter Sl B = Inter Sl P ∧ 2 ^ B.card * (Inter Sl P).card ≤ 2 ^ k ∧ B.card ≤ k + 1 := by
  induction P using Finset.induction_on with
  | empty => exact ⟨∅, subset_rfl, rfl, by simp [Inter, card_univ_W], by simp⟩
  | insert p P hp ih =>
    obtain ⟨B, hBP, hBeq, hcard, hk1⟩ := ih
    have hins : Inter Sl (insert p P) = Inter Sl P ∩ (Finset.univ : Finset (W k)).filter (Sl p) := by
      ext v; simp only [Inter, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        forall_eq_or_imp]; tauto
    by_cases hsame : Inter Sl P ∩ (Finset.univ : Finset (W k)).filter (Sl p) = Inter Sl P
    · refine ⟨B, hBP.trans (Finset.subset_insert _ _), by rw [hBeq, hins, hsame], ?_, hk1⟩
      rw [hins, hsame]; exact hcard
    · have hpB : p ∉ B := fun h => hp (hBP h)
      have hBins : Inter Sl (insert p B) = Inter Sl B ∩ (Finset.univ : Finset (W k)).filter (Sl p) := by
        ext v; simp only [Inter, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          forall_eq_or_imp]; tauto
      refine ⟨insert p B, Finset.insert_subset_insert p hBP, by rw [hBins, hins, hBeq], ?_, ?_⟩ <;>
        rw [Finset.card_insert_of_notMem hpB]
      · rw [hins, pow_succ]
        by_cases hn : (Inter Sl P ∩ (Finset.univ : Finset (W k)).filter (Sl p)).Nonempty
        · have h2 := halve (inter_affc Sl hS P) (by rw [← hins]; exact inter_affc Sl hS _)
            Finset.inter_subset_left hsame hn
          calc 2 ^ B.card * 2 * (Inter Sl P ∩ _).card = 2 ^ B.card * (2 * (Inter Sl P ∩ _).card) := by ring
            _ ≤ 2 ^ B.card * (Inter Sl P).card := Nat.mul_le_mul_left _ h2
            _ ≤ 2 ^ k := hcard
        · rw [Finset.not_nonempty_iff_eq_empty.1 hn]; simp
      · have hSne : (Inter Sl P).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]; intro h0; apply hsame; rw [h0]; simp
        have h1 : 1 ≤ (Inter Sl P).card := Finset.card_pos.2 hSne
        have : 2 ^ B.card ≤ 2 ^ k := le_trans (by nlinarith [Nat.one_le_two_pow (n := B.card)]) hcard
        have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 this
        omega

theorem rot_zero (k : ℕ) (hk : 0 < k) (a : ℕ) : rot k hk a 0 = 0 := by funext j; rfl

theorem main (k r s : ℕ) (hk : 0 < k) (gap initial : ℕ) (inject : ℕ → ℕ) (delta : Fin s → W k)
    (path : Fin (r + 1) → Fin s → W k) :
    let ok := okF k hk r s gap initial inject delta path
    let localSet := fun t : Fin r => (Finset.univ : Finset (W k)).filter (fun v => ∀ p : Fin s,
        layer k hk gap (v + path t.castSucc p) - layer k hk gap v + rot k hk (inject t.val) (delta p) = path t.succ p)
    let feasible := ∃ data : W k × (Fin r → W k), ok 0 data (Fin.last r) Finset.univ
    (feasible → ∃ keep : Fin (r + 1) → Finset (Fin s), keep 0 = ∅ ∧
      (∀ t : Fin r, keep t.castSucc ⊆ keep t.succ ∧
        (keep t.succ \ keep t.castSucc).card ≤ k - Nat.log2 (localSet t).card) ∧
      (∀ (raw : W k) (data : W k × (Fin r → W k)) (h : Fin (r + 1)),
        (ok raw data h (keep h) ↔ ok raw data h Finset.univ))) ∧
    (¬feasible → ∃ small : Finset (Fin s), small.card ≤ k + 1 ∧
      ∀ (raw : W k) (data : W k × (Fin r → W k)), ¬ok raw data (Fin.last r) small) := by
  intro ok localSet feasible
  have hloc : ∀ t, localSet t = Inter (Sol k hk r s gap inject delta path t) Finset.univ := by
    intro t; ext v; simp [localSet, Inter, Sol]
  have G : ∀ t : Fin r, ∃ B ⊆ (Finset.univ : Finset (Fin s)),
      Inter (Sol k hk r s gap inject delta path t) B = Inter (Sol k hk r s gap inject delta path t) Finset.univ ∧
      2 ^ B.card * (Inter (Sol k hk r s gap inject delta path t) Finset.univ).card ≤ 2 ^ k ∧ B.card ≤ k + 1 :=
    fun t => greedy _ (sol_affc k hk r s gap inject delta path t) _
  choose B _ hBeq hBcard hBk using G
  have memB : ∀ (t : Fin r) (v : W k), v ∈ Inter (Sol k hk r s gap inject delta path t) (B t) → v ∈ localSet t := by
    intro t v hv; rw [hBeq t, ← hloc t] at hv; exact hv
  constructor
  · rintro ⟨data0, hfeas⟩
    rw [show ok = okF k hk r s gap initial inject delta path from rfl, ok_iff] at hfeas
    have hinit : ∀ p, rot k hk initial (delta p) = path 0 p := fun p => (hfeas p (Finset.mem_univ p)).1
    have hne : ∀ t : Fin r, (localSet t).Nonempty := by
      intro t
      refine ⟨stateF k hk r gap initial inject data0 0 t.castSucc, ?_⟩
      simp only [localSet, Finset.mem_filter, Finset.mem_univ, true_and]
      intro p; exact (hfeas p (Finset.mem_univ p)).2 t (Fin.castSucc_lt_last t)
    refine ⟨fun h => ((Finset.univ : Finset (Fin r)).filter (fun t => t.castSucc < h)).biUnion B, ?_, ?_, ?_⟩
    · ext x; simp [Fin.not_lt_zero]
    · intro t
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        obtain ⟨t', ht', hx'⟩ := hx
        exact ⟨t', lt_trans ht' Fin.castSucc_lt_succ, hx'⟩
      · have hsub : (((Finset.univ : Finset (Fin r)).filter (fun t' => t'.castSucc < t.succ)).biUnion B \
            ((Finset.univ : Finset (Fin r)).filter (fun t' => t'.castSucc < t.castSucc)).biUnion B) ⊆ B t := by
          intro x hx
          simp only [Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hx
          obtain ⟨⟨t', ht', hx'⟩, hnot⟩ := hx
          by_cases htt : t' = t
          · rw [← htt]; exact hx'
          · exfalso; apply hnot
            refine ⟨t', ?_, hx'⟩
            rw [Fin.castSucc_lt_castSucc_iff]
            rw [Fin.castSucc_lt_succ_iff] at ht'
            exact lt_of_le_of_ne ht' htt
        refine (Finset.card_le_card hsub).trans ?_
        have hc := hBcard t
        rw [← hloc t] at hc
        have hpos : (localSet t).card ≠ 0 := Finset.card_ne_zero.2 (hne t)
        have hl := Nat.log2_self_le hpos
        have : 2 ^ ((B t).card + Nat.log2 (localSet t).card) ≤ 2 ^ k := by
          rw [pow_add]; exact le_trans (Nat.mul_le_mul_left _ hl) hc
        have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 this
        omega
    · intro raw data h
      rw [show ok = okF k hk r s gap initial inject delta path from rfl, ok_iff, ok_iff]
      constructor
      · intro hK p _
        refine ⟨hinit p, fun t ht => ?_⟩
        have hv : stateF k hk r gap initial inject data raw t.castSucc ∈
            Inter (Sol k hk r s gap inject delta path t) (B t) := by
          simp only [Inter, Finset.mem_filter, Finset.mem_univ, true_and]
          intro q hq
          have hmem : q ∈ ((Finset.univ : Finset (Fin r)).filter (fun t' => t'.castSucc < h)).biUnion B := by
            simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨t, ht, hq⟩
          exact (hK q hmem).2 t ht
        have := memB t _ hv
        simp only [localSet, Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact this p
      · intro hU p _; exact hU p (Finset.mem_univ p)
  · intro hnf
    by_cases hi : ∃ p, rot k hk initial (delta p) ≠ path 0 p
    · obtain ⟨p, hp⟩ := hi
      refine ⟨{p}, by simp, fun raw data hok => ?_⟩
      rw [show ok = okF k hk r s gap initial inject delta path from rfl, ok_iff] at hok
      exact hp (hok p (Finset.mem_singleton_self p)).1
    · push_neg at hi
      have hempty : ∃ t : Fin r, localSet t = ∅ := by
        by_contra hc
        push_neg at hc
        apply hnf
        have hn : ∀ t : Fin r, (localSet t).Nonempty := hc
        choose u hu using hn
        let U : Fin (r + 1) → W k := fun i => if h : i.val < r then u ⟨i.val, h⟩ else 0
        let data : W k × (Fin r → W k) := (U 0, fun t => U t.succ - layer k hk gap (U t.castSucc))
        have hst : ∀ i : Fin (r + 1), stateF k hk r gap initial inject data 0 i = U i := by
          intro i
          induction i using Fin.induction with
          | zero => rw [stateF_zero, rot_zero, zero_add]
          | succ i ih =>
            rw [stateF_succ, ih, rot_zero]
            show layer k hk gap (U i.castSucc) + 0 + (U i.succ - layer k hk gap (U i.castSucc)) = U i.succ
            abel
        refine ⟨data, ?_⟩
        rw [show ok = okF k hk r s gap initial inject delta path from rfl, ok_iff]
        intro p _
        refine ⟨hi p, fun t _ => ?_⟩
        rw [hst]
        have hU : U t.castSucc = u t := by simp [U]
        rw [hU]
        have := hu t
        simp only [localSet, Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact this p
      obtain ⟨t, ht⟩ := hempty
      refine ⟨B t, hBk t, fun raw data hok => ?_⟩
      rw [show ok = okF k hk r s gap initial inject delta path from rfl, ok_iff] at hok
      have hv : stateF k hk r gap initial inject data raw t.castSucc ∈
          Inter (Sol k hk r s gap inject delta path t) (B t) := by
        simp only [Inter, Finset.mem_filter, Finset.mem_univ, true_and]
        intro q hq; exact (hok q hq).2 t (Fin.castSucc_lt_last t)
      have := memB t _ hv
      rw [ht] at this; simp at this

end PEqualNP.Outside.L_meta_25888_aux

open PEqualNP.Outside.L_meta_25888_aux in
theorem PEqualNP.Outside.L_meta_25888 : (∀ (k r s : Nat) (hk : 0 < k),
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun t : Nat => (⟨t % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (amount : Nat) (x : W) (j : Fin k) => x (ix (j.val+k-amount % k))
  let layer := fun (gap : Nat) (x : W) =>
    let m := fun (j : Fin k) => x j + x (ix (j.val+gap)) + x (ix (j.val+k-gap % k))
    fun (j : Fin k) => m j + (1+m (ix (j.val+1))) * m (ix (j.val+2))
  ∀ (col : Bool) (delta : Fin s → W) (path : Fin (r+1) → Fin s → W),
    let initial := if col then 3 else 1
    let gap := if col then 2 else 1
    let inject := fun t : Nat => if col then 3*(t+1)+1 else 2*t
    let state := fun (data : W × (Fin r → W)) (key : W) (time : Fin (r+1)) =>
      ((List.finRange r).take time.val).foldl (fun v tick =>
        layer gap v + rot (inject tick.val) key + data.2 tick) (rot initial key + data.1)
    let S := Fin r → W
    let ok := fun (raw : W) (data : W × S) (h : Fin (r+1)) (keep : Finset (Fin s)) =>
      ∀ t : Fin (r+1), t ≤ h → ∀ p ∈ keep,
        state data (raw+delta p) t - state data raw t = path t p
    let localSet := fun (t : Fin r) => (Finset.univ : Finset W).filter (fun v =>
      ∀ p : Fin s, layer gap (v+path t.castSucc p) - layer gap v +
        rot (inject t.val) (delta p) = path t.succ p)
    let feasible := ∃ data : W × S, ok 0 data (Fin.last r) Finset.univ
    (feasible → ∃ keep : Fin (r+1) → Finset (Fin s),
      keep 0 = ∅ ∧
      (∀ t : Fin r, keep t.castSucc ⊆ keep t.succ ∧
        (keep t.succ \ keep t.castSucc).card ≤ k - Nat.log2 (localSet t).card) ∧
      (∀ (raw : W) (data : W × S) (h : Fin (r+1)),
        (ok raw data h (keep h) ↔ ok raw data h Finset.univ))) ∧
    (¬feasible → ∃ small : Finset (Fin s), small.card ≤ k+1 ∧
      ∀ (raw : W) (data : W × S), ¬ok raw data (Fin.last r) small)) := by
  intro k r s hk F W ix rot layer col delta path initial gap inject state S ok localSet feasible
  exact main k r s hk gap initial inject delta path
