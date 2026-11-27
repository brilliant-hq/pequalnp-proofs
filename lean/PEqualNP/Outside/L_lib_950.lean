import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_950

open Finset Module Matrix

noncomputable def red : ZMod 4 →+* ZMod 2 := ZMod.castHom (by norm_num) (ZMod 2)
def lift (c : ZMod 2) : ZMod 4 := (c.val : ZMod 4)
def dbl (c : ZMod 2) : ZMod 4 := 2 * (c.val : ZMod 4)
def hi (z : ZMod 4) : ZMod 2 := ((z.val / 2 : ℕ) : ZMod 2)

theorem red_val (z : ZMod 4) : red z = (z.val : ZMod 2) := by
  rw [red, ZMod.castHom_apply, ZMod.cast_eq_val]

theorem f_lift : ∀ c : ZMod 2, red (lift c) = c := by
  intro c; rw [red_val]; revert c; decide
theorem f_dbl : ∀ c : ZMod 2, red (dbl c) = 0 := by
  intro c; rw [red_val]; revert c; decide
theorem f_split : ∀ z : ZMod 4, z = lift (red z) + dbl (hi z) := by
  intro z; rw [red_val]; revert z; decide
theorem f_mul : ∀ (u : ZMod 4) (c : ZMod 2), u * dbl c = dbl (red u * c) := by
  intro u c; rw [red_val]; revert u c; decide
theorem f_add : ∀ a b : ZMod 2, dbl (a + b) = dbl a + dbl b := by decide
theorem f_dz : dbl 0 = 0 := by decide
theorem f_two : ∀ z : ZMod 4, z + z = 0 ↔ red z = 0 := by
  intro z; rw [red_val]; revert z; decide
theorem f_even : ∀ z : ZMod 4, red z = 0 → z = dbl (hi z) := by
  intro z; rw [red_val]; revert z; decide
theorem f_dred : ∀ z : ZMod 4, dbl (red z) = z + z := by
  intro z; rw [red_val]; revert z; decide
theorem f_dd : ∀ c : ZMod 2, dbl c + dbl c = 0 := by decide
theorem f_hd : ∀ c : ZMod 2, hi (dbl c) = c := by decide
theorem f_ld : ∀ a c : ZMod 2, lift a * dbl c = dbl (a * c) := by decide
theorem f_dl : ∀ a c : ZMod 2, dbl a * lift c = dbl (a * c) := by decide

def dblHom : ZMod 2 →+ ZMod 4 := AddMonoidHom.mk' dbl f_add

theorem dbl_sum {ι : Type} (s : Finset ι) (f : ι → ZMod 2) :
    dbl (∑ i ∈ s, f i) = ∑ i ∈ s, dbl (f i) :=
  map_sum dblHom f s

variable {a b n m : ℕ}

def rd (M : Matrix (Fin a) (Fin b) (ZMod 4)) : Matrix (Fin a) (Fin b) (ZMod 2) :=
  fun i j => ((M i j).val : ZMod 2)

theorem rd_eq (M : Matrix (Fin a) (Fin b) (ZMod 4)) : rd M = M.map red := by
  ext i j; simp [rd, red_val]

def out (M : Matrix (Fin a) (Fin b) (ZMod 4)) : Finset (Fin a → ZMod 4) :=
  Finset.univ.image (fun x : Fin b → ZMod 4 => M.mulVec x)

def kil (M : Matrix (Fin a) (Fin b) (ZMod 4)) : Finset (Fin a → ZMod 4) :=
  (out M).filter (fun y => ∀ i, y i + y i = 0)

theorem mem_out (M : Matrix (Fin a) (Fin b) (ZMod 4)) (y : Fin a → ZMod 4) :
    y ∈ out M ↔ ∃ x, M *ᵥ x = y := by
  simp [out]

theorem red_mulVec (M : Matrix (Fin a) (Fin b) (ZMod 4)) (x : Fin b → ZMod 4) :
    (fun i => red ((M *ᵥ x) i)) = M.map red *ᵥ (fun j => red (x j)) := by
  funext i
  exact RingHom.map_mulVec red M x i

theorem mulVec_dbl (M : Matrix (Fin a) (Fin b) (ZMod 4)) (c : Fin b → ZMod 2) :
    M *ᵥ (fun j => dbl (c j)) = fun i => dbl ((M.map red *ᵥ c) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, f_mul, dbl_sum]

theorem split_vec (y : Fin b → ZMod 4) :
    y = (fun j => lift (red (y j))) + fun j => dbl (hi (y j)) := by
  funext j; exact f_split (y j)

theorem decomp (M : Matrix (Fin a) (Fin b) (ZMod 4)) (y : Fin b → ZMod 4) :
    M *ᵥ y = M *ᵥ (fun j => lift (red (y j))) +
      fun i => dbl ((M.map red *ᵥ fun j => hi (y j)) i) := by
  conv_lhs => rw [split_vec y]
  rw [Matrix.mulVec_add, mulVec_dbl]

def rngF (M : Matrix (Fin a) (Fin b) (ZMod 2)) : Finset (Fin a → ZMod 2) :=
  Finset.univ.image (fun x => M *ᵥ x)

theorem cardSub (S : Submodule (ZMod 2) (Fin a → ZMod 2)) [DecidablePred (· ∈ S)] :
    (univ.filter (· ∈ S)).card = 2 ^ finrank (ZMod 2) S := by
  have h1 := Module.card_eq_pow_finrank (K := ZMod 2) (V := S)
  rw [ZMod.card] at h1
  rw [← h1, Fintype.card_subtype]

theorem card_rngF (M : Matrix (Fin a) (Fin b) (ZMod 2)) : (rngF M).card = 2 ^ M.rank := by
  classical
  have : rngF M = univ.filter (· ∈ LinearMap.range M.mulVecLin) := by
    ext y; simp [rngF, LinearMap.mem_range]
  rw [this, cardSub]; rfl

theorem mem_img (U : Matrix (Fin a) (Fin b) (ZMod 4)) (S : Finset (Fin b → ZMod 2))
    (y : Fin b → ZMod 4) (hy : (fun j => red (y j)) ∈ S) :
    U *ᵥ y ∈ (S ×ˢ rngF (U.map red)).image
      (fun ac => U *ᵥ (fun j => lift (ac.1 j)) + fun i => dbl (ac.2 i)) := by
  rw [Finset.mem_image]
  refine ⟨((fun j => red (y j)), U.map red *ᵥ fun j => hi (y j)), ?_, ?_⟩
  · simp only [Finset.mem_product, rngF, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨hy, _, rfl⟩
  · exact (decomp U y).symm

theorem card_img (U : Matrix (Fin a) (Fin b) (ZMod 4)) (S : Finset (Fin b → ZMod 2)) :
    ((S ×ˢ rngF (U.map red)).image
      (fun ac => U *ᵥ (fun j => lift (ac.1 j)) + fun i => dbl (ac.2 i))).card ≤
      S.card * 2 ^ (U.map red).rank := by
  refine (Finset.card_image_le).trans ?_
  rw [Finset.card_product, card_rngF]

theorem L1 (M : Matrix (Fin a) (Fin b) (ZMod 4)) :
    (out M).card = 2 ^ (M.map red).rank * (kil M).card := by
  classical
  let π : (Fin a → ZMod 4) → (Fin a → ZMod 2) := fun y i => red (y i)
  have himg : (out M).image π = rngF (M.map red) := by
    ext c
    simp only [Finset.mem_image, out, rngF, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
      exact ⟨fun j => red (x j), (red_mulVec M x).symm⟩
    · rintro ⟨x, rfl⟩
      refine ⟨_, ⟨fun j => lift (x j), rfl⟩, ?_⟩
      show (fun i => red ((M *ᵥ _) i)) = _
      rw [red_mulVec]
      simp [f_lift]
  rw [Finset.card_eq_sum_card_image π (out M), himg, ← card_rngF, ← smul_eq_mul,
    ← Finset.sum_const]
  apply Finset.sum_congr rfl
  intro c hc
  rw [← himg, Finset.mem_image] at hc
  obtain ⟨y0, hy0, rfl⟩ := hc
  obtain ⟨x0, rfl⟩ := (mem_out M y0).1 hy0
  symm
  refine Finset.card_bij' (fun k _ => M *ᵥ x0 + k) (fun y _ => y - M *ᵥ x0) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [kil, Finset.mem_filter] at hk
    obtain ⟨⟨x1, rfl⟩, h2⟩ := And.imp_left (mem_out M _).1 hk
    simp only [Finset.mem_filter]
    refine ⟨(mem_out M _).2 ⟨x0 + x1, Matrix.mulVec_add _ _ _⟩, ?_⟩
    funext i
    simp only [π, Pi.add_apply, map_add, (f_two _).1 (h2 i), add_zero]
  · intro y hy
    simp only [Finset.mem_filter] at hy
    obtain ⟨⟨x1, rfl⟩, h2⟩ := And.imp_left (mem_out M _).1 hy
    simp only [kil, Finset.mem_filter]
    refine ⟨(mem_out M _).2 ⟨x1 - x0, Matrix.mulVec_sub _ _ _⟩, ?_⟩
    intro i
    rw [f_two, Pi.sub_apply, map_sub]
    have := congrFun h2 i
    simp only [π] at this
    rw [this, sub_self]
  · intro k _; simp
  · intro y _; simp

theorem rank_cols {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (M : Matrix κ ι (ZMod 2)) (J : Finset ι) (h : ∀ j ∉ J, ∀ l, M l j = 0) :
    M.rank ≤ J.card := by
  rw [Matrix.rank_eq_finrank_span_cols]
  calc finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Mᵀ))
      ≤ finrank (ZMod 2) (Submodule.span (ZMod 2)
          ((J.image fun j => Mᵀ j : Finset (κ → ZMod 2)) : Set (κ → ZMod 2))) := by
        apply Submodule.finrank_mono
        apply Submodule.span_le.2
        rintro _ ⟨j, rfl⟩
        by_cases hj : j ∈ J
        · apply Submodule.subset_span
          simp only [Finset.coe_image]
          exact Set.mem_image_of_mem _ hj
        · have : Mᵀ j = 0 := by funext l; exact h j hj l
          rw [this]
          exact Submodule.zero_mem _
    _ ≤ (J.image fun j => Mᵀ j).card := finrank_span_finset_le_card _
    _ ≤ J.card := Finset.card_image_le

theorem rank_rows {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι κ (ZMod 2)) (J : Finset ι) (h : ∀ j ∉ J, ∀ k, M j k = 0) :
    M.rank ≤ J.card := by
  rw [← Matrix.rank_transpose]
  exact rank_cols Mᵀ J (fun j hj k => h j hj k)

theorem pad {ι : Type} [Fintype ι] [DecidableEq ι] (w : ℕ) (hw : Fintype.card ι ≤ w)
    (U0 : Matrix (Fin n) ι (ZMod 4)) (V0 : Matrix ι (Fin m) (ZMod 4)) :
    ∃ (U : Matrix (Fin n) (Fin w) (ZMod 4)) (V : Matrix (Fin w) (Fin m) (ZMod 4)),
      U * V = U0 * V0 ∧ (U.map red).rank ≤ (U0.map red).rank ∧
        (V.map red).rank ≤ (V0.map red).rank := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := ι) (β := Fin w) (by simpa using hw)
  let E : Matrix ι (Fin w) (ZMod 4) := Matrix.of fun a l => if e a = l then 1 else 0
  have hE : E * Eᵀ = 1 := by
    ext a c
    simp only [E, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply,
      mul_ite, mul_one, mul_zero]
    simp [Finset.sum_ite_eq, e.injective.eq_iff, eq_comm]
  refine ⟨U0 * E, Eᵀ * V0, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc E, hE, Matrix.one_mul]
  · rw [Matrix.map_mul]; exact Matrix.rank_mul_le_left _ _
  · rw [Matrix.map_mul]; exact Matrix.rank_mul_le_right _ _

theorem nec {w p q : ℕ} (G : Matrix (Fin n) (Fin m) (ZMod 4))
    (U : Matrix (Fin n) (Fin w) (ZMod 4)) (V : Matrix (Fin w) (Fin m) (ZMod 4))
    (h : U * V = G) (hp : (U.map red).rank ≤ p) (hq : (V.map red).rank ≤ q) :
    (G.map red).rank ≤ min p q ∧ (out G).card ≤ 2 ^ (p + q) ∧ (kil G).card ≤ 2 ^ w := by
  have hm : G.map red = U.map red * V.map red := by rw [← h, Matrix.map_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [hm]
    exact le_min ((Matrix.rank_mul_le_left _ _).trans hp) ((Matrix.rank_mul_le_right _ _).trans hq)
  · have sub : out G ⊆ (rngF (V.map red) ×ˢ rngF (U.map red)).image
        (fun ac => U *ᵥ (fun j => lift (ac.1 j)) + fun i => dbl (ac.2 i)) := by
      intro y hy
      obtain ⟨x, rfl⟩ := (mem_out G y).1 hy
      rw [← h, ← Matrix.mulVec_mulVec]
      apply mem_img
      rw [red_mulVec]
      simp [rngF]
    calc (out G).card ≤ _ := Finset.card_le_card sub
      _ ≤ _ := card_img U _
      _ = 2 ^ (V.map red).rank * 2 ^ (U.map red).rank := by rw [card_rngF]
      _ ≤ 2 ^ q * 2 ^ p := Nat.mul_le_mul (Nat.pow_le_pow_right two_pos hq)
          (Nat.pow_le_pow_right two_pos hp)
      _ = 2 ^ (p + q) := by rw [pow_add, mul_comm]
  · have sub : kil G ⊆ kil U := by
      intro y
      simp only [kil, Finset.mem_filter]
      rintro ⟨hy, h2⟩
      refine ⟨?_, h2⟩
      obtain ⟨x, rfl⟩ := (mem_out G _).1 hy
      exact (mem_out U _).2 ⟨V *ᵥ x, by rw [Matrix.mulVec_mulVec, h]⟩
    have subU : out U ⊆ ((univ : Finset (Fin w → ZMod 2)) ×ˢ rngF (U.map red)).image
        (fun ac => U *ᵥ (fun j => lift (ac.1 j)) + fun i => dbl (ac.2 i)) := by
      intro y hy
      obtain ⟨x, rfl⟩ := (mem_out U y).1 hy
      exact mem_img U _ x (Finset.mem_univ _)
    have h3 : 2 ^ (U.map red).rank * (kil U).card ≤ 2 ^ (U.map red).rank * 2 ^ w := by
      rw [← L1]
      calc (out U).card ≤ _ := Finset.card_le_card subU
        _ ≤ _ := card_img U _
        _ = _ := by simp [mul_comm]
    exact (Finset.card_le_card sub).trans (Nat.le_of_mul_le_mul_left h3 (by positivity))

theorem f_cases : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide

theorem card_lt (s s1 : ℕ) : (univ.filter fun j : Fin s => j.val < s1).card ≤ s1 := by
  calc _ ≤ (range s1).card := by
        apply Finset.card_le_card_of_injOn (fun j => j.val)
        · intro j hj
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hj
          simpa using hj
        · intro x _ y _ hxy; exact Fin.ext hxy
    _ = s1 := Finset.card_range _

theorem card_ge (s s1 : ℕ) : (univ.filter fun j : Fin s => ¬ j.val < s1).card ≤ s - s1 := by
  calc _ ≤ (range (s - s1)).card := by
        apply Finset.card_le_card_of_injOn (fun j => j.val - s1)
        · intro j hj
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hj
          simp only [Finset.coe_range, Set.mem_Iio]
          have := j.isLt
          omega
        · intro x hx y hy hxy
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx hy
          simp only at hxy
          exact Fin.ext (by omega)
    _ = s - s1 := Finset.card_range _

theorem suf {w p q : ℕ} (G : Matrix (Fin n) (Fin m) (ZMod 4))
    (h1 : (G.map red).rank ≤ min p q) (h2 : (out G).card ≤ 2 ^ (p + q))
    (h3 : (kil G).card ≤ 2 ^ w) :
    ∃ (U : Matrix (Fin n) (Fin w) (ZMod 4)) (V : Matrix (Fin w) (Fin m) (ZMod 4)),
      U * V = G ∧ (U.map red).rank ≤ p ∧ (V.map red).rank ≤ q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Gb := G.map red with hGb
  let R : Submodule (ZMod 2) (Fin n → ZMod 2) := LinearMap.range Gb.mulVecLin
  let T : Submodule (ZMod 2) (Fin n → ZMod 2) :=
    { carrier := {c | (fun i => dbl (c i)) ∈ out G}
      add_mem' := by
        intro c d hc hd
        obtain ⟨x, hx⟩ := (mem_out G _).1 hc
        obtain ⟨y, hy⟩ := (mem_out G _).1 hd
        refine (mem_out G _).2 ⟨x + y, ?_⟩
        rw [Matrix.mulVec_add, hx, hy]
        funext i
        simp [f_add]
      zero_mem' := (mem_out G _).2 ⟨0, by funext i; simp [f_dz]⟩
      smul_mem' := by
        intro s c hc
        have : s = 0 ∨ s = 1 := f_cases s
        rcases this with rfl | rfl
        · show (fun i => dbl (((0 : ZMod 2) • c) i)) ∈ out G
          simp only [zero_smul, Pi.zero_apply, f_dz]
          exact (mem_out G _).2 ⟨0, by funext i; simp⟩
        · show (fun i => dbl (((1 : ZMod 2) • c) i)) ∈ out G
          simpa using hc }
  have memT : ∀ c, c ∈ T ↔ (fun i => dbl (c i)) ∈ out G := fun c => Iff.rfl
  have hRT : R ≤ T := by
    rintro c ⟨x, rfl⟩
    rw [memT]
    refine (mem_out G _).2 ⟨(fun j => lift (x j)) + (fun j => lift (x j)), ?_⟩
    have : Gb.mulVecLin x = fun i => red ((G *ᵥ fun j => lift (x j)) i) := by
      rw [red_mulVec, Matrix.mulVecLin_apply]
      simp [Gb, f_lift]
    rw [this, Matrix.mulVec_add]
    funext i
    simp [f_dred]
  have hkT : (kil G).card = 2 ^ finrank (ZMod 2) T := by
    rw [← cardSub T]
    refine Finset.card_bij' (fun y _ => fun i => hi (y i)) (fun c _ => fun i => dbl (c i))
      ?_ ?_ ?_ ?_
    · intro y hy
      simp only [kil, Finset.mem_filter] at hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [memT]
      convert hy.1 using 1
      funext i
      exact (f_even _ ((f_two _).1 (hy.2 i))).symm
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
      simp only [kil, Finset.mem_filter]
      exact ⟨hc, fun i => f_dd _⟩
    · intro y hy
      simp only [kil, Finset.mem_filter] at hy
      funext i
      exact (f_even _ ((f_two _).1 (hy.2 i))).symm
    · intro c _
      funext i
      exact f_hd _
  have hL1 := L1 G
  have hrk : Gb.rank = finrank (ZMod 2) R := rfl
  have hrt : finrank (ZMod 2) R ≤ finrank (ZMod 2) T := Submodule.finrank_mono hRT
  have hpq : finrank (ZMod 2) R + finrank (ZMod 2) T ≤ p + q := by
    have : 2 ^ (finrank (ZMod 2) R + finrank (ZMod 2) T) ≤ 2 ^ (p + q) := by
      rw [pow_add, ← hrk, ← hkT, ← hL1]; exact h2
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  have htw : finrank (ZMod 2) T ≤ w := by
    rw [hkT] at h3
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h3
  have hrp : finrank (ZMod 2) R ≤ p := hrk ▸ (h1.trans (min_le_left _ _))
  have hrq : finrank (ZMod 2) R ≤ q := hrk ▸ (h1.trans (min_le_right _ _))
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl R
  let S := C ⊓ T
  have hTS : T = R ⊔ S := by
    rw [← sup_inf_assoc_of_le C hRT, hC.sup_eq_top, top_inf_eq]
  have hRS : R ⊓ S = ⊥ := by
    apply eq_bot_iff.2
    intro x hx
    have : x ∈ R ⊓ C := ⟨hx.1, hx.2.1⟩
    rw [hC.inf_eq_bot] at this
    exact this
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq R S
  rw [← hTS, hRS, finrank_bot, add_zero] at hsum
  set r := finrank (ZMod 2) R with hr
  set s := finrank (ZMod 2) S with hs
  let βR := Module.finBasis (ZMod 2) R
  let βS := Module.finBasis (ZMod 2) S
  let zR : Fin r → (Fin n → ZMod 2) := fun i => (βR i : Fin n → ZMod 2)
  let zS : Fin s → (Fin n → ZMod 2) := fun j => (βS j : Fin n → ZMod 2)
  have P1 : ∀ i, ∃ y, Gb *ᵥ y = zR i := by
    intro i
    obtain ⟨y, hy⟩ := LinearMap.mem_range.1 (βR i).2
    exact ⟨y, hy⟩
  choose y hy using P1
  let X : Matrix (Fin m) (Fin r) (ZMod 4) := Matrix.of fun k i => lift (y i k)
  let A' := G * X
  have hA : ∀ l i, red (A' l i) = zR i l := by
    intro l i
    rw [← hy i]
    simp only [A', X, Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul, f_lift,
      Matrix.mulVec, dotProduct, Gb, Matrix.map_apply]
  have P3 : ∀ c ∈ R, ∃ α : Fin r → ZMod 2, c = A'.map red *ᵥ α := by
    intro c hc
    refine ⟨βR.repr ⟨c, hc⟩, ?_⟩
    have e1 := congrArg Subtype.val (βR.sum_repr ⟨c, hc⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at e1
    conv_lhs => rw [← e1]
    funext l
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
      Matrix.map_apply, hA]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have P4 : ∀ e ∈ T, ∃ ρ ∈ R, ∃ δ : Fin s → ZMod 2, e = ρ + ∑ j, δ j • zS j := by
    intro e he
    rw [hTS] at he
    obtain ⟨y1, hy1, z1, hz1, hyz⟩ := Submodule.mem_sup.1 he
    refine ⟨y1, hy1, βS.repr ⟨z1, hz1⟩, ?_⟩
    have e1 := congrArg Subtype.val (βS.sum_repr ⟨z1, hz1⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at e1
    conv_lhs => rw [← hyz]
    exact congrArg (y1 + ·) e1.symm
  have hcol : ∀ k : Fin m, ∃ (α γ : Fin r → ZMod 2) (δ : Fin s → ZMod 2),
      ∀ l, G l k = (A' *ᵥ fun i => lift (α i) + dbl (γ i)) l + ∑ j, dbl (zS j l * δ j) := by
    intro k
    have hgR : (fun l => red (G l k)) ∈ R := by
      refine ⟨Pi.single k 1, ?_⟩
      funext l
      simp [Gb]
    obtain ⟨α, hα⟩ := P3 _ hgR
    set dv : Fin n → ZMod 4 := (fun l => G l k) - A' *ᵥ (fun i => lift (α i)) with hdv
    have hdout : dv ∈ out G := by
      refine (mem_out G _).2 ⟨Pi.single k 1 - X *ᵥ (fun i => lift (α i)), ?_⟩
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hdv]
      congr 1
      funext l
      simp
    have hdred : ∀ l, red (dv l) = 0 := by
      intro l
      have e1 := congrFun (red_mulVec A' (fun i => lift (α i))) l
      have e2 := congrFun hα l
      simp only [f_lift] at e1
      simp only [hdv, Pi.sub_apply, map_sub, e1, ← e2, sub_self]
    set e : Fin n → ZMod 2 := fun l => hi (dv l) with he
    have hde : ∀ l, dv l = dbl (e l) := fun l => f_even _ (hdred l)
    have heT : e ∈ T := by
      rw [memT]
      convert hdout using 1
      funext l
      exact (hde l).symm
    obtain ⟨ρ, hρ, δ, hρδ⟩ := P4 e heT
    obtain ⟨γ, hγ⟩ := P3 ρ hρ
    refine ⟨α, γ, δ, fun l => ?_⟩
    have hGl : G l k = (A' *ᵥ fun i => lift (α i)) l + dv l := by
      simp [hdv]
    have hsp : (fun i => lift (α i) + dbl (γ i)) = (fun i => lift (α i)) + fun i => dbl (γ i) :=
      rfl
    rw [hGl, hde, hsp, Matrix.mulVec_add, Pi.add_apply, add_assoc]
    congr 1
    rw [hρδ, hγ]
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, f_add, dbl_sum]
    congr 1
    · simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, f_mul, dbl_sum]
    · exact Finset.sum_congr rfl (fun j _ => by rw [mul_comm])
  choose α γ δ hcol using hcol
  let s1 := min s (p - r)
  let Zu : Matrix (Fin n) (Fin s) (ZMod 4) :=
    Matrix.of fun l j => if j.val < s1 then lift (zS j l) else dbl (zS j l)
  let Va : Matrix (Fin r) (Fin m) (ZMod 4) := Matrix.of fun i k => lift (α k i) + dbl (γ k i)
  let Vd : Matrix (Fin s) (Fin m) (ZMod 4) :=
    Matrix.of fun j k => if j.val < s1 then dbl (δ k j) else lift (δ k j)
  let U0 := Matrix.fromCols A' Zu
  let V0 := Matrix.fromRows Va Vd
  have hprod : U0 * V0 = G := by
    simp only [U0, V0]
    rw [Matrix.fromCols_mul_fromRows]
    ext l k
    rw [hcol k l, Matrix.add_apply]
    congr 1
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Zu, Vd, Matrix.of_apply]
    split_ifs
    · rw [f_ld, mul_comm]
    · rw [f_dl, mul_comm]
  have hU : (U0.map red).rank ≤ r + s1 := by
    refine (rank_cols (U0.map red) (univ.disjSum (univ.filter fun j : Fin s => j.val < s1))
      ?_).trans ?_
    · intro j hj l
      cases j with
      | inl i => simp at hj
      | inr j =>
        simp only [Finset.inr_mem_disjSum, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp [U0, Zu, hj, f_dbl]
    · rw [Finset.card_disjSum, Finset.card_univ, Fintype.card_fin]
      exact Nat.add_le_add_left (card_lt s s1) _
  have hV : (V0.map red).rank ≤ r + (s - s1) := by
    refine (rank_rows (V0.map red) (univ.disjSum (univ.filter fun j : Fin s => ¬ j.val < s1))
      ?_).trans ?_
    · intro j hj k
      cases j with
      | inl i => simp at hj
      | inr j =>
        simp only [Finset.inr_mem_disjSum, Finset.mem_filter, Finset.mem_univ, true_and,
          not_not] at hj
        simp [V0, Vd, hj, f_dbl]
    · rw [Finset.card_disjSum, Finset.card_univ, Fintype.card_fin]
      exact Nat.add_le_add_left (card_ge s s1) _
  obtain ⟨U, V, hUV, hU', hV'⟩ := pad w (by simp; omega) U0 V0
  refine ⟨U, V, hUV.trans hprod, ?_, ?_⟩
  · have : r + s1 ≤ p := by omega
    omega
  · have : r + (s - s1) ≤ q := by omega
    omega

end PEqualNP.Outside.L_lib_950

open PEqualNP.Outside.L_lib_950 in
theorem PEqualNP.Outside.L_lib_950 : ∀ (n m w p q : ℕ) (G : Matrix (Fin n) (Fin m) (ZMod 4)),
  let reduce := fun {a b : ℕ} (M : Matrix (Fin a) (Fin b) (ZMod 4)) =>
    (fun i j => ((M i j).val : ZMod 2) : Matrix (Fin a) (Fin b) (ZMod 2))
  let outputs := Finset.univ.image (fun x : Fin m → ZMod 4 => G.mulVec x)
  let killed := outputs.filter (fun y => ∀ i, y i + y i = 0)
  (∃ (U : Matrix (Fin n) (Fin w) (ZMod 4)) (V : Matrix (Fin w) (Fin m) (ZMod 4)),
    U * V = G ∧ Matrix.rank (reduce U) ≤ p ∧ Matrix.rank (reduce V) ≤ q) ↔
    Matrix.rank (reduce G) ≤ min p q ∧ outputs.card ≤ 2^(p+q) ∧ killed.card ≤ 2^w := by
  intro n m w p q G
  have key : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) (ZMod 4)),
      (fun i j => ((M i j).val : ZMod 2) : Matrix (Fin a) (Fin b) (ZMod 2)) = M.map red :=
    fun M => rd_eq M
  simp only [key]
  constructor
  · rintro ⟨U, V, h, hp, hq⟩
    exact nec G U V h hp hq
  · rintro ⟨h1, h2, h3⟩
    exact suf G h1 h2 h3
