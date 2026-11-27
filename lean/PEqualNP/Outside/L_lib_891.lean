import PEqualNP.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace PEqualNP.Outside.L_lib_891_aux

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  revert x; decide

lemma zmod2_mul_self (x : ZMod 2) : x * x = x := by
  revert x; decide

lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x; decide

lemma zmod2_add_cancel_right (x y : ZMod 2) : x + y + y = x := by
  revert x y; decide

lemma zmod2_add_cancel_left (x y : ZMod 2) : x + (x + y) = y := by
  revert x y; decide

lemma zmod2_neg (x : ZMod 2) : -x = x := by
  revert x; decide

def isQuad {n : ℕ} (q : (Fin n → ZMod 2) → ZMod 2) : Prop :=
  ∃ (s : ZMod 2) (h : Fin n → ZMod 2) (M : Fin n → Fin n → ZMod 2),
    ∀ x, q x = s + dotProduct h x + ∑ i, ∑ j, M i j * x i * x j

def isAff {n : ℕ} (q : (Fin n → ZMod 2) → ZMod 2) : Prop :=
  ∃ (s : ZMod 2) (h : Fin n → ZMod 2), ∀ x, q x = s + dotProduct h x

def diff {n : ℕ} (d : Fin n → ZMod 2) (f : (Fin n → ZMod 2) → ZMod 2)
    (x : Fin n → ZMod 2) : ZMod 2 :=
  f (x + d) + f x

lemma diff_add {n : ℕ} (d : Fin n → ZMod 2) (f g : (Fin n → ZMod 2) → ZMod 2)
    (x : Fin n → ZMod 2) :
    diff d (fun y => f y + g y) x = diff d f x + diff d g x := by
  unfold diff
  dsimp only
  ring

lemma diff_smul {n : ℕ} (d : Fin n → ZMod 2) (c : ZMod 2) (f : (Fin n → ZMod 2) → ZMod 2)
    (x : Fin n → ZMod 2) :
    diff d (fun y => c * f y) x = c * diff d f x := by
  unfold diff
  dsimp only
  ring

lemma diff_sum {n : ℕ} {ι : Type*} (s : Finset ι) (d : Fin n → ZMod 2)
    (f : ι → (Fin n → ZMod 2) → ZMod 2) (x : Fin n → ZMod 2) :
    diff d (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, diff d (f i) x := by
  unfold diff
  dsimp only
  rw [← Finset.sum_add_distrib]

lemma diff_const {n : ℕ} (d : Fin n → ZMod 2) (c : ZMod 2) (x : Fin n → ZMod 2) :
    diff d (fun _ => c) x = 0 := by
  unfold diff
  dsimp only
  exact zmod2_add_self c

lemma diff_mul_left_inv {n : ℕ} (d : Fin n → ZMod 2) (g f : (Fin n → ZMod 2) → ZMod 2)
    (hg : ∀ y, g (y + d) = g y) (x : Fin n → ZMod 2) :
    diff d (fun y => g y * f y) x = g x * diff d f x := by
  unfold diff
  dsimp only
  rw [hg x]
  ring

lemma diff2_mul_left_inv {n : ℕ} (d1 d2 : Fin n → ZMod 2) (g f : (Fin n → ZMod 2) → ZMod 2)
    (hg1 : ∀ y, g (y + d1) = g y) (hg2 : ∀ y, g (y + d2) = g y) (x : Fin n → ZMod 2) :
    diff d1 (diff d2 (fun y => g y * f y)) x = g x * diff d1 (diff d2 f) x := by
  have h1 : diff d2 (fun y => g y * f y) = fun y => g y * diff d2 f y := by
    funext y
    exact diff_mul_left_inv d2 g f hg2 y
  rw [h1]
  exact diff_mul_left_inv d1 g (diff d2 f) hg1 x

lemma diff_lin {n : ℕ} (d : Fin n → ZMod 2) (s : ZMod 2) (h : Fin n → ZMod 2)
    (x : Fin n → ZMod 2) :
    diff d (fun y => s + dotProduct h y) x = dotProduct h d := by
  unfold diff
  dsimp only
  rw [dotProduct_add]
  have h1 : s + (dotProduct h x + dotProduct h d) + (s + dotProduct h x) =
      (s + s) + (dotProduct h x + dotProduct h x) + dotProduct h d := by ring
  rw [h1, zmod2_add_self, zmod2_add_self, zero_add, zero_add]

lemma diff2_zero_of_isAff {n : ℕ} {f : (Fin n → ZMod 2) → ZMod 2} (hf : isAff f)
    (d1 d2 x : Fin n → ZMod 2) :
    diff d1 (diff d2 f) x = 0 := by
  rcases hf with ⟨s, h, hf⟩
  have h1 : diff d2 f = fun _ => dotProduct h d2 := by
    funext y
    have : f = fun z => s + dotProduct h z := funext hf
    rw [this]
    exact diff_lin d2 s h y
  rw [h1]
  exact diff_const d1 (dotProduct h d2) x

lemma isAff_const {n : ℕ} (c : ZMod 2) : isAff (n := n) (fun _ => c) := by
  refine ⟨c, 0, fun x => ?_⟩
  simp

lemma isAff_lin {n : ℕ} (s : ZMod 2) (h : Fin n → ZMod 2) :
    isAff (fun x => s + dotProduct h x) :=
  ⟨s, h, fun _ => rfl⟩

lemma isAff_coord {n : ℕ} (i : Fin n) : isAff (fun x : Fin n → ZMod 2 => x i) := by
  refine ⟨0, Pi.single i 1, fun x => ?_⟩
  dsimp only
  rw [zero_add, dotProduct]
  simp [Pi.single_apply]

lemma isAff_add {n : ℕ} {f g : (Fin n → ZMod 2) → ZMod 2}
    (hf : isAff f) (hg : isAff g) : isAff (fun x => f x + g x) := by
  rcases hf with ⟨sf, hf, hfeq⟩
  rcases hg with ⟨sg, hg, hgeq⟩
  refine ⟨sf + sg, hf + hg, fun x => ?_⟩
  dsimp only
  rw [hfeq x, hgeq x, add_dotProduct]
  ring

lemma isAff_smul {n : ℕ} (c : ZMod 2) {f : (Fin n → ZMod 2) → ZMod 2}
    (hf : isAff f) : isAff (fun x => c * f x) := by
  rcases hf with ⟨sf, hf, hfeq⟩
  refine ⟨c * sf, c • hf, fun x => ?_⟩
  dsimp only
  rw [hfeq x, smul_dotProduct, smul_eq_mul]
  ring

lemma isAff_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → (Fin n → ZMod 2) → ZMod 2)
    (hf : ∀ i ∈ s, isAff (f i)) : isAff (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using isAff_const (n := n) 0
  | @insert a s ha ih =>
    have h1 : isAff (f a) := hf a (Finset.mem_insert_self a s)
    have h2 : isAff (fun x => ∑ i ∈ s, f i x) :=
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have h3 : (fun x => ∑ i ∈ insert a s, f i x) = fun x => f a x + ∑ i ∈ s, f i x := by
      funext x
      exact Finset.sum_insert ha
    rw [h3]
    exact isAff_add h1 h2

lemma isAff_shift {n : ℕ} (d : Fin n → ZMod 2) {f : (Fin n → ZMod 2) → ZMod 2}
    (hf : isAff f) : isAff (fun x => f (x + d)) := by
  rcases hf with ⟨s, h, hfeq⟩
  refine ⟨s + dotProduct h d, h, fun x => ?_⟩
  dsimp only
  rw [hfeq (x + d), dotProduct_add]
  ring

lemma isQuad_of_isAff {n : ℕ} {f : (Fin n → ZMod 2) → ZMod 2} (hf : isAff f) : isQuad f := by
  rcases hf with ⟨s, h, hfeq⟩
  refine ⟨s, h, fun _ _ => 0, fun x => ?_⟩
  simp [hfeq x]

lemma isQuad_add {n : ℕ} {f g : (Fin n → ZMod 2) → ZMod 2}
    (hf : isQuad f) (hg : isQuad g) : isQuad (fun x => f x + g x) := by
  rcases hf with ⟨sf, hf, Mf, hfeq⟩
  rcases hg with ⟨sg, hg, Mg, hgeq⟩
  refine ⟨sf + sg, hf + hg, fun i j => Mf i j + Mg i j, fun x => ?_⟩
  dsimp only
  rw [hfeq x, hgeq x, add_dotProduct]
  have hsum : (∑ i : Fin n, ∑ j : Fin n, (Mf i j + Mg i j) * x i * x j) =
      (∑ i : Fin n, ∑ j : Fin n, Mf i j * x i * x j) +
      (∑ i : Fin n, ∑ j : Fin n, Mg i j * x i * x j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  ring

lemma isQuad_smul {n : ℕ} (c : ZMod 2) {f : (Fin n → ZMod 2) → ZMod 2}
    (hf : isQuad f) : isQuad (fun x => c * f x) := by
  rcases hf with ⟨sf, hf, Mf, hfeq⟩
  refine ⟨c * sf, c • hf, fun i j => c * Mf i j, fun x => ?_⟩
  dsimp only
  rw [hfeq x, smul_dotProduct, smul_eq_mul]
  have hsum : (∑ i : Fin n, ∑ j : Fin n, (c * Mf i j) * x i * x j) =
      c * ∑ i : Fin n, ∑ j : Fin n, Mf i j * x i * x j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  ring

lemma isQuad_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → (Fin n → ZMod 2) → ZMod 2)
    (hf : ∀ i ∈ s, isQuad (f i)) : isQuad (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using isQuad_of_isAff (isAff_const (n := n) 0)
  | @insert a s ha ih =>
    have h1 : isQuad (f a) := hf a (Finset.mem_insert_self a s)
    have h2 : isQuad (fun x => ∑ i ∈ s, f i x) :=
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have h3 : (fun x => ∑ i ∈ insert a s, f i x) = fun x => f a x + ∑ i ∈ s, f i x := by
      funext x
      exact Finset.sum_insert ha
    rw [h3]
    exact isQuad_add h1 h2

lemma isQuad_mul_isAff {n : ℕ} {f g : (Fin n → ZMod 2) → ZMod 2}
    (hf : isAff f) (hg : isAff g) : isQuad (fun x => f x * g x) := by
  rcases hf with ⟨sf, hf, hfeq⟩
  rcases hg with ⟨sg, hg, hgeq⟩
  refine ⟨sf * sg, sf • hg + sg • hf, fun i j => hf i * hg j, fun x => ?_⟩
  dsimp only
  rw [hfeq x, hgeq x, add_dotProduct, smul_dotProduct, smul_dotProduct,
    smul_eq_mul, smul_eq_mul]
  have hdot : dotProduct hf x * dotProduct hg x =
      ∑ i : Fin n, ∑ j : Fin n, hf i * hg j * x i * x j := by
    unfold dotProduct
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  calc (sf + dotProduct hf x) * (sg + dotProduct hg x)
      = sf * sg + (sf * dotProduct hg x + sg * dotProduct hf x) +
        dotProduct hf x * dotProduct hg x := by ring
    _ = sf * sg + (sf * dotProduct hg x + sg * dotProduct hf x) +
        ∑ i : Fin n, ∑ j : Fin n, hf i * hg j * x i * x j := by rw [hdot]

lemma isAff_diff_of_isQuad {n : ℕ} {q : (Fin n → ZMod 2) → ZMod 2}
    (hq : isQuad q) (d : Fin n → ZMod 2) : isAff (diff d q) := by
  rcases hq with ⟨s, h, M, hqeq⟩
  have hdiff : diff d q = fun x =>
      dotProduct h d + ∑ i : Fin n, ∑ j : Fin n,
        M i j * (d i * d j + d i * x j + d j * x i) := by
    funext x
    unfold diff
    rw [hqeq (x + d), hqeq x, dotProduct_add]
    have hlin : (s + (dotProduct h x + dotProduct h d) +
          ∑ i : Fin n, ∑ j : Fin n, M i j * (x + d) i * (x + d) j) +
        (s + dotProduct h x + ∑ i : Fin n, ∑ j : Fin n, M i j * x i * x j) =
        dotProduct h d +
        ((∑ i : Fin n, ∑ j : Fin n, M i j * (x i + d i) * (x j + d j)) +
         (∑ i : Fin n, ∑ j : Fin n, M i j * x i * x j)) := by
      have hss : s + s = 0 := zmod2_add_self s
      have hxx : dotProduct h x + dotProduct h x = 0 := zmod2_add_self _
      change (s + (dotProduct h x + dotProduct h d) +
            ∑ i : Fin n, ∑ j : Fin n, M i j * (x i + d i) * (x j + d j)) +
          (s + dotProduct h x + ∑ i : Fin n, ∑ j : Fin n, M i j * x i * x j) = _
      calc (s + (dotProduct h x + dotProduct h d) +
              ∑ i : Fin n, ∑ j : Fin n, M i j * (x i + d i) * (x j + d j)) +
            (s + dotProduct h x + ∑ i : Fin n, ∑ j : Fin n, M i j * x i * x j)
          = (s + s) + (dotProduct h x + dotProduct h x) + dotProduct h d +
            ((∑ i : Fin n, ∑ j : Fin n, M i j * (x i + d i) * (x j + d j)) +
             (∑ i : Fin n, ∑ j : Fin n, M i j * x i * x j)) := by ring
        _ = dotProduct h d +
            ((∑ i : Fin n, ∑ j : Fin n, M i j * (x i + d i) * (x j + d j)) +
             (∑ i : Fin n, ∑ j : Fin n, M i j * x i * x j)) := by
            rw [hss, hxx, zero_add, zero_add]
    rw [hlin]
    congr 1
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have h2 : M i j * x i * x j + M i j * x i * x j = 0 := zmod2_add_self _
    calc M i j * (x i + d i) * (x j + d j) + M i j * x i * x j
        = (M i j * x i * x j + M i j * x i * x j) +
          M i j * (d i * d j + d i * x j + d j * x i) := by ring
      _ = M i j * (d i * d j + d i * x j + d j * x i) := by rw [h2, zero_add]
  rw [hdiff]
  apply isAff_add (isAff_const _)
  apply isAff_sum
  intro i _
  apply isAff_sum
  intro j _
  apply isAff_smul
  exact isAff_add (isAff_add (isAff_const _) (isAff_smul _ (isAff_coord j)))
    (isAff_smul _ (isAff_coord i))

lemma diff3_zero_of_isQuad {n : ℕ} {q : (Fin n → ZMod 2) → ZMod 2}
    (hq : isQuad q) (d1 d2 d3 x : Fin n → ZMod 2) :
    diff d1 (diff d2 (diff d3 q)) x = 0 :=
  diff2_zero_of_isAff (isAff_diff_of_isQuad hq d3) d1 d2 x

lemma exists_dual_vector {n : ℕ} (W : Submodule (ZMod 2) (Fin n → ZMod 2))
    (v0 : Fin n → ZMod 2) (hv0 : v0 ∉ W) :
    ∃ d : Fin n → ZMod 2, dotProduct v0 d = 1 ∧ ∀ w ∈ W, dotProduct w d = 0 := by
  classical
  let L0 : Submodule (ZMod 2) (Fin n → ZMod 2) := Submodule.span (ZMod 2) {v0}
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (W ⊔ L0)
  let M : Submodule (ZMod 2) (Fin n → ZMod 2) := W ⊔ C
  have hv0M : v0 ∉ M := by
    intro hv
    rcases Submodule.mem_sup.mp hv with ⟨w, hw, c, hc, hwc⟩
    have hcWL : c ∈ W ⊔ L0 := by
      have hv0L : v0 ∈ W ⊔ L0 :=
        Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton v0))
      have hwWL : w ∈ W ⊔ L0 := Submodule.mem_sup_left hw
      have hceq : c = v0 - w := eq_sub_of_add_eq' hwc
      rw [hceq]
      exact Submodule.sub_mem _ hv0L hwWL
    have hc0 : c = 0 := by
      have hcinf : c ∈ (W ⊔ L0) ⊓ C := ⟨hcWL, hc⟩
      rw [hC.inf_eq_bot] at hcinf
      simpa using hcinf
    rw [hc0, add_zero] at hwc
    exact hv0 (hwc ▸ hw)
  have hdecomp : ∀ y : Fin n → ZMod 2, ∃ m ∈ M, ∃ a : ZMod 2, y = m + a • v0 := by
    intro y
    have hy : y ∈ (W ⊔ L0) ⊔ C := by
      rw [hC.sup_eq_top]
      trivial
    rcases Submodule.mem_sup.mp hy with ⟨u, hu, c, hc, huc⟩
    rcases Submodule.mem_sup.mp hu with ⟨w, hw, l, hl, hwl⟩
    rcases Submodule.mem_span_singleton.mp hl with ⟨a, rfl⟩
    refine ⟨w + c, Submodule.add_mem_sup hw hc, a, ?_⟩
    rw [← huc, ← hwl]
    abel
  let φ : (Fin n → ZMod 2) → ZMod 2 := fun y => if y ∈ M then 0 else 1
  have hφ_eval : ∀ m ∈ M, ∀ a : ZMod 2, φ (m + a • v0) = a := by
    intro m hm a
    rcases zmod2_eq_zero_or_one a with rfl | rfl
    · simp [φ, hm]
    · have hnot : m + v0 ∉ M := by
        intro hmem
        have hv : v0 = (m + v0) - m := by abel
        rw [hv] at hv0M
        exact hv0M (M.sub_mem hmem hm)
      rw [one_smul]
      simp [φ, hnot]
  have hφ_zero : φ 0 = 0 := by
    simp [φ, M.zero_mem]
  have hφ_add : ∀ y1 y2, φ (y1 + y2) = φ y1 + φ y2 := by
    intro y1 y2
    rcases hdecomp y1 with ⟨m1, hm1, a1, rfl⟩
    rcases hdecomp y2 with ⟨m2, hm2, a2, rfl⟩
    have hsum : (m1 + a1 • v0) + (m2 + a2 • v0) = (m1 + m2) + (a1 + a2) • v0 := by
      rw [add_smul]
      abel
    rw [hsum, hφ_eval (m1 + m2) (M.add_mem hm1 hm2), hφ_eval m1 hm1, hφ_eval m2 hm2]
  have hφ_smul : ∀ (c : ZMod 2) (y : Fin n → ZMod 2), φ (c • y) = c * φ y := by
    intro c y
    rcases zmod2_eq_zero_or_one c with rfl | rfl
    · simp [hφ_zero]
    · simp
  have hφ_sum : ∀ (s : Finset (Fin n)) (f : Fin n → (Fin n → ZMod 2)),
      φ (∑ j ∈ s, f j) = ∑ j ∈ s, φ (f j) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp [hφ_zero]
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hφ_add, ih]
  let d : Fin n → ZMod 2 := fun j => φ (Pi.single j 1)
  have hdot : ∀ y : Fin n → ZMod 2, dotProduct y d = φ y := by
    intro y
    have hy : y = ∑ j : Fin n, y j • Pi.single j (1 : ZMod 2) := by
      ext k
      rw [Finset.sum_apply]
      simp [Pi.single_apply]
    conv_rhs => rw [hy]
    rw [hφ_sum]
    unfold dotProduct
    apply Finset.sum_congr rfl
    intro j _
    rw [hφ_smul]
  refine ⟨d, ?_, ?_⟩
  · rw [hdot v0]
    simp [φ, hv0M]
  · intro w hw
    rw [hdot w]
    have hwM : w ∈ M := Submodule.mem_sup_left hw
    simp [φ, hwM]

lemma mem_span_image_finset {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ι → (Fin n → ZMod 2)) (s : Finset ι) {x : Fin n → ZMod 2}
    (hx : x ∈ Submodule.span (ZMod 2) (B '' (s : Set ι))) :
    ∃ c : ι → ZMod 2, (∀ p, p ∉ s → c p = 0) ∧ x = ∑ p, c p • B p := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with ⟨p0, hp0, rfl⟩
    refine ⟨Pi.single p0 1, ?_, ?_⟩
    · intro p hp
      have hne : p ≠ p0 := fun h => hp (h ▸ hp0)
      simp [hne]
    · symm
      rw [Finset.sum_eq_single p0]
      · simp
      · intro p _ hne
        simp [hne]
      · intro h
        exact absurd (Finset.mem_univ p0) h
  · refine ⟨0, fun _ _ => rfl, by simp⟩
  · rintro y1 y2 _ _ ⟨c1, hc1, rfl⟩ ⟨c2, hc2, rfl⟩
    refine ⟨c1 + c2, fun p hp => by simp [hc1 p hp, hc2 p hp], ?_⟩
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    rw [Pi.add_apply, add_smul]
  · rintro a y _ ⟨c, hc, rfl⟩
    refine ⟨fun p => a * c p, fun p hp => by simp [hc p hp], ?_⟩
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro p _
    dsimp only
    rw [smul_smul]

lemma mem_span_range {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ι → (Fin n → ZMod 2)) {x : Fin n → ZMod 2}
    (hx : x ∈ Submodule.span (ZMod 2) (Set.range B)) :
    ∃ c : ι → ZMod 2, x = ∑ p, c p • B p := by
  have hset : Set.range B = B '' ((Finset.univ : Finset ι) : Set ι) := by
    simp
  rw [hset] at hx
  rcases mem_span_image_finset B Finset.univ hx with ⟨c, _, hEq⟩
  exact ⟨c, hEq⟩

lemma sum_smul_mem_span_range {n : ℕ} {ι : Type*} [Fintype ι]
    (B : ι → (Fin n → ZMod 2)) (c : ι → ZMod 2) :
    (∑ p : ι, c p • B p) ∈ Submodule.span (ZMod 2) (Set.range B) := by
  apply Submodule.sum_mem
  intro p _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)

lemma solve_canonical {n m : ℕ}
    (B : Fin m × Bool → (Fin n → ZMod 2))
    (hB_indep : ∀ c : Fin m × Bool → ZMod 2, (∑ p, c p • B p) = 0 → ∀ p, c p = 0)
    (g0 gD : Fin n → ZMod 2)
    (hg0 : g0 ∉ Submodule.span (ZMod 2) (Set.range B))
    (β : Fin m × Bool → ZMod 2)
    (hgD : gD = ∑ p, β p • B p)
    (c0 cD : ZMod 2)
    (b : Fin m × Bool → ZMod 2)
    (u d : Fin m → ZMod 2)
    (hQ : isQuad (fun x =>
      ((c0 + dotProduct g0 x) + ∑ i : Fin m, u i *
        ((b (i, false) + dotProduct (B (i, false)) x) *
         (b (i, true) + dotProduct (B (i, true)) x))) *
      ((cD + dotProduct gD x) + ∑ i : Fin m, d i *
        ((b (i, false) + dotProduct (B (i, false)) x) *
         (b (i, true) + dotProduct (B (i, true)) x))))) :
    ∃ (X Y Z : (Fin n → ZMod 2) → ZMod 2) (w : Fin m → ZMod 2),
      isAff X ∧ isAff Y ∧ isAff Z ∧
      ∀ x,
        ((c0 + dotProduct g0 x) + ∑ i : Fin m, u i *
          ((b (i, false) + dotProduct (B (i, false)) x) *
           (b (i, true) + dotProduct (B (i, true)) x))) *
        ((cD + dotProduct gD x) + ∑ i : Fin m, d i *
          ((b (i, false) + dotProduct (B (i, false)) x) *
           (b (i, true) + dotProduct (B (i, true)) x))) =
        X x * Y x + Z x + ∑ i : Fin m, w i *
          ((b (i, false) + dotProduct (B (i, false)) x) *
           (b (i, true) + dotProduct (B (i, true)) x)) := by
  classical
  let W_old : Submodule (ZMod 2) (Fin n → ZMod 2) := Submodule.span (ZMod 2) (Set.range B)
  let ℓ0 : (Fin n → ZMod 2) → ZMod 2 := fun x => c0 + dotProduct g0 x
  let ℓD : (Fin n → ZMod 2) → ZMod 2 := fun x => cD + dotProduct gD x
  let L : Fin m × Bool → (Fin n → ZMod 2) → ZMod 2 := fun p x => b p + dotProduct (B p) x
  let P : Fin m → (Fin n → ZMod 2) → ZMod 2 := fun i x => L (i, false) x * L (i, true) x
  let U : (Fin n → ZMod 2) → ZMod 2 := fun x => ℓ0 x + ∑ i : Fin m, u i * P i x
  let D : (Fin n → ZMod 2) → ZMod 2 := fun x => ℓD x + ∑ i : Fin m, d i * P i x
  obtain ⟨e0, he0_g0, he0_W⟩ := exists_dual_vector W_old g0 hg0
  have he0_B : ∀ p, dotProduct (B p) e0 = 0 := fun p =>
    he0_W (B p) (Submodule.subset_span ⟨p, rfl⟩)
  have he0_gD : dotProduct gD e0 = 0 := by
    rw [hgD]
    exact he0_W _ (sum_smul_mem_span_range B β)
  have hex_e : ∀ q : Fin m × Bool, ∃ eq : Fin n → ZMod 2,
      dotProduct (B q) eq = 1 ∧ dotProduct g0 eq = 0 ∧
      ∀ p, p ≠ q → dotProduct (B p) eq = 0 := by
    intro q
    let Wq : Submodule (ZMod 2) (Fin n → ZMod 2) :=
      Submodule.span (ZMod 2) {g0} ⊔
      Submodule.span (ZMod 2) (B '' ((Finset.univ.erase q : Finset (Fin m × Bool)) : Set _))
    have hBq : B q ∉ Wq := by
      intro hmem
      rcases Submodule.mem_sup.mp hmem with ⟨x1, hx1, x2, hx2, hsum⟩
      rcases Submodule.mem_span_singleton.mp hx1 with ⟨a, rfl⟩
      rcases mem_span_image_finset B (Finset.univ.erase q) hx2 with ⟨c, hc0, rfl⟩
      have hcq : c q = 0 := hc0 q (by simp)
      rcases zmod2_eq_zero_or_one a with rfl | rfl
      · rw [zero_smul, zero_add] at hsum
        let c' : Fin m × Bool → ZMod 2 := fun p => c p + if p = q then 1 else 0
        have hzero : (∑ p : Fin m × Bool, c' p • B p) = 0 := by
          have h1 : (∑ p : Fin m × Bool, c' p • B p) =
              (∑ p : Fin m × Bool, c p • B p) + B q := by
            simp only [c', add_smul, Finset.sum_add_distrib]
            congr 1
            rw [Finset.sum_eq_single q]
            · simp
            · intro p _ hne; simp [hne]
            · intro h; exact absurd (Finset.mem_univ q) h
          rw [h1, hsum]
          ext k
          exact zmod2_add_self (B q k)
        have hcq' := hB_indep c' hzero q
        simp [c', hcq] at hcq'
      · rw [one_smul] at hsum
        have hg0_eq : g0 = B q + ∑ p : Fin m × Bool, c p • B p := by
          ext k
          have hk := congrFun hsum k
          simp only [Pi.add_apply] at hk ⊢
          calc g0 k = (g0 k + (∑ p, c p • B p) k) + (∑ p, c p • B p) k :=
                (zmod2_add_cancel_right _ _).symm
            _ = B q k + (∑ p, c p • B p) k := by rw [hk]
        have hg0_mem : g0 ∈ W_old := by
          rw [hg0_eq]
          exact W_old.add_mem (Submodule.subset_span ⟨q, rfl⟩) (sum_smul_mem_span_range B c)
        exact hg0 hg0_mem
    obtain ⟨eq, heq1, heqW⟩ := exists_dual_vector Wq (B q) hBq
    refine ⟨eq, heq1, ?_, ?_⟩
    · exact heqW g0 (Submodule.mem_sup_left (Submodule.subset_span (Set.mem_singleton g0)))
    · intro p hpq
      have hp_mem : B p ∈ B '' ((Finset.univ.erase q : Finset (Fin m × Bool)) : Set _) :=
        ⟨p, by simp [hpq], rfl⟩
      exact heqW (B p) (Submodule.mem_sup_right (Submodule.subset_span hp_mem))
  let e : Fin m × Bool → (Fin n → ZMod 2) := fun q => Classical.choose (hex_e q)
  have he_self : ∀ q, dotProduct (B q) (e q) = 1 := fun q => (Classical.choose_spec (hex_e q)).1
  have he_g0 : ∀ q, dotProduct g0 (e q) = 0 := fun q => (Classical.choose_spec (hex_e q)).2.1
  have he_ne : ∀ q p, p ≠ q → dotProduct (B p) (e q) = 0 :=
    fun q => (Classical.choose_spec (hex_e q)).2.2
  have he_gD : ∀ q, dotProduct gD (e q) = β q := by
    intro q
    rw [hgD, sum_dotProduct]
    rw [Finset.sum_eq_single q]
    · rw [smul_dotProduct, smul_eq_mul, he_self q, mul_one]
    · intro p _ hpq
      rw [smul_dotProduct, smul_eq_mul, he_ne q p hpq, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ q) h
  have hL_shift : ∀ p x y, L p (x + y) = L p x + dotProduct (B p) y := by
    intro p x y
    simp only [L, dotProduct_add]
    ring
  have hℓD_shift : ∀ x y, ℓD (x + y) = ℓD x + dotProduct gD y := by
    intro x y
    simp only [ℓD, dotProduct_add]
    ring
  have hP_inv_of_dot : ∀ i y,
      dotProduct (B (i, false)) y = 0 → dotProduct (B (i, true)) y = 0 →
      ∀ x, P i (x + y) = P i x := by
    intro i y h0 h1 x
    simp only [P, hL_shift, h0, h1, add_zero]
  have hdiff_e0 : diff e0 (fun x => U x * D x) = D := by
    funext x
    have hP0 : ∀ i, P i (x + e0) = P i x :=
      fun i => hP_inv_of_dot i e0 (he0_B _) (he0_B _) x
    have hU0 : U (x + e0) = U x + 1 := by
      simp only [U, ℓ0, dotProduct_add, he0_g0, hP0]
      ring
    have hD0 : D (x + e0) = D x := by
      simp only [D, hℓD_shift, he0_gD, add_zero, hP0]
    unfold diff
    dsimp only
    rw [hU0, hD0]
    have h2 : U x * D x + U x * D x = 0 := zmod2_add_self _
    calc (U x + 1) * D x + U x * D x = (U x * D x + U x * D x) + D x := by ring
      _ = D x := by rw [h2, zero_add]
  have hAffD : isAff D := by
    rw [← hdiff_e0]
    exact isAff_diff_of_isQuad hQ e0
  have hdiff2_P : ∀ i r x,
      diff (e (i, false)) (diff (e (i, true)) (P r)) x = if r = i then 1 else 0 := by
    intro i r x
    by_cases hri : r = i
    · subst hri
      have h1 : diff (e (r, true)) (P r) = L (r, false) := by
        funext y
        unfold diff
        have hfalse : L (r, false) (y + e (r, true)) = L (r, false) y := by
          rw [hL_shift, he_ne (r, true) (r, false) (by simp), add_zero]
        have htrue : L (r, true) (y + e (r, true)) = L (r, true) y + 1 := by
          rw [hL_shift, he_self]
        simp only [P, hfalse, htrue]
        have h2 : L (r, false) y * L (r, true) y + L (r, false) y * L (r, true) y = 0 :=
          zmod2_add_self _
        calc L (r, false) y * (L (r, true) y + 1) + L (r, false) y * L (r, true) y
            = (L (r, false) y * L (r, true) y + L (r, false) y * L (r, true) y) +
              L (r, false) y := by ring
          _ = L (r, false) y := by rw [h2, zero_add]
      rw [h1]
      simp only [ite_true]
      unfold diff
      rw [hL_shift, he_self]
      have h2 : L (r, false) x + L (r, false) x = 0 := zmod2_add_self _
      calc L (r, false) x + 1 + L (r, false) x
          = (L (r, false) x + L (r, false) x) + 1 := by ring
        _ = 1 := by rw [h2, zero_add]
    · simp only [hri, ite_false]
      have hne1 : (r, false) ≠ (i, true) := by simp [hri]
      have hne2 : (r, true) ≠ (i, true) := by simp [hri]
      have h1 : diff (e (i, true)) (P r) = fun _ => 0 := by
        funext y
        unfold diff
        rw [hP_inv_of_dot r (e (i, true)) (he_ne _ _ hne1) (he_ne _ _ hne2) y]
        exact zmod2_add_self _
      rw [h1]
      exact diff_const _ 0 x
  have hd_zero : ∀ i : Fin m, d i = 0 := by
    intro i
    have h0 := diff2_zero_of_isAff hAffD (e (i, false)) (e (i, true)) 0
    have hD_diff1 : diff (e (i, true)) D =
        fun y => diff (e (i, true)) ℓD y + ∑ r : Fin m, d r * diff (e (i, true)) (P r) y := by
      funext y
      change diff (e (i, true)) (fun z => ℓD z + ∑ r : Fin m, d r * P r z) y = _
      rw [diff_add, diff_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      exact diff_smul _ _ _ _
    have hD_diff2 : diff (e (i, false)) (diff (e (i, true)) D) 0 =
        diff (e (i, false)) (diff (e (i, true)) ℓD) 0 +
        ∑ r : Fin m, d r * diff (e (i, false)) (diff (e (i, true)) (P r)) 0 := by
      rw [hD_diff1, diff_add, diff_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      exact diff_smul _ _ _ _
    rw [hD_diff2, diff2_zero_of_isAff (isAff_lin cD gD), zero_add] at h0
    simp only [hdiff2_P] at h0
    rw [Finset.sum_eq_single i] at h0
    · simpa using h0
    · intro r _ hri
      simp [hri]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hD_eq : ∀ x, D x = ℓD x := by
    intro x
    simp [D, hd_zero]
  let K' : (Fin n → ZMod 2) → ZMod 2 := fun x => ∑ r : Fin m, u r * (P r x * ℓD x)
  have hUD_eq : ∀ x, U x * D x = ℓ0 x * ℓD x + K' x := by
    intro x
    rw [hD_eq x]
    simp only [U, K', add_mul, Finset.sum_mul, mul_assoc]
  have hK'_eq : K' = fun x => U x * D x + ℓ0 x * ℓD x := by
    funext x
    rw [hUD_eq x, add_comm (ℓ0 x * ℓD x) (K' x)]
    exact (zmod2_add_cancel_right _ _).symm
  have hQuadK' : isQuad K' := by
    rw [hK'_eq]
    exact isQuad_add hQ (isQuad_mul_isAff (isAff_lin c0 g0) (isAff_lin cD gD))
  have hstepB : ∀ (i j : Fin m), i ≠ j → ∀ b0 : Bool, u i * β (j, b0) = 0 := by
    intro i j hij b0
    have h0 := diff3_zero_of_isQuad hQuadK' (e (i, false)) (e (i, true)) (e (j, b0)) 0
    have hK1 : diff (e (j, b0)) K' =
        fun y => ∑ r : Fin m, u r * diff (e (j, b0)) (fun z => P r z * ℓD z) y := by
      funext y
      change diff (e (j, b0)) (fun z => ∑ r : Fin m, u r * (P r z * ℓD z)) y = _
      rw [diff_sum]
      apply Finset.sum_congr rfl
      intro r _
      exact diff_smul _ _ _ _
    have hK2 : diff (e (i, true)) (diff (e (j, b0)) K') =
        fun y => ∑ r : Fin m, u r *
          diff (e (i, true)) (diff (e (j, b0)) (fun z => P r z * ℓD z)) y := by
      funext y
      rw [hK1, diff_sum]
      apply Finset.sum_congr rfl
      intro r _
      exact diff_smul _ _ _ _
    have hK3 : diff (e (i, false)) (diff (e (i, true)) (diff (e (j, b0)) K')) 0 =
        ∑ r : Fin m, u r *
          diff (e (i, false)) (diff (e (i, true)) (diff (e (j, b0)) (fun z => P r z * ℓD z))) 0 := by
      rw [hK2, diff_sum]
      apply Finset.sum_congr rfl
      intro r _
      exact diff_smul _ _ _ _
    rw [hK3] at h0
    have hterm : ∀ r : Fin m,
        diff (e (i, false)) (diff (e (i, true)) (diff (e (j, b0)) (fun z => P r z * ℓD z))) 0 =
        if r = i then β (j, b0) else 0 := by
      intro r
      by_cases hrj : r = j
      · subst hrj
        simp only [hij.symm, ite_false]
        have hdj : diff (e (r, b0)) (fun z => P r z * ℓD z) =
            fun y => P r (y + e (r, b0)) * ℓD (y + e (r, b0)) + P r y * ℓD y := by
          funext y; rfl
        rw [hdj]
        have hstep1 : diff (e (i, true))
            (fun y => P r (y + e (r, b0)) * ℓD (y + e (r, b0)) + P r y * ℓD y) =
            fun y => diff (e (i, true)) (fun z => P r (z + e (r, b0)) * ℓD (z + e (r, b0))) y +
              diff (e (i, true)) (fun z => P r z * ℓD z) y := by
          funext y
          exact diff_add _ _ _ y
        rw [hstep1, diff_add]
        have hinv_f : ∀ y, P r (y + e (i, false)) = P r y :=
          hP_inv_of_dot r (e (i, false))
            (he_ne _ _ (by simp [hij.symm])) (he_ne _ _ (by simp [hij.symm]))
        have hinv_t : ∀ y, P r (y + e (i, true)) = P r y :=
          hP_inv_of_dot r (e (i, true))
            (he_ne _ _ (by simp [hij.symm])) (he_ne _ _ (by simp [hij.symm]))
        have hinv_sf : ∀ y, P r (y + e (i, false) + e (r, b0)) = P r (y + e (r, b0)) := by
          intro y
          have : y + e (i, false) + e (r, b0) = (y + e (r, b0)) + e (i, false) := by abel
          rw [this, hinv_f]
        have hinv_st : ∀ y, P r (y + e (i, true) + e (r, b0)) = P r (y + e (r, b0)) := by
          intro y
          have : y + e (i, true) + e (r, b0) = (y + e (r, b0)) + e (i, true) := by abel
          rw [this, hinv_t]
        rw [diff2_mul_left_inv _ _ _ _ hinv_sf hinv_st,
          diff2_mul_left_inv _ _ _ _ hinv_f hinv_t,
          diff2_zero_of_isAff (isAff_shift _ (isAff_lin cD gD)),
          diff2_zero_of_isAff (isAff_lin cD gD)]
        simp
      · have hne1 : (r, false) ≠ (j, b0) := by simp [hrj]
        have hne2 : (r, true) ≠ (j, b0) := by simp [hrj]
        have hdj : diff (e (j, b0)) (fun z => P r z * ℓD z) =
            fun y => β (j, b0) * P r y := by
          funext y
          unfold diff
          dsimp only
          rw [hP_inv_of_dot r (e (j, b0)) (he_ne _ _ hne1) (he_ne _ _ hne2) y,
            hℓD_shift, he_gD]
          have h2 : P r y * ℓD y + P r y * ℓD y = 0 := zmod2_add_self _
          calc P r y * (ℓD y + β (j, b0)) + P r y * ℓD y
              = (P r y * ℓD y + P r y * ℓD y) + β (j, b0) * P r y := by ring
            _ = β (j, b0) * P r y := by rw [h2, zero_add]
        rw [hdj]
        have hstep1 : diff (e (i, true)) (fun y => β (j, b0) * P r y) =
            fun y => β (j, b0) * diff (e (i, true)) (P r) y := by
          funext y
          exact diff_smul _ _ _ y
        rw [hstep1, diff_smul, hdiff2_P]
        by_cases hri : r = i
        · simp [hri]
        · simp [hri]
    simp only [hterm] at h0
    rw [Finset.sum_eq_single i] at h0
    · simpa using h0
    · intro r _ hri
      simp [hri]
    · intro h
      exact absurd (Finset.mem_univ i) h
  by_cases hβall : ∀ p : Fin m × Bool, β p = 0
  · have hgD0 : gD = 0 := by
      rw [hgD]
      simp [hβall]
    have hℓDc : ∀ x, ℓD x = cD := by
      intro x
      simp [ℓD, hgD0]
    refine ⟨fun _ => 0, fun _ => 0, fun x => cD * ℓ0 x, fun i => cD * u i,
      isAff_const 0, isAff_const 0, isAff_smul cD (isAff_lin c0 g0), fun x => ?_⟩
    change U x * D x = _
    rw [hD_eq x, hℓDc x]
    simp only [U, zero_mul, zero_add, add_mul, Finset.sum_mul]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro i _
      ring
  · rw [not_forall] at hβall
    rcases hβall with ⟨⟨i0, b0⟩, hβ0⟩
    have hβ0_eq : β (i0, b0) = 1 := by
      rcases zmod2_eq_zero_or_one (β (i0, b0)) with h | h
      · exact absurd h hβ0
      · exact h
    have hu_ne : ∀ i, i ≠ i0 → u i = 0 := by
      intro i hi
      have := hstepB i i0 hi b0
      rwa [hβ0_eq, mul_one] at this
    by_cases hui0 : u i0 = 0
    · have hu_all : ∀ i, u i = 0 := by
        intro i
        by_cases h : i = i0
        · subst h; exact hui0
        · exact hu_ne i h
      refine ⟨ℓ0, ℓD, fun _ => 0, fun _ => 0,
        isAff_lin c0 g0, isAff_lin cD gD, isAff_const 0, fun x => ?_⟩
      change U x * D x = _
      rw [hD_eq x]
      simp [U, hu_all]
    · have hui0_eq : u i0 = 1 := by
        rcases zmod2_eq_zero_or_one (u i0) with h | h
        · exact absurd h hui0
        · exact h
      have hβ_ne : ∀ j, j ≠ i0 → ∀ b1 : Bool, β (j, b1) = 0 := by
        intro j hj b1
        have := hstepB i0 j hj.symm b1
        rwa [hui0_eq, one_mul] at this
      have hgD_pair : gD = β (i0, false) • B (i0, false) + β (i0, true) • B (i0, true) := by
        rw [hgD, Fintype.sum_prod_type]
        rw [Finset.sum_eq_single i0]
        · simp [add_comm]
        · intro j _ hji
          simp [hβ_ne j hji]
        · intro h
          exact absurd (Finset.mem_univ i0) h
      let β0 := β (i0, false)
      let β1 := β (i0, true)
      let γ := cD + β0 * b (i0, false) + β1 * b (i0, true)
      have hℓD_eq : ∀ x, ℓD x = γ + β0 * L (i0, false) x + β1 * L (i0, true) x := by
        intro x
        simp only [ℓD, hgD_pair, add_dotProduct, smul_dotProduct, smul_eq_mul, L, γ, β0, β1]
        have h1 : β (i0, false) * b (i0, false) + β (i0, false) * b (i0, false) = 0 :=
          zmod2_add_self _
        have h2 : β (i0, true) * b (i0, true) + β (i0, true) * b (i0, true) = 0 :=
          zmod2_add_self _
        calc cD + (β (i0, false) * dotProduct (B (i0, false)) x +
              β (i0, true) * dotProduct (B (i0, true)) x)
            = cD + (β (i0, false) * dotProduct (B (i0, false)) x +
              β (i0, true) * dotProduct (B (i0, true)) x) +
              (β (i0, false) * b (i0, false) + β (i0, false) * b (i0, false)) +
              (β (i0, true) * b (i0, true) + β (i0, true) * b (i0, true)) := by
              rw [h1, h2, add_zero, add_zero]
          _ = cD + β (i0, false) * b (i0, false) + β (i0, true) * b (i0, true) +
              β (i0, false) * (b (i0, false) + dotProduct (B (i0, false)) x) +
              β (i0, true) * (b (i0, true) + dotProduct (B (i0, true)) x) := by ring
      have hP_mul_ℓD : ∀ x, P i0 x * ℓD x = (γ + β0 + β1) * P i0 x := by
        intro x
        rw [hℓD_eq x]
        simp only [P]
        have hf2 : L (i0, false) x * L (i0, false) x = L (i0, false) x := zmod2_mul_self _
        have ht2 : L (i0, true) x * L (i0, true) x = L (i0, true) x := zmod2_mul_self _
        calc L (i0, false) x * L (i0, true) x *
              (γ + β0 * L (i0, false) x + β1 * L (i0, true) x)
            = γ * (L (i0, false) x * L (i0, true) x) +
              β0 * (L (i0, false) x * L (i0, false) x) * L (i0, true) x +
              β1 * L (i0, false) x * (L (i0, true) x * L (i0, true) x) := by ring
          _ = γ * (L (i0, false) x * L (i0, true) x) +
              β0 * L (i0, false) x * L (i0, true) x +
              β1 * L (i0, false) x * L (i0, true) x := by rw [hf2, ht2]
          _ = (γ + β0 + β1) * (L (i0, false) x * L (i0, true) x) := by ring
      have hU_eq : ∀ x, U x = ℓ0 x + P i0 x := by
        intro x
        simp only [U]
        congr 1
        rw [Finset.sum_eq_single i0]
        · rw [hui0_eq, one_mul]
        · intro i _ hi
          rw [hu_ne i hi, zero_mul]
        · intro h
          exact absurd (Finset.mem_univ i0) h
      refine ⟨ℓ0, ℓD, fun _ => 0, fun i => if i = i0 then γ + β0 + β1 else 0,
        isAff_lin c0 g0, isAff_lin cD gD, isAff_const 0, fun x => ?_⟩
      change U x * D x = _
      dsimp only
      rw [hU_eq x, hD_eq x, add_mul, hP_mul_ℓD x, add_zero]
      congr 1
      rw [Finset.sum_eq_single i0]
      · simp [P, L]
      · intro i _ hi
        simp [hi]
      · intro h
        exact absurd (Finset.mem_univ i0) h

lemma indep_and_fresh_of_span_le {n m : ℕ}
    (A : Option (Fin m) × Bool → (Fin n → ZMod 2))
    (g : Fin n → ZMod 2)
    (hrank : 2 * m + 1 ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range A)))
    (hle : Submodule.span (ZMod 2) (Set.range A) ≤
      Submodule.span (ZMod 2) (Set.range (fun p : Fin m × Bool => A (some p.1, p.2))) ⊔
      Submodule.span (ZMod 2) {g}) :
    g ∉ Submodule.span (ZMod 2) (Set.range (fun p : Fin m × Bool => A (some p.1, p.2))) ∧
    ∀ c : Fin m × Bool → ZMod 2,
      (∑ p : Fin m × Bool, c p • A (some p.1, p.2)) = 0 → ∀ p, c p = 0 := by
  classical
  let B : Fin m × Bool → (Fin n → ZMod 2) := fun p => A (some p.1, p.2)
  let W_old : Submodule (ZMod 2) (Fin n → ZMod 2) := Submodule.span (ZMod 2) (Set.range B)
  let Φ : (Fin m × Bool → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
    { toFun := fun c => ∑ p : Fin m × Bool, c p • B p
      map_add' := fun c1 c2 => by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro p _
        rw [Pi.add_apply, add_smul]
      map_smul' := fun a c => by
        simp only [RingHom.id_apply, Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro p _
        rw [Pi.smul_apply, smul_eq_mul, smul_smul] }
  have hrange : LinearMap.range Φ = W_old := by
    apply le_antisymm
    · rintro _ ⟨c, rfl⟩
      exact sum_smul_mem_span_range B c
    · rw [Submodule.span_le]
      rintro _ ⟨p0, rfl⟩
      refine ⟨Pi.single p0 1, ?_⟩
      dsimp only [Φ, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Finset.sum_eq_single p0]
      · simp
      · intro p _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ p0) h
  have hcard : Module.finrank (ZMod 2) (Fin m × Bool → ZMod 2) = 2 * m := by
    rw [Module.finrank_pi, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, mul_comm]
  have hW_le : Module.finrank (ZMod 2) W_old ≤ 2 * m := by
    rw [← hrange, ← hcard]
    exact LinearMap.finrank_range_le Φ
  have hg : g ∉ W_old := by
    intro hgmem
    have hsup : W_old ⊔ Submodule.span (ZMod 2) {g} = W_old :=
      sup_eq_left.mpr (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hgmem))
    rw [hsup] at hle
    have hle_rank := Submodule.finrank_mono hle
    omega
  have hW_eq : Module.finrank (ZMod 2) W_old = 2 * m := by
    have hsup_rank : Module.finrank (ZMod 2) ↥(W_old ⊔ Submodule.span (ZMod 2) {g}) =
        Module.finrank (ZMod 2) W_old + 1 :=
      Submodule.finrank_sup_span_singleton hg
    have hle_rank : Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) (Set.range A)) ≤
        Module.finrank (ZMod 2) ↥(W_old ⊔ Submodule.span (ZMod 2) {g}) :=
      Submodule.finrank_mono hle
    omega
  let Φ' : (Fin m × Bool → ZMod 2) →ₗ[ZMod 2] W_old :=
    Φ.codRestrict W_old (fun c => sum_smul_mem_span_range B c)
  have hsurj : Function.Surjective Φ' := by
    rintro ⟨y, hy⟩
    rw [← hrange] at hy
    rcases hy with ⟨c, rfl⟩
    exact ⟨c, rfl⟩
  have hfin_eq : Module.finrank (ZMod 2) (Fin m × Bool → ZMod 2) =
      Module.finrank (ZMod 2) W_old := by
    rw [hcard, hW_eq]
  have hinj : Function.Injective Φ' :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin_eq).mpr hsurj
  refine ⟨hg, fun c hc p => ?_⟩
  have hc' : Φ' c = Φ' 0 := by
    apply Subtype.ext
    simpa [Φ', Φ] using hc
  have hcz : c = 0 := hinj hc'
  rw [hcz]
  rfl

lemma solve_dep {n m : ℕ}
    (A : Option (Fin m) × Bool → (Fin n → ZMod 2))
    (a : Option (Fin m) × Bool → ZMod 2)
    (k1 k2 : Option (Fin m) × Bool)
    (u1 u2 : Fin m → ZMod 2)
    (hrank : 2 * m + 1 ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range A)))
    (hspan_eq : Submodule.span (ZMod 2) (Set.range A) =
      Submodule.span (ZMod 2) (Set.range (fun p : Fin m × Bool => A (some p.1, p.2))) ⊔
      Submodule.span (ZMod 2) {A k1} ⊔ Submodule.span (ZMod 2) {A k2})
    (hdep : A k2 ∈ Submodule.span (ZMod 2) (Set.range (fun p : Fin m × Bool => A (some p.1, p.2))) ⊔
      Submodule.span (ZMod 2) {A k1})
    (hQ : isQuad (fun x =>
      ((a k1 + dotProduct (A k1) x) + ∑ i : Fin m, u1 i *
        ((a (some i, false) + dotProduct (A (some i, false)) x) *
         (a (some i, true) + dotProduct (A (some i, true)) x))) *
      ((a k2 + dotProduct (A k2) x) + ∑ i : Fin m, u2 i *
        ((a (some i, false) + dotProduct (A (some i, false)) x) *
         (a (some i, true) + dotProduct (A (some i, true)) x))))) :
    ∃ (X Y Z : (Fin n → ZMod 2) → ZMod 2) (w : Fin m → ZMod 2),
      isAff X ∧ isAff Y ∧ isAff Z ∧
      ∀ x,
        ((a k1 + dotProduct (A k1) x) + ∑ i : Fin m, u1 i *
          ((a (some i, false) + dotProduct (A (some i, false)) x) *
           (a (some i, true) + dotProduct (A (some i, true)) x))) *
        ((a k2 + dotProduct (A k2) x) + ∑ i : Fin m, u2 i *
          ((a (some i, false) + dotProduct (A (some i, false)) x) *
           (a (some i, true) + dotProduct (A (some i, true)) x))) =
        X x * Y x + Z x + ∑ i : Fin m, w i *
          ((a (some i, false) + dotProduct (A (some i, false)) x) *
           (a (some i, true) + dotProduct (A (some i, true)) x)) := by
  classical
  let B : Fin m × Bool → (Fin n → ZMod 2) := fun p => A (some p.1, p.2)
  let W_old : Submodule (ZMod 2) (Fin n → ZMod 2) := Submodule.span (ZMod 2) (Set.range B)
  have hle : Submodule.span (ZMod 2) (Set.range A) ≤ W_old ⊔ Submodule.span (ZMod 2) {A k1} := by
    rw [hspan_eq]
    exact sup_le le_rfl (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hdep))
  obtain ⟨hk1_fresh, hB_indep⟩ := indep_and_fresh_of_span_le A (A k1) hrank hle
  rcases Submodule.mem_sup.mp hdep with ⟨wvec, hwvec, lvec, hlvec, hwl⟩
  rcases Submodule.mem_span_singleton.mp hlvec with ⟨c, rfl⟩
  rcases mem_span_range B hwvec with ⟨β, rfl⟩
  rcases zmod2_eq_zero_or_one c with rfl | rfl
  · rw [zero_smul, add_zero] at hwl
    exact solve_canonical B hB_indep (A k1) (A k2) hk1_fresh β hwl.symm
      (a k1) (a k2) (fun p => a (some p.1, p.2)) u1 u2 hQ
  · rw [one_smul] at hwl
    have hsum_vec : A k1 + A k2 = ∑ p : Fin m × Bool, β p • B p := by
      ext j
      have hj := congrFun hwl j
      simp only [Pi.add_apply] at hj ⊢
      calc A k1 j + A k2 j = A k1 j + ((∑ p, β p • B p) j + A k1 j) := by rw [← hj]
        _ = (∑ p, β p • B p) j + (A k1 j + A k1 j) := by ring
        _ = (∑ p, β p • B p) j := by rw [zmod2_add_self, add_zero]
    let P : Fin m → (Fin n → ZMod 2) → ZMod 2 := fun i x =>
      (a (some i, false) + dotProduct (A (some i, false)) x) *
      (a (some i, true) + dotProduct (A (some i, true)) x)
    let U1 : (Fin n → ZMod 2) → ZMod 2 := fun x =>
      (a k1 + dotProduct (A k1) x) + ∑ i : Fin m, u1 i * P i x
    let U2 : (Fin n → ZMod 2) → ZMod 2 := fun x =>
      (a k2 + dotProduct (A k2) x) + ∑ i : Fin m, u2 i * P i x
    let D : (Fin n → ZMod 2) → ZMod 2 := fun x =>
      ((a k1 + a k2) + dotProduct (A k1 + A k2) x) + ∑ i : Fin m, (u1 i + u2 i) * P i x
    have hD_eq : ∀ x, D x = U1 x + U2 x := by
      intro x
      simp only [D, U1, U2, add_dotProduct]
      have hs : (∑ i : Fin m, (u1 i + u2 i) * P i x) =
          (∑ i : Fin m, u1 i * P i x) + (∑ i : Fin m, u2 i * P i x) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hs]
      ring
    have hU1D_eq : ∀ x, U1 x * D x = U1 x * U2 x + U1 x := by
      intro x
      rw [hD_eq x, mul_add, zmod2_mul_self, add_comm]
    have hQuadU1 : isQuad U1 := by
      apply isQuad_add (isQuad_of_isAff (isAff_lin (a k1) (A k1)))
      apply isQuad_sum
      intro i _
      apply isQuad_smul
      exact isQuad_mul_isAff (isAff_lin _ _) (isAff_lin _ _)
    have hQuadU1D : isQuad (fun x => U1 x * D x) := by
      have hfn : (fun x => U1 x * D x) = fun x => U1 x * U2 x + U1 x := funext hU1D_eq
      rw [hfn]
      exact isQuad_add hQ hQuadU1
    obtain ⟨X, Y, Z0, w0, hX, hY, hZ0, hEq⟩ :=
      solve_canonical B hB_indep (A k1) (A k1 + A k2) hk1_fresh β hsum_vec
        (a k1) (a k1 + a k2) (fun p => a (some p.1, p.2)) u1 (fun i => u1 i + u2 i) hQuadU1D
    refine ⟨X, Y, fun x => Z0 x + (a k1 + dotProduct (A k1) x), fun i => w0 i + u1 i,
      hX, hY, isAff_add hZ0 (isAff_lin (a k1) (A k1)), fun x => ?_⟩
    change U1 x * U2 x = _
    have h1 : U1 x * U2 x = U1 x * D x + U1 x := by
      rw [hU1D_eq x]
      exact (zmod2_add_cancel_right _ _).symm
    rw [h1, hEq x]
    dsimp only
    simp only [U1]
    have hs : (∑ i : Fin m, (w0 i + u1 i) * P i x) =
        (∑ i : Fin m, w0 i * P i x) + (∑ i : Fin m, u1 i * P i x) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hs]
    ring

end PEqualNP.Outside.L_lib_891_aux

theorem PEqualNP.Outside.L_lib_891 : (∀ n m : ℕ,
  let F := ZMod 2
  let V := Fin n → F
  let I := Option (Fin m) × Bool
  let quad := fun (q : V → F) => ∃ (s : F) (h : V) (M : Fin n → Fin n → F),
    ∀ x, q x = s + dotProduct h x + ∑ i, ∑ j, M i j * x i * x j
  let aff := fun (q : V → F) => ∃ (s : F) (h : V), ∀ x, q x = s + dotProduct h x
  ∀ (A : I → V) (a : I → F) (u v : Fin m → F),
    2*m+1 ≤ Module.finrank F (Submodule.span F (Set.range A)) →
    let lin := fun (k : I) (x : V) => a k + dotProduct (A k) x
    let P := fun (i : Fin m) (x : V) => lin (some i,false) x * lin (some i,true) x
    let H := fun (x : V) =>
      (lin (none,false) x + ∑ i, u i * P i x) * (lin (none,true) x + ∑ i, v i * P i x)
    quad H → ∃ (X Y Z : V → F) (w : Fin m → F), aff X ∧ aff Y ∧ aff Z ∧
      ∀ x, H x = X x * Y x + Z x + ∑ i, w i * P i x) := by
  intro n m F V I quad aff A a u v hrank lin P H hH
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let B : Fin m × Bool → (Fin n → ZMod 2) := fun p => A (some p.1, p.2)
  let W_old : Submodule (ZMod 2) (Fin n → ZMod 2) := Submodule.span (ZMod 2) (Set.range B)
  let kL : I := (none, false)
  let kR : I := (none, true)
  have hrange_eq : Set.range A = Set.range B ∪ ({A kL} ∪ {A kR}) := by
    ext y
    constructor
    · rintro ⟨⟨o, b⟩, rfl⟩
      rcases o with _ | i
      · rcases b with _ | _
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · exact Or.inl ⟨(i, b), rfl⟩
    · rintro (⟨p, rfl⟩ | rfl | rfl)
      · exact ⟨(some p.1, p.2), rfl⟩
      · exact ⟨kL, rfl⟩
      · exact ⟨kR, rfl⟩
  have hspan_eq : Submodule.span (ZMod 2) (Set.range A) =
      W_old ⊔ Submodule.span (ZMod 2) {A kL} ⊔ Submodule.span (ZMod 2) {A kR} := by
    rw [hrange_eq, Submodule.span_union, Submodule.span_union, sup_assoc]
  by_cases hCase1 :
      A kL ∉ W_old ⊔ Submodule.span (ZMod 2) {A kR} ∧
      A kR ∉ W_old ⊔ Submodule.span (ZMod 2) {A kL}
  · obtain ⟨dL, hdL_L, hdL_W⟩ :=
      PEqualNP.Outside.L_lib_891_aux.exists_dual_vector
        (W_old ⊔ Submodule.span (ZMod 2) {A kR}) (A kL) hCase1.1
    obtain ⟨dR, hdR_R, hdR_W⟩ :=
      PEqualNP.Outside.L_lib_891_aux.exists_dual_vector
        (W_old ⊔ Submodule.span (ZMod 2) {A kL}) (A kR) hCase1.2
    let U0 : V → F := fun x => lin kL x + ∑ i, u i * P i x
    let V0 : V → F := fun x => lin kR x + ∑ i, v i * P i x
    have hdL_B : ∀ p, dotProduct (B p) dL = 0 := fun p =>
      hdL_W (B p) (Submodule.mem_sup_left (Submodule.subset_span ⟨p, rfl⟩))
    have hdL_R : dotProduct (A kR) dL = 0 :=
      hdL_W (A kR) (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _)))
    have hdR_B : ∀ p, dotProduct (B p) dR = 0 := fun p =>
      hdR_W (B p) (Submodule.mem_sup_left (Submodule.subset_span ⟨p, rfl⟩))
    have hdR_L : dotProduct (A kL) dR = 0 :=
      hdR_W (A kL) (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _)))
    have hdiffL : PEqualNP.Outside.L_lib_891_aux.diff dL H = V0 := by
      funext x
      have hP0 : ∀ i, P i (x + dL) = P i x := by
        intro i
        simp only [P, lin, dotProduct_add]
        have h0 : dotProduct (A (some i, false)) dL = 0 := hdL_B (i, false)
        have h1 : dotProduct (A (some i, true)) dL = 0 := hdL_B (i, true)
        rw [h0, h1, add_zero, add_zero]
      have hU : U0 (x + dL) = U0 x + 1 := by
        simp only [U0, lin, dotProduct_add, hdL_L, hP0]
        ring
      have hV : V0 (x + dL) = V0 x := by
        simp only [V0, lin, dotProduct_add, hdL_R, add_zero, hP0]
      change U0 (x + dL) * V0 (x + dL) + U0 x * V0 x = V0 x
      rw [hU, hV]
      have h2 : U0 x * V0 x + U0 x * V0 x = 0 :=
        PEqualNP.Outside.L_lib_891_aux.zmod2_add_self _
      calc (U0 x + 1) * V0 x + U0 x * V0 x = (U0 x * V0 x + U0 x * V0 x) + V0 x := by ring
        _ = V0 x := by rw [h2, zero_add]
    have hdiffR : PEqualNP.Outside.L_lib_891_aux.diff dR H = U0 := by
      funext x
      have hP0 : ∀ i, P i (x + dR) = P i x := by
        intro i
        simp only [P, lin, dotProduct_add]
        have h0 : dotProduct (A (some i, false)) dR = 0 := hdR_B (i, false)
        have h1 : dotProduct (A (some i, true)) dR = 0 := hdR_B (i, true)
        rw [h0, h1, add_zero, add_zero]
      have hU : U0 (x + dR) = U0 x := by
        simp only [U0, lin, dotProduct_add, hdR_L, add_zero, hP0]
      have hV : V0 (x + dR) = V0 x + 1 := by
        simp only [V0, lin, dotProduct_add, hdR_R, hP0]
        ring
      change U0 (x + dR) * V0 (x + dR) + U0 x * V0 x = U0 x
      rw [hU, hV]
      have h2 : U0 x * V0 x + U0 x * V0 x = 0 :=
        PEqualNP.Outside.L_lib_891_aux.zmod2_add_self _
      calc U0 x * (V0 x + 1) + U0 x * V0 x = (U0 x * V0 x + U0 x * V0 x) + U0 x := by ring
        _ = U0 x := by rw [h2, zero_add]
    have hAffV0 : aff V0 := by
      rw [← hdiffL]
      exact PEqualNP.Outside.L_lib_891_aux.isAff_diff_of_isQuad hH dL
    have hAffU0 : aff U0 := by
      rw [← hdiffR]
      exact PEqualNP.Outside.L_lib_891_aux.isAff_diff_of_isQuad hH dR
    refine ⟨U0, V0, fun _ => 0, fun _ => 0, hAffU0, hAffV0,
      PEqualNP.Outside.L_lib_891_aux.isAff_const 0, fun x => ?_⟩
    simp [H, U0, V0, kL, kR]
  · rw [not_and_or, not_not, not_not] at hCase1
    rcases hCase1 with hLdep | hRdep
    · have hspan_swap : Submodule.span (ZMod 2) (Set.range A) =
          W_old ⊔ Submodule.span (ZMod 2) {A kR} ⊔ Submodule.span (ZMod 2) {A kL} := by
        rw [hspan_eq, sup_right_comm]
      have hH_swap : PEqualNP.Outside.L_lib_891_aux.isQuad (fun x =>
          ((a kR + dotProduct (A kR) x) + ∑ i : Fin m, v i *
            ((a (some i, false) + dotProduct (A (some i, false)) x) *
             (a (some i, true) + dotProduct (A (some i, true)) x))) *
          ((a kL + dotProduct (A kL) x) + ∑ i : Fin m, u i *
            ((a (some i, false) + dotProduct (A (some i, false)) x) *
             (a (some i, true) + dotProduct (A (some i, true)) x)))) := by
        have hfn : (fun x =>
            ((a kR + dotProduct (A kR) x) + ∑ i : Fin m, v i *
              ((a (some i, false) + dotProduct (A (some i, false)) x) *
               (a (some i, true) + dotProduct (A (some i, true)) x))) *
            ((a kL + dotProduct (A kL) x) + ∑ i : Fin m, u i *
              ((a (some i, false) + dotProduct (A (some i, false)) x) *
               (a (some i, true) + dotProduct (A (some i, true)) x)))) = H := by
          funext x
          exact mul_comm _ _
        rw [hfn]
        exact hH
      obtain ⟨X, Y, Z, w, hX, hY, hZ, hEq⟩ :=
        PEqualNP.Outside.L_lib_891_aux.solve_dep A a kR kL v u hrank hspan_swap hLdep hH_swap
      refine ⟨X, Y, Z, w, hX, hY, hZ, fun x => ?_⟩
      have hmul : H x =
          ((a kR + dotProduct (A kR) x) + ∑ i : Fin m, v i * P i x) *
          ((a kL + dotProduct (A kL) x) + ∑ i : Fin m, u i * P i x) :=
        mul_comm _ _
      rw [hmul]
      exact hEq x
    · exact PEqualNP.Outside.L_lib_891_aux.solve_dep A a kL kR u v hrank hspan_eq hRdep hH
