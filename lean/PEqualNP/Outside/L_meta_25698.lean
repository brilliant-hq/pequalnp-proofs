import PEqualNP.Defs
import PEqualNP.Outside.L_lib_505

/- The coding-theoretic endpoint is the binary Griesmer bound, PEqualNP.Outside.L_lib_505. -/

namespace PEqualNP.Outside.L_meta_25698
abbrev F := ZMod 2
end PEqualNP.Outside.L_meta_25698

namespace PEqualNP.Outside.L_meta_25698
def quadBit (ff ft tf tt : Bool) : Bool := xor (xor ff ft) (xor tf tt)

/-- Two-slot Boolean algebraic normal form, including repeated Boolean inputs. -/
theorem anf2 (ff ft tf tt a b : Bool) :
    (if a then (if b then tt else tf) else (if b then ft else ff)) =
      xor (xor (xor ff (xor tf ff && a)) (xor ft ff && b)) (quadBit ff ft tf tt && a && b) := by
  cases ff <;> cases ft <;> cases tf <;> cases tt <;> cases a <;> cases b <;> decide

theorem anf1 (f t a : Bool) :
    (if a then t else f) = xor f (xor t f && a) := by
  cases f <;> cases t <;> cases a <;> decide

theorem anf2_fun (f : Bool → Bool → Bool) (a b : Bool) :
    f a b = xor (xor (xor (f false false) (xor (f true false) (f false false) && a))
      (xor (f false true) (f false false) && b))
      (quadBit (f false false) (f false true) (f true false) (f true true) && a && b) := by
  have h := anf2 (f false false) (f false true) (f true false) (f true true) a b
  cases a <;> cases b <;> exact h

theorem anf1_fun (f : Bool → Bool) (a : Bool) :
    f a = xor (f false) (xor (f true) (f false) && a) := by
  have h := anf1 (f false) (f true) a
  cases a <;> exact h

theorem getD_append_one {A : Type} (l : List A) (a d : A) (i : Nat) :
    (l ++ [a]).getD i d = if i = l.length then a else l.getD i d := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h₁ : i < l.length
  · rw [List.getElem?_append_left h₁, ite_eq_right (by omega)]
  · rw [List.getElem?_append_right (by omega)]
    by_cases h₂ : i = l.length
    · simp [h₂]
    · have h₃ : l[i]? = none := List.getElem?_eq_none (by omega)
      have h₄ : [a][i-l.length]? = none := List.getElem?_eq_none (by simp; omega)
      simp [h₂, h₃, h₄]

end PEqualNP.Outside.L_meta_25698
open scoped BigOperators
namespace PEqualNP.Outside.L_meta_25698

section Multiplication
variable {K : Type*} [Field K] [Algebra F K]
variable {r s k : ℕ}

noncomputable def evalRow (b : Module.Basis (Fin k) F K) (L : K →ₗ[F] F) :
    K →ₗ[F] (Fin k → F) where
  toFun x j := L (x * b j)
  map_add' x y := by ext j; simp [add_mul]
  map_smul' c x := by ext j; simp

theorem evalRow_inj (b : Module.Basis (Fin k) F K) (L : K →ₗ[F] F) (hL : L ≠ 0) :
    Function.Injective (evalRow b L) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  by_contra hn
  have hall : ∀ z : K, L (x * z) = 0 := by
    intro z
    conv_lhs => rw [← b.sum_repr z]
    rw [Finset.mul_sum, map_sum]
    apply Finset.sum_eq_zero
    intro j _
    have h := congrFun hx j
    change L (x * b j) = 0 at h
    rw [mul_smul_comm, map_smul, h, smul_zero]
  apply hL
  apply LinearMap.ext
  intro z
  have hz := hall (x⁻¹ * z)
  simpa [← mul_assoc, hn] using hz

theorem mulRank (b : Module.Basis (Fin k) F K) (L : K →ₗ[F] F) (hL : L ≠ 0)
    (row : Fin r → K) (col : Fin s → K) (hr : LinearIndependent F row)
    (hc : LinearIndependent F col) :
    r + s ≤ (Matrix.of (fun i j => L (row i * col j))).rank + k := by
  let A : Matrix (Fin r) (Fin k) F := Matrix.of (fun i => evalRow b L (row i))
  let B : Matrix (Fin k) (Fin s) F := Matrix.of (fun i j => b.equivFun (col j) i)
  have hA : A.rank = r := by
    have hAr : LinearIndependent F A.row := hr.map' (evalRow b L) (LinearMap.ker_eq_bot.mpr (evalRow_inj b L hL))
    simpa using hAr.rank_matrix
  have hB : B.rank = s := by
    have hBr : LinearIndependent F B.transpose.row :=
      hc.map' b.equivFun.toLinearMap (LinearMap.ker_eq_bot.mpr b.equivFun.injective)
    simpa [Matrix.rank_transpose] using hBr.rank_matrix
  have hab : A * B = Matrix.of (fun i j => L (row i * col j)) := by
    ext i j
    change (∑ a, L (row i * b a) * b.equivFun (col j) a) = L (row i * col j)
    conv_rhs => rw [← b.sum_repr (col j), Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [mul_smul_comm, map_smul]
    change L (row i * b a) * b.equivFun (col j) a = b.repr (col j) a * L (row i * b a)
    rw [mul_comm]
    rfl
  simpa [hA, hB, hab] using Matrix.rank_mul_ge A B

theorem galoisMulRank (hk : 0 < k) (L : GaloisField 2 k →ₗ[F] F) (hL : L ≠ 0)
    (row : Fin r → GaloisField 2 k) (col : Fin s → GaloisField 2 k)
    (hr : LinearIndependent F row) (hc : LinearIndependent F col) :
    r + s ≤ (Matrix.of (fun i j => L (row i * col j))).rank + k := by
  exact mulRank (Module.finBasisOfFinrankEq F (GaloisField 2 k) (GaloisField.finrank 2 hk.ne')) L hL row col hr hc
end Multiplication
end PEqualNP.Outside.L_meta_25698

open scoped BigOperators
namespace PEqualNP.Outside.L_meta_25698
abbrev Table (r s : ℕ) := Fin (r+1) → Fin (s+1) → F
abbrev Panel (r s : ℕ) := Matrix (Fin r) (Fin s) F

variable {r s q t : ℕ}
def cross (f : Table r s) : Panel r s :=
  Matrix.of fun i j => f i.succ j.succ + f i.succ 0 + f 0 j.succ + f 0 0

theorem char2 (a : F) : a + a = 0 := CharTwo.add_self_eq_zero a

theorem cross_add (f g : Table r s) : cross (f+g) = cross f + cross g := by
  ext i j
  change (f i.succ j.succ + g i.succ j.succ) + (f i.succ 0 + g i.succ 0) +
      (f 0 j.succ + g 0 j.succ) + (f 0 0 + g 0 0) = _
  simp only [cross, Matrix.of_apply, Matrix.add_apply]
  ac_rfl

theorem cross_smul (a : F) (f : Table r s) : cross (a • f) = a • cross f := by
  ext i j
  change a * f i.succ j.succ + a * f i.succ 0 + a * f 0 j.succ + a * f 0 0 =
    a * (f i.succ j.succ + f i.succ 0 + f 0 j.succ + f 0 0)
  ring

theorem cross_raw_row (f : Fin (r+1) → F) : cross (s:=s) (fun i _ => f i) = 0 := by
  ext i j
  change f i.succ + f i.succ + f 0 + f 0 = 0
  rw [char2, zero_add, char2]

theorem cross_raw_col (f : Fin (s+1) → F) : cross (r:=r) (fun _ j => f j) = 0 := by
  ext i j
  change f j.succ + f 0 + f j.succ + f 0 = 0
  rw [show f j.succ + f 0 + f j.succ + f 0 =
    (f j.succ + f j.succ) + (f 0 + f 0) by ac_rfl, char2, zero_add, char2]

theorem cross_const (a : F) : cross (r:=r) (s:=s) (fun _ _ => a) = 0 :=
  cross_raw_row (fun _ => a)

def rowDiff (f : Table r s) (i : Fin r) := f i.succ 0 + f 0 0
def colDiff (f : Table r s) (j : Fin s) := f 0 j.succ + f 0 0

theorem cross0_apply {f : Table r s} (hf : cross f = 0) (i : Fin r) (j : Fin s) :
    f i.succ j.succ = f i.succ 0 + f 0 j.succ + f 0 0 := by
  have h := Matrix.ext_iff.mpr hf i j
  change f i.succ j.succ + f i.succ 0 + f 0 j.succ + f 0 0 = 0 at h
  let a := f i.succ 0 + f 0 j.succ + f 0 0
  have h' : f i.succ j.succ + a = 0 := by simpa [a, ← add_assoc] using h
  calc
    f i.succ j.succ = (f i.succ j.succ + a) + a := by rw [add_assoc, char2, add_zero]
    _ = a := by rw [h', zero_add]

theorem cross_mul (f g : Table r s) (hf : cross f = 0) (hg : cross g = 0) :
    cross (f * g) =
      Matrix.vecMulVec (rowDiff f) (colDiff g) +
      Matrix.vecMulVec (rowDiff g) (colDiff f) := by
  ext i j
  change f i.succ j.succ * g i.succ j.succ + f i.succ 0 * g i.succ 0 +
    f 0 j.succ * g 0 j.succ + f 0 0 * g 0 0 =
      rowDiff f i * colDiff g j + rowDiff g i * colDiff f j
  rw [cross0_apply hf, cross0_apply hg]
  unfold rowDiff colDiff
  calc
    _ = ((f i.succ 0 + f 0 0) * (g 0 j.succ + g 0 0) +
         (g i.succ 0 + g 0 0) * (f 0 j.succ + f 0 0)) +
         (f i.succ 0 * g i.succ 0 + f i.succ 0 * g i.succ 0) +
         (f 0 j.succ * g 0 j.succ + f 0 j.succ * g 0 j.succ) := by ring
    _ = _ := by simp only [char2, add_zero]

abbrev Factors (r s : ℕ) := Fin 2 → (Fin r → F) × (Fin s → F)

def factorPanel (p : Factors r s) : Panel r s :=
  Matrix.vecMulVec (p 0).1 (p 0).2 + Matrix.vecMulVec (p 1).1 (p 1).2

def zeroFactors : Factors r s := fun _ => (0,0)

theorem zero_factor_panel : factorPanel (zeroFactors (r:=r) (s:=s)) = 0 := by
  ext i j
  change 0 * 0 + 0 * 0 = (0 : F)
  simp

def crossFactors (f g : Table r s) : Factors r s :=
  fun i => if i = 0 then (rowDiff f, colDiff g) else (rowDiff g, colDiff f)

theorem cross_mul_factors (f g : Table r s) (hf : cross f = 0) (hg : cross g = 0) :
    cross (f*g) = factorPanel (crossFactors f g) := by
  rw [cross_mul f g hf hg]
  simp [factorPanel,crossFactors]

def weight (c : Fin t → F) :=
  ((Finset.univ : Finset (Fin t)).filter fun i => c i ≠ 0).card

theorem panels_weight_bound (G : Fin t → Factors r s) (c : Fin t → F) :
    (∑ h, c h • factorPanel (G h)).rank ≤ 2 * weight c := by
  classical
  let S : Finset (Fin t) := Finset.univ.filter (fun h => c h ≠ 0)
  let A : Matrix (Fin r) (S × Fin 2) F := Matrix.of (fun i h =>
    c h.1.1 * (G h.1.1 h.2).1 i)
  let B : Matrix (S × Fin 2) (Fin s) F := Matrix.of (fun h j => (G h.1.1 h.2).2 j)
  have heq : (∑ h, c h • factorPanel (G h)) = A * B := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.mul_apply, A, B, Matrix.of_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, smul_eq_mul, factorPanel, Matrix.add_apply, Matrix.vecMulVec_apply]
    let fn : Fin t → F := fun h =>
      c h * ((G h 0).1 i * (G h 0).2 j) + c h * ((G h 1).1 i * (G h 1).2 j)
    simp only [mul_add, mul_assoc]
    change ∑ h, fn h = ∑ h : S, fn h
    rw [S.sum_coe_sort fn]
    apply (Finset.sum_filter_of_ne (p:=fun h => c h ≠ 0) ?_).symm
    intro h _ hn
    by_contra hz
    simp [fn,hz] at hn
  calc
    _ = (A*B).rank := congrArg Matrix.rank heq
    _ ≤ A.rank := Matrix.rank_mul_le_left A B
    _ ≤ _ := by
      have h := Matrix.rank_le_card_width A
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, Nat.mul_comm] at h
      exact h

end PEqualNP.Outside.L_meta_25698
open scoped BigOperators
open PEqualNP.CircuitLowerBounds PEqualNP.Represents

namespace PEqualNP.Outside.L_meta_25698
variable {r s : ℕ}
abbrev BoolTab (r s : ℕ) := Fin (r+1) → Fin (s+1) → Bool

def bit (b : Bool) : F := if b then 1 else 0

theorem bit_xor (a b : Bool) : bit (xor a b) = bit a + bit b := by
  cases a <;> cases b <;> decide
theorem bit_and (a b : Bool) : bit (a && b) = bit a * bit b := by
  cases a <;> cases b <;> decide

def toTab (W : BoolTab r s) : Table r s := fun i j => bit (W i j)
def nonlin (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
      (xor (g.op.eval [true,false]) (g.op.eval [true,true]))
def gd (d : Nat → Nat) (g : Gate) :=
  (g.inputs.map d).foldr max 0 + (nonlin g).toNat

def dTrace (w : ℕ) (ls : List Gate) :=
  ls.foldl (fun (ds : List ℕ) g => ds ++ [gd (fun a => ds.getD a 0) g])
    (List.replicate w 0)

abbrev C (ls : List Gate) : Circuit := ⟨ls, 0⟩
def dep (ls : List Gate) (a : ℕ) : ℕ :=
  (dTrace (r+1+(s+1)) ls).getD a 0
def tab (ls : List Gate) (a : ℕ) : BoolTab r s :=
  fun i j => ((C ls).wires (oneEach i j)).getD a false

def gt (g : Gate) (W : ℕ → BoolTab r s) : BoolTab r s :=
  fun i j => g.op.eval (g.inputs.map fun a => W a i j)

private theorem dTrace_snoc (w : ℕ) (ls : List Gate) (g : Gate) :
    dTrace w (ls++[g]) = dTrace w ls ++ [gd (fun a => (dTrace w ls).getD a 0) g] := by
  simp only [dTrace, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem trace_len (w : ℕ) (ls : List Gate) :
    (dTrace w ls).length = w + ls.length := by
  induction ls using List.reverseRecOn with
  | nil => simp [dTrace]
  | append_singleton l a ih => rw [dTrace_snoc]; simp [ih, Nat.add_assoc]

private theorem wires_len (w : List Bool) (ls : List Gate) :
    ((C ls).wires w).length = w.length + ls.length := by
  induction ls using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton l a ih =>
    have e : (C (l++[a])).wires w =
        (C l).wires w ++ [a.op.eval (a.inputs.map fun i => ((C l).wires w).getD i false)] := by
      simp [Circuit.wires, List.foldl_append]
    simp [e, ih, Nat.add_assoc]

private theorem dep_snoc (ls : List Gate) (g : Gate) (a : ℕ) :
    dep (r:=r) (s:=s) (ls++[g]) a =
      if a = r+1+(s+1)+ls.length then gd (dep (r:=r) (s:=s) ls) g else dep (r:=r) (s:=s) ls a := by
  have e : dTrace (r+1+(s+1)) (ls++[g]) = dTrace (r+1+(s+1)) ls ++ [gd (dep (r:=r) (s:=s) ls) g] := by
    exact dTrace_snoc _ _ _
  rw [dep, e, getD_append_one, trace_len]
  rfl

private theorem tab_snoc (ls : List Gate) (g : Gate) (a : ℕ) :
    tab (r:=r) (s:=s) (ls++[g]) a =
      if a = r+1+(s+1)+ls.length then gt g (tab ls) else tab ls a := by
  ext i j
  have e : (C (ls++[g])).wires (oneEach i j) =
      (C ls).wires (oneEach i j) ++ [gt g (tab ls) i j] := by
    simp [Circuit.wires, tab, gt, List.foldl_append]
  conv_lhs => rw [tab, e, getD_append_one, wires_len]
  simp only [oneEach, List.length_append, List.length_ofFn]
  split <;> rfl

private theorem rawCross (a : ℕ) : cross (toTab (tab (r:=r) (s:=s) [] a)) = 0 := by
  by_cases h : a < r+1
  · have hl : ∀ (i : Fin (r+1)), a < (List.ofFn (fun x => decide (x=i))).length := by
      intro i; simpa using h
    convert cross_raw_row (s:=s) (fun i : Fin (r+1) => bit ((List.ofFn (fun x => decide (x=i))).getD a false)) using 2
    ext i j
    simp only [toTab, tab, Circuit.wires, List.foldl_nil, oneEach, List.getD_append _ _ _ _ (hl i)]
  · have hl : ∀ (i : Fin (r+1)), (List.ofFn (fun x => decide (x=i))).length ≤ a := by
      intro i; simpa using Nat.le_of_not_gt h
    convert cross_raw_col (r:=r) (fun j : Fin (s+1) => bit ((List.ofFn (fun y => decide (y=j))).getD (a-(r+1)) false)) using 2
    ext i j
    simp only [toTab, tab, Circuit.wires, List.foldl_nil, oneEach, List.getD_append_right _ _ _ _ (hl i),
      List.length_ofFn]

def Sspan {t : ℕ} (G : Fin t → Factors r s) :=
  Submodule.span F (Set.range fun i => factorPanel (G i))

private theorem affine1 (op : GateOp) (a : BoolTab r s) :
    toTab (fun i j => op.eval [a i j]) =
      (fun _ _ => bit (op.eval [false])) + (bit (xor (op.eval [true]) (op.eval [false]))) • toTab a := by
  ext i j
  change bit (op.eval [a i j]) = bit (op.eval [false]) +
    bit (xor (op.eval [true]) (op.eval [false])) * bit (a i j)
  simpa only [bit_xor, bit_and] using congrArg bit (anf1_fun (fun b => op.eval [b]) (a i j))

private theorem affine2 (op : GateOp) (a b : BoolTab r s) :
    toTab (fun i j => op.eval [a i j, b i j]) =
      (fun _ _ => bit (op.eval [false,false])) +
      (bit (xor (op.eval [true,false]) (op.eval [false,false]))) • toTab a +
      (bit (xor (op.eval [false,true]) (op.eval [false,false]))) • toTab b +
      bit (quadBit (op.eval [false,false]) (op.eval [false,true])
          (op.eval [true,false]) (op.eval [true,true])) • (toTab a * toTab b) := by
  ext i j
  change bit (op.eval [a i j, b i j]) =
    bit (op.eval [false,false]) +
    bit (xor (op.eval [true,false]) (op.eval [false,false])) * bit (a i j) +
    bit (xor (op.eval [false,true]) (op.eval [false,false])) * bit (b i j) +
    bit (quadBit (op.eval [false,false]) (op.eval [false,true]) (op.eval [true,false]) (op.eval [true,true])) *
      (bit (a i j) * bit (b i j))
  simpa only [bit_xor, bit_and, mul_assoc] using
    congrArg bit (anf2_fun (fun x y => op.eval [x,y]) (a i j) (b i j))

private theorem gate_linear {t : ℕ} (G : Fin t → Factors r s)
    (W : ℕ → BoolTab r s) (D : ℕ → ℕ) (g : Gate) (ha : g.inputs.length ≤ 2)
    (hl : nonlin g = false)
    (h₀ : ∀ a, D a = 0 → cross (toTab (W a)) = 0)
    (h₁ : ∀ a, D a ≤ 1 → cross (toTab (W a)) ∈ Sspan G) :
    (gd D g = 0 → cross (toTab (gt g W)) = 0) ∧
    (gd D g ≤ 1 → cross (toTab (gt g W)) ∈ Sspan G) := by
  rcases g with ⟨op, inp⟩
  rcases inp with _ | ⟨a, _ | ⟨b, _ | ⟨c,rest⟩⟩⟩
  · rw [show toTab (gt ⟨op, []⟩ W) = (fun _ _ => bit (op.eval [])) by rfl, cross_const]
    exact ⟨fun _ => rfl, fun _ => Submodule.zero_mem _⟩
  · rw [show toTab (gt ⟨op, [a]⟩ W) = toTab (fun i j => op.eval [W a i j]) by rfl,
      affine1, cross_add, cross_const, zero_add, cross_smul]
    simp only [gd, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
      max_zero, hl, Bool.toNat_false, Nat.add_zero]
    exact ⟨fun h => by rw [h₀ a h, smul_zero], fun h => Submodule.smul_mem _ _ (h₁ a h)⟩
  · have hq : quadBit (op.eval [false,false]) (op.eval [false,true])
        (op.eval [true,false]) (op.eval [true,true]) = false := by
      simpa [quadBit, nonlin] using hl
    rw [show toTab (gt ⟨op,[a,b]⟩ W) = toTab (fun i j => op.eval [W a i j, W b i j]) by rfl,
      affine2, hq]
    simp only [bit, Bool.false_eq_true, ite_false, zero_smul, add_zero]
    simp only [cross_add, cross_const, zero_add, cross_smul, gd, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, max_zero, hl, Bool.toNat_false, Nat.add_zero]
    constructor
    · intro h
      rw [h₀ a (by omega), h₀ b (by omega), smul_zero, smul_zero, zero_add]
    · intro h
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (h₁ a (by omega)))
        (Submodule.smul_mem _ _ (h₁ b (by omega)))
  · simp at ha

private theorem gate_nonlin (W : ℕ → BoolTab r s) (D : ℕ → ℕ) (g : Gate)
    (ha : g.inputs.length ≤ 2) (hl : nonlin g = true)
    (h₀ : ∀ a, D a = 0 → cross (toTab (W a)) = 0) :
    0 < gd D g ∧ ∃ p : Factors r s, gd D g ≤ 1 → cross (toTab (gt g W)) = factorPanel p := by
  refine ⟨by simp [gd, hl], ?_⟩
  rcases g with ⟨op, inp⟩
  rcases inp with _ | ⟨a, _ | ⟨b, _ | ⟨c,rest⟩⟩⟩
  · simp [nonlin] at hl
  · simp [nonlin] at hl
  · have hq : quadBit (op.eval [false,false]) (op.eval [false,true])
        (op.eval [true,false]) (op.eval [true,true]) = true := by
      simpa [quadBit, nonlin] using hl
    refine ⟨crossFactors (toTab (W a)) (toTab (W b)), fun h => ?_⟩
    have hm : max (D a) (D b) + 1 ≤ 1 := by simpa [gd,hl] using h
    rw [show toTab (gt ⟨op,[a,b]⟩ W) = toTab (fun i j => op.eval [W a i j, W b i j]) by rfl,
      affine2, hq]
    simp only [bit, ite_true, one_smul]
    have hA := h₀ a (by omega)
    have hB := h₀ b (by omega)
    simp only [cross_add, cross_const, cross_smul, hA, hB, smul_zero, zero_add, cross_mul_factors _ _ hA hB]
  · simp at ha

theorem extract (ls : List Gate) (ha : ∀ g ∈ ls, g.inputs.length ≤ 2) :
    ∃ G : Fin (ls.countP nonlin) → Factors r s,
      (∀ i, dep (r:=r) (s:=s) ls i = 0 → cross (toTab (tab (r:=r) (s:=s) ls i)) = 0) ∧
      (∀ i, dep (r:=r) (s:=s) ls i ≤ 1 → cross (toTab (tab ls i)) ∈ Sspan G) := by
  induction ls using List.reverseRecOn with
  | nil =>
    refine ⟨Fin.elim0, (fun i _ => rawCross i), fun i _ => ?_⟩
    rw [rawCross i]
    exact Submodule.zero_mem _
  | append_singleton ls g ih =>
    obtain ⟨G,h₀,h₁⟩ := ih (fun a hm => ha a (List.mem_append_left _ hm))
    have ar : g.inputs.length ≤ 2 := ha g (by simp)
    cases e : nonlin g
    · have key := gate_linear G (tab ls) (dep (r:=r) (s:=s) ls) g ar e h₀ h₁
      have hc : (ls++[g]).countP nonlin = ls.countP nonlin := by simp [e]
      rw [hc]
      refine ⟨G, ?_, ?_⟩
      · intro i hh
        by_cases hz : i = r+1+(s+1)+ls.length
        · have hh' : gd (dep (r:=r) (s:=s) ls) g = 0 := by simpa [dep_snoc, hz] using hh
          simpa [tab_snoc,hz] using key.1 hh'
        · have hh' : dep (r:=r) (s:=s) ls i = 0 := by simpa [dep_snoc, hz] using hh
          simpa [tab_snoc,hz] using h₀ i hh'
      · intro i hh
        by_cases hz : i = r+1+(s+1)+ls.length
        · have hh' : gd (dep (r:=r) (s:=s) ls) g ≤ 1 := by simpa [dep_snoc, hz] using hh
          simpa [tab_snoc,hz] using key.2 hh'
        · have hh' : dep (r:=r) (s:=s) ls i ≤ 1 := by simpa [dep_snoc, hz] using hh
          simpa [tab_snoc,hz] using h₁ i hh'
    · obtain ⟨hp,p,hpf⟩ := gate_nonlin (tab ls) (dep (r:=r) (s:=s) ls) g ar e h₀
      have hc : (ls++[g]).countP nonlin = ls.countP nonlin + 1 := by simp [e]
      rw [hc]
      let G' : Fin ((ls.countP nonlin)+1) → Factors r s := Fin.lastCases p G
      have hsub : Sspan G ≤ Sspan G' := by
        apply Submodule.span_mono
        rintro _ ⟨i,rfl⟩
        exact ⟨i.castSucc, by simp [G']⟩
      refine ⟨G', ?_, ?_⟩
      · intro i hh
        by_cases hz : i = r+1+(s+1)+ls.length
        · have hh' : gd (dep (r:=r) (s:=s) ls) g = 0 := by simpa [dep_snoc, hz] using hh
          omega
        · have hh' : dep (r:=r) (s:=s) ls i = 0 := by simpa [dep_snoc, hz] using hh
          simpa [tab_snoc,hz] using h₀ i hh'
      · intro i hh
        by_cases hz : i = r+1+(s+1)+ls.length
        · have hh' : gd (dep (r:=r) (s:=s) ls) g ≤ 1 := by simpa [dep_snoc, hz] using hh
          rw [tab_snoc, ite_eq_left hz, hpf hh']
          apply Submodule.subset_span
          exact ⟨Fin.last _, by simp [G']⟩
        · have hh' : dep (r:=r) (s:=s) ls i ≤ 1 := by simpa [dep_snoc, hz] using hh
          simpa [tab_snoc,hz] using hsub (h₁ i hh')
end PEqualNP.Outside.L_meta_25698
open scoped BigOperators
open PEqualNP.CircuitLowerBounds PEqualNP.Represents

namespace PEqualNP.Outside.L_meta_25698

private theorem bit_nonzero (x : F) : bit (decide (x ≠ 0)) = x := by
  by_cases h : x = 0
  · simp [h,bit]
  · have h1 : x = 1 := by
      apply ZMod.val_injective 2
      have hx := ZMod.val_lt x
      have h0 : x.val ≠ 0 := fun h0 => h ((ZMod.val_eq_zero x).mp h0)
      have hx1 : x.val = 1 := by omega
      simpa [ZMod.val_one_eq_one_mod] using hx1
    simp [h1,bit]

variable {r s k q t : ℕ}

abbrev K (k : ℕ) := GaloisField 2 k

private noncomputable def mulTab (row : Fin r → K k) (col : Fin s → K k) (L : K k →ₗ[F] F) :
    Table r s :=
  fun i j => L (Fin.cases 0 row i * Fin.cases 0 col j)

private theorem cross_mulTab (row : Fin r → K k) (col : Fin s → K k) (L : K k →ₗ[F] F) :
    cross (mulTab row col L) = Matrix.of (fun i j => L (row i * col j)) := by
  ext i j
  simp [cross,mulTab]

private theorem algebracombine {m : ℕ} (G : Fin m → Factors r s)
    (cs : Fin q → Fin m → F) (w : Fin q → F) :
    (∑ h, (Fintype.linearCombination F cs w) h • factorPanel (G h)) =
      ∑ j, w j • (∑ h, cs j h • factorPanel (G h)) := by
  calc
    _ = ∑ h, ∑ j, w j • (cs j h • factorPanel (G h)) := by
      refine Finset.sum_congr rfl fun h _ => ?_
      simp only [Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, Finset.sum_smul, smul_smul, smul_eq_mul]
    _ = ∑ j, ∑ h, w j • (cs j h • factorPanel (G h)) := Finset.sum_comm
    _ = _ := by simp only [Finset.smul_sum]

private theorem readMix (row : Fin r → K k) (col : Fin s → K k)
    (L : Fin q → (K k →ₗ[F] F)) (w : Fin q → F) :
    (∑ j, w j • Matrix.of (fun a b => L j (row a * col b))) =
      Matrix.of (fun a b => (Fintype.linearCombination F L w) (row a * col b)) := by
  ext a b
  simp only [Fintype.linearCombination_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply,
    LinearMap.sum_apply, LinearMap.smul_apply]

theorem finish (hk : 0 < k) (row : Fin r → K k) (col : Fin s → K k)
    (L : Fin q → (K k →ₗ[F] F))
    (hr : LinearIndependent F row) (hc : LinearIndependent F col) (hL : LinearIndependent F L)
    (C : Circuit) (tap : Fin q → ℕ) (ha : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (ht : C.gates.countP nonlin ≤ t)
    (htap : ∀ j : Fin q, dep (r:=r) (s:=s) C.gates (tap j) ≤ 1 ∧
      Represents (fun x y => decide (mulTab row col (L j) x y ≠ 0)) ⟨C.gates,tap j⟩) :
    (∑ i : Fin q, ((r+s-k+1)/2 + 2^i.val - 1) / 2^i.val) ≤ t := by
  classical
  let d := (r+s-k+1)/2
  change (∑ i : Fin q, (d + 2^i.val - 1) / 2^i.val) ≤ t
  by_cases hd : d = 0
  · have hz : ∀ (i : Fin q), (d + 2^i.val - 1) / 2^i.val = 0 := by
      intro i
      rw [hd, zero_add]
      apply Nat.div_eq_of_lt
      have hpos : 0 < (2 : ℕ)^i.val := pow_pos (by decide) _
      omega
    simp [hz]
  obtain ⟨G,_,hD⟩ := extract (r:=r) (s:=s) C.gates ha
  have hac (j : Fin q) : Matrix.of (fun a b => L j (row a * col b)) ∈ Sspan G := by
    have mem := hD (tap j) (htap j).1
    have heq : toTab (tab C.gates (tap j)) = mulTab row col (L j) := by
      ext x y
      have e := (htap j).2 x y
      change tab C.gates (tap j) x y = decide (mulTab row col (L j) x y ≠ 0) at e
      exact congrArg bit e |>.trans (bit_nonzero _)
    rwa [heq, cross_mulTab] at mem
  have hcoef (j : Fin q) : ∃ c : Fin (C.gates.countP nonlin) → F,
      (∑ h, c h • factorPanel (G h)) = Matrix.of (fun a b => L j (row a * col b)) :=
    (Submodule.mem_span_range_iff_exists_fun F).mp (hac j)
  choose coeff hcoeff using hcoef
  let E := Fintype.linearCombination F coeff
  have hcmin (w : Fin q → F) (hw : w ≠ 0) : d ≤ weight (E w) := by
    have hln : Fintype.linearCombination F L w ≠ 0 :=
      fun h => hw ((linearIndependent_iff_injective_fintypeLinearCombination.mp hL) (by simpa using h))
    have hgalois := galoisMulRank hk (Fintype.linearCombination F L w) hln row col hr hc
    have hb := panels_weight_bound G (E w)
    have heq : (∑ h, E w h • factorPanel (G h)) =
        Matrix.of (fun a b => (Fintype.linearCombination F L w) (row a * col b)) := by
      rw [show (∑ h, E w h • factorPanel (G h)) = ∑ j, w j • (∑ h, coeff j h • factorPanel (G h)) from
        algebracombine G coeff w]
      simp_rw [hcoeff]
      exact readMix row col L w
    rw [heq] at hb
    dsimp [d]
    omega
  exact (PEqualNP.Outside.L_lib_505 q (C.gates.countP nonlin) d (Nat.pos_of_ne_zero hd) E hcmin).trans ht
end PEqualNP.Outside.L_meta_25698


theorem PEqualNP.Outside.L_meta_25698 :
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)
let fits := fun (n m q : ℕ) (G : Fin q → Fin n → Fin m → Bool) (t : ℕ) =>
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin q → ℕ),
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
    ∀ j : Fin q, (depths (n+m) C).getD (tap j) 0 ≤ 1 ∧
      PEqualNP.Represents.Represents (G j) ⟨C.gates, tap j⟩
∀ (k r s q : ℕ), 0 < k →
  let F := ZMod 2
  let K := GaloisField 2 k
  ∀ (row : Fin r → K) (col : Fin s → K) (readout : Fin q → (K →ₗ[F] F)),
    LinearIndependent F row → LinearIndependent F col → LinearIndependent F readout →
    let rowAt : Fin (r+1) → K := Fin.cases 0 row
    let colAt : Fin (s+1) → K := Fin.cases 0 col
    let G := fun j x y => decide (readout j (rowAt x * colAt y) ≠ 0)
    let d := (r+s-k+1)/2
    ∀ t : ℕ, fits (r+1) (s+1) q G t →
      (∑ i : Fin q, (d + 2^i.val - 1) / 2^i.val) ≤ t
 := by
  dsimp only
  intro k r s q hk row col readout hrow hcol hreadout t hf
  obtain ⟨C,tap,_,harg,ht,hw⟩ := hf
  exact PEqualNP.Outside.L_meta_25698.finish hk row col readout hrow hcol hreadout C tap harg ht hw
