import Mathlib
import PEqualNP.Defs

-- The circuit criterion is by ovolee37, PR 39024, from the pinned file
-- lean/PEqualNP/Outside/L_meta_25647.lean at fa2348ccfea15fd12b5c24dc8b88ac377fe3ad9f.
-- The helper namespace is renamed and four-corner and protocol transfers are added.

namespace PEqualNP.Outside.L_meta_33678_aux
open PEqualNP.CircuitLowerBounds PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

theorem b2z_inj {a b : Bool} (h : b2z a = b2z b) : a = b := by
  cases a <;> cases b <;> simp [b2z] at h <;> rfl

theorem b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

theorem b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

theorem b2z_not (a : Bool) : b2z (!a) = 1 + b2z a := by
  cases a <;> decide

theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

theorem zmod2_two : (2 : ZMod 2) = 0 := rfl

theorem zmod2_ite_eq (x : ZMod 2) : (if x = 1 then (1 : ZMod 2) else 0) = x := by
  by_cases h : x = 1
  · simp [h]
  · simp only [h, ite_false]
    fin_cases x
    · rfl
    · exact absurd rfl h

def nlGate (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def depthsOf (w : ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat])
    (List.replicate w 0)

def wiresOf (x : List Bool) (gs : List Gate) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem wiresOf_length (x : List Bool) (gs : List Gate) :
    (wiresOf x gs).length = x.length + gs.length := by
  unfold wiresOf
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem depthsOf_length (w : ℕ) (gs : List Gate) :
    (depthsOf w gs).length = w + gs.length := by
  unfold depthsOf
  have aux : ∀ (ds : List ℕ) (gs : List Gate),
      (gs.foldl (fun (ds : List ℕ) g =>
        ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat]) ds).length =
      ds.length + gs.length := by
    intro ds gs
    induction gs generalizing ds with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  rw [aux, List.length_replicate]

theorem wiresOf_append (x : List Bool) (gs1 gs2 : List Gate) :
    wiresOf x (gs1 ++ gs2) =
      gs2.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (wiresOf x gs1) := by
  unfold wiresOf
  rw [List.foldl_append]

theorem depthsOf_append (w : ℕ) (gs1 gs2 : List Gate) :
    depthsOf w (gs1 ++ gs2) =
      gs2.foldl (fun (ds : List ℕ) g =>
        ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat])
        (depthsOf w gs1) := by
  unfold depthsOf
  rw [List.foldl_append]

theorem foldl_append_prefix {α β : Type*} (f : List α → β → α) (l : List β) (init : List α) :
    ∃ ext : List α, l.foldl (fun acc b => acc ++ [f acc b]) init = init ++ ext := by
  induction l generalizing init with
  | nil => exact ⟨[], by simp⟩
  | cons b l ih =>
    rw [List.foldl_cons]
    obtain ⟨ext, hext⟩ := ih (init ++ [f init b])
    exact ⟨f init b :: ext, by rw [hext]; simp⟩

theorem wiresOf_append_getD_lt (x : List Bool) (gs1 gs2 : List Gate) {k : ℕ}
    (hk : k < x.length + gs1.length) :
    (wiresOf x (gs1 ++ gs2)).getD k false = (wiresOf x gs1).getD k false := by
  rw [wiresOf_append]
  obtain ⟨ext, hext⟩ := foldl_append_prefix
    (fun (w : List Bool) (g : Gate) => g.op.eval (g.inputs.map fun i => w.getD i false))
    gs2 (wiresOf x gs1)
  rw [hext, List.getD_append _ _ _ _ (by rw [wiresOf_length]; exact hk)]

theorem depthsOf_append_getD_lt (w : ℕ) (gs1 gs2 : List Gate) {k : ℕ}
    (hk : k < w + gs1.length) :
    (depthsOf w (gs1 ++ gs2)).getD k 0 = (depthsOf w gs1).getD k 0 := by
  rw [depthsOf_append]
  obtain ⟨ext, hext⟩ := foldl_append_prefix
    (fun (ds : List ℕ) (g : Gate) =>
      (g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat)
    gs2 (depthsOf w gs1)
  rw [hext, List.getD_append _ _ _ _ (by rw [depthsOf_length]; exact hk)]

theorem wiresOf_getD_input (x : List Bool) (gs : List Gate) {k : ℕ} (hk : k < x.length) :
    (wiresOf x gs).getD k false = x.getD k false := by
  have h := wiresOf_append_getD_lt x [] gs (by simpa using hk)
  simpa [wiresOf] using h

theorem depthsOf_getD_input (w : ℕ) (gs : List Gate) {k : ℕ} (hk : k < w) :
    (depthsOf w gs).getD k 0 = 0 := by
  have h := depthsOf_append_getD_lt w [] gs (by simpa using hk)
  simp only [List.nil_append] at h
  rw [h]
  unfold depthsOf
  simp only [List.foldl_nil]
  rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_replicate]

theorem wiresOf_getD_gate (x : List Bool) (gs : List Gate) {idx : ℕ} (hidx : idx < gs.length)
    (hrb : ∀ a ∈ (gs[idx]).inputs, a < x.length + idx) :
    (wiresOf x gs).getD (x.length + idx) false =
      (gs[idx]).op.eval ((gs[idx]).inputs.map fun a => (wiresOf x gs).getD a false) := by
  have hsplit : gs = (gs.take idx ++ [gs[idx]]) ++ gs.drop (idx + 1) := by
    rw [List.take_append_getElem, List.take_append_drop]
  have hlen1 : (gs.take idx).length = idx := List.length_take_of_le (Nat.le_of_lt hidx)
  have hlen2 : (gs.take idx ++ [gs[idx]]).length = idx + 1 := by
    rw [List.length_append, hlen1]
    rfl
  conv_lhs => rw [hsplit]
  rw [wiresOf_append_getD_lt x (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [wiresOf_append, List.foldl_cons, List.foldl_nil]
  have hlw : (wiresOf x (gs.take idx)).length = x.length + idx := by
    rw [wiresOf_length, hlen1]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp only [hlw, Nat.sub_self, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro a ha
  have halt : a < x.length + (gs.take idx).length := by rw [hlen1]; exact hrb a ha
  conv_rhs => rw [hsplit]
  rw [wiresOf_append_getD_lt x (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [wiresOf_append_getD_lt x (gs.take idx) [gs[idx]] halt]

theorem depthsOf_getD_gate (w : ℕ) (gs : List Gate) {idx : ℕ} (hidx : idx < gs.length)
    (hrb : ∀ a ∈ (gs[idx]).inputs, a < w + idx) :
    (depthsOf w gs).getD (w + idx) 0 =
      ((gs[idx]).inputs.map (fun a => (depthsOf w gs).getD a 0)).foldr max 0 +
        (nlGate (gs[idx])).toNat := by
  have hsplit : gs = (gs.take idx ++ [gs[idx]]) ++ gs.drop (idx + 1) := by
    rw [List.take_append_getElem, List.take_append_drop]
  have hlen1 : (gs.take idx).length = idx := List.length_take_of_le (Nat.le_of_lt hidx)
  have hlen2 : (gs.take idx ++ [gs[idx]]).length = idx + 1 := by
    rw [List.length_append, hlen1]
    rfl
  conv_lhs => rw [hsplit]
  rw [depthsOf_append_getD_lt w (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [depthsOf_append, List.foldl_cons, List.foldl_nil]
  have hld : (depthsOf w (gs.take idx)).length = w + idx := by
    rw [depthsOf_length, hlen1]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp only [hld, Nat.sub_self, List.getD_cons_zero]
  congr 2
  apply List.map_congr_left
  intro a ha
  have halt : a < w + (gs.take idx).length := by rw [hlen1]; exact hrb a ha
  conv_rhs => rw [hsplit]
  rw [depthsOf_append_getD_lt w (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [depthsOf_append_getD_lt w (gs.take idx) [gs[idx]] halt]

theorem oneEach_length {n m : ℕ} (i : Fin n) (j : Fin m) :
    (oneEach i j).length = n + m := by
  simp [oneEach]

theorem oneEach_getD_left {n m : ℕ} (i : Fin n) (j : Fin m) {k : ℕ} (hk : k < n) :
    (oneEach i j).getD k false = decide (k = i.val) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simp [hk])]
  rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_ofFn]
  simp [Fin.ext_iff]

theorem oneEach_getD_right {n m : ℕ} (i : Fin n) (j : Fin m) {k : ℕ} (hk1 : n ≤ k)
    (hk2 : k < n + m) :
    (oneEach i j).getD k false = decide (k - n = j.val) := by
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by simp [hk1])]
  simp only [List.length_ofFn]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  simp [Fin.ext_iff]

theorem anf_one (f : Bool → Bool) (x : Bool) :
    b2z (f x) = b2z (f false) + (b2z (f false) + b2z (f true)) * b2z x := by
  cases x <;> cases h0 : f false <;> cases h1 : f true <;> decide

theorem anf_two (f : Bool → Bool → Bool) (x y : Bool) :
    b2z (f x y) =
      b2z (f false false) +
      (b2z (f false false) + b2z (f true false)) * b2z x +
      (b2z (f false false) + b2z (f false true)) * b2z y +
      b2z (xor (xor (f false false) (f false true)) (xor (f true false) (f true true))) *
        (b2z x * b2z y) := by
  cases x <;> cases y <;>
    cases h00 : f false false <;> cases h01 : f false true <;>
    cases h10 : f true false <;> cases h11 : f true true <;> decide

def anchor {n m : ℕ} (u : Fin n) (v : Fin m) (h : Fin n → Fin m → ZMod 2) :
    Matrix (Fin n) (Fin m) (ZMod 2) :=
  fun i j => h i j + h i v + h u j + h u v

theorem anchor_const {n m : ℕ} (u : Fin n) (v : Fin m) (c : ZMod 2) :
    anchor u v (fun _ _ => c) = 0 := by
  ext i j
  simp only [anchor, Matrix.zero_apply]
  simp [zmod2_add_self]

theorem anchor_split {n m : ℕ} (u : Fin n) (v : Fin m) (r : Fin n → ZMod 2) (s : Fin m → ZMod 2) :
    anchor u v (fun i j => r i + s j) = 0 := by
  ext i j
  simp only [anchor, Matrix.zero_apply]
  have h : (r i + s j) + (r i + s v) + (r u + s j) + (r u + s v) =
      (r i + r i) + (r u + r u) + (s j + s j) + (s v + s v) := by ring
  simp [h, zmod2_add_self]

theorem anchor_add {n m : ℕ} (u : Fin n) (v : Fin m) (h1 h2 : Fin n → Fin m → ZMod 2) :
    anchor u v (fun i j => h1 i j + h2 i j) = anchor u v h1 + anchor u v h2 := by
  ext i j
  simp only [anchor, Matrix.add_apply]
  ring

theorem anchor_smul {n m : ℕ} (u : Fin n) (v : Fin m) (c : ZMod 2) (h : Fin n → Fin m → ZMod 2) :
    anchor u v (fun i j => c * h i j) = c • anchor u v h := by
  ext i j
  simp only [anchor, Matrix.smul_apply, smul_eq_mul]
  ring

theorem anchor_prod_split {n m : ℕ} (u : Fin n) (v : Fin m)
    (r1 r2 : Fin n → ZMod 2) (s1 s2 : Fin m → ZMod 2) :
    anchor u v (fun i j => (r1 i + s1 j) * (r2 i + s2 j)) =
      Matrix.vecMulVec (fun i => r1 i + r1 u) (fun j => s2 j + s2 v) +
      Matrix.vecMulVec (fun i => r2 i + r2 u) (fun j => s1 j + s1 v) := by
  ext i j
  simp only [anchor, Matrix.add_apply, Matrix.vecMulVec_apply]
  have h : ((r1 i + s1 j) * (r2 i + s2 j) + (r1 i + s1 v) * (r2 i + s2 v) +
      (r1 u + s1 j) * (r2 u + s2 j) + (r1 u + s1 v) * (r2 u + s2 v)) +
      ((r1 i + r1 u) * (s2 j + s2 v) + (r2 i + r2 u) * (s1 j + s1 v)) =
      (2 : ZMod 2) * (r1 i * r2 i + r1 u * r2 u + s1 j * s2 j + s1 v * s2 v +
        r1 i * s2 j + r1 i * s2 v + r1 u * s2 j + r1 u * s2 v +
        r2 i * s1 j + r2 i * s1 v + r2 u * s1 j + r2 u * s1 v) := by ring
  rw [zmod2_two, zero_mul] at h
  have hsub : ∀ a b : ZMod 2, a + b = 0 → a = b := by
    intro a b hab
    calc a = a + 0 := (add_zero a).symm
      _ = a + (b + b) := by rw [zmod2_add_self]
      _ = (a + b) + b := by ring
      _ = 0 + b := by rw [hab]
      _ = b := zero_add b
  exact hsub _ _ h

theorem rank_of_factor {n m K : ℕ} (P : Matrix (Fin n) (Fin K) (ZMod 2))
    (Q : Matrix (Fin K) (Fin m) (ZMod 2)) : (P * Q).rank ≤ K := by
  calc (P * Q).rank ≤ P.rank := Matrix.rank_mul_le_left P Q
    _ = Module.finrank (ZMod 2) (LinearMap.range P.mulVecLin) := rfl
    _ ≤ Module.finrank (ZMod 2) (Fin K → ZMod 2) := LinearMap.finrank_range_le P.mulVecLin
    _ = K := Module.finrank_fin_fun (ZMod 2)

theorem factor_of_rank_le {n m K : ℕ} (A : Matrix (Fin n) (Fin m) (ZMod 2)) (h : A.rank ≤ K) :
    ∃ (rowVec : Fin K → Fin n → ZMod 2) (colVec : Fin K → Fin m → ZMod 2),
      ∀ i j, A i j = ∑ k : Fin K, rowVec k i * colVec k j := by
  let r := A.rank
  let b := Module.finBasisOfFinrankEq (ZMod 2) (LinearMap.range A.mulVecLin)
    (rfl : Module.finrank (ZMod 2) (LinearMap.range A.mulVecLin) = r)
  have hcol : ∀ j : Fin m, (fun i => A i j) ∈ LinearMap.range A.mulVecLin := by
    intro j
    refine ⟨Pi.single j 1, ?_⟩
    ext i
    simp [Matrix.mulVec_single]
  let rowVec : Fin K → Fin n → ZMod 2 := fun k i =>
    if hk : k.val < r then (b ⟨k.val, hk⟩).val i else 0
  let colVec : Fin K → Fin m → ZMod 2 := fun k j =>
    if hk : k.val < r then b.repr ⟨fun i => A i j, hcol j⟩ ⟨k.val, hk⟩ else 0
  refine ⟨rowVec, colVec, fun i j => ?_⟩
  have hrepr : ∑ t : Fin r, (b.repr ⟨fun i => A i j, hcol j⟩ t) • (b t) =
      ⟨fun i => A i j, hcol j⟩ := b.sum_repr ⟨fun i => A i j, hcol j⟩
  have heval : A i j = ∑ t : Fin r, (b t).val i * b.repr ⟨fun i => A i j, hcol j⟩ t := by
    have h1 := congrArg (fun (v : LinearMap.range A.mulVecLin) => v.val i) hrepr
    simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul_of_tower,
      Pi.smul_apply, smul_eq_mul] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun t _ => mul_comm _ _
  rw [heval]
  symm
  have hfilt : ∑ k : Fin K, rowVec k i * colVec k j =
      ∑ k ∈ Finset.univ.filter (fun k : Fin K => k.val < r), rowVec k i * colVec k j := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k _ hnk
    rw [Finset.mem_filter] at hnk
    have hge : ¬ k.val < r := fun hk => hnk ⟨Finset.mem_univ k, hk⟩
    simp [rowVec, colVec, hge]
  rw [hfilt]
  refine Finset.sum_bij (fun k hk => ⟨k.val, (Finset.mem_filter.mp hk).2⟩) ?_ ?_ ?_ ?_
  · intro _ _
    exact Finset.mem_univ _
  · intro k1 _ k2 _ heq
    exact Fin.ext (Fin.mk.inj heq)
  · intro t _
    refine ⟨⟨t.val, Nat.lt_of_lt_of_le t.isLt h⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.isLt⟩, Fin.ext rfl⟩
  · intro k hk
    have hlt : k.val < r := (Finset.mem_filter.mp hk).2
    simp only [rowVec, colVec, hlt, dite_true]
    rfl

theorem card_filter_fin_eq_countP {α : Type*} (l : List α) (p : α → Bool) :
    (Finset.univ.filter (fun idx : Fin l.length => p l[idx.val] = true)).card = l.countP p := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.countP_cons]
    have hsplit : (Finset.univ.filter (fun idx : Fin (a :: l).length => p (a :: l)[idx.val] = true)).card =
        (if p a = true then 1 else 0) +
        (Finset.univ.filter (fun idx : Fin l.length => p l[idx.val] = true)).card := by
      have hsum : ∀ (S : Finset (Fin (l.length + 1))), S.card =
          (if (0 : Fin (l.length + 1)) ∈ S then 1 else 0) +
          (Finset.univ.filter (fun idx : Fin l.length => idx.succ ∈ S)).card := by
        intro S
        have h1 : S.card = ∑ x : Fin (l.length + 1), if x ∈ S then 1 else 0 := by
          simp
        rw [h1, Fin.sum_univ_succ]
        congr 1
        simp
      have h2 := hsum (Finset.univ.filter (fun idx : Fin (a :: l).length => p (a :: l)[idx.val] = true))
      simpa using h2
    rw [hsplit, ih]
    cases p a <;> simp [Nat.add_comm]

theorem dir_le {n m : ℕ} (G : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m) (t : ℕ)
    (C : Circuit)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hrb : ReadsBack (n + m) C)
    (hrep : Represents G C)
    (hd1 : (depthsOf (n + m) C.gates).getD C.output 0 ≤ 1)
    (hcnt : C.gates.countP nlGate ≤ t) :
    (anchor u v (fun i j => b2z (G i j))).rank ≤ 2 * t := by
  let val : ℕ → Fin n → Fin m → ZMod 2 :=
    fun k i j => b2z ((wiresOf (oneEach i j) C.gates).getD k false)
  let dep : ℕ → ℕ := fun k => (depthsOf (n + m) C.gates).getD k 0
  have hrb' : ∀ (idx : ℕ) (hidx : idx < C.gates.length),
      ∀ a ∈ (C.gates[idx]).inputs, a < n + m + idx := by
    intro idx hidx a ha
    have h := hrb idx hidx a
    unfold gateAt at h
    rw [List.getD_eq_getElem _ _ hidx] at h
    exact h ha
  have hval_gate : ∀ (idx : ℕ) (hidx : idx < C.gates.length) (i : Fin n) (j : Fin m),
      val (n + m + idx) i j =
        b2z ((C.gates[idx]).op.eval ((C.gates[idx]).inputs.map fun a =>
          (wiresOf (oneEach i j) C.gates).getD a false)) := by
    intro idx hidx i j
    unfold val
    have h := wiresOf_getD_gate (oneEach i j) C.gates hidx (by
      intro a ha
      rw [oneEach_length]
      exact hrb' idx hidx a ha)
    rw [oneEach_length] at h
    rw [h]
  have hdep_gate : ∀ (idx : ℕ) (hidx : idx < C.gates.length),
      dep (n + m + idx) =
        ((C.gates[idx]).inputs.map (fun a => dep a)).foldr max 0 +
          (nlGate (C.gates[idx])).toNat := by
    intro idx hidx
    exact depthsOf_getD_gate (n + m) C.gates hidx (hrb' idx hidx)
  have hsplit_zero : ∀ k : ℕ, dep k = 0 →
      ∃ (r : Fin n → ZMod 2) (s : Fin m → ZMod 2), ∀ i j, val k i j = r i + s j := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hdk
      by_cases hk1 : k < n + m
      · by_cases hk0 : k < n
        · refine ⟨fun i => b2z (decide (k = i.val)), fun _ => 0, fun i j => ?_⟩
          unfold val
          rw [wiresOf_getD_input _ _ (by rw [oneEach_length]; exact hk1),
            oneEach_getD_left i j hk0, add_zero]
        · refine ⟨fun _ => 0, fun j => b2z (decide (k - n = j.val)), fun i j => ?_⟩
          unfold val
          rw [wiresOf_getD_input _ _ (by rw [oneEach_length]; exact hk1),
            oneEach_getD_right i j (by omega) hk1, zero_add]
      · by_cases hk2 : k < n + m + C.gates.length
        · let idx := k - (n + m)
          have hidx : idx < C.gates.length := by omega
          have hkeq : k = n + m + idx := by omega
          rw [hkeq] at hdk ⊢
          let g := C.gates[idx]
          have hdg := hdep_gate idx hidx
          change dep (n + m + idx) = (g.inputs.map dep).foldr max 0 + (nlGate g).toNat at hdg
          rw [hdk] at hdg
          have hnl : nlGate g = false := by
            have h0 : (nlGate g).toNat = 0 := by omega
            cases h : nlGate g
            · rfl
            · rw [h] at h0
              simp at h0
          have hgl : g.inputs.length ≤ 2 := hlen g (List.getElem_mem hidx)
          match hg_in : g.inputs with
          | [] =>
            refine ⟨fun _ => b2z (g.op.eval []), fun _ => 0, fun i j => ?_⟩
            rw [hval_gate idx hidx i j]
            change b2z (g.op.eval (g.inputs.map _)) = _
            rw [hg_in, List.map_nil, add_zero]
          | [a] =>
            have ha_lt : a < n + m + idx := hrb' idx hidx a (by rw [hg_in]; simp)
            have ha_d : dep a = 0 := by
              change 0 = (g.inputs.map dep).foldr max 0 + (nlGate g).toNat at hdg
              rw [hg_in] at hdg
              simp at hdg
              omega
            obtain ⟨r1, s1, h1⟩ := ih a (by omega) ha_d
            let c0 := b2z (g.op.eval [false])
            let c1 := b2z (g.op.eval [false]) + b2z (g.op.eval [true])
            refine ⟨fun i => c0 + c1 * r1 i, fun j => c1 * s1 j, fun i j => ?_⟩
            rw [hval_gate idx hidx i j]
            change b2z (g.op.eval (g.inputs.map _)) = _
            rw [hg_in, List.map_cons, List.map_nil]
            have hanf := anf_one (fun x => g.op.eval [x]) ((wiresOf (oneEach i j) C.gates).getD a false)
            change b2z (g.op.eval [_]) = c0 + c1 * val a i j at hanf
            rw [hanf, h1 i j]
            ring
          | [a, b] =>
            have ha_lt : a < n + m + idx := hrb' idx hidx a (by rw [hg_in]; simp)
            have hb_lt : b < n + m + idx := hrb' idx hidx b (by rw [hg_in]; simp)
            have hab_d : dep a = 0 ∧ dep b = 0 := by
              change 0 = (g.inputs.map dep).foldr max 0 + (nlGate g).toNat at hdg
              rw [hg_in] at hdg
              simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil] at hdg
              omega
            obtain ⟨r1, s1, h1⟩ := ih a (by omega) hab_d.1
            obtain ⟨r2, s2, h2⟩ := ih b (by omega) hab_d.2
            have hxor : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
                (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = false := by
              unfold nlGate at hnl
              rw [hg_in] at hnl
              simpa using hnl
            let c0 := b2z (g.op.eval [false, false])
            let c1 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [true, false])
            let c2 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [false, true])
            refine ⟨fun i => c0 + c1 * r1 i + c2 * r2 i, fun j => c1 * s1 j + c2 * s2 j, fun i j => ?_⟩
            rw [hval_gate idx hidx i j]
            change b2z (g.op.eval (g.inputs.map _)) = _
            rw [hg_in, List.map_cons, List.map_cons, List.map_nil]
            have hanf := anf_two (fun x y => g.op.eval [x, y])
              ((wiresOf (oneEach i j) C.gates).getD a false)
              ((wiresOf (oneEach i j) C.gates).getD b false)
            rw [hxor] at hanf
            have hbf : b2z false = 0 := rfl
            change b2z (g.op.eval [_, _]) = c0 + c1 * val a i j + c2 * val b i j + b2z false * _ at hanf
            rw [hbf, zero_mul, add_zero] at hanf
            rw [hanf, h1 i j, h2 i j]
            ring
          | _ :: _ :: _ :: _ =>
            rw [hg_in] at hgl
            simp at hgl
        · refine ⟨fun _ => 0, fun _ => 0, fun i j => ?_⟩
          unfold val
          have hge : (wiresOf (oneEach i j) C.gates).length ≤ k := by
            rw [wiresOf_length, oneEach_length]
            omega
          rw [List.getD_eq_default _ _ hge]
          simp [b2z]
  let NL : Finset (Fin C.gates.length) :=
    Finset.univ.filter (fun idx => nlGate (C.gates[idx.val]) = true ∧ dep (n + m + idx.val) ≤ 1)
  have hNL_card : NL.card ≤ t := by
    calc NL.card
        ≤ (Finset.univ.filter (fun idx : Fin C.gates.length => nlGate (C.gates[idx.val]) = true)).card :=
          Finset.card_le_card (fun idx hidx => Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, (Finset.mem_filter.mp hidx).2.1⟩)
      _ = C.gates.countP nlGate := card_filter_fin_eq_countP C.gates nlGate
      _ ≤ t := hcnt
  have hNL_outer : ∀ idx ∈ NL,
      ∃ (r1 r2 : Fin n → ZMod 2) (s1 s2 : Fin m → ZMod 2),
        anchor u v (val (n + m + idx.val)) =
          Matrix.vecMulVec r1 s1 + Matrix.vecMulVec r2 s2 := by
    intro idx hidx_mem
    have hnl : nlGate (C.gates[idx.val]) = true := (Finset.mem_filter.mp hidx_mem).2.1
    have hdg1 : dep (n + m + idx.val) ≤ 1 := (Finset.mem_filter.mp hidx_mem).2.2
    let g := C.gates[idx.val]
    have hlen2 : g.inputs.length = 2 := by
      unfold nlGate at hnl
      rw [Bool.and_eq_true] at hnl
      simpa using hnl.1
    obtain ⟨a, b, hab⟩ : ∃ a b, g.inputs = [a, b] := by
      match h : g.inputs with
      | [a, b] => exact ⟨a, b, rfl⟩
      | [] => rw [h] at hlen2; simp at hlen2
      | [_] => rw [h] at hlen2; simp at hlen2
      | _ :: _ :: _ :: _ => rw [h] at hlen2; simp at hlen2
    have hdg := hdep_gate idx.val idx.isLt
    change dep (n + m + idx.val) = (g.inputs.map dep).foldr max 0 + (nlGate g).toNat at hdg
    rw [hab, hnl] at hdg
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Bool.toNat_true] at hdg
    have hda : dep a = 0 := by omega
    have hdb : dep b = 0 := by omega
    obtain ⟨r1, s1, h1⟩ := hsplit_zero a hda
    obtain ⟨r2, s2, h2⟩ := hsplit_zero b hdb
    have hxor : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = true := by
      unfold nlGate at hnl
      rw [Bool.and_eq_true] at hnl
      exact hnl.2
    let c0 := b2z (g.op.eval [false, false])
    let c1 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [true, false])
    let c2 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [false, true])
    have hfun : val (n + m + idx.val) = fun i j =>
        (c0 + c1 * r1 i + c2 * r2 i + (c1 * s1 j + c2 * s2 j)) +
        (r1 i + s1 j) * (r2 i + s2 j) := by
      funext i j
      rw [hval_gate idx.val idx.isLt i j]
      change b2z (g.op.eval (g.inputs.map _)) = _
      rw [hab, List.map_cons, List.map_cons, List.map_nil]
      have hanf := anf_two (fun x y => g.op.eval [x, y])
        ((wiresOf (oneEach i j) C.gates).getD a false)
        ((wiresOf (oneEach i j) C.gates).getD b false)
      rw [hxor] at hanf
      have hbt : b2z true = 1 := rfl
      change b2z (g.op.eval [_, _]) = c0 + c1 * val a i j + c2 * val b i j + b2z true * (val a i j * val b i j) at hanf
      rw [hbt, one_mul] at hanf
      rw [hanf, h1 i j, h2 i j]
      ring
    refine ⟨fun i => r1 i + r1 u, fun i => r2 i + r2 u, fun j => s2 j + s2 v, fun j => s1 j + s1 v, ?_⟩
    rw [hfun, anchor_add, anchor_split, zero_add, anchor_prod_split]
  have hspan : ∀ k : ℕ, dep k ≤ 1 →
      ∃ coeff : Fin C.gates.length → ZMod 2,
        anchor u v (val k) = ∑ idx ∈ NL, coeff idx • anchor u v (val (n + m + idx.val)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hdk
      by_cases hdk0 : dep k = 0
      · obtain ⟨r, s, hrs⟩ := hsplit_zero k hdk0
        refine ⟨fun _ => 0, ?_⟩
        have hfun : val k = fun i j => r i + s j := by funext i j; exact hrs i j
        rw [hfun, anchor_split]
        simp
      · have hk1 : n + m ≤ k := by
          by_contra hlt
          have := depthsOf_getD_input (n + m) C.gates (by omega : k < n + m)
          exact hdk0 this
        have hk2 : k < n + m + C.gates.length := by
          by_contra hge
          have hlen_d : (depthsOf (n + m) C.gates).length ≤ k := by
            rw [depthsOf_length]
            omega
          exact hdk0 (List.getD_eq_default _ _ hlen_d)
        let idx : Fin C.gates.length := ⟨k - (n + m), by omega⟩
        have hkeq : k = n + m + idx.val := by simp [idx]; omega
        rw [hkeq] at hdk ⊢
        let g := C.gates[idx.val]
        by_cases hnl : nlGate g = true
        · have hmem : idx ∈ NL := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnl, hdk⟩
          refine ⟨fun idx' => if idx' = idx then 1 else 0, ?_⟩
          rw [Finset.sum_eq_single idx]
          · simp
          · intro idx' _ hne
            simp [hne]
          · intro h
            exact absurd hmem h
        · have hnlf : nlGate g = false := by cases h : nlGate g <;> simp_all
          have hdg := hdep_gate idx.val idx.isLt
          have hgl : g.inputs.length ≤ 2 := hlen g (List.getElem_mem idx.isLt)
          match hg_in : g.inputs with
          | [] =>
            refine ⟨fun _ => 0, ?_⟩
            have hfun : val (n + m + idx.val) = fun _ _ => b2z (g.op.eval []) := by
              funext i j
              rw [hval_gate idx.val idx.isLt i j]
              change b2z (g.op.eval (g.inputs.map _)) = _
              rw [hg_in, List.map_nil]
            rw [hfun, anchor_const]
            simp
          | [a] =>
            have ha_lt : a < n + m + idx.val := hrb' idx.val idx.isLt a (by rw [hg_in]; simp)
            have ha_d : dep a ≤ 1 := by
              change dep (n + m + idx.val) = (g.inputs.map dep).foldr max 0 + (nlGate g).toNat at hdg
              rw [hg_in] at hdg
              simp at hdg
              omega
            obtain ⟨ca, hca⟩ := ih a (by omega) ha_d
            let c0 := b2z (g.op.eval [false])
            let c1 := b2z (g.op.eval [false]) + b2z (g.op.eval [true])
            refine ⟨fun idx' => c1 * ca idx', ?_⟩
            have hfun : val (n + m + idx.val) = fun i j => c0 + c1 * val a i j := by
              funext i j
              rw [hval_gate idx.val idx.isLt i j]
              change b2z (g.op.eval (g.inputs.map _)) = _
              rw [hg_in, List.map_cons, List.map_nil]
              exact anf_one (fun x => g.op.eval [x]) ((wiresOf (oneEach i j) C.gates).getD a false)
            rw [hfun, anchor_add, anchor_const, zero_add, anchor_smul, hca, Finset.smul_sum]
            refine Finset.sum_congr rfl fun idx' _ => by rw [smul_smul]
          | [a, b] =>
            have ha_lt : a < n + m + idx.val := hrb' idx.val idx.isLt a (by rw [hg_in]; simp)
            have hb_lt : b < n + m + idx.val := hrb' idx.val idx.isLt b (by rw [hg_in]; simp)
            have hab_d : dep a ≤ 1 ∧ dep b ≤ 1 := by
              change dep (n + m + idx.val) = (g.inputs.map dep).foldr max 0 + (nlGate g).toNat at hdg
              rw [hg_in] at hdg
              simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil] at hdg
              omega
            obtain ⟨ca, hca⟩ := ih a (by omega) hab_d.1
            obtain ⟨cb, hcb⟩ := ih b (by omega) hab_d.2
            have hxor : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
                (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = false := by
              unfold nlGate at hnlf
              rw [hg_in] at hnlf
              simpa using hnlf
            let c0 := b2z (g.op.eval [false, false])
            let c1 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [true, false])
            let c2 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [false, true])
            refine ⟨fun idx' => c1 * ca idx' + c2 * cb idx', ?_⟩
            have hfun : val (n + m + idx.val) = fun i j => (c0 + c1 * val a i j) + c2 * val b i j := by
              funext i j
              rw [hval_gate idx.val idx.isLt i j]
              change b2z (g.op.eval (g.inputs.map _)) = _
              rw [hg_in, List.map_cons, List.map_cons, List.map_nil]
              have hanf := anf_two (fun x y => g.op.eval [x, y])
                ((wiresOf (oneEach i j) C.gates).getD a false)
                ((wiresOf (oneEach i j) C.gates).getD b false)
              rw [hxor] at hanf
              have hbf : b2z false = 0 := rfl
              change b2z (g.op.eval [_, _]) = c0 + c1 * val a i j + c2 * val b i j + b2z false * _ at hanf
              rw [hbf, zero_mul, add_zero] at hanf
              exact hanf
            rw [hfun, anchor_add, anchor_add, anchor_const, zero_add, anchor_smul, anchor_smul,
              hca, hcb, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun idx' _ => by
              rw [smul_smul, smul_smul, ← add_smul]
          | _ :: _ :: _ :: _ =>
            rw [hg_in] at hgl
            simp at hgl
  obtain ⟨coeff, hcoeff⟩ := hspan C.output hd1
  have hAeq : anchor u v (fun i j => b2z (G i j)) = anchor u v (val C.output) := by
    congr 1
    funext i j
    unfold val
    rw [← hrep i j]
    rfl
  rw [hAeq, hcoeff]
  choose r1 r2 s1 s2 houter using fun idx : NL => hNL_outer idx.val idx.property
  let P : Matrix (Fin n) (NL ⊕ NL) (ZMod 2) := fun i k =>
    match k with
    | Sum.inl idx => coeff idx.val * r1 idx i
    | Sum.inr idx => coeff idx.val * r2 idx i
  let Q : Matrix (NL ⊕ NL) (Fin m) (ZMod 2) := fun k j =>
    match k with
    | Sum.inl idx => s1 idx j
    | Sum.inr idx => s2 idx j
  have hPQ : ∑ idx ∈ NL, coeff idx • anchor u v (val (n + m + idx.val)) = P * Q := by
    ext i j
    rw [Matrix.mul_apply, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    simp only [Matrix.sum_apply]
    rw [← Finset.sum_attach NL]
    refine Finset.sum_congr rfl fun idx _ => ?_
    simp only [Matrix.smul_apply, smul_eq_mul, houter idx, Matrix.add_apply,
      Matrix.vecMulVec_apply, P, Q]
    ring
  rw [hPQ]
  calc (P * Q).rank ≤ P.rank := Matrix.rank_mul_le_left P Q
    _ = Module.finrank (ZMod 2) (LinearMap.range P.mulVecLin) := rfl
    _ ≤ Module.finrank (ZMod 2) (NL ⊕ NL → ZMod 2) := LinearMap.finrank_range_le P.mulVecLin
    _ = Fintype.card (NL ⊕ NL) := Module.finrank_pi (ZMod 2)
    _ = NL.card + NL.card := by simp
    _ ≤ 2 * t := by omega

def Valid (n m : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, g.inputs.length ≤ 2) ∧ ReadsBack (n + m) ⟨gs, 0⟩

theorem valid_nil (n m : ℕ) : Valid n m [] := by
  exact ⟨by simp, by simp [ReadsBack]⟩

theorem valid_snoc {n m : ℕ} {gs : List Gate} (hv : Valid n m gs) (g : Gate)
    (hlen : g.inputs.length ≤ 2) (hbound : ∀ a ∈ g.inputs, a < n + m + gs.length) :
    Valid n m (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.mp hg' with h | h
    · exact hv.1 g' h
    · rw [List.mem_singleton.mp h]
      exact hlen
  · intro j hj a ha
    change j < (gs ++ [g]).length at hj
    change a ∈ ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).inputs at ha
    by_cases hj' : j < gs.length
    · rw [List.getD_append _ _ _ _ hj'] at ha
      exact hv.2 j hj' a ha
    · have heq : j = gs.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      subst j
      rw [List.getD_append_right _ _ _ _ le_rfl] at ha
      simp only [Nat.sub_self, List.getD_cons_zero] at ha
      exact hbound a ha

theorem nlGate_or_nil : nlGate ⟨GateOp.or, []⟩ = false := rfl

theorem nlGate_mod2 (a b : ℕ) : nlGate ⟨GateOp.mod 2, [a, b]⟩ = false := rfl

theorem nlGate_not (a : ℕ) : nlGate ⟨GateOp.not, [a]⟩ = false := rfl

theorem nlGate_and (a b : ℕ) : nlGate ⟨GateOp.and, [a, b]⟩ = true := rfl

def pushFalse (gs : List Gate) : List Gate := gs ++ [⟨GateOp.or, []⟩]

def pushXor (n m : ℕ) (gs : List Gate) (a b : ℕ) : List Gate :=
  gs ++ [⟨GateOp.mod 2, [a, b]⟩, ⟨GateOp.not, [n + m + gs.length]⟩]

def pushAnd (gs : List Gate) (a b : ℕ) : List Gate :=
  gs ++ [⟨GateOp.and, [a, b]⟩]

theorem pushFalse_spec {n m : ℕ} {gs : List Gate} (hv : Valid n m gs) :
    let gs' := pushFalse gs
    let w := n + m + gs.length
    Valid n m gs' ∧ gs'.length = gs.length + 1 ∧
    gs'.countP nlGate = gs.countP nlGate ∧
    (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
    (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
      (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
    (depthsOf (n + m) gs').getD w 0 = 0 ∧
    (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD w false) = 0) := by
  refine ⟨valid_snoc hv _ (by simp) (by simp), by simp [pushFalse], ?_, ?_, ?_, ?_, ?_⟩
  · simp [pushFalse, List.countP_append, nlGate_or_nil]
  · intro k hk
    exact depthsOf_append_getD_lt (n + m) gs _ hk
  · intro i j k hk
    exact wiresOf_append_getD_lt (oneEach i j) gs _ (by rw [oneEach_length]; exact hk)
  · unfold pushFalse
    rw [depthsOf_append, List.foldl_cons, List.foldl_nil]
    have hl : (depthsOf (n + m) gs).length = n + m + gs.length := depthsOf_length (n + m) gs
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hl, nlGate_or_nil]
  · intro i j
    unfold pushFalse
    rw [wiresOf_append, List.foldl_cons, List.foldl_nil]
    have hl : (wiresOf (oneEach i j) gs).length = n + m + gs.length := by
      rw [wiresOf_length, oneEach_length]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hl, GateOp.eval, b2z]

theorem pushXor_spec {n m : ℕ} {gs : List Gate} (hv : Valid n m gs) {a b : ℕ}
    (ha : a < n + m + gs.length) (hb : b < n + m + gs.length) :
    let gs' := pushXor n m gs a b
    let w := n + m + gs.length + 1
    Valid n m gs' ∧ gs'.length = gs.length + 2 ∧
    gs'.countP nlGate = gs.countP nlGate ∧
    (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
    (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
      (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
    (depthsOf (n + m) gs').getD w 0 =
      max ((depthsOf (n + m) gs).getD a 0) ((depthsOf (n + m) gs).getD b 0) ∧
    (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD w false) =
      b2z ((wiresOf (oneEach i j) gs).getD a false) +
      b2z ((wiresOf (oneEach i j) gs).getD b false)) := by
  let g1 : Gate := ⟨GateOp.mod 2, [a, b]⟩
  let g2 : Gate := ⟨GateOp.not, [n + m + gs.length]⟩
  have hsplit : pushXor n m gs a b = (gs ++ [g1]) ++ [g2] := by
    simp [pushXor, g1, g2]
  have hv1 : Valid n m (gs ++ [g1]) := valid_snoc hv g1 (by simp [g1]) (by
    intro x hx; simp only [g1, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption)
  have hv2 : Valid n m ((gs ++ [g1]) ++ [g2]) := valid_snoc hv1 g2 (by simp [g2]) (by
    intro x hx; simp only [g2, List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx; simp)
  refine ⟨hsplit ▸ hv2, by simp [pushXor], ?_, ?_, ?_, ?_, ?_⟩
  · simp [pushXor, List.countP_append, nlGate_mod2, nlGate_not]
  · intro k hk
    exact depthsOf_append_getD_lt (n + m) gs _ hk
  · intro i j k hk
    exact wiresOf_append_getD_lt (oneEach i j) gs _ (by rw [oneEach_length]; exact hk)
  · rw [hsplit, depthsOf_append, List.foldl_cons, List.foldl_nil]
    have hl1 : (depthsOf (n + m) (gs ++ [g1])).length = n + m + gs.length + 1 := by
      rw [depthsOf_length]; simp; omega
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hl1, Nat.sub_self, List.getD_cons_zero, g2, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, nlGate_not, Bool.toNat_false, add_zero, Nat.max_zero]
    rw [depthsOf_append, List.foldl_cons, List.foldl_nil]
    have hl0 : (depthsOf (n + m) gs).length = n + m + gs.length := depthsOf_length (n + m) gs
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hl0, Nat.sub_self, List.getD_cons_zero, g1, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, nlGate_mod2, Bool.toNat_false, add_zero, Nat.max_zero]
  · intro i j
    rw [hsplit, wiresOf_append, List.foldl_cons, List.foldl_nil]
    have hl1 : (wiresOf (oneEach i j) (gs ++ [g1])).length = n + m + gs.length + 1 := by
      rw [wiresOf_length, oneEach_length]; simp; omega
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hl1, Nat.sub_self, List.getD_cons_zero, g2, List.map_cons, List.map_nil]
    rw [wiresOf_append, List.foldl_cons, List.foldl_nil]
    have hl0 : (wiresOf (oneEach i j) gs).length = n + m + gs.length := by
      rw [wiresOf_length, oneEach_length]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hl0, Nat.sub_self, List.getD_cons_zero, g1, List.map_cons, List.map_nil]
    generalize (wiresOf (oneEach i j) gs).getD a false = va
    generalize (wiresOf (oneEach i j) gs).getD b false = vb
    cases va <;> cases vb <;> decide

theorem pushAnd_spec {n m : ℕ} {gs : List Gate} (hv : Valid n m gs) {a b : ℕ}
    (ha : a < n + m + gs.length) (hb : b < n + m + gs.length) :
    let gs' := pushAnd gs a b
    let w := n + m + gs.length
    Valid n m gs' ∧ gs'.length = gs.length + 1 ∧
    gs'.countP nlGate = gs.countP nlGate + 1 ∧
    (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
    (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
      (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
    (depthsOf (n + m) gs').getD w 0 =
      max ((depthsOf (n + m) gs).getD a 0) ((depthsOf (n + m) gs).getD b 0) + 1 ∧
    (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD w false) =
      b2z ((wiresOf (oneEach i j) gs).getD a false) *
      b2z ((wiresOf (oneEach i j) gs).getD b false)) := by
  refine ⟨valid_snoc hv _ (by simp) (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption), by simp [pushAnd], ?_, ?_, ?_, ?_, ?_⟩
  · simp [pushAnd, List.countP_append, nlGate_and]
  · intro k hk
    exact depthsOf_append_getD_lt (n + m) gs _ hk
  · intro i j k hk
    exact wiresOf_append_getD_lt (oneEach i j) gs _ (by rw [oneEach_length]; exact hk)
  · unfold pushAnd
    rw [depthsOf_append, List.foldl_cons, List.foldl_nil]
    have hl0 : (depthsOf (n + m) gs).length = n + m + gs.length := depthsOf_length (n + m) gs
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hl0, Nat.sub_self, List.getD_cons_zero, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, nlGate_and, Bool.toNat_true, Nat.max_zero]
  · intro i j
    unfold pushAnd
    rw [wiresOf_append, List.foldl_cons, List.foldl_nil]
    have hl0 : (wiresOf (oneEach i j) gs).length = n + m + gs.length := by
      rw [wiresOf_length, oneEach_length]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hl0, Nat.sub_self, List.getD_cons_zero, List.map_cons, List.map_nil]
    generalize (wiresOf (oneEach i j) gs).getD a false = va
    generalize (wiresOf (oneEach i j) gs).getD b false = vb
    cases va <;> cases vb <;> decide

theorem build_xor_list {n m : ℕ} (D : ℕ) (ws : List ℕ) (gs : List Gate) (hv : Valid n m gs)
    (hb : ∀ w ∈ ws, w < n + m + gs.length)
    (hd : ∀ w ∈ ws, (depthsOf (n + m) gs).getD w 0 ≤ D) :
    ∃ (gs' : List Gate) (out : ℕ),
      Valid n m gs' ∧ gs.length ≤ gs'.length ∧ out < n + m + gs'.length ∧
      gs'.countP nlGate = gs.countP nlGate ∧
      (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
      (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
        (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
      (depthsOf (n + m) gs').getD out 0 ≤ D ∧
      (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD out false) =
        (ws.map (fun w => b2z ((wiresOf (oneEach i j) gs).getD w false))).sum) := by
  induction ws generalizing gs with
  | nil =>
    obtain ⟨hv', hlen', hcnt', hdp', hwp', hdout, hwout⟩ := pushFalse_spec hv
    exact ⟨pushFalse gs, n + m + gs.length, hv', by omega, by omega, hcnt', hdp', hwp',
      by omega, fun i j => by simpa using hwout i j⟩
  | cons w ws ih =>
    have hw_lt : w < n + m + gs.length := hb w List.mem_cons_self
    have hw_d : (depthsOf (n + m) gs).getD w 0 ≤ D := hd w List.mem_cons_self
    obtain ⟨gs1, out1, hv1, hle1, hout1, hcnt1, hdp1, hwp1, hd1, hw1⟩ :=
      ih gs hv (fun a ha => hb a (List.mem_cons_of_mem w ha))
        (fun a ha => hd a (List.mem_cons_of_mem w ha))
    obtain ⟨hv2, hlen2, hcnt2, hdp2, hwp2, hd2, hw2⟩ :=
      pushXor_spec hv1 (by omega : w < n + m + gs1.length) hout1
    refine ⟨pushXor n m gs1 w out1, n + m + gs1.length + 1, hv2, by omega, by omega,
      by omega, ?_, ?_, ?_, ?_⟩
    · intro k hk
      rw [hdp2 k (by omega), hdp1 k hk]
    · intro i j k hk
      rw [hwp2 i j k (by omega), hwp1 i j k hk]
    · rw [hd2, hdp1 w hw_lt]
      exact max_le hw_d hd1
    · intro i j
      rw [hw2 i j, hwp1 i j w hw_lt, hw1 i j]
      simp

theorem build_row_fn {n m : ℕ} (f : Fin n → ZMod 2) (gs : List Gate) (hv : Valid n m gs) :
    ∃ (gs' : List Gate) (out : ℕ),
      Valid n m gs' ∧ gs.length ≤ gs'.length ∧ out < n + m + gs'.length ∧
      gs'.countP nlGate = gs.countP nlGate ∧
      (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
      (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
        (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
      (depthsOf (n + m) gs').getD out 0 = 0 ∧
      (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD out false) = f i) := by
  let ws : List ℕ := ((List.finRange n).filter (fun k : Fin n => decide (f k = 1))).map Fin.val
  have hwb : ∀ w ∈ ws, w < n + m + gs.length := by
    intro w hw
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hw
    omega
  have hwd : ∀ w ∈ ws, (depthsOf (n + m) gs).getD w 0 ≤ 0 := by
    intro w hw
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hw
    rw [depthsOf_getD_input (n + m) gs (by omega)]
  obtain ⟨gs', out, hv', hle', hout', hcnt', hdp', hwp', hdout', hwout'⟩ :=
    build_xor_list 0 ws gs hv hwb hwd
  refine ⟨gs', out, hv', hle', hout', hcnt', hdp', hwp', by omega, fun i j => ?_⟩
  rw [hwout' i j]
  have hsum : (ws.map (fun w => b2z ((wiresOf (oneEach i j) gs).getD w false))).sum =
      ∑ k : Fin n, if f k = 1 then (if k = i then (1 : ZMod 2) else 0) else 0 := by
    have hmap : ws.map (fun w => b2z ((wiresOf (oneEach i j) gs).getD w false)) =
        ((List.finRange n).filter (fun k : Fin n => decide (f k = 1))).map
          (fun k : Fin n => if k = i then (1 : ZMod 2) else 0) := by
      unfold ws
      rw [List.map_map]
      apply List.map_congr_left
      intro k _
      simp only [Function.comp_apply]
      rw [wiresOf_getD_input _ _ (by rw [oneEach_length]; omega), oneEach_getD_left i j k.isLt]
      by_cases hki : k = i
      · subst hki; simp [b2z]
      · have hne : k.val ≠ i.val := fun e => hki (Fin.ext e)
        simp [b2z, hki, hne]
    rw [hmap]
    have hfilt : ∀ (l : List (Fin n)),
        ((l.filter (fun k => decide (f k = 1))).map (fun k => if k = i then (1 : ZMod 2) else 0)).sum =
        (l.map (fun k => if f k = 1 then (if k = i then (1 : ZMod 2) else 0) else 0)).sum := by
      intro l
      induction l with
      | nil => simp
      | cons a l ihl =>
        rw [List.filter_cons]
        by_cases hfa : f a = 1 <;> simp [hfa, ihl]
    rw [hfilt]
    rw [← Fin.sum_univ_def]
  rw [hsum]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true]
    exact zmod2_ite_eq (f i)
  · intro k _ hki
    simp [hki]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem build_col_fn {n m : ℕ} (g : Fin m → ZMod 2) (gs : List Gate) (hv : Valid n m gs) :
    ∃ (gs' : List Gate) (out : ℕ),
      Valid n m gs' ∧ gs.length ≤ gs'.length ∧ out < n + m + gs'.length ∧
      gs'.countP nlGate = gs.countP nlGate ∧
      (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
      (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
        (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
      (depthsOf (n + m) gs').getD out 0 = 0 ∧
      (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD out false) = g j) := by
  let ws : List ℕ :=
    ((List.finRange m).filter (fun k : Fin m => decide (g k = 1))).map (fun k => n + k.val)
  have hwb : ∀ w ∈ ws, w < n + m + gs.length := by
    intro w hw
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hw
    omega
  have hwd : ∀ w ∈ ws, (depthsOf (n + m) gs).getD w 0 ≤ 0 := by
    intro w hw
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hw
    rw [depthsOf_getD_input (n + m) gs (by omega)]
  obtain ⟨gs', out, hv', hle', hout', hcnt', hdp', hwp', hdout', hwout'⟩ :=
    build_xor_list 0 ws gs hv hwb hwd
  refine ⟨gs', out, hv', hle', hout', hcnt', hdp', hwp', by omega, fun i j => ?_⟩
  rw [hwout' i j]
  have hsum : (ws.map (fun w => b2z ((wiresOf (oneEach i j) gs).getD w false))).sum =
      ∑ k : Fin m, if g k = 1 then (if k = j then (1 : ZMod 2) else 0) else 0 := by
    have hmap : ws.map (fun w => b2z ((wiresOf (oneEach i j) gs).getD w false)) =
        ((List.finRange m).filter (fun k : Fin m => decide (g k = 1))).map
          (fun k : Fin m => if k = j then (1 : ZMod 2) else 0) := by
      unfold ws
      rw [List.map_map]
      apply List.map_congr_left
      intro k _
      simp only [Function.comp_apply]
      rw [wiresOf_getD_input _ _ (by rw [oneEach_length]; omega),
        oneEach_getD_right i j (by omega) (by omega)]
      simp only [Nat.add_sub_cancel_left]
      by_cases hkj : k = j
      · subst hkj; simp [b2z]
      · have hne : k.val ≠ j.val := fun e => hkj (Fin.ext e)
        simp [b2z, hkj, hne]
    rw [hmap]
    have hfilt : ∀ (l : List (Fin m)),
        ((l.filter (fun k => decide (g k = 1))).map (fun k => if k = j then (1 : ZMod 2) else 0)).sum =
        (l.map (fun k => if g k = 1 then (if k = j then (1 : ZMod 2) else 0) else 0)).sum := by
      intro l
      induction l with
      | nil => simp
      | cons a l ihl =>
        rw [List.filter_cons]
        by_cases hga : g a = 1 <;> simp [hga, ihl]
    rw [hfilt]
    rw [← Fin.sum_univ_def]
  rw [hsum]
  rw [Finset.sum_eq_single j]
  · simp only [ite_true]
    exact zmod2_ite_eq (g j)
  · intro k _ hkj
    simp [hkj]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem build_pair_and {n m : ℕ} (a b : Fin n → ZMod 2) (c d : Fin m → ZMod 2)
    (gs : List Gate) (hv : Valid n m gs) :
    ∃ (gs' : List Gate) (out : ℕ),
      Valid n m gs' ∧ gs.length ≤ gs'.length ∧ out < n + m + gs'.length ∧
      gs'.countP nlGate = gs.countP nlGate + 1 ∧
      (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
      (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
        (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
      (depthsOf (n + m) gs').getD out 0 ≤ 1 ∧
      (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD out false) =
        (a i + d j) * (b i + c j)) := by
  obtain ⟨gs1, wa, hv1, hl1, hwa, hc1, hd1, hw1, hda, hfa⟩ := build_row_fn a gs hv
  obtain ⟨gs2, wd, hv2, hl2, hwd, hc2, hd2, hw2, hdd, hfd⟩ := build_col_fn d gs1 hv1
  obtain ⟨hv3, hl3, hc3, hd3, hw3, hdL, hwL⟩ :=
    pushXor_spec hv2 (by omega : wa < n + m + gs2.length) hwd
  set gs3 := pushXor n m gs2 wa wd
  let wL := n + m + gs2.length + 1
  obtain ⟨gs4, wb, hv4, hl4, hwb, hc4, hd4, hw4, hdb, hfb⟩ := build_row_fn b gs3 hv3
  obtain ⟨gs5, wc, hv5, hl5, hwc, hc5, hd5, hw5, hdc, hfc⟩ := build_col_fn c gs4 hv4
  obtain ⟨hv6, hl6, hc6, hd6, hw6, hdR, hwR⟩ :=
    pushXor_spec hv5 (by omega : wb < n + m + gs5.length) hwc
  set gs6 := pushXor n m gs5 wb wc
  let wR := n + m + gs5.length + 1
  obtain ⟨hv7, hl7, hc7, hd7, hw7, hdP, hwP⟩ :=
    pushAnd_spec hv6 (by omega : wL < n + m + gs6.length) (by omega : wR < n + m + gs6.length)
  set gs7 := pushAnd gs6 wL wR
  let out := n + m + gs6.length
  refine ⟨gs7, out, hv7, by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [hd7 k (by omega), hd6 k (by omega), hd5 k (by omega), hd4 k (by omega),
      hd3 k (by omega), hd2 k (by omega), hd1 k hk]
  · intro i j k hk
    rw [hw7 i j k (by omega), hw6 i j k (by omega), hw5 i j k (by omega), hw4 i j k (by omega),
      hw3 i j k (by omega), hw2 i j k (by omega), hw1 i j k hk]
  · rw [hdP]
    have hL0 : (depthsOf (n + m) gs6).getD wL 0 = 0 := by
      rw [hd6 wL (by omega), hd5 wL (by omega), hd4 wL (by omega), hdL, hd2 wa hwa, hda, hdd]
      simp
    have hR0 : (depthsOf (n + m) gs6).getD wR 0 = 0 := by
      rw [hdR, hd5 wb hwb, hdb, hdc]
      simp
    rw [hL0, hR0]
    simp
  · intro i j
    rw [hwP i j]
    have hLv : b2z ((wiresOf (oneEach i j) gs6).getD wL false) = a i + d j := by
      rw [hw6 i j wL (by omega), hw5 i j wL (by omega), hw4 i j wL (by omega),
        hwL i j, hw2 i j wa hwa, hfa i j, hfd i j]
    have hRv : b2z ((wiresOf (oneEach i j) gs6).getD wR false) = b i + c j := by
      rw [hwR i j, hw5 i j wb hwb, hfb i j, hfc i j]
    rw [hLv, hRv]

theorem build_many_pairs {n m : ℕ} (t : ℕ)
    (a b : Fin t → Fin n → ZMod 2) (c d : Fin t → Fin m → ZMod 2)
    (gs : List Gate) (hv : Valid n m gs) :
    ∃ (gs' : List Gate) (ws : List ℕ),
      Valid n m gs' ∧ gs.length ≤ gs'.length ∧
      (∀ w ∈ ws, w < n + m + gs'.length) ∧
      (∀ w ∈ ws, (depthsOf (n + m) gs').getD w 0 ≤ 1) ∧
      gs'.countP nlGate = gs.countP nlGate + t ∧
      (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
      (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
        (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
      (∀ (i : Fin n) (j : Fin m), (ws.map (fun w => b2z ((wiresOf (oneEach i j) gs').getD w false))).sum =
        ∑ p : Fin t, (a p i + d p j) * (b p i + c p j)) := by
  induction t generalizing gs with
  | zero =>
    exact ⟨gs, [], hv, le_rfl, by simp, by simp, by simp, fun _ _ => rfl, fun _ _ _ _ => rfl,
      fun _ _ => by simp⟩
  | succ t ih =>
    obtain ⟨gs1, w0, hv1, hl1, hw0, hc1, hd1, hwp1, hdw0, hfv0⟩ :=
      build_pair_and (a 0) (b 0) (c 0) (d 0) gs hv
    obtain ⟨gs2, ws, hv2, hl2, hws, hdws, hc2, hd2, hwp2, hsum⟩ :=
      ih (fun p => a p.succ) (fun p => b p.succ) (fun p => c p.succ) (fun p => d p.succ) gs1 hv1
    refine ⟨gs2, w0 :: ws, hv2, by omega, ?_, ?_, by omega, ?_, ?_, ?_⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · omega
      · exact hws w hw
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · rw [hd2 w hw0]; exact hdw0
      · exact hdws w hw
    · intro k hk
      rw [hd2 k (by omega), hd1 k hk]
    · intro i j k hk
      rw [hwp2 i j k (by omega), hwp1 i j k hk]
    · intro i j
      rw [List.map_cons, List.sum_cons, hwp2 i j w0 hw0, hfv0 i j, hsum i j, Fin.sum_univ_succ]

theorem dir_ge {n m : ℕ} (G : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m) (t : ℕ)
    (hr : (anchor u v (fun i j => b2z (G i j))).rank ≤ 2 * t) :
    ∃ C : Circuit,
      ((∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ ReadsBack (n + m) C ∧ Represents G C) ∧
      (depthsOf (n + m) C.gates).getD C.output 0 ≤ 1 ∧
      C.gates.countP nlGate ≤ t := by
  obtain ⟨rowVec, colVec, hfac⟩ := factor_of_rank_le (anchor u v (fun i j => b2z (G i j))) hr
  let a : Fin t → Fin n → ZMod 2 := fun p => rowVec ⟨2 * p.val, by omega⟩
  let b : Fin t → Fin n → ZMod 2 := fun p => rowVec ⟨2 * p.val + 1, by omega⟩
  let c : Fin t → Fin m → ZMod 2 := fun p => colVec ⟨2 * p.val, by omega⟩
  let d : Fin t → Fin m → ZMod 2 := fun p => colVec ⟨2 * p.val + 1, by omega⟩
  let R : Fin n → ZMod 2 := fun i => b2z (G i v) + b2z (G u v) + ∑ p : Fin t, a p i * b p i
  let S : Fin m → ZMod 2 := fun j => b2z (G u j) + ∑ p : Fin t, c p j * d p j
  have hdecomp : ∀ i j, b2z (G i j) = R i + S j + ∑ p : Fin t, (a p i + d p j) * (b p i + c p j) := by
    intro i j
    have hA := hfac i j
    have hpair : ∑ k : Fin (2 * t), rowVec k i * colVec k j =
        ∑ p : Fin t, (a p i * c p j + b p i * d p j) := by
      let e : Fin t × Fin 2 ≃ Fin (2 * t) := {
        toFun := fun x => ⟨2 * x.1.val + x.2.val, by omega⟩
        invFun := fun k => (⟨k.val / 2, by omega⟩, ⟨k.val % 2, by omega⟩)
        left_inv := fun ⟨p, q⟩ => by
          ext
          · simp; omega
          · simp; omega
        right_inv := fun k => by
          ext
          simp
          omega
      }
      rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Fin.sum_univ_two]
      rfl
    rw [hpair] at hA
    simp only [anchor] at hA
    have hterm : ∑ p : Fin t, (a p i + d p j) * (b p i + c p j) =
        ∑ p : Fin t, (a p i * b p i + c p j * d p j) +
        ∑ p : Fin t, (a p i * c p j + b p i * d p j) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => by ring
    rw [hterm, ← hA]
    simp only [R, S, Finset.sum_add_distrib]
    have h2 : (b2z (G i v) + b2z (G u v) + ∑ p : Fin t, a p i * b p i) +
        (b2z (G u j) + ∑ p : Fin t, c p j * d p j) +
        ((∑ p : Fin t, a p i * b p i + ∑ p : Fin t, c p j * d p j) +
        (b2z (G i j) + b2z (G i v) + b2z (G u j) + b2z (G u v))) =
        b2z (G i j) + (2 : ZMod 2) * (b2z (G i v) + b2z (G u j) + b2z (G u v) +
          ∑ p : Fin t, a p i * b p i + ∑ p : Fin t, c p j * d p j) := by ring
    rw [h2, zmod2_two, zero_mul, add_zero]
  obtain ⟨gs1, wR, hv1, hl1, hwR, hc1, _, _, hdR, hfR⟩ := build_row_fn R [] (valid_nil n m)
  obtain ⟨gs2, wS, hv2, hl2, hwS, hc2, hd2, hw2, hdS, hfS⟩ := build_col_fn S gs1 hv1
  obtain ⟨gs3, ws, hv3, hl3, hws, hdws, hc3, hd3, hw3, hsum3⟩ :=
    build_many_pairs t a b c d gs2 hv2
  obtain ⟨gs4, out, hv4, hl4, hout, hc4, hd4, hw4, hdout, hwout⟩ :=
    build_xor_list 1 (wR :: wS :: ws) gs3 hv3
      (by
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · omega
        · rcases List.mem_cons.mp hw with rfl | hw
          · omega
          · exact hws w hw)
      (by
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · rw [hd3 w (by omega), hd2 w hwR, hdR]; omega
        · rcases List.mem_cons.mp hw with rfl | hw
          · rw [hd3 w hwS, hdS]; omega
          · exact hdws w hw)
  refine ⟨⟨gs4, out⟩, ⟨hv4.1, hv4.2, ?_⟩, hdout, ?_⟩
  · intro i j
    apply b2z_inj
    change b2z ((wiresOf (oneEach i j) gs4).getD out false) = b2z (G i j)
    rw [hwout i j]
    simp only [List.map_cons, List.sum_cons]
    rw [hw3 i j wR (by omega), hw2 i j wR hwR, hfR i j,
      hw3 i j wS hwS, hfS i j, hsum3 i j, hdecomp i j]
    ring
  · change gs4.countP nlGate ≤ t
    simp only [List.countP_nil] at hc1
    omega

theorem main (n m : ℕ) (G : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m) (t : ℕ) :
    (anchor u v (fun i j => b2z (G i j))).rank ≤ 2 * t ↔
      ∃ C : Circuit,
        ((∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ ReadsBack (n + m) C ∧ Represents G C) ∧
        (depthsOf (n + m) C.gates).getD C.output 0 ≤ 1 ∧
        C.gates.countP nlGate ≤ t :=
  ⟨dir_ge G u v t, fun ⟨C, ⟨hlen, hrb, hrep⟩, hd1, hcnt⟩ => dir_le G u v t C hlen hrb hrep hd1 hcnt⟩

section CircuitTransfer

abbrev Full (a b : ℕ) := Matrix (Fin (a+1)) (Fin (b+1)) (ZMod 2)
abbrev Inner (a b : ℕ) := Matrix (Fin a) (Fin b) (ZMod 2)

private def corner {a b : ℕ} : Full a b →ₗ[ZMod 2] Inner a b where
  toFun A := (anchor 0 0 A).submatrix Fin.succ Fin.succ
  map_add' A B := by
    ext i j
    simp only [Matrix.submatrix_apply, anchor, Matrix.add_apply]
    abel
  map_smul' c A := by
    ext i j
    simp only [Matrix.submatrix_apply, anchor, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

private def zeroBorder {a b : ℕ} : Inner a b →ₗ[ZMod 2] Full a b where
  toFun X := fun i j => Fin.cases 0 (fun i => Fin.cases 0 (X i) j) i
  map_add' X Y := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i
    · change (0 : ZMod 2) = 0 + 0
      rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · change (0 : ZMod 2) = 0 + 0
        rfl
      · rfl
  map_smul' c X := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i
    · change (0 : ZMod 2) = c * 0
      rw [mul_zero]
    · refine Fin.cases ?_ (fun j => ?_) j
      · change (0 : ZMod 2) = c * 0
        rw [mul_zero]
      · rfl

private lemma corner_zeroBorder {a b : ℕ} (X : Inner a b) : corner (zeroBorder X) = X := by
  ext i j
  change X i j + 0 + 0 + 0 = X i j
  simp

private lemma anchor_zero_left {a b : ℕ} (A : Full a b) (j : Fin (b+1)) :
    anchor 0 0 A 0 j = 0 := by
  unfold anchor
  rw [show A 0 j + A 0 0 + A 0 j + A 0 0 = (A 0 j + A 0 j) + (A 0 0 + A 0 0) by abel,
    zmod2_add_self, zmod2_add_self, add_zero]

private lemma anchor_zero_right {a b : ℕ} (A : Full a b) (i : Fin (a+1)) :
    anchor 0 0 A i 0 = 0 := by
  simp [anchor, zmod2_add_self]

private lemma anchor_eq_zeroBorder {a b : ℕ} (A : Full a b) :
    anchor 0 0 A = zeroBorder (corner A) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · exact anchor_zero_left A j
  · refine Fin.cases ?_ (fun j => ?_) j
    · exact anchor_zero_right A i.succ
    · rfl

private lemma zeroBorder_rank {a b : ℕ} (X : Inner a b) : (zeroBorder X).rank = X.rank := by
  apply le_antisymm
  · let L : Matrix (Fin (a+1)) (Fin a) (ZMod 2) := fun i k => if i = k.succ then 1 else 0
    let R : Matrix (Fin b) (Fin (b+1)) (ZMod 2) := fun k j => if j = k.succ then 1 else 0
    have hL (i : Fin a) (j : Fin b) : (L * X) i.succ j = X i j := by
      rw [Matrix.mul_apply]
      simp [L, ite_mul]
    have hzero (j : Fin b) : (L * X) 0 j = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro k _
      simp [L, (Fin.succ_ne_zero k).symm]
    have hfact : zeroBorder X = (L * X) * R := by
      ext i j
      refine Fin.cases ?_ (fun j => ?_) j
      · rw [Matrix.mul_apply]
        have hz : zeroBorder X i 0 = 0 := by
          refine Fin.cases ?_ (fun i => ?_) i <;> rfl
        rw [hz]
        symm
        apply Finset.sum_eq_zero
        intro k _
        simp [R, (Fin.succ_ne_zero k).symm]
      · have hp : ((L * X) * R) i j.succ = (L * X) i j := by
          rw [Matrix.mul_apply]
          simp [R, mul_ite]
        rw [hp]
        refine Fin.cases ?_ (fun i => ?_) i
        · exact (hzero j).symm
        · exact (hL i j).symm
    rw [hfact]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · have h := (zeroBorder X).rank_submatrix_le (Fin.succ : Fin a → Fin (a+1))
        (Fin.succ : Fin b → Fin (b+1))
    exact h

private lemma bit_decide_ne_zero (x : ZMod 2) : b2z (decide (x ≠ 0)) = x := by
  revert x
  decide

private lemma fits_rank {a b t : ℕ} (A : Full a b) :
    (∃ Q : Circuit,
      (∀ g ∈ Q.gates, g.inputs.length ≤ 2) ∧
      ReadsBack (a+1+(b+1)) Q ∧ Represents (fun x y => decide (A x y ≠ 0)) Q ∧
      (depthsOf (a+1+(b+1)) Q.gates).getD Q.output 0 ≤ 1 ∧
      Q.gates.countP nlGate ≤ t) ↔ (corner A).rank ≤ 2*t := by
  have hb : (fun x y => b2z (decide (A x y ≠ 0))) = A := by
    ext x y
    exact bit_decide_ne_zero _
  have h := main (a+1) (b+1) (fun x y => decide (A x y ≠ 0)) 0 0 t
  rw [hb, anchor_eq_zeroBorder, zeroBorder_rank] at h
  constructor
  · rintro ⟨Q, hf, hb, hp, hd, hc⟩
    exact h.mpr ⟨Q, ⟨hf, hb, hp⟩, hd, hc⟩
  · intro hr
    obtain ⟨Q, ⟨hf, hb, hp⟩, hd, hc⟩ := h.mp hr
    exact ⟨Q, hf, hb, hp, hd, hc⟩

end CircuitTransfer


noncomputable section AdaptiveLower

open scoped BigOperators
open Module

private abbrev ALF := ZMod 2
private abbrev ALM (a b : ℕ) := Matrix (Fin a) (Fin b) ALF

/-- A nonempty linear fiber is a translate of the kernel. -/
private def alFiberEquiv {V W : Type*} [AddCommGroup V] [Module ALF V]
    [AddCommGroup W] [Module ALF W] (f : V →ₗ[ALF] W) {y : W}
    (x : V) (hx : f x = y) : {v : V // f v = y} ≃ f.ker where
  toFun v := ⟨v.val - x, LinearMap.mem_ker.mpr (by rw [map_sub, v.property, hx, sub_self])⟩
  invFun k := ⟨k.val + x, by rw [map_add, LinearMap.mem_ker.mp k.property, hx, zero_add]⟩
  left_inv v := Subtype.ext (sub_add_cancel v.val x)
  right_inv k := Subtype.ext (add_sub_cancel_right k.val x)

private theorem alFieldCard : Nat.card ALF = 2 := by
  rw [Nat.card_eq_fintype_card, ZMod.card]

private theorem alCard {V : Type*} [AddCommGroup V] [Module ALF V] [Module.Finite ALF V] :
    Nat.card V = 2 ^ finrank ALF V := by
  rw [Module.natCard_eq_pow_finrank (K := ALF), alFieldCard]

private def alRank {V : Type*} [AddCommGroup V] [Module ALF V] {b : ℕ}
    (v : Fin b → V) : ℕ := finrank ALF (Submodule.span ALF (Set.range v))

private def alCount (a b r : ℕ) : ℕ :=
  Nat.card {v : Fin b → Fin a → ALF // r < alRank v}

private theorem alCount_matrix (a b r : ℕ) :
    Nat.card {X : ALM a b // r < X.rank} = alCount a b r := by
  apply Nat.card_congr
  exact Equiv.subtypeEquiv (Matrix.colEquiv (Fin a) (Fin b) ALF) fun X => by
    rw [Matrix.rank_eq_finrank_span_cols] <;> rfl

private theorem alCount_zero_of_width_le {a b r : ℕ} (h : b ≤ r) : alCount a b r = 0 := by
  rw [← alCount_matrix]
  exact Nat.card_eq_zero.mpr (Or.inl ⟨fun X => (not_lt_of_ge (X.val.rank_le_width.trans h)) X.property⟩)

private theorem alRank_eq_zero_iff {a b : ℕ} (v : Fin b → Fin a → ALF) :
    alRank v = 0 ↔ v = 0 := by
  unfold alRank
  rw [Submodule.finrank_eq_zero]
  constructor
  · intro h
    funext j
    have hj := Submodule.subset_span (R := ALF) (Set.mem_range_self j : v j ∈ Set.range v)
    rw [h] at hj
    change v j ∈ (⊥ : Submodule ALF (Fin a → ALF)) at hj
    exact (Submodule.mem_bot (R := ALF)).mp hj
  · intro h
    subst v
    apply le_antisymm _ bot_le
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact Submodule.zero_mem _

private theorem alNatCard_ne_zero {V : Type*} [Finite V] [Zero V] :
    Nat.card {v : V // v ≠ 0} = Nat.card V - 1 := by
  classical
  letI := Fintype.ofFinite V
  simp only [Nat.card_eq_fintype_card, ne_eq, Fintype.card_subtype_compl, Fintype.card_subtype_eq]

private theorem alCount_rank_zero (a b : ℕ) : alCount a b 0 = 2 ^ (a * b) - 1 := by
  unfold alCount
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun v =>
    Nat.pos_iff_ne_zero.trans (not_congr (alRank_eq_zero_iff v)))), alNatCard_ne_zero]
  rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin, alFieldCard, ← pow_mul]

private theorem alRank_cons_zero {V : Type*} [AddCommGroup V] [Module ALF V] {b : ℕ}
    (w : Fin b → V) : alRank (Fin.cons 0 w) = alRank w := by
  rw [alRank, Fin.range_cons, Submodule.span_insert_zero] <;> rfl

/-- Modulo the first nonzero column, the column space loses one dimension. -/
private theorem alRank_cons_quot {V : Type*} [AddCommGroup V] [Module ALF V]
    [Module.Finite ALF V] {b : ℕ} {v : V} (hv : v ≠ 0) (w : Fin b → V) :
    alRank (Fin.cons v w) = alRank (fun j => (Submodule.span ALF {v}).mkQ (w j)) + 1 := by
  let p := Submodule.span ALF ({v} : Set V)
  let s := Submodule.span ALF (Set.range (Fin.cons v w))
  have hs : s = p ⊔ Submodule.span ALF (Set.range w) := by
    dsimp [s, p]
    rw [Fin.range_cons, Submodule.span_insert]
  have hp : p ≤ s := hs.symm ▸ le_sup_left
  have hker : (p.mkQ.domRestrict s).ker = p.submoduleOf s := by
    rw [LinearMap.ker_domRestrict, Submodule.ker_mkQ, Submodule.submoduleOf]
  have hrankKer : finrank ALF (p.mkQ.domRestrict s).ker = 1 := by
    rw [hker, (Submodule.submoduleOfEquivOfLe hp).finrank_eq, finrank_span_singleton hv]
  have hrankRange : finrank ALF (LinearMap.range (p.mkQ.domRestrict s)) =
      alRank (fun j => p.mkQ (w j)) := by
    rw [LinearMap.range_domRestrict, hs, Submodule.map_sup, p.mkQ_map_self, bot_sup_eq,
      Submodule.map_span, alRank, Set.range_comp' (fun x => p.mkQ x) w]
  have h := (p.mkQ.domRestrict s).finrank_range_add_finrank_ker
  rw [hrankKer, hrankRange] at h
  exact h.symm

private theorem alRank_postcompose {V W : Type*} [AddCommGroup V] [Module ALF V]
    [AddCommGroup W] [Module ALF W] {b : ℕ} (e : V ≃ₗ[ALF] W) (w : Fin b → V) :
    alRank w = alRank (fun j => e (w j)) := by
  unfold alRank
  rw [Set.range_comp' (fun x => e x) w]
  change _ = Module.finrank ALF
    (Submodule.span ALF ((e : V →ₗ[ALF] W) '' Set.range w))
  rw [← Submodule.map_span, e.finrank_map_eq]

/-- Count the tails above a fixed nonzero first column. -/
private theorem alCount_nonzero_column (a b r : ℕ) (v : Fin (a + 1) → ALF) (hv : v ≠ 0) :
    Nat.card {w : Fin b → Fin (a + 1) → ALF // r + 1 < alRank (Fin.cons v w)} =
      2 ^ b * alCount a b r := by
  classical
  let V := Fin (a + 1) → ALF
  let p : Submodule ALF V := Submodule.span ALF {v}
  have hp : finrank ALF p = 1 := finrank_span_singleton hv
  have hV : finrank ALF V = a + 1 := by simp [V, Module.finrank_fintype_fun_eq_card]
  have hQ := p.finrank_quotient_add_finrank
  rw [hp, hV] at hQ
  let e : (V ⧸ p) ≃ₗ[ALF] (Fin a → ALF) :=
    LinearEquiv.ofFinrankEq (V ⧸ p) (Fin a → ALF) (by
      have h : finrank ALF (V ⧸ p) = a := by omega
      rw [h, Module.finrank_fin_fun])
  let f : V →ₗ[ALF] (Fin a → ALF) := e.toLinearMap.comp p.mkQ
  have hf : Function.Surjective f := e.surjective.comp p.mkQ_surjective
  have hk : f.ker = p := by
    ext x
    change e (p.mkQ x) = 0 ↔ x ∈ p
    rw [← e.map_zero, e.injective.eq_iff]
    exact (LinearMap.mem_ker (f := p.mkQ)).symm.trans (by rw [p.ker_mkQ])
  let g : (Fin b → V) → (Fin b → Fin a → ALF) := fun w j => f (w j)
  have hr (w : Fin b → V) :
      r + 1 < alRank (Fin.cons v w) ↔ r < alRank (g w) := by
    rw [alRank_cons_quot hv, alRank_postcompose e]
    exact Nat.add_lt_add_iff_right
  let lift (y : Fin a → ALF) := Classical.choose (hf y)
  have hlift (y : Fin a → ALF) : f (lift y) = y := Classical.choose_spec (hf y)
  have cardFiber (y : {w : Fin b → Fin a → ALF // r < alRank w}) :
      Nat.card {w : Fin b → V // g w = y.val} = 2 ^ b := by
    let E : {w : Fin b → V // g w = y.val} ≃ (∀ j : Fin b, {x : V // f x = y.val j}) := {
      toFun := fun w j => ⟨w.val j, congrFun w.property j⟩
      invFun := fun w => ⟨fun j => (w j).val, funext fun j => (w j).property⟩
      left_inv := fun w => Subtype.ext (by funext j; rfl)
      right_inv := fun w => funext fun j => Subtype.ext rfl }
    rw [Nat.card_congr (E.trans (Equiv.piCongrRight fun j => alFiberEquiv f _ (hlift (y.val j)))),
      Nat.card_fun, alCard (V := f.ker), hk, hp, pow_one, Nat.card_fin]
  let E := Equiv.sigmaSubtypeFiberEquivSubtype
    (p := fun w => r + 1 < alRank (Fin.cons v w)) (q := fun w => r < alRank w) g hr
  rw [← Nat.card_congr E, Nat.card_sigma]
  simp only [cardFiber, Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
  rw [mul_comm, ← Nat.card_eq_fintype_card] <;> rfl

private theorem alCount_succ (a b r : ℕ) :
    alCount (a + 1) (b + 1) (r + 1) =
      alCount (a + 1) b (r + 1) + (2 ^ (a + 1) - 1) * 2 ^ b * alCount a b r := by
  classical
  let V := Fin (a + 1) → ALF
  let p (v : V) (w : Fin b → V) := r + 1 < alRank (Fin.cons v w)
  let E : V × (Fin b → V) ≃ (Fin (b + 1) → V) := {
    toFun := fun vw => Fin.cons vw.1 vw.2
    invFun := fun x => (x 0, Fin.tail x)
    left_inv := by intro x; simp
    right_inv := by intro x; exact Fin.cons_self_tail x }
  have h : (Σ v : V, {w : Fin b → V // p v w}) ≃
      {x : Fin (b + 1) → V // r + 1 < alRank x} :=
    (Equiv.subtypeProdEquivSigmaSubtype (fun v w => p v w)).symm.trans
      (E.subtypeEquiv fun _ => Iff.rfl)
  have hz : Nat.card {w : Fin b → V // p 0 w} = alCount (a + 1) b (r + 1) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun w => by dsimp [p]; rw [alRank_cons_zero])
  have hnz (v : V) (hv : v ≠ 0) : Nat.card {w : Fin b → V // p v w} =
      2 ^ b * alCount a b r := alCount_nonzero_column a b r v hv
  unfold alCount at ⊢
  rw [← Nat.card_congr h, Nat.card_sigma, ← Fintype.sum_subtype_add_sum_subtype (fun v : V => v = 0)]
  have hf₀ (v : {v : V // v = 0}) : Nat.card {w : Fin b → V // p v.val w} =
      alCount (a + 1) b (r + 1) := v.property.symm ▸ hz
  have hf₁ (v : {v : V // v ≠ 0}) : Nat.card {w : Fin b → V // p v.val w} =
      2 ^ b * alCount a b r := hnz v.val v.property
  have hcard : Nat.card V = 2 ^ (a + 1) := by
    change Nat.card (Fin (a + 1) → ALF) = _
    rw [Nat.card_fun, Nat.card_fin, alFieldCard]
  simp only [hf₀, hf₁, Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul,
    Fintype.card_subtype_eq, one_mul]
  simp only [← Nat.card_eq_fintype_card, alNatCard_ne_zero, hcard, mul_assoc] <;> rfl

private theorem alOdd_pow_sub_one {n : ℕ} (hn : 0 < n) : Odd (2 ^ n - 1 : ℕ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hp : 0 < (2 : ℕ) ^ k := pow_pos (by decide) _
  rw [Nat.odd_iff, pow_succ]
  omega

/-- The rejecting count is a power of two times an odd integer. -/
private theorem alCount_odd_factor (a b r : ℕ) (ha : r < a) (hb : r < b) :
    ∃ q : ℕ, Odd q ∧ alCount a b r = 2 ^ Nat.choose (r + 1) 2 * q := by
  induction b generalizing a r with
  | zero => omega
  | succ b ih =>
    cases r with
    | zero =>
      rw [alCount_rank_zero]
      exact ⟨2 ^ (a * (b + 1)) - 1, alOdd_pow_sub_one (Nat.mul_pos ha (Nat.succ_pos b)),
        by simp [Nat.choose]⟩
    | succ r =>
      cases a with
      | zero => omega
      | succ a =>
        have ha' : r < a := by omega
        have hb' : r < b := by omega
        obtain ⟨q, hq, hqeq⟩ := ih a r ha' hb'
        have hchoose : Nat.choose (r + 1 + 1) 2 = (r + 1) + Nat.choose (r + 1) 2 := by
          rw [show 2 = 1 + 1 by decide, Nat.choose_succ_succ', Nat.choose_one_right]
        rw [alCount_succ, hqeq, hchoose]
        have hvOdd : Odd ((2 ^ (a + 1) - 1) * q) :=
          (alOdd_pow_sub_one (Nat.succ_pos a)).mul hq
        by_cases heq : b = r + 1
        · rw [alCount_zero_of_width_le (heq.le), zero_add, heq]
          exact ⟨_, hvOdd, by rw [pow_add (2 : ℕ) (r + 1) (Nat.choose (r + 1) 2)]; ac_rfl⟩
        · have hlt : r + 1 < b := by omega
          obtain ⟨q', hq', hq'eq⟩ := ih (a + 1) (r + 1) ha hlt
          have hsplit : (2 : ℕ) ^ b = 2 ^ (r + 1) * 2 ^ (b - (r + 1)) := by
            conv_lhs =>
              rw [show b = (r + 1) + (b - (r + 1)) by omega, pow_add]
          have heven : Even (2 ^ (b - (r + 1)) * ((2 ^ (a + 1) - 1) * q) : ℕ) := by
            rw [even_iff_two_dvd]
            apply dvd_mul_of_dvd_left
            simpa only [pow_one] using
              (Nat.pow_dvd_pow 2 (show 1 ≤ b - (r + 1) by omega))
          rw [hq'eq, hchoose]
          refine ⟨q' + 2 ^ (b - (r + 1)) * ((2 ^ (a + 1) - 1) * q), heven.odd_add hq', ?_⟩
          simp only [hsplit, pow_add (2 : ℕ) (r + 1) (Nat.choose (r + 1) 2), mul_add]
          ac_rfl

/-- Determinism gives exactly one reachable transcript for each matrix. -/
private theorem alTranscript_existsUnique {a b d : ℕ}
    (ask : (i : Fin d) → (Fin i.val → ALF) → ALM a b →ₗ[ALF] ALF) (X : ALM a b) :
    ∃! z : Fin d → ALF,
      ∀ i, ask i (fun j => z ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) X = z i := by
  let wf := (measure (fun i : Fin d => i.val)).wf
  let step (i : Fin d) (prev : ∀ j : Fin d, j.val < i.val → ALF) : ALF :=
    ask i (fun j => prev ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩ j.isLt) X
  let z := wf.fix step
  have hz (i : Fin d) : ask i (fun j => z ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) X = z i := by
    exact (WellFounded.fix_eq wf step i).symm
  refine ⟨z, hz, fun y hy => ?_⟩
  funext i
  induction i using wf.induction with
  | h i ih =>
    rw [← hy i, ← hz i]
    apply congrArg (fun u : Fin i.val → ALF => ask i u X)
    funext j
    exact ih ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩ j.isLt

private theorem alCount_dvd_of_protocol {a b d r : ℕ}
    (ask : (i : Fin d) → (Fin i.val → ALF) → ALM a b →ₗ[ALF] ALF)
    (out : (Fin d → ALF) → Bool)
    (h : ∀ (X : ALM a b) (z : Fin d → ALF),
      (∀ i, ask i (fun j => z ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) X = z i) →
        (out z = true ↔ X.rank ≤ r)) :
    (2 : ℕ) ^ (a * b - d) ∣ alCount a b r := by
  classical
  let tr (X : ALM a b) := Classical.choose (alTranscript_existsUnique ask X)
  have ht (X : ALM a b) :
      ∀ i, ask i (fun j => tr X ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) X = tr X i :=
    (Classical.choose_spec (alTranscript_existsUnique ask X)).1
  have hu (X : ALM a b) (z : Fin d → ALF)
      (hz : ∀ i, ask i (fun j => z ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) X = z i) :
      z = tr X := (Classical.choose_spec (alTranscript_existsUnique ask X)).2 z hz
  have hr (X : ALM a b) : r < X.rank ↔ out (tr X) ≠ true :=
    lt_iff_not_ge.trans (not_congr (h X (tr X) (ht X))).symm
  let E := Equiv.sigmaSubtypeFiberEquivSubtype
    (p := fun X => r < X.rank) (q := fun z => out z ≠ true) tr hr
  rw [← alCount_matrix, ← Nat.card_congr E, Nat.card_sigma]
  apply Finset.dvd_sum
  intro z _
  let L : ALM a b →ₗ[ALF] (Fin d → ALF) :=
    LinearMap.pi fun i => ask i (fun j => z.val ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩)
  have hL (X : ALM a b) : tr X = z.val ↔ L X = z.val := by
    constructor
    · intro hx
      have hx' := ht X
      rw [hx] at hx'
      exact funext hx'
    · intro hx
      exact (hu X z.val (congrFun hx)).symm
  rw [Nat.card_congr (Equiv.subtypeEquivRight hL)]
  by_cases hz : ∃ X, L X = z.val
  · obtain ⟨X, hX⟩ := hz
    rw [Nat.card_congr (alFiberEquiv L X hX), alCard (V := L.ker)]
    have hdim := L.finrank_range_add_finrank_ker
    have hdimL : finrank ALF (LinearMap.range L) ≤ d := by
      simpa [Module.finrank_fintype_fun_eq_card] using (LinearMap.range L).finrank_le
    have hdimM : finrank ALF (ALM a b) = a * b := by simp [Module.finrank_matrix, ALM]
    exact Nat.pow_dvd_pow 2 (by omega)
  · have hempty : IsEmpty {X : ALM a b // L X = z.val} := ⟨fun X => hz ⟨X.val, X.property⟩⟩
    rw [Nat.card_eq_zero.mpr (Or.inl hempty)]
    exact dvd_zero _

/-- Any adaptive linear-query protocol for a rank threshold has the stated depth lower bound. -/
theorem adaptive_rank_lower (a b r d : ℕ)
    (h : ∃ (ask : (i : Fin d) → (Fin i.val → ZMod 2) →
        Matrix (Fin a) (Fin b) (ZMod 2) →ₗ[ZMod 2] ZMod 2)
        (out : (Fin d → ZMod 2) → Bool),
      ∀ (X : Matrix (Fin a) (Fin b) (ZMod 2)) (z : Fin d → ZMod 2),
        (∀ i, ask i (fun j => z ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) X = z i) →
          (out z = true ↔ X.rank ≤ r)) :
    min a b ≤ r ∨ a * b - Nat.choose (r + 1) 2 ≤ d := by
  by_cases hmin : min a b ≤ r
  · exact Or.inl hmin
  · refine Or.inr ?_
    obtain ⟨ask, out, hp⟩ := h
    have hdvd := alCount_dvd_of_protocol ask out hp
    have ha : r < a := lt_of_lt_of_le (Nat.lt_of_not_ge hmin) (min_le_left _ _)
    have hb : r < b := lt_of_lt_of_le (Nat.lt_of_not_ge hmin) (min_le_right _ _)
    obtain ⟨q, hq, heq⟩ := alCount_odd_factor a b r ha hb
    by_contra hlt
    let c := Nat.choose (r + 1) 2
    have hc : c + 1 ≤ a * b - d := by dsimp [c]; omega
    have hd : (2 : ℕ) ^ (c + 1) ∣ 2 ^ c * q :=
      (Nat.pow_dvd_pow 2 hc).trans (heq ▸ hdvd)
    rw [pow_succ, Nat.mul_dvd_mul_iff_left (pow_pos (by decide : 0 < (2 : ℕ)) _)] at hd
    exact (Nat.not_even_iff_odd.mpr hq) (even_iff_two_dvd.mpr hd)

end AdaptiveLower


section Batch

private abbrev BatchMatrix (a b : ℕ) := Matrix (Fin a) (Fin b) (ZMod 2)

private def batchPeriod {a b : ℕ} (r : ℕ) (D : BatchMatrix a b) : Prop :=
  ∀ A : BatchMatrix a b, A.rank ≤ r ↔ (A + D).rank ≤ r

private theorem batchPeriod_sub {a b r : ℕ} {D E : BatchMatrix a b}
    (hD : batchPeriod r D) (hE : batchPeriod r E) : batchPeriod r (D - E) := by
  intro A
  have he : (A + (D - E)) + E = A + D := by abel
  have h := hE (A + (D - E))
  rw [he] at h
  exact (hD A).trans h.symm

private theorem batchPeriod_mul_left {a b r : ℕ} {D : BatchMatrix a b}
    (hD : batchPeriod r D) (i j : Fin a) (hij : i ≠ j) :
    batchPeriod r (Matrix.transvection i j (1 : ZMod 2) * D) := by
  let T : BatchMatrix a a := Matrix.transvection i j 1
  let U : BatchMatrix a a := Matrix.transvection i j (-1)
  have hTU : T * U = 1 := by
    simp only [T, U, Matrix.transvection_mul_transvection_same i j hij, add_neg_cancel,
      Matrix.transvection_zero]
  have hrank (A : BatchMatrix a b) : (T * A).rank = A.rank :=
    Matrix.rank_mul_eq_right_of_det_ne_zero _ _ (by simp [T, hij])
  intro A
  change A.rank ≤ r ↔ (A + T * D).rank ≤ r
  have hpre : T * (U * A) = A := by rw [← Matrix.mul_assoc, hTU, Matrix.one_mul]
  have hpost : T * (U * A + D) = A + T * D := by rw [Matrix.mul_add, hpre]
  have h := hD (U * A)
  rwa [← hrank (U * A), ← hrank (U * A + D), hpre, hpost] at h

private theorem batchPeriod_mul_right {a b r : ℕ} {D : BatchMatrix a b}
    (hD : batchPeriod r D) (i j : Fin b) (hij : i ≠ j) :
    batchPeriod r (D * Matrix.transvection i j (1 : ZMod 2)) := by
  let T : BatchMatrix b b := Matrix.transvection i j 1
  let U : BatchMatrix b b := Matrix.transvection i j (-1)
  have hUT : U * T = 1 := by
    simp only [T, U, Matrix.transvection_mul_transvection_same i j hij,
      neg_add_cancel, Matrix.transvection_zero]
  have hrank (A : BatchMatrix a b) : (A * T).rank = A.rank :=
    Matrix.rank_mul_eq_left_of_det_ne_zero _ _ (by simp [T, hij])
  intro A
  change A.rank ≤ r ↔ (A + D * T).rank ≤ r
  have hpre : (A * U) * T = A := by rw [Matrix.mul_assoc, hUT, Matrix.mul_one]
  have hpost : (A * U + D) * T = A + D * T := by rw [Matrix.add_mul, hpre]
  have h := hD (A * U)
  rwa [← hrank (A * U), ← hrank (A * U + D), hpre, hpost] at h

private theorem batchEmbeddingLast {r n : ℕ} (h : r < n) (i : Fin n) :
    ∃ p : Fin (r + 1) ↪ Fin n, p (Fin.last r) = i := by
  let f : Fin (r + 1) ↪ Fin n := Fin.castLEEmb h
  let g := Equiv.swap (f (Fin.last r)) i
  refine ⟨f.trans g.toEmbedding, ?_⟩
  exact Equiv.swap_apply_left _ _

private theorem batchSingleNotPeriod {a b r : ℕ} (ha : r < a) (hb : r < b)
    (i : Fin a) (j : Fin b) (c : ZMod 2) (hc : c ≠ 0) :
    ¬batchPeriod r (Matrix.single i j c) := by
  classical
  obtain ⟨p, hpi⟩ := batchEmbeddingLast ha i
  obtain ⟨q, hqj⟩ := batchEmbeddingLast hb j
  let X : BatchMatrix a b := Matrix.of fun u v =>
    if ∃ k : Fin r, u = p k.castSucc ∧ v = q k.castSucc then 1 else 0
  let rows : Finset (Fin a) := Finset.univ.map (Fin.castSuccEmb.trans p)
  have hrows : Function.support X.row ⊆ (↑rows : Set (Fin a)) := by
    intro u hu
    change X u ≠ 0 at hu
    change u ∈ rows
    by_contra hn
    apply hu
    funext v
    change (if ∃ k : Fin r, u = p k.castSucc ∧ v = q k.castSucc then 1 else 0) = 0
    apply ite_eq_right
    rintro ⟨k, hk, _⟩
    exact hn (Finset.mem_map.mpr ⟨k, Finset.mem_univ _, hk.symm⟩)
  have hX : X.rank ≤ r := by
    simpa [rows] using X.rank_le_card_of_support_subset rows hrows
  let w : Fin (r + 1) → ZMod 2 := fun k => if k = Fin.last r then c else 1
  have hsub : (X + Matrix.single i j c).submatrix p q = Matrix.diagonal w := by
    apply Matrix.ext
    intro u v
    change X (p u) (q v) + Matrix.single i j c (p u) (q v) = _
    rw [← hpi, ← hqj]
    simp only [X, Matrix.of_apply, Matrix.single_apply, p.injective.eq_iff, q.injective.eq_iff]
    by_cases huv : u = v
    · subst v
      by_cases hu : u = Fin.last r
      · subst u
        have hnone : ¬∃ k : Fin r, Fin.last r = k.castSucc ∧ Fin.last r = k.castSucc :=
          fun ⟨k, hk, _⟩ => Fin.castSucc_ne_last k hk.symm
        rw [ite_eq_right hnone]
        simp [w]
      · obtain ⟨k, hk⟩ := Fin.eq_castSucc_of_ne_last hu
        have hex : ∃ k : Fin r, u = k.castSucc ∧ u = k.castSucc := ⟨k, hk.symm, hk.symm⟩
        rw [ite_eq_left hex]
        simp [w, hu, Ne.symm hu]
    · have hnone : ¬∃ k : Fin r, u = k.castSucc ∧ v = k.castSucc :=
        fun ⟨_, hu, hv⟩ => huv (hu.trans hv.symm)
      have hshift : ¬(Fin.last r = u ∧ Fin.last r = v) :=
        fun ⟨hu, hv⟩ => huv (hu.symm.trans hv)
      simp [hnone, hshift, Matrix.diagonal_apply_ne _ huv]
  have hdet : (Matrix.diagonal w).det ≠ 0 := by
    rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    intro k _
    by_cases hk : k = Fin.last r <;> simp [w, hk, hc]
  have hlarge : r + 1 ≤ (X + Matrix.single i j c).rank := by
    have h := (X + Matrix.single i j c).rank_submatrix_le p q
    rw [hsub, Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin] at h
    exact h
  intro hp
  have hsmall := (hp X).mp hX
  omega

private theorem batchOtherIndex {n : ℕ} (hn : 1 < n) (i : Fin n) :
    ∃ j : Fin n, j ≠ i := by
  let z : Fin n := ⟨0, by omega⟩
  by_cases hz : z = i
  · refine ⟨⟨1, hn⟩, ?_⟩
    intro h
    have hv := congrArg Fin.val (h.trans hz.symm)
    change 1 = 0 at hv
    omega
  · exact ⟨z, hz⟩

private theorem batchNoPeriod {a b r : ℕ} (hr : r < min a b) {D : BatchMatrix a b}
    (hD : D ≠ 0) : ¬batchPeriod r D := by
  classical
  obtain ⟨i, j, hentry⟩ : ∃ i j, D i j ≠ 0 := by
    by_contra! h
    exact hD (Matrix.ext fun i j => by simpa using h i j)
  intro hper
  have ha : r < a := hr.trans_le (min_le_left _ _)
  have hb : r < b := hr.trans_le (min_le_right _ _)
  by_cases hzero : r = 0
  · subst r
    have hD0 : D.rank ≤ 0 := by simpa using (hper 0).mp (by simp)
    let w : Fin 1 → ZMod 2 := fun _ => D i j
    have hminor : D.submatrix (fun _ : Fin 1 => i) (fun _ : Fin 1 => j) =
        Matrix.diagonal w := by
      apply Matrix.ext
      intro u v
      have huv : u = v := Subsingleton.elim _ _
      subst v
      simp [w]
    have hdet : (Matrix.diagonal w).det ≠ 0 := by
      rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
      exact fun _ _ => hentry
    have h := D.rank_submatrix_le (fun _ : Fin 1 => i) (fun _ : Fin 1 => j)
    rw [hminor, Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin] at h
    omega
  · obtain ⟨k, hk⟩ := batchOtherIndex (show 1 < a by omega) i
    obtain ⟨l, hl⟩ := batchOtherIndex (show 1 < b by omega) j
    let H := Matrix.transvection k i (1 : ZMod 2) * D - D
    have hH : batchPeriod r H := batchPeriod_sub (batchPeriod_mul_left hper k i hk) hper
    have hHentry (u : Fin a) (v : Fin b) : H u v = if u = k then D i v else 0 := by
      by_cases hu : u = k
      · subst u
        simp [H, Matrix.sub_apply]
      · simp [H, Matrix.sub_apply, hu]
    let K := H * Matrix.transvection j l (1 : ZMod 2) - H
    have hK : batchPeriod r K := batchPeriod_sub (batchPeriod_mul_right hH j l hl.symm) hH
    have hKentry (u : Fin a) (v : Fin b) : K u v = if v = l then H u j else 0 := by
      by_cases hv : v = l
      · subst v
        simp [K, Matrix.sub_apply]
      · simp [K, Matrix.sub_apply, hv]
    have hsingle : K = Matrix.single k l (D i j) := by
      apply Matrix.ext
      intro u v
      rw [hKentry, hHentry, Matrix.single_apply]
      by_cases hu : u = k
      · subst u
        by_cases hv : v = l
        · subst v
          simp
        · simp [hv, Ne.symm hv]
      · simp [hu, Ne.symm hu]
    exact batchSingleNotPeriod ha hb k l _ hentry (hsingle ▸ hK)

private theorem batchCommonReport {d e : ℕ} (u v : Fin d → ZMod 2)
    (h : hammingDist u v ≤ 2 * e) :
    ∃ z : Fin d → ZMod 2, hammingDist z u ≤ e ∧ hammingDist z v ≤ e := by
  classical
  let D := Finset.univ.filter (fun j => u j ≠ v j)
  change D.card ≤ 2 * e at h
  obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq (s := D) (min_le_left D.card e)
  let z : Fin d → ZMod 2 := fun j => if j ∈ S then v j else u j
  have hzu : Finset.univ.filter (fun j => z j ≠ u j) = S := by
    ext j
    by_cases hj : j ∈ S
    · have hne : u j ≠ v j := (Finset.mem_filter.mp (hS hj)).2
      simp [z, hj, hne.symm]
    · simp [z, hj]
  have hzv : Finset.univ.filter (fun j => z j ≠ v j) = D \ S := by
    ext j
    by_cases hj : j ∈ S <;> simp [D, z, hj]
  refine ⟨z, ?_, ?_⟩
  · unfold hammingDist
    rw [hzu, hScard]
    exact min_le_right _ _
  · unfold hammingDist
    rw [hzv, Finset.card_sdiff_of_subset hS, hScard]
    by_cases he : D.card ≤ e
    · rw [min_eq_left he]
      omega
    · rw [min_eq_right (by omega)]
      omega

private theorem batchNormSub {d : ℕ} (u v : Fin d → ZMod 2) :
    hammingNorm (u - v) = hammingDist u v := by
  simp [hammingNorm, hammingDist, Pi.sub_apply, sub_eq_zero]

/-- Batch recognition of a nontrivial rank threshold needs exactly an error-correcting code. -/
theorem batchIff (a b r d e : ℕ) :
    (∃ (ask : Matrix (Fin a) (Fin b) (ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2))
       (out : (Fin d → ZMod 2) → Bool), ∀ (A : Matrix (Fin a) (Fin b) (ZMod 2))
       (z : Fin d → ZMod 2),
         (Finset.univ.filter (fun j => z j ≠ ask A j)).card ≤ e →
           (out z = true ↔ A.rank ≤ r)) ↔
      min a b ≤ r ∨
        (∃ C : Matrix (Fin a) (Fin b) (ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2),
          ∀ X, X ≠ 0 → 2 * e + 1 ≤ (Finset.univ.filter (fun j => C X j ≠ 0)).card) := by
  classical
  constructor
  · rintro ⟨ask, out, hout⟩
    by_cases hr : min a b ≤ r
    · exact Or.inl hr
    · right
      refine ⟨ask, fun D hD => ?_⟩
      change 2 * e + 1 ≤ hammingNorm (ask D)
      by_contra hnorm
      apply batchNoPeriod (Nat.lt_of_not_ge hr) hD
      intro A
      have hdist : hammingDist (ask A) (ask (A + D)) ≤ 2 * e := by
        rw [hammingDist_comm, ← batchNormSub, ← map_sub]
        have hs : A + D - A = D := by abel
        rw [hs]
        omega
      obtain ⟨z, hz₁, hz₂⟩ := batchCommonReport (ask A) (ask (A + D)) hdist
      exact (hout A z hz₁).symm.trans (hout (A + D) z hz₂)
  · rintro (hr | ⟨C, hC⟩)
    · refine ⟨0, fun _ => true, fun A _ _ => ⟨fun _ => ?_, fun _ => rfl⟩⟩
      exact (le_min A.rank_le_height A.rank_le_width).trans hr
    · refine ⟨C, fun z => decide (∃ X : BatchMatrix a b,
        hammingDist z (C X) ≤ e ∧ X.rank ≤ r), ?_⟩
      intro A z hz
      change hammingDist z (C A) ≤ e at hz
      simp only [decide_eq_true_eq]
      constructor
      · rintro ⟨Y, hy, hYr⟩
        have heq : A = Y := by
          by_contra hne
          have hlarge := hC (A - Y) (sub_ne_zero.mpr hne)
          change 2 * e + 1 ≤ hammingNorm (C (A - Y)) at hlarge
          rw [map_sub, batchNormSub] at hlarge
          have ht := hammingDist_triangle_left (C A) (C Y) z
          omega
        rwa [heq]
      · exact fun hA => ⟨A, hz, hA⟩

end Batch


private abbrev UpperF := ZMod 2
private abbrev UpperM (a b : ℕ) := Matrix (Fin a) (Fin b) UpperF

private def upperPast {d : ℕ} (z : Fin d → UpperF) (i : Fin d) (j : Fin i.val) : UpperF :=
  z ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩

private abbrev UpperAsk (M : Type) [AddCommMonoid M] [Module UpperF M] (d : ℕ) :=
  (i : Fin d) → (Fin i.val → UpperF) → M →ₗ[UpperF] UpperF

private abbrev UpperPlan (M : Type) [AddCommMonoid M] [Module UpperF M]
    (d : ℕ) (P : M → Prop) :=
  { p : UpperAsk M d × ((Fin d → UpperF) → Bool) //
    ∀ X z, (∀ i, p.1 i (upperPast z i) X = z i) → (p.2 z = true ↔ P X) }

section AdaptiveUpperProtocol

variable {M N : Type} [AddCommMonoid M] [Module UpperF M]
  [AddCommMonoid N] [Module UpperF N]

private def UpperPlan.ask {d : ℕ} {P : M → Prop} (p : UpperPlan M d P) : UpperAsk M d := p.1.1

private def UpperPlan.out {d : ℕ} {P : M → Prop} (p : UpperPlan M d P) :
    (Fin d → UpperF) → Bool := p.1.2

private theorem UpperPlan.correct {d : ℕ} {P : M → Prop} (p : UpperPlan M d P) :
    ∀ X z, (∀ i, p.ask i (upperPast z i) X = z i) → (p.out z = true ↔ P X) :=
  p.2

private def upperMake {d : ℕ} {P : M → Prop} (ask : UpperAsk M d) (out : (Fin d → UpperF) → Bool)
    (correct : ∀ X z, (∀ i, ask i (upperPast z i) X = z i) → (out z = true ↔ P X)) :
    UpperPlan M d P :=
  ⟨(ask, out), correct⟩

private def upperTrue {d : ℕ} {P : M → Prop} (h : ∀ X, P X) : UpperPlan M d P :=
  upperMake (fun _ _ => 0) (fun _ => true) (fun X _ _ => iff_of_true rfl (h X))

private def upperPullback {d : ℕ} {P : N → Prop} (L : M →ₗ[UpperF] N)
    (p : UpperPlan N d P) : UpperPlan M d (fun X => P (L X)) :=
  upperMake (fun i z => (p.ask i z).comp L) p.out (fun X z h => p.correct (L X) z h)

private def upperChange {d : ℕ} {P Q : M → Prop} (p : UpperPlan M d P)
    (h : ∀ X, P X ↔ Q X) : UpperPlan M d Q :=
  upperMake p.ask p.out (fun X z hz => (p.correct X z hz).trans (h X))

private def upperPad {d D : ℕ} {P : M → Prop} (p : UpperPlan M d P) (h : d ≤ D) :
    UpperPlan M D P :=
  upperMake (fun i z => if hi : i.val < d then p.ask ⟨i.val, hi⟩ z else 0)
    (fun z => p.out (fun j => z ⟨j.val, Nat.lt_of_lt_of_le j.isLt h⟩)) (by
    intro X z hX
    let w : Fin d → UpperF := fun j => z ⟨j.val, Nat.lt_of_lt_of_le j.isLt h⟩
    apply p.correct X w
    intro j
    let jD : Fin D := ⟨j.val, Nat.lt_of_lt_of_le j.isLt h⟩
    have hq := hX jD
    change (if hi : j.val < d then p.ask ⟨j.val, hi⟩ (upperPast z jD) else 0) X = z jD at hq
    rw [dite_eq_left j.isLt] at hq
    change p.ask j (upperPast w j) X = w j at hq
    exact hq
  )

private def upperPrefixAsk {c k : ℕ} {Q : (Fin c → UpperF) → M → Prop}
    (ask₀ : Fin c → M →ₗ[UpperF] UpperF) (p : (v : Fin c → UpperF) → UpperPlan M k (Q v))
    (i : Fin (c + k)) : (Fin i.val → UpperF) → M →ₗ[UpperF] UpperF :=
  Fin.addCases (m := c) (n := k) (motive := fun i => (Fin i.val → UpperF) → M →ₗ[UpperF] UpperF)
    (fun j _ => ask₀ j)
    (fun j z =>
      let v : Fin c → UpperF := fun t => z ⟨t.val, by
        change t.val < c + j.val
        exact t.isLt.trans_le (Nat.le_add_right _ _)⟩
      (p v).ask j (fun t => z ⟨c + t.val, by
        change c + t.val < c + j.val
        exact Nat.add_lt_add_left t.isLt c⟩))
    i

private def upperPrefix {c k : ℕ} {P : M → Prop} {Q : (Fin c → UpperF) → M → Prop}
    (ask₀ : Fin c → M →ₗ[UpperF] UpperF) (p : (v : Fin c → UpperF) → UpperPlan M k (Q v))
    (rel : ∀ X, Q (fun i => ask₀ i X) X ↔ P X) : UpperPlan M (c + k) P :=
  upperMake (upperPrefixAsk ask₀ p) (fun z =>
    let v : Fin c → UpperF := fun i => z (Fin.castAdd k i)
    let w : Fin k → UpperF := fun j => z (Fin.natAdd c j)
    (p v).out w) (by
    intro X z hX
    let v : Fin c → UpperF := fun i => z (Fin.castAdd k i)
    let w : Fin k → UpperF := fun j => z (Fin.natAdd c j)
    have hv : v = fun i => ask₀ i X := by
      funext i
      change z (Fin.castAdd k i) = ask₀ i X
      simpa only [upperPrefixAsk, Fin.addCases_left] using (hX (Fin.castAdd k i)).symm
    have hw : ∀ j, (p v).ask j (upperPast w j) X = w j := by
      intro j
      have hq := hX (Fin.natAdd c j)
      simp only [upperPrefixAsk, Fin.addCases_right] at hq
      change (p v).ask j (upperPast w j) X = w j at hq
      exact hq
    change (p v).out w = true ↔ P X
    rw [(p v).correct X w hw, hv]
    exact rel X
  )

end AdaptiveUpperProtocol

private def upperEntry {a b : ℕ} (i : Fin a) (j : Fin b) : UpperM a b →ₗ[UpperF] UpperF where
  toFun X := X i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem upperEntry_apply {a b : ℕ} (i : Fin a) (j : Fin b) (X : UpperM a b) :
    upperEntry i j X = X i j := rfl

private def upperTail {a b : ℕ} : UpperM a (b + 1) →ₗ[UpperF] UpperM a b where
  toFun X := X.submatrix id Fin.succ
  map_add' _ _ := by ext i j <;> rfl
  map_smul' _ _ := by ext i j <;> rfl

private def upperProject {a : ℕ} (v : Fin (a + 1) → UpperF) (p : Fin (a + 1)) :
    (Fin (a + 1) → UpperF) →ₗ[UpperF] (Fin a → UpperF) where
  toFun x i := x (p.succAbove i) - x p * v (p.succAbove i)
  map_add' x y := by
    funext i
    simp only [Pi.add_apply, add_mul]
    ring
  map_smul' c x := by
    funext i
    change c * x (p.succAbove i) - c * x p * v (p.succAbove i) =
      c * (x (p.succAbove i) - x p * v (p.succAbove i))
    ring

private def upperElim {a b : ℕ} (v : Fin (a + 1) → UpperF) (p : Fin (a + 1)) :
    UpperM (a + 1) (b + 1) →ₗ[UpperF] UpperM a b where
  toFun X := Matrix.of fun i j => upperProject v p (X.col j.succ) i
  map_add' X Y := by
    ext i j
    exact congrFun ((upperProject v p).map_add (X.col j.succ) (Y.col j.succ)) i
  map_smul' c X := by
    ext i j
    exact congrFun ((upperProject v p).map_smul c (X.col j.succ)) i

private theorem upperRankTail {a b : ℕ} (X : UpperM a (b + 1)) (h₀ : X.col 0 = 0) :
    (upperTail X).rank = X.rank := by
  have hspan : Submodule.span UpperF (Set.range (upperTail X).col) =
      Submodule.span UpperF (Set.range X.col) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro x ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i.succ, rfl⟩
    · apply Submodule.span_le.mpr
      rintro x ⟨i, rfl⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [h₀]
        exact Submodule.zero_mem _
      · exact Submodule.subset_span ⟨j, rfl⟩
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols, hspan]

private theorem upperProjectKer {a : ℕ} {v : Fin (a + 1) → UpperF} {p : Fin (a + 1)}
    (hp : v p = 1) : LinearMap.ker (upperProject v p) = Submodule.span UpperF {v} := by
  apply Submodule.ext
  intro x
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro hx
    refine ⟨x p, funext ((Fin.forall_iff_succAbove p).2 ⟨?_, fun i => ?_⟩)⟩
    · change x p * v p = x p
      rw [hp, mul_one]
    · have hz := congrFun hx i
      change x (p.succAbove i) - x p * v (p.succAbove i) = 0 at hz
      exact (sub_eq_zero.mp hz).symm
  · rintro ⟨c, rfl⟩
    funext i
    change c * v (p.succAbove i) - (c * v p) * v (p.succAbove i) = 0
    rw [hp, mul_one, sub_self]

private theorem upperRankPivot {a b : ℕ} (X : UpperM (a + 1) (b + 1))
    {v : Fin (a + 1) → UpperF} {p : Fin (a + 1)} (h₀ : X.col 0 = v) (hp : v p = 1) :
    X.rank = (upperElim v p X).rank + 1 := by
  let S := Submodule.span UpperF (Set.range X.col)
  let T := Submodule.span UpperF (Set.range (upperElim v p X).col)
  have hvS : Submodule.span UpperF {v} ≤ S := by
    apply Submodule.span_le.mpr
    rintro x (rfl : x = v)
    exact Submodule.subset_span ⟨0, h₀⟩
  have hv₀ : v ≠ 0 := fun h => one_ne_zero (hp.symm.trans (congrFun h p))
  have hker : LinearMap.ker ((upperProject v p).domRestrict S) =
      (Submodule.span UpperF {v}).comap S.subtype := by
    change LinearMap.ker ((upperProject v p).comp S.subtype) = _
    rw [LinearMap.ker_comp, upperProjectKer hp]
  have hrange : LinearMap.range ((upperProject v p).domRestrict S) = T := by
    rw [LinearMap.range_domRestrict]
    apply le_antisymm
    · apply (Submodule.map_span_le _ _ _).mpr
      rintro x ⟨j, rfl⟩
      refine Fin.cases ?_ (fun i => ?_) j
      · have hz : upperProject v p v = 0 := by
          funext i
          change v (p.succAbove i) - v p * v (p.succAbove i) = 0
          rw [hp, one_mul, sub_self]
        rw [h₀, hz]
        exact Submodule.zero_mem _
      · exact Submodule.subset_span ⟨i, rfl⟩
    · apply Submodule.span_le.mpr
      rintro x ⟨j, rfl⟩
      exact Submodule.mem_map.mpr ⟨X.col j.succ, Submodule.subset_span ⟨j.succ, rfl⟩, rfl⟩
  have hdim := ((upperProject v p).domRestrict S).finrank_range_add_finrank_ker
  rw [hrange, hker, (Submodule.comapSubtypeEquivOfLe hvS).finrank_eq,
    finrank_span_singleton (K := UpperF) hv₀] at hdim
  simpa only [Matrix.rank_eq_finrank_span_cols] using hdim.symm

private theorem upperRankZero {a b : ℕ} (X : UpperM a b) : X.rank ≤ 0 ↔ X = 0 := by
  constructor
  · intro h
    have hz : X.rank = 0 := Nat.eq_zero_of_le_zero h
    have hs : Submodule.span UpperF (Set.range X.col) = ⊥ :=
      Submodule.finrank_eq_zero.mp ((Matrix.rank_eq_finrank_span_cols X).symm.trans hz)
    ext i j
    have hm : X.col j ∈ Submodule.span UpperF (Set.range X.col) :=
      Submodule.subset_span ⟨j, rfl⟩
    rw [hs] at hm
    exact congrFun ((Submodule.mem_bot UpperF).mp hm) i
  · rintro rfl
    simp

private noncomputable def upperAll (a b : ℕ) : UpperPlan (UpperM a b) (a * b) (fun X => X.rank ≤ 0) := by
  let e : Fin a × Fin b ≃ Fin (a * b) := finProdFinEquiv
  refine upperMake (fun i _ => upperEntry (e.symm i).1 (e.symm i).2)
    (fun z => decide (∀ i, z i = 0)) ?_
  intro X z hX
  rw [decide_eq_true_eq, upperRankZero]
  constructor
  · intro hz
    ext i j
    have hq := hX (e (i, j))
    change X (e.symm (e (i, j))).1 (e.symm (e (i, j))).2 = z (e (i, j)) at hq
    simpa [hz] using hq
  · intro hx i
    have hq := (hX i).symm
    change z i = X (e.symm i).1 (e.symm i).2 at hq
    rw [hx] at hq
    exact hq

private theorem upperPivotExists {a : ℕ} (v : Fin (a + 1) → UpperF) (h : v ≠ 0) :
    ∃ p, v p ≠ 0 := by
  classical
  by_contra hn
  apply h
  funext i
  by_contra hi
  exact hn ⟨i, hi⟩

private noncomputable def upperPivot {a : ℕ} (v : Fin (a + 1) → UpperF) (h : v ≠ 0) : Fin (a + 1) :=
  Classical.choose (upperPivotExists v h)

private theorem upperPivotOne {a : ℕ} (v : Fin (a + 1) → UpperF) (h : v ≠ 0) :
    v (upperPivot v h) = 1 := by
  have hone : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  exact hone _ (Classical.choose_spec (upperPivotExists v h))

private noncomputable def upperBranch {a b : ℕ} (r : ℕ) (v : Fin (a + 1) → UpperF)
    (X : UpperM (a + 1) (b + 1)) : Prop :=
  if h : v = 0 then (upperTail X).rank ≤ r + 1
  else (upperElim v (upperPivot v h) X).rank ≤ r

private theorem upperBranchCorrect {a b : ℕ} (r : ℕ) (X : UpperM (a + 1) (b + 1)) :
    upperBranch r (X.col 0) X ↔ X.rank ≤ r + 1 := by
  by_cases h : X.col 0 = 0
  · rw [upperBranch, dite_eq_left h, upperRankTail X h]
  · rw [upperBranch, dite_eq_right h, upperRankPivot X rfl (upperPivotOne (X.col 0) h)]
    omega

private theorem upperPlanExists (a b r d : ℕ)
    (h : min a b ≤ r ∨ a * b - Nat.choose (r + 1) 2 ≤ d) :
    Nonempty (UpperPlan (UpperM a b) d (fun X => X.rank ≤ r)) := by
  induction b generalizing a r d with
  | zero =>
    exact ⟨upperTrue (fun X => X.rank_le_width.trans (Nat.zero_le r))⟩
  | succ b ih =>
    by_cases hdim : min a (b + 1) ≤ r
    · exact ⟨upperTrue (fun X => (le_min X.rank_le_height X.rank_le_width).trans hdim)⟩
    have hd := h.resolve_left hdim
    have hlt : r < min a (b + 1) := lt_of_not_ge hdim
    have ha : r < a := hlt.trans_le (min_le_left _ _)
    have hb : r ≤ b := Nat.lt_succ_iff.mp (hlt.trans_le (min_le_right _ _))
    cases r with
    | zero =>
      have hdb : a * (b + 1) ≤ d := by simpa using hd
      exact ⟨upperPad (upperAll a (b + 1)) hdb⟩
    | succ r =>
      cases a with
      | zero => omega
      | succ a =>
        change (a + 1) * (b + 1) - Nat.choose (r + 1 + 1) 2 ≤ d at hd
        have hchoose : Nat.choose (r + 1 + 1) 2 ≤ (a + 1) * b := by
          calc
            _ ≤ (r + 1 + 1) * (r + 1) := by
              rw [Nat.choose_two_right, show r + 1 + 1 - 1 = r + 1 by omega]
              exact Nat.div_le_self _ _
            _ ≤ _ := Nat.mul_le_mul (by omega) hb
        have hstep : Nat.choose (r + 1 + 1) 2 = Nat.choose (r + 1) 2 + (r + 1) := by
          rw [Nat.choose_succ_succ' (r + 1) 1, Nat.choose_one_right, Nat.add_comm]
        have htotal : (a + 1) * (b + 1) = (a + 1) * b + (a + 1) := Nat.mul_succ _ _
        have hcross : (a + 1) * b = a * b + b := Nat.succ_mul _ _
        have hsplit : (a + 1) + (d - (a + 1)) = d := by omega
        have hzero : (a + 1) * b - Nat.choose (r + 1 + 1) 2 ≤ d - (a + 1) := by omega
        have hpivot : a * b - Nat.choose (r + 1) 2 ≤ d - (a + 1) := by omega
        obtain ⟨p₀⟩ := ih (a + 1) (r + 1) (d - (a + 1)) (.inr hzero)
        obtain ⟨p₁⟩ := ih a r (d - (a + 1)) (.inr hpivot)
        have next : (v : Fin (a + 1) → UpperF) →
            UpperPlan (UpperM (a + 1) (b + 1)) (d - (a + 1)) (upperBranch r v) := by
          intro v
          by_cases hv : v = 0
          · refine upperChange (upperPullback upperTail p₀) ?_
            intro X
            rw [upperBranch, dite_eq_left hv]
          · refine upperChange (upperPullback (upperElim v (upperPivot v hv)) p₁) ?_
            intro X
            rw [upperBranch, dite_eq_right hv]
        have result := upperPrefix (P := fun X : UpperM (a + 1) (b + 1) => X.rank ≤ r + 1)
          (fun i => upperEntry i (0 : Fin (b + 1))) next (fun X => by
            simpa only [upperEntry_apply, Matrix.col_apply'] using upperBranchCorrect r X)
        exact ⟨hsplit ▸ result⟩

/-- Adaptive linear queries decide a rank threshold with the stated depth budget. -/
theorem adaptiveUpper (a b r d : ℕ)
    (h : min a b ≤ r ∨ a * b - Nat.choose (r + 1) 2 ≤ d) :
    ∃ (ask : (i : Fin d) → (Fin i.val → ZMod 2) →
          Matrix (Fin a) (Fin b) (ZMod 2) →ₗ[ZMod 2] ZMod 2)
      (out : (Fin d → ZMod 2) → Bool),
      ∀ (X : Matrix (Fin a) (Fin b) (ZMod 2)) (z : Fin d → ZMod 2),
        (∀ i, ask i (fun j => z ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) X = z i) →
        (out z = true ↔ X.rank ≤ r) := by
  obtain ⟨p⟩ := upperPlanExists a b r d h
  exact ⟨p.ask, p.out, p.correct⟩

end PEqualNP.Outside.L_meta_33678_aux

open PEqualNP.Outside.L_meta_33678_aux

theorem PEqualNP.Outside.L_meta_33678 :
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depth := fun (w : ℕ) (Q : PEqualNP.CircuitLowerBounds.Circuit) =>
  (Q.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun h => ds.getD h 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate w 0)).getD Q.output 0
∀ (a b t d e : ℕ),
  let F := ZMod 2
  let M := Matrix (Fin (a+1)) (Fin (b+1)) F
  let W := Fin d → F
  let r := 2*t
  let fits := fun (A : M) => ∃ Q : PEqualNP.CircuitLowerBounds.Circuit,
    (∀ g ∈ Q.gates, g.inputs.length ≤ 2) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (a+1+(b+1)) Q ∧
    PEqualNP.Represents.Represents (fun x y => decide (A x y ≠ 0)) Q ∧
    depth (a+1+(b+1)) Q ≤ 1 ∧ Q.gates.countP nonlinear ≤ t
  let past := fun (z : W) (i : Fin d) (j : Fin i.val) => z ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩
  let adaptive := ∃ (ask : (i : Fin d) → (Fin i.val → F) → M →ₗ[F] F) (out : W → Bool),
    ∀ (A : M) (z : W), (∀ i, ask i (past z i) A = z i) → (out z = true ↔ fits A)
  let batch := ∃ (ask : M →ₗ[F] W) (out : W → Bool), ∀ (A : M) (z : W),
    (Finset.univ.filter (fun j => z j ≠ (ask A) j)).card ≤ e → (out z = true ↔ fits A)
  let code := ∃ C : (Matrix (Fin a) (Fin b) F) →ₗ[F] W, ∀ X, X ≠ 0 →
    2*e+1 ≤ (Finset.univ.filter (fun j => C X j ≠ 0)).card
  (adaptive ↔ min a b ≤ r ∨ a*b - Nat.choose (r+1) 2 ≤ d) ∧
    (batch ↔ min a b ≤ r ∨ code) := by
  intro nonlinear depth a b t d e F M W r fits past adaptive batch code
  have hfit (A : M) : fits A ↔ (corner A).rank ≤ r := fits_rank A
  have har : adaptive ↔ (∃ (ask : (i : Fin d) → (Fin i.val → F) → Inner a b →ₗ[F] F)
      (out : W → Bool), ∀ (X : Inner a b) (z : W),
        (∀ i, ask i (past z i) X = z i) → (out z = true ↔ X.rank ≤ r)) := by
    change (∃ (ask : (i : Fin d) → (Fin i.val → F) → M →ₗ[F] F)
      (out : W → Bool), ∀ (A : M) (z : W),
        (∀ i, ask i (past z i) A = z i) → (out z = true ↔ fits A)) ↔ _
    constructor
    · rintro ⟨ask, out, h⟩
      refine ⟨fun i p => (ask i p).comp zeroBorder, out, fun X z hz => ?_⟩
      simpa only [corner_zeroBorder] using (h (zeroBorder X) z hz).trans (hfit (zeroBorder X))
    · rintro ⟨ask, out, h⟩
      exact ⟨fun i p => (ask i p).comp corner, out,
        fun A z hz => (h (corner A) z hz).trans (hfit A).symm⟩
  have hbr : batch ↔ (∃ (ask : Inner a b →ₗ[F] W) (out : W → Bool),
      ∀ (X : Inner a b) (z : W),
        (Finset.univ.filter (fun j => z j ≠ (ask X) j)).card ≤ e →
          (out z = true ↔ X.rank ≤ r)) := by
    change (∃ (ask : M →ₗ[F] W) (out : W → Bool), ∀ (A : M) (z : W),
        (Finset.univ.filter (fun j => z j ≠ (ask A) j)).card ≤ e →
          (out z = true ↔ fits A)) ↔ _
    constructor
    · rintro ⟨ask, out, h⟩
      refine ⟨ask.comp zeroBorder, out, fun X z hz => ?_⟩
      simpa only [corner_zeroBorder] using (h (zeroBorder X) z hz).trans (hfit (zeroBorder X))
    · rintro ⟨ask, out, h⟩
      exact ⟨ask.comp corner, out, fun A z hz => (h (corner A) z hz).trans (hfit A).symm⟩
  exact ⟨har.trans ⟨adaptive_rank_lower a b r d, adaptiveUpper a b r d⟩,
    hbr.trans (batchIff a b r d e)⟩
