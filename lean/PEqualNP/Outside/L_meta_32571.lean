import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32571

open PEqualNP.CircuitLowerBounds PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

abbrev F2 := ZMod 2

-- ============================================================================
-- Part 1: Basic ZMod 2, Bool, and Circuit Evaluation / Depth Lemmas
-- ============================================================================

def b2z (b : Bool) : F2 := if b then 1 else 0

lemma b2z_inj {a b : Bool} (h : b2z a = b2z b) : a = b := by
  cases a <;> cases b <;> simp [b2z] at h <;> rfl

lemma b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

lemma b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

lemma b2z_not (a : Bool) : b2z (!a) = 1 + b2z a := by
  cases a <;> decide

lemma zmod2_eq_zero_or_one (x : F2) : x = 0 ∨ x = 1 := by
  match x with
  | ⟨0, _⟩ => left; rfl
  | ⟨1, _⟩ => right; rfl

lemma zmod2_eq_zero_of_ne_one {x : F2} (h : x ≠ 1) : x = 0 := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl
  · rfl
  · exact absurd rfl h

lemma b2z_nonzero (x : F2) : b2z (decide (x ≠ 0)) = x := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;> rfl

lemma zmod2_add_self (x : F2) : x + x = 0 := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;> rfl

lemma zmod2_two : (2 : F2) = 0 := rfl

lemma zmod2_neg (x : F2) : -x = x := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;> rfl

lemma zmod2_sub (x y : F2) : x - y = x + y := by
  rw [sub_eq_add_neg, zmod2_neg]

lemma zmod2_eq_of_add_eq_zero {x y : F2} (h : x + y = 0) : x = y := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;>
  rcases zmod2_eq_zero_or_one y with rfl | rfl
  · rfl
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · rfl

lemma zmod2_eq_one_of_ne_zero {x : F2} (h : x ≠ 0) : x = 1 := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl
  · exact absurd rfl h
  · rfl

lemma zmod2_ite_eq (x : F2) : (if x = 1 then (1 : F2) else 0) = x := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;> rfl

lemma zmod2_mul_self (x : F2) : x * x = x := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;> rfl

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

lemma wiresOf_length (x : List Bool) (gs : List Gate) :
    (wiresOf x gs).length = x.length + gs.length := by
  unfold wiresOf
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma depthsOf_length (w : ℕ) (gs : List Gate) :
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

lemma wiresOf_append (x : List Bool) (gs1 gs2 : List Gate) :
    wiresOf x (gs1 ++ gs2) =
      gs2.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (wiresOf x gs1) := by
  unfold wiresOf
  rw [List.foldl_append]

lemma depthsOf_append (w : ℕ) (gs1 gs2 : List Gate) :
    depthsOf w (gs1 ++ gs2) =
      gs2.foldl (fun (ds : List ℕ) g =>
        ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat])
        (depthsOf w gs1) := by
  unfold depthsOf
  rw [List.foldl_append]

lemma foldl_append_prefix {α β : Type*} (f : List α → β → α) (l : List β) (init : List α) :
    ∃ ext : List α, l.foldl (fun acc b => acc ++ [f acc b]) init = init ++ ext := by
  induction l generalizing init with
  | nil => exact ⟨[], by simp⟩
  | cons b l ih =>
    rw [List.foldl_cons]
    obtain ⟨ext, hext⟩ := ih (init ++ [f init b])
    exact ⟨f init b :: ext, by rw [hext]; simp⟩

lemma wiresOf_append_getD_lt (x : List Bool) (gs1 gs2 : List Gate) {k : ℕ}
    (hk : k < x.length + gs1.length) :
    (wiresOf x (gs1 ++ gs2)).getD k false = (wiresOf x gs1).getD k false := by
  rw [wiresOf_append]
  obtain ⟨ext, hext⟩ := foldl_append_prefix
    (fun (w : List Bool) (g : Gate) => g.op.eval (g.inputs.map fun i => w.getD i false))
    gs2 (wiresOf x gs1)
  rw [hext, List.getD_append _ _ _ _ (by rw [wiresOf_length]; exact hk)]

lemma depthsOf_append_getD_lt (w : ℕ) (gs1 gs2 : List Gate) {k : ℕ}
    (hk : k < w + gs1.length) :
    (depthsOf w (gs1 ++ gs2)).getD k 0 = (depthsOf w gs1).getD k 0 := by
  rw [depthsOf_append]
  obtain ⟨ext, hext⟩ := foldl_append_prefix
    (fun (ds : List ℕ) (g : Gate) =>
      (g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat)
    gs2 (depthsOf w gs1)
  rw [hext, List.getD_append _ _ _ _ (by rw [depthsOf_length]; exact hk)]

lemma wiresOf_getD_input (x : List Bool) (gs : List Gate) {k : ℕ} (hk : k < x.length) :
    (wiresOf x gs).getD k false = x.getD k false := by
  have h := wiresOf_append_getD_lt x [] gs (by simpa using hk)
  simp only [List.nil_append] at h
  rw [h]
  rfl

lemma depthsOf_getD_input (w : ℕ) (gs : List Gate) {k : ℕ} (hk : k < w) :
    (depthsOf w gs).getD k 0 = 0 := by
  have h := depthsOf_append_getD_lt w [] gs (by simpa using hk)
  simp only [List.nil_append] at h
  rw [h]
  unfold depthsOf
  simp only [List.foldl_nil]
  rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_replicate]

lemma wiresOf_getD_oob (x : List Bool) (gs : List Gate) {k : ℕ}
    (hk : x.length + gs.length ≤ k) :
    (wiresOf x gs).getD k false = false := by
  rw [List.getD_eq_default _ _ (by rw [wiresOf_length]; exact hk)]

lemma depthsOf_getD_oob (w : ℕ) (gs : List Gate) {k : ℕ}
    (hk : w + gs.length ≤ k) :
    (depthsOf w gs).getD k 0 = 0 := by
  rw [List.getD_eq_default _ _ (by rw [depthsOf_length]; exact hk)]

lemma wiresOf_getD_gate (x : List Bool) (gs : List Gate) {idx : ℕ} (hidx : idx < gs.length)
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

lemma depthsOf_getD_gate (w : ℕ) (gs : List Gate) {idx : ℕ} (hidx : idx < gs.length)
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

lemma oneEach_length {n m : ℕ} (i : Fin n) (j : Fin m) :
    (oneEach i j).length = n + m := by
  simp [oneEach]

lemma oneEach_getD_left {n m : ℕ} (i : Fin n) (j : Fin m) {k : ℕ} (hk : k < n) :
    (oneEach i j).getD k false = decide (k = i.val) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simp [hk])]
  rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_ofFn]
  simp [Fin.ext_iff]

lemma oneEach_getD_right {n m : ℕ} (i : Fin n) (j : Fin m) {k : ℕ} (hk1 : n ≤ k)
    (hk2 : k < n + m) :
    (oneEach i j).getD k false = decide (k - n = j.val) := by
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by simp [hk1])]
  simp only [List.length_ofFn]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  simp [Fin.ext_iff]

lemma anf_one (f : Bool → Bool) (x : Bool) :
    b2z (f x) = b2z (f false) + (b2z (f false) + b2z (f true)) * b2z x := by
  cases x <;> cases h0 : f false <;> cases h1 : f true <;> decide

lemma anf_two (f : Bool → Bool → Bool) (x y : Bool) :
    b2z (f x y) =
      b2z (f false false) +
      (b2z (f false false) + b2z (f true false)) * b2z x +
      (b2z (f false false) + b2z (f false true)) * b2z y +
      b2z (xor (xor (f false false) (f false true)) (xor (f true false) (f true true))) *
        (b2z x * b2z y) := by
  cases x <;> cases y <;>
    cases h00 : f false false <;> cases h01 : f false true <;>
    cases h10 : f true false <;> cases h11 : f true true <;> decide

-- ============================================================================
-- Part 2: Problem Definitions, Rank-2 Matrices, and Anchor Reduction
-- ============================================================================

def IsAlt {d : ℕ} (H : Matrix (Fin d) (Fin d) F2) : Prop :=
  H.transpose = H ∧ ∀ i, H i i = 0

def padTable {d : ℕ} (H : Matrix (Fin d) (Fin d) F2) (x y : Fin (d + 1)) : Bool :=
  Fin.cases false (fun i => Fin.cases false (fun j => decide (H i j ≠ 0)) y) x

def Bank (d : ℕ) (U : Matrix (Fin d) (Fin d) F2) (t : ℕ) : Prop :=
  ∃ (C : Circuit) (tap : Matrix (Fin d) (Fin d) F2 → ℕ),
    ReadsBack ((d + 1) + (d + 1)) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
    C.gates.countP nlGate ≤ t ∧
    ∀ H : Matrix (Fin d) (Fin d) F2, IsAlt H →
      (depthsOf ((d + 1) + (d + 1)) C.gates).getD (tap H) 0 ≤ 1 ∧
      Represents (padTable (U * H * U.transpose + H)) ⟨C.gates, tap H⟩

def rk2Mat {d : ℕ} (a b c e : Fin d → F2) : Matrix (Fin d) (Fin d) F2 :=
  fun i j => a i * b j + c i * e j

def subAnchor {d : ℕ} (h : Fin (d + 1) → Fin (d + 1) → F2) : Matrix (Fin d) (Fin d) F2 :=
  fun i j => h i.succ j.succ + h i.succ 0 + h 0 j.succ + h 0 0

lemma subAnchor_const {d : ℕ} (c : F2) :
    subAnchor (d := d) (fun _ _ => c) = 0 := by
  ext i j
  simp [subAnchor, zmod2_add_self]

lemma subAnchor_split {d : ℕ} (r s : Fin (d + 1) → F2) :
    subAnchor (d := d) (fun x y => r x + s y) = 0 := by
  ext i j
  simp only [subAnchor, Matrix.zero_apply]
  have h : (r i.succ + s j.succ) + (r i.succ + s 0) + (r 0 + s j.succ) + (r 0 + s 0) =
      (r i.succ + r i.succ) + (r 0 + r 0) + (s j.succ + s j.succ) + (s 0 + s 0) := by ring
  rw [h]
  simp [zmod2_add_self]

lemma subAnchor_add {d : ℕ} (h1 h2 : Fin (d + 1) → Fin (d + 1) → F2) :
    subAnchor (fun x y => h1 x y + h2 x y) = subAnchor h1 + subAnchor h2 := by
  ext i j
  simp only [subAnchor, Matrix.add_apply]
  ring

lemma subAnchor_smul {d : ℕ} (c : F2) (h : Fin (d + 1) → Fin (d + 1) → F2) :
    subAnchor (fun x y => c * h x y) = c • subAnchor h := by
  ext i j
  simp only [subAnchor, Matrix.smul_apply, smul_eq_mul]
  ring

lemma subAnchor_prod_split {d : ℕ} (r1 r2 s1 s2 : Fin (d + 1) → F2) :
    subAnchor (fun x y => (r1 x + s1 y) * (r2 x + s2 y)) =
      rk2Mat (fun i => r1 i.succ + r1 0) (fun j => s2 j.succ + s2 0)
             (fun i => r2 i.succ + r2 0) (fun j => s1 j.succ + s1 0) := by
  ext i j
  simp only [subAnchor, rk2Mat]
  have h : ((r1 i.succ + s1 j.succ) * (r2 i.succ + s2 j.succ) +
            (r1 i.succ + s1 0) * (r2 i.succ + s2 0) +
            (r1 0 + s1 j.succ) * (r2 0 + s2 j.succ) +
            (r1 0 + s1 0) * (r2 0 + s2 0)) +
           ((r1 i.succ + r1 0) * (s2 j.succ + s2 0) +
            (r2 i.succ + r2 0) * (s1 j.succ + s1 0)) =
      (2 : F2) * (r1 i.succ * r2 i.succ + r1 0 * r2 0 + s1 j.succ * s2 j.succ + s1 0 * s2 0 +
        r1 i.succ * s2 j.succ + r1 i.succ * s2 0 + r1 0 * s2 j.succ + r1 0 * s2 0 +
        r2 i.succ * s1 j.succ + r2 i.succ * s1 0 + r2 0 * s1 j.succ + r2 0 * s1 0) := by ring
  rw [zmod2_two, zero_mul] at h
  exact zmod2_eq_of_add_eq_zero h

lemma subAnchor_padTable {d : ℕ} (M : Matrix (Fin d) (Fin d) F2) :
    subAnchor (fun x y => b2z (padTable M x y)) = M := by
  ext i j
  simp only [subAnchor, padTable, Fin.cases_zero, Fin.cases_succ]
  have hf : b2z false = 0 := rfl
  rw [hf, add_zero, add_zero, add_zero]
  exact b2z_nonzero (M i j)

lemma gateAt_eq_getElem (C : Circuit) {idx : ℕ} (hidx : idx < C.gates.length) :
    gateAt C idx = C.gates[idx] := by
  simp [gateAt, hidx]

lemma countP_eq_card_fin {α : Type*} (p : α → Bool) (l : List α) :
    l.countP p = (Finset.univ.filter (fun i : Fin l.length => p l[i.val] = true)).card := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.countP_cons, ih]
    change (Finset.univ.filter (fun i : Fin l.length => p l[i.val] = true)).card +
        (if p a then 1 else 0) =
      (Finset.univ.filter (fun i : Fin (l.length + 1) => p (a :: l)[i.val] = true)).card
    symm
    let f0 : Fin (l.length + 1) → Prop := fun i => p (a :: l)[i.val] = true
    have hsplit : Finset.univ.filter f0 =
        (Finset.univ.filter (fun i : Fin (l.length + 1) => i ≠ 0 ∧ f0 i)) ∪
        (Finset.univ.filter (fun i : Fin (l.length + 1) => i = 0 ∧ f0 i)) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
      by_cases hi : i = 0 <;> simp [hi]
    have hdisj : Disjoint
        (Finset.univ.filter (fun i : Fin (l.length + 1) => i ≠ 0 ∧ f0 i))
        (Finset.univ.filter (fun i : Fin (l.length + 1) => i = 0 ∧ f0 i)) := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      exact (Finset.mem_filter.mp hi1).2.1 (Finset.mem_filter.mp hi2).2.1
    rw [hsplit, Finset.card_union_of_disjoint hdisj]
    congr 1
    · symm
      refine Finset.card_bij (fun (j : Fin l.length) _ => j.succ) ?_ ?_ ?_
      · intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.succ_ne_zero j, (Finset.mem_filter.mp hj).2⟩
      · intro j1 _ j2 _ h
        exact Fin.succ_injective _ h
      · intro i hi
        have hne := (Finset.mem_filter.mp hi).2.1
        have hfi := (Finset.mem_filter.mp hi).2.2
        refine ⟨i.pred hne, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Fin.succ_pred i hne⟩
        have hsp : (i.pred hne).succ = i := Fin.succ_pred i hne
        rw [← hsp] at hfi
        exact hfi
    · by_cases hpa : p a = true
      · have heq : Finset.univ.filter (fun i : Fin (l.length + 1) => i = 0 ∧ f0 i) = {0} := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          exact ⟨fun h => h.1, fun h => ⟨h, by subst h; exact hpa⟩⟩
        rw [heq, Finset.card_singleton]; simp only [hpa, ↓reduceIte]
      · have heq : Finset.univ.filter (fun i : Fin (l.length + 1) => i = 0 ∧ f0 i) = ∅ := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
            iff_false, not_and]
          intro hi; subst hi; exact hpa
        rw [heq, Finset.card_empty]; simp [hpa]

lemma foldr_max_eq_zero_iff (l : List ℕ) :
    l.foldr max 0 = 0 ↔ ∀ x ∈ l, x = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons, Nat.max_eq_zero_iff, ih, List.mem_cons, forall_eq_or_imp]

lemma foldr_max_le_iff (l : List ℕ) (k : ℕ) :
    l.foldr max 0 ≤ k ↔ ∀ x ∈ l, x ≤ k := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons, Nat.max_le, ih, List.mem_cons, forall_eq_or_imp]

lemma depth_zero_split {d : ℕ} (C : Circuit)
    (hrb : ReadsBack ((d + 1) + (d + 1)) C)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∀ k : ℕ, (depthsOf ((d + 1) + (d + 1)) C.gates).getD k 0 = 0 →
      ∃ r s : Fin (d + 1) → F2, ∀ x y : Fin (d + 1),
        b2z ((wiresOf (oneEach x y) C.gates).getD k false) = r x + s y := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hdep
    set w := (d + 1) + (d + 1)
    by_cases hk1 : k < d + 1
    · refine ⟨fun x => b2z (decide (k = x.val)), fun _ => 0, fun x y => ?_⟩
      rw [wiresOf_getD_input _ _ (by rw [oneEach_length]; omega)]
      rw [oneEach_getD_left x y hk1, add_zero]
    · by_cases hk2 : k < w
      · refine ⟨fun _ => 0, fun y => b2z (decide (k - (d + 1) = y.val)), fun x y => ?_⟩
        rw [wiresOf_getD_input _ _ (by rw [oneEach_length]; omega)]
        rw [oneEach_getD_right x y (by omega) hk2, zero_add]
      · by_cases hk3 : k < w + C.gates.length
        · set idx := k - w
          have hidx : idx < C.gates.length := by omega
          have hk_eq : k = w + idx := by omega
          have hrb_idx : ∀ a ∈ (C.gates[idx]).inputs, a < w + idx := by
            intro a ha
            have := hrb idx hidx a
            rw [gateAt_eq_getElem C hidx] at this
            exact this ha
          have hdg := depthsOf_getD_gate w C.gates hidx hrb_idx
          rw [← hk_eq] at hdg
          rw [hdep] at hdg
          have hmax0 : ((C.gates[idx]).inputs.map
              (fun a => (depthsOf w C.gates).getD a 0)).foldr max 0 = 0 := by omega
          have hnl0 : nlGate (C.gates[idx]) = false := by
            cases h : nlGate (C.gates[idx])
            · rfl
            · simp [h] at hdg
          have hdeps0 : ∀ a ∈ (C.gates[idx]).inputs, (depthsOf w C.gates).getD a 0 = 0 := by
            intro a ha
            exact (foldr_max_eq_zero_iff _).mp hmax0 _ (List.mem_map.mpr ⟨a, ha, rfl⟩)
          have hglen : (C.gates[idx]).inputs.length ≤ 2 := hlen _ (List.getElem_mem hidx)
          have hwg : ∀ x y : Fin (d + 1),
              (wiresOf (oneEach x y) C.gates).getD k false =
                (C.gates[idx]).op.eval ((C.gates[idx]).inputs.map fun a =>
                  (wiresOf (oneEach x y) C.gates).getD a false) := by
            intro x y
            have := wiresOf_getD_gate (oneEach x y) C.gates hidx
              (by rw [oneEach_length]; exact hrb_idx)
            rw [oneEach_length, ← hk_eq] at this
            exact this
          cases hin : (C.gates[idx]).inputs with
          | nil =>
            refine ⟨fun _ => b2z ((C.gates[idx]).op.eval []), fun _ => 0, fun x y => ?_⟩
            rw [hwg x y, hin, List.map_nil, add_zero]
          | cons a rest =>
            cases rest with
            | nil =>
              have ha_mem : a ∈ (C.gates[idx]).inputs := by simp [hin]
              obtain ⟨r1, s1, h1⟩ := ih a (by have := hrb_idx a ha_mem; omega) (hdeps0 a ha_mem)
              let f : Bool → Bool := fun b => (C.gates[idx]).op.eval [b]
              refine ⟨fun x => b2z (f false) + (b2z (f false) + b2z (f true)) * r1 x,
                      fun y => (b2z (f false) + b2z (f true)) * s1 y, fun x y => ?_⟩
              rw [hwg x y, hin, List.map_cons, List.map_nil]
              change b2z (f ((wiresOf (oneEach x y) C.gates).getD a false)) = _
              rw [anf_one f, h1 x y]
              ring
            | cons b rest2 =>
              cases rest2 with
              | nil =>
                have ha_mem : a ∈ (C.gates[idx]).inputs := by simp [hin]
                have hb_mem : b ∈ (C.gates[idx]).inputs := by simp [hin]
                obtain ⟨r1, s1, h1⟩ := ih a (by have := hrb_idx a ha_mem; omega) (hdeps0 a ha_mem)
                obtain ⟨r2, s2, h2⟩ := ih b (by have := hrb_idx b hb_mem; omega) (hdeps0 b hb_mem)
                let f : Bool → Bool → Bool := fun b1 b2 => (C.gates[idx]).op.eval [b1, b2]
                have hquad : xor (xor (f false false) (f false true))
                    (xor (f true false) (f true true)) = false := by
                  unfold nlGate at hnl0
                  simp only [hin, List.length_cons, List.length_nil, beq_self_eq_true,
                    Bool.true_and] at hnl0
                  exact hnl0
                refine ⟨fun x => b2z (f false false) +
                          (b2z (f false false) + b2z (f true false)) * r1 x +
                          (b2z (f false false) + b2z (f false true)) * r2 x,
                        fun y => (b2z (f false false) + b2z (f true false)) * s1 y +
                          (b2z (f false false) + b2z (f false true)) * s2 y, fun x y => ?_⟩
                rw [hwg x y, hin, List.map_cons, List.map_cons, List.map_nil]
                change b2z (f ((wiresOf (oneEach x y) C.gates).getD a false)
                              ((wiresOf (oneEach x y) C.gates).getD b false)) = _
                rw [anf_two f, hquad]
                have hf0 : b2z false = 0 := rfl
                rw [hf0, zero_mul, add_zero, h1 x y, h2 x y]
                ring
              | cons c rest3 =>
                simp [hin] at hglen
        · refine ⟨fun _ => 0, fun _ => 0, fun x y => ?_⟩
          rw [wiresOf_getD_oob _ _ (by rw [oneEach_length]; omega)]
          simp [b2z]

theorem bank_to_rk2_span {d t : ℕ} {U : Matrix (Fin d) (Fin d) F2}
    (hb : Bank d U t) :
    ∃ (m : ℕ) (a b c e : Fin m → Fin d → F2),
      m ≤ t ∧
      ∀ H : Matrix (Fin d) (Fin d) F2, IsAlt H →
        U * H * U.transpose + H ∈
          Submodule.span F2 (Set.range fun l : Fin m => rk2Mat (a l) (b l) (c l) (e l)) := by
  classical
  obtain ⟨C, tap, hrb, hlen, hcnt, htap⟩ := hb
  set w := (d + 1) + (d + 1)
  let nlIdx : Finset (Fin C.gates.length) :=
    Finset.univ.filter (fun j => nlGate C.gates[j.val] = true ∧
      (depthsOf w C.gates).getD (w + j.val) 0 = 1)
  have hcard_le : nlIdx.card ≤ t := by
    have hsub : nlIdx ⊆ Finset.univ.filter (fun j : Fin C.gates.length =>
        nlGate C.gates[j.val] = true) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.1⟩
    calc nlIdx.card ≤ (Finset.univ.filter (fun j : Fin C.gates.length =>
            nlGate C.gates[j.val] = true)).card := Finset.card_le_card hsub
      _ = C.gates.countP nlGate := (countP_eq_card_fin nlGate C.gates).symm
      _ ≤ t := hcnt
  have hgen_rk2 : ∀ j : nlIdx, ∃ a b c e : Fin d → F2,
      subAnchor (fun x y => b2z ((wiresOf (oneEach x y) C.gates).getD (w + j.1.val) false)) =
        rk2Mat a b c e := by
    intro ⟨j, hj⟩
    have hnl : nlGate C.gates[j.val] = true := (Finset.mem_filter.mp hj).2.1
    have hdep1 : (depthsOf w C.gates).getD (w + j.val) 0 = 1 := (Finset.mem_filter.mp hj).2.2
    have hrb_j : ∀ u ∈ (C.gates[j.val]).inputs, u < w + j.val := by
      intro u hu
      have := hrb j.val j.isLt u
      rw [gateAt_eq_getElem C j.isLt] at this
      exact this hu
    have hdg := depthsOf_getD_gate w C.gates j.isLt hrb_j
    rw [hdep1, hnl] at hdg
    simp only [Bool.toNat_true] at hdg
    have hmax0 : ((C.gates[j.val]).inputs.map
        (fun u => (depthsOf w C.gates).getD u 0)).foldr max 0 = 0 := by omega
    have hlen2 : (C.gates[j.val]).inputs.length = 2 := by
      unfold nlGate at hnl
      rw [Bool.and_eq_true, beq_iff_eq] at hnl
      exact hnl.1
    have hquad1 : xor (xor ((C.gates[j.val]).op.eval [false, false])
                           ((C.gates[j.val]).op.eval [false, true]))
                      (xor ((C.gates[j.val]).op.eval [true, false])
                           ((C.gates[j.val]).op.eval [true, true])) = true := by
      unfold nlGate at hnl
      rw [Bool.and_eq_true] at hnl
      exact hnl.2
    cases hin : (C.gates[j.val]).inputs with
    | nil => simp [hin] at hlen2
    | cons u rest =>
      cases rest with
      | nil => simp [hin] at hlen2
      | cons v rest2 =>
        cases rest2 with
        | cons _ _ => simp [hin] at hlen2
        | nil =>
          have hu_dep : (depthsOf w C.gates).getD u 0 = 0 :=
            (foldr_max_eq_zero_iff _).mp hmax0 _ (List.mem_map.mpr ⟨u, by simp [hin], rfl⟩)
          have hv_dep : (depthsOf w C.gates).getD v 0 = 0 :=
            (foldr_max_eq_zero_iff _).mp hmax0 _ (List.mem_map.mpr ⟨v, by simp [hin], rfl⟩)
          obtain ⟨r1, s1, h1⟩ := depth_zero_split C hrb hlen u hu_dep
          obtain ⟨r2, s2, h2⟩ := depth_zero_split C hrb hlen v hv_dep
          refine ⟨fun i => r1 i.succ + r1 0, fun k => s2 k.succ + s2 0,
                  fun i => r2 i.succ + r2 0, fun k => s1 k.succ + s1 0, ?_⟩
          let f : Bool → Bool → Bool := fun b1 b2 => (C.gates[j.val]).op.eval [b1, b2]
          have hval : (fun x y => b2z ((wiresOf (oneEach x y) C.gates).getD (w + j.val) false)) =
              fun x y =>
                (b2z (f false false) +
                 (b2z (f false false) + b2z (f true false)) * (r1 x + s1 y) +
                 (b2z (f false false) + b2z (f false true)) * (r2 x + s2 y)) +
                ((r1 x + s1 y) * (r2 x + s2 y)) := by
            funext x y
            have hwg := wiresOf_getD_gate (oneEach x y) C.gates j.isLt
              (by rw [oneEach_length]; exact hrb_j)
            rw [oneEach_length] at hwg
            rw [hwg, hin, List.map_cons, List.map_cons, List.map_nil]
            change b2z (f ((wiresOf (oneEach x y) C.gates).getD u false)
                          ((wiresOf (oneEach x y) C.gates).getD v false)) = _
            rw [anf_two f, hquad1]
            have hb1 : b2z true = 1 := rfl
            rw [hb1, one_mul, h1 x y, h2 x y]
          rw [hval, subAnchor_add, subAnchor_prod_split]
          have hlin0 : subAnchor (fun x y =>
              b2z (f false false) +
              (b2z (f false false) + b2z (f true false)) * (r1 x + s1 y) +
              (b2z (f false false) + b2z (f false true)) * (r2 x + s2 y)) = 0 := by
            have heq : (fun x y =>
                b2z (f false false) +
                (b2z (f false false) + b2z (f true false)) * (r1 x + s1 y) +
                (b2z (f false false) + b2z (f false true)) * (r2 x + s2 y)) =
              fun x y =>
                (b2z (f false false) +
                 (b2z (f false false) + b2z (f true false)) * r1 x +
                 (b2z (f false false) + b2z (f false true)) * r2 x) +
                ((b2z (f false false) + b2z (f true false)) * s1 y +
                 (b2z (f false false) + b2z (f false true)) * s2 y) := by
              funext x y; ring
            rw [heq, subAnchor_split]
          rw [hlin0, zero_add]
  let eqv := Fintype.equivFin nlIdx
  let m := Fintype.card nlIdx
  have hm_le : m ≤ t := by
    have : m = nlIdx.card := Fintype.card_coe nlIdx
    omega
  let a : Fin m → Fin d → F2 := fun l => (hgen_rk2 (eqv.symm l)).choose
  let b : Fin m → Fin d → F2 := fun l => (hgen_rk2 (eqv.symm l)).choose_spec.choose
  let c : Fin m → Fin d → F2 := fun l => (hgen_rk2 (eqv.symm l)).choose_spec.choose_spec.choose
  let e : Fin m → Fin d → F2 :=
    fun l => (hgen_rk2 (eqv.symm l)).choose_spec.choose_spec.choose_spec.choose
  have hgen_eq : ∀ j : nlIdx,
      subAnchor (fun x y => b2z ((wiresOf (oneEach x y) C.gates).getD (w + j.1.val) false)) =
        rk2Mat (a (eqv j)) (b (eqv j)) (c (eqv j)) (e (eqv j)) := by
    intro j
    have hs := (hgen_rk2 j).choose_spec.choose_spec.choose_spec.choose_spec
    simpa [a, b, c, e] using hs
  let S := Submodule.span F2 (Set.range fun l : Fin m => rk2Mat (a l) (b l) (c l) (e l))
  have hwire_mem : ∀ k : ℕ, (depthsOf w C.gates).getD k 0 ≤ 1 →
      subAnchor (fun x y => b2z ((wiresOf (oneEach x y) C.gates).getD k false)) ∈ S := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hdep
      by_cases hdep0 : (depthsOf w C.gates).getD k 0 = 0
      · obtain ⟨r, s, hrs⟩ := depth_zero_split C hrb hlen k hdep0
        have heq : (fun x y => b2z ((wiresOf (oneEach x y) C.gates).getD k false)) =
            fun x y => r x + s y := by funext x y; exact hrs x y
        rw [heq, subAnchor_split]
        exact S.zero_mem
      · have hdep1 : (depthsOf w C.gates).getD k 0 = 1 := by omega
        have hk_ge : w ≤ k := by
          by_contra hlt
          have : (depthsOf w C.gates).getD k 0 = 0 := depthsOf_getD_input w C.gates (by omega)
          omega
        have hk_lt : k < w + C.gates.length := by
          by_contra hge
          have : (depthsOf w C.gates).getD k 0 = 0 := depthsOf_getD_oob w C.gates (by omega)
          omega
        set idx := k - w
        have hidx : idx < C.gates.length := by omega
        have hk_eq : k = w + idx := by omega
        by_cases hnl : nlGate C.gates[idx] = true
        · have hmem_nl : (⟨idx, hidx⟩ : Fin C.gates.length) ∈ nlIdx := by
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnl, ?_⟩
            rw [← hk_eq]; exact hdep1
          rw [hk_eq, hgen_eq ⟨⟨idx, hidx⟩, hmem_nl⟩]
          exact Submodule.subset_span ⟨eqv ⟨⟨idx, hidx⟩, hmem_nl⟩, rfl⟩
        · have hnlf : nlGate C.gates[idx] = false := Bool.eq_false_iff.mpr hnl
          have hrb_idx : ∀ u ∈ (C.gates[idx]).inputs, u < w + idx := by
            intro u hu
            have := hrb idx hidx u
            rw [gateAt_eq_getElem C hidx] at this
            exact this hu
          have hdg := depthsOf_getD_gate w C.gates hidx hrb_idx
          rw [← hk_eq, hdep1, hnlf] at hdg
          simp only [Bool.toNat_false, add_zero] at hdg
          have hmax_le : ((C.gates[idx]).inputs.map
              (fun u => (depthsOf w C.gates).getD u 0)).foldr max 0 ≤ 1 := by omega
          have hdeps_le : ∀ u ∈ (C.gates[idx]).inputs, (depthsOf w C.gates).getD u 0 ≤ 1 := by
            intro u hu
            exact (foldr_max_le_iff _ 1).mp hmax_le _ (List.mem_map.mpr ⟨u, hu, rfl⟩)
          have hglen : (C.gates[idx]).inputs.length ≤ 2 := hlen _ (List.getElem_mem hidx)
          have hwg : ∀ x y : Fin (d + 1),
              (wiresOf (oneEach x y) C.gates).getD k false =
                (C.gates[idx]).op.eval ((C.gates[idx]).inputs.map fun u =>
                  (wiresOf (oneEach x y) C.gates).getD u false) := by
            intro x y
            have := wiresOf_getD_gate (oneEach x y) C.gates hidx
              (by rw [oneEach_length]; exact hrb_idx)
            rw [oneEach_length, ← hk_eq] at this
            exact this
          cases hin : (C.gates[idx]).inputs with
          | nil =>
            have heq : (fun (x y : Fin (d + 1)) => b2z ((wiresOf (oneEach x y) C.gates).getD k false)) =
                fun _ _ => b2z ((C.gates[idx]).op.eval []) := by
              funext x y; rw [hwg x y, hin, List.map_nil]
            rw [heq, subAnchor_const]
            exact S.zero_mem
          | cons u rest =>
            cases rest with
            | nil =>
              have hu_mem : u ∈ (C.gates[idx]).inputs := by simp [hin]
              have hu_S := ih u (by have := hrb_idx u hu_mem; omega) (hdeps_le u hu_mem)
              let f : Bool → Bool := fun b => (C.gates[idx]).op.eval [b]
              have heq : (fun (x y : Fin (d + 1)) => b2z ((wiresOf (oneEach x y) C.gates).getD k false)) =
                  fun x y => b2z (f false) + (b2z (f false) + b2z (f true)) *
                    b2z ((wiresOf (oneEach x y) C.gates).getD u false) := by
                funext x y
                rw [hwg x y, hin, List.map_cons, List.map_nil]
                exact anf_one f _
              rw [heq, subAnchor_add, subAnchor_const, zero_add, subAnchor_smul]
              exact S.smul_mem _ hu_S
            | cons v rest2 =>
              cases rest2 with
              | nil =>
                have hu_mem : u ∈ (C.gates[idx]).inputs := by simp [hin]
                have hv_mem : v ∈ (C.gates[idx]).inputs := by simp [hin]
                have hu_S := ih u (by have := hrb_idx u hu_mem; omega) (hdeps_le u hu_mem)
                have hv_S := ih v (by have := hrb_idx v hv_mem; omega) (hdeps_le v hv_mem)
                let f : Bool → Bool → Bool := fun b1 b2 => (C.gates[idx]).op.eval [b1, b2]
                have hquad : xor (xor (f false false) (f false true))
                    (xor (f true false) (f true true)) = false := by
                  unfold nlGate at hnlf
                  simp only [hin, List.length_cons, List.length_nil, beq_self_eq_true,
                    Bool.true_and] at hnlf
                  exact hnlf
                have heq : (fun (x y : Fin (d + 1)) => b2z ((wiresOf (oneEach x y) C.gates).getD k false)) =
                    fun x y =>
                      (b2z (f false false) +
                       (b2z (f false false) + b2z (f true false)) *
                         b2z ((wiresOf (oneEach x y) C.gates).getD u false)) +
                      (b2z (f false false) + b2z (f false true)) *
                        b2z ((wiresOf (oneEach x y) C.gates).getD v false) := by
                  funext x y
                  rw [hwg x y, hin, List.map_cons, List.map_cons, List.map_nil]
                  change b2z (f _ _) = _
                  rw [anf_two f, hquad]
                  have hf0 : b2z false = 0 := rfl
                  rw [hf0, zero_mul, add_zero]
                rw [heq, subAnchor_add, subAnchor_add, subAnchor_const, zero_add,
                    subAnchor_smul, subAnchor_smul]
                exact S.add_mem (S.smul_mem _ hu_S) (S.smul_mem _ hv_S)
              | cons _ _ => simp [hin] at hglen
  refine ⟨m, a, b, c, e, hm_le, fun H hH => ?_⟩
  obtain ⟨hdep, hrep⟩ := htap H hH
  have hmem := hwire_mem (tap H) hdep
  have heq : (fun x y => b2z ((wiresOf (oneEach x y) C.gates).getD (tap H) false)) =
      fun x y => b2z (padTable (U * H * U.transpose + H) x y) := by
    funext x y
    have hxy : (wiresOf (oneEach x y) C.gates).getD (tap H) false =
        padTable (U * H * U.transpose + H) x y := hrep x y
    rw [hxy]
  rw [heq, subAnchor_padTable] at hmem
  exact hmem

-- ============================================================================
-- Part 3: Circuit Upper Bound Construction (rk2_span_to_bank)
-- ============================================================================

structure CState (d : ℕ) where
  gates : List Gate
  rb : ReadsBack ((d + 1) + (d + 1)) ⟨gates, 0⟩
  fanin : ∀ g ∈ gates, g.inputs.length ≤ 2

def CState.empty (d : ℕ) : CState d where
  gates := []
  rb := by intro j hj; simp at hj
  fanin := by intro g hg; simp at hg

def CState.push {d : ℕ} (st : CState d) (g : Gate)
    (hfan : g.inputs.length ≤ 2)
    (hrb : ∀ a ∈ g.inputs, a < ((d + 1) + (d + 1)) + st.gates.length) : CState d where
  gates := st.gates ++ [g]
  rb := by
    intro j hj a ha
    rw [List.length_append, List.length_singleton] at hj
    rw [gateAt_eq_getElem _ (by rw [List.length_append, List.length_singleton]; exact hj)] at ha
    by_cases hjlt : j < st.gates.length
    · rw [List.getElem_append_left hjlt] at ha
      have hst := st.rb j hjlt a
      rw [gateAt_eq_getElem _ hjlt] at hst
      exact hst ha
    · have hjeq : j = st.gates.length := by omega
      subst hjeq
      rw [List.getElem_append_right (Nat.le_refl _)] at ha
      simp only [Nat.sub_self, List.getElem_cons_zero] at ha
      exact hrb a ha
  fanin := by
    intro g' hg'
    rw [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · exact st.fanin g' hg'
    · exact hfan

lemma CState.push_length {d : ℕ} (st : CState d) (g : Gate) (hfan hrb) :
    (st.push g hfan hrb).gates.length = st.gates.length + 1 := by
  simp [CState.push]

lemma CState.push_countP {d : ℕ} (st : CState d) (g : Gate) (hfan hrb) :
    (st.push g hfan hrb).gates.countP nlGate = st.gates.countP nlGate + (nlGate g).toNat := by
  simp [CState.push, List.countP_append]
  cases nlGate g <;> rfl

lemma CState.push_wires_old {d : ℕ} (st : CState d) (g : Gate) (hfan hrb)
    (x y : Fin (d + 1)) {k : ℕ} (hk : k < ((d + 1) + (d + 1)) + st.gates.length) :
    (wiresOf (oneEach x y) (st.push g hfan hrb).gates).getD k false =
      (wiresOf (oneEach x y) st.gates).getD k false := by
  exact wiresOf_append_getD_lt (oneEach x y) st.gates [g] (by rw [oneEach_length]; exact hk)

lemma CState.push_depths_old {d : ℕ} (st : CState d) (g : Gate) (hfan hrb)
    {k : ℕ} (hk : k < ((d + 1) + (d + 1)) + st.gates.length) :
    (depthsOf ((d + 1) + (d + 1)) (st.push g hfan hrb).gates).getD k 0 =
      (depthsOf ((d + 1) + (d + 1)) st.gates).getD k 0 := by
  exact depthsOf_append_getD_lt ((d + 1) + (d + 1)) st.gates [g] hk

lemma CState.push_wires_new {d : ℕ} (st : CState d) (g : Gate) (hfan hrb)
    (x y : Fin (d + 1)) :
    (wiresOf (oneEach x y) (st.push g hfan hrb).gates).getD
      (((d + 1) + (d + 1)) + st.gates.length) false =
      g.op.eval (g.inputs.map fun a => (wiresOf (oneEach x y) st.gates).getD a false) := by
  dsimp [CState.push]
  rw [wiresOf_append, List.foldl_cons, List.foldl_nil]
  have hlen : (wiresOf (oneEach x y) st.gates).length = ((d + 1) + (d + 1)) + st.gates.length := by
    rw [wiresOf_length, oneEach_length]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp [hlen]

lemma CState.push_depths_new {d : ℕ} (st : CState d) (g : Gate) (hfan hrb) :
    (depthsOf ((d + 1) + (d + 1)) (st.push g hfan hrb).gates).getD
      (((d + 1) + (d + 1)) + st.gates.length) 0 =
      (g.inputs.map fun a => (depthsOf ((d + 1) + (d + 1)) st.gates).getD a 0).foldr max 0 +
        (nlGate g).toNat := by
  dsimp [CState.push]
  rw [depthsOf_append, List.foldl_cons, List.foldl_nil]
  have hlen : (depthsOf ((d + 1) + (d + 1)) st.gates).length =
      ((d + 1) + (d + 1)) + st.gates.length := depthsOf_length _ _
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp [hlen]

def CState.Extends {d : ℕ} (st1 st2 : CState d) : Prop :=
  ∃ ext : List Gate, st2.gates = st1.gates ++ ext

lemma CState.Extends.refl {d : ℕ} (st : CState d) : st.Extends st := ⟨[], by simp⟩

lemma CState.Extends.trans {d : ℕ} {s1 s2 s3 : CState d}
    (h12 : s1.Extends s2) (h23 : s2.Extends s3) : s1.Extends s3 := by
  obtain ⟨e1, he1⟩ := h12
  obtain ⟨e2, he2⟩ := h23
  exact ⟨e1 ++ e2, by rw [he2, he1, List.append_assoc]⟩

lemma CState.Extends.push {d : ℕ} (st : CState d) (g : Gate) (hfan hrb) :
    st.Extends (st.push g hfan hrb) := ⟨[g], rfl⟩

lemma CState.Extends.length_le {d : ℕ} {s1 s2 : CState d} (h : s1.Extends s2) :
    s1.gates.length ≤ s2.gates.length := by
  obtain ⟨e, he⟩ := h
  rw [he, List.length_append]
  omega

lemma CState.Extends.wires_eq {d : ℕ} {s1 s2 : CState d} (h : s1.Extends s2)
    (x y : Fin (d + 1)) {k : ℕ} (hk : k < ((d + 1) + (d + 1)) + s1.gates.length) :
    (wiresOf (oneEach x y) s2.gates).getD k false =
      (wiresOf (oneEach x y) s1.gates).getD k false := by
  obtain ⟨e, he⟩ := h
  rw [he]
  exact wiresOf_append_getD_lt (oneEach x y) s1.gates e (by rw [oneEach_length]; exact hk)

lemma CState.Extends.depths_eq {d : ℕ} {s1 s2 : CState d} (h : s1.Extends s2)
    {k : ℕ} (hk : k < ((d + 1) + (d + 1)) + s1.gates.length) :
    (depthsOf ((d + 1) + (d + 1)) s2.gates).getD k 0 =
      (depthsOf ((d + 1) + (d + 1)) s1.gates).getD k 0 := by
  obtain ⟨e, he⟩ := h
  rw [he]
  exact depthsOf_append_getD_lt ((d + 1) + (d + 1)) s1.gates e hk

lemma nlGate_false_gate : nlGate ⟨GateOp.or, []⟩ = false := rfl
lemma nlGate_mod2 (u v : ℕ) : nlGate ⟨GateOp.mod 2, [u, v]⟩ = false := rfl
lemma nlGate_not (u : ℕ) : nlGate ⟨GateOp.not, [u]⟩ = false := rfl
lemma nlGate_and (u v : ℕ) : nlGate ⟨GateOp.and, [u, v]⟩ = true := rfl

lemma eval_not_mod2 (a b : Bool) :
    GateOp.not.eval [(GateOp.mod 2).eval [a, b]] = xor a b := by
  cases a <;> cases b <;> decide

lemma mkFalse {d : ℕ} (st : CState d) :
    ∃ (st' : CState d) (out : ℕ),
      st.Extends st' ∧
      st'.gates.countP nlGate = st.gates.countP nlGate ∧
      out < ((d + 1) + (d + 1)) + st'.gates.length ∧
      (depthsOf ((d + 1) + (d + 1)) st'.gates).getD out 0 = 0 ∧
      ∀ x y : Fin (d + 1), b2z ((wiresOf (oneEach x y) st'.gates).getD out false) = 0 := by
  let g : Gate := ⟨GateOp.or, []⟩
  let st' := st.push g (by simp [g]) (by intro a ha; simp [g] at ha)
  refine ⟨st', ((d + 1) + (d + 1)) + st.gates.length, CState.Extends.push _ _ _ _, ?_, ?_, ?_, ?_⟩
  · rw [CState.push_countP]; simp [g, nlGate_false_gate]
  · rw [CState.push_length]; omega
  · rw [CState.push_depths_new]; simp [g, nlGate_false_gate]
  · intro x y; rw [CState.push_wires_new]; simp [g, GateOp.eval, b2z]

lemma mkXor {d : ℕ} (st : CState d) (u v : ℕ)
    (hu : u < ((d + 1) + (d + 1)) + st.gates.length)
    (hv : v < ((d + 1) + (d + 1)) + st.gates.length) :
    ∃ (st' : CState d) (out : ℕ),
      st.Extends st' ∧
      st'.gates.countP nlGate = st.gates.countP nlGate ∧
      out < ((d + 1) + (d + 1)) + st'.gates.length ∧
      (depthsOf ((d + 1) + (d + 1)) st'.gates).getD out 0 =
        max ((depthsOf ((d + 1) + (d + 1)) st.gates).getD u 0)
            ((depthsOf ((d + 1) + (d + 1)) st.gates).getD v 0) ∧
      ∀ x y : Fin (d + 1),
        b2z ((wiresOf (oneEach x y) st'.gates).getD out false) =
          b2z ((wiresOf (oneEach x y) st.gates).getD u false) +
          b2z ((wiresOf (oneEach x y) st.gates).getD v false) := by
  set w := (d + 1) + (d + 1)
  let g1 : Gate := ⟨GateOp.mod 2, [u, v]⟩
  let st1 := st.push g1 (by simp [g1]) (by intro a ha; simp [g1] at ha; rcases ha with rfl | rfl <;> assumption)
  set w1 := w + st.gates.length
  have hw1 : w1 < w + st1.gates.length := by rw [CState.push_length]; omega
  let g2 : Gate := ⟨GateOp.not, [w1]⟩
  let st2 := st1.push g2 (by simp [g2]) (by intro a ha; simp [g2] at ha; subst ha; exact hw1)
  set w2 := w + st1.gates.length
  have hext : st.Extends st2 := (CState.Extends.push _ _ _ _).trans (CState.Extends.push _ _ _ _)
  refine ⟨st2, w2, hext, ?_, ?_, ?_, ?_⟩
  · rw [CState.push_countP, CState.push_countP]
    simp [g1, g2, nlGate_mod2, nlGate_not]
  · rw [CState.push_length]; omega
  · rw [CState.push_depths_new]
    simp only [g2, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
      nlGate_not, Bool.toNat_false, add_zero, Nat.max_zero]
    rw [CState.push_depths_new]
    simp only [g1, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
      nlGate_mod2, Bool.toNat_false, add_zero, Nat.max_zero]
    rfl
  · intro x y
    rw [CState.push_wires_new]
    simp only [g2, List.map_cons, List.map_nil]
    rw [CState.push_wires_new]
    simp only [g1, List.map_cons, List.map_nil]
    rw [eval_not_mod2, b2z_xor]

lemma mkAnd {d : ℕ} (st : CState d) (u v : ℕ)
    (hu : u < ((d + 1) + (d + 1)) + st.gates.length)
    (hv : v < ((d + 1) + (d + 1)) + st.gates.length) :
    ∃ (st' : CState d) (out : ℕ),
      st.Extends st' ∧
      st'.gates.countP nlGate = st.gates.countP nlGate + 1 ∧
      out < ((d + 1) + (d + 1)) + st'.gates.length ∧
      (depthsOf ((d + 1) + (d + 1)) st'.gates).getD out 0 =
        max ((depthsOf ((d + 1) + (d + 1)) st.gates).getD u 0)
            ((depthsOf ((d + 1) + (d + 1)) st.gates).getD v 0) + 1 ∧
      ∀ x y : Fin (d + 1),
        b2z ((wiresOf (oneEach x y) st'.gates).getD out false) =
          b2z ((wiresOf (oneEach x y) st.gates).getD u false) *
          b2z ((wiresOf (oneEach x y) st.gates).getD v false) := by
  let g : Gate := ⟨GateOp.and, [u, v]⟩
  let st' := st.push g (by simp [g]) (by intro a ha; simp [g] at ha; rcases ha with rfl | rfl <;> assumption)
  refine ⟨st', ((d + 1) + (d + 1)) + st.gates.length, CState.Extends.push _ _ _ _, ?_, ?_, ?_, ?_⟩
  · rw [CState.push_countP]; simp [g, nlGate_and]
  · rw [CState.push_length]; omega
  · rw [CState.push_depths_new]; simp [g, nlGate_and]
  · intro x y
    rw [CState.push_wires_new]
    simp only [g, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
      id_eq, Bool.and_true]
    exact b2z_and _ _

lemma mkXorList {d : ℕ} (st : CState d) (ws : List ℕ) (B : ℕ)
    (hws : ∀ u ∈ ws, u < ((d + 1) + (d + 1)) + st.gates.length)
    (hdep : ∀ u ∈ ws, (depthsOf ((d + 1) + (d + 1)) st.gates).getD u 0 ≤ B) :
    ∃ (st' : CState d) (out : ℕ),
      st.Extends st' ∧
      st'.gates.countP nlGate = st.gates.countP nlGate ∧
      out < ((d + 1) + (d + 1)) + st'.gates.length ∧
      (depthsOf ((d + 1) + (d + 1)) st'.gates).getD out 0 ≤ B ∧
      ∀ x y : Fin (d + 1),
        b2z ((wiresOf (oneEach x y) st'.gates).getD out false) =
          (ws.map fun u => b2z ((wiresOf (oneEach x y) st.gates).getD u false)).sum := by
  induction ws generalizing st with
  | nil =>
    obtain ⟨st', out, hext, hcnt, hout, hd, hv⟩ := mkFalse st
    exact ⟨st', out, hext, hcnt, hout, by omega, by intro x y; simp only [List.map_nil, List.sum_nil]; exact hv x y⟩
  | cons u rest ih =>
    have hu : u < ((d + 1) + (d + 1)) + st.gates.length := hws u (by simp)
    have hdu : (depthsOf ((d + 1) + (d + 1)) st.gates).getD u 0 ≤ B := hdep u (by simp)
    obtain ⟨st1, out1, hext1, hcnt1, hout1, hd1, hv1⟩ :=
      ih st (fun a ha => hws a (by simp [ha])) (fun a ha => hdep a (by simp [ha]))
    have hu1 : u < ((d + 1) + (d + 1)) + st1.gates.length := by
      have := hext1.length_le; omega
    obtain ⟨st2, out2, hext2, hcnt2, hout2, hd2, hv2⟩ := mkXor st1 u out1 hu1 hout1
    refine ⟨st2, out2, hext1.trans hext2, by omega, hout2, ?_, ?_⟩
    · rw [hd2, hext1.depths_eq hu]
      exact Nat.max_le.mpr ⟨hdu, hd1⟩
    · intro x y
      rw [hv2 x y, hext1.wires_eq x y hu, hv1 x y]
      simp

def padVec {d : ℕ} (v : Fin d → F2) (x : Fin (d + 1)) : F2 :=
  Fin.cases 0 v x

lemma list_sum_filter_left {d : ℕ} (v : Fin d → F2) (l : List (Fin d)) (hnd : l.Nodup)
    (x : Fin (d + 1)) :
    ((l.filter fun i => decide (v i = 1)).map
      fun i => b2z (decide (i.val + 1 = x.val))).sum =
      Fin.cases 0 (fun k => if k ∈ l then v k else 0) x := by
  induction l with
  | nil =>
    cases x using Fin.cases with
    | zero => simp
    | succ k => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    have ihl := ih hnd.2
    rw [List.filter_cons]
    cases x using Fin.cases with
    | zero =>
      simp only [Fin.cases_zero] at ihl ⊢
      by_cases hva : v a = 1
      · simp only [hva, decide_true, ↓reduceIte, List.map_cons, List.sum_cons]
        have hne0 : ¬(a.val + 1 = (0 : Fin (d + 1)).val) := by simp
        have hbf : b2z (decide (a.val + 1 = (0 : Fin (d + 1)).val)) = 0 := by simp [hne0, b2z]
        rw [hbf, zero_add, ihl]
      · simp only [hva, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact ihl
    | succ k =>
      simp only [Fin.cases_succ] at ihl ⊢
      by_cases hka : k = a
      · subst hka
        have hnot : k ∉ l := hnd.1
        simp only [List.mem_cons, true_or, ↓reduceIte]
        rw [if_neg hnot] at ihl
        by_cases hvk : v k = 1
        · simp only [hvk, decide_true, ↓reduceIte, List.map_cons, List.sum_cons, ihl, add_zero]
          have hbt : b2z (decide (k.val + 1 = k.succ.val)) = 1 := by simp [b2z]
          exact hbt
        · have hv0 : v k = 0 := zmod2_eq_zero_of_ne_one hvk
          simp only [hvk, decide_false, Bool.false_eq_true, ↓reduceIte, hv0]
          exact ihl
      · have hne : a.val + 1 ≠ (k.succ).val := by
          intro heq
          apply hka
          exact Fin.ext (by simp at heq; omega)
        simp only [List.mem_cons, hka, false_or]
        by_cases hva : v a = 1
        · simp only [hva, decide_true, ↓reduceIte, List.map_cons, List.sum_cons]
          have hbf : b2z (decide (a.val + 1 = k.succ.val)) = 0 := by rw [decide_eq_false hne]; rfl
          rw [hbf, zero_add, ihl]
        · simp only [hva, decide_false, Bool.false_eq_true, ↓reduceIte]
          exact ihl

lemma mkLeftLin {d : ℕ} (st : CState d) (v : Fin d → F2) :
    ∃ (st' : CState d) (out : ℕ),
      st.Extends st' ∧
      st'.gates.countP nlGate = st.gates.countP nlGate ∧
      out < ((d + 1) + (d + 1)) + st'.gates.length ∧
      (depthsOf ((d + 1) + (d + 1)) st'.gates).getD out 0 = 0 ∧
      ∀ x y : Fin (d + 1),
        b2z ((wiresOf (oneEach x y) st'.gates).getD out false) = padVec v x := by
  let ws : List ℕ := ((List.finRange d).filter fun i => decide (v i = 1)).map fun i => i.val + 1
  have hws : ∀ u ∈ ws, u < ((d + 1) + (d + 1)) + st.gates.length := by
    intro u hu
    simp only [ws, List.mem_map, List.mem_filter, List.mem_finRange, true_and] at hu
    obtain ⟨i, _, rfl⟩ := hu
    omega
  have hdep : ∀ u ∈ ws, (depthsOf ((d + 1) + (d + 1)) st.gates).getD u 0 ≤ 0 := by
    intro u hu
    simp only [ws, List.mem_map, List.mem_filter, List.mem_finRange, true_and] at hu
    obtain ⟨i, _, rfl⟩ := hu
    rw [depthsOf_getD_input _ _ (by omega)]
  obtain ⟨st', out, hext, hcnt, hout, hd, hv⟩ := mkXorList st ws 0 hws hdep
  refine ⟨st', out, hext, hcnt, hout, Nat.le_zero.mp hd, fun x y => ?_⟩
  rw [hv x y]
  simp only [ws, List.map_map]
  have hmap : (((List.finRange d).filter fun i => decide (v i = 1)).map
      ((fun u => b2z ((wiresOf (oneEach x y) st.gates).getD u false)) ∘ fun i => i.val + 1)) =
      (((List.finRange d).filter fun i => decide (v i = 1)).map
        fun i => b2z (decide (i.val + 1 = x.val))) := by
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    rw [wiresOf_getD_input _ _ (by rw [oneEach_length]; omega)]
    rw [oneEach_getD_left x y (by omega)]
  rw [hmap, list_sum_filter_left v (List.finRange d) (List.nodup_finRange d) x]
  cases x using Fin.cases with
  | zero => rfl
  | succ k => simp [padVec]

lemma mkRightLin {d : ℕ} (st : CState d) (v : Fin d → F2) :
    ∃ (st' : CState d) (out : ℕ),
      st.Extends st' ∧
      st'.gates.countP nlGate = st.gates.countP nlGate ∧
      out < ((d + 1) + (d + 1)) + st'.gates.length ∧
      (depthsOf ((d + 1) + (d + 1)) st'.gates).getD out 0 = 0 ∧
      ∀ x y : Fin (d + 1),
        b2z ((wiresOf (oneEach x y) st'.gates).getD out false) = padVec v y := by
  let ws : List ℕ :=
    ((List.finRange d).filter fun j => decide (v j = 1)).map fun j => (d + 1) + (j.val + 1)
  have hws : ∀ u ∈ ws, u < ((d + 1) + (d + 1)) + st.gates.length := by
    intro u hu
    simp only [ws, List.mem_map, List.mem_filter, List.mem_finRange, true_and] at hu
    obtain ⟨j, _, rfl⟩ := hu
    omega
  have hdep : ∀ u ∈ ws, (depthsOf ((d + 1) + (d + 1)) st.gates).getD u 0 ≤ 0 := by
    intro u hu
    simp only [ws, List.mem_map, List.mem_filter, List.mem_finRange, true_and] at hu
    obtain ⟨j, _, rfl⟩ := hu
    rw [depthsOf_getD_input _ _ (by omega)]
  obtain ⟨st', out, hext, hcnt, hout, hd, hv⟩ := mkXorList st ws 0 hws hdep
  refine ⟨st', out, hext, hcnt, hout, Nat.le_zero.mp hd, fun x y => ?_⟩
  rw [hv x y]
  simp only [ws, List.map_map]
  have hmap : (((List.finRange d).filter fun j => decide (v j = 1)).map
      ((fun u => b2z ((wiresOf (oneEach x y) st.gates).getD u false)) ∘
        fun j => (d + 1) + (j.val + 1))) =
      (((List.finRange d).filter fun j => decide (v j = 1)).map
        fun j => b2z (decide (j.val + 1 = y.val))) := by
    apply List.map_congr_left
    intro j _
    simp only [Function.comp_apply]
    rw [wiresOf_getD_input _ _ (by rw [oneEach_length]; omega)]
    rw [oneEach_getD_right x y (by omega) (by omega)]
    simp
  rw [hmap, list_sum_filter_left v (List.finRange d) (List.nodup_finRange d) y]
  cases y using Fin.cases with
  | zero => rfl
  | succ k => simp [padVec]

lemma padVec_mul {d : ℕ} (u v : Fin d → F2) (x : Fin (d + 1)) :
    padVec (fun i => u i * v i) x = padVec u x * padVec v x := by
  cases x using Fin.cases with
  | zero => simp [padVec]
  | succ k => simp [padVec]

lemma padTable_rk2Mat {d : ℕ} (a b c e : Fin d → F2) (x y : Fin (d + 1)) :
    b2z (padTable (rk2Mat a b c e) x y) =
      padVec a x * padVec b y + padVec c x * padVec e y := by
  cases x using Fin.cases with
  | zero => simp [padTable, padVec, b2z]
  | succ i =>
    cases y using Fin.cases with
    | zero => simp [padTable, padVec, b2z]
    | succ j =>
      simp only [padTable, Fin.cases_succ, padVec, rk2Mat]
      exact b2z_nonzero _

lemma mkRank2 {d : ℕ} (st : CState d) (a b c e : Fin d → F2) :
    ∃ (st' : CState d) (out : ℕ),
      st.Extends st' ∧
      st'.gates.countP nlGate = st.gates.countP nlGate + 1 ∧
      out < ((d + 1) + (d + 1)) + st'.gates.length ∧
      (depthsOf ((d + 1) + (d + 1)) st'.gates).getD out 0 ≤ 1 ∧
      ∀ x y : Fin (d + 1),
        b2z ((wiresOf (oneEach x y) st'.gates).getD out false) =
          b2z (padTable (rk2Mat a b c e) x y) := by
  obtain ⟨s1, w1x, e1, c1, hw1x, d1x, v1x⟩ := mkLeftLin st a
  obtain ⟨s2, w1y, e2, c2, hw1y, d1y, v1y⟩ := mkRightLin s1 e
  have hw1x2 : w1x < ((d + 1) + (d + 1)) + s2.gates.length := by have := e2.length_le; omega
  obtain ⟨s3, wL1, e3, c3, hwL1, dL1, vL1⟩ := mkXor s2 w1x w1y hw1x2 hw1y
  have hdL1 : (depthsOf ((d + 1) + (d + 1)) s3.gates).getD wL1 0 = 0 := by
    rw [dL1, e2.depths_eq hw1x, d1x, d1y]; rfl
  have hvL1 : ∀ x y, b2z ((wiresOf (oneEach x y) s3.gates).getD wL1 false) =
      padVec a x + padVec e y := by
    intro x y; rw [vL1 x y, e2.wires_eq x y hw1x, v1x x y, v1y x y]
  obtain ⟨s4, w2x, e4, c4, hw2x, d2x, v2x⟩ := mkLeftLin s3 c
  obtain ⟨s5, w2y, e5, c5, hw2y, d2y, v2y⟩ := mkRightLin s4 b
  have hw2x5 : w2x < ((d + 1) + (d + 1)) + s5.gates.length := by have := e5.length_le; omega
  obtain ⟨s6, wL2, e6, c6, hwL2, dL2, vL2⟩ := mkXor s5 w2x w2y hw2x5 hw2y
  have hdL2 : (depthsOf ((d + 1) + (d + 1)) s6.gates).getD wL2 0 = 0 := by
    rw [dL2, e5.depths_eq hw2x, d2x, d2y]; rfl
  have hvL2 : ∀ x y, b2z ((wiresOf (oneEach x y) s6.gates).getD wL2 false) =
      padVec c x + padVec b y := by
    intro x y; rw [vL2 x y, e5.wires_eq x y hw2x, v2x x y, v2y x y]
  have e36 : s3.Extends s6 := e4.trans (e5.trans e6)
  have hwL1_6 : wL1 < ((d + 1) + (d + 1)) + s6.gates.length := by have := e36.length_le; omega
  obtain ⟨s7, wP, e7, c7, hwP, dP, vP⟩ := mkAnd s6 wL1 wL2 hwL1_6 hwL2
  have hdP : (depthsOf ((d + 1) + (d + 1)) s7.gates).getD wP 0 = 1 := by
    rw [dP, e36.depths_eq hwL1, hdL1, hdL2]; rfl
  have hvP : ∀ x y, b2z ((wiresOf (oneEach x y) s7.gates).getD wP false) =
      (padVec a x + padVec e y) * (padVec c x + padVec b y) := by
    intro x y; rw [vP x y, e36.wires_eq x y hwL1, hvL1 x y, hvL2 x y]
  obtain ⟨s8, wCx, e8, c8, hwCx, dCx, vCx⟩ := mkLeftLin s7 (fun i => a i * c i)
  have hwP8 : wP < ((d + 1) + (d + 1)) + s8.gates.length := by have := e8.length_le; omega
  obtain ⟨s9, wT, e9, c9, hwT, dT, vT⟩ := mkXor s8 wP wCx hwP8 hwCx
  have hdT : (depthsOf ((d + 1) + (d + 1)) s9.gates).getD wT 0 = 1 := by
    rw [dT, e8.depths_eq hwP, hdP, dCx]; rfl
  obtain ⟨s10, wCy, e10, c10, hwCy, dCy, vCy⟩ := mkRightLin s9 (fun j => b j * e j)
  have hwT10 : wT < ((d + 1) + (d + 1)) + s10.gates.length := by have := e10.length_le; omega
  obtain ⟨s11, wOut, e11, c11, hwOut, dOut, vOut⟩ := mkXor s10 wT wCy hwT10 hwCy
  have hext : st.Extends s11 :=
    e1.trans (e2.trans (e3.trans (e36.trans (e7.trans (e8.trans (e9.trans (e10.trans e11)))))))
  refine ⟨s11, wOut, hext, by omega, hwOut, ?_, ?_⟩
  · rw [dOut, e10.depths_eq hwT, hdT, dCy]; simp
  · intro x y
    rw [vOut x y, e10.wires_eq x y hwT, vT x y, e8.wires_eq x y hwP, hvP x y, vCx x y, vCy x y]
    rw [padVec_mul, padVec_mul, padTable_rk2Mat]
    have hsum :
        ((padVec a x + padVec e y) * (padVec c x + padVec b y) +
          padVec a x * padVec c x + padVec b y * padVec e y) +
        (padVec a x * padVec b y + padVec c x * padVec e y) =
        (2 : F2) * (padVec a x * padVec c x + padVec b y * padVec e y +
          padVec a x * padVec b y + padVec c x * padVec e y) := by ring
    rw [zmod2_two, zero_mul] at hsum
    exact zmod2_eq_of_add_eq_zero hsum

lemma buildRank2Bank {d : ℕ} (m : ℕ) (a b c e : Fin m → Fin d → F2) :
    ∃ (st : CState d) (ws : Fin m → ℕ),
      st.gates.countP nlGate = m ∧
      (∀ l : Fin m, ws l < ((d + 1) + (d + 1)) + st.gates.length) ∧
      (∀ l : Fin m, (depthsOf ((d + 1) + (d + 1)) st.gates).getD (ws l) 0 ≤ 1) ∧
      (∀ l : Fin m, ∀ x y : Fin (d + 1),
        b2z ((wiresOf (oneEach x y) st.gates).getD (ws l) false) =
          b2z (padTable (rk2Mat (a l) (b l) (c l) (e l)) x y)) := by
  induction m with
  | zero =>
    exact ⟨CState.empty d, fun l => Fin.elim0 l, rfl,
      fun l => Fin.elim0 l, fun l => Fin.elim0 l, fun l => Fin.elim0 l⟩
  | succ m ih =>
    obtain ⟨st1, ws1, hcnt1, hlt1, hdep1, hval1⟩ :=
      ih (fun l => a l.castSucc) (fun l => b l.castSucc)
         (fun l => c l.castSucc) (fun l => e l.castSucc)
    obtain ⟨st2, out, hext, hcnt2, hout, hdout, hvout⟩ :=
      mkRank2 st1 (a (Fin.last m)) (b (Fin.last m)) (c (Fin.last m)) (e (Fin.last m))
    refine ⟨st2, Fin.lastCases out ws1, by omega, ?_, ?_, ?_⟩
    · intro l
      refine Fin.lastCases ?_ ?_ l
      · simpa using hout
      · intro l'; simp only [Fin.lastCases_castSucc]
        have := hext.length_le; have := hlt1 l'; omega
    · intro l
      refine Fin.lastCases ?_ ?_ l
      · simpa using hdout
      · intro l'; simp only [Fin.lastCases_castSucc]
        rw [hext.depths_eq (hlt1 l')]; exact hdep1 l'
    · intro l x y
      refine Fin.lastCases ?_ ?_ l
      · simpa using hvout x y
      · intro l'; simp only [Fin.lastCases_castSucc]
        rw [hext.wires_eq x y (hlt1 l')]; exact hval1 l' x y

lemma list_sum_filter_coeff {m : ℕ} (coeff : Fin m → F2) (f : Fin m → F2) :
    (((List.finRange m).filter fun l => decide (coeff l = 1)).map f).sum =
      ∑ l : Fin m, coeff l * f l := by
  have haux : ∀ (l : List (Fin m)),
      ((l.filter fun i => decide (coeff i = 1)).map f).sum =
        (l.map fun i => coeff i * f i).sum := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      rw [List.filter_cons, List.map_cons, List.sum_cons]
      by_cases hci : coeff i = 1
      · simp [hci, ih]
      · have h0 : coeff i = 0 := zmod2_eq_zero_of_ne_one hci
        simp [hci, h0, ih]
  rw [haux]
  rw [← Fin.sum_univ_def]

lemma padTable_linear_comb {d m : ℕ} (G : Fin m → Matrix (Fin d) (Fin d) F2)
    (coeff : Fin m → F2) (x y : Fin (d + 1)) :
    b2z (padTable (∑ l : Fin m, coeff l • G l) x y) =
      ∑ l : Fin m, coeff l * b2z (padTable (G l) x y) := by
  cases x using Fin.cases with
  | zero => simp [padTable, b2z]
  | succ i =>
    cases y using Fin.cases with
    | zero => simp [padTable, b2z]
    | succ j =>
      simp only [padTable, Fin.cases_succ, b2z_nonzero, Matrix.sum_apply,
        Matrix.smul_apply, smul_eq_mul]

theorem rk2_span_to_bank {d t : ℕ} {U : Matrix (Fin d) (Fin d) F2}
    (m : ℕ) (hm : m ≤ t) (a b c e : Fin m → Fin d → F2)
    (hspan : ∀ H : Matrix (Fin d) (Fin d) F2, IsAlt H →
      U * H * U.transpose + H ∈
        Submodule.span F2 (Set.range fun l : Fin m => rk2Mat (a l) (b l) (c l) (e l))) :
    Bank d U t := by
  classical
  let G : Fin m → Matrix (Fin d) (Fin d) F2 := fun l => rk2Mat (a l) (b l) (c l) (e l)
  obtain ⟨st0, ws, hcnt0, hlt0, hdep0, hval0⟩ := buildRank2Bank m a b c e
  have hbuild : ∀ (Hs : List (Matrix (Fin d) (Fin d) F2)),
      ∃ (st : CState d) (tap : Matrix (Fin d) (Fin d) F2 → ℕ),
        st0.Extends st ∧
        st.gates.countP nlGate = m ∧
        ∀ H ∈ Hs, IsAlt H →
          tap H < ((d + 1) + (d + 1)) + st.gates.length ∧
          (depthsOf ((d + 1) + (d + 1)) st.gates).getD (tap H) 0 ≤ 1 ∧
          Represents (padTable (U * H * U.transpose + H)) ⟨st.gates, tap H⟩ := by
    intro Hs
    induction Hs with
    | nil =>
      exact ⟨st0, fun _ => 0, CState.Extends.refl _, hcnt0, fun _ h => by simp at h⟩
    | cons H rest ih =>
      obtain ⟨st1, tap1, hext1, hcnt1, hrest⟩ := ih
      by_cases hH : IsAlt H
      · have hmem := hspan H hH
        rw [Submodule.mem_span_range_iff_exists_fun] at hmem
        obtain ⟨coeff, hcoeff⟩ := hmem
        let idxList := ((List.finRange m).filter fun l => decide (coeff l = 1)).map ws
        have hws1 : ∀ u ∈ idxList, u < ((d + 1) + (d + 1)) + st1.gates.length := by
          intro u hu
          simp only [idxList, List.mem_map] at hu
          obtain ⟨l, _, rfl⟩ := hu
          have := hext1.length_le; have := hlt0 l; omega
        have hdp1 : ∀ u ∈ idxList, (depthsOf ((d + 1) + (d + 1)) st1.gates).getD u 0 ≤ 1 := by
          intro u hu
          simp only [idxList, List.mem_map] at hu
          obtain ⟨l, _, rfl⟩ := hu
          rw [hext1.depths_eq (hlt0 l)]; exact hdep0 l
        obtain ⟨st2, out, hext2, hcnt2, hout, hdout, hvout⟩ := mkXorList st1 idxList 1 hws1 hdp1
        refine ⟨st2, fun H' => if H' = H then out else tap1 H',
          hext1.trans hext2, by omega, fun H' hH' hAlt => ?_⟩
        rw [List.mem_cons] at hH'
        by_cases heq : H' = H
        · subst heq
          simp only [↓reduceIte]
          refine ⟨hout, hdout, fun x y => ?_⟩
          apply b2z_inj
          unfold Circuit.eval Circuit.wires
          change b2z ((wiresOf (oneEach x y) st2.gates).getD out false) = _
          rw [hvout x y]
          simp only [idxList, List.map_map]
          have hcongr : (((List.finRange m).filter fun l => decide (coeff l = 1)).map
              ((fun u => b2z ((wiresOf (oneEach x y) st1.gates).getD u false)) ∘ ws)) =
              (((List.finRange m).filter fun l => decide (coeff l = 1)).map
                fun l => b2z (padTable (G l) x y)) := by
            apply List.map_congr_left
            intro l _
            simp only [Function.comp_apply]
            rw [hext1.wires_eq x y (hlt0 l)]
            exact hval0 l x y
          rw [hcongr, list_sum_filter_coeff, ← padTable_linear_comb, hcoeff]
        · simp only [heq, ↓reduceIte]
          have hmem_rest : H' ∈ rest := hH'.resolve_left heq
          obtain ⟨htlt, htdep, htrep⟩ := hrest H' hmem_rest hAlt
          refine ⟨by have := hext2.length_le; omega,
            by rw [hext2.depths_eq htlt]; exact htdep,
            fun x y => ?_⟩
          unfold Circuit.eval Circuit.wires
          change (wiresOf (oneEach x y) st2.gates).getD (tap1 H') false = _
          rw [hext2.wires_eq x y htlt]
          exact htrep x y
      · refine ⟨st1, tap1, hext1, hcnt1, fun H' hH' hAlt => ?_⟩
        rw [List.mem_cons] at hH'
        rcases hH' with rfl | hmem_rest
        · exact absurd hAlt hH
        · exact hrest H' hmem_rest hAlt
  obtain ⟨st, tap, _, hcnt, hall⟩ := hbuild (Finset.univ : Finset (Matrix (Fin d) (Fin d) F2)).toList
  refine ⟨⟨st.gates, 0⟩, tap, st.rb, st.fanin, by change st.gates.countP nlGate ≤ t; omega, fun H hH => ?_⟩
  have hmem : H ∈ (Finset.univ : Finset (Matrix (Fin d) (Fin d) F2)).toList := by simp
  obtain ⟨_, hdep, hrep⟩ := hall H hmem hH
  exact ⟨hdep, hrep⟩

-- ============================================================================
-- Part 4: Adapted Coordinates for a ZMod 2 Involution (U * U = 1)
-- ============================================================================

def J0 (d r : ℕ) : Matrix (Fin d) (Fin d) F2 :=
  fun i j => if i.val < r ∧ j.val = r + i.val then 1 else 0

def U0 (d r : ℕ) : Matrix (Fin d) (Fin d) F2 := 1 + J0 d r

lemma involution_rank_le {d : ℕ} (U : Matrix (Fin d) (Fin d) F2) (hU : U * U = 1) :
    (U - 1) * (U - 1) = 0 ∧
    LinearMap.range (U - 1).mulVecLin ≤ LinearMap.ker (U - 1).mulVecLin ∧
    2 * (U - 1).rank ≤ d := by
  set N := U - 1
  have hN2 : N * N = 0 := by
    ext i j
    have h1 : (U - 1) * (U - 1) = U * U - U - U + 1 := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one]
      abel
    rw [h1, hU]
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.zero_apply]
    have hsub : ∀ a b : F2, a - b - b + a = 0 := by
      intro a b
      rcases zmod2_eq_zero_or_one a with rfl | rfl <;>
      rcases zmod2_eq_zero_or_one b with rfl | rfl <;> rfl
    exact hsub _ _
  have hsub_ker : LinearMap.range N.mulVecLin ≤ LinearMap.ker N.mulVecLin := by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    change N.mulVec (N.mulVec x) = 0
    rw [Matrix.mulVec_mulVec, hN2, Matrix.zero_mulVec]
  have hr_eq : N.rank = Module.finrank F2 (LinearMap.range N.mulVecLin) := rfl
  have hr_le_ker : N.rank ≤ Module.finrank F2 (LinearMap.ker N.mulVecLin) :=
    Submodule.finrank_mono hsub_ker
  have hrn : Module.finrank F2 (LinearMap.range N.mulVecLin) +
      Module.finrank F2 (LinearMap.ker N.mulVecLin) = d := by
    simpa [Module.finrank_fin_fun] using LinearMap.finrank_range_add_finrank_ker N.mulVecLin
  exact ⟨hN2, hsub_ker, by omega⟩

lemma adapted_cols_li {d r : ℕ} (N : Matrix (Fin d) (Fin d) F2) (h2r : 2 * r ≤ d)
    (hsub_ker : LinearMap.range N.mulVecLin ≤ LinearMap.ker N.mulVecLin)
    (bA : Module.Basis (Fin r) F2 (LinearMap.range N.mulVecLin))
    (bB : Fin r → (Fin d → F2))
    (hbB_spec : ∀ i : Fin r, N.mulVec (bB i) = (bA i : Fin d → F2))
    (Csub : Submodule F2 (Fin d → F2))
    (hCsub_le : Csub ≤ LinearMap.ker N.mulVecLin)
    (hCsub_disj : Disjoint (LinearMap.range N.mulVecLin) Csub)
    (bC : Module.Basis (Fin (d - 2 * r)) F2 Csub) :
    LinearIndependent F2 (fun j : Fin d =>
      if h1 : j.val < r then (bA ⟨j.val, h1⟩ : Fin d → F2)
      else if h2 : j.val < 2 * r then bB ⟨j.val - r, by omega⟩
      else (bC ⟨j.val - 2 * r, by omega⟩ : Fin d → F2)) := by
  classical
  let cols : Fin d → (Fin d → F2) := fun j =>
    if h1 : j.val < r then (bA ⟨j.val, h1⟩ : Fin d → F2)
    else if h2 : j.val < 2 * r then bB ⟨j.val - r, by omega⟩
    else (bC ⟨j.val - 2 * r, by omega⟩ : Fin d → F2)
  change LinearIndependent F2 cols
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hN_apply : N.mulVecLin (∑ j : Fin d, g j • cols j) = 0 := by
    change N.mulVec (∑ j : Fin d, g j • cols j) = 0
    rw [hg, Matrix.mulVec_zero]
  have hN_sum : ∑ j : Fin d, g j • N.mulVec (cols j) = 0 := by
    simpa [map_sum, map_smul] using hN_apply
  have hN_col : ∀ j : Fin d, N.mulVec (cols j) =
      if h : r ≤ j.val ∧ j.val < 2 * r then (bA ⟨j.val - r, by omega⟩ : Fin d → F2) else 0 := by
    intro j
    dsimp only [cols]
    split_ifs with h1 h2 h3
    · omega
    · exact hsub_ker (bA ⟨j.val, h1⟩).2
    · exact hbB_spec ⟨j.val - r, by omega⟩
    · omega
    · omega
    · exact hCsub_le (bC ⟨j.val - 2 * r, by omega⟩).2
  have hB_sum : ∑ i : Fin r, g ⟨r + i.val, by omega⟩ • (bA i : Fin d → F2) = 0 := by
    have h1 : ∑ j : Fin d, g j • N.mulVec (cols j) =
        ∑ j ∈ Finset.univ.filter (fun j : Fin d => r ≤ j.val ∧ j.val < 2 * r),
          g j • N.mulVec (cols j) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun j : Fin d => r ≤ j.val ∧ j.val < 2 * r)]
      have hzero : ∑ j ∈ Finset.univ.filter (fun j : Fin d => ¬(r ≤ j.val ∧ j.val < 2 * r)),
          g j • N.mulVec (cols j) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [hN_col j, dif_neg (Finset.mem_filter.mp hj).2, smul_zero]
      rw [hzero, add_zero]
    rw [h1] at hN_sum
    rw [← hN_sum]
    refine Finset.sum_bij (fun (i : Fin r) _ => (⟨r + i.val, by have := i.isLt; omega⟩ : Fin d)) ?_ ?_ ?_ ?_
    · intro i _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_add_right r i.val, by dsimp; have := i.isLt; omega⟩
    · intro i1 _ i2 _ heq
      exact Fin.ext (by have := congrArg Fin.val heq; dsimp at this; omega)
    · intro j hj
      have hjp := (Finset.mem_filter.mp hj).2
      exact ⟨⟨j.val - r, by omega⟩, Finset.mem_univ _, Fin.ext (by dsimp; omega)⟩
    · intro i _
      have hcond : r ≤ r + i.val ∧ r + i.val < 2 * r := ⟨Nat.le_add_right _ _, by have := i.isLt; omega⟩
      rw [hN_col ⟨r + i.val, by have := i.isLt; omega⟩, dif_pos hcond]
      congr 1
      exact congrArg (fun k : Fin r => (bA k : Fin d → F2)) (Fin.ext (by dsimp; omega))
  have hgB : ∀ i : Fin r, g ⟨r + i.val, by have := i.isLt; omega⟩ = 0 := by
    have hsub_zero : ∑ i : Fin r, g ⟨r + i.val, by have := i.isLt; omega⟩ • bA i = 0 := by
      apply Subtype.ext
      simpa [Submodule.coe_sum, Submodule.coe_smul] using hB_sum
    exact Fintype.linearIndependent_iff.mp bA.linearIndependent _ hsub_zero
  let sumA : Fin d → F2 := ∑ i : Fin r, g ⟨i.val, by have := i.isLt; omega⟩ • (bA i : Fin d → F2)
  let sumC : Fin d → F2 :=
    ∑ c : Fin (d - 2 * r), g ⟨2 * r + c.val, by have := c.isLt; omega⟩ • (bC c : Fin d → F2)
  have hAC : sumA + sumC = 0 := by
    have hdecomp : ∑ j : Fin d, g j • cols j = sumA + sumC := by
      have hpart : (Finset.univ : Finset (Fin d)) =
          (Finset.univ.filter fun j : Fin d => j.val < r) ∪
          ((Finset.univ.filter fun j : Fin d => r ≤ j.val ∧ j.val < 2 * r) ∪
           (Finset.univ.filter fun j : Fin d => 2 * r ≤ j.val)) := by
        ext j; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
        omega
      have hd1 : Disjoint
          (Finset.univ.filter fun j : Fin d => j.val < r)
          ((Finset.univ.filter fun j : Fin d => r ≤ j.val ∧ j.val < 2 * r) ∪
           (Finset.univ.filter fun j : Fin d => 2 * r ≤ j.val)) := by
        rw [Finset.disjoint_left]; intro j h1 h2
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and] at h1 h2
        omega
      have hd2 : Disjoint
          (Finset.univ.filter fun j : Fin d => r ≤ j.val ∧ j.val < 2 * r)
          (Finset.univ.filter fun j : Fin d => 2 * r ≤ j.val) := by
        rw [Finset.disjoint_left]; intro j h1 h2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        omega
      rw [hpart, Finset.sum_union hd1, Finset.sum_union hd2]
      have hB0 : ∑ j ∈ Finset.univ.filter (fun j : Fin d => r ≤ j.val ∧ j.val < 2 * r),
          g j • cols j = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hjp := (Finset.mem_filter.mp hj).2
        have hj_eq : j = ⟨r + (j.val - r), by omega⟩ := Fin.ext (by dsimp; omega)
        rw [hj_eq, hgB ⟨j.val - r, by omega⟩, zero_smul]
      rw [hB0, zero_add]
      congr 1
      · refine Finset.sum_bij (fun (j : Fin d) hj =>
            (⟨j.val, (Finset.mem_filter.mp hj).2⟩ : Fin r)) ?_ ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro j1 _ j2 _ heq; exact Fin.ext (congrArg (fun x : Fin r => x.val) heq)
        · intro i _; exact ⟨⟨i.val, by have := i.isLt; omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩, rfl⟩
        · intro j hj
          have hlt := (Finset.mem_filter.mp hj).2
          dsimp only [cols]
          rw [dif_pos hlt]
      · refine Finset.sum_bij (fun (j : Fin d) hj =>
            (⟨j.val - 2 * r, by have := (Finset.mem_filter.mp hj).2; omega⟩ : Fin (d - 2 * r)))
            ?_ ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro j1 hj1 j2 hj2 heq
          have h1 := (Finset.mem_filter.mp hj1).2
          have h2 := (Finset.mem_filter.mp hj2).2
          have hv := congrArg (fun x : Fin (d - 2 * r) => x.val) heq
          dsimp at hv
          exact Fin.ext (by omega)
        · intro c _
          exact ⟨⟨2 * r + c.val, by have := c.isLt; omega⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_add_right _ _⟩, Fin.ext (Nat.add_sub_cancel_left _ _)⟩
        · intro j hj
          have hge := (Finset.mem_filter.mp hj).2
          have h1 : ¬(j.val < r) := by omega
          have h2 : ¬(j.val < 2 * r) := by omega
          have hj_eq : (⟨2 * r + (j.val - 2 * r), by omega⟩ : Fin d) = j :=
            Fin.ext (by dsimp; omega)
          dsimp only [cols]
          rw [dif_neg h1, dif_neg h2, hj_eq]
    rw [← hdecomp, hg]
  have hsumA_mem : sumA ∈ LinearMap.range N.mulVecLin :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (bA i).2
  have hsumC_mem : sumC ∈ Csub :=
    Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (bC c).2
  have hsumA_eq_C : sumA = sumC := by
    funext x
    have hx := congrFun hAC x
    simp only [Pi.add_apply, Pi.zero_apply] at hx
    exact zmod2_eq_of_add_eq_zero hx
  have hsumA_zero : sumA = 0 :=
    Submodule.disjoint_def.mp hCsub_disj sumA hsumA_mem (hsumA_eq_C ▸ hsumC_mem)
  have hsumC_zero : sumC = 0 := by rw [← hsumA_eq_C, hsumA_zero]
  have hgA : ∀ i : Fin r, g ⟨i.val, by have := i.isLt; omega⟩ = 0 := by
    have hsub_zero : ∑ i : Fin r, g ⟨i.val, by have := i.isLt; omega⟩ • bA i = 0 := by
      apply Subtype.ext
      simpa [Submodule.coe_sum, Submodule.coe_smul] using hsumA_zero
    exact Fintype.linearIndependent_iff.mp bA.linearIndependent _ hsub_zero
  have hgC : ∀ c : Fin (d - 2 * r), g ⟨2 * r + c.val, by have := c.isLt; omega⟩ = 0 := by
    have hsub_zero : ∑ c : Fin (d - 2 * r), g ⟨2 * r + c.val, by have := c.isLt; omega⟩ • bC c = 0 := by
      apply Subtype.ext
      simpa [Submodule.coe_sum, Submodule.coe_smul] using hsumC_zero
    exact Fintype.linearIndependent_iff.mp bC.linearIndependent _ hsub_zero
  intro j
  by_cases h1 : j.val < r
  · exact hgA ⟨j.val, h1⟩
  · by_cases h2 : j.val < 2 * r
    · have hj_eq : j = ⟨r + (j.val - r), by omega⟩ := Fin.ext (by dsimp; omega)
      rw [hj_eq]; exact hgB ⟨j.val - r, by omega⟩
    · have hj_eq : j = ⟨2 * r + (j.val - 2 * r), by omega⟩ := Fin.ext (by dsimp; omega)
      rw [hj_eq]; exact hgC ⟨j.val - 2 * r, by omega⟩

lemma exists_adapted_coords {d : ℕ} (U : Matrix (Fin d) (Fin d) F2) (hU : U * U = 1) :
    let r := (U - 1).rank
    2 * r ≤ d ∧
    ∃ P Q : Matrix (Fin d) (Fin d) F2,
      P * Q = 1 ∧ Q * P = 1 ∧ Q * U * P = U0 d r := by
  classical
  set N := U - 1
  set r := N.rank
  obtain ⟨hN2, hsub_ker, h2r⟩ := involution_rank_le U hU
  have hr_eq : r = Module.finrank F2 (LinearMap.range N.mulVecLin) := rfl
  have hrn : Module.finrank F2 (LinearMap.range N.mulVecLin) +
      Module.finrank F2 (LinearMap.ker N.mulVecLin) = d := by
    simpa [Module.finrank_fin_fun] using LinearMap.finrank_range_add_finrank_ker N.mulVecLin
  let bA : Module.Basis (Fin r) F2 (LinearMap.range N.mulVecLin) :=
    Module.finBasisOfFinrankEq F2 (LinearMap.range N.mulVecLin) hr_eq.symm
  have hbB_ex : ∀ i : Fin r, ∃ v : Fin d → F2, N.mulVec v = (bA i : Fin d → F2) :=
    fun i => (bA i).2
  let bB : Fin r → (Fin d → F2) := fun i => (hbB_ex i).choose
  have hbB_spec : ∀ i : Fin r, N.mulVec (bB i) = (bA i : Fin d → F2) :=
    fun i => (hbB_ex i).choose_spec
  let Rker : Submodule F2 (LinearMap.ker N.mulVecLin) :=
    (LinearMap.range N.mulVecLin).comap (LinearMap.ker N.mulVecLin).subtype
  obtain ⟨Cker, hCker⟩ := Submodule.exists_isCompl Rker
  let Csub : Submodule F2 (Fin d → F2) := Cker.map (LinearMap.ker N.mulVecLin).subtype
  have hCsub_le : Csub ≤ LinearMap.ker N.mulVecLin := by
    intro x hx; rcases hx with ⟨y, _, rfl⟩; exact y.2
  have hCsub_disj : Disjoint (LinearMap.range N.mulVecLin) Csub := by
    rw [Submodule.disjoint_def]
    intro x hxR hxC
    rcases hxC with ⟨y, hyC, rfl⟩
    have hy0 : y ∈ Rker ⊓ Cker := ⟨hxR, hyC⟩
    rw [hCker.inf_eq_bot] at hy0
    rw [Submodule.mem_bot] at hy0
    simp [hy0]
  have hCsub_finrank : Module.finrank F2 Csub = d - 2 * r := by
    have hRker_fr : Module.finrank F2 Rker = r := by
      have hmap : Rker.map (LinearMap.ker N.mulVecLin).subtype = LinearMap.range N.mulVecLin := by
        ext x
        simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype, Rker]
        constructor
        · rintro ⟨y, hy, rfl⟩; exact hy
        · intro hx; exact ⟨⟨x, hsub_ker hx⟩, hx, rfl⟩
      rw [hr_eq, ← hmap, Submodule.finrank_map_subtype_eq]
    have hCker_fr : Module.finrank F2 Cker = Module.finrank F2 Csub :=
      (Submodule.finrank_map_subtype_eq (LinearMap.ker N.mulVecLin) Cker).symm
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq Rker Cker
    rw [hCker.sup_eq_top, hCker.inf_eq_bot, finrank_top, finrank_bot, add_zero] at hsum
    omega
  let bC : Module.Basis (Fin (d - 2 * r)) F2 Csub :=
    Module.finBasisOfFinrankEq F2 Csub hCsub_finrank
  let cols : Fin d → (Fin d → F2) := fun j =>
    if h1 : j.val < r then (bA ⟨j.val, h1⟩ : Fin d → F2)
    else if h2 : j.val < 2 * r then bB ⟨j.val - r, by omega⟩
    else (bC ⟨j.val - 2 * r, by omega⟩ : Fin d → F2)
  have hcols_li : LinearIndependent F2 cols :=
    adapted_cols_li N h2r hsub_ker bA bB hbB_spec Csub hCsub_le hCsub_disj bC
  let P : Matrix (Fin d) (Fin d) F2 := fun i j => cols j i
  have hP_mulVec : ∀ x : Fin d → F2, P.mulVec x = ∑ j : Fin d, x j • cols j := by
    intro x; funext i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hP_inj : Function.Injective P.mulVecLin := by
    intro x y hxy
    have hsub : P.mulVec (x - y) = 0 := by
      change P.mulVecLin (x - y) = 0
      rw [map_sub, hxy, sub_self]
    rw [hP_mulVec] at hsub
    have hz := Fintype.linearIndependent_iff.mp hcols_li (x - y) hsub
    funext j
    exact sub_eq_zero.mp (hz j)
  let e : (Fin d → F2) ≃ₗ[F2] (Fin d → F2) :=
    LinearEquiv.ofBijective P.mulVecLin ⟨hP_inj, Finite.injective_iff_surjective.mp hP_inj⟩
  let Q : Matrix (Fin d) (Fin d) F2 := fun i j => e.symm (Pi.single j 1) i
  have hQ_mulVec : ∀ y : Fin d → F2, Q.mulVec y = e.symm y := by
    intro y
    have hy : y = ∑ j : Fin d, y j • Pi.single j (1 : F2) := by
      funext i; simp [Pi.single_apply]
    conv_rhs => rw [hy, map_sum]
    funext i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_smul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hPQ : P * Q = 1 := by
    ext i j
    have hcol : (P * Q).mulVec (Pi.single j 1) = Pi.single j 1 := by
      rw [← Matrix.mulVec_mulVec, hQ_mulVec]
      exact e.apply_symm_apply (Pi.single j 1)
    have hi := congrFun hcol i
    simp only [Matrix.mulVec_single, mul_one, Pi.single_apply] at hi
    rw [Matrix.one_apply]
    by_cases hij : i = j <;> simp [hij] at hi ⊢ <;> exact hi
  have hQP : Q * P = 1 := by
    ext i j
    have hcol : (Q * P).mulVec (Pi.single j 1) = Pi.single j 1 := by
      rw [← Matrix.mulVec_mulVec, hQ_mulVec]
      exact e.symm_apply_apply (Pi.single j 1)
    have hi := congrFun hcol i
    simp only [Matrix.mulVec_single, mul_one, Pi.single_apply] at hi
    rw [Matrix.one_apply]
    by_cases hij : i = j <;> simp [hij] at hi ⊢ <;> exact hi
  have hNP : N * P = P * J0 d r := by
    ext i j
    have hcol : (N * P).mulVec (Pi.single j 1) = (P * J0 d r).mulVec (Pi.single j 1) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      have hPsingle : P.mulVec (Pi.single j 1) = cols j := by
        rw [hP_mulVec]
        simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      rw [hPsingle]
      have hJsingle : (J0 d r).mulVec (Pi.single j 1) =
          if h : r ≤ j.val ∧ j.val < 2 * r then Pi.single ⟨j.val - r, by omega⟩ 1 else 0 := by
        funext k
        have hmul_j : (J0 d r).mulVec (Pi.single j 1) k = J0 d r k j := by
          simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
            Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        rw [hmul_j]
        by_cases h2 : r ≤ j.val ∧ j.val < 2 * r
        · rw [dif_pos h2]
          simp only [J0, Pi.single_apply]
          by_cases h1 : k.val < r ∧ j.val = r + k.val
          · have hk : k = ⟨j.val - r, by omega⟩ := Fin.ext (by dsimp; omega)
            rw [if_pos h1, if_pos hk]
          · have hne : k ≠ ⟨j.val - r, by omega⟩ := by
              intro hk; apply h1; rw [hk]; dsimp; omega
            rw [if_neg h1, if_neg hne]
        · rw [dif_neg h2]
          simp only [J0, Pi.zero_apply]
          have h1 : ¬(k.val < r ∧ j.val = r + k.val) := by omega
          rw [if_neg h1]
      rw [hJsingle]
      split_ifs with h
      · rw [hP_mulVec]; simp only [Pi.single_apply, ite_smul, one_smul, zero_smul,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        have h1 : ¬(j.val < r) := by omega
        have h2 : j.val < 2 * r := h.2
        have h3 : (⟨j.val - r, by omega⟩ : Fin d).val < r := by dsimp; omega
        dsimp only [cols]
        rw [dif_neg h1, dif_pos h2, dif_pos h3]
        exact hbB_spec ⟨j.val - r, by omega⟩
      · rw [Matrix.mulVec_zero]
        dsimp only [cols]
        split_ifs with h1 h2
        · exact hsub_ker (bA ⟨j.val, h1⟩).2
        · exfalso; omega
        · exact hCsub_le (bC ⟨j.val - 2 * r, by omega⟩).2
    have hi := congrFun hcol i
    simpa [Matrix.mulVec_single] using hi
  have hQUP : Q * U * P = U0 d r := by
    have hUeq : U = 1 + N := by
      ext i j; simp only [N, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply]
      ring
    rw [hUeq, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hQP, Matrix.mul_assoc, hNP,
        ← Matrix.mul_assoc, hQP, Matrix.one_mul]
    rfl
  exact ⟨h2r, P, Q, hPQ, hQP, hQUP⟩

-- ============================================================================
-- Part 5: Alternating Matrices, W0 Space, and Dimension D
-- ============================================================================

lemma sum_symm_zero_diag {n : ℕ} (f : Fin n → Fin n → F2)
    (hsym : ∀ i j, f i j = f j i) (hdiag : ∀ i, f i i = 0) :
    ∑ i : Fin n, ∑ j : Fin n, f i j = 0 := by
  rw [← Fintype.sum_prod_type']
  let ltSet := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)
  let eqSet := Finset.univ.filter (fun p : Fin n × Fin n => p.1 = p.2)
  let gtSet := Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1)
  have hpart : (Finset.univ : Finset (Fin n × Fin n)) = ltSet ∪ (eqSet ∪ gtSet) := by
    ext ⟨i, j⟩
    simp only [ltSet, eqSet, gtSet, Finset.mem_univ, Finset.mem_union, Finset.mem_filter,
      true_and, true_iff]
    exact lt_trichotomy i j
  have hd1 : Disjoint ltSet (eqSet ∪ gtSet) := by
    rw [Finset.disjoint_left]; intro ⟨i, j⟩ h1 h2
    simp only [ltSet, eqSet, gtSet, Finset.mem_filter, Finset.mem_union, Finset.mem_univ,
      true_and] at h1 h2
    rcases h2 with rfl | h2
    · exact lt_irrefl i h1
    · exact lt_asymm h1 h2
  have hd2 : Disjoint eqSet gtSet := by
    rw [Finset.disjoint_left]; intro ⟨i, j⟩ h1 h2
    simp only [eqSet, gtSet, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    rw [h1] at h2; exact lt_irrefl j h2
  rw [hpart, Finset.sum_union hd1, Finset.sum_union hd2]
  have heq0 : ∑ p ∈ eqSet, f p.1 p.2 = 0 := by
    apply Finset.sum_eq_zero
    intro ⟨i, j⟩ hp
    have hij := (Finset.mem_filter.mp hp).2
    dsimp only at hij
    subst hij; exact hdiag i
  have hgt_eq : ∑ p ∈ gtSet, f p.1 p.2 = ∑ p ∈ ltSet, f p.1 p.2 := by
    refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro ⟨i, j⟩ hp; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩
    · intro ⟨i1, j1⟩ _ ⟨i2, j2⟩ _ heq
      simp only [Prod.mk.injEq] at heq; exact Prod.ext heq.2 heq.1
    · intro ⟨i, j⟩ hp
      exact ⟨(j, i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩, rfl⟩
    · intro ⟨i, j⟩ _; exact hsym i j
  rw [heq0, zero_add, hgt_eq, zmod2_add_self]

lemma isAlt_cong {d : ℕ} (P H : Matrix (Fin d) (Fin d) F2) (hH : IsAlt H) :
    IsAlt (P * H * P.transpose) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hH.1,
        Matrix.mul_assoc]
  · intro i
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine sum_symm_zero_diag (fun k l => P i k * H k l * P i l) ?_ ?_
    · intro k l
      have hsym : H l k = H k l := congrFun (congrFun hH.1 k) l
      rw [hsym]; ring
    · intro k; rw [hH.2 k, mul_zero, zero_mul]

lemma rk2Mat_cong {d : ℕ} (Q : Matrix (Fin d) (Fin d) F2) (a b c e : Fin d → F2) :
    Q * rk2Mat a b c e * Q.transpose =
      rk2Mat (Q.mulVec a) (Q.mulVec b) (Q.mulVec c) (Q.mulVec e) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, rk2Mat, Matrix.mulVec, dotProduct]
  simp_rw [mul_add, Finset.sum_add_distrib, add_mul, Finset.sum_add_distrib]
  congr 1
  · simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro l _
    ring
  · simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro l _
    ring

def IsW0 (d r : ℕ) (hr : 2 * r ≤ d) (M : Matrix (Fin d) (Fin d) F2) : Prop :=
  IsAlt M ∧
  (∀ i j : Fin d, r ≤ i.val → r ≤ j.val → M i j = 0) ∧
  (∀ i j : Fin r, M ⟨i.val, by omega⟩ ⟨r + j.val, by omega⟩ =
                  M ⟨j.val, by omega⟩ ⟨r + i.val, by omega⟩) ∧
  (∀ i : Fin r, M ⟨i.val, by omega⟩ ⟨r + i.val, by omega⟩ = 0)

def W0Sub (d r : ℕ) (hr : 2 * r ≤ d) : Submodule F2 (Matrix (Fin d) (Fin d) F2) :=
  { carrier := {M | IsW0 d r hr M}
    zero_mem' := ⟨⟨by simp, fun _ => rfl⟩, fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩, add_mem' := by
      intro M1 M2 h1 h2
      refine ⟨⟨by rw [Matrix.transpose_add, h1.1.1, h2.1.1],
               fun i => by simp [h1.1.2 i, h2.1.2 i]⟩,
              fun i j hi hj => by simp [h1.2.1 i j hi hj, h2.2.1 i j hi hj],
              fun i j => by simp [h1.2.2.1 i j, h2.2.2.1 i j],
              fun i => by simp [h1.2.2.2 i, h2.2.2.2 i]⟩
    smul_mem' := by
      intro c M h
      refine ⟨⟨by rw [Matrix.transpose_smul, h.1.1],
               fun i => by simp [h.1.2 i]⟩,
              fun i j hi hj => by simp [h.2.1 i j hi hj],
              fun i j => by simp [h.2.2.1 i j],
              fun i => by simp [h.2.2.2 i]⟩ }

lemma U0_conj_apply {d r : ℕ} (hr : 2 * r ≤ d) (H : Matrix (Fin d) (Fin d) F2) (i j : Fin d) :
    (U0 d r * H * (U0 d r).transpose + H) i j =
      (if hi : i.val < r then H ⟨r + i.val, by omega⟩ j else 0) +
      (if hj : j.val < r then H i ⟨r + j.val, by omega⟩ else 0) +
      (if hi : i.val < r then
        if hj : j.val < r then H ⟨r + i.val, by omega⟩ ⟨r + j.val, by omega⟩ else 0
       else 0) := by
  have hJH : ∀ (M : Matrix (Fin d) (Fin d) F2) (a b : Fin d), (J0 d r * M) a b =
      if ha : a.val < r then M ⟨r + a.val, by omega⟩ b else 0 := by
    intro M a b
    simp only [Matrix.mul_apply, J0]
    by_cases ha : a.val < r
    · simp only [ha, true_and, dite_true]
      rw [Finset.sum_eq_single ⟨r + a.val, by omega⟩]
      · simp
      · intro k _ hne
        have : k.val ≠ r + a.val := fun h => hne (Fin.ext h)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp only [ha, false_and, ↓reduceIte, zero_mul, Finset.sum_const_zero, dite_false]
  have hHJT : ∀ (M : Matrix (Fin d) (Fin d) F2) (a b : Fin d), (M * (J0 d r).transpose) a b =
      if hb : b.val < r then M a ⟨r + b.val, by omega⟩ else 0 := by
    intro M a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, J0]
    by_cases hb : b.val < r
    · simp only [hb, true_and, dite_true]
      rw [Finset.sum_eq_single ⟨r + b.val, by omega⟩]
      · simp
      · intro k _ hne
        have : k.val ≠ r + b.val := fun h => hne (Fin.ext h)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp only [hb, false_and, ↓reduceIte, mul_zero, Finset.sum_const_zero, dite_false]
  have hJHJT : ∀ a b : Fin d, (J0 d r * H * (J0 d r).transpose) a b =
      if ha : a.val < r then
        if hb : b.val < r then H ⟨r + a.val, by omega⟩ ⟨r + b.val, by omega⟩ else 0
      else 0 := by
    intro a b
    rw [hHJT (J0 d r * H) a b]
    by_cases hb : b.val < r
    · simp only [hb, dite_true, hJH H a ⟨r + b.val, by omega⟩]
    · by_cases ha : a.val < r <;> simp [ha, hb]
  have hexpand : U0 d r * H * (U0 d r).transpose + H =
      J0 d r * H + H * (J0 d r).transpose + J0 d r * H * (J0 d r).transpose := by
    unfold U0
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.transpose_add, Matrix.transpose_one,
        Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, Matrix.mul_one, Matrix.mul_one]
    ext a b
    simp only [Matrix.add_apply]
    have hcalc : (H a b + (J0 d r * H) a b) +
        ((H * (J0 d r).transpose) a b + (J0 d r * H * (J0 d r).transpose) a b) + H a b =
        (H a b + H a b) + ((J0 d r * H) a b + (H * (J0 d r).transpose) a b +
          (J0 d r * H * (J0 d r).transpose) a b) := by ring
    rw [hcalc, zmod2_add_self, zero_add]
  rw [hexpand, Matrix.add_apply, Matrix.add_apply, hJH, hHJT, hJHJT]

lemma mem_W0Sub_iff_exists_alt {d r : ℕ} (hr : 2 * r ≤ d) (M : Matrix (Fin d) (Fin d) F2) :
    M ∈ W0Sub d r hr ↔ ∃ H : Matrix (Fin d) (Fin d) F2, IsAlt H ∧
      U0 d r * H * (U0 d r).transpose + H = M := by
  constructor
  · intro hM
    let H : Matrix (Fin d) (Fin d) F2 := fun i j =>
      if h1 : i.val < r ∧ r ≤ j.val ∧ j.val < 2 * r then
        if i.val < j.val - r then M i ⟨j.val - r, by omega⟩ + M i j else 0
      else if h2 : r ≤ i.val ∧ i.val < 2 * r ∧ j.val < r then
        if j.val < i.val - r then M j ⟨i.val - r, by omega⟩ + M j i else 0
      else if h3 : r ≤ i.val ∧ i.val < 2 * r ∧ r ≤ j.val ∧ j.val < 2 * r then
        M ⟨i.val - r, by omega⟩ j
      else if h4 : r ≤ i.val ∧ i.val < 2 * r ∧ 2 * r ≤ j.val then
        M ⟨i.val - r, by omega⟩ j
      else if h5 : 2 * r ≤ i.val ∧ r ≤ j.val ∧ j.val < 2 * r then
        M ⟨j.val - r, by omega⟩ i
      else 0
    have hH_AB : ∀ (i j : Fin d), i.val < r → r ≤ j.val → j.val < 2 * r →
        H i j = if i.val < j.val - r then M i ⟨j.val - r, by omega⟩ + M i j else 0 := by
      intro i j hi hj1 hj2; dsimp only [H]; rw [dif_pos ⟨hi, hj1, hj2⟩]
    have hH_BA : ∀ (i j : Fin d), r ≤ i.val → i.val < 2 * r → j.val < r →
        H i j = if j.val < i.val - r then M j ⟨i.val - r, by omega⟩ + M j i else 0 := by
      intro i j hi1 hi2 hj; dsimp only [H]; rw [dif_neg (by omega), dif_pos ⟨hi1, hi2, hj⟩]
    have hH_BB : ∀ (i j : Fin d), r ≤ i.val → i.val < 2 * r → r ≤ j.val → j.val < 2 * r →
        H i j = M ⟨i.val - r, by omega⟩ j := by
      intro i j hi1 hi2 hj1 hj2; dsimp only [H]
      rw [dif_neg (by omega), dif_neg (by omega), dif_pos ⟨hi1, hi2, hj1, hj2⟩]
    have hH_BC : ∀ (i j : Fin d), r ≤ i.val → i.val < 2 * r → 2 * r ≤ j.val →
        H i j = M ⟨i.val - r, by omega⟩ j := by
      intro i j hi1 hi2 hj; dsimp only [H]
      rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos ⟨hi1, hi2, hj⟩]
    have hH_CB : ∀ (i j : Fin d), 2 * r ≤ i.val → r ≤ j.val → j.val < 2 * r →
        H i j = M ⟨j.val - r, by omega⟩ i := by
      intro i j hi hj1 hj2; dsimp only [H]
      rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega),
          dif_pos ⟨hi, hj1, hj2⟩]
    have hH_zero : ∀ (i j : Fin d),
        ¬(i.val < r ∧ r ≤ j.val ∧ j.val < 2 * r) →
        ¬(r ≤ i.val ∧ i.val < 2 * r ∧ j.val < r) →
        ¬(r ≤ i.val ∧ i.val < 2 * r ∧ r ≤ j.val ∧ j.val < 2 * r) →
        ¬(r ≤ i.val ∧ i.val < 2 * r ∧ 2 * r ≤ j.val) →
        ¬(2 * r ≤ i.val ∧ r ≤ j.val ∧ j.val < 2 * r) → H i j = 0 := by
      intro i j h1 h2 h3 h4 h5; dsimp only [H]
      rw [dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_neg h5]
    have hH_alt : IsAlt H := by
      refine ⟨?_, ?_⟩
      · ext i j
        simp only [Matrix.transpose_apply]
        by_cases hi1 : i.val < r
        · by_cases hj1 : j.val < r
          · rw [hH_zero j i (by omega) (by omega) (by omega) (by omega) (by omega),
                hH_zero i j (by omega) (by omega) (by omega) (by omega) (by omega)]
          · by_cases hj2 : j.val < 2 * r
            · rw [hH_BA j i (by omega) hj2 hi1, hH_AB i j hi1 (by omega) hj2]
            · rw [hH_zero j i (by omega) (by omega) (by omega) (by omega) (by omega),
                  hH_zero i j (by omega) (by omega) (by omega) (by omega) (by omega)]
        · by_cases hi2 : i.val < 2 * r
          · by_cases hj1 : j.val < r
            · rw [hH_AB j i hj1 (by omega) hi2, hH_BA i j (by omega) hi2 hj1]
            · by_cases hj2 : j.val < 2 * r
              · rw [hH_BB j i (by omega) hj2 (by omega) hi2,
                    hH_BB i j (by omega) hi2 (by omega) hj2]
                have hsymK := hM.2.2.1 ⟨j.val - r, by omega⟩ ⟨i.val - r, by omega⟩
                dsimp only at hsymK
                have hie : (⟨r + (i.val - r), by omega⟩ : Fin d) = i := Fin.ext (by dsimp; omega)
                have hje : (⟨r + (j.val - r), by omega⟩ : Fin d) = j := Fin.ext (by dsimp; omega)
                rw [hie, hje] at hsymK
                exact hsymK
              · rw [hH_CB j i (by omega) (by omega) hi2, hH_BC i j (by omega) hi2 (by omega)]
          · by_cases hj1 : j.val < r
            · rw [hH_zero j i (by omega) (by omega) (by omega) (by omega) (by omega),
                  hH_zero i j (by omega) (by omega) (by omega) (by omega) (by omega)]
            · by_cases hj2 : j.val < 2 * r
              · rw [hH_BC j i (by omega) hj2 (by omega), hH_CB i j (by omega) (by omega) hj2]
              · rw [hH_zero j i (by omega) (by omega) (by omega) (by omega) (by omega),
                    hH_zero i j (by omega) (by omega) (by omega) (by omega) (by omega)]
      · intro i
        by_cases hi1 : i.val < r
        · exact hH_zero i i (by omega) (by omega) (by omega) (by omega) (by omega)
        · by_cases hi2 : i.val < 2 * r
          · rw [hH_BB i i (by omega) hi2 (by omega) hi2]
            have hd0 := hM.2.2.2 ⟨i.val - r, by omega⟩
            dsimp only at hd0
            have hie : (⟨r + (i.val - r), by omega⟩ : Fin d) = i := Fin.ext (by dsimp; omega)
            rw [hie] at hd0
            exact hd0
          · exact hH_zero i i (by omega) (by omega) (by omega) (by omega) (by omega)
    refine ⟨H, hH_alt, ?_⟩
    ext i j
    rw [U0_conj_apply hr H i j]
    by_cases hi : i.val < r
    · by_cases hj : j.val < r
      · rw [dif_pos hi, dif_pos hj, dif_pos hi, dif_pos hj]
        have h1 : H ⟨r + i.val, by omega⟩ j =
            if j.val < i.val then M j i + M j ⟨r + i.val, by omega⟩ else 0 := by
          rw [hH_BA ⟨r + i.val, by omega⟩ j (by dsimp; omega) (by dsimp; omega) hj]
          simp only [Nat.add_sub_cancel_left]
        have h2 : H i ⟨r + j.val, by omega⟩ =
            if i.val < j.val then M i j + M i ⟨r + j.val, by omega⟩ else 0 := by
          rw [hH_AB i ⟨r + j.val, by omega⟩ hi (by dsimp; omega) (by dsimp; omega)]
          simp only [Nat.add_sub_cancel_left]
        have h3 : H ⟨r + i.val, by omega⟩ ⟨r + j.val, by omega⟩ =
            M i ⟨r + j.val, by omega⟩ := by
          rw [hH_BB ⟨r + i.val, by omega⟩ ⟨r + j.val, by omega⟩
              (by dsimp; omega) (by dsimp; omega) (by dsimp; omega) (by dsimp; omega)]
          have : (⟨r + i.val - r, by omega⟩ : Fin d) = i := Fin.ext (by dsimp; omega)
          rw [this]
        rw [h1, h2, h3]
        rcases lt_trichotomy i.val j.val with hlt | heq | hgt
        · have hnot : ¬(j.val < i.val) := by omega
          rw [if_neg hnot, if_pos hlt, zero_add, add_assoc, zmod2_add_self, add_zero]
        · have hij : i = j := Fin.ext heq
          subst hij
          rw [if_neg (lt_irrefl _), zero_add, zero_add]
          have hd0 := hM.2.2.2 ⟨i.val, hi⟩
          dsimp only at hd0
          rw [hd0, hM.1.2 i]
        · have hnot : ¬(i.val < j.val) := by omega
          rw [if_pos hgt, if_neg hnot, add_zero]
          have hMsym : M j i = M i j := congrFun (congrFun hM.1.1 i) j
          have hKsym : M j ⟨r + i.val, by omega⟩ = M i ⟨r + j.val, by omega⟩ :=
            hM.2.2.1 ⟨j.val, hj⟩ ⟨i.val, hi⟩
          rw [hMsym, hKsym, add_assoc, zmod2_add_self, add_zero]
      · rw [dif_pos hi, dif_neg hj, dif_pos hi, dif_neg hj, add_zero, add_zero]
        by_cases hj2 : j.val < 2 * r
        · rw [hH_BB ⟨r + i.val, by omega⟩ j (by dsimp; omega) (by dsimp; omega) (by omega) hj2]
          have : (⟨r + i.val - r, by omega⟩ : Fin d) = i := Fin.ext (by dsimp; omega)
          rw [this]
        · rw [hH_BC ⟨r + i.val, by omega⟩ j (by dsimp; omega) (by dsimp; omega) (by omega)]
          have : (⟨r + i.val - r, by omega⟩ : Fin d) = i := Fin.ext (by dsimp; omega)
          rw [this]
    · by_cases hj : j.val < r
      · rw [dif_neg hi, dif_pos hj, dif_neg hi, zero_add, add_zero]
        have hMsym : M j i = M i j := congrFun (congrFun hM.1.1 i) j
        by_cases hi2 : i.val < 2 * r
        · rw [hH_BB i ⟨r + j.val, by omega⟩ (by omega) hi2 (by dsimp; omega) (by dsimp; omega)]
          have hK := hM.2.2.1 ⟨i.val - r, by omega⟩ ⟨j.val, hj⟩
          dsimp only at hK
          have hie : (⟨r + (i.val - r), by omega⟩ : Fin d) = i := Fin.ext (by dsimp; omega)
          rw [hie] at hK
          rw [hK, hMsym]
        · rw [hH_CB i ⟨r + j.val, by omega⟩ (by omega) (by dsimp; omega) (by dsimp; omega)]
          have : (⟨r + j.val - r, by omega⟩ : Fin d) = j := Fin.ext (by dsimp; omega)
          rw [this, hMsym]
      · rw [dif_neg hi, dif_neg hj, dif_neg hi, zero_add, add_zero]
        exact (hM.2.1 i j (by omega) (by omega)).symm
  · rintro ⟨H, hH, rfl⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h1 := isAlt_cong (U0 d r) H hH
      refine ⟨by rw [Matrix.transpose_add, h1.1, hH.1],
              fun i => by simp [h1.2 i, hH.2 i]⟩
    · intro i j hi hj
      rw [U0_conj_apply hr H i j]
      simp [show ¬(i.val < r) by omega, show ¬(j.val < r) by omega]
    · intro i j
      rw [U0_conj_apply hr H, U0_conj_apply hr H]
      simp only [i.isLt, j.isLt, dite_true,
        show ¬(r + j.val < r) by omega, show ¬(r + i.val < r) by omega, dite_false, add_zero]
      have := congrFun (congrFun hH.1 ⟨r + j.val, by omega⟩) ⟨r + i.val, by omega⟩
      exact this
    · intro i
      rw [U0_conj_apply hr H]
      simp only [i.isLt, dite_true, show ¬(r + i.val < r) by omega, dite_false, add_zero]
      exact hH.2 ⟨r + i.val, by omega⟩

abbrev PairIdx (r : ℕ) := {p : Fin r × Fin r // p.1 < p.2}
abbrev W0Idx (d r : ℕ) := PairIdx r ⊕ PairIdx r ⊕ (Fin r × Fin (d - 2 * r))

lemma card_pairIdx (r : ℕ) : Fintype.card (PairIdx r) = Nat.choose r 2 := by
  induction r with
  | zero => simp [PairIdx]
  | succ r ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right, ← ih]
    let S1 := Finset.univ.filter (fun p : PairIdx (r + 1) => p.1.2.val < r)
    let S2 := Finset.univ.filter (fun p : PairIdx (r + 1) => p.1.2.val = r)
    have hpart : (Finset.univ : Finset (PairIdx (r + 1))) = S1 ∪ S2 := by
      ext p; simp only [S1, S2, Finset.mem_univ, Finset.mem_union, Finset.mem_filter,
        true_and, true_iff]
      have := p.1.2.isLt; omega
    have hdisj : Disjoint S1 S2 := by
      rw [Finset.disjoint_left]; intro p h1 h2
      have := (Finset.mem_filter.mp h1).2
      have := (Finset.mem_filter.mp h2).2
      omega
    rw [← Finset.card_univ, hpart, Finset.card_union_of_disjoint hdisj]
    have hS1 : S1.card = Fintype.card (PairIdx r) := by
      rw [← Finset.card_univ]
      refine Finset.card_bij (fun p hp =>
        (⟨(⟨p.1.1.val, by have := (Finset.mem_filter.mp hp).2; have := p.2; omega⟩,
           ⟨p.1.2.val, (Finset.mem_filter.mp hp).2⟩), p.2⟩ : PairIdx r)) ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro p1 _ p2 _ heq
        apply Subtype.ext; apply Prod.ext
        · exact Fin.ext (congrArg (fun q : PairIdx r => q.1.1.val) heq)
        · exact Fin.ext (congrArg (fun q : PairIdx r => q.1.2.val) heq)
      · intro q _
        exact ⟨⟨(q.1.1.castSucc, q.1.2.castSucc), q.2⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, q.1.2.isLt⟩, rfl⟩
    have hS2 : S2.card = r := by
      conv_rhs => rw [show r = (Finset.univ : Finset (Fin r)).card by simp]
      refine Finset.card_bij (fun p hp =>
        (⟨p.1.1.val, by have := (Finset.mem_filter.mp hp).2; have := p.2; omega⟩ : Fin r)) ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro p1 hp1 p2 hp2 heq
        apply Subtype.ext; apply Prod.ext
        · exact Fin.ext (congrArg (fun x : Fin r => x.val) heq)
        · exact Fin.ext (by
            have h1 := (Finset.mem_filter.mp hp1).2
            have h2 := (Finset.mem_filter.mp hp2).2
            omega)
      · intro i _
        exact ⟨⟨(i.castSucc, Fin.last r), i.isLt⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩
    rw [hS1, hS2, Nat.add_comm]

lemma two_mul_choose_two (r : ℕ) : Nat.choose r 2 + Nat.choose r 2 = r * (r - 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    cases r with
    | zero => simp
    | succ k =>
      simp only [Nat.add_sub_cancel] at ih ⊢
      change (k + 1) + Nat.choose (k + 1) 2 + ((k + 1) + Nat.choose (k + 1) 2) = (k + 1 + 1) * (k + 1)
      have h1 : (k + 1 + 1) * (k + 1) = (k + 1) * k + (k + 1) + (k + 1) := by ring
      omega

lemma dim_formula {d r : ℕ} (hr : 2 * r ≤ d) :
    Nat.choose r 2 + Nat.choose r 2 + r * (d - 2 * r) = r * (d - r - 1) := by
  rw [two_mul_choose_two]
  cases r with
  | zero => simp
  | succ r =>
    rw [← Nat.mul_add]
    congr 1
    omega

def W0Recon {d r : ℕ} (hr : 2 * r ≤ d) (f : W0Idx d r → F2) : Matrix (Fin d) (Fin d) F2 :=
  fun i j =>
    if h1 : i.val < r ∧ j.val < r then
      if hlt : i.val < j.val then f (Sum.inl ⟨(⟨i.val, h1.1⟩, ⟨j.val, h1.2⟩), hlt⟩)
      else if hgt : j.val < i.val then f (Sum.inl ⟨(⟨j.val, h1.2⟩, ⟨i.val, h1.1⟩), hgt⟩)
      else 0
    else if h2 : i.val < r ∧ r ≤ j.val ∧ j.val < 2 * r then
      if hlt : i.val < j.val - r then
        f (Sum.inr (Sum.inl ⟨(⟨i.val, h2.1⟩, ⟨j.val - r, by omega⟩), hlt⟩))
      else if hgt : j.val - r < i.val then
        f (Sum.inr (Sum.inl ⟨(⟨j.val - r, by omega⟩, ⟨i.val, h2.1⟩), hgt⟩))
      else 0
    else if h3 : r ≤ i.val ∧ i.val < 2 * r ∧ j.val < r then
      if hlt : i.val - r < j.val then
        f (Sum.inr (Sum.inl ⟨(⟨i.val - r, by omega⟩, ⟨j.val, h3.2.2⟩), hlt⟩))
      else if hgt : j.val < i.val - r then
        f (Sum.inr (Sum.inl ⟨(⟨j.val, h3.2.2⟩, ⟨i.val - r, by omega⟩), hgt⟩))
      else 0
    else if h4 : i.val < r ∧ 2 * r ≤ j.val then
      f (Sum.inr (Sum.inr (⟨i.val, h4.1⟩, ⟨j.val - 2 * r, by omega⟩)))
    else if h5 : 2 * r ≤ i.val ∧ j.val < r then
      f (Sum.inr (Sum.inr (⟨j.val, h5.2⟩, ⟨i.val - 2 * r, by omega⟩)))
    else 0

lemma W0Recon_AA {d r : ℕ} (hr : 2 * r ≤ d) (f : W0Idx d r → F2) {i j : Fin d}
    (hi : i.val < r) (hj : j.val < r) :
    W0Recon hr f i j =
      if hlt : i.val < j.val then f (Sum.inl ⟨(⟨i.val, hi⟩, ⟨j.val, hj⟩), hlt⟩)
      else if hgt : j.val < i.val then f (Sum.inl ⟨(⟨j.val, hj⟩, ⟨i.val, hi⟩), hgt⟩)
      else 0 := dif_pos ⟨hi, hj⟩

lemma W0Recon_AB {d r : ℕ} (hr : 2 * r ≤ d) (f : W0Idx d r → F2) {i j : Fin d}
    (hi : i.val < r) (hj1 : r ≤ j.val) (hj2 : j.val < 2 * r) :
    W0Recon hr f i j =
      if hlt : i.val < j.val - r then
        f (Sum.inr (Sum.inl ⟨(⟨i.val, hi⟩, ⟨j.val - r, by omega⟩), hlt⟩))
      else if hgt : j.val - r < i.val then
        f (Sum.inr (Sum.inl ⟨(⟨j.val - r, by omega⟩, ⟨i.val, hi⟩), hgt⟩))
      else 0 := by
  unfold W0Recon; rw [dif_neg (by omega), dif_pos ⟨hi, hj1, hj2⟩]

lemma W0Recon_BA {d r : ℕ} (hr : 2 * r ≤ d) (f : W0Idx d r → F2) {i j : Fin d}
    (hi1 : r ≤ i.val) (hi2 : i.val < 2 * r) (hj : j.val < r) :
    W0Recon hr f i j =
      if hlt : i.val - r < j.val then
        f (Sum.inr (Sum.inl ⟨(⟨i.val - r, by omega⟩, ⟨j.val, hj⟩), hlt⟩))
      else if hgt : j.val < i.val - r then
        f (Sum.inr (Sum.inl ⟨(⟨j.val, hj⟩, ⟨i.val - r, by omega⟩), hgt⟩))
      else 0 := by
  unfold W0Recon; rw [dif_neg (by omega), dif_neg (by omega), dif_pos ⟨hi1, hi2, hj⟩]

lemma W0Recon_AC {d r : ℕ} (hr : 2 * r ≤ d) (f : W0Idx d r → F2) {i j : Fin d}
    (hi : i.val < r) (hj : 2 * r ≤ j.val) :
    W0Recon hr f i j = f (Sum.inr (Sum.inr (⟨i.val, hi⟩, ⟨j.val - 2 * r, by omega⟩))) := by
  unfold W0Recon; rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos ⟨hi, hj⟩]

lemma W0Recon_CA {d r : ℕ} (hr : 2 * r ≤ d) (f : W0Idx d r → F2) {i j : Fin d}
    (hi : 2 * r ≤ i.val) (hj : j.val < r) :
    W0Recon hr f i j = f (Sum.inr (Sum.inr (⟨j.val, hj⟩, ⟨i.val - 2 * r, by omega⟩))) := by
  unfold W0Recon
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos ⟨hi, hj⟩]

lemma W0Recon_zero {d r : ℕ} (hr : 2 * r ≤ d) (f : W0Idx d r → F2) {i j : Fin d}
    (hi : r ≤ i.val) (hj : r ≤ j.val) :
    W0Recon hr f i j = 0 := by
  unfold W0Recon
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]

lemma W0Recon_mem {d r : ℕ} (hr : 2 * r ≤ d) (f : W0Idx d r → F2) :
    W0Recon hr f ∈ W0Sub d r hr := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · ext i j
    simp only [Matrix.transpose_apply]
    by_cases hi1 : i.val < r
    · by_cases hj1 : j.val < r
      · rw [W0Recon_AA hr f hj1 hi1, W0Recon_AA hr f hi1 hj1]
        rcases lt_trichotomy i.val j.val with hlt | heq | hgt
        · rw [dif_neg (by omega), dif_pos hlt, dif_pos hlt]
        · rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]
        · rw [dif_pos hgt, dif_neg (by omega), dif_pos hgt]
      · by_cases hj2 : j.val < 2 * r
        · rw [W0Recon_BA hr f (by omega) hj2 hi1, W0Recon_AB hr f hi1 (by omega) hj2]
          rcases lt_trichotomy i.val (j.val - r) with hlt | heq | hgt
          · rw [dif_neg (by omega), dif_pos hlt, dif_pos hlt]
          · rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]
          · rw [dif_pos hgt, dif_neg (by omega), dif_pos hgt]
        · rw [W0Recon_CA hr f (by omega) hi1, W0Recon_AC hr f hi1 (by omega)]
    · by_cases hj1 : j.val < r
      · by_cases hi2 : i.val < 2 * r
        · rw [W0Recon_AB hr f hj1 (by omega) hi2, W0Recon_BA hr f (by omega) hi2 hj1]
          rcases lt_trichotomy j.val (i.val - r) with hlt | heq | hgt
          · rw [dif_pos hlt, dif_neg (by omega), dif_pos hlt]
          · rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]
          · rw [dif_neg (by omega), dif_pos hgt, dif_pos hgt]
        · rw [W0Recon_AC hr f hj1 (by omega), W0Recon_CA hr f (by omega) hj1]
      · rw [W0Recon_zero hr f (by omega) (by omega), W0Recon_zero hr f (by omega) (by omega)]
  · intro i
    by_cases hi : i.val < r
    · rw [W0Recon_AA hr f hi hi, dif_neg (lt_irrefl _), dif_neg (lt_irrefl _)]
    · exact W0Recon_zero hr f (by omega) (by omega)
  · intro i j hi hj
    exact W0Recon_zero hr f hi hj
  · intro i j
    rw [W0Recon_AB hr f i.isLt (by dsimp; omega) (by dsimp; have := j.isLt; omega),
        W0Recon_AB hr f j.isLt (by dsimp; omega) (by dsimp; have := i.isLt; omega)]
    simp only [Nat.add_sub_cancel_left]
    rcases lt_trichotomy i.val j.val with hlt | heq | hgt
    · rw [dif_pos hlt, dif_neg (by omega), dif_pos hlt]
    · rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]
    · rw [dif_neg (by omega), dif_pos hgt, dif_pos hgt]
  · intro i
    rw [W0Recon_AB hr f i.isLt (by dsimp; omega) (by dsimp; have := i.isLt; omega)]
    simp only [Nat.add_sub_cancel_left, lt_irrefl, ↓reduceDIte]

def W0Equiv {d r : ℕ} (hr : 2 * r ≤ d) : W0Sub d r hr ≃ₗ[F2] (W0Idx d r → F2) where
  toFun M := fun idx =>
    match idx with
    | Sum.inl p => M.1 ⟨p.1.1.val, by omega⟩ ⟨p.1.2.val, by omega⟩
    | Sum.inr (Sum.inl p) => M.1 ⟨p.1.1.val, by omega⟩ ⟨r + p.1.2.val, by omega⟩
    | Sum.inr (Sum.inr (i, c)) => M.1 ⟨i.val, by omega⟩ ⟨2 * r + c.val, by omega⟩
  map_add' M1 M2 := by
    funext idx; rcases idx with p | p | ⟨i, c⟩ <;> rfl
  map_smul' c M := by
    funext idx; rcases idx with p | p | ⟨i, k⟩ <;> rfl
  invFun f := ⟨W0Recon hr f, W0Recon_mem hr f⟩
  left_inv M := by
    apply Subtype.ext; ext i j
    dsimp only
    by_cases hi1 : i.val < r
    · by_cases hj1 : j.val < r
      · rw [W0Recon_AA hr _ hi1 hj1]
        rcases lt_trichotomy i.val j.val with hlt | heq | hgt
        · rw [dif_pos hlt]
        · rw [dif_neg (by omega), dif_neg (by omega)]
          have hij : i = j := Fin.ext heq; subst hij; exact (M.2.1.2 i).symm
        · rw [dif_neg (by omega), dif_pos hgt]
          exact congrFun (congrFun M.2.1.1 i) j
      · by_cases hj2 : j.val < 2 * r
        · rw [W0Recon_AB hr _ hi1 (by omega) hj2]
          have hje : (⟨r + (j.val - r), by omega⟩ : Fin d) = j := Fin.ext (by dsimp; omega)
          rcases lt_trichotomy i.val (j.val - r) with hlt | heq | hgt
          · rw [dif_pos hlt]
            change M.1 ⟨i.val, _⟩ ⟨r + (j.val - r), _⟩ = M.1 i j
            rw [hje]
          · rw [dif_neg (by omega), dif_neg (by omega)]
            have hd0 := M.2.2.2.2 ⟨i.val, hi1⟩
            dsimp only at hd0
            have hje2 : (⟨r + i.val, by omega⟩ : Fin d) = j := Fin.ext (by dsimp; omega)
            rw [hje2] at hd0; exact hd0.symm
          · rw [dif_neg (by omega), dif_pos hgt]
            change M.1 ⟨j.val - r, _⟩ ⟨r + i.val, _⟩ = M.1 i j
            have hsymK := M.2.2.2.1 ⟨j.val - r, by omega⟩ ⟨i.val, hi1⟩
            dsimp only at hsymK
            rw [hje] at hsymK; exact hsymK
        · rw [W0Recon_AC hr _ hi1 (by omega)]
          change M.1 ⟨i.val, _⟩ ⟨2 * r + (j.val - 2 * r), _⟩ = M.1 i j
          have hje : (⟨2 * r + (j.val - 2 * r), by omega⟩ : Fin d) = j := Fin.ext (by dsimp; omega)
          rw [hje]
    · by_cases hj1 : j.val < r
      · have hsym : M.1 j i = M.1 i j := congrFun (congrFun M.2.1.1 i) j
        by_cases hi2 : i.val < 2 * r
        · rw [W0Recon_BA hr _ (by omega) hi2 hj1]
          have hie : (⟨r + (i.val - r), by omega⟩ : Fin d) = i := Fin.ext (by dsimp; omega)
          rcases lt_trichotomy (i.val - r) j.val with hlt | heq | hgt
          · rw [dif_pos hlt]
            change M.1 ⟨i.val - r, _⟩ ⟨r + j.val, _⟩ = M.1 i j
            have hsymK := M.2.2.2.1 ⟨i.val - r, by omega⟩ ⟨j.val, hj1⟩
            dsimp only at hsymK
            rw [hie] at hsymK; rw [hsymK]; exact hsym
          · rw [dif_neg (by omega), dif_neg (by omega)]
            have hd0 := M.2.2.2.2 ⟨j.val, hj1⟩
            dsimp only at hd0
            have hie2 : (⟨r + j.val, by omega⟩ : Fin d) = i := Fin.ext (by dsimp; omega)
            rw [hie2] at hd0; rw [← hsym]; exact hd0.symm
          · rw [dif_neg (by omega), dif_pos hgt]
            change M.1 ⟨j.val, _⟩ ⟨r + (i.val - r), _⟩ = M.1 i j
            rw [hie]; exact hsym
        · rw [W0Recon_CA hr _ (by omega) hj1]
          change M.1 ⟨j.val, _⟩ ⟨2 * r + (i.val - 2 * r), _⟩ = M.1 i j
          have hie : (⟨2 * r + (i.val - 2 * r), by omega⟩ : Fin d) = i := Fin.ext (by dsimp; omega)
          rw [hie]; exact hsym
      · rw [W0Recon_zero hr _ (by omega) (by omega)]
        exact (M.2.2.1 i j (by omega) (by omega)).symm
  right_inv f := by
    funext idx
    rcases idx with ⟨⟨i, j⟩, hij⟩ | ⟨⟨i, j⟩, hij⟩ | ⟨i, c⟩
    · change W0Recon hr f ⟨i.val, _⟩ ⟨j.val, _⟩ = _
      rw [W0Recon_AA hr f i.isLt j.isLt]; dsimp only
      rw [dif_pos (show i.val < j.val from hij)]
    · change W0Recon hr f ⟨i.val, _⟩ ⟨r + j.val, _⟩ = _
      rw [W0Recon_AB hr f i.isLt (by dsimp; omega) (by dsimp; have := j.isLt; omega)]
      simp only [Nat.add_sub_cancel_left]
      rw [dif_pos (show i.val < j.val from hij)]
    · change W0Recon hr f ⟨i.val, _⟩ ⟨2 * r + c.val, _⟩ = _
      rw [W0Recon_AC hr f i.isLt (by dsimp; omega)]
      simp only [Nat.add_sub_cancel_left]

lemma finrank_W0Sub {d r : ℕ} (hr : 2 * r ≤ d) :
    Module.finrank F2 (W0Sub d r hr) = r * (d - r - 1) := by
  rw [(W0Equiv hr).finrank_eq, Module.finrank_fintype_fun_eq_card F2]
  simp only [W0Idx, Fintype.card_sum, Fintype.card_prod, card_pairIdx, Fintype.card_fin]
  rw [← Nat.add_assoc]
  exact dim_formula hr

-- ============================================================================
-- Part 6: Upper Bound — Explicit Rank-2 Spanning Set of Size D + min(C(r,2), r)
-- ============================================================================

def eb {d : ℕ} (k : Fin d) : Fin d → F2 := fun i => if i = k then 1 else 0

def padA {d r : ℕ} (u : Fin r → F2) : Fin d → F2 :=
  fun i => if hi : i.val < r then u ⟨i.val, hi⟩ else 0

def padB {d r : ℕ} (u : Fin r → F2) : Fin d → F2 :=
  fun i => if hi : r ≤ i.val ∧ i.val < 2 * r then u ⟨i.val - r, by omega⟩ else 0

lemma padA_lt {d r : ℕ} (u : Fin r → F2) {i : Fin d} (hi : i.val < r) :
    padA u i = u ⟨i.val, hi⟩ := dif_pos hi

lemma padA_ge {d r : ℕ} (u : Fin r → F2) {i : Fin d} (hi : r ≤ i.val) :
    padA u i = 0 := dif_neg (by omega)

lemma padB_mid {d r : ℕ} (u : Fin r → F2) {i : Fin d} (h1 : r ≤ i.val) (h2 : i.val < 2 * r) :
    padB u i = u ⟨i.val - r, by omega⟩ := dif_pos ⟨h1, h2⟩

lemma padB_not_mid {d r : ℕ} (u : Fin r → F2) {i : Fin d} (h : ¬(r ≤ i.val ∧ i.val < 2 * r)) :
    padB u i = 0 := dif_neg h

lemma padA_add {d r : ℕ} (u v : Fin r → F2) (i : Fin d) :
    padA (u + v) i = padA u i + padA v i := by
  unfold padA; by_cases hi : i.val < r <;> simp [hi]

lemma padB_add {d r : ℕ} (u v : Fin r → F2) (i : Fin d) :
    padB (u + v) i = padB u i + padB v i := by
  unfold padB; by_cases hi : r ≤ i.val ∧ i.val < 2 * r <;> simp [hi]

lemma rk2_eb_symm {d : ℕ} (p q : Fin d) (hpq : p ≠ q) :
    rk2Mat (eb p) (eb q) (eb q) (eb p) =
      fun i j => if (i = p ∧ j = q) ∨ (i = q ∧ j = p) then 1 else 0 := by
  ext i j
  simp only [rk2Mat, eb]
  by_cases hip : i = p
  · subst hip
    by_cases hjq : j = q
    · subst hjq; simp [hpq, Ne.symm hpq]
    · simp [hjq, hpq]
  · by_cases hiq : i = q
    · subst hiq
      by_cases hjp : j = p
      · subst hjp; simp [hpq, Ne.symm hpq]
      · simp [hjp, Ne.symm hpq]
    · simp [hip, hiq]

lemma W0Recon_single_S {d r : ℕ} (hr : 2 * r ≤ d) (p : PairIdx r) :
    W0Recon hr (Pi.single (Sum.inl p) 1) =
      rk2Mat (eb ⟨p.1.1.val, by omega⟩) (eb ⟨p.1.2.val, by omega⟩)
             (eb ⟨p.1.2.val, by omega⟩) (eb ⟨p.1.1.val, by omega⟩) := by
  have hp1 : p.1.1.val < r := p.1.1.isLt
  have hp2 : p.1.2.val < r := p.1.2.isLt
  have hplt : p.1.1.val < p.1.2.val := p.2
  have hne : (⟨p.1.1.val, by omega⟩ : Fin d) ≠ ⟨p.1.2.val, by omega⟩ :=
    fun h => ne_of_lt p.2 (Fin.ext (congrArg (fun x : Fin d => x.val) h))
  rw [rk2_eb_symm _ _ hne]
  ext i j
  by_cases hi : i.val < r
  · by_cases hj : j.val < r
    · rw [W0Recon_AA hr _ hi hj]
      rcases lt_trichotomy i.val j.val with hlt | heq | hgt
      · rw [dif_pos hlt, Pi.single_apply]
        by_cases h : i.val = p.1.1.val ∧ j.val = p.1.2.val
        · have heq : (Sum.inl ⟨(⟨i.val, hi⟩, ⟨j.val, hj⟩), hlt⟩ : W0Idx d r) = Sum.inl p :=
            congrArg Sum.inl (Subtype.ext (Prod.ext (Fin.ext h.1) (Fin.ext h.2)))
          have hdisj : (i = ⟨p.1.1.val, by omega⟩ ∧ j = ⟨p.1.2.val, by omega⟩) ∨
                       (i = ⟨p.1.2.val, by omega⟩ ∧ j = ⟨p.1.1.val, by omega⟩) :=
            Or.inl ⟨Fin.ext h.1, Fin.ext h.2⟩
          rw [if_pos heq, if_pos hdisj]
        · have hne' : (Sum.inl ⟨(⟨i.val, hi⟩, ⟨j.val, hj⟩), hlt⟩ : W0Idx d r) ≠ Sum.inl p := by
            intro he; injection he with he
            exact h ⟨congrArg (fun x : PairIdx r => x.1.1.val) he, congrArg (fun x : PairIdx r => x.1.2.val) he⟩
          have hnot : ¬((i = ⟨p.1.1.val, by omega⟩ ∧ j = ⟨p.1.2.val, by omega⟩) ∨
                        (i = ⟨p.1.2.val, by omega⟩ ∧ j = ⟨p.1.1.val, by omega⟩)) := by
            rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
            · exact h ⟨congrArg Fin.val h1, congrArg Fin.val h2⟩
            · have := congrArg Fin.val h1; have := congrArg Fin.val h2; dsimp at *; omega
          rw [if_neg hne', if_neg hnot]
      · rw [dif_neg (by omega), dif_neg (by omega)]
        have hnot : ¬((i = ⟨p.1.1.val, by omega⟩ ∧ j = ⟨p.1.2.val, by omega⟩) ∨
                      (i = ⟨p.1.2.val, by omega⟩ ∧ j = ⟨p.1.1.val, by omega⟩)) := by
          rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
          · have := congrArg Fin.val h1; have := congrArg Fin.val h2; dsimp at *; omega
        simp only [hnot, ↓reduceIte]
      · rw [dif_neg (by omega), dif_pos hgt, Pi.single_apply]
        by_cases h : j.val = p.1.1.val ∧ i.val = p.1.2.val
        · have heq : (Sum.inl ⟨(⟨j.val, hj⟩, ⟨i.val, hi⟩), hgt⟩ : W0Idx d r) = Sum.inl p :=
            congrArg Sum.inl (Subtype.ext (Prod.ext (Fin.ext h.1) (Fin.ext h.2)))
          have hdisj : (i = ⟨p.1.1.val, by omega⟩ ∧ j = ⟨p.1.2.val, by omega⟩) ∨
                       (i = ⟨p.1.2.val, by omega⟩ ∧ j = ⟨p.1.1.val, by omega⟩) :=
            Or.inr ⟨Fin.ext h.2, Fin.ext h.1⟩
          rw [if_pos heq, if_pos hdisj]
        · have hne' : (Sum.inl ⟨(⟨j.val, hj⟩, ⟨i.val, hi⟩), hgt⟩ : W0Idx d r) ≠ Sum.inl p := by
            intro he; injection he with he
            exact h ⟨congrArg (fun x : PairIdx r => x.1.1.val) he, congrArg (fun x : PairIdx r => x.1.2.val) he⟩
          have hnot : ¬((i = ⟨p.1.1.val, by omega⟩ ∧ j = ⟨p.1.2.val, by omega⟩) ∨
                        (i = ⟨p.1.2.val, by omega⟩ ∧ j = ⟨p.1.1.val, by omega⟩)) := by
            rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
            · have := congrArg Fin.val h1; have := congrArg Fin.val h2; dsimp at *; omega
            · exact h ⟨congrArg Fin.val h2, congrArg Fin.val h1⟩
          rw [if_neg hne', if_neg hnot]
    · have hnot : ¬((i = ⟨p.1.1.val, by omega⟩ ∧ j = ⟨p.1.2.val, by omega⟩) ∨
                    (i = ⟨p.1.2.val, by omega⟩ ∧ j = ⟨p.1.1.val, by omega⟩)) := by
        rintro (⟨_, h2⟩ | ⟨_, h2⟩) <;> (have := congrArg Fin.val h2; dsimp at *; omega)
      simp only [hnot, ↓reduceIte]
      by_cases hj2 : j.val < 2 * r
      · rw [W0Recon_AB hr _ hi (by omega) hj2]
        by_cases hlt : i.val < j.val - r
        · rw [dif_pos hlt]; simp [Pi.single_apply]
        · by_cases hgt : j.val - r < i.val
          · rw [dif_neg hlt, dif_pos hgt]; simp [Pi.single_apply]
          · rw [dif_neg hlt, dif_neg hgt]
      · rw [W0Recon_AC hr _ hi (by omega)]; simp [Pi.single_apply]
  · have hnot : ¬((i = ⟨p.1.1.val, by omega⟩ ∧ j = ⟨p.1.2.val, by omega⟩) ∨
                  (i = ⟨p.1.2.val, by omega⟩ ∧ j = ⟨p.1.1.val, by omega⟩)) := by
      rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> (have := congrArg Fin.val h1; dsimp at *; omega)
    simp only [hnot, ↓reduceIte]
    by_cases hj : j.val < r
    · by_cases hi2 : i.val < 2 * r
      · rw [W0Recon_BA hr _ (by omega) hi2 hj]
        by_cases hlt : i.val - r < j.val
        · rw [dif_pos hlt]; simp [Pi.single_apply]
        · by_cases hgt : j.val < i.val - r
          · rw [dif_neg hlt, dif_pos hgt]; simp [Pi.single_apply]
          · rw [dif_neg hlt, dif_neg hgt]
      · rw [W0Recon_CA hr _ (by omega) hj]; simp [Pi.single_apply]
    · exact W0Recon_zero hr _ (by omega) (by omega)

lemma W0Recon_single_L {d r : ℕ} (hr : 2 * r ≤ d) (i0 : Fin r) (c0 : Fin (d - 2 * r)) :
    W0Recon hr (Pi.single (Sum.inr (Sum.inr (i0, c0))) 1) =
      rk2Mat (eb ⟨i0.val, by omega⟩) (eb ⟨2 * r + c0.val, by omega⟩)
             (eb ⟨2 * r + c0.val, by omega⟩) (eb ⟨i0.val, by omega⟩) := by
  have hi0 : i0.val < r := i0.isLt
  have hne : (⟨i0.val, by omega⟩ : Fin d) ≠ ⟨2 * r + c0.val, by omega⟩ := by
    intro h; have := congrArg Fin.val h; dsimp at this; omega
  rw [rk2_eb_symm _ _ hne]
  ext i j
  by_cases hi : i.val < r
  · by_cases hj2 : 2 * r ≤ j.val
    · rw [W0Recon_AC hr _ hi hj2, Pi.single_apply]
      by_cases h : i.val = i0.val ∧ j.val - 2 * r = c0.val
      · have heq : (Sum.inr (Sum.inr (⟨i.val, hi⟩, ⟨j.val - 2 * r, by omega⟩)) : W0Idx d r) =
            Sum.inr (Sum.inr (i0, c0)) := by
          congr 2; exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
        have hdisj : (i = ⟨i0.val, by omega⟩ ∧ j = ⟨2 * r + c0.val, by omega⟩) ∨
                     (i = ⟨2 * r + c0.val, by omega⟩ ∧ j = ⟨i0.val, by omega⟩) :=
          Or.inl ⟨Fin.ext h.1, Fin.ext (by dsimp; omega)⟩
        rw [if_pos heq, if_pos hdisj]
      · have hne' : (Sum.inr (Sum.inr (⟨i.val, hi⟩, ⟨j.val - 2 * r, by omega⟩)) : W0Idx d r) ≠
            Sum.inr (Sum.inr (i0, c0)) := by
          intro he; injection he with he; injection he with he
          exact h ⟨congrArg (fun x : Fin r × Fin (d - 2 * r) => x.1.val) he,
                   congrArg (fun x : Fin r × Fin (d - 2 * r) => x.2.val) he⟩
        have hnot : ¬((i = ⟨i0.val, by omega⟩ ∧ j = ⟨2 * r + c0.val, by omega⟩) ∨
                      (i = ⟨2 * r + c0.val, by omega⟩ ∧ j = ⟨i0.val, by omega⟩)) := by
          rintro (⟨h1, h2⟩ | ⟨h1, _⟩)
          · apply h; have := congrArg Fin.val h1; have := congrArg Fin.val h2; dsimp at *; omega
          · have := congrArg Fin.val h1; dsimp at *; omega
        rw [if_neg hne', if_neg hnot]
    · have hnot : ¬((i = ⟨i0.val, by omega⟩ ∧ j = ⟨2 * r + c0.val, by omega⟩) ∨
                    (i = ⟨2 * r + c0.val, by omega⟩ ∧ j = ⟨i0.val, by omega⟩)) := by
        rintro (⟨_, h2⟩ | ⟨h1, _⟩)
        · have := congrArg Fin.val h2; dsimp at this; omega
        · have := congrArg Fin.val h1; dsimp at this; omega
      simp only [hnot, ↓reduceIte]
      by_cases hj : j.val < r
      · rw [W0Recon_AA hr _ hi hj]
        by_cases hlt : i.val < j.val
        · rw [dif_pos hlt]; simp [Pi.single_apply]
        · by_cases hgt : j.val < i.val
          · rw [dif_neg hlt, dif_pos hgt]; simp [Pi.single_apply]
          · rw [dif_neg hlt, dif_neg hgt]
      · rw [W0Recon_AB hr _ hi (by omega) (by omega)]
        by_cases hlt : i.val < j.val - r
        · rw [dif_pos hlt]; simp [Pi.single_apply]
        · by_cases hgt : j.val - r < i.val
          · rw [dif_neg hlt, dif_pos hgt]; simp [Pi.single_apply]
          · rw [dif_neg hlt, dif_neg hgt]
  · by_cases hj : j.val < r
    · by_cases hi2 : 2 * r ≤ i.val
      · rw [W0Recon_CA hr _ hi2 hj, Pi.single_apply]
        by_cases h : j.val = i0.val ∧ i.val - 2 * r = c0.val
        · have heq : (Sum.inr (Sum.inr (⟨j.val, hj⟩, ⟨i.val - 2 * r, by omega⟩)) : W0Idx d r) =
              Sum.inr (Sum.inr (i0, c0)) := by
            congr 2; exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
          have hdisj : (i = ⟨i0.val, by omega⟩ ∧ j = ⟨2 * r + c0.val, by omega⟩) ∨
                       (i = ⟨2 * r + c0.val, by omega⟩ ∧ j = ⟨i0.val, by omega⟩) :=
            Or.inr ⟨Fin.ext (by dsimp; omega), Fin.ext h.1⟩
          rw [if_pos heq, if_pos hdisj]
        · have hne' : (Sum.inr (Sum.inr (⟨j.val, hj⟩, ⟨i.val - 2 * r, by omega⟩)) : W0Idx d r) ≠
              Sum.inr (Sum.inr (i0, c0)) := by
            intro he; injection he with he; injection he with he
            exact h ⟨congrArg (fun x : Fin r × Fin (d - 2 * r) => x.1.val) he,
                     congrArg (fun x : Fin r × Fin (d - 2 * r) => x.2.val) he⟩
          have hnot : ¬((i = ⟨i0.val, by omega⟩ ∧ j = ⟨2 * r + c0.val, by omega⟩) ∨
                        (i = ⟨2 * r + c0.val, by omega⟩ ∧ j = ⟨i0.val, by omega⟩)) := by
            rintro (⟨h1, _⟩ | ⟨h1, h2⟩)
            · have := congrArg Fin.val h1; dsimp at *; omega
            · apply h; have := congrArg Fin.val h1; have := congrArg Fin.val h2; dsimp at *; omega
          rw [if_neg hne', if_neg hnot]
      · have hnot : ¬((i = ⟨i0.val, by omega⟩ ∧ j = ⟨2 * r + c0.val, by omega⟩) ∨
                      (i = ⟨2 * r + c0.val, by omega⟩ ∧ j = ⟨i0.val, by omega⟩)) := by
          rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> (have := congrArg Fin.val h1; dsimp at *; omega)
        simp only [hnot, ↓reduceIte]
        rw [W0Recon_BA hr _ (by omega) (by omega) hj]
        by_cases hlt : i.val - r < j.val
        · rw [dif_pos hlt]; simp [Pi.single_apply]
        · by_cases hgt : j.val < i.val - r
          · rw [dif_neg hlt, dif_pos hgt]; simp [Pi.single_apply]
          · rw [dif_neg hlt, dif_neg hgt]
    · have hnot : ¬((i = ⟨i0.val, by omega⟩ ∧ j = ⟨2 * r + c0.val, by omega⟩) ∨
                    (i = ⟨2 * r + c0.val, by omega⟩ ∧ j = ⟨i0.val, by omega⟩)) := by
        rintro (⟨h1, _⟩ | ⟨_, h2⟩)
        · have := congrArg Fin.val h1; dsimp at this; omega
        · have := congrArg Fin.val h2; dsimp at this; omega
      simp only [hnot, ↓reduceIte]
      exact W0Recon_zero hr _ (by omega) (by omega)

private lemma single_K_entry {d r : ℕ} (p : PairIdx r) (u v : Fin r) :
    (if hlt : u.val < v.val then
       (Pi.single (Sum.inr (Sum.inl p)) (1 : F2) : W0Idx d r → F2) (Sum.inr (Sum.inl ⟨(u, v), hlt⟩))
     else if hgt : v.val < u.val then
       (Pi.single (Sum.inr (Sum.inl p)) (1 : F2) : W0Idx d r → F2) (Sum.inr (Sum.inl ⟨(v, u), hgt⟩))
     else 0) =
    (if u = p.1.1 then (1 : F2) else 0) * (if v = p.1.2 then 1 else 0) +
    (if u = p.1.2 then (1 : F2) else 0) * (if v = p.1.1 then 1 else 0) := by
  have hplt : p.1.1.val < p.1.2.val := p.2
  have hne_p : p.1.1 ≠ p.1.2 := fun h => ne_of_lt p.2 h
  rcases lt_trichotomy u.val v.val with hlt | heq | hgt
  · rw [dif_pos hlt, Pi.single_apply]
    have hnot2 : ¬(u = p.1.2 ∧ v = p.1.1) := by rintro ⟨rfl, rfl⟩; omega
    by_cases h1 : u = p.1.1 ∧ v = p.1.2
    · rcases h1 with ⟨rfl, rfl⟩
      have heq_p : (Sum.inr (Sum.inl ⟨(p.1.1, p.1.2), hlt⟩) : W0Idx d r) = Sum.inr (Sum.inl p) := rfl
      rw [if_pos heq_p]; simp [hne_p]
    · have hne : (Sum.inr (Sum.inl ⟨(u, v), hlt⟩) : W0Idx d r) ≠ Sum.inr (Sum.inl p) := by
        intro he; injection he with he; injection he with he
        exact h1 ⟨congrArg (fun q : PairIdx r => q.1.1) he, congrArg (fun q : PairIdx r => q.1.2) he⟩
      rw [if_neg hne]
      by_cases hu1 : u = p.1.1
      · subst hu1; have hv2 : v ≠ p.1.2 := fun hv => h1 ⟨rfl, hv⟩
        simp [hv2, hne_p]
      · by_cases hu2 : u = p.1.2
        · subst hu2; have hv1 : v ≠ p.1.1 := fun hv => hnot2 ⟨rfl, hv⟩
          simp [hu1, hv1]
        · simp [hu1, hu2]
  · rw [dif_neg (by omega), dif_neg (by omega)]
    have huv : u = v := Fin.ext heq; subst huv
    by_cases hu1 : u = p.1.1
    · subst hu1; simp [hne_p]
    · by_cases hu2 : u = p.1.2
      · subst hu2; simp [hne_p.symm]
      · simp [hu1, hu2]
  · rw [dif_neg (by omega), dif_pos hgt, Pi.single_apply]
    have hnot1 : ¬(u = p.1.1 ∧ v = p.1.2) := by rintro ⟨rfl, rfl⟩; omega
    by_cases h2 : u = p.1.2 ∧ v = p.1.1
    · rcases h2 with ⟨rfl, rfl⟩
      have heq_p : (Sum.inr (Sum.inl ⟨(p.1.1, p.1.2), hgt⟩) : W0Idx d r) = Sum.inr (Sum.inl p) := rfl
      rw [if_pos heq_p]; simp [hne_p.symm]
    · have hne : (Sum.inr (Sum.inl ⟨(v, u), hgt⟩) : W0Idx d r) ≠ Sum.inr (Sum.inl p) := by
        intro he; injection he with he; injection he with he
        exact h2 ⟨congrArg (fun q : PairIdx r => q.1.2) he, congrArg (fun q : PairIdx r => q.1.1) he⟩
      rw [if_neg hne]
      by_cases hu1 : u = p.1.1
      · subst hu1; have hv2 : v ≠ p.1.2 := fun hv => hnot1 ⟨rfl, hv⟩
        simp [hv2, hne_p]
      · by_cases hu2 : u = p.1.2
        · subst hu2; have hv1 : v ≠ p.1.1 := fun hv => h2 ⟨rfl, hv⟩
          simp [hu1, hv1]
        · simp [hu1, hu2]

lemma W0Recon_single_K_dir {d r : ℕ} (hr : 2 * r ≤ d) (p : PairIdx r) :
    W0Recon hr (Pi.single (Sum.inr (Sum.inl p)) 1) =
      rk2Mat (padA (eb p.1.1)) (padB (eb p.1.2)) (padB (eb p.1.2)) (padA (eb p.1.1)) +
      rk2Mat (padA (eb p.1.2)) (padB (eb p.1.1)) (padB (eb p.1.1)) (padA (eb p.1.2)) := by
  ext i j
  simp only [Matrix.add_apply, rk2Mat]
  by_cases hi : i.val < r
  · have hi_nm : ¬(r ≤ i.val ∧ i.val < 2 * r) := by omega
    by_cases hj1 : j.val < r
    · have hj_nm : ¬(r ≤ j.val ∧ j.val < 2 * r) := by omega
      rw [W0Recon_AA hr _ hi hj1,
          padB_not_mid _ hi_nm, padB_not_mid _ hi_nm,
          padB_not_mid _ hj_nm, padB_not_mid _ hj_nm]
      simp only [mul_zero, zero_mul, add_zero]
      by_cases hlt : i.val < j.val
      · rw [dif_pos hlt]; simp [Pi.single_apply]
      · by_cases hgt : j.val < i.val
        · rw [dif_neg hlt, dif_pos hgt]; simp [Pi.single_apply]
        · rw [dif_neg hlt, dif_neg hgt]
    · by_cases hj2 : j.val < 2 * r
      · have hj_ge : r ≤ j.val := by omega
        rw [W0Recon_AB hr _ hi hj_ge hj2,
            padA_lt _ hi, padA_lt _ hi, padB_mid _ hj_ge hj2, padB_mid _ hj_ge hj2,
            padB_not_mid _ hi_nm, padB_not_mid _ hi_nm]
        simp only [zero_mul, add_zero, eb]
        exact single_K_entry (d := d) p ⟨i.val, hi⟩ ⟨j.val - r, by omega⟩
      · have hj_nm : ¬(r ≤ j.val ∧ j.val < 2 * r) := by omega
        rw [W0Recon_AC hr _ hi (by omega),
            padB_not_mid _ hi_nm, padB_not_mid _ hi_nm,
            padB_not_mid _ hj_nm, padB_not_mid _ hj_nm]
        simp [Pi.single_apply]
  · have hi_ge : r ≤ i.val := by omega
    by_cases hj : j.val < r
    · by_cases hi2 : i.val < 2 * r
      · rw [W0Recon_BA hr _ hi_ge hi2 hj,
            padA_ge _ hi_ge, padA_ge _ hi_ge,
            padB_mid _ hi_ge hi2, padB_mid _ hi_ge hi2,
            padA_lt _ hj, padA_lt _ hj]
        simp only [zero_mul, zero_add, eb]
        exact (single_K_entry (d := d) p ⟨i.val - r, by omega⟩ ⟨j.val, hj⟩).trans (add_comm _ _)
      · have hi_nm : ¬(r ≤ i.val ∧ i.val < 2 * r) := by omega
        rw [W0Recon_CA hr _ (by omega) hj,
            padA_ge _ hi_ge, padA_ge _ hi_ge,
            padB_not_mid _ hi_nm, padB_not_mid _ hi_nm]
        simp [Pi.single_apply]
    · have hj_ge : r ≤ j.val := by omega
      rw [W0Recon_zero hr _ hi_ge hj_ge,
          padA_ge _ hi_ge, padA_ge _ hi_ge,
          padA_ge _ hj_ge, padA_ge _ hj_ge]
      simp only [zero_mul, mul_zero, add_zero]

lemma W0Recon_single_K_sq {d r : ℕ} (hr : 2 * r ≤ d) (p : PairIdx r) :
    W0Recon hr (Pi.single (Sum.inr (Sum.inl p)) 1) =
      rk2Mat (padA (eb p.1.1 + eb p.1.2)) (padB (eb p.1.1 + eb p.1.2))
             (padB (eb p.1.1 + eb p.1.2)) (padA (eb p.1.1 + eb p.1.2)) +
      rk2Mat (padA (eb p.1.1)) (padB (eb p.1.1)) (padB (eb p.1.1)) (padA (eb p.1.1)) +
      rk2Mat (padA (eb p.1.2)) (padB (eb p.1.2)) (padB (eb p.1.2)) (padA (eb p.1.2)) := by
  rw [W0Recon_single_K_dir hr p]
  ext i j
  simp only [Matrix.add_apply, rk2Mat, padA_add, padB_add]
  have h : ∀ x1 x2 y1 y2 z1 z2 w1 w2 : F2,
      (x1 * y2 + z2 * w1) + (x2 * y1 + z1 * w2) +
      (((x1 + x2) * (y1 + y2) + (z1 + z2) * (w1 + w2)) + (x1 * y1 + z1 * w1) + (x2 * y2 + z2 * w2)) =
      (2 : F2) * (x1 * y1 + x1 * y2 + x2 * y1 + x2 * y2 + z1 * w1 + z1 * w2 + z2 * w1 + z2 * w2) := by
    intro x1 x2 y1 y2 z1 z2 w1 w2; ring
  have h0 := h (padA (eb p.1.1) i) (padA (eb p.1.2) i) (padB (eb p.1.1) j) (padB (eb p.1.2) j)
               (padB (eb p.1.1) i) (padB (eb p.1.2) i) (padA (eb p.1.1) j) (padA (eb p.1.2) j)
  rw [zmod2_two, zero_mul] at h0
  exact zmod2_eq_of_add_eq_zero h0

lemma W0_upper_span {d r : ℕ} (hr : 2 * r ≤ d) :
    ∃ (m : ℕ) (a b c e : Fin m → Fin d → F2),
      m = r * (d - r - 1) + min (Nat.choose r 2) r ∧
      W0Sub d r hr ≤
        Submodule.span F2 (Set.range fun l : Fin m => rk2Mat (a l) (b l) (c l) (e l)) := by
  classical
  -- We construct generators indexed by a Fintype and re-index via Fintype.equivFin
  by_cases hmin : Nat.choose r 2 ≤ r
  · -- Way 2: S (choose r 2) + L (r*(d-2r)) + K_dir1 (choose r 2) + K_dir2 (choose r 2)
    let Idx := PairIdx r ⊕ (Fin r × Fin (d - 2 * r)) ⊕ PairIdx r ⊕ PairIdx r
    let genA : Idx → Fin d → F2
      | Sum.inl p => eb ⟨p.1.1.val, by omega⟩
      | Sum.inr (Sum.inl (i, _)) => eb ⟨i.val, by omega⟩
      | Sum.inr (Sum.inr (Sum.inl p)) => padA (eb p.1.1)
      | Sum.inr (Sum.inr (Sum.inr p)) => padA (eb p.1.2)
    let genB : Idx → Fin d → F2
      | Sum.inl p => eb ⟨p.1.2.val, by omega⟩
      | Sum.inr (Sum.inl (_, c)) => eb ⟨2 * r + c.val, by omega⟩
      | Sum.inr (Sum.inr (Sum.inl p)) => padB (eb p.1.2)
      | Sum.inr (Sum.inr (Sum.inr p)) => padB (eb p.1.1)
    let genC : Idx → Fin d → F2 := genB
    let genE : Idx → Fin d → F2 := genA
    let eqv := Fintype.equivFin Idx
    have hcard : Fintype.card Idx = r * (d - r - 1) + min (Nat.choose r 2) r := by
      simp only [Idx, Fintype.card_sum, Fintype.card_prod, card_pairIdx, Fintype.card_fin]
      rw [min_eq_left hmin, ← dim_formula hr]
      omega
    refine ⟨Fintype.card Idx, fun l => genA (eqv.symm l), fun l => genB (eqv.symm l),
            fun l => genC (eqv.symm l), fun l => genE (eqv.symm l), hcard, ?_⟩
    intro M hM
    let S := Submodule.span F2
      (Set.range fun l : Fin (Fintype.card Idx) =>
        rk2Mat (genA (eqv.symm l)) (genB (eqv.symm l)) (genC (eqv.symm l)) (genE (eqv.symm l)))
    have hgen_mem : ∀ x : Idx, rk2Mat (genA x) (genB x) (genC x) (genE x) ∈ S := fun x =>
      Submodule.subset_span ⟨eqv x, by simp⟩
    let f := W0Equiv hr ⟨M, hM⟩
    have hMeq : M = ∑ k : W0Idx d r, f k • W0Recon hr (Pi.single k 1) := by
      have hf : f = ∑ k : W0Idx d r, f k • Pi.single k (1 : F2) := by
        funext x; simp [Pi.single_apply]
      have hM1 : (⟨M, hM⟩ : W0Sub d r hr) = (W0Equiv hr).symm f := ((W0Equiv hr).symm_apply_apply _).symm
      have hM2 : M = ((W0Equiv hr).symm (∑ k : W0Idx d r, f k • Pi.single k (1 : F2))).1 := by
        rw [← hf]; exact congrArg Subtype.val hM1
      rw [hM2, map_sum]
      simp only [Submodule.coe_sum, map_smul, Submodule.coe_smul]
      rfl
    rw [hMeq]
    refine Submodule.sum_mem S fun k _ => Submodule.smul_mem S _ ?_
    rcases k with p | p | ⟨i0, c0⟩
    · rw [W0Recon_single_S hr p]; exact hgen_mem (Sum.inl p)
    · rw [W0Recon_single_K_dir hr p]
      exact S.add_mem (hgen_mem (Sum.inr (Sum.inr (Sum.inl p))))
                      (hgen_mem (Sum.inr (Sum.inr (Sum.inr p))))
    · rw [W0Recon_single_L hr i0 c0]; exact hgen_mem (Sum.inr (Sum.inl (i0, c0)))
  · -- Way 1: S (choose r 2) + L (r*(d-2r)) + K_diag (r) + K_sq (choose r 2)
    let Idx := PairIdx r ⊕ (Fin r × Fin (d - 2 * r)) ⊕ Fin r ⊕ PairIdx r
    let genA : Idx → Fin d → F2
      | Sum.inl p => eb ⟨p.1.1.val, by omega⟩
      | Sum.inr (Sum.inl (i, _)) => eb ⟨i.val, by omega⟩
      | Sum.inr (Sum.inr (Sum.inl i)) => padA (eb i)
      | Sum.inr (Sum.inr (Sum.inr p)) => padA (eb p.1.1 + eb p.1.2)
    let genB : Idx → Fin d → F2
      | Sum.inl p => eb ⟨p.1.2.val, by omega⟩
      | Sum.inr (Sum.inl (_, c)) => eb ⟨2 * r + c.val, by omega⟩
      | Sum.inr (Sum.inr (Sum.inl i)) => padB (eb i)
      | Sum.inr (Sum.inr (Sum.inr p)) => padB (eb p.1.1 + eb p.1.2)
    let genC : Idx → Fin d → F2 := genB
    let genE : Idx → Fin d → F2 := genA
    let eqv := Fintype.equivFin Idx
    have hcard : Fintype.card Idx = r * (d - r - 1) + min (Nat.choose r 2) r := by
      simp only [Idx, Fintype.card_sum, Fintype.card_prod, card_pairIdx, Fintype.card_fin]
      rw [min_eq_right (by omega), ← dim_formula hr]
      omega
    refine ⟨Fintype.card Idx, fun l => genA (eqv.symm l), fun l => genB (eqv.symm l),
            fun l => genC (eqv.symm l), fun l => genE (eqv.symm l), hcard, ?_⟩
    intro M hM
    let S := Submodule.span F2
      (Set.range fun l : Fin (Fintype.card Idx) =>
        rk2Mat (genA (eqv.symm l)) (genB (eqv.symm l)) (genC (eqv.symm l)) (genE (eqv.symm l)))
    have hgen_mem : ∀ x : Idx, rk2Mat (genA x) (genB x) (genC x) (genE x) ∈ S := fun x =>
      Submodule.subset_span ⟨eqv x, by simp⟩
    let f := W0Equiv hr ⟨M, hM⟩
    have hMeq : M = ∑ k : W0Idx d r, f k • W0Recon hr (Pi.single k 1) := by
      have hf : f = ∑ k : W0Idx d r, f k • Pi.single k (1 : F2) := by
        funext x; simp [Pi.single_apply]
      have hM1 : (⟨M, hM⟩ : W0Sub d r hr) = (W0Equiv hr).symm f := ((W0Equiv hr).symm_apply_apply _).symm
      have hM2 : M = ((W0Equiv hr).symm (∑ k : W0Idx d r, f k • Pi.single k (1 : F2))).1 := by
        rw [← hf]; exact congrArg Subtype.val hM1
      rw [hM2, map_sum]
      simp only [Submodule.coe_sum, map_smul, Submodule.coe_smul]
      rfl
    rw [hMeq]
    refine Submodule.sum_mem S fun k _ => Submodule.smul_mem S _ ?_
    rcases k with p | p | ⟨i0, c0⟩
    · rw [W0Recon_single_S hr p]; exact hgen_mem (Sum.inl p)
    · rw [W0Recon_single_K_sq hr p]
      exact S.add_mem (S.add_mem (hgen_mem (Sum.inr (Sum.inr (Sum.inr p))))
                                 (hgen_mem (Sum.inr (Sum.inr (Sum.inl p.1.1)))))
                      (hgen_mem (Sum.inr (Sum.inr (Sum.inl p.1.2))))
    · rw [W0Recon_single_L hr i0 c0]; exact hgen_mem (Sum.inr (Sum.inl (i0, c0)))

-- ============================================================================
-- Part 7: Lower Bound — D ≤ t and r ≤ 4 * (t - D) + 1
-- ============================================================================

lemma no_rank2_four (a1 a2 b1 b2 : Fin 4 → F2)
    (h20 : a1 2 * b1 0 + a2 2 * b2 0 = 0)
    (h21 : a1 2 * b1 1 + a2 2 * b2 1 = 1)
    (h22 : a1 2 * b1 2 + a2 2 * b2 2 = 0)
    (h30 : a1 3 * b1 0 + a2 3 * b2 0 = 1)
    (h31 : a1 3 * b1 1 + a2 3 * b2 1 = 0)
    (h32 : a1 3 * b1 2 + a2 3 * b2 2 = 0)
    (h12 : a1 1 * b1 2 + a2 1 * b2 2 = 1) : False := by
  let det := a1 2 * a2 3 + a2 2 * a1 3
  have hdet_mul : det * (b1 0 * b2 1 + b2 0 * b1 1) = 1 := by
    have h1 : det * (b1 0 * b2 1 + b2 0 * b1 1) +
        ((a1 2 * b1 0 + a2 2 * b2 0) * (a1 3 * b1 1 + a2 3 * b2 1) +
         (a1 2 * b1 1 + a2 2 * b2 1) * (a1 3 * b1 0 + a2 3 * b2 0)) =
        (2 : F2) * (a1 2 * a1 3 * b1 0 * b1 1 + a2 2 * a2 3 * b2 0 * b2 1 +
          a1 2 * a2 3 * b1 0 * b2 1 + a2 2 * a1 3 * b2 0 * b1 1 +
          a1 2 * a2 3 * b1 1 * b2 0 + a2 2 * a1 3 * b2 1 * b1 0) := by
      dsimp [det]; ring
    rw [zmod2_two, zero_mul, h20, h31, h21, h30] at h1
    simp only [mul_zero, mul_one, zero_add] at h1
    exact zmod2_eq_of_add_eq_zero h1
  have hdet1 : det = 1 := by
    apply zmod2_eq_one_of_ne_zero
    intro h0; rw [h0, zero_mul] at hdet_mul; exact zero_ne_one hdet_mul
  have hb1 : b1 2 = 0 := by
    have h1 : det * b1 2 + (a2 3 * (a1 2 * b1 2 + a2 2 * b2 2) +
        a2 2 * (a1 3 * b1 2 + a2 3 * b2 2)) =
        (2 : F2) * (a1 2 * a2 3 * b1 2 + a2 2 * a1 3 * b1 2 + a2 2 * a2 3 * b2 2) := by
      dsimp [det]; ring
    rw [zmod2_two, zero_mul, h22, h32, hdet1] at h1
    simpa using h1
  have hb2 : b2 2 = 0 := by
    have h1 : det * b2 2 + (a1 3 * (a1 2 * b1 2 + a2 2 * b2 2) +
        a1 2 * (a1 3 * b1 2 + a2 3 * b2 2)) =
        (2 : F2) * (a1 2 * a1 3 * b1 2 + a1 2 * a2 3 * b2 2 + a2 2 * a1 3 * b2 2) := by
      dsimp [det]; ring
    rw [zmod2_two, zero_mul, h22, h32, hdet1] at h1
    simpa using h1
  rw [hb1, hb2, mul_zero, mul_zero, add_zero] at h12
  exact zero_ne_one h12

lemma exists_minimal_span_subset {V : Type*} [AddCommGroup V] [Module F2 V]
    {m : ℕ} (v : Fin m → V) :
    ∃ J : Finset (Fin m),
      LinearIndependent F2 (fun j : J => v j.1) ∧
      ∀ l : Fin m, v l ∈ Submodule.span F2 (Set.range fun j : J => v j.1) := by
  classical
  let P : ℕ → Prop := fun k => ∃ J : Finset (Fin m), J.card = k ∧
    ∀ l : Fin m, v l ∈ Submodule.span F2 (Set.range fun j : J => v j.1)
  have hex : ∃ k, P k := by
    refine ⟨m, Finset.univ, Finset.card_fin m, fun l => ?_⟩
    exact Submodule.subset_span ⟨⟨l, Finset.mem_univ l⟩, rfl⟩
  let k0 := Nat.find hex
  obtain ⟨J, hJcard, hJspan⟩ := Nat.find_spec hex
  refine ⟨J, ?_, hJspan⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push_neg at hne
  obtain ⟨j0, hj0⟩ := hne
  have hc0 : c j0 = 1 := zmod2_eq_one_of_ne_zero hj0
  -- Express v j0 in terms of J.erase j0
  let J' : Finset (Fin m) := J.erase j0.1
  have hJ'_card : J'.card < k0 := by
    dsimp only [k0]
    rw [← hJcard]
    exact Finset.card_erase_lt_of_mem j0.2
  have hvj0_mem : v j0.1 ∈ Submodule.span F2 (Set.range fun j : J' => v j.1) := by
    have hsplit := Finset.add_sum_erase (s := (Finset.univ : Finset J))
      (f := fun j : J => c j • v j.1) (a := j0) (Finset.mem_univ j0)
    rw [hc0, one_smul] at hsplit
    rw [← hsplit] at hc
    have heq : v j0.1 = ∑ j ∈ (Finset.univ : Finset J).erase j0, c j • v j.1 := by
      have hneg : v j0.1 = -(∑ j ∈ (Finset.univ : Finset J).erase j0, c j • v j.1) :=
        eq_neg_of_add_eq_zero_left hc
      rw [hneg]
      have hchar : ∀ x : V, -x = x := fun x => by
        have h2 : (1 + 1 : F2) • x = 0 := by
          have : (1 + 1 : F2) = 0 := rfl
          rw [this, zero_smul]
        rw [add_smul, one_smul] at h2
        exact (eq_neg_of_add_eq_zero_left h2).symm
      exact hchar _
    rw [heq]
    refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_
    have hne_j : j.1 ≠ j0.1 := fun h => (Finset.mem_erase.mp hj).1 (Subtype.ext h)
    have hmem' : j.1 ∈ J' := Finset.mem_erase.mpr ⟨hne_j, j.2⟩
    exact Submodule.subset_span ⟨⟨j.1, hmem'⟩, rfl⟩
  have hJ'_span : ∀ l : Fin m, v l ∈ Submodule.span F2 (Set.range fun j : J' => v j.1) := by
    intro l
    have hl := hJspan l
    refine Submodule.span_le.mpr ?_ hl
    rintro x ⟨⟨j, hj⟩, rfl⟩
    by_cases hjeq : j = j0.1
    · subst hjeq; exact hvj0_mem
    · exact Submodule.subset_span ⟨⟨j, Finset.mem_erase.mpr ⟨hjeq, hj⟩⟩, rfl⟩
  exact Nat.find_min hex hJ'_card ⟨J', rfl, hJ'_span⟩

def dotB {d r : ℕ} (hr : 2 * r ≤ d) (M : Matrix (Fin d) (Fin d) F2) (x y : Fin r → F2) : F2 :=
  ∑ p : Fin r, ∑ q : Fin r, x p * M ⟨p.val, by have := p.isLt; omega⟩ ⟨r + q.val, by have := q.isLt; omega⟩ * y q

def dotC {d r : ℕ} (hr : 2 * r ≤ d) (M : Matrix (Fin d) (Fin d) F2) (x y : Fin r → F2) : F2 :=
  ∑ p : Fin r, ∑ q : Fin r, x p * M ⟨r + p.val, by have := p.isLt; omega⟩ ⟨q.val, by have := q.isLt; omega⟩ * y q

def dotE {d r : ℕ} (hr : 2 * r ≤ d) (M : Matrix (Fin d) (Fin d) F2) (x y : Fin r → F2) : F2 :=
  ∑ p : Fin r, ∑ q : Fin r, x p * M ⟨r + p.val, by have := p.isLt; omega⟩ ⟨r + q.val, by have := q.isLt; omega⟩ * y q

lemma dotB_add {d r : ℕ} (hr : 2 * r ≤ d) (M1 M2 : Matrix (Fin d) (Fin d) F2) (x y : Fin r → F2) :
    dotB hr (M1 + M2) x y = dotB hr M1 x y + dotB hr M2 x y := by
  simp only [dotB, Matrix.add_apply]; simp_rw [mul_add, add_mul, Finset.sum_add_distrib]

lemma dotC_add {d r : ℕ} (hr : 2 * r ≤ d) (M1 M2 : Matrix (Fin d) (Fin d) F2) (x y : Fin r → F2) :
    dotC hr (M1 + M2) x y = dotC hr M1 x y + dotC hr M2 x y := by
  simp only [dotC, Matrix.add_apply]; simp_rw [mul_add, add_mul, Finset.sum_add_distrib]

lemma dotE_add {d r : ℕ} (hr : 2 * r ≤ d) (M1 M2 : Matrix (Fin d) (Fin d) F2) (x y : Fin r → F2) :
    dotE hr (M1 + M2) x y = dotE hr M1 x y + dotE hr M2 x y := by
  simp only [dotE, Matrix.add_apply]; simp_rw [mul_add, add_mul, Finset.sum_add_distrib]

lemma dotB_sum {d r : ℕ} (hr : 2 * r ≤ d) {ι : Type*} (s : Finset ι) (f : ι → F2)
    (M : ι → Matrix (Fin d) (Fin d) F2) (x y : Fin r → F2) :
    dotB hr (∑ i ∈ s, f i • M i) x y = ∑ i ∈ s, f i * dotB hr (M i) x y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dotB]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, dotB_add, ih, Finset.sum_insert ha]
    congr 1
    simp only [dotB, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    ring

lemma dotC_sum {d r : ℕ} (hr : 2 * r ≤ d) {ι : Type*} (s : Finset ι) (f : ι → F2)
    (M : ι → Matrix (Fin d) (Fin d) F2) (x y : Fin r → F2) :
    dotC hr (∑ i ∈ s, f i • M i) x y = ∑ i ∈ s, f i * dotC hr (M i) x y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dotC]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, dotC_add, ih, Finset.sum_insert ha]
    congr 1
    simp only [dotC, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    ring

lemma dotE_sum {d r : ℕ} (hr : 2 * r ≤ d) {ι : Type*} (s : Finset ι) (f : ι → F2)
    (M : ι → Matrix (Fin d) (Fin d) F2) (x y : Fin r → F2) :
    dotE hr (∑ i ∈ s, f i • M i) x y = ∑ i ∈ s, f i * dotE hr (M i) x y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dotE]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, dotE_add, ih, Finset.sum_insert ha]
    congr 1
    simp only [dotE, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    ring

lemma dot_W0_props {d r : ℕ} (hr : 2 * r ≤ d) {W : Matrix (Fin d) (Fin d) F2}
    (hW : W ∈ W0Sub d r hr) :
    (∀ x y, dotE hr W x y = 0) ∧
    (∀ x y, dotC hr W x y = dotB hr W x y) ∧
    (∀ x y, dotB hr W x y = dotB hr W y x) ∧
    (∀ x, dotB hr W x x = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    simp only [dotE]
    apply Finset.sum_eq_zero; intro p _
    apply Finset.sum_eq_zero; intro q _
    rw [hW.2.1 _ _ (by dsimp; omega) (by dsimp; omega), mul_zero, zero_mul]
  · intro x y
    simp only [dotC, dotB]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    have hsym : W ⟨r + p.val, by have := p.isLt; omega⟩ ⟨q.val, by have := q.isLt; omega⟩ =
        W ⟨q.val, by have := q.isLt; omega⟩ ⟨r + p.val, by have := p.isLt; omega⟩ :=
      congrFun (congrFun hW.1.1 ⟨q.val, by have := q.isLt; omega⟩) ⟨r + p.val, by have := p.isLt; omega⟩
    rw [hsym, hW.2.2.1 q p]
  · intro x y
    simp only [dotB]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro q _
    apply Finset.sum_congr rfl; intro p _
    rw [hW.2.2.1 p q]; ring
  · intro x
    refine sum_symm_zero_diag (fun p q => x p * W ⟨p.val, by have := p.isLt; omega⟩ ⟨r + q.val, by have := q.isLt; omega⟩ * x q)
      ?_ ?_
    · intro p q; rw [hW.2.2.1 p q]; ring
    · intro p; rw [hW.2.2.2 p, mul_zero, zero_mul]

lemma ker_Λ_finrank_le_one {d r m : ℕ} (hr : 2 * r ≤ d)
    (a b c e : Fin m → Fin d → F2)
    (hW0 : W0Sub d r hr ≤
      Submodule.span F2 (Set.range fun l : Fin m => rk2Mat (a l) (b l) (c l) (e l)))
    (J : Finset (Fin m))
    (hJ_span : ∀ l : Fin m, (W0Sub d r hr).mkQ (rk2Mat (a l) (b l) (c l) (e l)) ∈
      Submodule.span F2 (Set.range fun j : J => (W0Sub d r hr).mkQ (rk2Mat (a j.1) (b j.1) (c j.1) (e j.1))))
    (Λ : (Fin r → F2) →ₗ[F2] (J × Fin 4 → F2))
    (hΛ_ker : ∀ x ∈ LinearMap.ker Λ, ∀ j : J,
      (∑ i : Fin r, b j.1 ⟨r + i.val, by have := i.isLt; omega⟩ * x i = 0) ∧
      (∑ i : Fin r, e j.1 ⟨r + i.val, by have := i.isLt; omega⟩ * x i = 0) ∧
      (∑ i : Fin r, a j.1 ⟨r + i.val, by have := i.isLt; omega⟩ * x i = 0) ∧
      (∑ i : Fin r, c j.1 ⟨r + i.val, by have := i.isLt; omega⟩ * x i = 0)) :
    Module.finrank F2 (LinearMap.ker Λ) ≤ 1 := by
  classical
  let G : Fin m → Matrix (Fin d) (Fin d) F2 := fun l => rk2Mat (a l) (b l) (c l) (e l)
  let qMap := (W0Sub d r hr).mkQ
  by_contra hgt
  have hge2 : 2 ≤ Module.finrank F2 (LinearMap.ker Λ) := by omega
  let bK := Module.finBasis F2 (LinearMap.ker Λ)
  let v : Fin r → F2 := (bK ⟨0, by omega⟩).1
  let w : Fin r → F2 := (bK ⟨1, by omega⟩).1
  have hv_ker : v ∈ LinearMap.ker Λ := (bK ⟨0, by omega⟩).2
  have hw_ker : w ∈ LinearMap.ker Λ := (bK ⟨1, by omega⟩).2
  have hv_ne0 : v ≠ 0 := by
    intro h0
    exact bK.ne_zero ⟨0, by omega⟩ (Subtype.ext h0)
  have hw_ne0 : w ≠ 0 := by
    intro h0
    exact bK.ne_zero ⟨1, by omega⟩ (Subtype.ext h0)
  have hvw_ne : v ≠ w := by
    intro heq
    have hinj := bK.injective (Subtype.ext heq)
    have := congrArg Fin.val hinj; dsimp at this; omega
  have hGj_zero : ∀ j : J, ∀ x ∈ LinearMap.ker Λ, ∀ y ∈ LinearMap.ker Λ,
      dotB hr (G j.1) x y = 0 ∧ dotC hr (G j.1) x y = 0 ∧ dotE hr (G j.1) x y = 0 := by
    intro j x hx y hy
    obtain ⟨hy1, hy2, _, _⟩ := hΛ_ker y hy j
    obtain ⟨_, _, hx1, hx2⟩ := hΛ_ker x hx j
    refine ⟨?_, ?_, ?_⟩
    · simp only [dotB, G, rk2Mat]
      have hfac : ∀ p q : Fin r,
          x p * (a j.1 ⟨p.val, by have := p.isLt; omega⟩ * b j.1 ⟨r + q.val, by have := q.isLt; omega⟩ +
                 c j.1 ⟨p.val, by have := p.isLt; omega⟩ * e j.1 ⟨r + q.val, by have := q.isLt; omega⟩) * y q =
          (x p * a j.1 ⟨p.val, by have := p.isLt; omega⟩) * (b j.1 ⟨r + q.val, by have := q.isLt; omega⟩ * y q) +
          (x p * c j.1 ⟨p.val, by have := p.isLt; omega⟩) * (e j.1 ⟨r + q.val, by have := q.isLt; omega⟩ * y q) := by
        intro p q; ring
      simp_rw [hfac, Finset.sum_add_distrib, ← Finset.mul_sum, hy1, hy2, mul_zero,
        Finset.sum_const_zero, add_zero]
    · simp only [dotC, G, rk2Mat]
      have hfac : ∀ p q : Fin r,
          x p * (a j.1 ⟨r + p.val, by have := p.isLt; omega⟩ * b j.1 ⟨q.val, by have := q.isLt; omega⟩ +
                 c j.1 ⟨r + p.val, by have := p.isLt; omega⟩ * e j.1 ⟨q.val, by have := q.isLt; omega⟩) * y q =
          (a j.1 ⟨r + p.val, by have := p.isLt; omega⟩ * x p) * (b j.1 ⟨q.val, by have := q.isLt; omega⟩ * y q) +
          (c j.1 ⟨r + p.val, by have := p.isLt; omega⟩ * x p) * (e j.1 ⟨q.val, by have := q.isLt; omega⟩ * y q) := by
        intro p q; ring
      simp_rw [hfac, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
        hx1, hx2, zero_mul, add_zero]
    · simp only [dotE, G, rk2Mat]
      have hfac : ∀ p q : Fin r,
          x p * (a j.1 ⟨r + p.val, by have := p.isLt; omega⟩ * b j.1 ⟨r + q.val, by have := q.isLt; omega⟩ +
                 c j.1 ⟨r + p.val, by have := p.isLt; omega⟩ * e j.1 ⟨r + q.val, by have := q.isLt; omega⟩) * y q =
          (a j.1 ⟨r + p.val, by have := p.isLt; omega⟩ * x p) * (b j.1 ⟨r + q.val, by have := q.isLt; omega⟩ * y q) +
          (c j.1 ⟨r + p.val, by have := p.isLt; omega⟩ * x p) * (e j.1 ⟨r + q.val, by have := q.isLt; omega⟩ * y q) := by
        intro p q; ring
      simp_rw [hfac, Finset.sum_add_distrib, ← Finset.mul_sum, hy1, hy2, mul_zero,
        Finset.sum_const_zero, add_zero]
  have hGl_vw_zero : ∀ l : Fin m, dotB hr (G l) v w = 0 := by
    intro l
    have hml := hJ_span l
    rw [Submodule.mem_span_range_iff_exists_fun] at hml
    obtain ⟨coeff, hcoeff⟩ := hml
    let Mcorr := ∑ j : J, coeff j • G j.1
    let W := G l + Mcorr
    have hW_mem : W ∈ W0Sub d r hr := by
      have hq : qMap W = 0 := by
        simp only [W, Mcorr, map_add, map_sum, map_smul]
        rw [hcoeff]
        have hchar : ∀ z : Matrix (Fin d) (Fin d) F2 ⧸ W0Sub d r hr, z + z = 0 := fun z => by
          have : (1 + 1 : F2) • z = 0 := by
            have h2 : (1 + 1 : F2) = 0 := rfl; rw [h2, zero_smul]
          rwa [add_smul, one_smul] at this
        exact hchar _
      exact (Submodule.Quotient.mk_eq_zero (W0Sub d r hr)).mp hq
    have hcorr_zero : ∀ x ∈ LinearMap.ker Λ, ∀ y ∈ LinearMap.ker Λ,
        dotB hr Mcorr x y = 0 ∧ dotC hr Mcorr x y = 0 ∧ dotE hr Mcorr x y = 0 := by
      intro x hx y hy
      refine ⟨?_, ?_, ?_⟩
      · rw [dotB_sum]; exact Finset.sum_eq_zero fun j _ => by rw [(hGj_zero j x hx y hy).1, mul_zero]
      · rw [dotC_sum]; exact Finset.sum_eq_zero fun j _ => by rw [(hGj_zero j x hx y hy).2.1, mul_zero]
      · rw [dotE_sum]; exact Finset.sum_eq_zero fun j _ => by rw [(hGj_zero j x hx y hy).2.2, mul_zero]
    have hG_eq_W : ∀ x ∈ LinearMap.ker Λ, ∀ y ∈ LinearMap.ker Λ,
        dotB hr (G l) x y = dotB hr W x y ∧
        dotC hr (G l) x y = dotC hr W x y ∧
        dotE hr (G l) x y = dotE hr W x y := by
      intro x hx y hy
      obtain ⟨hb, hc, he⟩ := hcorr_zero x hx y hy
      exact ⟨by simp [W, dotB_add, hb], by simp [W, dotC_add, hc], by simp [W, dotE_add, he]⟩
    obtain ⟨hW_E0, hW_CeqB, hW_Bsym, hW_Bdiag⟩ := dot_W0_props hr hW_mem
    by_contra hne0
    have h1 : dotB hr (G l) v w = 1 := zmod2_eq_one_of_ne_zero hne0
    have hW1 : dotB hr W v w = 1 := by rw [← (hG_eq_W v hv_ker w hw_ker).1]; exact h1
    let α1 : Fin 4 → F2
      | ⟨0, _⟩ => ∑ p : Fin r, v p * a l ⟨p.val, by have := p.isLt; omega⟩
      | ⟨1, _⟩ => ∑ p : Fin r, w p * a l ⟨p.val, by have := p.isLt; omega⟩
      | ⟨2, _⟩ => ∑ p : Fin r, v p * a l ⟨r + p.val, by have := p.isLt; omega⟩
      | ⟨3, _⟩ => ∑ p : Fin r, w p * a l ⟨r + p.val, by have := p.isLt; omega⟩
    let α2 : Fin 4 → F2
      | ⟨0, _⟩ => ∑ p : Fin r, v p * c l ⟨p.val, by have := p.isLt; omega⟩
      | ⟨1, _⟩ => ∑ p : Fin r, w p * c l ⟨p.val, by have := p.isLt; omega⟩
      | ⟨2, _⟩ => ∑ p : Fin r, v p * c l ⟨r + p.val, by have := p.isLt; omega⟩
      | ⟨3, _⟩ => ∑ p : Fin r, w p * c l ⟨r + p.val, by have := p.isLt; omega⟩
    let β1 : Fin 4 → F2
      | ⟨0, _⟩ => ∑ q : Fin r, b l ⟨q.val, by have := q.isLt; omega⟩ * v q
      | ⟨1, _⟩ => ∑ q : Fin r, b l ⟨q.val, by have := q.isLt; omega⟩ * w q
      | ⟨2, _⟩ => ∑ q : Fin r, b l ⟨r + q.val, by have := q.isLt; omega⟩ * v q
      | ⟨3, _⟩ => ∑ q : Fin r, b l ⟨r + q.val, by have := q.isLt; omega⟩ * w q
    let β2 : Fin 4 → F2
      | ⟨0, _⟩ => ∑ q : Fin r, e l ⟨q.val, by have := q.isLt; omega⟩ * v q
      | ⟨1, _⟩ => ∑ q : Fin r, e l ⟨q.val, by have := q.isLt; omega⟩ * w q
      | ⟨2, _⟩ => ∑ q : Fin r, e l ⟨r + q.val, by have := q.isLt; omega⟩ * v q
      | ⟨3, _⟩ => ∑ q : Fin r, e l ⟨r + q.val, by have := q.isLt; omega⟩ * w q
    have hfacB : ∀ x y : Fin r → F2,
        (∑ p : Fin r, x p * a l ⟨p.val, by have := p.isLt; omega⟩) *
          (∑ q : Fin r, b l ⟨r + q.val, by have := q.isLt; omega⟩ * y q) +
        (∑ p : Fin r, x p * c l ⟨p.val, by have := p.isLt; omega⟩) *
          (∑ q : Fin r, e l ⟨r + q.val, by have := q.isLt; omega⟩ * y q) =
        dotB hr (G l) x y := by
      intro x y; simp only [dotB, G, rk2Mat]
      rw [Finset.sum_mul, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro p _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro q _
      ring
    have hfacC : ∀ x y : Fin r → F2,
        (∑ p : Fin r, x p * a l ⟨r + p.val, by have := p.isLt; omega⟩) *
          (∑ q : Fin r, b l ⟨q.val, by have := q.isLt; omega⟩ * y q) +
        (∑ p : Fin r, x p * c l ⟨r + p.val, by have := p.isLt; omega⟩) *
          (∑ q : Fin r, e l ⟨q.val, by have := q.isLt; omega⟩ * y q) =
        dotC hr (G l) x y := by
      intro x y; simp only [dotC, G, rk2Mat]
      rw [Finset.sum_mul, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro p _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro q _
      ring
    have hfacE : ∀ x y : Fin r → F2,
        (∑ p : Fin r, x p * a l ⟨r + p.val, by have := p.isLt; omega⟩) *
          (∑ q : Fin r, b l ⟨r + q.val, by have := q.isLt; omega⟩ * y q) +
        (∑ p : Fin r, x p * c l ⟨r + p.val, by have := p.isLt; omega⟩) *
          (∑ q : Fin r, e l ⟨r + q.val, by have := q.isLt; omega⟩ * y q) =
        dotE hr (G l) x y := by
      intro x y; simp only [dotE, G, rk2Mat]
      rw [Finset.sum_mul, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro p _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro q _
      ring
    refine no_rank2_four α1 α2 β1 β2 ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · change _ = 0; rw [hfacC v v, (hG_eq_W v hv_ker v hv_ker).2.1, hW_CeqB, hW_Bdiag]
    · change _ = 1; rw [hfacC v w, (hG_eq_W v hv_ker w hw_ker).2.1, hW_CeqB, hW1]
    · change _ = 0; rw [hfacE v v, (hG_eq_W v hv_ker v hv_ker).2.2, hW_E0]
    · change _ = 1; rw [hfacC w v, (hG_eq_W w hw_ker v hv_ker).2.1, hW_CeqB, hW_Bsym, hW1]
    · change _ = 0; rw [hfacC w w, (hG_eq_W w hw_ker w hw_ker).2.1, hW_CeqB, hW_Bdiag]
    · change _ = 0; rw [hfacE w v, (hG_eq_W w hw_ker v hv_ker).2.2, hW_E0]
    · change _ = 1; rw [hfacB w v, (hG_eq_W w hw_ker v hv_ker).1, hW_Bsym, hW1]
  have hex_pair : ∃ p : PairIdx r, v p.1.1 * w p.1.2 + v p.1.2 * w p.1.1 = 1 := by
    by_contra hnone
    push_neg at hnone
    have hall : ∀ i j : Fin r, v i * w j = v j * w i := by
      intro i j
      rcases lt_trichotomy i j with hlt | rfl | hgt
      · have h0 : v i * w j + v j * w i = 0 :=
          zmod2_eq_zero_of_ne_one (hnone ⟨(i, j), hlt⟩)
        exact zmod2_eq_of_add_eq_zero h0
      · rfl
      · have h0 : v j * w i + v i * w j = 0 :=
          zmod2_eq_zero_of_ne_one (hnone ⟨(j, i), hgt⟩)
        exact (zmod2_eq_of_add_eq_zero h0).symm
    have hv_ex : ∃ i : Fin r, v i = 1 := by
      by_contra h0; push_neg at h0
      apply hv_ne0; funext i
      exact zmod2_eq_zero_of_ne_one (h0 i)
    obtain ⟨i0, hi0⟩ := hv_ex
    rcases zmod2_eq_zero_or_one (w i0) with hwi0 | hwi0
    · apply hw_ne0; funext j
      have h := hall i0 j; rw [hi0, hwi0, one_mul, mul_zero] at h; exact h
    · apply hvw_ne; funext j
      have h := hall i0 j; rw [hi0, hwi0, one_mul, mul_one] at h; exact h.symm
  obtain ⟨p0, hp0⟩ := hex_pair
  let MK : Matrix (Fin d) (Fin d) F2 := W0Recon hr (Pi.single (Sum.inr (Sum.inl p0)) 1)
  have hMK_mem : MK ∈ Submodule.span F2 (Set.range G) := hW0 (W0Recon_mem hr _)
  rw [Submodule.mem_span_range_iff_exists_fun] at hMK_mem
  obtain ⟨coeff, hcoeff⟩ := hMK_mem
  have hdot_zero : dotB hr MK v w = 0 := by
    rw [← hcoeff, dotB_sum]
    exact Finset.sum_eq_zero fun l _ => by rw [hGl_vw_zero l, mul_zero]
  have hdot_one : dotB hr MK v w = 1 := by
    simp only [dotB, MK]
    have hMK_entry : ∀ p q : Fin r,
        W0Recon hr (Pi.single (Sum.inr (Sum.inl p0)) 1)
          ⟨p.val, by have := p.isLt; omega⟩ ⟨r + q.val, by have := q.isLt; omega⟩ =
        (if p = p0.1.1 ∧ q = p0.1.2 then 1 else 0) + (if p = p0.1.2 ∧ q = p0.1.1 then 1 else 0) := by
      intro p q
      rw [W0Recon_AB hr _ p.isLt (by dsimp; omega) (by dsimp; have := q.isLt; omega)]
      simp only [Nat.add_sub_cancel_left]
      have hmul : ∀ (P Q : Prop) [Decidable P] [Decidable Q],
          (if P then (1 : F2) else 0) * (if Q then 1 else 0) = if P ∧ Q then 1 else 0 := by
        intro P Q _ _; by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]
      exact (single_K_entry (d := d) p0 p q).trans (by rw [hmul, hmul])
    simp_rw [hMK_entry, mul_add, add_mul, Finset.sum_add_distrib]
    have hterm : ∀ (a0 b0 : Fin r),
        ∑ p : Fin r, ∑ q : Fin r, v p * (if p = a0 ∧ q = b0 then (1 : F2) else 0) * w q =
          v a0 * w b0 := by
      intro a0 b0
      rw [Finset.sum_eq_single a0]
      · rw [Finset.sum_eq_single b0]
        · simp
        · intro q _ hq; simp [hq]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro p _ hp
        apply Finset.sum_eq_zero; intro q _; simp [hp]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hterm p0.1.1 p0.1.2, hterm p0.1.2 p0.1.1]
    exact hp0
  rw [hdot_zero] at hdot_one
  exact zero_ne_one hdot_one

lemma W0_lower_bound {d r m : ℕ} (hr : 2 * r ≤ d)
    (a b c e : Fin m → Fin d → F2)
    (hW0 : W0Sub d r hr ≤
      Submodule.span F2 (Set.range fun l : Fin m => rk2Mat (a l) (b l) (c l) (e l))) :
    r * (d - r - 1) ≤ m ∧ r ≤ 4 * (m - r * (d - r - 1)) + 1 := by
  classical
  let G : Fin m → Matrix (Fin d) (Fin d) F2 := fun l => rk2Mat (a l) (b l) (c l) (e l)
  let Usub : Submodule F2 (Matrix (Fin d) (Fin d) F2) := Submodule.span F2 (Set.range G)
  let L : (Fin m → F2) →ₗ[F2] Matrix (Fin d) (Fin d) F2 :=
    { toFun := fun x => ∑ l : Fin m, x l • G l
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun k x => by simp [Finset.smul_sum, smul_smul] }
  have hU_eq_range : Usub = LinearMap.range L := by
    ext M
    simp only [Usub, LinearMap.mem_range, L, LinearMap.coe_mk, AddHom.coe_mk]
    exact Submodule.mem_span_range_iff_exists_fun F2
  have hfinU : Module.finrank F2 Usub ≤ m := by
    rw [hU_eq_range]
    calc Module.finrank F2 (LinearMap.range L)
        ≤ Module.finrank F2 (Fin m → F2) := LinearMap.finrank_range_le L
      _ = m := Module.finrank_fin_fun F2
  have hD_le_U : r * (d - r - 1) ≤ Module.finrank F2 Usub := by
    rw [← finrank_W0Sub hr]
    exact Submodule.finrank_mono hW0
  have hD_le_m : r * (d - r - 1) ≤ m := le_trans hD_le_U hfinU
  refine ⟨hD_le_m, ?_⟩
  let qMap := (W0Sub d r hr).mkQ
  obtain ⟨J, hJ_li, hJ_span⟩ := exists_minimal_span_subset (fun l : Fin m => qMap (G l))
  have hJ_card : J.card ≤ m - r * (d - r - 1) := by
    let qU := qMap.domRestrict Usub
    have hker_eq : LinearMap.ker qU = (W0Sub d r hr).comap Usub.subtype := by
      ext ⟨M, hM⟩
      simp [qU, qMap, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    have hker_fr : Module.finrank F2 (LinearMap.ker qU) = r * (d - r - 1) := by
      rw [hker_eq]
      have hmap : ((W0Sub d r hr).comap Usub.subtype).map Usub.subtype = W0Sub d r hr := by
        ext M
        simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
        constructor
        · rintro ⟨⟨x, _⟩, hx, rfl⟩; exact hx
        · intro hx; exact ⟨⟨M, hW0 hx⟩, hx, rfl⟩
      calc Module.finrank F2 ((W0Sub d r hr).comap Usub.subtype)
          = Module.finrank F2 (((W0Sub d r hr).comap Usub.subtype).map Usub.subtype) :=
            (Submodule.finrank_map_subtype_eq Usub ((W0Sub d r hr).comap Usub.subtype)).symm
        _ = Module.finrank F2 (W0Sub d r hr) := by rw [hmap]
        _ = r * (d - r - 1) := finrank_W0Sub hr
    have hrn := LinearMap.finrank_range_add_finrank_ker qU
    rw [hker_fr] at hrn
    have hrange_le : Module.finrank F2 (LinearMap.range qU) ≤ m - r * (d - r - 1) := by omega
    have hJ_in_range : ∀ j : J, qMap (G j.1) ∈ LinearMap.range qU := fun j =>
      ⟨⟨G j.1, Submodule.subset_span ⟨j.1, rfl⟩⟩, rfl⟩
    let vJ : J → LinearMap.range qU := fun j => ⟨qMap (G j.1), hJ_in_range j⟩
    have hvJ_li : LinearIndependent F2 vJ := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      apply Fintype.linearIndependent_iff.mp hJ_li c
      have := congrArg Subtype.val hc
      simpa [vJ, Submodule.coe_sum, Submodule.coe_smul] using this
    have hcard_le_fr : Fintype.card J ≤ Module.finrank F2 (LinearMap.range qU) :=
      hvJ_li.fintype_card_le_finrank
    rw [Fintype.card_coe] at hcard_le_fr
    exact le_trans hcard_le_fr hrange_le
  let Λ : (Fin r → F2) →ₗ[F2] (J × Fin 4 → F2) :=
    { toFun := fun v p =>
        match p.2 with
        | ⟨0, _⟩ => ∑ i : Fin r, b p.1.1 ⟨r + i.val, by have := i.isLt; omega⟩ * v i
        | ⟨1, _⟩ => ∑ i : Fin r, e p.1.1 ⟨r + i.val, by have := i.isLt; omega⟩ * v i
        | ⟨2, _⟩ => ∑ i : Fin r, a p.1.1 ⟨r + i.val, by have := i.isLt; omega⟩ * v i
        | ⟨3, _⟩ => ∑ i : Fin r, c p.1.1 ⟨r + i.val, by have := i.isLt; omega⟩ * v i
      map_add' := fun u v => by
        funext ⟨j, k⟩
        match k with
        | ⟨0, _⟩ => simp [mul_add, Finset.sum_add_distrib]
        | ⟨1, _⟩ => simp [mul_add, Finset.sum_add_distrib]
        | ⟨2, _⟩ => simp [mul_add, Finset.sum_add_distrib]
        | ⟨3, _⟩ => simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun s v => by
        funext ⟨j, k⟩
        match k with
        | ⟨0, _⟩ => simp [Finset.mul_sum, mul_left_comm]
        | ⟨1, _⟩ => simp [Finset.mul_sum, mul_left_comm]
        | ⟨2, _⟩ => simp [Finset.mul_sum, mul_left_comm]
        | ⟨3, _⟩ => simp [Finset.mul_sum, mul_left_comm] }
  have hrn_Λ : Module.finrank F2 (LinearMap.range Λ) + Module.finrank F2 (LinearMap.ker Λ) = r := by
    simpa [Module.finrank_fin_fun] using LinearMap.finrank_range_add_finrank_ker Λ
  have hrange_Λ : Module.finrank F2 (LinearMap.range Λ) ≤ 4 * J.card := by
    calc Module.finrank F2 (LinearMap.range Λ)
        ≤ Module.finrank F2 (J × Fin 4 → F2) := Submodule.finrank_le (LinearMap.range Λ)
      _ = Fintype.card (J × Fin 4) := Module.finrank_fintype_fun_eq_card F2
      _ = J.card * 4 := by simp
      _ = 4 * J.card := Nat.mul_comm _ _
  have hΛ_ker : ∀ x ∈ LinearMap.ker Λ, ∀ j : J,
      (∑ i : Fin r, b j.1 ⟨r + i.val, by have := i.isLt; omega⟩ * x i = 0) ∧
      (∑ i : Fin r, e j.1 ⟨r + i.val, by have := i.isLt; omega⟩ * x i = 0) ∧
      (∑ i : Fin r, a j.1 ⟨r + i.val, by have := i.isLt; omega⟩ * x i = 0) ∧
      (∑ i : Fin r, c j.1 ⟨r + i.val, by have := i.isLt; omega⟩ * x i = 0) := by
    intro x hx j
    rw [LinearMap.mem_ker] at hx
    exact ⟨congrFun hx (j, 0), congrFun hx (j, 1), congrFun hx (j, 2), congrFun hx (j, 3)⟩
  have hker_le_one : Module.finrank F2 (LinearMap.ker Λ) ≤ 1 :=
    ker_Λ_finrank_le_one hr a b c e hW0 J hJ_span Λ hΛ_ker
  omega

-- ============================================================================
-- Part 8: Assembly of the Main Theorem
-- ============================================================================

theorem main_proof (d : ℕ) (U : Matrix (Fin d) (Fin d) F2) (hU : U * U = 1) :
    let r := (U - 1).rank
    let D := r * (d - r - 1)
    Bank d U (D + min (Nat.choose r 2) r) ∧
      ∀ t : ℕ, Bank d U t → D ≤ t ∧ r ≤ 4 * (t - D) + 1 := by
  intro r D
  obtain ⟨hr, P, Q, hPQ, hQP, hQUP⟩ := exists_adapted_coords U hU
  have hU_eq : U = P * U0 d r * Q := by
    calc U = 1 * U * 1 := by rw [Matrix.one_mul, Matrix.mul_one]
      _ = (P * Q) * U * (P * Q) := by rw [hPQ]
      _ = P * (Q * U * P) * Q := by simp only [Matrix.mul_assoc]
      _ = P * U0 d r * Q := by rw [hQUP]
  have hQP_T : Q.transpose * P.transpose = 1 := by
    rw [← Matrix.transpose_mul, hPQ, Matrix.transpose_one]
  have hPQ_T : P.transpose * Q.transpose = 1 := by
    rw [← Matrix.transpose_mul, hQP, Matrix.transpose_one]
  have hcong_eq : ∀ H : Matrix (Fin d) (Fin d) F2,
      U * H * U.transpose + H =
        P * (U0 d r * (Q * H * Q.transpose) * (U0 d r).transpose + (Q * H * Q.transpose)) *
          P.transpose := by
    intro H
    have h1 : P * (U0 d r * (Q * H * Q.transpose) * (U0 d r).transpose) * P.transpose =
        U * H * U.transpose := by
      rw [hU_eq, Matrix.transpose_mul, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    have h2 : P * (Q * H * Q.transpose) * P.transpose = H := by
      calc P * (Q * H * Q.transpose) * P.transpose
          = (P * Q) * H * (Q.transpose * P.transpose) := by simp only [Matrix.mul_assoc]
        _ = 1 * H * 1 := by rw [hPQ, hQP_T]
        _ = H := by rw [Matrix.one_mul, Matrix.mul_one]
    rw [Matrix.mul_add, Matrix.add_mul, h1, h2]
  constructor
  · -- Upper bound
    obtain ⟨m, a, b, c, e, hm, hW0_span⟩ := W0_upper_span hr
    refine rk2_span_to_bank m (le_of_eq hm)
      (fun l => P.mulVec (a l)) (fun l => P.mulVec (b l))
      (fun l => P.mulVec (c l)) (fun l => P.mulVec (e l)) ?_
    intro H hH
    have hH'_alt : IsAlt (Q * H * Q.transpose) := isAlt_cong Q H hH
    have hM'_mem : U0 d r * (Q * H * Q.transpose) * (U0 d r).transpose + (Q * H * Q.transpose) ∈
        W0Sub d r hr :=
      (mem_W0Sub_iff_exists_alt hr _).mpr ⟨Q * H * Q.transpose, hH'_alt, rfl⟩
    have hM'_span := hW0_span hM'_mem
    rw [Submodule.mem_span_range_iff_exists_fun] at hM'_span ⊢
    obtain ⟨coeff, hcoeff⟩ := hM'_span
    refine ⟨coeff, ?_⟩
    rw [hcong_eq H, ← hcoeff]
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
    apply Finset.sum_congr rfl; intro l _
    congr 1
    exact (rk2Mat_cong P (a l) (b l) (c l) (e l)).symm
  · -- Lower bound
    intro t hb
    obtain ⟨m, a, b, c, e, hm, hspan⟩ := bank_to_rk2_span hb
    have hW0_span : W0Sub d r hr ≤
        Submodule.span F2 (Set.range fun l : Fin m =>
          rk2Mat (Q.mulVec (a l)) (Q.mulVec (b l)) (Q.mulVec (c l)) (Q.mulVec (e l))) := by
      intro M hM
      obtain ⟨H0, hH0_alt, hH0_eq⟩ := (mem_W0Sub_iff_exists_alt hr M).mp hM
      let H := P * H0 * P.transpose
      have hH_alt : IsAlt H := isAlt_cong P H0 hH0_alt
      have hQH : Q * H * Q.transpose = H0 := by
        calc Q * (P * H0 * P.transpose) * Q.transpose
            = (Q * P) * H0 * (P.transpose * Q.transpose) := by simp only [Matrix.mul_assoc]
          _ = 1 * H0 * 1 := by rw [hQP, hPQ_T]
          _ = H0 := by rw [Matrix.one_mul, Matrix.mul_one]
      have hM_eq : Q * (U * H * U.transpose + H) * Q.transpose = M := by
        rw [hcong_eq H, hQH, hH0_eq]
        calc Q * (P * M * P.transpose) * Q.transpose
            = (Q * P) * M * (P.transpose * Q.transpose) := by simp only [Matrix.mul_assoc]
          _ = 1 * M * 1 := by rw [hQP, hPQ_T]
          _ = M := by rw [Matrix.one_mul, Matrix.mul_one]
      have hU_span := hspan H hH_alt
      rw [Submodule.mem_span_range_iff_exists_fun] at hU_span ⊢
      obtain ⟨coeff, hcoeff⟩ := hU_span
      refine ⟨coeff, ?_⟩
      rw [← hM_eq, ← hcoeff]
      simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
      apply Finset.sum_congr rfl; intro l _
      congr 1
      exact (rk2Mat_cong Q (a l) (b l) (c l) (e l)).symm
    obtain ⟨hD_le_m, hr_le⟩ := W0_lower_bound hr
      (fun l => Q.mulVec (a l)) (fun l => Q.mulVec (b l))
      (fun l => Q.mulVec (c l)) (fun l => Q.mulVec (e l)) hW0_span
    refine ⟨le_trans hD_le_m hm, ?_⟩
    dsimp only [D, r] at *
    omega

end PEqualNP.Outside.L_meta_32571

theorem PEqualNP.Outside.L_meta_32571 :
    let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)
let F := ZMod 2
∀ (d : ℕ) (U : Matrix (Fin d) (Fin d) F), U*U = 1 →
  let Mat := Matrix (Fin d) (Fin d) F
  let alt := fun (H : Mat) => H.transpose = H ∧ ∀ i, H i i = 0
  let r := (U-1).rank
  let table := fun (H : Mat) (x y : Fin (d+1)) =>
    Fin.cases false (fun i => Fin.cases false (fun j => decide (H i j ≠ 0)) y) x
  let D := r*(d-r-1)
  let bank := fun (t : ℕ) =>
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Mat → ℕ),
      PEqualNP.MetaComplexity.NestedCover.ReadsBack ((d+1)+(d+1)) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
      ∀ H : Mat, alt H →
        (depths ((d+1)+(d+1)) C).getD (tap H) 0 ≤ 1 ∧
        PEqualNP.Represents.Represents (table (U*H*U.transpose + H)) ⟨C.gates, tap H⟩
  bank (D + min (Nat.choose r 2) r) ∧
    ∀ t : ℕ, bank t → D ≤ t ∧ r ≤ 4*(t-D)+1 := by
  intro nonlinear depths F d U hU Mat alt r table D bank
  exact PEqualNP.Outside.L_meta_32571.main_proof d U hU
