import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25930

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (x : List Bool) : List Bool := gs.foldl step x

theorem W_append (gs hs : List Gate) (x : List Bool) : W (gs ++ hs) x = W hs (W gs x) := by
  simp [W, List.foldl_append]

theorem W_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    W (g :: gs) x = W gs (step x g) := rfl

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

theorem getD_app (l l' : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem W_len (gs : List Gate) : ∀ x : List Bool, (W gs x).length = x.length + gs.length := by
  induction gs with
  | nil => intro x; simp [W]
  | cons g gs ih => intro x; rw [W_cons, ih]; simp [step]; omega

theorem W_pre (gs : List Gate) : ∀ (x : List Bool) (i : ℕ), i < x.length →
    (W gs x).getD i false = x.getD i false := by
  induction gs with
  | nil => intro x i _; rfl
  | cons g gs ih =>
    intro x i hi
    rw [W_cons, ih _ _ (by simp [step]; omega)]
    exact getD_app _ _ _ hi

theorem W_gate (gs : List Gate) (x : List Bool) (N : ℕ) (hN : x.length = N) (j : ℕ)
    (hj : j < gs.length) :
    (W gs x).getD (N + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < N + j then (W gs x).getD i false else false) := by
  have hsplit : gs = gs.take j ++ (gs[j] :: gs.drop (j + 1)) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hylen : (W (gs.take j) x).length = N + j := by
    rw [W_len, List.length_take]; omega
  have key : W gs x = W (gs.drop (j + 1)) (step (W (gs.take j) x) gs[j]) := by
    conv_lhs => rw [hsplit]
    rw [W_append, W_cons]
  have hsl : (step (W (gs.take j) x) gs[j]).length = N + j + 1 := by
    simp [step, hylen]
  have h0 : (W gs x).getD (N + j) false = (step (W (gs.take j) x) gs[j]).getD (N + j) false := by
    rw [key, W_pre _ _ _ (by omega)]
  have hval : ∀ i, i < N + j → (W gs x).getD i false = (W (gs.take j) x).getD i false := by
    intro i hi
    rw [key, W_pre _ _ _ (by omega)]
    unfold step
    exact getD_app _ _ _ (by omega)
  have e1 : (step (W (gs.take j) x) gs[j]).getD (N + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (W (gs.take j) x).getD i false) := by
    rw [step, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    simp [hylen]
  rw [h0, e1]
  congr 1
  apply List.map_congr_left
  intro i _
  split_ifs with h
  · exact (hval i h).symm
  · exact getD_ge _ _ (by omega)

def isNot : GateOp → Bool
  | GateOp.not => true
  | _ => false

theorem isNot_iff (o : GateOp) : isNot o = true ↔ o = GateOp.not := by
  cases o <;> simp [isNot]

def rd (g : Gate) (w : ℕ) : Finset ℕ :=
  if isNot g.op then (g.inputs.take 1).toFinset.filter (· < w)
  else g.inputs.toFinset.filter (· < w)

theorem rd_lt (g : Gate) (w i : ℕ) (h : i ∈ rd g w) : i < w := by
  unfold rd at h
  split_ifs at h <;> simp_all

theorem gate_congr (g : Gate) (w : ℕ) (f1 f2 : ℕ → Bool) (h : ∀ i ∈ rd g w, f1 i = f2 i) :
    g.op.eval (g.inputs.map fun i => if i < w then f1 i else false) =
    g.op.eval (g.inputs.map fun i => if i < w then f2 i else false) := by
  by_cases hn : isNot g.op = true
  · have hop := (isNot_iff _).mp hn
    rw [hop]
    simp only [GateOp.eval]
    cases hl : g.inputs with
    | nil => simp
    | cons i rest =>
      simp only [List.map_cons, List.headD_cons]
      by_cases hi : i < w
      · simp only [hi, if_true]
        rw [h i (by simp [rd, hn, hl, hi])]
      · simp [hi]
  · congr 1
    apply List.map_congr_left
    intro i hi
    split_ifs with hw
    · exact h i (by simp [rd, hn, hi, hw])
    · rfl

def Reach (gs : List Gate) (N out : ℕ) (w : ℕ) : Prop :=
  ∀ S : Set ℕ, out ∈ S →
    (∀ (j : ℕ) (hj : j < gs.length), N + j ∈ S → ∀ i ∈ rd gs[j] (N + j), i ∈ S) → w ∈ S

theorem Reach.base {gs : List Gate} {N out : ℕ} : Reach gs N out out := fun _ h _ => h

theorem Reach.step {gs : List Gate} {N out : ℕ} (j i : ℕ) (hj : j < gs.length)
    (hr : Reach gs N out (N + j)) (hm : i ∈ rd gs[j] (N + j)) : Reach gs N out i :=
  fun S h0 h1 => h1 j hj (hr S h0 h1) i hm

theorem reach_cases (gs : List Gate) (N out i : ℕ) (h : Reach gs N out i) :
    i = out ∨ ∃ (j : ℕ) (hj : j < gs.length), Reach gs N out (N + j) ∧ i ∈ rd gs[j] (N + j) := by
  refine h {i | i = out ∨ ∃ (j : ℕ) (hj : j < gs.length), Reach gs N out (N + j) ∧
    i ∈ rd gs[j] (N + j)} (Or.inl rfl) ?_
  intro j hj hS i hi
  refine Or.inr ⟨j, hj, ?_, hi⟩
  rcases hS with hS | ⟨j', hj', hr, hm⟩
  · rw [hS]; exact Reach.base
  · exact Reach.step j' _ hj' hr hm

theorem reach_le (gs : List Gate) (N out i : ℕ) (h : Reach gs N out i) : i ≤ out := by
  refine h {i | i ≤ out} (show out ≤ out from le_refl _) ?_
  intro j hj hS i hi
  have := rd_lt _ _ _ hi
  simp only [Set.mem_setOf_eq] at hS ⊢
  omega

theorem agree (gs1 gs2 : List Gate) (x1 x2 : List Bool) (out N : ℕ)
    (hx1 : x1.length = N) (hx2 : x2.length = N) (hlen : gs1.length = gs2.length)
    (hg : ∀ j (hj : j < gs1.length), Reach gs1 N out (N + j) → gs2[j]'(hlen ▸ hj) = gs1[j])
    (hin : ∀ i, i < N → Reach gs1 N out i → x1.getD i false = x2.getD i false) :
    ∀ w, Reach gs1 N out w → (W gs1 x1).getD w false = (W gs2 x2).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw
  by_cases h1 : w < N
  · rw [W_pre _ _ _ (by omega), W_pre _ _ _ (by omega)]
    exact hin w h1 hw
  · by_cases h2 : w < N + gs1.length
    · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
      have hj : j < gs1.length := by omega
      rw [W_gate gs1 x1 N hx1 j hj, W_gate gs2 x2 N hx2 j (hlen ▸ hj), hg j hj hw]
      apply gate_congr
      intro i hi
      exact ih i (rd_lt _ _ _ hi) (Reach.step j i hj hw hi)
    · rw [getD_ge _ _ (by rw [W_len]; omega), getD_ge _ _ (by rw [W_len]; omega)]

def dg : Gate := ⟨GateOp.and, []⟩

theorem count (gs : List Gate) (N out : ℕ) (hF : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∃ I K : Finset ℕ, (∀ i, i ∈ I ↔ i < N ∧ Reach gs N out i) ∧
      (∀ j, j ∈ K ↔ j < gs.length ∧ Reach gs N out (N + j) ∧ isNot (gs.getD j dg).op = true) ∧
      I.card + K.card ≤ gs.length + 1 := by
  classical
  let U := (Finset.range (out + 1)).filter (Reach gs N out)
  let I := U.filter (· < N)
  let J := (Finset.range gs.length).filter (fun j => Reach gs N out (N + j))
  let K := J.filter (fun j => isNot (gs.getD j dg).op = true)
  let R : ℕ → Finset ℕ := fun j => rd (gs.getD j dg) (N + j)
  have hU : ∀ i, i ∈ U ↔ Reach gs N out i := by
    intro i
    simp only [U, Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨by have := reach_le gs N out i h; omega, h⟩
  refine ⟨I, K, ?_, ?_, ?_⟩
  · intro i
    simp only [I, Finset.mem_filter, hU]
    tauto
  · intro j
    simp only [K, J, Finset.mem_filter, Finset.mem_range]
    tauto
  · have hA : I.card + J.card ≤ U.card := by
      have hd : Disjoint I (J.image (fun j => N + j)) := by
        rw [Finset.disjoint_left]
        intro i hi hi'
        simp only [I, Finset.mem_filter] at hi
        simp only [Finset.mem_image] at hi'
        obtain ⟨j, _, rfl⟩ := hi'
        omega
      have hs : I ∪ J.image (fun j => N + j) ⊆ U := by
        intro i hi
        rcases Finset.mem_union.mp hi with hi | hi
        · exact (Finset.mem_filter.mp hi).1
        · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
          exact (hU _).mpr (Finset.mem_filter.mp hj).2
      have := Finset.card_le_card hs
      rw [Finset.card_union_of_disjoint hd,
        Finset.card_image_of_injective _ (add_right_injective N)] at this
      exact this
    have hB : U.card ≤ (J.biUnion R).card + 1 := by
      have hs : U ⊆ insert out (J.biUnion R) := by
        intro i hi
        rw [hU] at hi
        rcases reach_cases gs N out i hi with hi | ⟨j, hj, hr, hm⟩
        · rw [hi]; exact Finset.mem_insert_self _ _
        · apply Finset.mem_insert_of_mem
          rw [Finset.mem_biUnion]
          refine ⟨j, ?_, ?_⟩
          · simp only [J, Finset.mem_filter, Finset.mem_range]; exact ⟨hj, hr⟩
          · simp only [R]; rw [List.getD_eq_getElem _ _ hj]; exact hm
      exact (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)
    have hC : (J.biUnion R).card ≤ ∑ j ∈ J, (R j).card := Finset.card_biUnion_le
    have hD : ∀ j ∈ J, (R j).card + (if isNot (gs.getD j dg).op = true then 1 else 0) ≤ 2 := by
      intro j hj
      have hjl : j < gs.length := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      have hmem : gs.getD j dg ∈ gs := by
        rw [List.getD_eq_getElem _ _ hjl]; exact List.getElem_mem hjl
      have hl := hF _ hmem
      simp only [R, rd]
      split_ifs with hn
      · have h1 := Finset.card_filter_le ((List.take 1 (gs.getD j dg).inputs).toFinset) (· < N + j)
        have h2 := List.toFinset_card_le (List.take 1 (gs.getD j dg).inputs)
        have h3 := List.length_take_le 1 (gs.getD j dg).inputs
        omega
      · have h1 := Finset.card_filter_le ((gs.getD j dg).inputs.toFinset) (· < N + j)
        have h2 := List.toFinset_card_le (gs.getD j dg).inputs
        omega
    have hE : ∑ j ∈ J, (R j).card + K.card ≤ 2 * J.card := by
      have hk : K.card = ∑ j ∈ J, (if isNot (gs.getD j dg).op = true then 1 else 0) :=
        Finset.card_filter _ _
      rw [hk, ← Finset.sum_add_distrib]
      calc ∑ j ∈ J, ((R j).card + (if isNot (gs.getD j dg).op = true then 1 else 0))
          ≤ ∑ _j ∈ J, 2 := Finset.sum_le_sum hD
        _ = 2 * J.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hJ : J.card ≤ gs.length := by
      have := Finset.card_filter_le (Finset.range gs.length) (fun j => Reach gs N out (N + j))
      simpa using this
    omega

theorem oneEach_len (n m : ℕ) (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

theorem oneEach_getD (n m : ℕ) (u : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach u v).getD i false = (decide (i = u.val) || decide (i = n + v.val)) := by
  unfold oneEach
  by_cases h : i < n
  · rw [getD_app _ _ _ (by simpa using h), List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    have hv : i ≠ n + v.val := by omega
    simp [h, Fin.ext_iff, hv]
  · have hu : i ≠ u.val := by have := u.isLt; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn, List.getElem?_ofFn]
    by_cases h2 : i - n < m
    · have e : (i - n = v.val) ↔ (i = n + v.val) := by omega
      simp [h2, Fin.ext_iff, hu, e]
    · have hv : i ≠ n + v.val := by have := v.isLt; omega
      simp [h2, hu, hv]

def fix (g : Gate) : Gate := if isNot g.op then ⟨GateOp.and, g.inputs⟩ else g

end PEqualNP.Outside.L_meta_25930

open PEqualNP.Outside.L_meta_25930 in
theorem PEqualNP.Outside.L_meta_25930 : ∀ (n m a b s : ℕ) (G : Fin n → Fin m → Bool),
  (∃ (r t : Fin n) (c u : Fin m), G r c ≠ G t u) →
  (∀ r : Fin n, (Finset.univ.filter (fun t : Fin n => ∀ c : Fin m, G t c = G r c)).card ≤ a) →
  (∀ c : Fin m, (Finset.univ.filter (fun u : Fin m => ∀ r : Fin n, G r u = G r c)).card ≤ b) →
  s + a + b < n + m →
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
    C.size ≤ s ∧ PEqualNP.Represents.Represents G C) →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
    D.size ≤ s ∧ PEqualNP.Represents.Represents G D := by
  intro n m a b s G _ hrow hcol hs hC
  classical
  obtain ⟨C, hF, hsize, hrep⟩ := hC
  obtain ⟨I, K, hI, hK, hcount⟩ := count C.gates (n + m) C.output
    (fun g hg => (hF g hg).2)
  have key : ∀ x y : List Bool, x.length = n + m → y.length = n + m →
      (∀ i ∈ I, x.getD i false = y.getD i false) → C.eval x = C.eval y := by
    intro x y hx hy hxy
    exact agree C.gates C.gates x y C.output (n + m) hx hy rfl (fun _ _ _ => rfl)
      (fun i hi hr => hxy i ((hI i).mpr ⟨hi, hr⟩)) C.output Reach.base
  -- unread rows
  have hR : (Finset.univ.filter (fun r : Fin n => r.val ∉ I)).card ≤ a := by
    by_cases hne : (Finset.univ.filter (fun r : Fin n => r.val ∉ I)).Nonempty
    · obtain ⟨r0, hr0⟩ := hne
      refine le_trans (Finset.card_le_card ?_) (hrow r0)
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht hr0 ⊢
      intro c
      rw [← hrep, ← hrep]
      apply key _ _ (oneEach_len _ _ _ _) (oneEach_len _ _ _ _)
      intro i hi
      rw [oneEach_getD, oneEach_getD]
      have h1 : i ≠ t.val := fun h => ht (h ▸ hi)
      have h2 : i ≠ r0.val := fun h => hr0 (h ▸ hi)
      simp [h1, h2]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp
  have hCo : (Finset.univ.filter (fun c : Fin m => n + c.val ∉ I)).card ≤ b := by
    by_cases hne : (Finset.univ.filter (fun c : Fin m => n + c.val ∉ I)).Nonempty
    · obtain ⟨c0, hc0⟩ := hne
      refine le_trans (Finset.card_le_card ?_) (hcol c0)
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hc0 ⊢
      intro r
      rw [← hrep, ← hrep]
      apply key _ _ (oneEach_len _ _ _ _) (oneEach_len _ _ _ _)
      intro i hi
      rw [oneEach_getD, oneEach_getD]
      have h1 : i ≠ n + u.val := fun h => hu (h ▸ hi)
      have h2 : i ≠ n + c0.val := fun h => hc0 (h ▸ hi)
      simp [h1, h2]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp
  have hread : (Finset.univ.filter (fun r : Fin n => r.val ∈ I)).card +
      (Finset.univ.filter (fun c : Fin m => n + c.val ∈ I)).card ≤ I.card := by
    let A1 := (Finset.univ.filter (fun r : Fin n => r.val ∈ I)).image (fun r => r.val)
    let A2 := (Finset.univ.filter (fun c : Fin m => n + c.val ∈ I)).image (fun c => n + c.val)
    have hd : Disjoint A1 A2 := by
      rw [Finset.disjoint_left]
      intro i hi hi'
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hi'
      have := r.isLt
      omega
    have hsub : A1 ∪ A2 ⊆ I := by
      intro i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hi
        exact (Finset.mem_filter.mp hr).2
      · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hi
        exact (Finset.mem_filter.mp hc).2
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ Fin.val_injective,
      Finset.card_image_of_injective _ (fun c1 c2 h => Fin.ext (by simpa using h))] at this
    exact this
  have hn1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (p := fun r : Fin n => r.val ∈ I)
  have hm1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
    (p := fun c : Fin m => n + c.val ∈ I)
  simp only [Finset.card_univ, Fintype.card_fin] at hn1 hm1
  have hsz : C.gates.length ≤ s := hsize
  have hK0 : K.card = 0 := by omega
  have hnot : ∀ j (hj : j < C.gates.length), Reach C.gates (n + m) C.output (n + m + j) →
      isNot (C.gates[j]).op = false := by
    intro j hj hr
    cases h : isNot (C.gates[j]).op
    · rfl
    · exfalso
      have hmem : j ∈ K := (hK j).mpr ⟨hj, hr, by rw [List.getD_eq_getElem _ _ hj]; exact h⟩
      rw [Finset.card_eq_zero.mp hK0] at hmem
      simp at hmem
  refine ⟨⟨C.gates.map fix, C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    obtain ⟨hop, hl⟩ := hF g0 hg0
    unfold fix
    by_cases hn : isNot g0.op = true
    · rw [if_pos hn]; exact ⟨by simp, hl⟩
    · rw [if_neg hn]
      refine ⟨?_, hl⟩
      have : g0.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not := fun h => hn ((isNot_iff _).mpr h)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
      rcases hop with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h this
  · show (C.gates.map fix).length ≤ s
    rw [List.length_map]; exact hsz
  · intro u v
    rw [← hrep u v]
    show (W (C.gates.map fix) (PEqualNP.Represents.oneEach u v)).getD C.output false =
      (W C.gates (PEqualNP.Represents.oneEach u v)).getD C.output false
    symm
    refine agree C.gates (C.gates.map fix) _ _ C.output (n + m) (oneEach_len _ _ _ _)
      (oneEach_len _ _ _ _) (by simp) ?_ (fun _ _ _ => rfl) C.output Reach.base
    intro j hj hr
    rw [List.getElem_map]
    unfold fix
    rw [if_neg (by rw [hnot j hj hr]; simp)]
