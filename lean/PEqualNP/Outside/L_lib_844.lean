import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_844_aux

open PEqualNP.CircuitLowerBounds

abbrev F := ZMod 2

def bv (b : Bool) : F := if b then 1 else 0

@[simp] theorem bv_true : bv true = 1 := rfl
@[simp] theorem bv_false : bv false = 0 := rfl
theorem bv_not (b : Bool) : bv (!b) = 1 + bv b := by cases b <;> decide
theorem bv_xor (a b : Bool) : bv (Bool.xor a b) = bv a + bv b := by cases a <;> cases b <;> decide
theorem bv_and (a b : Bool) : bv (a && b) = bv a * bv b := by cases a <;> cases b <;> decide
theorem bv_or (a b : Bool) : bv (a || b) = bv a + bv b + bv a * bv b := by
  cases a <;> cases b <;> decide
theorem bv_of_dec (u : F) : bv (decide (u = 1)) = u := by fin_cases u <;> rfl
theorem bv_inj {a b : Bool} (h : bv a = bv b) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem bv_mod_nat (n : ℕ) : bv (decide (n % 2 = 0)) = 1 + (n : F) := by
  rw [← ZMod.natCast_mod n 2]
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h] <;> decide

theorem count_bv (l : List Bool) : ((l.count true : ℕ) : F) = (l.map bv).sum := by
  induction l with
  | nil => simp
  | cons b l ih => cases b <;> simp [List.count_cons, ih] <;> ring

theorem bv_mod2 (l : List Bool) : bv (decide (l.count true % 2 = 0)) = 1 + (l.map bv).sum := by
  rw [bv_mod_nat, count_bv]

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (G : List Gate) (w : List Bool) : List Bool := G.foldl step w

theorem wires_run (C : Circuit) (x : List Bool) : C.wires x = run C.gates x := rfl

theorem run_append (G H : List Gate) (w : List Bool) : run (G ++ H) w = run H (run G w) :=
  List.foldl_append

theorem run_snoc (G : List Gate) (g : Gate) (w : List Bool) :
    run (G ++ [g]) w = step (run G w) g := by
  rw [run_append]; rfl

theorem run_cons (g : Gate) (G : List Gate) (w : List Bool) :
    run (g :: G) w = run G (step w g) := rfl

theorem length_step (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem length_run (G : List Gate) (w : List Bool) : (run G w).length = w.length + G.length := by
  induction G using List.reverseRecOn with
  | nil => rfl
  | append_singleton G g ih => rw [run_snoc, length_step, ih]; simp; omega

theorem getD_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

theorem getD_step_ne (w : List Bool) (g : Gate) (i : ℕ) (h : i ≠ w.length) :
    (step w g).getD i false = w.getD i false := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rw [getD_ge _ _ (by rw [length_step]; omega), getD_ge _ _ (by omega)]

theorem getD_step_self (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [step, List.getD_eq_getElem?_getD]

theorem getD_run_lt (G : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (run G w).getD i false = w.getD i false := by
  induction G using List.reverseRecOn with
  | nil => rfl
  | append_singleton G g ih =>
    rw [run_snoc, getD_step_ne _ _ _ (by rw [length_run]; omega), ih]

theorem getD_run_ne (G : List Gate) (g : Gate) (w : List Bool) (i : ℕ)
    (h : i ≠ w.length + G.length) :
    (run (G ++ [g]) w).getD i false = (run G w).getD i false := by
  rw [run_snoc, getD_step_ne _ _ _ (by rw [length_run]; exact h)]

theorem getD_run_self (G : List Gate) (g : Gate) (w : List Bool) :
    (run (G ++ [g]) w).getD (w.length + G.length) false =
      g.op.eval (g.inputs.map fun i => (run G w).getD i false) := by
  rw [run_snoc, ← length_run, getD_step_self]

def shapeOK (h : Gate) : Prop :=
  h.inputs.length ≤ 2 ∧
    (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1))

def okL (n : ℕ) (G : List Gate) : Prop :=
  ∀ j (hj : j < G.length), shapeOK G[j] ∧ ∀ i ∈ G[j].inputs, i < n + j

theorem okL_nil (n : ℕ) : okL n [] := fun j hj => absurd hj (by simp)

theorem okL_append (n : ℕ) (G H : List Gate) :
    okL n (G ++ H) ↔ okL n G ∧ okL (n + G.length) H := by
  constructor
  · intro h
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · have := h j (by simp; omega)
      rw [List.getElem_append_left hj] at this
      exact this
    · have := h (G.length + j) (by simp; omega)
      rw [List.getElem_append_right (by omega)] at this
      simp only [Nat.add_sub_cancel_left] at this
      refine ⟨this.1, fun i hi => ?_⟩
      have := this.2 i hi; omega
  · rintro ⟨h1, h2⟩ j hj
    by_cases hj' : j < G.length
    · rw [List.getElem_append_left hj']; exact h1 j hj'
    · rw [List.getElem_append_right (by omega)]
      have := h2 (j - G.length) (by simp at hj; omega)
      refine ⟨this.1, fun i hi => ?_⟩
      have := this.2 i hi; omega

theorem okL_single (n : ℕ) (g : Gate) : okL n [g] ↔ shapeOK g ∧ ∀ i ∈ g.inputs, i < n := by
  constructor
  · intro h; have := h 0 (by simp); simpa using this
  · intro h j hj
    have : j = 0 := by simp at hj; omega
    subst this; simpa using h

theorem okL_cons (n : ℕ) (g : Gate) (H : List Gate) :
    okL n (g :: H) ↔ (shapeOK g ∧ ∀ i ∈ g.inputs, i < n) ∧ okL (n + 1) H := by
  rw [show g :: H = [g] ++ H from rfl, okL_append, okL_single]; rfl

theorem legal_iff (n : ℕ) (C : Circuit) :
    (PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
      ∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
        (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1))) ↔
      okL n C.gates := by
  unfold PEqualNP.MetaComplexity.NestedCover.ReadsBack PEqualNP.MetaComplexity.NestedCover.gateAt
  constructor
  · rintro ⟨h1, h2⟩ j hj
    refine ⟨h2 _ (List.getElem_mem hj), fun i hi => ?_⟩
    have := h1 j hj i
    rw [List.getD_eq_getElem _ _ hj] at this
    exact this hi
  · intro h
    refine ⟨fun j hj i hi => ?_, fun g hg => ?_⟩
    · rw [List.getD_eq_getElem _ _ hj] at hi; exact (h j hj).2 i hi
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      exact (h j hj).1

def cnt (h : Gate) : Prop := (h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2

noncomputable def costL (G : List Gate) : ℕ := G.countP (fun h => @decide (cnt h) (Classical.propDecidable _))

theorem costL_append (G H : List Gate) : costL (G ++ H) = costL G + costL H :=
  List.countP_append

theorem costL_nil : costL [] = 0 := rfl

open Classical in
theorem costL_single (g : Gate) : costL [g] = if cnt g then 1 else 0 := by
  classical
  unfold costL
  by_cases h : cnt g <;> simp [h]

open Classical in
theorem costL_cons (g : Gate) (H : List Gate) :
    costL (g :: H) = (if cnt g then 1 else 0) + costL H := by
  classical
  rw [show g :: H = [g] ++ H from rfl, costL_append, costL_single]

def xc : ℕ → List ℕ → ℕ → List Gate
  | _, [], _ => []
  | acc, l :: L, b => ⟨.mod 2, [acc, l]⟩ :: ⟨.not, [b]⟩ :: xc (b + 1) L (b + 2)

def xo : ℕ → List ℕ → ℕ → ℕ
  | acc, [], _ => acc
  | _, _ :: L, b => xo (b + 1) L (b + 2)

theorem xc_length (acc : ℕ) (L : List ℕ) (b : ℕ) : (xc acc L b).length = 2 * L.length := by
  induction L generalizing acc b with
  | nil => rfl
  | cons l L ih => simp [xc, ih]; ring

theorem xc_cost (acc : ℕ) (L : List ℕ) (b : ℕ) : costL (xc acc L b) = 0 := by
  induction L generalizing acc b with
  | nil => rfl
  | cons l L ih => simp [xc, costL_cons, ih, cnt]

theorem xo_lt (acc : ℕ) (L : List ℕ) (b : ℕ) (ha : acc < b) : xo acc L b < b + 2 * L.length := by
  induction L generalizing acc b with
  | nil => simpa [xo] using ha
  | cons l L ih => have := ih (b + 1) (b + 2) (by omega); simp [xo]; omega

theorem xc_ok (acc : ℕ) (L : List ℕ) (b : ℕ) (ha : acc < b) (hL : ∀ l ∈ L, l < b) :
    okL b (xc acc L b) := by
  induction L generalizing acc b with
  | nil => exact okL_nil _
  | cons l L ih =>
    simp only [xc, okL_cons]
    refine ⟨⟨⟨by simp, by simp⟩, ?_⟩, ⟨⟨by simp, by simp⟩, by simp⟩, ?_⟩
    · intro i hi; simp at hi; rcases hi with rfl | rfl
      · exact ha
      · exact hL _ (by simp)
    · exact ih (b + 1) (b + 1 + 1) (by omega) (fun l' hl' => by
        have := hL l' (by simp [hl']); omega)

theorem xc_val (acc : ℕ) (L : List ℕ) (w : List Bool) (ha : acc < w.length)
    (hL : ∀ l ∈ L, l < w.length) :
    bv ((run (xc acc L w.length) w).getD (xo acc L w.length) false) =
      bv (w.getD acc false) + (L.map fun l => bv (w.getD l false)).sum := by
  induction L generalizing acc w with
  | nil => simp [xc, xo, run]
  | cons l L ih =>
    have hl : l < w.length := hL l (by simp)
    set g1 : Gate := ⟨.mod 2, [acc, l]⟩
    set g2 : Gate := ⟨.not, [w.length]⟩
    set w2 := step (step w g1) g2 with hw2
    have hlen : w2.length = w.length + 2 := by simp [hw2, length_step]
    have e1 : ∀ i, i < w.length → w2.getD i false = w.getD i false := by
      intro i hi
      rw [hw2, getD_step_ne _ _ _ (by rw [length_step]; omega), getD_step_ne _ _ _ (by omega)]
    have hrun : run (xc acc (l :: L) w.length) w = run (xc (w.length + 1) L w2.length) w2 := by
      rw [hlen]; rfl
    have hxo : xo acc (l :: L) w.length = xo (w.length + 1) L w2.length := by rw [hlen]; rfl
    rw [hrun, hxo, ih (w.length + 1) w2 (by omega) (fun l' hl' => by
      have := hL l' (by simp [hl']); omega)]
    have v2 : bv (w2.getD (w.length + 1) false) = bv (w.getD acc false) + bv (w.getD l false) := by
      have : w.length + 1 = (step w g1).length := by rw [length_step]
      rw [hw2, this, getD_step_self]
      simp only [g2, GateOp.eval, List.map, List.headD]
      rw [bv_not, getD_step_self]
      simp only [g1, GateOp.eval, List.map]
      rw [bv_mod2]; simp; ring_nf; rw [show (2:F) = 0 from rfl, zero_add]
    rw [v2, List.map_congr_left (fun l' hl' => by rw [e1 l' (hL l' (by simp [hl']))])]
    simp; ring

def aff (c : Bool) (L : List ℕ) (b : ℕ) : List Gate :=
  ⟨if c then .and else .or, []⟩ :: xc b L (b + 1)

def affo (L : List ℕ) (b : ℕ) : ℕ := xo b L (b + 1)

theorem aff_length (c : Bool) (L : List ℕ) (b : ℕ) : (aff c L b).length = 2 * L.length + 1 := by
  simp [aff, xc_length]

theorem aff_cost (c : Bool) (L : List ℕ) (b : ℕ) : costL (aff c L b) = 0 := by
  rw [aff, costL_cons, xc_cost]; cases c <;> simp [cnt]

theorem affo_lt (c : Bool) (L : List ℕ) (b : ℕ) : affo L b < b + (aff c L b).length := by
  have := xo_lt b L (b + 1) (by omega); rw [aff_length]; unfold affo; omega

theorem aff_ok (c : Bool) (L : List ℕ) (b : ℕ) (hL : ∀ l ∈ L, l < b) : okL b (aff c L b) := by
  rw [aff, okL_cons]
  refine ⟨⟨⟨by simp, by cases c <;> simp⟩, by simp⟩, xc_ok _ _ _ (by omega) (fun l hl => ?_)⟩
  have := hL l hl; omega

theorem aff_val (c : Bool) (L : List ℕ) (w : List Bool) (hL : ∀ l ∈ L, l < w.length) :
    bv ((run (aff c L w.length) w).getD (affo L w.length) false) =
      bv c + (L.map fun l => bv (w.getD l false)).sum := by
  set g : Gate := ⟨if c then .and else .or, []⟩
  have hlen : (step w g).length = w.length + 1 := length_step _ _
  have hrun : run (aff c L w.length) w = run (xc w.length L (step w g).length) (step w g) := by
    rw [hlen]; rfl
  have hxo : affo L w.length = xo w.length L (step w g).length := by rw [hlen]; rfl
  rw [hrun, hxo, xc_val _ _ _ (by omega) (fun l hl => by have := hL l hl; omega),
    getD_step_self]
  have : g.op.eval ([].map fun i => w.getD i false) = c := by cases c <;> rfl
  rw [this]
  congr 1
  exact congrArg List.sum (List.map_congr_left (fun l hl => by
    rw [getD_step_ne _ _ _ (by have := hL l hl; omega)]))

theorem sum_filter_map {ι : Type*} (J : List ι) (P : ι → Bool) (f : ι → F) :
    ((J.filter P).map f).sum = (J.map fun j => if P j then f j else 0).sum := by
  induction J with
  | nil => rfl
  | cons j J ih => by_cases h : P j <;> simp [List.filter_cons, h, ih]

theorem sel_sum {k : ℕ} (ℓ f : Fin k → F) :
    (((List.finRange k).filter (fun j => decide (ℓ j = 1))).map f).sum = ∑ j, ℓ j * f j := by
  rw [sum_filter_map, Fin.sum_univ_def]
  congr 1
  apply List.map_congr_left
  intro j _
  have : ∀ a : F, a = 0 ∨ a = 1 := by decide
  rcases this (ℓ j) with h | h <;> simp [h]

theorem lin_dot {k : ℕ} (f : (Fin k → F) →ₗ[F] F) (v : Fin k → F) :
    f v = v ⬝ᵥ (fun j => f (Pi.single j 1)) := by
  conv_lhs => rw [show v = ∑ j, v j • (Pi.single j (1 : F) : Fin k → F) by
    ext i; simp [Finset.sum_apply, Pi.single_apply]]
  simp [map_sum, dotProduct]

theorem dual_exists {k : ℕ} (W : Submodule F (Fin k → F)) (c : Fin k → F) (hc : c ∉ W) :
    ∃ u : Fin k → F, (∀ w ∈ W, w ⬝ᵥ u = 0) ∧ c ⬝ᵥ u = 1 := by
  obtain ⟨f, hf, hW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hc inferInstance
  refine ⟨fun j => f (Pi.single j 1), fun w hw => ?_, ?_⟩
  · rw [← lin_dot]
    have : f w ∈ Submodule.map f W := Submodule.mem_map_of_mem hw
    rw [hW] at this; simpa using this
  · rw [← lin_dot]
    generalize f c = a at hf
    fin_cases a <;> first | rfl | exact absurd rfl hf

def bits (n : ℕ) (u : Fin n → F) : List Bool := List.ofFn (fun j : Fin n => decide (u j = 1))

theorem length_bits (n : ℕ) (u : Fin n → F) : (bits n u).length = n := by simp [bits]

theorem getD_bits (n : ℕ) (u : Fin n → F) (j : Fin n) : bv ((bits n u).getD j false) = u j := by
  simp [bits, List.getD_eq_getElem?_getD, bv_of_dec]

def sgn (b : Bool) : ℤ := if b then -1 else 1

def sgF (f : F) : ℤ := if f = 0 then 1 else -1

theorem sgn_eq (b : Bool) : sgn b = sgF (bv b) := by cases b <;> rfl

theorem sgF_add (a b : F) : sgF (a + b) = sgF a * sgF b := by
  fin_cases a <;> fin_cases b <;> rfl

theorem sgF_one_add (a : F) : sgF (1 + a) = - sgF a := by
  fin_cases a <;> rfl

theorem sgn_xor (a b : Bool) : sgn (Bool.xor a b) = sgF (bv a + bv b) := by
  rw [sgn_eq, bv_xor]

theorem F_cases (a : F) : a = 0 ∨ a = 1 := by fin_cases a; exacts [Or.inl rfl, Or.inr rfl]

theorem F_add_self (a : F) : a + a = 0 := by fin_cases a <;> rfl

theorem F_neg (a : F) : -a = a := by fin_cases a <;> rfl

theorem F_sub (a b : F) : a - b = a + b := by rw [sub_eq_add_neg, F_neg]

namespace D1

variable {k : ℕ}

open Classical in
noncomputable def piece (W : Submodule F (Fin k → F)) (p : Fin k → F) : Finset (Fin k → F) :=
  Finset.univ.filter (fun x => ∀ w ∈ W, w ⬝ᵥ x = w ⬝ᵥ p)

theorem mem_piece (W : Submodule F (Fin k → F)) (p x : Fin k → F) :
    x ∈ piece W p ↔ ∀ w ∈ W, w ⬝ᵥ x = w ⬝ᵥ p := by
  simp [piece]

theorem piece_bot (p : Fin k → F) : piece ⊥ p = Finset.univ := by
  ext x; simp [mem_piece]

theorem chsum_mem (W : Submodule F (Fin k → F)) (p c : Fin k → F) (hc : c ∈ W) (g : F → ℤ) :
    ∑ x ∈ piece W p, g (c ⬝ᵥ x) = (piece W p).card * g (c ⬝ᵥ p) := by
  rw [Finset.sum_congr rfl (fun x hx => by rw [(mem_piece W p x).1 hx c hc]), Finset.sum_const,
    nsmul_eq_mul]

theorem chsum_nmem (W : Submodule F (Fin k → F)) (p c : Fin k → F) (hc : c ∉ W) (e : F) :
    ∑ x ∈ piece W p, sgF (c ⬝ᵥ x + e) = 0 := by
  obtain ⟨u, hu, hcu⟩ := dual_exists W c hc
  refine Finset.sum_involution (fun x _ => x + u) (fun x _ => ?_) (fun x _ _ => ?_)
    (fun x hx => ?_) (fun x _ => ?_)
  · rw [dotProduct_add, hcu, show c ⬝ᵥ x + 1 + e = 1 + (c ⬝ᵥ x + e) by ring, sgF_one_add]; ring
  · intro h
    have : u = 0 := by simpa using h
    rw [this, dotProduct_zero] at hcu; exact absurd hcu (by decide)
  · rw [mem_piece] at hx ⊢
    intro w hw; rw [dotProduct_add, hu w hw, add_zero, hx w hw]
  · ext j; simp only [Pi.add_apply]; rw [add_assoc, F_add_self, add_zero]

theorem split_piece (W : Submodule F (Fin k → F)) (p ℓ u : Fin k → F)
    (hu : ∀ w ∈ W, w ⬝ᵥ u = 0) (hℓu : ℓ ⬝ᵥ u = 1) (τ : F) :
    piece (W ⊔ Submodule.span F {ℓ}) (p + (ℓ ⬝ᵥ p + τ) • u) =
      (piece W p).filter (fun x => ℓ ⬝ᵥ x = τ) := by
  have hW : ∀ w ∈ W, w ⬝ᵥ (p + (ℓ ⬝ᵥ p + τ) • u) = w ⬝ᵥ p := by
    intro w hw; rw [dotProduct_add, dotProduct_smul, hu w hw, smul_zero, add_zero]
  have hℓ : ℓ ⬝ᵥ (p + (ℓ ⬝ᵥ p + τ) • u) = τ := by
    rw [dotProduct_add, dotProduct_smul, hℓu, smul_eq_mul, mul_one, ← add_assoc, F_add_self,
      zero_add]
  ext x
  rw [Finset.mem_filter, mem_piece, mem_piece]
  constructor
  · intro h
    refine ⟨fun w hw => ?_, ?_⟩
    · rw [h w (Submodule.mem_sup_left hw), hW w hw]
    · rw [h ℓ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self ℓ)), hℓ]
  · rintro ⟨h1, h2⟩ w' hw'
    obtain ⟨w, hw, v, hv, rfl⟩ := Submodule.mem_sup.1 hw'
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
    rw [add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, h1 w hw, hW w hw, h2, hℓ]

theorem F_ne (a τ : F) : ¬ a = τ ↔ a = 1 + τ := by
  rcases F_cases a with rfl | rfl <;> rcases F_cases τ with rfl | rfl <;> decide

theorem split_sum (W : Submodule F (Fin k → F)) (p ℓ : Fin k → F) (τ : F) (φ : (Fin k → F) → ℤ) :
    ∑ x ∈ piece W p, φ x = ∑ x ∈ (piece W p).filter (fun x => ℓ ⬝ᵥ x = τ), φ x +
      ∑ x ∈ (piece W p).filter (fun x => ℓ ⬝ᵥ x = 1 + τ), φ x := by
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun x => ℓ ⬝ᵥ x = τ)]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext x; simp [F_ne]

theorem split_card (W : Submodule F (Fin k → F)) (p ℓ u : Fin k → F)
    (hu : ∀ w ∈ W, w ⬝ᵥ u = 0) (hℓu : ℓ ⬝ᵥ u = 1) (τ : F) (r : ℕ) (hr : r ≤ k)
    (hcard : (piece W p).card = 2 ^ (k - r)) :
    r + 1 ≤ k ∧ ((piece W p).filter (fun x => ℓ ⬝ᵥ x = τ)).card = 2 ^ (k - (r + 1)) := by
  have heq : ((piece W p).filter (fun x => ℓ ⬝ᵥ x = τ)).card =
      ((piece W p).filter (fun x => ℓ ⬝ᵥ x = 1 + τ)).card := by
    apply Finset.card_bij (fun x _ => x + u)
    · intro x hx
      rw [Finset.mem_filter, mem_piece] at hx ⊢
      refine ⟨fun w hw => ?_, ?_⟩
      · rw [dotProduct_add, hu w hw, add_zero, hx.1 w hw]
      · rw [dotProduct_add, hx.2, hℓu, add_comm]
    · intro a _ b _ h; simpa using h
    · intro b hb
      refine ⟨b + u, ?_, ?_⟩
      · rw [Finset.mem_filter, mem_piece] at hb ⊢
        refine ⟨fun w hw => ?_, ?_⟩
        · rw [dotProduct_add, hu w hw, add_zero, hb.1 w hw]
        · rw [dotProduct_add, hb.2, hℓu, add_comm, ← add_assoc, F_add_self, zero_add]
      · ext j; simp only [Pi.add_apply]; rw [add_assoc, F_add_self, add_zero]
  have hsum := split_sum W p ℓ τ (fun _ => (1 : ℤ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hcard] at hsum
  rw [← heq] at hsum
  have hsum' : 2 ^ (k - r) = 2 * ((piece W p).filter (fun x => ℓ ⬝ᵥ x = τ)).card := by
    have : 2 ^ (k - r) = ((piece W p).filter (fun x => ℓ ⬝ᵥ x = τ)).card +
        ((piece W p).filter (fun x => ℓ ⬝ᵥ x = τ)).card := by exact_mod_cast hsum
    omega
  rcases Nat.eq_zero_or_pos (k - r) with h0 | h0
  · rw [h0] at hsum'; omega
  · refine ⟨by omega, ?_⟩
    have : 2 ^ (k - r) = 2 * 2 ^ (k - (r + 1)) := by
      rw [← pow_succ']; congr 1; omega
    omega

theorem finrank_split (W : Submodule F (Fin k → F)) (ℓ : Fin k → F) (hℓ : ℓ ∉ W) :
    Module.finrank F ↥(W ⊔ Submodule.span F {ℓ}) = Module.finrank F W + 1 := by
  have h0 : ℓ ≠ 0 := fun h => hℓ (h ▸ W.zero_mem)
  have hinf : W ⊓ Submodule.span F {ℓ} = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv2
    rcases F_cases c with rfl | rfl
    · simp
    · exact absurd (by simpa using hv1) hℓ
  have := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span F {ℓ})
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton h0] at this
  exact this

def pr (f : ℕ → ℕ × ℕ) (n b : ℕ) : List Gate :=
  (List.range n).flatMap fun j => [⟨.mod 2, [(f j).1, (f j).2]⟩, ⟨.not, [b + 2 * j]⟩]

theorem pr_succ (f : ℕ → ℕ × ℕ) (n b : ℕ) :
    pr f (n + 1) b = pr f n b ++ [⟨.mod 2, [(f n).1, (f n).2]⟩, ⟨.not, [b + 2 * n]⟩] := by
  simp [pr, List.range_succ, List.flatMap_append]

theorem pr_length (f : ℕ → ℕ × ℕ) (n b : ℕ) : (pr f n b).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pr_succ]; simp [ih]; ring

theorem pr_cost (f : ℕ → ℕ × ℕ) (n b : ℕ) : costL (pr f n b) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pr_succ, costL_append, ih]; simp [costL_cons, cnt, costL_nil]

theorem pr_ok (f : ℕ → ℕ × ℕ) (n b : ℕ) (hf : ∀ j < n, (f j).1 < b ∧ (f j).2 < b) :
    okL b (pr f n b) := by
  induction n with
  | zero => exact okL_nil _
  | succ n ih =>
    rw [pr_succ, okL_append, pr_length]
    refine ⟨ih (fun j hj => hf j (by omega)), ?_⟩
    rw [okL_cons, okL_single]
    have := hf n (by omega)
    refine ⟨⟨⟨by simp, by simp⟩, ?_⟩, ⟨by simp, by simp⟩, ?_⟩
    · intro i hi; simp at hi; omega
    · intro i hi; simp at hi; omega

theorem pr_val (f : ℕ → ℕ × ℕ) (n : ℕ) (w : List Bool)
    (hf : ∀ j < n, (f j).1 < w.length ∧ (f j).2 < w.length) (j : ℕ) (hj : j < n) :
    bv ((run (pr f n w.length) w).getD (w.length + 2 * j + 1) false) =
      bv (w.getD (f j).1 false) + bv (w.getD (f j).2 false) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [pr_succ, run_append]
    set w1 := run (pr f n w.length) w with hw1
    have hl1 : w1.length = w.length + 2 * n := by rw [hw1, length_run, pr_length]
    have hpre : ∀ i < w.length, w1.getD i false = w.getD i false := fun i hi =>
      getD_run_lt _ _ _ hi
    rcases Nat.lt_or_ge j n with hjn | hjn
    · rw [getD_run_lt _ _ _ (by omega), ih (fun j hj => hf j (by omega)) hjn]
    · have hjn : j = n := by omega
      subst hjn
      have h2 := hf j (by omega)
      rw [show [(⟨.mod 2, [(f j).1, (f j).2]⟩ : Gate), ⟨.not, [w.length + 2 * j]⟩] =
          [⟨.mod 2, [(f j).1, (f j).2]⟩] ++ [⟨.not, [w.length + 2 * j]⟩] from rfl,
        show w.length + 2 * j + 1 = w1.length + [(⟨.mod 2, [(f j).1, (f j).2]⟩ : Gate)].length by
          simp [hl1]]
      rw [getD_run_self]
      simp only [GateOp.eval, List.map, List.headD]
      rw [bv_not, show w.length + 2 * j = w1.length + ([] : List Gate).length by simp [hl1],
        show run [(⟨.mod 2, [(f j).1, (f j).2]⟩ : Gate)] w1 = step w1 ⟨.mod 2, [(f j).1, (f j).2]⟩
          from rfl, List.length_nil, add_zero, getD_step_self]
      simp only [GateOp.eval, List.map]
      rw [bv_mod2, hpre _ h2.1, hpre _ h2.2]
      simp; ring_nf; rw [show (2:F) = 0 from rfl, zero_add]

theorem getD_app_left (l1 l2 : List Bool) (i : ℕ) (h : i < l1.length) :
    (l1 ++ l2).getD i false = l1.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_right (l1 l2 : List Bool) (i : ℕ) (h : l1.length ≤ i) :
    (l1 ++ l2).getD i false = l2.getD (i - l1.length) false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem runD_app (D E : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length + D.length) :
    (run (D ++ E) w).getD i false = (run D w).getD i false := by
  rw [run_append, getD_run_lt _ _ _ (by rw [length_run]; exact h)]

variable {t : ℕ}

def inD (y : Fin k → F) (z : Fin t → F) : List Bool := bits k y ++ bits t z

def inC (x y : Fin k → F) (z : Fin t → F) : List Bool := bits k x ++ inD y z

theorem length_inD (y : Fin k → F) (z : Fin t → F) : (inD y z).length = k + t := by
  simp [inD, length_bits]

theorem length_inC (x y : Fin k → F) (z : Fin t → F) : (inC x y z).length = 2 * k + t := by
  simp [inC, length_bits, length_inD]; ring

def pt (D : List Gate) (tap : Fin k → ℕ) (y : Fin k → F) (z : Fin t → F) : Fin k → F :=
  fun j => bv ((run D (inD y z)).getD (tap j) false)

theorem pt_app (D E : List Gate) (tap : Fin k → ℕ) (htap : ∀ j, tap j < k + t + D.length)
    (y : Fin k → F) (z : Fin t → F) : pt (D ++ E) tap y z = pt D tap y z := by
  ext j; unfold pt; rw [runD_app _ _ _ _ (by rw [length_inD]; exact htap j)]

def Good (t : ℕ) (G : List Gate) (W : Submodule F (Fin k → F)) (D : List Gate) (tap : Fin k → ℕ)
    (ℓ : ℕ → Fin k → F) (d : ℕ → ℕ) : Prop :=
  okL (k + t) D ∧ costL D + Module.finrank F W ≤ costL G ∧ k + t + 1 < k + t + D.length ∧
  (∀ (y : Fin k → F) (z : Fin t → F), (run D (inD y z)).getD (k + t) false = false ∧
    (run D (inD y z)).getD (k + t + 1) false = true) ∧
  (∀ j, tap j < k + t + D.length) ∧ (∀ i, d i < k + t + D.length) ∧ Module.finrank F W ≤ k ∧
  (∀ (y : Fin k → F) (z : Fin t → F), (piece W (pt D tap y z)).card = 2 ^ (k - Module.finrank F W)) ∧
  ∀ (y : Fin k → F) (z : Fin t → F) x, x ∈ piece W (pt D tap y z) → ∀ i,
    bv ((run G (inC x y z)).getD i false) = ℓ i ⬝ᵥ x + bv ((run D (inD y z)).getD (d i) false)

theorem good_extend (G : List Gate) (g : Gate) (W : Submodule F (Fin k → F)) (D : List Gate)
    (tap : Fin k → ℕ) (ℓ : ℕ → Fin k → F) (d : ℕ → ℕ) (hb : Good t G W D tap ℓ d)
    (W' : Submodule F (Fin k → F)) (E : List Gate) (tap' : Fin k → ℕ) (lm : Fin k → F) (dm : ℕ)
    (hE : okL (k + t + D.length) E)
    (hcost : costL E + Module.finrank F W' ≤ Module.finrank F W + costL [g])
    (htap : ∀ j, tap' j < k + t + D.length + E.length)
    (hdm : dm < k + t + D.length + E.length)
    (hrank : Module.finrank F W' ≤ k)
    (hsub : ∀ y (z : Fin t → F), piece W' (pt (D ++ E) tap' y z) ⊆ piece W (pt D tap y z))
    (hcard : ∀ y (z : Fin t → F),
      (piece W' (pt (D ++ E) tap' y z)).card = 2 ^ (k - Module.finrank F W'))
    (hval : ∀ y (z : Fin t → F) x, x ∈ piece W' (pt (D ++ E) tap' y z) →
      bv (g.op.eval (g.inputs.map fun i => (run G (inC x y z)).getD i false)) =
        lm ⬝ᵥ x + bv ((run (D ++ E) (inD y z)).getD dm false)) :
    Good t (G ++ [g]) W' (D ++ E) tap' (Function.update ℓ (2 * k + t + G.length) lm)
      (Function.update d (2 * k + t + G.length) dm) := by
  obtain ⟨hD, hc, h2, hconst, htp, hd, hr, hcd, hv⟩ := hb
  refine ⟨(okL_append _ _ _).2 ⟨hD, hE⟩, ?_, ?_, ?_, ?_, ?_, hrank, hcard, ?_⟩
  · rw [costL_append, costL_append]; omega
  · simp; omega
  · intro y z
    rw [runD_app _ _ _ _ (by rw [length_inD]; omega), runD_app _ _ _ _ (by rw [length_inD]; omega)]
    exact hconst y z
  · intro j; have := htap j; simp; omega
  · intro i
    by_cases hi : i = 2 * k + t + G.length
    · subst hi; rw [Function.update_self]; simp; omega
    · rw [Function.update_of_ne hi]; have := hd i; simp; omega
  · intro y z x hx i
    by_cases hi : i = 2 * k + t + G.length
    · subst hi
      rw [Function.update_self, Function.update_self, ← length_inC x y z, getD_run_self]
      exact hval y z x hx
    · rw [Function.update_of_ne hi, Function.update_of_ne hi,
        getD_run_ne _ _ _ _ (by rw [length_inC]; exact hi),
        runD_app _ _ _ _ (by rw [length_inD]; exact hd i)]
      exact hv y z x (hsub y z hx) i

theorem good_single (G : List Gate) (g : Gate) (W : Submodule F (Fin k → F)) (D : List Gate)
    (tap : Fin k → ℕ) (ℓ : ℕ → Fin k → F) (d : ℕ → ℕ) (hb : Good t G W D tap ℓ d)
    (e : Gate) (lm : Fin k → F) (he : shapeOK e) (hei : ∀ i ∈ e.inputs, i < k + t + D.length)
    (hcost : costL [e] ≤ costL [g])
    (hval : ∀ y (z : Fin t → F) x, x ∈ piece W (pt D tap y z) →
      bv (g.op.eval (g.inputs.map fun i => (run G (inC x y z)).getD i false)) =
        lm ⬝ᵥ x + bv (e.op.eval (e.inputs.map fun i => (run D (inD y z)).getD i false))) :
    Good t (G ++ [g]) W (D ++ [e]) tap (Function.update ℓ (2 * k + t + G.length) lm)
      (Function.update d (2 * k + t + G.length) (k + t + D.length)) := by
  have htp := hb.2.2.2.2.1
  have hpt : ∀ y (z : Fin t → F), pt (D ++ [e]) tap y z = pt D tap y z :=
    fun y z => pt_app D [e] tap htp y z
  refine good_extend G g W D tap ℓ d hb W [e] tap lm _ ((okL_single _ _).2 ⟨he, hei⟩)
    (by omega) (fun j => by have := htp j; simp; omega) (by simp) hb.2.2.2.2.2.2.1
    (fun y z => by rw [hpt]) (fun y z => by rw [hpt]; exact hb.2.2.2.2.2.2.2.1 y z) ?_
  intro y z x hx
  rw [hpt] at hx
  rw [hval y z x hx, show k + t + D.length = (inD y z).length + D.length by rw [length_inD],
    getD_run_self]

def D0 : List Gate := [⟨.or, []⟩, ⟨.and, []⟩]

def ℓ0 (k : ℕ) : ℕ → Fin k → F := fun i => if h : i < k then Pi.single ⟨i, h⟩ 1 else 0

def d0 (k t : ℕ) : ℕ → ℕ := fun i => if k ≤ i ∧ i < 2 * k + t then i - k else k + t

theorem D0_const (w : List Bool) :
    (run D0 w).getD w.length false = false ∧ (run D0 w).getD (w.length + 1) false = true := by
  simp [D0, run, step, List.getD_eq_getElem?_getD, GateOp.eval]

theorem good_init : Good t [] ⊥ D0 (fun _ => k + t) (ℓ0 k) (d0 k t) := by
  have hc : ∀ (y : Fin k → F) (z : Fin t → F), (run D0 (inD y z)).getD (k + t) false = false ∧
      (run D0 (inD y z)).getD (k + t + 1) false = true := by
    intro y z; have := D0_const (inD y z); rwa [length_inD] at this
  refine ⟨?_, ?_, by simp [D0], hc, fun _ => by simp [D0], fun i => ?_, by simp, fun y z => ?_, ?_⟩
  · rw [D0, okL_cons, okL_single]; simp [shapeOK]
  · simp [D0, costL_cons, costL_nil, cnt]
  · unfold d0; split_ifs <;> simp [D0] <;> omega
  · rw [piece_bot, Finset.card_univ]; simp
  · intro y z x _ i
    rw [show run ([] : List Gate) (inC x y z) = inC x y z from rfl]
    by_cases h1 : i < k
    · have hd : d0 k t i = k + t := by unfold d0; rw [if_neg (by omega)]
      rw [hd, (hc y z).1, inC, getD_app_left _ _ _ (by rw [length_bits]; exact h1)]
      have := getD_bits k x ⟨i, h1⟩
      simp only at this
      rw [this]
      simp [ℓ0, h1, single_dotProduct]
    · by_cases h2 : i < 2 * k + t
      · have hd : d0 k t i = i - k := by unfold d0; rw [if_pos (by omega)]
        rw [hd, inC, getD_app_right _ _ _ (by rw [length_bits]; omega), length_bits,
          getD_run_lt _ _ _ (by rw [length_inD]; omega)]
        simp [ℓ0, h1]
      · have hd : d0 k t i = k + t := by unfold d0; rw [if_neg (by omega)]
        rw [hd, (hc y z).1, getD_ge _ _ (by rw [length_inC]; omega)]
        simp [ℓ0, h1]

theorem list_sum_dot (L : List ℕ) (ℓ : ℕ → Fin k → F) (x : Fin k → F) :
    (L.map ℓ).sum ⬝ᵥ x = (L.map fun i => ℓ i ⬝ᵥ x).sum := by
  induction L with
  | nil => simp
  | cons i L ih => simp [add_dotProduct, ih]

theorem good_not (G : List Gate) (g : Gate) (W : Submodule F (Fin k → F)) (D : List Gate)
    (tap : Fin k → ℕ) (ℓ : ℕ → Fin k → F) (d : ℕ → ℕ) (hb : Good t G W D tap ℓ d)
    (i : ℕ) (hop : g.op = .not) (hin : g.inputs = [i]) :
    Good t (G ++ [g]) W (D ++ [⟨.not, [d i]⟩]) tap (Function.update ℓ (2 * k + t + G.length) (ℓ i))
      (Function.update d (2 * k + t + G.length) (k + t + D.length)) := by
  refine good_single G g W D tap ℓ d hb _ _ ⟨by simp, by simp⟩ (by simpa using hb.2.2.2.2.2.1 i)
    (by simp [costL_single, cnt]) ?_
  intro y z x hx
  rw [hop, hin]
  simp only [GateOp.eval, List.map, List.headD]
  rw [bv_not, bv_not, hb.2.2.2.2.2.2.2.2 y z x hx i]; ring

theorem good_mod (G : List Gate) (g : Gate) (W : Submodule F (Fin k → F)) (D : List Gate)
    (tap : Fin k → ℕ) (ℓ : ℕ → Fin k → F) (d : ℕ → ℕ) (hb : Good t G W D tap ℓ d)
    (hop : g.op = .mod 2) (hlen : g.inputs.length ≤ 2) :
    Good t (G ++ [g]) W (D ++ [⟨.mod 2, g.inputs.map d⟩]) tap
      (Function.update ℓ (2 * k + t + G.length) (g.inputs.map ℓ).sum)
      (Function.update d (2 * k + t + G.length) (k + t + D.length)) := by
  refine good_single G g W D tap ℓ d hb _ _ ⟨by simpa using hlen, by simp⟩
    (by intro i hi; simp at hi; obtain ⟨a, _, rfl⟩ := hi; exact hb.2.2.2.2.2.1 a)
    (by simp [costL_single, cnt]) ?_
  intro y z x hx
  rw [hop]
  simp only [GateOp.eval]
  rw [bv_mod2, bv_mod2, List.map_map, List.map_map, List.map_map, list_sum_dot]
  have e : ∀ i ∈ g.inputs, (bv ∘ fun i => (run G (inC x y z)).getD i false) i =
      (fun i => ℓ i ⬝ᵥ x) i + ((bv ∘ fun i => (run D (inD y z)).getD i false) ∘ d) i :=
    fun i _ => hb.2.2.2.2.2.2.2.2 y z x hx i
  rw [List.map_congr_left e, List.sum_map_add]; ring

theorem good_ao01 (G : List Gate) (g : Gate) (W : Submodule F (Fin k → F)) (D : List Gate)
    (tap : Fin k → ℕ) (ℓ : ℕ → Fin k → F) (d : ℕ → ℕ) (hb : Good t G W D tap ℓ d)
    (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length ≤ 1) :
    Good t (G ++ [g]) W (D ++ [⟨g.op, g.inputs.map d⟩]) tap
      (Function.update ℓ (2 * k + t + G.length) (g.inputs.map ℓ).sum)
      (Function.update d (2 * k + t + G.length) (k + t + D.length)) := by
  refine good_single G g W D tap ℓ d hb _ _ ⟨by simp; omega, by rcases hop with h | h <;> simp [h]⟩
    (by intro i hi; simp at hi; obtain ⟨a, _, rfl⟩ := hi; exact hb.2.2.2.2.2.1 a)
    (by rw [costL_single, if_neg (by simp [cnt]; omega)]; exact Nat.zero_le _) ?_
  intro y z x hx
  match hg : g.inputs, hlen with
  | [], _ => simp
  | [i], _ =>
    have := hb.2.2.2.2.2.2.2.2 y z x hx i
    rcases hop with h | h <;> simp only [h, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false, List.sum_cons,
      List.sum_nil, add_zero] <;> exact this

def sel (ℓv : Fin k → F) (tap : Fin k → ℕ) : List ℕ :=
  ((List.finRange k).filter (fun j => decide (ℓv j = 1))).map tap

theorem sel_val (w : List Bool) (tap : Fin k → ℕ) (ℓv : Fin k → F) :
    ((sel ℓv tap).map fun l => bv (w.getD l false)).sum =
      ℓv ⬝ᵥ (fun j => bv (w.getD (tap j) false)) := by
  unfold sel; rw [List.map_map]; exact sel_sum ℓv _

theorem sel_lt (ℓv : Fin k → F) (tap : Fin k → ℕ) (b : ℕ) (h : ∀ j, tap j < b) :
    ∀ l ∈ sel ℓv tap, l < b := by
  intro l hl; unfold sel at hl; simp at hl; obtain ⟨j, _, rfl⟩ := hl; exact h j

theorem affD (D : List Gate) (c : Bool) (L : List ℕ) (w : List Bool)
    (hL : ∀ l ∈ L, l < w.length + D.length) (R : List Gate) :
    bv ((run (D ++ aff c L (w.length + D.length) ++ R) w).getD (affo L (w.length + D.length))
      false) = bv c + (L.map fun l => bv ((run D w).getD l false)).sum := by
  have hl : (run D w).length = w.length + D.length := length_run _ _
  rw [run_append, run_append, getD_run_lt _ _ _ (by
    rw [length_run, hl]; exact affo_lt c L _), ← hl,
    aff_val _ _ _ (by rw [hl]; exact hL)]

theorem gadget_aff (D : List Gate) (c : Bool) (L : List ℕ) (hL : ∀ l ∈ L, l < k + t + D.length) :
    ∃ A o, okL (k + t + D.length) A ∧ costL A = 0 ∧ o < k + t + D.length + A.length ∧
      ∀ (y : Fin k → F) (z : Fin t → F) (R : List Gate),
        bv ((run (D ++ A ++ R) (inD y z)).getD o false) =
          bv c + (L.map fun l => bv ((run D (inD y z)).getD l false)).sum := by
  refine ⟨aff c L (k + t + D.length), affo L (k + t + D.length), aff_ok _ _ _ hL, aff_cost _ _ _,
    affo_lt _ _ _, fun y z R => ?_⟩
  have := affD D c L (inD y z) (by rw [length_inD]; exact hL) R
  rwa [length_inD] at this

theorem good_copy (G : List Gate) (g : Gate) (W : Submodule F (Fin k → F)) (D : List Gate)
    (tap : Fin k → ℕ) (ℓ : ℕ → Fin k → F) (d : ℕ → ℕ) (hb : Good t G W D tap ℓ d)
    (hop : g.op = .and ∨ g.op = .or) (i j : ℕ) (hin : g.inputs = [i, j])
    (hi : ℓ i ∈ W) (hj : ℓ j ∈ W) :
    ∃ D' dm, Good t (G ++ [g]) W D' tap (Function.update ℓ (2 * k + t + G.length) 0)
      (Function.update d (2 * k + t + G.length) dm) ∧
      ∀ y (z : Fin t → F), pt D' tap y z = pt D tap y z := by
  obtain ⟨hD, hc, h2, hconst, htp, hd, hr, hcd, hv⟩ := hb
  have hb : Good t G W D tap ℓ d := ⟨hD, hc, h2, hconst, htp, hd, hr, hcd, hv⟩
  have hL : ∀ m, ∀ l ∈ d m :: sel (ℓ m) tap, l < k + t + D.length := by
    intro m l hl; simp only [List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact hd m
    · exact sel_lt _ _ _ htp l hl
  obtain ⟨A, oA, hAok, hAc, hoA, hAv⟩ := gadget_aff (t := t) D false _ (hL i)
  obtain ⟨B, oB, hBok, hBc, hoB, hBv⟩ := gadget_aff (k := k) (t := t) (D ++ A) false (d j :: sel (ℓ j) tap)
    (fun l hl => by have := hL j l hl; simp; omega)
  have hpt : ∀ y (z : Fin t → F), pt (D ++ (A ++ B ++ [⟨g.op, [oA, oB]⟩])) tap y z = pt D tap y z :=
    fun y z => pt_app D _ tap htp y z
  have key := good_extend G g W D tap ℓ d hb W (A ++ B ++ [⟨g.op, [oA, oB]⟩]) tap 0
    (k + t + (D ++ A ++ B).length) ?_ ?_ (fun j => by have := htp j; simp; omega)
    (by simp; omega) hr (fun y z => by rw [hpt]) (fun y z => by rw [hpt]; exact hcd y z) ?_
  · refine ⟨_, _, key, hpt⟩
  · rw [okL_append, okL_append]
    refine ⟨⟨hAok, by simpa [Nat.add_assoc] using hBok⟩, ?_⟩
    rw [okL_single]
    refine ⟨⟨by simp, by rcases hop with h | h <;> simp [h]⟩, ?_⟩
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    simp only [List.length_append] at hoB ⊢
    rcases hl with rfl | rfl <;> omega
  · rw [costL_append, costL_append, hAc, hBc, costL_single, costL_single,
      if_pos (show cnt ⟨g.op, [oA, oB]⟩ from ⟨hop, rfl⟩),
      if_pos (show cnt g from ⟨hop, by simp [hin]⟩)]
    omega
  · intro y z x hx
    rw [hpt] at hx
    have hl : (inD y z).length = k + t := length_inD y z
    have hvi := hv y z x hx i
    have hvj := hv y z x hx j
    have eA : bv ((run (D ++ A ++ B) (inD y z)).getD oA false) =
        bv ((run G (inC x y z)).getD i false) := by
      rw [hAv y z B, hvi]
      simp only [List.map_cons, List.sum_cons, sel_val, bv_false, zero_add]
      rw [(mem_piece W _ x).1 hx (ℓ i) hi]; unfold pt; ring
    have eB : bv ((run (D ++ A ++ B) (inD y z)).getD oB false) =
        bv ((run G (inC x y z)).getD j false) := by
      have := hBv y z []
      rw [List.append_nil] at this
      rw [this, hvj]
      simp only [List.map_cons, List.sum_cons, sel_val, bv_false, zero_add]
      rw [runD_app _ _ _ _ (by rw [hl]; exact hd j)]
      have : (fun j => bv ((run (D ++ A) (inD y z)).getD (tap j) false)) = pt D tap y z := by
        ext jj; unfold pt; rw [runD_app _ _ _ _ (by rw [hl]; exact htp jj)]
      rw [this, (mem_piece W _ x).1 hx (ℓ j) hj]; unfold pt; ring
    rw [show D ++ (A ++ B ++ [⟨g.op, [oA, oB]⟩]) = (D ++ A ++ B) ++ [⟨g.op, [oA, oB]⟩] by simp,
      show k + t + (D ++ A ++ B).length = (inD y z).length + (D ++ A ++ B).length by rw [hl],
      getD_run_self, zero_dotProduct, zero_add, hin]
    simp only [List.map]
    rw [bv_inj eA, bv_inj eB]

theorem good_split (G : List Gate) (g : Gate) (W : Submodule F (Fin k → F)) (D : List Gate)
    (tap : Fin k → ℕ) (ℓ : ℕ → Fin k → F) (d : ℕ → ℕ) (hb : Good t G W D tap ℓ d)
    (hcg : costL [g] = 1) (s : ℕ) (hs : ℓ s ∉ W) (β : Bool) (lm : Fin k → F) (dm : ℕ)
    (hdm : dm < k + t + D.length)
    (hres : ∀ y (z : Fin t → F) x, x ∈ piece W (pt D tap y z) →
      (run G (inC x y z)).getD s false = β →
      bv (g.op.eval (g.inputs.map fun i => (run G (inC x y z)).getD i false)) =
        lm ⬝ᵥ x + bv ((run D (inD y z)).getD dm false)) :
    ∃ D' tap', Good t (G ++ [g]) (W ⊔ Submodule.span F {ℓ s}) D' tap'
      (Function.update ℓ (2 * k + t + G.length) lm) (Function.update d (2 * k + t + G.length) dm) ∧
      ∀ y (z : Fin t → F), piece (W ⊔ Submodule.span F {ℓ s}) (pt D' tap' y z) =
        (piece W (pt D tap y z)).filter
          (fun x => ℓ s ⬝ᵥ x = bv β + bv ((run D (inD y z)).getD (d s) false)) := by
  obtain ⟨hD, hc, h2, hconst, htp, hd, hr, hcd, hv⟩ := hb
  have hb : Good t G W D tap ℓ d := ⟨hD, hc, h2, hconst, htp, hd, hr, hcd, hv⟩
  obtain ⟨u, hu, hsu⟩ := dual_exists W (ℓ s) hs
  have hLs : ∀ l ∈ d s :: sel (ℓ s) tap, l < k + t + D.length := by
    intro l hl; simp only [List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact hd s
    · exact sel_lt _ _ _ htp l hl
  obtain ⟨A, σ, hAok, hAc, hσ, hAv⟩ := gadget_aff (t := t) D β _ hLs
  set b1 := k + t + D.length + A.length with hb1
  set f : ℕ → ℕ × ℕ := fun jj => if h : jj < k then
    (tap ⟨jj, h⟩, if u ⟨jj, h⟩ = 1 then σ else k + t) else (k + t, k + t) with hf
  have hfl : ∀ jj < k, (f jj).1 < b1 ∧ (f jj).2 < b1 := by
    intro jj hjj
    simp only [hf, dif_pos hjj]
    refine ⟨by have := htp ⟨jj, hjj⟩; omega, ?_⟩
    split_ifs <;> omega
  set P := pr f k b1
  set tap' : Fin k → ℕ := fun j => b1 + 2 * j + 1
  have keyp : ∀ y (z : Fin t → F), pt (D ++ (A ++ P)) tap' y z = pt D tap y z +
      (ℓ s ⬝ᵥ pt D tap y z + (bv β + bv ((run D (inD y z)).getD (d s) false))) • u := by
    intro y z
    ext j
    have hl : (inD y z).length = k + t := length_inD y z
    have hw1 : (run (D ++ A) (inD y z)).length = b1 := by
      rw [length_run, hl]; simp [hb1]; omega
    simp only [pt, tap']
    rw [← List.append_assoc, run_append]
    have hpv := pr_val f k (run (D ++ A) (inD y z)) (by rw [hw1]; exact hfl) j j.2
    rw [hw1] at hpv
    rw [hpv]
    simp only [hf, dif_pos j.2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [runD_app _ _ _ _ (by rw [hl]; exact htp j)]
    congr 1
    rcases F_cases (u j) with h0 | h1
    · have : ¬ u ⟨j.1, j.2⟩ = 1 := by rw [h0]; decide
      rw [if_neg this, runD_app _ _ _ _ (by rw [hl]; omega), (hconst y z).1, h0]; simp
    · have : u ⟨j.1, j.2⟩ = 1 := h1
      rw [if_pos this, h1, mul_one]
      have := hAv y z []
      rw [List.append_nil] at this
      rw [this]
      simp only [List.map_cons, List.sum_cons, sel_val]
      unfold pt; ring
  have hpiece : ∀ y (z : Fin t → F), piece (W ⊔ Submodule.span F {ℓ s}) (pt (D ++ (A ++ P)) tap' y z) =
      (piece W (pt D tap y z)).filter
        (fun x => ℓ s ⬝ᵥ x = bv β + bv ((run D (inD y z)).getD (d s) false)) := by
    intro y z; rw [keyp]; exact split_piece W _ (ℓ s) u hu hsu _
  have hrk := finrank_split W (ℓ s) hs
  refine ⟨D ++ (A ++ P), tap', good_extend G g W D tap ℓ d hb _ (A ++ P) tap' lm dm ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_, hpiece⟩
  · rw [okL_append]; exact ⟨hAok, pr_ok f k _ hfl⟩
  · rw [costL_append, hAc, pr_cost, hrk, hcg]; omega
  · intro j
    have hPl : P.length = 2 * k := pr_length _ _ _
    have := j.2
    simp only [tap', List.length_append, hPl, hb1]; omega
  · simp; omega
  · rw [hrk]
    exact (split_card W (pt D tap 0 (0 : Fin t → F)) (ℓ s) u hu hsu 0 _ hr (hcd 0 0)).1
  · intro y z; rw [hpiece]; exact Finset.filter_subset _ _
  · intro y z; rw [hpiece, hrk]
    exact (split_card W (pt D tap y z) (ℓ s) u hu hsu _ _ hr (hcd y z)).2
  · intro y z x hx
    rw [hpiece, Finset.mem_filter] at hx
    have hl : (inD y z).length = k + t := length_inD y z
    have hvs := hv y z x hx.1 s
    rw [hx.2] at hvs
    have hβ : (run G (inC x y z)).getD s false = β := by
      apply bv_inj; rw [hvs, add_assoc, F_add_self, add_zero]
    rw [hres y z x hx.1 hβ, runD_app _ _ _ _ (by rw [hl]; exact hdm)]

abbrev Br (k : ℕ) := Submodule F (Fin k → F) × List Gate × (Fin k → ℕ) × (ℕ → Fin k → F) × (ℕ → ℕ)

def GoodT (t : ℕ) (G : List Gate) (b : Br k) : Prop :=
  Good t G b.1 b.2.1 b.2.2.1 b.2.2.2.1 b.2.2.2.2

noncomputable def pieceT (b : Br k) (y : Fin k → F) (z : Fin t → F) : Finset (Fin k → F) :=
  piece b.1 (pt b.2.1 b.2.2.1 y z)

theorem step_two (G : List Gate) (g : Gate) (W : Submodule F (Fin k → F)) (D : List Gate)
    (tap : Fin k → ℕ) (ℓ : ℕ → Fin k → F) (d : ℕ → ℕ) (hb : Good t G W D tap ℓ d)
    (hop : g.op = .and ∨ g.op = .or) (i j : ℕ) (hin : g.inputs = [i, j]) :
    ∃ Lb : List (Br k), (∀ b ∈ Lb, GoodT t (G ++ [g]) b) ∧
      ∀ y (z : Fin t → F) (φ : (Fin k → F) → ℤ), ∑ x ∈ piece W (pt D tap y z), φ x =
        (Lb.map fun b => ∑ x ∈ pieceT b y z, φ x).sum := by
  by_cases hc : ℓ i ∈ W ∧ ℓ j ∈ W
  · obtain ⟨D', dm, hG, hpt⟩ := good_copy G g W D tap ℓ d hb hop i j hin hc.1 hc.2
    exact ⟨[(W, D', tap, _, _)], by simpa [GoodT] using hG,
      fun y z φ => by simp [pieceT, hpt]⟩
  have hso : ∃ s o, ℓ s ∉ W ∧ (g.op = .and → ∀ v : ℕ → Bool, g.op.eval (g.inputs.map v) =
      (v s && v o)) ∧ (g.op = .or → ∀ v : ℕ → Bool, g.op.eval (g.inputs.map v) = (v s || v o)) := by
    by_cases hi : ℓ i ∈ W
    · refine ⟨j, i, fun hj => hc ⟨hi, hj⟩, fun h v => ?_, fun h v => ?_⟩ <;>
        rw [hin, h] <;> simp [GateOp.eval, Bool.and_comm, Bool.or_comm]
    · refine ⟨i, j, hi, fun h v => ?_, fun h v => ?_⟩ <;> rw [hin, h] <;> simp [GateOp.eval]
  obtain ⟨s, o, hs, hevA, hevO⟩ := hso
  have hcg : costL [g] = 1 := by rw [costL_single, if_pos ⟨hop, by simp [hin]⟩]
  obtain ⟨hD, hc', h2, hconst, htp, hd, hr, hcd, hv⟩ := hb
  have hb : Good t G W D tap ℓ d := ⟨hD, hc', h2, hconst, htp, hd, hr, hcd, hv⟩
  have hsum : ∀ (DF DT : List Gate) (tF tT : Fin k → ℕ),
      (∀ y (z : Fin t → F), piece (W ⊔ Submodule.span F {ℓ s}) (pt DF tF y z) =
        (piece W (pt D tap y z)).filter
          (fun x => ℓ s ⬝ᵥ x = bv false + bv ((run D (inD y z)).getD (d s) false))) →
      (∀ y (z : Fin t → F), piece (W ⊔ Submodule.span F {ℓ s}) (pt DT tT y z) =
        (piece W (pt D tap y z)).filter
          (fun x => ℓ s ⬝ᵥ x = bv true + bv ((run D (inD y z)).getD (d s) false))) →
      ∀ y (z : Fin t → F) (φ : (Fin k → F) → ℤ), ∑ x ∈ piece W (pt D tap y z), φ x =
        ∑ x ∈ piece (W ⊔ Submodule.span F {ℓ s}) (pt DF tF y z), φ x +
          ∑ x ∈ piece (W ⊔ Submodule.span F {ℓ s}) (pt DT tT y z), φ x := by
    intro DF DT tF tT hF hT y z φ
    rw [hF, hT, split_sum W _ (ℓ s) (bv false + bv ((run D (inD y z)).getD (d s) false)) φ]
    simp
  rcases hop with hop | hop
  · obtain ⟨DF, tF, hF, pF⟩ := good_split G g W D tap ℓ d hb hcg s hs false 0 (k + t) (by omega)
      (fun y z x _ h => by
        rw [hevA hop, h, Bool.false_and, (hconst y z).1, zero_dotProduct]; rfl)
    obtain ⟨DT, tT, hT, pT⟩ := good_split G g W D tap ℓ d hb hcg s hs true (ℓ o) (d o) (hd o)
      (fun y z x hx h => by rw [hevA hop, h, Bool.true_and]; exact hv y z x hx o)
    refine ⟨[(W ⊔ Submodule.span F {ℓ s}, DF, tF, Function.update ℓ (2 * k + t + G.length) 0,
      Function.update d (2 * k + t + G.length) (k + t)), (W ⊔ Submodule.span F {ℓ s}, DT, tT,
      Function.update ℓ (2 * k + t + G.length) (ℓ o), Function.update d (2 * k + t + G.length) (d o))], ?_, fun y z φ => ?_⟩
    · intro b hb'; simp at hb'; rcases hb' with rfl | rfl
      · exact hF
      · exact hT
    · rw [hsum DF DT tF tT pF pT y z φ]; simp [pieceT]
  · obtain ⟨DF, tF, hF, pF⟩ := good_split G g W D tap ℓ d hb hcg s hs false (ℓ o) (d o) (hd o)
      (fun y z x hx h => by rw [hevO hop, h, Bool.false_or]; exact hv y z x hx o)
    obtain ⟨DT, tT, hT, pT⟩ := good_split G g W D tap ℓ d hb hcg s hs true 0 (k + t + 1) (by omega)
      (fun y z x _ h => by
        rw [hevO hop, h, Bool.true_or, (hconst y z).2, zero_dotProduct]; rfl)
    refine ⟨[(W ⊔ Submodule.span F {ℓ s}, DF, tF, Function.update ℓ (2 * k + t + G.length) (ℓ o),
      Function.update d (2 * k + t + G.length) (d o)), (W ⊔ Submodule.span F {ℓ s}, DT, tT,
      Function.update ℓ (2 * k + t + G.length) 0, Function.update d (2 * k + t + G.length) (k + t + 1))], ?_, fun y z φ => ?_⟩
    · intro b hb'; simp at hb'; rcases hb' with rfl | rfl
      · exact hF
      · exact hT
    · rw [hsum DF DT tF tT pF pT y z φ]; simp [pieceT]

theorem step_gate (G : List Gate) (g : Gate) (b : Br k) (hb : GoodT t G b) (hg : shapeOK g) :
    ∃ Lb : List (Br k), (∀ b' ∈ Lb, GoodT t (G ++ [g]) b') ∧
      ∀ y (z : Fin t → F) (φ : (Fin k → F) → ℤ), ∑ x ∈ pieceT b y z, φ x =
        (Lb.map fun b' => ∑ x ∈ pieceT b' y z, φ x).sum := by
  obtain ⟨W, D, tap, ℓ, d⟩ := b
  simp only [GoodT] at hb
  have htp := hb.2.2.2.2.1
  have single : ∀ e : Gate, ∀ lm dm, Good t (G ++ [g]) W (D ++ [e]) tap
      (Function.update ℓ (2 * k + t + G.length) lm) (Function.update d (2 * k + t + G.length) dm) →
      ∃ Lb : List (Br k), (∀ b' ∈ Lb, GoodT t (G ++ [g]) b') ∧
        ∀ y (z : Fin t → F) (φ : (Fin k → F) → ℤ), ∑ x ∈ pieceT (W, D, tap, ℓ, d) y z, φ x =
          (Lb.map fun b' => ∑ x ∈ pieceT b' y z, φ x).sum := by
    intro e lm dm h
    exact ⟨[(W, D ++ [e], tap, _, _)], by simpa [GoodT] using h,
      fun y z φ => by simp [pieceT, pt_app D [e] tap htp]⟩
  obtain ⟨hlen, hop⟩ := hg
  rcases hop with hop | hop | hop | ⟨hop, h1⟩
  · rcases hin : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨l, L⟩⟩⟩
    · exact single _ _ _ (good_ao01 G g W D tap ℓ d hb (Or.inl hop) (by simp [hin]))
    · exact single _ _ _ (good_ao01 G g W D tap ℓ d hb (Or.inl hop) (by simp [hin]))
    · exact step_two G g W D tap ℓ d hb (Or.inl hop) i j hin
    · rw [hin] at hlen; simp at hlen
  · rcases hin : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨l, L⟩⟩⟩
    · exact single _ _ _ (good_ao01 G g W D tap ℓ d hb (Or.inr hop) (by simp [hin]))
    · exact single _ _ _ (good_ao01 G g W D tap ℓ d hb (Or.inr hop) (by simp [hin]))
    · exact step_two G g W D tap ℓ d hb (Or.inr hop) i j hin
    · rw [hin] at hlen; simp at hlen
  · exact single _ _ _ (good_mod G g W D tap ℓ d hb hop hlen)
  · rcases hin : g.inputs with _ | ⟨i, _ | ⟨j, L⟩⟩
    · rw [hin] at h1; simp at h1
    · exact single _ _ _ (good_not G g W D tap ℓ d hb i hop hin)
    · rw [hin] at h1; simp at h1

theorem combine (G G' : List Gate) (L : List (Br k)) (hL : ∀ b ∈ L, GoodT t G b)
    (hstep : ∀ b, GoodT t G b → ∃ Lb : List (Br k), (∀ b' ∈ Lb, GoodT t G' b') ∧
      ∀ y (z : Fin t → F) (φ : (Fin k → F) → ℤ), ∑ x ∈ pieceT b y z, φ x =
        (Lb.map fun b' => ∑ x ∈ pieceT b' y z, φ x).sum) :
    ∃ L' : List (Br k), (∀ b ∈ L', GoodT t G' b) ∧
      ∀ y (z : Fin t → F) (φ : (Fin k → F) → ℤ),
        (L.map fun b => ∑ x ∈ pieceT b y z, φ x).sum =
          (L'.map fun b => ∑ x ∈ pieceT b y z, φ x).sum := by
  induction L with
  | nil => exact ⟨[], by simp, fun _ _ _ => rfl⟩
  | cons b L ih =>
    obtain ⟨Lb, h1, h2⟩ := hstep b (hL b (by simp))
    obtain ⟨L', h3, h4⟩ := ih (fun b' hb' => hL b' (by simp [hb']))
    refine ⟨Lb ++ L', fun b' hb' => ?_, fun y z φ => ?_⟩
    · rcases List.mem_append.1 hb' with h | h
      · exact h1 b' h
      · exact h3 b' h
    · rw [List.map_cons, List.sum_cons, h2 y z φ, h4 y z φ, List.map_append, List.sum_append]

theorem decomp (G : List Gate) (hG : okL (2 * k + t) G) :
    ∃ L : List (Br k), (∀ b ∈ L, GoodT t G b) ∧
      ∀ y (z : Fin t → F) (φ : (Fin k → F) → ℤ), ∑ x, φ x =
        (L.map fun b => ∑ x ∈ pieceT b y z, φ x).sum := by
  induction G using List.reverseRecOn with
  | nil =>
    refine ⟨[(⊥, D0, fun _ => k + t, ℓ0 k, d0 k t)], by simpa [GoodT] using good_init,
      fun y z φ => ?_⟩
    simp [pieceT, piece_bot]
  | append_singleton G g ih =>
    rw [okL_append, okL_single] at hG
    obtain ⟨L, h1, h2⟩ := ih hG.1
    obtain ⟨L', h3, h4⟩ := combine G (G ++ [g]) L h1
      (fun b hb => step_gate G g b hb hG.2.1)
    exact ⟨L', h3, fun y z φ => by rw [h2 y z φ, h4 y z φ]⟩

theorem sum_get {α M : Type*} [AddCommMonoid M] (L : List α) (f : α → M) :
    ∑ i : Fin L.length, f (L.get i) = (L.map f).sum := by
  rw [Fin.sum_univ_def]
  congr 1
  rw [show (List.finRange L.length).map (fun i => f (L.get i)) =
    ((List.finRange L.length).map L.get).map f by rw [List.map_map]; rfl]
  congr 1
  exact List.ext_get (by simp) (by simp)

open Classical in
theorem leaf (C : Circuit) (s : ℕ) (hcost : costL C.gates ≤ s) (b : Br k) (hb : GoodT t C.gates b) :
    ∃ A : (Fin k → F) → (Fin t → F) → ℤ,
      (∃ (W : Submodule F (Fin k → F)) (a : Fin k → F) (D : Circuit) (tap : Fin k → ℕ),
        Module.finrank F W = Module.finrank F b.1 ∧ okL (k + t) D.gates ∧
        costL D.gates + Module.finrank F b.1 ≤ s ∧
        D.output < k + t + D.size ∧ (∀ j, tap j < k + t + D.size) ∧
        ∀ (y : Fin k → F) (z : Fin t → F),
          (y - a ∈ W → A y z = sgn (Bool.xor (D.eval (bits k y ++ bits t z))
            (decide ((fun j => bv ((D.wires (bits k y ++ bits t z)).getD (tap j) false)) ⬝ᵥ y = 1)))) ∧
          (y - a ∉ W → A y z = 0)) ∧
      ∀ (y : Fin k → F) (z : Fin t → F),
        ∑ x ∈ pieceT b y z, sgn (Bool.xor (C.eval (bits k x ++ bits k y ++ bits t z))
          (decide (x ⬝ᵥ y = 1))) = (2 : ℤ) ^ (k - Module.finrank F b.1) * A y z := by
  obtain ⟨W, D, tap, ℓ, d⟩ := b
  obtain ⟨hD, hc, h2, hconst, htp, hd, hr, hcd, hv⟩ := hb
  simp only at hD hc h2 hconst htp hd hr hcd hv ⊢
  have hLo : ∀ l ∈ d C.output :: sel (ℓ C.output) tap, l < k + t + D.length := by
    intro l hl; simp only [List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact hd _
    · exact sel_lt _ _ _ htp l hl
  obtain ⟨Ag, o, hAok, hAc, ho, hAv⟩ := gadget_aff (k := k) (t := t) D false _ hLo
  set a := ℓ C.output
  set Dc : Circuit := ⟨D ++ Ag, o⟩
  have hDv : ∀ (y : Fin k → F) (z : Fin t → F), bv (Dc.eval (bits k y ++ bits t z)) =
      bv ((run D (inD y z)).getD (d C.output) false) + a ⬝ᵥ pt D tap y z := by
    intro y z
    have := hAv y z []
    rw [List.append_nil] at this
    rw [show Dc.eval (bits k y ++ bits t z) = (run (D ++ Ag) (inD y z)).getD o false from rfl, this]
    simp only [List.map_cons, List.sum_cons, sel_val, bv_false, zero_add]
    rfl
  have hpDc : ∀ (y : Fin k → F) (z : Fin t → F),
      (fun j => bv ((Dc.wires (bits k y ++ bits t z)).getD (tap j) false)) = pt D tap y z := by
    intro y z
    exact pt_app D Ag tap htp y z
  refine ⟨fun y z => if y - a ∈ W then sgn (Bool.xor (Dc.eval (bits k y ++ bits t z))
      (decide ((fun j => bv ((Dc.wires (bits k y ++ bits t z)).getD (tap j) false)) ⬝ᵥ y = 1)))
      else 0, ⟨W, a, Dc, tap, rfl, (okL_append _ _ _).2 ⟨hD, hAok⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show costL (D ++ Ag) + _ ≤ s
    rw [costL_append, hAc]; omega
  · show o < k + t + (D ++ Ag).length
    simp; omega
  · intro j; show tap j < k + t + (D ++ Ag).length
    have := htp j; simp; omega
  · intro y z
    exact ⟨fun h => if_pos h, fun h => if_neg h⟩
  · intro y z
    have hya : y - a ∈ W ↔ a + y ∈ W := by
      rw [show y - a = a + y by ext j; simp [F_sub, add_comm]]
    have hsum : ∀ x ∈ piece W (pt D tap y z),
        sgn (Bool.xor (C.eval (bits k x ++ bits k y ++ bits t z)) (decide (x ⬝ᵥ y = 1))) =
          sgF ((a + y) ⬝ᵥ x + bv ((run D (inD y z)).getD (d C.output) false)) := by
      intro x hx
      rw [show C.eval (bits k x ++ bits k y ++ bits t z) = (run C.gates (inC x y z)).getD C.output false
        by simp [Circuit.eval, wires_run, inC, inD], sgn_xor, hv y z x hx, bv_of_dec, add_dotProduct,
        dotProduct_comm x y]
      congr 1; ring
    unfold pieceT
    simp only
    rw [Finset.sum_congr rfl hsum]
    by_cases hW : y - a ∈ W
    · rw [if_pos hW, chsum_mem W _ _ (hya.1 hW) (fun c => sgF (c + _)), hcd y z, sgn_xor,
        hDv y z, hpDc y z, bv_of_dec]
      push_cast
      congr 1
      congr 1
      rw [add_dotProduct, dotProduct_comm y]; ring
    · rw [if_neg hW, chsum_nmem W _ _ (fun h => hW (hya.2 h)), mul_zero]

theorem dir1 (k t s : ℕ) (C : Circuit) (hC : okL (2 * k + t) C.gates) (hcost : costL C.gates ≤ s) :
    ∃ (N : ℕ) (r : Fin N → ℕ) (A : Fin N → (Fin k → F) → (Fin t → F) → ℤ),
      (∀ i, ∃ (W : Submodule F (Fin k → F)) (a : Fin k → F) (D : Circuit) (tap : Fin k → ℕ),
        Module.finrank F W = r i ∧ okL (k + t) D.gates ∧ costL D.gates + r i ≤ s ∧
        D.output < k + t + D.size ∧ (∀ j, tap j < k + t + D.size) ∧
        ∀ (y : Fin k → F) (z : Fin t → F),
          (y - a ∈ W → A i y z = sgn (Bool.xor (D.eval (bits k y ++ bits t z))
            (decide ((fun j => bv ((D.wires (bits k y ++ bits t z)).getD (tap j) false)) ⬝ᵥ y = 1)))) ∧
          (y - a ∉ W → A i y z = 0)) ∧
      (∑ i, 2 ^ (k - r i) : ℕ) = 2 ^ k ∧
      ∀ (y : Fin k → F) (z : Fin t → F),
        (∑ x : Fin k → F, sgn (Bool.xor (C.eval (bits k x ++ bits k y ++ bits t z))
          (decide (x ⬝ᵥ y = 1)))) = ∑ i, (2 : ℤ) ^ (k - r i) * A i y z := by
  obtain ⟨L, hL, hpart⟩ := decomp (k := k) (t := t) C.gates hC
  have hex : ∀ b ∈ L, ∃ A : (Fin k → F) → (Fin t → F) → ℤ,
      (∃ (W : Submodule F (Fin k → F)) (a : Fin k → F) (D : Circuit) (tap : Fin k → ℕ),
        Module.finrank F W = Module.finrank F b.1 ∧ okL (k + t) D.gates ∧
        costL D.gates + Module.finrank F b.1 ≤ s ∧
        D.output < k + t + D.size ∧ (∀ j, tap j < k + t + D.size) ∧
        ∀ (y : Fin k → F) (z : Fin t → F),
          (y - a ∈ W → A y z = sgn (Bool.xor (D.eval (bits k y ++ bits t z))
            (decide ((fun j => bv ((D.wires (bits k y ++ bits t z)).getD (tap j) false)) ⬝ᵥ y = 1)))) ∧
          (y - a ∉ W → A y z = 0)) ∧
      ∀ (y : Fin k → F) (z : Fin t → F),
        ∑ x ∈ pieceT b y z, sgn (Bool.xor (C.eval (bits k x ++ bits k y ++ bits t z))
          (decide (x ⬝ᵥ y = 1))) = (2 : ℤ) ^ (k - Module.finrank F b.1) * A y z :=
    fun b hb => leaf C s hcost b (hL b hb)
  choose! Af hAf1 hAf2 using hex
  refine ⟨L.length, fun i => Module.finrank F (L.get i).1, fun i => Af (L.get i),
    fun i => hAf1 _ (List.get_mem _ _), ?_, fun y z => ?_⟩
  · have h1 := hpart 0 0 (fun _ => 1)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h1
    rw [List.map_congr_left (g := fun b => (((2 ^ (k - Module.finrank F b.1) : ℕ)) : ℤ))
      (fun b hb => by simp only [pieceT]; rw [(hL b hb).2.2.2.2.2.2.2.1 0 0])] at h1
    rw [sum_get L (fun b => 2 ^ (k - Module.finrank F b.1))]
    have h3 : (((L.map fun b => 2 ^ (k - Module.finrank F b.1)).sum : ℕ) : ℤ) = ((2 ^ k : ℕ) : ℤ) := by
      rw [Nat.cast_list_sum, List.map_map, Function.comp_def, ← h1]; simp
    exact_mod_cast h3
  · rw [hpart y z, ← sum_get L]
    exact Finset.sum_congr rfl (fun i _ => hAf2 _ (List.get_mem _ _) y z)

end D1

namespace D2

def shG (k : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (· + k)⟩

def sh (k : ℕ) (G : List Gate) : List Gate := G.map (shG k)

theorem sh_run (k : ℕ) (G : List Gate) (xs w : List Bool) (hxs : xs.length = k) (i : ℕ) :
    (run (sh k G) (xs ++ w)).getD (i + k) false = (run G w).getD i false := by
  induction G using List.reverseRecOn generalizing i with
  | nil =>
    simp only [sh, List.map_nil, run, List.foldl_nil, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    congr 2; omega
  | append_singleton G g ih =>
    have hs : sh k (G ++ [g]) = sh k G ++ [shG k g] := by simp [sh]
    have hl : (sh k G).length = G.length := by simp [sh]
    rw [hs]
    by_cases h : i = w.length + G.length
    · subst h
      have e : w.length + G.length + k = (xs ++ w).length + (sh k G).length := by
        simp [hl, hxs]; omega
      rw [e, getD_run_self, getD_run_self]
      simp only [shG, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      simp only [Function.comp]
      exact ih j
    · rw [getD_run_ne _ _ _ _ (by simp [hl, hxs]; omega), getD_run_ne _ _ _ _ h]
      exact ih i

theorem sh_run_lt (k : ℕ) (G : List Gate) (xs w : List Bool) (hxs : xs.length = k) (i : ℕ)
    (hi : i < k) : (run (sh k G) (xs ++ w)).getD i false = xs.getD i false := by
  rw [getD_run_lt _ _ _ (by simp; omega)]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by omega)]

theorem sh_ok (k n : ℕ) (G : List Gate) (h : okL n G) : okL (n + k) (sh k G) := by
  intro j hj
  simp only [sh, List.length_map] at hj
  have := h j hj
  simp only [sh, List.getElem_map, shG]
  refine ⟨⟨by simpa using this.1.1, by simpa using this.1.2⟩, ?_⟩
  intro i hi
  simp only [List.mem_map] at hi
  obtain ⟨i', hi', rfl⟩ := hi
  have := this.2 i' hi'; omega

theorem sh_cost (k : ℕ) (G : List Gate) : costL (sh k G) = costL G := by
  induction G with
  | nil => rfl
  | cons g G ih =>
    have : sh k (g :: G) = shG k g :: sh k G := rfl
    rw [this, costL_cons, costL_cons, ih]
    have e : cnt (shG k g) ↔ cnt g := by simp [shG, cnt]
    by_cases h : cnt g
    · rw [if_pos h, if_pos (e.2 h)]
    · rw [if_neg h, if_neg (fun h' => h (e.1 h'))]

def Lm {k : ℕ} (m : Fin k → F) (g : Fin k → ℕ) (f0 : ℕ) : List ℕ :=
  List.ofFn (fun j => if m j = 1 then g j else f0)

theorem Lm_length {k : ℕ} (m : Fin k → F) (g : Fin k → ℕ) (f0 : ℕ) : (Lm m g f0).length = k := by
  simp [Lm]

theorem Lm_lt {k : ℕ} (m : Fin k → F) (g : Fin k → ℕ) (f0 b : ℕ) (hg : ∀ j, g j < b)
    (hf : f0 < b) : ∀ l ∈ Lm m g f0, l < b := by
  intro l hl
  simp only [Lm, List.mem_ofFn] at hl
  obtain ⟨j, rfl⟩ := hl
  split <;> simp_all

theorem ite_mul_F (m v : F) : (if m = 1 then v else 0) = m * v := by
  rcases F_cases m with h | h <;> simp [h]

theorem Lm_sum {k : ℕ} (m : Fin k → F) (g : Fin k → ℕ) (f0 : ℕ) (w : List Bool)
    (hf : w.getD f0 false = false) :
    ((Lm m g f0).map fun l => bv (w.getD l false)).sum = ∑ j, m j * bv (w.getD (g j) false) := by
  simp only [Lm, List.map_ofFn, List.sum_ofFn, Function.comp]
  apply Finset.sum_congr rfl
  intro j _
  rw [← ite_mul_F]
  by_cases h : m j = 1
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, hf]; rfl

def blk (cq : Bool) (LQ LS : List ℕ) (st : ℕ) : List Gate :=
  aff cq LQ st ++ aff false LS (st + (2 * LQ.length + 1)) ++
    [⟨.and, [affo LQ st, affo LS (st + (2 * LQ.length + 1))]⟩]

theorem blk_length (cq : Bool) (LQ LS : List ℕ) (st : ℕ) :
    (blk cq LQ LS st).length = 2 * LQ.length + 2 * LS.length + 3 := by
  simp [blk, aff_length]; omega

theorem blk_cost (cq : Bool) (LQ LS : List ℕ) (st : ℕ) : costL (blk cq LQ LS st) = 1 := by
  simp [blk, costL_append, aff_cost, costL_single, cnt]

theorem blk_ok (cq : Bool) (LQ LS : List ℕ) (st : ℕ) (hQ : ∀ l ∈ LQ, l < st)
    (hS : ∀ l ∈ LS, l < st) : okL st (blk cq LQ LS st) := by
  unfold blk
  rw [okL_append, okL_append, okL_single]
  have h1 := affo_lt cq LQ st
  have h2 := affo_lt false LS (st + (2 * LQ.length + 1))
  rw [aff_length] at h1 h2
  refine ⟨⟨aff_ok _ _ _ hQ, ?_⟩, ⟨⟨by simp, by simp⟩, ?_⟩⟩
  · rw [aff_length]
    exact aff_ok _ _ _ (fun l hl => by have := hS l hl; omega)
  · intro i hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    simp only [List.length_append, aff_length]
    rcases hi with rfl | rfl <;> omega

theorem blk_val (cq : Bool) (LQ LS : List ℕ) (w : List Bool) (hQ : ∀ l ∈ LQ, l < w.length)
    (hS : ∀ l ∈ LS, l < w.length) :
    bv ((run (blk cq LQ LS w.length) w).getD (w.length + 2 * LQ.length + 2 * LS.length + 2) false) =
      (bv cq + (LQ.map fun l => bv (w.getD l false)).sum) *
        (LS.map fun l => bv (w.getD l false)).sum := by
  unfold blk
  set A := aff cq LQ w.length
  set w1 := run A w with hw1
  have hl1 : w1.length = w.length + (2 * LQ.length + 1) := by
    rw [hw1, length_run, aff_length]
  set B := aff false LS w1.length with hBd
  have hB : aff false LS (w.length + (2 * LQ.length + 1)) = B := by rw [hBd, hl1]
  have ho : affo LS (w.length + (2 * LQ.length + 1)) = affo LS w1.length := by rw [hl1]
  rw [hB, ho, run_append, run_append]
  set w2 := run B w1 with hw2
  have hl2 : w2.length = w.length + 2 * LQ.length + 2 * LS.length + 2 := by
    rw [hw2, length_run, aff_length, hl1]; ring
  rw [← hl2]
  change bv ((step w2 _).getD w2.length false) = _
  rw [getD_step_self]
  simp only [GateOp.eval, List.map, List.all_cons, List.all_nil, Bool.and_true, id]
  rw [bv_and]
  have hq := affo_lt cq LQ w.length
  rw [aff_length] at hq
  rw [hw2, getD_run_lt _ _ _ (by omega), hw1, aff_val _ _ _ hQ]
  rw [aff_val _ _ _ (fun l hl => by have := hS l hl; omega)]
  simp only [bv_false, zero_add]
  congr 1
  exact congrArg List.sum (List.map_congr_left (fun l hl => by
    rw [getD_run_lt _ _ _ (hS l hl)]))

def blks (cq : ℕ → Bool) (LQ LS : ℕ → List ℕ) (b1 B : ℕ) : ℕ → List Gate
  | 0 => []
  | m + 1 => blks cq LQ LS b1 B m ++ blk (cq m) (LQ m) (LS m) (b1 + m * B)

theorem blks_length (cq : ℕ → Bool) (LQ LS : ℕ → List ℕ) (b1 B : ℕ)
    (hB : ∀ i, 2 * (LQ i).length + 2 * (LS i).length + 3 = B) (m : ℕ) :
    (blks cq LQ LS b1 B m).length = m * B := by
  induction m with
  | zero => simp [blks]
  | succ m ih => simp [blks, ih, blk_length, hB]; ring

theorem blks_cost (cq : ℕ → Bool) (LQ LS : ℕ → List ℕ) (b1 B : ℕ) (m : ℕ) :
    costL (blks cq LQ LS b1 B m) = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [blks, costL_append, ih, blk_cost]

theorem blks_ok (cq : ℕ → Bool) (LQ LS : ℕ → List ℕ) (b1 B : ℕ)
    (hB : ∀ i, 2 * (LQ i).length + 2 * (LS i).length + 3 = B)
    (hQ : ∀ i, ∀ l ∈ LQ i, l < b1) (hS : ∀ i, ∀ l ∈ LS i, l < b1) (m : ℕ) :
    okL b1 (blks cq LQ LS b1 B m) := by
  induction m with
  | zero => exact okL_nil _
  | succ m ih =>
    simp only [blks]
    rw [okL_append, blks_length _ _ _ _ _ hB]
    exact ⟨ih, blk_ok _ _ _ _ (fun l hl => by have := hQ m l hl; omega)
      (fun l hl => by have := hS m l hl; omega)⟩

theorem blks_val (cq : ℕ → Bool) (LQ LS : ℕ → List ℕ) (B : ℕ) (w : List Bool)
    (hB : ∀ i, 2 * (LQ i).length + 2 * (LS i).length + 3 = B)
    (hQ : ∀ i, ∀ l ∈ LQ i, l < w.length) (hS : ∀ i, ∀ l ∈ LS i, l < w.length) (m : ℕ) :
    ∀ i < m, bv ((run (blks cq LQ LS w.length B m) w).getD (w.length + i * B + (B - 1)) false) =
      (bv (cq i) + ((LQ i).map fun l => bv (w.getD l false)).sum) *
        ((LS i).map fun l => bv (w.getD l false)).sum := by
  induction m with
  | zero => intro i hi; omega
  | succ m ih =>
    intro i hi
    have hB3 : 3 ≤ B := by have := hB 0; omega
    simp only [blks]
    rw [run_append]
    set w' := run (blks cq LQ LS w.length B m) w with hw'
    have hl : w'.length = w.length + m * B := by
      rw [hw', length_run, blks_length _ _ _ _ _ hB]
    rcases Nat.lt_or_ge i m with h | h
    · have : i * B + B ≤ m * B := by nlinarith
      rw [getD_run_lt _ _ _ (by omega), hw', ih i h]
    · have him : i = m := by omega
      subst him
      have e1 : w.length + i * B = w'.length := hl.symm
      have e2 : w'.length + (B - 1) =
          w'.length + 2 * (LQ i).length + 2 * (LS i).length + 2 := by
        have := hB i; omega
      rw [e1, e2, blk_val _ _ _ _ (fun l hl' => by have := hQ i l hl'; omega)
        (fun l hl' => by have := hS i l hl'; omega)]
      have es : ∀ L : List ℕ, (∀ l ∈ L, l < w.length) →
          (L.map fun l => bv (w'.getD l false)).sum = (L.map fun l => bv (w.getD l false)).sum :=
        fun L hL => congrArg List.sum (List.map_congr_left (fun l hl' => by
          rw [hw', getD_run_lt _ _ _ (hL l hl')]))
      rw [es _ (hQ i), es _ (hS i)]

def Lout {k : ℕ} (r B b1 o : ℕ) (a : Fin k → F) (tap : Fin k → ℕ) (f0 : ℕ) : List ℕ :=
  [o + k] ++ (Lm a (fun j => j.val) f0 ++ Lm a (fun j => tap j + k) f0) ++
    List.ofFn (fun i : Fin r => b1 + i.val * B + (B - 1))

def LQ {k : ℕ} (mq : ℕ → Fin k → F) (f0 : ℕ) (i : ℕ) : List ℕ :=
  Lm (mq i) (fun j => k + j.val) f0

def LS {k : ℕ} (wn : ℕ → Fin k → F) (tap : Fin k → ℕ) (f0 : ℕ) (i : ℕ) : List ℕ :=
  Lm (wn i) (fun j => j.val) f0 ++ Lm (wn i) (fun j => tap j + k) f0

def Cg (k t r : ℕ) (D : Circuit) (tap : Fin k → ℕ) (a : Fin k → F) (cn : ℕ → F)
    (mq wn : ℕ → Fin k → F) : Circuit :=
  let b0 := 2 * k + t + D.size
  let B := 6 * k + 3
  ⟨sh k D.gates ++ ([⟨.or, []⟩] ++ (blks (fun i => decide (cn i = 1)) (LQ mq b0) (LS wn tap b0)
      (b0 + 1) B r ++ aff false (Lout r B (b0 + 1) D.output a tap b0) (b0 + 1 + r * B))),
    affo (Lout r B (b0 + 1) D.output a tap b0) (b0 + 1 + r * B)⟩

theorem hB_ok {k : ℕ} (mq wn : ℕ → Fin k → F) (tap : Fin k → ℕ) (f0 : ℕ) (i : ℕ) :
    2 * (LQ mq f0 i).length + 2 * (LS wn tap f0 i).length + 3 = 6 * k + 3 := by
  simp [LQ, LS, Lm_length]; ring

theorem LQ_lt {k t : ℕ} (mq : ℕ → Fin k → F) (b0 : ℕ) (hb : 2 * k + t ≤ b0) (i : ℕ) :
    ∀ l ∈ LQ mq b0 i, l < b0 + 1 :=
  Lm_lt _ _ _ _ (fun j => by have := j.isLt; omega) (by omega)

theorem LS_lt {k t : ℕ} (D : Circuit) (wn : ℕ → Fin k → F) (tap : Fin k → ℕ)
    (htap : ∀ j, tap j < k + t + D.size) (i : ℕ) :
    ∀ l ∈ LS wn tap (2 * k + t + D.size) i, l < 2 * k + t + D.size + 1 := by
  intro l hl
  simp only [LS, List.mem_append] at hl
  rcases hl with hl | hl
  · exact Lm_lt _ _ _ _ (fun j => by have := j.isLt; omega) (by omega) l hl
  · exact Lm_lt _ _ _ _ (fun j => by have := htap j; omega) (by omega) l hl

theorem Lout_lt {k t r : ℕ} (D : Circuit) (a : Fin k → F) (tap : Fin k → ℕ)
    (htap : ∀ j, tap j < k + t + D.size) (hout : D.output < k + t + D.size) :
    ∀ l ∈ Lout r (6 * k + 3) (2 * k + t + D.size + 1) D.output a tap (2 * k + t + D.size),
      l < 2 * k + t + D.size + 1 + r * (6 * k + 3) := by
  intro l hl
  simp only [Lout, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl with (rfl | hl | hl) | hl
  · omega
  · have := Lm_lt _ _ _ (2 * k + t + D.size + 1) (fun j => by have := j.isLt; omega) (by omega) l hl
    omega
  · have := Lm_lt _ _ _ (2 * k + t + D.size + 1) (fun j => by have := htap j; omega)
      (by omega) l hl
    omega
  · simp only [List.mem_ofFn] at hl
    obtain ⟨i, rfl⟩ := hl
    have := i.isLt
    have : (i.val + 1) * (6 * k + 3) ≤ r * (6 * k + 3) := Nat.mul_le_mul_right _ (by omega)
    rw [add_mul, one_mul] at this
    generalize i.val * (6 * k + 3) = P at this ⊢
    generalize r * (6 * k + 3) = Q at this ⊢
    omega

theorem Cg_ok (k t r : ℕ) (D : Circuit) (tap : Fin k → ℕ) (a : Fin k → F) (cn : ℕ → F)
    (mq wn : ℕ → Fin k → F) (hD : okL (k + t) D.gates)
    (hout : D.output < k + t + D.size) (htap : ∀ j, tap j < k + t + D.size) :
    okL (2 * k + t) (Cg k t r D tap a cn mq wn).gates := by
  simp only [Cg]
  rw [okL_append, okL_append, okL_append, okL_single]
  have hsl : (sh k D.gates).length = D.size := by simp [sh, Circuit.size]
  refine ⟨by rw [show 2 * k + t = k + t + k by omega]; exact sh_ok k _ _ hD,
    ⟨⟨by simp, by simp⟩, by simp⟩, ?_, ?_⟩
  · rw [hsl, List.length_singleton]
    exact blks_ok _ _ _ _ _ (hB_ok mq wn tap _) (LQ_lt (t := t) mq _ (by omega))
      (LS_lt D wn tap htap) r
  · rw [hsl, blks_length _ _ _ _ _ (hB_ok mq wn tap _)]
    simp only [List.length_cons, List.length_nil]
    rw [show 2 * k + t + D.size + (0 + 1) + r * (6 * k + 3) =
      2 * k + t + D.size + 1 + r * (6 * k + 3) by omega]
    exact aff_ok _ _ _ (Lout_lt D a tap htap hout)

theorem Cg_cost (k t r : ℕ) (D : Circuit) (tap : Fin k → ℕ) (a : Fin k → F) (cn : ℕ → F)
    (mq wn : ℕ → Fin k → F) : costL (Cg k t r D tap a cn mq wn).gates = costL D.gates + r := by
  simp only [Cg]
  rw [costL_append, costL_append, costL_append, sh_cost, blks_cost, aff_cost, costL_single]
  simp [cnt]

theorem Cg_val (k t r : ℕ) (D : Circuit) (tap : Fin k → ℕ) (a : Fin k → F) (cn : ℕ → F)
    (mq wn : ℕ → Fin k → F) (hout : D.output < k + t + D.size)
    (htap : ∀ j, tap j < k + t + D.size) (x y : Fin k → F) (z : Fin t → F) :
    bv ((Cg k t r D tap a cn mq wn).eval (bits k x ++ bits k y ++ bits t z)) =
      bv (D.eval (bits k y ++ bits t z)) +
        (a ⬝ᵥ x + a ⬝ᵥ (fun j => bv ((D.wires (bits k y ++ bits t z)).getD (tap j) false))) +
        ∑ i : Fin r, (cn i + mq i ⬝ᵥ y) * (wn i ⬝ᵥ x +
          wn i ⬝ᵥ (fun j => bv ((D.wires (bits k y ++ bits t z)).getD (tap j) false))) := by
  set YZ := bits k y ++ bits t z with hYZ
  have hYZl : YZ.length = k + t := by simp [hYZ, length_bits]
  set b0 := 2 * k + t + D.size with hb0
  set B := 6 * k + 3 with hBd
  rw [List.append_assoc, ← hYZ]
  unfold Cg Circuit.eval
  rw [wires_run]
  simp only []
  rw [run_append, run_append, run_append]
  set w0 := run (sh k D.gates) (bits k x ++ YZ) with hw0
  have hl0 : w0.length = b0 := by
    rw [hw0, length_run]; simp [sh, length_bits, hYZl, hb0, Circuit.size]; omega
  set w1 := run [⟨.or, []⟩] w0 with hw1
  have hw1' : w1 = step w0 ⟨.or, []⟩ := rfl
  have hl1 : w1.length = b0 + 1 := by rw [hw1', length_step, hl0]
  set cq : ℕ → Bool := fun i => decide (cn i = 1) with hcq
  have hb := blks_val cq (LQ mq b0) (LS wn tap b0) B w1 (hB_ok mq wn tap b0)
    (fun i l hl => by rw [hl1]; exact LQ_lt (t := t) mq b0 (by omega) i l hl)
    (fun i l hl => by rw [hl1]; exact LS_lt D wn tap htap i l hl) r
  rw [hl1] at hb
  set w2 := run (blks cq (LQ mq b0) (LS wn tap b0) (b0 + 1) B r) w1 with hw2
  have hl2 : w2.length = b0 + 1 + r * B := by
    rw [hw2, length_run, blks_length _ _ _ _ _ (hB_ok mq wn tap b0), hl1]
  rw [← hl2, aff_val _ _ _ (by rw [hl2]; exact Lout_lt D a tap htap hout)]

  have v1 : ∀ l, l < b0 + 1 → w2.getD l false = w1.getD l false := fun l hl => by
    rw [hw2, getD_run_lt _ _ _ (by omega)]
  have v0 : ∀ l, l < b0 → w1.getD l false = w0.getD l false := fun l hl => by
    rw [hw1', getD_step_ne _ _ _ (by omega)]
  have vf : w1.getD b0 false = false := by
    rw [hw1', ← hl0, getD_step_self]; rfl
  have vf2 : w2.getD b0 false = false := by rw [v1 _ (by omega), vf]
  have vx : ∀ j : Fin k, bv (w0.getD j false) = x j := fun j => by
    rw [hw0, sh_run_lt _ _ _ _ (length_bits k x) _ j.isLt, getD_bits]
  have vD : ∀ i, w0.getD (i + k) false = (run D.gates YZ).getD i false := fun i => by
    rw [hw0, sh_run _ _ _ _ (length_bits k x)]
  have vy : ∀ j : Fin k, bv ((run D.gates YZ).getD j false) = y j := fun j => by
    rw [getD_run_lt _ _ _ (by rw [hYZl]; omega), hYZ]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by rw [length_bits]; exact j.isLt)]
    have := getD_bits k y j
    simpa only [List.getD_eq_getElem?_getD] using this
  have hx2 : ∀ j : Fin k, bv (w2.getD j false) = x j := fun j => by
    rw [v1 _ (by omega), v0 _ (by omega), vx]
  have hp2 : ∀ j : Fin k, w2.getD (tap j + k) false = (D.wires YZ).getD (tap j) false :=
    fun j => by
      have := htap j
      rw [v1 _ (by omega), v0 _ (by omega), vD]; rfl
  have hp1 : ∀ j : Fin k, w1.getD (tap j + k) false = (D.wires YZ).getD (tap j) false :=
    fun j => by
      have := htap j
      rw [v0 _ (by omega), vD]; rfl
  have hx1 : ∀ j : Fin k, bv (w1.getD j false) = x j := fun j => by
    rw [v0 _ (by omega), vx]
  have hy1 : ∀ j : Fin k, bv (w1.getD (k + j) false) = y j := fun j => by
    rw [v0 _ (by omega), add_comm, vD, vy]
  have ho2 : w2.getD (D.output + k) false = (D.wires YZ).getD D.output false := by
    rw [v1 _ (by omega), v0 _ (by omega), vD]; rfl
  simp only [Lout, List.map_append, List.sum_append, List.map_cons, List.sum_cons, List.map_nil,
    List.sum_nil, List.map_ofFn, List.sum_ofFn, Function.comp, add_zero, bv_false, zero_add]
  rw [Lm_sum _ _ _ _ vf2, Lm_sum _ _ _ _ vf2, ho2]
  have e1 : ∑ j : Fin k, a j * bv (w2.getD j false) = a ⬝ᵥ x :=
    Finset.sum_congr rfl (fun j _ => by rw [hx2])
  have e2 : ∑ j : Fin k, a j * bv (w2.getD (tap j + k) false) =
      a ⬝ᵥ (fun j => bv ((D.wires YZ).getD (tap j) false)) :=
    Finset.sum_congr rfl (fun j _ => by rw [hp2])
  rw [e1, e2]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [hb i i.isLt]
    simp only [LQ, LS, List.map_append, List.sum_append]
    rw [Lm_sum _ _ _ _ vf, Lm_sum _ _ _ _ vf, Lm_sum _ _ _ _ vf, hcq, bv_of_dec]
    congr 2
    · exact Finset.sum_congr rfl (fun j _ => by rw [hy1])
    · exact Finset.sum_congr rfl (fun j _ => by rw [hx1])
    · exact Finset.sum_congr rfl (fun j _ => by rw [hp1])

theorem V_add_self {k : ℕ} (u : Fin k → F) : u + u = 0 := by ext j; exact F_add_self _

theorem char_univ (k : ℕ) (c : Fin k → F) :
    ∑ x : Fin k → F, sgF (x ⬝ᵥ c) = if c = 0 then (2 : ℤ) ^ k else 0 := by
  by_cases hc : c = 0
  · subst hc
    simp [sgF, Finset.card_univ, Fintype.card_fun, ZMod.card]
  · rw [if_neg hc]
    obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
      by_contra h; push_neg at h; exact hc (funext h)
    have hj1 : c j = 1 := by rcases F_cases (c j) with h | h; exact absurd h hj; exact h
    set e : Fin k → F := Pi.single j 1
    have he : e ⬝ᵥ c = 1 := by simp [e, single_dotProduct, hj1]
    refine Finset.sum_involution (fun x _ => x + e) (fun x _ => ?_) (fun x _ _ => ?_)
      (fun x _ => Finset.mem_univ _) (fun x _ => ?_)
    · rw [add_dotProduct, he, add_comm (x ⬝ᵥ c), sgF_one_add]; ring
    · intro h
      have := congrFun h j
      simp [e] at this
    · rw [add_assoc, V_add_self, add_zero]

theorem key3 : ∀ u v w : F, u + v + w = 0 → v = w + u := by decide

open Classical in
theorem dir2 (k t s r : ℕ) (W : Submodule F (Fin k → F)) (a : Fin k → F) (D : Circuit)
    (tap : Fin k → ℕ)
    (hr : Module.finrank F W = r) (hD : okL (k + t) D.gates) (hcost : costL D.gates + r ≤ s)
    (hout : D.output < k + t + D.size) (htap : ∀ j, tap j < k + t + D.size) :
    ∃ C : Circuit, okL (2 * k + t) C.gates ∧ costL C.gates ≤ s ∧
      ∀ (y : Fin k → F) (z : Fin t → F),
        (∑ x : Fin k → F, sgn (Bool.xor (C.eval (bits k x ++ bits k y ++ bits t z))
          (decide (x ⬝ᵥ y = 1)))) =
          (2 : ℤ) ^ k * (if y - a ∈ W then
            sgn (Bool.xor (D.eval (bits k y ++ bits t z))
              (decide ((fun j => bv ((D.wires (bits k y ++ bits t z)).getD (tap j) false)) ⬝ᵥ y = 1)))
            else 0) := by
  obtain ⟨Wc, hWc⟩ := W.exists_isCompl
  set π := W.projectionOnto Wc hWc with hπd
  set bW := Module.finBasisOfFinrankEq F W hr
  set φ : Fin r → (Fin k → F) →ₗ[F] F := fun i => (bW.coord i).comp π with hφ
  have hπ : ∀ v, ((π v : W) : Fin k → F) = ∑ i, φ i v • (bW i : Fin k → F) := by
    intro v
    conv_lhs => rw [← bW.sum_repr (π v)]
    rw [Submodule.coe_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [hφ, Module.Basis.coord_apply]
  set cn : ℕ → F := fun i => if h : i < r then φ ⟨i, h⟩ a else 0 with hcn
  set mq : ℕ → Fin k → F := fun i => if h : i < r then (fun j => φ ⟨i, h⟩ (Pi.single j 1)) else 0
    with hmq
  set wn : ℕ → Fin k → F := fun i => if h : i < r then (bW ⟨i, h⟩ : Fin k → F) else 0 with hwn
  refine ⟨Cg k t r D tap a cn mq wn, Cg_ok k t r D tap a cn mq wn hD hout htap,
    by rw [Cg_cost]; exact hcost, ?_⟩
  intro y z
  set p : Fin k → F := fun j => bv ((D.wires (bits k y ++ bits t z)).getD (tap j) false) with hp
  set hD' := bv (D.eval (bits k y ++ bits t z))
  set q : Fin k → F := a + ((π (y + a) : W) : Fin k → F) with hq
  have hv : ∀ x, bv ((Cg k t r D tap a cn mq wn).eval (bits k x ++ bits k y ++ bits t z)) =
      hD' + q ⬝ᵥ (x + p) := by
    intro x
    rw [Cg_val k t r D tap a cn mq wn hout htap x y z]
    have ecn : ∀ i : Fin r, cn i = φ i a := fun i => dite_cond_eq_true (eq_true i.isLt)
    have emq : ∀ i : Fin r, mq i ⬝ᵥ y = φ i y := fun i => by
      rw [show mq i = fun j => φ i (Pi.single j 1) from dite_cond_eq_true (eq_true i.isLt), dotProduct_comm,
        ← lin_dot]
    have ewn : ∀ i : Fin r, wn i = (bW i : Fin k → F) := fun i => dite_cond_eq_true (eq_true i.isLt)
    simp only [ecn, emq, ewn]
    rw [hq, hπ, add_dotProduct, dotProduct_comm (∑ i, _), dotProduct_sum]
    simp only [dotProduct_smul, smul_eq_mul, map_add, dotProduct_add]
    rw [add_assoc]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    rw [add_comm ((φ i) a) ((φ i) y), dotProduct_comm (x + p), dotProduct_add]
  have hsum : ∀ x : Fin k → F, sgn (Bool.xor ((Cg k t r D tap a cn mq wn).eval
      (bits k x ++ bits k y ++ bits t z)) (decide (x ⬝ᵥ y = 1))) =
      sgF (hD' + q ⬝ᵥ p) * sgF (x ⬝ᵥ (q + y)) := by
    intro x
    rw [sgn_xor, hv, bv_of_dec, ← sgF_add]
    congr 1
    rw [dotProduct_add, dotProduct_add, dotProduct_comm q x]
    ring
  rw [Finset.sum_congr rfl (fun x _ => hsum x), ← Finset.mul_sum, char_univ]
  have ya : y - a = y + a := by ext j; exact F_sub _ _
  rw [ya]
  by_cases hW : y + a ∈ W
  · have hpi : ((π (y + a) : W) : Fin k → F) = y + a := by
      have := Submodule.projectionOnto_apply_left hWc ⟨y + a, hW⟩
      rw [hπd]; exact congrArg Subtype.val this
    have hqy : q = y := by
      rw [hq, hpi, add_comm y a, ← add_assoc, V_add_self, zero_add]
    rw [hqy, V_add_self, if_pos rfl, if_pos hW, sgn_xor, bv_of_dec, dotProduct_comm y p]
    ring
  · rw [if_neg hW, mul_zero, if_neg, mul_zero]
    intro h
    apply hW
    have : ((π (y + a) : W) : Fin k → F) = y + a := by
      ext j
      have := congrFun h j
      simp only [hq, Pi.add_apply, Pi.zero_apply] at this
      exact key3 _ _ _ this
    rw [← this]
    exact (π (y + a)).2

end D2

end PEqualNP.Outside.L_lib_844_aux

theorem PEqualNP.Outside.L_lib_844 : (∀ (k t : ℕ),
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let F := ZMod 2
  let legal := fun (n : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
      (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
        (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))
  let cost := fun (C : Circ) => C.gates.countP (fun h => @decide
    ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))
  let bits := fun (n : ℕ) (u : Fin n → F) => List.ofFn (fun j : Fin n => decide (u j = 1))
  let V := Fin k → F
  let Z := Fin t → F
  let sign := fun (b : Bool) => if b then (-1 : ℤ) else 1
  let prof := fun (C : Circ) (y : V) (z : Z) =>
    ∑ x : V, sign (Bool.xor (C.eval (bits k x ++ bits k y ++ bits t z)) (decide (dotProduct x y = 1)))
  ∀ s : ℕ,
    let atom := fun (r : ℕ) (A : V → Z → ℤ) =>
      ∃ (W : Submodule F V) (a : V) (D : Circ) (tap : Fin k → ℕ),
        Module.finrank F W = r ∧ legal (k+t) D ∧ cost D + r ≤ s ∧
        D.output < k+t+D.size ∧ (∀ j, tap j < k+t+D.size) ∧
        ∀ (y : V) (z : Z),
          let inp := bits k y ++ bits t z
          let p := fun j : Fin k => if (D.wires inp).getD (tap j) false then (1 : F) else 0
          (y-a ∈ W → A y z = sign (Bool.xor (D.eval inp) (decide (dotProduct p y = 1)))) ∧
            (y-a ∉ W → A y z = 0)
    (∀ C : Circ, legal (2*k+t) C → cost C ≤ s →
      ∃ (N : ℕ) (r : Fin N → ℕ) (A : Fin N → V → Z → ℤ),
        (∀ i, atom (r i) (A i)) ∧ (∑ i, 2^(k-r i) : ℕ) = 2^k ∧
        ∀ y z, prof C y z = ∑ i, (2 : ℤ)^(k-r i) * A i y z) ∧
    (∀ (r : ℕ) (A : V → Z → ℤ), atom r A →
      ∃ C : Circ, legal (2*k+t) C ∧ cost C ≤ s ∧
        ∀ y z, prof C y z = (2 : ℤ)^k * A y z)) := by
  intro k t Circ F legal cost bits V Z sign prof s atom
  refine ⟨fun C hC hc => ?_, fun r A hA => ?_⟩
  · obtain ⟨N, r, A, h1, h2, h3⟩ :=
      PEqualNP.Outside.L_lib_844_aux.D1.dir1 k t s C
        ((PEqualNP.Outside.L_lib_844_aux.legal_iff _ _).1 hC) hc
    refine ⟨N, r, A, fun i => ?_, h2, fun y z => h3 y z⟩
    obtain ⟨W, a, D, tap, hW, hD, hcost, hout, htap, hA⟩ := h1 i
    exact ⟨W, a, D, tap, hW, (PEqualNP.Outside.L_lib_844_aux.legal_iff _ _).2 hD, hcost, hout, htap,
      fun y z => hA y z⟩
  · obtain ⟨W, a, D, tap, hW, hD, hcost, hout, htap, hA⟩ := hA
    obtain ⟨C, hC, hc, hp⟩ := PEqualNP.Outside.L_lib_844_aux.D2.dir2 k t s r W a D tap hW
      ((PEqualNP.Outside.L_lib_844_aux.legal_iff _ _).1 hD) hcost hout htap
    refine ⟨C, (PEqualNP.Outside.L_lib_844_aux.legal_iff _ _).2 hC, hc, fun y z => ?_⟩
    have hp' := hp y z
    by_cases hy : y - a ∈ W
    · rw [if_pos hy] at hp'
      rw [(hA y z).1 hy]
      exact hp'
    · rw [if_neg hy] at hp'
      rw [(hA y z).2 hy]
      exact hp'
