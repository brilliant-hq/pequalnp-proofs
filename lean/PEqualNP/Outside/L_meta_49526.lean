import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49526

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket
open scoped BigOperators

/-! ### Part 1: Fan-in-two ReadsBack Circuit Framework with `(mono, nots)` Cost -/

abbrev Sig (n : ℕ) := Finset (Fin n) → Bool

def inputOf {n : ℕ} (x : Finset (Fin n)) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]

lemma inputOf_length {n : ℕ} (x : Finset (Fin n)) : (inputOf x).length = n + 2 := by
  simp [inputOf]

def isNotOp : GateOp → Bool
  | GateOp.not => true
  | _ => false

def monoCount (C : Circuit) : ℕ :=
  (C.gates.filter fun g => !isNotOp g.op).length

lemma notCount_eq_filter_isNotOp (C : Circuit) :
    notCount C = (C.gates.filter fun g => isNotOp g.op).length := by
  unfold notCount
  congr 1
  induction C.gates with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.filter_cons, ih]
    cases g.op <;> rfl

lemma notCount_add_monoCount (C : Circuit) : notCount C + monoCount C = C.size := by
  rw [notCount_eq_filter_isNotOp]
  unfold monoCount Circuit.size
  induction C.gates with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.filter_cons, List.length_cons]
    cases isNotOp g.op <;> simp [← ih] <;> omega

lemma monoCount_eq_size_sub_notCount (C : Circuit) : monoCount C = C.size - notCount C := by
  have h := notCount_add_monoCount C
  omega

lemma notCount_snoc (C : Circuit) (g : Gate) :
    notCount ⟨C.gates ++ [g], 0⟩ = notCount C + if isNotOp g.op then 1 else 0 := by
  rw [notCount_eq_filter_isNotOp, notCount_eq_filter_isNotOp]
  simp only [List.filter_append, List.length_append]
  rcases g with ⟨op, ins⟩
  cases op <;> rfl

lemma monoCount_snoc (C : Circuit) (g : Gate) :
    monoCount ⟨C.gates ++ [g], 0⟩ = monoCount C + if isNotOp g.op then 0 else 1 := by
  unfold monoCount
  simp only [List.filter_append, List.length_append]
  rcases g with ⟨op, ins⟩
  cases op <;> rfl

def HasWire {n : ℕ} (C : Circuit) (f : Sig n) : Prop :=
  ∃ w : Fin (n + 2 + C.size), ∀ x : Finset (Fin n),
    (C.wires (inputOf x)).getD w.val false = f x

def Extends (n : ℕ) (S T : Set (Sig n)) (mono nots : ℕ) : Prop :=
  ∀ (C : Circuit), FanInTwo C → ReadsBack (n + 2) C → (∀ f ∈ S, HasWire C f) →
    ∃ (C' : Circuit), FanInTwo C' ∧ ReadsBack (n + 2) C' ∧
      monoCount C' ≤ monoCount C + mono ∧
      notCount C' ≤ notCount C + nots ∧
      (∀ f : Sig n, HasWire C f → HasWire C' f) ∧
      (∀ f ∈ T, HasWire C' f)

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  unfold Circuit.wires
  induction C.gates generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp only [List.length_append, List.length_singleton]
    omega

lemma wires_append (gs₁ gs₂ : List Gate) (x : List Bool) :
    (Circuit.mk (gs₁ ++ gs₂) 0).wires x =
      (Circuit.mk gs₂ 0).wires ((Circuit.mk gs₁ 0).wires x) := by
  unfold Circuit.wires
  simp [List.foldl_append]

lemma wires_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    (Circuit.mk (gs ++ [g]) 0).wires x =
      (Circuit.mk gs 0).wires x ++
        [g.op.eval (g.inputs.map fun i => ((Circuit.mk gs 0).wires x).getD i false)] := by
  rw [wires_append]
  simp [Circuit.wires]

lemma getD_append_left_lt {α : Type*} (l₁ l₂ : List α) (i : ℕ) (d : α) (h : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp [List.getD, List.getElem?_append_left h]

lemma getD_append_right_eq {α : Type*} (l₁ : List α) (a : α) (d : α) :
    (l₁ ++ [a]).getD l₁.length d = a := by
  simp [List.getD]

lemma push_gate {n : ℕ} (C : Circuit) (hFan : FanInTwo C) (hBack : ReadsBack (n + 2) C)
    (g : Gate)
    (hgFan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hgBack : ∀ i ∈ g.inputs, i < n + 2 + C.size) :
    let C' : Circuit := ⟨C.gates ++ [g], 0⟩
    FanInTwo C' ∧ ReadsBack (n + 2) C' ∧
      monoCount C' = monoCount C + (if isNotOp g.op then 0 else 1) ∧
      notCount C' = notCount C + (if isNotOp g.op then 1 else 0) ∧
      (∀ f : Sig n, HasWire C f → HasWire C' f) ∧
      (∀ x : Finset (Fin n),
        (C'.wires (inputOf x)).getD (n + 2 + C.size) false =
          g.op.eval (g.inputs.map fun i => (C.wires (inputOf x)).getD i false)) := by
  intro C'
  have hsize : C'.size = C.size + 1 := by simp [C', Circuit.size]
  have hFan' : FanInTwo C' := by
    intro g' hg'
    simp only [C', List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · exact hFan g' hg'
    · exact hgFan
  have hBack' : ReadsBack (n + 2) C' := by
    intro j hj i hi
    simp only [C', List.length_append, List.length_singleton] at hj
    by_cases hlt : j < C.gates.length
    · have hget : gateAt C' j = gateAt C j := by
        unfold gateAt
        exact getD_append_left_lt C.gates [g] j _ hlt
      rw [hget] at hi
      exact hBack j hlt i hi
    · have hjeq : j = C.gates.length := by omega
      subst hjeq
      have hget : gateAt C' C.gates.length = g := by
        unfold gateAt
        exact getD_append_right_eq C.gates g _
      rw [hget] at hi
      exact hgBack i hi
  have hkeep : ∀ f : Sig n, HasWire C f → HasWire C' f := by
    rintro f ⟨w, hw⟩
    refine ⟨⟨w.val, by rw [hsize]; omega⟩, fun x => ?_⟩
    have hlen : (C.wires (inputOf x)).length = n + 2 + C.size := by
      rw [wires_length, inputOf_length]; rfl
    have hCeq : (Circuit.mk C.gates 0).wires (inputOf x) = C.wires (inputOf x) := rfl
    change ((Circuit.mk (C.gates ++ [g]) 0).wires (inputOf x)).getD w.val false = f x
    rw [wires_snoc, hCeq, getD_append_left_lt _ _ _ _ (by omega)]
    exact hw x
  have hnew : ∀ x : Finset (Fin n),
      (C'.wires (inputOf x)).getD (n + 2 + C.size) false =
        g.op.eval (g.inputs.map fun i => (C.wires (inputOf x)).getD i false) := by
    intro x
    have hlen : (C.wires (inputOf x)).length = n + 2 + C.size := by
      rw [wires_length, inputOf_length]; rfl
    have hCeq : (Circuit.mk C.gates 0).wires (inputOf x) = C.wires (inputOf x) := rfl
    change ((Circuit.mk (C.gates ++ [g]) 0).wires (inputOf x)).getD (n + 2 + C.size) false = _
    rw [wires_snoc, hCeq, ← hlen, getD_append_right_eq]
  exact ⟨hFan', hBack', monoCount_snoc C g, notCount_snoc C g, hkeep, hnew⟩

def baseSigs (n : ℕ) : Set (Sig n) :=
  {fun _ => false, fun _ => true} ∪ Set.range (fun i : Fin n => fun x => decide (i ∈ x))

lemma base_circuit (n : ℕ) :
    let C0 : Circuit := ⟨[], 0⟩
    FanInTwo C0 ∧ ReadsBack (n + 2) C0 ∧ monoCount C0 = 0 ∧ notCount C0 = 0 ∧
      ∀ f ∈ baseSigs n, HasWire C0 f := by
  refine ⟨?_, ?_, rfl, rfl, ?_⟩
  · intro g hg; simp at hg
  · intro j hj; simp at hj
  · rintro f ((rfl | rfl) | ⟨i, rfl⟩)
    · refine ⟨⟨n, by simp [Circuit.size]⟩, fun x => ?_⟩
      simp [Circuit.wires, inputOf, List.getD]
    · refine ⟨⟨n + 1, by simp [Circuit.size]⟩, fun x => ?_⟩
      simp [Circuit.wires, inputOf, List.getD]
    · refine ⟨⟨i.val, by simp [Circuit.size]; omega⟩, fun x => ?_⟩
      have hlt : i.val < (List.ofFn (fun k : Fin n => decide (k ∈ x))).length := by simp
      simp only [Circuit.wires, List.foldl_nil, inputOf]
      rw [getD_append_left_lt _ _ _ _ hlt]
      simp [List.getD, i.isLt]

lemma Extends.of_subset {n : ℕ} {S T : Set (Sig n)} (h : T ⊆ S) : Extends n S T 0 0 := by
  intro C hF hB hS
  exact ⟨C, hF, hB, by omega, by omega, fun _ hw => hw, fun f hf => hS f (h hf)⟩

lemma Extends.mono {n : ℕ} {S S' T T' : Set (Sig n)} {cm cm' cn cn' : ℕ}
    (hS : S ⊆ S') (hT : T' ⊆ T) (hcm : cm ≤ cm') (hcn : cn ≤ cn') (h : Extends n S T cm cn) :
    Extends n S' T' cm' cn' := by
  intro C hF hB hW
  obtain ⟨C', hF', hB', hm, hn, hkeep, hT'⟩ := h C hF hB (fun f hf => hW f (hS hf))
  exact ⟨C', hF', hB', by omega, by omega, hkeep, fun f hf => hT' f (hT hf)⟩

lemma Extends.trans {n : ℕ} {S T₁ T₂ : Set (Sig n)} {cm₁ cn₁ cm₂ cn₂ : ℕ}
    (h₁ : Extends n S T₁ cm₁ cn₁) (h₂ : Extends n (S ∪ T₁) T₂ cm₂ cn₂) :
    Extends n S (T₁ ∪ T₂) (cm₁ + cm₂) (cn₁ + cn₂) := by
  intro C hF hB hS
  obtain ⟨C₁, hF₁, hB₁, hm₁, hn₁, hkeep₁, hT₁⟩ := h₁ C hF hB hS
  have hST₁ : ∀ f ∈ S ∪ T₁, HasWire C₁ f := by
    rintro f (hf | hf)
    · exact hkeep₁ f (hS f hf)
    · exact hT₁ f hf
  obtain ⟨C₂, hF₂, hB₂, hm₂, hn₂, hkeep₂, hT₂⟩ := h₂ C₁ hF₁ hB₁ hST₁
  refine ⟨C₂, hF₂, hB₂, by omega, by omega, fun f hw => hkeep₂ f (hkeep₁ f hw), ?_⟩
  rintro f (hf | hf)
  · exact hkeep₂ f (hT₁ f hf)
  · exact hT₂ f hf

lemma Extends.seq {n : ℕ} {S T₁ T₂ : Set (Sig n)} {cm₁ cn₁ cm₂ cn₂ : ℕ}
    (h₁ : Extends n S T₁ cm₁ cn₁) (h₂ : Extends n (S ∪ T₁) T₂ cm₂ cn₂) :
    Extends n S T₂ (cm₁ + cm₂) (cn₁ + cn₂) :=
  (h₁.trans h₂).mono Set.Subset.rfl Set.subset_union_right le_rfl le_rfl

lemma Extends.union {n : ℕ} {S T₁ T₂ : Set (Sig n)} {cm₁ cn₁ cm₂ cn₂ : ℕ}
    (h₁ : Extends n S T₁ cm₁ cn₁) (h₂ : Extends n S T₂ cm₂ cn₂) :
    Extends n S (T₁ ∪ T₂) (cm₁ + cm₂) (cn₁ + cn₂) :=
  h₁.trans (h₂.mono Set.subset_union_left Set.Subset.rfl le_rfl le_rfl)

lemma Extends.add_and {n : ℕ} {S : Set (Sig n)} {f g : Sig n} (hf : f ∈ S) (hg : g ∈ S) :
    Extends n S {fun x => f x && g x} 1 0 := by
  intro C hF hB hS
  obtain ⟨wf, hwf⟩ := hS f hf
  obtain ⟨wg, hwg⟩ := hS g hg
  have hpg := push_gate C hF hB ⟨GateOp.and, [wf.val, wg.val]⟩
    ⟨Or.inl rfl, by simp⟩ (by intro i hi; simp at hi; rcases hi with rfl | rfl; exact wf.isLt; exact wg.isLt)
  rcases hpg with ⟨hF', hB', hm', hn', hkeep, hnew⟩
  refine ⟨⟨C.gates ++ [⟨GateOp.and, [wf.val, wg.val]⟩], 0⟩, hF', hB',
    by simp [isNotOp] at hm'; omega, by simp [isNotOp] at hn'; omega, hkeep, ?_⟩
  rintro _ rfl
  refine ⟨⟨n + 2 + C.size, by simp [Circuit.size]⟩, fun x => ?_⟩
  rw [hnew x]; simp only [List.map_cons, List.map_nil, hwf x, hwg x]; simp [GateOp.eval]

lemma Extends.add_or {n : ℕ} {S : Set (Sig n)} {f g : Sig n} (hf : f ∈ S) (hg : g ∈ S) :
    Extends n S {fun x => f x || g x} 1 0 := by
  intro C hF hB hS
  obtain ⟨wf, hwf⟩ := hS f hf
  obtain ⟨wg, hwg⟩ := hS g hg
  have hpg := push_gate C hF hB ⟨GateOp.or, [wf.val, wg.val]⟩
    ⟨Or.inr (Or.inl rfl), by simp⟩ (by intro i hi; simp at hi; rcases hi with rfl | rfl; exact wf.isLt; exact wg.isLt)
  rcases hpg with ⟨hF', hB', hm', hn', hkeep, hnew⟩
  refine ⟨⟨C.gates ++ [⟨GateOp.or, [wf.val, wg.val]⟩], 0⟩, hF', hB',
    by simp [isNotOp] at hm'; omega, by simp [isNotOp] at hn'; omega, hkeep, ?_⟩
  rintro _ rfl
  refine ⟨⟨n + 2 + C.size, by simp [Circuit.size]⟩, fun x => ?_⟩
  rw [hnew x]; simp only [List.map_cons, List.map_nil, hwf x, hwg x]; simp [GateOp.eval]

lemma Extends.add_not {n : ℕ} {S : Set (Sig n)} {f : Sig n} (hf : f ∈ S) :
    Extends n S {fun x => !f x} 0 1 := by
  intro C hF hB hS
  obtain ⟨wf, hwf⟩ := hS f hf
  have hpg := push_gate C hF hB ⟨GateOp.not, [wf.val]⟩
    ⟨Or.inr (Or.inr rfl), by simp⟩ (by intro i hi; simp at hi; subst hi; exact wf.isLt)
  rcases hpg with ⟨hF', hB', hm', hn', hkeep, hnew⟩
  refine ⟨⟨C.gates ++ [⟨GateOp.not, [wf.val]⟩], 0⟩, hF', hB',
    by simp [isNotOp] at hm'; omega, by simp [isNotOp] at hn'; omega, hkeep, ?_⟩
  rintro _ rfl
  refine ⟨⟨n + 2 + C.size, by simp [Circuit.size]⟩, fun x => ?_⟩
  rw [hnew x]; simp only [List.map_cons, List.map_nil, hwf x]; simp [GateOp.eval]

lemma Extends.parallel_fin_sum {n k : ℕ} {S : Set (Sig n)} (T : Fin k → Set (Sig n))
    (cm cn : Fin k → ℕ) (h : ∀ i : Fin k, Extends n S (T i) (cm i) (cn i)) :
    Extends n S (⋃ i : Fin k, T i) (∑ i : Fin k, cm i) (∑ i : Fin k, cn i) := by
  induction k with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact (Extends.of_subset (Set.empty_subset S)).mono Set.Subset.rfl
      (by intro z hz; simp at hz) le_rfl le_rfl
  | succ k ih =>
    have hinit := ih (fun i => T i.castSucc) (fun i => cm i.castSucc) (fun i => cn i.castSucc)
      (fun i => h i.castSucc)
    have hlast := h (Fin.last k)
    refine (hinit.union hlast).mono Set.Subset.rfl ?_ (by rw [Fin.sum_univ_castSucc])
      (by rw [Fin.sum_univ_castSucc])
    rintro z hz
    rcases Set.mem_iUnion.mp hz with ⟨i, hi⟩
    refine Fin.lastCases ?_ ?_ i hi
    · intro hlast_mem; exact Or.inr hlast_mem
    · intro j hj; exact Or.inl (Set.mem_iUnion.mpr ⟨j, hj⟩)

lemma Extends.add_range_fin_sum {n k : ℕ} {S : Set (Sig n)} (f : Fin k → Sig n)
    (cm cn : Fin k → ℕ) (h : ∀ i : Fin k, Extends n S {f i} (cm i) (cn i)) :
    Extends n S (Set.range f) (∑ i : Fin k, cm i) (∑ i : Fin k, cn i) := by
  refine (Extends.parallel_fin_sum (fun i => {f i}) cm cn h).mono Set.Subset.rfl ?_ le_rfl le_rfl
  rintro _ ⟨i, rfl⟩
  exact Set.mem_iUnion.mpr ⟨i, rfl⟩

lemma Extends.add_range_fin {n k : ℕ} {S : Set (Sig n)} (f : Fin k → Sig n)
    (cm cn : ℕ) (h : ∀ i : Fin k, Extends n S {f i} cm cn) :
    Extends n S (Set.range f) (k * cm) (k * cn) := by
  simpa [Finset.sum_const, smul_eq_mul] using
    Extends.add_range_fin_sum f (fun _ => cm) (fun _ => cn) h

lemma Extends.fold_nat_sum {n : ℕ} (k : ℕ) (Inv : ℕ → Set (Sig n))
    (cm cn : ℕ → ℕ) (h : ∀ t < k, Extends n (Inv t) (Inv (t + 1)) (cm t) (cn t)) :
    Extends n (Inv 0) (Inv k) (∑ t ∈ Finset.range k, cm t) (∑ t ∈ Finset.range k, cn t) := by
  induction k with
  | zero => simpa using Extends.of_subset Set.Subset.rfl
  | succ k ih =>
    have h1 := ih (fun t ht => h t (by omega))
    have h2 := h k (by omega)
    refine (h1.seq (h2.mono Set.subset_union_right Set.Subset.rfl le_rfl le_rfl)).mono
      Set.Subset.rfl Set.Subset.rfl (by rw [Finset.sum_range_succ]) (by rw [Finset.sum_range_succ])

lemma Extends.add_and_list {n : ℕ} {S : Set (Sig n)} (l : List (Sig n))
    (htrue : (fun _ : Finset (Fin n) => true) ∈ S) (hl : ∀ f ∈ l, f ∈ S) :
    Extends n S {fun x => l.all fun f => f x} l.length 0 := by
  induction l with
  | nil =>
    exact (Extends.of_subset (by intro z hz; simp at hz; subst hz; exact htrue)).mono
      Set.Subset.rfl Set.Subset.rfl (by simp) le_rfl
  | cons a t ih =>
    have htail := ih (fun f hf => hl f (List.mem_cons_of_mem a hf))
    have ha : a ∈ S ∪ {fun x => t.all fun f => f x} := Or.inl (hl a List.mem_cons_self)
    have hcomb := htail.seq (Extends.add_and ha (Or.inr rfl))
    refine hcomb.mono Set.Subset.rfl ?_ (by simp) (by omega)
    rintro z hz; simp only [Set.mem_singleton_iff] at hz ⊢; exact hz

lemma Extends.add_or_list {n : ℕ} {S : Set (Sig n)} (l : List (Sig n))
    (hfalse : (fun _ : Finset (Fin n) => false) ∈ S) (hl : ∀ f ∈ l, f ∈ S) :
    Extends n S {fun x => l.any fun f => f x} l.length 0 := by
  induction l with
  | nil =>
    exact (Extends.of_subset (by intro z hz; simp at hz; subst hz; exact hfalse)).mono
      Set.Subset.rfl Set.Subset.rfl (by simp) le_rfl
  | cons a t ih =>
    have htail := ih (fun f hf => hl f (List.mem_cons_of_mem a hf))
    have ha : a ∈ S ∪ {fun x => t.any fun f => f x} := Or.inl (hl a List.mem_cons_self)
    have hcomb := htail.seq (Extends.add_or ha (Or.inr rfl))
    refine hcomb.mono Set.Subset.rfl ?_ (by simp) (by omega)
    rintro z hz; simp only [Set.mem_singleton_iff] at hz ⊢; exact hz

/-! ### Part 2: Exact Rank Decoder via Recursive Halving (`≤ r` NOTs, `≤ 4*L` Mono Gates) -/

lemma Extends.decode_rank {n : ℕ} (d : ℕ) :
    ∀ (L : ℕ), L < 2 ^ d →
      ∀ (R : Finset (Fin n) → ℕ), (∀ x, R x ≤ L) →
      Extends n
        ({fun _ => false, fun _ => true} ∪
          Set.range (fun t : Fin (L + 1) => fun x => decide (t.val ≤ R x)))
        (Set.range (fun t : Fin (L + 1) => fun x => decide (R x = t.val)))
        (4 * L) d := by
  induction d with
  | zero =>
    intro L hL R hR
    have hL0 : L = 0 := by simp at hL; omega
    subst hL0
    refine (Extends.of_subset ?_).mono Set.Subset.rfl Set.Subset.rfl (by omega) (by omega)
    rintro _ ⟨t, rfl⟩
    have ht0 : t.val = 0 := by omega
    have heq : (fun x => decide (R x = t.val)) = fun _ => true := by
      funext x; have := hR x; rw [ht0, decide_eq_true (by omega)]
    dsimp only; rw [heq]; exact Or.inl (Or.inr rfl)
  | succ d ih =>
    intro L hL R hR
    by_cases hL0 : L = 0
    · subst hL0
      refine (Extends.of_subset ?_).mono Set.Subset.rfl Set.Subset.rfl (by omega) (by omega)
      rintro _ ⟨t, rfl⟩
      have ht0 : t.val = 0 := by omega
      have heq : (fun x => decide (R x = t.val)) = fun _ => true := by
        funext x; have := hR x; rw [ht0, decide_eq_true (by omega)]
      dsimp only; rw [heq]; exact Or.inl (Or.inr rfl)
    · let mid := (L + 1) / 2
      let L0 := mid - 1
      let L1 := L - mid
      have hmid_pos : 1 ≤ mid := by dsimp only [mid]; omega
      have hmid_le : mid ≤ L := by dsimp only [mid]; omega
      have hL0_le : L0 ≤ L1 := by dsimp only [L0, L1, mid]; omega
      have hL1_lt : L1 < 2 ^ d := by
        have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
        dsimp only [L1, mid]; omega
      let Base : Set (Sig n) :=
        {fun _ => false, fun _ => true} ∪
          Set.range (fun t : Fin (L + 1) => fun x => decide (t.val ≤ R x))
      let bit : Sig n := fun x => decide (mid ≤ R x)
      let nbit : Sig n := fun x => !bit x
      have hbit_mem : bit ∈ Base := Or.inr ⟨⟨mid, by omega⟩, rfl⟩
      have hnbit : Extends n Base {nbit} 0 1 := Extends.add_not hbit_mem
      let R' : Finset (Fin n) → ℕ := fun x => if mid ≤ R x then R x - mid else R x
      have hR' : ∀ x, R' x ≤ L1 := fun x => by
        dsimp only [R', L1, mid]; have := hR x; split_ifs <;> omega
      let T' (s : Fin (L1 + 1)) : Sig n := fun x => decide (s.val ≤ R' x)
      let foldCost (s : Fin (L1 + 1)) : ℕ := if 1 ≤ s.val ∧ s.val ≤ L0 then 2 else 0
      have hfold : Extends n (Base ∪ {nbit}) (Set.range T') (∑ s : Fin (L1 + 1), foldCost s) 0 := by
        have h1 := Extends.add_range_fin_sum (S := Base ∪ {nbit}) T' foldCost (fun _ => 0) (fun s => by
          by_cases hs : 1 ≤ s.val ∧ s.val ≤ L0
          · have hfc : foldCost s = 2 := by simp [foldCost, hs]
            rw [hfc]
            let hiSig : Sig n := fun x => decide (mid + s.val ≤ R x)
            let loSig : Sig n := fun x => decide (s.val ≤ R x)
            have hhi : hiSig ∈ Base ∪ {nbit} := Or.inl (Or.inr ⟨⟨mid + s.val, by omega⟩, rfl⟩)
            have hlo : loSig ∈ Base ∪ {nbit} := Or.inl (Or.inr ⟨⟨s.val, by omega⟩, rfl⟩)
            have hand : Extends n (Base ∪ {nbit}) {fun x => nbit x && loSig x} 1 0 :=
              Extends.add_and (Or.inr rfl) hlo
            have hor : Extends n ((Base ∪ {nbit}) ∪ {fun x => nbit x && loSig x})
                {fun x => hiSig x || (nbit x && loSig x)} 1 0 :=
              Extends.add_or (Or.inl hhi) (Or.inr rfl)
            have heq : (fun x => hiSig x || (nbit x && loSig x)) = T' s := by
              funext x; dsimp only [hiSig, loSig, nbit, bit, T', R']
              by_cases hge : mid ≤ R x
              · simp only [hge, decide_true, Bool.not_true, Bool.false_and, Bool.or_false, ↓reduceIte]
                rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; omega
              · have hhiF : ¬ mid + s.val ≤ R x := by omega
                simp only [hge, hhiF, decide_false, Bool.not_false, Bool.true_and, Bool.false_or, ↓reduceIte]
            rw [heq] at hor
            exact (hand.seq hor).mono Set.Subset.rfl Set.Subset.rfl (by omega) (by omega)
          · have hfc : foldCost s = 0 := by simp [foldCost, hs]
            rw [hfc]
            by_cases hs0 : s.val = 0
            · have heq : T' s = fun _ => true := by funext x; simp [T', hs0]
              rw [heq]
              exact Extends.of_subset (by rintro _ rfl; exact Or.inl (Or.inl (Or.inr rfl)))
            · have heq : T' s = fun x => decide (mid + s.val ≤ R x) := by
                funext x; dsimp only [T', R']
                by_cases hge : mid ≤ R x
                · simp only [hge, ↓reduceIte]; rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; omega
                · simp only [hge, ↓reduceIte]; rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]
                  dsimp only [L0, mid] at hs; omega
              rw [heq]
              exact Extends.of_subset (by rintro _ rfl; exact Or.inl (Or.inr ⟨⟨mid + s.val, by omega⟩, rfl⟩)))
        simpa using h1
      have hfold_sum : ∑ s : Fin (L1 + 1), foldCost s = 2 * L0 := by
        dsimp only [foldCost]
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
        have hcard : (Finset.univ.filter (fun s : Fin (L1 + 1) => 1 ≤ s.val ∧ s.val ≤ L0)).card = L0 := by
          have hbij : (Finset.univ.filter (fun s : Fin (L1 + 1) => 1 ≤ s.val ∧ s.val ≤ L0)).card =
              (Finset.univ : Finset (Fin L0)).card := by
            refine Finset.card_bij (fun s hs => ⟨s.val - 1, by
                have := (Finset.mem_filter.mp hs).2; omega⟩)
              (fun _ _ => Finset.mem_univ _)
              (fun s₁ hs₁ s₂ hs₂ heq => by
                have h1 := (Finset.mem_filter.mp hs₁).2
                have h2 := (Finset.mem_filter.mp hs₂).2
                have hv := Fin.mk.inj heq
                exact Fin.ext (by omega))
              (fun i _ => ⟨⟨i.val + 1, by have := i.isLt; dsimp only [L0, L1] at this ⊢; omega⟩,
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, by have := i.isLt; dsimp only [L0, L1] at this ⊢; omega⟩,
                Fin.ext (by simp)⟩)
          simpa using hbij
        rw [hcard, mul_comm]
      rw [hfold_sum] at hfold
      let E' (s : Fin (L1 + 1)) : Sig n := fun x => decide (R' x = s.val)
      have hrec : Extends n ((Base ∪ {nbit}) ∪ Set.range T') (Set.range E') (4 * L1) d :=
        (ih L1 hL1_lt R' hR').mono (by
          rintro z ((rfl | rfl) | h)
          · exact Or.inl (Or.inl (Or.inl (Or.inl rfl)))
          · exact Or.inl (Or.inl (Or.inl (Or.inr rfl)))
          · exact Or.inr h) Set.Subset.rfl le_rfl le_rfl
      let E (t : Fin (L + 1)) : Sig n := fun x => decide (R x = t.val)
      have hunpack : Extends n ((Base ∪ {nbit}) ∪ Set.range E') (Set.range E) (L + 1) 0 := by
        simpa [mul_one, mul_zero] using Extends.add_range_fin
          (S := (Base ∪ {nbit}) ∪ Set.range E') E 1 0 (fun t => by
            by_cases ht : t.val < mid
            · have heq : E t = fun x => nbit x && E' ⟨t.val, by omega⟩ x := by
                funext x; dsimp only [E, nbit, bit, E', R']
                by_cases hge : mid ≤ R x
                · simp only [hge, decide_true, Bool.not_true, Bool.false_and]
                  exact decide_eq_false (by omega)
                · simp only [hge, decide_false, Bool.not_false, Bool.true_and, ↓reduceIte]
              rw [heq]
              exact Extends.add_and (Or.inl (Or.inr rfl)) (Or.inr ⟨⟨t.val, by omega⟩, rfl⟩)
            · have heq : E t = fun x => bit x && E' ⟨t.val - mid, by omega⟩ x := by
                funext x; dsimp only [E, bit, E', R']
                by_cases hge : mid ≤ R x
                · simp only [hge, decide_true, Bool.true_and, ↓reduceIte]
                  rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; omega
                · simp only [hge, decide_false, Bool.false_and]
                  exact decide_eq_false (by omega)
              rw [heq]
              exact Extends.add_and (Or.inl (Or.inl hbit_mem)) (Or.inr ⟨⟨t.val - mid, by omega⟩, rfl⟩))
      have hcomb := hnbit.seq ((hfold.seq hrec).seq hunpack)
      refine hcomb.mono Set.Subset.rfl Set.Subset.rfl ?_ (by omega)
      dsimp only [L0, L1, mid]
      omega


/-! ### Part 3: Monotone Bit-Counter & Common-Neighbor Table Decoder (`L-meta-49526`) -/

section CommonNeighbor

lemma Extends.add_bit_count {n k : ℕ} {S : Set (Sig n)}
    (hfalse : (fun _ : Finset (Fin n) => false) ∈ S)
    (htrue : (fun _ : Finset (Fin n) => true) ∈ S)
    (b : Fin k → Sig n) (hb : ∀ i : Fin k, b i ∈ S) :
    Extends n S
      (Set.range (fun t : Fin (k + 1) => fun x : Finset (Fin n) =>
        decide (t.val ≤ (Finset.univ.filter (fun i : Fin k => b i x = true)).card)))
      (2 * k * (k + 1)) 0 := by
  let cntPref (j : ℕ) (x : Finset (Fin n)) : ℕ :=
    (Finset.univ.filter (fun i : Fin k => i.val < j ∧ b i x = true)).card
  let Inv (j : ℕ) : Set (Sig n) :=
    S ∪ Set.range (fun t : Fin (k + 1) => fun x => decide (t.val ≤ cntPref j x))
  have hInv0 : Inv 0 ⊆ S := by
    rintro f (hf | ⟨t, rfl⟩)
    · exact hf
    · dsimp only
      have hc0 : ∀ x, cntPref 0 x = 0 := fun x => by simp [cntPref]
      by_cases ht : t.val = 0
      · have h1 : (fun x => decide (t.val ≤ cntPref 0 x)) = fun _ => true := by funext x; simp [hc0, ht]
        rw [h1]; exact htrue
      · have h1 : (fun x => decide (t.val ≤ cntPref 0 x)) = fun _ => false := by funext x; simp [hc0, ht]
        rw [h1]; exact hfalse
  have hStep : ∀ j < k, Extends n (Inv j) (Inv (j + 1)) (2 * (k + 1)) 0 := by
    intro j hj
    let jf : Fin k := ⟨j, hj⟩
    have hcnt_step : ∀ x, cntPref (j + 1) x = cntPref j x + (b jf x).toNat := by
      intro x
      dsimp only [cntPref]
      by_cases hbj : b jf x = true
      · have hset : Finset.univ.filter (fun i : Fin k => i.val < j + 1 ∧ b i x = true) =
            insert jf (Finset.univ.filter (fun i : Fin k => i.val < j ∧ b i x = true)) := by
          ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          constructor
          · rintro ⟨hlt, hbi⟩
            by_cases heq : i.val = j
            · left; exact Fin.ext heq
            · right; exact ⟨by omega, hbi⟩
          · rintro (rfl | ⟨hlt, hbi⟩)
            · exact ⟨by simp [jf], hbj⟩
            · exact ⟨by omega, hbi⟩
        have hnot : jf ∉ Finset.univ.filter (fun i : Fin k => i.val < j ∧ b i x = true) := by simp [jf]
        rw [hset, Finset.card_insert_of_notMem hnot, hbj, Bool.toNat_true]
      · have hbf : b jf x = false := Bool.eq_false_iff.mpr hbj
        have hset : Finset.univ.filter (fun i : Fin k => i.val < j + 1 ∧ b i x = true) =
            Finset.univ.filter (fun i : Fin k => i.val < j ∧ b i x = true) := by
          ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hlt, hbi⟩
            have hne : i.val ≠ j := by
              intro heq
              have : i = jf := Fin.ext heq
              rw [this, hbf] at hbi; cases hbi
            exact ⟨by omega, hbi⟩
          · rintro ⟨hlt, hbi⟩; exact ⟨by omega, hbi⟩
        rw [hset, hbf, Bool.toNat_false, add_zero]
    have hrange := Extends.add_range_fin (S := Inv j)
      (fun t : Fin (k + 1) => fun x => decide (t.val ≤ cntPref (j + 1) x)) 2 0 (fun t => by
        by_cases ht : t.val = 0
        · have heq : (fun x => decide (t.val ≤ cntPref (j + 1) x)) = fun _ => true := by
            funext x; simp [ht]
          rw [heq]
          exact (Extends.of_subset (Set.singleton_subset_iff.mpr (Or.inl htrue))).mono
            Set.Subset.rfl Set.Subset.rfl (by omega) le_rfl
        · let t' : Fin (k + 1) := ⟨t.val - 1, by have := t.isLt; omega⟩
          have hand : Extends n (Inv j) {fun x => b jf x && decide (t'.val ≤ cntPref j x)} 1 0 :=
            Extends.add_and (Or.inl (hb jf)) (Or.inr ⟨t', rfl⟩)
          have hor : Extends n (Inv j ∪ {fun x => b jf x && decide (t'.val ≤ cntPref j x)})
              {fun x => decide (t.val ≤ cntPref j x) || (b jf x && decide (t'.val ≤ cntPref j x))} 1 0 :=
            Extends.add_or (Or.inl (Or.inr ⟨t, rfl⟩)) (Or.inr rfl)
          have heq : (fun x => decide (t.val ≤ cntPref j x) || (b jf x && decide (t'.val ≤ cntPref j x))) =
              (fun x => decide (t.val ≤ cntPref (j + 1) x)) := by
            funext x
            rw [hcnt_step x]
            apply Bool.eq_iff_iff.mpr
            cases hbx : b jf x
            · simp only [Bool.false_and, Bool.or_false, Bool.toNat_false, add_zero]
            · simp only [Bool.true_and, Bool.or_eq_true, decide_eq_true_eq, Bool.toNat_true, t']
              omega
          rw [heq] at hor
          exact (hand.seq hor).mono Set.Subset.rfl Set.Subset.rfl (by omega) (by omega))
    refine ((Extends.of_subset (Set.subset_union_left : S ⊆ Inv j)).union hrange).mono
      Set.Subset.rfl Set.Subset.rfl (by ring_nf; omega) (by omega)
  have hfold := Extends.fold_nat_sum k Inv (fun _ => 2 * (k + 1)) (fun _ => 0) hStep
  have hcntk : ∀ x, cntPref k x = (Finset.univ.filter (fun i : Fin k => b i x = true)).card := fun x => by
    dsimp only [cntPref]; congr 1; ext i; simp [i.isLt]
  refine hfold.mono hInv0 ?_ ?_ (by simp)
  · rintro _ ⟨t, rfl⟩
    refine Or.inr ⟨t, ?_⟩
    funext x; simp only [hcntk x]
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    ring_nf; omega

lemma solve_49526 (n m L D : Nat) (g : Fin n → Fin n → Prop)
    (hL : ∀ u v : Fin n, u ≠ v →
      ((Finset.univ : Finset (Fin n)).filter (fun c => @decide (∀ w ∈ ({u, v} : Finset (Fin n)), g w c)
        (Classical.propDecidable _))).card ≤ L)
    (A W : Fin n → Fin n → Nat) (j : Fin m → Fin n) (test : Fin m → Nat → Bool)
    (r : Nat) (hr : L + 2 < 2 ^ r) :
    let centers := fun (x : Finset (Fin n)) =>
      (Finset.univ : Finset (Fin n)).filter (fun c => @decide (∀ u ∈ x, g u c) (Classical.propDecidable _))
    let f := fun (x : Finset (Fin n)) (v : Fin n) =>
      if x = ∅ then D
      else if x.card = 1 then x.sup (fun u => A u v)
      else (centers x).sup (fun c => W c v)
    ∃ (C : Circuit) (tap : Fin m → Fin (n + 2 + C.size)),
      FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size ∧
      notCount C ≤ r ∧ C.size ≤ 64 * (n + 1) ^ 2 * (n + m + 2) ∧
      ∀ x : Finset (Fin n), ∀ b : Fin m,
        (C.wires (inputOf x)).getD (tap b).val false = test b (f x (j b)) := by
  intro centers f
  classical
  let L' : ℕ := min L n
  have hL'_le_L : L' ≤ L := Nat.min_le_left L n
  have hL'_le_n : L' ≤ n := Nat.min_le_right L n
  let r' : ℕ := min r (L' + 2)
  have hr'_le_r : r' ≤ r := Nat.min_le_left _ _
  have hr'_le_n : r' ≤ n + 2 := by omega
  have hL'_lt_pow : L' + 2 < 2 ^ r' := by
    by_cases hcmp : r ≤ L' + 2
    · have : r' = r := Nat.min_eq_left hcmp
      rw [this]; omega
    · have : r' = L' + 2 := Nat.min_eq_right (by omega)
      rw [this]; exact Nat.lt_two_pow_self
  have hcenters_le_L' : ∀ x : Finset (Fin n), 2 ≤ x.card → (centers x).card ≤ L' := by
    intro x hx
    obtain ⟨u, hu, v, hv, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < x.card)
    have hsub : centers x ⊆ (Finset.univ : Finset (Fin n)).filter
        (fun c => @decide (∀ w ∈ ({u, v} : Finset (Fin n)), g w c) (Classical.propDecidable _)) := by
      intro c hc
      simp only [centers, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hc ⊢
      intro w hw
      rcases Finset.mem_insert.mp hw with hwu | hw2
      · rw [hwu]; exact hc u hu
      · rw [Finset.mem_singleton.mp hw2]; exact hc v hv
    have h1 := (Finset.card_le_card hsub).trans (hL u v hne)
    have h2 : (centers x).card ≤ n := (Finset.card_le_univ _).trans (by simp)
    omega
  -- Step 1: Monotone `miss c x` (`c ∉ centers x`) for all `c : Fin n`
  let miss (c : Fin n) (x : Finset (Fin n)) : Bool :=
    @decide (∃ u ∈ x, ¬ g u c) (Classical.propDecidable _)
  have hmiss_iff : ∀ c x, miss c x = true ↔ c ∉ centers x := by
    intro c x
    simp only [miss, centers, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
    push Not; rfl
  let missCnt (x : Finset (Fin n)) : ℕ :=
    (Finset.univ.filter (fun c : Fin n => miss c x = true)).card
  have hmissCnt_add : ∀ x, missCnt x + (centers x).card = n := by
    intro x
    have hcomp : Finset.univ.filter (fun c : Fin n => miss c x = true) = Finset.univ \ centers x := by
      ext c; simp [hmiss_iff]
    dsimp only [missCnt]
    rw [hcomp, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    have hle : (centers x).card ≤ n := (Finset.card_le_univ _).trans (by simp)
    omega
  -- Step 1a: Build `Set.range miss` from `baseSigs n` (`≤ n^2` mono gates)
  have hmiss_ext : Extends n (baseSigs n) (Set.range miss) (n * n) 0 := by
    refine (Extends.add_range_fin miss n 0 fun c => ?_).mono Set.Subset.rfl Set.Subset.rfl le_rfl (by simp)
    let badL : List (Fin n) := (Finset.univ.filter (fun u : Fin n => ¬ g u c)).toList
    let sigs : List (Sig n) := badL.map (fun u x => decide (u ∈ x))
    have hlen : sigs.length ≤ n := by
      simp only [sigs, badL, List.length_map, Finset.length_toList]
      exact (Finset.card_le_univ _).trans (by simp)
    have hor := Extends.add_or_list (S := baseSigs n) sigs (Or.inl (Or.inl rfl)) (fun f hf => by
      rcases List.mem_map.mp hf with ⟨u, _, rfl⟩; exact Or.inr ⟨u, rfl⟩)
    have heq : (fun x => sigs.any fun f => f x) = miss c := by
      funext x; apply Bool.eq_iff_iff.mpr
      simp only [sigs, badL, List.any_map, List.any_eq_true, Finset.mem_toList, Finset.mem_filter,
        Finset.mem_univ, true_and, Function.comp_apply, decide_eq_true_eq, miss]
      exact ⟨fun ⟨u, hng, hux⟩ => ⟨u, hux, hng⟩, fun ⟨u, hux, hng⟩ => ⟨u, hng, hux⟩⟩
    rw [heq] at hor
    exact hor.mono Set.Subset.rfl Set.Subset.rfl hlen le_rfl
  -- Step 2: Build cardinality thresholds `decide (t ≤ x.card)` and `decide (t ≤ missCnt x)`
  let S1 : Set (Sig n) := baseSigs n ∪ Set.range miss
  have hcard_ext : Extends n S1
      (Set.range (fun t : Fin (n + 1) => fun x : Finset (Fin n) => decide (t.val ≤ x.card)))
      (2 * n * (n + 1)) 0 := by
    have h := Extends.add_bit_count (S := S1) (Or.inl (Or.inl (Or.inl rfl))) (Or.inl (Or.inl (Or.inr rfl)))
      (fun i x => decide (i ∈ x)) (fun i => Or.inl (Or.inr ⟨i, rfl⟩))
    have hfeq : ∀ x : Finset (Fin n),
        (Finset.univ.filter (fun i : Fin n => decide (i ∈ x) = true)).card = x.card := by
      intro x; congr 1; ext i; simp
    refine h.mono Set.Subset.rfl ?_ le_rfl le_rfl
    rintro _ ⟨t, rfl⟩; refine ⟨t, ?_⟩; funext x; simp only [hfeq x]
  have hmcnt_ext : Extends n S1
      (Set.range (fun t : Fin (n + 1) => fun x : Finset (Fin n) => decide (t.val ≤ missCnt x)))
      (2 * n * (n + 1)) 0 :=
    Extends.add_bit_count (S := S1) (Or.inl (Or.inl (Or.inl rfl))) (Or.inl (Or.inl (Or.inr rfl)))
      miss (fun c => Or.inr ⟨c, rfl⟩)
  -- Step 3: Build `missCntExcl c` thresholds for EVERY `c : Fin n` (`2 * n^2 * (n + 1)` mono gates)
  let missCntExcl (c : Fin n) (x : Finset (Fin n)) : ℕ :=
    (Finset.univ.filter (fun c' : Fin n => (if c' = c then false else miss c' x) = true)).card
  have hexcl_ext : Extends n S1
      (⋃ c : Fin n, Set.range (fun t : Fin (n + 1) => fun x : Finset (Fin n) => decide (t.val ≤ missCntExcl c x)))
      (n * (2 * n * (n + 1))) 0 := by
    have h := Extends.parallel_fin_sum (S := S1)
      (fun c : Fin n => Set.range (fun t : Fin (n + 1) => fun x => decide (t.val ≤ missCntExcl c x)))
      (fun _ => 2 * n * (n + 1)) (fun _ => 0) (fun c =>
        Extends.add_bit_count (S := S1) (Or.inl (Or.inl (Or.inl rfl))) (Or.inl (Or.inl (Or.inr rfl)))
          (fun c' x => if c' = c then false else miss c' x) (fun c' => by
            by_cases heq : c' = c
            · have : (fun x => if c' = c then false else miss c' x) = fun _ => false := by funext x; simp [heq]
              rw [this]; exact Or.inl (Or.inl (Or.inl rfl))
            · have : (fun x => if c' = c then false else miss c' x) = miss c' := by funext x; simp [heq]
              rw [this]; exact Or.inr ⟨c', rfl⟩))
    simpa [Finset.sum_const, smul_eq_mul] using h
  -- Step 4: Define monotone rank `rk x ∈ [0, L' + 2]`, build its thresholds `T_t`, and decode `E_t` using ≤ r' NOTs!
  let rk (x : Finset (Fin n)) : ℕ :=
    if x = ∅ then 0
    else if x.card = 1 then 1
    else 2 + (L' - (centers x).card)
  have hrk_le : ∀ x, rk x ≤ L' + 2 := fun x => by dsimp only [rk]; split_ifs <;> omega
  let S2 : Set (Sig n) :=
    S1 ∪ ((Set.range (fun t : Fin (n + 1) => fun x : Finset (Fin n) => decide (t.val ≤ x.card)) ∪
           Set.range (fun t : Fin (n + 1) => fun x : Finset (Fin n) => decide (t.val ≤ missCnt x))) ∪
          (⋃ c : Fin n, Set.range (fun t : Fin (n + 1) => fun x : Finset (Fin n) => decide (t.val ≤ missCntExcl c x))))
  have hS12_ext : Extends n S1
      ((Set.range (fun t : Fin (n + 1) => fun x : Finset (Fin n) => decide (t.val ≤ x.card)) ∪
        Set.range (fun t : Fin (n + 1) => fun x : Finset (Fin n) => decide (t.val ≤ missCnt x))) ∪
       (⋃ c : Fin n, Set.range (fun t : Fin (n + 1) => fun x : Finset (Fin n) => decide (t.val ≤ missCntExcl c x))))
      (2 * n * (n + 1) + 2 * n * (n + 1) + n * (2 * n * (n + 1))) 0 :=
    ((hcard_ext.union hmcnt_ext).union hexcl_ext).mono Set.Subset.rfl Set.Subset.rfl le_rfl (by omega)
  have hrk_thresh_ext : Extends n S2
      (Set.range (fun t : Fin (L' + 3) => fun x : Finset (Fin n) => decide (t.val ≤ rk x)))
      (L' + 3) 0 := by
    refine (Extends.add_range_fin (S := S2)
      (fun t : Fin (L' + 3) => fun x => decide (t.val ≤ rk x)) 1 0 fun t => ?_).mono
      Set.Subset.rfl Set.Subset.rfl (by omega) (by simp)
    by_cases ht0 : t.val = 0
    · have heq : (fun x => decide (t.val ≤ rk x)) = fun _ => true := by funext x; simp [ht0]
      rw [heq]
      exact (Extends.of_subset (Set.singleton_subset_iff.mpr (Or.inl (Or.inl (Or.inl (Or.inr rfl)))))).mono
        Set.Subset.rfl Set.Subset.rfl (by omega) le_rfl
    · by_cases ht1 : t.val = 1
      · by_cases hn0 : n = 0
        · have heq : (fun x : Finset (Fin n) => decide (t.val ≤ rk x)) = fun _ => false := by
            funext x; have hx0 : x = ∅ := by ext i; exact absurd i.isLt (by omega)
            simp [rk, hx0, ht1]
          rw [heq]
          exact (Extends.of_subset (Set.singleton_subset_iff.mpr (Or.inl (Or.inl (Or.inl (Or.inl rfl)))))).mono
            Set.Subset.rfl Set.Subset.rfl (by omega) le_rfl
        · have heq : (fun x : Finset (Fin n) => decide (t.val ≤ rk x)) = fun x => decide (1 ≤ x.card) := by
            funext x; apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq, rk, ht1]
            by_cases hx0 : x = ∅
            · simp [hx0]
            · have hpos : 1 ≤ x.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hx0)
              simp only [hx0, ↓reduceIte]; split_ifs <;> omega
          rw [heq]
          exact (Extends.of_subset (Set.singleton_subset_iff.mpr
            (Or.inr (Or.inl (Or.inl ⟨⟨1, by omega⟩, rfl⟩))))).mono
            Set.Subset.rfl Set.Subset.rfl (by omega) le_rfl
      · by_cases hn1 : n < 2
        · have heq : (fun x : Finset (Fin n) => decide (t.val ≤ rk x)) = fun _ => false := by
            funext x
            have hxc : x.card ≤ n := (Finset.card_le_univ x).trans (by simp)
            dsimp only [rk]; split_ifs with h1 h2
            · simp [show ¬ t.val ≤ 0 by omega]
            · simp [show ¬ t.val ≤ 1 by omega]
            · exfalso
              have hpos : 1 ≤ x.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr h1)
              omega
          rw [heq]
          exact (Extends.of_subset (Set.singleton_subset_iff.mpr (Or.inl (Or.inl (Or.inl (Or.inl rfl)))))).mono
            Set.Subset.rfl Set.Subset.rfl (by omega) le_rfl
        · let d := t.val - 2
          have hd_le : d ≤ L' := by have := t.isLt; omega
          have hge2_mem : (fun x : Finset (Fin n) => decide (2 ≤ x.card)) ∈ S2 :=
            Or.inr (Or.inl (Or.inl ⟨⟨2, by omega⟩, rfl⟩))
          have hmc_mem : (fun x : Finset (Fin n) => decide (n - L' + d ≤ missCnt x)) ∈ S2 :=
            Or.inr (Or.inl (Or.inr ⟨⟨n - L' + d, by omega⟩, rfl⟩))
          have heq : (fun x : Finset (Fin n) => decide (2 ≤ x.card) && decide (n - L' + d ≤ missCnt x)) =
              (fun x => decide (t.val ≤ rk x)) := by
            funext x; apply Bool.eq_iff_iff.mpr
            simp only [Bool.and_eq_true, decide_eq_true_eq, rk]
            by_cases hx0 : x = ∅
            · simp only [hx0, Finset.card_empty, ↓reduceIte, show ¬ 2 ≤ 0 by decide, false_and, false_iff]; omega
            · by_cases hx1 : x.card = 1
              · simp only [hx0, hx1, ↓reduceIte, show ¬ 2 ≤ 1 by decide, false_and, false_iff]; omega
              · have hge2 : 2 ≤ x.card := by
                  have hpos : 1 ≤ x.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hx0)
                  omega
                have hcL := hcenters_le_L' x hge2
                have hadd := hmissCnt_add x
                simp only [hx0, hx1, ↓reduceIte, hge2, true_and]
                dsimp only [d]; omega
          rw [← heq]
          exact Extends.add_and hge2_mem hmc_mem
  have hdec_ext : Extends n
      (S2 ∪ Set.range (fun t : Fin (L' + 3) => fun x : Finset (Fin n) => decide (t.val ≤ rk x)))
      (Set.range (fun t : Fin (L' + 3) => fun x : Finset (Fin n) => decide (rk x = t.val)))
      (4 * (L' + 2)) r' :=
    (Extends.decode_rank r' (L' + 2) hL'_lt_pow rk hrk_le).mono (by
      rintro z ((rfl | rfl) | h)
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl rfl))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr rfl))))
      · exact Or.inr h) Set.Subset.rfl le_rfl le_rfl
  -- Step 5: Compute `inCenter c x := decide (2 ≤ x.card ∧ c ∈ centers x)` for all `c : Fin n` (`2 * n^2` mono gates)
  let S3 : Set (Sig n) := S2 ∪ Set.range (fun t : Fin (L' + 3) => fun x : Finset (Fin n) => decide (rk x = t.val))
  let inCenter (c : Fin n) (x : Finset (Fin n)) : Bool :=
    @decide (2 ≤ x.card ∧ c ∈ centers x) (Classical.propDecidable _)
  have hinCenter_ext : Extends n S3 (Set.range inCenter) (n * (2 * n)) 0 := by
    refine (Extends.add_range_fin (S := S3) inCenter (2 * n) 0 fun c => ?_).mono
      Set.Subset.rfl Set.Subset.rfl le_rfl (by simp)
    let term (d : Fin L') (x : Finset (Fin n)) : Bool :=
      decide (rk x = 2 + d.val) && decide (n - L' + d.val ≤ missCntExcl c x)
    have hterms : Extends n S3 (Set.range term) L' 0 := by
      refine (Extends.add_range_fin (S := S3) term 1 0 fun d => ?_).mono
        Set.Subset.rfl Set.Subset.rfl (by omega) (by simp)
      have hE : (fun x => decide (rk x = 2 + d.val)) ∈ S3 :=
        Or.inr ⟨⟨2 + d.val, by have := d.isLt; omega⟩, rfl⟩
      have hEx : (fun x => decide (n - L' + d.val ≤ missCntExcl c x)) ∈ S3 :=
        Or.inl (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨c, ⟨⟨n - L' + d.val, by have := d.isLt; omega⟩, rfl⟩⟩)))
      exact Extends.add_and hE hEx
    let l : List (Sig n) := (List.finRange L').map term
    have hlen : l.length = L' := by simp [l]
    have hor := Extends.add_or_list (S := S3 ∪ Set.range term) l
      (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl rfl))))))
      (fun f hf => by rcases List.mem_map.mp hf with ⟨d, _, rfl⟩; exact Or.inr ⟨d, rfl⟩)
    have heq : (fun x => l.any fun f => f x) = inCenter c := by
      funext x; apply Bool.eq_iff_iff.mpr
      simp only [l, List.any_map, List.any_eq_true, List.mem_finRange, true_and,
        Function.comp_apply, term, Bool.and_eq_true, decide_eq_true_eq, inCenter]
      have hexcl_rel : missCntExcl c x + (miss c x).toNat = missCnt x := by
        dsimp only [missCntExcl, missCnt]
        by_cases hmc : miss c x = true
        · have hset : Finset.univ.filter (fun c' : Fin n => miss c' x = true) =
              insert c (Finset.univ.filter (fun c' : Fin n => (if c' = c then false else miss c' x) = true)) := by
            ext c'; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
            by_cases heq : c' = c
            · subst heq; simp [hmc]
            · simp [heq]
          have hnot : c ∉ Finset.univ.filter (fun c' : Fin n => (if c' = c then false else miss c' x) = true) := by simp
          rw [hset, Finset.card_insert_of_notMem hnot, hmc, Bool.toNat_true]
        · have hmf : miss c x = false := Bool.eq_false_iff.mpr hmc
          have hset : Finset.univ.filter (fun c' : Fin n => (if c' = c then false else miss c' x) = true) =
              Finset.univ.filter (fun c' : Fin n => miss c' x = true) := by
            ext c'; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            by_cases heq : c' = c
            · subst heq; simp [hmf]
            · simp [heq]
          rw [hset, hmf, Bool.toNat_false, add_zero]
      constructor
      · rintro ⟨d, hrkd, hex⟩
        have hge2 : 2 ≤ x.card := by
          dsimp only [rk] at hrkd; split_ifs at hrkd with h1 h2
          · omega
          · omega
          · have hpos : 1 ≤ x.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr h1)
            omega
        have hcL := hcenters_le_L' x hge2
        have hadd := hmissCnt_add x
        have hrk_val : rk x = 2 + (L' - (centers x).card) := by
          dsimp only [rk]
          have h1 : x ≠ ∅ := Finset.nonempty_iff_ne_empty.mp (Finset.card_pos.mp (by omega))
          have h2 : x.card ≠ 1 := by omega
          simp [h1, h2]
        rw [hrk_val] at hrkd
        have hmc_eq : missCnt x = n - L' + d.val := by omega
        have hmf : miss c x = false := by
          cases hmc : miss c x
          · rfl
          · rw [hmc, Bool.toNat_true] at hexcl_rel; omega
        refine ⟨hge2, ?_⟩
        by_contra hnot
        have := (hmiss_iff c x).mpr hnot
        rw [hmf] at this; cases this
      · rintro ⟨hge2, hcin⟩
        have hc_pos : 1 ≤ (centers x).card := Finset.one_le_card.mpr ⟨c, hcin⟩
        have hcL := hcenters_le_L' x hge2
        have hadd := hmissCnt_add x
        have hmf : miss c x = false := by
          cases hmc : miss c x
          · rfl
          · exact absurd hcin ((hmiss_iff c x).mp hmc)
        have h1 : x ≠ ∅ := Finset.nonempty_iff_ne_empty.mp (Finset.card_pos.mp (by omega))
        have h2 : x.card ≠ 1 := by omega
        refine ⟨⟨L' - (centers x).card, by omega⟩, ?_, ?_⟩
        · dsimp only [rk]; simp [h1, h2]
        · dsimp only; rw [hmf, Bool.toNat_false, add_zero] at hexcl_rel; omega
    rw [heq, hlen] at hor
    exact (hterms.seq hor).mono Set.Subset.rfl Set.Subset.rfl (by omega) (by omega)
  -- Step 6: Compute `fun x => test b (f x (j b))` for every `b : Fin m`!
  let S4 : Set (Sig n) := S3 ∪ Set.range inCenter
  let outSig (b : Fin m) (x : Finset (Fin n)) : Bool := test b (f x (j b))
  have hout_ext : Extends n S4 (Set.range outSig) (m * (8 * (n + 1) ^ 2)) 0 := by
    refine (Extends.add_range_fin (S := S4) outSig (8 * (n + 1) ^ 2) 0 fun b => ?_).mono
      Set.Subset.rfl Set.Subset.rfl le_rfl (by simp)
    have hfalse4 : (fun _ : Finset (Fin n) => false) ∈ S4 := Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl rfl)))))
    have htrue4 : (fun _ : Finset (Fin n) => true) ∈ S4 := Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr rfl)))))
    have hvar4 : ∀ u : Fin n, (fun x : Finset (Fin n) => decide (u ∈ x)) ∈ S4 :=
      fun u => Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨u, rfl⟩))))
    have hmiss4 : ∀ c : Fin n, miss c ∈ S4 :=
      fun c => Or.inl (Or.inl (Or.inl (Or.inr ⟨c, rfl⟩)))
    have hE4 : ∀ t : Fin (L' + 3), (fun x => decide (rk x = t.val)) ∈ S4 :=
      fun t => Or.inl (Or.inr ⟨t, rfl⟩)
    have hinC4 : ∀ c : Fin n, inCenter c ∈ S4 := fun c => Or.inr ⟨c, rfl⟩
    -- Build `isMax c* x := inCenter c* x && (∀ c', W c* (j b) < W c' (j b) → miss c' x = true)`
    let isMax (cstar : Fin n) (x : Finset (Fin n)) : Bool :=
      inCenter cstar x && @decide (∀ c' : Fin n, W cstar (j b) < W c' (j b) → miss c' x = true)
        (Classical.propDecidable _)
    have hisMax_ext : Extends n S4 (Set.range isMax) (n * (n + 1)) 0 := by
      refine (Extends.add_range_fin (S := S4) isMax (n + 1) 0 fun cstar => ?_).mono
        Set.Subset.rfl Set.Subset.rfl le_rfl (by simp)
      let bigL : List (Fin n) := (Finset.univ.filter (fun c' : Fin n => W cstar (j b) < W c' (j b))).toList
      let bigSigs : List (Sig n) := bigL.map miss
      have hblen : bigSigs.length ≤ n := by
        simp only [bigSigs, bigL, List.length_map, Finset.length_toList]
        exact (Finset.card_le_univ _).trans (by simp)
      have handL := Extends.add_and_list (S := S4) bigSigs htrue4 (fun s hs => by
        rcases List.mem_map.mp hs with ⟨c', _, rfl⟩; exact hmiss4 c')
      have handC := Extends.add_and (S := S4 ∪ {fun x => bigSigs.all fun s => s x})
        (Or.inl (hinC4 cstar)) (Or.inr rfl)
      have heq : (fun x => inCenter cstar x && bigSigs.all fun s => s x) = isMax cstar := by
        funext x; apply Bool.eq_iff_iff.mpr
        simp only [isMax, bigSigs, bigL, List.all_map, List.all_eq_true, Finset.mem_toList,
          Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq]
      rw [heq] at handC
      exact (handL.seq handC).mono Set.Subset.rfl Set.Subset.rfl (by omega) (by omega)
    -- Build the 4 branch signals inside `S5 = S4 ∪ Set.range isMax`
    let S5 : Set (Sig n) := S4 ∪ Set.range isMax
    let case0 : Sig n := fun x => decide (rk x = 0) && test b D
    let case1 : Sig n := fun x =>
      decide (rk x = 1) && ((Finset.univ.filter (fun u : Fin n => test b (A u (j b)) = true)).toList.map
        (fun u x => decide (u ∈ x))).any (fun s => s x)
    let caseEmpty : Sig n := fun x => decide (rk x = 2 + L') && test b 0
    let casePos : Sig n := fun x =>
      ((Finset.univ.filter (fun cstar : Fin n => test b (W cstar (j b)) = true)).toList.map isMax).any (fun s => s x)
    have hc0 : Extends n S5 {case0} 1 0 :=
      Extends.add_and (Or.inl (hE4 ⟨0, by omega⟩))
        (by cases test b D; exact Or.inl hfalse4; exact Or.inl htrue4)
    have hc1 : Extends n S5 {case1} (n + 1) 0 := by
      let uSigs : List (Sig n) := (Finset.univ.filter (fun u : Fin n => test b (A u (j b)) = true)).toList.map
        (fun u x => decide (u ∈ x))
      have hulen : uSigs.length ≤ n := by
        simp only [uSigs, List.length_map, Finset.length_toList]
        exact (Finset.card_le_univ _).trans (by simp)
      have hor := Extends.add_or_list (S := S5) uSigs (Or.inl hfalse4) (fun s hs => by
        rcases List.mem_map.mp hs with ⟨u, _, rfl⟩; exact Or.inl (hvar4 u))
      have hand := Extends.add_and (S := S5 ∪ {fun x => uSigs.any fun s => s x})
        (Or.inl (Or.inl (hE4 ⟨1, by omega⟩))) (Or.inr rfl)
      exact (hor.seq hand).mono Set.Subset.rfl Set.Subset.rfl (by omega) (by omega)
    have hcE : Extends n S5 {caseEmpty} 1 0 :=
      Extends.add_and (Or.inl (hE4 ⟨2 + L', by omega⟩))
        (by cases test b 0; exact Or.inl hfalse4; exact Or.inl htrue4)
    have hcP : Extends n S5 {casePos} n 0 := by
      let cSigs : List (Sig n) := (Finset.univ.filter (fun cstar : Fin n => test b (W cstar (j b)) = true)).toList.map isMax
      have hclen : cSigs.length ≤ n := by
        simp only [cSigs, List.length_map, Finset.length_toList]
        exact (Finset.card_le_univ _).trans (by simp)
      have hor := Extends.add_or_list (S := S5) cSigs (Or.inl hfalse4) (fun s hs => by
        rcases List.mem_map.mp hs with ⟨cstar, _, rfl⟩; exact Or.inr ⟨cstar, rfl⟩)
      exact hor.mono Set.Subset.rfl Set.Subset.rfl hclen le_rfl
    have h4cases := ((hc0.union hc1).union (hcE.union hcP))
    have hcomb := Extends.add_or_list (S := S5 ∪ (({case0} ∪ {case1}) ∪ ({caseEmpty} ∪ {casePos})))
      [case0, case1, caseEmpty, casePos] (Or.inl (Or.inl hfalse4)) (by
        intro s hs; simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl | rfl
        · exact Or.inr (Or.inl (Or.inl rfl))
        · exact Or.inr (Or.inl (Or.inr rfl))
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl)))
    have hout_eq : (fun x => ([case0, case1, caseEmpty, casePos] : List (Sig n)).any fun s => s x) = outSig b := by
      funext x
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, outSig, f]
      by_cases hx0 : x = ∅
      · subst hx0
        have hrk0 : rk ∅ = 0 := by simp [rk]
        have hnot2 : ¬ 2 ≤ (∅ : Finset (Fin n)).card := by simp
        have hc1f : case1 ∅ = false := by simp [case1, hrk0]
        have hcEf : caseEmpty ∅ = false := by
          have hne : (0 : ℕ) ≠ 2 + L' := by omega
          simp [caseEmpty, hrk0, hne]
        have hcPf : casePos ∅ = false := by
          simp only [casePos, List.any_map, List.any_eq_false, Function.comp_apply, isMax, inCenter, hnot2, false_and,
            decide_false, Bool.false_and]
          intro _ _; decide
        simp [case0, hrk0, hc1f, hcEf, hcPf]
      · by_cases hx1 : x.card = 1
        · obtain ⟨u0, rfl⟩ := Finset.card_eq_one.mp hx1
          have hrk1 : rk {u0} = 1 := by simp [rk]
          have hnot2 : ¬ 2 ≤ ({u0} : Finset (Fin n)).card := by simp
          have hc0f : case0 {u0} = false := by simp [case0, hrk1]
          have hcEf : caseEmpty {u0} = false := by
            have hne : (1 : ℕ) ≠ 2 + L' := by omega
            simp [caseEmpty, hrk1, hne]
          have hcPf : casePos {u0} = false := by
            simp only [casePos, List.any_map, List.any_eq_false, Function.comp_apply, isMax, inCenter, hnot2, false_and,
              decide_false, Bool.false_and]
            intro _ _; decide
          simp only [Finset.singleton_ne_empty, Finset.card_singleton, ↓reduceIte, Finset.sup_singleton,
            hc0f, hcEf, hcPf, Bool.false_eq_true, false_or, or_false]
          simp only [case1, hrk1, decide_true, Bool.true_and, List.any_map, List.any_eq_true,
            Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply,
            decide_eq_true_eq, Finset.mem_singleton]
          exact ⟨fun ⟨u, ht, hu⟩ => by rw [hu] at ht; exact ht, fun ht => ⟨u0, ht, rfl⟩⟩
        · have hge2 : 2 ≤ x.card := by
            have hpos : 1 ≤ x.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hx0)
            omega
          have hrk_val : rk x = 2 + (L' - (centers x).card) := by simp [rk, hx0, hx1]
          have hc0f : case0 x = false := by simp [case0, hrk_val]
          have hc1f : case1 x = false := by
            have hne : 2 + (L' - (centers x).card) ≠ 1 := by omega
            simp [case1, hrk_val, hne]
          by_cases hce : centers x = ∅
          · have hrkE : rk x = 2 + L' := by simp [hrk_val, hce]
            have hcPf : casePos x = false := by
              simp only [casePos, List.any_map, List.any_eq_false, Function.comp_apply, isMax, inCenter, hce,
                Finset.notMem_empty, and_false, decide_false, Bool.false_and]
              intro _ _; decide
            simp [hx0, hx1, hce, caseEmpty, hrkE, hc0f, hc1f, hcPf]
          · have hcne : (centers x).Nonempty := Finset.nonempty_iff_ne_empty.mpr hce
            have hc_pos : 1 ≤ (centers x).card := Finset.one_le_card.mpr hcne
            have hcL := hcenters_le_L' x hge2
            have hneE : rk x ≠ 2 + L' := by omega
            have hcEf : caseEmpty x = false := by simp [caseEmpty, hneE]
            simp only [hx0, hx1, ↓reduceIte, hc0f, hc1f, hcEf, Bool.false_eq_true, false_or, or_false]
            simp only [casePos, List.any_map, List.any_eq_true, Finset.mem_toList, Finset.mem_filter,
              Finset.mem_univ, true_and, Function.comp_apply, isMax, inCenter, hge2, true_and,
              Bool.and_eq_true, decide_eq_true_eq]
            constructor
            · rintro ⟨cstar, htest, hcin, hbig⟩
              have hsup_eq : (centers x).sup (fun c => W c (j b)) = W cstar (j b) := by
                apply le_antisymm
                · refine Finset.sup_le fun c' hc' => ?_
                  by_contra hlt
                  have hlt' : W cstar (j b) < W c' (j b) := by omega
                  exact (hmiss_iff c' x).mp (hbig c' hlt') hc'
                · exact Finset.le_sup (f := fun c => W c (j b)) hcin
              rw [hsup_eq]; exact htest
            · intro htest
              obtain ⟨cstar, hcin, hmax⟩ := Finset.exists_mem_eq_sup (centers x) hcne (fun c => W c (j b))
              refine ⟨cstar, by rwa [hmax] at htest, hcin, fun c' hlt => ?_⟩
              refine (hmiss_iff c' x).mpr fun hc' => ?_
              have hle : W c' (j b) ≤ (centers x).sup (fun c => W c (j b)) :=
                Finset.le_sup (f := fun c => W c (j b)) hc'
              rw [hmax] at hle; omega
    rw [hout_eq] at hcomb
    have hcost_b : n * (n + 1) + (1 + (n + 1) + (1 + n) + 4) ≤ 8 * (n + 1) ^ 2 := by
      have hpoly : n * (n + 1) + (1 + (n + 1) + (1 + n) + 4) + (7 * n * n + 13 * n + 1) =
          8 * (n + 1) ^ 2 := by ring
      omega
    exact (hisMax_ext.seq (h4cases.seq hcomb)).mono Set.Subset.rfl Set.Subset.rfl (by simp; omega) (by omega)
  -- Step 7: Chain all extensions from `base_circuit n` and check total size & NOT count!
  have hbase_S2 : Extends n (baseSigs n) S2
      (n * n + (2 * n * (n + 1) + 2 * n * (n + 1) + n * (2 * n * (n + 1)))) 0 :=
    (((Extends.of_subset Set.Subset.rfl).union hmiss_ext).trans
      (hS12_ext.mono (by rintro z (hz | hz); exact Or.inl hz; exact Or.inr (Or.inr hz)) Set.Subset.rfl le_rfl le_rfl)).mono
      Set.Subset.rfl (by rintro z (hz | hz); exact Or.inl hz; exact Or.inr hz) (by omega) (by omega)
  have hS2_S3 : Extends n S2 S3 ((L' + 3) + 4 * (L' + 2)) r' :=
    ((Extends.of_subset Set.Subset.rfl).union (hrk_thresh_ext.seq hdec_ext)).mono
      Set.Subset.rfl Set.Subset.rfl (by omega) (by omega)
  have hS3_S4 : Extends n S3 S4 (n * (2 * n)) 0 :=
    ((Extends.of_subset Set.Subset.rfl).union hinCenter_ext).mono
      Set.Subset.rfl Set.Subset.rfl (by omega) (by omega)
  have hAll : Extends n (baseSigs n) (Set.range outSig)
      ((n * n + (2 * n * (n + 1) + 2 * n * (n + 1) + n * (2 * n * (n + 1)))) +
        ((L' + 3) + 4 * (L' + 2)) + n * (2 * n) + m * (8 * (n + 1) ^ 2)) r' :=
    (((hbase_S2.seq (hS2_S3.mono Set.subset_union_right Set.Subset.rfl le_rfl le_rfl)).seq
      (hS3_S4.mono Set.subset_union_right Set.Subset.rfl le_rfl le_rfl)).seq
      (hout_ext.mono Set.subset_union_right Set.Subset.rfl le_rfl le_rfl)).mono
      Set.Subset.rfl Set.Subset.rfl (by omega) (by omega)
  obtain ⟨hF0, hB0, hm0, hn0, hW0⟩ := base_circuit n
  obtain ⟨C, hFC, hBC, hmC, hnC, _, hWC⟩ := hAll ⟨[], 0⟩ hF0 hB0 hW0
  have hCnot : notCount C ≤ r := by omega
  have hCsize : C.size ≤ 64 * (n + 1) ^ 2 * (n + m + 2) := by
    have hsum := notCount_add_monoCount C
    have h1 : monoCount C ≤ (n * n + (2 * n * (n + 1) + 2 * n * (n + 1) + n * (2 * n * (n + 1)))) +
        ((n + 3) + 4 * (n + 2)) + n * (2 * n) + m * (8 * (n + 1) ^ 2) := by omega
    have h2 : notCount C ≤ n + 2 := by omega
    have hpoly : (n * n + (2 * n * (n + 1) + 2 * n * (n + 1) + n * (2 * n * (n + 1)))) +
        ((n + 3) + 4 * (n + 2)) + n * (2 * n) + m * (8 * (n + 1) ^ 2) + (n + 2) +
        (62 * n ^ 3 + 247 * n ^ 2 + 310 * n + 115 + 56 * m * (n + 1) ^ 2) =
        64 * (n + 1) ^ 2 * (n + m + 2) := by ring
    omega
  have htap_ex : ∀ b : Fin m, ∃ w : Fin (n + 2 + C.size),
      ∀ x : Finset (Fin n), (C.wires (inputOf x)).getD w.val false = outSig b x :=
    fun b => hWC (outSig b) ⟨b, rfl⟩
  let tap : Fin m → Fin (n + 2 + C.size) := fun b => (htap_ex b).choose
  refine ⟨⟨C.gates, 0⟩, tap, hFC, hBC, by simp [Circuit.size], hCnot, hCsize, fun x b => (htap_ex b).choose_spec x⟩

end CommonNeighbor

end PEqualNP.Outside.L_meta_49526

open PEqualNP.Outside.L_meta_49526 in
theorem PEqualNP.Outside.L_meta_49526 :
letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (n m L D : Nat) (g : Fin n → Fin n → Prop),
  let X := Finset (Fin n)
  let centers := fun (x : X) => (Finset.univ : X).filter (fun c => ∀ u ∈ x, g u c)
  (∀ u v : Fin n, u ≠ v → (centers {u,v}).card ≤ L) →
  ∀ (A W : Fin n → Fin n → Nat) (j : Fin m → Fin n) (test : Fin m → Nat → Bool),
    let f := fun (x : X) (v : Fin n) => if x = ∅ then D
      else if x.card = 1 then x.sup (fun u => A u v)
      else (centers x).sup (fun c => W c v)
    ∀ r : Nat, L+2 < 2^r →
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin m → Fin (n+2+C.size)),
        PEqualNP.MetaComplexity.FanInTwo C ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧ C.output < n+2+C.size ∧
        PEqualNP.NotBracket.notCount C ≤ r ∧ C.size ≤ 64*(n+1)^2*(n+m+2) ∧
        ∀ x : X, let inputs := List.ofFn (fun v : Fin n => decide (v ∈ x)) ++ [false,true]
                 ∀ b, (C.wires inputs).getD (tap b).val false = test b (f x (j b)) := by
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  intro n m L D g X centers hL A W j test f r hr
  have hcent_eq : ∀ x : Finset (Fin n),
      centers x = (@Finset.filter (Fin n)
        (fun c => @decide (∀ u ∈ x, g u c) (Classical.propDecidable _) = true)
        (fun _ => instDecidableEqBool _ _) Finset.univ) := by
    intro x; dsimp only [centers]; ext c; simp
  have hL' : ∀ u v : Fin n, u ≠ v →
      ((@Finset.filter (Fin n)
        (fun c => @decide (∀ w ∈ (@insert (Fin n) (Finset (Fin n)) (@Finset.instInsert (Fin n) (instDecidableEqFin n)) u {v}), g w c)
          (Classical.propDecidable _) = true)
        (fun _ => instDecidableEqBool _ _) Finset.univ)).card ≤ L := by
    intro u v hne
    have heq : (@Finset.filter (Fin n)
        (fun c => @decide (∀ w ∈ (@insert (Fin n) (Finset (Fin n)) (@Finset.instInsert (Fin n) (instDecidableEqFin n)) u {v}), g w c)
          (Classical.propDecidable _) = true)
        (fun _ => instDecidableEqBool _ _) Finset.univ) =
        centers (@insert (Fin n) (Finset (Fin n)) (@Finset.instInsert (Fin n) (fun a b => Classical.propDecidable (a = b))) u {v}) := by
      rw [hcent_eq]; ext c; simp
    rw [heq]; exact hL u v hne
  obtain ⟨C, tap, hF, hB, hout, hnot, hsize, hspec⟩ := solve_49526 n m L D g hL' A W j test r hr
  refine ⟨C, tap, hF, hB, hout, hnot, hsize, fun x => ?_⟩
  dsimp only
  intro b
  have hinp : (List.ofFn (fun v : Fin n => decide (v ∈ x)) ++ [false, true]) = inputOf x := by
    dsimp only [inputOf]; congr 1; congr 1; funext v
    exact congrArg (@decide (v ∈ x)) (Subsingleton.elim _ _)
  have hf_eq : f x (j b) =
      (if x = ∅ then D else if x.card = 1 then x.sup (fun u => A u (j b))
       else ((@Finset.filter (Fin n)
        (fun c => @decide (∀ u ∈ x, g u c) (Classical.propDecidable _) = true)
        (fun _ => instDecidableEqBool _ _) Finset.univ)).sup (fun c => W c (j b))) := by
    dsimp only [f]; rw [hcent_eq x]
  rw [hinp, hf_eq]
  simpa only [] using hspec x b
