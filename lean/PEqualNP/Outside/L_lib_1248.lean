import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1248

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

/-! ### Part 3: Combinatorics of `named`, `feasible`, `enabled`, and Decision-Diagram DP -/

def namedF {n m : ℕ} (a b c d : Fin m → Finset (Fin n)) (js : List (Fin m)) (y : Finset (Fin n)) : Prop :=
  List.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
    (fun j _ prev y => ∃ u v, prev u ∧ u ⊆ v ∧ v ⊆ y ∧
      a j ⊆ u ∧ u ⊆ b j ∧ c j ⊆ v ∧ v ⊆ d j) js y

lemma namedF_mono {n m : ℕ} (a b c d : Fin m → Finset (Fin n))
    (js : List (Fin m)) {y₁ y₂ : Finset (Fin n)} (hsub : y₁ ⊆ y₂)
    (h : namedF a b c d js y₁) : namedF a b c d js y₂ := by
  cases js with
  | nil => trivial
  | cons j rest =>
    rcases h with ⟨u, v, hprev, huv, hvy, hau, hub, hcv, hvd⟩
    exact ⟨u, v, hprev, huv, hvy.trans hsub, hau, hub, hcv, hvd⟩

lemma namedF_tail {n m : ℕ} (a b c d : Fin m → Finset (Fin n))
    (j : Fin m) (rest : List (Fin m)) (y : Finset (Fin n))
    (h : namedF a b c d (j :: rest) y) : namedF a b c d rest Finset.univ := by
  rcases h with ⟨u, _, hprev, _⟩
  exact namedF_mono a b c d rest (Finset.subset_univ u) hprev

lemma namedF_drop {n m : ℕ} (a b c d : Fin m → Finset (Fin n))
    (k : ℕ) (js : List (Fin m)) (h : namedF a b c d js Finset.univ) :
    namedF a b c d (js.drop k) Finset.univ := by
  induction k generalizing js with
  | zero => simpa using h
  | succ k ih =>
    cases js with
    | nil => simp [namedF]
    | cons j rest =>
      simp only [List.drop_succ_cons]
      exact ih rest (namedF_tail a b c d j rest Finset.univ h)

lemma namedF_inter {n m : ℕ} (a b c d : Fin m → Finset (Fin n))
    (js : List (Fin m)) (y₁ y₂ : Finset (Fin n))
    (h : namedF a b c d js y₁)
    (hen : ∀ i ∈ js, a i ∪ c i ⊆ y₂) :
    namedF a b c d js (y₁ ∩ y₂) := by
  induction js generalizing y₁ with
  | nil => trivial
  | cons j rest ih =>
    rcases h with ⟨u, v, hprev, huv, hvy, hau, hub, hcv, hvd⟩
    have hj : a j ∪ c j ⊆ y₂ := hen j List.mem_cons_self
    have hrest : ∀ i ∈ rest, a i ∪ c i ⊆ y₂ := fun i hi => hen i (List.mem_cons_of_mem j hi)
    refine ⟨u ∩ y₂, v ∩ y₂, ih u hprev hrest, Finset.inter_subset_inter_right huv,
      Finset.inter_subset_inter_right hvy, ?_, Finset.inter_subset_left.trans hub,
      ?_, Finset.inter_subset_left.trans hvd⟩
    · exact Finset.subset_inter hau (Finset.subset_union_left.trans hj)
    · exact Finset.subset_inter hcv (Finset.subset_union_right.trans hj)

lemma namedF_replicate {n m : ℕ} (a b c d : Fin m → Finset (Fin n))
    (j : Fin m) (u : Finset (Fin n)) (ha : a j ⊆ u) (hb : u ⊆ b j) (hc : c j ⊆ u) (hd : u ⊆ d j) :
    ∀ k : ℕ, namedF a b c d (List.replicate k j) u := by
  intro k
  induction k with
  | zero => trivial
  | succ k ih =>
    exact ⟨u, u, ih, Finset.Subset.rfl, Finset.Subset.rfl, ha, hb, hc, hd⟩

lemma feasible_card_le {n m h : ℕ} (a b c d : Fin m → Finset (Fin n))
    (hmax : ∀ js : List (Fin m), js.length = h + 1 → ¬namedF a b c d js Finset.univ)
    (S : Finset (Fin m))
    (hfeas : ∃ js : List (Fin m), js.Nodup ∧ js.toFinset = S ∧ namedF a b c d js Finset.univ) :
    S.card ≤ h := by
  rcases hfeas with ⟨js, hnd, rfl, hnam⟩
  rw [List.toFinset_card_of_nodup hnd]
  by_contra hgt
  have hge : h + 1 ≤ js.length := by omega
  have hdrop := namedF_drop a b c d (js.length - (h + 1)) js hnam
  have hlen : (js.drop (js.length - (h + 1))).length = h + 1 := by simp; omega
  exact hmax _ hlen hdrop

lemma enabled_mono {n m : ℕ} {a c : Fin m → Finset (Fin n)} {S : Finset (Fin m)}
    {y₁ y₂ : Finset (Fin n)} (hsub : y₁ ⊆ y₂)
    (h : ∀ i ∈ S, a i ∪ c i ⊆ y₁) : ∀ i ∈ S, a i ∪ c i ⊆ y₂ :=
  fun i hi => (h i hi).trans hsub

def capOk {n m : ℕ} (a b c : Fin m → Finset (Fin n)) (cap : Option (Fin m)) (i : Fin m) : Bool :=
  match cap with
  | none => true
  | some j => decide (a i ∪ c i ⊆ b j)

def capSet {n m : ℕ} (b : Fin m → Finset (Fin n)) (cap : Option (Fin m)) (x : Finset (Fin n)) : Finset (Fin n) :=
  match cap with
  | none => x
  | some j => x ∩ b j

lemma cap_enabled_iff {n m : ℕ} (a b c : Fin m → Finset (Fin n)) (cap : Option (Fin m))
    (x : Finset (Fin n)) (i : Fin m) :
    (a i ∪ c i ⊆ capSet b cap x) ↔ (capOk a b c cap i = true ∧ a i ∪ c i ⊆ x) := by
  cases cap with
  | none => simp [capOk, capSet]
  | some j =>
    simp only [capOk, capSet, decide_eq_true_eq, Finset.subset_inter_iff]
    tauto

noncomputable def outEdgeSet {m W : ℕ} (edge : Fin m → Fin W → Bool → Fin W → Prop)
    (i : Fin m) (u : Fin W) : Finset (Bool × Fin W) := by
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  exact (Finset.univ : Finset (Bool × Fin W)).filter (fun p => edge i u p.1 p.2)

lemma mem_outEdgeSet {m W : ℕ} {edge : Fin m → Fin W → Bool → Fin W → Prop}
    {i : Fin m} {u : Fin W} {p : Bool × Fin W} :
    p ∈ outEdgeSet edge i u ↔ edge i u p.1 p.2 := by
  unfold outEdgeSet
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  simp

lemma sum_card_outEdgeSet {m W : ℕ} (edge : Fin m → Fin W → Bool → Fin W → Prop) :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∑ i : Fin m, ∑ u : Fin W, (outEdgeSet edge i u).card =
      ((Finset.univ : Finset (Fin m × Fin W × Bool × Fin W)).filter
        (fun v => edge v.1 v.2.1 v.2.2.1 v.2.2.2)).card := by
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  have h1 : (∑ i : Fin m, ∑ u : Fin W, (outEdgeSet edge i u).card) =
      ((Finset.univ : Finset (Fin m)).sigma (fun i =>
        (Finset.univ : Finset (Fin W)).sigma (fun u => outEdgeSet edge i u))).card := by
    simp [Finset.card_sigma]
  rw [h1]
  refine Finset.card_bij
    (fun s _ => (s.1, s.2.1, s.2.2.1, s.2.2.2))
    (fun s hs => ?_) (fun s₁ _ s₂ _ heq => ?_) (fun v hv => ?_)
  · simp only [Finset.mem_sigma, Finset.mem_univ, true_and, outEdgeSet, Finset.mem_filter] at hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
  · rcases s₁ with ⟨i₁, u₁, b₁, v₁⟩
    rcases s₂ with ⟨i₂, u₂, b₂, v₂⟩
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl, rfl, rfl⟩
    rfl
  · rcases v with ⟨i, u, b, v⟩
    have hv' : edge i u b v := (Finset.mem_filter.mp hv).2
    refine ⟨⟨i, ⟨u, (b, v)⟩⟩, ?_, rfl⟩
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and, outEdgeSet, Finset.mem_filter]
    exact hv'

noncomputable def dpStep {n m W : ℕ} (a b c : Fin m → Finset (Fin n))
    (edge : Fin m → Fin W → Bool → Fin W → Prop) (finals : Finset (Fin W))
    (cap : Option (Fin m)) (x : Finset (Fin n)) :
    (k : ℕ) → k ≤ m → Fin W → ℕ → Bool
  | 0, _, u, t => decide (u ∈ finals) && decide (t = 0)
  | k + 1, hk, u, t =>
    let i : Fin m := ⟨m - 1 - k, by omega⟩
    (outEdgeSet edge i u).toList.any fun p =>
      if p.1 then
        if capOk a b c cap i then
          decide (a i ∪ c i ⊆ x) && dpStep a b c edge finals cap x k (by omega) p.2 (t - 1)
        else false
      else
        dpStep a b c edge finals cap x k (by omega) p.2 t

lemma dpStep_spec {n m W : ℕ} (a b c : Fin m → Finset (Fin n))
    (edge : Fin m → Fin W → Bool → Fin W → Prop) (finals : Finset (Fin W))
    (cap : Option (Fin m)) (x : Finset (Fin n)) :
    ∀ (k : ℕ) (hk : k ≤ m) (u : Fin W) (t : ℕ),
      dpStep a b c edge finals cap x k hk u t = true ↔
      ∃ (S : Finset (Fin m)) (st : Fin (m + 1) → Fin W),
        (∀ r ∈ S, m - k ≤ r.val) ∧
        (∀ r ∈ S, a r ∪ c r ⊆ capSet b cap x) ∧
        t ≤ S.card ∧
        st ⟨m - k, by omega⟩ = u ∧
        st (Fin.last m) ∈ finals ∧
        ∀ r : Fin m, m - k ≤ r.val → edge r (st r.castSucc) (decide (r ∈ S)) (st r.succ) := by
  intro k
  induction k with
  | zero =>
    intro hk u t
    simp only [dpStep, Bool.and_eq_true, decide_eq_true_eq, Nat.sub_zero]
    constructor
    · rintro ⟨hu, rfl⟩
      refine ⟨∅, fun _ => u, by simp, by simp, by simp, rfl, hu, fun r hr => by omega⟩
    · rintro ⟨S, st, hSge, _, htcard, hstu, hstf, _⟩
      have hSe : S = ∅ := by
        ext r; simp only [Finset.notMem_empty, iff_false]
        intro hr; have := hSge r hr; omega
      subst hSe
      have hlast : (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m := Fin.ext rfl
      rw [hlast] at hstu
      exact ⟨hstu ▸ hstf, by simp at htcard; omega⟩
  | succ k ih =>
    intro hk u t
    let i : Fin m := ⟨m - 1 - k, by omega⟩
    have hi_val : i.val = m - (k + 1) := by dsimp only [i]; omega
    have hi_succ : i.val + 1 = m - k := by dsimp only [i]; omega
    simp only [dpStep, List.any_eq_true, Finset.mem_toList]
    constructor
    · rintro ⟨⟨br, v⟩, hedge, hbody⟩
      have hedge' : edge i u br v := mem_outEdgeSet.mp hedge
      cases br
      · dsimp only at hbody
        obtain ⟨S, st, hSge, hSen, hScard, hstv, hstf, hstedge⟩ := (ih (by omega) v t).mp hbody
        have hi_not : i ∉ S := fun hiS => by have := hSge i hiS; omega
        let st' : Fin (m + 1) → Fin W := fun q => if q.val = i.val then u else st q
        refine ⟨S, st', fun r hr => by have := hSge r hr; omega, hSen, hScard, ?_, ?_, ?_⟩
        · simp [st', hi_val]
        · have hne : m ≠ i.val := by dsimp only [i]; omega
          simp [st', hne, hstf]
        · intro r hr
          by_cases hri : r = i
          · rw [hri]
            have hc : i.castSucc.val = i.val := rfl
            have hs : i.succ.val ≠ i.val := by simp [Fin.succ]
            have hst_succ : st i.succ = v := by
              have heq : i.succ = ⟨m - k, by omega⟩ := Fin.ext (by simp [Fin.succ, hi_succ])
              rw [heq, hstv]
            simp only [st', hc, ↓reduceIte, hs, hst_succ, decide_eq_false hi_not]
            exact hedge'
          · have hrgt : m - k ≤ r.val := by
              have : r.val ≠ i.val := fun h => hri (Fin.ext h)
              omega
            have hc : r.castSucc.val ≠ i.val := by simp [Fin.castSucc]; omega
            have hs : r.succ.val ≠ i.val := by simp [Fin.succ]; omega
            simp only [st', hc, hs, ↓reduceIte]
            exact hstedge r hrgt
      · dsimp only at hbody
        by_cases hcap : capOk a b c cap i = true
        · dsimp only [i] at hcap
          simp only [hcap, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hbody
          rcases hbody with ⟨hen_i, hrec⟩
          obtain ⟨S, st, hSge, hSen, hScard, hstv, hstf, hstedge⟩ := (ih (by omega) v (t - 1)).mp hrec
          have hi_not : i ∉ S := fun hiS => by have := hSge i hiS; omega
          let st' : Fin (m + 1) → Fin W := fun q => if q.val = i.val then u else st q
          refine ⟨insert i S, st', ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro r hr
            rcases Finset.mem_insert.mp hr with rfl | hrS
            · omega
            · have := hSge r hrS; omega
          · intro r hr
            rcases Finset.mem_insert.mp hr with rfl | hrS
            · exact (cap_enabled_iff a b c cap x i).mpr ⟨hcap, hen_i⟩
            · exact hSen r hrS
          · rw [Finset.card_insert_of_notMem hi_not]; omega
          · simp [st', hi_val]
          · have hne : m ≠ i.val := by dsimp only [i]; omega
            simp [st', hne, hstf]
          · intro r hr
            by_cases hri : r = i
            · rw [hri]
              have hc : i.castSucc.val = i.val := rfl
              have hs : i.succ.val ≠ i.val := by simp [Fin.succ]
              have hst_succ : st i.succ = v := by
                have heq : i.succ = ⟨m - k, by omega⟩ := Fin.ext (by simp [Fin.succ, hi_succ])
                rw [heq, hstv]
              simp only [st', hc, ↓reduceIte, hs, hst_succ, Finset.mem_insert_self, decide_true]
              exact hedge'
            · have hrgt : m - k ≤ r.val := by
                have : r.val ≠ i.val := fun h => hri (Fin.ext h)
                omega
              have hc : r.castSucc.val ≠ i.val := by simp [Fin.castSucc]; omega
              have hs : r.succ.val ≠ i.val := by simp [Fin.succ]; omega
              have hmem : (r ∈ insert i S) ↔ (r ∈ S) := by simp [hri]
              simp only [st', hc, hs, ↓reduceIte, hmem]
              exact hstedge r hrgt
        · dsimp only [i] at hcap
          simp [hcap] at hbody
    · rintro ⟨S, st, hSge, hSen, hScard, hstu, hstf, hstedge⟩
      let br : Bool := decide (i ∈ S)
      let v : Fin W := st i.succ
      have hi_cast : st i.castSucc = u := by
        have heq : i.castSucc = ⟨m - (k + 1), by omega⟩ := Fin.ext (by simp [Fin.castSucc, hi_val])
        rw [heq, hstu]
      have hedge_i : edge i u br v := by
        rw [← hi_cast]; exact hstedge i (by omega)
      have hmem_out : (br, v) ∈ outEdgeSet edge i u := mem_outEdgeSet.mpr hedge_i
      refine ⟨(br, v), hmem_out, ?_⟩
      by_cases hiS : i ∈ S
      · have hbr : br = true := decide_eq_true hiS
        have hcap_en := (cap_enabled_iff a b c cap x i).mp (hSen i hiS)
        have hcap_t : capOk a b c cap ⟨m - 1 - k, by omega⟩ = true := hcap_en.1
        simp only [hbr, ↓reduceIte, hcap_t, Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨hcap_en.2, (ih (by omega) v (t - 1)).mpr ?_⟩
        refine ⟨S.erase i, st, ?_, fun r hr => hSen r (Finset.mem_of_mem_erase hr), ?_, ?_, hstf, ?_⟩
        · intro r hr
          rcases Finset.mem_erase.mp hr with ⟨hne, hrS⟩
          have hge := hSge r hrS
          have hnev : r.val ≠ i.val := fun h => hne (Fin.ext h)
          omega
        · rw [Finset.card_erase_of_mem hiS]; omega
        · have heq : (⟨m - k, by omega⟩ : Fin (m + 1)) = i.succ := Fin.ext (by simp [Fin.succ, hi_succ])
          rw [heq]
        · intro r hr
          have hne : r ≠ i := fun h => by subst h; omega
          have hmem : (r ∈ S.erase i) ↔ (r ∈ S) := by simp [hne]
          simp only [hmem]
          exact hstedge r (by omega)
      · have hbr : br = false := decide_eq_false hiS
        simp only [hbr, Bool.false_eq_true, ↓reduceIte]
        refine (ih (by omega) v t).mpr ⟨S, st, ?_, hSen, hScard, ?_, hstf, fun r hr => hstedge r (by omega)⟩
        · intro r hr
          have hge := hSge r hr
          have hne : r ≠ i := fun h => by subst h; exact hiS hr
          have hnev : r.val ≠ i.val := fun h => hne (Fin.ext h)
          omega
        · have heq : (⟨m - k, by omega⟩ : Fin (m + 1)) = i.succ := Fin.ext (by simp [Fin.succ, hi_succ])
          rw [heq]

lemma dpStep_top_iff {n m W : ℕ} (a b c d : Fin m → Finset (Fin n))
    (start : Fin W) (finals : Finset (Fin W)) (edge : Fin m → Fin W → Bool → Fin W → Prop)
    (hrec : ∀ S : Finset (Fin m),
      (∃ js : List (Fin m), js.Nodup ∧ js.toFinset = S ∧ namedF a b c d js Finset.univ) ↔
      ∃ st : Fin (m + 1) → Fin W, st 0 = start ∧ st (Fin.last m) ∈ finals ∧
        ∀ i : Fin m, edge i (st i.castSucc) (decide (i ∈ S)) (st i.succ))
    (cap : Option (Fin m)) (x : Finset (Fin n)) (t : ℕ) :
    dpStep a b c edge finals cap x m le_rfl start t = true ↔
    ∃ S : Finset (Fin m),
      (∃ js : List (Fin m), js.Nodup ∧ js.toFinset = S ∧ namedF a b c d js Finset.univ) ∧
      (∀ r ∈ S, a r ∪ c r ⊆ capSet b cap x) ∧ t ≤ S.card := by
  rw [dpStep_spec]
  constructor
  · rintro ⟨S, st, _, hSen, hScard, hst0, hstf, hstedge⟩
    refine ⟨S, (hrec S).mpr ⟨st, ?_, hstf, fun i => hstedge i (by omega)⟩, hSen, hScard⟩
    have h0 : (0 : Fin (m + 1)) = ⟨m - m, by omega⟩ := Fin.ext (by simp)
    rw [h0]; exact hst0
  · rintro ⟨S, hfeas, hSen, hScard⟩
    obtain ⟨st, hst0, hstf, hstedge⟩ := (hrec S).mp hfeas
    refine ⟨S, st, fun _ _ => by omega, hSen, hScard, ?_, hstf, fun i _ => hstedge i⟩
    have h0 : (⟨m - m, by omega⟩ : Fin (m + 1)) = 0 := Fin.ext (by simp)
    rw [h0]; exact hst0

/-! ### Part 4: Circuit Compilation of Stages 1–4 -/

lemma Extends.subset_sig {n : ℕ} (A : Finset (Fin n)) :
    Extends n (baseSigs n) {fun x => decide (A ⊆ x)} n 0 := by
  let l : List (Sig n) := A.toList.map (fun i => fun x => decide (i ∈ x))
  have hl_mem : ∀ f ∈ l, f ∈ baseSigs n := by
    intro f hf
    rcases List.mem_map.mp hf with ⟨i, _, rfl⟩
    exact Or.inr ⟨i, rfl⟩
  have hand := Extends.add_and_list l (Or.inl (Or.inr rfl)) hl_mem
  have heq : (fun x : Finset (Fin n) => l.all fun f => f x) = fun x => decide (A ⊆ x) := by
    funext x
    rw [Bool.eq_iff_iff]
    simp only [l, List.all_map, List.all_eq_true, Finset.mem_toList, Function.comp_apply,
      decide_eq_true_eq, Finset.subset_iff]
  rw [heq] at hand
  have hlen : l.length ≤ n := by
    simp only [l, List.length_map, Finset.length_toList]
    exact (Finset.card_le_univ A).trans (by simp)
  exact hand.mono Set.Subset.rfl Set.Subset.rfl hlen le_rfl

lemma Extends.dp_cap_sig {n m h W : ℕ} (a b c : Fin m → Finset (Fin n))
    (edge : Fin m → Fin W → Bool → Fin W → Prop) (finals : Finset (Fin W))
    (cap : Option (Fin m)) :
    let Base : Set (Sig n) :=
      baseSigs n ∪ Set.range (fun i : Fin m => fun x => decide (a i ∪ c i ⊆ x))
    Extends n Base
      (Set.range (fun p : Fin W × Fin (h + 1) => fun x => dpStep a b c edge finals cap x m le_rfl p.1 p.2.val))
      (2 * (h + 1) * ∑ i : Fin m, ∑ u : Fin W, (outEdgeSet edge i u).card) 0 := by
  intro Base
  let layerSigs (k : ℕ) (hk : k ≤ m) : Set (Sig n) :=
    Set.range (fun p : Fin W × Fin (h + 1) => fun x => dpStep a b c edge finals cap x k hk p.1 p.2.val)
  let Inv (k : ℕ) : Set (Sig n) :=
    if hk : k ≤ m then Base ∪ layerSigs k hk else Base
  have h0 : Extends n Base (Inv 0) 0 0 := by
    refine Extends.of_subset ?_
    simp only [Inv, Nat.zero_le, ↓reduceDIte]
    rintro z (hb | ⟨⟨u, t⟩, rfl⟩)
    · exact hb
    · by_cases hc : u ∈ finals ∧ t.val = 0
      · have heq : (fun x : Finset (Fin n) => dpStep a b c edge finals cap x 0 (Nat.zero_le m) u t.val) =
            fun _ => true := by funext x; simp [dpStep, hc.1, hc.2]
        dsimp only; rw [heq]; exact Or.inl (Or.inl (Or.inr rfl))
      · have heq : (fun x : Finset (Fin n) => dpStep a b c edge finals cap x 0 (Nat.zero_le m) u t.val) =
            fun _ => false := by
          funext x; unfold dpStep; rw [Bool.and_eq_false_iff]
          by_cases hu : u ∈ finals
          · right; exact decide_eq_false (fun ht => hc ⟨hu, ht⟩)
          · left; exact decide_eq_false hu
        dsimp only; rw [heq]; exact Or.inl (Or.inl (Or.inl rfl))
  let stepCost (k : ℕ) : ℕ :=
    if hk : k < m then
      2 * (h + 1) * ∑ u : Fin W, (outEdgeSet edge ⟨m - 1 - k, by omega⟩ u).card
    else 0
  have hstep : ∀ k < m, Extends n (Inv k) (Inv (k + 1)) (stepCost k) 0 := by
    intro k hk
    let i : Fin m := ⟨m - 1 - k, by omega⟩
    have hinv_k : Inv k = Base ∪ layerSigs k (by omega) := dif_pos (by omega)
    have hinv_k1 : Inv (k + 1) = Base ∪ layerSigs (k + 1) (by omega) := dif_pos (by omega)
    rw [hinv_k, hinv_k1]
    have hsc : stepCost k = 2 * (h + 1) * ∑ u : Fin W, (outEdgeSet edge i u).card := dif_pos hk
    rw [hsc]
    -- Build each (u, t) from Base ∪ layerSigs k in ≤ 2 * (outEdgeSet edge i u).card mono gates!
    have hperUT : ∀ (u : Fin W) (t : Fin (h + 1)),
        Extends n (Base ∪ layerSigs k (by omega))
          {fun x => dpStep a b c edge finals cap x (k + 1) (by omega) u t.val}
          (2 * (outEdgeSet edge i u).card) 0 := by
      intro u t
      let edges : List (Bool × Fin W) := (outEdgeSet edge i u).toList
      let termSig (p : Bool × Fin W) : Sig n := fun x =>
        if p.1 then
          if capOk a b c cap i then
            decide (a i ∪ c i ⊆ x) && dpStep a b c edge finals cap x k (by omega) p.2 (t.val - 1)
          else false
        else
          dpStep a b c edge finals cap x k (by omega) p.2 t.val
      have hterms : Extends n (Base ∪ layerSigs k (by omega))
          (Set.range (fun idx : Fin edges.length => termSig (edges[idx.val]'idx.isLt)))
          edges.length 0 := by
        simpa [mul_one, mul_zero] using Extends.add_range_fin
          (S := Base ∪ layerSigs k (by omega))
          (f := fun idx : Fin edges.length => termSig (edges[idx.val]'idx.isLt)) 1 0 (fun idx => by
            let p := edges[idx.val]'idx.isLt
            cases hp1 : p.1
            · have heq : termSig p = fun x => dpStep a b c edge finals cap x k (by omega) p.2 t.val := by
                funext x; simp [termSig, hp1]
              dsimp only [p] at heq ⊢; rw [heq]
              exact (Extends.of_subset (by rintro _ rfl; exact Or.inr ⟨(p.2, t), rfl⟩)).mono
                Set.Subset.rfl Set.Subset.rfl (by omega) le_rfl
            · by_cases hcap : capOk a b c cap i = true
              · have heq : termSig p = fun x =>
                    decide (a i ∪ c i ⊆ x) &&
                    dpStep a b c edge finals cap x k (by omega) p.2 (t.val - 1) := by
                  funext x; simp [termSig, hp1, hcap]
                dsimp only [p] at heq ⊢; rw [heq]
                exact Extends.add_and (Or.inl (Or.inr ⟨i, rfl⟩))
                  (Or.inr ⟨(p.2, ⟨t.val - 1, by omega⟩), rfl⟩)
              · have heq : termSig p = fun _ => false := by
                  funext x; simp [termSig, hp1, hcap]
                dsimp only [p] at heq ⊢; rw [heq]
                exact (Extends.of_subset (by rintro _ rfl; exact Or.inl (Or.inl (Or.inl (Or.inl rfl))))).mono
                  Set.Subset.rfl Set.Subset.rfl (by omega) le_rfl)
      let termList : List (Sig n) := edges.map termSig
      have hor : Extends n ((Base ∪ layerSigs k (by omega)) ∪
          Set.range (fun idx : Fin edges.length => termSig (edges[idx.val]'idx.isLt)))
          {fun x => termList.any fun f => f x} termList.length 0 := by
        refine Extends.add_or_list termList (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl rfl))))) ?_
        intro f hf
        rcases List.mem_map.mp hf with ⟨p, hp, rfl⟩
        rcases List.getElem_of_mem hp with ⟨idx, hidx, rfl⟩
        exact Or.inr ⟨⟨idx, hidx⟩, rfl⟩
      have heq_dp : (fun x => termList.any fun f => f x) =
          fun x => dpStep a b c edge finals cap x (k + 1) (by omega) u t.val := by
        funext x; simp only [termList, List.any_map, Function.comp_def, termSig, edges, dpStep, i]
      rw [heq_dp] at hor
      have hlen : edges.length = (outEdgeSet edge i u).card := Finset.length_toList _
      have htlen : termList.length = edges.length := List.length_map _
      exact (hterms.seq hor).mono Set.Subset.rfl Set.Subset.rfl (by omega) (by omega)
    have hlayer : Extends n (Base ∪ layerSigs k (by omega)) (layerSigs (k + 1) (by omega))
        (2 * (h + 1) * ∑ u : Fin W, (outEdgeSet edge i u).card) 0 := by
      have hforT : ∀ t : Fin (h + 1),
          Extends n (Base ∪ layerSigs k (by omega))
            (Set.range (fun u : Fin W => fun x => dpStep a b c edge finals cap x (k + 1) (by omega) u t.val))
            (∑ u : Fin W, 2 * (outEdgeSet edge i u).card) 0 := fun t => by
        simpa using Extends.add_range_fin_sum
          (S := Base ∪ layerSigs k (by omega))
          (f := fun u : Fin W => fun x => dpStep a b c edge finals cap x (k + 1) (by omega) u t.val)
          (fun u => 2 * (outEdgeSet edge i u).card) (fun _ => 0) (fun u => hperUT u t)
      have hall := Extends.parallel_fin_sum
        (S := Base ∪ layerSigs k (by omega))
        (T := fun t : Fin (h + 1) =>
          Set.range (fun u : Fin W => fun x => dpStep a b c edge finals cap x (k + 1) (by omega) u t.val))
        (fun _ => ∑ u : Fin W, 2 * (outEdgeSet edge i u).card) (fun _ => 0) hforT
      refine hall.mono Set.Subset.rfl ?_ ?_ (by simp)
      · rintro _ ⟨⟨u, t⟩, rfl⟩
        exact Set.mem_iUnion.mpr ⟨t, ⟨u, rfl⟩⟩
      · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum]
        ring_nf; exact le_rfl
    exact ((Extends.of_subset Set.subset_union_left).union hlayer).mono
      Set.Subset.rfl Set.Subset.rfl (by omega) (by omega)
  have hfold := Extends.fold_nat_sum m Inv stepCost (fun _ => 0) hstep
  have hcomb := h0.seq (hfold.mono Set.subset_union_right Set.Subset.rfl le_rfl le_rfl)
  have hinv_m : Inv m = Base ∪ layerSigs m le_rfl := dif_pos le_rfl
  rw [hinv_m] at hcomb
  refine hcomb.mono Set.Subset.rfl Set.subset_union_right ?_ (by simp)
  have hsum_eq : ∑ k ∈ Finset.range m, stepCost k =
      2 * (h + 1) * ∑ i : Fin m, ∑ u : Fin W, (outEdgeSet edge i u).card := by
    rw [Finset.mul_sum]
    have h1 : ∑ k ∈ Finset.range m, stepCost k =
        ∑ k : Fin m, 2 * (h + 1) * ∑ u : Fin W, (outEdgeSet edge ⟨m - 1 - k.val, by omega⟩ u).card := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun k _ => dif_pos k.isLt
    rw [h1]
    refine Finset.sum_bij (fun k _ => (⟨m - 1 - k.val, by omega⟩ : Fin m))
      (fun _ _ => Finset.mem_univ _)
      (fun k₁ _ k₂ _ heq => Fin.ext (by have := Fin.mk.inj heq; omega))
      (fun i _ => ⟨⟨m - 1 - i.val, by omega⟩, Finset.mem_univ _, Fin.ext (by dsimp only; omega)⟩)
      (fun _ _ => rfl)
  rw [zero_add, hsum_eq]

lemma exists_max_rank {n m h : ℕ} (a b c d : Fin m → Finset (Fin n))
    (hmax : ∀ js : List (Fin m), js.length = h + 1 → ¬namedF a b c d js Finset.univ)
    (x : Finset (Fin n)) :
    let feasible := fun (S : Finset (Fin m)) =>
      ∃ js : List (Fin m), js.Nodup ∧ js.toFinset = S ∧ namedF a b c d js Finset.univ
    ∃ M : ℕ, M ≤ h ∧
      (∃ S : Finset (Fin m), feasible S ∧ (∀ i ∈ S, a i ∪ c i ⊆ x) ∧ S.card = M) ∧
      (∀ S : Finset (Fin m), feasible S → (∀ i ∈ S, a i ∪ c i ⊆ x) → S.card ≤ M) := by
  intro feasible
  classical
  have hfeas_empty : feasible ∅ := ⟨[], List.nodup_nil, rfl, trivial⟩
  have hfeas_le : ∀ S, feasible S → S.card ≤ h := feasible_card_le a b c d hmax
  let okSets : Finset (Finset (Fin m)) :=
    Finset.univ.filter (fun S => feasible S ∧ ∀ i ∈ S, a i ∪ c i ⊆ x)
  have hne : okSets.Nonempty := ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfeas_empty, by simp⟩⟩
  obtain ⟨S0, hS0, hS0max⟩ := Finset.exists_max_image okSets Finset.card hne
  have hS0' := (Finset.mem_filter.mp hS0).2
  refine ⟨S0.card, hfeas_le S0 hS0'.1, ⟨S0, hS0'.1, hS0'.2, rfl⟩, fun S hSf hSe => ?_⟩
  exact hS0max S (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSf, hSe⟩)

lemma solve_1248 (n m h r : ℕ) (a b c d : Fin m → Finset (Fin n))
    (W : ℕ) (start : Fin W) (finals : Finset (Fin W))
    (edge : Fin m → Fin W → Bool → Fin W → Prop)
    (hrec : ∀ S : Finset (Fin m),
      (∃ js : List (Fin m), js.Nodup ∧ js.toFinset = S ∧ namedF a b c d js Finset.univ) ↔
      ∃ st : Fin (m + 1) → Fin W, st 0 = start ∧ st (Fin.last m) ∈ finals ∧
        ∀ i : Fin m, edge i (st i.castSucc) (decide (i ∈ S)) (st i.succ))
    (hr : h < 2 ^ r)
    (hmax : ∀ js : List (Fin m), js.length = h + 1 → ¬namedF a b c d js Finset.univ)
    (Ecard : ℕ) (hEcard : Ecard = ∑ i : Fin m, ∑ u : Fin W, (outEdgeSet edge i u).card) :
    ∃ (C : Circuit) (tap : Fin m → Fin (n + 2 + C.size)),
      FanInTwo C ∧ ReadsBack (n + 2) C ∧
      C.output < n + 2 + C.size ∧ notCount C ≤ r ∧
      C.size - notCount C ≤
        2 * n * m + 2 * (m + 1) * (h + 1) * Ecard + m * (2 * (h + 1) + 1) + 4 * h ∧
      ∀ (x : Finset (Fin n)) (j : Fin m),
        let input := List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]
        let out := (C.wires input).getD (tap j).val false
        let enabled := fun (S : Finset (Fin m)) (y : Finset (Fin n)) =>
          ∀ i ∈ S, (a i ∪ c i) ⊆ y
        let feasible := fun (S : Finset (Fin m)) =>
          ∃ js : List (Fin m), js.Nodup ∧ js.toFinset = S ∧ namedF a b c d js Finset.univ
        (a j ⊆ x ∧ x ⊆ b j → out = true) ∧ (c j ⊆ x ∧ x ⊆ d j → out = false) ∧
        (out = true ↔ a j ⊆ x ∧ a j ⊆ b j ∧
          ∃ S, feasible S ∧ enabled S (x ∩ b j) ∧
            ∀ T, feasible T → enabled T x → T.card ≤ S.card) := by
  let feasible := fun (S : Finset (Fin m)) =>
    ∃ js : List (Fin m), js.Nodup ∧ js.toFinset = S ∧ namedF a b c d js Finset.univ
  let R (x : Finset (Fin n)) : ℕ := (exists_max_rank a b c d hmax x).choose
  have hR_all : ∀ x, R x ≤ h ∧
      (∃ S, feasible S ∧ (∀ i ∈ S, a i ∪ c i ⊆ x) ∧ S.card = R x) ∧
      (∀ S, feasible S → (∀ i ∈ S, a i ∪ c i ⊆ x) → S.card ≤ R x) :=
    fun x => (exists_max_rank a b c d hmax x).choose_spec
  have hR_le : ∀ x, R x ≤ h := fun x => (hR_all x).1
  have hR_spec : ∀ (x : Finset (Fin n)) (t : ℕ),
      t ≤ R x ↔ ∃ S : Finset (Fin m), feasible S ∧ (∀ i ∈ S, a i ∪ c i ⊆ x) ∧ t ≤ S.card := by
    intro x t
    constructor
    · intro ht
      obtain ⟨S0, hS0f, hS0e, hS0c⟩ := (hR_all x).2.1
      exact ⟨S0, hS0f, hS0e, by omega⟩
    · rintro ⟨S, hSf, hSe, htS⟩
      exact le_trans htS ((hR_all x).2.2 S hSf hSe)
  -- Stage 1: en_j and lo'_j (≤ 2 * n * m mono, 0 NOTs)
  let enSig (j : Fin m) : Sig n := fun x => decide (a j ∪ c j ⊆ x)
  let loSig (j : Fin m) : Sig n := fun x => decide (a j ⊆ x ∧ a j ⊆ b j)
  have hEn : Extends n (baseSigs n) (Set.range enSig) (m * n) 0 := by
    simpa [mul_zero] using Extends.add_range_fin (S := baseSigs n) enSig n 0
      (fun j => Extends.subset_sig (a j ∪ c j))
  have hLo : Extends n (baseSigs n) (Set.range loSig) (m * n) 0 := by
    simpa [mul_zero] using Extends.add_range_fin (S := baseSigs n) loSig n 0 (fun j => by
      by_cases hab : a j ⊆ b j
      · have heq : loSig j = fun x => decide (a j ⊆ x) := by
          funext x; simp [loSig, hab]
        rw [heq]; exact Extends.subset_sig (a j)
      · have heq : loSig j = fun _ => false := by
          funext x; simp [loSig, hab]
        rw [heq]
        exact (Extends.of_subset (by rintro _ rfl; exact Or.inl (Or.inl rfl))).mono
          Set.Subset.rfl Set.Subset.rfl (Nat.zero_le _) le_rfl)
  have hStage1 : Extends n (baseSigs n) (Set.range enSig ∪ Set.range loSig) (2 * n * m) 0 :=
    (hEn.union hLo).mono Set.Subset.rfl Set.Subset.rfl (by ring_nf; omega) (by omega)
  -- Stage 2: DP for top cap (`none`) and each `some j` (≤ 2 * (m + 1) * (h + 1) * Ecard mono, 0 NOTs)
  let S1 : Set (Sig n) := baseSigs n ∪ (Set.range enSig ∪ Set.range loSig)
  let Gsig (t : Fin (h + 1)) : Sig n := fun x => decide (t.val ≤ R x)
  let Fsig (j : Fin m) (t : Fin (h + 1)) : Sig n :=
    fun x => dpStep a b c edge finals (some j) x m le_rfl start t.val
  have hG_eq : ∀ (t : Fin (h + 1)),
      Gsig t = fun x => dpStep a b c edge finals none x m le_rfl start t.val := by
    intro t; funext x; rw [Bool.eq_iff_iff]
    rw [dpStep_top_iff a b c d start finals edge hrec none x t.val]
    simp only [Gsig, decide_eq_true_eq, capSet]
    exact hR_spec x t.val
  have hDP_top : Extends n S1 (Set.range Gsig) (2 * (h + 1) * Ecard) 0 := by
    have h1 := Extends.dp_cap_sig (h := h) a b c edge finals none
    rw [← hEcard] at h1
    refine h1.mono (by rintro z (h | h); exact Or.inl h; exact Or.inr (Or.inl h)) ?_ le_rfl le_rfl
    rintro _ ⟨t, rfl⟩
    refine ⟨(start, t), ?_⟩
    exact (hG_eq t).symm
  have hDP_caps : Extends n S1 (⋃ j : Fin m, Set.range (Fsig j)) (m * (2 * (h + 1) * Ecard)) 0 := by
    have hall := Extends.parallel_fin_sum (S := S1)
      (T := fun j : Fin m => Set.range (Fsig j))
      (fun _ => 2 * (h + 1) * Ecard) (fun _ => 0) (fun j => by
        have h1 := Extends.dp_cap_sig (h := h) a b c edge finals (some j)
        rw [← hEcard] at h1
        refine h1.mono (by rintro z (h | h); exact Or.inl h; exact Or.inr (Or.inl h)) ?_ le_rfl le_rfl
        rintro _ ⟨t, rfl⟩
        exact ⟨(start, t), rfl⟩)
    simpa [Finset.sum_const, smul_eq_mul] using hall
  have hStage2 : Extends n S1 (Set.range Gsig ∪ ⋃ j : Fin m, Set.range (Fsig j))
      (2 * (m + 1) * (h + 1) * Ecard) 0 :=
    (hDP_top.union hDP_caps).mono Set.Subset.rfl Set.Subset.rfl (by ring_nf; omega) (by omega)
  -- Stage 3: Decode global rank R(x) (≤ 4 * h mono, ≤ r NOTs)
  let Esig (t : Fin (h + 1)) : Sig n := fun x => decide (R x = t.val)
  let S2 : Set (Sig n) := S1 ∪ (Set.range Gsig ∪ ⋃ j : Fin m, Set.range (Fsig j))
  have hStage3 : Extends n S2 (Set.range Esig) (4 * h) r :=
    (Extends.decode_rank r h hr R hR_le).mono (by
      rintro z ((rfl | rfl) | h)
      · exact Or.inl (Or.inl (Or.inl (Or.inl rfl)))
      · exact Or.inl (Or.inl (Or.inl (Or.inr rfl)))
      · exact Or.inr (Or.inl h)) Set.Subset.rfl le_rfl le_rfl
  -- Stage 4: Per-tap canonical output (≤ m * (2 * (h + 1) + 1) mono, 0 NOTs)
  let outSig (j : Fin m) : Sig n := fun x =>
    loSig j x && (List.finRange (h + 1)).any (fun t => Esig t x && Fsig j t x)
  let S3 : Set (Sig n) := S2 ∪ Set.range Esig
  have hStage4 : Extends n S3 (Set.range outSig) (m * (2 * (h + 1) + 1)) 0 := by
    simpa [mul_zero] using Extends.add_range_fin (S := S3) outSig (2 * (h + 1) + 1) 0 (fun j => by
      let pairSig (t : Fin (h + 1)) : Sig n := fun x => Esig t x && Fsig j t x
      have hpairs : Extends n S3 (Set.range pairSig) (h + 1) 0 := by
        simpa [mul_one, mul_zero] using Extends.add_range_fin (S := S3) pairSig 1 0 (fun t =>
          Extends.add_and (Or.inr ⟨t, rfl⟩)
            (Or.inl (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨j, ⟨t, rfl⟩⟩)))))
      let pairList : List (Sig n) := (List.finRange (h + 1)).map pairSig
      have hany : Extends n (S3 ∪ Set.range pairSig)
          {fun x => pairList.any fun f => f x} pairList.length 0 := by
        refine Extends.add_or_list pairList (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl rfl)))))) ?_
        intro f hf
        rcases List.mem_map.mp hf with ⟨t, _, rfl⟩
        exact Or.inr ⟨t, rfl⟩
      have heq_any : (fun x => pairList.any fun f => f x) =
          fun x => (List.finRange (h + 1)).any (fun t => Esig t x && Fsig j t x) := by
        funext x; simp only [pairList, pairSig, List.any_map]; rfl
      rw [heq_any] at hany
      have hfinal : Extends n (S3 ∪ {fun x => (List.finRange (h + 1)).any (fun t => Esig t x && Fsig j t x)})
          {outSig j} 1 0 :=
        Extends.add_and (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr ⟨j, rfl⟩))))) (Or.inr rfl)
      have hlen : pairList.length = h + 1 := by simp [pairList]
      exact ((hpairs.seq hany).seq hfinal).mono Set.Subset.rfl Set.Subset.rfl (by omega) (by omega))
  -- Combine Stages 1–4!
  have hAll := hStage1.seq ((hStage2.trans hStage3).seq (hStage4.mono (by
    rintro z ((h1 | h2) | h3)
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr h3)) Set.Subset.rfl le_rfl le_rfl))
  obtain ⟨hF0, hB0, hm0, hn0, hbase0⟩ := base_circuit n
  obtain ⟨C, hF, hB, hmono, hnot, _, hOuts⟩ := hAll ⟨[], 0⟩ hF0 hB0 hbase0
  have hex_tap : ∃ tap : Fin m → Fin (n + 2 + C.size),
      ∀ (j : Fin m) (x : Finset (Fin n)), (C.wires (inputOf x)).getD (tap j).val false = outSig j x :=
    ⟨fun j => (hOuts _ ⟨j, rfl⟩).choose, fun j => (hOuts _ ⟨j, rfl⟩).choose_spec⟩
  obtain ⟨tap, htap⟩ := hex_tap
  let C' : Circuit := ⟨C.gates, 0⟩
  have hF' : FanInTwo C' := hF
  have hB' : ReadsBack (n + 2) C' := hB
  have hnot' : notCount C' ≤ r := by change notCount C ≤ r; omega
  have hmono' : C'.size - notCount C' ≤ 2 * n * m + 2 * (m + 1) * (h + 1) * Ecard + m * (2 * (h + 1) + 1) + 4 * h := by
    have hmeq : C'.size - notCount C' = monoCount C := (monoCount_eq_size_sub_notCount C).symm
    rw [hmeq]; omega
  refine ⟨C', tap, hF', hB', by simp [C', Circuit.size], hnot', hmono', ?_⟩
  intro x j input out enabled _
  have hout_eq : out = outSig j x := htap j x
  have hchar : out = true ↔ a j ⊆ x ∧ a j ⊆ b j ∧
      ∃ S, feasible S ∧ enabled S (x ∩ b j) ∧ ∀ T, feasible T → enabled T x → T.card ≤ S.card := by
    rw [hout_eq]
    simp only [outSig, loSig, Esig, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
      List.mem_finRange, true_and]
    constructor
    · rintro ⟨⟨hajx, hajb⟩, ⟨t, hRt, hFt⟩⟩
      refine ⟨hajx, hajb, ?_⟩
      have hdp := (dpStep_top_iff a b c d start finals edge hrec (some j) x t.val).mp hFt
      rcases hdp with ⟨S, hSf, hSe, htS⟩
      refine ⟨S, hSf, hSe, fun T hTf hTe => ?_⟩
      have hTleR : T.card ≤ R x := (hR_spec x T.card).mpr ⟨T, hTf, hTe, le_rfl⟩
      omega
    · rintro ⟨hajx, hajb, ⟨S, hSf, hSe, hSmax⟩⟩
      refine ⟨⟨hajx, hajb⟩, ⟨⟨R x, by have := hR_le x; omega⟩, rfl, ?_⟩⟩
      rw [dpStep_top_iff a b c d start finals edge hrec (some j) x (R x)]
      refine ⟨S, hSf, hSe, ?_⟩
      obtain ⟨T0, hT0f, hT0e, hRleT0⟩ := (hR_spec x (R x)).mp le_rfl
      exact le_trans hRleT0 (hSmax T0 hT0f hT0e)
  refine ⟨?_, ?_, hchar⟩
  · rintro ⟨hajx, hxjb⟩
    rw [hchar]
    have hxinter : x ∩ b j = x := Finset.inter_eq_left.mpr hxjb
    obtain ⟨S0, hS0f, hS0e, hRleS0⟩ := (hR_spec x (R x)).mp le_rfl
    refine ⟨hajx, hajx.trans hxjb, S0, hS0f, hxinter.symm ▸ hS0e, fun T hTf hTe => ?_⟩
    have hTleR : T.card ≤ R x := (hR_spec x T.card).mpr ⟨T, hTf, hTe, le_rfl⟩
    omega
  · rintro ⟨hcjx, hxjd⟩
    rw [Bool.eq_false_iff]
    intro houtT
    rcases hchar.mp houtT with ⟨hajx, hajb, S, hSf, hSe, hSmax⟩
    by_cases hjS : j ∈ S
    · have hj_sub : a j ∪ c j ⊆ x ∩ b j := hSe j hjS
      have hrep := namedF_replicate a b c d j (x ∩ b j)
        (Finset.subset_union_left.trans hj_sub) Finset.inter_subset_right
        (Finset.subset_union_right.trans hj_sub) (Finset.inter_subset_left.trans hxjd) (h + 1)
      exact hmax (List.replicate (h + 1) j) (List.length_replicate)
        (namedF_mono a b c d _ (Finset.subset_univ _) hrep)
    · rcases hSf with ⟨js, hnd, rfl, hnam⟩
      have hnam_u : namedF a b c d js (x ∩ b j) := by
        have h1 := namedF_inter a b c d js Finset.univ (x ∩ b j) hnam (fun i hi =>
          hSe i (List.mem_toFinset.mpr hi))
        simpa using h1
      have hnam_cons : namedF a b c d (j :: js) Finset.univ :=
        ⟨x ∩ b j, x, hnam_u, Finset.inter_subset_left, Finset.subset_univ _,
          Finset.subset_inter hajx hajb, Finset.inter_subset_right, hcjx, hxjd⟩
      have hj_not_js : j ∉ js := fun hmem => hjS (List.mem_toFinset.mpr hmem)
      have hnd_cons : (j :: js).Nodup := List.nodup_cons.mpr ⟨hj_not_js, hnd⟩
      let T : Finset (Fin m) := insert j js.toFinset
      have hTf : feasible T := ⟨j :: js, hnd_cons, by simp [T], hnam_cons⟩
      have hTe : enabled T x := by
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hiS
        · exact Finset.union_subset hajx hcjx
        · exact (hSe i hiS).trans Finset.inter_subset_left
      have hcard_le := hSmax T hTf hTe
      have hTcard : T.card = js.toFinset.card + 1 := Finset.card_insert_of_notMem hjS
      omega

end PEqualNP.Outside.L_lib_1248

open PEqualNP.Outside.L_lib_1248 in
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket in
theorem PEqualNP.Outside.L_lib_1248 :
letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (n m h r : Nat) (a b c d : Fin m → Finset (Fin n)),
  let named := fun (js : List (Fin m)) =>
    List.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
      (fun j _ prev y => ∃ u v, prev u ∧ u ⊆ v ∧ v ⊆ y ∧
        a j ⊆ u ∧ u ⊆ b j ∧ c j ⊆ v ∧ v ⊆ d j) js Finset.univ
  let feasible := fun (S : Finset (Fin m)) =>
    ∃ js : List (Fin m), js.Nodup ∧ js.toFinset = S ∧ named js
  let recognizes := fun (W : Nat) (start : Fin W) (finals : Finset (Fin W))
      (edge : Fin m → Fin W → Bool → Fin W → Prop) =>
    ∀ S : Finset (Fin m), feasible S ↔
      ∃ st : Fin (m+1) → Fin W, st 0 = start ∧ st (Fin.last m) ∈ finals ∧
        ∀ i : Fin m, edge i (st i.castSucc) (decide (i ∈ S)) (st i.succ)
  let cost := fun (W : Nat) (edge : Fin m → Fin W → Bool → Fin W → Prop) =>
    (Finset.univ : Finset (Fin m × Fin W × Bool × Fin W)).filter
      (fun v => edge v.1 v.2.1 v.2.2.1 v.2.2.2)
  ∀ (W : Nat) (start : Fin W) (finals : Finset (Fin W))
    (edge : Fin m → Fin W → Bool → Fin W → Prop),
    recognizes W start finals edge → h < 2^r →
    (∀ js : List (Fin m), js.length = h+1 → ¬named js) →
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin m → Fin (n+2+C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
      C.output < n+2+C.size ∧ PEqualNP.NotBracket.notCount C ≤ r ∧
      C.size-PEqualNP.NotBracket.notCount C ≤
        2*n*m + 2*(m+1)*(h+1)*(cost W edge).card + m*(2*(h+1)+1) + 4*h ∧
      ∀ (x : Finset (Fin n)) (j : Fin m),
        let input := List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false,true]
        let out := (C.wires input).getD (tap j).val false
        let enabled := fun (S : Finset (Fin m)) (y : Finset (Fin n)) =>
          ∀ i ∈ S, (a i ∪ c i) ⊆ y
        (a j ⊆ x ∧ x ⊆ b j → out = true) ∧ (c j ⊆ x ∧ x ⊆ d j → out = false) ∧
        (out = true ↔ a j ⊆ x ∧ a j ⊆ b j ∧
          ∃ S, feasible S ∧ enabled S (x ∩ b j) ∧
            ∀ T, feasible T → enabled T x → T.card ≤ S.card) := by
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  intro n m h r a b c d named feasible recognizes cost W start finals edge hrec hr hmax
  have htoFinset : ∀ js : List (Fin m),
      @List.toFinset (Fin m) (fun a b => Classical.propDecidable (a = b)) js =
      @List.toFinset (Fin m) (instDecidableEqFin m) js :=
    fun js => Finset.ext fun a => by simp [List.mem_toFinset]
  have hfeas_iff : ∀ S : Finset (Fin m),
      feasible S ↔ (∃ js : List (Fin m), js.Nodup ∧
        @List.toFinset (Fin m) (instDecidableEqFin m) js = S ∧ namedF a b c d js Finset.univ) := by
    intro S
    change (∃ js : List (Fin m), js.Nodup ∧
      @List.toFinset (Fin m) (fun a b => Classical.propDecidable (a = b)) js = S ∧
      namedF a b c d js Finset.univ) ↔ _
    simp only [htoFinset]
  have hrec' : ∀ S : Finset (Fin m),
      (∃ js : List (Fin m), js.Nodup ∧
        @List.toFinset (Fin m) (instDecidableEqFin m) js = S ∧ namedF a b c d js Finset.univ) ↔
      ∃ st : Fin (m + 1) → Fin W, st 0 = start ∧ st (Fin.last m) ∈ finals ∧
        ∀ i : Fin m, edge i (st i.castSucc)
          (@decide (i ∈ S) (@Finset.decidableMem (Fin m) (instDecidableEqFin m) i S)) (st i.succ) := by
    intro S
    refine (hfeas_iff S).symm.trans ((hrec S).trans ?_)
    constructor
    · rintro ⟨st, h0, hf, he⟩
      exact ⟨st, h0, hf, fun i => by
        rw [Subsingleton.elim (@Finset.decidableMem (Fin m) (instDecidableEqFin m) i S)
          (Classical.propDecidable (i ∈ S))]
        exact he i⟩
    · rintro ⟨st, h0, hf, he⟩
      exact ⟨st, h0, hf, fun i => by
        rw [Subsingleton.elim (Classical.propDecidable (i ∈ S))
          (@Finset.decidableMem (Fin m) (instDecidableEqFin m) i S)]
        exact he i⟩
  have hres := solve_1248 n m h r a b c d W start finals edge hrec' hr hmax
    (cost W edge).card (sum_card_outEdgeSet edge).symm
  rcases hres with ⟨C, tap, hF, hB, hO, hN, hM, hProp⟩
  refine ⟨C, tap, hF, hB, hO, hN, hM, fun x j => ?_⟩
  have hxj := hProp x j
  have hin : (List.ofFn (fun i : Fin n => @decide (i ∈ x) (Classical.propDecidable _)) ++ [false, true]) =
      (List.ofFn (fun i : Fin n => @decide (i ∈ x) (@Finset.decidableMem (Fin n) (instDecidableEqFin n) i x)) ++ [false, true]) := by
    congr 1
    apply congrArg List.ofFn
    funext i
    exact congrArg (@decide (i ∈ x)) (Subsingleton.elim _ _)
  dsimp only at hxj ⊢
  rw [hin]
  simp only [hfeas_iff]
  have hmax_eq : ∀ s t : Finset (Fin n),
      @max (Finset (Fin n)) (@Finset.instMax (Fin n) (fun a b => Classical.propDecidable (a = b))) s t =
      @max (Finset (Fin n)) (@Finset.instMax (Fin n) (instDecidableEqFin n)) s t :=
    fun s t => Finset.ext fun u => by simp
  have hmin_eq : ∀ s t : Finset (Fin n),
      @min (Finset (Fin n)) (@Finset.instMin (Fin n) (fun a b => Classical.propDecidable (a = b))) s t =
      @min (Finset (Fin n)) (@Finset.instMin (Fin n) (instDecidableEqFin n)) s t :=
    fun s t => Finset.ext fun u => by simp
  convert hxj using 3
  all_goals first | rfl | (simp only [hmax_eq, hmin_eq]) | (congr 1; funext _; exact Subsingleton.elim _ _)
