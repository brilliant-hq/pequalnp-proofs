import Mathlib
import PEqualNP.Defs

-- Credit: the circuit building framework (Scheduled, Build, gate and ripple adder lemmas)
-- is adapted from the merged proof L_meta_25680 on upstream main (PR 39166), with the gate
-- shape changed to binary AND or OR and unary NOT.

namespace PEqualNP.Outside.L_lib_580

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

private abbrev Sig (N : ℕ) := (Fin N → Bool) → Bool

def Strict (gs : List Gate) : Prop :=
  ∀ g ∈ gs, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨ (g.op = .not ∧ g.inputs.length = 1)

private def Scheduled (N : ℕ) (k : ℕ) (S : Set (Sig N)) : Prop :=
  ∃ gs : List Gate, gs.length = k ∧ ReadsBack N ⟨gs, 0⟩ ∧ Strict gs ∧
    ∀ a ∈ S, ∃ i : ℕ, i < N + k ∧
      ∀ x : Fin N → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = a x

private theorem wireLength (C : Circuit) (w : List Bool) :
    (C.wires w).length = w.length + C.gates.length := by
  rcases C with ⟨gs, out⟩
  change (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    w).length = w.length + gs.length
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

private theorem startSched (N : ℕ) :
    Scheduled N 0 (Set.range (fun i : Fin N => fun x : Fin N → Bool => x i)) := by
  refine ⟨[], rfl, by simp [ReadsBack], by simp [Strict], ?_⟩
  intro a ha
  obtain ⟨i, rfl⟩ := Set.mem_range.mp ha
  refine ⟨i.val, by simp, fun x => ?_⟩
  change (List.ofFn x).getD i.val false = x i
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

private theorem realizeDeps {N k : ℕ} {S : Set (Sig N)} {gs : List Gate}
    (hw : ∀ a ∈ S, ∃ i : ℕ, i < N + k ∧
      ∀ x : Fin N → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = a x)
    (deps : List (Sig N)) (hdeps : ∀ a ∈ deps, a ∈ S) :
    ∃ is : List ℕ, is.length = deps.length ∧ (∀ i ∈ is, i < N + k) ∧
      ∀ x : Fin N → Bool,
        is.map (fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false) =
          deps.map (fun a => a x) := by
  induction deps with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | cons a deps ih =>
    obtain ⟨i, hi, hval⟩ := hw a (hdeps a List.mem_cons_self)
    obtain ⟨is, hlen, hbound, hvals⟩ := ih (fun b hb => hdeps b (List.mem_cons_of_mem a hb))
    refine ⟨i :: is, by simp [hlen], ?_, fun x => ?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact hbound j hj
    · simp only [List.map_cons, hval x, hvals x]

private theorem pushSched {N k : ℕ} {S : Set (Sig N)}
    (h : Scheduled N k S) (op : GateOp) (deps : List (Sig N)) (out : Sig N)
    (hsh : ((op = .and ∨ op = .or) ∧ deps.length = 2) ∨ (op = .not ∧ deps.length = 1))
    (hdeps : ∀ a ∈ deps, a ∈ S)
    (hval : ∀ x, out x = op.eval (deps.map fun a => a x)) :
    Scheduled N (k + 1) (insert out S) := by
  obtain ⟨gs, hgs, hr, hf, hw⟩ := h
  obtain ⟨is, his, hbound, hvalues⟩ := realizeDeps hw deps hdeps
  let g : Gate := ⟨op, is⟩
  have hlength (x : Fin N → Bool) :
      ((Circuit.mk gs 0).wires (List.ofFn x)).length = N + k := by
    rw [wireLength]; simpa using congrArg (N + ·) hgs
  have hsnoc (x : Fin N → Bool) :
      (Circuit.mk (gs ++ [g]) 0).wires (List.ofFn x) =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [out x] := by
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (Circuit.mk gs 0).wires (List.ofFn x) ++
      [op.eval (is.map fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false)] =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [out x]
    rw [hvalues x, hval x]
  refine ⟨gs ++ [g], by simp [hgs], ?_, ?_, ?_⟩
  · intro j hj i hi
    change j < (gs ++ [g]).length at hj
    change i ∈ ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).inputs at hi
    by_cases hj' : j < gs.length
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact hr j hj' i hi
    · have heq : j = gs.length := by simp at hj; omega
      subst j
      rw [List.getD_append_right _ _ _ _ le_rfl] at hi
      have hi' : i ∈ is := by simpa [g] using hi
      simpa [hgs] using hbound i hi'
  · intro g' hg'
    rcases List.mem_append.mp hg' with hg' | hg'
    · exact hf g' hg'
    · rw [List.mem_singleton.mp hg']
      change ((op = .and ∨ op = .or) ∧ is.length = 2) ∨ (op = .not ∧ is.length = 1)
      rw [his]; exact hsh
  · intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · refine ⟨N + k, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append_right _ _ _ _ (by simp [hlength x])]
      simp [hlength x]
    · obtain ⟨i, hi, hval'⟩ := hw a ha
      refine ⟨i, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append _ _ _ _ (by simpa [hlength x] using hi), hval' x]

private theorem finishFinBits {N k L : ℕ} {S : Set (Sig N)}
    (h : Scheduled N k S) (bits : Fin L → Sig N) (hbits : ∀ p, bits p ∈ S) :
    ∃ (C : Circuit) (out : Fin L → Fin (N + C.size)),
      Strict C.gates ∧ ReadsBack N C ∧ C.size = k ∧
      ∀ (p : Fin L) (x : Fin N → Bool),
        (C.wires (List.ofFn x)).getD (out p).val false = bits p x := by
  obtain ⟨gs, hgs, hr, hf, hw⟩ := h
  have hcho : ∀ p : Fin L, ∃ i : Fin (N + gs.length),
      ∀ x : Fin N → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i.val false = bits p x := by
    intro p
    obtain ⟨i, hi, hv⟩ := hw (bits p) (hbits p)
    exact ⟨⟨i, by omega⟩, hv⟩
  choose out hout using hcho
  refine ⟨⟨gs, 0⟩, out, hf, hr, hgs, ?_⟩
  intro p x
  exact hout p x

private structure Build {N : ℕ} (A B : Set (Sig N)) (b : ℕ) : Prop where
  run : ∀ {k : ℕ} {S : Set (Sig N)}, Scheduled N k S → A ⊆ S →
    ∃ c ≤ b, Scheduled N (k + c) (S ∪ B)

private theorem idleB {N : ℕ} {A B : Set (Sig N)} (h : B ⊆ A) : Build A B 0 :=
  ⟨fun hs ha => ⟨0, le_rfl, by simpa [Set.union_eq_left.mpr (h.trans ha)] using hs⟩⟩

private theorem relaxB {N : ℕ} {A A' B B' : Set (Sig N)} {b b' : ℕ}
    (H : Build A B b) (hA : A ⊆ A') (hB : B' ⊆ A' ∪ B) (hb : b ≤ b') : Build A' B' b' :=
  ⟨fun hs ha => by
    obtain ⟨c, hc, hsc⟩ := H.run hs (hA.trans ha)
    obtain ⟨gs, hgs, hr, hf, hw⟩ := hsc
    refine ⟨c, hc.trans hb, gs, hgs, hr, hf, fun a hmem => ?_⟩
    rcases hmem with h1 | h2
    · exact hw a (Or.inl h1)
    · rcases hB h2 with h2a | h2b
      · exact hw a (Or.inl (ha h2a))
      · exact hw a (Or.inr h2b)⟩

private theorem seqB {N : ℕ} {A B C : Set (Sig N)} {b c : ℕ}
    (H1 : Build A B b) (H2 : Build (A ∪ B) C c) : Build A (B ∪ C) (b + c) :=
  ⟨fun hs ha => by
    obtain ⟨c1, hc1, hs1⟩ := H1.run hs ha
    obtain ⟨c2, hc2, hs2⟩ := H2.run hs1
      (Set.union_subset (ha.trans Set.subset_union_left) Set.subset_union_right)
    refine ⟨c1 + c2, Nat.add_le_add hc1 hc2, ?_⟩
    simpa [Nat.add_assoc, Set.union_assoc] using hs2⟩

private theorem seq2B {N : ℕ} {A B C : Set (Sig N)} {b c : ℕ}
    (H1 : Build A B b) (H2 : Build (A ∪ B) C c) : Build A C (b + c) :=
  relaxB (seqB H1 H2) le_rfl (fun _ h => Or.inr (Or.inr h)) le_rfl

private theorem extB {N : ℕ} {A B : Set (Sig N)} {b : ℕ} (H : Build A B b) : Build A (A ∪ B) b :=
  relaxB H le_rfl le_rfl le_rfl

private theorem transB {N : ℕ} {A B C : Set (Sig N)} {b c : ℕ}
    (H1 : Build A B b) (H2 : Build B C c) : Build A C (b + c) :=
  relaxB (seqB H1 (relaxB H2 Set.subset_union_right Set.subset_union_right le_rfl))
    le_rfl (fun _ h => Or.inr (Or.inr h)) le_rfl

private theorem gateB {N : ℕ} {A : Set (Sig N)} (op : GateOp) (deps : List (Sig N)) (out : Sig N)
    (hsh : ((op = .and ∨ op = .or) ∧ deps.length = 2) ∨ (op = .not ∧ deps.length = 1))
    (hdeps : ∀ a ∈ deps, a ∈ A)
    (hval : ∀ x, out x = op.eval (deps.map fun a => a x)) :
    Build A {out} 1 :=
  ⟨fun hs ha => ⟨1, le_rfl, by
    simpa [Set.union_singleton] using
      pushSched hs op deps out hsh (fun a hm => ha (hdeps a hm)) hval⟩⟩

private theorem notB {N : ℕ} {A : Set (Sig N)} {f : Sig N} (hf : f ∈ A) :
    Build A {fun x => !(f x)} 1 :=
  gateB .not [f] (fun x => !(f x)) (Or.inr ⟨rfl, rfl⟩) (by simpa using hf) (fun _ => rfl)

private theorem andB {N : ℕ} {A : Set (Sig N)} {f g : Sig N} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {fun x => f x && g x} 1 :=
  gateB .and [f, g] (fun x => f x && g x) (Or.inl ⟨Or.inl rfl, rfl⟩)
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with rfl | rfl <;> assumption)
    (fun _ => by simp [GateOp.eval])

private theorem orB {N : ℕ} {A : Set (Sig N)} {f g : Sig N} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {fun x => f x || g x} 1 :=
  gateB .or [f, g] (fun x => f x || g x) (Or.inl ⟨Or.inr rfl, rfl⟩)
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with rfl | rfl <;> assumption)
    (fun _ => by simp [GateOp.eval])

private theorem xor_eq_or_and_not_and (a b : Bool) :
    xor a b = ((a || b) && !(a && b)) := by
  cases a <;> cases b <;> rfl

private theorem xorB {N : ℕ} {A : Set (Sig N)} {f g : Sig N} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {fun x => xor (f x) (g x)} 4 := by
  let s1 : Sig N := fun x => f x || g x
  let s2 : Sig N := fun x => f x && g x
  let s3 : Sig N := fun x => !(s2 x)
  let s4 : Sig N := fun x => s1 x && s3 x
  have h1 : Build A {s1} 1 := orB hf hg
  have h2 : Build (A ∪ {s1}) {s2} 1 := andB (Or.inl hf) (Or.inl hg)
  have h3 : Build (A ∪ ({s1} ∪ {s2})) {s3} 1 := notB (Or.inr (Or.inr rfl))
  have h4 : Build (A ∪ (({s1} ∪ {s2}) ∪ {s3})) {s4} 1 :=
    andB (Or.inr (Or.inl (Or.inl rfl))) (Or.inr (Or.inr rfl))
  have heq : s4 = fun x => xor (f x) (g x) := by
    funext x
    simp only [s4, s3, s2, s1]
    exact (xor_eq_or_and_not_and (f x) (g x)).symm
  refine relaxB (seqB (seqB (seqB h1 h2) h3) h4) le_rfl ?_ (by omega)
  intro h hm
  rw [Set.mem_singleton_iff.mp hm, ← heq]
  exact Or.inr (Or.inr rfl)

private theorem iteB {N : ℕ} {A : Set (Sig N)} {c a b : Sig N}
    (hc : c ∈ A) (ha : a ∈ A) (hb : b ∈ A) :
    Build A {fun x => if c x then a x else b x} 4 := by
  let nc : Sig N := fun x => !(c x)
  let t1 : Sig N := fun x => c x && a x
  let t2 : Sig N := fun x => nc x && b x
  let out : Sig N := fun x => t1 x || t2 x
  have h1 : Build A {nc} 1 := notB hc
  have h2 : Build (A ∪ {nc}) {t1} 1 := andB (Or.inl hc) (Or.inl ha)
  have h3 : Build (A ∪ ({nc} ∪ {t1})) {t2} 1 :=
    andB (Or.inr (Or.inl rfl)) (Or.inl hb)
  have h4 : Build (A ∪ (({nc} ∪ {t1}) ∪ {t2})) {out} 1 :=
    orB (Or.inr (Or.inl (Or.inr rfl))) (Or.inr (Or.inr rfl))
  have heq : out = fun x => if c x then a x else b x := by
    funext x
    simp only [out, t1, t2, nc]
    cases c x <;> cases a x <;> cases b x <;> rfl
  refine relaxB (seqB (seqB (seqB h1 h2) h3) h4) le_rfl ?_ (by omega)
  intro h hm
  rw [Set.mem_singleton_iff.mp hm, ← heq]
  exact Or.inr (Or.inr rfl)

private theorem listB {N : ℕ} {α : Type*} {A : Set (Sig N)} (F : α → Set (Sig N)) (c : ℕ)
    (xs : List α) (h : ∀ a ∈ xs, Build A (F a) c) :
    Build A (⋃ a ∈ xs, F a) (xs.length * c) := by
  induction xs with
  | nil =>
    simp only [List.length_nil, Nat.zero_mul]
    exact idleB (by simp)
  | cons a xs ih =>
    have h1 := h a List.mem_cons_self
    have h2 : Build (A ∪ F a) (⋃ b ∈ xs, F b) (xs.length * c) :=
      relaxB (ih (fun b hb => h b (List.mem_cons_of_mem a hb)))
        Set.subset_union_left Set.subset_union_right le_rfl
    have hseq := seqB h1 h2
    refine relaxB hseq le_rfl ?_ (by simp [Nat.succ_mul, Nat.add_comm])
    intro f hf
    simp only [Set.mem_iUnion, List.mem_cons] at hf
    rcases hf with ⟨b, rfl | hb, hfb⟩
    · exact Or.inr (Or.inl hfb)
    · exact Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hb, hfb⟩⟩))

private theorem finB {N n : ℕ} {A : Set (Sig N)} (F : Fin n → Set (Sig N)) (c : ℕ)
    (h : ∀ i : Fin n, Build A (F i) c) :
    Build A (⋃ i : Fin n, F i) (n * c) := by
  have hl := listB F c (List.finRange n) (fun i _ => h i)
  refine relaxB hl le_rfl ?_ (by simp)
  intro f hf
  rcases Set.mem_iUnion.mp hf with ⟨i, hfi⟩
  exact Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨List.mem_finRange i, hfi⟩⟩)

private theorem finSigB {N n : ℕ} {A : Set (Sig N)} (F : Fin n → Sig N) (c : ℕ)
    (h : ∀ i : Fin n, Build A {F i} c) :
    Build A (Set.range F) (n * c) := by
  refine relaxB (finB (fun i => {F i}) c h) le_rfl ?_ le_rfl
  intro f hf
  rcases Set.mem_range.mp hf with ⟨i, rfl⟩
  exact Or.inr (Set.mem_iUnion.mpr ⟨i, rfl⟩)

private theorem fin2SigB {N n1 n2 : ℕ} {A : Set (Sig N)} (F : Fin n1 → Fin n2 → Sig N) (c : ℕ)
    (h : ∀ i j, Build A {F i j} c) :
    Build A {f | ∃ i j, F i j = f} (n1 * (n2 * c)) := by
  have h1 : Build A (⋃ i : Fin n1, Set.range (F i)) (n1 * (n2 * c)) :=
    finB (fun i => Set.range (F i)) (n2 * c) (fun i => finSigB (F i) c (fun j => h i j))
  refine relaxB h1 le_rfl ?_ le_rfl
  rintro f ⟨i, j, rfl⟩
  exact Or.inr (Set.mem_iUnion.mpr ⟨i, ⟨j, rfl⟩⟩)

private theorem unionB {N : ℕ} {A B C : Set (Sig N)} {b c : ℕ}
    (H1 : Build A B b) (H2 : Build A C c) : Build A (B ∪ C) (b + c) :=
  seqB H1 (relaxB H2 Set.subset_union_left Set.subset_union_right le_rfl)

private theorem andListB {N : ℕ} {A : Set (Sig N)} (xs : List (Sig N))
    (hxs : ∀ f ∈ xs, f ∈ A) (htrue : (fun _ => true) ∈ A) :
    Build A {fun x => xs.all (fun f => f x)} xs.length := by
  induction xs with
  | nil =>
    exact idleB (by simpa using htrue)
  | cons f xs ih =>
    have h1 := ih (fun g hg => hxs g (List.mem_cons_of_mem f hg))
    have h2 : Build (A ∪ {fun x => xs.all (fun g => g x)})
        {fun x => (f :: xs).all (fun g => g x)} 1 := by
      have heq : (fun x => (f :: xs).all (fun g => g x)) =
          (fun x => f x && xs.all (fun g => g x)) := by
        funext x; simp [List.all_cons]
      rw [heq]
      exact andB (Or.inl (hxs f List.mem_cons_self)) (Or.inr rfl)
    exact relaxB (seqB h1 h2) le_rfl (by intro a ha; exact Or.inr (Or.inr ha)) (by simp)

private theorem orListB {N : ℕ} {A : Set (Sig N)} (xs : List (Sig N))
    (hxs : ∀ f ∈ xs, f ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {fun x => xs.any (fun f => f x)} xs.length := by
  induction xs with
  | nil =>
    exact idleB (by simpa using hfalse)
  | cons f xs ih =>
    have h1 := ih (fun g hg => hxs g (List.mem_cons_of_mem f hg))
    have h2 : Build (A ∪ {fun x => xs.any (fun g => g x)})
        {fun x => (f :: xs).any (fun g => g x)} 1 := by
      have heq : (fun x => (f :: xs).any (fun g => g x)) =
          (fun x => f x || xs.any (fun g => g x)) := by
        funext x; simp [List.any_cons]
      rw [heq]
      exact orB (Or.inl (hxs f List.mem_cons_self)) (Or.inr rfl)
    exact relaxB (seqB h1 h2) le_rfl (by intro a ha; exact Or.inr (Or.inr ha)) (by simp)

private def xorList (bs : List Bool) : Bool :=
  bs.foldr xor false

private theorem xorListB {N : ℕ} {A : Set (Sig N)} (xs : List (Sig N))
    (hxs : ∀ f ∈ xs, f ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {fun x => xorList (xs.map fun f => f x)} (4 * xs.length) := by
  induction xs with
  | nil =>
    exact idleB (by simpa [xorList] using hfalse)
  | cons f xs ih =>
    have h1 := ih (fun g hg => hxs g (List.mem_cons_of_mem f hg))
    have h2 : Build (A ∪ {fun x => xorList (xs.map fun g => g x)})
        {fun x => xorList ((f :: xs).map fun g => g x)} 4 := by
      have heq : (fun x => xorList ((f :: xs).map fun g => g x)) =
          (fun x => xor (f x) (xorList (xs.map fun g => g x))) := by
        funext x; rfl
      rw [heq]
      exact xorB (Or.inl (hxs f List.mem_cons_self)) (Or.inr rfl)
    exact relaxB (seqB h1 h2) le_rfl (by intro a ha; exact Or.inr (Or.inr ha)) (by simp; omega)

private theorem iterB {N : ℕ} {α : Type*} (Sigs : ((Fin N → Bool) → α) → Set (Sig N))
    (step : ℕ → α → α) (c : ℕ) (Base : Set (Sig N))
    (hstep : ∀ t (st : (Fin N → Bool) → α),
      Build (Base ∪ Sigs st) (Sigs (fun x => step t (st x))) c) :
    ∀ T (st0 : (Fin N → Bool) → α),
      Build (Base ∪ Sigs st0)
        (Sigs (fun x => (List.range T).foldl (fun s t => step t s) (st0 x)))
        (T * c) := by
  intro T
  induction T with
  | zero =>
    intro st0
    simpa using idleB (A := Base ∪ Sigs st0) (B := Sigs st0) Set.subset_union_right
  | succ T ih =>
    intro st0
    let stT : (Fin N → Bool) → α :=
      fun x => (List.range T).foldl (fun s t => step t s) (st0 x)
    have h1 : Build (Base ∪ Sigs st0) (Sigs stT) (T * c) := ih st0
    have h2 : Build ((Base ∪ Sigs st0) ∪ Sigs stT) (Sigs (fun x => step T (stT x))) c :=
      relaxB (hstep T stT)
        (Set.union_subset (Set.subset_union_left.trans Set.subset_union_left) Set.subset_union_right)
        Set.subset_union_right le_rfl
    have heq : (fun x => (List.range (T + 1)).foldl (fun s t => step t s) (st0 x)) =
        (fun x => step T (stT x)) := by
      funext x
      simp [List.range_succ, List.foldl_append, stT]
    rw [heq]
    exact relaxB (seq2B h1 h2) le_rfl Set.subset_union_right (by simp [Nat.succ_mul])

private def faSum (a b c : Bool) : Bool := xor (xor a b) c

private def faCarry (a b c : Bool) : Bool := (a && b) || (xor a b && c)

private theorem fullAdderB {N : ℕ} {A : Set (Sig N)} {fa fb fc : Sig N}
    (ha : fa ∈ A) (hb : fb ∈ A) (hc : fc ∈ A) :
    Build A ({fun x => faSum (fa x) (fb x) (fc x), fun x => faCarry (fa x) (fb x) (fc x)}) 9 := by
  let abOr : Sig N := fun x => fa x || fb x
  let abAnd : Sig N := fun x => fa x && fb x
  let abNand : Sig N := fun x => !(abAnd x)
  let t1 : Sig N := fun x => abOr x && abNand x
  let tcOr : Sig N := fun x => t1 x || fc x
  let tcAnd : Sig N := fun x => t1 x && fc x
  let tcNand : Sig N := fun x => !(tcAnd x)
  let sOut : Sig N := fun x => tcOr x && tcNand x
  let cOut : Sig N := fun x => abAnd x || tcAnd x
  have h1 : Build A {abOr} 1 := orB ha hb
  have h2 : Build (A ∪ {abOr}) {abAnd} 1 := andB (Or.inl ha) (Or.inl hb)
  have h3 : Build (A ∪ ({abOr} ∪ {abAnd})) {abNand} 1 := notB (Or.inr (Or.inr rfl))
  have h4 : Build (A ∪ (({abOr} ∪ {abAnd}) ∪ {abNand})) {t1} 1 :=
    andB (Or.inr (Or.inl (Or.inl rfl))) (Or.inr (Or.inr rfl))
  have h5 : Build (A ∪ ((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1})) {tcOr} 1 :=
    orB (Or.inr (Or.inr rfl)) (Or.inl hc)
  have h6 : Build (A ∪ (((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1}) ∪ {tcOr})) {tcAnd} 1 :=
    andB (Or.inr (Or.inl (Or.inr rfl))) (Or.inl hc)
  have h7 : Build (A ∪ ((((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1}) ∪ {tcOr}) ∪ {tcAnd})) {tcNand} 1 :=
    notB (Or.inr (Or.inr rfl))
  have h8 : Build (A ∪ (((((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1}) ∪ {tcOr}) ∪ {tcAnd}) ∪ {tcNand})) {sOut} 1 :=
    andB (Or.inr (Or.inl (Or.inl (Or.inr rfl)))) (Or.inr (Or.inr rfl))
  have h9 : Build (A ∪ ((((((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1}) ∪ {tcOr}) ∪ {tcAnd}) ∪ {tcNand}) ∪ {sOut})) {cOut} 1 :=
    orB (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr rfl))))))))
        (Or.inr (Or.inl (Or.inl (Or.inr rfl))))
  have hall := seqB (seqB (seqB (seqB (seqB (seqB (seqB (seqB h1 h2) h3) h4) h5) h6) h7) h8) h9
  have hsEq : sOut = fun x => faSum (fa x) (fb x) (fc x) := by
    funext x
    simp only [sOut, tcOr, tcNand, tcAnd, t1, abOr, abNand, abAnd, faSum]
    rw [xor_eq_or_and_not_and (fa x) (fb x), xor_eq_or_and_not_and _ (fc x)]
  have hcEq : cOut = fun x => faCarry (fa x) (fb x) (fc x) := by
    funext x
    simp only [cOut, tcAnd, t1, abOr, abNand, abAnd, faCarry]
    rw [xor_eq_or_and_not_and (fa x) (fb x)]
  refine relaxB hall le_rfl ?_ (by omega)
  intro f hf
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl
  · rw [← hsEq]
    exact Or.inr (Or.inl (Or.inr rfl))
  · rw [← hcEq]
    exact Or.inr (Or.inr rfl)

private def rippleCarry (a b : ℕ) : ℕ → Bool
  | 0 => false
  | j + 1 => faCarry (a.testBit j) (b.testBit j) (rippleCarry a b j)

private theorem testBit_eq_decide_div_mod (x j : ℕ) :
    x.testBit j = decide ((x / 2 ^ j) % 2 = 1) := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two]
  have hlt : (x / 2 ^ j) % 2 < 2 := Nat.mod_lt _ (by omega)
  have hcases : (x / 2 ^ j) % 2 = 0 ∨ (x / 2 ^ j) % 2 = 1 := by omega
  rcases hcases with h | h <;> simp [h]

private theorem mod_two_pow_succ_eq (a j : ℕ) :
    a % 2 ^ (j + 1) = a % 2 ^ j + (if a.testBit j then 2 ^ j else 0) := by
  have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
  have hdiv1 := Nat.div_add_mod a (2 ^ j)
  have hdiv2 := Nat.div_add_mod (a / 2 ^ j) 2
  have ha_eq : a = (a % 2 ^ j + 2 ^ j * ((a / 2 ^ j) % 2)) + 2 ^ (j + 1) * (a / 2 ^ j / 2) := by
    rw [Nat.pow_succ]
    have h1 : 2 ^ j * (a / 2 ^ j) = 2 ^ j * (2 * (a / 2 ^ j / 2) + (a / 2 ^ j) % 2) := by
      rw [hdiv2]
    rw [Nat.mul_add] at h1
    have h2 : 2 ^ j * (2 * (a / 2 ^ j / 2)) = 2 ^ j * 2 * (a / 2 ^ j / 2) := by ring
    omega
  have hlt_rem : a % 2 ^ j + 2 ^ j * ((a / 2 ^ j) % 2) < 2 ^ (j + 1) := by
    have h1 : a % 2 ^ j < 2 ^ j := Nat.mod_lt _ hpos
    have h2 : (a / 2 ^ j) % 2 ≤ 1 := by have := Nat.mod_lt (a / 2 ^ j) (by omega : 0 < 2); omega
    have h3 : 2 ^ j * ((a / 2 ^ j) % 2) ≤ 2 ^ j := by
      calc 2 ^ j * ((a / 2 ^ j) % 2) ≤ 2 ^ j * 1 := Nat.mul_le_mul_left _ h2
        _ = 2 ^ j := Nat.mul_one _
    rw [Nat.pow_succ]; omega
  have h1 : a % 2 ^ (j + 1) = a % 2 ^ j + 2 ^ j * ((a / 2 ^ j) % 2) := by
    conv_lhs => rw [ha_eq]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt_rem]
  rw [h1, testBit_eq_decide_div_mod a j]
  have hcases : (a / 2 ^ j) % 2 = 0 ∨ (a / 2 ^ j) % 2 = 1 := by
    have := Nat.mod_lt (a / 2 ^ j) (by omega : 0 < 2); omega
  rcases hcases with h | h <;> simp [h]

private theorem rippleCarry_spec (a b : ℕ) :
    ∀ j : ℕ,
      rippleCarry a b j = decide (2 ^ j ≤ a % 2 ^ j + b % 2 ^ j) ∧
      (a + b).testBit j = faSum (a.testBit j) (b.testBit j) (rippleCarry a b j) := by
  intro j
  have hcarry : ∀ k : ℕ, rippleCarry a b k = decide (2 ^ k ≤ a % 2 ^ k + b % 2 ^ k) := by
    intro k
    induction k with
    | zero => simp [rippleCarry, Nat.mod_one]
    | succ k ih =>
      unfold rippleCarry
      rw [ih, mod_two_pow_succ_eq a k, mod_two_pow_succ_eq b k]
      have ha_lt : a % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
      have hb_lt : b % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
      have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
      cases h1 : a.testBit k <;> cases h2 : b.testBit k <;>
        by_cases h3 : 2 ^ k ≤ a % 2 ^ k + b % 2 ^ k <;>
        simp [faCarry, h3, hp] <;> omega
  refine ⟨hcarry j, ?_⟩
  rw [hcarry j]
  have hdiv : (a + b) / 2 ^ j =
      a / 2 ^ j + b / 2 ^ j + (a % 2 ^ j + b % 2 ^ j) / 2 ^ j := by
    have ha := Nat.div_add_mod a (2 ^ j)
    have hb := Nat.div_add_mod b (2 ^ j)
    have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
    have hsum : a + b = (a % 2 ^ j + b % 2 ^ j) + (a / 2 ^ j + b / 2 ^ j) * 2 ^ j := by
      have : 2 ^ j * (a / 2 ^ j) = (a / 2 ^ j) * 2 ^ j := Nat.mul_comm _ _
      have : 2 ^ j * (b / 2 ^ j) = (b / 2 ^ j) * 2 ^ j := Nat.mul_comm _ _
      rw [Nat.add_mul]; omega
    rw [hsum, Nat.add_mul_div_right _ _ hpos]
    omega
  have hcdiv : (a % 2 ^ j + b % 2 ^ j) / 2 ^ j = if 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j then 1 else 0 := by
    have ha_lt : a % 2 ^ j < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos j)
    have hb_lt : b % 2 ^ j < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos j)
    by_cases hle : 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j
    · simp only [hle, ↓reduceIte]
      have hsub : a % 2 ^ j + b % 2 ^ j = (a % 2 ^ j + b % 2 ^ j - 2 ^ j) + 1 * 2 ^ j := by omega
      rw [hsub, Nat.add_mul_div_right _ _ (Nat.two_pow_pos j), Nat.div_eq_of_lt (by omega)]
    · simp only [hle, ↓reduceIte]
      exact Nat.div_eq_of_lt (by omega)
  rw [testBit_eq_decide_div_mod (a + b) j, testBit_eq_decide_div_mod a j,
    testBit_eq_decide_div_mod b j, hdiv, hcdiv]
  have ha2 : (a / 2 ^ j) % 2 = 0 ∨ (a / 2 ^ j) % 2 = 1 := by
    have := Nat.mod_lt (a / 2 ^ j) (by omega : 0 < 2); omega
  have hb2 : (b / 2 ^ j) % 2 = 0 ∨ (b / 2 ^ j) % 2 = 1 := by
    have := Nat.mod_lt (b / 2 ^ j) (by omega : 0 < 2); omega
  have hmod : (a / 2 ^ j + b / 2 ^ j + if 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j then 1 else 0) % 2 =
      ((a / 2 ^ j) % 2 + (b / 2 ^ j) % 2 + if 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j then 1 else 0) % 2 := by
    omega
  rw [hmod]
  by_cases hc : 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j <;>
  rcases ha2 with ha | ha <;>
  rcases hb2 with hb | hb <;>
  simp [faSum, hc, ha, hb]

private def bitsOf {N : ℕ} (L : ℕ) (F : (Fin N → Bool) → ℕ) : Fin L → Sig N :=
  fun j x => (F x).testBit j.val

private theorem rippleB {N : ℕ} {A : Set (Sig N)} (F G : (Fin N → Bool) → ℕ)
    (hfalse : (fun _ => false) ∈ A) :
    ∀ L : ℕ,
      (∀ j : Fin L, (fun x => (F x).testBit j.val) ∈ A) →
      (∀ j : Fin L, (fun x => (G x).testBit j.val) ∈ A) →
      Build A
        ((Set.range (bitsOf L (fun x => F x + G x))) ∪ {fun x => rippleCarry (F x) (G x) L})
        (9 * L) := by
  intro L
  induction L with
  | zero =>
    intro _ _
    simp only [Nat.mul_zero]
    apply idleB
    intro f hf
    rcases hf with ⟨j, _⟩ | rfl
    · exact Fin.elim0 j
    · exact hfalse
  | succ L ih =>
    intro hF hG
    have hprev := ih (fun j => hF j.castSucc) (fun j => hG j.castSucc)
    have hstep : Build
        (A ∪ (Set.range (bitsOf L (fun x => F x + G x)) ∪ {fun x => rippleCarry (F x) (G x) L}))
        ({fun x => faSum ((F x).testBit L) ((G x).testBit L) (rippleCarry (F x) (G x) L),
          fun x => faCarry ((F x).testBit L) ((G x).testBit L) (rippleCarry (F x) (G x) L)}) 9 :=
      fullAdderB (Or.inl (hF (Fin.last L))) (Or.inl (hG (Fin.last L))) (Or.inr (Or.inr rfl))
    have hseq := seqB hprev hstep
    refine relaxB hseq le_rfl ?_ (by omega)
    intro f hf
    rcases hf with ⟨j, rfl⟩ | rfl
    · by_cases hj : j.val < L
      · have hjeq : bitsOf (L + 1) (fun x => F x + G x) j =
            bitsOf L (fun x => F x + G x) ⟨j.val, hj⟩ := rfl
        rw [hjeq]
        exact Or.inr (Or.inl (Or.inl ⟨⟨j.val, hj⟩, rfl⟩))
      · have hjeq : j.val = L := by omega
        have hfeq : bitsOf (L + 1) (fun x => F x + G x) j =
            fun x => faSum ((F x).testBit L) ((G x).testBit L) (rippleCarry (F x) (G x) L) := by
          funext x
          unfold bitsOf
          rw [hjeq]
          exact (rippleCarry_spec (F x) (G x) L).2
        rw [hfeq]
        exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

private theorem sumTwoB {N : ℕ} {A : Set (Sig N)} (L : ℕ) (F G : (Fin N → Bool) → ℕ)
    (hfalse : (fun _ => false) ∈ A)
    (hF : ∀ j : Fin L, bitsOf L F j ∈ A)
    (hG : ∀ j : Fin L, bitsOf L G j ∈ A) :
    Build A (Set.range (bitsOf L (fun x => F x + G x))) (9 * L) :=
  relaxB (rippleB F G hfalse L hF hG) le_rfl
    (fun _ hf => Or.inr (Or.inl hf)) le_rfl

private def sumListVal {N : ℕ} : List ((Fin N → Bool) → ℕ) → (Fin N → Bool) → ℕ
  | [] => fun _ => 0
  | f :: fs => fun x => f x + sumListVal fs x

private theorem sumListB {N : ℕ} {A : Set (Sig N)} (L : ℕ)
    (hfalse : (fun _ => false) ∈ A)
    (Fs : List ((Fin N → Bool) → ℕ))
    (hFs : ∀ F ∈ Fs, ∀ j : Fin L, bitsOf L F j ∈ A) :
    Build A (Set.range (bitsOf L (sumListVal Fs))) (Fs.length * (9 * L)) := by
  induction Fs with
  | nil =>
    simp only [List.length_nil, Nat.zero_mul]
    apply idleB
    rintro _ ⟨j, rfl⟩
    have : bitsOf L (sumListVal ([] : List ((Fin N → Bool) → ℕ))) j = fun _ => false := by
      funext x; simp [bitsOf, sumListVal]
    rw [this]; exact hfalse
  | cons F Fs ih =>
    have h1 := ih (fun G hG => hFs G (List.mem_cons_of_mem F hG))
    have h2 : Build (A ∪ Set.range (bitsOf L (sumListVal Fs)))
        (Set.range (bitsOf L (fun x => F x + sumListVal Fs x))) (9 * L) :=
      sumTwoB L F (sumListVal Fs) (Or.inl hfalse)
        (fun j => Or.inl (hFs F List.mem_cons_self j))
        (fun j => Or.inr ⟨j, rfl⟩)
    refine relaxB (seq2B h1 h2) le_rfl Set.subset_union_right ?_
    simp only [List.length_cons]
    ring_nf
    omega

open Finset

theorem tb_split (a c k j : ℕ) (ha : a < 2 ^ k) :
    (a + 2 ^ k * c).testBit j = if j < k then a.testBit j else c.testBit (j - k) := by
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add c ha]

def valB (b : ℕ) (f : Fin b → Bool) : ℕ := ∑ j : Fin b, if f j then 2 ^ j.val else 0

theorem valB_spec : ∀ (b : ℕ) (f : Fin b → Bool),
    valB b f < 2 ^ b ∧ ∀ r (hr : r < b), (valB b f).testBit r = f ⟨r, hr⟩
  | 0, f => by simp [valB]
  | b + 1, f => by
    obtain ⟨h1, h2⟩ := valB_spec b (fun j => f j.castSucc)
    have he : valB (b + 1) f =
        valB b (fun j => f j.castSucc) + 2 ^ b * (if f (Fin.last b) then 1 else 0) := by
      unfold valB
      rw [Fin.sum_univ_castSucc]
      cases f (Fin.last b) <;> simp [Fin.val_last]
    rw [he]
    refine ⟨?_, ?_⟩
    · have : 2 ^ (b + 1) = 2 ^ b + 2 ^ b := by rw [Nat.pow_succ]; omega
      split_ifs <;> omega
    · intro r hr
      rw [tb_split _ _ _ _ h1]
      by_cases hrb : r < b
      · rw [if_pos hrb, h2 r hrb]
        rfl
      · have hr' : r = b := by omega
        subst hr'
        rw [if_neg (lt_irrefl _), Nat.sub_self]
        have : (⟨r, hr⟩ : Fin (r + 1)) = Fin.last r := rfl
        rw [this]
        cases f (Fin.last r) <;> simp

theorem valB_hi (b : ℕ) (f : Fin b → Bool) (r : ℕ) (hr : b ≤ r) : (valB b f).testBit r = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (valB_spec b f).1 (Nat.pow_le_pow_right (by omega) hr))

theorem blk_lt (B : ℕ) (E : ℕ → ℕ) : ∀ k, (∀ i, i < k → E i < B) →
    ∑ i ∈ range k, E i * B ^ i < B ^ k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hE
    rw [sum_range_succ, pow_succ]
    have h1 := ih (fun i hi => hE i (by omega))
    have h2 := hE k (by omega)
    have h3 : (E k + 1) * B ^ k ≤ B * B ^ k := Nat.mul_le_mul_right _ h2
    nlinarith

theorem dm (a a' c c' K : ℕ) (ha : a < K) (ha' : a' < K) (h : a + K * c = a' + K * c') :
    a = a' ∧ c = c' := by
  have hK : 0 < K := by omega
  have e1 : (a + K * c) % K = a := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  have e2 : (a' + K * c') % K = a' := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha']
  have haa : a = a' := by rw [← e1, ← e2, h]
  subst haa
  refine ⟨rfl, ?_⟩
  have : K * c = K * c' := by omega
  exact Nat.eq_of_mul_eq_mul_left hK this

theorem blk_inj (B : ℕ) (E F : ℕ → ℕ) : ∀ k, (∀ i, i < k → E i < B) → (∀ i, i < k → F i < B) →
    ∑ i ∈ range k, E i * B ^ i = ∑ i ∈ range k, F i * B ^ i → ∀ i, i < k → E i = F i := by
  intro k
  induction k with
  | zero => intro _ _ _ i hi; omega
  | succ k ih =>
    intro hE hF h i hi
    rw [sum_range_succ, sum_range_succ, mul_comm (E k), mul_comm (F k)] at h
    have l1 := blk_lt B E k (fun i hi => hE i (by omega))
    have l2 := blk_lt B F k (fun i hi => hF i (by omega))
    obtain ⟨d1, d2⟩ := dm _ _ _ _ _ l1 l2 h
    by_cases hik : i < k
    · exact ih (fun i hi => hE i (by omega)) (fun i hi => hF i (by omega)) d1 i hik
    · have : i = k := by omega
      subst this
      exact d2

theorem blk_tb (b : ℕ) (E : ℕ → ℕ) (q r : ℕ) (hr : r < b + 1) : ∀ k, (∀ i, i < k → E i < 2 ^ (b + 1)) →
    (∑ i ∈ range k, E i * (2 ^ (b + 1)) ^ i).testBit ((b + 1) * q + r) =
      if q < k then (E q).testBit r else false := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hE
    have hl := blk_lt (2 ^ (b + 1)) E k (fun i hi => hE i (by omega))
    rw [← pow_mul] at hl
    rw [sum_range_succ, mul_comm (E k), ← pow_mul, tb_split _ _ _ _ hl]
    by_cases hq : q < k
    · have hm := Nat.mul_le_mul_left (b + 1) (show q + 1 ≤ k by omega)
      rw [Nat.mul_succ] at hm
      rw [if_pos (by omega), ih (fun i hi => hE i (by omega)), if_pos hq, if_pos (by omega)]
    · have hm := Nat.mul_le_mul_left (b + 1) (show k ≤ q by omega)
      rw [if_neg (by omega)]
      by_cases hqk : q = k
      · subst hqk
        rw [if_pos (by omega)]
        congr 1
        omega
      · have hm2 := Nat.mul_le_mul_left (b + 1) (show k + 1 ≤ q by omega)
        rw [Nat.mul_succ] at hm2
        rw [if_neg (by omega)]
        apply Nat.testBit_eq_false_of_lt
        exact lt_of_lt_of_le (hE k (by omega)) (Nat.pow_le_pow_right (by omega) (by omega))

theorem sumListVal_ofFn {N : ℕ} : ∀ (n : ℕ) (f : Fin n → (Fin N → Bool) → ℕ) (x : Fin N → Bool),
    sumListVal (List.ofFn f) x = ∑ j, f j x
  | 0, f, x => by simp [sumListVal]
  | n + 1, f, x => by
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    show f 0 x + sumListVal (List.ofFn fun i => f i.succ) x = _
    rw [sumListVal_ofFn n]

-- the tree of sums

def TT {N : ℕ} (sq : ℕ → (Fin N → Bool) → ℕ) : ℕ → ℕ → (Fin N → Bool) → ℕ
  | 0, i => sq i
  | d + 1, i => fun x => TT sq d (2 * i) x + TT sq d (2 * i + 1) x

theorem TT_sum {N : ℕ} (sq : ℕ → (Fin N → Bool) → ℕ) (x : Fin N → Bool) :
    ∀ d i, TT sq d i x = ∑ k ∈ range (2 ^ d), sq (2 ^ d * i + k) x := by
  intro d
  induction d with
  | zero => intro i; simp [TT]
  | succ d ih =>
    intro i
    show TT sq d (2 * i) x + TT sq d (2 * i + 1) x = _
    rw [ih, ih, show 2 ^ (d + 1) = 2 ^ d + 2 ^ d by rw [pow_succ]; ring, sum_range_add]
    congr 1
    · exact sum_congr rfl (fun k _ => by congr 1; ring)
    · exact sum_congr rfl (fun k _ => by congr 1; ring)

theorem TT_lt {N : ℕ} (sq : ℕ → (Fin N → Bool) → ℕ) (w : ℕ) (hlt : ∀ i x, sq i x < 2 ^ w)
    (x : Fin N → Bool) (d i : ℕ) : TT sq d i x < 2 ^ (w + d) := by
  rw [TT_sum]
  calc ∑ k ∈ range (2 ^ d), sq (2 ^ d * i + k) x < ∑ _k ∈ range (2 ^ d), 2 ^ w :=
        sum_lt_sum_of_nonempty ⟨0, by simp⟩ (fun k _ => hlt _ x)
    _ = 2 ^ (w + d) := by rw [sum_const, card_range, smul_eq_mul, pow_add, mul_comm]

def cT (w : ℕ) : ℕ → ℕ
  | 0 => 0
  | d + 1 => 2 * cT w d + 9 * (w + d + 1)

theorem cT_le (w : ℕ) : ∀ d, cT w d + 9 * (w + d + 3) ≤ 9 * 2 ^ d * (w + 3) := by
  intro d
  induction d with
  | zero => simp [cT]
  | succ d ih =>
    simp only [cT]
    rw [pow_succ]
    nlinarith

theorem treeB {N : ℕ} (A : Set (Sig N)) (w : ℕ) (sq : ℕ → (Fin N → Bool) → ℕ)
    (hlt : ∀ i x, sq i x < 2 ^ w) (hfalse : (fun _ => false) ∈ A)
    (hA : ∀ i (j : Fin w), bitsOf w (sq i) j ∈ A) :
    ∀ d i, Build A (Set.range (bitsOf (w + d) (TT sq d i))) (cT w d) := by
  intro d
  induction d with
  | zero =>
    intro i
    apply idleB
    rintro _ ⟨j, rfl⟩
    exact hA i j
  | succ d ih =>
    intro i
    have H1 := ih (2 * i)
    have H2 : Build (A ∪ Set.range (bitsOf (w + d) (TT sq d (2 * i))))
        (Set.range (bitsOf (w + d) (TT sq d (2 * i + 1)))) (cT w d) :=
      relaxB (ih (2 * i + 1)) Set.subset_union_left Set.subset_union_right le_rfl
    have H12 := seqB H1 H2
    have hbit : ∀ i' : ℕ, ∀ j : Fin (w + d + 1),
        bitsOf (w + d + 1) (TT sq d i') j ∈ A ∪ Set.range (bitsOf (w + d) (TT sq d i')) := by
      intro i' j
      by_cases hj : j.val < w + d
      · exact Or.inr ⟨⟨j.val, hj⟩, rfl⟩
      · left
        have : bitsOf (w + d + 1) (TT sq d i') j = fun _ => false := by
          funext x
          apply Nat.testBit_eq_false_of_lt
          exact lt_of_lt_of_le (TT_lt sq w hlt x d i') (Nat.pow_le_pow_right (by omega) (by omega))
        rw [this]
        exact hfalse
    have H3 : Build (A ∪ (Set.range (bitsOf (w + d) (TT sq d (2 * i))) ∪
        Set.range (bitsOf (w + d) (TT sq d (2 * i + 1)))))
        (Set.range (bitsOf (w + d + 1) (fun x => TT sq d (2 * i) x + TT sq d (2 * i + 1) x)))
        (9 * (w + d + 1)) := by
      apply sumTwoB (w + d + 1) _ _ (Or.inl hfalse)
      · intro j
        rcases hbit (2 * i) j with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · intro j
        rcases hbit (2 * i + 1) j with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
    exact relaxB (seq2B H12 H3) le_rfl Set.subset_union_right (by simp only [cT]; omega)

-- digits

def dd (t b : ℕ) (i j : ℕ) : Sig (t * b) := fun x => (List.ofFn x).getD (i * b + j) false

def dig (t b : ℕ) (x : Fin (t * b) → Bool) (i : ℕ) : ℕ :=
  ∑ j : Fin b, if (List.ofFn x).getD (i * b + j.val) false then 2 ^ j.val else 0

theorem dig_eq (t b : ℕ) (x : Fin (t * b) → Bool) (i : ℕ) :
    dig t b x i = valB b (fun j => dd t b i j.val x) := rfl

theorem dig_lt (t b : ℕ) (x : Fin (t * b) → Bool) (i : ℕ) : dig t b x i < 2 ^ b := by
  rw [dig_eq]; exact (valB_spec _ _).1

theorem dig_tb (t b : ℕ) (x : Fin (t * b) → Bool) (i r : ℕ) (hr : r < b) :
    (dig t b x i).testBit r = dd t b i r x := by
  rw [dig_eq, (valB_spec _ _).2 r hr]

theorem dig_hi (t b : ℕ) (x : Fin (t * b) → Bool) (i r : ℕ) (hr : b ≤ r) :
    (dig t b x i).testBit r = false := by
  rw [dig_eq]; exact valB_hi _ _ r hr

theorem idx_lt (t b i j : ℕ) (hi : i < t) (hj : j < b) : i * b + j < t * b := by
  have := Nat.mul_le_mul_right b (show i + 1 ≤ t by omega)
  rw [Nat.succ_mul] at this
  omega

theorem dd_eq (t b i j : ℕ) (hi : i < t) (hj : j < b) :
    dd t b i j = fun x => x ⟨i * b + j, idx_lt t b i j hi hj⟩ := by
  funext x
  unfold dd
  rw [List.getD_eq_getElem _ _ (by simpa using idx_lt t b i j hi hj), List.getElem_ofFn]

theorem raw_rec (t b : ℕ) (hb : 0 < b) (x : Fin (t * b) → Bool) (k : Fin (t * b)) :
    x k = (dig t b x (k.val / b)).testBit (k.val % b) := by
  rw [dig_tb _ _ _ _ _ (Nat.mod_lt _ hb)]
  unfold dd
  rw [Nat.div_add_mod' k.val b, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

def lowS (t b : ℕ) (x : Fin (t * b) → Bool) : ℕ := ∑ i ∈ range t, dig t b x i * (2 ^ (b + 1)) ^ i
def sqS (t b : ℕ) (x : Fin (t * b) → Bool) : ℕ := ∑ i ∈ range t, dig t b x i ^ 2

def liftF (t b : ℕ) (x : Fin (t * b) → Bool) : ℕ :=
  (∑ i : Fin t, dig t b x i.val * 2 ^ ((b + 1) * i.val)) +
    2 ^ (t * (b + 1)) * ∑ i : Fin t, (dig t b x i.val) ^ 2

theorem liftF_eq (t b : ℕ) (x : Fin (t * b) → Bool) :
    liftF t b x = lowS t b x + 2 ^ (t * (b + 1)) * sqS t b x := by
  unfold liftF lowS sqS
  rw [Fin.sum_univ_eq_sum_range (fun i => dig t b x i * 2 ^ ((b + 1) * i)) t,
    Fin.sum_univ_eq_sum_range (fun i => dig t b x i ^ 2) t]
  congr 1
  exact sum_congr rfl (fun i _ => by rw [pow_mul])

theorem lowS_lt2 (t b : ℕ) (x : Fin (t * b) → Bool) : 2 * lowS t b x < 2 ^ (t * (b + 1)) := by
  have h := blk_lt (2 ^ (b + 1)) (fun i => 2 * dig t b x i) t (fun i _ => by
    have := dig_lt t b x i; rw [pow_succ]; omega)
  rw [← pow_mul, mul_comm (b + 1)] at h
  unfold lowS
  rw [mul_sum]
  simpa [mul_assoc] using h

theorem lowS_lt (t b : ℕ) (x : Fin (t * b) → Bool) : lowS t b x < 2 ^ (t * (b + 1)) := by
  have := lowS_lt2 t b x; omega

theorem sqS_lt (t b : ℕ) (ht : 0 < t) (x : Fin (t * b) → Bool) :
    sqS t b x < 2 ^ (2 * b + Nat.clog 2 t) := by
  unfold sqS
  calc ∑ i ∈ range t, dig t b x i ^ 2 < ∑ _i ∈ range t, 2 ^ (2 * b) :=
        sum_lt_sum_of_nonempty ⟨0, by simpa using ht⟩ (fun i _ => by
          rw [mul_comm, pow_mul]
          exact Nat.pow_lt_pow_left (dig_lt t b x i) (by omega))
    _ = t * 2 ^ (2 * b) := by rw [sum_const, card_range, smul_eq_mul]
    _ ≤ 2 ^ Nat.clog 2 t * 2 ^ (2 * b) := Nat.mul_le_mul_right _ (Nat.le_pow_clog (by omega) t)
    _ = 2 ^ (2 * b + Nat.clog 2 t) := by rw [← pow_add, add_comm]

theorem prog (t b : ℕ) (hb : 0 < b) (x y z : Fin (t * b) → Bool)
    (h : liftF t b x + liftF t b z = 2 * liftF t b y) : x = y ∧ y = z := by
  rw [liftF_eq, liftF_eq, liftF_eq] at h
  set K := 2 ^ (t * (b + 1)) with hK
  have e1 : lowS t b x + K * sqS t b x + (lowS t b z + K * sqS t b z) =
      (lowS t b x + lowS t b z) + K * (sqS t b x + sqS t b z) := by ring
  have e2 : 2 * (lowS t b y + K * sqS t b y) = 2 * lowS t b y + K * (2 * sqS t b y) := by ring
  rw [e1, e2] at h
  have hl1 : lowS t b x + lowS t b z < K := by
    have := lowS_lt2 t b x; have := lowS_lt2 t b z; omega
  obtain ⟨hL, hQ⟩ := dm _ _ _ _ _ hl1 (lowS_lt2 t b y) h
  -- digits
  have hd : ∀ i, i < t → dig t b x i + dig t b z i = 2 * dig t b y i := by
    apply blk_inj (2 ^ (b + 1)) _ _ t
    · intro i _
      have := dig_lt t b x i; have := dig_lt t b z i; rw [pow_succ]; omega
    · intro i _
      have := dig_lt t b y i; rw [pow_succ]; omega
    · unfold lowS at hL
      rw [← sum_add_distrib, mul_sum] at hL
      exact Eq.trans (sum_congr rfl (fun i _ => by ring)) (hL.trans (sum_congr rfl (fun i _ => by ring)))
  have hsq : ∀ i ∈ range t, (dig t b x i + dig t b z i) ^ 2 ≤
      2 * (dig t b x i ^ 2 + dig t b z i ^ 2) := by
    intro i _
    nlinarith [sq_nonneg ((dig t b x i : ℤ) - dig t b z i)]
  have hsum : ∑ i ∈ range t, (dig t b x i + dig t b z i) ^ 2 =
      ∑ i ∈ range t, 2 * (dig t b x i ^ 2 + dig t b z i ^ 2) := by
    rw [← mul_sum, sum_add_distrib]
    unfold sqS at hQ
    rw [hQ]
    rw [mul_sum, mul_sum]
    apply sum_congr rfl
    intro i hi
    rw [hd i (mem_range.mp hi)]
    ring
  have heq := (sum_eq_sum_iff_of_le hsq).mp hsum
  have hxz : ∀ i, i < t → dig t b x i = dig t b z i ∧ dig t b y i = dig t b x i := by
    intro i hi
    have h1 := heq i (mem_range.mpr hi)
    have h2 := hd i hi
    have h3 : ((dig t b x i : ℤ) - dig t b z i) ^ 2 = 0 := by
      have : ((dig t b x i + dig t b z i) ^ 2 : ℤ) = 2 * ((dig t b x i : ℤ) ^ 2 + (dig t b z i) ^ 2) := by
        exact_mod_cast h1
      nlinarith
    have h4 : (dig t b x i : ℤ) = dig t b z i := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3
      linarith
    have h5 : dig t b x i = dig t b z i := by exact_mod_cast h4
    refine ⟨h5, ?_⟩
    omega
  have hkt : ∀ k : Fin (t * b), k.val / b < t := by
    intro k
    rw [Nat.div_lt_iff_lt_mul hb]
    exact k.2
  constructor
  · funext k
    rw [raw_rec t b hb x k, raw_rec t b hb y k, (hxz _ (hkt k)).2]
  · funext k
    rw [raw_rec t b hb y k, raw_rec t b hb z k, (hxz _ (hkt k)).2, (hxz _ (hkt k)).1]

theorem bound (t b : ℕ) (ht : 0 < t) (x : Fin (t * b) → Bool) :
    2 * liftF t b x < 2 ^ (t * (b + 1) + 2 * b + Nat.clog 2 t + 1) := by
  rw [liftF_eq]
  have h1 := lowS_lt2 t b x
  have h2 := sqS_lt t b ht x
  have e : 2 ^ (t * (b + 1) + 2 * b + Nat.clog 2 t + 1) =
      2 ^ (t * (b + 1)) * 2 ^ (2 * b + Nat.clog 2 t) * 2 := by
    rw [← pow_add, ← pow_succ]; ring_nf
  rw [e]
  set K := 2 ^ (t * (b + 1))
  set Q := 2 ^ (2 * b + Nat.clog 2 t)
  have h3 : K * (sqS t b x + 1) ≤ K * Q := Nat.mul_le_mul_left _ h2
  nlinarith

-- rows of a square

def RR (t b : ℕ) (i j : ℕ) : (Fin (t * b) → Bool) → ℕ :=
  fun x => dig t b x i * (if dd t b i j x then 2 ^ j else 0)

theorem rows_sum (t b : ℕ) (i : ℕ) (x : Fin (t * b) → Bool) :
    sumListVal (List.ofFn (fun j : Fin b => RR t b i j.val)) x = dig t b x i ^ 2 := by
  rw [sumListVal_ofFn]
  unfold RR
  rw [← mul_sum, sq]
  rfl

theorem row_bits (t b i j k : ℕ) :
    (fun x => (RR t b i j x).testBit k) =
      if j ≤ k ∧ k - j < b then (fun x => dd t b i j x && dd t b i (k - j) x) else (fun _ => false) := by
  by_cases hc : j ≤ k ∧ k - j < b
  · rw [if_pos hc]
    funext x
    unfold RR
    cases hdx : dd t b i j x
    · simp
    · rw [if_pos rfl, Nat.testBit_mul_two_pow, decide_eq_true hc.1]
      simp only [Bool.true_and]
      exact dig_tb _ _ _ _ _ hc.2
  · rw [if_neg hc]
    funext x
    unfold RR
    cases hdx : dd t b i j x
    · simp
    · rw [if_pos rfl, Nat.testBit_mul_two_pow]
      by_cases hjk : j ≤ k
      · rw [dig_hi _ _ _ _ _ (by omega)]; simp
      · simp [hjk]

theorem rowsB (t b : ℕ) (A : Set (Sig (t * b))) (hfalse : (fun _ => false) ∈ A) (i : ℕ)
    (hpp : ∀ j k, j < b → k < b → (fun x => dd t b i j x && dd t b i k x) ∈ A) :
    Build A (Set.range (bitsOf (2 * b) (fun x => dig t b x i ^ 2))) (b * (9 * (2 * b))) := by
  have H := sumListB (2 * b) hfalse (List.ofFn (fun j : Fin b => RR t b i j.val)) ?_
  · have he : sumListVal (List.ofFn (fun j : Fin b => RR t b i j.val)) = fun x => dig t b x i ^ 2 :=
      funext (rows_sum t b i)
    rw [he, List.length_ofFn] at H
    exact H
  · intro F hF k
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hF
    show (fun x => (RR t b i j.val x).testBit k.val) ∈ A
    rw [row_bits]
    split_ifs with hc
    · exact hpp _ _ j.2 hc.2
    · exact hfalse

theorem root_eq (t b : ℕ) (x : Fin (t * b) → Bool) :
    TT (fun i x => if i < t then dig t b x i ^ 2 else 0) (Nat.clog 2 t) 0 x = sqS t b x := by
  rw [TT_sum]
  simp only [mul_zero, zero_add]
  have hle := Nat.le_pow_clog (by norm_num : 1 < 2) t
  rw [show 2 ^ Nat.clog 2 t = t + (2 ^ Nat.clog 2 t - t) by omega, sum_range_add]
  have h0 : ∑ k ∈ range (2 ^ Nat.clog 2 t - t),
      (if t + k < t then dig t b x (t + k) ^ 2 else 0) = 0 :=
    sum_eq_zero (fun k _ => if_neg (by omega))
  rw [h0, add_zero]
  unfold sqS
  exact sum_congr rfl (fun k hk => if_pos (mem_range.mp hk))

theorem pow_clog_lt (t : ℕ) (ht : 0 < t) : 2 ^ Nat.clog 2 t < 2 * t := by
  rcases Nat.lt_or_ge 1 t with h1 | h1
  · have hpos := Nat.clog_pos (by norm_num : 1 < 2) h1
    have hp := Nat.pow_pred_clog_lt_self 2 h1
    obtain ⟨e, he⟩ : ∃ e, Nat.clog 2 t = e + 1 := ⟨Nat.clog 2 t - 1, by omega⟩
    rw [he] at hp ⊢
    simp only [Nat.pred_succ] at hp
    rw [pow_succ]
    omega
  · have : t = 1 := by omega
    subst this
    simp

theorem circ (t b : ℕ) (ht : 0 < t) (hb : 0 < b) :
    ∃ (C : Circuit) (out : Fin (t * (b + 1) + 2 * b + Nat.clog 2 t + 1) → Fin (t * b + C.size)),
      ReadsBack (t * b) C ∧ Strict C.gates ∧
      C.size ≤ 256 * (t * b * b + (t * (b + 1) + 2 * b + Nat.clog 2 t + 1) + 1) ∧
      ∀ (word : Fin (t * b) → Bool) (j : Fin (t * (b + 1) + 2 * b + Nat.clog 2 t + 1)),
        (C.wires (List.ofFn word)).getD (out j).val false = (liftF t b word).testBit j.val := by
  classical
  have hN0 : 0 < t * b := Nat.mul_pos ht hb
  let A0 : Set (Sig (t * b)) := Set.range (fun k : Fin (t * b) => fun x : Fin (t * b) → Bool => x k)
  have S0 : Scheduled (t * b) 0 A0 := startSched (t * b)
  let k0 : Fin (t * b) := ⟨0, hN0⟩
  have hk0 : (fun x : Fin (t * b) → Bool => x k0) ∈ A0 := ⟨k0, rfl⟩
  have B1 : Build A0 {fun _ => false} 2 := by
    have h1 : Build A0 {fun x => !(x k0)} 1 := notB hk0
    have h2 : Build (A0 ∪ {fun x => !(x k0)}) {fun x => x k0 && !(x k0)} 1 :=
      andB (Or.inl hk0) (Or.inr rfl)
    refine relaxB (seq2B h1 h2) le_rfl ?_ le_rfl
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    subst hf
    right
    show (fun _ => false) = fun x : Fin (t * b) → Bool => x k0 && !(x k0)
    funext x
    simp
  obtain ⟨c1, hc1, S1⟩ := B1.run S0 (fun _ h => h)
  let S1set : Set (Sig (t * b)) := A0 ∪ {fun _ => false}
  let F : Fin t → Fin b → Fin b → Sig (t * b) := fun i j k => fun x => dd t b i j x && dd t b i k x
  have hdd : ∀ (i : Fin t) (j : Fin b), dd t b i j ∈ S1set := fun i j =>
    Or.inl ⟨⟨i * b + j, idx_lt _ _ _ _ i.2 j.2⟩, (dd_eq t b i j i.2 j.2).symm⟩
  have B2 : Build S1set (⋃ i : Fin t, {f | ∃ j k, F i j k = f}) (t * (b * (b * 1))) :=
    finB _ _ (fun i => fin2SigB (F i) 1 (fun j k => andB (hdd i j) (hdd i k)))
  obtain ⟨c2, hc2, S2⟩ := B2.run S1 (fun _ h => h)
  let S2set : Set (Sig (t * b)) := S1set ∪ ⋃ i : Fin t, {f | ∃ j k, F i j k = f}
  have hf2 : (fun _ => false) ∈ S2set := Or.inl (Or.inr rfl)
  have B3 : Build S2set (⋃ i : Fin t, Set.range (bitsOf (2 * b) (fun x => dig t b x i ^ 2)))
      (t * (b * (9 * (2 * b)))) :=
    finB _ _ (fun i => rowsB t b S2set hf2 i (fun j k hj hk =>
      Or.inr (Set.mem_iUnion.mpr ⟨i, ⟨⟨j, hj⟩, ⟨k, hk⟩, rfl⟩⟩)))
  obtain ⟨c3, hc3, S3⟩ := B3.run S2 (fun _ h => h)
  let S3set : Set (Sig (t * b)) :=
    S2set ∪ ⋃ i : Fin t, Set.range (bitsOf (2 * b) (fun x => dig t b x i ^ 2))
  let sq' : ℕ → (Fin (t * b) → Bool) → ℕ := fun i x => if i < t then dig t b x i ^ 2 else 0
  have hsqlt : ∀ i x, sq' i x < 2 ^ (2 * b) := by
    intro i x
    simp only [sq']
    split_ifs
    · rw [mul_comm, pow_mul]
      exact Nat.pow_lt_pow_left (dig_lt t b x i) (by omega)
    · positivity
  have hA4 : ∀ i (j : Fin (2 * b)), bitsOf (2 * b) (sq' i) j ∈ S3set := by
    intro i j
    by_cases hi : i < t
    · right
      refine Set.mem_iUnion.mpr ⟨⟨i, hi⟩, ⟨j, ?_⟩⟩
      funext x
      simp [bitsOf, sq', hi]
    · left; left; right
      show bitsOf (2 * b) (sq' i) j = fun _ => false
      funext x
      simp [bitsOf, sq', hi]
  have B4 := treeB S3set (2 * b) sq' hsqlt (Or.inl (Or.inl (Or.inr rfl))) hA4 (Nat.clog 2 t) 0
  obtain ⟨c4, hc4, S4⟩ := B4.run S3 (fun _ h => h)
  let S4set : Set (Sig (t * b)) :=
    S3set ∪ Set.range (bitsOf (2 * b + Nat.clog 2 t) (TT sq' (Nat.clog 2 t) 0))
  have hfalse4 : (fun _ => false) ∈ S4set := Or.inl (Or.inl (Or.inl (Or.inr rfl)))
  have hin4 : ∀ k : Fin (t * b), (fun x => x k) ∈ S4set :=
    fun k => Or.inl (Or.inl (Or.inl (Or.inl ⟨k, rfl⟩)))
  have hmem : ∀ p : Fin (t * (b + 1) + 2 * b + Nat.clog 2 t + 1),
      (fun x => (liftF t b x).testBit p.val) ∈ S4set := by
    intro p
    have hl : ∀ x, (liftF t b x).testBit p.val = if p.val < t * (b + 1) then (lowS t b x).testBit p.val
        else (sqS t b x).testBit (p.val - t * (b + 1)) := by
      intro x
      rw [liftF_eq, tb_split _ _ _ _ (lowS_lt t b x)]
    by_cases hp : p.val < t * (b + 1)
    · have hq : p.val / (b + 1) < t := by rw [Nat.div_lt_iff_lt_mul (by omega)]; exact hp
      have hpr := Nat.div_add_mod p.val (b + 1)
      have hbt : ∀ x, (liftF t b x).testBit p.val = (dig t b x (p.val / (b + 1))).testBit (p.val % (b + 1)) := by
        intro x
        rw [hl x, if_pos hp]
        unfold lowS
        conv_lhs => rw [← hpr]
        rw [blk_tb b (dig t b x) _ _ (Nat.mod_lt _ (by omega)) t (fun i _ => by
          have := dig_lt t b x i; rw [pow_succ]; omega), if_pos hq]
      by_cases hr : p.val % (b + 1) < b
      · have : (fun x => (liftF t b x).testBit p.val) =
            fun x => x ⟨p.val / (b + 1) * b + p.val % (b + 1), idx_lt _ _ _ _ hq hr⟩ := by
          funext x
          rw [hbt x, dig_tb _ _ _ _ _ hr, dd_eq t b _ _ hq hr]
        rw [this]
        exact hin4 _
      · have : (fun x => (liftF t b x).testBit p.val) = fun _ => false := by
          funext x
          rw [hbt x, dig_hi _ _ _ _ _ (by omega)]
        rw [this]
        exact hfalse4
    · by_cases hp2 : p.val - t * (b + 1) < 2 * b + Nat.clog 2 t
      · right
        refine ⟨⟨p.val - t * (b + 1), hp2⟩, ?_⟩
        funext x
        show (TT sq' (Nat.clog 2 t) 0 x).testBit (p.val - t * (b + 1)) = _
        rw [hl x, if_neg hp]
        exact congrArg (fun v => v.testBit (p.val - t * (b + 1))) (root_eq t b x)
      · have : (fun x => (liftF t b x).testBit p.val) = fun _ => false := by
          funext x
          rw [hl x, if_neg hp]
          apply Nat.testBit_eq_false_of_lt
          exact lt_of_lt_of_le (sqS_lt t b ht x) (Nat.pow_le_pow_right (by omega) (by omega))
        rw [this]
        exact hfalse4
  obtain ⟨C, out, hS, hR, hsz, hval⟩ :=
    finishFinBits S4 (fun p : Fin (t * (b + 1) + 2 * b + Nat.clog 2 t + 1) =>
      fun x => (liftF t b x).testBit p.val) hmem
  refine ⟨C, out, hR, hS, ?_, fun word j => hval j word⟩
  rw [hsz]
  have hP := pow_clog_lt t ht
  have hcT := cT_le (2 * b) (Nat.clog 2 t)
  have h9 : 9 * 2 ^ Nat.clog 2 t * (2 * b + 3) ≤ 9 * (2 * t) * (2 * b + 3) := by
    apply Nat.mul_le_mul_right; omega
  have hb1 : 1 ≤ b := hb
  nlinarith [Nat.zero_le (t * b), Nat.zero_le (t * b * b)]

end PEqualNP.Outside.L_lib_580

open PEqualNP.Outside.L_lib_580 in
theorem PEqualNP.Outside.L_lib_580 : ∀ (t b : ℕ), 0 < t → 0 < b →
  let m := t*b
  let X := Fin m → Bool
  let low := t*(b+1)
  let h := low + 2*b + Nat.clog 2 t + 1
  let digit := fun (raw : X) (i : Fin t) => ∑ j : Fin b,
    if (List.ofFn raw).getD (i.val*b+j.val) false then 2^j.val else 0
  let lift := fun payload : X =>
    (∑ i : Fin t, digit payload i * 2^((b+1)*i.val)) + 2^low * ∑ i : Fin t, (digit payload i)^2
  (∀ x : X, 2 * lift x < 2^h) ∧ Function.Injective lift ∧
  (∀ x y z : X, lift x + lift z = 2 * lift y → x = y ∧ y = z) ∧
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin h → Fin (m+C.size)),
    PEqualNP.MetaComplexity.NestedCover.ReadsBack m C ∧
    (∀ g ∈ C.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
      (g.op = .not ∧ g.inputs.length = 1)) ∧
    C.size ≤ 256*(t*b*b+h+1) ∧ ∀ (word : X) (j : Fin h),
      (C.wires (List.ofFn word)).getD (out j).val false = (lift word).testBit j.val := by
  intro t b ht hb m X low h digit lift
  refine ⟨fun x => bound t b ht x, fun x y hxy => (prog t b hb x y y (by
    have e : liftF t b x = liftF t b y := hxy
    rw [e]; ring)).1, fun x y z hxyz => prog t b hb x y z hxyz, ?_⟩
  obtain ⟨C, out, h1, h2, h3, h4⟩ := circ t b ht hb
  exact ⟨C, out, h1, h2, h3, h4⟩
