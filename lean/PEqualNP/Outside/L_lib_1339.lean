import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1339

section WireAndSynthesis
open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private abbrev Col (m : ℕ) := Fin m → Bool

private noncomputable def bitsDef (d : ℕ) (x : Finset (Fin d)) : List Bool :=
  List.ofFn (fun a : Fin d => decide (a ∈ x)) ++ [false, true]

private noncomputable def raw (x : Fin m → Finset (Fin n)) (i : Fin m) : List Bool :=
  bitsDef n (x i)

private noncomputable def val (x : Fin m → Finset (Fin n)) (gs : List Gate) (p : ℕ) : Col m :=
  fun i => ((Circuit.mk gs 0).wires (raw x i)).getD p false

private noncomputable def ix (gs : List Gate) : List ℕ :=
  (List.range gs.length).filter fun j =>
    decide ((gs.getD j ⟨.or, []⟩).op = GateOp.not)

private noncomputable def trace (x : Fin m → Finset (Fin n)) (gs : List Gate) : List (Col m) :=
  (ix gs).map fun j => val x gs (n + 2 + j)

private noncomputable def sing (x : Fin m → Finset (Fin n)) (a : Fin n) : Col m :=
  fun i => decide (a ∈ x i)

private noncomputable def base (x : Fin m → Finset (Fin n)) : Set (Col m) :=
  {f | f = (fun _ => false) ∨ f = (fun _ => true) ∨ ∃ a, f = sing x a}

private noncomputable def inv (f : Col m) : Col m := fun i => !(f i)
private noncomputable def conj (f g : Col m) : Col m := fun i => f i && g i
private noncomputable def disj (f g : Col m) : Col m := fun i => f i || g i

private theorem bitsDef_length (d : ℕ) (x : Finset (Fin d)) : (bitsDef d x).length = d + 2 := by
  simp [bitsDef]

private theorem bitsDef_getD_d (d : ℕ) (x : Finset (Fin d)) :
    (bitsDef d x).getD d false = false := by
  simp [bitsDef]

private theorem bitsDef_getD_d1 (d : ℕ) (x : Finset (Fin d)) :
    (bitsDef d x).getD (d + 1) false = true := by
  simp [bitsDef]

private theorem wirelen (gs : List Gate) (u : List Bool) :
    ((Circuit.mk gs 0).wires u).length = u.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    simpa [Circuit.wires, List.foldl_append, Nat.add_assoc] using congrArg Nat.succ ih

private theorem wires_snoc (gs : List Gate) (g : Gate) (u : List Bool) :
    (Circuit.mk (gs ++ [g]) 0).wires u =
      (Circuit.mk gs 0).wires u ++
        [g.op.eval (g.inputs.map fun i => ((Circuit.mk gs 0).wires u).getD i false)] := by
  simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem wires_prefix (gs hs : List Gate) (u : List Bool) (p : ℕ)
    (hp : p < u.length + gs.length) :
    ((Circuit.mk (gs ++ hs) 0).wires u).getD p false =
      ((Circuit.mk gs 0).wires u).getD p false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, wires_snoc]
    have hlen : ((Circuit.mk (gs ++ hs) 0).wires u).length = u.length + (gs ++ hs).length :=
      wirelen (gs ++ hs) u
    rw [List.getD_append _ _ _ _ (by rw [hlen, List.length_append]; omega)]
    exact ih

private theorem wires_input (gs : List Gate) (u : List Bool) (p : ℕ) (hp : p < u.length) :
    ((Circuit.mk gs 0).wires u).getD p false = u.getD p false := by
  have h := wires_prefix [] gs u p (by simpa using hp)
  simpa [Circuit.wires] using h

private theorem wires_gate_eval (gs : List Gate) (u : List Bool) (j : ℕ) (hj : j < gs.length)
    (hRB : ∀ i ∈ (gs.getD j ⟨.or, []⟩).inputs, i < u.length + j) :
    ((Circuit.mk gs 0).wires u).getD (u.length + j) false =
      (gs.getD j ⟨.or, []⟩).op.eval
        ((gs.getD j ⟨.or, []⟩).inputs.map fun i => ((Circuit.mk gs 0).wires u).getD i false) := by
  have hget : gs.getD j ⟨.or, []⟩ = gs[j] := List.getD_eq_getElem gs _ hj
  have hsp : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    have h1 : gs.take (j + 1) = gs.take j ++ [gs[j]] := List.take_succ_eq_append_getElem hj
    rw [← h1, List.take_append_drop]
  have htl : (gs.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have h1 : ((Circuit.mk gs 0).wires u).getD (u.length + j) false =
      ((Circuit.mk (gs.take j ++ [gs[j]]) 0).wires u).getD (u.length + j) false := by
    conv_lhs => rw [hsp]
    exact wires_prefix _ _ _ _ (by rw [List.length_append, htl, List.length_singleton]; omega)
  rw [h1, wires_snoc]
  have hlen : ((Circuit.mk (gs.take j) 0).wires u).length = u.length + j := by
    rw [wirelen, htl]
  conv_lhs => rw [← hlen]
  rw [List.getD_append_right _ _ _ _ le_rfl]
  simp only [Nat.sub_self, List.getD_cons_zero, hget]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  have hilt : i < u.length + j := by rw [← hget] at hi; exact hRB i hi
  conv_rhs => rw [hsp, List.append_assoc]
  exact (wires_prefix (gs.take j) _ u i (by rw [htl]; exact hilt)).symm

private theorem old (x : Fin m → Finset (Fin n)) (gs : List Gate) (g : Gate) {p}
    (hp : p < n + 2 + gs.length) :
    val x (gs ++ [g]) p = val x gs p := by
  funext i
  exact wires_prefix gs [g] (raw x i) p (by rw [raw, bitsDef_length]; exact hp)

private theorem fresh (x : Fin m → Finset (Fin n)) (gs : List Gate) (g : Gate) (i : Fin m) :
    val x (gs ++ [g]) (n + 2 + gs.length) i =
      g.op.eval (g.inputs.map fun p => val x gs p i) := by
  have len := wirelen gs (raw x i)
  rw [show (raw x i).length = n + 2 by simp [raw, bitsDef]] at len
  simp only [val, wires_snoc]
  rw [← len, List.getD_append_right _ _ _ _ le_rfl]
  simp

private theorem ixAdd (gs : List Gate) (g : Gate) :
    ix (gs ++ [g]) = ix gs ++ (if g.op = .not then [gs.length] else []) := by
  unfold ix
  simp only [List.length_append, List.length_singleton, List.range_succ, List.filter_append]
  congr 1
  · apply List.filter_congr
    intro i hi
    rw [List.getD_append _ _ _ _ (List.mem_range.mp hi)]
  · by_cases h : g.op = .not <;> simp [h]

private theorem ixRange {gs : List Gate} {j} (h : j ∈ ix gs) : j < gs.length :=
  List.mem_range.mp (List.mem_filter.mp h).1

private theorem traceAdd (x : Fin m → Finset (Fin n)) (gs : List Gate) (g : Gate) :
    trace x (gs ++ [g]) =
      trace x gs ++ (if g.op = .not then [val x (gs ++ [g]) (n + 2 + gs.length)] else []) := by
  unfold trace
  rw [ixAdd, List.map_append]
  congr 1
  · apply List.map_congr_left
    intro j hj
    exact old _ _ _ (by have := ixRange hj; omega)
  · split <;> rfl

private theorem countIx (gs : List Gate) : PEqualNP.NotBracket.notCount ⟨gs, 0⟩ = (ix gs).length := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [ixAdd]
    unfold PEqualNP.NotBracket.notCount at *
    by_cases h : g.op = .not <;> simp [List.filter_append, h, ih]

private theorem notCount_eq_ix_length (C : Circuit) :
    PEqualNP.NotBracket.notCount C = (ix C.gates).length := by
  simpa [PEqualNP.NotBracket.notCount] using countIx C.gates

private theorem extendBack (n : ℕ) (gs : List Gate) (g : Gate) (h : ReadsBack (n + 2) ⟨gs, 0⟩)
    (ok : ∀ p ∈ g.inputs, p < n + 2 + gs.length) : ReadsBack (n + 2) ⟨gs ++ [g], 0⟩ := by
  intro j hj p hp
  simp only [List.length_append, List.length_singleton] at hj
  by_cases hj' : j < gs.length
  · apply h j hj' p
    simpa only [gateAt, List.getD_append _ _ _ _ hj'] using hp
  · obtain rfl : j = gs.length := by omega
    apply ok
    simpa [gateAt, List.getD_append_right _ _ _ _ le_rfl] using hp

private noncomputable def Built (x : Fin m → Finset (Fin n)) (tr : List (Col m)) (k : ℕ)
    (S : Set (Col m)) : Prop :=
  ∃ gs : List Gate, FanInTwo ⟨gs, 0⟩ ∧ ReadsBack (n + 2) ⟨gs, 0⟩ ∧ gs.length ≤ k ∧
    trace x gs = tr ∧ ∀ f ∈ S, ∃ p < n + 2 + gs.length, val x gs p = f

private theorem Built.start {n m : ℕ} {x : Fin m → Finset (Fin n)} : Built x [] 0 (base x) := by
  refine ⟨[], by simp [FanInTwo], by simp [ReadsBack], by simp, rfl, ?_⟩
  intro f hf
  rcases hf with rfl | rfl | ⟨a, rfl⟩
  · refine ⟨n, by simp, ?_⟩
    funext i
    simp [val, Circuit.wires, raw, bitsDef]
  · refine ⟨n + 1, by simp, ?_⟩
    funext i
    simp [val, Circuit.wires, raw, bitsDef]
  · refine ⟨a.val, by have := a.isLt; simp; omega, ?_⟩
    funext i
    change ((List.ofFn fun u : Fin n => decide (u ∈ x i)) ++ [false, true]).getD a.val false = _
    rw [List.getD_append _ _ _ _ (by simp)]
    simp [sing]

private theorem Built.relax {n m k K : ℕ} {x : Fin m → Finset (Fin n)} {tr : List (Col m)}
    {S T : Set (Col m)} (ih : Built x tr k S) (sz : k ≤ K) (sub : T ⊆ S) : Built x tr K T := by
  obtain ⟨gs, fan, back, le, trEq, signal⟩ := ih
  exact ⟨gs, fan, back, le.trans sz, trEq, fun f hf => signal f (sub hf)⟩

private theorem Built.andGate {n m k : ℕ} {x : Fin m → Finset (Fin n)} {tr : List (Col m)}
    {S : Set (Col m)} {f z : Col m} (ih : Built x tr k S) (hf : f ∈ S) (hg : z ∈ S) :
    Built x tr (k + 1) (insert (conj f z) S) := by
  obtain ⟨gs, fan, back, sz, ht, sig⟩ := ih
  obtain ⟨a, ha, ea⟩ := sig _ hf
  obtain ⟨b, hb, eb⟩ := sig _ hg
  let g : Gate := ⟨.and, [a, b]⟩
  refine ⟨gs ++ [g], ?_, ?_, by simpa using sz, ?_, ?_⟩
  · intro j hj
    rcases List.mem_append.mp hj with oj | nj
    · exact fan j oj
    · obtain rfl : j = g := List.mem_singleton.mp nj
      simp [g]
  · apply extendBack n _ _ back
    simp_all [g]
  · rw [traceAdd]; simpa [g] using ht
  · intro f mem
    rcases mem with rfl | mem
    · refine ⟨n + 2 + gs.length, by simp, ?_⟩
      funext i; rw [fresh]; simp [g, GateOp.eval, ea, eb, conj]
    · obtain ⟨p, hp, eq⟩ := sig _ mem
      exact ⟨p, by simp; omega, (old _ _ _ hp).trans eq⟩

private theorem Built.orGate {n m k : ℕ} {x : Fin m → Finset (Fin n)} {tr : List (Col m)}
    {S : Set (Col m)} {f z : Col m} (ih : Built x tr k S) (hf : f ∈ S) (hg : z ∈ S) :
    Built x tr (k + 1) (insert (disj f z) S) := by
  obtain ⟨gs, fan, back, sz, ht, sig⟩ := ih
  obtain ⟨a, ha, ea⟩ := sig _ hf
  obtain ⟨b, hb, eb⟩ := sig _ hg
  let g : Gate := ⟨.or, [a, b]⟩
  refine ⟨gs ++ [g], ?_, ?_, by simpa using sz, ?_, ?_⟩
  · intro j hj
    rcases List.mem_append.mp hj with oj | nj
    · exact fan j oj
    · obtain rfl : j = g := List.mem_singleton.mp nj
      simp [g]
  · apply extendBack n _ _ back
    simp_all [g]
  · rw [traceAdd]; simpa [g] using ht
  · intro f mem
    rcases mem with rfl | mem
    · refine ⟨n + 2 + gs.length, by simp, ?_⟩
      funext i; rw [fresh]; simp [g, GateOp.eval, ea, eb, disj]
    · obtain ⟨p, hp, eq⟩ := sig _ mem
      exact ⟨p, by simp; omega, (old _ _ _ hp).trans eq⟩

private theorem Built.notGate {n m k : ℕ} {x : Fin m → Finset (Fin n)} {tr : List (Col m)}
    {S : Set (Col m)} {f : Col m} (ih : Built x tr k S) (hf : f ∈ S) :
    Built x (tr ++ [inv f]) (k + 1) (insert (inv f) S) := by
  obtain ⟨gs, fan, back, sz, ht, sig⟩ := ih
  obtain ⟨a, ha, ea⟩ := sig _ hf
  let g : Gate := ⟨.not, [a]⟩
  have ev : val x (gs ++ [g]) (n + 2 + gs.length) = inv f := by
    funext i; rw [fresh]; simp [g, GateOp.eval, ea, inv]
  refine ⟨gs ++ [g], ?_, ?_, by simpa using sz, by simp [traceAdd, g, ht, ev], ?_⟩
  · intro j hj
    rcases List.mem_append.mp hj with oldG | newG
    · exact fan j oldG
    · obtain rfl : j = g := List.mem_singleton.mp newG
      simp [g]
  · apply extendBack n _ _ back; simpa [g] using ha
  · intro f mem
    rcases mem with rfl | mem
    · exact ⟨_, by simp, ev⟩
    · obtain ⟨p, hp, eq⟩ := sig _ mem
      exact ⟨p, by simp; omega, (old _ _ _ hp).trans eq⟩

private noncomputable def Grow (x : Fin m → Finset (Fin n)) (tr : List (Col m)) (k : ℕ)
    (S : Set (Col m)) (b : ℕ) (f : Col m) : Prop :=
  ∃ T, Built x tr (k + b) T ∧ S ⊆ T ∧ f ∈ T

private theorem batch {n m k : ℕ} {x : Fin m → Finset (Fin n)} {tr : List (Col m)}
    {S : Set (Col m)} {ι : Type} (s : Finset ι) (F : ι → Col m) (b : ℕ) (H : Built x tr k S)
    (make : ∀ {K T}, Built x tr K T → S ⊆ T → ∀ a ∈ s, Grow x tr K T b (F a)) :
    ∃ T, Built x tr (k + s.card * b) T ∧ S ⊆ T ∧ ∀ a ∈ s, F a ∈ T := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨S, by simpa using H, Set.Subset.rfl, by simp⟩
  | @insert a s freshA ih =>
    obtain ⟨U, hU, sub, allU⟩ := ih (fun h st i hi => make h st i (Finset.mem_insert_of_mem hi))
    obtain ⟨T, hT, ut, hit⟩ := make hU sub a (Finset.mem_insert_self _ _)
    refine ⟨T, by simpa [Finset.card_insert_of_notMem freshA, Nat.add_mul, Nat.add_assoc] using hT,
      sub.trans ut, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hh
    · exact hit
    · exact ut (allU _ hh)

private theorem allFold {n m k : ℕ} {x : Fin m → Finset (Fin n)} {tr : List (Col m)}
    {S : Set (Col m)} {ι : Type} (s : Finset ι) (F : ι → Col m) (H : Built x tr k S)
    (unit : (fun _ => true) ∈ S) (get : ∀ a ∈ s, F a ∈ S) :
    Grow x tr k S s.card (fun j => decide (∀ a ∈ s, F a j = true)) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨S, by simpa using H, Set.Subset.rfl, by simpa using unit⟩
  | @insert a s fr ih =>
    obtain ⟨T, h, st, ft⟩ := ih (fun a ha => get a (Finset.mem_insert_of_mem ha))
    have g := Built.andGate h (st (get a (Finset.mem_insert_self _ _))) ft
    refine ⟨_, by simpa [Finset.card_insert_of_notMem fr, Nat.add_assoc] using g,
      st.trans (Set.subset_insert _ _), ?_⟩
    apply Set.mem_insert_iff.mpr; left
    funext j
    simp [conj, Bool.decide_and]

private theorem anyFold {n m k : ℕ} {x : Fin m → Finset (Fin n)} {tr : List (Col m)}
    {S : Set (Col m)} {ι : Type} (s : Finset ι) (F : ι → Col m) (H : Built x tr k S)
    (unit : (fun _ => false) ∈ S) (get : ∀ a ∈ s, F a ∈ S) :
    Grow x tr k S s.card (fun j => decide (∃ a ∈ s, F a j = true)) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨S, by simpa using H, Set.Subset.rfl, by simpa using unit⟩
  | @insert a s fr ih =>
    obtain ⟨T, h, st, ft⟩ := ih (fun a ha => get a (Finset.mem_insert_of_mem ha))
    have g := Built.orGate h (st (get a (Finset.mem_insert_self _ _))) ft
    refine ⟨_, by simpa [Finset.card_insert_of_notMem fr, Nat.add_assoc] using g,
      st.trans (Set.subset_insert _ _), ?_⟩
    apply Set.mem_insert_iff.mpr; left
    funext j
    simp [disj, Bool.decide_or]

private noncomputable def indicator (x : Fin m → Finset (Fin n)) (v : Fin m → ℕ) (i : Fin m) :
    Col m :=
  fun j => decide (x i ⊆ x j ∧ v i = v j)

private noncomputable def hist (r : ℕ) (v : Fin m → ℕ) : List (Col m) :=
  List.ofFn fun b : Fin r => fun i => !(v i).testBit (r - 1 - b.val)

private theorem hist_succ (r : ℕ) (v : Fin m → ℕ) :
    hist (r + 1) v = hist r (fun i => v i / 2) ++ [fun i => !(v i).testBit 0] := by
  rw [hist, List.ofFn_succ', List.concat_eq_append]
  congr 1
  · unfold hist
    congr 1
    funext b i
    simp [Nat.testBit_div_two, show r - 1 - (b : ℕ) + 1 = r + 1 - 1 - b by have := b.isLt; omega]
  · simp

private theorem stages {n m : ℕ} (x : Fin m → Finset (Fin n)) (r : ℕ) (v : Fin m → ℕ)
    (cap : ∀ i, v i < 2 ^ r) (mono : ∀ i j, x i ⊆ x j → v i ≤ v j) :
    ∃ S, Built x (hist r v) (m * (n + 2 * r) + r) S ∧ base x ⊆ S ∧ ∀ i, indicator x v i ∈ S := by
  induction r generalizing v with
  | zero =>
    have z : ∀ i, v i = 0 := fun i => by have := cap i; simp at this; omega
    obtain ⟨T, bt, st, allT⟩ := batch (Finset.univ : Finset (Fin m)) (indicator x v) n
      (Built.start (x := x)) (by
      intro K U h bu i _
      obtain ⟨V, hh, sub, fi⟩ := allFold (x i) (sing x) h (bu (Or.inr (Or.inl rfl)))
        (fun a _ => bu (Or.inr (Or.inr ⟨a, rfl⟩)))
      have lim := Finset.card_le_univ (x i)
      refine ⟨V, hh.relax (by simpa using Nat.add_le_add_left lim K) Set.Subset.rfl, sub, ?_⟩
      have eq : indicator x v i = (fun j => decide (∀ a ∈ x i, sing x a j = true)) := by
        funext j; simp [indicator, sing, z, Finset.subset_iff]
      rw [eq]; convert fi using 1; funext j; apply Bool.eq_iff_iff.mpr; simp)
    exact ⟨T, by simpa [hist] using bt, st, fun i => allT i (Finset.mem_univ _)⟩
  | succ r ih =>
    let u := fun i => v i / 2
    have ucap : ∀ i, u i < 2 ^ r := fun i => by
      have := cap i; simp [pow_succ] at this; dsimp [u]; omega
    obtain ⟨S, h, bs, hInd⟩ := ih u ucap (fun i j h => Nat.div_le_div_right (mono i j h))
    let bit : Col m := fun i => (v i).testBit 0
    let sel := Finset.univ.filter fun i => bit i = true
    obtain ⟨T, hT, st, hit⟩ := anyFold sel (indicator x u) h (bs (Or.inl rfl)) (fun i _ => hInd i)
    have eqn : (fun j => decide (∃ a ∈ sel, indicator x u a j = true)) = bit := by
      funext j
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, indicator, sel, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨a, ba, sub, eq⟩
        have ord := mono a j sub
        simp [u] at eq
        simp [bit] at ba ⊢
        omega
      · intro b; exact ⟨j, b, Finset.Subset.rfl, rfl⟩
    have hit2 : bit ∈ T := by
      rw [← eqn]; convert hit using 1; funext j; apply Bool.eq_iff_iff.mpr; simp
    have hn := Built.notGate hT hit2
    let U := insert (inv bit) T
    have su : S ⊆ U := st.trans (Set.subset_insert _ _)
    obtain ⟨V, hV, uv, allV⟩ := batch (Finset.univ : Finset (Fin m)) (indicator x v) 1 hn (by
      intro K W hw uw i _
      have iw := uw (su (hInd i))
      by_cases bi : bit i = true
      · have same : indicator x v i = indicator x u i := by
          funext j; simp only [indicator, decide_eq_decide]
          constructor
          · rintro ⟨a, b⟩; exact ⟨a, congrArg (· / 2) b⟩
          · rintro ⟨a, b⟩; have ord := mono i j a
            simp [bit] at bi; dsimp [u] at b; exact ⟨a, by omega⟩
        exact ⟨W, hw.relax (by omega) Set.Subset.rfl, Set.Subset.rfl, same ▸ iw⟩
      · have bw : inv bit ∈ W := uw (Set.mem_insert _ _)
        have made := Built.andGate hw iw bw
        refine ⟨_, made, Set.subset_insert _ _, Set.mem_insert_iff.mpr (Or.inl ?_)⟩
        funext j
        apply Bool.eq_iff_iff.mpr
        simp only [indicator, conj, inv, decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true']
        simp [bit] at bi
        simp [bit, u]
        grind)
    have lim : sel.card ≤ m := by simpa using Finset.card_le_univ sel
    rw [hist_succ]
    refine ⟨V, hV.relax ?_ Set.Subset.rfl, (bs.trans su).trans uv,
      fun i => allV i (Finset.mem_univ _)⟩
    simp only [Finset.card_univ, Fintype.card_fin, mul_one]
    simp only [Nat.mul_add, Nat.mul_succ] at *
    omega

private noncomputable def decode (i : Fin m) : List (Col m) → ℕ
  | [] => 0
  | a :: as => 2 * decode i as + if a i then 0 else 1

private noncomputable def score (i : Fin m) (word : List (Col m)) : ℕ :=
  decode i word.reverse

private theorem snocScore (i : Fin m) (l : List (Col m)) (f : Col m) :
    score i (l ++ [f]) = 2 * score i l + if f i then 0 else 1 := by
  simp [score, decode]

private theorem decodeHist {m : ℕ} (i : Fin m) (r : ℕ) (v : Fin m → ℕ)
    (cap : ∀ j, v j < 2 ^ r) :
    score i (hist r v) = v i := by
  induction r generalizing v with
  | zero =>
    have hi := cap i
    simpa [hist, score, decode] using
      (show 0 = v i by simpa using (Nat.eq_zero_of_le_zero (by simpa using hi)).symm)
  | succ r ih =>
    rw [hist_succ, snocScore, ih _ (fun j => by have := cap j; rw [pow_succ] at this; omega)]
    simp [Nat.testBit_zero]
    split <;> omega

private theorem other (x : Fin m → Finset (Fin n)) (gs : List Gate) (g : Gate) {p}
    (hp : p ≠ n + 2 + gs.length) : val x (gs ++ [g]) p = val x gs p := by
  by_cases low : p < n + 2 + gs.length
  · exact old x gs g low
  funext i
  have oz := wirelen gs (raw x i)
  have nz := wirelen (gs ++ [g]) (raw x i)
  rw [show (raw x i).length = n + 2 by simp [raw, bitsDef]] at oz nz
  simp only [List.length_append, List.length_singleton] at nz
  unfold val
  rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

private theorem rawMono {n m : ℕ} {x : Fin m → Finset (Fin n)} {i j : Fin m}
    (sub : x i ⊆ x j) (p : ℕ) :
    val x [] p i = true → val x [] p j = true := by
  by_cases hp : p < n
  · simp only [val, Circuit.wires, List.foldl_nil, raw, bitsDef]
    rw [List.getD_append _ _ _ _ (by simpa using hp),
      List.getD_append _ _ _ _ (by simpa using hp)]
    simpa [List.getD_eq_getElem?_getD, hp] using @sub ⟨p, hp⟩
  · simp only [val, Circuit.wires, List.foldl_nil, raw, bitsDef]
    rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hp),
      List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hp)]
    simp

private theorem ordinary {n m : ℕ} {x : Fin m → Finset (Fin n)} {i j : Fin m} {gs : List Gate}
    (prior : ∀ p, val x gs p i = true → val x gs p j = true)
    (g : Gate) (op : g.op = .and ∨ g.op = .or) :
    val x (gs ++ [g]) (n + 2 + gs.length) i = true →
      val x (gs ++ [g]) (n + 2 + gs.length) j = true := by
  rw [fresh, fresh]
  rcases op with op | op
  · simp only [op, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    exact fun h p hp => prior _ (h p hp)
  · simp only [op, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨p, hp, v⟩; exact ⟨p, hp, prior _ v⟩

private theorem inverseGate {n m : ℕ} {x : Fin m → Finset (Fin n)} {i j : Fin m} {gs : List Gate}
    (prior : ∀ p, val x gs p i = true → val x gs p j = true)
    (g : Gate) (op : g.op = .not) :
    val x (gs ++ [g]) (n + 2 + gs.length) j = true →
      val x (gs ++ [g]) (n + 2 + gs.length) i = true := by
  rw [fresh, fresh]
  cases args : g.inputs with
  | nil => simp [op, GateOp.eval]
  | cons a l =>
    have h := prior a
    simp [op, GateOp.eval]
    cases e : val x gs a i <;> cases d : val x gs a j <;> simp_all

private theorem stepOrder {n m : ℕ} (x : Fin m → Finset (Fin n)) (gs : List Gate)
    (fan : FanInTwo ⟨gs, 0⟩) (i j : Fin m) (sub : x i ⊆ x j) :
    score i (trace x gs) ≤ score j (trace x gs) ∧
      (score i (trace x gs) = score j (trace x gs) →
        ∀ p, val x gs p i = true → val x gs p j = true) := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨le_refl _, fun _ => rawMono sub⟩
  | append_singleton gs g ih =>
    obtain ⟨le, transfer⟩ := ih (fun u hu => fan u (List.mem_append_left _ hu))
    have ops := (fan g (List.mem_append_right _ (List.mem_singleton_self _))).1
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at ops
    by_cases nt : g.op = .not
    · simp only [traceAdd, ite_eq_left nt, snocScore]
      let p := n + 2 + gs.length
      by_cases eq : score i (trace x gs) = score j (trace x gs)
      · have ant := inverseGate (transfer eq) g nt
        constructor
        · rw [eq]
          change _ + (if val x (gs ++ [g]) p i then 0 else 1) ≤
            _ + (if val x (gs ++ [g]) p j then 0 else 1)
          cases ai : val x (gs ++ [g]) p i <;> cases aj : val x (gs ++ [g]) p j <;> simp_all [p]
        · intro same a
          by_cases aeq : a = p
          · subst a
            dsimp [p] at *
            split at same <;> split at same <;> simp_all
          · rw [other x gs g aeq]; exact transfer eq _
      · have strict := lt_of_le_of_ne le eq
        split <;> split <;> constructor <;> omega
    · have ao : g.op = .and ∨ g.op = .or := ops.elim Or.inl (fun h => Or.inr (h.resolve_right nt))
      simp only [traceAdd, ite_eq_right nt, List.append_nil]
      refine ⟨le, fun eq a => ?_⟩
      by_cases he : a = n + 2 + gs.length
      · subst a; exact ordinary (transfer eq) g ao
      · rw [other x gs g he]; exact transfer eq _

end WireAndSynthesis

section BinFoldAndRank
open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private def binFold (f : ℕ → Bool) (l : List ℕ) (acc : ℕ) : ℕ :=
  l.foldl (fun v j => 2 * v + if f j then 0 else 1) acc

private theorem binFold_snoc (f : ℕ → Bool) (l : List ℕ) (a acc : ℕ) :
    binFold f (l ++ [a]) acc = 2 * binFold f l acc + if f a then 0 else 1 := by
  simp [binFold, List.foldl_append]

private theorem binFold_append (f : ℕ → Bool) (l1 l2 : List ℕ) (acc : ℕ) :
    binFold f (l1 ++ l2) acc = binFold f l2 (binFold f l1 acc) := by
  simp [binFold, List.foldl_append]

private theorem binFold_acc (f : ℕ → Bool) (l : List ℕ) (acc : ℕ) :
    binFold f l acc = acc * 2 ^ l.length + binFold f l 0 := by
  induction l using List.reverseRecOn with
  | nil => simp [binFold]
  | append_singleton l a ih =>
    rw [binFold_snoc, binFold_snoc, ih]
    simp only [List.length_append, List.length_singleton, pow_succ]
    ring

private theorem binFold_lt (f : ℕ → Bool) (l : List ℕ) :
    binFold f l 0 < 2 ^ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [binFold]
  | append_singleton l a ih =>
    rw [binFold_snoc]
    simp only [List.length_append, List.length_singleton, pow_succ]
    cases f a <;> simp <;> omega

private theorem binFold_div_pow (f : ℕ → Bool) (l : List ℕ) (s : ℕ) :
    binFold f l 0 / 2 ^ s = binFold f (l.take (l.length - s)) 0 := by
  by_cases hs : s ≤ l.length
  · have hsp : l = l.take (l.length - s) ++ l.drop (l.length - s) := (List.take_append_drop _ _).symm
    have hdl : (l.drop (l.length - s)).length = s := by simp; omega
    conv_lhs => rw [hsp]
    rw [binFold_append, binFold_acc, hdl]
    have hlt : binFold f (l.drop (l.length - s)) 0 < 2 ^ s := by
      simpa [hdl] using binFold_lt f (l.drop (l.length - s))
    have hpos : 0 < 2 ^ s := Nat.two_pow_pos s
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlt, Nat.zero_add]
  · have hzero : l.length - s = 0 := by omega
    rw [hzero, List.take_zero]
    simp only [binFold, List.foldl_nil]
    have hlt : binFold f l 0 < 2 ^ s :=
      lt_of_lt_of_le (binFold_lt f l) (Nat.pow_le_pow_right (by omega) (by omega))
    exact Nat.div_eq_of_lt hlt

private theorem binFold_inj (f g : ℕ → Bool) (l : List ℕ)
    (heq : binFold f l 0 = binFold g l 0) : ∀ j ∈ l, f j = g j := by
  induction l using List.reverseRecOn with
  | nil => intro j hj; cases hj
  | append_singleton l a ih =>
    rw [binFold_snoc, binFold_snoc] at heq
    have hfa : f a = g a := by
      cases hf : f a <;> cases hg : g a <;> simp_all <;> omega
    have hl : binFold f l 0 = binFold g l 0 := by
      rw [hfa] at heq; omega
    intro j hj
    rcases List.mem_append.mp hj with h1 | h2
    · exact ih hl j h1
    · rw [List.mem_singleton.mp h2]; exact hfa

private noncomputable def rankDef (d : ℕ) (C : Circuit) (x : Finset (Fin d)) : ℕ :=
  binFold (fun j => (C.wires (bitsDef d x)).getD (d + 2 + j) false) (ix C.gates) 0

private theorem score_eq_binFold {n m : ℕ} (x : Fin m → Finset (Fin n)) (gs : List Gate)
    (i : Fin m) :
    score i (trace x gs) =
      binFold (fun j => ((Circuit.mk gs 0).wires (bitsDef n (x i))).getD (n + 2 + j) false)
        (ix gs) 0 := by
  have hgen : ∀ (l : List ℕ),
      score i (l.map fun j => val x gs (n + 2 + j)) =
        binFold (fun j => ((Circuit.mk gs 0).wires (bitsDef n (x i))).getD (n + 2 + j) false)
          l 0 := by
    intro l
    induction l using List.reverseRecOn with
    | nil => simp [score, decode, binFold]
    | append_singleton l a ih =>
      rw [List.map_append, List.map_singleton, snocScore, binFold_snoc, ih]
      rfl
  exact hgen (ix gs)

private theorem rankDef_lt (d : ℕ) (C : Circuit) (x : Finset (Fin d)) :
    rankDef d C x < 2 ^ PEqualNP.NotBracket.notCount C := by
  rw [notCount_eq_ix_length]
  exact binFold_lt _ _

private theorem rankDef_mono (d : ℕ) (C : Circuit) (hFan : FanInTwo C)
    {u v : Finset (Fin d)} (huv : u ⊆ v) :
    rankDef d C u ≤ rankDef d C v := by
  let x : Fin 2 → Finset (Fin d) := fun idx => if idx.val = 0 then u else v
  have hfan0 : FanInTwo ⟨C.gates, 0⟩ := hFan
  have hst := (stepOrder x C.gates hfan0 0 1 (by simpa [x] using huv)).1
  rw [score_eq_binFold, score_eq_binFold] at hst
  simpa [rankDef, x, Circuit.wires] using hst

private theorem mem_filter_range_take (p : ℕ → Bool) (m t h : ℕ)
    (ht : t < m) (hpt : p t = true)
    (hcnt : ((List.range t).filter p).length < h) :
    t ∈ ((List.range m).filter p).take h := by
  have hsplit : ∃ rest, (List.range m).filter p = (List.range t).filter p ++ t :: rest := by
    induction m with
    | zero => omega
    | succ m ih =>
      by_cases htm : t < m
      · obtain ⟨rest, hrest⟩ := ih htm
        refine ⟨rest ++ (if p m then [m] else []), ?_⟩
        rw [List.range_succ, List.filter_append, hrest]
        by_cases hpm : p m = true <;> simp [hpm, List.append_assoc]
      · obtain rfl : t = m := by omega
        refine ⟨[], ?_⟩
        rw [List.range_succ, List.filter_append]
        simp [hpt]
  obtain ⟨rest, hrest⟩ := hsplit
  rw [hrest, List.take_append]
  have hsub : 1 ≤ h - ((List.range t).filter p).length := by omega
  obtain ⟨k, hk⟩ : ∃ k, h - ((List.range t).filter p).length = k + 1 :=
    ⟨h - ((List.range t).filter p).length - 1, by omega⟩
  rw [hk, List.take_succ_cons]
  exact List.mem_append_right _ List.mem_cons_self

end BinFoldAndRank

section FreezeCircuit
open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private noncomputable def notBefore (gs : List Gate) (m : ℕ) : ℕ :=
  ((List.range m).filter (fun j => decide ((gs.getD j ⟨.or, []⟩).op = .not))).length

private theorem notBefore_zero (gs : List Gate) : notBefore gs 0 = 0 := rfl

private theorem notBefore_succ (gs : List Gate) (m : ℕ) :
    notBefore gs (m + 1) =
      notBefore gs m + if (gs.getD m ⟨.or, []⟩).op = .not then 1 else 0 := by
  unfold notBefore
  rw [List.range_succ, List.filter_append, List.length_append]
  by_cases h : (gs.getD m ⟨.or, []⟩).op = .not
  · simp only [List.filter_cons, List.filter_nil, decide_eq_true h, ↓reduceIte,
      List.length_singleton, ite_eq_left h]
  · simp only [List.filter_cons, List.filter_nil, decide_eq_false h, Bool.false_eq_true,
      ↓reduceIte, List.length_nil, ite_eq_right h]

private theorem notBefore_length (gs : List Gate) : notBefore gs gs.length = (ix gs).length := rfl

private noncomputable def freezeStep (d h : ℕ) (val0 : ℕ → Bool) (gs : List Gate) :
    ℕ → List Gate × (ℕ → ℕ) × ℕ
  | 0 => ([], id, 0)
  | m + 1 =>
    let (out, mp, fr) := freezeStep d h val0 gs m
    let g := gs.getD m ⟨.or, []⟩
    if g.op = .not ∧ fr < h then
      let w := if val0 (d + 2 + m) then d + 1 else d
      (out, fun j => if j = d + 2 + m then w else mp j, fr + 1)
    else
      let g' : Gate := ⟨g.op, g.inputs.map mp⟩
      let w := d + 2 + out.length
      (out ++ [g'], fun j => if j = d + 2 + m then w else mp j, fr)

private theorem freezeStep_spec (d h : ℕ) (C : Circuit) (val0 : ℕ → Bool)
    (hFan : FanInTwo C) (hRB : ReadsBack (d + 2) C) :
    ∀ m ≤ C.gates.length,
      let res := freezeStep d h val0 C.gates m
      let out := res.1
      let mp := res.2.1
      let fr := res.2.2
      FanInTwo ⟨out, 0⟩ ∧
      ReadsBack (d + 2) ⟨out, 0⟩ ∧
      out.length + fr = m ∧
      (ix out).length + fr = notBefore C.gates m ∧
      fr = min h (notBefore C.gates m) ∧
      (∀ j < d + 2 + m, mp j < d + 2 + out.length) ∧
      ∀ (x : Finset (Fin d)),
        (∀ t < m, (C.gates.getD t ⟨.or, []⟩).op = .not → notBefore C.gates t < h →
          (C.wires (bitsDef d x)).getD (d + 2 + t) false = val0 (d + 2 + t)) →
        ∀ j < d + 2 + m,
          ((Circuit.mk out 0).wires (bitsDef d x)).getD (mp j) false =
            (C.wires (bitsDef d x)).getD j false := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨by simp [freezeStep, FanInTwo], by simp [freezeStep, ReadsBack],
      rfl, rfl, by simp [freezeStep, notBefore], fun j hj => by simpa [freezeStep] using hj, ?_⟩
    intro x _ j hj
    simp only [freezeStep, id_eq]
    have hlen : j < (bitsDef d x).length := by rw [bitsDef_length]; omega
    rw [wires_input [] (bitsDef d x) j hlen]
    exact (wires_input C.gates (bitsDef d x) j hlen).symm
  | succ m ih =>
    intro hm1
    have hm : m < C.gates.length := Nat.lt_of_succ_le hm1
    obtain ⟨ihFan, ihRB, ihLen, ihNot, ihFr, ihBound, ihSim⟩ := ih (Nat.le_of_lt hm)
    rcases hres_def : freezeStep d h val0 C.gates m with ⟨out, mp, fr⟩
    simp only [hres_def] at ihFan ihRB ihLen ihNot ihFr ihBound ihSim
    set g := C.gates.getD m ⟨.or, []⟩ with hg_def
    have hg_mem : g ∈ C.gates := by
      rw [hg_def, List.getD_eq_getElem C.gates _ hm]
      exact List.getElem_mem hm
    have hrb_m : ∀ u ∈ g.inputs, u < d + 2 + m := fun u hu => hRB m hm u hu
    have hnb_succ : notBefore C.gates (m + 1) = notBefore C.gates m + if g.op = .not then 1 else 0 :=
      notBefore_succ C.gates m
    by_cases hcond : g.op = .not ∧ fr < h
    · have hStep : freezeStep d h val0 C.gates (m + 1) =
          (out, fun j => if j = d + 2 + m then (if val0 (d + 2 + m) then d + 1 else d) else mp j,
            fr + 1) := by
        dsimp only [freezeStep]
        rw [hres_def]
        dsimp only
        rw [← hg_def]
        exact ite_eq_left hcond
      rw [hStep]
      dsimp only
      have hnb_lt : notBefore C.gates m < h := by omega
      refine ⟨ihFan, ihRB, by omega, ?_, ?_, ?_, ?_⟩
      · rw [hnb_succ, ite_eq_left hcond.1]; omega
      · rw [hnb_succ, ite_eq_left hcond.1]; omega
      · intro j hj
        by_cases hjm : j = d + 2 + m
        · rw [ite_eq_left hjm]; cases val0 (d + 2 + m) <;> simp <;> omega
        · rw [ite_eq_right hjm]; exact ihBound j (by omega)
      · intro x hAgree j hj
        by_cases hjm : j = d + 2 + m
        · subst hjm
          rw [ite_eq_left rfl]
          have hAx := hAgree m (Nat.lt_succ_self m) hcond.1 hnb_lt
          rw [hAx]
          cases hval : val0 (d + 2 + m)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            rw [wires_input out (bitsDef d x) d (by rw [bitsDef_length]; omega), bitsDef_getD_d]
          · simp only [↓reduceIte]
            rw [wires_input out (bitsDef d x) (d + 1) (by rw [bitsDef_length]; omega), bitsDef_getD_d1]
        · rw [ite_eq_right hjm]
          exact ihSim x (fun t ht => hAgree t (Nat.lt_trans ht (Nat.lt_succ_self m))) j (by omega)
    · have hStep : freezeStep d h val0 C.gates (m + 1) =
          (out ++ [⟨g.op, g.inputs.map mp⟩],
            fun j => if j = d + 2 + m then d + 2 + out.length else mp j, fr) := by
        dsimp only [freezeStep]
        rw [hres_def]
        dsimp only
        rw [← hg_def]
        exact ite_eq_right hcond
      rw [hStep]
      dsimp only
      let g' : Gate := ⟨g.op, g.inputs.map mp⟩
      have hFan' : FanInTwo ⟨out ++ [g'], 0⟩ := by
        intro u hu
        rcases List.mem_append.mp hu with h1 | h2
        · exact ihFan u h1
        · obtain rfl : u = g' := List.mem_singleton.mp h2
          have hf := hFan g hg_mem
          exact ⟨hf.1, by simp [g', hf.2]⟩
      have hRB' : ReadsBack (d + 2) ⟨out ++ [g'], 0⟩ := by
        apply extendBack d out g' ihRB
        intro p hp
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hp
        exact ihBound u (hrb_m u hu)
      have hix' : (ix (out ++ [g'])).length = (ix out).length + if g.op = .not then 1 else 0 := by
        rw [ixAdd]
        by_cases hn : g.op = .not
        · simp only [g', hn, ↓reduceIte, List.length_append, List.length_singleton]
        · simp only [g', hn, ↓reduceIte, List.append_nil, Nat.add_zero]
      refine ⟨hFan', hRB', by simp; omega, ?_, ?_, ?_, ?_⟩
      · rw [hix', hnb_succ]; omega
      · rw [hnb_succ]
        by_cases hn : g.op = .not
        · have hge : h ≤ fr := by
            by_contra hlt; exact hcond ⟨hn, by omega⟩
          simp only [ite_eq_left hn]; omega
        · simp only [ite_eq_right hn, Nat.add_zero]; exact ihFr
      · intro j hj
        by_cases hjm : j = d + 2 + m
        · rw [ite_eq_left hjm]; simp
        · rw [ite_eq_right hjm]; have := ihBound j (by omega); simp; omega
      · intro x hAgree j hj
        have hAgree_prev : ∀ t < m, (C.gates.getD t ⟨.or, []⟩).op = .not →
            notBefore C.gates t < h →
            (C.wires (bitsDef d x)).getD (d + 2 + t) false = val0 (d + 2 + t) :=
          fun t ht => hAgree t (Nat.lt_trans ht (Nat.lt_succ_self m))
        by_cases hjm : j = d + 2 + m
        · subst hjm
          rw [ite_eq_left rfl]
          have hlen_out : ((Circuit.mk out 0).wires (bitsDef d x)).length = d + 2 + out.length := by
            rw [wirelen, bitsDef_length]
          rw [wires_snoc]
          conv_lhs => rw [← hlen_out]
          rw [List.getD_append_right _ _ _ _ le_rfl]
          simp only [Nat.sub_self, List.getD_cons_zero, List.map_map]
          have hCeval := wires_gate_eval C.gates (bitsDef d x) m hm (by
            rw [bitsDef_length]; exact hrb_m)
          rw [bitsDef_length] at hCeval
          change _ = ((Circuit.mk C.gates 0).wires (bitsDef d x)).getD (d + 2 + m) false
          rw [hCeval, ← hg_def]
          congr 1
          refine List.map_congr_left fun u hu => ?_
          exact ihSim x hAgree_prev u (hrb_m u hu)
        · rw [ite_eq_right hjm]
          have hlt : mp j < (bitsDef d x).length + out.length := by
            rw [bitsDef_length]; exact ihBound j (by omega)
          rw [wires_prefix out [g'] (bitsDef d x) (mp j) hlt]
          exact ihSim x hAgree_prev j (by omega)

end FreezeCircuit

section MainProof
open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private theorem div_pred_ne_of_dvd {c s : ℕ} (hc : 0 < c) (hdvd : 2 ^ s ∣ c) :
    (c - 1) / 2 ^ s ≠ c / 2 ^ s := by
  obtain ⟨q, hq⟩ := hdvd
  have hpos : 0 < 2 ^ s := Nat.two_pow_pos s
  have hqpos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with rfl | hp
    · simp at hq; omega
    · exact hp
  have h1 : c / 2 ^ s = q := by rw [hq, Nat.mul_div_right _ hpos]
  have h2 : c - 1 = (2 ^ s - 1) + 2 ^ s * (q - 1) := by
    have : 2 ^ s * q = 2 ^ s * (q - 1) + 2 ^ s := by
      conv_lhs => rw [show q = (q - 1) + 1 by omega, Nat.mul_add, Nat.mul_one]
    omega
  have h3 : (c - 1) / 2 ^ s = q - 1 := by
    rw [h2, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt (by omega), Nat.zero_add]
  omega

private theorem forward_dir (k b L : ℕ) (s : Fin k → ℕ)
    (hnpack : ¬ ∃ J : Finset (Fin k), L < J.card ∧ ∃ c : Fin k → ℕ,
      (∀ i ∈ J, 0 < c i ∧ c i < 2 ^ b ∧ 2 ^ (s i) ∣ c i) ∧
      ∀ i ∈ J, ∀ j ∈ J, i < j → c i < c j)
    (d : ℕ) (G : Fin k → Finset (Finset (Fin d))) (C : Circuit)
    (hG : ∀ i, (G i).Nonempty)
    (hord : ∀ i j, i < j → ∀ x ∈ G i, ∀ y ∈ G j, x ⊆ y)
    (hFan : FanInTwo C) (hRB : ReadsBack (d + 2) C)
    (hNot : PEqualNP.NotBracket.notCount C = b) :
    ∃ H : Finset (Fin k), k - L ≤ H.card ∧ ∀ i ∈ H,
      ∃ (z : ℕ) (D : Circuit) (copy : ℕ → ℕ),
        (FanInTwo D ∧ ReadsBack (d + 2) D ∧ D.output < d + 2 + D.size) ∧
        PEqualNP.NotBracket.notCount D ≤ s i ∧
        D.size - PEqualNP.NotBracket.notCount D ≤ C.size - b ∧
        (∀ j, j < d + 2 + C.size → copy j < d + 2 + D.size) ∧
        ∀ x ∈ G i, rankDef d C x / 2 ^ (s i) = z ∧
          ∀ j, j < d + 2 + C.size →
            (D.wires (bitsDef d x)).getD (copy j) false = (C.wires (bitsDef d x)).getD j false := by
  let H : Finset (Fin k) := Finset.univ.filter fun i =>
    ∀ x ∈ G i, ∀ y ∈ G i, rankDef d C x / 2 ^ (s i) = rankDef d C y / 2 ^ (s i)
  let Bad : Finset (Fin k) := Finset.univ \ H
  have hBad_le : Bad.card ≤ L := by
    by_contra hgt
    have hgt : L < Bad.card := Nat.lt_of_not_ge hgt
    let img : Fin k → Finset ℕ := fun i => (G i).image (rankDef d C)
    have himg_ne : ∀ i, (img i).Nonempty := fun i => (hG i).image (rankDef d C)
    let lo : Fin k → ℕ := fun i => (img i).min' (himg_ne i)
    let hi : Fin k → ℕ := fun i => (img i).max' (himg_ne i)
    have hlo_mem : ∀ i, ∃ x ∈ G i, rankDef d C x = lo i := fun i =>
      Finset.mem_image.mp (Finset.min'_mem (img i) (himg_ne i))
    have hhi_mem : ∀ i, ∃ x ∈ G i, rankDef d C x = hi i := fun i =>
      Finset.mem_image.mp (Finset.max'_mem (img i) (himg_ne i))
    have hlo_le : ∀ i, ∀ x ∈ G i, lo i ≤ rankDef d C x := fun i x hx =>
      Finset.min'_le (img i) _ (Finset.mem_image_of_mem _ hx)
    have hle_hi : ∀ i, ∀ x ∈ G i, rankDef d C x ≤ hi i := fun i x hx =>
      Finset.le_max' (img i) _ (Finset.mem_image_of_mem _ hx)
    have hhi_lt : ∀ i, hi i < 2 ^ b := by
      intro i
      obtain ⟨x, _, hx⟩ := hhi_mem i
      rw [← hx, ← hNot]
      exact rankDef_lt d C x
    have hhi_le_lo : ∀ i j, i < j → hi i ≤ lo j := by
      intro i j hij
      obtain ⟨x, hx, hrx⟩ := hhi_mem i
      obtain ⟨y, hy, hry⟩ := hlo_mem j
      rw [← hrx, ← hry]
      exact rankDef_mono d C hFan (hord i j hij x hx y hy)
    have hBad_lt : ∀ i ∈ Bad, lo i / 2 ^ (s i) < hi i / 2 ^ (s i) := by
      intro i hiBad
      have hnotH : i ∉ H := (Finset.mem_sdiff.mp hiBad).2
      simp only [H, Finset.mem_filter, Finset.mem_univ, true_and, not_forall] at hnotH
      obtain ⟨x, hx, y, hy, hne⟩ := hnotH
      have hx1 : lo i / 2 ^ (s i) ≤ rankDef d C x / 2 ^ (s i) := Nat.div_le_div_right (hlo_le i x hx)
      have hx2 : rankDef d C x / 2 ^ (s i) ≤ hi i / 2 ^ (s i) := Nat.div_le_div_right (hle_hi i x hx)
      have hy1 : lo i / 2 ^ (s i) ≤ rankDef d C y / 2 ^ (s i) := Nat.div_le_div_right (hlo_le i y hy)
      have hy2 : rankDef d C y / 2 ^ (s i) ≤ hi i / 2 ^ (s i) := Nat.div_le_div_right (hle_hi i y hy)
      omega
    let c : Fin k → ℕ := fun i => 2 ^ (s i) * (lo i / 2 ^ (s i) + 1)
    have hc_lo : ∀ i, lo i < c i := by
      intro i
      dsimp only [c]
      have hdm := Nat.div_add_mod (lo i) (2 ^ (s i))
      have hml := Nat.mod_lt (lo i) (Nat.two_pow_pos (s i))
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have hc_hi : ∀ i ∈ Bad, c i ≤ hi i := by
      intro i hiBad
      dsimp only [c]
      have h1 : lo i / 2 ^ (s i) + 1 ≤ hi i / 2 ^ (s i) := hBad_lt i hiBad
      have h2 := Nat.mul_le_mul_left (2 ^ (s i)) h1
      have h3 := Nat.mul_div_le (hi i) (2 ^ (s i))
      omega
    apply hnpack
    refine ⟨Bad, hgt, c, ?_, ?_⟩
    · intro i hiBad
      refine ⟨Nat.mul_pos (Nat.two_pow_pos (s i)) (Nat.succ_pos _),
        lt_of_le_of_lt (hc_hi i hiBad) (hhi_lt i), ⟨_, rfl⟩⟩
    · intro i hiBad j hjBad hij
      exact lt_of_le_of_lt (le_trans (hc_hi i hiBad) (hhi_le_lo i j hij)) (hc_lo j)
  have hH_card : k - L ≤ H.card := by
    have hsum : H.card + Bad.card = k := by
      have hsub : H ⊆ Finset.univ := Finset.subset_univ H
      have hc := Finset.card_sdiff_add_card_eq_card hsub
      simpa [Bad, Nat.add_comm] using hc
    omega
  refine ⟨H, hH_card, ?_⟩
  intro i hiH
  have hconst : ∀ x ∈ G i, ∀ y ∈ G i, rankDef d C x / 2 ^ (s i) = rankDef d C y / 2 ^ (s i) :=
    (Finset.mem_filter.mp hiH).2
  obtain ⟨x0, hx0⟩ := hG i
  let z := rankDef d C x0 / 2 ^ (s i)
  let h := b - s i
  let val0 : ℕ → Bool := fun w => (C.wires (bitsDef d x0)).getD w false
  obtain ⟨hFanD, hRBD, hLenD, hNotD, hFrD, hBoundD, hSimD⟩ :=
    freezeStep_spec d h C val0 hFan hRB C.gates.length le_rfl
  rcases hres : freezeStep d h val0 C.gates C.gates.length with ⟨out, copy, fr⟩
  simp only [hres] at hFanD hRBD hLenD hNotD hFrD hBoundD hSimD
  let D : Circuit := ⟨out, 0⟩
  have hix_len : (ix C.gates).length = b := by rw [← notCount_eq_ix_length, hNot]
  have hnb_len : notBefore C.gates C.gates.length = b := by rw [notBefore_length, hix_len]
  have hFr_val : fr = b - s i := by
    rw [hFrD, hnb_len]
    exact Nat.min_eq_left (Nat.sub_le b (s i))
  have hNot_D_eq : PEqualNP.NotBracket.notCount D = (ix out).length := notCount_eq_ix_length D
  refine ⟨z, D, copy, ⟨hFanD, hRBD, by simp [D, Circuit.size]⟩, ?_, ?_, ?_, ?_⟩
  · rw [hNot_D_eq]
    rw [hnb_len] at hNotD
    omega
  · rw [hNot_D_eq]
    change out.length - (ix out).length ≤ C.gates.length - b
    rw [hnb_len] at hNotD
    omega
  · intro j hj
    exact hBoundD j hj
  · intro x hx
    have hdiv_eq : rankDef d C x / 2 ^ (s i) = z := hconst x hx x0 hx0
    refine ⟨hdiv_eq, ?_⟩
    have hAgree : ∀ t < C.gates.length, (C.gates.getD t ⟨.or, []⟩).op = .not →
        notBefore C.gates t < h →
        (C.wires (bitsDef d x)).getD (d + 2 + t) false = val0 (d + 2 + t) := by
      intro t ht hnot_t hcnt_t
      have hbf_eq : binFold (fun j => (C.wires (bitsDef d x)).getD (d + 2 + j) false)
            ((ix C.gates).take h) 0 =
          binFold (fun j => (C.wires (bitsDef d x0)).getD (d + 2 + j) false)
            ((ix C.gates).take h) 0 := by
        have h1 := binFold_div_pow (fun j => (C.wires (bitsDef d x)).getD (d + 2 + j) false)
          (ix C.gates) (s i)
        have h2 := binFold_div_pow (fun j => (C.wires (bitsDef d x0)).getD (d + 2 + j) false)
          (ix C.gates) (s i)
        rw [hix_len] at h1 h2
        rw [← h1, ← h2]
        exact hdiv_eq
      have ht_mem : t ∈ (ix C.gates).take h := by
        apply mem_filter_range_take (fun j => decide ((C.gates.getD j ⟨.or, []⟩).op = .not))
          C.gates.length t h ht (decide_eq_true hnot_t) hcnt_t
      exact binFold_inj _ _ _ hbf_eq t ht_mem
    exact hSimD x hAgree

private theorem backward_dir (k b L : ℕ) (s : Fin k → ℕ)
    (hpack : ∃ J : Finset (Fin k), L < J.card ∧ ∃ c : Fin k → ℕ,
      (∀ i ∈ J, 0 < c i ∧ c i < 2 ^ b ∧ 2 ^ (s i) ∣ c i) ∧
      ∀ i ∈ J, ∀ j ∈ J, i < j → c i < c j) :
    ¬ ∀ (d : ℕ) (G : Fin k → Finset (Finset (Fin d))) (C : Circuit),
        (∀ i, (G i).Nonempty) → (∀ i j, i < j → ∀ x ∈ G i, ∀ y ∈ G j, x ⊆ y) →
        (FanInTwo C ∧ ReadsBack (d + 2) C ∧ C.output < d + 2 + C.size) →
        PEqualNP.NotBracket.notCount C = b →
        ∃ H : Finset (Fin k), k - L ≤ H.card ∧ ∀ i ∈ H,
          ∃ (z : ℕ) (D : Circuit) (copy : ℕ → ℕ),
            (FanInTwo D ∧ ReadsBack (d + 2) D ∧ D.output < d + 2 + D.size) ∧
            PEqualNP.NotBracket.notCount D ≤ s i ∧
            D.size - PEqualNP.NotBracket.notCount D ≤ C.size - b ∧
            (∀ j, j < d + 2 + C.size → copy j < d + 2 + D.size) ∧
            ∀ x ∈ G i, rankDef d C x / 2 ^ (s i) = z ∧
              ∀ j, j < d + 2 + C.size →
                (D.wires (bitsDef d x)).getD (copy j) false =
                  (C.wires (bitsDef d x)).getD j false := by
  intro hall
  obtain ⟨J, hJcard, c, hcSpec, hcMono⟩ := hpack
  have hJne : J.Nonempty := Finset.card_pos.mp (by omega)
  have h2b_pos : 1 < 2 ^ b := by
    obtain ⟨j0, hj0⟩ := hJne
    have := hcSpec j0 hj0
    omega
  let d := 2 * k
  let X : Fin d → Finset (Fin d) := fun t => Finset.univ.filter fun a : Fin d => a.val < t.val
  have hX_sub : ∀ t u : Fin d, X t ⊆ X u ↔ t.val ≤ u.val := by
    intro t u
    constructor
    · intro hsub
      by_contra hgt
      have hut : u.val < t.val := by omega
      have hmem : u ∈ X t := by simp [X]; exact hut
      have hmemu : u ∈ X u := hsub hmem
      simp [X] at hmemu
    · intro hle a ha
      simp only [X, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      omega
  let G : Fin k → Finset (Finset (Fin d)) := fun i =>
    {X ⟨2 * i.val, by omega⟩, X ⟨2 * i.val + 1, by omega⟩}
  have hG_ne : ∀ i, (G i).Nonempty := fun i => ⟨X ⟨2 * i.val, by omega⟩, by simp [G]⟩
  have hG_ord : ∀ i j, i < j → ∀ x ∈ G i, ∀ y ∈ G j, x ⊆ y := by
    intro i j hij x hx y hy
    simp only [G, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      exact (hX_sub _ _).mpr (by dsimp only; have : i.val < j.val := hij; omega)
  let hold : Fin k → ℕ := fun i => (J.filter (· < i)).sup c
  let v : Fin d → ℕ := fun t =>
    let i : Fin k := ⟨t.val / 2, by omega⟩
    if i ∈ J then (if t.val % 2 = 0 then c i - 1 else c i) else hold i
  have hhold_lt : ∀ i, hold i < 2 ^ b := by
    intro i
    have hle : hold i ≤ 2 ^ b - 1 := by
      apply Finset.sup_le
      intro j hj
      have hjJ : j ∈ J := (Finset.mem_filter.mp hj).1
      have := (hcSpec j hjJ).2.1
      omega
    omega
  have hv_cap : ∀ t : Fin d, v t < 2 ^ b := by
    intro t
    dsimp only [v]
    split_ifs with h1 h2
    · have := (hcSpec _ h1).2.1; omega
    · exact (hcSpec _ h1).2.1
    · exact hhold_lt _
  have hv_mono : ∀ t u : Fin d, X t ⊆ X u → v t ≤ v u := by
    intro t u hsub
    have hle : t.val ≤ u.val := (hX_sub t u).mp hsub
    let i : Fin k := ⟨t.val / 2, by omega⟩
    let j : Fin k := ⟨u.val / 2, by omega⟩
    have hij_le : i.val ≤ j.val := by dsimp [i, j]; omega
    by_cases hij_eq : i = j
    · dsimp only [v]
      change (if i ∈ J then (if t.val % 2 = 0 then c i - 1 else c i) else hold i) ≤
        if j ∈ J then (if u.val % 2 = 0 then c j - 1 else c j) else hold j
      rw [hij_eq]
      split_ifs with h1 h2 h3
      · exact le_refl _
      · exact Nat.sub_le _ _
      · have hdiv : t.val / 2 = u.val / 2 := congrArg Fin.val hij_eq
        omega
      · exact le_refl _
      · exact le_refl _
    · have hij : i < j := Fin.lt_def.mpr (lt_of_le_of_ne hij_le (fun he => hij_eq (Fin.ext he)))
      have hvt_le_hold : v t ≤ hold j := by
        dsimp only [v]
        change (if i ∈ J then (if t.val % 2 = 0 then c i - 1 else c i) else hold i) ≤ hold j
        split_ifs with hiJ hmod
        · have hmem : i ∈ J.filter (· < j) := Finset.mem_filter.mpr ⟨hiJ, hij⟩
          exact le_trans (Nat.sub_le _ _) (Finset.le_sup (f := c) hmem)
        · have hmem : i ∈ J.filter (· < j) := Finset.mem_filter.mpr ⟨hiJ, hij⟩
          exact Finset.le_sup (f := c) hmem
        · apply Finset.sup_mono
          intro r hr
          simp only [Finset.mem_filter] at hr ⊢
          exact ⟨hr.1, lt_trans hr.2 hij⟩
      have hhold_le_vu : hold j ≤ v u := by
        dsimp only [v]
        change hold j ≤ if j ∈ J then (if u.val % 2 = 0 then c j - 1 else c j) else hold j
        split_ifs with hjJ hmod
        · apply Finset.sup_le
          intro r hr
          simp only [Finset.mem_filter] at hr
          have hlt := hcMono r hr.1 j hjJ hr.2
          omega
        · apply Finset.sup_le
          intro r hr
          simp only [Finset.mem_filter] at hr
          exact le_of_lt (hcMono r hr.1 j hjJ hr.2)
        · exact le_refl _
      exact le_trans hvt_le_hold hhold_le_vu
  obtain ⟨S, hBuilt, _, _⟩ := stages X b v hv_cap hv_mono
  obtain ⟨gs, hFan, hRB, _, htr, _⟩ := hBuilt
  let C : Circuit := ⟨gs, 0⟩
  have hNotC : PEqualNP.NotBracket.notCount C = b := by
    rw [notCount_eq_ix_length]
    have hlen := congrArg List.length htr
    simpa [trace, hist] using hlen
  have hrank_X : ∀ t : Fin d, rankDef d C (X t) = v t := by
    intro t
    have h1 := score_eq_binFold X gs t
    have h2 : score t (trace X gs) = v t := by
      rw [htr]; exact decodeHist t b v hv_cap
    rw [← h2, h1]
    rfl
  obtain ⟨H, hHcard, hHspec⟩ := hall d G C hG_ne hG_ord
    ⟨hFan, hRB, by simp [C, Circuit.size]⟩ hNotC
  have hHsub : H ⊆ Finset.univ \ J := by
    intro i hiH
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ i, ?_⟩
    intro hiJ
    obtain ⟨z, _, _, _, _, _, _, hGspec⟩ := hHspec i hiH
    let t0 : Fin d := ⟨2 * i.val, by omega⟩
    let t1 : Fin d := ⟨2 * i.val + 1, by omega⟩
    have ht0_mem : X t0 ∈ G i := by simp [G, t0]
    have ht1_mem : X t1 ∈ G i := by simp [G, t1]
    have h0 := (hGspec (X t0) ht0_mem).1
    have h1 := (hGspec (X t1) ht1_mem).1
    rw [hrank_X t0] at h0
    rw [hrank_X t1] at h1
    have hv0 : v t0 = c i - 1 := by
      have hi0 : (⟨t0.val / 2, by omega⟩ : Fin k) = i := Fin.ext (by dsimp [t0]; omega)
      have hm0 : t0.val % 2 = 0 := by dsimp [t0]; omega
      simp [v, hi0, hiJ, hm0]
    have hv1 : v t1 = c i := by
      have hi1 : (⟨t1.val / 2, by omega⟩ : Fin k) = i := Fin.ext (by dsimp [t1]; omega)
      have hm1 : t1.val % 2 ≠ 0 := by dsimp [t1]; omega
      simp [v, hi1, hiJ, hm1]
    rw [hv0] at h0
    rw [hv1] at h1
    have hspec := hcSpec i hiJ
    exact div_pred_ne_of_dvd hspec.1 hspec.2.2 (h0.trans h1.symm)
  have hle1 : H.card ≤ (Finset.univ \ J).card := Finset.card_le_card hHsub
  have hle2 : (Finset.univ \ J).card = k - J.card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  have hJle : J.card ≤ k := by
    simpa using Finset.card_le_univ J
  omega

end MainProof

end PEqualNP.Outside.L_lib_1339

theorem PEqualNP.Outside.L_lib_1339 :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
let valid := fun (d : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (d+2) C ∧
  C.output < d+2+C.size
let bits := fun (d : Nat) (x : Finset (Fin d)) =>
  List.ofFn (fun a : Fin d => decide (a ∈ x)) ++ [false,true]
let rank := fun (d : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) (x : Finset (Fin d)) =>
  let w := C.wires (bits d x)
  let gates := (List.range C.size).filter (fun j => decide
    ((C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op = .not))
  gates.foldl (fun v j => 2*v+(if w.getD (d+2+j) false then 0 else 1)) 0
∀ (k b L : Nat) (s : Fin k → Nat), 0 < k →
  let pack := ∃ J : Finset (Fin k), L < J.card ∧ ∃ c : Fin k → Nat,
    (∀ i ∈ J, 0 < c i ∧ c i < 2^b ∧ 2^(s i) ∣ c i) ∧
    ∀ i ∈ J, ∀ j ∈ J, i < j → c i < c j
  (¬ pack) ↔
    ∀ (d : Nat) (G : Fin k → Finset (Finset (Fin d))) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ i, (G i).Nonempty) → (∀ i j, i < j → ∀ x ∈ G i, ∀ y ∈ G j, x ⊆ y) →
      valid d C → PEqualNP.NotBracket.notCount C = b →
      ∃ H : Finset (Fin k), k-L ≤ H.card ∧ ∀ i ∈ H,
        ∃ (z : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) (copy : Nat → Nat),
          valid d D ∧ PEqualNP.NotBracket.notCount D ≤ s i ∧
          D.size-PEqualNP.NotBracket.notCount D ≤ C.size-b ∧
          (∀ j, j < d+2+C.size → copy j < d+2+D.size) ∧
          ∀ x ∈ G i, rank d C x / 2^(s i) = z ∧
            ∀ j, j < d+2+C.size →
              (D.wires (bits d x)).getD (copy j) false = (C.wires (bits d x)).getD j false := by
  dsimp only
  intro k b L s _
  have hbits : ∀ (d : Nat) (x : Finset (Fin d)),
      (List.ofFn (fun a : Fin d => @decide (a ∈ x) (Classical.propDecidable _)) ++ [false, true]) =
        PEqualNP.Outside.L_lib_1339.bitsDef d x := by
    intro d x
    unfold PEqualNP.Outside.L_lib_1339.bitsDef
    congr 1; congr 1; funext a
    exact decide_eq_decide.mpr Iff.rfl
  have hrank : ∀ (d : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) (x : Finset (Fin d)),
      ((List.range C.size).filter (fun j => @decide
        ((C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op = .not)
        (Classical.propDecidable _))).foldl
        (fun v j => 2 * v + (@ite Nat
          ((C.wires (List.ofFn (fun a : Fin d => @decide (a ∈ x) (Classical.propDecidable _)) ++
            [false, true])).getD (d + 2 + j) false = true)
          (Classical.propDecidable _) 0 1)) 0 =
        PEqualNP.Outside.L_lib_1339.rankDef d C x := by
    intro d C x
    rw [hbits]
    unfold PEqualNP.Outside.L_lib_1339.rankDef PEqualNP.Outside.L_lib_1339.binFold
      PEqualNP.Outside.L_lib_1339.ix
    have hfilt :
        (List.range C.size).filter (fun j => @decide
          ((C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op = .not)
          (Classical.propDecidable _)) =
        (List.range C.gates.length).filter (fun j => @decide
          ((C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op = .not)
          (Classical.propDecidable _)) := rfl
    rw [hfilt]
    congr 1
    funext v j
    congr 1
    by_cases hb : (C.wires (PEqualNP.Outside.L_lib_1339.bitsDef d x)).getD (d + 2 + j) false = true
    · rw [ite_eq_left hb, ite_eq_left hb]
    · rw [ite_eq_right hb, ite_eq_right hb]
  constructor
  · intro hnpack d G C hG hord hvalid hNot
    obtain ⟨H, hHcard, hHspec⟩ := PEqualNP.Outside.L_lib_1339.forward_dir k b L s hnpack d G C
      hG hord hvalid.1 hvalid.2.1 hNot
    refine ⟨H, hHcard, fun i hi => ?_⟩
    obtain ⟨z, D, copy, hvalD, hnotD, hsizeD, hcopyD, hGspec⟩ := hHspec i hi
    refine ⟨z, D, copy, hvalD, hnotD, hsizeD, hcopyD, fun x hx => ?_⟩
    obtain ⟨hr, hw⟩ := hGspec x hx
    refine ⟨?_, fun j hj => ?_⟩
    · rw [hrank]; exact hr
    · rw [hbits]; exact hw j hj
  · intro hall hpack
    apply PEqualNP.Outside.L_lib_1339.backward_dir k b L s hpack
    intro d G C hG hord hvalid hNot
    obtain ⟨H, hHcard, hHspec⟩ := hall d G C hG hord hvalid hNot
    refine ⟨H, hHcard, fun i hi => ?_⟩
    obtain ⟨z, D, copy, hvalD, hnotD, hsizeD, hcopyD, hGspec⟩ := hHspec i hi
    refine ⟨z, D, copy, hvalD, hnotD, hsizeD, hcopyD, fun x hx => ?_⟩
    obtain ⟨hr, hw⟩ := hGspec x hx
    refine ⟨?_, fun j hj => ?_⟩
    · rw [← hrank]; exact hr
    · rw [← hbits]; exact hw j hj
