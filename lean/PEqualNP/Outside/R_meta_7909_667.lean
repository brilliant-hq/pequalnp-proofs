import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7909_667
  (wireMono : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
    PEqualNP.MetaComplexity.Monotone2 C → ∀ (i : ℕ) (x y : Fin n → Bool),
    (∀ j, x j = true → y j = true) → (C.wires (List.ofFn x)).getD i false = true →
    (C.wires (List.ofFn y)).getD i false = true)
  (splitCost : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
    400 ≤ q → N = q^2+q+1 →
    (∀ l, Fintype.card {p // I p l} = q+1) →
    (∀ p p', p ≠ p' → ∃! l, I p l ∧ I p' l) →
    (∀ D E : Finset (Fin N), D.card ≤ q → E.card ≤ q →
       (∀ p, (∃ l ∈ D, I p l) ↔ ∃ l ∈ E, I p l) → D = E) →
    PEqualNP.TopForm.IsAO2 (N+N) C → a < b → b < N+N+C.size →
    (∀ D : Finset (Fin N), D.card ≤ q → ∃ w : ℕ, (w = a ∨ w = b) ∧
      ∀ X : Finset (Fin N),
      ((C.wires (List.ofFn (Fin.append (fun p => decide (p ∈ X)) (fun l => decide (l ∈ D))))).getD w false = true ↔
        ∃ p ∈ X, ∃ l ∈ D, I p l)) →
    (∀ p l, I p l → ∀ w : ℕ, (w = a ∨ w = b) →
      (C.wires (List.ofFn (fun j : Fin (N+N) => decide (j = Fin.castAdd N p ∨ j = Fin.natAdd N l)))).getD w false = true) →
    N*q ≤ 100*C.size) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (400 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x2 + x2 ≤ x5.output → x5.output < x2 + x2 + x5.size → (∃ (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x5.output - (x2 + x2)]? = Option.some x13 ∧ x13.op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x14 : ℕ) (x15 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x14]? = Option.some x15 → ∃ (x17 : ℕ) (x18 : ℕ), x15.inputs = [x17, x18] ∧ x17 < x18 ∧ x18 < x2 + x2 + x14) → (∀ (x15 x16 : Fin x2), x3 x15 x16 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x18 : Fin (x2 + x2)) => Decidable.decide (x18 = Fin.castAdd x2 x15 ∨ x18 = Fin.natAdd x2 x16)) = Bool.true) → (∀ (x16 : Fin (x2 + x2) → Bool), Fintype.card { x17 : Fin x2 // x16 (Fin.natAdd x2 x17) = Bool.true } ≤ x1 → (¬∃ (x18 : Fin x2) (x19 : Fin x2), x3 x18 x19 ∧ x16 (Fin.castAdd x2 x18) = Bool.true ∧ x16 (Fin.natAdd x2 x19) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x16 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  classical
  intro x1 x2 x3 x4 x5 hx1 hx2 hLine hUniq hMono houtLo houtHi hOutAnd hStrict hPos hNeg
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have run_snoc : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate) (x : List Bool),
      (gs ++ [g]).foldl step x = gs.foldl step x ++ [g.op.eval (g.inputs.map fun i => (gs.foldl step x).getD i false)] := by
    intro gs g x
    simp [step, List.foldl_append]
  have run_length : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool),
      (gs.foldl step x).length = x.length + gs.length := by
    intro gs x
    induction gs using List.reverseRecOn with
    | nil => simp
    | append_singleton gs g ih =>
      rw [run_snoc]
      simp [ih]
      omega
  have run_prefix : ∀ (gs hs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (i : ℕ),
      i < x.length + gs.length →
      ((gs ++ hs).foldl step x).getD i false = (gs.foldl step x).getD i false := by
    intro gs hs x i hi
    induction hs using List.reverseRecOn with
    | nil => simp
    | append_singleton hs g ih =>
      rw [← List.append_assoc, run_snoc]
      have hlen : ((gs ++ hs).foldl step x).length = x.length + (gs ++ hs).length := run_length (gs ++ hs) x
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hlen, List.length_append]; omega), ← List.getD_eq_getElem?_getD]
      exact ih
  have run_input : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (i : ℕ),
      i < x.length → (gs.foldl step x).getD i false = x.getD i false := by
    intro gs x i hi
    have := run_prefix [] gs x i (by simpa using hi)
    simpa using this
  have run_gate : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length),
      (gs.foldl step x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i =>
        if i < x.length + j then (gs.foldl step x).getD i false else false) := by
    intro gs x
    induction gs using List.reverseRecOn with
    | nil => intro j hj; simp at hj
    | append_singleton gs g ih =>
      intro j hj
      have hlen : (gs.foldl step x).length = x.length + gs.length := run_length gs x
      have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
          (l.map fun i => if i < x.length + k then ((gs ++ [g]).foldl step x).getD i false else false) =
          l.map fun i => if i < x.length + k then (gs.foldl step x).getD i false else false := by
        intro k hk l
        refine List.map_congr_left fun i _ => ?_
        split_ifs with h
        · exact run_prefix gs [g] x i (by omega)
        · rfl
      rcases Nat.lt_or_ge j gs.length with h | h
      · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
        exact ih j h
      · have hjj : j = gs.length := by simp at hj; omega
        subst hjj
        have hg : (gs ++ [g])[gs.length] = g := by simp
        rw [hg, same _ le_rfl, run_snoc, ← hlen]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        split_ifs with h
        · rfl
        · exact List.getD_eq_default _ _ (by omega)
  have hAO : PEqualNP.TopForm.IsAO2 (x2 + x2) x5 := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using (hMono g hg).1
    · intro j hj i hi
      have hge : PEqualNP.MetaComplexity.NestedCover.gateAt x5 j = x5.gates[j] :=
        List.getD_eq_getElem _ _ hj
      rw [hge] at hi
      obtain ⟨a, b, hab, hlt, hblt⟩ := hStrict j x5.gates[j] (List.getElem?_eq_getElem hj)
      rw [hab] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    · intro g hg
      obtain ⟨j, hj, hgj⟩ := List.getElem_of_mem hg
      obtain ⟨a, b, hab, _, _⟩ := hStrict j g (by rw [← hgj]; exact List.getElem?_eq_getElem hj)
      rw [hab]
      rfl
  let j : ℕ := x5.output - (x2 + x2)
  have hj : j < x5.gates.length := by
    change x5.output - (x2 + x2) < x5.size
    omega
  have houtEq : x5.output = x2 + x2 + j := by omega
  rcases hOutAnd with ⟨g, hgSome, hgAnd⟩
  have hgEq : x5.gates[j] = g := by
    have h1 : x5.gates[j]? = Option.some x5.gates[j] := List.getElem?_eq_getElem hj
    rw [h1] at hgSome
    exact Option.some.inj hgSome
  obtain ⟨a, b, hab, habLt, hbLt⟩ := hStrict j g hgSome
  have heval_and : ∀ (x : Fin (x2 + x2) → Bool),
      PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x =
      ((x5.wires (List.ofFn x)).getD a false && (x5.wires (List.ofFn x)).getD b false) := by
    intro x
    change (x5.gates.foldl step (List.ofFn x)).getD x5.output false = _
    rw [houtEq]
    have hrg := run_gate x5.gates (List.ofFn x) j hj
    rw [List.length_ofFn] at hrg
    rw [hrg, hgEq, hgAnd, hab]
    have haLt' : a < x2 + x2 + j := by omega
    simp only [List.map_cons, List.map_nil, haLt', hbLt, ite_true]
    change ([(x5.gates.foldl step (List.ofFn x)).getD a false,
      (x5.gates.foldl step (List.ofFn x)).getD b false].all id) = _
    simp only [List.all_cons, List.all_nil, id_eq, Bool.and_true]
    rfl
  have other_line_intersections {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
      (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l)
      {l k : Fin N} (hne : l ≠ k) :
      ((Finset.univ : Finset (Fin N)).filter (fun p => I p l ∧ I p k)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp p' hp'
    by_contra hn
    obtain ⟨w, _, hw⟩ := huniq p p' hn
    have a := (Finset.mem_filter.mp hp).2
    have b := (Finset.mem_filter.mp hp').2
    exact hne ((hw l ⟨a.1,b.1⟩).trans (hw k ⟨a.2,b.2⟩).symm)
  have uncovered_on_line {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
      (hdeg : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1)
      (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l)
      (D : Finset (Fin N)) (hD : D.card ≤ q) (l : Fin N) (hl : l ∉ D) :
      ∃ p : Fin N, I p l ∧ ∀ k ∈ D, ¬ I p k := by
    classical
    let L : Finset (Fin N) := Finset.univ.filter (fun p => I p l)
    let cap (k : Fin N) := (Finset.univ : Finset (Fin N)).filter (fun p => I p l ∧ I p k)
    have size : L.card = q+1 := by
      simpa [L, Fintype.card_subtype] using hdeg l
    have small : (D.biUnion cap).card ≤ q := calc
      _ ≤ ∑ k ∈ D, (cap k).card := Finset.card_biUnion_le
      _ ≤ ∑ k ∈ D, 1 := Finset.sum_le_sum (fun k hk => other_line_intersections I huniq (fun h => hl (h ▸ hk)))
      _ ≤ q := by simpa using hD
    have outside : ¬ L ⊆ D.biUnion cap := by
      intro sub
      have := Finset.card_le_card sub
      omega
    obtain ⟨p, hp, hnot⟩ := Finset.not_subset.mp outside
    have pin : I p l := (Finset.mem_filter.mp hp).2
    refine ⟨p, pin, ?_⟩
    intro k hk hI
    apply hnot
    exact Finset.mem_biUnion.mpr ⟨k,hk,Finset.mem_filter.mpr ⟨Finset.mem_univ _,pin,hI⟩⟩
  have recover_sparse_lines {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
      (hdeg : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1)
      (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l)
      (D E : Finset (Fin N)) (hD : D.card ≤ q) (hE : E.card ≤ q)
      (same : ∀ p, (∃ l ∈ D, I p l) ↔ (∃ l ∈ E, I p l)) : D = E := by
    have sub (X Y : Finset (Fin N)) (small : Y.card ≤ q)
        (incl : ∀ p, (∃ l ∈ X, I p l) → (∃ l ∈ Y, I p l)) : X ⊆ Y := by
      intro l hl
      by_contra miss
      obtain ⟨p, hp, hrest⟩ := uncovered_on_line I hdeg huniq Y small l miss
      obtain ⟨k,hk,he⟩ := incl p ⟨l,hl,hp⟩
      exact hrest k hk he
    exact Finset.Subset.antisymm (sub D E hE (fun p => (same p).mp))
      (sub E D hD (fun p => (same p).mpr))
  apply splitCost x1 x2 x3 x5 a b hx1 hx2 hLine hUniq (recover_sparse_lines x3 hLine hUniq) hAO habLt (by omega)
  · intro D hD
    let z (X : Finset (Fin x2)) := Fin.append (fun p => decide (p ∈ X)) (fun l => decide (l ∈ D))
    let Z := (Finset.univ : Finset (Fin x2)).filter (fun p => ∀ l ∈ D, ¬ x3 p l)
    have count : Fintype.card {l : Fin x2 // z Z (Fin.natAdd x2 l) = true} ≤ x1 := by
      simpa only [z, Fin.append_right, decide_eq_true_eq, Fintype.card_coe] using hD
    have zero := hNeg (z Z) count (by
      rintro ⟨p,l,hI,hp,hl⟩
      simp only [z, Fin.append_left, decide_eq_true_eq, Z, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [z, Fin.append_right, decide_eq_true_eq] at hl
      exact hp l hl hI)
    rw [heval_and, Bool.and_eq_false_iff] at zero
    have core (w : ℕ) (hw : w = a ∨ w = b)
        (hz : (x5.wires (List.ofFn (z Z))).getD w false = false) :
        ∀ X : Finset (Fin x2), (x5.wires (List.ofFn (z X))).getD w false = true ↔
          ∃ p ∈ X, ∃ l ∈ D, x3 p l := by
      intro X
      constructor
      · intro high
        by_contra neg
        have sub : X ⊆ Z := by
          intro p hp
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, fun l hl hi => neg ⟨p,hp,l,hl,hi⟩⟩
        have up := wireMono _ x5 hMono w (z X) (z Z) (by
          intro j
          refine Fin.addCases (motive := fun j => z X j = true → z Z j = true) ?_ ?_ j
          · intro p; simpa [z] using (fun (h : p ∈ X) => sub h)
          · intro l; simp only [z, Fin.append_right, imp_self]) high
        rw [hz] at up
        contradiction
      · rintro ⟨p,hp,l,hl,hit⟩
        have yes := hPos p l hit
        rw [heval_and, Bool.and_eq_true_iff] at yes
        apply wireMono _ x5 hMono w _ (z X) _ (show (x5.wires (List.ofFn (fun j : Fin (x2+x2) => decide (j = Fin.castAdd x2 p ∨ j = Fin.natAdd x2 l)))).getD w false = true from by
          rcases hw with rfl | rfl
          · exact yes.1
          · exact yes.2)
        intro j hj
        rcases of_decide_eq_true hj with rfl | rfl
        · simp [z,hp]
        · simp only [z, Fin.append_right, decide_eq_true_eq]; exact hl
    rcases zero with ha | hb
    · exact ⟨a,Or.inl rfl,core a (Or.inl rfl) ha⟩
    · exact ⟨b,Or.inr rfl,core b (Or.inr rfl) hb⟩
  · intro p l hit w hw
    have yes := hPos p l hit
    rw [heval_and, Bool.and_eq_true_iff] at yes
    rcases hw with rfl | rfl
    · exact yes.1
    · exact yes.2
