import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20604

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def coneWires (gs : List Gate) (x : List Bool) : List Bool :=
  (⟨gs, 0⟩ : Circuit).wires x

private theorem read_snoc (x : List Bool) (b : Bool) (i : ℕ) :
    (x ++ [b]).getD i false = if i = x.length then b else x.getD i false := by
  split_ifs with h
  · subst i
    simp
  · rcases Nat.lt_or_gt_of_ne h with lt | gt
    · exact List.getD_append _ _ _ _ lt
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private theorem coneSupportList (gs : List Gate)
    (fanIn : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ n o : ℕ, ∃ S : Finset ℕ, S.card ≤ gs.length + 1 ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
        (∀ i ∈ S, x.getD i false = y.getD i false) →
        (coneWires gs x).getD o false = (coneWires gs y).getD o false := by
  induction gs with
  | nil =>
    intro n o
    refine ⟨{o}, by simp, ?_⟩
    intro x y _ _ agree
    exact agree o (Finset.mem_singleton_self o)
  | cons g rest ih =>
    intro n o
    obtain ⟨S, cardS, tail⟩ :=
      ih (fun a ha => fanIn a (List.mem_cons_of_mem _ ha)) (n + 1) o
    by_cases used : n ∈ S
    · refine ⟨S.erase n ∪ g.inputs.toFinset, ?_, ?_⟩
      · have erased := Finset.card_erase_of_mem used
        have nonempty : 0 < S.card := Finset.card_pos.2 ⟨n, used⟩
        have arity := (List.toFinset_card_le (l := g.inputs)).trans (fanIn g (by simp))
        have union := Finset.card_union_le (S.erase n) g.inputs.toFinset
        simp only [List.length_cons]
        omega
      · intro x y hx hy agree
        have gateEq : g.op.eval (g.inputs.map fun i => x.getD i false) =
            g.op.eval (g.inputs.map fun i => y.getD i false) := by
          apply congrArg g.op.eval
          apply List.map_congr_left
          intro i hi
          exact agree i (Finset.mem_union_right _ (by simpa using hi))
        change (coneWires rest (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])).getD o false =
          (coneWires rest (y ++ [g.op.eval (g.inputs.map fun i => y.getD i false)])).getD o false
        apply tail _ _ (by simp [hx]) (by simp [hy])
        intro i hi
        rw [read_snoc, read_snoc, hx, hy]
        by_cases atGate : i = n
        · simpa [atGate] using gateEq
        · simpa [atGate] using agree i (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨atGate, hi⟩))
    · refine ⟨S, ?_, ?_⟩
      · simp only [List.length_cons]
        omega
      · intro x y hx hy agree
        change (coneWires rest (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])).getD o false =
          (coneWires rest (y ++ [g.op.eval (g.inputs.map fun i => y.getD i false)])).getD o false
        apply tail _ _ (by simp [hx]) (by simp [hy])
        intro i hi
        have atGate : i ≠ n := fun e => used (e ▸ hi)
        rw [read_snoc, read_snoc, hx, hy]
        simpa [atGate] using agree i hi

private theorem coneSupport (C : Circuit) (h : Monotone2 C) (n : ℕ) :
    ∃ S : Finset ℕ, S.card ≤ C.size + 1 ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
        (∀ i ∈ S, x.getD i false = y.getD i false) → C.eval x = C.eval y := by
  exact coneSupportList C.gates (fun g hg => (h g hg).2) n C.output

private def graph (u v : Fin 5) : Bool :=
  (14713856 : ℕ).testBit (5 * u.val + v.val)

private def assignment (P : Finset ℕ) : List Bool :=
  List.ofFn fun i : Fin 10 => decide (i.val ∈ P)

private theorem read_assignment (P : Finset ℕ) (i : ℕ) :
    (assignment P).getD i false = decide (i < 10 ∧ i ∈ P) := by
  unfold assignment
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases hi : i < 10 <;> simp [hi]

private theorem one_each_eq : ∀ u v : Fin 5,
    oneEach u v = assignment {u.val, 5 + v.val} := by decide

private theorem gate_mono (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (x y : ℕ → Bool) (h : ∀ i, x i = true → y i = true)
    (he : g.op.eval (g.inputs.map x) = true) : g.op.eval (g.inputs.map y) = true := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop <;> rw [hop] at he ⊢
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id] at he ⊢
    exact fun i hi => h i (he i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at he ⊢
    obtain ⟨i, hi, hv⟩ := he
    exact ⟨i, hi, h i hv⟩

private theorem wires_mono (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    ∀ x y : List Bool, x.length = y.length →
      (∀ i, x.getD i false = true → y.getD i false = true) →
      ∀ o, (Circuit.wires ⟨gs, o⟩ x).getD o false = true →
        (Circuit.wires ⟨gs, o⟩ y).getD o false = true := by
  induction gs with
  | nil => exact fun _ _ _ h o => h o
  | cons g gs ih =>
    intro x y hlen h o
    simp only [Circuit.wires, List.foldl_cons]
    apply ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) _ _ (by simp [hlen]) _ o
    intro i
    rw [read_snoc, read_snoc, ← hlen]
    by_cases hi : i = x.length
    · simpa only [hi, ite_true] using
        gate_mono g (hg g (by simp)) (fun j => x.getD j false) (fun j => y.getD j false) h
    · simpa only [hi, ite_false] using h i

private theorem assignment_mono (C : Circuit) (hm : Monotone2 C)
    {P Q : Finset ℕ} (h : P ⊆ Q) :
    C.eval (assignment P) = true → C.eval (assignment Q) = true := by
  rcases C with ⟨gs, o⟩
  unfold Circuit.eval
  apply wires_mono gs (fun g hg => (hm g hg).1) _ _ (by simp [assignment]) _ o
  intro i
  simp only [read_assignment, decide_eq_true_eq]
  exact fun hi => ⟨hi.1, h hi.2⟩

private def requiredWires : Finset ℕ := {2, 3, 4, 5, 6, 7, 8}

private theorem distinguish (i : ℕ) (hi : i ∈ requiredWires) :
    ∃ u v u' v' : Fin 5, graph u v = true ∧ graph u' v' = false ∧
    ({u.val, 5 + v.val} : Finset ℕ).erase i ⊆ {u'.val, 5 + v'.val} := by
  simp only [requiredWires, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, 0, 0, 0, by decide, by decide, by decide⟩
  · exact ⟨3, 0, 0, 0, by decide, by decide, by decide⟩
  · exact ⟨4, 1, 0, 1, by decide, by decide, by decide⟩
  · exact ⟨2, 0, 2, 1, by decide, by decide, by decide⟩
  · exact ⟨4, 1, 4, 0, by decide, by decide, by decide⟩
  · exact ⟨4, 2, 4, 0, by decide, by decide, by decide⟩
  · exact ⟨4, 3, 4, 0, by decide, by decide, by decide⟩

private theorem support_at_least_seven (C : Circuit) (hm : Monotone2 C) (hr : Represents graph C)
    (S : Finset ℕ) (hs : ∀ x y : List Bool, x.length = 10 → y.length = 10 →
      (∀ i ∈ S, x.getD i false = y.getD i false) → C.eval x = C.eval y) :
    7 ≤ S.card := by
  have hincl : requiredWires ⊆ S := by
    intro i hi
    by_contra hn
    obtain ⟨u, v, u', v', hp, hq, hsub⟩ := distinguish i hi
    let P : Finset ℕ := {u.val, 5 + v.val}
    let Q : Finset ℕ := {u'.val, 5 + v'.val}
    have hP : C.eval (assignment P) = true := by
      simpa only [P, one_each_eq, hp] using hr u v
    have hQ : C.eval (assignment Q) = false := by
      simpa only [Q, one_each_eq, hq] using hr u' v'
    have heq := hs (assignment P) (assignment (P.erase i))
      (by simp [assignment]) (by simp [assignment])
    have he : ∀ j ∈ S,
        (assignment P).getD j false = (assignment (P.erase i)).getD j false := by
      intro j hj
      have hne : j ≠ i := fun e => hn (e ▸ hj)
      rw [read_assignment, read_assignment, decide_eq_decide]
      exact ⟨fun h => ⟨h.1, Finset.mem_erase.mpr ⟨hne, h.2⟩⟩,
        fun h => ⟨h.1, Finset.mem_of_mem_erase h.2⟩⟩
    rw [heq he] at hP
    exact Bool.false_ne_true (hQ.symm.trans (assignment_mono C hm hsub hP))
  have hcard : requiredWires.card = 7 := by decide
  simpa only [hcard] using Finset.card_le_card hincl

private theorem upperBound : RepSizeAtMost graph 6 := by
  refine ⟨⟨[⟨.or, [2, 3]⟩, ⟨.and, [10, 5]⟩, ⟨.or, [6, 7]⟩,
    ⟨.or, [12, 8]⟩, ⟨.and, [4, 13]⟩, ⟨.or, [11, 14]⟩], 15⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel

private theorem lowerBound : ¬ RepSizeAtMost graph 5 := by
  rintro ⟨C, monotone, sizeBound, represents⟩
  obtain ⟨support, cardBound, agrees⟩ := coneSupport C monotone 10
  have seven := support_at_least_seven C monotone represents support agrees
  omega

end PEqualNP.Outside.L_meta_20604

open PEqualNP.Outside.L_meta_20604 in
theorem PEqualNP.Outside.L_meta_20604 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (14713856 : ℕ).testBit (5 * u.val + v.val)) 6 ∧ ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (14713856 : ℕ).testBit (5 * u.val + v.val)) 5) := by
  exact ⟨upperBound, lowerBound⟩
