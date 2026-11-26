import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20605

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def gateStep (xs : List Bool) (g : Gate) :=
  xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]

def Agree (T : Finset ℕ) (x y : List Bool) : Prop :=
  ∀ i ∈ T, x.getD i false = true → y.getD i false = true

private lemma unchanged (xs : List Bool) (b : Bool) (i : ℕ) (h : i ≠ xs.length) :
    (xs ++ [b]).getD i false = xs.getD i false := by
  by_cases hi : i < xs.length
  · exact List.getD_append _ _ _ _ hi
  · have ha : (xs ++ [b]).length ≤ i := by simp; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none ha,
      List.getElem?_eq_none (show xs.length ≤ i by omega)]

private lemma atNew (xs : List Bool) (g : Gate) :
    (gateStep xs g).getD xs.length false = g.op.eval (g.inputs.map fun i => xs.getD i false) := by
  simp [gateStep,List.getD_eq_getElem?_getD]

private lemma gateImpl (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (h : Agree g.inputs.toFinset x y) :
    g.op.eval (g.inputs.map fun i => x.getD i false) = true →
    g.op.eval (g.inputs.map fun i => y.getD i false) = true := by
  rcases hg with ha | ho
  · simp only [ha, GateOp.eval,List.all_eq_true,List.mem_map,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂,id_eq]
    intro hx i hi
    exact h i (List.mem_toFinset.mpr hi) (hx i hi)
  · simp only [ho, GateOp.eval,List.any_eq_true,List.mem_map,exists_exists_and_eq_and,id_eq]
    rintro ⟨i,hi,hx⟩
    exact ⟨i,hi,h i (List.mem_toFinset.mpr hi) hx⟩

theorem support (gs : List Gate)
    (mono : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (N : ℕ) (goal : Finset ℕ) :
    ∃ S : Finset ℕ, S.card ≤ goal.card + gs.length ∧
      ∀ x y : List Bool, x.length = N → y.length = N → Agree S x y →
        Agree goal (gs.foldl gateStep x) (gs.foldl gateStep y) := by
  induction gs generalizing N with
  | nil => exact ⟨goal,by simp,fun _ _ _ _ h => h⟩
  | cons g gs ih =>
    have hg := mono g (by simp)
    obtain ⟨T,ct,ht⟩ := ih (fun z hz => mono z (List.mem_cons_of_mem _ hz)) (N+1)
    let S := if N ∈ T then T.erase N ∪ g.inputs.toFinset else T
    refine ⟨S,?_,?_⟩
    · by_cases hn : N ∈ T
      · have a := Finset.card_union_le (T.erase N) g.inputs.toFinset
        have b := Finset.card_erase_add_one hn
        have d := List.toFinset_card_le g.inputs
        simp only [S,ite_eq_left hn,List.length_cons]
        omega
      · simp only [S,ite_eq_right hn,List.length_cons]; omega
    · intro x y hx hy h
      apply ht _ _ (by simp [gateStep,hx]) (by simp [gateStep,hy])
      intro i hi
      by_cases e : i = N
      · subst i
        have hinputs : Agree g.inputs.toFinset x y := by
          intro j hj
          exact h j (by simp only [S,ite_eq_left hi,Finset.mem_union]; exact Or.inr hj)
        rw [←hx,atNew,hx,←hy,atNew]
        exact gateImpl g hg.1 x y hinputs
      · have hs : i ∈ S := by
          by_cases hn : N ∈ T
          · simp only [S,ite_eq_left hn,Finset.mem_union,Finset.mem_erase]
            exact Or.inl ⟨e,hi⟩
          · simpa [S,hn] using hi
        unfold gateStep
        rw [unchanged _ _ _ (by rwa [hx]),unchanged _ _ _ (by rwa [hy])]
        exact h i hs

def graph (u v : Fin 5) := (15139840 : ℕ).testBit (5*u.val+v.val)
def must : Finset ℕ := {2,3,4,5,6,7,8}

theorem witnesses : ∀ i : Fin 10, i.val ∈ must → ∃ a b c d : Fin 5,
    graph a b = true ∧ graph c d = false ∧ ∀ j : Fin 10, j.val ≠ i.val →
      (oneEach a b).getD j.val false = true → (oneEach c d).getD j.val false = true := by
  decide +kernel

theorem lower : ¬ RepSizeAtMost graph 5 := by
  rintro ⟨C,mono,sz,rep⟩
  obtain ⟨S,card,hs⟩ := support C.gates (fun g hg => by
    simpa [Set.mem_insert_iff,Set.mem_singleton_iff] using mono g hg) 10 {C.output}
  have subset : must ⊆ S := by
    intro i hi
    by_contra missing
    have ilt : i < 10 := by simp [must] at hi; omega
    obtain ⟨a,b,c,d,hpos,hneg,horder⟩ := witnesses ⟨i,ilt⟩ hi
    have ord : Agree S (oneEach a b) (oneEach c d) := by
      intro j hj
      by_cases jlt : j < 10
      · apply horder ⟨j,jlt⟩
        intro e
        change j = i at e
        exact missing (e ▸ hj)
      · have hle : (oneEach a b).length ≤ j := by simp [oneEach]; omega
        simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none hle]
    have ev := hs _ _ (by simp [oneEach]) (by simp [oneEach]) ord C.output (by simp)
    change C.eval (oneEach a b) = true → C.eval (oneEach c d) = true at ev
    rw [rep,rep,hpos,hneg] at ev
    simp at ev
  have ct := Finset.card_le_card subset
  have cm : must.card = 7 := by decide +kernel
  simp only [Finset.card_singleton] at card
  change C.gates.length ≤ 5 at sz
  omega

def circuit : Circuit := ⟨[⟨.and,[2,5]⟩,⟨.or,[3,4]⟩,⟨.or,[6,7]⟩,⟨.or,[12,8]⟩,
  ⟨.and,[11,13]⟩,⟨.or,[10,14]⟩],15⟩

theorem upper : RepSizeAtMost graph 6 := by
  refine ⟨circuit,?_,by decide +kernel,by decide +kernel⟩
  intro g hg
  simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp

end PEqualNP.Outside.L_meta_20605

theorem PEqualNP.Outside.L_meta_20605 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (15139840 : ℕ).testBit (5 * u.val + v.val)) 6 ∧ ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (15139840 : ℕ).testBit (5 * u.val + v.val)) 5) := by
  exact ⟨PEqualNP.Outside.L_meta_20605.upper,PEqualNP.Outside.L_meta_20605.lower⟩
