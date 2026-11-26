import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20589

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def A : Fin 5 → Fin 5 → Bool :=
  fun u v => (7569408 : ℕ).testBit (5 * u.val + v.val)

def witness : Circuit :=
  ⟨[⟨.or, [3, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [11, 7]⟩, ⟨.and, [10, 12]⟩], 13⟩

theorem witness_mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

theorem upper : RepSizeAtMost A 4 :=
  ⟨witness, witness_mono, by decide, by decide +kernel⟩

def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wiresOf (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl wireStep x

theorem wiresOf_append (gs : List Gate) (g : Gate) (x : List Bool) :
    wiresOf (gs ++ [g]) x = wireStep (wiresOf gs x) g := by
  simp [wiresOf, List.foldl_append]

theorem wiresOf_length (gs : List Gate) (x : List Bool) :
    (wiresOf gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wiresOf]
  | append_singleton gs g ih =>
    rw [wiresOf_append, wireStep, List.length_append, List.length_singleton, ih, List.length_append,
      List.length_singleton, Nat.add_assoc]

theorem getD_append_lt {α : Type} (l₁ l₂ : List α) (i : ℕ) (d : α) (h : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq {α : Type} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_out {α : Type} (l : List α) (i : ℕ) (d : α) (h : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem gate_mono (g : Gate) (hg : g.op = .and ∨ g.op = .or) (w₁ w₂ : List Bool)
    (hle : ∀ i, w₁.getD i false = true → w₂.getD i false = true) :
    g.op.eval (g.inputs.map fun i => w₁.getD i false) = true →
    g.op.eval (g.inputs.map fun i => w₂.getD i false) = true := by
  rcases hg with hop | hop <;> rw [hop]
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro h b hb
    rcases hb with ⟨i, hi, rfl⟩
    exact hle i (h _ ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨_, ⟨i, hi, rfl⟩, htrue⟩
    exact ⟨w₂.getD i false, ⟨i, hi, rfl⟩, hle i htrue⟩

theorem wiresOf_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (x y : List Bool) (hlen : x.length = y.length)
    (hle : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ w, (wiresOf gs x).getD w false = true → (wiresOf gs y).getD w false = true := by
  induction gs using List.reverseRecOn with
  | nil => exact hle
  | append_singleton gs g ih =>
    have hgs' : ∀ g' ∈ gs, g'.op = .and ∨ g'.op = .or :=
      fun g' hg' => hgs g' (List.mem_append_left _ hg')
    have hg : g.op = .and ∨ g.op = .or := hgs g (List.mem_append_right _ List.mem_cons_self)
    have hprev := ih hgs'
    have lx : (wiresOf gs x).length = x.length + gs.length := wiresOf_length gs x
    have ly : (wiresOf gs y).length = x.length + gs.length := by rw [wiresOf_length, ← hlen]
    intro w hw
    rw [wiresOf_append, wireStep] at hw ⊢
    by_cases hlt : w < x.length + gs.length
    · rw [getD_append_lt _ _ _ _ (by omega)] at hw ⊢
      exact hprev w hw
    · by_cases heq : w = x.length + gs.length
      · subst heq
        rw [← lx, getD_snoc_eq] at hw
        rw [← ly, getD_snoc_eq]
        exact gate_mono g hg (wiresOf gs x) (wiresOf gs y) hprev hw
      · rw [getD_out _ _ _ (by simp [lx]; omega)] at hw
        exact Bool.noConfusion hw

def coneStep (cs : List (Finset ℕ)) (g : Gate) : List (Finset ℕ) :=
  cs ++ [insert cs.length (g.inputs.foldl (fun s i => s ∪ cs.getD i ∅) ∅)]

def cones (gs : List Gate) : List (Finset ℕ) :=
  gs.foldl coneStep ((List.range 10).map fun i => {i})

theorem cones_append (gs : List Gate) (g : Gate) :
    cones (gs ++ [g]) = coneStep (cones gs) g := by
  simp [cones, List.foldl_append]

theorem cones_length (gs : List Gate) : (cones gs).length = 10 + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [cones]
  | append_singleton gs g ih =>
    rw [cones_append, coneStep, List.length_append, List.length_singleton, ih, List.length_append,
      List.length_singleton, Nat.add_assoc]

theorem foldl_union_subset {α : Type} [DecidableEq α] (f : ℕ → Finset α) (l : List ℕ) (acc : Finset α) :
    acc ⊆ l.foldl (fun s i => s ∪ f i) acc := by
  induction l generalizing acc with
  | nil => exact Finset.Subset.rfl
  | cons a l ih =>
    simp only [List.foldl_cons]
    exact Finset.subset_union_left.trans (ih (acc ∪ f a))

theorem mem_foldl_union {α : Type} [DecidableEq α] (f : ℕ → Finset α) (l : List ℕ) (acc : Finset α)
    (i : ℕ) (hi : i ∈ l) : f i ⊆ l.foldl (fun s j => s ∪ f j) acc := by
  induction l generalizing acc with
  | nil => simp at hi
  | cons a l ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hi with rfl | hi
    · exact Finset.subset_union_right.trans (foldl_union_subset f l (acc ∪ f i))
    · exact ih (acc ∪ f a) hi

theorem foldl_union_mem_iff {α : Type} [DecidableEq α] (f : ℕ → Finset α) (l : List ℕ) (acc : Finset α) (v : α) :
    v ∈ l.foldl (fun s j => s ∪ f j) acc ↔ v ∈ acc ∨ ∃ j ∈ l, v ∈ f j := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, ih, Finset.mem_union, List.mem_cons]
    constructor
    · rintro ((h | h) | ⟨j, hj, hv⟩)
      · exact Or.inl h
      · exact Or.inr ⟨a, Or.inl rfl, h⟩
      · exact Or.inr ⟨j, Or.inr hj, hv⟩
    · rintro (h | ⟨j, rfl | hj, hv⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr hv)
      · exact Or.inr ⟨j, hj, hv⟩

theorem cones_mem_lt (gs : List Gate) (w v : ℕ) (hv : v ∈ (cones gs).getD w ∅) :
    v < 10 + gs.length := by
  induction gs using List.reverseRecOn generalizing w with
  | nil =>
    by_cases hw : w < 10
    · have hget : (cones []).getD w ∅ = {w} := by
        simp [cones, List.getD_eq_getElem?_getD, hw]
      rw [hget, Finset.mem_singleton] at hv
      omega
    · rw [getD_out _ _ _ (by simp [cones]; omega)] at hv
      simp at hv
  | append_singleton gs g ih =>
    have lc : (cones gs).length = 10 + gs.length := cones_length gs
    rw [cones_append, coneStep] at hv
    by_cases hw : w < 10 + gs.length
    · rw [getD_append_lt _ _ _ _ (by omega)] at hv
      have := ih w hv
      simp; omega
    · by_cases heq : w = 10 + gs.length
      · subst heq
        rw [← lc, getD_snoc_eq, Finset.mem_insert, foldl_union_mem_iff] at hv
        rcases hv with rfl | hv | ⟨j, _, hj⟩
        · simp [lc]
        · simp at hv
        · have := ih j hj
          simp; omega
      · rw [getD_out _ _ _ (by simp [lc]; omega)] at hv
        simp at hv

theorem cones_self (gs : List Gate) (w : ℕ) (hw : w < 10 + gs.length) :
    w ∈ (cones gs).getD w ∅ := by
  induction gs using List.reverseRecOn with
  | nil =>
    have hget : (cones []).getD w ∅ = {w} := by
      simp [cones, List.getD_eq_getElem?_getD, show w < 10 by simpa using hw]
    rw [hget]
    exact Finset.mem_singleton_self w
  | append_singleton gs g ih =>
    have lc : (cones gs).length = 10 + gs.length := cones_length gs
    rw [cones_append, coneStep]
    by_cases hlt : w < 10 + gs.length
    · rw [getD_append_lt _ _ _ _ (by omega)]
      exact ih hlt
    · have heq : w = 10 + gs.length := by simp at hw; omega
      subst heq
      rw [← lc, getD_snoc_eq]
      exact Finset.mem_insert_self _ _

def reads (gs : List Gate) (S : Finset ℕ) : Finset ℕ :=
  (S.filter fun u => 10 ≤ u ∧ u < 10 + gs.length).biUnion fun u =>
    (gs.getD (u - 10) ⟨.and, []⟩).inputs.toFinset

theorem reads_mono (gs : List Gate) {S₁ S₂ : Finset ℕ} (h : S₁ ⊆ S₂) :
    reads gs S₁ ⊆ reads gs S₂ := by
  intro v hv
  simp only [reads, Finset.mem_biUnion, Finset.mem_filter] at hv ⊢
  rcases hv with ⟨u, ⟨huS, huB⟩, hvu⟩
  exact ⟨u, ⟨h huS, huB⟩, hvu⟩

theorem reads_append_le (gs : List Gate) (g : Gate) (S : Finset ℕ) :
    reads gs S ⊆ reads (gs ++ [g]) S := by
  intro v hv
  simp only [reads, Finset.mem_biUnion, Finset.mem_filter] at hv ⊢
  rcases hv with ⟨u, ⟨huS, h10, hlt⟩, hvu⟩
  refine ⟨u, ⟨huS, h10, by simp; omega⟩, ?_⟩
  rwa [getD_append_lt _ _ _ _ (by omega)]

theorem cones_subset_reads (gs : List Gate) (w : ℕ) :
    ((cones gs).getD w ∅).erase w ⊆ reads gs ((cones gs).getD w ∅) := by
  induction gs using List.reverseRecOn generalizing w with
  | nil =>
    intro v hv
    rw [Finset.mem_erase] at hv
    by_cases hw : w < 10
    · have hget : (cones []).getD w ∅ = {w} := by
        simp [cones, List.getD_eq_getElem?_getD, hw]
      rw [hget, Finset.mem_singleton] at hv
      exact (hv.1 hv.2).elim
    · rw [getD_out _ _ _ (by simp [cones]; omega)] at hv
      simp at hv
  | append_singleton gs g ih =>
    have lc : (cones gs).length = 10 + gs.length := cones_length gs
    intro v hv
    rw [Finset.mem_erase] at hv
    rw [cones_append, coneStep] at hv ⊢
    by_cases hw : w < 10 + gs.length
    · rw [getD_append_lt _ _ _ _ (by omega)] at hv ⊢
      exact reads_append_le gs g _ (ih w (Finset.mem_erase.mpr hv))
    · by_cases heq : w = 10 + gs.length
      · subst heq
        rw [← lc, getD_snoc_eq] at hv ⊢
        set base := g.inputs.foldl (fun s i => s ∪ (cones gs).getD i ∅) ∅ with hbase
        set S := insert (cones gs).length base with hS
        have hv' : v ∈ base := (Finset.mem_insert.mp hv.2).resolve_left hv.1
        rw [hbase, foldl_union_mem_iff] at hv'
        rcases hv' with hv' | ⟨j, hj, hvj⟩
        · simp at hv'
        · by_cases hvj_eq : v = j
          · subst hvj_eq
            simp only [reads, Finset.mem_biUnion, Finset.mem_filter]
            refine ⟨(cones gs).length, ⟨Finset.mem_insert_self _ _, by omega, by simp [lc]⟩, ?_⟩
            have hsub : (cones gs).length - 10 = gs.length := by omega
            rw [hsub, getD_snoc_eq]
            exact List.mem_toFinset.mpr hj
          · have hsubS : (cones gs).getD j ∅ ⊆ S :=
              (mem_foldl_union (fun i => (cones gs).getD i ∅) g.inputs ∅ j hj).trans
                (Finset.subset_insert _ _)
            exact reads_mono (gs ++ [g]) hsubS (reads_append_le gs g _
              (ih j (Finset.mem_erase.mpr ⟨hvj_eq, hvj⟩)))
      · rw [getD_out _ _ _ (by simp [lc]; omega)] at hv
        simp at hv

theorem wiresOf_eq_of_agree (gs : List Gate) (x y : List Bool)
    (hx : x.length = 10) (hy : y.length = 10) :
    ∀ w, (∀ i ∈ (cones gs).getD w ∅, i < 10 → x.getD i false = y.getD i false) →
      (wiresOf gs x).getD w false = (wiresOf gs y).getD w false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro w hag
    by_cases hw : w < 10
    · have hmem : w ∈ (cones []).getD w ∅ := cones_self [] w (by simpa using hw)
      exact hag w hmem hw
    · simp only [wiresOf, List.foldl_nil]
      rw [getD_out x w false (by omega), getD_out y w false (by omega)]
  | append_singleton gs g ih =>
    have lc : (cones gs).length = 10 + gs.length := cones_length gs
    have lx : (wiresOf gs x).length = 10 + gs.length := by rw [wiresOf_length, hx]
    have ly : (wiresOf gs y).length = 10 + gs.length := by rw [wiresOf_length, hy]
    intro w hag
    rw [cones_append, coneStep] at hag
    rw [wiresOf_append, wireStep, wiresOf_append, wireStep]
    by_cases hw : w < 10 + gs.length
    · rw [getD_append_lt _ _ _ _ (by omega)] at hag
      rw [getD_append_lt _ _ _ _ (by omega), getD_append_lt _ _ _ _ (by omega)]
      exact ih w hag
    · by_cases heq : w = 10 + gs.length
      · subst heq
        have hxy : (wiresOf gs x).length = (wiresOf gs y).length := by omega
        rw [← lc, getD_snoc_eq] at hag
        rw [← lx, getD_snoc_eq, hxy, getD_snoc_eq]
        congr 1
        apply List.map_congr_left
        intro j hj
        apply ih j
        intro i hi hi10
        exact hag i (Finset.mem_insert_of_mem
          (mem_foldl_union (fun u => (cones gs).getD u ∅) g.inputs ∅ j hj hi)) hi10
      · rw [getD_out _ _ _ (by simp [lx]; omega), getD_out _ _ _ (by simp [ly]; omega)]

theorem cones_lt_ten (gs : List Gate) (w : ℕ) (hw : w < 10) :
    (cones gs).getD w ∅ = {w} := by
  induction gs using List.reverseRecOn with
  | nil => simp [cones, List.getD_eq_getElem?_getD, hw]
  | append_singleton gs g ih =>
    rw [cones_append, coneStep, getD_append_lt _ _ _ _ (by rw [cones_length]; omega)]
    exact ih

theorem inputs_card_le (gs : List Gate) (hfan : ∀ g ∈ gs, g.inputs.length ≤ 2) (w : ℕ) :
    (((cones gs).getD w ∅).filter (· < 10)).card ≤ gs.length + 1 := by
  set S := (cones gs).getD w ∅
  set I := S.filter (· < 10)
  set G := S.filter fun u => 10 ≤ u ∧ u < 10 + gs.length
  by_cases hw10 : w < 10
  · have hS : S = {w} := cones_lt_ten gs w hw10
    have hI : I.card ≤ S.card := Finset.card_filter_le _ _
    rw [hS, Finset.card_singleton] at hI
    omega
  · by_cases hwlt : w < 10 + gs.length
    · have hwS : w ∈ S := cones_self gs w hwlt
      have hwG : w ∈ G := Finset.mem_filter.mpr ⟨hwS, by omega, hwlt⟩
      have hdisj : Disjoint I (G.erase w) := by
        rw [Finset.disjoint_left]
        intro u huI huG
        have h1 := (Finset.mem_filter.mp huI).2
        have h2 := (Finset.mem_filter.mp (Finset.mem_erase.mp huG).2).2.1
        omega
      have hsub : I ∪ G.erase w ⊆ S.erase w := by
        intro u hu
        rcases Finset.mem_union.mp hu with huI | huG
        · have h1 := Finset.mem_filter.mp huI
          exact Finset.mem_erase.mpr ⟨by omega, h1.1⟩
        · exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp huG).1,
            (Finset.mem_filter.mp (Finset.mem_erase.mp huG).2).1⟩
      have h1 : I.card + (G.erase w).card ≤ (reads gs S).card := by
        rw [← Finset.card_union_of_disjoint hdisj]
        exact (Finset.card_le_card hsub).trans (Finset.card_le_card (cones_subset_reads gs w))
      have h2 : (reads gs S).card ≤ 2 * G.card := by
        calc (reads gs S).card
            ≤ ∑ u ∈ G, ((gs.getD (u - 10) ⟨.and, []⟩).inputs.toFinset).card := Finset.card_biUnion_le
          _ ≤ ∑ u ∈ G, 2 := by
              apply Finset.sum_le_sum
              intro u hu
              have huB := (Finset.mem_filter.mp hu).2
              have hidx : u - 10 < gs.length := by omega
              have hmem : gs.getD (u - 10) ⟨.and, []⟩ ∈ gs := by
                simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx, Option.getD_some]
                exact List.getElem_mem hidx
              exact (List.toFinset_card_le _).trans (hfan _ hmem)
          _ = 2 * G.card := by simp [Nat.mul_comm]
      have hGcard : G.card ≤ gs.length := by
        have hGsub : G ⊆ Finset.Ico 10 (10 + gs.length) := by
          intro u hu
          have := (Finset.mem_filter.mp hu).2
          exact Finset.mem_Ico.mpr this
        exact (Finset.card_le_card hGsub).trans (by simp)
      have hGerase : (G.erase w).card + 1 = G.card := Finset.card_erase_add_one hwG
      omega
    · have hS : S = ∅ := getD_out (cones gs) w ∅ (by rw [cones_length]; omega)
      have hI : I = ∅ := by simp [I, hS]
      rw [hI, Finset.card_empty]
      omega

theorem must_depend (C : Circuit) (hmono : Monotone2 C) (hrep : Represents A C)
    (u₁ v₁ u₂ v₂ : Fin 5) (k : ℕ) (hk : k < 10)
    (h1 : A u₁ v₁ = true) (h2 : A u₂ v₂ = false)
    (hdom : ∀ i : ℕ, i ≠ k → (oneEach u₁ v₁).getD i false = true → (oneEach u₂ v₂).getD i false = true) :
    k ∈ ((cones C.gates).getD C.output ∅).filter (· < 10) := by
  refine Finset.mem_filter.mpr ⟨?_, hk⟩
  by_contra hnot
  let z : List Bool := (oneEach u₁ v₁).set k false
  have hzlen : z.length = 10 := by simp [z, oneEach]
  have h1len : (oneEach u₁ v₁).length = 10 := by simp [oneEach]
  have h2len : (oneEach u₂ v₂).length = 10 := by simp [oneEach]
  have hag : ∀ i ∈ (cones C.gates).getD C.output ∅, i < 10 →
      (oneEach u₁ v₁).getD i false = z.getD i false := by
    intro i hi hi10
    have hne : k ≠ i := fun h => hnot (h ▸ hi)
    simp only [z, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]
  have heq : C.eval (oneEach u₁ v₁) = C.eval z :=
    wiresOf_eq_of_agree C.gates (oneEach u₁ v₁) z h1len hzlen C.output hag
  have hztrue : C.eval z = true := by rw [← heq, hrep u₁ v₁, h1]
  have hle : ∀ i, z.getD i false = true → (oneEach u₂ v₂).getD i false = true := by
    intro i hi
    by_cases hik : k = i
    · subst hik
      simp only [z, List.getD_eq_getElem?_getD, List.getElem?_set_self (by omega : k < (oneEach u₁ v₁).length),
        Option.getD_some] at hi
      exact Bool.noConfusion hi
    · simp only [z, List.getD_eq_getElem?_getD, List.getElem?_set_ne hik] at hi
      exact hdom i (Ne.symm hik) (by simpa [List.getD_eq_getElem?_getD] using hi)
  have hgs : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or := by
    intro g hg
    have hop := (hmono g hg).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hop
  have hytrue : C.eval (oneEach u₂ v₂) = true :=
    wiresOf_mono C.gates hgs z (oneEach u₂ v₂) (by omega) hle C.output hztrue
  rw [hrep u₂ v₂, h2] at hytrue
  exact Bool.noConfusion hytrue

theorem dom_check (u₁ v₁ u₂ v₂ : Fin 5) (k : ℕ)
    (hfin : ∀ i : Fin 10, i.val ≠ k → (oneEach u₁ v₁).getD i.val false = true → (oneEach u₂ v₂).getD i.val false = true) :
    ∀ i : ℕ, i ≠ k → (oneEach u₁ v₁).getD i false = true → (oneEach u₂ v₂).getD i false = true := by
  intro i hi h
  by_cases hlt : i < 10
  · exact hfin ⟨i, hlt⟩ hi h
  · rw [getD_out _ _ _ (by simp [oneEach]; omega)] at h
    exact Bool.noConfusion h

theorem lower : ¬ RepSizeAtMost A 3 := by
  rintro ⟨C, hmono, hsize, hrep⟩
  set I := ((cones C.gates).getD C.output ∅).filter (· < 10)
  have h3 : 3 ∈ I := must_depend C hmono hrep 3 0 0 0 3 (by decide) (by decide) (by decide)
    (dom_check 3 0 0 0 3 (by decide))
  have h4 : 4 ∈ I := must_depend C hmono hrep 4 0 0 0 4 (by decide) (by decide) (by decide)
    (dom_check 4 0 0 0 4 (by decide))
  have h5 : 5 ∈ I := must_depend C hmono hrep 3 0 3 3 5 (by decide) (by decide) (by decide)
    (dom_check 3 0 3 3 5 (by decide))
  have h6 : 6 ∈ I := must_depend C hmono hrep 3 1 3 3 6 (by decide) (by decide) (by decide)
    (dom_check 3 1 3 3 6 (by decide))
  have h7 : 7 ∈ I := must_depend C hmono hrep 3 2 3 3 7 (by decide) (by decide) (by decide)
    (dom_check 3 2 3 3 7 (by decide))
  have hsub : ({3, 4, 5, 6, 7} : Finset ℕ) ⊆ I := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  have h5le : 5 ≤ I.card := (by decide : ({3, 4, 5, 6, 7} : Finset ℕ).card = 5) ▸ Finset.card_le_card hsub
  have hle4 : I.card ≤ C.gates.length + 1 := inputs_card_le C.gates (fun g hg => (hmono g hg).2) C.output
  change C.gates.length ≤ 3 at hsize
  omega

end PEqualNP.Outside.L_meta_20589

theorem PEqualNP.Outside.L_meta_20589 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (7569408 : ℕ).testBit (5 * u.val + v.val)) 4 ∧ ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (7569408 : ℕ).testBit (5 * u.val + v.val)) 3) :=
  ⟨PEqualNP.Outside.L_meta_20589.upper, PEqualNP.Outside.L_meta_20589.lower⟩
