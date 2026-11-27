import PEqualNP.Defs
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Union


namespace PEqualNP.Outside.L_meta_29920.InternalMask

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

lemma run_prefix (gs : List Gate) (w : List Bool) (k : Nat) (hk : k < w.length) :
    (run gs w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD k false = w.getD k false
    rw [ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hk

lemma append_agree (w v : List Bool) (b : Bool) (hlen : w.length = v.length)
    (heq : ∀ k, k ≠ 0 → w.getD k false = v.getD k false) :
    ∀ k, k ≠ 0 → (w ++ [b]).getD k false = (v ++ [b]).getD k false := by
  intro k hk
  by_cases hkw : k < w.length
  · rw [List.getD_append _ _ _ _ hkw,
      List.getD_append _ _ _ _ (by omega)]
    exact heq k hk
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), hlen]

lemma or_true (w : List Bool) (g : Gate) (j : Nat)
    (hop : g.op = GateOp.or) (hmem : j ∈ g.inputs) (hj : w.getD j false = true) :
    g.op.eval (g.inputs.map fun k => w.getD k false) = true := by
  rw [hop]
  change (g.inputs.map fun k => w.getD k false).any id = true
  apply List.any_eq_true.mpr
  exact ⟨true, List.mem_map.mpr ⟨j, hmem, hj⟩, rfl⟩

lemma run_masked_agree (gs : List Gate) (w v : List Bool) (j : Nat)
    (hlen : w.length = v.length)
    (heq : ∀ k, k ≠ 0 → w.getD k false = v.getD k false)
    (hjw : (run gs w).getD j false = true)
    (hjv : (run gs v).getD j false = true)
    (hgood : ∀ k : Fin gs.length, 0 ∈ (gs.get k).inputs →
      (gs.get k).op = GateOp.or ∧ j ∈ (gs.get k).inputs ∧ j < w.length + k.val) :
    ∀ k, k ≠ 0 → (run gs w).getD k false = (run gs v).getD k false := by
  induction gs generalizing w v with
  | nil => exact heq
  | cons g gs ih =>
    have hval : g.op.eval (g.inputs.map fun k => w.getD k false) =
        g.op.eval (g.inputs.map fun k => v.getD k false) := by
      by_cases h0 : 0 ∈ g.inputs
      · have hg := hgood ⟨0, by simp⟩ h0
        simp only [List.get_eq_getElem, List.getElem_cons_zero, Nat.add_zero] at hg
        obtain ⟨hop, hmem, hjl⟩ := hg
        have hw : w.getD j false = true := by
          rw [← run_prefix (g :: gs) w j hjl]
          exact hjw
        have hv : v.getD j false = true := by
          rw [← run_prefix (g :: gs) v j (by omega)]
          exact hjv
        rw [or_true w g j hop hmem hw, or_true v g j hop hmem hv]
      · congr 1
        apply List.map_congr_left
        intro k hk
        apply heq k
        intro hz
        subst k
        exact h0 hk
    have hext : ∀ k, k ≠ 0 → (step w g).getD k false = (step v g).getD k false := by
      unfold step
      rw [hval]
      exact append_agree w v _ hlen heq
    change ∀ k, k ≠ 0 → (run gs (step w g)).getD k false =
      (run gs (step v g)).getD k false
    apply ih (step w g) (step v g)
    · simp [step, hlen]
    · exact hext
    · exact hjw
    · exact hjv
    · intro k hk
      have h := hgood k.succ hk
      simp only [List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ] at h
      obtain ⟨hop, hmem, hlt⟩ := h
      refine ⟨hop, hmem, ?_⟩
      simp only [step, List.length_append, List.length_singleton]
      omega

lemma run_unread_prefix (gs : List Gate) (w v : List Bool) (j : Nat)
    (hlen : w.length = v.length)
    (heq : ∀ k, k ≠ 0 → w.getD k false = v.getD k false)
    (hj : j ≠ 0)
    (hbefore : ∀ k : Fin gs.length, 0 ∈ (gs.get k).inputs → j < w.length + k.val) :
    (run gs w).getD j false = (run gs v).getD j false := by
  induction gs generalizing w v with
  | nil => exact heq j hj
  | cons g gs ih =>
    by_cases hjl : j < w.length
    · rw [run_prefix (g :: gs) w j hjl,
        run_prefix (g :: gs) v j (by omega)]
      exact heq j hj
    · have h0 : 0 ∉ g.inputs := by
        intro hmem
        have h := hbefore ⟨0, by simp⟩ hmem
        simp only [Nat.add_zero] at h
        omega
      have hval : g.op.eval (g.inputs.map fun k => w.getD k false) =
          g.op.eval (g.inputs.map fun k => v.getD k false) := by
        congr 1
        apply List.map_congr_left
        intro k hk
        apply heq k
        intro hz
        subst k
        exact h0 hk
      have hext : ∀ k, k ≠ 0 → (step w g).getD k false = (step v g).getD k false := by
        unfold step
        rw [hval]
        exact append_agree w v _ hlen heq
      change (run gs (step w g)).getD j false = (run gs (step v g)).getD j false
      apply ih (step w g) (step v g)
      · simp [step, hlen]
      · exact hext
      · intro k hk
        have h := hbefore k.succ hk
        simp only [Fin.val_succ] at h
        simp only [step, List.length_append, List.length_singleton]
        omega

theorem circuit_collision (C : Circuit) (i : Fin C.gates.length)
    (j : Nat) (w v : List Bool)
    (hlen : w.length = v.length)
    (heq : ∀ k, k ≠ 0 → w.getD k false = v.getD k false)
    (hjw : (C.wires w).getD j false = true)
    (hjv : (C.wires v).getD j false = true)
    (hunique : ∀ q : Fin C.gates.length, 0 ∈ (C.gates.get q).inputs → q = i)
    (hop : (C.gates.get i).op = GateOp.or)
    (hmem : j ∈ (C.gates.get i).inputs)
    (hj : j < w.length + i.val) (hout : C.output ≠ 0) :
    C.eval w = C.eval v := by
  apply run_masked_agree C.gates w v j hlen heq hjw hjv ?_ C.output hout
  intro q hq
  have hi := hunique q hq
  subst q
  exact ⟨hop, hmem, hj⟩

theorem circuit_collision_of_one_true (C : Circuit) (i : Fin C.gates.length)
    (j : Nat) (w v : List Bool)
    (hlen : w.length = v.length)
    (heq : ∀ k, k ≠ 0 → w.getD k false = v.getD k false)
    (hjw : (C.wires w).getD j false = true)
    (hunique : ∀ q : Fin C.gates.length, 0 ∈ (C.gates.get q).inputs → q = i)
    (hop : (C.gates.get i).op = GateOp.or)
    (hmem : j ∈ (C.gates.get i).inputs)
    (hj : j < w.length + i.val) (hj0 : j ≠ 0) (hout : C.output ≠ 0) :
    C.eval w = C.eval v := by
  have hwire : (C.wires w).getD j false = (C.wires v).getD j false := by
    apply run_unread_prefix C.gates w v j hlen heq hj0
    intro q hq
    have hi := hunique q hq
    subst q
    exact hj
  have hjv : (C.wires v).getD j false = true := hwire.symm.trans hjw
  exact circuit_collision C i j w v hlen heq hjw hjv hunique hop hmem hj hout

end PEqualNP.Outside.L_meta_29920.InternalMask


namespace PEqualNP.Outside.L_meta_29920.TightReadOnce

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.inputs.length ≤ 2

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def reads (g : Gate) : List ℕ :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

theorem reads_le (g : Gate) : (reads g).length ≤ g.inputs.length := by
  cases h : g.op <;> simp [reads, h, Nat.min_le_right]

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  ((reads g).map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ reads g, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem eval_congr_reads (g : Gate) (w w' : List Bool)
    (h : ∀ a ∈ reads g, w.getD a false = w'.getD a false) :
    g.op.eval (g.inputs.map fun a => w.getD a false) =
      g.op.eval (g.inputs.map fun a => w'.getD a false) := by
  by_cases hn : g.op = .not
  · rw [hn]
    cases hi : g.inputs with
    | nil => simp [GateOp.eval, hi]
    | cons a l =>
      have ha := h a (by simp [reads, hn, hi])
      change (!w.getD a false) = !w'.getD a false
      rw [ha]
  · have he : g.inputs.map (fun a => w.getD a false) =
        g.inputs.map (fun a => w'.getD a false) := by
      apply List.map_congr_left
      intro a ha
      exact h a (by cases ho : g.op <;> simp_all [reads])
    rw [he]

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      apply eval_congr_reads
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ (reads g).toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ (reads g).toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) (le_trans (reads_le g) hg)) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ (reads g).toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self) h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this


theorem getD_take_eq (C : Circuit) (n k w : Nat)
    (hk : k ≤ C.gates.length) (hw : w < n + k) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).getD w false =
      (wiresFrom (C.gates.take k) (List.ofFn x)).getD w false := by
  change (wiresFrom C.gates (List.ofFn x)).getD w false = _
  conv_lhs => rw [← List.take_append_drop k C.gates]
  rw [wiresFrom_append]
  apply getD_wiresFrom
  rw [length_wiresFrom]
  simpa [List.length_take, Nat.min_eq_left hk] using hw

theorem wire_support (C : Circuit) (n k w : Nat)
    (hk : k ≤ C.gates.length) (hw : w < n + k)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∃ S : Finset (Fin n), S.card ≤ k + 1 ∧
      ∀ x y : Fin n → Bool, (∀ i ∈ S, x i = y i) →
        (C.wires (List.ofFn x)).getD w false =
          (C.wires (List.ofFn y)).getD w false := by
  let S := (suppsFrom (C.gates.take k) (inputSupps n)).getD w ∅
  refine ⟨S, ?_, ?_⟩
  · have hc := cnt_suppsFrom (C.gates.take k) 0 (inputSupps n)
      (fun g hg => hfan g (List.mem_of_mem_take hg)) cnt_inputs {w}
    simpa only [Finset.singleton_biUnion, Finset.card_singleton, zero_add,
      List.length_take, Nat.min_eq_left hk] using hc
  · intro x y heq
    rw [getD_take_eq C n k w hk hw x, getD_take_eq C n k w hk hw y]
    exact (agree_wiresFrom x y (C.gates.take k) _ _ _ (agree_inputs x y)).2.2 w heq

theorem wire_essential_bound (C : Circuit) (n k w : Nat)
    (hk : k ≤ C.gates.length) (hw : w < n + k)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (E : Finset (Fin n))
    (hsens : ∀ i ∈ E, ∃ x y : Fin n → Bool,
      (∀ j, j ≠ i → x j = y j) ∧
        (C.wires (List.ofFn x)).getD w false ≠
          (C.wires (List.ofFn y)).getD w false) :
    E.card ≤ k + 1 := by
  obtain ⟨S, hcard, hdep⟩ := wire_support C n k w hk hw hfan
  apply le_trans (Finset.card_le_card (t := S) ?_) hcard
  intro i hi
  by_contra hni
  obtain ⟨x, y, hxy, hne⟩ := hsens i hi
  apply hne (hdep x y ?_)
  intro j hj
  apply hxy j
  intro hji
  subst j
  exact hni hj



/-- Read-once positive AND/OR formulas, indexed by their exact leaf set. -/
def RO (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ Q : Finset (Fin n) → ((Fin n → Bool) → Bool) → Prop,
    (∀ i : Fin n, Q {i} (fun x => x i)) →
    (∀ A B a b, Disjoint A B → Q A a → Q B b →
      Q (A ∪ B) (fun x => a x && b x) ∧ Q (A ∪ B) (fun x => a x || b x)) → Q S f

theorem ro_leaf (i : Fin n) : RO {i} (fun x => x i) := fun _ hl _ => hl i

theorem ro_and {A B : Finset (Fin n)} {a b : (Fin n → Bool) → Bool}
    (hd : Disjoint A B) (ha : RO A a) (hb : RO B b) :
    RO (A ∪ B) (fun x => a x && b x) :=
  fun Q hl hj => (hj A B a b hd (ha Q hl hj) (hb Q hl hj)).1

theorem ro_or {A B : Finset (Fin n)} {a b : (Fin n → Bool) → Bool}
    (hd : Disjoint A B) (ha : RO A a) (hb : RO B b) :
    RO (A ∪ B) (fun x => a x || b x) :=
  fun Q hl hj => (hj A B a b hd (ha Q hl hj) (hb Q hl hj)).2

def Fam (L : List (Finset (Fin n))) (F : ℕ → (Fin n → Bool) → Bool) (W : Finset ℕ) : Prop :=
  (∀ w ∈ W, RO (L.getD w ∅) (F w)) ∧
  (∀ w ∈ W, ∀ v ∈ W, w ≠ v → Disjoint (L.getD w ∅) (L.getD v ∅))

def Tight (t : ℕ) (L : List (Finset (Fin n))) (F : ℕ → (Fin n → Bool) → Bool) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card = t + W.card → Fam L F W

theorem tight_inputs : Tight 0 (inputSupps n) (fun j x => (List.ofFn x).getD j false) := by
  intro W heq
  have hvalid : ∀ j ∈ W, j < n := by
    intro j hj
    by_contra hn
    have hz : (inputSupps n).getD j ∅ = ∅ :=
      List.getD_eq_default _ _ (by simp [inputSupps]; omega)
    have he := heq
    rw [← Finset.insert_erase hj, Finset.biUnion_insert, hz, Finset.empty_union] at he
    rw [Finset.insert_erase hj] at he
    have hc := cnt_inputs (n := n) (W.erase j)
    have hcard := Finset.card_erase_add_one hj
    omega
  constructor
  · intro j hj
    have hv := hvalid j hj
    have hs : (inputSupps n).getD j ∅ = {⟨j, hv⟩} := by simp [inputSupps, hv]
    have hf : (fun x : Fin n → Bool => (List.ofFn x).getD j false) = (fun x => x ⟨j,hv⟩) := by
      funext x; simp [hv]
    rw [hs]
    change RO {⟨j,hv⟩} (fun x : Fin n → Bool => (List.ofFn x).getD j false)
    rw [hf]
    exact ro_leaf _
  · intro j hj k hk hne
    have hjn := hvalid j hj
    have hkn := hvalid k hk
    simpa [inputSupps, hjn, hkn, Fin.ext_iff] using hne


theorem union_step (L : List (Finset (Fin n))) (g : Gate) (W : Finset ℕ)
    (hW : L.length ∈ W) :
    (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅) =
      ((W.erase L.length ∪ (reads g).toFinset).biUnion fun j => L.getD j ∅) := by
  ext i
  constructor
  · intro hi
    rw [Finset.mem_biUnion] at hi ⊢
    obtain ⟨j, hjW, hij⟩ := hi
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hij
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
      exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
    · rw [getD_snoc_ne _ _ _ _ hjl] at hij
      exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
  · intro hi
    obtain ⟨j,hj,hi⟩ := Finset.mem_biUnion.mp hi
    rcases Finset.mem_union.mp hj with hj | hj
    · refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_of_mem_erase hj, ?_⟩
      rw [getD_snoc_ne _ _ _ _ (Finset.ne_of_mem_erase hj)]
      exact hi
    · refine Finset.mem_biUnion.mpr ⟨L.length,hW,?_⟩
      rw [getD_snoc_eq]
      exact (mem_gateSupp L g i).mpr ⟨j,List.mem_toFinset.mp hj,hi⟩

theorem binary_of_reads (g : Gate)
    (ho : g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (hlen : g.inputs.length ≤ 2) (hcard : (reads g).toFinset.card = 2) :
    ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ (g.op = .and ∨ g.op = .or) := by
  have hn : g.op ≠ .not := by
    intro hn
    have hc := List.toFinset_card_le (reads g)
    have hl : (reads g).length ≤ 1 := by simp [reads,hn]
    omega
  have hop : g.op = .and ∨ g.op = .or := by rcases ho with h | h | h <;> simp_all
  have hr : reads g = g.inputs := by rcases hop with h | h <;> simp [reads,h]
  rw [hr] at hcard
  rcases hi : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp [hi] at hcard
  · simp [hi] at hcard
  · refine ⟨a,b,rfl,?_,hop⟩
    intro hab
    simp [hi,hab] at hcard
  · simp [hi] at hlen

def nextF (L : List (Finset (Fin n))) (F : ℕ → (Fin n → Bool) → Bool) (g : Gate)
    (j : ℕ) (x : Fin n → Bool) : Bool :=
  if j = L.length then g.op.eval (g.inputs.map fun a => F a x) else F j x

theorem tight_step (t : ℕ) (L : List (Finset (Fin n))) (F : ℕ → (Fin n → Bool) → Bool)
    (g : Gate) (ho : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hlen : g.inputs.length ≤ 2)
    (hc : Cnt t L) (ht : Tight t L F) :
    Tight (t+1) (L ++ [gateSupp L g]) (nextF L F g) := by
  intro W heq
  have hW : L.length ∈ W := by
    by_contra hn
    have hU : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅) =
        (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun h => hn (h ▸ hj))
    rw [hU] at heq
    have := hc W
    omega
  let E := W.erase L.length
  let B := (reads g).toFinset
  let P := E ∪ B
  have hEc : E.card+1 = W.card := Finset.card_erase_add_one hW
  have hBc : B.card ≤ 2 := le_trans (List.toFinset_card_le _) (le_trans (reads_le g) hlen)
  have hPc : P.card ≤ E.card + B.card := Finset.card_union_le _ _
  have hU : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅) =
      (P.biUnion fun j => L.getD j ∅) := union_step L g W hW
  rw [hU] at heq
  have hcP := hc P
  have hB2 : B.card = 2 := by omega
  have hPexact : P.card = E.card + B.card := by omega
  have hTexact : (P.biUnion fun j => L.getD j ∅).card = t + P.card := by omega
  have hEB : Disjoint E B := Finset.card_union_eq_card_add_card.mp hPexact
  obtain ⟨a,b,hin,hab,hop⟩ := binary_of_reads g ho hlen hB2
  have hreads : reads g = [a,b] := by rcases hop with h | h <;> simp [reads,h,hin]
  have haB : a ∈ B := by simp [B,hreads]
  have hbB : b ∈ B := by simp [B,hreads]
  have haP : a ∈ P := Finset.mem_union_right _ haB
  have hbP : b ∈ P := Finset.mem_union_right _ hbB
  have hF := ht P hTexact
  have hEP : E ⊆ P := Finset.subset_union_left
  have hneA : ∀ w ∈ E, w ≠ a := by
    intro w hw hwa; subst w
    exact Finset.disjoint_left.mp hEB hw haB
  have hneB : ∀ w ∈ E, w ≠ b := by
    intro w hw hwb; subst w
    exact Finset.disjoint_left.mp hEB hw hbB
  have hS : gateSupp L g = L.getD a ∅ ∪ L.getD b ∅ := by simp [gateSupp,hreads]
  have hnew : RO (gateSupp L g) (nextF L F g L.length) := by
    rw [hS]
    have hd := hF.2 a haP b hbP hab
    rcases hop with hop | hop
    · have hf : nextF L F g L.length = (fun x => F a x && F b x) := by
        funext x; simp [nextF,hin,hop,GateOp.eval]
      rw [hf]; exact ro_and hd (hF.1 a haP) (hF.1 b hbP)
    · have hf : nextF L F g L.length = (fun x => F a x || F b x) := by
        funext x; simp [nextF,hin,hop,GateOp.eval]
      rw [hf]; exact ro_or hd (hF.1 a haP) (hF.1 b hbP)
  have hother : ∀ w ∈ E, (L ++ [gateSupp L g]).getD w ∅ = L.getD w ∅ :=
    fun w hw => getD_snoc_ne _ _ _ _ (Finset.ne_of_mem_erase hw)
  have hnewdis : ∀ w ∈ E, Disjoint (gateSupp L g) (L.getD w ∅) := by
    intro w hw
    rw [hS,Finset.disjoint_union_left]
    exact ⟨hF.2 a haP w (hEP hw) (hneA w hw).symm,
      hF.2 b hbP w (hEP hw) (hneB w hw).symm⟩
  constructor
  · intro w hw
    by_cases hwk : w = L.length
    · subst w
      rw [getD_snoc_eq]
      exact hnew
    · have hwE : w ∈ E := Finset.mem_erase.mpr ⟨hwk,hw⟩
      rw [hother w hwE]
      have hf : nextF L F g w = F w := by funext x; simp [nextF,hwk]
      rw [hf]
      exact hF.1 w (hEP hwE)
  · intro w hw v hv hne
    by_cases hwk : w = L.length
    · subst w
      have hvE : v ∈ E := Finset.mem_erase.mpr ⟨hne.symm,hv⟩
      rw [getD_snoc_eq,hother v hvE]
      exact hnewdis v hvE
    · have hwE : w ∈ E := Finset.mem_erase.mpr ⟨hwk,hw⟩
      rw [hother w hwE]
      by_cases hvk : v = L.length
      · subst v
        rw [getD_snoc_eq]
        exact (hnewdis w hwE).symm
      · have hvE : v ∈ E := Finset.mem_erase.mpr ⟨hvk,hv⟩
        rw [hother v hvE]
        exact hF.2 w (hEP hwE) v (hEP hvE) hne


theorem tight_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n)))
    (v : (Fin n → Bool) → List Bool), (∀ x, (v x).length = L.length) →
    (∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) →
    Cnt t L → Tight t L (fun j x => (v x).getD j false) →
    Tight (t+gs.length) (suppsFrom gs L) (fun j x => (wiresFrom gs (v x)).getD j false) := by
  induction gs with
  | nil => intro t L v hv _ hc ht; exact ht
  | cons g gs ih =>
    intro t L v hv hg hc ht
    let v' := fun x : Fin n → Bool => v x ++ [g.op.eval (g.inputs.map fun a => (v x).getD a false)]
    have hv' : ∀ x, (v' x).length = (L ++ [gateSupp L g]).length := by
      intro x; simp [v',hv x]
    have hf : (fun j x => (v' x).getD j false) =
        nextF L (fun j x => (v x).getD j false) g := by
      funext j x
      by_cases hj : j = L.length
      · subst j
        simp only [nextF,ite_true]
        dsimp only [v']
        rw [← hv x,getD_snoc_eq]
      · simp only [nextF,hj,ite_false]
        exact getD_snoc_ne _ _ _ _ (by rw [hv x]; exact hj)
    have hgg := hg g List.mem_cons_self
    have ht' : Tight (t+1) (L ++ [gateSupp L g]) (fun j x => (v' x).getD j false) := by
      rw [hf]
      exact tight_step t L _ g hgg.1 hgg.2 hc ht
    have hres := ih (t+1) (L ++ [gateSupp L g]) v' hv'
      (fun g' h => hg g' (List.mem_cons_of_mem g h)) (cnt_step t L g hgg.2 hc) ht'
    simpa only [List.length_cons,show t+(gs.length+1)=t+1+gs.length by omega,
      suppsFrom,wiresFrom,List.foldl_cons,v'] using hres

/-- Equality in the fan-in-two input bound forces a positive read-once formula. -/
theorem wire_read_once (C : Circuit) (n k w : Nat)
    (hk : k ≤ C.gates.length) (hw : w < n+k)
    (hfan : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (E : Finset (Fin n)) (hE : E.card = k+1)
    (hsens : ∀ i ∈ E, ∃ x y : Fin n → Bool,
      (∀ j, j ≠ i → x j = y j) ∧
      (C.wires (List.ofFn x)).getD w false ≠ (C.wires (List.ofFn y)).getD w false) :
    RO E (fun x => (C.wires (List.ofFn x)).getD w false) := by
  let gs := C.gates.take k
  let L := suppsFrom gs (inputSupps n)
  let S := L.getD w ∅
  have hlen : gs.length = k := by simp [gs,List.length_take,Nat.min_eq_left hk]
  have hfan' : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 :=
    fun g hg => hfan g (List.mem_of_mem_take hg)
  have hc := cnt_suppsFrom gs 0 (inputSupps n) (fun g hg => (hfan' g hg).2) cnt_inputs
  have hSc : S.card ≤ k+1 := by
    have := hc {w}
    simpa only [Finset.singleton_biUnion,Finset.card_singleton,zero_add,hlen] using this
  have hdep : ∀ x y : Fin n → Bool, (∀ i ∈ S,x i=y i) →
      (C.wires (List.ofFn x)).getD w false = (C.wires (List.ofFn y)).getD w false := by
    intro x y hxy
    rw [getD_take_eq C n k w hk hw x,getD_take_eq C n k w hk hw y]
    exact (agree_wiresFrom x y gs _ _ _ (agree_inputs x y)).2.2 w hxy
  have hsub : E ⊆ S := by
    intro i hi
    by_contra hni
    obtain ⟨x,y,hxy,hne⟩ := hsens i hi
    apply hne (hdep x y ?_)
    intro j hj
    exact hxy j (fun h => hni (h ▸ hj))
  have hES : E = S := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hT := tight_suppsFrom gs 0 (inputSupps n) (fun x => List.ofFn x)
    (fun x => by simp [inputSupps]) hfan' cnt_inputs tight_inputs
  have heq : (({w} : Finset ℕ).biUnion fun j => L.getD j ∅).card = (0+gs.length)+({w} : Finset ℕ).card := by
    have hS : S.card = k+1 := by rw [←hES]; exact hE
    simpa only [Finset.singleton_biUnion,Finset.card_singleton,zero_add,hlen] using hS
  have hR := (hT {w} heq).1 w (Finset.mem_singleton_self w)
  change RO S _ at hR
  rw [←hES] at hR
  have hf : (fun x : Fin n → Bool => (wiresFrom gs (List.ofFn x)).getD w false) =
      (fun x => (C.wires (List.ofFn x)).getD w false) := by
    funext x; exact (getD_take_eq C n k w hk hw x).symm
  change RO E (fun x : Fin n → Bool => (wiresFrom gs (List.ofFn x)).getD w false) at hR
  rw [hf] at hR
  exact hR

end PEqualNP.Outside.L_meta_29920.TightReadOnce


namespace PEqualNP.Outside.L_meta_29920.Gate8

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_29920.InternalMask

def cycle7 (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0)

def bits (m : Nat) : Fin 7 → Bool := fun k => m.testBit k.val

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = _
    rw [ih]
    simp [step]
    omega

lemma output_nonzero (C : Circuit)
    (hc : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = cycle7 x) : C.output ≠ 0 := by
  intro hz
  have h := hc (bits 6)
  change (run C.gates (List.ofFn (bits 6))).getD C.output false = _ at h
  rw [hz, run_prefix C.gates (List.ofFn (bits 6)) 0 (by simp)] at h
  have hl : (List.ofFn (bits 6)).getD 0 false = false := by decide
  have hr : cycle7 (bits 6) = true := by decide
  rw [hl, hr] at h
  cases h

lemma two_tail (gs : List Gate) (h : gs.length = 10) :
    ∃ p : List Gate, ∃ a b : Gate, p.length = 8 ∧ gs = p ++ [a,b] := by
  have hd : (gs.drop 8).length = 2 := by simp [h]
  have hs : ∃ a b : Gate, gs.drop 8 = [a,b] := by
    generalize gs.drop 8 = ds at hd ⊢
    cases ds with
    | nil => simp at hd
    | cons a ds =>
      cases ds with
      | nil => simp at hd
      | cons b ds =>
        cases ds with
        | nil => exact ⟨a,b,rfl⟩
        | cons c ds => simp only [List.length_cons] at hd; omega
  obtain ⟨a,b,hab⟩ := hs
  exact ⟨gs.take 8,a,b,by simp [h],by rw [← hab, List.take_append_drop]⟩

lemma ofFn_agree_zero (x y : Fin 7 → Bool)
    (h : ∀ k : Fin 7, k ≠ 0 → x k = y k) :
    ∀ k, k ≠ 0 → (List.ofFn x).getD k false = (List.ofFn y).getD k false := by
  intro k hk
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split_ifs with hlt
  · simp only [Option.getD_some]
    apply h
    intro hz
    have hzv := congrArg Fin.val hz
    simp only [Fin.val_zero] at hzv
    exact hk hzv
  · rfl

lemma pair64_agree : ∀ k : Fin 7, k ≠ 0 → bits 64 k = bits 65 k := by decide

lemma output_lower (C : Circuit) (i : Fin C.gates.length)
    (hi : i.val = 8)
    (hc : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = cycle7 x)
    (hunique : ∀ q : Fin C.gates.length, 0 ∈ (C.gates.get q).inputs → q = i) :
    15 ≤ C.output := by
  by_contra h
  have he := run_unread_prefix C.gates (List.ofFn (bits 64)) (List.ofFn (bits 65))
    C.output (by simp) (ofFn_agree_zero _ _ pair64_agree) (output_nonzero C hc) ?_
  · change C.eval (List.ofFn (bits 64)) = C.eval (List.ofFn (bits 65)) at he
    rw [hc, hc] at he
    have hf : cycle7 (bits 64) = false := by decide
    have ht : cycle7 (bits 65) = true := by decide
    rw [hf,ht] at he
    cases he
  · intro q hq
    have hqi := hunique q hq
    subst q
    simp only [List.length_ofFn,hi]
    omega

lemma output_upper (C : Circuit) (hsize : C.size = 10)
    (hc : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = cycle7 x) :
    C.output < 17 := by
  by_contra h
  have he := hc (bits 3)
  have hl : (run C.gates (List.ofFn (bits 3))).length = 17 := by
    rw [run_length]
    simp only [List.length_ofFn]
    change 7 + C.size = 17
    omega
  change (run C.gates (List.ofFn (bits 3))).getD C.output false = _ at he
  rw [List.getD_eq_default _ _ (by omega)] at he
  have ht : cycle7 (bits 3) = true := by decide
  rw [ht] at he
  cases he

lemma get_eight (C : Circuit) (i : Fin C.gates.length) (hi : i.val = 8)
    (p : List Gate) (a b : Gate) (hp : p.length = 8) (hgs : C.gates = p ++ [a,b]) :
    C.gates.get i = a := by
  simp only [List.get_eq_getElem]
  rw [List.getElem_eq_getD a,hi,hgs,List.getD_append_right _ _ _ _ (by omega)]
  simp [hp]

lemma output_not_eight (C : Circuit) (i : Fin C.gates.length)
    (hi : i.val = 8) (hsize : C.size = 10)
    (hc : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = cycle7 x)
    (hread : 0 ∈ (C.gates.get i).inputs)
    (hop : (C.gates.get i).op = GateOp.or) : C.output ≠ 15 := by
  obtain ⟨p,a,b,hp,hgs⟩ := two_tail C.gates hsize
  have hga := get_eight C i hi p a b hp hgs
  have hread' : 0 ∈ a.inputs := by rw [← hga]; exact hread
  have hop' : a.op = GateOp.or := by rw [← hga]; exact hop
  let w := run p (List.ofFn (bits 1))
  have hwlen : w.length = 15 := by simp [w,run_length,hp]
  have hw0 : w.getD 0 false = true := by
    rw [show w = run p (List.ofFn (bits 1)) from rfl, run_prefix p _ 0 (by simp)]
    decide
  have ha : a.op.eval (a.inputs.map fun k => w.getD k false) = true :=
    or_true w a 0 hop' hread' hw0
  intro hout
  have he := hc (bits 1)
  change (run C.gates (List.ofFn (bits 1))).getD C.output false = _ at he
  rw [hgs,hout] at he
  simp only [run,List.foldl_append,List.foldl_cons,List.foldl_nil] at he
  change (step (step w a) b).getD 15 false = _ at he
  have hslen : (step w a).length = 16 := by simp [step,hwlen]
  change (step w a ++ [_]).getD 15 false = _ at he
  rw [List.getD_append _ _ _ _ (by omega)] at he
  change (w ++ [_]).getD 15 false = _ at he
  rw [List.getD_append_right _ _ _ _ (by omega)] at he
  simp only [hwlen,Nat.sub_self,List.getD_cons_zero,ha] at he
  have hf : cycle7 (bits 1) = false := by decide
  rw [hf] at he
  cases he

lemma output_last (C : Circuit) (i : Fin C.gates.length)
    (hi : i.val = 8) (hsize : C.size = 10)
    (hc : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = cycle7 x)
    (hread : 0 ∈ (C.gates.get i).inputs)
    (hunique : ∀ q : Fin C.gates.length, 0 ∈ (C.gates.get q).inputs → q = i)
    (hop : (C.gates.get i).op = GateOp.or) : C.output = 16 := by
  have h₁ := output_lower C i hi hc hunique
  have h₂ := output_upper C hsize hc
  have h₃ := output_not_eight C i hi hsize hc hread hop
  omega

lemma inputs_pair (l : List Nat) (j : Nat) (hl : l.length ≤ 2)
    (h0 : 0 ∈ l) (hj : j ∈ l) (hne : j ≠ 0) :
    l = [0,j] ∨ l = [j,0] := by
  cases l with
  | nil => simp at h0
  | cons a l =>
    cases l with
    | nil =>
      simp only [List.mem_singleton] at h0 hj
      omega
    | cons b l =>
      cases l with
      | cons c l => simp only [List.length_cons] at hl; omega
      | nil =>
        simp at h0 hj
        rcases h0 with h0 | h0
        · subst a
          rcases hj with hj | hj
          · exact (hne hj).elim
          · subst b; exact Or.inl rfl
        · subst b
          rcases hj with hj | hj
          · subst a; exact Or.inr rfl
          · exact (hne hj).elim

lemma get_nine (C : Circuit) (k : Fin C.gates.length) (hk : k.val = 9)
    (p : List Gate) (a b : Gate) (hp : p.length = 8) (hgs : C.gates = p ++ [a,b]) :
    C.gates.get k = b := by
  simp only [List.get_eq_getElem]
  rw [List.getElem_eq_getD b,hk,hgs,List.getD_append_right _ _ _ _ (by omega)]
  simp [hp]

lemma partner_true_on_positive (C : Circuit) (i k : Fin C.gates.length) (j : Nat)
    (hi : i.val = 8) (hsize : C.size = 10)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hc : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = cycle7 x)
    (hread : 0 ∈ (C.gates.get i).inputs)
    (hunique : ∀ q : Fin C.gates.length, 0 ∈ (C.gates.get q).inputs → q = i)
    (hop : (C.gates.get i).op = GateOp.or)
    (hkop : (C.gates.get k).op = GateOp.and) (hik : i.val < k.val)
    (hreadik : 7 + i.val ∈ (C.gates.get k).inputs)
    (hpartner : j ∈ (C.gates.get i).inputs) (hj0 : j ≠ 0) (hjl : j < 7+i.val)
    (x : Fin 7 → Bool) (hx0 : x 0 = false) (hxf : cycle7 x = true) :
    (C.wires (List.ofFn x)).getD j false = true := by
  have hk : k.val = 9 := by
    have hkb := k.isLt
    change k.val < C.size at hkb
    omega
  have hout := output_last C i hi hsize hc hread hunique hop
  obtain ⟨p,a,b,hp,hgs⟩ := two_tail C.gates hsize
  have hga := get_eight C i hi p a b hp hgs
  have hgb := get_nine C k hk p a b hp hgs
  have hread' : 0 ∈ a.inputs := by rw [← hga]; exact hread
  have hpartner' : j ∈ a.inputs := by rw [← hga]; exact hpartner
  have hop' : a.op = GateOp.or := by rw [← hga]; exact hop
  have hkop' : b.op = GateOp.and := by rw [← hgb]; exact hkop
  have hreadik' : 15 ∈ b.inputs := by rw [← hgb]; simpa [hi] using hreadik
  have hfan' : a.inputs.length ≤ 2 := by apply hfan; rw [hgs]; simp
  have hpair := inputs_pair a.inputs j hfan' hread' hpartner' hj0
  let w := run p (List.ofFn x)
  have hwlen : w.length = 15 := by simp [w,run_length,hp]
  have hslen : (step w a).length = 16 := by simp [step,hwlen]
  have hw0 : w.getD 0 false = false := by
    rw [show w = run p (List.ofFn x) from rfl,run_prefix p _ 0 (by simp)]
    simpa [List.getD_eq_getElem?_getD,List.getElem?_ofFn] using hx0
  have he := hc x
  rw [hxf] at he
  change (run C.gates (List.ofFn x)).getD C.output false = true at he
  rw [hgs,hout] at he
  simp only [run,List.foldl_append,List.foldl_cons,List.foldl_nil] at he
  change (step w a ++ [b.op.eval (b.inputs.map fun l => (step w a).getD l false)]).getD 16 false = true at he
  rw [List.getD_append_right _ _ _ _ (by omega)] at he
  simp only [hslen,Nat.sub_self,List.getD_cons_zero] at he
  rw [hkop'] at he
  change (b.inputs.map fun l => (step w a).getD l false).all id = true at he
  have he8 : (step w a).getD 15 false = true := by
    exact List.all_eq_true.mp he _ (List.mem_map.mpr ⟨15,hreadik',rfl⟩)
  change (w ++ [a.op.eval (a.inputs.map fun l => w.getD l false)]).getD 15 false = true at he8
  rw [List.getD_append_right _ _ _ _ (by omega)] at he8
  simp only [hwlen,Nat.sub_self,List.getD_cons_zero] at he8
  rw [hop'] at he8
  have hq : w.getD j false = true := by
    rcases hpair with ha | ha
    · rw [ha] at he8
      simpa only [GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
        id_eq,Bool.or_false,hw0,Bool.false_or] using he8
    · rw [ha] at he8
      simpa only [GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
        id_eq,Bool.or_false,hw0,Bool.false_or] using he8
  change (run C.gates (List.ofFn x)).getD j false = true
  rw [hgs]
  simp only [run,List.foldl_append,List.foldl_cons,List.foldl_nil]
  change (run [a,b] w).getD j false = true
  rw [run_prefix [a,b] w j (by omega)]
  exact hq

def negative : Fin 7 → Nat := ![0,68,2,18,10,18,34]
def positive : Fin 7 → Nat := ![0,70,6,26,26,50,98]
def flipped : Fin 7 → Nat := ![0,69,3,19,11,19,35]

lemma witness_facts : ∀ r : Fin 7, r ≠ 0 →
    bits (negative r) 0 = false ∧ bits (positive r) 0 = false ∧
    cycle7 (bits (negative r)) = false ∧ cycle7 (bits (positive r)) = true ∧
    cycle7 (bits (flipped r)) = true ∧
    (∀ s : Fin 7, s ≠ 0 → bits (negative r) s = bits (flipped r) s) ∧
    (∀ s : Fin 7, s ≠ r → bits (negative r) s = bits (positive r) s) := by
  decide

theorem partner_sensitive (C : Circuit) (i k : Fin C.gates.length) (j : Nat)
    (hi : i.val = 8) (hsize : C.size = 10)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hc : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = cycle7 x)
    (hread : 0 ∈ (C.gates.get i).inputs)
    (hunique : ∀ q : Fin C.gates.length, 0 ∈ (C.gates.get q).inputs → q = i)
    (hop : (C.gates.get i).op = GateOp.or)
    (hkop : (C.gates.get k).op = GateOp.and) (hik : i.val < k.val)
    (hreadik : 7 + i.val ∈ (C.gates.get k).inputs)
    (hpartner : j ∈ (C.gates.get i).inputs) (hj0 : j ≠ 0) (hjl : j < 7+i.val) :
    ∀ r : Fin 7, r ≠ 0 → ∃ x y : Fin 7 → Bool,
      (∀ s, s ≠ r → x s = y s) ∧
      (C.wires (List.ofFn x)).getD j false ≠ (C.wires (List.ofFn y)).getD j false := by
  intro r hr
  obtain ⟨hn0,hp0,hnf,hpf,hff,hnflip,hchange⟩ := witness_facts r hr
  have hqpos := partner_true_on_positive C i k j hi hsize hfan hc hread hunique hop
    hkop hik hreadik hpartner hj0 hjl (bits (positive r)) hp0 hpf
  have hqneg : (C.wires (List.ofFn (bits (negative r)))).getD j false = false := by
    cases hv : (C.wires (List.ofFn (bits (negative r)))).getD j false with
    | false => rfl
    | true =>
      have he := circuit_collision_of_one_true C i j
        (List.ofFn (bits (negative r))) (List.ofFn (bits (flipped r)))
        (by simp) (ofFn_agree_zero _ _ hnflip) hv hunique hop hpartner
        (by simpa only [List.length_ofFn] using hjl) hj0 (output_nonzero C hc)
      rw [hc,hc,hnf,hff] at he
      cases he
  refine ⟨bits (negative r),bits (positive r),hchange,?_⟩
  rw [hqneg,hqpos]
  decide

end PEqualNP.Outside.L_meta_29920.Gate8


namespace PEqualNP.Outside.L_meta_29920.ReadOncePath
open PEqualNP.Outside.L_meta_29920.TightReadOnce

variable {n : ℕ} {S : Finset (Fin n)} {f : (Fin n → Bool) → Bool}

theorem ro_nonempty (h : RO S f) : S.Nonempty := by
  apply h (fun S _ => S.Nonempty)
  · intro i; exact Finset.singleton_nonempty i
  · intro A B a b hd ha hb
    exact ⟨ha.mono Finset.subset_union_left,ha.mono Finset.subset_union_left⟩

theorem ro_zero (h : RO S f) (x : Fin n → Bool) (hx : ∀ i ∈ S,x i=false) : f x=false := by
  apply h (fun S f => ∀ x, (∀ i ∈ S,x i=false) → f x=false) ?_ ?_ x hx
  · intro i x hx; exact hx i (Finset.mem_singleton_self _)
  · intro A B a b hd ha hb
    constructor <;> intro x hx
    · dsimp only
      rw [ha x (fun i hi => hx i (Finset.mem_union_left _ hi)),
        hb x (fun i hi => hx i (Finset.mem_union_right _ hi))]; rfl
    · dsimp only
      rw [ha x (fun i hi => hx i (Finset.mem_union_left _ hi)),
        hb x (fun i hi => hx i (Finset.mem_union_right _ hi))]; rfl

theorem ro_depends (h : RO S f) (x y : Fin n → Bool) (hx : ∀ i ∈ S,x i=y i) : f x=f y := by
  apply h (fun S f => ∀ x y, (∀ i ∈ S,x i=y i) → f x=f y) ?_ ?_ x y hx
  · intro i x y hx; exact hx i (Finset.mem_singleton_self _)
  · intro A B a b hd ha hb
    constructor <;> intro x y hx <;> dsimp only <;>
      rw [ha x y (fun i hi => hx i (Finset.mem_union_left _ hi)),
        hb x y (fun i hi => hx i (Finset.mem_union_right _ hi))]

theorem ro_mono (h : RO S f) (x y : Fin n → Bool)
    (hxy : ∀ i,x i=true → y i=true) (hf : f x=true) : f y=true := by
  apply h (fun _ f => ∀ x y, (∀ i,x i=true → y i=true) → f x=true → f y=true) ?_ ?_ x y hxy hf
  · intro i x y hxy hf; exact hxy i hf
  · intro A B a b hd ha hb
    constructor
    · intro x y hxy hf
      simp only [Bool.and_eq_true] at hf ⊢
      exact ⟨ha x y hxy hf.1,hb x y hxy hf.2⟩
    · intro x y hxy hf
      simp only [Bool.or_eq_true] at hf ⊢
      exact hf.elim (fun h => Or.inl (ha x y hxy h)) (fun h => Or.inr (hb x y hxy h))

theorem ro_split (h : RO S f) :
    (∃ i : Fin n,S={i} ∧ f=(fun x => x i)) ∨
    ∃ A B a b, Disjoint A B ∧ S=A∪B ∧ RO A a ∧ RO B b ∧
      (f=(fun x => a x && b x) ∨ f=(fun x => a x || b x)) := by
  let Q := fun S f => RO S f ∧
    ((∃ i : Fin n,S={i} ∧ f=(fun x => x i)) ∨
    ∃ A B a b, Disjoint A B ∧ S=A∪B ∧ RO A a ∧ RO B b ∧
      (f=(fun x => a x && b x) ∨ f=(fun x => a x || b x)))
  have hQ : Q S f := h Q (fun i => ⟨ro_leaf i,Or.inl ⟨i,rfl,rfl⟩⟩) (by
    intro A B a b hd ha hb
    constructor
    · exact ⟨ro_and hd ha.1 hb.1,Or.inr ⟨A,B,a,b,hd,rfl,ha.1,hb.1,Or.inl rfl⟩⟩
    · exact ⟨ro_or hd ha.1 hb.1,Or.inr ⟨A,B,a,b,hd,rfl,ha.1,hb.1,Or.inr rfl⟩⟩)
  exact hQ.2

def pair (i j : Fin n) : Fin n → Bool := fun k => decide (k=i ∨ k=j)
def single (i : Fin n) : Fin n → Bool := fun k => decide (k=i)

theorem pair_comm (i j : Fin n) : pair i j=pair j i := by funext k; simp [pair,or_comm]

theorem pair_zero (h : RO S f) (i j : Fin n) (hi : i ∉ S) (hj : j ∉ S) : f (pair i j)=false := by
  apply ro_zero h
  intro k hk
  simp only [pair,decide_eq_false_iff_not,not_or]
  exact ⟨fun hki => hi (hki ▸ hk),fun hkj => hj (hkj ▸ hk)⟩

theorem pair_left (h : RO S f) (i j : Fin n) (hj : j ∉ S) :
    f (pair i j)=f (single i) := by
  apply ro_depends h
  intro k hk
  have hkj : k≠j := fun hkj => hj (hkj ▸ hk)
  simp [pair,single,hkj]

theorem pair_right (h : RO S f) (i j : Fin n) (hi : i ∉ S) :
    f (pair i j)=f (single j) := by rw [pair_comm]; exact pair_left h j i hi

def E : Finset (Fin 7) := Finset.univ.erase 0
def lo (e : Fin 5) : Fin 7 := ⟨e.val+1,by omega⟩
def hi (e : Fin 5) : Fin 7 := ⟨e.val+2,by omega⟩
def negatives : Fin 4 → Fin 7 × Fin 7 := ![(1,3),(1,4),(1,5),(2,6)]

theorem path_connected : ∀ c : Fin 7 → Bool,
    (∀ e : Fin 5,c (lo e)=c (hi e)) →
    ∀ i j : Fin 7,i≠0 → j≠0 → c i=c j := by decide +kernel

theorem path_alternating : ∀ c : Fin 7 → Bool,
    (∀ e : Fin 5,c (lo e)≠c (hi e)) → c 1≠c 4 := by decide +kernel

theorem vertex_negative : ∀ i : Fin 7,i≠0 → ∃ p : Fin 4,
    ∀ j : Fin 7,single i j=true → pair (negatives p).1 (negatives p).2 j=true := by decide +kernel

theorem no_path_ro (f : (Fin 7 → Bool) → Bool) (hf : RO E f)
    (hp : ∀ e : Fin 5,f (pair (lo e) (hi e))=true)
    (hn : ∀ p : Fin 4,f (pair (negatives p).1 (negatives p).2)=false) : False := by
  have hs : ∀ i : Fin 7,i≠0 → f (single i)=false := by
    intro i hi
    obtain ⟨p,hp⟩ := vertex_negative i hi
    cases hh : f (single i) with
    | false => rfl
    | true =>
      have h := ro_mono hf _ _ hp hh
      rw [hn p] at h
      contradiction
  rcases ro_split hf with ⟨i,hE,hf⟩ | ⟨A,B,a,b,hd,hE,ha,hb,hf⟩
  · have hc : E.card=6 := by decide
    rw [hE] at hc
    simp at hc
  have hAm : ∀ i∈A,i≠0 := by
    intro i hi
    have hiE : i∈E := hE ▸ Finset.mem_union_left B hi
    exact (Finset.mem_erase.mp hiE).1
  have hBm : ∀ i∈B,i≠0 := by
    intro i hi
    have hiE : i∈E := hE ▸ Finset.mem_union_right A hi
    exact (Finset.mem_erase.mp hiE).1
  have hab : ∀ i∈A,i∉B := fun i hi => Finset.disjoint_left.mp hd hi
  have hba : ∀ i∈B,i∉A := fun i hi => Finset.disjoint_right.mp hd hi
  have hcover : ∀ i : Fin 7,i≠0 → i∈A ∨ i∈B := by
    intro i hi
    have hiE : i∈E := by simp [E,hi]
    rw [hE] at hiE
    exact Finset.mem_union.mp hiE
  let c : Fin 7 → Bool := fun i => decide (i∈A)
  have hcolor : ∀ i : Fin 7,c i=true ↔ i∈A := by intro i; simp [c]
  have hcolor' : ∀ i : Fin 7,c i=false ↔ i∉A := by intro i; simp [c]
  rcases hf with hf | hf
  · have hedge : ∀ e : Fin 5,c (lo e)≠c (hi e) := by
      intro e heq
      have hp' := hp e
      rw [hf] at hp'
      by_cases hl : lo e∈A
      · have hh : hi e∈A := (hcolor _).mp (heq ▸ (hcolor _).mpr hl)
        have hz := pair_zero hb (lo e) (hi e) (hab _ hl) (hab _ hh)
        simp only [hz,Bool.and_false] at hp'
        contradiction
      · have hh : hi e∉A := (hcolor' _).mp (heq ▸ (hcolor' _).mpr hl)
        have hz := pair_zero ha (lo e) (hi e) hl hh
        simp only [hz,Bool.false_and] at hp'
        contradiction
    have h14 := path_alternating c hedge
    have h12 := hedge 0
    have h34 := hedge 2
    change c 1≠c 2 at h12
    change c 3≠c 4 at h34
    have hp12 := hp 0
    have hp34 := hp 2
    change f (pair 1 2)=true at hp12
    change f (pair 3 4)=true at hp34
    have hn14 := hn 1
    change f (pair 1 4)=false at hn14
    rw [hf] at hp12 hp34 hn14
    dsimp only at hp12 hp34 hn14
    by_cases h1 : (1 : Fin 7)∈A
    · have h2 : (2 : Fin 7)∉A := by intro h2; exact h12 ((hcolor _).mpr h1 |>.trans ((hcolor _).mpr h2).symm)
      have h4 : (4 : Fin 7)∉A := by intro h4; exact h14 ((hcolor _).mpr h1 |>.trans ((hcolor _).mpr h4).symm)
      have h3 : (3 : Fin 7)∈A := by
        by_contra h3
        exact h34 ((hcolor' _).mpr h3 |>.trans ((hcolor' _).mpr h4).symm)
      have h3B := hab 3 h3
      have h1B := hab 1 h1
      rw [pair_left ha 1 2 h2] at hp12
      rw [pair_right hb 3 4 h3B] at hp34
      rw [pair_left ha 1 4 h4,pair_right hb 1 4 h1B] at hn14
      simp only [Bool.and_eq_true] at hp12 hp34
      rw [hp12.1,hp34.2] at hn14
      contradiction
    · have h2 : (2 : Fin 7)∈A := by
        by_contra h2
        exact h12 ((hcolor' _).mpr h1 |>.trans ((hcolor' _).mpr h2).symm)
      have h4 : (4 : Fin 7)∈A := by
        by_contra h4
        exact h14 ((hcolor' _).mpr h1 |>.trans ((hcolor' _).mpr h4).symm)
      have h3 : (3 : Fin 7)∉A := by intro h3; exact h34 ((hcolor _).mpr h3 |>.trans ((hcolor _).mpr h4).symm)
      have h2B := hab 2 h2
      have h4B := hab 4 h4
      rw [pair_right ha 3 4 h3] at hp34
      rw [pair_left hb 1 2 h2B] at hp12
      rw [pair_right ha 1 4 h1,pair_left hb 1 4 h4B] at hn14
      simp only [Bool.and_eq_true] at hp12 hp34
      rw [hp34.1,hp12.2] at hn14
      contradiction
  · have hedge : ∀ e : Fin 5,c (lo e)=c (hi e) := by
      intro e
      have hl0 : lo e≠0 := by
        intro h; have h := congrArg Fin.val h; change e.val+1=0 at h; omega
      have hh0 : hi e≠0 := by
        intro h; have h := congrArg Fin.val h; change e.val+2=0 at h; omega
      have hsl := hs (lo e) hl0
      have hsh := hs (hi e) hh0
      have hp' := hp e
      rw [hf] at hsl hsh hp'
      dsimp only at hsl hsh hp'
      simp only [Bool.or_eq_false_iff] at hsl hsh
      by_cases hl : lo e∈A
      · by_cases hh : hi e∈A
        · exact ((hcolor _).mpr hl).trans ((hcolor _).mpr hh).symm
        · have hlB := hab _ hl
          rw [pair_left ha _ _ hh,pair_right hb _ _ hlB,hsl.1,hsh.2] at hp'
          contradiction
      · by_cases hh : hi e∈A
        · have hhB := hab _ hh
          rw [pair_right ha _ _ hl,pair_left hb _ _ hhB,hsh.1,hsl.2] at hp'
          contradiction
        · exact ((hcolor' _).mpr hl).trans ((hcolor' _).mpr hh).symm
    obtain ⟨u,hu⟩ := ro_nonempty ha
    obtain ⟨v,hv⟩ := ro_nonempty hb
    have hh := path_connected c hedge u v (hAm u hu) (hBm v hv)
    rw [(hcolor _).mpr hu,(hcolor' _).mpr (hba v hv)] at hh
    contradiction

end PEqualNP.Outside.L_meta_29920.ReadOncePath


namespace PEqualNP.Outside.L_meta_29920.Gate8Extension
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_29920.InternalMask PEqualNP.Outside.L_meta_29920.Gate8
open PEqualNP.Outside.L_meta_29920.TightReadOnce PEqualNP.Outside.L_meta_29920.ReadOncePath

theorem positive_facts : ∀ e : Fin 5,
    pair (lo e) (hi e) 0=false ∧ cycle7 (pair (lo e) (hi e))=true := by decide +kernel

theorem negative_facts : ∀ p : Fin 4,
    cycle7 (pair (negatives p).1 (negatives p).2)=false ∧
    cycle7 (Function.update (pair (negatives p).1 (negatives p).2) 0 true)=true := by decide +kernel

theorem no_partner_five (C : Circuit) (i k : Fin C.gates.length)
    (hi : i.val = 8) (hsize : C.size = 10)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hc : ∀ x : Fin 7 → Bool,C.eval (List.ofFn x)=cycle7 x)
    (hread : 0∈(C.gates.get i).inputs)
    (hunique : ∀ q : Fin C.gates.length,0∈(C.gates.get q).inputs → q=i)
    (hop : (C.gates.get i).op=.or)
    (hkop : (C.gates.get k).op=.and) (hik : i.val<k.val)
    (hreadik : 7+i.val∈(C.gates.get k).inputs)
    (hpartner : 11∈(C.gates.get i).inputs) : False := by
  have hj0 : (11 : Nat)≠0 := by decide
  have hjl : 11<7+i.val := by omega
  have hlen : C.gates.length=10 := hsize
  have hfan' : ∀ g∈C.gates,g.inputs.length≤2 := fun g hg => (hfan g hg).2
  have hfan'' : ∀ g∈C.gates,(g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2 := by
    intro g hg
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hfan g hg
  have hsens := partner_sensitive C i k 11 hi hsize hfan' hc hread hunique hop
    hkop hik hreadik hpartner hj0 hjl
  have hRO := wire_read_once C 7 5 11 (by omega) (by omega) hfan'' E (by decide)
    (fun r hr => hsens r (Finset.mem_erase.mp hr).1)
  apply no_path_ro (fun x => (C.wires (List.ofFn x)).getD 11 false) hRO
  · intro e
    obtain ⟨hx0,hxc⟩ := positive_facts e
    exact partner_true_on_positive C i k 11 hi hsize hfan' hc hread hunique hop
      hkop hik hreadik hpartner hj0 hjl _ hx0 hxc
  · intro p
    let x := pair (negatives p).1 (negatives p).2
    let y := Function.update x 0 true
    obtain ⟨hxf,hyf⟩ := negative_facts p
    change (C.wires (List.ofFn x)).getD 11 false=false
    cases hv : (C.wires (List.ofFn x)).getD 11 false with
    | false => rfl
    | true =>
      have hxy : ∀ s : Fin 7,s≠0 → x s=y s := by
        intro s hs; simp [y,Function.update_of_ne hs]
      have he := circuit_collision_of_one_true C i 11 (List.ofFn x) (List.ofFn y)
        (by simp) (ofFn_agree_zero _ _ hxy) hv hunique hop hpartner
        (by simpa only [List.length_ofFn] using hjl) hj0 (output_nonzero C hc)
      rw [hc,hc,hxf,hyf] at he
      cases he

end PEqualNP.Outside.L_meta_29920.Gate8Extension

theorem PEqualNP.Outside.L_meta_29920 :
¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 8 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 11 ∈ (C.gates.get i).inputs ∧ 11 ≠ 0 ∧ 11 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 11 false = true) := by
  rintro ⟨C,i,k,hi,hfan,hsize,hc,hread,hunique,hop,hkop,hik,hreadik,hpartner,hj0,hjl,hx⟩
  exact PEqualNP.Outside.L_meta_29920.Gate8Extension.no_partner_five C i k hi hsize hfan hc hread hunique hop
    hkop hik hreadik hpartner
