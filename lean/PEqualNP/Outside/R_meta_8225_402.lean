import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8225_402
    (witness : ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x5]? = Option.some x6 → (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x8 : ℕ) (x9 : ℕ), x6.inputs = [x8, x9] ∧ x8 ≠ x9 ∧ x8 < (26 : ℕ) + x5 ∧ x9 < (26 : ℕ) + x5) ∧ (∀ (x5 : Fin (26 : ℕ) → Bool), x4.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) ∧ x4.size ≤ (64 : ℕ) ∧ PEqualNP.EdgeOwnership.HasStarProfile (26 : ℕ) (PEqualNP.EdgeOwnership.edgeGraph (26 : ℕ) (List.flatMap (fun (x6 : Fin (13 : ℕ)) => List.map (fun (x7 : Fin (13 : ℕ)) => (↑x6, (13 : ℕ) + ↑x7)) (List.filter (fun (x7 : Fin (13 : ℕ)) => Decidable.decide (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ)))) (List.finRange (13 : ℕ)))) (List.finRange (13 : ℕ)))) x4)
    (small : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → x1.size ≤ (63 : ℕ) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x5]? = Option.some x6 → (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x8 : ℕ) (x9 : ℕ), x6.inputs = [x8, x9] ∧ x8 ≠ x9 ∧ x8 < (26 : ℕ) + x5 ∧ x9 < (26 : ℕ) + x5) ∧ (∀ (x5 : Fin (26 : ℕ) → Bool), x4.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) ∧ x4.size ≤ x1.size ∧ PEqualNP.EdgeOwnership.HasStarProfile (26 : ℕ) (PEqualNP.EdgeOwnership.edgeGraph (26 : ℕ) (List.flatMap (fun (x6 : Fin (13 : ℕ)) => List.map (fun (x7 : Fin (13 : ℕ)) => (↑x6, (13 : ℕ) + ↑x7)) (List.filter (fun (x7 : Fin (13 : ℕ)) => Decidable.decide (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ)))) (List.finRange (13 : ℕ)))) (List.finRange (13 : ℕ)))) x4) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x5]? = Option.some x6 → (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x8 : ℕ) (x9 : ℕ), x6.inputs = [x8, x9] ∧ x8 ≠ x9 ∧ x8 < (26 : ℕ) + x5 ∧ x9 < (26 : ℕ) + x5) ∧ (∀ (x5 : Fin (26 : ℕ) → Bool), x4.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) ∧ x4.size ≤ x1.size ∧ ∃ (x5 : SimpleGraph (Fin (26 : ℕ))), x5 = PEqualNP.EdgeOwnership.edgeGraph (26 : ℕ) (List.flatMap (fun (x6 : Fin (13 : ℕ)) => List.map (fun (x7 : Fin (13 : ℕ)) => (↑x6, (13 : ℕ) + ↑x7)) (List.filter (fun (x7 : Fin (13 : ℕ)) => Decidable.decide (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ)))) (List.finRange (13 : ℕ)))) (List.finRange (13 : ℕ))) ∧ PEqualNP.EdgeOwnership.HasStarProfile (26 : ℕ) x5 x4 ∧ PEqualNP.EdgeOwnership.EveryEdgeOwned (26 : ℕ) x5 x4) := by
  intro C hgates heval
  have pref : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false
        = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons, ih _ i (by simp; omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have key : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (wx wy wz : List Bool),
      wy.length = wx.length → wz.length = wx.length →
      (∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      (∀ k, (gs.getD k ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op =
          PEqualNP.CircuitLowerBounds.GateOp.and → k < gs.length →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) wx).getD
          (wx.length + k) false = false) →
      (∀ i, wx.getD i false = true → wy.getD i false = true ∨ wz.getD i false = true) →
      ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) wx).getD i false = true →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) wy).getD i false = true ∨
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) wz).getD i false = true := by
    intro gs
    induction gs with
    | nil => intro wx wy wz _ _ _ _ hinv i hi; exact hinv i hi
    | cons g gs ih =>
      intro wx wy wz hy hz hops hand hinv
      rw [List.foldl_cons, List.foldl_cons, List.foldl_cons]
      have hg := hops g List.mem_cons_self
      have hgx : g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
          g.op.eval (g.inputs.map fun i => wx.getD i false) = false := by
        intro ha
        have h0 := hand 0 (by simpa using ha) (by simp)
        rw [List.foldl_cons, Nat.add_zero, pref _ _ _ (by simp)] at h0
        simpa [List.getD_eq_getElem?_getD] using h0
      apply ih _ _ _ (by simp [hy]) (by simp [hz]) (fun g' hg' => hops g' (List.mem_cons_of_mem _ hg'))
      · intro k hk hlt
        have h1 := hand (k + 1) (by simpa using hk) (by simp; omega)
        rw [List.foldl_cons] at h1
        simpa [Nat.add_assoc, Nat.add_comm 1 k] using h1
      · intro i hi
        rcases lt_trichotomy i wx.length with h | h | h
        · have hyl : i < wy.length := hy ▸ h
          have hzl : i < wz.length := hz ▸ h
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h,
            List.getElem?_append_left hyl, List.getElem?_append_left hzl] at hi ⊢
          have := hinv i
          simpa [List.getD_eq_getElem?_getD] using this hi
        · subst h
          have hl : ∀ (l : List Bool) (e : Bool), (l ++ [e]).getD l.length false = e := by
            intro l e; simp [List.getD_eq_getElem?_getD]
          rw [hl] at hi
          rw [show wx.length = wy.length from hy.symm, hl,
            show wy.length = wz.length from hy.trans hz.symm, hl]
          rcases hg with ha | ho
          · rw [hgx ha] at hi; exact absurd hi (by simp)
          · rw [ho] at hi ⊢
            simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_map, List.any_eq_true,
              Function.comp_apply] at hi ⊢
            obtain ⟨a, ha, hav⟩ := hi
            rcases hinv a (by simpa using hav) with h' | h'
            · exact Or.inl ⟨a, ha, by simpa using h'⟩
            · exact Or.inr ⟨a, ha, by simpa using h'⟩
        · exfalso
          have hl : (wx ++ [g.op.eval (g.inputs.map fun i => wx.getD i false)]).length ≤ i := by
            simp; omega
          rw [List.getD_eq_default _ _ hl] at hi
          exact absurd hi (by simp)
  have owned : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), D.gates[x5]? = Option.some x6 → (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x8 : ℕ) (x9 : ℕ), x6.inputs = [x8, x9] ∧ x8 ≠ x9 ∧ x8 < (26 : ℕ) + x5 ∧ x9 < (26 : ℕ) + x5) →
      (∀ (x5 : Fin (26 : ℕ) → Bool), D.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) →
      PEqualNP.EdgeOwnership.EveryEdgeOwned (26 : ℕ) (PEqualNP.EdgeOwnership.edgeGraph (26 : ℕ) (List.flatMap (fun (x6 : Fin (13 : ℕ)) => List.map (fun (x7 : Fin (13 : ℕ)) => (↑x6, (13 : ℕ) + ↑x7)) (List.filter (fun (x7 : Fin (13 : ℕ)) => Decidable.decide (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ)))) (List.finRange (13 : ℕ)))) (List.finRange (13 : ℕ)))) D := by
    intro D hg he u v hadj
    classical
    by_contra hno
    have hfalse : ∀ j, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op =
        PEqualNP.CircuitLowerBounds.GateOp.and → j < D.gates.length →
        PEqualNP.EdgeOwnership.gateVal 26 D j (PEqualNP.EdgeOwnership.pairInput u v) = false := by
      intro j
      induction j using Nat.strong_induction_on with
      | _ j ihj =>
        intro hand hlt
        by_contra hT
        rw [Bool.not_eq_false] at hT
        exact hno ⟨j, hlt, hlt, hand, hT, fun i hij _ hai => ihj i hij hai (by omega)⟩
    have hops : ∀ g ∈ D.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
      intro g hmem
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hmem
      exact (hg k g hk).1
    have single : ∀ w : Fin 26, D.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput w w)) = false := by
      intro w
      by_contra hT
      rw [Bool.not_eq_false] at hT
      obtain ⟨p, l, _, hp, hl⟩ := (he _).mp hT
      simp only [PEqualNP.EdgeOwnership.pairInput, or_self, decide_eq_true_eq] at hp hl
      have h1 := congrArg Fin.val hp
      have h2 := congrArg Fin.val hl
      simp [Fin.castAdd, Fin.natAdd] at h1 h2
      omega
    have edge : D.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) = true := by
      apply (he _).mpr
      obtain ⟨hne, hmem⟩ := hadj
      rcases hmem with hm | hm
      · simp only [List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
          decide_eq_true_eq, Prod.mk.injEq] at hm
        obtain ⟨p, l, hI, hpu, hlv⟩ := hm
        refine ⟨p, l, hI, ?_, ?_⟩
        · simp [PEqualNP.EdgeOwnership.pairInput]; left; ext; simp [Fin.castAdd]; omega
        · simp [PEqualNP.EdgeOwnership.pairInput]; right; ext; simp [Fin.natAdd]; omega
      · simp only [List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
          decide_eq_true_eq, Prod.mk.injEq] at hm
        obtain ⟨p, l, hI, hpu, hlv⟩ := hm
        refine ⟨p, l, hI, ?_, ?_⟩
        · simp [PEqualNP.EdgeOwnership.pairInput]; right; ext; simp [Fin.castAdd]; omega
        · simp [PEqualNP.EdgeOwnership.pairInput]; left; ext; simp [Fin.natAdd]; omega
    have res := key D.gates (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))
      (List.ofFn (PEqualNP.EdgeOwnership.pairInput u u)) (List.ofFn (PEqualNP.EdgeOwnership.pairInput v v))
      (by simp) (by simp) hops
      (by
        intro k hk hlt
        have := hfalse k hk hlt
        simpa [PEqualNP.EdgeOwnership.gateVal, PEqualNP.CircuitLowerBounds.Circuit.wires] using this)
      (by
        intro i hi
        by_cases hi26 : i < 26
        · have e : ∀ f : Fin 26 → Bool, (List.ofFn f).getD i false = f ⟨i, hi26⟩ := by
            intro f; rw [List.getD_eq_getElem _ _ (by simpa using hi26)]; simp only [List.getElem_ofFn]
          rw [e] at hi
          rw [e, e]
          simp only [PEqualNP.EdgeOwnership.pairInput, or_self, decide_eq_true_eq] at hi ⊢
          exact hi
        · exfalso
          rw [List.getD_eq_default _ _ (by simp; omega)] at hi
          exact absurd hi (by simp))
      D.output edge
    rcases res with h | h
    · have h0 := single u
      simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires] at h0
      rw [h0] at h; exact absurd h (by simp)
    · have h0 := single v
      simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires] at h0
      rw [h0] at h; exact absurd h (by simp)
  by_cases hs : C.size ≤ 63
  · obtain ⟨D, hD1, hD2, hD3, hD4⟩ := small C hgates heval hs
    exact ⟨D, hD1, hD2, hD3, _, rfl, hD4, owned D hD1 hD2⟩
  · obtain ⟨D, hD1, hD2, hD3, hD4⟩ := witness
    exact ⟨D, hD1, hD2, by unfold PEqualNP.CircuitLowerBounds.Circuit.size at *; omega, _, rfl, hD4, owned D hD1 hD2⟩
