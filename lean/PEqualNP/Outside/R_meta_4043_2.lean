import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_4043_2
    (hFlat : ∀ (C : Circuit) (x2 : Fin 26), Monotone2 C → ReadsBack 26 C →
      (¬ ∃ i j : ℕ, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧ InCone 26 C i j) →
      (∀ (x4 : Fin 26 → Bool), x4 x2 = Bool.false →
        (C.eval (List.ofFn x4) = Bool.true ↔
          ∃ (x6 x7 : Fin 13), (x6 = x7 ∨ x6 = x7 + 1 ∨ x6 = x7 + 3 ∨ x6 = x7 + 9) ∧
            x4 (Fin.castAdd 13 x6) = Bool.true ∧ x4 (Fin.natAdd 13 x7) = Bool.true)) →
      58 ≤ C.size)
    (hNested : ∀ (C : Circuit) (x2 : Fin 26), Monotone2 C → ReadsBack 26 C →
      (∃ i j : ℕ, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧ InCone 26 C i j) →
      (∀ (x4 : Fin 26 → Bool), x4 x2 = Bool.false →
        (C.eval (List.ofFn x4) = Bool.true ↔
          ∃ (x6 x7 : Fin 13), (x6 = x7 ∨ x6 = x7 + 1 ∨ x6 = x7 + 3 ∨ x6 = x7 + 9) ∧
            x4 (Fin.castAdd 13 x6) = Bool.true ∧ x4 (Fin.natAdd 13 x7) = Bool.true)) →
      58 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (26 : ℕ)), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x4 : Fin (26 : ℕ) → Bool), x4 x2 = Bool.false → (x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x4 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x7) = Bool.true)) → (58 : ℕ) ≤ x1.size := by
  classical
  intro C x2 hMono hSpec
  let cleanGate : ℕ → Gate → Gate := fun bound g =>
    if g.op = GateOp.and then
      if g.inputs.all (fun i => decide (i < bound)) then g else ⟨GateOp.or, []⟩
    else
      ⟨g.op, g.inputs.filter (fun i => decide (i < bound))⟩
  let D : Circuit := ⟨C.gates.mapIdx (fun j g => cleanGate (26 + j) g), C.output⟩
  have hSize : D.size = C.size := by simp [D, Circuit.size]
  have hCleanMono : Monotone2 D := by
    intro g hg
    simp only [D, List.mem_mapIdx] at hg
    rcases hg with ⟨j, hj, rfl⟩
    have hg' := hMono C.gates[j] (List.getElem_mem hj)
    dsimp [cleanGate]
    split_ifs
    · exact hg'
    · exact ⟨by simp, by simp⟩
    · exact ⟨hg'.1, (List.length_filter_le _ _).trans hg'.2⟩
  have hBack : ReadsBack 26 D := by
    intro j hj i hi
    have hj' : j < C.gates.length := by simpa [D] using hj
    have hget : (gateAt D j) = cleanGate (26 + j) C.gates[j] := by
      simp [gateAt, D, hj']
    rw [hget] at hi
    dsimp [cleanGate] at hi
    split_ifs at hi with h1 h2
    · simp only [List.all_eq_true, decide_eq_true_eq] at h2
      exact h2 i hi
    · simp at hi
    · simp only [List.mem_filter, decide_eq_true_eq] at hi
      exact hi.2
  have hWires : ∀ x : List Bool, x.length = 26 → D.wires x = C.wires x := by
    intro x hx
    have hFold : ∀ (gs : List Gate) (w : List Bool),
        (∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2) →
        (gs.mapIdx (fun j g => cleanGate (w.length + j) g)).foldl
          (fun w' g => w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]) w =
        gs.foldl (fun w' g => w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]) w := by
      intro gs
      induction gs with
      | nil => intro w _; simp
      | cons g gs ih =>
        intro w hgs
        have hgOp : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := (hgs g (by simp)).1
        simp only [List.mapIdx_cons, Nat.add_zero, List.foldl_cons]
        have hEq : (cleanGate w.length g).op.eval ((cleanGate w.length g).inputs.map fun i => w.getD i false) =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          dsimp [cleanGate]
          split_ifs with h1 h2
          · rfl
          · rw [h1]
            simp only [GateOp.eval, List.all_eq_true, decide_eq_true_eq, not_forall, not_lt,
              List.map_nil, List.any_nil] at h2 ⊢
            rcases h2 with ⟨k, hk, hle⟩
            have hfalse : (w.getD k false) = false := List.getD_eq_default w false hle
            symm
            rw [List.all_eq_false]
            exact ⟨false, List.mem_map.mpr ⟨k, hk, hfalse⟩, by simp⟩
          · rcases hgOp with hAnd | hOr
            · exact absurd hAnd h1
            · rw [hOr]
              simp only [GateOp.eval]
              have hAny : ∀ l : List ℕ,
                  (List.map (fun i => w.getD i false) (l.filter (fun i => decide (i < w.length)))).any id =
                  (List.map (fun i => w.getD i false) l).any id := by
                intro l
                induction l with
                | nil => simp
                | cons a as ihl =>
                  by_cases ha : a < w.length
                  · simp only [List.filter_cons, ha, decide_true, ↓reduceIte, List.map_cons, List.any_cons, id_eq]
                    rw [ihl]
                  · have hget : w.getD a false = false := List.getD_eq_default w false (Nat.le_of_not_lt ha)
                    simp only [List.filter_cons, ha, decide_false, Bool.false_eq_true, ↓reduceIte, List.map_cons,
                      List.any_cons, id_eq, hget, Bool.false_or]
                    exact ihl
              exact hAny g.inputs
        rw [hEq]
        have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (fun g' hg' => hgs g' (by simp [hg']))
        simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
    have := hFold C.gates x hMono
    rw [hx] at this
    exact this
  by_cases hN : ∃ i j : ℕ, (gateAt D i).op = GateOp.and ∧ (gateAt D j).op = GateOp.and ∧ InCone 26 D i j
  · have := hNested D x2 hCleanMono hBack hN (fun x4 hx4 => by
      have hev : D.eval (List.ofFn x4) = C.eval (List.ofFn x4) := by
        unfold Circuit.eval
        rw [hWires (List.ofFn x4) (by simp)]
      rw [hev]; exact hSpec x4 hx4)
    omega
  · have := hFlat D x2 hCleanMono hBack hN (fun x4 hx4 => by
      have hev : D.eval (List.ofFn x4) = C.eval (List.ofFn x4) := by
        unfold Circuit.eval
        rw [hWires (List.ofFn x4) (by simp)]
      rw [hev]; exact hSpec x4 hx4)
    omega
