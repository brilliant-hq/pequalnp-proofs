import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7161_2
    (h1 : let star := fun (j l : ℕ) =>
      let a := fun d => (13 + d - l) % 13
      let w := 26 + 4*j
      ([(true,a 0,a 1),(true,a 3,a 9),(true,w,w+1),(false,13+l,w+2)] : List (Bool × ℕ × ℕ))
    let gs := (List.range 7).flatMap (fun j => star j (([5,6,7,8,10,11,12] : List ℕ).getD j 0)) ++
      (List.range 6).map (fun j => (true, if j = 0 then 29 else 53+j, 33+4*j))
    let P : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨gs.map (fun (b,i,j) => ⟨if b then .or else .and,[i,j]⟩),59⟩
    let R : List (Fin 13) := [0,1,3,9,2,4]
    let e := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
    let v := PEqualNP.GenericRejection.incidenceInput (n := 13) (m := 13)
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      D.size ≤ 28 ∧ 59 < D.output ∧
      ∀ s t : Finset (Fin 13), D.eval (P.wires (v s t)) = true ↔
        ∃ p ∈ s, ∃ l ∈ t, l ∈ R ∧ e p l)
    (h2 : let star := fun (j l : ℕ) =>
      let a := fun d => (13 + d - l) % 13
      let w := 26 + 4*j
      ([(true,a 0,a 1),(true,a 3,a 9),(true,w,w+1),(false,13+l,w+2)] : List (Bool × ℕ × ℕ))
    let gs := (List.range 7).flatMap (fun j => star j (([5,6,7,8,10,11,12] : List ℕ).getD j 0)) ++
      (List.range 6).map (fun j => (true, if j = 0 then 29 else 53+j, 33+4*j))
    let P : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨gs.map (fun (b,i,j) => ⟨if b then .or else .and,[i,j]⟩),59⟩
    let R : List (Fin 13) := [0,1,3,9,2,4]
    let e := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
    let v := PEqualNP.GenericRejection.incidenceInput (n := 13) (m := 13)
    let off := fun s : Finset (Fin 13) => Finset.univ.filter fun l => ∀ p ∈ s, ¬ e p l
    PEqualNP.MetaComplexity.Monotone2 P ∧ P.size = 34 ∧
      (∀ p l : Fin 13, l ∉ R → e p l → P.eval (v {p} {l}) = true) ∧
      ∀ s : Finset (Fin 13), s.card ≤ 3 →
        P.eval (v s (off s)) = false ∧ P.eval (v (off s) s) = false) :
    let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x2 : Finset (Fin (13 : ℕ))) => {x3 : Fin (13 : ℕ) | ∀ x4 ∈ x2, ¬x1 x4 x3}; have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x3 x4 : Finset (Fin (13 : ℕ))) => List.ofFn fun (x5 : Fin (26 : ℕ)) => if ↑x5 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x3) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x4); ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) (x6 : ℕ) (x7 : Bool),   PEqualNP.MetaComplexity.Monotone2 x4 ∧     x4.size ≤ (62 : ℕ) ∧       x5 < x6 ∧         have x8 : ℕ → Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x8 : ℕ) (x9 x10 : Finset (Fin (13 : ℕ))) => (x4.wires (x3 x9 x10)).getD x8 Bool.false;         have x9 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x9 x10 : Finset (Fin (13 : ℕ))) => (if x7 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or).eval [x8 x5 x9 x10, x8 x6 x9 x10];         (∀ (x10 x11 : Fin (13 : ℕ)), x1 x10 x11 → x9 {x10} {x11} = Bool.true) ∧ ∀ (x10 : Finset (Fin (13 : ℕ))), x10.card ≤ (3 : ℕ) → x9 x10 (x2 x10) = Bool.false ∧ x9 (x2 x10) x10 = Bool.false := by
  let star := fun (j l : ℕ) =>
    let a := fun d => (13 + d - l) % 13
    let w := 26 + 4*j
    ([(true,a 0,a 1),(true,a 3,a 9),(true,w,w+1),(false,13+l,w+2)] : List (Bool × ℕ × ℕ))
  let gs := (List.range 7).flatMap (fun j => star j (([5,6,7,8,10,11,12] : List ℕ).getD j 0)) ++
    (List.range 6).map (fun j => (true, if j = 0 then 29 else 53+j, 33+4*j))
  let P : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨gs.map (fun (b,i,j) => ⟨if b then .or else .and,[i,j]⟩),59⟩
  let R : List (Fin 13) := [0,1,3,9,2,4]
  let e := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
  let off := fun s : Finset (Fin 13) => Finset.univ.filter fun l => ∀ p ∈ s, ¬ e p l
  let v := PEqualNP.GenericRejection.incidenceInput (n := 13) (m := 13)
  obtain ⟨D, monoD, szD, ho, hsuffix⟩ := h1
  obtain ⟨monoP, szP, hpos, hneg⟩ := h2
  change PEqualNP.MetaComplexity.Monotone2 P at monoP
  change P.size = 34 at szP
  change (∀ s t : Finset (Fin 13), D.eval (P.wires (v s t)) = true ↔
    ∃ p ∈ s, ∃ l ∈ t, l ∈ R ∧ e p l) at hsuffix
  change (∀ p l : Fin 13, l ∉ R → e p l → P.eval (v {p} {l}) = true) at hpos
  change (∀ s : Finset (Fin 13), s.card ≤ 3 →
    P.eval (v s (off s)) = false ∧ P.eval (v (off s) s) = false) at hneg
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨P.gates ++ D.gates, 0⟩
  have monoC : PEqualNP.MetaComplexity.Monotone2 C := by
    intro g hg
    rcases List.mem_append.mp hg with hp | hd
    · exact monoP g hp
    · exact monoD g hd
  have szC : C.size ≤ 62 := by
    change (P.gates ++ D.gates).length ≤ 62
    change P.gates.length = 34 at szP
    change D.gates.length ≤ 28 at szD
    rw [List.length_append, szP]
    omega
  let f := fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have len (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
      (gs.foldl f w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => simp only [List.foldl_cons, ih, f, List.length_append, List.length_cons,
        List.length_nil]; omega
  have keep (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl f w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (f w g) (by simp [f]; omega)]
      exact List.getD_append _ _ _ _ hi
  have joined (s t : Finset (Fin 13)) : C.wires (v s t) = D.wires (P.wires (v s t)) := List.foldl_append
  have preserved (s t : Finset (Fin 13)) :
      (C.wires (v s t)).getD 59 false = P.eval (v s t) := by
    rw [joined]
    apply keep
    change 59 < (P.gates.foldl f (v s t)).length
    rw [len]
    change P.gates.length = 34 at szP
    rw [szP]
    simp [v, PEqualNP.GenericRejection.incidenceInput]
  have readout (s t : Finset (Fin 13)) :
      PEqualNP.CircuitLowerBounds.GateOp.or.eval
        [(C.wires (v s t)).getD 59 false, (C.wires (v s t)).getD D.output false] =
      (P.eval (v s t) || D.eval (P.wires (v s t))) := by
    rw [preserved, joined]
    simp [PEqualNP.CircuitLowerBounds.GateOp.eval, PEqualNP.CircuitLowerBounds.Circuit.eval]
  refine ⟨C, 59, D.output, false, monoC, szC, ho, ?_, ?_⟩
  · intro p l h
    change PEqualNP.CircuitLowerBounds.GateOp.or.eval
      [(C.wires (v {p} {l})).getD 59 false, (C.wires (v {p} {l})).getD D.output false] = true
    rw [readout, Bool.or_eq_true]
    by_cases hl : l ∈ R
    · exact Or.inr ((hsuffix _ _).mpr ⟨p, by simp, l, by simp, hl, h⟩)
    · exact Or.inl (hpos _ _ hl h)
  · intro s hs
    change PEqualNP.CircuitLowerBounds.GateOp.or.eval
        [(C.wires (v s (off s))).getD 59 false, (C.wires (v s (off s))).getD D.output false] = false ∧
      PEqualNP.CircuitLowerBounds.GateOp.or.eval
        [(C.wires (v (off s) s)).getD 59 false, (C.wires (v (off s) s)).getD D.output false] = false
    obtain ⟨ha, hb⟩ := hneg s hs
    have hn (u v' : Finset (Fin 13)) (no : ∀ p ∈ u, ∀ l ∈ v', ¬ e p l) :
        D.eval (P.wires (v u v')) = false := Bool.eq_false_iff.mpr fun h =>
      let ⟨p, hp, l, hl, _, hl'⟩ := (hsuffix _ _).mp h
      no p hp l hl hl'
    have c := hn s (off s) fun p hp l hl => (Finset.mem_filter.mp hl).2 p hp
    have d := hn (off s) s fun p hp l hl h => (Finset.mem_filter.mp hp).2 l hl
      (show e l p from by unfold e at h ⊢; rwa [Nat.add_comm])
    rw [readout, readout, ha, hb, c, d]
    exact ⟨rfl, rfl⟩
