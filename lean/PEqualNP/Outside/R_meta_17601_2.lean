import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17601_2
    (h1 : let S := PEqualNP.HeptadCover.singerLines3
    let row (A B : Finset (Fin 13)) := PEqualNP.GenericRejection.incidenceInput A B
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (s : List ℕ) (p l : Fin 13),
    s.length ≤ 2 → (∀ i ∈ s, i < 26) → p ∈ S l → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack 28 C →
    let ev (A B : Finset (Fin 13)) (b : Bool) := C.eval (row A B ++ [s.any fun i => (row A B).getD i false] ++ [b])
    (∀ i j, i ∈ S j → ev {i} {j} (decide (i=p ∧ j=l)) = true) →
    (∀ Q, PEqualNP.HeptadCover.IsQuadrangle S Q → ev Q (PEqualNP.HeptadCover.missLines S Q) false = false) →
    ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (b : Bool), PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 D ∧
      (∀ i j, i ∈ S j → (b = true ∨ (i,j) ≠ ((0 : Fin 13), (0 : Fin 13))) → D.eval (row {i} {j}) = true) ∧
      (∀ Q, PEqualNP.HeptadCover.IsQuadrangle S Q → D.eval (row Q (PEqualNP.HeptadCover.missLines S Q)) = false) ∧
      D.size ≤ C.size + (if b then 1 else 0))
    (h2 : let S := PEqualNP.HeptadCover.singerLines3
    let row := @PEqualNP.GenericRejection.incidenceInput 13 13
    let G (b : Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) := PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C ∧
      (∀ i j, i ∈ S j → (b = true ∨ (i,j) ≠ ((0 : Fin 13),0)) → C.eval (row {i} {j}) = true) ∧ (∀ Q, PEqualNP.HeptadCover.IsQuadrangle S Q → C.eval (row Q (PEqualNP.HeptadCover.missLines S Q)) = false)
    let packed (C : PEqualNP.CircuitLowerBounds.Circuit) :=
      let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
      let v (x : List Bool) (i : ℕ) := (C.wires x).getD i false
      let born (g : ℕ) (x : List Bool) := ∀ a ∈ (gate g).inputs, ∃ i ∈ PEqualNP.TopForm.orIn 26 C a, x.getD i.val false = true
      ∃ U ⊆ PEqualNP.HeptadCover.incidences S, ∃ w : Fin 13 × Fin 13 → ℕ, (U.image w).card + 3 ≤ U.card ∧
        ∀ g ∈ U.image w, ∃ Q : Finset (Fin 13), let y := row Q (PEqualNP.HeptadCover.missLines S Q)
          (gate g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.HeptadCover.IsQuadrangle S Q ∧ born g y ∧ (gate g).inputs.toFinset.card = 2 ∧
          ∀ t ∈ U, w t = g → let x := row {t.1} {t.2}; born g x ∧ ∃ j > g, (gate j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
            v x (26+j) = true ∧ (∃ a ∈ (gate j).inputs, v y a = true) ∧ ∃ a ∈ (gate j).inputs, v y a = false
    ∀ b C, G b C → (∀ D, G b D → C.size ≤ D.size) → C.size < (if b then 63 else 62) → 2 ≤ PEqualNP.TopForm.andPairs 26 C ∧ packed C)
    (h3 : let S := PEqualNP.HeptadCover.singerLines3
    let row := @PEqualNP.GenericRejection.incidenceInput 13 13
    let G (C : PEqualNP.CircuitLowerBounds.Circuit) := PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C ∧
      (∀ i j, i ∈ S j → C.eval (row {i} {j}) = true) ∧ (∀ Q, PEqualNP.HeptadCover.IsQuadrangle S Q → C.eval (row Q (PEqualNP.HeptadCover.missLines S Q)) = false)
    let packed (C : PEqualNP.CircuitLowerBounds.Circuit) :=
      let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
      let v (x : List Bool) (i : ℕ) := (C.wires x).getD i false
      let born (g : ℕ) (x : List Bool) := ∀ a ∈ (gate g).inputs, ∃ i ∈ PEqualNP.TopForm.orIn 26 C a, x.getD i.val false = true
      ∃ U ⊆ PEqualNP.HeptadCover.incidences S, ∃ w : Fin 13 × Fin 13 → ℕ, (U.image w).card + 3 ≤ U.card ∧
        ∀ g ∈ U.image w, ∃ Q : Finset (Fin 13), let y := row Q (PEqualNP.HeptadCover.missLines S Q)
          (gate g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.HeptadCover.IsQuadrangle S Q ∧ born g y ∧ (gate g).inputs.toFinset.card = 2 ∧
          ∀ t ∈ U, w t = g → let x := row {t.1} {t.2}; born g x ∧ ∃ j > g, (gate j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
            v x (26+j) = true ∧ (∃ a ∈ (gate j).inputs, v y a = true) ∧ ∃ a ∈ (gate j).inputs, v y a = false
    ∀ C, G C → (∀ D, G D → C.size ≤ D.size) →
      (∀ D, G D → D.size = C.size → PEqualNP.TopForm.andPairs 26 C ≤ PEqualNP.TopForm.andPairs 26 D) →
      2 ≤ PEqualNP.TopForm.andPairs 26 C → packed C → 63 ≤ C.size)
    (h4 : let S := PEqualNP.HeptadCover.singerLines3
    let row := @PEqualNP.GenericRejection.incidenceInput 13 13
    let G (C : PEqualNP.CircuitLowerBounds.Circuit) := PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C ∧
      (∀ i j, i ∈ S j → (i,j) ≠ ((0 : Fin 13),0) → C.eval (row {i} {j}) = true) ∧ (∀ Q, PEqualNP.HeptadCover.IsQuadrangle S Q → C.eval (row Q (PEqualNP.HeptadCover.missLines S Q)) = false)
    let packed (C : PEqualNP.CircuitLowerBounds.Circuit) :=
      let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
      let v (x : List Bool) (i : ℕ) := (C.wires x).getD i false
      let born (g : ℕ) (x : List Bool) := ∀ a ∈ (gate g).inputs, ∃ i ∈ PEqualNP.TopForm.orIn 26 C a, x.getD i.val false = true
      ∃ U ⊆ PEqualNP.HeptadCover.incidences S, ∃ w : Fin 13 × Fin 13 → ℕ, (U.image w).card + 3 ≤ U.card ∧
        ∀ g ∈ U.image w, ∃ Q : Finset (Fin 13), let y := row Q (PEqualNP.HeptadCover.missLines S Q)
          (gate g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.HeptadCover.IsQuadrangle S Q ∧ born g y ∧ (gate g).inputs.toFinset.card = 2 ∧
          ∀ t ∈ U, w t = g → let x := row {t.1} {t.2}; born g x ∧ ∃ j > g, (gate j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
            v x (26+j) = true ∧ (∃ a ∈ (gate j).inputs, v y a = true) ∧ ∃ a ∈ (gate j).inputs, v y a = false
    ∀ C, G C → (∀ D, G D → C.size ≤ D.size) →
      (∀ D, G D → D.size = C.size → PEqualNP.TopForm.andPairs 26 C ≤ PEqualNP.TopForm.andPairs 26 D) →
      2 ≤ PEqualNP.TopForm.andPairs 26 C → packed C → 62 ≤ C.size)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ) (x3 x4 : Fin (13 : ℕ)),   x2 ∈ [[], [(0 : ℕ)], [(13 : ℕ)], [(0 : ℕ), (1 : ℕ)], [(13 : ℕ), (14 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)]] →     x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 →       have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool → Bool := fun (x7 x8 : Finset (Fin (13 : ℕ))) (x9 : Bool) =>         have x10 : List Bool := PEqualNP.GenericRejection.incidenceInput x7 x8;         x1.eval (x10 ++ [x2.any fun (x11 : ℕ) => x10.getD x11 Bool.false] ++ [x9]);       PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (28 : ℕ) x1 → (∀ (x10 x11 : Fin (13 : ℕ)), x10 ∈ PEqualNP.HeptadCover.singerLines3 x11 → x7 {x10} {x11} (Decidable.decide (x10 = x3 ∧ x11 = x4)) = Bool.true) → (∀ (x11 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x11 → x7 x11 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x11) Bool.false = Bool.false) → (62 : ℕ) ≤ x1.size := open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.HeptadCover PEqualNP.GenericRejection in by
  classical
  intro C s p l hs hedge ev hm hr hp hq
  have hvalid : s.length ≤ 2 ∧ ∀ i ∈ s, i < 26 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨D,b,hmD,hrD,hpD,hqD,hlen⟩ := h1 C s p l hvalid.1 hvalid.2 hedge hm hr hp hq
  let e (C : Circuit) (A B : Finset (Fin 13)) := C.eval (incidenceInput A B)
  let G (b : Bool) (C : Circuit) := Monotone2 C ∧ ReadsBack 26 C ∧
    (∀ i j, i ∈ singerLines3 j → (b = true ∨ (i,j) ≠ ((0 : Fin 13), (0 : Fin 13))) → e C {i} {j} = true) ∧
    (∀ Q, IsQuadrangle singerLines3 Q → e C Q (missLines singerLines3 Q) = false)
  have hGD : G b D := ⟨hmD,hrD,hpD,hqD⟩
  have exsize : ∃ n, ∃ E, G b E ∧ E.size = n := ⟨_,D,hGD,rfl⟩
  obtain ⟨D0,h0,hn⟩ := Nat.find_spec exsize
  have expair : ∃ k, ∃ E, G b E ∧ E.size = Nat.find exsize ∧ andPairs 26 E = k := ⟨_,D0,h0,hn,rfl⟩
  obtain ⟨E,hE,hsize,hpair⟩ := Nat.find_spec expair
  have minS (F : Circuit) (hF : G b F) : E.size ≤ F.size := hsize ▸ Nat.find_min' exsize ⟨F,hF,rfl⟩
  have minP (F : Circuit) (hF : G b F) (he : F.size = E.size) : andPairs 26 E ≤ andPairs 26 F :=
    hpair ▸ Nat.find_min' expair ⟨F,hF,he.trans hsize,rfl⟩
  have hmE := minS D hGD
  by_contra! small
  have lo : E.size < (if b then 63 else 62) := by cases b <;> simp at hlen ⊢ <;> omega
  obtain ⟨deep,pack⟩ := h2 b E hE minS lo
  cases b with
  | false =>
    simp only [Bool.false_eq_true,false_or,G] at hE minS minP
    have := h4 E hE minS minP deep pack; simp at lo; omega
  | true =>
    simp only [true_or,forall_const,G] at hE minS minP
    have := h3 E hE minS minP deep pack; simp at lo; omega
