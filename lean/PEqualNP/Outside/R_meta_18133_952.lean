import PEqualNP.Defs

-- The G11 mask representation follows PR 22669.
-- The complement of a marked mask covers the graph of star edges.
-- Small complements leave degree-two vertices with both incident edges uncovered.

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem PEqualNP.Outside.R_meta_18133_952
    (oneCase :
      let ends (i : ℕ) : ℕ × ℕ :=
        ((9756579394148765952 >>> (4*i)) % 16, (11071986058226140329 >>> (4*i)) % 16)

      let graph : SimpleGraph (Fin 11) := PEqualNP.EdgeOwnership.edgeGraph 11 ((List.range 16).map ends)

      let marked (k : ℕ) : Bool :=
        ([(9799982322739576832 : ℕ), 9799982322739576832, 9799982322739576832,
          9838263503687778304, 12249940522713513984, 12249940522713513984,
          12249940522713513984, 12297791852880363648, 14699973487330639872,
          14699973487330639872, 14699973487330639872, 14757395258765525184,
          18374910784070270976, 18374910784070270976, 18374910784070270976,
          18446687779320545472].getD (k/64) 0).testBit (k%64)

      let nVertices (k : ℕ) := ((List.range 11).filter fun i => (k+1024).testBit i).length

      let edgeAt (i : ℕ) : Sym2 (Fin 11) :=
        s(Fin.ofNat 11 (ends i).1, Fin.ofNat 11 (ends i).2)


      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO graph C → PEqualNP.TopForm.TopForm graph C →
        (PEqualNP.TopForm.Ustar graph C).card = 4 → (PEqualNP.TopForm.centreless graph C).card = 1 →
        (PEqualNP.TopForm.orN graph C \ PEqualNP.TopForm.lam graph C).card = 1 → 3 ≤ (PEqualNP.TopForm.junk graph C).card →
        ∀ k < 1024, marked k = true →
          (∀ i < 16, (k+1024).testBit (ends i).1 = true →
            (k+1024).testBit (ends i).2 = true → edgeAt i ∈ PEqualNP.TopForm.Ustar graph C) →
          (PEqualNP.TopForm.Ustar graph C).card + nVertices k ≤
            2*(PEqualNP.TopForm.centreless graph C).card + (PEqualNP.TopForm.junk graph C).card + (PEqualNP.TopForm.orN graph C \ PEqualNP.TopForm.lam graph C).card + 4)
  (smallCoverComplement :
      let ends (i : ℕ) : ℕ × ℕ :=
        ((9756579394148765952 >>> (4*i)) % 16, (11071986058226140329 >>> (4*i)) % 16)
      let G := edgeGraph 11 ((List.range 16).map ends)
      ∀ C : Circuit, IsLeastAO G C → TopForm G C →
        let U := Ustar G C
        let V := centreless G C
        let E := orN G C \ lam G C
        let J := junk G C
        let D := 2 * V.card + J.card + E.card
        C.size ≤ 21 → 3 ≤ J.card → 4 ≤ U.card → D < 2 * U.card →
        ¬ (U.card = 4 ∧ V.card = 1 ∧ E.card = 1) →
        ∀ K : Finset (Fin 11), 4 ≤ K.card → K.card ≤ 6 → (10 : Fin 11) ∉ K →
          (G.deleteEdges ↑U).IsVertexCover ↑K →
          (∀ v ∈ K, (G.neighborFinset v \ K).Nonempty ∧
            ∀ u : Fin 11, G.neighborFinset v \ K = {u} → (G.neighborFinset u ⊆ K ∧ u < v)) →
          D + K.card ≤ U.card + 6 → False)
  (manyIsolated :
      let ends (i : ℕ) : ℕ × ℕ :=
        ((9756579394148765952 >>> (4*i)) % 16, (11071986058226140329 >>> (4*i)) % 16)
      let G := edgeGraph 11 ((List.range 16).map ends)
      let cast (v : Fin 4) : Fin 11 := Fin.ofNat 11 v.val
      ∀ C : Circuit, IsLeastAO G C → TopForm G C →
        let U := Ustar G C
        let V := centreless G C
        let E := orN G C \ lam G C
        let J := junk G C
        let D := 2 * V.card + J.card + E.card
        C.size ≤ 21 → 3 ≤ J.card → 6 ≤ U.card → D < 2 * U.card →
        ∀ K : Finset (Fin 11), K.card ≤ 3 → (10 : Fin 11) ∉ K → (G.deleteEdges ↑U).IsVertexCover ↑K →
          ([16,12,9,6] : List ℕ).getD K.card 0 ≤ U.card →
          let I := Finset.univ.filter (fun v : Fin 4 =>
            cast v ∉ K ∧ ∀ w : Fin 11, G.Adj (cast v) w → w ∉ K ∧ s(cast v,w) ∈ U)
          4 ≤ K.card + I.card → D + K.card ≤ U.card + 6 → False) :
    have x1 : ℕ → ℕ × ℕ := fun (x1 : ℕ) => ((9756579394148765952 : ℕ) >>> ((4 : ℕ) * x1) % (16 : ℕ), (11071986058226140329 : ℕ) >>> ((4 : ℕ) * x1) % (16 : ℕ)); let x2 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map x1 (List.range (16 : ℕ))); have x3 : List ℕ := [(9799982322739576832 : ℕ), (9799982322739576832 : ℕ), (9799982322739576832 : ℕ), (9838263503687778304 : ℕ), (12249940522713513984 : ℕ), (12249940522713513984 : ℕ), (12249940522713513984 : ℕ), (12297791852880363648 : ℕ), (14699973487330639872 : ℕ), (14699973487330639872 : ℕ), (14699973487330639872 : ℕ), (14757395258765525184 : ℕ), (18374910784070270976 : ℕ), (18374910784070270976 : ℕ), (18374910784070270976 : ℕ), (18446687779320545472 : ℕ)]; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x2 x4 →     PEqualNP.TopForm.TopForm x2 x4 →       have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x2 x4;       have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card;       x4.size ≤ (21 : ℕ) → (3 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x4).card → (4 : ℕ) ≤ x7.card → x8 < (2 : ℕ) * x7.card → ∀ x13 < (1024 : ℕ), (x3.getD (x13 / (64 : ℕ)) (0 : ℕ)).testBit (x13 % (64 : ℕ)) = Bool.true → (∀ x16 < (16 : ℕ), (x13 + (1024 : ℕ)).testBit (x1 x16).1 = Bool.true → (x13 + (1024 : ℕ)).testBit (x1 x16).2 = Bool.true → s(Fin.ofNat (11 : ℕ) (x1 x16).1, Fin.ofNat (11 : ℕ) (x1 x16).2) ∈ x7) → x7.card + (List.filter (fun (x17 : ℕ) => (x13 + (1024 : ℕ)).testBit x17) (List.range (11 : ℕ))).length ≤ x8 + (4 : ℕ) := by
  intro sourceEdges sourceGraph sourceWords C least top seen totalCharge small dirty many short k hk mark contained
  let ends (i : ℕ) : ℕ × ℕ :=
    ((9756579394148765952 >>> (4*i)) % 16, (11071986058226140329 >>> (4*i)) % 16)
  
  let graph : SimpleGraph (Fin 11) := PEqualNP.EdgeOwnership.edgeGraph 11 ((List.range 16).map ends)
  
  let marked (k : ℕ) : Bool :=
    ([(9799982322739576832 : ℕ), 9799982322739576832, 9799982322739576832,
      9838263503687778304, 12249940522713513984, 12249940522713513984,
      12249940522713513984, 12297791852880363648, 14699973487330639872,
      14699973487330639872, 14699973487330639872, 14757395258765525184,
      18374910784070270976, 18374910784070270976, 18374910784070270976,
      18446687779320545472].getD (k/64) 0).testBit (k%64)
  
  let nVertices (k : ℕ) := ((List.range 11).filter fun i => (k+1024).testBit i).length
  
  let edgeAt (i : ℕ) : Sym2 (Fin 11) :=
    s(Fin.ofNat 11 (ends i).1, Fin.ofNat 11 (ends i).2)

  let U := Ustar graph C
  let D := 2 * (centreless graph C).card + (junk graph C).card + (orN graph C \ lam graph C).card
  change 4 ≤ U.card at many
  change D < 2 * U.card at short
  change ∀ i < 16, (k+1024).testBit (ends i).1 = true →
      (k+1024).testBit (ends i).2 = true → edgeAt i ∈ U at contained
  change U.card + nVertices k ≤ D + 4
  by_cases special : U.card = 4 ∧ (centreless graph C).card = 1 ∧
      (orN graph C \ lam graph C).card = 1
  · exact oneCase C least top special.1 special.2.1 special.2.2 dirty k hk mark contained
  let K (r : ℕ) : Finset (Fin 11) := Finset.univ.filter (fun v => (r+1024).testBit v.val = false)
  let cast (v : Fin 4) : Fin 11 := Fin.ofNat 11 v.val
  let chosen (r : ℕ) : Finset (Fin 16) :=
    Finset.univ.filter (fun i => (r+1024).testBit (ends i.val).1 && (r+1024).testBit (ends i.val).2)
  let isolated (r : ℕ) : Finset (Fin 4) := Finset.univ.filter (fun v : Fin 4 =>
    cast v ∉ K r ∧ ∀ i : Fin 16, cast v ∈ edgeAt i.val → i ∈ chosen r)
  let I := Finset.univ.filter (fun v : Fin 4 =>
    cast v ∉ K k ∧ ∀ w : Fin 11, graph.Adj (cast v) w → w ∉ K k ∧ s(cast v,w) ∈ U)
  let canonical (B : Finset (Fin 11)) : Prop :=
    ∀ v ∈ B, (graph.neighborFinset v \ B).Nonempty ∧
      ∀ u : Fin 11, graph.neighborFinset v \ B = {u} → (graph.neighborFinset u ⊆ B ∧ u < v)
  have lowTable : ∀ q : Fin 16, ∀ r : Fin 64,
      let t := 64*q.val + r.val
      marked t = true → 4 ≤ (K t).card → canonical (K t) := by
    intro q
    fin_cases q <;> decide +kernel
  have table : ∀ q : Fin 16, ∀ r : Fin 64,
      let t := 64*q.val + r.val
      (K t).card + nVertices t = 11 ∧ (10 : Fin 11) ∉ K t ∧
      (marked t = true → (K t).card ≤ 6 ∧
         ((K t).card ≤ 3 → 6 ≤ (chosen t).card ∧
           ([16,12,9,6] : List ℕ).getD (K t).card 0 ≤ (chosen t).card ∧
           4 ≤ (K t).card + (isolated t).card)) := by
    intro q
    fin_cases q <;> decide +kernel
  have edgeInfo : ∀ a b : Fin 11, graph.Adj a b ↔
      ∃ i : Fin 16, edgeAt i.val = s(a,b) := by decide +kernel
  have endsSmall : ∀ i : Fin 16, (ends i.val).1 < 11 ∧ (ends i.val).2 < 11 := by decide +kernel
  have distinctEdges : Function.Injective (fun i : Fin 16 => edgeAt i.val) := by decide +kernel
  have hrow : (K k).card + nVertices k = 11 ∧ (10 : Fin 11) ∉ K k ∧
      (marked k = true → (K k).card ≤ 6 ∧
        ((K k).card ≤ 3 → 6 ≤ (chosen k).card ∧
          ([16,12,9,6] : List ℕ).getD (K k).card 0 ≤ (chosen k).card ∧
          4 ≤ (K k).card + (isolated k).card)) := by
    let q : Fin 16 := ⟨k / 64, by omega⟩
    let r : Fin 64 := ⟨k % 64, Nat.mod_lt _ (by decide)⟩
    have hkEq : 64*q.val + r.val = k := by
      change 64*(k/64)+k%64 = k
      omega
    have row := table q r
    dsimp only at row
    rwa [hkEq] at row
  have chosenIn (i : Fin 16) (hi : i ∈ chosen k) : edgeAt i.val ∈ U := by
    obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp ((Finset.mem_filter.mp hi).2)
    exact contained i.val i.isLt a b
  have coverHit : (graph.deleteEdges ↑U).IsVertexCover (↑(K k) : Set (Fin 11)) := by
    intro a b hab
    obtain ⟨adj, avoid⟩ := SimpleGraph.deleteEdges_adj.mp hab
    obtain ⟨i, hi⟩ := (edgeInfo a b).mp adj
    change a ∈ K k ∨ b ∈ K k
    by_contra! misses
    have lit {v : Fin 11} (hv : v ∉ K k) : (k+1024).testBit v.val = true := by
      cases hb : (k+1024).testBit v.val with
      | false => exact (hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩)).elim
      | true => rfl
    have both (u v : Fin 11) (he : s(u,v) = s(a,b)) :
        (k+1024).testBit u.val = true ∧ (k+1024).testBit v.val = true := by
      rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨lit misses.1,lit misses.2⟩
      · exact ⟨lit misses.2,lit misses.1⟩
    obtain ⟨hl,hr⟩ := both _ _ hi
    change (k+1024).testBit ((ends i.val).1 % 11) = true at hl
    change (k+1024).testBit ((ends i.val).2 % 11) = true at hr
    rw [Nat.mod_eq_of_lt (endsSmall i).1] at hl
    rw [Nat.mod_eq_of_lt (endsSmall i).2] at hr
    exact avoid (hi ▸ contained i.val i.isLt hl hr)
  have isolatedIn : isolated k ⊆ I := by
    intro v hv
    obtain ⟨out, h⟩ := (Finset.mem_filter.mp hv).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,out, ?_⟩
    intro w hw
    obtain ⟨i,hi⟩ := (edgeInfo (cast v) w).mp hw
    have head : cast v ∈ s(cast v,w) := Sym2.mem_mk_left _ _
    have picked := h i (hi.symm ▸ head)
    refine ⟨?_,hi ▸ chosenIn i picked⟩
    obtain ⟨yesLeft,yesRight⟩ := Bool.and_eq_true_iff.mp ((Finset.mem_filter.mp picked).2)
    have outLeft : Fin.ofNat 11 (ends i.val).1 ∉ K k := fun yes => by
      have bit0 := (Finset.mem_filter.mp yes).2
      change (k+1024).testBit ((ends i.val).1 % 11) = false at bit0
      rw [Nat.mod_eq_of_lt (endsSmall i).1, yesLeft] at bit0
      contradiction
    have outRight : Fin.ofNat 11 (ends i.val).2 ∉ K k := fun yes => by
      have bit0 := (Finset.mem_filter.mp yes).2
      change (k+1024).testBit ((ends i.val).2 % 11) = false at bit0
      rw [Nat.mod_eq_of_lt (endsSmall i).2, yesRight] at bit0
      contradiction
    rcases Sym2.eq_iff.mp hi with ⟨_, eq⟩ | ⟨eq, _⟩
    · exact eq ▸ outRight
    · exact eq ▸ outLeft
  by_contra! failed
  have chargeDeficit : D + (K k).card ≤ U.card + 6 := by have := hrow.1; omega
  by_cases high : (K k).card ≤ 3
  · obtain ⟨chosenMany,chosenFloor,isolatedMany⟩ := (hrow.2.2 mark).2 high
    have subset : (chosen k).image (fun i => edgeAt i.val) ⊆ U := by
      intro e he
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp he
      exact chosenIn i hi
    have chosenLe : (chosen k).card ≤ U.card := by
      rw [← Finset.card_image_of_injective _ distinctEdges]
      exact Finset.card_le_card subset
    have isolatedLe : (isolated k).card ≤ I.card := Finset.card_le_card isolatedIn
    have isolatedBound : 4 ≤ (K k).card + I.card := by omega
    exact manyIsolated C least top small dirty (chosenMany.trans chosenLe) short (K k) high
      hrow.2.1 coverHit (chosenFloor.trans chosenLe) isolatedBound chargeDeficit
  · have lower : 4 ≤ (K k).card := by omega
    let q : Fin 16 := ⟨k / 64, by omega⟩
    let r : Fin 64 := ⟨k % 64, Nat.mod_lt _ (by decide)⟩
    have hkEq : 64*q.val + r.val = k := by
      change 64*(k/64)+k%64 = k
      omega
    have rows := lowTable q r
    dsimp only at rows
    rw [hkEq] at rows
    exact smallCoverComplement C least top small dirty many short special (K k) lower
      (hrow.2.2 mark).1 hrow.2.1 coverHit (rows mark lower) chargeDeficit
