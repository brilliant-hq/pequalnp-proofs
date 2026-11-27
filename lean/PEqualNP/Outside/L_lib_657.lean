import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_657_aux

theorem foldl_fixed {α ι : Type} (f : α → ι → α) (Good : α → Prop)
    (h1 : ∀ u, Good u → ∀ s, f u s = u) :
    ∀ (l : List ι) (u : α), Good u → l.foldl f u = u := by
  intro l
  induction l with
  | nil => intro u _; rfl
  | cons s t ih =>
    intro u hu
    rw [List.foldl_cons, h1 u hu s]
    exact ih u hu

theorem exists_choices {α : Type} {b : ℕ} (hb : 0 < b) (stepfn : α → Fin b → α)
    (Good I : α → Prop) (μ : α → ℕ)
    (h0 : ∀ u, I u → μ u = 0 → Good u)
    (h1 : ∀ u, Good u → ∀ ch, stepfn u ch = u)
    (h2 : ∀ u, I u → ¬ Good u → ∃ ch, I (stepfn u ch) ∧ μ (stepfn u ch) + 1 = μ u) :
    ∀ (r : ℕ) (u : α), I u → μ u ≤ r →
      ∃ choices : Fin r → Fin b,
        Good ((List.finRange r).foldl (fun used step => stepfn used (choices step)) u) := by
  intro r
  induction r with
  | zero =>
    intro u hI hμ
    refine ⟨fun _ => ⟨0, hb⟩, ?_⟩
    simpa using h0 u hI (by omega)
  | succ r ih =>
    intro u hI hμ
    by_cases hg : Good u
    · refine ⟨fun _ => ⟨0, hb⟩, ?_⟩
      have hfix := foldl_fixed (fun (used : α) (_ : Fin (r + 1)) => stepfn used ⟨0, hb⟩) Good
        (fun v hv _ => h1 v hv _) (List.finRange (r + 1)) u hg
      show Good (List.foldl (fun (used : α) (_ : Fin (r + 1)) => stepfn used ⟨0, hb⟩) u
        (List.finRange (r + 1)))
      rw [hfix]
      exact hg
    · obtain ⟨ch, hI', hμ'⟩ := h2 u hI hg
      obtain ⟨choices, hc⟩ := ih (stepfn u ch) hI' (by omega)
      refine ⟨Fin.cons ch choices, ?_⟩
      rw [List.finRange_succ, List.foldl_cons, List.foldl_map]
      simpa using hc

theorem card_foldl {α ι : Type} [DecidableEq α] (f : Finset α → ι → Finset α)
    (h : ∀ u s, (f u s).card ≤ u.card + 1) :
    ∀ (l : List ι) (u : Finset α), (l.foldl f u).card ≤ u.card + l.length := by
  intro l
  induction l with
  | nil => intro u; simp
  | cons s t ih =>
    intro u
    rw [List.foldl_cons, List.length_cons]
    have h1 := ih (f u s)
    have h2 := h u s
    omega

end PEqualNP.Outside.L_lib_657_aux

theorem PEqualNP.Outside.L_lib_657 : (∀ (n b r : Nat), 0 < b →
  let V := Fin n
  let Point := V → Bool
  let Clause := Finset (V × Bool)
  let sat := fun (formula : Finset Clause) (x : Point) =>
    ∀ c ∈ formula, ∃ lit ∈ c, x lit.1 = lit.2
  ∀ (clauses : List Clause) (center : Point),
    let F := clauses.toFinset
    let bad := fun (x : Point) (c : Clause) => ∀ lit ∈ c, x lit.1 ≠ lit.2
    let vars := fun (c : Clause) => c.image Prod.fst
    let state := fun (flipped : Finset V) (v : V) =>
      if v ∈ flipped then !(center v) else center v
    let run := fun (choices : Fin r → Fin b) =>
      (List.finRange r).foldl (fun used step =>
        let c := (clauses.find? (fun d => decide (bad (state used) d))).getD ∅
        let options := ((vars c) \ used).sort (· ≤ ·)
        let picked := options[ (choices step).val ]?
        used ∪ picked.toList.toFinset) (∅ : Finset V)
    (∀ c ∈ F, (vars c).card ≤ b+1) →
    (∀ c ∈ F, bad center c → (vars c).card ≤ b) →
    ((∃ y : Point, sat F y ∧ ((Finset.univ : Finset V).filter (fun i => y i ≠ center i)).card ≤ r) ↔
      (∃ choices : Fin r → Fin b, sat F (state (run choices))))) := by
  intro n b r hb V Point Clause sat clauses center F bad vars state run hw hbad
  let stepfn : Finset V → Fin b → Finset V := fun used ch =>
    let c := (clauses.find? (fun d => decide (bad (state used) d))).getD ∅
    let options := ((vars c) \ used).sort (· ≤ ·)
    let picked := options[ch.val]?
    used ∪ picked.toList.toFinset
  have hrun : ∀ choices : Fin r → Fin b, run choices =
      (List.finRange r).foldl (fun used step => stepfn used (choices step)) ∅ := fun _ => rfl
  have h1 : ∀ u : Finset V, sat F (state u) → ∀ ch, stepfn u ch = u := by
    intro u hs ch
    have hnone : clauses.find? (fun d => decide (bad (state u) d)) = none := by
      rw [List.find?_eq_none]
      intro d hd
      simp only [decide_eq_true_eq]
      intro hbd
      obtain ⟨lit, hl, he⟩ := hs d (List.mem_toFinset.mpr hd)
      exact hbd lit hl he
    have hstep : stepfn u ch = u ∪ ((((Finset.image Prod.fst (∅ : Finset (V × Bool))) \ u).sort
        (· ≤ ·))[ch.val]?).toList.toFinset := by
      show u ∪ (((vars ((clauses.find? (fun d => decide (bad (state u) d))).getD ∅) \ u).sort
        (· ≤ ·))[ch.val]?).toList.toFinset = _
      rw [hnone]
      rfl
    rw [hstep, Finset.image_empty, Finset.empty_sdiff, Finset.sort_empty]
    simp
  constructor
  · rintro ⟨y, hy, hyr⟩
    let D : Finset V := (Finset.univ : Finset V).filter (fun i => y i ≠ center i)
    have hD : ∀ v, v ∈ D ↔ y v ≠ center v := by intro v; simp [D]
    have h0 : ∀ u : Finset V, u ⊆ D → (D \ u).card = 0 → sat F (state u) := by
      intro u hu hc
      have hDu : u = D :=
        Finset.Subset.antisymm hu (Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hc))
      have hst : state u = y := by
        funext v
        by_cases hv : v ∈ u
        · have hne : y v ≠ center v := (hD v).mp (hDu ▸ hv)
          have : state u v = !(center v) := by simp [state, hv]
          rw [this]
          cases hyv : y v <;> cases hcv : center v <;> simp_all
        · have he : y v = center v := by
            by_contra hne
            exact hv (hDu ▸ (hD v).mpr hne)
          have : state u v = center v := by simp [state, hv]
          rw [this, he]
      rw [hst]
      exact hy
    have h2 : ∀ u : Finset V, u ⊆ D → ¬ sat F (state u) →
        ∃ ch, stepfn u ch ⊆ D ∧ (D \ stepfn u ch).card + 1 = (D \ u).card := by
      intro u hu hns
      have hex : ∃ d ∈ clauses, bad (state u) d := by
        by_contra hcon
        apply hns
        intro c hc
        by_contra hno
        exact hcon ⟨c, List.mem_toFinset.mp hc, fun lit hl he => hno ⟨lit, hl, he⟩⟩
      obtain ⟨d0, hd0, hbd0⟩ := hex
      cases hfind : clauses.find? (fun d => decide (bad (state u) d)) with
      | none =>
        rw [List.find?_eq_none] at hfind
        have := hfind d0 hd0
        simp only [decide_eq_true_eq] at this
        exact absurd hbd0 this
      | some c =>
        have hcmem : c ∈ clauses := List.mem_of_find?_eq_some hfind
        have hcbad : bad (state u) c := by
          have := List.find?_some hfind
          simpa using this
        obtain ⟨lit, hl, hyl⟩ := hy c (List.mem_toFinset.mpr hcmem)
        have hne : state u lit.1 ≠ lit.2 := hcbad lit hl
        have hvu : lit.1 ∉ u := by
          intro hin
          have e1 : state u lit.1 = !(center lit.1) := by simp [state, hin]
          have e2 : y lit.1 ≠ center lit.1 := (hD _).mp (hu hin)
          apply hne
          rw [e1, ← hyl]
          cases hyv : y lit.1 <;> cases hcv : center lit.1 <;> simp_all
        have hsc : state u lit.1 = center lit.1 := by simp [state, hvu]
        have hvD : lit.1 ∈ D := by
          rw [hD]
          intro h
          exact hne (hsc.trans (h.symm.trans hyl))
        have hcard : (vars c \ u).card ≤ b := by
          by_cases hb0 : bad center c
          · exact (Finset.card_le_card Finset.sdiff_subset).trans
              (hbad c (List.mem_toFinset.mpr hcmem) hb0)
          · have hex2 : ∃ l' ∈ c, center l'.1 = l'.2 := by
              by_contra hcon
              exact hb0 (fun l hl he => hcon ⟨l, hl, he⟩)
            obtain ⟨l', hl', he'⟩ := hex2
            have hin : l'.1 ∈ u := by
              by_contra hnin
              have : state u l'.1 = center l'.1 := by simp [state, hnin]
              exact hcbad l' hl' (this.trans he')
            have hmem : l'.1 ∈ vars c := Finset.mem_image_of_mem Prod.fst hl'
            have hss : vars c \ u ⊆ (vars c).erase l'.1 := by
              intro x hx
              rw [Finset.mem_sdiff] at hx
              rw [Finset.mem_erase]
              exact ⟨fun h => hx.2 (h ▸ hin), hx.1⟩
            have h3 := Finset.card_le_card hss
            rw [Finset.card_erase_of_mem hmem] at h3
            have h4 := hw c (List.mem_toFinset.mpr hcmem)
            omega
        have hvin : lit.1 ∈ (vars c \ u).sort (· ≤ ·) := by
          rw [Finset.mem_sort]
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_image_of_mem Prod.fst hl, hvu⟩
        obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hvin
        have hlen : ((vars c \ u).sort (· ≤ ·)).length ≤ b := by
          rw [Finset.length_sort]
          exact hcard
        have hib : i < b := by omega
        refine ⟨⟨i, hib⟩, ?_⟩
        have hstep : stepfn u ⟨i, hib⟩ = insert lit.1 u := by
          simp only [stepfn, hfind, Option.getD_some]
          rw [List.getElem?_eq_getElem hi, hget]
          ext x
          simp
        rw [hstep]
        constructor
        · exact Finset.insert_subset hvD hu
        · have hE : D \ insert lit.1 u = (D \ u).erase lit.1 := by
            ext x
            simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
            tauto
          rw [hE]
          exact Finset.card_erase_add_one (Finset.mem_sdiff.mpr ⟨hvD, hvu⟩)
    obtain ⟨choices, hc⟩ := PEqualNP.Outside.L_lib_657_aux.exists_choices hb stepfn
      (fun u => sat F (state u)) (fun u => u ⊆ D) (fun u => (D \ u).card) h0 h1 h2 r ∅
      (Finset.empty_subset _) (by rw [Finset.sdiff_empty]; exact hyr)
    exact ⟨choices, hc⟩
  · rintro ⟨choices, hc⟩
    refine ⟨state (run choices), hc, ?_⟩
    have hEq : ∀ U : Finset V,
        (Finset.univ : Finset V).filter (fun i => state U i ≠ center i) = U := by
      intro U
      ext v
      by_cases hv : v ∈ U <;> simp [state, hv]
    rw [hEq]
    have key : ∀ o : Option V, o.toList.toFinset.card ≤ 1 := by
      intro o
      cases o <;> simp
    have hstepcard : ∀ (u : Finset V) (ch : Fin b), (stepfn u ch).card ≤ u.card + 1 := by
      intro u ch
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left (key _) _)
    have hfold := PEqualNP.Outside.L_lib_657_aux.card_foldl
      (fun (used : Finset V) (step : Fin r) => stepfn used (choices step))
      (fun u s => hstepcard u (choices s)) (List.finRange r) ∅
    rw [hrun]
    simpa using hfold
