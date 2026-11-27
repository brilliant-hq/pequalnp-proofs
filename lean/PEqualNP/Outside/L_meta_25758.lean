import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25758_aux

def radOf (f : Bool → Bool → Bool) : ℕ :=
  let ones := ((Finset.univ : Finset (Bool × Bool)).filter (fun z => f z.1 z.2)).card
  if ones = 0 ∨ ones = 4 then 1 else if ones = 2 then 2 else 3

theorem colOf_exists (f : Bool → Bool → Bool) :
    ∃ col : Bool × Bool → Fin (radOf f),
      ∀ p1 p2 : Bool × Bool, col p1 = col p2 → f p1.1 p2.2 = f p2.1 p1.2 := by
  let v00 := f false false
  let v01 := f false true
  let v10 := f true false
  let v11 := f true true
  have hf : f = fun a b => match a, b with
    | false, false => v00
    | false, true => v01
    | true, false => v10
    | true, true => v11 := by
    funext a b; cases a <;> cases b <;> rfl
  rw [hf]
  cases v00 <;> cases v01 <;> cases v10 <;> cases v11
  · exact ⟨fun _ => ⟨0, by decide⟩, by decide⟩
  · exact ⟨fun p => if p = (false, false) ∨ p = (true, true) then ⟨0, by decide⟩ else if p = (true, false) then ⟨1, by decide⟩ else ⟨2, by decide⟩, by decide⟩
  · exact ⟨fun p => if p = (false, true) ∨ p = (true, false) then ⟨0, by decide⟩ else if p = (false, false) then ⟨1, by decide⟩ else ⟨2, by decide⟩, by decide⟩
  · exact ⟨fun p => if p.1 then ⟨1, by decide⟩ else ⟨0, by decide⟩, by decide⟩
  · exact ⟨fun p => if p = (true, false) ∨ p = (false, true) then ⟨0, by decide⟩ else if p = (false, false) then ⟨1, by decide⟩ else ⟨2, by decide⟩, by decide⟩
  · exact ⟨fun p => if p.2 then ⟨1, by decide⟩ else ⟨0, by decide⟩, by decide⟩
  · exact ⟨fun p => if xor p.1 p.2 then ⟨1, by decide⟩ else ⟨0, by decide⟩, by decide⟩
  · exact ⟨fun p => if p = (false, false) ∨ p = (true, true) then ⟨0, by decide⟩ else if p = (true, false) then ⟨1, by decide⟩ else ⟨2, by decide⟩, by decide⟩
  · exact ⟨fun p => if p = (false, false) ∨ p = (true, true) then ⟨0, by decide⟩ else if p = (true, false) then ⟨1, by decide⟩ else ⟨2, by decide⟩, by decide⟩
  · exact ⟨fun p => if xor p.1 p.2 then ⟨1, by decide⟩ else ⟨0, by decide⟩, by decide⟩
  · exact ⟨fun p => if p.2 then ⟨1, by decide⟩ else ⟨0, by decide⟩, by decide⟩
  · exact ⟨fun p => if p = (true, false) ∨ p = (false, true) then ⟨0, by decide⟩ else if p = (false, false) then ⟨1, by decide⟩ else ⟨2, by decide⟩, by decide⟩
  · exact ⟨fun p => if p.1 then ⟨1, by decide⟩ else ⟨0, by decide⟩, by decide⟩
  · exact ⟨fun p => if p = (false, true) ∨ p = (true, false) then ⟨0, by decide⟩ else if p = (false, false) then ⟨1, by decide⟩ else ⟨2, by decide⟩, by decide⟩
  · exact ⟨fun p => if p = (false, false) ∨ p = (true, true) then ⟨0, by decide⟩ else if p = (true, false) then ⟨1, by decide⟩ else ⟨2, by decide⟩, by decide⟩
  · exact ⟨fun _ => ⟨0, by decide⟩, by decide⟩

theorem embOf_exists (f : Bool → Bool → Bool) :
    ∃ emb : Fin (radOf f) → Bool × Bool,
      ∀ a b : Fin (radOf f), a ≠ b → f (emb a).1 (emb b).2 ≠ f (emb b).1 (emb a).2 := by
  let v00 := f false false
  let v01 := f false true
  let v10 := f true false
  let v11 := f true true
  have hf : f = fun a b => match a, b with
    | false, false => v00
    | false, true => v01
    | true, false => v10
    | true, true => v11 := by
    funext a b; cases a <;> cases b <;> rfl
  rw [hf]
  cases v00 <;> cases v01 <;> cases v10 <;> cases v11
  · exact ⟨fun _ => (false, false), by decide⟩
  · exact ⟨fun a => if a.val = 0 then (true, true) else if a.val = 1 then (true, false) else (false, true), by decide⟩
  · exact ⟨fun a => if a.val = 0 then (true, false) else if a.val = 1 then (true, true) else (false, false), by decide⟩
  · exact ⟨fun a => if a.val = 0 then (false, false) else (true, false), by decide⟩
  · exact ⟨fun a => if a.val = 0 then (false, true) else if a.val = 1 then (false, false) else (true, true), by decide⟩
  · exact ⟨fun a => if a.val = 0 then (false, false) else (false, true), by decide⟩
  · exact ⟨fun a => if a.val = 0 then (false, false) else (false, true), by decide⟩
  · exact ⟨fun a => if a.val = 0 then (false, false) else if a.val = 1 then (false, true) else (true, false), by decide⟩
  · exact ⟨fun a => if a.val = 0 then (false, false) else if a.val = 1 then (false, true) else (true, false), by decide⟩
  · exact ⟨fun a => if a.val = 0 then (false, false) else (false, true), by decide⟩
  · exact ⟨fun a => if a.val = 0 then (false, false) else (false, true), by decide⟩
  · exact ⟨fun a => if a.val = 0 then (false, true) else if a.val = 1 then (false, false) else (true, true), by decide⟩
  · exact ⟨fun a => if a.val = 0 then (false, false) else (true, false), by decide⟩
  · exact ⟨fun a => if a.val = 0 then (true, false) else if a.val = 1 then (true, true) else (false, false), by decide⟩
  · exact ⟨fun a => if a.val = 0 then (true, true) else if a.val = 1 then (true, false) else (false, true), by decide⟩
  · exact ⟨fun _ => (false, false), by decide⟩

theorem min'_pair {α : Type*} [LinearOrder α] {a b : α} (hab : a ≤ b) :
    ({a, b} : Finset α).min' (by simp) = a := by
  apply le_antisymm
  · exact Finset.min'_le _ _ (by simp)
  · apply Finset.le_min'
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact le_rfl
    · exact hab

theorem max'_pair {α : Type*} [LinearOrder α] {a b : α} (hab : a ≤ b) :
    ({a, b} : Finset α).max' (by simp) = b := by
  apply le_antisymm
  · apply Finset.max'_le
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hab
    · exact le_rfl
  · exact Finset.le_max' _ _ (by simp)

theorem main_proof : ∀ (n q : ℕ) (op : Fin q → Bool → Bool → Bool),
  let I := Fin n
  let rad := fun (f : Bool → Bool → Bool) =>
    let ones := ((Finset.univ : Finset (Bool × Bool)).filter (fun z => f z.1 z.2)).card
    if ones = 0 ∨ ones = 4 then 1 else if ones = 2 then 2 else 3
  let D := ∏ t : Fin q, rad (op t)
  ∀ (H : I → I → Bool) (π : Equiv.Perm I) (e : ℕ),
    (∃ (R C : Fin q → I → Bool) (out : Finset I → (Fin q → Bool) → Bool),
      ((Finset.univ : Finset (I × I)).filter (fun z =>
        out {z.1,z.2} (fun t => op t (R t z.1) (C t (π z.2))) ≠ H z.1 (π z.2))).card ≤ e) ↔
    ∃ label : I → Fin D,
      ((Finset.univ : Finset (I × I)).filter (fun z =>
        z.1 < z.2 ∧ label z.1 = label z.2 ∧ H z.1 (π z.2) ≠ H z.2 (π z.1))).card ≤ e := by
  intro n q op I rad D H π e
  have hcard : Fintype.card (∀ t : Fin q, Fin (radOf (op t))) = D := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    rfl
  let eD : (∀ t : Fin q, Fin (radOf (op t))) ≃ Fin D := Fintype.equivFinOfCardEq hcard
  constructor
  · rintro ⟨R, C, out, hbad⟩
    choose col hcol using fun t : Fin q => colOf_exists (op t)
    let label : I → Fin D := fun i => eD (fun t => col t (R t i, C t (π i)))
    refine ⟨label, le_trans ?_ hbad⟩
    let pick : I × I → I × I := fun z =>
      if out {z.1, z.2} (fun t => op t (R t z.1) (C t (π z.2))) ≠ H z.1 (π z.2) then z else (z.2, z.1)
    apply Finset.card_le_card_of_injOn pick
    · intro z hz
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      rcases hz with ⟨hlt, hlab, hHne⟩
      have hsame_sig : (fun t => op t (R t z.1) (C t (π z.2))) =
          (fun t => op t (R t z.2) (C t (π z.1))) := by
        funext t
        have hct : col t (R t z.1, C t (π z.1)) = col t (R t z.2, C t (π z.2)) :=
          congrFun (eD.injective hlab) t
        exact hcol t (R t z.1, C t (π z.1)) (R t z.2, C t (π z.2)) hct
      by_cases h1 : out {z.1, z.2} (fun t => op t (R t z.1) (C t (π z.2))) ≠ H z.1 (π z.2)
      · have hpick : pick z = z := by dsimp only [pick]; simp [h1]
        rw [hpick]; exact h1
      · have h1' : out {z.1, z.2} (fun t => op t (R t z.1) (C t (π z.2))) = H z.1 (π z.2) :=
          Classical.not_not.mp h1
        have h2 : out {z.2, z.1} (fun t => op t (R t z.2) (C t (π z.1))) ≠ H z.2 (π z.1) := by
          rw [Finset.pair_comm, ← hsame_sig, h1']
          exact hHne
        have hpick : pick z = (z.2, z.1) := by dsimp only [pick]; simp [h1]
        rw [hpick]; exact h2
    · intro z1 hz1 z2 hz2 heq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hz1 hz2
      dsimp only [pick] at heq
      split_ifs at heq with h1 h2 h2
      · exact heq
      · exfalso
        have e1 : z1.1 = z2.2 := congrArg Prod.fst heq
        have e2 : z1.2 = z2.1 := congrArg Prod.snd heq
        exact lt_asymm hz1.1 (e1.symm ▸ e2.symm ▸ hz2.1)
      · exfalso
        have e1 : z1.2 = z2.1 := congrArg Prod.fst heq
        have e2 : z1.1 = z2.2 := congrArg Prod.snd heq
        exact lt_asymm hz1.1 (e1 ▸ e2 ▸ hz2.1)
      · exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
  · rintro ⟨label, hcol⟩
    choose emb hemb using fun t : Fin q => embOf_exists (op t)
    let R : Fin q → I → Bool := fun t i => (emb t (eD.symm (label i) t)).1
    let C : Fin q → I → Bool := fun t j => (emb t (eD.symm (label (π.symm j)) t)).2
    let sigOf : I → I → Fin q → Bool := fun i j t => op t (R t i) (C t (π j))
    let out : Finset I → (Fin q → Bool) → Bool := fun S sig =>
      if hS : S.Nonempty then
        let a := S.min' hS
        let b := S.max' hS
        if sig = sigOf a b then H a (π b) else H b (π a)
      else false
    refine ⟨R, C, out, le_trans ?_ hcol⟩
    apply Finset.card_le_card_of_injOn (fun z : I × I => (z.2, z.1))
    · intro z hz
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      have hne_le : ¬ z.1 ≤ z.2 := by
        intro hle
        apply hz
        have hne : ({z.1, z.2} : Finset I).Nonempty := by simp
        dsimp only [out]
        simp only [hne, ↓reduceDIte, min'_pair hle, max'_pair hle]
        change (if sigOf z.1 z.2 = sigOf z.1 z.2 then H z.1 (π z.2) else H z.2 (π z.1)) = H z.1 (π z.2)
        simp
      have hlt : z.2 < z.1 := lt_of_not_ge hne_le
      have hne : ({z.1, z.2} : Finset I).Nonempty := by simp
      have hmin : ({z.1, z.2} : Finset I).min' hne = z.2 := by
        have hne2 : ({z.2, z.1} : Finset I).Nonempty := by simp
        calc ({z.1, z.2} : Finset I).min' hne = ({z.2, z.1} : Finset I).min' hne2 := by
              congr 1; exact Finset.pair_comm z.1 z.2
          _ = z.2 := min'_pair (le_of_lt hlt)
      have hmax : ({z.1, z.2} : Finset I).max' hne = z.1 := by
        have hne2 : ({z.2, z.1} : Finset I).Nonempty := by simp
        calc ({z.1, z.2} : Finset I).max' hne = ({z.2, z.1} : Finset I).max' hne2 := by
              congr 1; exact Finset.pair_comm z.1 z.2
          _ = z.1 := max'_pair (le_of_lt hlt)
      dsimp only [out] at hz
      simp only [hne, ↓reduceDIte, hmin, hmax] at hz
      have hsig_eq : sigOf z.1 z.2 = sigOf z.2 z.1 := by
        by_contra hsig_ne
        apply hz
        change (if sigOf z.1 z.2 = sigOf z.2 z.1 then H z.2 (π z.1) else H z.1 (π z.2)) = H z.1 (π z.2)
        simp [hsig_ne]
      have hlab : label z.2 = label z.1 := by
        by_contra hlab_ne
        have hsym_ne : eD.symm (label z.2) ≠ eD.symm (label z.1) := fun h => hlab_ne (eD.symm.injective h)
        have hex : ∃ t : Fin q, eD.symm (label z.2) t ≠ eD.symm (label z.1) t := by
          by_contra hall
          exact hsym_ne (funext (fun t => Classical.not_not.mp (fun ht => hall ⟨t, ht⟩)))
        rcases hex with ⟨t, ht⟩
        have hdiff := hemb t (eD.symm (label z.2) t) (eD.symm (label z.1) t) ht
        have heq_t := congrFun hsig_eq t
        dsimp only [sigOf, R, C] at heq_t
        simp only [Equiv.symm_apply_apply] at heq_t
        exact hdiff heq_t.symm
      have hHne : H z.2 (π z.1) ≠ H z.1 (π z.2) := by
        change (if sigOf z.1 z.2 = sigOf z.2 z.1 then H z.2 (π z.1) else H z.1 (π z.2)) ≠ H z.1 (π z.2) at hz
        simpa [hsig_eq] using hz
      exact ⟨hlt, hlab, hHne⟩
    · intro z1 _ z2 _ heq
      exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)

end PEqualNP.Outside.L_meta_25758_aux

theorem PEqualNP.Outside.L_meta_25758 : (∀ (n q : ℕ) (op : Fin q → Bool → Bool → Bool),
  let I := Fin n
  let rad := fun (f : Bool → Bool → Bool) =>
    let ones := ((Finset.univ : Finset (Bool × Bool)).filter (fun z => f z.1 z.2)).card
    if ones = 0 ∨ ones = 4 then 1 else if ones = 2 then 2 else 3
  let D := ∏ t : Fin q, rad (op t)
  ∀ (H : I → I → Bool) (π : Equiv.Perm I) (e : ℕ),
    (∃ (R C : Fin q → I → Bool) (out : Finset I → (Fin q → Bool) → Bool),
      ((Finset.univ : Finset (I × I)).filter (fun z =>
        out {z.1,z.2} (fun t => op t (R t z.1) (C t (π z.2))) ≠ H z.1 (π z.2))).card ≤ e) ↔
    ∃ label : I → Fin D,
      ((Finset.univ : Finset (I × I)).filter (fun z =>
        z.1 < z.2 ∧ label z.1 = label z.2 ∧ H z.1 (π z.2) ≠ H z.2 (π z.1))).card ≤ e) :=
  PEqualNP.Outside.L_meta_25758_aux.main_proof
