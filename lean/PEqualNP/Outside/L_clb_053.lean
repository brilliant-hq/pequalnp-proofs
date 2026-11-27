import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_053

open PEqualNP.BranchingProgram

private noncomputable def choices {X : Type} (rs : List (X → Bool)) : Finset (X → Bool) := by
  classical
  exact insert (fun _ => false) (insert (fun _ => true) rs.toFinset)

private lemma sink_mem {X : Type} (rs : List (X → Bool)) (b : Bool) :
    (fun _ => b) ∈ choices rs := by
  classical
  cases b <;> simp [choices]

private lemma row_mem {X : Type} {rs : List (X → Bool)} {r : X → Bool}
    (h : r ∈ rs) : r ∈ choices rs := by
  classical
  simp [choices, h]

private lemma choices_mono {X : Type} (f : X → Bool) (rs : List (X → Bool)) :
    choices rs ⊆ choices (f :: rs) := by
  classical
  intro r hr
  simp only [choices, Finset.mem_insert, List.mem_toFinset, List.mem_cons] at hr ⊢
  tauto

private lemma choices_card {X : Type} (rs : List (X → Bool)) :
    (choices rs).card ≤ rs.length + 2 := by
  classical
  unfold choices
  calc
    _ ≤ (insert (fun _ => true) rs.toFinset).card + 1 := Finset.card_insert_le _ _
    _ ≤ (rs.toFinset.card + 1) + 1 := Nat.add_le_add_right (Finset.card_insert_le _ _) _
    _ ≤ rs.length + 2 := by
      simpa only [Nat.add_assoc] using Nat.add_le_add_right rs.toFinset_card_le 2

private def selectRow {X : Type} (z : X → Bool) (p : (X → Bool) × (X → Bool)) : X → Bool :=
  fun x => if z x then p.2 x else p.1 x

private noncomputable def extend {X : Type} (z : X → Bool) (rs : List (X → Bool)) :
    Finset (List (X → Bool)) := by
  classical
  exact ((choices rs).product (choices rs)).image (fun p => selectRow z p :: rs)

private noncomputable def tables {X : Type} : List (X → Bool) → Finset (List (X → Bool))
  | [] => {[]}
  | z :: zs => by
    classical
    exact (tables zs).biUnion (extend z)

private lemma tables_prepend {X : Type} {z : X → Bool} {zs rs : List (X → Bool)}
    (hrs : rs ∈ tables zs) (p : (X → Bool) × (X → Bool))
    (h₀ : p.1 ∈ choices rs) (h₁ : p.2 ∈ choices rs) :
    selectRow z p :: rs ∈ tables (z :: zs) := by
  classical
  change _ ∈ (tables zs).biUnion (extend z)
  refine Finset.mem_biUnion.mpr ⟨rs, hrs, ?_⟩
  unfold extend
  exact Finset.mem_image.mpr ⟨p, Finset.mem_product.mpr ⟨h₀, h₁⟩, rfl⟩

private lemma tables_length {X : Type} (zs rs : List (X → Bool)) (h : rs ∈ tables zs) :
    rs.length = zs.length := by
  classical
  induction zs generalizing rs with
  | nil =>
    have : rs = [] := by simpa [tables] using h
    simp [this]
  | cons z zs ih =>
    change rs ∈ (tables zs).biUnion (extend z) at h
    obtain ⟨tail, ht, hrs⟩ := Finset.mem_biUnion.mp h
    unfold extend at hrs
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hrs
    simp [ih tail ht]

private lemma tables_card {X : Type} (zs : List (X → Bool)) :
    (tables zs).card ≤ (zs.length + 1).factorial ^ 2 := by
  classical
  induction zs with
  | nil => simp [tables]
  | cons z zs ih =>
    change ((tables zs).biUnion (extend z)).card ≤ ((zs.length + 1) + 1).factorial ^ 2
    calc
      _ ≤ (tables zs).card * (zs.length + 2) ^ 2 := by
        apply Finset.card_biUnion_le_card_mul
        intro rs hrs
        unfold extend
        refine Finset.card_image_le.trans ?_
        have h := choices_card rs
        rw [tables_length zs rs hrs] at h
        calc
          _ = (choices rs).card * (choices rs).card := Finset.card_product _ _
          _ ≤ (zs.length + 2) ^ 2 := by
            simpa only [pow_two] using Nat.mul_le_mul h h
      _ ≤ (zs.length + 1).factorial ^ 2 * (zs.length + 2) ^ 2 := Nat.mul_le_mul_right _ ih
      _ = ((zs.length + 1) + 1).factorial ^ 2 := by
        rw [Nat.factorial_succ (zs.length + 1), mul_pow, Nat.mul_comm]

private lemma run_stable (P : Program) (hf : P.Forward) (xs : List Bool) (fuel : ℕ) :
    ∀ q f, P.length - q ≤ fuel → P.length - q ≤ f → P.run xs fuel q = P.run xs f q := by
  induction fuel with
  | zero =>
    intro q f hq _
    have hnone : P[q]? = none := List.getElem?_eq_none (by omega)
    cases f <;> simp [Program.run, hnone]
  | succ fuel ih =>
    intro q f hfuel hq
    cases f with
    | zero =>
      have hnone : P[q]? = none := List.getElem?_eq_none (by omega)
      simp [Program.run, hnone]
    | succ f =>
      cases hs : P[q]? with
      | none => simp [Program.run, hs]
      | some st =>
        simp only [Program.run, hs]
        cases hb : (if xs.getD st.var false then st.hi else st.lo) with
        | out b => rfl
        | state k =>
          have edge : st.lo = Next.state k ∨ st.hi = Next.state k := by
            split at hb
            · exact Or.inr hb
            · exact Or.inl hb
          have hk := (hf q st hs k edge).1
          exact ih k f (by omega) (by omega)

private def mixed {m : ℕ} (S : Finset (Fin m)) (a x : Fin m → Bool) : List Bool :=
  List.ofFn (fun j => if j ∈ S then x j else a j)

private def inside {m : ℕ} (S : Finset (Fin m)) (st : State) : Bool :=
  decide (st.var ∈ S.image Fin.val)

private def query {m : ℕ} (st : State) (x : Fin m → Bool) : Bool :=
  (List.ofFn x).getD st.var false

private lemma read_mixed {m : ℕ} (S : Finset (Fin m)) (a x : Fin m → Bool) (st : State)
    (h : st.var < m) :
    (mixed S a x).getD st.var false = if inside S st then query st x else query st a := by
  have hj : (⟨st.var, h⟩ : Fin m) ∈ S ↔ st.var ∈ S.image Fin.val := by
    constructor
    · intro hm
      exact Finset.mem_image.mpr ⟨⟨st.var, h⟩, hm, rfl⟩
    · intro hm
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hm
      have hi' : i = (⟨st.var, h⟩ : Fin m) := Fin.ext he
      exact hi' ▸ hi
  have hquery (y : Fin m → Bool) : query st y = y ⟨st.var, h⟩ := by
    unfold query
    rw [List.getD_eq_getElem (List.ofFn y) false (by simpa using h), List.getElem_ofFn]
  change query st (fun j => if j ∈ S then x j else a j) =
    if inside S st then query st x else query st a
  simp only [hquery, inside, decide_eq_true_eq, hj]

private def residual {m : ℕ} (P : Program) (S : Finset (Fin m)) (a : Fin m → Bool)
    (q : ℕ) (x : Fin m → Bool) : Bool := P.run (mixed S a x) (P.length - q) q

private def exitRow {m : ℕ} (P : Program) (S : Finset (Fin m)) (a : Fin m → Bool) :
    Next → (Fin m → Bool) → Bool
  | Next.state k => residual P S a k
  | Next.out b => fun _ => b

private lemma residual_step {m : ℕ} (P : Program) (S : Finset (Fin m)) (a : Fin m → Bool)
    (hf : P.Forward) {q : ℕ} {st : State} (hs : P[q]? = some st) (x : Fin m → Bool) :
    residual P S a q x =
      exitRow P S a (if (mixed S a x).getD st.var false then st.hi else st.lo) x := by
  have hq : q < P.length := List.getElem?_eq_some_iff.mp hs |>.1
  obtain ⟨n, hn⟩ : ∃ n, P.length - q = n + 1 := ⟨P.length - q - 1, by omega⟩
  simp only [residual, hn, Program.run, hs]
  cases hb : (if (mixed S a x).getD st.var false then st.hi else st.lo) with
  | out b => rfl
  | state k =>
    have edge : st.lo = Next.state k ∨ st.hi = Next.state k := by
      split at hb
      · exact Or.inr hb
      · exact Or.inl hb
    have hk := (hf q st hs k edge).1
    exact run_stable P hf _ n k _ (by omega) (Nat.le_refl _)

private lemma suffix_tables {m : ℕ} (P : Program) (S : Finset (Fin m)) (a : Fin m → Bool)
    (hf : P.Forward) (hr : P.ReadsBelow m) (l : List State) :
    ∀ q, P.drop q = l → ∃ rs ∈ tables ((l.filter (inside S)).map query),
      ∀ k, q ≤ k → k < P.length → residual P S a k ∈ choices rs := by
  classical
  induction l with
  | nil =>
    intro q hq
    refine ⟨[], by simp [tables], ?_⟩
    have h := List.drop_eq_nil_iff.mp hq
    intro k hqk hk
    omega
  | cons st l ih =>
    intro q hdrop
    have hq : q < P.length := by
      by_contra hn
      have hempty := List.drop_eq_nil_iff.mpr (Nat.le_of_not_gt hn)
      rw [hdrop] at hempty
      contradiction
    have hcons := (List.drop_eq_getElem_cons hq).symm.trans hdrop
    have hst : P[q]? = some st := by
      rw [List.getElem?_eq_getElem hq, (List.cons.inj hcons).1]
    obtain ⟨rs, hrs, htail⟩ := ih (q + 1) (List.cons.inj hcons).2
    have hvar := hr st (List.mem_of_getElem? hst)
    have hexit (e : Next) (he : st.lo = e ∨ st.hi = e) : exitRow P S a e ∈ choices rs := by
      cases e with
      | out b => exact sink_mem rs b
      | state k =>
        obtain ⟨h₁, h₂⟩ := hf q st hst k he
        exact htail k h₁ h₂
    cases hin : inside S st with
    | false =>
      refine ⟨rs, by simpa [List.filter_cons, hin] using hrs, ?_⟩
      intro k hqk hk
      by_cases heq : k = q
      · subst k
        have he : residual P S a q = exitRow P S a (if query st a then st.hi else st.lo) := by
          funext x
          rw [residual_step P S a hf hst x, read_mixed S a x st hvar, hin]
          rfl
        rw [he]
        apply hexit
        split
        · exact Or.inr rfl
        · exact Or.inl rfl
      · exact htail k (by omega) hk
    | true =>
      let p := (exitRow P S a st.lo, exitRow P S a st.hi)
      have he : residual P S a q = selectRow (query st) p := by
        funext x
        rw [residual_step P S a hf hst x, read_mixed S a x st hvar, hin]
        simp only [ite_true, selectRow, p]
        split <;> rfl
      refine ⟨residual P S a q :: rs, ?_, ?_⟩
      · simp only [List.filter_cons, hin, ite_true, List.map_cons]
        rw [he]
        exact tables_prepend hrs p (hexit _ (Or.inl rfl)) (hexit _ (Or.inr rfl))
      · intro k hqk hk
        by_cases heq : k = q
        · subst k
          exact row_mem (by simp)
        · exact choices_mono _ _ (htail k (by omega) hk)

private lemma bound (m : ℕ) (S : Finset (Fin m)) (P : Program)
    (hf : P.Forward) (hr : P.ReadsBelow m) :
    let t := (P.filter (fun st => st.var ∈ S.image Fin.val)).length
    let res := fun (a x : Fin m → Bool) => P.eval (mixed S a x)
    (Finset.univ.image res).card ≤ (t + 2) * (Nat.factorial (t + 1)) ^ 2 := by
  classical
  let zs := (P.filter (inside S)).map (query (m := m))
  let res := fun (a x : Fin m → Bool) => P.eval (mixed S a x)
  have hz : zs.length = (P.filter (inside S)).length := List.length_map _
  change (Finset.univ.image res).card ≤
    ((P.filter (inside S)).length + 2) * ((P.filter (inside S)).length + 1).factorial ^ 2
  rw [← hz]
  have hsub : Finset.univ.image res ⊆ (tables zs).biUnion choices := by
    intro r h
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨rs, hrs, hall⟩ := suffix_tables P S a hf hr P 0 List.drop_zero
    refine Finset.mem_biUnion.mpr ⟨rs, hrs, ?_⟩
    by_cases hP : 0 < P.length
    · have he : res a = residual P S a 0 := by
        funext x
        simp [res, Program.eval, residual]
      rw [he]
      exact hall 0 (Nat.le_refl 0) hP
    · have he : res a = (fun _ => false) := by
        funext x
        have hl : P.length = 0 := by omega
        simp [res, Program.eval, hl, Program.run]
      rw [he]
      exact sink_mem rs false
  calc
    _ ≤ ((tables zs).biUnion choices).card := Finset.card_le_card hsub
    _ ≤ (tables zs).card * (zs.length + 2) := by
      apply Finset.card_biUnion_le_card_mul
      intro rs hrs
      simpa only [tables_length zs rs hrs] using choices_card rs
    _ ≤ zs.length.succ.factorial ^ 2 * (zs.length + 2) :=
      Nat.mul_le_mul_right _ (tables_card zs)
    _ = _ := Nat.mul_comm _ _

end PEqualNP.Outside.L_clb_053

theorem PEqualNP.Outside.L_clb_053 : ∀ (m : ℕ) (S : Finset (Fin m)) (P : PEqualNP.BranchingProgram.Program),
  P.Forward → P.ReadsBelow m →
  let t := (P.filter (fun st => st.var ∈ S.image Fin.val)).length
  let res := fun (a x : Fin m → Bool) =>
    P.eval (List.ofFn (fun j => if j ∈ S then x j else a j))
  (Finset.univ.image res).card ≤ (t + 2) * (Nat.factorial (t + 1)) ^ 2 := by
  exact PEqualNP.Outside.L_clb_053.bound
