import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_619

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

theorem key (n : ℕ) (P : Finset (Fin n → ZMod 2))
    (h : ∀ s ⊆ P, s.card ≤ n + 1 → s.card % 2 = 1 → (∑ v ∈ s, v) ≠ 0) :
    ∃ φ : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2, ∀ v ∈ P, φ v = 1 := by
  classical
  obtain ⟨b, hbP, hspan, hli⟩ := exists_linearIndependent (ZMod 2) (P : Set (Fin n → ZMod 2))
  let B := Module.Basis.span hli
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (B.constr (ZMod 2) (fun _ => (1 : ZMod 2)))
  refine ⟨g, fun v hv => ?_⟩
  have hvs : v ∈ Submodule.span (ZMod 2) (Set.range ((↑) : b → (Fin n → ZMod 2))) := by
    rw [Subtype.range_coe, hspan]
    exact Submodule.subset_span hv
  let w : Submodule.span (ZMod 2) (Set.range ((↑) : b → (Fin n → ZMod 2))) := ⟨v, hvs⟩
  have hgw : g v = B.constr (ZMod 2) (fun _ => (1 : ZMod 2)) w := by
    rw [← hg]; rfl
  have hsum := B.sum_repr w
  set c := B.repr w with hc
  let S : Finset b := Finset.univ.filter (fun i => c i = 1)
  have hval : B.constr (ZMod 2) (fun _ => (1 : ZMod 2)) w = (S.card : ZMod 2) := by
    conv_lhs => rw [← hsum]
    rw [map_sum]
    simp only [map_smul, Module.Basis.constr_basis, smul_eq_mul, mul_one]
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases zmod2_cases (c i) with h0 | h1
    · rw [h0]; simp
    · rw [h1]; simp
  have hvsum : v = ∑ i ∈ S, (i : Fin n → ZMod 2) := by
    have := congrArg Subtype.val hsum
    rw [Submodule.coe_sum] at this
    simp only [Submodule.coe_smul] at this
    show (w : Fin n → ZMod 2) = _
    rw [← this, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases zmod2_cases (c i) with h0 | h1
    · rw [h0]; simp
    · rw [h1]; simp [B]
  by_cases hvb : v ∈ b
  · have hwB : w = B ⟨v, hvb⟩ := by
      apply Subtype.ext
      rw [Module.Basis.coe_span_apply]
    rw [hgw, hwB, Module.Basis.constr_basis]
  rw [hgw, hval]
  let T : Finset (Fin n → ZMod 2) := S.map (Function.Embedding.subtype _)
  have hTb : (T : Set (Fin n → ZMod 2)) ⊆ b := by
    intro x hx
    simp only [T, Finset.coe_map, Set.mem_image, Function.Embedding.coe_subtype] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact y.2
  have hTcard : T.card ≤ n := by
    have hl : LinearIndependent (ZMod 2) (fun x => x : T → (Fin n → ZMod 2)) :=
      ((show LinearIndepOn (ZMod 2) id b from hli).mono hTb).linearIndependent
    have := hl.finset_card_le_finrank
    simpa using this
  have hTsum : ∑ x ∈ T, x = v := by
    rw [hvsum, Finset.sum_map]; rfl
  have hST : S.card = T.card := (Finset.card_map _).symm
  have hvT : v ∉ T := fun hx => hvb (hTb hx)
  have hsP : insert v T ⊆ P := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hv
    · exact hbP (hTb hx)
  have hcard : (insert v T).card = T.card + 1 := Finset.card_insert_of_notMem hvT
  have hz : (∑ x ∈ insert v T, x) = 0 := by
    rw [Finset.sum_insert hvT, hTsum]
    funext j
    simp only [Pi.add_apply, Pi.zero_apply]
    rcases zmod2_cases (v j) with h0 | h0 <;> rw [h0] <;> rfl
  have hpar : (insert v T).card % 2 ≠ 1 := fun hodd =>
    h _ hsP (by omega) hodd hz
  rw [← ZMod.natCast_mod, hST]
  have : T.card % 2 = 1 := by omega
  rw [this, Nat.cast_one]

theorem add_ne (a b : ZMod 2) (h : a ≠ b) : a + b = 1 := by
  rcases zmod2_cases a with ha | ha <;> rcases zmod2_cases b with hb | hb <;>
    rw [ha, hb] at h ⊢ <;> first | rfl | exact absurd rfl h

theorem add_self (a : ZMod 2) : a + a = 0 := by
  rcases zmod2_cases a with ha | ha <;> rw [ha] <;> rfl

end PEqualNP.Outside.L_lib_619

theorem PEqualNP.Outside.L_lib_619 : (∀ (n q rows cols pairs names messages : ℕ)
    (Y : Fin rows → Fin pairs → Bool → Fin names) (pass : Fin names → Bool)
    (col : Fin cols → Fin pairs → Bool → Bool) (pick : Fin rows → Fin pairs → Bool)
    (tag : Fin rows → Fin messages) (feature : Fin rows → Fin pairs → Fin n → ZMod 2),
  let V := Fin n → ZMod 2
  let edge := fun (r : Fin rows) (c : Fin cols) =>
    ∃ (z : Fin pairs) (p : Bool), pass (Y r z p) = true ∧ col c z p = true
  let seen := fun (r : Fin rows) (z : Fin pairs) => Y r z (pick r z)
  let direct := fun (r : Fin rows) (c : Fin cols) =>
    ∃ z, pass (seen r z) = true ∧ col c z (pick r z) = true
  let avail := fun (r : Fin rows) (c : Fin cols) (z : Fin pairs) =>
    col c z (!(pick r z)) = true
  let Need := {cell : Fin rows × Fin cols // edge cell.1 cell.2 ∧ ¬direct cell.1 cell.2}
  let conflict := fun (sel : Need → Fin pairs) (d : V) =>
    ∃ (t : Need) (r : Fin rows) (c : Fin cols) (z : Fin pairs),
      ¬edge r c ∧ avail r c z ∧ tag t.val.1 = tag r ∧
      seen t.val.1 (sel t) = seen r z ∧ feature t.val.1 (sel t) + feature r z = d
  (∃ (query : Fin q → (V →ₗ[ZMod 2] ZMod 2))
      (lookup : Fin messages → Fin names → (Fin q → ZMod 2) → Bool),
    ∀ (r : Fin rows) (c : Fin cols), edge r c ↔
      (direct r c ∨ ∃ z, avail r c z ∧
        lookup (tag r) (seen r z) (fun i => query i (feature r z)) = true)) ↔
  ∃ sel : Need → Fin pairs,
    (∀ t, avail t.val.1 t.val.2 (sel t)) ∧ ∃ parts : Fin q → Finset V,
      (∀ d, conflict sel d ↔ ∃ i, d ∈ parts i) ∧
      ∀ (i : Fin q) (s : Finset V), s ⊆ parts i → s.card ≤ n + 1 →
        s.card % 2 = 1 → (∑ v ∈ s, v) ≠ 0) := by
  classical
  intro n q rows cols pairs names messages Y pass col pick tag feature V edge seen direct avail
    Need conflict
  constructor
  · rintro ⟨query, lookup, hq⟩
    have hex : ∀ t : Need, ∃ z, avail t.val.1 t.val.2 z ∧
        lookup (tag t.val.1) (seen t.val.1 z) (fun i => query i (feature t.val.1 z)) = true := by
      intro t
      rcases (hq t.val.1 t.val.2).mp t.prop.1 with hd | hz
      · exact absurd hd t.prop.2
      · exact hz
    choose sel hsel1 hsel2 using hex
    refine ⟨sel, hsel1, fun i => Finset.univ.filter (fun d => conflict sel d ∧ query i d = 1),
      fun d => ?_, ?_⟩
    · constructor
      · intro hc
        obtain ⟨t, r, c, z, hne, hav, htag, hseen, hd⟩ := hc
        have hfalse : lookup (tag r) (seen r z) (fun i => query i (feature r z)) ≠ true := by
          intro hl
          exact hne ((hq r c).mpr (Or.inr ⟨z, hav, hl⟩))
        have hvec : (fun i => query i (feature t.val.1 (sel t))) ≠
            (fun i => query i (feature r z)) := by
          intro he
          apply hfalse
          rw [← htag, ← hseen, ← he]
          exact hsel2 t
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hvec
        refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨t, r, c, z, hne, hav, htag, hseen, hd⟩, ?_⟩⟩
        rw [← hd, map_add]
        exact PEqualNP.Outside.L_lib_619.add_ne _ _ hi
      · rintro ⟨i, hi⟩
        exact (Finset.mem_filter.mp hi).2.1
    · intro i s hs _ hodd hz
      have h1 : ∀ v ∈ s, query i v = 1 := fun v hv => (Finset.mem_filter.mp (hs hv)).2.2
      have hsum := congrArg (query i) hz
      rw [map_sum, map_zero, Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one,
        ← ZMod.natCast_mod, hodd] at hsum
      exact absurd hsum (by decide)
  · rintro ⟨sel, hav, parts, hparts, hodd⟩
    have hphi : ∀ i, ∃ φ : V →ₗ[ZMod 2] ZMod 2, ∀ v ∈ parts i, φ v = 1 :=
      fun i => PEqualNP.Outside.L_lib_619.key n (parts i) (hodd i)
    choose query hquery using hphi
    refine ⟨query, fun m nm vec => decide (∃ t : Need, tag t.val.1 = m ∧
      seen t.val.1 (sel t) = nm ∧ (fun i => query i (feature t.val.1 (sel t))) = vec), ?_⟩
    intro r c
    constructor
    · intro he
      by_cases hd : direct r c
      · exact Or.inl hd
      · let t : Need := ⟨(r, c), he, hd⟩
        exact Or.inr ⟨sel t, hav t, decide_eq_true ⟨t, rfl, rfl, rfl⟩⟩
    · rintro (⟨z, hp, hc⟩ | ⟨z, hz, hl⟩)
      · exact ⟨z, pick r z, hp, hc⟩
      · obtain ⟨t, htag, hseen, hvec⟩ := of_decide_eq_true hl
        by_contra hne
        obtain ⟨i, hi⟩ := (hparts (feature t.val.1 (sel t) + feature r z)).mp
          ⟨t, r, c, z, hne, hz, htag, hseen, rfl⟩
        have h1 := hquery i _ hi
        rw [map_add, congrFun hvec i, PEqualNP.Outside.L_lib_619.add_self] at h1
        exact absurd h1 (by decide)
