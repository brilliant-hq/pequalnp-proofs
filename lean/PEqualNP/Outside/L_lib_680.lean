import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace PEqualNP.Outside.L_lib_680_aux

abbrev K := ZMod 2
abbrev Bits (r : ℕ) := Fin r → K
abbrev Queries (m h q : ℕ) :=
  (j : Fin q) → Bits j.val → (Bits h × Bits m) →ₗ[K] K

def past {q : ℕ} (t : Bits q) (j : Fin q) : Bits j.val :=
  fun i => t ⟨i.val, i.isLt.trans j.isLt⟩

def Feasible {m h : ℕ} (q : ℕ) (label : Bits h → Bits m → Bool) : Prop :=
  ∃ (ask : Queries m h q) (ans : Bits h → Bits m → Bits q) (leaf : Bits q → Bool),
    (∀ u x j, ans u x j = ask j (past (ans u x) j) (u,x)) ∧ ∀ u x, label u x = leaf (ans u x)

def rejected {m h : ℕ} (label : Bits h → Bits m → Bool) (x : Bits m) : ℕ :=
  (Finset.univ.filter fun u => label u x = false).card

def Shape {n : ℕ} (h q : ℕ) (d : Fin n → ℕ) : Prop :=
  (∀ i, d i ≤ min h q) ∧ ∑ i, 2 ^ (h - d i) = 2 ^ h

def mass {m h q n : ℕ} (d : Fin n → ℕ) (maps : (i : Fin n) → Bits m →ₗ[K] Bits (q-d i))
    (x : Bits m) : ℕ := ∑ i, if maps i x = 0 then 2 ^ (h-d i) else 0

theorem bits_card (h : ℕ) : Fintype.card (Bits h) = 2 ^ h := by
  rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]

def along {m h q : ℕ} (ask : Queries m h q) (t : Bits q) : (Bits h × Bits m) →ₗ[K] Bits q :=
  LinearMap.pi fun j => ask j (past t j)

theorem transcript_iff {m h q : ℕ} (ask : Queries m h q) (ans : Bits h → Bits m → Bits q)
    (run : ∀ u x j, ans u x j = ask j (past (ans u x) j) (u,x))
    (u : Bits h) (x : Bits m) (t : Bits q) : ans u x = t ↔ along ask t (u,x) = t := by
  constructor
  · intro eq
    funext j
    change ask j (past t j) (u,x) = t j
    simpa only [eq] using (run u x j).symm
  · intro eq
    have agree : ∀ k : ℕ, ∀ j : Fin q, j.val = k → ans u x j = t j := by
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro j hj
        have hist : past (ans u x) j = past t j := by
          funext i
          exact ih i.val (by omega) ⟨i.val, i.isLt.trans j.isLt⟩ rfl
        rw [run u x j, hist]
        exact congrFun eq j
    exact funext fun j => agree j.val j rfl

noncomputable def rankW {h q : ℕ} (A : Bits h →ₗ[K] Bits q) : ℕ :=
  Module.finrank K (LinearMap.range A)

theorem rankW_le {h q : ℕ} (A : Bits h →ₗ[K] Bits q) : rankW A ≤ min h q := by
  exact le_min (by simpa [rankW, Bits] using A.finrank_range_le)
    (by simpa [rankW, Bits] using (LinearMap.range A).finrank_le)

noncomputable def quotientCoordinates {h q : ℕ} (A : Bits h →ₗ[K] Bits q) :
    (Bits q ⧸ LinearMap.range A) ≃ₗ[K] Bits (q - rankW A) :=
  LinearEquiv.ofFinrankEq _ _ (by
    have eq := (LinearMap.range A).finrank_quotient_add_finrank
    rw [Module.finrank_fin_fun] at eq ⊢
    unfold rankW
    omega)

noncomputable def obstruction {m h q : ℕ} (A : Bits h →ₗ[K] Bits q) (B : Bits m →ₗ[K] Bits q) :
    Bits m →ₗ[K] Bits (q - rankW A) :=
  (quotientCoordinates A).toLinearMap.comp ((LinearMap.range A).mkQ.comp B)

theorem obstruction_zero {m h q : ℕ} (A : Bits h →ₗ[K] Bits q) (B : Bits m →ₗ[K] Bits q)
    (x : Bits m) : obstruction A B x = 0 ↔ B x ∈ LinearMap.range A := by
  change quotientCoordinates A ((LinearMap.range A).mkQ (B x)) = 0 ↔ _
  rw [(quotientCoordinates A).map_eq_zero_iff]
  exact Submodule.Quotient.mk_eq_zero _

theorem fiber_card {h q : ℕ} (A : Bits h →ₗ[K] Bits q) (v : Bits h) :
    (Finset.univ.filter fun u => A u = A v).card = 2 ^ (h - rankW A) := by
  classical
  let e : {u : Bits h // A u = A v} ≃ LinearMap.ker A :=
    { toFun := fun u => ⟨u.1 - v, by change A (u.1-v) = 0; rw [map_sub, u.property, sub_self]⟩
      invFun := fun z => ⟨z.1 + v, by rw [map_add, (show A z.1 = 0 from z.property), zero_add]⟩
      left_inv := fun u => Subtype.ext (sub_add_cancel _ _)
      right_inv := fun z => Subtype.ext (add_sub_cancel_right _ _) }
  have rank := A.finrank_range_add_finrank_ker
  rw [Module.finrank_fin_fun] at rank
  have dim : Module.finrank K (LinearMap.ker A) = h - rankW A := by unfold rankW; omega
  rw [← Fintype.card_subtype, Fintype.card_congr e, Module.card_eq_pow_finrank (K := K), dim, ZMod.card]

theorem lower_envelope {m h q : ℕ} (label : Bits h → Bits m → Bool)
    (feasible : Feasible q label) (zeroReject : ∀ u, label u 0 = false) :
    ∃ (n : ℕ) (d : Fin n → ℕ) (maps : (i : Fin n) → Bits m →ₗ[K] Bits (q-d i)),
      Shape h q d ∧ ∀ x, mass (h := h) d maps x ≤ rejected label x := by
  classical
  obtain ⟨ask, ans, leaf, run, readout⟩ := feasible
  let A (t : Bits q) := (along ask t).comp (LinearMap.inl K (Bits h) (Bits m))
  let B (t : Bits q) := (along ask t).comp (LinearMap.inr K (Bits h) (Bits m))
  have path (u : Bits h) (x : Bits m) (t : Bits q) :
      ans u x = t ↔ A t u + B t x = t := by
    rw [transcript_iff ask ans run]
    have eq : (along ask t) (u,x) = A t u + B t x := by
      change (along ask t) (u,x) = (along ask t) (u,0) + (along ask t) (0,x)
      rw [← map_add]
      simp
    rw [eq]
  have count (t : Bits q) (x : Bits m) (v : Bits h) (reached : ans v x = t) :
      (Finset.univ.filter fun u => ans u x = t).card = 2 ^ (h - rankW (A t)) := by
    have ev := (path v x t).1 reached
    have eq : (Finset.univ.filter fun u => ans u x = t) =
        (Finset.univ.filter fun u => A t u = A t v) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, path]
      constructor
      · intro hu
        exact add_right_cancel (hu.trans ev.symm)
      · intro hu
        rw [hu]
        exact ev
    rw [eq, fiber_card]
  let S := Finset.univ.image fun u => ans u 0
  let e := (Fintype.equivFin (↥S)).symm
  have reindex (f : Bits q → ℕ) :
      (∑ i, f (e i).val) = ∑ t ∈ S, f t := (e.sum_comp (fun t : ↥S => f t.val)).trans (Finset.sum_coe_sort S f)
  refine ⟨_, fun i => rankW (A (e i).val), fun i => obstruction (A (e i).val) (B (e i).val), ⟨?_, ?_⟩, ?_⟩
  · intro i
    exact rankW_le _
  · rw [reindex (fun t => 2 ^ (h - rankW (A t)))]
    calc
      _ = ∑ t ∈ S, (Finset.univ.filter fun u => ans u 0 = t).card := by
        apply Finset.sum_congr rfl
        intro t ht
        obtain ⟨v, -, hv⟩ := Finset.mem_image.mp ht
        exact (count t 0 v hv).symm
      _ = (Finset.univ : Finset (Bits h)).card := (Finset.card_eq_sum_card_image _ _).symm
      _ = 2^h := bits_card h
  · intro x
    unfold mass
    rw [reindex (fun t => if obstruction (A t) (B t) x = 0 then 2 ^ (h-rankW (A t)) else 0)]
    calc
      _ ≤ ∑ t ∈ S, (Finset.univ.filter fun u => ans u x = t).card := by
        apply Finset.sum_le_sum
        intro t ht
        split_ifs with ob
        · obtain ⟨v, -, hv⟩ := Finset.mem_image.mp ht
          have av : A t v = t := by simpa using (path v 0 t).1 hv
          obtain ⟨w, hw⟩ := (obstruction_zero (A t) (B t) x).1 ob
          have witness : ans (v-w) x = t := (path _ _ _).2 (by rw [map_sub, hw, sub_add_cancel, av])
          exact (count t x _ witness).symm.le
        · exact Nat.zero_le _
      _ = (Finset.univ.filter fun u => ans u x ∈ S).card := Finset.sum_card_fiberwise_eq_card_filter _ _ _
      _ ≤ rejected label x := by
        apply Finset.card_le_card
        intro u hu
        obtain ⟨v, -, hv⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hu).2
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, (readout u x).trans (by rw [← hv, ← readout, zeroReject])⟩

def atBit {b : ℕ} (u : Bits b) (i : ℕ) : K := if hi : i < b then u ⟨i,hi⟩ else 0
def cutBits {b : ℕ} (a : ℕ) (u : Bits b) : Bits a := fun j => atBit u j.val

theorem cut_self {a : ℕ} (w : Bits a) : cutBits a w = w := by
  funext i
  simp [cutBits, atBit, i.isLt]

theorem cut_comp {a b c : ℕ} (hab : a ≤ b) (w : Bits c) :
    cutBits a (cutBits b w) = cutBits a w := by
  funext i
  change atBit (cutBits b w) i.val = atBit w i.val
  simp [atBit, cutBits, i.isLt.trans_le hab]

def cutL (a b : ℕ) : Bits b →ₗ[K] Bits a :=
  LinearMap.pi fun i => if hi : i.val < b then LinearMap.proj (R := K) (φ := fun _ : Fin b => K) ⟨i.val,hi⟩ else 0

theorem cutL_apply {a b : ℕ} (u : Bits b) : cutL a b u = cutBits a u := by
  funext i
  by_cases hi : i.val < b <;> simp [cutL, cutBits, atBit, hi]

theorem prefix_card {a b : ℕ} (hab : a ≤ b) (word : Bits a) :
    (Finset.univ.filter fun u : Bits b => cutBits a u = word).card = 2^(b-a) := by
  classical
  have right (w : Bits a) : cutL a b (cutBits b w) = w := by rw [cutL_apply, cut_comp hab, cut_self]
  have onto : Function.Surjective (cutL a b) := fun w => ⟨_, right w⟩
  have rank : rankW (cutL a b) = a := by
    rw [rankW, LinearMap.range_eq_top.mpr onto, finrank_top, Module.finrank_fin_fun]
  have eq := fiber_card (cutL a b) (cutBits b word)
  rw [right, rank] at eq
  simpa only [cutL_apply] using eq

theorem pack_set {n h : ℕ} (d : Fin n → ℕ) (dh : ∀ i, d i ≤ h) (s : Finset (Fin n))
    (cap : ∑ i ∈ s, 2^(h-d i) ≤ 2^h) :
    ∃ code : (i : Fin n) → Bits (d i),
      ∀ (u : Bits h) (i j : Fin n), i ∈ s → j ∈ s →
      cutBits (d i) u = code i → cutBits (d j) u = code j → i = j := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases nonempty : s.Nonempty
    · obtain ⟨i, hi, mx⟩ := s.exists_max_image d nonempty
      let rest := s.erase i
      have sumEq : (∑ j ∈ rest, 2^(h-d j)) + 2^(h-d i) = ∑ j ∈ s, 2^(h-d j) :=
        Finset.sum_erase_add _ _ hi
      have capR : (∑ j ∈ rest, 2^(h-d j)) ≤ 2^h := (Nat.le_add_right _ _).trans (sumEq.le.trans cap)
      obtain ⟨code, unique⟩ := ih rest (Finset.erase_ssubset hi) capR
      let taken (j : Fin n) := Finset.univ.filter fun t : Bits (d i) => cutBits (d j) t = code j
      have relative : (∑ j ∈ rest, 2^(d i-d j)) * 2^(h-d i) = ∑ j ∈ rest, 2^(h-d j) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        have hjd := mx j (Finset.mem_erase.mp hj).2
        have hid := dh i
        rw [← pow_add, show d i-d j + (h-d i) = h-d j by omega]
      have whole : 2^(d i) * 2^(h-d i) = 2^h := by
        rw [← pow_add, show d i + (h-d i) = h by have := dh i; omega]
      have room : (∑ j ∈ rest, 2^(d i-d j)) < 2^(d i) := by
        by_contra! bad
        have large := Nat.mul_le_mul_right (2^(h-d i)) bad
        rw [relative, whole] at large
        have pos : 0 < 2^(h-d i) := Nat.pow_pos (by decide)
        omega
      have small : (rest.biUnion taken).card < (Finset.univ : Finset (Bits (d i))).card := calc
        _ ≤ ∑ j ∈ rest, (taken j).card := Finset.card_biUnion_le
        _ = ∑ j ∈ rest, 2^(d i-d j) :=
          Finset.sum_congr rfl fun j hj => prefix_card (mx j (Finset.mem_erase.mp hj).2) _
        _ < _ := by simpa only [Finset.card_univ, bits_card] using room
      obtain ⟨word, -, fresh⟩ := Finset.exists_mem_notMem_of_card_lt_card small
      have avoid (u : Bits h) (j : Fin n) (hj : j ∈ rest) (hit : cutBits (d i) u = word)
          (old : cutBits (d j) u = code j) : False := by
        apply fresh
        apply Finset.mem_biUnion.mpr
        refine ⟨j, hj, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        rw [← hit, cut_comp (mx j (Finset.mem_erase.mp hj).2), old]
      refine ⟨Function.update code i word, ?_⟩
      intro u a b ha hb ea eb
      by_cases ai : a = i <;> by_cases bi : b = i
      · exact ai.trans bi.symm
      · subst a
        rw [Function.update_self] at ea
        rw [Function.update_of_ne bi] at eb
        exact False.elim (avoid u b (Finset.mem_erase.mpr ⟨bi,hb⟩) ea eb)
      · subst b
        rw [Function.update_self] at eb
        rw [Function.update_of_ne ai] at ea
        exact False.elim (avoid u a (Finset.mem_erase.mpr ⟨ai,ha⟩) eb ea)
      · rw [Function.update_of_ne ai] at ea
        rw [Function.update_of_ne bi] at eb
        exact unique u a b (Finset.mem_erase.mpr ⟨ai,ha⟩) (Finset.mem_erase.mpr ⟨bi,hb⟩) ea eb
    · exact ⟨fun _ => 0, fun _ i _ hi => False.elim (nonempty ⟨i,hi⟩)⟩

theorem complete_code {n h q : ℕ} (d : Fin n → ℕ) (shape : Shape h q d) :
    ∃ (code : (i : Fin n) → Bits (d i)) (pick : Bits h → Fin n),
      (∀ u i, pick u = i ↔ cutBits (d i) u = code i) ∧
      ∀ (r : ℕ) (s : Bits r) (i j : Fin n), cutBits (d i) s = code i →
        cutBits (d j) s = code j → i = j := by
  classical
  have dh (i) : d i ≤ h := (le_min_iff.mp (shape.1 i)).1
  obtain ⟨code, unique⟩ := pack_set d dh Finset.univ shape.2.le
  let cells (i : Fin n) := Finset.univ.filter fun u : Bits h => cutBits (d i) u = code i
  have disjoint : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint cells := by
    intro i _ j _ ij
    apply Finset.disjoint_left.mpr
    intro u h1 h2
    exact ij (unique u i j (Finset.mem_univ _) (Finset.mem_univ _)
      (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2)
  have card : (Finset.univ.biUnion cells).card = 2^h := calc
    _ = ∑ i, (cells i).card := Finset.card_biUnion disjoint
    _ = ∑ i, 2 ^ (h-d i) := Finset.sum_congr rfl fun i _ => prefix_card (dh i) _
    _ = _ := shape.2
  have cover : Finset.univ.biUnion cells = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by rw [Finset.card_univ, bits_card, card])
  have coding (u : Bits h) : ∃ i, cutBits (d i) u = code i := by
    have mem : u ∈ Finset.univ.biUnion cells := cover ▸ Finset.mem_univ _
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp mem
    exact ⟨i, (Finset.mem_filter.mp hi).2⟩
  choose pick hp using coding
  refine ⟨code, pick, ?_, ?_⟩
  · intro u i
    exact ⟨fun e => e ▸ hp u, fun hi => unique u _ _ (Finset.mem_univ _) (Finset.mem_univ _) (hp u) hi⟩
  · intro r s i j hi hj
    apply unique (cutBits h s) i j (Finset.mem_univ _) (Finset.mem_univ _)
    · rwa [cut_comp (dh i)]
    · rwa [cut_comp (dh j)]

def concatenate {b q : ℕ} (word : Bits b) (tail : Bits (q-b)) : Bits q := fun j =>
  if hj : j.val < b then word ⟨j.val,hj⟩ else tail ⟨j.val-b, by omega⟩

theorem concatenate_prefix {b q : ℕ} (hb : b ≤ q) (word : Bits b) (tail : Bits (q-b)) :
    cutBits b (concatenate word tail) = word := by
  funext i
  simp [cutBits, atBit, concatenate, i.isLt, i.isLt.trans_le hb]

theorem concatenate_injective {b q : ℕ} (hb : b ≤ q) (word : Bits b) :
    Function.Injective (concatenate (q := q) word) := by
  intro z y eq
  funext i
  have e := congrFun eq (⟨b+i.val, by omega⟩ : Fin q)
  simpa [concatenate, Nat.not_lt.mpr (Nat.le_add_right b i.val)] using e

theorem cut_past {q a : ℕ} (t : Bits q) (j : Fin q) (h : a ≤ j.val) :
    cutBits a (past t j) = cutBits a t := by
  funext i
  have hi := i.isLt.trans_le h
  simp [cutBits, atBit, past, hi, hi.trans j.isLt]

def ready {n r : ℕ} (d : Fin n → ℕ) (code : (i : Fin n) → Bits (d i))
    (s : Bits r) (i : Fin n) : Prop :=
  d i ≤ r ∧ cutBits (d i) s = code i

def featureQuery {m h q n : ℕ} (d : Fin n → ℕ)
    (maps : (i : Fin n) → Bits m →ₗ[K] Bits (q-d i)) (j : Fin q) (i : Fin n) (hi : d i ≤ j.val) :
    (Bits h × Bits m) →ₗ[K] K :=
  (LinearMap.proj (R := K) (φ := fun _ : Fin (q-d i) => K) ⟨j.val-d i, by omega⟩).comp
    ((maps i).comp (LinearMap.snd K (Bits h) (Bits m)))

noncomputable def prefixQueries {m h q n : ℕ} (d : Fin n → ℕ) (code : (i : Fin n) → Bits (d i))
    (maps : (i : Fin n) → Bits m →ₗ[K] Bits (q-d i)) : Queries m h q := by
  classical
  exact fun j s =>
    if hit : ∃ i, ready d code s i then
      featureQuery d maps j hit.choose hit.choose_spec.1
    else if hj : j.val < h then
      (LinearMap.proj (R := K) (φ := fun _ : Fin h => K) ⟨j.val,hj⟩).comp (LinearMap.fst K (Bits h) (Bits m))
    else 0

theorem prefix_run {m h q n : ℕ} (d : Fin n → ℕ) (shape : Shape h q d) (code : (i : Fin n) → Bits (d i))
    (pick : Bits h → Fin n) (assign : ∀ u i, pick u = i ↔ cutBits (d i) u = code i)
    (unique : ∀ (r : ℕ) (s : Bits r) (i j : Fin n), cutBits (d i) s = code i → cutBits (d j) s = code j → i = j)
    (maps : (i : Fin n) → Bits m →ₗ[K] Bits (q-d i)) (u : Bits h) (x : Bits m) (j : Fin q) :
    let t := concatenate (code (pick u)) (maps (pick u) x)
    t j = prefixQueries d code maps j (past t j) (u,x) := by
  classical
  let i := pick u
  let t : Bits q := concatenate (code i) (maps i x)
  change t j = prefixQueries d code maps j (past t j) (u,x)
  have hq : d i ≤ q := (le_min_iff.mp (shape.1 i)).2
  have pref : cutBits (d i) t = code i := concatenate_prefix hq _ _
  have identify (l : Fin n) (hl : ready d code (past t j) l) : l = i :=
    unique q t l i ((cut_past t j hl.1).symm.trans hl.2) pref
  by_cases reached : d i ≤ j.val
  · have hit : ∃ l, ready d code (past t j) l := ⟨i, reached, (cut_past t j reached).trans pref⟩
    have eq : hit.choose = i := identify _ hit.choose_spec
    have same {l : Fin n} (hl : d l ≤ j.val) (e : l = i) :
        featureQuery (h := h) d maps j l hl = featureQuery d maps j i reached := by subst l; rfl
    rw [prefixQueries, dite_eq_left hit, same _ eq]
    simp [t, concatenate, Nat.not_lt.mpr reached, featureQuery]
  · have notHit : ¬ ∃ l, ready d code (past t j) l := by
      rintro ⟨l, hl⟩
      exact reached (identify l hl ▸ hl.1)
    have before : j.val < d i := Nat.lt_of_not_ge reached
    have hj : j.val < h := before.trans_le (le_min_iff.mp (shape.1 i)).1
    have word := congrFun ((assign u i).1 rfl) (⟨j.val,before⟩ : Fin (d i))
    simp only [cutBits, atBit, dite_eq_left hj] at word
    simp [prefixQueries, notHit, hj, t, concatenate, before, word]

theorem attainable {m h q n : ℕ} (d : Fin n → ℕ)
    (maps : (i : Fin n) → Bits m →ₗ[K] Bits (q-d i)) (shape : Shape h q d) :
    ∃ label : Bits h → Bits m → Bool, Feasible q label ∧
      ∀ x, rejected label x = mass (h := h) d maps x := by
  classical
  obtain ⟨code, pick, assign, unique⟩ := complete_code d shape
  let label (u : Bits h) (x : Bits m) := decide (maps (pick u) x ≠ 0)
  let ans (u : Bits h) (x : Bits m) := concatenate (q := q) (code (pick u)) (maps (pick u) x)
  let leaf (t : Bits q) := decide (¬ ∃ i : Fin n, t = concatenate (q := q) (code i) 0)
  refine ⟨label, ⟨prefixQueries d code maps, ans, leaf, prefix_run d shape code pick assign unique maps, ?_⟩, ?_⟩
  · intro u x
    have eq : (∃ i : Fin n, ans u x = concatenate (q := q) (code i) 0) ↔ maps (pick u) x = 0 := by
      constructor
      · rintro ⟨i, hi⟩
        have first : cutBits (d (pick u)) (ans u x) = code (pick u) :=
          concatenate_prefix (le_min_iff.mp (shape.1 _)).2 _ _
        have second : cutBits (d i) (ans u x) = code i := by
          rw [hi]
          exact concatenate_prefix (le_min_iff.mp (shape.1 _)).2 _ _
        have same := unique q (ans u x) i (pick u) second first
        subst i
        exact concatenate_injective (le_min_iff.mp (shape.1 _)).2 _ hi
      · intro kernel
        exact ⟨pick u, by simp [ans, kernel]⟩
    simp only [label, leaf, eq, ne_eq]
  · intro x
    let zeros := Finset.univ.filter fun i => maps i x = 0
    have classes (i : Fin n) : (Finset.univ.filter fun u => pick u = i).card = 2^(h-d i) := by
      have same : (Finset.univ.filter fun u => pick u = i) =
          (Finset.univ.filter fun u : Bits h => cutBits (d i) u = code i) := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, assign]
      rw [same, prefix_card (le_min_iff.mp (shape.1 i)).1]
    calc
      rejected label x = (Finset.univ.filter fun u => pick u ∈ zeros).card := by
        apply congrArg Finset.card
        ext u
        simp [label, zeros]
      _ = ∑ i ∈ zeros, (Finset.univ.filter fun u => pick u = i).card :=
        (Finset.sum_card_fiberwise_eq_card_filter Finset.univ zeros pick).symm
      _ = ∑ i ∈ zeros, 2^(h-d i) := Finset.sum_congr rfl fun i _ => classes i
      _ = mass (h := h) d maps x := by simp only [zeros, Finset.sum_filter, mass]

end PEqualNP.Outside.L_lib_680_aux

theorem PEqualNP.Outside.L_lib_680 : (∀ (m h q : Nat),
  let U := Fin h → ZMod 2
  let V := Fin m → ZMod 2
  let feasible := fun (label : U → V → Bool) =>
    ∃ (ask : (j : Fin q) → (Fin j.val → ZMod 2) → ((U × V) →ₗ[ZMod 2] ZMod 2))
      (answers : U → V → Fin q → ZMod 2) (leaf : (Fin q → ZMod 2) → Bool),
      (∀ (u : U) (x : V) (j : Fin q), answers u x j =
        ask j (fun i => answers u x ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) (u,x)) ∧
      ∀ (u : U) (x : V), label u x = leaf (answers u x)
  let rejected := fun (label : U → V → Bool) (x : V) =>
    ((Finset.univ : Finset U).filter (fun witness => label witness x = false)).card
  let shape := fun (n : Nat) (depth : Fin n → Nat) =>
    (∀ i, depth i ≤ min h q) ∧ (∑ i : Fin n, 2^(h-depth i)) = 2^h
  let mass := fun (n : Nat) (depth : Fin n → Nat)
    (maps : (i : Fin n) → V →ₗ[ZMod 2] (Fin (q-depth i) → ZMod 2)) (x : V) =>
      ∑ i : Fin n, if maps i x = 0 then 2^(h-depth i) else 0
  (∀ label : U → V → Bool, feasible label → (∀ witness, label witness 0 = false) →
    ∃ (n : Nat) (depth : Fin n → Nat)
      (maps : (i : Fin n) → V →ₗ[ZMod 2] (Fin (q-depth i) → ZMod 2)),
      shape n depth ∧ ∀ x : V, mass n depth maps x ≤ rejected label x) ∧
  (∀ (n : Nat) (depth : Fin n → Nat)
    (maps : (i : Fin n) → V →ₗ[ZMod 2] (Fin (q-depth i) → ZMod 2)),
    shape n depth → ∃ label : U → V → Bool, feasible label ∧
      ∀ x : V, rejected label x = mass n depth maps x)) := by
  intro m h q
  dsimp only
  exact ⟨fun label feasible zeroReject =>
      PEqualNP.Outside.L_lib_680_aux.lower_envelope (m := m) (h := h) (q := q) label feasible zeroReject,
    fun n d maps shape =>
      PEqualNP.Outside.L_lib_680_aux.attainable (m := m) (h := h) (q := q) (n := n) d maps shape⟩
