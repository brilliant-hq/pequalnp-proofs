import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19198_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem len (gs : List Gate) (x : List Bool) : (gs.foldl stp x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih => simp [List.foldl_append, stp, ih]; omega

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

/-- Only the wires of a set of at most `|R| + |gs|` wires decide the wires in `R`. -/
theorem cone (N : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) (R : Finset ℕ) :
    ∃ R' : Finset ℕ, R'.card ≤ R.card + gs.length ∧ ∀ x y : List Bool, x.length = N → y.length = N →
      (∀ i ∈ R', x.getD i false = y.getD i false) →
      ∀ w ∈ R, (gs.foldl stp x).getD w false = (gs.foldl stp y).getD w false := by
  induction gs using List.reverseRecOn generalizing R with
  | nil => exact ⟨R, by simp, fun x y _ _ h => by simpa using h⟩
  | append_singleton gs g ih =>
    have hg' : ∀ g ∈ gs, g.inputs.length ≤ 2 := fun g' h => hg g' (by simp [h])
    have h2 : g.inputs.length ≤ 2 := hg g (by simp)
    let t := N + gs.length
    let R0 := if t ∈ R then R.erase t ∪ g.inputs.toFinset else R
    obtain ⟨R', hc, hR'⟩ := ih hg' R0
    refine ⟨R', ?_, ?_⟩
    · have : R0.card ≤ R.card + 1 := by
        simp only [R0]; split_ifs with ht
        · have := Finset.card_union_le (R.erase t) g.inputs.toFinset
          have := Finset.card_erase_of_mem ht
          have := List.toFinset_card_le g.inputs
          have : 0 < R.card := Finset.card_pos.2 ⟨t, ht⟩
          omega
        · omega
      simp; omega
    · intro x y hx hy hxy w hw
      have e := hR' x y hx hy hxy
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, stp]
      rw [getD_snoc, getD_snoc, len, len, hx, hy]
      split_ifs with h1 h3
      · exact e w (by simp only [R0]; split_ifs <;> simp_all; omega)
      · have ht : t ∈ R := by simp only [t]; rw [← h3]; exact hw
        congr 1
        refine List.map_congr_left fun i hi => e i ?_
        simp [R0, ht, hi]
      · rfl

theorem oe {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega

end PEqualNP.Outside.L_meta_19198_aux

open PEqualNP.Outside.L_meta_19198_aux PEqualNP.CircuitLowerBounds PEqualNP.Represents in
theorem PEqualNP.Outside.L_meta_19198 : ∀ (n : ℕ) (A : Fin n → Fin n → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ n → (∀ u u' : Fin n, u ≠ u' → ∃ v, A u v ≠ A u' v) → (∀ v v' : Fin n, v ≠ v' → ∃ u, A u v ≠ A u v') → PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → 2 * n - 3 ≤ C.size := by
  intro n A C hn hrow hcol hF hR
  obtain ⟨R', hc, hR'⟩ := cone (n + n) C.gates (fun g hg => (hF g hg).2) {C.output}
  rw [Finset.card_singleton] at hc
  have key : ∀ u u' v v' : Fin n, (∀ i ∈ R', ((oneEach u v).getD i false = true ↔
      (oneEach u' v').getD i false = true)) → A u v = A u' v' := by
    intro u u' v v' h
    have e1 := hR u v
    have e2 := hR u' v'
    simp only [Circuit.eval, Circuit.wires] at e1 e2
    change (C.gates.foldl stp _).getD _ _ = _ at e1 e2
    rw [← e1, ← e2]
    exact hR' _ _ (by simp [oneEach]) (by simp [oneEach])
      (fun i hi => Bool.eq_iff_iff.2 (h i hi)) _ (Finset.mem_singleton_self _)
  let F := (Finset.range (n + n)).filter (· ∉ R')
  have hlo : (F.filter (· < n)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [F, Finset.mem_filter, Finset.mem_range] at ha hb
    by_contra hab
    obtain ⟨v, hv⟩ := hrow ⟨a, ha.2⟩ ⟨b, hb.2⟩ (fun e => hab (congrArg Fin.val e))
    refine hv (key _ _ v v fun i hi => ?_)
    have : i ≠ a := fun e => ha.1.2 (e ▸ hi)
    have : i ≠ b := fun e => hb.1.2 (e ▸ hi)
    simp only [oe]
    constructor <;> intro h <;> omega
  have hhi : (F.filter (¬ · < n)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [F, Finset.mem_filter, Finset.mem_range] at ha hb
    by_contra hab
    obtain ⟨u, hu⟩ := hcol ⟨a - n, by omega⟩ ⟨b - n, by omega⟩
      (fun e => hab (by have := congrArg Fin.val e; simp at this; omega))
    refine hu (key _ _ _ _ fun i hi => ?_)
    have : i ≠ a := fun e => ha.1.2 (e ▸ hi)
    have : i ≠ b := fun e => hb.1.2 (e ▸ hi)
    simp only [oe]
    constructor <;> intro h <;> omega
  have hF2 : F.card ≤ 2 := by
    have := (Finset.card_filter_add_card_filter_not (s := F) (· < n))
    omega
  have h3 := Finset.card_filter_add_card_filter_not (s := Finset.range (n + n)) (· ∈ R')
  have h4 := Finset.card_le_card (fun x hx => (Finset.mem_filter.1 hx).2 :
    (Finset.range (n + n)).filter (· ∈ R') ⊆ R')
  rw [Finset.card_range] at h3
  change _ + F.card = _ at h3
  simp only [Circuit.size]
  omega
