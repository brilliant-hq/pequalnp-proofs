import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25419_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem len (gs : List Gate) (x : List Bool) : (gs.foldl stp x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [stp]; omega

private theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

private theorem pre (gs : List Gate) : ∀ (x : List Bool) (w : ℕ), w < x.length →
    (gs.foldl stp x).getD w false = x.getD w false := by
  induction gs with
  | nil => intro x w _; rfl
  | cons g gs ih =>
    intro x w h
    rw [List.foldl_cons, ih _ _ (by simp [stp]; omega), stp, getD_snoc, if_pos h]

private theorem oe {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega

private def chain (b a : ℕ) : List ℕ → List Gate
  | [] => []
  | c :: L => ⟨GateOp.or, [a, c]⟩ :: chain (b + 1) b L

private def last (b a : ℕ) : List ℕ → ℕ
  | [] => a
  | _ :: L => last (b + 1) b L

private theorem chain_good (b a : ℕ) (L : List ℕ) :
    ∀ g ∈ chain b a L, g.op = GateOp.or ∧ g.inputs.length ≤ 2 := by
  induction L generalizing b a with
  | nil => simp [chain]
  | cons c L ih =>
    intro g hg
    simp only [chain, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp
    · exact ih _ _ g hg

private theorem chain_len (b a : ℕ) (L : List ℕ) : (chain b a L).length = L.length := by
  induction L generalizing b a with
  | nil => rfl
  | cons c L ih => simp [chain, ih]

private theorem last_lt (L : List ℕ) : ∀ b a : ℕ, a < b → last b a L < b + L.length := by
  induction L with
  | nil => intro b a h; simpa [last] using h
  | cons c L ih => intro b a _; have := ih (b + 1) b (by omega); simp [last]; omega

private theorem anyc {f g : ℕ → Bool} : ∀ (L : List ℕ), (∀ c ∈ L, f c = g c) → L.any f = L.any g
  | [], _ => rfl
  | c :: L, h => by
    rw [List.any_cons, List.any_cons, h c (by simp), anyc L fun c' h' => h c' (by simp [h'])]

private theorem chain_val (L : List ℕ) : ∀ (x : List Bool) (a : ℕ), (∀ c ∈ L, c < x.length) →
    a < x.length →
    ((chain x.length a L).foldl stp x).getD (last x.length a L) false =
      (x.getD a false || L.any fun c => x.getD c false) := by
  induction L with
  | nil => intro x a _ ha; simp [chain, last]
  | cons c L ih =>
    intro x a hc ha
    have hl : (stp x ⟨GateOp.or, [a, c]⟩).length = x.length + 1 := by simp [stp]
    have hc' : ∀ c' ∈ L, c' < (stp x ⟨GateOp.or, [a, c]⟩).length := fun c' h => by
      have := hc c' (by simp [h]); omega
    have h2 := ih (stp x ⟨GateOp.or, [a, c]⟩) x.length hc' (by omega)
    simp only [chain, last, List.foldl_cons]
    rw [hl] at h2
    have : ∀ c' ∈ L, (stp x ⟨GateOp.or, [a, c]⟩).getD c' false = x.getD c' false :=
      fun c' h => by rw [stp, getD_snoc, if_pos (hc c' (by simp [h]))]
    rw [h2, anyc L this, stp, getD_snoc, if_neg (lt_irrefl _), if_pos rfl]
    simp [GateOp.eval, Bool.or_assoc]

private def Builds {n : ℕ} (f : Fin n → Fin n → Bool) (cost : ℕ) : Prop :=
  ∀ b, n+n ≤ b → ∃ (gs : List Gate) (o : ℕ),
    Monotone2 ⟨gs,o⟩ ∧ gs.length = cost ∧ o < b+cost ∧
    ∀ u v (w : List Bool), w.length = b →
      (∀ j < n+n, w.getD j false = (oneEach u v).getD j false) →
      (gs.foldl stp w).getD o false = f u v

private theorem combine {n s t : ℕ} {f h : Fin n → Fin n → Bool}
    (hf : Builds f s) (hh : Builds h t) (op : GateOp) (hop : op = .and ∨ op = .or) :
    Builds (fun u v => op.eval [f u v,h u v]) (s+t+1) := by
  intro b hb
  obtain ⟨gs,o,good,lg,ho,hg⟩ := hf b hb
  obtain ⟨ts,q,good',lt',hq,ht⟩ := hh (b+s) (by omega)
  let g : Gate := ⟨op,[o,q]⟩
  refine ⟨(gs ++ ts) ++ [g], b+s+t, ?_, by simp [lg,lt',Nat.add_assoc], by omega, ?_⟩
  · intro a ha
    change a ∈ (gs ++ ts) ++ [g] at ha
    simp only [List.mem_append,List.mem_singleton] at ha
    rcases ha with (ha|ha)|rfl
    · exact good a ha
    · exact good' a ha
    · rcases hop with rfl | rfl <;> simp [g]
  · intro u v w hw hp
    let y := gs.foldl stp w
    let z := ts.foldl stp y
    have ly : y.length = b+s := by rw [show y = gs.foldl stp w from rfl,len,hw,lg]
    have lz : z.length = b+s+t := by rw [show z = ts.foldl stp y from rfl,len,ly,lt']
    have hy : ∀ j < n+n, y.getD j false = (oneEach u v).getD j false := by
      intro j hj
      exact (pre gs w j (by omega)).trans (hp j hj)
    have vo : z.getD o false = f u v :=
      (pre ts y o (by omega)).trans (hg u v w hw hp)
    have vq : z.getD q false = h u v := ht u v y ly hy
    simp only [List.foldl_append,List.foldl_cons,List.foldl_nil]
    change (stp z g).getD (b+s+t) false = _
    rw [stp,getD_snoc,if_neg (by omega),if_pos lz.symm]
    change op.eval [z.getD o false,z.getD q false] = _
    rw [vo,vq]

private theorem group {n : ℕ} (L : List ℕ) (non : L ≠ []) (hl : ∀ i ∈ L, i < n+n) :
    Builds (fun u v : Fin n => L.any (fun i => (oneEach u v).getD i false)) (L.length-1) := by
  cases L with
  | nil => contradiction
  | cons a L =>
    intro b hb
    have ha := hl a List.mem_cons_self
    have hr : ∀ i ∈ L, i < n+n := fun i h => hl i (List.mem_cons_of_mem a h)
    refine ⟨chain b a L,last b a L,?_,by simp [chain_len],?_,?_⟩
    · intro g hg
      obtain ⟨hg1,hg2⟩ := chain_good b a L g hg
      exact ⟨by simp [hg1],hg2⟩
    · simpa using last_lt L b a (by omega)
    · intro u v w hw hp
      subst b
      dsimp only
      rw [chain_val L w a (fun i h => lt_of_lt_of_le (hr i h) hb) (by omega),
        hp a ha, List.any_cons, anyc L (fun i h => hp i (hr i h))]

private theorem groupSet {n : ℕ} (S : Finset (Fin n)) (hs : S.Nonempty)
    (index : Fin n → ℕ) (pick : Fin n → Fin n → Fin n)
    (bound : ∀ a, index a < n+n)
    (read : ∀ u v a, (oneEach u v).getD (index a) false = true ↔ a = pick u v) :
    Builds (fun u v => decide (pick u v ∈ S)) (S.card-1) := by
  classical
  let L := S.toList.map index
  have lenL : L.length = S.card := by simp [L]
  have nn : L ≠ [] := by
    intro h
    have hz : L.length = 0 := by rw [h]; rfl
    have := hs.card_pos
    omega
  have h := group (n := n) L nn (by
    intro i hi
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hi
    exact bound a)
  have vals : (fun u v : Fin n => L.any (fun i => (oneEach u v).getD i false)) =
      (fun u v => decide (pick u v ∈ S)) := by
    funext u v
    apply Bool.eq_iff_iff.mpr
    simp [L, List.any_eq_true]
    change (∃ x ∈ S, (oneEach u v).getD (index x) false = true) ↔ _
    constructor
    · rintro ⟨a,ha,hr⟩
      exact (read u v a).mp hr ▸ ha
    · intro hp
      exact ⟨pick u v, hp, (read u v _).mpr rfl⟩
  rwa [vals,lenL] at h

private theorem rows {n : ℕ} (S : Finset (Fin n)) (hs : S.Nonempty) :
    Builds (fun u (_ : Fin n) => decide (u ∈ S)) (S.card-1) := by
  apply groupSet S hs Fin.val (fun u _ => u)
  · intro a; have := a.isLt; omega
  · intro u v a
    rw [oe, Fin.ext_iff]
    have := a.isLt
    omega

private theorem cols {n : ℕ} (S : Finset (Fin n)) (hs : S.Nonempty) :
    Builds (fun (_ : Fin n) v => decide (v ∈ S)) (S.card-1) := by
  apply groupSet S hs (fun a => n+a.val) (fun _ v => v)
  · intro a; have := a.isLt; omega
  · intro u v a
    rw [oe, Fin.ext_iff]
    have := u.isLt
    omega

end PEqualNP.Outside.L_meta_25419_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Outside.L_meta_25419_aux

theorem PEqualNP.Outside.L_meta_25419 : (∀ (n : ℕ) (S T : Finset (Fin n)), 3 ≤ n → S.Nonempty → Sᶜ.Nonempty → T.Nonempty → Tᶜ.Nonempty → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide ((u ∈ S ∧ v ∈ T) ∨ (u ∉ S ∧ v ∉ T))) (2 * n - 1)) := by
  intro n S T _ hS hSc hT hTc
  have a := combine (rows S hS) (cols T hT) .and (Or.inl rfl)
  have b := combine (rows Sᶜ hSc) (cols Tᶜ hTc) .and (Or.inl rfl)
  obtain ⟨gs,o,hg,hl,_,hout⟩ := combine a b .or (Or.inr rfl) (n+n) le_rfl
  refine ⟨⟨gs,o⟩,hg,?_,?_⟩
  · change gs.length ≤ 2*n-1
    rw [hl]
    have h1 := Finset.card_compl_add_card S
    have h2 := Finset.card_compl_add_card T
    simp only [Fintype.card_fin] at h1 h2
    have := hS.card_pos
    have := hSc.card_pos
    have := hT.card_pos
    have := hTc.card_pos
    omega
  · intro u v
    have hv := hout u v (oneEach u v) (by simp [oneEach]) (fun _ _ => rfl)
    change (gs.foldl stp (oneEach u v)).getD o false = _
    simpa [GateOp.eval] using hv
