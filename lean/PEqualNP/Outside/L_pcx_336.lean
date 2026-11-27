import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_336_aux

open Classical
open PEqualNP.ProofComplexity

private def join (a b : ℕ) : ℕ := if a = b then a + 1 else max a b

private lemma join_comm (a b : ℕ) : join a b = join b a := by
  unfold join
  by_cases h : a = b
  · subst h; simp
  · have h' : b ≠ a := Ne.symm h
    simp [h, h', max_comm]

private lemma join_mono {a a' b b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    join a b ≤ join a' b' := by
  unfold join
  split_ifs <;> omega

private lemma le_join_left (a b : ℕ) : a ≤ join a b := by
  unfold join; split_ifs <;> omega

private lemma le_join_right (a b : ℕ) : b ≤ join a b := by
  unfold join; split_ifs <;> omega

private lemma min_add_one_le_join (a b : ℕ) : min a b + 1 ≤ join a b := by
  unfold join; split_ifs <;> omega

private lemma join_add_right (a b c : ℕ) : join (a + c) (b + c) = join a b + c := by
  unfold join
  by_cases h : a = b
  · subst h; simp; omega
  · simp [h, Nat.add_max_add_right]

private def shape (N J : Finset (List Bool)) : Prop :=
  [] ∈ N ∧ J ⊆ N ∧
  (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
  ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N

private lemma shape_take_mem_J {N J : Finset (List Bool)} (hsh : shape N J) :
    ∀ (p : List Bool), p ∈ N → ∀ (k : ℕ), k < p.length → p.take k ∈ J := by
  intro p
  induction p using List.reverseRecOn with
  | nil => intro _ k hk; simp at hk
  | append_singleton p' b ih =>
      intro hp k hk
      have hp'J : p' ∈ J := hsh.2.2.1 p' b hp
      have hp'N : p' ∈ N := hsh.2.1 hp'J
      simp only [List.length_append, List.length_singleton] at hk
      by_cases hlt : k < p'.length
      · rw [List.take_append_of_le_length (le_of_lt hlt)]
        exact ih hp'N k hlt
      · have hkeq : k = p'.length := by omega
        subst hkeq
        simpa using hp'J

private lemma list_ofFn_eq_of_eq {α : Type} {m₁ m₂ : ℕ} (h : m₁ = m₂) (f : ℕ → α) :
    List.ofFn (fun j : Fin m₁ => f j.val) = List.ofFn (fun j : Fin m₂ => f j.val) := by
  subst h; rfl

private lemma list_ofFn_snoc {α : Type} :
    ∀ (m : ℕ) (f : ℕ → α),
      List.ofFn (fun j : Fin (m + 1) => f j.val) =
        List.ofFn (fun j : Fin m => f j.val) ++ [f m]
  | 0, f => by simp
  | m + 1, f => by
      conv_lhs => rw [List.ofFn_succ]
      conv_rhs => rw [List.ofFn_succ, List.cons_append]
      congr 1
      exact list_ofFn_snoc m (fun k => f (k + 1))

private lemma ofFn_nodup_ne {α : Type} :
    ∀ {m : ℕ} {f : Fin m → α}, (List.ofFn f).Nodup →
      ∀ {i j : Fin m}, i ≠ j → f i ≠ f j
  | 0, _, _, i, _ => fun _ => i.elim0
  | m + 1, f, hnd, i, j => by
      rw [List.ofFn_succ, List.nodup_cons] at hnd
      revert j
      refine Fin.cases ?_ ?_ i
      · intro j
        refine Fin.cases ?_ ?_ j
        · intro hne; exact (hne rfl).elim
        · intro j' _ heq
          exact hnd.1 (List.mem_ofFn.mpr ⟨j', heq.symm⟩)
      · intro i' j
        refine Fin.cases ?_ ?_ j
        · intro _ heq
          exact hnd.1 (List.mem_ofFn.mpr ⟨i', heq⟩)
        · intro j' hne
          exact ofFn_nodup_ne hnd.2 (fun hij => hne (congrArg Fin.succ hij))

private inductive BTree (I L : Type)
  | leaf (l : L)
  | node (i : I) (lo hi : BTree I L)

namespace BTree

private def anyLeaf {I L : Type} : BTree I L → L
  | leaf l => l
  | node _ lo _ => lo.anyLeaf

private def nodes {I L : Type} : BTree I L → Finset (List Bool)
  | leaf _ => {[]}
  | node _ lo hi =>
      insert [] ((lo.nodes.image (fun p => false :: p)) ∪ (hi.nodes.image (fun p => true :: p)))

private def internals {I L : Type} : BTree I L → Finset (List Bool)
  | leaf _ => ∅
  | node _ lo hi =>
      insert [] ((lo.internals.image (fun p => false :: p)) ∪ (hi.internals.image (fun p => true :: p)))

private def get {I L : Type} : BTree I L → List Bool → Option (BTree I L)
  | t, [] => some t
  | leaf _, _ :: _ => none
  | node _ lo hi, b :: bs => if b then hi.get bs else lo.get bs

private def qAt {V Ans : Type} (t : BTree V Ans) (p : List Bool) : Option V :=
  match t.get p with
  | some (node v _ _) => some v
  | _ => none

private lemma nil_mem_nodes {I L : Type} (t : BTree I L) : [] ∈ t.nodes := by
  cases t <;> simp [nodes]

private lemma internals_subset_nodes {I L : Type} (t : BTree I L) : t.internals ⊆ t.nodes := by
  induction t with
  | leaf _ => simp [internals]
  | node _ lo hi ihlo ihhi =>
      intro p hp
      simp only [internals, nodes, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp ⊢
      rcases hp with rfl | (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨q, ihlo hq, rfl⟩)
      · exact Or.inr (Or.inr ⟨q, ihhi hq, rfl⟩)

private lemma mem_nodes_iff_isSome_get {I L : Type} (t : BTree I L) (p : List Bool) :
    p ∈ t.nodes ↔ (t.get p).isSome := by
  induction t generalizing p with
  | leaf _ =>
      cases p <;> simp [nodes, get]
  | node _ lo hi ihlo ihhi =>
      cases p with
      | nil => simp [nodes, get]
      | cons b bs =>
          cases b <;> simp [nodes, get, ihlo, ihhi]

private lemma mem_internals_iff_get_node {I L : Type} (t : BTree I L) (p : List Bool) :
    p ∈ t.internals ↔ ∃ i lo hi, t.get p = some (node i lo hi) := by
  induction t generalizing p with
  | leaf _ =>
      cases p <;> simp [internals, get]
  | node i lo hi ihlo ihhi =>
      cases p with
      | nil => simp [internals, get]
      | cons b bs =>
          cases b <;> simp [internals, get, ihlo, ihhi]

private lemma mem_leaves_iff_get_leaf {I L : Type} (t : BTree I L) (p : List Bool) :
    p ∈ t.nodes \ t.internals ↔ ∃ l, t.get p = some (leaf l) := by
  rw [Finset.mem_sdiff, mem_nodes_iff_isSome_get, mem_internals_iff_get_node]
  cases h : t.get p with
  | none => simp
  | some s =>
      cases s <;> simp

private lemma get_append_singleton {I L : Type} (t : BTree I L) (p : List Bool) (b : Bool) :
    t.get (p ++ [b]) =
      match t.get p with
      | some (node _ lo hi) => if b then some hi else some lo
      | _ => none := by
  induction t generalizing p with
  | leaf _ =>
      cases p <;> simp [get]
  | node _ lo hi ihlo ihhi =>
      cases p with
      | nil =>
          cases b <;> simp [get]
      | cons c cs =>
          cases c <;> simp [get, ihlo, ihhi]

private lemma shape_nodes_internals {I L : Type} (t : BTree I L) :
    shape t.nodes t.internals := by
  refine ⟨nil_mem_nodes t, internals_subset_nodes t, ?_, ?_⟩
  · intro p b hp
    rw [mem_nodes_iff_isSome_get, get_append_singleton] at hp
    rw [mem_internals_iff_get_node]
    cases h : t.get p with
    | none => simp [h] at hp
    | some s =>
        cases s with
        | leaf _ => simp [h] at hp
        | node i lo hi => exact ⟨i, lo, hi, rfl⟩
  · intro p hp
    rw [mem_internals_iff_get_node] at hp
    obtain ⟨i, lo, hi, hget⟩ := hp
    constructor <;> rw [mem_nodes_iff_isSome_get, get_append_singleton, hget] <;> simp

private def height {I L : Type} : BTree I L → ℕ
  | leaf _ => 0
  | node _ lo hi => 1 + max lo.height hi.height

private def rank {I L : Type} : BTree I L → ℕ
  | leaf _ => 0
  | node _ lo hi => join lo.rank hi.rank

private def wHeight {I L : Type} (len : I → ℕ) : BTree I L → ℕ
  | leaf _ => 0
  | node i lo hi => len i + max (lo.wHeight len) (hi.wHeight len)

private def wRank {I L : Type} (fee : I → ℕ) (pay : L → ℕ) : BTree I L → ℕ
  | leaf l => pay l
  | node i lo hi => fee i + join (lo.wRank fee pay) (hi.wRank fee pay)

private lemma length_le_height {I L : Type} (t : BTree I L) (p : List Bool) (hp : p ∈ t.nodes) :
    p.length ≤ t.height := by
  induction t generalizing p with
  | leaf _ =>
      simp only [nodes, Finset.mem_singleton] at hp
      subst hp; simp [height]
  | node _ lo hi ihlo ihhi =>
      simp only [nodes, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
      rcases hp with rfl | (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
      · simp [height]
      · have := ihlo q hq
        simp only [height, List.length_cons]
        omega
      · have := ihhi q hq
        simp only [height, List.length_cons]
        omega

private def ofShapeAux {I L : Type} (N J : Finset (List Bool))
    (fi : List Bool → I) (fl : List Bool → L) : ℕ → List Bool → BTree I L
  | 0, p => leaf (fl p)
  | fuel + 1, p =>
      if p ∈ J then
        node (fi p) (ofShapeAux N J fi fl fuel (p ++ [false]))
                    (ofShapeAux N J fi fl fuel (p ++ [true]))
      else leaf (fl p)

end BTree

section ParityLift

variable {n : ℕ} {w : Fin n → ℕ}

private abbrev Raw (w : Fin n → ℕ) := (i : Fin n) × Fin (w i)

private def parity (y : Raw w → Bool) (i : Fin n) : Bool :=
  decide (Odd ((Finset.univ : Finset (Fin (w i))).filter (fun j => y ⟨i, j⟩ = true)).card)

private def liftAx (F : Set (Clause (Fin n))) (A : Clause (Raw w)) : Prop :=
  ∃ C ∈ F, ∃ y : Raw w → Bool, (∀ lit ∈ C, parity y lit.1 ≠ lit.2) ∧
    A = ((Finset.univ : Finset (Raw w)).filter (fun b => b.1 ∈ C.image Prod.fst)).image
      (fun b => (b, !(y b)))

private lemma parity_update (y : Raw w → Bool) (i : Fin n) (j : Fin (w i)) (b : Bool) :
    parity (Function.update y ⟨i, j⟩ b) i =
      if y ⟨i, j⟩ = b then parity y i else !(parity y i) := by
  by_cases h : y ⟨i, j⟩ = b
  · simp only [h, ↓reduceIte]
    have heq : Function.update y ⟨i, j⟩ b = y := by
      funext k
      by_cases hk : k = ⟨i, j⟩
      · subst hk; simp [h]
      · simp [hk]
    rw [heq]
  · simp only [h, ↓reduceIte, parity]
    let S := (Finset.univ : Finset (Fin (w i))).filter (fun j' => y ⟨i, j'⟩ = true)
    let S' := (Finset.univ : Finset (Fin (w i))).filter
      (fun j' => Function.update y ⟨i, j⟩ b ⟨i, j'⟩ = true)
    have hcard : S'.card = if b = true then S.card + 1 else S.card - 1 := by
      cases hb : b
      · have hy : y ⟨i, j⟩ = true := by cases hy' : y ⟨i, j⟩ <;> simp_all
        have hjS : j ∈ S := by simp [S, hy]
        have hS' : S' = S.erase j := by
          ext j'
          by_cases hj' : j' = j
          · subst hj'; simp [S', S, hb]
          · have hne : (⟨i, j'⟩ : Raw w) ≠ ⟨i, j⟩ := by intro h0; apply hj'; cases h0; rfl
            simp [S', S, hj', hne]
        rw [hS', Finset.card_erase_of_mem hjS]
        simp
      · have hy : y ⟨i, j⟩ = false := by cases hy' : y ⟨i, j⟩ <;> simp_all
        have hjS : j ∉ S := by simp [S, hy]
        have hS' : S' = insert j S := by
          ext j'
          by_cases hj' : j' = j
          · subst hj'; simp [S', S, hb]
          · have hne : (⟨i, j'⟩ : Raw w) ≠ ⟨i, j⟩ := by intro h0; apply hj'; cases h0; rfl
            simp [S', S, hj', hne]
        rw [hS', Finset.card_insert_of_notMem hjS]
        simp
    change decide (Odd S'.card) = !decide (Odd S.card)
    rw [hcard]
    cases hb : b
    · have hy : y ⟨i, j⟩ = true := by cases hy' : y ⟨i, j⟩ <;> simp_all
      have hpos : 0 < S.card := Finset.card_pos.mpr ⟨j, by simp [S, hy]⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases ho : Odd S.card
      · have hne : ¬ Odd (S.card - 1) := by
          intro h1; obtain ⟨k, hk⟩ := h1; obtain ⟨m, hm⟩ := ho; omega
        simp [ho, hne]
      · have he : Odd (S.card - 1) := by
          rw [Nat.not_odd_iff_even] at ho
          obtain ⟨k, hk⟩ := ho
          exact ⟨k - 1, by omega⟩
        simp [ho, he]
    · simp only [↓reduceIte]
      by_cases ho : Odd S.card
      · have hne : ¬ Odd (S.card + 1) := by
          intro h1; obtain ⟨k, hk⟩ := h1; obtain ⟨m, hm⟩ := ho; omega
        simp [ho, hne]
      · have he : Odd (S.card + 1) := by
          rw [Nat.not_odd_iff_even] at ho
          obtain ⟨k, hk⟩ := ho
          exact ⟨k, by omega⟩
        simp [ho, he]

private lemma parity_congr {y₁ y₂ : Raw w → Bool} {i : Fin n}
    (h : ∀ j : Fin (w i), y₁ ⟨i, j⟩ = y₂ ⟨i, j⟩) : parity y₁ i = parity y₂ i := by
  unfold parity
  apply congrArg (fun S : Finset (Fin (w i)) => decide (Odd S.card))
  ext j
  simp [h j]

private def Agrees {V : Type} (ρ : V → Option Bool) (y : V → Bool) : Prop :=
  ∀ v b, ρ v = some b → y v = b

private lemma agrees_update {V : Type} [DecidableEq V] {ρ : V → Option Bool} {y : V → Bool}
    {v : V} {b : Bool} (h : Agrees ρ y) (hv : y v = b) :
    Agrees (Function.update ρ v (some b)) y := by
  intro u c huc
  by_cases huv : u = v
  · subst huv
    simp only [Function.update_self, Option.some.injEq] at huc
    exact hv.trans huc
  · rw [Function.update_of_ne huv] at huc
    exact h u c huc

private lemma agrees_of_update_none {V : Type} [DecidableEq V] {ρ : V → Option Bool} {y : V → Bool}
    {v : V} {b : Bool} (hnone : ρ v = none) (h : Agrees (Function.update ρ v (some b)) y) :
    Agrees ρ y := by
  intro u c huc
  have huv : u ≠ v := by rintro rfl; simp [hnone] at huc
  exact h u c (by rw [Function.update_of_ne huv]; exact huc)

private def TreeValid {V Ans : Type} [DecidableEq V] (ok : (V → Bool) → Ans → Prop) :
    BTree V Ans → (V → Option Bool) → Prop
  | .leaf a, ρ => ∀ y : V → Bool, Agrees ρ y → ok y a
  | .node v lo hi, ρ =>
      ρ v = none ∧
      TreeValid ok lo (Function.update ρ v (some false)) ∧
      TreeValid ok hi (Function.update ρ v (some true))

private def rootClause {V : Type} : BTree (Clause V) (Clause V) → Clause V
  | .leaf a => a
  | .node a _ _ => a

private def IsResTree (F : Set (Clause (Fin n))) :
    BTree (Clause (Raw w)) (Clause (Raw w)) → Prop
  | .leaf A => liftAx F A
  | .node C lo hi =>
      IsResolvent (rootClause lo) (rootClause hi) C ∧ IsResTree F lo ∧ IsResTree F hi

private lemma isResTree_get {F : Set (Clause (Fin n))}
    {t : BTree (Clause (Raw w)) (Clause (Raw w))} (ht : IsResTree F t) :
    ∀ {p : List Bool} {sub : BTree (Clause (Raw w)) (Clause (Raw w))},
      t.get p = some sub → IsResTree F sub := by
  induction t with
  | leaf A =>
      intro p sub hget
      cases p with
      | nil => simp [BTree.get] at hget; subst hget; exact ht
      | cons _ _ => simp [BTree.get] at hget
  | node C lo hi ihlo ihhi =>
      intro p sub hget
      cases p with
      | nil => simp [BTree.get] at hget; subst hget; exact ht
      | cons b bs =>
          cases b with
          | false =>
              simp only [BTree.get, Bool.false_eq_true, ↓reduceIte] at hget
              exact ihlo ht.2.1 hget
          | true =>
              simp only [BTree.get, ↓reduceIte] at hget
              exact ihhi ht.2.2 hget

private lemma refutes_to_resTree {F : Set (Clause (Fin n))} {H s : ℕ}
    {N J : Finset (List Bool)} {line : List Bool → Clause (Raw w)} {r : List Bool → ℕ}
    (hsh : shape N J) (hroot : line [] = ∅) (hr0 : r [] ≤ s)
    (hlen : ∀ p ∈ N, p.length ≤ H)
    (hL : ∀ p ∈ N \ J, liftAx F (line p) ∧ r p = 0)
    (hJ : ∀ p ∈ J, IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p) ∧
      r p = join (r (p ++ [false])) (r (p ++ [true]))) :
    ∃ t : BTree (Clause (Raw w)) (Clause (Raw w)),
      rootClause t = ∅ ∧ IsResTree F t ∧ t.height ≤ H ∧ t.rank ≤ s := by
  have haux : ∀ (fuel : ℕ) (p : List Bool), p ∈ N → H - p.length ≤ fuel →
      let t := BTree.ofShapeAux N J line line fuel p
      rootClause t = line p ∧ IsResTree F t ∧ t.height ≤ H - p.length ∧ t.rank = r p := by
    intro fuel
    induction fuel with
    | zero =>
        intro p hp hle
        have hpJ : p ∉ J := by
          intro hmem
          have hch := hlen _ (hsh.2.2.2 p hmem).1
          simp at hch; omega
        have hleaf := hL p (Finset.mem_sdiff.mpr ⟨hp, hpJ⟩)
        refine ⟨rfl, hleaf.1, by simp [BTree.ofShapeAux, BTree.height], ?_⟩
        simp [BTree.ofShapeAux, BTree.rank, hleaf.2]
    | succ fuel ih =>
        intro p hp hle
        by_cases hpJ : p ∈ J
        · have h0 := (hsh.2.2.2 p hpJ).1
          have h1 := (hsh.2.2.2 p hpJ).2
          have hlen0 := hlen _ h0
          simp only [List.length_append, List.length_singleton] at hlen0
          obtain ⟨hrc0, hrt0, hh0, hrk0⟩ := ih (p ++ [false]) h0 (by simp; omega)
          obtain ⟨hrc1, hrt1, hh1, hrk1⟩ := ih (p ++ [true]) h1 (by simp; omega)
          obtain ⟨hres, hrp⟩ := hJ p hpJ
          dsimp only [BTree.ofShapeAux]
          simp only [hpJ, ↓reduceIte]
          refine ⟨rfl, ?_, ?_, ?_⟩
          · exact ⟨by rwa [hrc0, hrc1], hrt0, hrt1⟩
          · simp only [BTree.height]
            simp only [List.length_append, List.length_singleton] at hh0 hh1
            omega
          · simp only [BTree.rank]
            rw [hrk0, hrk1, hrp]
        · have hleaf := hL p (Finset.mem_sdiff.mpr ⟨hp, hpJ⟩)
          dsimp only [BTree.ofShapeAux]
          simp only [hpJ, ↓reduceIte]
          refine ⟨rfl, hleaf.1, by simp [BTree.height], ?_⟩
          simp [BTree.rank, hleaf.2]
  obtain ⟨hrc, hrt, hh, hrk⟩ := haux H [] hsh.1 (by simp)
  exact ⟨BTree.ofShapeAux N J line line H [], hrc.trans hroot, hrt, by simpa using hh, hrk.le.trans hr0⟩

private noncomputable def resToRaw {F : Set (Clause (Fin n))} :
    BTree (Clause (Raw w)) (Clause (Raw w)) → (Raw w → Option Bool) →
    BTree (Raw w) (Clause (Fin n))
  | .leaf A, _ =>
      if h : liftAx F A then .leaf (Classical.choose h) else .leaf ∅
  | .node C lo hi, ρ =>
      if h : IsResolvent (rootClause lo) (rootClause hi) C then
        let v := Classical.choose h
        match ρ v with
        | some false => resToRaw (F := F) lo ρ
        | some true => resToRaw (F := F) hi ρ
        | none => .node v (resToRaw (F := F) lo (Function.update ρ v (some false)))
                          (resToRaw (F := F) hi (Function.update ρ v (some true)))
      else .leaf ∅

private lemma resToRaw_spec {F : Set (Clause (Fin n))}
    (t : BTree (Clause (Raw w)) (Clause (Raw w))) (ht : IsResTree F t)
    (ρ : Raw w → Option Bool)
    (hfals : ∀ y : Raw w → Bool, Agrees ρ y → ¬ ClauseSat y (rootClause t)) :
    let rt := resToRaw (F := F) t ρ
    rt.height ≤ t.height ∧ rt.rank ≤ t.rank ∧
    TreeValid (fun y C => C ∈ F ∧ ¬ ClauseSat (parity y) C) rt ρ := by
  induction t generalizing ρ with
  | leaf A =>
      dsimp only [resToRaw]
      have hA : liftAx F A := ht
      simp only [hA, ↓reduceDIte]
      refine ⟨le_rfl, le_rfl, ?_⟩
      intro y hy
      have hspec := Classical.choose_spec hA
      refine ⟨hspec.1, fun hsat => ?_⟩
      obtain ⟨y₀, hy₀, hAeq⟩ := hspec.2
      obtain ⟨lit, hlit, hval⟩ := hsat
      have hblock : ∀ j : Fin (w lit.1), y ⟨lit.1, j⟩ = y₀ ⟨lit.1, j⟩ := by
        intro j
        have hmem : (⟨lit.1, j⟩, !(y₀ ⟨lit.1, j⟩)) ∈ A := by
          rw [hAeq, Finset.mem_image]
          refine ⟨⟨lit.1, j⟩, ?_, rfl⟩
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨lit, hlit, rfl⟩⟩
        have hneq : y ⟨lit.1, j⟩ ≠ !(y₀ ⟨lit.1, j⟩) := fun h => hfals y hy ⟨_, hmem, h⟩
        revert hneq
        cases y ⟨lit.1, j⟩ <;> cases y₀ ⟨lit.1, j⟩ <;> simp
      have hp : parity y lit.1 = parity y₀ lit.1 := parity_congr hblock
      exact hy₀ lit hlit (hp.symm.trans hval)
  | node C lo hi ihlo ihhi =>
      obtain ⟨hres, hlo, hhi⟩ := ht
      dsimp only [resToRaw]
      simp only [hres, ↓reduceDIte]
      set v := Classical.choose hres
      have hv_spec := Classical.choose_spec hres
      have hlo_step : ∀ (y : Raw w → Bool), ¬ ClauseSat y C → y v = false →
          ¬ ClauseSat y (rootClause lo) := by
        intro y hyC hyv ⟨lit, hlit, hval⟩
        by_cases hlv : lit = (v, true)
        · subst hlv; simp [hyv] at hval
        · apply hyC
          refine ⟨lit, ?_, hval⟩
          rw [hv_spec.2.2]
          exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hlv, hlit⟩)
      have hhi_step : ∀ (y : Raw w → Bool), ¬ ClauseSat y C → y v = true →
          ¬ ClauseSat y (rootClause hi) := by
        intro y hyC hyv ⟨lit, hlit, hval⟩
        by_cases hlv : lit = (v, false)
        · subst hlv; simp [hyv] at hval
        · apply hyC
          refine ⟨lit, ?_, hval⟩
          rw [hv_spec.2.2]
          exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hlv, hlit⟩)
      cases hρv : ρ v with
      | some b =>
          cases b with
          | false =>
              have hf0 : ∀ y, Agrees ρ y → ¬ ClauseSat y (rootClause lo) :=
                fun y hy => hlo_step y (hfals y hy) (hy v false hρv)
              obtain ⟨hh, hr, hv⟩ := ihlo hlo ρ hf0
              exact ⟨by simp [BTree.height]; omega, le_trans hr (le_join_left _ _), hv⟩
          | true =>
              have hf1 : ∀ y, Agrees ρ y → ¬ ClauseSat y (rootClause hi) :=
                fun y hy => hhi_step y (hfals y hy) (hy v true hρv)
              obtain ⟨hh, hr, hv⟩ := ihhi hhi ρ hf1
              exact ⟨by simp [BTree.height]; omega, le_trans hr (le_join_right _ _), hv⟩
      | none =>
          have hf0 : ∀ y, Agrees (Function.update ρ v (some false)) y → ¬ ClauseSat y (rootClause lo) :=
            fun y hy => hlo_step y (hfals y (agrees_of_update_none hρv hy)) (hy v false (by simp))
          have hf1 : ∀ y, Agrees (Function.update ρ v (some true)) y → ¬ ClauseSat y (rootClause hi) :=
            fun y hy => hhi_step y (hfals y (agrees_of_update_none hρv hy)) (hy v true (by simp))
          obtain ⟨hh0, hr0, hv0⟩ := ihlo hlo (Function.update ρ v (some false)) hf0
          obtain ⟨hh1, hr1, hv1⟩ := ihhi hhi (Function.update ρ v (some true)) hf1
          refine ⟨?_, ?_, hρv, hv0, hv1⟩
          · simp only [BTree.height]; omega
          · exact join_mono hr0 hr1

private def unsetIn (ρ : Raw w → Option Bool) (i : Fin n) : Finset (Fin (w i)) :=
  Finset.univ.filter (fun j => ρ ⟨i, j⟩ = none)

private def unknownBlocks (ρ : Raw w → Option Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => 0 < (unsetIn ρ i).card)

private def credit (ρ : Raw w → Option Bool) : ℕ :=
  ∑ i ∈ unknownBlocks ρ, (w i - (unsetIn ρ i).card)

private def blockParity (ρ : Raw w → Option Bool) (i : Fin n) : Bool :=
  decide (Odd ((Finset.univ : Finset (Fin (w i))).filter (fun j => ρ ⟨i, j⟩ = some true)).card)

private def outerOfRaw (ρ : Raw w → Option Bool) : Fin n → Option Bool :=
  fun i => if (unsetIn ρ i).card = 0 then some (blockParity ρ i) else none

private lemma unsetIn_card_le (ρ : Raw w → Option Bool) (i : Fin n) :
    (unsetIn ρ i).card ≤ w i := by
  calc (unsetIn ρ i).card ≤ (Finset.univ : Finset (Fin (w i))).card := Finset.card_le_univ _
    _ = w i := Fintype.card_fin (w i)

private lemma credit_empty : credit (w := w) (fun _ => none) = 0 := by
  unfold credit
  refine Finset.sum_eq_zero fun i _ => ?_
  have hcard : (unsetIn (w := w) (fun _ => none) i).card = w i := by
    simp [unsetIn]
  omega

private lemma outerOfRaw_empty (hw : ∀ i, 0 < w i) :
    outerOfRaw (w := w) (fun _ => none) = (fun _ => none) := by
  funext i
  have hcard : (unsetIn (w := w) (fun _ => none) i).card = w i := by
    simp [unsetIn]
  have hpos := hw i
  have hne : (unsetIn (w := w) (fun _ => none) i).card ≠ 0 := by omega
  simp only [outerOfRaw, hne, ↓reduceIte]

private lemma unsetIn_update_self (ρ : Raw w → Option Bool) (i : Fin n) (j : Fin (w i))
    (b : Bool) (hnone : ρ ⟨i, j⟩ = none) :
    (unsetIn (Function.update ρ ⟨i, j⟩ (some b)) i).card = (unsetIn ρ i).card - 1 := by
  have hj : j ∈ unsetIn ρ i := by simp [unsetIn, hnone]
  have hset : unsetIn (Function.update ρ ⟨i, j⟩ (some b)) i = (unsetIn ρ i).erase j := by
    ext j'
    by_cases hj' : j' = j
    · subst hj'; simp [unsetIn]
    · have hne : (⟨i, j'⟩ : Raw w) ≠ ⟨i, j⟩ := by intro h0; apply hj'; cases h0; rfl
      simp [unsetIn, hj', hne]
  rw [hset, Finset.card_erase_of_mem hj]

private lemma unsetIn_update_ne (ρ : Raw w → Option Bool) (i i' : Fin n) (j : Fin (w i))
    (b : Bool) (hne : i' ≠ i) :
    unsetIn (Function.update ρ ⟨i, j⟩ (some b)) i' = unsetIn ρ i' := by
  ext j'
  have hne' : (⟨i', j'⟩ : Raw w) ≠ ⟨i, j⟩ := by intro h0; apply hne; cases h0; rfl
  simp [unsetIn, hne']

private lemma blockParity_update_ne (ρ : Raw w → Option Bool) (i i' : Fin n) (j : Fin (w i))
    (b : Bool) (hne : i' ≠ i) :
    blockParity (Function.update ρ ⟨i, j⟩ (some b)) i' = blockParity ρ i' := by
  unfold blockParity
  apply congrArg (fun S : Finset (Fin (w i')) => decide (Odd S.card))
  ext j'
  have hne' : (⟨i', j'⟩ : Raw w) ≠ ⟨i, j⟩ := by intro h0; apply hne; cases h0; rfl
  simp [hne']

private lemma blockParity_update_self (ρ : Raw w → Option Bool) (i : Fin n) (j : Fin (w i))
    (b : Bool) (hnone : ρ ⟨i, j⟩ = none) :
    blockParity (Function.update ρ ⟨i, j⟩ (some b)) i =
      if b then !(blockParity ρ i) else blockParity ρ i := by
  unfold blockParity
  let S := (Finset.univ : Finset (Fin (w i))).filter (fun j' => ρ ⟨i, j'⟩ = some true)
  let S' := (Finset.univ : Finset (Fin (w i))).filter
    (fun j' => Function.update ρ ⟨i, j⟩ (some b) ⟨i, j'⟩ = some true)
  cases b with
  | false =>
      have hS' : S' = S := by
        ext j'
        by_cases hj' : j' = j
        · subst hj'; simp [S', S, hnone]
        · have hne : (⟨i, j'⟩ : Raw w) ≠ ⟨i, j⟩ := by intro h0; apply hj'; cases h0; rfl
          simp [S', S, hne]
      simp only [Bool.false_eq_true, ↓reduceIte]
      change decide (Odd S'.card) = decide (Odd S.card)
      rw [hS']
  | true =>
      have hjS : j ∉ S := by simp [S, hnone]
      have hS' : S' = insert j S := by
        ext j'
        by_cases hj' : j' = j
        · subst hj'; simp [S', S]
        · have hne : (⟨i, j'⟩ : Raw w) ≠ ⟨i, j⟩ := by intro h0; apply hj'; cases h0; rfl
          simp [S', S, hj', hne]
      simp only [↓reduceIte]
      change decide (Odd S'.card) = !decide (Odd S.card)
      rw [hS', Finset.card_insert_of_notMem hjS]
      by_cases ho : Odd S.card
      · have hne : ¬ Odd (S.card + 1) := by
          intro h1; obtain ⟨k, hk⟩ := h1; obtain ⟨m, hm⟩ := ho; omega
        simp [ho, hne]
      · have he : Odd (S.card + 1) := by
          rw [Nat.not_odd_iff_even] at ho
          obtain ⟨k, hk⟩ := ho
          exact ⟨k, by omega⟩
        simp [ho, he]

private lemma credit_update_gt_one (ρ : Raw w → Option Bool) (i : Fin n) (j : Fin (w i))
    (b : Bool) (hnone : ρ ⟨i, j⟩ = none) (hgt : 1 < (unsetIn ρ i).card) :
    credit (Function.update ρ ⟨i, j⟩ (some b)) = credit ρ + 1 := by
  let ρ' := Function.update ρ ⟨i, j⟩ (some b)
  have hU : unknownBlocks ρ' = unknownBlocks ρ := by
    ext i'
    by_cases hi : i' = i
    · subst hi
      have hc := unsetIn_update_self ρ i' j b hnone
      simp only [unknownBlocks, Finset.mem_filter, Finset.mem_univ, true_and, ρ']
      omega
    · simp only [unknownBlocks, Finset.mem_filter, Finset.mem_univ, true_and, ρ',
        unsetIn_update_ne ρ i i' j b hi]
  have hiU : i ∈ unknownBlocks ρ := by
    simp only [unknownBlocks, Finset.mem_filter, Finset.mem_univ, true_and]; omega
  unfold credit
  rw [hU, ← Finset.add_sum_erase _ _ hiU, ← Finset.add_sum_erase _ _ hiU]
  have hsum : ∑ x ∈ (unknownBlocks ρ).erase i, (w x - (unsetIn ρ' x).card) =
      ∑ x ∈ (unknownBlocks ρ).erase i, (w x - (unsetIn ρ x).card) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [unsetIn_update_ne ρ i x j b (Finset.mem_erase.mp hx).1]
  rw [hsum]
  have hc := unsetIn_update_self ρ i j b hnone
  have hle := unsetIn_card_le ρ i
  change (w i - (unsetIn ρ' i).card) + _ = (w i - (unsetIn ρ i).card) + _ + 1
  rw [hc]
  omega

private lemma credit_update_eq_one (ρ : Raw w → Option Bool) (i : Fin n) (j : Fin (w i))
    (b : Bool) (hnone : ρ ⟨i, j⟩ = none) (heq : (unsetIn ρ i).card = 1) :
    credit (Function.update ρ ⟨i, j⟩ (some b)) + (w i - 1) = credit ρ := by
  let ρ' := Function.update ρ ⟨i, j⟩ (some b)
  have hiU : i ∈ unknownBlocks ρ := by
    simp only [unknownBlocks, Finset.mem_filter, Finset.mem_univ, true_and, heq]; omega
  have hU : unknownBlocks ρ' = (unknownBlocks ρ).erase i := by
    ext i'
    by_cases hi : i' = i
    · subst hi
      have hc := unsetIn_update_self ρ i' j b hnone
      simp only [unknownBlocks, Finset.mem_erase, ne_eq, not_true_eq_false, false_and,
        Finset.mem_filter, Finset.mem_univ, true_and, iff_false, ρ']
      omega
    · simp only [unknownBlocks, Finset.mem_erase, ne_eq, hi, not_false_eq_true, true_and,
        Finset.mem_filter, Finset.mem_univ, ρ', unsetIn_update_ne ρ i i' j b hi]
  unfold credit
  rw [hU, ← Finset.add_sum_erase _ _ hiU]
  have hsum : ∑ x ∈ (unknownBlocks ρ).erase i, (w x - (unsetIn ρ' x).card) =
      ∑ x ∈ (unknownBlocks ρ).erase i, (w x - (unsetIn ρ x).card) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [unsetIn_update_ne ρ i x j b (Finset.mem_erase.mp hx).1]
  rw [hsum, heq]
  omega

private lemma outerOfRaw_update_gt_one (ρ : Raw w → Option Bool) (i : Fin n) (j : Fin (w i))
    (b : Bool) (hnone : ρ ⟨i, j⟩ = none) (hgt : 1 < (unsetIn ρ i).card) :
    outerOfRaw (Function.update ρ ⟨i, j⟩ (some b)) = outerOfRaw ρ := by
  funext i'
  by_cases hi : i' = i
  · subst hi
    have hc := unsetIn_update_self ρ i' j b hnone
    have h1 : (unsetIn (Function.update ρ ⟨i', j⟩ (some b)) i').card ≠ 0 := by omega
    have h2 : (unsetIn ρ i').card ≠ 0 := by omega
    simp only [outerOfRaw, h1, h2, ↓reduceIte]
  · unfold outerOfRaw
    rw [unsetIn_update_ne ρ i i' j b hi, blockParity_update_ne ρ i i' j b hi]

private lemma outerOfRaw_update_eq_one (ρ : Raw w → Option Bool) (i : Fin n) (j : Fin (w i))
    (outBit : Bool) (hnone : ρ ⟨i, j⟩ = none) (heq : (unsetIn ρ i).card = 1) :
    outerOfRaw (Function.update ρ ⟨i, j⟩ (some (outBit != blockParity ρ i))) =
      Function.update (outerOfRaw ρ) i (some outBit) := by
  funext i'
  by_cases hi : i' = i
  · subst hi
    have hc := unsetIn_update_self ρ i' j (outBit != blockParity ρ i') hnone
    have h0 : (unsetIn (Function.update ρ ⟨i', j⟩ (some (outBit != blockParity ρ i'))) i').card = 0 := by omega
    simp only [outerOfRaw, Function.update_self, h0, ↓reduceIte,
      blockParity_update_self ρ i' j (outBit != blockParity ρ i') hnone]
    cases outBit <;> cases blockParity ρ i' <;> rfl
  · unfold outerOfRaw
    rw [Function.update_of_ne hi, unsetIn_update_ne ρ i i' j _ hi,
      blockParity_update_ne ρ i i' j _ hi]

private lemma exists_raw_extension (ρ : Raw w → Option Bool) (x : Fin n → Bool)
    (hagr : Agrees (outerOfRaw ρ) x) :
    ∃ y : Raw w → Bool, Agrees ρ y ∧ parity y = x := by
  let y0 : Raw w → Bool := fun p => (ρ p).getD false
  have hy0_agr : Agrees ρ y0 := by
    intro p b hpb; simp [y0, hpb]
  let pick : ∀ (i : Fin n), 0 < (unsetIn ρ i).card → Fin (w i) :=
    fun i hpos => (Finset.card_pos.mp hpos).choose
  have hpick : ∀ (i : Fin n) (hpos : 0 < (unsetIn ρ i).card), ρ ⟨i, pick i hpos⟩ = none := by
    intro i hpos
    have hmem : pick i hpos ∈ unsetIn ρ i := (Finset.card_pos.mp hpos).choose_spec
    simpa [unsetIn] using hmem
  let y : Raw w → Bool := fun p =>
    if hpos : 0 < (unsetIn ρ p.1).card then
      if p.2 = pick p.1 hpos then (x p.1 != parity y0 p.1) else y0 p
    else y0 p
  refine ⟨y, ?_, ?_⟩
  · rintro ⟨i, j⟩ b hpb
    dsimp only [y]
    by_cases hpos : 0 < (unsetIn ρ i).card
    · simp only [hpos, ↓reduceDIte]
      by_cases hj0 : j = pick i hpos
      · exfalso
        rw [hj0, hpick i hpos] at hpb
        cases hpb
      · simp only [hj0, ↓reduceIte]
        exact hy0_agr ⟨i, j⟩ b hpb
    · simp only [hpos, ↓reduceDIte]
      exact hy0_agr ⟨i, j⟩ b hpb
  · funext i
    by_cases hpos : 0 < (unsetIn ρ i).card
    · set j0 : Fin (w i) := pick i hpos
      have hj0_none : ρ ⟨i, j0⟩ = none := hpick i hpos
      have hy0_j0 : y0 ⟨i, j0⟩ = false := by simp [y0, hj0_none]
      have hblock : ∀ j : Fin (w i),
          y ⟨i, j⟩ = Function.update y0 ⟨i, j0⟩ (x i != parity y0 i) ⟨i, j⟩ := by
        intro j
        dsimp only [y]
        simp only [hpos, ↓reduceDIte]
        by_cases hj : j = j0
        · subst hj
          simp [j0]
        · have hne : (⟨i, j⟩ : Raw w) ≠ ⟨i, j0⟩ := by intro h0; apply hj; cases h0; rfl
          simp [hj, hne, j0]
      rw [parity_congr hblock, parity_update y0 i j0 (x i != parity y0 i), hy0_j0]
      cases x i <;> cases parity y0 i <;> rfl
    · have hzero : (unsetIn ρ i).card = 0 := by omega
      have hxi : x i = blockParity ρ i := hagr i (blockParity ρ i) (by simp [outerOfRaw, hzero])
      rw [hxi]
      have hblock : ∀ j : Fin (w i), y ⟨i, j⟩ = y0 ⟨i, j⟩ := by
        intro j
        dsimp only [y]
        simp only [hpos, ↓reduceDIte]
      rw [parity_congr hblock]
      unfold parity blockParity
      apply congrArg (fun S : Finset (Fin (w i)) => decide (Odd S.card))
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, y0]
      cases hρ : ρ ⟨i, j⟩ with
      | none =>
          exfalso
          have : j ∈ unsetIn ρ i := by simp [unsetIn, hρ]
          have : 0 < (unsetIn ρ i).card := Finset.card_pos.mpr ⟨j, this⟩
          omega
      | some b =>
          cases b <;> simp

private def rawToOuter (t : BTree (Raw w) (Clause (Fin n))) (ρ : Raw w → Option Bool) :
    BTree (Fin n) (Clause (Fin n)) :=
  match t with
  | .leaf C => .leaf C
  | .node ⟨i, j⟩ lo hi =>
      if 1 < (unsetIn ρ i).card then
        if lo.rank ≤ hi.rank then
          rawToOuter lo (Function.update ρ ⟨i, j⟩ (some false))
        else
          rawToOuter hi (Function.update ρ ⟨i, j⟩ (some true))
      else
        let p0 := blockParity ρ i
        let s0 := if (false != p0) then
            rawToOuter hi (Function.update ρ ⟨i, j⟩ (some true))
          else
            rawToOuter lo (Function.update ρ ⟨i, j⟩ (some false))
        let s1 := if (true != p0) then
            rawToOuter hi (Function.update ρ ⟨i, j⟩ (some true))
          else
            rawToOuter lo (Function.update ρ ⟨i, j⟩ (some false))
        .node i s0 s1

private lemma rawToOuter_spec (hw : ∀ i, 0 < w i) {F : Set (Clause (Fin n))}
    (t : BTree (Raw w) (Clause (Fin n))) (ρ : Raw w → Option Bool)
    (hvalid : TreeValid (fun y C => C ∈ F ∧ ¬ ClauseSat (parity y) C) t ρ) :
    let st := rawToOuter t ρ
    st.wHeight w ≤ t.height + credit ρ ∧
    st.wRank (fun i => w i - 1) (fun _ => 0) ≤ t.rank + credit ρ ∧
    TreeValid (fun x C => C ∈ F ∧ ¬ ClauseSat x C) st (outerOfRaw ρ) := by
  induction t generalizing ρ with
  | leaf C =>
      dsimp only [rawToOuter]
      refine ⟨by simp [BTree.wHeight], by simp [BTree.wRank], ?_⟩
      intro x hx
      obtain ⟨y, hy_agr, hy_par⟩ := exists_raw_extension ρ x hx
      rw [← hy_par]
      exact hvalid y hy_agr
  | node p lo hi ihlo ihhi =>
      rcases p with ⟨i, j⟩
      obtain ⟨hnone, hvlo, hvhi⟩ := hvalid
      have hj_mem : j ∈ unsetIn ρ i := by simp [unsetIn, hnone]
      have hpos : 0 < (unsetIn ρ i).card := Finset.card_pos.mpr ⟨j, hj_mem⟩
      by_cases hgt : 1 < (unsetIn ρ i).card
      · dsimp only [rawToOuter]
        simp only [hgt, ↓reduceIte]
        by_cases hle : lo.rank ≤ hi.rank
        · simp only [hle, ↓reduceIte]
          obtain ⟨hh, hr, hv⟩ := ihlo (Function.update ρ ⟨i, j⟩ (some false)) hvlo
          rw [credit_update_gt_one ρ i j false hnone hgt] at hh hr
          rw [outerOfRaw_update_gt_one ρ i j false hnone hgt] at hv
          have hmin : lo.rank + 1 ≤ join lo.rank hi.rank := by
            have := min_add_one_le_join lo.rank hi.rank
            rw [min_eq_left hle] at this
            exact this
          refine ⟨?_, ?_, hv⟩
          · simp only [BTree.height]; omega
          · simp only [BTree.rank]; omega
        · simp only [hle, ↓reduceIte]
          obtain ⟨hh, hr, hv⟩ := ihhi (Function.update ρ ⟨i, j⟩ (some true)) hvhi
          rw [credit_update_gt_one ρ i j true hnone hgt] at hh hr
          rw [outerOfRaw_update_gt_one ρ i j true hnone hgt] at hv
          have hmin : hi.rank + 1 ≤ join lo.rank hi.rank := by
            have := min_add_one_le_join lo.rank hi.rank
            rw [min_eq_right (by omega)] at this
            exact this
          refine ⟨?_, ?_, hv⟩
          · simp only [BTree.height]; omega
          · simp only [BTree.rank]; omega
      · have heq : (unsetIn ρ i).card = 1 := by omega
        dsimp only [rawToOuter]
        simp only [hgt, ↓reduceIte]
        obtain ⟨hh0, hr0, hv0⟩ := ihlo (Function.update ρ ⟨i, j⟩ (some false)) hvlo
        obtain ⟨hh1, hr1, hv1⟩ := ihhi (Function.update ρ ⟨i, j⟩ (some true)) hvhi
        have hcr0 := credit_update_eq_one ρ i j false hnone heq
        have hcr1 := credit_update_eq_one ρ i j true hnone heq
        have hwi : 0 < w i := hw i
        have hout_none : outerOfRaw ρ i = none := by simp [outerOfRaw, heq]
        have ho0 := outerOfRaw_update_eq_one ρ i j false hnone heq
        have ho1 := outerOfRaw_update_eq_one ρ i j true hnone heq
        cases hp0 : blockParity ρ i
        · simp only [Bool.bne_false, Bool.false_eq_true, ↓reduceIte]
          rw [hp0, Bool.bne_false] at ho0 ho1
          rw [ho0] at hv0
          rw [ho1] at hv1
          refine ⟨?_, ?_, hout_none, hv0, hv1⟩
          · simp only [BTree.wHeight, BTree.height]; omega
          · simp only [BTree.wRank, BTree.rank]
            have h1 : join ((rawToOuter lo (Function.update ρ ⟨i, j⟩ (some false))).wRank
                (fun i => w i - 1) (fun _ => 0))
                ((rawToOuter hi (Function.update ρ ⟨i, j⟩ (some true))).wRank
                (fun i => w i - 1) (fun _ => 0)) ≤
                join (lo.rank + credit (Function.update ρ ⟨i, j⟩ (some false)))
                     (hi.rank + credit (Function.update ρ ⟨i, j⟩ (some true))) :=
              join_mono hr0 hr1
            have hceq : credit (Function.update ρ ⟨i, j⟩ (some true)) =
                credit (Function.update ρ ⟨i, j⟩ (some false)) := by omega
            rw [hceq, join_add_right] at h1
            omega
        · simp only [Bool.bne_true, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          rw [hp0, Bool.bne_true, Bool.not_false] at ho0
          rw [hp0, Bool.bne_true, Bool.not_true] at ho1
          rw [ho0] at hv1
          rw [ho1] at hv0
          refine ⟨?_, ?_, hout_none, hv1, hv0⟩
          · simp only [BTree.wHeight, BTree.height]; omega
          · simp only [BTree.wRank, BTree.rank]
            have h1 : join ((rawToOuter hi (Function.update ρ ⟨i, j⟩ (some true))).wRank
                (fun i => w i - 1) (fun _ => 0))
                ((rawToOuter lo (Function.update ρ ⟨i, j⟩ (some false))).wRank
                (fun i => w i - 1) (fun _ => 0)) ≤
                join (hi.rank + credit (Function.update ρ ⟨i, j⟩ (some true)))
                     (lo.rank + credit (Function.update ρ ⟨i, j⟩ (some false))) :=
              join_mono hr1 hr0
            have hceq : credit (Function.update ρ ⟨i, j⟩ (some true)) =
                credit (Function.update ρ ⟨i, j⟩ (some false)) := by omega
            rw [hceq, join_add_right, join_comm hi.rank lo.rank] at h1
            omega

private lemma btree_path_spec {V Ans : Type} [DecidableEq V] (len : V → ℕ)
    (ok : (V → Bool) → Ans → Prop) (t : BTree V Ans) :
    ∀ (ρ : V → Option Bool) (p : List Bool),
      TreeValid ok t ρ → p ∈ t.nodes →
      (List.ofFn (fun j : Fin p.length => t.qAt (p.take j.val))).Nodup ∧
      (∀ j : Fin p.length, ∀ v, t.qAt (p.take j.val) = some v → ρ v = none) ∧
      (List.ofFn (fun j : Fin p.length => (t.qAt (p.take j.val)).elim 0 len)).sum ≤ t.wHeight len ∧
      (∀ a, t.get p = some (.leaf a) → ∀ x : V → Bool, Agrees ρ x →
        (∀ j : Fin p.length, (t.qAt (p.take j.val)).map x = some (p.get j)) → ok x a) := by
  induction t with
  | leaf a =>
      intro ρ p hv hp
      simp only [BTree.nodes, Finset.mem_singleton] at hp
      subst hp
      refine ⟨by simp, fun j => j.elim0, by simp [BTree.wHeight], ?_⟩
      intro a' hget x hx _
      simp only [BTree.get, Option.some.injEq, BTree.leaf.injEq] at hget
      subst hget
      exact hv x hx
  | node v lo hi ihlo ihhi =>
      intro ρ p hv hp
      obtain ⟨hnone, hvlo, hvhi⟩ := hv
      cases p with
      | nil =>
          refine ⟨by simp, fun j => j.elim0, by simp [BTree.wHeight], ?_⟩
          intro a' hget; simp [BTree.get] at hget
      | cons b bs =>
          cases b with
          | false =>
              have hbs : bs ∈ lo.nodes := by
                rw [BTree.mem_nodes_iff_isSome_get] at hp ⊢
                simpa [BTree.get] using hp
              obtain ⟨hnd, hfree, hsum, hleaf⟩ :=
                ihlo (Function.update ρ v (some false)) bs hvlo hbs
              have hq0 : (BTree.node v lo hi).qAt [] = some v := rfl
              have hqt : ∀ k : ℕ, (BTree.node v lo hi).qAt (false :: bs.take k) = lo.qAt (bs.take k) := by
                intro k; simp [BTree.qAt, BTree.get]
              have hfree_ext : ∀ j : Fin (false :: bs).length, ∀ u,
                  (BTree.node v lo hi).qAt ((false :: bs).take j.val) = some u → ρ u = none := by
                intro j u hqu
                refine Fin.cases ?_ ?_ j hqu
                · intro h0
                  simp only [Fin.val_zero, List.take_zero, hq0, Option.some.injEq] at h0
                  subst h0; exact hnone
                · intro j' hj'
                  simp only [Fin.val_succ, List.take_succ_cons, hqt] at hj'
                  have hfu := hfree j' u hj'
                  by_cases huv : u = v
                  · subst huv; simp at hfu
                  · rwa [Function.update_of_ne huv] at hfu
              refine ⟨?_, hfree_ext, ?_, ?_⟩
              · rw [List.length_cons, List.ofFn_succ, List.nodup_cons]
                refine ⟨?_, ?_⟩
                · intro hmem
                  obtain ⟨j', hj'⟩ := List.mem_ofFn.mp hmem
                  simp only [Fin.val_succ, List.take_succ_cons, hqt, Fin.val_zero, List.take_zero, hq0] at hj'
                  have := hfree j' v hj'
                  simp at this
                · simpa [Fin.val_succ, List.take_succ_cons, hqt] using hnd
              · rw [List.length_cons, List.ofFn_succ, List.sum_cons]
                simp only [Fin.val_zero, List.take_zero, hq0, Option.elim_some,
                  Fin.val_succ, List.take_succ_cons, hqt, BTree.wHeight]
                omega
              · intro a' hget x hx hmatch
                simp only [BTree.get, Bool.false_eq_true, ↓reduceIte] at hget
                have hx0 := hmatch ⟨0, by simp⟩
                simp only [List.take_zero, hq0, Option.map_some, List.get_eq_getElem,
                  List.getElem_cons_zero, Option.some.injEq] at hx0
                apply hleaf a' hget x (agrees_update hx hx0)
                intro j'
                have hmj := hmatch j'.succ
                simpa [Fin.val_succ, List.take_succ_cons, hqt] using hmj
          | true =>
              have hbs : bs ∈ hi.nodes := by
                rw [BTree.mem_nodes_iff_isSome_get] at hp ⊢
                simpa [BTree.get] using hp
              obtain ⟨hnd, hfree, hsum, hleaf⟩ :=
                ihhi (Function.update ρ v (some true)) bs hvhi hbs
              have hq0 : (BTree.node v lo hi).qAt [] = some v := rfl
              have hqt : ∀ k : ℕ, (BTree.node v lo hi).qAt (true :: bs.take k) = hi.qAt (bs.take k) := by
                intro k; simp [BTree.qAt, BTree.get]
              have hfree_ext : ∀ j : Fin (true :: bs).length, ∀ u,
                  (BTree.node v lo hi).qAt ((true :: bs).take j.val) = some u → ρ u = none := by
                intro j u hqu
                refine Fin.cases ?_ ?_ j hqu
                · intro h0
                  simp only [Fin.val_zero, List.take_zero, hq0, Option.some.injEq] at h0
                  subst h0; exact hnone
                · intro j' hj'
                  simp only [Fin.val_succ, List.take_succ_cons, hqt] at hj'
                  have hfu := hfree j' u hj'
                  by_cases huv : u = v
                  · subst huv; simp at hfu
                  · rwa [Function.update_of_ne huv] at hfu
              refine ⟨?_, hfree_ext, ?_, ?_⟩
              · rw [List.length_cons, List.ofFn_succ, List.nodup_cons]
                refine ⟨?_, ?_⟩
                · intro hmem
                  obtain ⟨j', hj'⟩ := List.mem_ofFn.mp hmem
                  simp only [Fin.val_succ, List.take_succ_cons, hqt, Fin.val_zero, List.take_zero, hq0] at hj'
                  have := hfree j' v hj'
                  simp at this
                · simpa [Fin.val_succ, List.take_succ_cons, hqt] using hnd
              · rw [List.length_cons, List.ofFn_succ, List.sum_cons]
                simp only [Fin.val_zero, List.take_zero, hq0, Option.elim_some,
                  Fin.val_succ, List.take_succ_cons, hqt, BTree.wHeight]
                omega
              · intro a' hget x hx hmatch
                simp only [BTree.get, ↓reduceIte] at hget
                have hx0 := hmatch ⟨0, by simp⟩
                simp only [List.take_zero, hq0, Option.map_some, List.get_eq_getElem,
                  List.getElem_cons_zero, Option.some.injEq] at hx0
                apply hleaf a' hget x (agrees_update hx hx0)
                intro j'
                have hmj := hmatch j'.succ
                simpa [Fin.val_succ, List.take_succ_cons, hqt] using hmj

private lemma btree_to_search {V Ans : Type} [DecidableEq V] (len fee : V → ℕ) (pay : Ans → ℕ)
    (ok : (V → Bool) → Ans → Prop) {H s : ℕ}
    (t : BTree V Ans) (hvalid : TreeValid ok t (fun _ => none))
    (hH : t.wHeight len ≤ H) (hs : t.wRank fee pay ≤ s) :
    ∃ (N J : Finset (List Bool)) (q : List Bool → Option V)
      (out : List Bool → Ans) (r : List Bool → ℕ),
      shape N J ∧ r [] ≤ s ∧
      (∀ p ∈ N, (List.ofFn (fun j : Fin p.length => q (p.take j.val))).Nodup ∧
        (List.ofFn (fun j : Fin p.length => (q (p.take j.val)).elim 0 len)).sum ≤ H) ∧
      (∀ p ∈ J, ∃ v, q p = some v ∧
        r p = fee v + join (r (p ++ [false])) (r (p ++ [true]))) ∧
      ∀ p ∈ N \ J, r p = pay (out p) ∧ ∀ x : V → Bool,
        (∀ j : Fin p.length, (q (p.take j.val)).map x = some (p.get j)) → ok x (out p) := by
  let out : List Bool → Ans := fun p =>
    match t.get p with
    | some (.leaf a) => a
    | _ => t.anyLeaf
  let r : List Bool → ℕ := fun p =>
    match t.get p with
    | some sub => sub.wRank fee pay
    | none => 0
  refine ⟨t.nodes, t.internals, t.qAt, out, r, BTree.shape_nodes_internals t, ?_, ?_, ?_, ?_⟩
  · simpa [r, BTree.get] using hs
  · intro p hp
    obtain ⟨hnd, _, hsum, _⟩ := btree_path_spec len ok t (fun _ => none) p hvalid hp
    exact ⟨hnd, le_trans hsum hH⟩
  · intro p hp
    rw [BTree.mem_internals_iff_get_node] at hp
    obtain ⟨v, lo, hi, hget⟩ := hp
    refine ⟨v, by simp [BTree.qAt, hget], ?_⟩
    simp only [r, BTree.get_append_singleton, hget, Bool.false_eq_true, ↓reduceIte, BTree.wRank]
  · intro p hp
    have hpN : p ∈ t.nodes := (Finset.mem_sdiff.mp hp).1
    rw [BTree.mem_leaves_iff_get_leaf] at hp
    obtain ⟨a, hget⟩ := hp
    obtain ⟨_, _, _, hleaf⟩ := btree_path_spec len ok t (fun _ => none) p hvalid hpN
    refine ⟨by simp [r, out, hget, BTree.wRank], ?_⟩
    intro x hmatch
    have hout : out p = a := by simp [out, hget]
    rw [hout]
    exact hleaf a hget x (fun _ _ h => by simp at h) hmatch

private def parityExpand {Ans : Type} (i : Fin n) (t0 t1 : BTree (Raw w) Ans) :
    (k : ℕ) → k ≤ w i → Bool → BTree (Raw w) Ans
  | k, _hk, acc =>
      if hlt : k < w i then
        .node ⟨i, ⟨k, hlt⟩⟩
          (parityExpand i t0 t1 (k + 1) hlt acc)
          (parityExpand i t0 t1 (k + 1) hlt (!acc))
      else
        if acc then t1 else t0
termination_by k _ _ => w i - k

private lemma parityExpand_height {Ans : Type} (i : Fin n) (t0 t1 : BTree (Raw w) Ans)
    (k : ℕ) (hk : k ≤ w i) (acc : Bool) :
    (parityExpand i t0 t1 k hk acc).height ≤ (w i - k) + max t0.height t1.height := by
  induction hd : w i - k generalizing k acc with
  | zero =>
      have hge : ¬ k < w i := by omega
      rw [parityExpand]
      simp only [hge, ↓reduceDIte]
      cases acc <;> simp
  | succ d ih =>
      have hlt : k < w i := by omega
      rw [parityExpand]
      simp only [hlt, ↓reduceDIte, BTree.height]
      have h1 := ih (k + 1) hlt acc (by omega)
      have h2 := ih (k + 1) hlt (!acc) (by omega)
      omega

private lemma parityExpand_rank {Ans : Type} (i : Fin n) (t0 t1 : BTree (Raw w) Ans)
    (k : ℕ) (hk : k < w i) (acc : Bool) :
    (parityExpand i t0 t1 k (le_of_lt hk) acc).rank =
      (w i - k - 1) + join t0.rank t1.rank := by
  induction hd : w i - k - 1 generalizing k acc with
  | zero =>
      have hlt : k < w i := hk
      have hnot : ¬ (k + 1 < w i) := by omega
      rw [parityExpand]
      simp only [hlt, ↓reduceDIte, BTree.rank]
      rw [parityExpand, parityExpand]
      simp only [hnot, ↓reduceDIte]
      cases acc <;> simp [join_comm]
  | succ d ih =>
      have hlt : k < w i := hk
      have hlt1 : k + 1 < w i := by omega
      rw [parityExpand]
      simp only [hlt, ↓reduceDIte, BTree.rank]
      rw [ih (k + 1) hlt1 acc (by omega), ih (k + 1) hlt1 (!acc) (by omega)]
      simp only [join, ↓reduceIte]
      omega

private def expandOuter {Ans : Type} (hw : ∀ i, 0 < w i) :
    BTree (Fin n) Ans → BTree (Raw w) Ans
  | .leaf a => .leaf a
  | .node i lo hi =>
      parityExpand i (expandOuter hw lo) (expandOuter hw hi) 0 (Nat.zero_le _) false

private lemma expandOuter_height {Ans : Type} (hw : ∀ i, 0 < w i) (s : BTree (Fin n) Ans) :
    (expandOuter hw s).height ≤ s.wHeight w := by
  induction s with
  | leaf _ => simp [expandOuter, BTree.height, BTree.wHeight]
  | node i lo hi ihlo ihhi =>
      simp only [expandOuter, BTree.wHeight]
      have h1 := parityExpand_height i (expandOuter hw lo) (expandOuter hw hi) 0 (Nat.zero_le _) false
      simp only [Nat.sub_zero] at h1
      omega

private lemma expandOuter_rank {Ans : Type} (hw : ∀ i, 0 < w i) (s : BTree (Fin n) Ans) :
    (expandOuter hw s).rank = s.wRank (fun i => w i - 1) (fun _ => 0) := by
  induction s with
  | leaf _ => simp [expandOuter, BTree.rank, BTree.wRank]
  | node i lo hi ihlo ihhi =>
      simp only [expandOuter, BTree.wRank]
      rw [parityExpand_rank i (expandOuter hw lo) (expandOuter hw hi) 0 (hw i) false,
        ihlo, ihhi, Nat.sub_zero]

private def PathOK (F : Set (Clause (Fin n))) :
    BTree (Raw w) (Clause (Fin n)) → Clause (Raw w) → Prop
  | .leaf _, Γ => ∃ A : Clause (Raw w), liftAx F A ∧ A ⊆ Γ
  | .node v lo hi, Γ =>
      PathOK F lo (insert (v, true) Γ) ∧ PathOK F hi (insert (v, false) Γ)

private def Matches (σ : Fin n → Option Bool) (τ : Raw w → Option Bool) (Γ : Clause (Raw w)) : Prop :=
  (∀ p b, τ p = some b → (p, !b) ∈ Γ) ∧
  (∀ i b, σ i = some b → (∀ j : Fin (w i), (τ ⟨i, j⟩).isSome) ∧ blockParity τ i = b) ∧
  (∀ i, σ i = none → ∀ j : Fin (w i), τ ⟨i, j⟩ = none)

private lemma parityExpand_pathOK {F : Set (Clause (Fin n))} (i : Fin n)
    (t0 t1 : BTree (Raw w) (Clause (Fin n))) (σ : Fin n → Option Bool)
    (h0 : ∀ τ Γ, Matches (Function.update σ i (some false)) τ Γ → PathOK F t0 Γ)
    (h1 : ∀ τ Γ, Matches (Function.update σ i (some true)) τ Γ → PathOK F t1 Γ)
    (k : ℕ) (hk : k ≤ w i) (acc : Bool) (τ : Raw w → Option Bool) (Γ : Clause (Raw w))
    (hΓ : ∀ p b, τ p = some b → (p, !b) ∈ Γ)
    (hset : ∀ i' b, i' ≠ i → σ i' = some b →
      (∀ j : Fin (w i'), (τ ⟨i', j⟩).isSome) ∧ blockParity τ i' = b)
    (hnone : ∀ i', i' ≠ i → σ i' = none → ∀ j : Fin (w i'), τ ⟨i', j⟩ = none)
    (hlt_set : ∀ j : Fin (w i), j.val < k → (τ ⟨i, j⟩).isSome)
    (hge_none : ∀ j : Fin (w i), k ≤ j.val → τ ⟨i, j⟩ = none)
    (hacc : blockParity τ i = acc) :
    PathOK F (parityExpand i t0 t1 k hk acc) Γ := by
  induction hd : w i - k generalizing k acc τ Γ with
  | zero =>
      have hge : ¬ k < w i := by omega
      rw [parityExpand]
      simp only [hge, ↓reduceDIte]
      have hM : Matches (Function.update σ i (some acc)) τ Γ := by
        refine ⟨hΓ, ?_, ?_⟩
        · intro i' b hi'
          by_cases hEq : i' = i
          · subst hEq
            simp only [Function.update_self, Option.some.injEq] at hi'
            subst hi'
            exact ⟨fun j => hlt_set j (by omega), hacc⟩
          · rw [Function.update_of_ne hEq] at hi'
            exact hset i' b hEq hi'
        · intro i' hi'
          by_cases hEq : i' = i
          · subst hEq; simp at hi'
          · rw [Function.update_of_ne hEq] at hi'
            exact hnone i' hEq hi'
      cases acc with
      | false => exact h0 τ Γ hM
      | true => exact h1 τ Γ hM
  | succ d ih =>
      have hlt : k < w i := by omega
      rw [parityExpand]
      simp only [hlt, ↓reduceDIte, PathOK]
      let j0 : Fin (w i) := ⟨k, hlt⟩
      have hj0_none : τ ⟨i, j0⟩ = none := hge_none j0 (le_refl k)
      have hstep : ∀ (b : Bool),
          PathOK F (parityExpand i t0 t1 (k + 1) hlt (if b then !acc else acc))
            (insert (⟨i, j0⟩, !b) Γ) := by
        intro b
        let τ' := Function.update τ ⟨i, j0⟩ (some b)
        apply ih (k + 1) hlt (if b then !acc else acc) τ' (insert (⟨i, j0⟩, !b) Γ)
        · intro p c hpc
          by_cases hp : p = ⟨i, j0⟩
          · subst hp
            simp only [τ', Function.update_self, Option.some.injEq] at hpc
            subst hpc
            exact Finset.mem_insert_self _ _
          · simp only [τ', Function.update_of_ne hp] at hpc
            exact Finset.mem_insert_of_mem (hΓ p c hpc)
        · intro i' c hne hi'
          have hne_raw : ∀ j : Fin (w i'), (⟨i', j⟩ : Raw w) ≠ ⟨i, j0⟩ := by
            intro j h0; apply hne; cases h0; rfl
          refine ⟨fun j => ?_, ?_⟩
          · simp only [τ', Function.update_of_ne (hne_raw j)]
            exact (hset i' c hne hi').1 j
          · rw [blockParity_update_ne τ i i' j0 b hne]
            exact (hset i' c hne hi').2
        · intro i' hne hi' j
          have hne_raw : (⟨i', j⟩ : Raw w) ≠ ⟨i, j0⟩ := by intro h0; apply hne; cases h0; rfl
          simp only [τ', Function.update_of_ne hne_raw]
          exact hnone i' hne hi' j
        · intro j hj
          by_cases hjk : j.val < k
          · have hne_raw : (⟨i, j⟩ : Raw w) ≠ ⟨i, j0⟩ := by
              intro h0
              have : j = j0 := by cases h0; rfl
              have : j.val = k := congrArg Fin.val this
              omega
            simp only [τ', Function.update_of_ne hne_raw]
            exact hlt_set j hjk
          · have hjeq : j = j0 := Fin.ext (by dsimp [j0]; omega)
            subst hjeq
            simp [τ']
        · intro j hj
          have hne_raw : (⟨i, j⟩ : Raw w) ≠ ⟨i, j0⟩ := by
            intro h0
            have : j = j0 := by cases h0; rfl
            have : j.val = k := congrArg Fin.val this
            omega
          simp only [τ', Function.update_of_ne hne_raw]
          exact hge_none j (by omega)
        · rw [blockParity_update_self τ i j0 b hj0_none, hacc]
        · omega
      exact ⟨by simpa using hstep false, by simpa using hstep true⟩

private lemma expandOuter_pathOK (hw : ∀ i, 0 < w i) {F : Set (Clause (Fin n))}
    (s : BTree (Fin n) (Clause (Fin n))) :
    ∀ (σ : Fin n → Option Bool) (τ : Raw w → Option Bool) (Γ : Clause (Raw w)),
      TreeValid (fun x C => C ∈ F ∧ ¬ ClauseSat x C) s σ →
      Matches σ τ Γ →
      PathOK F (expandOuter hw s) Γ := by
  induction s with
  | leaf C =>
      intro σ τ Γ hvalid hM
      simp only [expandOuter, PathOK]
      let x0 : Fin n → Bool := fun i => (σ i).getD false
      have hx0_agr : Agrees σ x0 := by intro i b hib; simp [x0, hib]
      have hCF : C ∈ F := (hvalid x0 hx0_agr).1
      have hlit_set : ∀ lit ∈ C, σ lit.1 = some (!lit.2) := by
        rintro ⟨v, val⟩ hlit
        cases hσ : σ v with
        | none =>
            exfalso
            let x' := Function.update x0 v val
            have hx'_agr : Agrees σ x' := by
              intro i b hib
              have hne : i ≠ v := by rintro rfl; simp [hσ] at hib
              simp [x', hne, x0, hib]
            exact (hvalid x' hx'_agr).2 ⟨(v, val), hlit, by simp [x']⟩
        | some b =>
            have hx0_lit : x0 v = b := by simp [x0, hσ]
            have hne : b ≠ val := fun h => (hvalid x0 hx0_agr).2 ⟨(v, val), hlit, hx0_lit.trans h⟩
            cases b <;> cases val <;> simp_all
      let y : Raw w → Bool := fun p => (τ p).getD false
      let A : Clause (Raw w) :=
        ((Finset.univ : Finset (Raw w)).filter (fun b => b.1 ∈ C.image Prod.fst)).image
          (fun b => (b, !(y b)))
      refine ⟨A, ⟨C, hCF, y, ?_, rfl⟩, ?_⟩
      · intro lit hlit
        obtain ⟨hall, hbp⟩ := hM.2.1 lit.1 (!lit.2) (hlit_set lit hlit)
        have hpar : parity y lit.1 = blockParity τ lit.1 := by
          unfold parity blockParity
          apply congrArg (fun S : Finset (Fin (w lit.1)) => decide (Odd S.card))
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, y]
          cases hτ : τ ⟨lit.1, j⟩ with
          | none =>
              have := hall j
              simp [hτ] at this
          | some b =>
              cases b <;> simp
        rw [hpar, hbp]
        cases lit.2 <;> simp
      · intro l hl
        simp only [A, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hl
        obtain ⟨b, hb_img, rfl⟩ := hl
        obtain ⟨lit, hlit, hlit_eq⟩ := hb_img
        have hσb : σ b.1 = some (!lit.2) := hlit_eq ▸ hlit_set lit hlit
        have hisSome : (τ b).isSome := by
          have := (hM.2.1 b.1 (!lit.2) hσb).1 b.2
          simpa using this
        cases hτ : τ b with
        | none => simp [hτ] at hisSome
        | some d =>
            have hyb : y b = d := by simp [y, hτ]
            rw [hyb]
            exact hM.1 b d hτ
  | node i lo hi ihlo ihhi =>
      intro σ τ Γ hvalid hM
      obtain ⟨hσi, hvlo, hvhi⟩ := hvalid
      simp only [expandOuter]
      apply parityExpand_pathOK i (expandOuter hw lo) (expandOuter hw hi) σ
        (fun τ' Γ' hM' => ihlo _ τ' Γ' hvlo hM')
        (fun τ' Γ' hM' => ihhi _ τ' Γ' hvhi hM')
        0 (Nat.zero_le _) false τ Γ
      · exact hM.1
      · intro i' b _ hi'; exact hM.2.1 i' b hi'
      · intro i' _ hi'; exact hM.2.2 i' hi'
      · intro j hj; omega
      · intro j _; exact hM.2.2 i hσi j
      · unfold blockParity
        have hempty : (Finset.univ : Finset (Fin (w i))).filter (fun j => τ ⟨i, j⟩ = some true) = ∅ := by
          ext j
          simp [hM.2.2 i hσi j]
        rw [hempty]
        simp

private noncomputable def rawToRes {F : Set (Clause (Fin n))} :
    BTree (Raw w) (Clause (Fin n)) → Clause (Raw w) →
    BTree (Clause (Raw w)) (Clause (Raw w))
  | .leaf _, Γ =>
      if h : ∃ A : Clause (Raw w), liftAx F A ∧ A ⊆ Γ then
        .leaf (Classical.choose h)
      else .leaf ∅
  | .node v lo hi, Γ =>
      let rlo := rawToRes (F := F) lo (insert (v, true) Γ)
      let rhi := rawToRes (F := F) hi (insert (v, false) Γ)
      if (v, true) ∈ rootClause rlo then
        if (v, false) ∈ rootClause rhi then
          .node ((rootClause rlo).erase (v, true) ∪ (rootClause rhi).erase (v, false)) rlo rhi
        else rhi
      else rlo

private lemma rawToRes_spec {F : Set (Clause (Fin n))}
    (t : BTree (Raw w) (Clause (Fin n))) :
    ∀ (Γ : Clause (Raw w)), PathOK F t Γ →
      let rt := rawToRes (F := F) t Γ
      IsResTree F rt ∧ rootClause rt ⊆ Γ ∧ rt.height ≤ t.height ∧ rt.rank ≤ t.rank := by
  induction t with
  | leaf _ =>
      intro Γ hok
      change ∃ A : Clause (Raw w), liftAx F A ∧ A ⊆ Γ at hok
      dsimp only [rawToRes]
      simp only [hok, ↓reduceDIte]
      have hspec := Classical.choose_spec hok
      exact ⟨hspec.1, hspec.2, le_rfl, le_rfl⟩
  | node v lo hi ihlo ihhi =>
      intro Γ hok
      obtain ⟨hres0, hsub0, hh0, hr0⟩ := ihlo (insert (v, true) Γ) hok.1
      obtain ⟨hres1, hsub1, hh1, hr1⟩ := ihhi (insert (v, false) Γ) hok.2
      dsimp only [rawToRes]
      set rlo := rawToRes (F := F) lo (insert (v, true) Γ)
      set rhi := rawToRes (F := F) hi (insert (v, false) Γ)
      by_cases h1 : (v, true) ∈ rootClause rlo
      · simp only [h1, ↓reduceIte]
        by_cases h2 : (v, false) ∈ rootClause rhi
        · simp only [h2, ↓reduceIte]
          refine ⟨⟨⟨v, h1, h2, rfl⟩, hres0, hres1⟩, ?_, ?_, ?_⟩
          · intro lit hlit
            rcases Finset.mem_union.mp hlit with hL | hR
            · obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hL
              exact (Finset.mem_insert.mp (hsub0 hmem)).resolve_left hne
            · obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hR
              exact (Finset.mem_insert.mp (hsub1 hmem)).resolve_left hne
          · simp only [BTree.height]; omega
          · exact join_mono hr0 hr1
        · simp only [h2, ↓reduceIte]
          refine ⟨hres1, ?_, ?_, le_trans hr1 (le_join_right _ _)⟩
          · intro lit hlit
            have hne : lit ≠ (v, false) := fun h => h2 (h ▸ hlit)
            exact (Finset.mem_insert.mp (hsub1 hlit)).resolve_left hne
          · simp only [BTree.height]; omega
      · simp only [h1, ↓reduceIte]
        refine ⟨hres0, ?_, ?_, le_trans hr0 (le_join_left _ _)⟩
        · intro lit hlit
          have hne : lit ≠ (v, true) := fun h => h1 (h ▸ hlit)
          exact (Finset.mem_insert.mp (hsub0 hlit)).resolve_left hne
        · simp only [BTree.height]; omega

private lemma resTree_to_refutes {F : Set (Clause (Fin n))} {H s : ℕ}
    (rt : BTree (Clause (Raw w)) (Clause (Raw w)))
    (hrt : IsResTree F rt) (hroot : rootClause rt = ∅)
    (hH : rt.height ≤ H) (hs : rt.rank ≤ s) :
    ∃ (N J : Finset (List Bool)) (line : List Bool → Clause (Raw w))
      (r : List Bool → ℕ), shape N J ∧ line [] = ∅ ∧ r [] ≤ s ∧ (∀ p ∈ N, p.length ≤ H) ∧
      (∀ p ∈ N \ J, liftAx F (line p) ∧ r p = 0) ∧
      ∀ p ∈ J, IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p) ∧
        r p = join (r (p ++ [false])) (r (p ++ [true])) := by
  let line : List Bool → Clause (Raw w) := fun p =>
    match rt.get p with
    | some sub => rootClause sub
    | none => ∅
  let r : List Bool → ℕ := fun p =>
    match rt.get p with
    | some sub => sub.rank
    | none => 0
  refine ⟨rt.nodes, rt.internals, line, r, BTree.shape_nodes_internals rt,
    by simpa [line, BTree.get] using hroot, by simpa [r, BTree.get] using hs,
    fun p hp => le_trans (BTree.length_le_height rt p hp) hH, ?_, ?_⟩
  · intro p hp
    rw [BTree.mem_leaves_iff_get_leaf] at hp
    obtain ⟨A, hget⟩ := hp
    have hsub : liftAx F A := isResTree_get hrt hget
    exact ⟨by simpa [line, hget, rootClause] using hsub, by simp [r, hget, BTree.rank]⟩
  · intro p hp
    rw [BTree.mem_internals_iff_get_node] at hp
    obtain ⟨C, lo, hi, hget⟩ := hp
    have hsub := isResTree_get hrt hget
    refine ⟨?_, ?_⟩
    · simp only [line, BTree.get_append_singleton, hget, Bool.false_eq_true, ↓reduceIte, rootClause]
      exact hsub.1
    · simp only [r, BTree.get_append_singleton, hget, Bool.false_eq_true, ↓reduceIte, BTree.rank]

private lemma search_to_btree (hn : 0 < n) (hw : ∀ i, 0 < w i)
    {ok : (Fin n → Bool) → Clause (Fin n) → Prop} {H s : ℕ}
    {N J : Finset (List Bool)} {q : List Bool → Option (Fin n)}
    {out : List Bool → Clause (Fin n)} {r : List Bool → ℕ}
    (hsh : shape N J) (hr0 : r [] ≤ s)
    (hpath : ∀ p ∈ N, (List.ofFn (fun j : Fin p.length => q (p.take j.val))).Nodup ∧
      (List.ofFn (fun j : Fin p.length => (q (p.take j.val)).elim 0 w)).sum ≤ H)
    (hJ : ∀ p ∈ J, ∃ v, q p = some v ∧
      r p = (w v - 1) + join (r (p ++ [false])) (r (p ++ [true])))
    (hL : ∀ p ∈ N \ J, r p = 0 ∧ ∀ x : Fin n → Bool,
      (∀ j : Fin p.length, (q (p.take j.val)).map x = some (p.get j)) → ok x (out p)) :
    ∃ t : BTree (Fin n) (Clause (Fin n)),
      t.wHeight w ≤ H ∧ t.wRank (fun i => w i - 1) (fun _ => 0) ≤ s ∧
      TreeValid ok t (fun _ => none) := by
  have hlen : ∀ p ∈ N, p.length ≤ H := by
    intro p hp
    have hsum := (hpath p hp).2
    have hge : p.length ≤ (List.ofFn (fun j : Fin p.length => (q (p.take j.val)).elim 0 w)).sum := by
      have h1 : ∀ (m : ℕ) (f : Fin m → ℕ), (∀ j, 1 ≤ f j) → m ≤ (List.ofFn f).sum := by
        intro m
        induction m with
        | zero => intro _ _; simp
        | succ m ih =>
            intro f hf
            rw [List.ofFn_succ, List.sum_cons]
            have h0 := hf 0
            have hm := ih (fun j => f j.succ) (fun j => hf j.succ)
            omega
      apply h1 p.length
      intro j
      have hmemJ := shape_take_mem_J hsh p hp j.val j.isLt
      obtain ⟨v, hqv, _⟩ := hJ _ hmemJ
      simp only [hqv, Option.elim_some]
      exact hw v
    exact le_trans hge hsum
  let fi : List Bool → Fin n := fun p => (q p).getD ⟨0, hn⟩
  have haux : ∀ (fuel : ℕ) (p : List Bool) (σ : Fin n → Option Bool),
      p ∈ N → H - p.length ≤ fuel →
      (∀ j : Fin p.length, ∃ v, q (p.take j.val) = some v ∧ σ v = some (p.get j)) →
      (∀ v, (σ v).isSome → ∃ j : Fin p.length, q (p.take j.val) = some v) →
      let sub := BTree.ofShapeAux N J fi out fuel p
      sub.wHeight w + (List.ofFn (fun j : Fin p.length => (q (p.take j.val)).elim 0 w)).sum ≤ H ∧
      sub.wRank (fun i => w i - 1) (fun _ => 0) = r p ∧
      TreeValid ok sub σ := by
    intro fuel
    induction fuel with
    | zero =>
        intro p σ hp hle hσ1 _
        have hpJ : p ∉ J := by
          intro hmem
          have hch := hlen _ (hsh.2.2.2 p hmem).1
          simp at hch; omega
        have hleaf := hL p (Finset.mem_sdiff.mpr ⟨hp, hpJ⟩)
        refine ⟨?_, ?_, ?_⟩
        · simpa [BTree.ofShapeAux, BTree.wHeight] using (hpath p hp).2
        · simp [BTree.ofShapeAux, BTree.wRank, hleaf.1]
        · intro x hx
          apply hleaf.2 x
          intro j
          obtain ⟨v, hqv, hσv⟩ := hσ1 j
          rw [hqv]
          simp [hx v (p.get j) hσv]
    | succ fuel ih =>
        intro p σ hp hle hσ1 hσ2
        by_cases hpJ : p ∈ J
        · obtain ⟨v, hqv, hrp⟩ := hJ p hpJ
          have hfip : fi p = v := by simp [fi, hqv]
          have h0 : p ++ [false] ∈ N := (hsh.2.2.2 p hpJ).1
          have h1 : p ++ [true] ∈ N := (hsh.2.2.2 p hpJ).2
          have hσv_none : σ v = none := by
            cases hσv : σ v with
            | none => rfl
            | some b =>
                exfalso
                obtain ⟨j, hj⟩ := hσ2 v (by simp [hσv])
                have hnd := (hpath (p ++ [false]) h0).1
                let i1 : Fin (p ++ [false]).length := ⟨j.val, by simp [Nat.lt_succ_of_lt j.isLt]⟩
                let i2 : Fin (p ++ [false]).length := ⟨p.length, by simp⟩
                have hne : i1 ≠ i2 := by
                  intro h; have := congrArg Fin.val h; dsimp [i1, i2] at this; omega
                have heq : q ((p ++ [false]).take i1.val) = q ((p ++ [false]).take i2.val) := by
                  dsimp [i1, i2]
                  rw [List.take_append_of_le_length (le_of_lt j.isLt)]
                  simpa [hqv] using hj
                exact ofFn_nodup_ne hnd hne heq
          have hstep : ∀ (b : Bool), p ++ [b] ∈ N →
              let sub := BTree.ofShapeAux N J fi out fuel (p ++ [b])
              sub.wHeight w + ((List.ofFn (fun j : Fin p.length =>
                (q (p.take j.val)).elim 0 w)).sum + w v) ≤ H ∧
              sub.wRank (fun i => w i - 1) (fun _ => 0) = r (p ++ [b]) ∧
              TreeValid ok sub (Function.update σ v (some b)) := by
            intro b hpb
            have hsum_eq : (List.ofFn (fun j : Fin (p ++ [b]).length =>
                (q ((p ++ [b]).take j.val)).elim 0 w)).sum =
                (List.ofFn (fun j : Fin p.length => (q (p.take j.val)).elim 0 w)).sum + w v := by
              have hlist := list_ofFn_eq_of_eq (by simp : (p ++ [b]).length = p.length + 1)
                (fun k => (q ((p ++ [b]).take k)).elim 0 w)
              rw [hlist, list_ofFn_snoc p.length (fun k => (q ((p ++ [b]).take k)).elim 0 w),
                List.sum_append, List.sum_singleton]
              congr 1
              · congr 1
                congr 1
                funext j
                rw [List.take_append_of_le_length (le_of_lt j.isLt)]
              · simp [hqv]
            have hσ1' : ∀ j : Fin (p ++ [b]).length,
                ∃ u, q ((p ++ [b]).take j.val) = some u ∧
                  Function.update σ v (some b) u = some ((p ++ [b]).get j) := by
              intro j
              by_cases hlt : j.val < p.length
              · obtain ⟨u, hqu, hσu⟩ := hσ1 ⟨j.val, hlt⟩
                have huv : u ≠ v := by rintro rfl; simp [hσv_none] at hσu
                refine ⟨u, ?_, ?_⟩
                · rwa [List.take_append_of_le_length (le_of_lt hlt)]
                · rw [Function.update_of_ne huv, hσu]
                  simp [List.get_eq_getElem, List.getElem_append_left hlt]
              · have hjeq : j.val = p.length := by
                  have := j.isLt; simp at this; omega
                refine ⟨v, ?_, ?_⟩
                · simp [hjeq, hqv]
                · simp [List.get_eq_getElem, hjeq]
            have hσ2' : ∀ u, (Function.update σ v (some b) u).isSome →
                ∃ j : Fin (p ++ [b]).length, q ((p ++ [b]).take j.val) = some u := by
              intro u hu
              by_cases huv : u = v
              · subst huv
                exact ⟨⟨p.length, by simp⟩, by simp [hqv]⟩
              · rw [Function.update_of_ne huv] at hu
                obtain ⟨j, hj⟩ := hσ2 u hu
                refine ⟨⟨j.val, by simp [Nat.lt_succ_of_lt j.isLt]⟩, ?_⟩
                rwa [List.take_append_of_le_length (le_of_lt j.isLt)]
            have hres := ih (p ++ [b]) (Function.update σ v (some b)) hpb (by simp; omega) hσ1' hσ2'
            rwa [hsum_eq] at hres
          obtain ⟨hh0, hrk0, hv0⟩ := hstep false h0
          obtain ⟨hh1, hrk1, hv1⟩ := hstep true h1
          dsimp only [BTree.ofShapeAux]
          simp only [hpJ, ↓reduceIte, hfip]
          refine ⟨?_, ?_, hσv_none, hv0, hv1⟩
          · simp only [BTree.wHeight]; omega
          · simp only [BTree.wRank]; rw [hrk0, hrk1, hrp]
        · have hleaf := hL p (Finset.mem_sdiff.mpr ⟨hp, hpJ⟩)
          dsimp only [BTree.ofShapeAux]
          simp only [hpJ, ↓reduceIte]
          refine ⟨?_, ?_, ?_⟩
          · simpa [BTree.wHeight] using (hpath p hp).2
          · simp [BTree.wRank, hleaf.1]
          · intro x hx
            apply hleaf.2 x
            intro j
            obtain ⟨v, hqv, hσv⟩ := hσ1 j
            rw [hqv]
            simp [hx v (p.get j) hσv]
  obtain ⟨hh, hrk, hv⟩ := haux H [] (fun _ => none) hsh.1 (by simp)
    (fun j => j.elim0) (fun _ h => by simp at h)
  exact ⟨BTree.ofShapeAux N J fi out H [], by simpa using hh, hrk.le.trans hr0, hv⟩

end ParityLift

end PEqualNP.Outside.L_pcx_336_aux

theorem PEqualNP.Outside.L_pcx_336 :
∀ (n : ℕ) (w : Fin n → ℕ), (∀ i, 0 < w i) →
  let Raw := (i : Fin n) × Fin (w i)
  let parity := fun (y : Raw → Bool) (i : Fin n) =>
    decide (Odd ((Finset.univ : Finset (Fin (w i))).filter (fun j => y ⟨i,j⟩ = true)).card)
  let liftAx := fun (F : Set (PEqualNP.ProofComplexity.Clause (Fin n)))
      (A : PEqualNP.ProofComplexity.Clause Raw) =>
    ∃ C ∈ F, ∃ y : Raw → Bool, (∀ lit ∈ C, parity y lit.1 ≠ lit.2) ∧
      A = ((Finset.univ : Finset Raw).filter (fun b => b.1 ∈ C.image Prod.fst)).image
        (fun b => (b, !(y b)))
  let shape := fun (N J : Finset (List Bool)) =>
    [] ∈ N ∧ J ⊆ N ∧
    (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N
  let join := fun a b : ℕ => if a = b then a+1 else max a b
  let refutes := fun (F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) (H s : ℕ) =>
    ∃ (N J : Finset (List Bool)) (line : List Bool → PEqualNP.ProofComplexity.Clause Raw)
      (r : List Bool → ℕ), shape N J ∧ line [] = ∅ ∧ r [] ≤ s ∧ (∀ p ∈ N, p.length ≤ H) ∧
      (∀ p ∈ N \ J, liftAx F (line p) ∧ r p = 0) ∧
      ∀ p ∈ J, PEqualNP.ProofComplexity.IsResolvent (line (p ++ [false]))
        (line (p ++ [true])) (line p) ∧ r p = join (r (p ++ [false])) (r (p ++ [true]))
  let search := fun {V Ans : Type} (len fee : V → ℕ) (pay : Ans → ℕ)
      (ok : (V → Bool) → Ans → Prop) (H s : ℕ) =>
    ∃ (N J : Finset (List Bool)) (q : List Bool → Option V)
      (out : List Bool → Ans) (r : List Bool → ℕ),
      shape N J ∧ r [] ≤ s ∧
      (∀ p ∈ N, (List.ofFn (fun j : Fin p.length => q (p.take j.val))).Nodup ∧
        (List.ofFn (fun j : Fin p.length => (q (p.take j.val)).elim 0 len)).sum ≤ H) ∧
      (∀ p ∈ J, ∃ v, q p = some v ∧
        r p = fee v + join (r (p ++ [false])) (r (p ++ [true]))) ∧
      ∀ p ∈ N \ J, r p = pay (out p) ∧ ∀ x : V → Bool,
        (∀ j : Fin p.length, (q (p.take j.val)).map x = some (p.get j)) → ok x (out p)
  ∀ (F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) (H s : ℕ),
    refutes F H s ↔ search w (fun i => w i-1) (fun _ => 0)
      (fun x C => C ∈ F ∧ ¬ PEqualNP.ProofComplexity.ClauseSat x C) H s := by
  intro n w hw Raw parity liftAx shape join refutes search F H s
  constructor
  · rintro ⟨N, J, line, r, hsh, hroot, hr0, hlen, hL, hJ⟩
    obtain ⟨rt, hrt_root, hrt_ok, hrt_H, hrt_r⟩ :=
      PEqualNP.Outside.L_pcx_336_aux.refutes_to_resTree (w := w) hsh hroot hr0 hlen hL hJ
    have hfals : ∀ y : PEqualNP.Outside.L_pcx_336_aux.Raw w → Bool,
        PEqualNP.Outside.L_pcx_336_aux.Agrees (fun _ => none) y →
        ¬ PEqualNP.ProofComplexity.ClauseSat y (PEqualNP.Outside.L_pcx_336_aux.rootClause rt) := by
      intro y _
      rw [hrt_root]
      rintro ⟨lit, hlit, _⟩
      simp at hlit
    obtain ⟨hraw_H, hraw_r, hraw_v⟩ :=
      PEqualNP.Outside.L_pcx_336_aux.resToRaw_spec rt hrt_ok (fun _ => none) hfals
    obtain ⟨hout_H, hout_r, hout_v⟩ :=
      PEqualNP.Outside.L_pcx_336_aux.rawToOuter_spec hw
        (PEqualNP.Outside.L_pcx_336_aux.resToRaw (F := F) rt (fun _ => none))
        (fun _ => none) hraw_v
    rw [PEqualNP.Outside.L_pcx_336_aux.credit_empty, Nat.add_zero] at hout_H hout_r
    rw [PEqualNP.Outside.L_pcx_336_aux.outerOfRaw_empty hw] at hout_v
    exact PEqualNP.Outside.L_pcx_336_aux.btree_to_search w (fun i => w i - 1) (fun _ => 0)
      (fun x C => C ∈ F ∧ ¬ PEqualNP.ProofComplexity.ClauseSat x C) _ hout_v
      (le_trans hout_H (le_trans hraw_H hrt_H))
      (le_trans hout_r (le_trans hraw_r hrt_r))
  · rintro ⟨N, J, q, out, r, hsh, hr0, hpath, hJ, hL⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hnilJ : [] ∉ J := by
        intro hmem
        obtain ⟨v, _, _⟩ := hJ [] hmem
        exact v.elim0
      have hleaf := hL [] (Finset.mem_sdiff.mpr ⟨hsh.1, hnilJ⟩)
      have hCF : out [] ∈ F := (hleaf.2 (fun i => i.elim0) (fun j => j.elim0)).1
      have hout_empty : out [] = ∅ := by
        ext lit; exact lit.1.elim0
      rw [hout_empty] at hCF
      refine ⟨{[]}, ∅, fun _ => ∅, fun _ => 0, ?_, rfl, Nat.zero_le s, ?_, ?_, ?_⟩
      · refine ⟨Finset.mem_singleton_self [], Finset.empty_subset _, ?_, ?_⟩
        · intro p b hp
          simp only [Finset.mem_singleton] at hp
          have := congrArg List.length hp
          simp at this
        · intro p hp; simp at hp
      · intro p hp
        simp only [Finset.mem_singleton] at hp
        subst hp; simp
      · intro p _
        refine ⟨⟨∅, hCF, fun b => b.1.elim0, fun lit hlit => by simp at hlit, ?_⟩, rfl⟩
        ext l; exact l.1.1.elim0
      · intro p hp; simp at hp
    · dsimp only at hL
      obtain ⟨st, hst_H, hst_r, hst_v⟩ :=
        PEqualNP.Outside.L_pcx_336_aux.search_to_btree
          (ok := fun x C => C ∈ F ∧ ¬ PEqualNP.ProofComplexity.ClauseSat x C)
          hn hw hsh hr0 hpath hJ hL
      have hM0 : PEqualNP.Outside.L_pcx_336_aux.Matches (w := w)
          (fun _ => none) (fun _ => none) ∅ := by
        refine ⟨fun _ _ h => by simp at h, fun _ _ h => by simp at h, fun _ _ _ => rfl⟩
      have hok := PEqualNP.Outside.L_pcx_336_aux.expandOuter_pathOK hw st
        (fun _ => none) (fun _ => none) ∅ hst_v hM0
      obtain ⟨hrt_ok, hrt_sub, hrt_H, hrt_r⟩ :=
        PEqualNP.Outside.L_pcx_336_aux.rawToRes_spec
          (PEqualNP.Outside.L_pcx_336_aux.expandOuter hw st) ∅ hok
      have hrt_root : PEqualNP.Outside.L_pcx_336_aux.rootClause
          (PEqualNP.Outside.L_pcx_336_aux.rawToRes (F := F)
            (PEqualNP.Outside.L_pcx_336_aux.expandOuter hw st) ∅) = ∅ :=
        Finset.subset_empty.mp hrt_sub
      exact PEqualNP.Outside.L_pcx_336_aux.resTree_to_refutes _ hrt_ok hrt_root
        (le_trans hrt_H (le_trans (PEqualNP.Outside.L_pcx_336_aux.expandOuter_height hw st) hst_H))
        (le_trans hrt_r (by rw [PEqualNP.Outside.L_pcx_336_aux.expandOuter_rank hw st]; exact hst_r))
