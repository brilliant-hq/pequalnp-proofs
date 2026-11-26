import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25419_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def combine (t a b : Bool) : Bool := if t then a && b else a || b


inductive Formula (α : Type) where
  | var (a : α)
  | join (t : Bool) (left right : Formula α)

def leaves {α : Type} : Formula α → List α
  | .var a => [a]
  | .join _ f g => leaves f ++ leaves g


def evalF {α : Type} (x : α → Bool) : Formula α → Bool
  | .var a => x a
  | .join t f g => combine t (evalF x f) (evalF x g)


theorem foldl_snoc_keeps {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    init <+: gs.foldl (fun R g => R ++ [F R g]) init := by
  induction gs generalizing init with
  | nil => exact List.prefix_refl _
  | cons g gs ih => exact (List.prefix_append init [F init g]).trans (ih _)

theorem foldl_snoc_length {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    (gs.foldl (fun R g => R ++ [F R g]) init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih => simp [ih]; omega

theorem getD_of_initial {α : Type _} {P L : List α} (h : P <+: L) {i : ℕ} (hi : i < P.length)
    (d : α) : L.getD i d = P.getD i d := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]


def readGate (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)


def step (w : List Bool) (g : Gate) : List Bool := w ++ [readGate w g]


def binaryOp (t : Bool) : GateOp := if t then .and else .or

theorem binary_eval (t a b : Bool) : (binaryOp t).eval [a, b] = combine t a b := by
  cases t <;> simp [binaryOp, combine, GateOp.eval]

theorem binary_op (t : Bool) : binaryOp t = .and ∨ binaryOp t = .or := by
  cases t <;> simp [binaryOp]

def post {N : ℕ} (k : ℕ) : Formula (Fin N) → Circuit
  | .var a => ⟨[], a.val⟩
  | .join t f g =>
    let L := post k f
    let R := post (k + L.size) g
    ⟨L.gates ++ R.gates ++ [⟨binaryOp t, [L.output, R.output]⟩], k + L.size + R.size⟩

theorem post_small {N : ℕ} (f : Formula (Fin N)) {k : ℕ} (hk : N ≤ k) :
    (post k f).output < k + (post k f).size := by
  cases f with
  | var a =>
    have h := a.isLt
    change a.val < k + 0
    omega
  | join t f g =>
    simp only [post, Circuit.size, List.length_append, List.length_singleton]
    omega


def Wired : ℕ → List Gate → Prop
  | _, [] => True
  | k, g :: gs =>
      ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∧
      (∀ a ∈ g.inputs, a < k) ∧ Wired (k + 1) gs

theorem wired_append (k : ℕ) (l r : List Gate) :
    Wired k (l ++ r) ↔ Wired k l ∧ Wired (k + l.length) r := by
  induction l generalizing k with
  | nil => simp [Wired]
  | cons a l ih =>
    simp only [List.cons_append, Wired, List.length_cons, ih, Nat.add_assoc, Nat.add_comm 1]
    tauto

theorem post_wired {N : ℕ} (f : Formula (Fin N)) {k : ℕ} (hk : N ≤ k) :
    Wired k (post k f).gates := by
  induction f generalizing k with
  | var a => trivial
  | join t f g ihf ihg =>
    let L := post k f
    let R := post (k + L.size) g
    change Wired k (L.gates ++ R.gates ++ [⟨binaryOp t, [L.output, R.output]⟩])
    rw [List.append_assoc, wired_append, wired_append]
    have hr : N ≤ k + L.size := by omega
    refine ⟨ihf hk, ihg hr, ⟨binary_op t, rfl⟩, ?_, trivial⟩
    intro i hi
    have hl := post_small f hk
    have hv := post_small g hr
    change i < k + L.size + R.size
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · change L.output < k + L.size at hl
      omega
    · exact hv

theorem wired_shape {gs : List Gate} {k : ℕ} (hw : Wired k gs) :
    ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  induction gs generalizing k with
  | nil => simp
  | cons g gs ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hw.1
    · exact ih hw.2.2 a ha


theorem post_eval {N : ℕ} (f : Formula (Fin N)) (x : Fin N → Bool)
    (k : ℕ) (hk : N ≤ k) (init : List Bool) (hi : init.length = k)
    (h : ∀ i : Fin N, init.getD i.val false = x i) :
    ((post k f).gates.foldl step init).getD (post k f).output false = evalF x f := by
  induction f generalizing k init with
  | var a => exact h a
  | join t f g ihf ihg =>
    let L := post k f
    let R := post (k + L.size) g
    let a := L.gates.foldl step init
    let b := R.gates.foldl step a
    have ha : a.length = k + L.size := by
      change (L.gates.foldl (fun l g => l ++ [readGate l g]) init).length = _
      rw [foldl_snoc_length readGate, hi]
      rfl
    have hb : b.length = k + L.size + R.size := by
      change (R.gates.foldl (fun l g => l ++ [readGate l g]) a).length = _
      rw [foldl_snoc_length readGate, ha]
      rfl
    have hp : init <+: a := foldl_snoc_keeps readGate L.gates init
    have hq : a <+: b := foldl_snoc_keeps readGate R.gates a
    have hka : N ≤ k + L.size := by omega
    have hf0 : a.getD L.output false = evalF x f := ihf k hk init hi h
    have hf : b.getD L.output false = evalF x f := by
      have hlt : L.output < a.length := ha.symm ▸ post_small f hk
      exact (getD_of_initial hq hlt false).trans hf0
    have hg : b.getD R.output false = evalF x g := by
      apply ihg (k + L.size) hka a ha
      intro i
      have hlt : i.val < init.length := by have := i.isLt; omega
      exact (getD_of_initial hp hlt false).trans (h i)
    change ((L.gates ++ R.gates ++ ([⟨binaryOp t, [L.output, R.output]⟩] : List Gate)).foldl step init).getD
      (k + L.size + R.size) false = _
    rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (b ++ [readGate b ⟨binaryOp t, [L.output, R.output]⟩]).getD (k + L.size + R.size) false = _
    rw [← hb]
    rw [show (b ++ [readGate b ⟨binaryOp t, [L.output, R.output]⟩]).getD b.length false =
      readGate b ⟨binaryOp t, [L.output, R.output]⟩ by simp]
    change (binaryOp t).eval [b.getD L.output false, b.getD R.output false] = _
    rw [binary_eval, hf, hg]
    rfl


theorem each_value {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  have hu := u.isLt
  have hv := v.isLt
  apply Bool.eq_iff_iff.2
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs <;> simp [Fin.ext_iff] <;> omega






def group {α : Type} (d : α) : List α → Formula α
  | [] => .var d
  | [a] => .var a
  | a :: b :: l => .join false (.var a) (group d (b :: l))

theorem group_leaves {α : Type} (d : α) (l : List α) (hn : l ≠ []) :
    leaves (group d l) = l := by
  induction l with
  | nil => contradiction
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l =>
      simp [group, leaves, ih (by simp)]

theorem group_eval {α : Type} (d : α) (l : List α) (x : α → Bool) (hn : l ≠ []) :
    evalF x (group d l) = l.any x := by
  induction l with
  | nil => contradiction
  | cons a l ih =>
    cases l with
    | nil => simp [group, evalF]
    | cons b l =>
      simp only [group, evalF, combine, Bool.false_eq_true, ite_false]
      have he := ih (by simp)
      rw [he]
      rfl

theorem post_size {N : ℕ} (f : Formula (Fin N)) (k : ℕ) :
    (post k f).size + 1 = (leaves f).length := by
  induction f generalizing k with
  | var a => rfl
  | join t f g ihf ihg =>
    have hf := ihf k
    have hg := ihg (k + (post k f).size)
    simp only [post, Circuit.size, leaves, List.length_append, List.length_singleton] at hf hg ⊢
    omega

theorem group_value {α β : Type} [DecidableEq α] (d : β) (s : Finset α)
    (f : α → β) (x : β → Bool) (u : α)
    (hn : s.Nonempty) (hx : ∀ i, x (f i) = decide (i = u)) :
    evalF x (group d (s.toList.map f)) = decide (u ∈ s) := by
  have hne : s.toList.map f ≠ [] := by
    intro e
    have h := congrArg List.length e
    simp only [List.length_map, Finset.length_toList, List.length_nil] at h
    have hp := Finset.card_pos.mpr hn
    omega
  rw [group_eval d _ x hne]
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, List.mem_map, Finset.mem_toList, decide_eq_true_eq]
  constructor
  · rintro ⟨a, ⟨i, hi, rfl⟩, he⟩
    rw [hx, decide_eq_true_eq] at he
    exact he ▸ hi
  · intro hu
    exact ⟨f u, ⟨u, hu, rfl⟩, by simp [hx]⟩

end PEqualNP.Outside.L_meta_25419_aux

open PEqualNP.Outside.L_meta_25419_aux PEqualNP.CircuitLowerBounds PEqualNP.Represents in
theorem PEqualNP.Outside.L_meta_25419 : ∀ (n : ℕ) (S T : Finset (Fin n)), 3 ≤ n → S.Nonempty → Sᶜ.Nonempty → T.Nonempty → Tᶜ.Nonempty → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide ((u ∈ S ∧ v ∈ T) ∨ (u ∉ S ∧ v ∉ T))) (2 * n - 1) := by
  intro n S T hn hS hSc hT hTc
  let d : Fin (n + n) := ⟨0, by omega⟩
  let rows (U : Finset (Fin n)) := U.toList.map (Fin.castAdd n)
  let cols (V : Finset (Fin n)) := V.toList.map (Fin.natAdd n)
  let f := Formula.join false
    (.join true (group d (rows S)) (group d (cols T)))
    (.join true (group d (rows Sᶜ)) (group d (cols Tᶜ)))
  let C := post (n + n) f
  have wr (U : Finset (Fin n)) (hU : U.Nonempty) : rows U ≠ [] := by
    intro e
    have h := congrArg List.length e
    simp only [rows, List.length_map, Finset.length_toList, List.length_nil] at h
    have hp := Finset.card_pos.mpr hU
    omega
  have wc (V : Finset (Fin n)) (hV : V.Nonempty) : cols V ≠ [] := by
    intro e
    have h := congrArg List.length e
    simp only [cols, List.length_map, Finset.length_toList, List.length_nil] at h
    have hp := Finset.card_pos.mpr hV
    omega
  have sz : C.size + 1 = n + n := by
    have hs : C.size + 1 = (leaves f).length := post_size f _
    simp only [f, leaves, List.length_append] at hs
    rw [group_leaves d _ (wr S hS), group_leaves d _ (wc T hT),
      group_leaves d _ (wr Sᶜ hSc), group_leaves d _ (wc Tᶜ hTc)] at hs
    simp only [rows, cols, List.length_map, Finset.length_toList, Finset.card_compl,
      Fintype.card_fin] at hs
    have hsle : S.card ≤ n := by simpa using Finset.card_le_univ S
    have htle : T.card ≤ n := by simpa using Finset.card_le_univ T
    omega
  refine ⟨C, ?_, by omega, ?_⟩
  · intro g hg
    obtain ⟨he, hL⟩ := wired_shape (post_wired f (k := n + n) le_rfl) g hg
    rcases he with he | he <;> simp [he, hL]
  · intro u v
    let x : Fin (n + n) → Bool := fun i => (oneEach u v).getD i.val false
    have hlength : (oneEach u v).length = n + n := by simp [oneEach]
    have hr (i : Fin n) : x (Fin.castAdd n i) = decide (i = u) := by
      change (oneEach u v).getD i.val false = _
      rw [each_value]
      have h := i.isLt
      simp [Fin.ext_iff, show i.val ≠ n + v.val by omega]
    have hc (i : Fin n) : x (Fin.natAdd n i) = decide (i = v) := by
      change (oneEach u v).getD (n + i.val) false = _
      rw [each_value]
      have h := u.isLt
      simp [Fin.ext_iff, show n + i.val ≠ u.val by omega]
    have h1 := group_value d S (Fin.castAdd n) x u hS hr
    have h2 := group_value d T (Fin.natAdd n) x v hT hc
    have h3 := group_value d Sᶜ (Fin.castAdd n) x u hSc hr
    have h4 := group_value d Tᶜ (Fin.natAdd n) x v hTc hc
    change evalF x (group d (rows S)) = _ at h1
    change evalF x (group d (cols T)) = _ at h2
    change evalF x (group d (rows Sᶜ)) = _ at h3
    change evalF x (group d (cols Tᶜ)) = _ at h4
    have ho : C.eval (oneEach u v) = evalF x f := post_eval f x _ le_rfl _ hlength (fun _ => rfl)
    rw [ho]
    apply Bool.eq_iff_iff.2
    simp [f, evalF, combine, h1, h2, h3, h4, Finset.mem_compl]
