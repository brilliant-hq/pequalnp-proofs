import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50047

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

abbrev Word := BitVec 5

def initial : List Word := [30, 28, 24, 16, 0, 31]
def goals : List Word := [2, 11, 18]

def bit (t : Fin 5) (w : Word) : Bool := w.getLsbD t.val
def inputAt (t : Fin 5) : List Bool :=
  (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false, true]

def isNot (g : Gate) : Bool :=
  match g.op with
  | .not => true
  | _ => false

def evalWord (op : GateOp) (xs : List Word) : Word :=
  match op with
  | .and => xs.foldr (· &&& ·) (BitVec.allOnes 5)
  | .or => xs.foldr (· ||| ·) 0
  | .not => ~~~(xs.headD 0)
  | _ => 0

def extend (w : List Word) (g : Gate) : List Word :=
  w ++ [evalWord g.op (g.inputs.map (fun j => w.getD j 0))]

def legal (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

theorem bit_getD (t : Fin 5) (w : List Word) (j : Nat) :
    bit t (w.getD j 0) = (w.map (bit t)).getD j false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[j]? <;> simp [bit]

theorem bit_and_fold (t : Fin 5) (xs : List Word) :
    bit t (xs.foldr (· &&& ·) (BitVec.allOnes 5)) = (xs.map (bit t)).all id := by
  induction xs with
  | nil =>
    change (BitVec.allOnes 5).getLsbD t.val = true
    rw [BitVec.getLsbD_allOnes, decide_eq_true t.isLt]
  | cons a xs ih =>
    change bit t (a &&& xs.foldr (· &&& ·) (BitVec.allOnes 5)) = (bit t a && (xs.map (bit t)).all id)
    rw [← ih]
    simp [bit]

theorem bit_or_fold (t : Fin 5) (xs : List Word) :
    bit t (xs.foldr (· ||| ·) 0) = (xs.map (bit t)).any id := by
  induction xs with
  | nil => simp [bit]
  | cons a xs ih =>
    change bit t (a ||| xs.foldr (· ||| ·) 0) = (bit t a || (xs.map (bit t)).any id)
    rw [← ih]
    simp [bit]

theorem bit_eval (t : Fin 5) (g : Gate) (h : legal g) (xs : List Word) :
    bit t (evalWord g.op xs) = g.op.eval (xs.map (bit t)) := by
  rcases h.1 with a | a | a
  · simpa [evalWord, GateOp.eval, a] using bit_and_fold t xs
  · simpa [evalWord, GateOp.eval, a] using bit_or_fold t xs
  · have ones : ∀ t : Fin 5, bit t 31 = true := by decide +kernel
    cases xs with
    | nil =>
      rw [a]
      exact ones t
    | cons b bs => simp [evalWord, GateOp.eval, a, bit, t.isLt]

theorem simulate (t : Fin 5) (gs : List Gate) (w : List Word)
    (h : ∀ g ∈ gs, legal g) :
    (gs.foldl extend w).map (bit t) =
      gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun j => v.getD j false)])
        (w.map (bit t)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun q hq => h q (List.mem_cons.mpr (Or.inr hq)))]
    congr 1
    simp only [extend, List.map_append, List.map_cons, List.map_nil,
      bit_eval t g (h g List.mem_cons_self), List.map_map, Function.comp_def, bit_getD]

def bins (stock : List Word) : List Word :=
  stock.flatMap fun a => stock.flatMap fun b => [a &&& b, a ||| b]

def fresh (stock choices : List Word) : List Word :=
  (choices.filter (fun a => !stock.contains a)).eraseDups

def lacks (stock : List Word) : Finset Word :=
  goals.toFinset \ stock.toFinset

def search : Nat → Nat → List Word → Bool
  | 0, _, stock => goals.all stock.contains
  | k + 1, n, stock =>
      if (lacks stock).card ≤ k + 1 then
        search k n stock ||
          (fresh stock (bins stock)).any (fun v => search k n (v :: stock)) ||
          (n != 0 && (fresh stock (stock.map (~~~ ·))).any
            (fun v => search k (n - 1) (v :: stock)))
      else false

theorem getCovered (w stock : List Word) (cover : ∀ a ∈ w, a ∈ stock)
    (zero : (0 : Word) ∈ stock) (j : Nat) : w.getD j 0 ∈ stock := by
  by_cases hj : j < w.length
  · simpa [List.getD_eq_getElem?_getD, hj] using cover w[j] (List.getElem_mem hj)
  · simpa [List.getD_eq_getElem?_getD, hj] using zero

theorem evalChoice (g : Gate) (ok : legal g) (xs stock : List Word)
    (size : xs.length ≤ 2) (cover : ∀ x ∈ xs, x ∈ stock)
    (zero : (0 : Word) ∈ stock) (one : (31 : Word) ∈ stock) :
    evalWord g.op xs ∈ stock ∨
      (isNot g = false ∧ evalWord g.op xs ∈ bins stock) ∨
      (isNot g = true ∧ evalWord g.op xs ∈ stock.map (~~~ ·)) := by
  have andChoice {a b : Word} (ha : a ∈ stock) (hb : b ∈ stock) : a &&& b ∈ bins stock := by
    exact List.mem_flatMap.mpr ⟨a, ha, List.mem_flatMap.mpr ⟨b, hb, by simp⟩⟩
  have orChoice {a b : Word} (ha : a ∈ stock) (hb : b ∈ stock) : a ||| b ∈ bins stock := by
    exact List.mem_flatMap.mpr ⟨a, ha, List.mem_flatMap.mpr ⟨b, hb, by simp⟩⟩
  rcases g with ⟨op, js⟩
  rcases ok.1 with h | h | h
  · change op = .and at h
    subst op
    rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩
    · exact Or.inl one
    · exact Or.inl (by simpa only [evalWord, List.foldr_cons, List.foldr_nil,
        BitVec.and_allOnes] using cover a (by simp))
    · exact Or.inr (Or.inl ⟨rfl, by
        simpa only [evalWord, List.foldr_cons, List.foldr_nil, BitVec.and_allOnes]
          using (andChoice (cover a (by simp)) (cover b (by simp)))⟩)
    · simp at size
  · change op = .or at h
    subst op
    rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩
    · exact Or.inl zero
    · exact Or.inl (by simpa [evalWord] using cover a (by simp))
    · exact Or.inr (Or.inl ⟨rfl, by
        simpa [evalWord] using (orChoice (cover a (by simp)) (cover b (by simp)))⟩)
    · simp at size
  · change op = .not at h
    subst op
    cases xs with
    | nil => exact Or.inr (Or.inr ⟨rfl, List.mem_map_of_mem zero⟩)
    | cons a tl =>
      exact Or.inr (Or.inr ⟨rfl, List.mem_map_of_mem (cover a List.mem_cons_self)⟩)

theorem fresh_mem {stock opts : List Word} {v : Word} (h : v ∈ opts) (new : v ∉ stock) :
    v ∈ fresh stock opts := by
  simp [fresh, h, new]

def produced : List Gate → List Word → List Word
  | [], _ => []
  | g :: gs, w => evalWord g.op (g.inputs.map (fun i => w.getD i 0)) :: produced gs (extend w g)

theorem produced_length (gs : List Gate) (w : List Word) :
    (produced gs w).length = gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => simp [produced, ih]

theorem append_produced (gs : List Gate) (w : List Word) :
    gs.foldl extend w = w ++ produced gs w := by
  induction gs generalizing w with
  | nil => simp [produced]
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [extend, produced, List.append_assoc]

theorem capacity (gs : List Gate) (w stock : List Word) (k : Nat)
    (cover : ∀ a ∈ w, a ∈ stock) (hk : gs.length ≤ k)
    (finish : ∀ a ∈ goals, a ∈ gs.foldl extend w) :
    (lacks stock).card ≤ k := by
  have sub : lacks stock ⊆ (produced gs w).toFinset := by
    intro a ha
    obtain ⟨wanted, absent⟩ := Finset.mem_sdiff.mp ha
    have h := finish a (List.mem_toFinset.mp wanted)
    rw [append_produced] at h
    exact List.mem_toFinset.mpr ((List.mem_append.mp h).resolve_left
      (fun h => absent (List.mem_toFinset.mpr (cover a h))))
  exact (Finset.card_le_card sub).trans ((List.toFinset_card_le _).trans
    (by simpa [produced_length] using hk))

theorem search_complete (gs : List Gate) (w stock : List Word) (k n : Nat)
    (ok : ∀ g ∈ gs, legal g)
    (cover : ∀ a ∈ w, a ∈ stock)
    (zero : (0 : Word) ∈ stock) (one : (31 : Word) ∈ stock)
    (hk : gs.length ≤ k) (hn : (gs.filter isNot).length ≤ n)
    (finish : ∀ a ∈ goals, a ∈ gs.foldl extend w) :
    search k n stock = true := by
  induction k generalizing gs w stock n with
  | zero =>
    have hnil : gs = [] := List.length_eq_zero_iff.mp (by omega)
    subst gs
    exact List.all_eq_true.mpr (fun a ha => List.contains_iff_mem.mpr (cover a (finish a ha)))
  | succ k ih =>
    have fit := capacity gs w stock (k+1) cover hk finish
    cases gs with
    | nil =>
      have done := ih [] w stock n ok cover zero one (by simp) hn finish
      simp [search, fit, done]
    | cons g gs =>
      let xs := g.inputs.map (fun j => w.getD j 0)
      let v := evalWord g.op xs
      have hg := ok g List.mem_cons_self
      have tailOk : ∀ q ∈ gs, legal q := fun q hq => ok q (List.mem_cons_of_mem _ hq)
      have tailLen : gs.length ≤ k := by simpa using hk
      have tailN : (gs.filter isNot).length ≤ n := by
        have h := hn
        simp only [List.filter_cons] at h
        split at h <;> simp_all
        omega
      have tailNNot (ng : isNot g = true) : (gs.filter isNot).length ≤ n - 1 := by
        have h := hn
        simp [ng] at h
        omega
      have posNot (ng : isNot g = true) : n ≠ 0 := by
        have h := hn
        simp [ng] at h
        omega
      have tailFinish : ∀ a ∈ goals, a ∈ gs.foldl extend (w ++ [v]) := finish
      have tailCover {s : List Word} (old : ∀ a ∈ stock, a ∈ s) (val : v ∈ s) :
          ∀ a ∈ w ++ [v], a ∈ s := by
        intro a ha
        simp only [List.mem_append, List.mem_singleton] at ha
        exact ha.elim (fun h => old a (cover a h)) (fun h => h ▸ val)
      have possible : v ∈ stock ∨ (isNot g = false ∧ v ∈ bins stock) ∨
          (isNot g = true ∧ v ∈ stock.map (~~~ ·)) :=
        evalChoice g hg xs stock (by simpa [xs] using hg.2)
          (fun a ha => by
            obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
            exact getCovered w stock cover zero i) zero one
      by_cases hv : v ∈ stock
      · have done := ih gs (w ++ [v]) stock n tailOk
          (tailCover (fun _ h => h) hv) zero one tailLen tailN tailFinish
        simp [search, fit, done]
      · have covers : ∀ a ∈ w ++ [v], a ∈ v :: stock :=
          tailCover (fun _ h => List.mem_cons_of_mem _ h) List.mem_cons_self
        have zero' := List.mem_cons_of_mem v zero
        have one' := List.mem_cons_of_mem v one
        rcases possible.resolve_left hv with ⟨_, hop⟩ | ⟨notg, hop⟩
        · have done := ih gs (w ++ [v]) (v :: stock) n tailOk
            covers zero' one' tailLen tailN tailFinish
          have step : (fresh stock (bins stock)).any (fun x => search k n (x :: stock)) = true :=
            List.any_eq_true.mpr ⟨v, fresh_mem hop hv, done⟩
          simp [search, fit, step]
        · have done := ih gs (w ++ [v]) (v :: stock) (n - 1) tailOk
            covers zero' one' tailLen (tailNNot notg) tailFinish
          have step : (fresh stock (stock.map (~~~ ·))).any
              (fun x => search k (n - 1) (x :: stock)) = true :=
            List.any_eq_true.mpr ⟨v, fresh_mem hop hv, done⟩
          simp [search, fit, posNot notg, step]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noSearch : search 5 2 initial = false := by
  decide +kernel

theorem initialBits : ∀ t : Fin 5, initial.map (bit t) = inputAt t := by
  decide +kernel

theorem sameCount (D : Circuit) : (D.gates.filter isNot).length = notCount D := by
  unfold notCount
  congr 1
  apply List.filter_congr
  intro g _
  rcases g with ⟨op, js⟩
  cases op <;> rfl

theorem word_at (D : Circuit) (ok : ∀ g ∈ D.gates, legal g) (j : Nat) (a : Word)
    (h : ∀ t : Fin 5, (D.wires (inputAt t)).getD j false = a.getLsbD t.val) :
    (D.gates.foldl extend initial).getD j 0 = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let t : Fin 5 := ⟨i, hi⟩
  have sim := simulate t D.gates initial ok
  rw [initialBits] at sim
  change (D.gates.foldl extend initial).map (bit t) = D.wires (inputAt t) at sim
  change bit t ((D.gates.foldl extend initial).getD j 0) = a.getLsbD t.val
  rw [bit_getD, sim]
  exact h t

theorem wires_length (gs : List Gate) (w : List Word) :
    (gs.foldl extend w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, extend, List.length_append, List.length_cons,
      List.length_nil]
    omega

theorem answer : ¬ (∃ (D : Circuit) (p q r : Fin (6 + D.size)),
    FanInTwo D ∧ NestedCover.ReadsBack 6 D ∧ notCount D ≤ 2 ∧ D.size ≤ 5 ∧
    ∀ t : Fin 5,
      let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
      let w := D.wires xs
      w.getD p.val false = (2 : Nat).testBit t.val ∧
      w.getD q.val false = (11 : Nat).testBit t.val ∧
      w.getD r.val false = (18 : Nat).testBit t.val) := by
  rintro ⟨D, p, q, r, forms, _, negs, size, table⟩
  have legalGates (g : Gate) (hg : g ∈ D.gates) : legal g := by
    have got := forms g hg
    simpa [legal, Set.mem_insert_iff, Set.mem_singleton_iff] using got
  let w := D.gates.foldl extend initial
  have contains (j : Fin (6 + D.size)) (a : Word)
      (h : ∀ t : Fin 5, (D.wires (inputAt t)).getD j.val false = a.getLsbD t.val) :
      a ∈ w := by
    have eq := word_at D legalGates j.val a h
    have len : j.val < w.length := by
      simpa [w, wires_length, initial, Circuit.size] using j.isLt
    have em : w[j.val] ∈ w := List.getElem_mem len
    rwa [show w[j.val] = a by simpa [w, List.getD_eq_getElem?_getD, len] using eq] at em
  have hp := contains p 2 (fun t => (table t).1)
  have hq := contains q 11 (fun t => (table t).2.1)
  have hr := contains r 18 (fun t => (table t).2.2)
  have checked := search_complete D.gates initial initial 5 2 legalGates
    (fun _ h => h) (by simp [initial]) (by simp [initial]) size
    (by simpa [sameCount D] using negs) (by
      intro a ha
      simp [goals] at ha
      rcases ha with rfl | rfl | rfl
      exacts [hp, hq, hr])
  rw [noSearch] at checked
  contradiction

end PEqualNP.Outside.L_meta_50047

theorem PEqualNP.Outside.L_meta_50047 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 5,
    let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (2 : Nat).testBit t.val ∧
    w.getD q.val false = (11 : Nat).testBit t.val ∧
    w.getD r.val false = (18 : Nat).testBit t.val)) :=
  PEqualNP.Outside.L_meta_50047.answer
