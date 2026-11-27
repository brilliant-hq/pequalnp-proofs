import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27189

open PEqualNP.CircuitLowerBounds

abbrev Row := Fin 256
abbrev Signal := Row → Bool

def raw (i : Fin 8) (row : Row) : Bool := row.val.testBit i.val

def base (i : Fin 9) (row : Row) : Bool :=
  if i.val < 8 then row.val.testBit i.val else raw 0 row && raw 3 row

def target (row : Row) : Bool :=
  (raw 0 row && raw 3 row && raw 7 row) || (raw 0 row && raw 4 row && raw 6 row) ||
  (raw 1 row && raw 2 row && raw 7 row) || (raw 1 row && raw 4 row && raw 5 row) ||
  (raw 2 row && raw 6 row) || (raw 3 row && raw 5 row)

def singleRows (i : Fin 8) : Row × Row :=
  [(80, 81), (48, 50), (64, 68), (32, 40), (34, 50), (8, 40), (4, 68), (6, 134)][i.val]!

lemma singleRows_ok (i : Fin 8) :
    (∀ j : Fin 9, j.val ≠ i.val → base j (singleRows i).1 = base j (singleRows i).2) ∧
    target (singleRows i).1 ≠ target (singleRows i).2 := by
  fin_cases i <;> decide

def pairRows (left right : Fin 8) : List (Row × Row) :=
  match left.val, right.val with
  | 0, 1 => [(80, 81), (48, 50), (49, 50)]
  | 0, 2 => [(80, 81), (64, 68), (65, 68)]
  | 0, 3 => [(80, 81), (32, 40), (33, 40)]
  | 0, 4 => [(136, 137), (34, 50), (35, 50)]
  | 0, 5 => [(80, 81), (8, 40), (9, 40)]
  | 0, 6 => [(136, 137), (4, 68), (5, 68)]
  | 0, 7 => [(80, 81), (6, 134), (7, 134)]
  | 1, 2 => [(48, 50), (64, 68), (50, 52)]
  | 1, 3 => [(48, 50), (32, 40), (34, 40)]
  | 1, 4 => [(132, 134), (65, 81), (67, 81)]
  | 1, 5 => [(132, 134), (8, 40), (10, 40)]
  | 1, 6 => [(48, 50), (4, 68), (6, 68)]
  | 1, 7 => [(48, 50), (9, 137), (11, 137)]
  | 2, 3 => [(64, 68), (32, 40), (36, 40)]
  | 2, 4 => [(64, 68), (34, 50), (38, 50)]
  | 2, 5 => [(64, 68), (8, 40), (12, 40)]
  | 2, 6 => [(130, 134), (17, 81), (21, 81)]
  | 2, 7 => [(64, 68), (9, 137), (13, 137)]
  | 3, 4 => [(32, 40), (34, 50), (40, 48)]
  | 3, 5 => [(129, 137), (18, 50), (26, 50)]
  | 3, 6 => [(32, 40), (4, 68), (12, 68)]
  | 3, 7 => [(32, 40), (6, 134), (14, 134)]
  | 4, 5 => [(65, 81), (8, 40), (24, 40)]
  | 4, 6 => [(34, 50), (4, 68), (20, 68)]
  | 4, 7 => [(34, 50), (6, 134), (22, 134)]
  | 5, 6 => [(8, 40), (4, 68), (36, 68)]
  | 5, 7 => [(8, 40), (6, 134), (38, 134)]
  | 6, 7 => [(4, 68), (6, 134), (68, 132)]
  | _, _ => []

def separates (left right : Fin 8) (op : Bool → Bool → Bool) (rows : Row × Row) : Prop :=
  (∀ i : Fin 8, i ≠ left → i ≠ right → raw i rows.1 = raw i rows.2) ∧
    op (raw left rows.1) (raw right rows.1) = op (raw left rows.2) (raw right rows.2) ∧
    target rows.1 ≠ target rows.2

def pairCheck (left right : Fin 8) (start finish : Bool × Bool) (rows : Row × Row) : Prop :=
  (∀ i : Fin 8, i ≠ left → i ≠ right → raw i rows.1 = raw i rows.2) ∧
    (raw left rows.1, raw right rows.1) = start ∧
    (raw left rows.2, raw right rows.2) = finish ∧
    target rows.1 ≠ target rows.2

def pairCheckDecidable (left right : Fin 8) (start finish : Bool × Bool) (rows : Row × Row) :
    Decidable (pairCheck left right start finish rows) := by unfold pairCheck; infer_instance

lemma pairCheck.of_checked {left right : Fin 8} {start finish : Bool × Bool} {rows : Row × Row}
    (checked : @decide _ (pairCheckDecidable left right start finish rows) = true) :
    pairCheck left right start finish rows :=
  @of_decide_eq_true _ (pairCheckDecidable left right start finish rows) checked

def pairChecks (left right : Fin 8) : Bool :=
  let rows := pairRows left right
  @decide _ (pairCheckDecidable left right (false, false) (true, false) rows[0]!) &&
    @decide _ (pairCheckDecidable left right (false, false) (false, true) rows[1]!) &&
    @decide _ (pairCheckDecidable left right (true, false) (false, true) rows[2]!)

set_option maxRecDepth 4096 in
lemma pairRows_ok : ∀ (left right : Fin 8), left < right → pairChecks left right = true := by
  intro left right
  fin_cases left <;> fin_cases right <;> decide

lemma pairCheck.separates {left right : Fin 8} {start finish : Bool × Bool} {rows : Row × Row}
    (cert : pairCheck left right start finish rows) (op : Bool → Bool → Bool)
    (heq : op start.1 start.2 = op finish.1 finish.2) : separates left right op rows := by
  refine ⟨cert.1, ?_, cert.2.2.2⟩
  have hfirst := congrArg (fun bits : Bool × Bool => op bits.1 bits.2) cert.2.1
  have hsecond := congrArg (fun bits : Bool × Bool => op bits.1 bits.2) cert.2.2.1
  exact hfirst.trans (heq.trans hsecond.symm)

lemma bool_repeat (first second third : Bool) : first = second ∨ first = third ∨ second = third := by
  revert first second third
  decide

lemma pair_separates (left right : Fin 8) (hne : left ≠ right) (op : Bool → Bool → Bool) :
    ∃ rows, separates left right op rows := by
  have ordered : ∀ (first second : Fin 8), first < second → ∀ comb : Bool → Bool → Bool,
      ∃ rows, separates first second comb rows := by
    intro first second hlt comb
    have cert := pairRows_ok first second hlt
    simp only [pairChecks, Bool.and_eq_true] at cert
    rcases bool_repeat (comb false false) (comb true false) (comb false true) with heq | heq | heq
    · exact ⟨_, (pairCheck.of_checked cert.1.1).separates comb heq⟩
    · exact ⟨_, (pairCheck.of_checked cert.1.2).separates comb heq⟩
    · exact ⟨_, (pairCheck.of_checked cert.2).separates comb heq⟩
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact ordered left right hlt op
  · obtain ⟨rows, hs⟩ := ordered right left hlt (fun rightBit leftBit => op leftBit rightBit)
    exact ⟨rows, fun i hl hr => hs.1 i hr hl, hs.2⟩

def Determines {ι : Type} (signals : ι → Signal) (indices : Finset ι) (value : Signal) : Prop :=
  ∀ x y, (∀ i ∈ indices, signals i x = signals i y) → value x = value y

abbrev liftRaw (i : Fin 8) : Fin 9 := ⟨i.val, by omega⟩

def rawIndices : Finset (Fin 9) := Finset.univ.image liftRaw

lemma mem_rawIndices (i : Fin 9) : i ∈ rawIndices ↔ i.val < 8 := by
  change i ∈ Finset.univ.image liftRaw ↔ _
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    exact j.isLt
  · intro hi
    exact ⟨⟨i.val, hi⟩, rfl⟩

lemma rawIndices_card : rawIndices.card = 8 := by decide

lemma target_card (indices : Finset (Fin 9)) (h : Determines base indices target) :
    8 ≤ indices.card := by
  rw [← rawIndices_card]
  apply Finset.card_le_card
  intro i hi
  by_contra hm
  let j : Fin 8 := ⟨i.val, (mem_rawIndices i).mp hi⟩
  obtain ⟨hag, hne⟩ := singleRows_ok j
  apply hne
  apply h
  intro k hk
  apply hag
  intro heq
  exact hm ((Fin.ext heq : k = i) ▸ hk)

lemma target_no_merge (indices : Finset (Fin 9)) (hsize : indices.card ≤ 6)
    (left right : Fin 9) (op : Bool → Bool → Bool)
    (h : ∀ x y, (∀ i ∈ indices, base i x = base i y) →
      op (base left x) (base right x) = op (base left y) (base right y) → target x = target y) : False := by
  let allIndices := insert left (insert right indices)
  have hincl : rawIndices ⊆ allIndices := by
    intro i hi
    by_contra hm
    let j : Fin 8 := ⟨i.val, (mem_rawIndices i).mp hi⟩
    obtain ⟨hag, hne⟩ := singleRows_ok j
    have agree : ∀ k ∈ allIndices, base k (singleRows j).1 = base k (singleRows j).2 := by
      intro k hk
      apply hag
      intro heq
      exact hm ((Fin.ext heq : k = i) ▸ hk)
    apply hne
    exact h _ _ (fun k hk => agree k (by simp [allIndices, hk]))
      (congrArg₂ op (agree left (by simp [allIndices])) (agree right (by simp [allIndices])))
  have hcard : allIndices.card ≤ 8 := by
    calc
      _ ≤ (insert right indices).card + 1 := Finset.card_insert_le _ _
      _ ≤ indices.card + 2 := by have := Finset.card_insert_le right indices; omega
      _ ≤ 8 := by omega
  have heq : rawIndices = allIndices := Finset.eq_of_subset_of_card_le hincl (by rw [rawIndices_card]; exact hcard)
  have hleft : left ∈ rawIndices := by rw [heq]; simp [allIndices]
  have hright : right ∈ rawIndices := by rw [heq]; simp [allIndices]
  have hleftnew : left ∉ insert right indices := by
    intro hm
    have he := Finset.card_le_card hincl
    rw [rawIndices_card] at he
    dsimp [allIndices] at he
    rw [Finset.insert_eq_of_mem hm] at he
    have := Finset.card_insert_le right indices
    omega
  have hrightnew : right ∉ indices := by
    intro hm
    have he := Finset.card_le_card hincl
    rw [rawIndices_card] at he
    dsimp [allIndices] at he
    rw [Finset.insert_eq_of_mem hm] at he
    have := Finset.card_insert_le left indices
    omega
  let first : Fin 8 := ⟨left.val, (mem_rawIndices left).mp hleft⟩
  let second : Fin 8 := ⟨right.val, (mem_rawIndices right).mp hright⟩
  have hdif : first ≠ second := by
    intro hh
    have hh' : left = right := Fin.ext (congrArg (fun k : Fin 8 => k.val) hh)
    exact hleftnew (by simp [hh'])
  obtain ⟨rows, hrow⟩ := pair_separates first second hdif op
  apply hrow.2.2
  apply h
  · intro i hi
    have hi' : i ∈ rawIndices := by rw [heq]; simp [allIndices, hi]
    have hil := (mem_rawIndices i).mp hi'
    let k : Fin 8 := ⟨i.val, hil⟩
    have hnleft : k ≠ first := by
      intro hh
      have hh' : i = left := Fin.ext (congrArg (fun k : Fin 8 => k.val) hh)
      exact hleftnew (Finset.mem_insert_of_mem (hh' ▸ hi))
    have hnright : k ≠ second := by
      intro hh
      have hh' : i = right := Fin.ext (congrArg (fun k : Fin 8 => k.val) hh)
      exact hrightnew (hh' ▸ hi)
    simpa only [base, ite_eq_left hil, raw] using hrow.1 k hnleft hnright
  · simpa only [base, ite_eq_left ((mem_rawIndices left).mp hleft),
      ite_eq_left ((mem_rawIndices right).mp hright), raw] using hrow.2.1

def arityCost (deps : List ℕ) : ℕ := deps.length - 1

def budget (program : List (List ℕ)) : ℕ := (program.map arityCost).sum

def CanRead (signals : ℕ → Signal) (next : ℕ) (deps : List ℕ) : Prop :=
  deps.length ≤ 2 ∧ (∀ i ∈ deps, i < next) ∧ Determines signals deps.toFinset (signals next)

def Legal (signals : ℕ → Signal) (next : ℕ) : List (List ℕ) → Prop
  | [] => True
  | deps :: rest => CanRead signals next deps ∧ Legal signals (next + 1) rest

lemma frontier (signals : ℕ → Signal) (program : List (List ℕ)) (next out : ℕ)
    (legal : Legal signals next program) (hout : out < next + program.length) :
    ∃ indices : Finset ℕ, (∀ i ∈ indices, i < next) ∧ indices.card ≤ budget program + 1 ∧
      Determines signals indices (signals out) := by
  induction program generalizing next with
  | nil => exact ⟨{out}, by simpa using hout, by simp [budget], fun _ _ ha => ha out (by simp)⟩
  | cons deps rest ih =>
    have htail : out < next + 1 + rest.length := by simp at hout; omega
    obtain ⟨indices, hidx, hcard, hdet⟩ := ih (next + 1) legal.2 htail
    by_cases hmem : next ∈ indices
    · refine ⟨indices.erase next ∪ deps.toFinset, ?_, ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_union.mp hi with hi | hi
        · obtain ⟨hne, hn⟩ := Finset.mem_erase.mp hi
          have := hidx i hn
          omega
        · exact legal.1.2.1 i (List.mem_toFinset.mp hi)
      · have hsize := Finset.card_union_le (indices.erase next) deps.toFinset
        have herase := Finset.card_erase_add_one hmem
        have hd := List.toFinset_card_le deps
        simp only [budget, List.map_cons, List.sum_cons, arityCost] at hcard ⊢
        omega
      · intro x y ha
        apply hdet
        intro i hi
        by_cases hni : i = next
        · subst i
          exact legal.1.2.2 x y (fun j hj => ha j (Finset.mem_union_right _ hj))
        · exact ha i (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hni, hi⟩))
    · refine ⟨indices, ?_, ?_, hdet⟩
      · intro i hi
        have := hidx i hi
        have hne : i ≠ next := by rintro rfl; exact hmem hi
        omega
      · simp only [budget, List.map_cons, List.sum_cons] at hcard ⊢
        omega

def UnaryBase (value : Signal) : Prop := ∃ i : Fin 9, ∃ op : Bool → Bool,
  ∀ row, value row = op (base i row)

lemma factor {α : Type} (key : Row → α) (value : Signal)
    (h : ∀ x y, key x = key y → value x = value y) : ∃ op : α → Bool,
    ∀ row, value row = op (key row) := by
  classical
  refine ⟨fun code => if hex : ∃ row, key row = code then value (Classical.choose hex) else false, ?_⟩
  intro row
  dsimp only
  rw [dite_eq_left ⟨row, rfl⟩]
  exact h _ _ (Classical.choose_spec (show ∃ other, key other = key row from ⟨row, rfl⟩)).symm

lemma unary_extend (signals : ℕ → Signal) (next : ℕ) (deps : List ℕ)
    (short : deps.length ≤ 1) (legal : CanRead signals next deps)
    (initial : ∀ i < next, UnaryBase (signals i)) : UnaryBase (signals next) := by
  cases deps with
  | nil => exact ⟨0, fun _ => signals next 0, fun row => legal.2.2 row 0 (by simp)⟩
  | cons head tail =>
    cases tail with
    | cons head' tail' => simp at short
    | nil =>
      obtain ⟨i, op, h⟩ := initial head (legal.2.1 head (by simp))
      obtain ⟨comb, hcomb⟩ := factor (base i) (signals next) (by
        intro x y hx
        apply legal.2.2
        intro j hj
        have he : j = head := by simpa using hj
        subst j
        rw [h, h, hx])
      exact ⟨i, comb, hcomb⟩

lemma binary_factor (signals : ℕ → Signal) (next first second : ℕ)
    (legal : CanRead signals next [first, second])
    (initial : ∀ i < next, UnaryBase (signals i)) :
    ∃ left right : Fin 9, ∃ op : Bool → Bool → Bool,
      ∀ row, signals next row = op (base left row) (base right row) := by
  obtain ⟨left, lop, hl⟩ := initial first (legal.2.1 _ (by simp))
  obtain ⟨right, rop, hr⟩ := initial second (legal.2.1 _ (by simp))
  obtain ⟨comb, hc⟩ := factor (fun row => (base left row, base right row)) (signals next) (by
    intro x y hxy
    apply legal.2.2
    intro j hj
    have hh : j = first ∨ j = second := by simpa using hj
    rcases hh with rfl | rfl
    · have he : base left x = base left y := congrArg Prod.fst hxy
      rw [hl, hl, he]
    · have he : base right x = base right y := congrArg Prod.snd hxy
      rw [hr, hr, he])
  exact ⟨left, right, fun lbit rbit => comb (lbit, rbit), hc⟩

lemma unary_support (signals : ℕ → Signal) (indices : Finset ℕ)
    (h : ∀ i ∈ indices, UnaryBase (signals i)) : ∃ support : Finset (Fin 9),
      support.card ≤ indices.card ∧ ∀ x y, (∀ j ∈ support, base j x = base j y) →
        ∀ i ∈ indices, signals i x = signals i y := by
  classical
  induction indices using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp⟩
  | @insert head rest hnot ih =>
    obtain ⟨i, op, heq⟩ := h head (by simp)
    obtain ⟨support, hcard, hs⟩ := ih (fun j hj => h j (by simp [hj]))
    refine ⟨insert i support, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hnot]
      exact (Finset.card_insert_le _ _).trans (by omega)
    · intro x y hag j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · rw [heq, heq, hag i (by simp)]
      · exact hs x y (fun k hk => hag k (by simp [hk])) j hj

lemma reject_program (signals : ℕ → Signal) (program : List (List ℕ)) (next out : ℕ)
    (legal : Legal signals next program) (hout : out < next + program.length)
    (small : budget program ≤ 7) (initial : ∀ i < next, UnaryBase (signals i))
    (final : signals out = target) : False := by
  induction program generalizing next with
  | nil =>
    have hi : out < next := by simpa using hout
    obtain ⟨i, op, hop⟩ := initial out hi
    have hd : Determines base {i} target := by
      intro x y ha
      rw [← final, hop, hop, ha i (by simp)]
    have := target_card {i} hd
    simp at this
  | cons deps rest ih =>
    have htail : out < next + 1 + rest.length := by simp at hout; omega
    have hb : budget (deps :: rest) = arityCost deps + budget rest := rfl
    by_cases hshort : deps.length ≤ 1
    · apply ih (next + 1) legal.2 htail (by omega) _
      intro i hi
      by_cases heq : i = next
      · subst i
        exact unary_extend signals next deps hshort legal.1 initial
      · exact initial i (by omega)
    · obtain ⟨first, second, rfl⟩ : ∃ first second, deps = [first, second] := by
        have hd := legal.1.1
        cases deps with
        | nil => simp at hshort
        | cons first rest =>
          cases rest with
          | nil => simp at hshort
          | cons second rest =>
            cases rest with
            | nil => exact ⟨first, second, rfl⟩
            | cons third rest => simp at hd
      have hbudget : budget rest ≤ 6 := by simp [arityCost] at hb; omega
      obtain ⟨left, right, op, hop⟩ := binary_factor signals next first second legal.1 initial
      obtain ⟨indices, hidx, hcard, hdet⟩ := frontier signals rest (next + 1) out legal.2 htail
      by_cases hm : next ∈ indices
      · obtain ⟨support, hc, hs⟩ := unary_support signals (indices.erase next) (by
          intro i hi
          obtain ⟨hne, hi⟩ := Finset.mem_erase.mp hi
          have := hidx i hi
          exact initial i (by omega))
        have he := Finset.card_erase_add_one hm
        apply target_no_merge support (by omega) left right op
        intro x y ha hopxy
        rw [← final]
        apply hdet
        intro i hi
        by_cases heq : i = next
        · subst i
          simpa only [hop] using hopxy
        · exact hs x y ha i (Finset.mem_erase.mpr ⟨heq, hi⟩)
      · obtain ⟨support, hc, hs⟩ := unary_support signals indices (by
          intro i hi
          have hne : i ≠ next := fun he => hm (he ▸ hi)
          have := hidx i hi
          exact initial i (by omega))
        have ht := target_card support (by
          intro x y ha
          rw [← final]
          exact hdet x y (hs x y ha))
        omega

def wire (circ : Circuit) (input : Fin 9 → Bool) (index : ℕ) : Bool :=
  (circ.wires (List.ofFn input)).getD index false

def appendGate (bank : List Bool) (gate : Gate) : List Bool :=
  bank ++ [gate.op.eval (gate.inputs.map fun i => bank.getD i false)]

lemma fold_prefix_length (program : List Gate) (bank : List Bool) :
    bank <+: program.foldl appendGate bank ∧
    (program.foldl appendGate bank).length = bank.length + program.length := by
  induction program generalizing bank with
  | nil => simp
  | cons gate rest ih =>
    obtain ⟨hp, hl⟩ := ih (appendGate bank gate)
    refine ⟨(List.prefix_append bank _).trans hp, ?_⟩
    rw [List.foldl_cons, hl]
    simp [appendGate]
    omega

lemma getD_prefix {left right : List Bool} (h : left <+: right) (index : ℕ)
    (hi : index < left.length) : right.getD index false = left.getD index false := by
  obtain ⟨tail, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wire_input (circ : Circuit) (input : Fin 9 → Bool) (i : Fin 9) :
    wire circ input i.val = input i := by
  unfold wire Circuit.wires
  change (circ.gates.foldl appendGate (List.ofFn input)).getD i.val false = _
  have hi : i.val < (List.ofFn input).length := by simpa only [List.length_ofFn] using i.isLt
  rw [getD_prefix (fold_prefix_length _ _).1 _ hi]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, List.getElem_ofFn]

lemma wire_gate (circ : Circuit) (input : Fin 9 → Bool) (j : Fin circ.gates.length)
    (back : ∀ i ∈ (circ.gates.get j).inputs, i < 9 + j.val) :
    wire circ input (9 + j.val) =
      (circ.gates.get j).op.eval ((circ.gates.get j).inputs.map (wire circ input)) := by
  let bank := (circ.gates.take j.val).foldl appendGate (List.ofFn input)
  have hlen : bank.length = 9 + j.val := by
    dsimp [bank]
    rw [(fold_prefix_length _ _).2]
    simp
  have hsplit : circ.gates = circ.gates.take j.val ++
      circ.gates.get j :: circ.gates.drop (j.val + 1) := by
    simp [List.get_eq_getElem]
  have hpre : appendGate bank (circ.gates.get j) <+:
      circ.gates.foldl appendGate (List.ofFn input) := by
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    exact (fold_prefix_length _ _).1
  have hbank : bank <+: circ.gates.foldl appendGate (List.ofFn input) :=
    (List.prefix_append bank _).trans hpre
  unfold wire Circuit.wires
  change (circ.gates.foldl appendGate (List.ofFn input)).getD (9 + j.val) false = _
  rw [getD_prefix hpre _ (by simp [appendGate, hlen])]
  conv_lhs => rw [← hlen]
  simp only [appendGate, List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (getD_prefix hbank i (by rw [hlen]; exact back i hi)).symm

def NormalGate (next : ℕ) (gate : Gate) : Prop :=
  (gate.op = .not ∧ ∃ a, a < next ∧ gate.inputs = [a]) ∨
  ((gate.op = .and ∨ gate.op = .or) ∧ ∃ a b, a < b ∧ b < next ∧ gate.inputs = [a,b])

lemma NormalGate.back {next : ℕ} {gate : Gate} (hn : NormalGate next gate) :
    ∀ i ∈ gate.inputs, i < next := by
  intro i hi
  rcases hn with ⟨_, a, ha, hlist⟩ | ⟨_, a, b, hab, hb, hlist⟩
  · have he : i = a := by simpa [hlist] using hi
    exact he.symm ▸ ha
  · simp [hlist] at hi
    rcases hi with rfl | rfl <;> omega

def Good (circ : Circuit) : Prop :=
  ∀ j : Fin circ.gates.length, NormalGate (9 + j.val) (circ.gates.get j)

def firstGate : Gate := ⟨.and, [0,4]⟩
def secondGate : Gate := ⟨.not, [2]⟩

def Starts (circ : Circuit) : Prop := ∃ rest, circ.gates = firstGate :: secondGate :: rest

lemma Starts.length_ge {circ : Circuit} (hstart : Starts circ) : 2 ≤ circ.gates.length := by
  obtain ⟨rest, hr⟩ := hstart
  simp [hr]

lemma wire_first (circ : Circuit) (hstart : Starts circ) (input : Fin 9 → Bool) :
    wire circ input 9 = (input 0 && input 4) := by
  obtain ⟨rest, hr⟩ := hstart
  let j : Fin circ.gates.length := ⟨0, by simp [hr]⟩
  have hg : circ.gates.get j = firstGate := by simp [List.get_eq_getElem, j, hr]
  have h := wire_gate circ input j (by rw [hg]; simp [firstGate, j])
  have hzero := wire_input circ input 0
  have hfour := wire_input circ input 4
  change wire circ input 0 = input 0 at hzero
  change wire circ input 4 = input 4 at hfour
  rw [hg] at h
  simpa [j, firstGate, GateOp.eval, hzero, hfour] using h

lemma wire_second (circ : Circuit) (hstart : Starts circ) (input : Fin 9 → Bool) :
    wire circ input 10 = !input 2 := by
  obtain ⟨rest, hr⟩ := hstart
  let j : Fin circ.gates.length := ⟨1, by simp [hr]⟩
  have hg : circ.gates.get j = secondGate := by simp [List.get_eq_getElem, j, hr]
  have h := wire_gate circ input j (by rw [hg]; simp [secondGate, j])
  have htwo := wire_input circ input 2
  change wire circ input 2 = input 2 at htwo
  rw [hg] at h
  simpa [j, secondGate, GateOp.eval, htwo] using h

def liftRow (fixed : Bool) (row : Row) (i : Fin 9) : Bool :=
  if i.val = 2 then fixed else row.val.testBit (if i.val < 2 then i.val else i.val - 1)

def perfect (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
    (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

lemma perfect_liftRow (row : Row) : perfect (liftRow true row) = target row := by
  rfl

def restricted (circ : Circuit) (index : ℕ) (row : Row) : Bool :=
  wire circ (liftRow true row) index

lemma restricted_two (circ : Circuit) (row : Row) : restricted circ 2 row = true :=
  wire_input circ (liftRow true row) 2

lemma restricted_ten (circ : Circuit) (hstart : Starts circ) (row : Row) :
    restricted circ 10 row = false := wire_second circ hstart (liftRow true row)

lemma restricted_base (circ : Circuit) (hstart : Starts circ) :
    ∀ i < 11, UnaryBase (restricted circ i) := by
  intro i hi
  have hin : ∀ j : Fin 9, restricted circ j.val = (liftRow true · j) := by
    intro j
    funext row
    exact wire_input circ (liftRow true row) j
  interval_cases i
  · exact ⟨0, id, fun row => congrFun (hin 0) row⟩
  · exact ⟨1, id, fun row => congrFun (hin 1) row⟩
  · exact ⟨0, fun _ => true, restricted_two circ⟩
  · exact ⟨2, id, fun row => congrFun (hin 3) row⟩
  · exact ⟨3, id, fun row => congrFun (hin 4) row⟩
  · exact ⟨4, id, fun row => congrFun (hin 5) row⟩
  · exact ⟨5, id, fun row => congrFun (hin 6) row⟩
  · exact ⟨6, id, fun row => congrFun (hin 7) row⟩
  · exact ⟨7, id, fun row => congrFun (hin 8) row⟩
  · exact ⟨8, id, fun row => wire_first circ hstart (liftRow true row)⟩
  · exact ⟨0, fun _ => false, restricted_ten circ hstart⟩

def depsOf (gate : Gate) : List ℕ := gate.inputs.filter fun i => i != 2 && i != 10

lemma deps_le {next : ℕ} {gate : Gate} (good : NormalGate next gate) :
    (depsOf gate).length ≤ 2 := by
  have hbound := List.length_filter_le (p := fun i : ℕ => i != 2 && i != 10) gate.inputs
  apply hbound.trans
  rcases good with ⟨_, a, _, hi⟩ | ⟨_, a, b, _, _, hi⟩ <;> simp [hi]

lemma deps_zero_of_not {next : ℕ} {gate : Gate} (good : NormalGate next gate)
    (hnot : gate.op = .not) : arityCost (depsOf gate) = 0 := by
  rcases good with ⟨_, a, _, hinputs⟩ | ⟨hop, _⟩
  · have h := List.length_filter_le (p := fun i : ℕ => i != 2 && i != 10) gate.inputs
    change (depsOf gate).length ≤ gate.inputs.length at h
    rw [hinputs] at h
    simp only [List.length_singleton] at h
    simp [arityCost, Nat.sub_eq_zero_of_le h]
  · simp [hnot] at hop

lemma deps_zero_of_const {next : ℕ} {gate : Gate} (good : NormalGate next gate)
    (i : ℕ) (hi : i = 2 ∨ i = 10) (hread : i ∈ gate.inputs) :
    arityCost (depsOf gate) = 0 := by
  have hshort : (depsOf gate).length < gate.inputs.length := by
    apply List.length_filter_lt_length_iff_exists.mpr
    exact ⟨i, hread, by rcases hi with rfl | rfl <;> decide⟩
  have hg : gate.inputs.length ≤ 2 := by
    rcases good with ⟨_, a, _, hlist⟩ | ⟨_, a, b, _, _, hlist⟩ <;> simp [hlist]
  unfold arityCost
  omega

lemma restricted_reads (circ : Circuit) (hstart : Starts circ) (good : Good circ)
    (j : Fin circ.gates.length) :
    CanRead (restricted circ) (9 + j.val) (depsOf (circ.gates.get j)) := by
  refine ⟨deps_le (good j), ?_, ?_⟩
  · intro i hi
    exact (good j).back i (List.mem_filter.mp hi).1
  · intro x y hxy
    unfold restricted
    rw [wire_gate circ _ j (good j).back, wire_gate circ _ j (good j).back]
    congr 1
    apply List.map_congr_left
    intro i hi
    by_cases htwo : i = 2
    · subst i
      exact (restricted_two circ x).trans (restricted_two circ y).symm
    by_cases hten : i = 10
    · subst i
      exact (restricted_ten circ hstart x).trans (restricted_ten circ hstart y).symm
    exact hxy i (List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hi, by simp [htwo, hten]⟩))

lemma legal_of_get (signals : ℕ → Signal) (program : List (List ℕ)) (next : ℕ)
    (h : ∀ j : Fin program.length, CanRead signals (next + j.val) (program.get j)) :
    Legal signals next program := by
  induction program generalizing next with
  | nil => trivial
  | cons head tail ih =>
    refine ⟨h ⟨0, by simp⟩, ih (next + 1) ?_⟩
    intro j
    simpa [Nat.add_right_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      h ⟨j.val + 1, by simpa using j.isLt⟩

lemma budget_small (program : List (List ℕ))
    (hshort : ∀ deps ∈ program, deps.length ≤ 2)
    (first second : Fin program.length) (hne : first ≠ second)
    (hfirst : arityCost (program.get first) = 0) (hsecond : arityCost (program.get second) = 0) :
    budget program ≤ program.length - 2 := by
  have hsum : budget program = ∑ i : Fin program.length, arityCost (program.get i) := by
    rw [← List.sum_ofFn]
    simp [budget, List.ofFn_getElem_eq_map, List.get_eq_getElem]
  let remaining := (Finset.univ.erase first).erase second
  have hs : (∑ i ∈ remaining, arityCost (program.get i)) = budget program := by
    rw [hsum]
    have hf := Finset.sum_erase_add (s := Finset.univ) (f := fun i => arityCost (program.get i))
      (Finset.mem_univ first)
    have ht := Finset.sum_erase_add (s := Finset.univ.erase first) (f := fun i => arityCost (program.get i))
      (show second ∈ Finset.univ.erase first by simp [hne.symm])
    rw [hsecond, Nat.add_zero] at ht
    rw [hfirst, Nat.add_zero] at hf
    exact ht.trans hf
  have hc : remaining.card = program.length - 2 := by
    have hp := Finset.card_erase_of_mem (s := Finset.univ) (Finset.mem_univ first)
    have hq := Finset.card_erase_of_mem (show second ∈ Finset.univ.erase first by simp [hne.symm])
    simp only [Finset.card_univ, Fintype.card_fin] at hp
    dsimp [remaining]
    omega
  rw [← hs, ← hc]
  calc
    _ ≤ ∑ _ ∈ remaining, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro i _
      have hi := hshort (program.get i) (List.get_mem _ _)
      unfold arityCost
      omega
    _ = _ := by simp

def DistinctWires (circ : Circuit) : Prop :=
  ∀ j : Fin circ.gates.length, ∀ k, k < 9 + j.val → ∃ input : Fin 9 → Bool,
    wire circ input (9 + j.val) ≠ wire circ input k

def NonconstantWires (circ : Circuit) : Prop :=
  ∀ j : Fin circ.gates.length, ∃ x y : Fin 9 → Bool,
    wire circ x (9 + j.val) ≠ wire circ y (9 + j.val)

def UsedGates (circ : Circuit) : Prop :=
  ∀ j : Fin circ.gates.length, j.val + 1 < circ.gates.length →
    ∃ k : Fin circ.gates.length, j.val < k.val ∧ 9 + j.val ∈ (circ.gates.get k).inputs

lemma input_two (circ : Circuit) (input : Fin 9 → Bool) : wire circ input 2 = input 2 :=
  wire_input circ input 2

lemma reader_ten (circ : Circuit) (hstart : Starts circ) (good : Good circ)
    (distinct : DistinctWires circ) (used : UsedGates circ) (hl : 2 < circ.gates.length) :
    ∃ j : Fin circ.gates.length, 2 ≤ j.val ∧ 10 ∈ (circ.gates.get j).inputs ∧
      (circ.gates.get j).op ≠ .not := by
  let second : Fin circ.gates.length := ⟨1, by omega⟩
  obtain ⟨j, hgt, hj⟩ := used second (by simpa [second] using hl)
  refine ⟨j, by change 1 < j.val at hgt; omega, hj, ?_⟩
  intro hn
  rcases good j with ⟨_, a, _, hi⟩ | ⟨hop, _⟩
  · change 10 ∈ (circ.gates.get j).inputs at hj
    rw [hi, List.mem_singleton] at hj
    have ha : a = 10 := hj.symm
    obtain ⟨input, hdiff⟩ := distinct j 2 (by omega)
    apply hdiff
    rw [wire_gate circ input j (good j).back, hn, hi, ha, input_two]
    simp [GateOp.eval, wire_second circ hstart input]
  · rw [hn] at hop
    rcases hop with hop | hop <;> contradiction

lemma not_reads_both (circ : Circuit) (hstart : Starts circ) (good : Good circ)
    (nonconst : NonconstantWires circ) (j : Fin circ.gates.length)
    (h2 : 2 ∈ (circ.gates.get j).inputs) (h10 : 10 ∈ (circ.gates.get j).inputs) : False := by
  rcases good j with ⟨_, a, _, hi⟩ | ⟨hop, a, b, hab, _, hi⟩
  · rw [hi, List.mem_singleton] at h2 h10
    omega
  · have hinputs : (circ.gates.get j).inputs = [2,10] := by
      rw [hi] at h2 h10
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h2 h10
      have hindices : a = 2 ∧ b = 10 := by
        rcases h2 with h2 | h2 <;> rcases h10 with h10 | h10 <;> omega
      rw [hi, hindices.1, hindices.2]
    obtain ⟨x, y, hdiff⟩ := nonconst j
    apply hdiff
    rw [wire_gate circ x j (good j).back, wire_gate circ y j (good j).back, hinputs]
    rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval, input_two, wire_second circ hstart]

lemma bool_binary_mono (a b c d : Bool) (ha : a ≤ c) (hb : b ≤ d) :
    (a && b) ≤ (c && d) ∧ (a || b) ≤ (c || d) := by
  revert a b c d
  decide

lemma flip_wire (circ : Circuit) (hstart : Starts circ) (good : Good circ)
    (hnot : ∀ j : Fin circ.gates.length, 2 ≤ j.val → (circ.gates.get j).op ≠ .not)
    (hreader : ∀ j : Fin circ.gates.length, 2 ≤ j.val → 2 ∉ (circ.gates.get j).inputs)
    (row : Row) (i : ℕ) (hibound : i < 9 + circ.gates.length) (hi2 : i ≠ 2) :
    wire circ (liftRow true row) i ≤ wire circ (liftRow false row) i := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases hin : i < 9
    · let idx : Fin 9 := ⟨i, hin⟩
      have ht := wire_input circ (liftRow true row) idx
      have hf := wire_input circ (liftRow false row) idx
      change wire circ (liftRow true row) i = _ at ht
      change wire circ (liftRow false row) i = _ at hf
      rw [ht, hf]
      simp [liftRow, idx, hi2]
    by_cases hfirst : i = 9
    · subst i
      simp [wire_first circ hstart, liftRow]
    by_cases hsecond : i = 10
    · subst i
      simp [wire_second circ hstart, liftRow]
    let j : Fin circ.gates.length := ⟨i - 9, by omega⟩
    have hj : 2 ≤ j.val := by dsimp [j]; omega
    have heq : 9 + j.val = i := by dsimp [j]; omega
    rw [← heq, wire_gate circ _ j (good j).back, wire_gate circ _ j (good j).back]
    rcases good j with ⟨hop, _⟩ | ⟨hop, a, b, hab, hb, hinputs⟩
    · exact (hnot j hj hop).elim
    · have hneA : a ≠ 2 := by
        intro he
        exact hreader j hj (by rw [hinputs, he]; simp)
      have hneB : b ≠ 2 := by
        intro he
        exact hreader j hj (by rw [hinputs, he]; simp)
      obtain ⟨hand, hor⟩ := bool_binary_mono _ _ _ _
        (ih a (by omega) (by omega) hneA) (ih b (by omega) (by omega) hneB)
      rw [hinputs]
      rcases hop with hop | hop
      · rw [hop]
        simpa [GateOp.eval] using hand
      · rw [hop]
        simpa [GateOp.eval] using hor

lemma reader_two_of_monotone (circ : Circuit) (hstart : Starts circ) (good : Good circ)
    (hnot : ∀ j : Fin circ.gates.length, 2 ≤ j.val → (circ.gates.get j).op ≠ .not)
    (hout : circ.output + 1 = 9 + circ.gates.length)
    (heval : ∀ input : Fin 9 → Bool, wire circ input circ.output = perfect input) :
    ∃ j : Fin circ.gates.length, 2 ≤ j.val ∧ 2 ∈ (circ.gates.get j).inputs := by
  by_contra! hreader
  have hc := hstart.length_ge
  have hmono := flip_wire circ hstart good hnot hreader 68 circ.output (by omega) (by omega)
  rw [heval, heval] at hmono
  exact (show ¬ (perfect (liftRow true 68) ≤ perfect (liftRow false 68)) by decide) hmono

lemma drop_two_losses (circ : Circuit) (hstart : Starts circ) (good : Good circ)
    (nonconst : NonconstantWires circ) (distinct : DistinctWires circ) (used : UsedGates circ)
    (hout : circ.output + 1 = 9 + circ.gates.length)
    (heval : ∀ input : Fin 9 → Bool, wire circ input circ.output = perfect input)
    (hsize : circ.gates.length ≤ 11) :
    budget ((circ.gates.drop 2).map depsOf) ≤ 7 := by
  classical
  have hl : 2 < circ.gates.length := by
    have hbound := hstart.length_ge
    by_contra! hle
    have heq : circ.output = 10 := by omega
    have ht : wire circ (liftRow true 68) 10 = true := by
      rw [← heq, heval]
      decide
    rw [wire_second circ hstart] at ht
    change false = true at ht
    contradiction
  obtain ⟨first, hfirst, hten, hnfirst⟩ := reader_ten circ hstart good distinct used hl
  obtain ⟨second, hsecond, hne, hzero⟩ : ∃ j : Fin circ.gates.length,
      2 ≤ j.val ∧ first ≠ j ∧ arityCost (depsOf (circ.gates.get j)) = 0 := by
    by_cases hex : ∃ j : Fin circ.gates.length, 2 ≤ j.val ∧ (circ.gates.get j).op = .not
    · obtain ⟨j, hj, hnot⟩ := hex
      exact ⟨j, hj, fun he => hnfirst (he ▸ hnot), deps_zero_of_not (good j) hnot⟩
    · push Not at hex
      obtain ⟨j, hj, htwo⟩ := reader_two_of_monotone circ hstart good hex hout heval
      exact ⟨j, hj, fun he => not_reads_both circ hstart good nonconst j htwo (he ▸ hten),
        deps_zero_of_const (good j) 2 (Or.inl rfl) htwo⟩
  let program := (circ.gates.drop 2).map depsOf
  have hlen : program.length = circ.gates.length - 2 := by simp [program]
  let front : Fin program.length := ⟨first.val - 2, by rw [hlen]; have := first.isLt; omega⟩
  let back : Fin program.length := ⟨second.val - 2, by rw [hlen]; have := second.isLt; omega⟩
  have align (j : Fin program.length) : program.get j =
      depsOf (circ.gates.get ⟨2 + j.val, by have := j.isLt; omega⟩) := by
    simp [List.get_eq_getElem, program, Nat.add_comm]
  have hfront : program.get front = depsOf (circ.gates.get first) := by
    rw [align]
    congr 2
    apply Fin.ext
    dsimp [front]
    omega
  have hback : program.get back = depsOf (circ.gates.get second) := by
    rw [align]
    congr 2
    apply Fin.ext
    dsimp [back]
    omega
  have hdiff : front ≠ back := by
    intro he
    apply hne
    apply Fin.ext
    have hv := congrArg Fin.val he
    dsimp [front, back] at hv
    omega
  have hs := budget_small program (by
    intro deps hd
    obtain ⟨j, hj⟩ := List.get_of_mem hd
    rw [← hj, align]
    exact deps_le (good _)) front back hdiff
    (by rw [hfront]; exact deps_zero_of_const (good first) 10 (Or.inr rfl) hten)
    (by rw [hback]; exact hzero)
  change budget program ≤ 7
  omega

lemma starts_of_heads (circ : Circuit) (hhead : circ.gates.head? = some firstGate)
    (htail : circ.gates.tail.head? = some secondGate) : Starts circ := by
  cases hg : circ.gates with
  | nil => simp [hg] at hhead
  | cons first rest =>
    cases hr : rest with
    | nil => simp [hg, hr] at htail
    | cons second tail =>
      simp [hg, hr] at hhead htail
      exact ⟨tail, by simp [hg, hr, hhead, htail]⟩

lemma reject_circuit (circ : Circuit) (hstart : Starts circ) (good : Good circ)
    (nonconst : NonconstantWires circ) (distinct : DistinctWires circ) (used : UsedGates circ)
    (hout : circ.output + 1 = 9 + circ.gates.length)
    (heval : ∀ input : Fin 9 → Bool, wire circ input circ.output = perfect input)
    (hsize : circ.gates.length ≤ 11) : False := by
  let program := (circ.gates.drop 2).map depsOf
  have hlen : program.length = circ.gates.length - 2 := by simp [program]
  have hbase := hstart.length_ge
  apply reject_program (restricted circ) program 11 circ.output
  · apply legal_of_get
    intro j
    have hj := j.isLt
    let k : Fin circ.gates.length := ⟨2 + j.val, by omega⟩
    have heq : program.get j = depsOf (circ.gates.get k) := by
      simp [List.get_eq_getElem, program, k, Nat.add_comm]
    rw [heq]
    convert restricted_reads circ hstart good k using 1
    dsimp [k]
    omega
  · omega
  · exact drop_two_losses circ hstart good nonconst distinct used hout heval hsize
  · exact restricted_base circ hstart
  · funext row
    exact (heval _).trans (perfect_liftRow row)

end PEqualNP.Outside.L_meta_27189

theorem PEqualNP.Outside.L_meta_27189 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [2]⟩)) := by
  rintro ⟨circ, _, hsize, heval, hout, hnormal, hwires, hused, hfirst, hsecond⟩
  exact _root_.PEqualNP.Outside.L_meta_27189.reject_circuit circ
    (_root_.PEqualNP.Outside.L_meta_27189.starts_of_heads circ hfirst hsecond) hnormal
    (fun j => (hwires j).1) (fun j => (hwires j).2) hused hout heval hsize
