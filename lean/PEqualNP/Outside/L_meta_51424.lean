import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_51424_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket

noncomputable def inp {n : Nat} (x : Finset (Fin n)) : List Bool :=
  List.ofFn (fun i : Fin n => @decide (i ∈ x) (Classical.propDecidable _)) ++ [false, true]

lemma inp_length {n : Nat} (x : Finset (Fin n)) : (inp x).length = n + 2 := by simp [inp]

lemma classical_insert {n : Nat} (j : Fin n) (x : Finset (Fin n)) :
    (letI : ∀ p : Prop, Decidable p := Classical.propDecidable; insert j x) = insert j x := by
  ext i
  simp only [Finset.mem_insert]

noncomputable def val {n : Nat} (C : Circuit) (a : Fin n → Fin (n + 2 + C.size))
    (x : Finset (Fin n)) (j : Fin n) : Bool :=
  (C.wires (inp x)).getD (a j).val false

def valid (n b : Nat) (C : Circuit) : Prop :=
  FanInTwo C ∧ ReadsBack (n+2) C ∧ C.output < n+2+C.size ∧ notCount C ≤ b

-- Wire, sequential gate-building, and unary inversion helpers adapted from
-- lean/PEqualNP/Outside/L_lib_1262.lean at 232d467ea394f7d4d61352a1740c7df677fb40fc.
-- The construction below uses shared sparse containment tests of both ordinary and cofactored inputs.
def evalWires (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma evalWires_append (gs₁ gs₂ : List Gate) (x : List Bool) :
    evalWires (gs₁ ++ gs₂) x = evalWires gs₂ (evalWires gs₁ x) := by
  unfold evalWires
  rw [List.foldl_append]

lemma evalWires_length (gs : List Gate) (x : List Bool) :
    (evalWires gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [evalWires]
  | cons g tl ih =>
    simp only [evalWires, List.foldl_cons]
    have := ih (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])
    unfold evalWires at this
    rw [this, List.length_append, List.length_singleton, List.length_cons]
    omega

lemma getD_append_left {α : Type*} (l₁ l₂ : List α) (d : α) {i : ℕ} (hi : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
    List.getD_eq_getElem _ _ hi, List.getElem_append_left hi]

lemma getD_append_singleton_last {α : Type*} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]
  simp

lemma evalWires_snoc_last (gs : List Gate) (g : Gate) (x : List Bool) :
    (evalWires (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (evalWires gs x).getD i false) := by
  rw [evalWires_append]
  unfold evalWires
  simp only [List.foldl_cons, List.foldl_nil]
  rw [← evalWires_length gs x]
  exact getD_append_singleton_last (evalWires gs x) _ false

lemma getD_of_le {α : Type*} (l : List α) (d : α) {i : ℕ} (hi : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD, List.getElem?_eq_none hi]

lemma evalWires_snoc_old (gs : List Gate) (g : Gate) (x : List Bool) {i : ℕ}
    (hi : i < x.length + gs.length) :
    (evalWires (gs ++ [g]) x).getD i false = (evalWires gs x).getD i false := by
  rw [evalWires_append]
  change (evalWires gs x ++ [g.op.eval (g.inputs.map fun k => (evalWires gs x).getD k false)]).getD i false = _
  apply getD_append_left
  rw [evalWires_length]
  exact hi
def nc (gs : List Gate) : ℕ := notCount ⟨gs, 0⟩

lemma nc_append (a b : List Gate) : nc (a ++ b) = nc a + nc b := by
  simp [nc, notCount, List.filter_append]

lemma nc_and (l : List ℕ) : nc [⟨GateOp.and, l⟩] = 0 := by simp [nc, notCount]
lemma nc_or (l : List ℕ) : nc [⟨GateOp.or, l⟩] = 0 := by simp [nc, notCount]
lemma nc_not (l : List ℕ) : nc [⟨GateOp.not, l⟩] = 1 := by simp [nc, notCount]

def Ok (I : ℕ) (gs : List Gate) : Prop := FanInTwo ⟨gs, 0⟩ ∧ ReadsBack I ⟨gs, 0⟩

lemma ok_nil (I : ℕ) : Ok I [] := by
  refine ⟨?_, ?_⟩
  · intro g hg; simp at hg
  · intro j hj; simp at hj

lemma ok_snoc {I : ℕ} {gs : List Gate} {g : Gate} (h : Ok I gs)
    (hop : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hlen : g.inputs.length ≤ 2)
    (hin : ∀ i ∈ g.inputs, i < I + gs.length) : Ok I (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro g' hg'
    simp only [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · exact h.1 g' hg'
    · refine ⟨?_, hlen⟩
      rcases hop with hop | hop | hop <;> simp [hop]
  · intro j hj i hi
    have h2 := h.2
    simp only [List.length_append, List.length_singleton] at hj
    unfold gateAt at hi
    by_cases hjl : j < gs.length
    · have : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ :=
        getD_append_left _ _ _ hjl
      rw [this] at hi
      exact h2 j hjl i hi
    · have hj' : j = gs.length := by omega
      subst hj'
      have : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := getD_append_singleton_last _ _ _
      rw [this] at hi
      exact hin i hi

lemma evalWires_getD_lt (hs : List Gate) (y : List Bool) {i : ℕ} (hi : i < y.length) :
    (evalWires hs y).getD i false = y.getD i false := by
  induction hs generalizing y with
  | nil => rfl
  | cons g hs ih =>
    simp only [evalWires, List.foldl_cons]
    have := ih (y ++ [g.op.eval (g.inputs.map fun k => y.getD k false)]) (by simp; omega)
    unfold evalWires at this
    rw [this]
    exact getD_append_left _ _ _ hi

section Build
variable {X : Type*} {I : ℕ} {inp : X → List Bool}

def V (inp : X → List Bool) (gs : List Gate) (x : X) (w : ℕ) : Bool :=
  (evalWires gs (inp x)).getD w false

def Carries (I : ℕ) (inp : X → List Bool) (gs : List Gate) (w : ℕ) (φ : X → Bool) : Prop :=
  w < I + gs.length ∧ ∀ x, V inp gs x w = φ x

lemma carries_congr {gs : List Gate} {w : ℕ} {φ ψ : X → Bool} (h : Carries I inp gs w φ)
    (he : ∀ x, φ x = ψ x) : Carries I inp gs w ψ :=
  ⟨h.1, fun x => (h.2 x).trans (he x)⟩

lemma carries_ext (hI : ∀ x, (inp x).length = I) {gs : List Gate} {w : ℕ} {φ : X → Bool}
    (h : Carries I inp gs w φ) (hs : List Gate) : Carries I inp (gs ++ hs) w φ := by
  refine ⟨by have := h.1; simp; omega, fun x => ?_⟩
  unfold V
  rw [evalWires_append, evalWires_getD_lt _ _ (by rw [evalWires_length, hI]; exact h.1)]
  exact h.2 x

lemma carries_pre (hI : ∀ x, (inp x).length = I) {gs gs' : List Gate} {w : ℕ} {φ : X → Bool}
    (h : Carries I inp gs w φ) (hp : gs <+: gs') : Carries I inp gs' w φ := by
  obtain ⟨hs, rfl⟩ := hp
  exact carries_ext hI h hs

lemma carries_input (hI : ∀ x, (inp x).length = I) (gs : List Gate) {i : ℕ} (hi : i < I) :
    Carries I inp gs i (fun x => (inp x).getD i false) := by
  refine ⟨by omega, fun x => ?_⟩
  unfold V
  rw [evalWires_getD_lt _ _ (by rw [hI]; exact hi)]

lemma V_snoc (hI : ∀ x, (inp x).length = I) (gs : List Gate) (g : Gate) (x : X) :
    V inp (gs ++ [g]) x (I + gs.length) = g.op.eval (g.inputs.map (V inp gs x)) := by
  unfold V
  rw [← hI x]
  exact evalWires_snoc_last gs g (inp x)

lemma add2 (hI : ∀ x, (inp x).length = I) {gs : List Gate} {p q : ℕ} {φ ψ : X → Bool}
    {op : GateOp} (hop : op = .and ∨ op = .or) (hok : Ok I gs)
    (hp : Carries I inp gs p φ) (hq : Carries I inp gs q ψ) :
    Ok I (gs ++ [⟨op, [p, q]⟩]) ∧ nc [⟨op, [p, q]⟩] = 0 ∧
      Carries I inp (gs ++ [⟨op, [p, q]⟩]) (I + gs.length) (fun x => op.eval [φ x, ψ x]) := by
  refine ⟨ok_snoc hok (by rcases hop with h | h <;> simp [h]) (by simp) ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact hp.1
    · exact hq.1
  · rcases hop with rfl | rfl
    · exact nc_and _
    · exact nc_or _
  · simp
  · intro x
    rw [V_snoc hI]
    simp [hp.2 x, hq.2 x]

lemma addNot (hI : ∀ x, (inp x).length = I) {gs : List Gate} {p : ℕ} {φ : X → Bool}
    (hok : Ok I gs) (hp : Carries I inp gs p φ) :
    Ok I (gs ++ [⟨GateOp.not, [p]⟩]) ∧ nc [⟨GateOp.not, [p]⟩] = 1 ∧
      Carries I inp (gs ++ [⟨GateOp.not, [p]⟩]) (I + gs.length) (fun x => !φ x) := by
  refine ⟨ok_snoc hok (by simp) (by simp) ?_, nc_not _, by simp, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi; exact hp.1
  · intro x
    rw [V_snoc hI]
    simp [hp.2 x, GateOp.eval]

lemma chain (hI : ∀ x, (inp x).length = I) {β : Type*} (op : GateOp) (hop : op = .and ∨ op = .or)
    (wf : β → ℕ) (ψ : β → X → Bool) :
    ∀ (l : List β) (gs : List Gate) (acc : ℕ) (φ0 : X → Bool), Ok I gs →
      Carries I inp gs acc φ0 → (∀ b ∈ l, Carries I inp gs (wf b) (ψ b)) →
      ∃ hs, Ok I (gs ++ hs) ∧ nc hs = 0 ∧ hs.length = l.length ∧ ∃ w,
        Carries I inp (gs ++ hs) w (fun x => l.foldl (fun a b => op.eval [a, ψ b x]) (φ0 x)) := by
  intro l
  induction l with
  | nil =>
    intro gs acc φ0 hok hacc _
    exact ⟨[], by simpa using hok, rfl, rfl, acc, by simpa using hacc⟩
  | cons b l ih =>
    intro gs acc φ0 hok hacc hl
    obtain ⟨hok1, hnc1, hw1⟩ := add2 hI hop hok hacc (hl b (List.mem_cons_self ..))
    obtain ⟨hs, hok2, hnc2, hlen2, w, hw⟩ := ih (gs ++ [⟨op, [acc, wf b]⟩]) (I + gs.length) _ hok1
      hw1 (fun b' hb' => carries_ext hI (hl b' (List.mem_cons_of_mem _ hb')) _)
    refine ⟨[⟨op, [acc, wf b]⟩] ++ hs, ?_, ?_, by simp [hlen2], w, ?_⟩
    · rw [← List.append_assoc]; exact hok2
    · rw [nc_append, hnc1, hnc2]
    · rw [← List.append_assoc]; exact hw

lemma foldl_and {β : Type*} (ψ : β → Bool) :
    ∀ (l : List β) (a : Bool), l.foldl (fun a b => GateOp.and.eval [a, ψ b]) a = (a && l.all ψ)
  | [], a => by simp
  | b :: l, a => by
    rw [List.foldl_cons, foldl_and ψ l]
    simp [GateOp.eval, Bool.and_assoc]

lemma foldl_or {β : Type*} (ψ : β → Bool) :
    ∀ (l : List β) (a : Bool), l.foldl (fun a b => GateOp.or.eval [a, ψ b]) a = (a || l.any ψ)
  | [], a => by simp
  | b :: l, a => by
    rw [List.foldl_cons, foldl_or ψ l]
    simp [GateOp.eval, Bool.or_assoc]

lemma many (hI : ∀ x, (inp x).length = I) {β : Type*} (c : ℕ) (φ : β → X → Bool)
    (gs : List Gate) (hok : Ok I gs) :
    ∀ (L : List β), (∀ hs0, Ok I (gs ++ hs0) → ∀ b ∈ L, ∃ hs, Ok I (gs ++ hs0 ++ hs) ∧ nc hs = 0 ∧
      hs.length ≤ c ∧ ∃ w, Carries I inp (gs ++ hs0 ++ hs) w (φ b)) →
    ∃ hs, Ok I (gs ++ hs) ∧ nc hs = 0 ∧ hs.length ≤ c * L.length ∧
      ∃ wf : β → ℕ, ∀ b ∈ L, Carries I inp (gs ++ hs) (wf b) (φ b) := by
  classical
  intro L
  induction L with
  | nil =>
    intro _
    exact ⟨[], by simpa using hok, rfl, by simp, fun _ => 0, by simp⟩
  | cons b L ih =>
    intro hstep
    obtain ⟨hs1, ok1, nc1, len1, wf, hwf⟩ :=
      ih (fun hs0 h b' hb' => hstep hs0 h b' (List.mem_cons_of_mem _ hb'))
    obtain ⟨hs2, ok2, nc2, len2, w, hw⟩ := hstep hs1 ok1 b (List.mem_cons_self ..)
    refine ⟨hs1 ++ hs2, by rw [← List.append_assoc]; exact ok2, by rw [nc_append, nc1, nc2],
      ?_, fun b' => if b' = b then w else wf b', ?_⟩
    · simp only [List.length_append, List.length_cons, Nat.mul_succ]; omega
    · intro b' hb'
      by_cases hbb : b' = b
      · subst hbb; simp only [ite_true]; rw [← List.append_assoc]; exact hw
      · simp only [hbb, ite_false]
        have hb'' : b' ∈ L := by
          rcases List.mem_cons.mp hb' with h | h
          · exact absurd h hbb
          · exact h
        rw [← List.append_assoc]
        exact carries_ext hI (hwf b' hb'') _

end Build

def nb : ℕ → ℕ
  | 0 => 0
  | m + 1 => nb ((m + 1) / 2) + 1
decreasing_by omega

lemma nb_succ (m : ℕ) : nb (m + 1) = nb ((m + 1) / 2) + 1 := by
  rw [nb]

lemma nb_le : ∀ r m : ℕ, m < 2 ^ r → nb m ≤ r
  | 0, m, h => by
    have : m = 0 := by simpa using h
    subst this; simp [nb]
  | r + 1, m, h => by
    rcases m with _ | m
    · simp [nb]
    · rw [nb_succ]
      have := nb_le r ((m + 1) / 2) (by rw [pow_succ] at h; omega)
      omega

section Inv
variable {X : Type*} {I : ℕ} {inp : X → List Bool}

lemma inv (hI : ∀ x, (inp x).length = I) (z : ℕ) :
    ∀ (m : ℕ) (gs : List Gate) (a : ℕ → ℕ) (ρ : X → ℕ), Ok I gs →
      Carries I inp gs z (fun _ => false) → (∀ x, ρ x ≤ m) →
      (∀ i < m, Carries I inp gs (a i) (fun x => decide (i < ρ x))) →
      ∃ hs, Ok I (gs ++ hs) ∧ nc hs ≤ nb m ∧ hs.length ≤ nc hs + 4 * m ∧
        ∃ b : ℕ → ℕ, ∀ i < m, Carries I inp (gs ++ hs) (b i) (fun x => decide (ρ x ≤ i)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro gs a ρ hok hz hρ ha
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact ⟨[], by simpa using hok, by simp [nc, notCount], by simp, a, fun i hi => absurd hi (by omega)⟩
  set h := m / 2 with hh
  have hhm : h < m := by omega

  obtain ⟨ok1, nc1, hc⟩ := addNot hI hok (ha h hhm)
  set gs1 := gs ++ [⟨GateOp.not, [a h]⟩] with hgs1
  set c := I + gs.length with hcdef
  have hc' : Carries I inp gs1 c (fun x => decide (ρ x ≤ h)) :=
    carries_congr hc (fun x => Bool.eq_iff_iff.mpr (by simp))

  set ρ' : X → ℕ := fun x => if ρ x ≤ h then ρ x else ρ x - h - 1 with hρ'
  obtain ⟨hs2, ok2, nc2, len2, d, hd⟩ := many hI 2 (fun i x => decide (i < ρ' x)) gs1 ok1
    (List.range h) (by
      intro hs0 hok0 i hi
      have hi' : i < h := List.mem_range.mp hi
      have hai : Carries I inp (gs1 ++ hs0) (a i) (fun x => decide (i < ρ x)) :=
        carries_ext hI (carries_ext hI (ha i (by omega)) _) _
      have hc0 : Carries I inp (gs1 ++ hs0) c (fun x => decide (ρ x ≤ h)) := carries_ext hI hc' _
      have hpad : Carries I inp (gs1 ++ hs0) (if h + 1 + i < m then a (h + 1 + i) else z)
          (fun x => decide (h + 1 + i < ρ x)) := by
        split_ifs with hlt
        · exact carries_ext hI (carries_ext hI (ha _ hlt) _) _
        · refine carries_congr (carries_ext hI (carries_ext hI hz _) _) (fun x => ?_)
          have := hρ x
          simp only [Bool.false_eq, decide_eq_false_iff_not, not_lt]
          omega
      obtain ⟨okA, ncA, hA⟩ := add2 hI (Or.inl rfl) hok0 hai hc0
      obtain ⟨okB, ncB, hB⟩ := add2 hI (Or.inr rfl) okA hA (carries_ext hI hpad _)
      refine ⟨[⟨GateOp.and, [a i, c]⟩] ++ [⟨GateOp.or, [I + (gs1 ++ hs0).length,
        if h + 1 + i < m then a (h + 1 + i) else z]⟩], ?_, ?_, by simp,
        I + (gs1 ++ hs0 ++ [(⟨GateOp.and, [a i, c]⟩ : Gate)]).length, ?_⟩
      · rw [← List.append_assoc]; exact okB
      · rw [nc_append, ncA, ncB]
      · rw [← List.append_assoc]
        refine carries_congr hB (fun x => ?_)
        have := hρ x
        by_cases hx : ρ x ≤ h
        · simp only [hρ', hx, ite_true]
          simp [GateOp.eval]
          omega
        · simp only [hρ', hx, ite_false]
          simp [GateOp.eval]
          omega)

  have hh2 : h < m := hhm
  obtain ⟨hs3, ok3, nc3, len3, nd, hnd⟩ := ih h hh2 (gs1 ++ hs2) d ρ' ok2
    (carries_ext hI (carries_ext hI hz _) _)
    (fun x => by
      have := hρ x
      simp only [hρ']
      split_ifs <;> omega)
    (fun i hi => hd i (List.mem_range.mpr hi))

  set gs3 := gs1 ++ hs2 ++ hs3 with hgs3
  obtain ⟨hs4, ok4, nc4, len4, b, hb⟩ := many hI 1 (fun i x => decide (ρ x ≤ i)) gs3 ok3
    (List.range m) (by
      intro hs0 hok0 i hi
      have hi' : i < m := List.mem_range.mp hi
      have hc0 : Carries I inp (gs3 ++ hs0) c (fun x => decide (ρ x ≤ h)) :=
        carries_ext hI (carries_ext hI (carries_ext hI hc' _) _) _
      rcases lt_trichotomy i h with hlt | heq | hgt
      · have hn : Carries I inp (gs3 ++ hs0) (nd i) (fun x => decide (ρ' x ≤ i)) :=
          carries_ext hI (hnd i hlt) _
        obtain ⟨okA, ncA, hA⟩ := add2 hI (Or.inl rfl) hok0 hc0 hn
        refine ⟨_, okA, ncA, by simp, _, carries_congr hA (fun x => ?_)⟩
        have := hρ x
        by_cases hx : ρ x ≤ h
        · simp only [hρ', hx, ite_true]; simp [GateOp.eval]
        · simp only [hρ', hx, ite_false]; simp [GateOp.eval]; omega
      · subst heq
        obtain ⟨okA, ncA, hA⟩ := add2 hI (Or.inl rfl) hok0 hc0 hc0
        exact ⟨_, okA, ncA, by simp, _, carries_congr hA (fun x => by simp [GateOp.eval])⟩
      · have hn : Carries I inp (gs3 ++ hs0) (nd (i - h - 1)) (fun x => decide (ρ' x ≤ i - h - 1)) :=
          carries_ext hI (hnd (i - h - 1) (by omega)) _
        obtain ⟨okA, ncA, hA⟩ := add2 hI (Or.inr rfl) hok0 hc0 hn
        refine ⟨_, okA, ncA, by simp, _, carries_congr hA (fun x => ?_)⟩
        have := hρ x
        by_cases hx : ρ x ≤ h
        · simp only [hρ', hx, ite_true]; simp [GateOp.eval]; omega
        · simp only [hρ', hx, ite_false]; simp [GateOp.eval]; omega)
  refine ⟨[⟨GateOp.not, [a h]⟩] ++ hs2 ++ hs3 ++ hs4, ?_, ?_, ?_, b, ?_⟩
  · have : gs ++ ([⟨GateOp.not, [a h]⟩] ++ hs2 ++ hs3 ++ hs4) = gs3 ++ hs4 := by
      simp [hgs3, hgs1]
    rw [this]; exact ok4
  · rw [nc_append, nc_append, nc_append, nc1, nc2, nc4]
    have : nb m = nb h + 1 := by
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [nb_succ]
    omega
  · simp only [List.length_append, List.length_singleton, List.length_range] at len2 len4 ⊢
    rw [nc_append, nc_append, nc_append, nc1, nc2, nc4]
    omega
  · intro i hi
    have : gs ++ ([⟨GateOp.not, [a h]⟩] ++ hs2 ++ hs3 ++ hs4) = gs3 ++ hs4 := by
      simp [hgs3, hgs1]
    rw [this]
    exact hb i (List.mem_range.mpr hi)

end Inv
lemma inp_getD (n : ℕ) (P : Fin n → Bool) (w : ℕ) :
    (List.ofFn P ++ [false, true]).getD w false =
      if h : w < n then P ⟨w, h⟩ else decide (w = n + 1) := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_append_left (by simpa using h)]
    simp [h]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn]
    rcases Nat.lt_or_ge w (n + 2) with h2 | h2
    · by_cases h3 : w = n + 1
      · subst h3; simp
      · have : w = n := by omega
        subst this; simp
    · rw [List.getElem?_eq_none (by simp; omega)]
      simp; omega
lemma nb_le_self (m : Nat) : nb m ≤ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    cases m with
    | zero => simp [nb]
    | succ k =>
      rw [nb_succ]
      have h := ih ((k + 1) / 2) (by omega)
      omega

def cof {n : Nat} (o : Option (Fin n)) (x : Finset (Fin n)) : Finset (Fin n) :=
  o.elim x (fun j => insert j x)

lemma cof_subset {n : Nat} (o : Option (Fin n)) (Y x : Finset (Fin n)) :
    Y ⊆ cof o x ↔ ∀ i ∈ Y, o ≠ some i → i ∈ x := by
  cases o with
  | none => simp [cof, Finset.subset_iff]
  | some j =>
    constructor
    · intro h i hi hji
      have hx : i ∈ insert j x := h hi
      rcases Finset.mem_insert.mp hx with e | hx
      · subst i; exact (hji rfl).elim
      · exact hx
    · intro h i hi
      change i ∈ insert j x
      by_cases e : i = j
      · exact Finset.mem_insert.mpr (Or.inl e)
      · exact Finset.mem_insert.mpr (Or.inr (h i hi (by simpa [eq_comm] using e)))

lemma sparseCompile {n m b s : Nat} (S : Finset (Finset (Fin n)))
    (H : Finset (Fin n) → Nat) (hS : S.card ≤ s) (hm : m ≤ n) (hmb : m < 2^b)
    (hH : ∀ x, H x = (S.filter (fun Y => Y ⊆ x)).sup H)
    (hbound : ∀ x, H x ≤ m) :
    ∃ (C : Circuit) (a : Fin n → Fin (n+2+C.size)),
      valid n b C ∧ C.size ≤ 64*(n+1)^2*(s+1) ∧
      ∀ x j, val C a x j = decide (H x < H (insert j x)) := by
  classical
  have hI : ∀ x : Finset (Fin n), (inp x).length = n+2 := inp_length
  have hz : ∀ gs, Carries (n+2) inp gs n (fun _ => false) := fun gs =>
    carries_congr (carries_input hI gs (by omega)) (fun x => by simp [inp, inp_getD])
  have ht : ∀ gs, Carries (n+2) inp gs (n+1) (fun _ => true) := fun gs =>
    carries_congr (carries_input hI gs (by omega)) (fun x => by
      rw [inp, inp_getD, dif_neg (by omega), decide_eq_true_eq])
  have hx : ∀ gs (i : Fin n), Carries (n+2) inp gs i.val (fun x => decide (i ∈ x)) := fun gs i =>
    carries_congr (carries_input hI gs (by omega)) (fun x => by
      rw [inp, inp_getD, dif_pos i.isLt]
      exact decide_eq_decide.mpr Iff.rfl)
  let W : List (Option (Fin n)) := none :: (List.finRange n).map some
  have hW : W.length = n+1 := by simp [W, Nat.add_comm]
  have hWs : ∀ j : Fin n, some j ∈ W := fun j => by
    simp [W, List.mem_finRange]
  have hWn : none ∈ W := List.mem_cons_self ..
  obtain ⟨G1, ok1, nc1, len1, sw, hsw⟩ := many hI n
    (fun (p : Option (Fin n) × Finset (Fin n)) x => decide (p.2 ⊆ cof p.1 x))
    [] (ok_nil _) (W.product S.toList) (by
      intro G hok p _
      obtain ⟨U, ok, hn, hl, w, hw⟩ := chain hI GateOp.and (Or.inl rfl) (fun i : Fin n => i.val)
        (fun i x => decide (i ∈ x)) (p.2.filter (fun i => p.1 ≠ some i)).toList
        ([] ++ G) (n+1) (fun _ => true) hok (ht _) (fun i _ => hx _ i)
      refine ⟨U, ok, hn, ?_, w, carries_congr hw (fun x => ?_)⟩
      · rw [hl, Finset.length_toList]
        exact (Finset.card_le_univ _).trans (by simp)
      · apply Bool.eq_iff_iff.mpr
        simp only [foldl_and, Bool.true_and, List.all_eq_true, Finset.mem_toList,
          Finset.mem_filter, decide_eq_true_eq, cof_subset]
        exact ⟨fun h i hi hne => h i ⟨hi, hne⟩, fun h i hi => h i hi.1 hi.2⟩)
  simp only [List.nil_append] at ok1 hsw
  obtain ⟨G2, ok2, nc2, len2, U, hU⟩ := many hI S.card
    (fun (p : Option (Fin n) × Nat) x => decide (p.2 < H (cof p.1 x))) G1 ok1
    (W.product (List.range m)) (by
      intro G hok p hp
      have ho := (List.mem_product.mp hp).1
      obtain ⟨G', ok', hn, hl, w, hw⟩ := chain hI GateOp.or (Or.inr rfl)
        (fun Y => sw (p.1, Y)) (fun Y x => decide (Y ⊆ cof p.1 x))
        (S.filter (fun Y => p.2 < H Y)).toList (G1 ++ G) n (fun _ => false) hok (hz _)
        (fun Y hY => carries_ext hI
          (hsw (p.1,Y) (List.mem_product.mpr ⟨ho, Finset.mem_toList.mpr
            (Finset.mem_filter.mp (Finset.mem_toList.mp hY)).1⟩)) _)
      refine ⟨G', ok', hn, ?_, w, carries_congr hw (fun x => ?_)⟩
      · rw [hl, Finset.length_toList]
        exact Finset.card_filter_le _ _
      · apply Bool.eq_iff_iff.mpr
        simp only [foldl_or, Bool.false_or, List.any_eq_true, Finset.mem_toList,
          Finset.mem_filter, decide_eq_true_eq]
        rw [hH (cof p.1 x), Finset.lt_sup_iff]
        simp only [Finset.mem_filter]
        exact ⟨fun ⟨Y, ⟨hY, hk⟩, hsub⟩ => ⟨Y, ⟨hY, hsub⟩, hk⟩,
          fun ⟨Y, ⟨hY, hsub⟩, hk⟩ => ⟨Y, ⟨hY, hk⟩, hsub⟩⟩)
  have hUa (o : Option (Fin n)) (ho : o ∈ W) (k : Nat) (hk : k < m) :
      Carries (n+2) inp (G1 ++ G2) (U (o,k)) (fun x => decide (k < H (cof o x))) :=
    hU (o,k) (List.mem_product.mpr ⟨ho, List.mem_range.mpr hk⟩)
  obtain ⟨G3, ok3, nc3, len3, N, hN⟩ := inv hI n m (G1 ++ G2) (fun k => U (none,k)) H ok2
    (hz _) hbound (fun k hk => hUa none hWn k hk)
  let G := G1 ++ G2 ++ G3
  obtain ⟨G4, ok4, nc4, len4, out, hout⟩ := many hI (2*m)
    (fun (j : Fin n) x => decide (H x < H (insert j x))) G ok3 (List.finRange n) (by
      intro P hok j _
      obtain ⟨A, okA, ncA, lenA, a, ha⟩ := many hI 1
        (fun k x => decide (H x ≤ k ∧ k < H (insert j x))) (G ++ P) hok (List.range m) (by
          intro B hokB k hk
          have hkm : k < m := List.mem_range.mp hk
          have hn := carries_ext hI (carries_ext hI (hN k hkm) P) B
          have hp := carries_ext hI (carries_ext hI (carries_ext hI
            (hUa (some j) (hWs j) k hkm) G3) P) B
          obtain ⟨ok, hn0, hw⟩ := add2 hI (Or.inl rfl) hokB hn hp
          exact ⟨_, ok, hn0, by simp, _, carries_congr hw (fun x => by
            apply Bool.eq_iff_iff.mpr
            simp only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true,
              Bool.and_eq_true, decide_eq_true_eq] <;> rfl)⟩)
      obtain ⟨O, okO, ncO, lenO, w, hw⟩ := chain hI GateOp.or (Or.inr rfl) a
        (fun k x => decide (H x ≤ k ∧ k < H (insert j x))) (List.range m)
        (G ++ P ++ A) n (fun _ => false) okA (hz _) ha
      refine ⟨A ++ O, by simpa only [List.append_assoc] using okO,
        by rw [nc_append, ncA, ncO], ?_, w, ?_⟩
      · simp only [List.length_range, one_mul] at lenA
        simp only [List.length_range] at lenO
        simp only [List.length_append]
        omega
      · rw [← List.append_assoc]
        refine carries_congr hw (fun x => ?_)
        apply Bool.eq_iff_iff.mpr
        simp only [foldl_or, Bool.false_or, List.any_eq_true, List.mem_range, decide_eq_true_eq]
        constructor
        · rintro ⟨k, _, h1, h2⟩; omega
        · intro h
          exact ⟨H x, lt_of_lt_of_le h (hbound _), le_rfl, h⟩)
  let C : Circuit := ⟨G ++ G4, 0⟩
  let a : Fin n → Fin (n+2+C.size) := fun j =>
    ⟨out j, (hout j (List.mem_finRange j)).1⟩
  refine ⟨C, a, ⟨ok4.1, ok4.2, by change 0 < n+2+(G ++ G4).length; omega, ?_⟩, ?_, ?_⟩
  · change nc (G1 ++ G2 ++ G3 ++ G4) ≤ b
    simp only [nc_append, nc1, nc2, nc4, zero_add, add_zero]
    exact nc3.trans (nb_le b m hmb)
  · change (G1 ++ G2 ++ G3 ++ G4).length ≤ _
    simp only [List.length_append]
    let B := (n+1)^2*(s+1)
    have hA : n * (n+1) ≤ (n+1)^2 := by rw [pow_two]; gcongr; omega
    have hN2 : n ≤ (n+1)^2 := by
      rw [pow_two]
      exact (show n ≤ n+1 by omega).trans (Nat.le_mul_of_pos_right _ (by omega))
    have hNB : n ≤ B := by
      change n ≤ (n+1)^2*(s+1)
      exact hN2.trans (Nat.le_mul_of_pos_right _ (by omega))
    have h1 : G1.length ≤ B := by
      have lp : (W.product S.toList).length = W.length * S.toList.length :=
        List.length_product W _
      rw [lp, hW, Finset.length_toList] at len1
      calc
        G1.length ≤ n * ((n+1) * S.card) := len1
        _ = (n * (n+1)) * S.card := by ring
        _ ≤ B := Nat.mul_le_mul hA (by omega)
    have h2 : G2.length ≤ B := by
      have lp : (W.product (List.range m)).length = W.length * (List.range m).length :=
        List.length_product W _
      rw [lp, hW, List.length_range] at len2
      calc
        G2.length ≤ S.card * ((n+1) * m) := len2
        _ = (m * (n+1)) * S.card := by ring
        _ ≤ B := Nat.mul_le_mul ((Nat.mul_le_mul_right (n+1) hm).trans hA) (by omega)
    have h3 : G3.length ≤ 5*B := by
      have hnc := nc3.trans (nb_le_self m)
      have h := hm.trans hNB
      omega
    have h4 : G4.length ≤ 2*B := by
      simp only [List.length_finRange] at len4
      calc
        G4.length ≤ (2*m)*n := len4
        _ = 2*(m*n) := by ring
        _ ≤ 2*B := by
          apply Nat.mul_le_mul_left
          exact ((Nat.mul_le_mul hm (show n ≤ n+1 by omega)).trans hA).trans
            (Nat.le_mul_of_pos_right _ (by omega))
    rw [Nat.mul_assoc]
    change _ ≤ 64*B
    omega
  · intro x j
    exact (hout j (List.mem_finRange j)).2 x
noncomputable def pre {n : Nat} (π : Equiv.Perm (Fin n)) (k : Fin n) : Finset (Fin n) :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < k.val)).image (fun i => π i)

noncomputable def support {n : Nat} (q : Finset (Fin n) → Fin n → Nat) : Nat :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  (Finset.univ : Finset (Finset (Fin n))).sum (fun x =>
    ((Finset.univ : Finset (Fin n)).filter (fun j => j ∉ x ∧ 0 < q x j)).card)

private theorem heightLength {n : Nat} {l : List (Fin n)} (h : l.Nodup) : l.length ≤ n := by
  rw [← List.toFinset_card_of_nodup h]
  exact card_finset_fin_le _

private noncomputable def heightPaths {n : Nat} (x : Finset (Fin n)) : Finset (List (Fin n)) := by
  classical
  exact ((Finset.univ : Finset (Σ k : Fin (n + 1), Fin k.val → Fin n)).image
    (fun a => List.ofFn a.2)).filter (fun l => l.Nodup ∧ l.toFinset = x)

private theorem heightMemPaths {n : Nat} {x : Finset (Fin n)} {l : List (Fin n)} :
    l ∈ heightPaths x ↔ l.Nodup ∧ l.toFinset = x := by
  classical
  simp only [heightPaths, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  exact ⟨⟨⟨l.length, Nat.lt_succ_of_le (heightLength h.1)⟩, l.get⟩, List.ofFn_get l⟩

private def heightFrom {n : Nat} (w : Finset (Fin n) → Fin n → Nat)
    (x : Finset (Fin n)) : List (Fin n) → Nat
  | [] => 0
  | j :: l => w x j + heightFrom w (insert j x) l

private def heightWeight {n : Nat} (w : Finset (Fin n) → Fin n → Nat) (l : List (Fin n)) : Nat :=
  heightFrom w ∅ l

private theorem heightFromAppend {n : Nat} (w : Finset (Fin n) → Fin n → Nat)
    (x : Finset (Fin n)) (l r : List (Fin n)) :
    heightFrom w x (l ++ r) = heightFrom w x l + heightFrom w (x ∪ l.toFinset) r := by
  classical
  induction l generalizing x with
  | nil => simp [heightFrom]
  | cons j l ih =>
    have h : insert j x ∪ l.toFinset = x ∪ insert j l.toFinset := by
      ext k
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto
    simp only [List.cons_append, heightFrom, ih, List.toFinset_cons, h, Nat.add_assoc]

private theorem heightWeightSnoc {n : Nat} (w : Finset (Fin n) → Fin n → Nat)
    (l : List (Fin n)) (j : Fin n) :
    heightWeight w (l ++ [j]) = heightWeight w l + w l.toFinset j := by
  simp [heightWeight, heightFromAppend, heightFrom]

private theorem heightSnocFinset {n : Nat} (l : List (Fin n)) (j : Fin n) :
    (l ++ [j]).toFinset = insert j l.toFinset := by
  ext k
  simp [List.mem_append, or_comm]

private theorem heightExtend {n : Nat} {l : List (Fin n)} {x : Finset (Fin n)}
    (hl : l.Nodup) (hx : l.toFinset ⊆ x) :
    ∃ r, (l ++ r).Nodup ∧ (l ++ r).toFinset = x := by
  classical
  let s := x \ l.toFinset
  refine ⟨s.toList, hl.append s.nodup_toList ?_, ?_⟩
  · intro j hj hm
    have hs := Finset.mem_sdiff.mp (Finset.mem_toList.mp hm)
    exact hs.2 (List.mem_toFinset.mpr hj)
  · rw [List.toFinset_append, Finset.toList_toFinset]
    exact Finset.union_sdiff_of_subset hx

private noncomputable def heightBest {n : Nat} (w : Finset (Fin n) → Fin n → Nat)
    (x : Finset (Fin n)) : Nat := (heightPaths x).sup (heightWeight w)

private theorem heightWeightLeBest {n : Nat} (w : Finset (Fin n) → Fin n → Nat)
    {x : Finset (Fin n)} {l : List (Fin n)} (hl : l.Nodup) (hx : l.toFinset = x) :
    heightWeight w l ≤ heightBest w x :=
  Finset.le_sup (heightMemPaths.mpr ⟨hl, hx⟩)

private theorem heightBestWitness {n : Nat} (w : Finset (Fin n) → Fin n → Nat)
    (x : Finset (Fin n)) : ∃ l, l.Nodup ∧ l.toFinset = x ∧ heightBest w x = heightWeight w l := by
  classical
  have hx : (heightPaths x).Nonempty :=
    ⟨x.toList, heightMemPaths.mpr ⟨x.nodup_toList, Finset.toList_toFinset x⟩⟩
  obtain ⟨l, hl, he⟩ := Finset.exists_mem_eq_sup _ hx (heightWeight w)
  exact ⟨l, (heightMemPaths.mp hl).1, (heightMemPaths.mp hl).2, he⟩

private theorem heightBestMono {n : Nat} (w : Finset (Fin n) → Fin n → Nat)
    {x y : Finset (Fin n)} (h : x ⊆ y) : heightBest w x ≤ heightBest w y := by
  obtain ⟨l, hl, hxl, he⟩ := heightBestWitness w x
  have hsub : l.toFinset ⊆ y := hxl.symm ▸ h
  obtain ⟨r, hr, hyr⟩ := heightExtend hl hsub
  calc
    heightBest w x = heightWeight w l := he
    _ ≤ heightWeight w (l ++ r) := by
      simp only [heightWeight, heightFromAppend]
      omega
    _ ≤ heightBest w y := heightWeightLeBest w hr hyr

private theorem heightBestStep {n : Nat} (w : Finset (Fin n) → Fin n → Nat)
    {x : Finset (Fin n)} {j : Fin n} (hj : j ∉ x) :
    heightBest w x + w x j ≤ heightBest w (insert j x) := by
  classical
  obtain ⟨l, hl, hxl, he⟩ := heightBestWitness w x
  have hd : (l ++ [j]).Nodup := hl.append (by simp) (by
    intro k hk hm
    have hkj : k = j := by simpa using hm
    subst k
    exact hj (by rw [← hxl]; exact List.mem_toFinset.mpr hk))
  have hs : (l ++ [j]).toFinset = insert j x := (heightSnocFinset l j).trans (by rw [hxl])
  calc
    heightBest w x + w x j = heightWeight w (l ++ [j]) := by rw [heightWeightSnoc, he, hxl]
    _ ≤ heightBest w (insert j x) := heightWeightLeBest w hd hs

private theorem heightFromIndices {n : Nat} (w : Finset (Fin n) → Fin n → Nat)
    (x : Finset (Fin n)) (l : List (Fin n)) :
    heightFrom w x l = Finset.univ.sum (fun k : Fin l.length =>
      w (x ∪ (l.take k.val).toFinset) (l.get k)) := by
  classical
  induction l generalizing x with
  | nil => simp [heightFrom]
  | cons j l ih =>
    simp only [heightFrom, List.length_cons, Fin.sum_univ_succ, Fin.val_zero, List.take_zero,
      List.toFinset_nil, Finset.union_empty, List.get_cons_zero, ih]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    simp only [Fin.val_succ, List.take_succ_cons, List.toFinset_cons, List.get_cons_succ']
    congr 1
    ext a
    simp only [Finset.mem_union, Finset.mem_insert]
    tauto

private theorem heightPreTake {n : Nat} (π : Equiv.Perm (Fin n)) (k : Fin n) :
    pre π k = ((List.ofFn (fun i => π i)).take k.val).toFinset := by
  classical
  ext a
  simp only [pre, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    List.mem_toFinset, List.mem_take_iff_getElem, List.length_ofFn, List.getElem_ofFn]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.val, lt_min hi i.isLt, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, (lt_min_iff.mp hi).2⟩, (lt_min_iff.mp hi).1, rfl⟩

private theorem heightSumCast {m n : Nat} (e : m = n) (f : Fin m → Nat) :
    Finset.univ.sum f = Finset.univ.sum (fun i : Fin n => f (Fin.cast e.symm i)) := by
  subst n
  simp

private theorem heightPermutationWeight {n : Nat} (q : Finset (Fin n) → Fin n → Nat)
    (π : Equiv.Perm (Fin n)) :
    heightWeight q (List.ofFn (fun i => π i)) = Finset.univ.sum (fun k => q (pre π k) (π k)) := by
  rw [heightWeight, heightFromIndices, heightSumCast List.length_ofFn]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Fin.val_cast, Finset.empty_union, ← heightPreTake, List.get_ofFn,
    Fin.cast_cast, Fin.cast_refl, id_eq]

private theorem heightBestBound {n D : Nat} (q : Finset (Fin n) → Fin n → Nat)
    (hp : ∀ π : Equiv.Perm (Fin n), Finset.univ.sum (fun k => q (pre π k) (π k)) ≤ D)
    (x : Finset (Fin n)) : heightBest q x ≤ D := by
  classical
  obtain ⟨l, hl, _, he⟩ := heightBestWitness q x
  obtain ⟨r, hr, hfull⟩ := heightExtend hl (Finset.subset_univ l.toFinset)
  have hlen : (l ++ r).length = n := by
    rw [← List.toFinset_card_of_nodup hr, hfull, Finset.card_fin]
  have hmem : ∀ j : Fin n, j ∈ l ++ r := fun j => List.mem_toFinset.mp (by
    rw [hfull]
    exact Finset.mem_univ j)
  let π : Equiv.Perm (Fin n) := (finCongr hlen.symm).trans
    (List.Nodup.getEquivOfForallMemList (l ++ r) hr hmem)
  have hπ : List.ofFn (fun i => π i) = l ++ r := calc
    List.ofFn (fun i => π i) = List.ofFn (l ++ r).get := (List.ofFn_congr hlen _).symm
    _ = l ++ r := List.ofFn_get _
  have hm : heightWeight q l ≤ heightWeight q (l ++ r) := by
    simp only [heightWeight, heightFromAppend]
    omega
  rw [he]
  refine hm.trans ?_
  rw [← hπ, heightPermutationWeight]
  exact hp π

private noncomputable def heightEdges {n : Nat} (q : Finset (Fin n) → Fin n → Nat) :
    Finset (Σ x : Finset (Fin n), Fin n) :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  (Finset.univ : Finset (Finset (Fin n))).sigma (fun x =>
    (Finset.univ : Finset (Fin n)).filter (fun j => j ∉ x ∧ 0 < q x j))

private noncomputable def heightEndpoints {n : Nat} (q : Finset (Fin n) → Fin n → Nat) :
    Finset (Finset (Fin n)) :=
  (heightEdges q).image (fun a => insert a.2 a.1)

private theorem heightEndpointsCard {n : Nat} (q : Finset (Fin n) → Fin n → Nat) :
    (heightEndpoints q).card ≤ support q := by
  unfold heightEndpoints heightEdges support
  exact Finset.card_image_le.trans_eq (Finset.card_sigma _ _)

private theorem heightMemEndpoints {n : Nat} {q : Finset (Fin n) → Fin n → Nat}
    {x : Finset (Fin n)} {j : Fin n} (hj : j ∉ x) (hq : 0 < q x j) :
    insert j x ∈ heightEndpoints q := by
  unfold heightEndpoints
  refine Finset.mem_image.mpr ⟨⟨x, j⟩, ?_, rfl⟩
  simp only [heightEdges, Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hj, hq⟩

-- Slot t counts times congruent to t strictly before the current time.
private def heightRank {T : Nat} (t : Fin T) (s : Nat) : Nat := (s + (T - (t.val + 1))) / T

private theorem heightRankStrict {T a r s : Nat} (t : Fin T) (ha : a % T = t.val)
    (hr : r ≤ a) (hs : a < s) : heightRank t r < heightRank t s := by
  have hT : 0 < T := Nat.zero_lt_of_lt t.isLt
  have ht := t.isLt
  have ha' := Nat.mod_add_div' a T
  rw [ha] at ha'
  have hcut : (a / T + 1) * T = a + (T - (t.val + 1)) + 1 := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have h₁ : heightRank t r < a / T + 1 := (Nat.div_lt_iff_lt_mul hT).mpr (by
    rw [hcut]
    omega)
  have h₂ : a / T + 1 ≤ heightRank t s := (Nat.le_div_iff_mul_le hT).mpr (by
    rw [hcut]
    omega)
  exact h₁.trans_le h₂

private theorem heightRankBound {T d s : Nat} (t : Fin T) (hs : s ≤ T * d) :
    heightRank t s ≤ d := by
  have hT : 0 < T := Nat.zero_lt_of_lt t.isLt
  have ht := t.isLt
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hT).mpr
  rw [Nat.succ_mul, Nat.mul_comm d T]
  omega

private noncomputable def heightSelect {n T : Nat} (q : Finset (Fin n) → Fin n → Nat)
    (t : Fin T) (x : Finset (Fin n)) (j : Fin n) : Nat := by
  classical
  exact if ∃ a : Nat, heightBest q x ≤ a ∧ a < heightBest q x + q x j ∧ a % T = t.val then 1 else 0

private theorem heightSelectedStep {n T : Nat} (q : Finset (Fin n) → Fin n → Nat)
    (t : Fin T) {x : Finset (Fin n)} {j : Fin n} (hj : j ∉ x) :
    heightRank t (heightBest q x) + heightSelect q t x j ≤
      heightRank t (heightBest q (insert j x)) := by
  classical
  unfold heightSelect
  split
  · rename_i h
    obtain ⟨a, ha, hb, hmod⟩ := h
    exact heightRankStrict t hmod ha (hb.trans_le (heightBestStep q hj))
  · rw [Nat.add_zero]
    exact Nat.div_le_div_right (Nat.add_le_add_right
      (heightBestMono q (Finset.subset_insert j x)) (T - (t.val + 1)))

private theorem heightSelectLeOne {n T : Nat} (q : Finset (Fin n) → Fin n → Nat)
    (t : Fin T) (x : Finset (Fin n)) (j : Fin n) : heightSelect q t x j ≤ 1 := by
  unfold heightSelect
  split <;> omega

private theorem heightSelectPositive {n T : Nat} {q : Finset (Fin n) → Fin n → Nat}
    {t : Fin T} {x : Finset (Fin n)} {j : Fin n} (h : 0 < heightSelect q t x j) : 0 < q x j := by
  unfold heightSelect at h
  split at h
  · rename_i hex
    obtain ⟨a, ha, hb, _⟩ := hex
    omega
  · omega

private theorem heightSelectPath {n T : Nat} (q : Finset (Fin n) → Fin n → Nat)
    (t : Fin T) (l : List (Fin n)) (hl : l.Nodup) :
    heightWeight (heightSelect q t) l ≤ l.length ∧
    heightWeight (heightSelect q t) l ≤ heightRank t (heightBest q l.toFinset) := by
  classical
  induction l using List.reverseRecOn with
  | nil => simp [heightWeight, heightFrom]
  | append_singleton l j ih =>
    obtain ⟨h₁, h₂⟩ := ih hl.of_append_left
    have hj : j ∉ l.toFinset := fun hm => hl.disjoint (List.mem_toFinset.mp hm) (by simp)
    rw [heightWeightSnoc, heightSnocFinset, List.length_append, List.length_singleton]
    exact ⟨Nat.add_le_add h₁ (heightSelectLeOne q t _ _),
      (Nat.add_le_add_right h₂ _).trans (heightSelectedStep q t hj)⟩

private theorem heightCompress {n T : Nat} (q : Finset (Fin n) → Fin n → Nat)
    (t : Fin T) (x : Finset (Fin n)) :
    heightBest (heightSelect q t) x =
      ((heightEndpoints q).filter (fun y => y ⊆ x)).sup (heightBest (heightSelect q t)) := by
  classical
  let F := ((heightEndpoints q).filter (fun y => y ⊆ x)).sup (heightBest (heightSelect q t))
  change heightBest (heightSelect q t) x = F
  apply le_antisymm
  · have aux (l : List (Fin n)) (hl : l.Nodup) (hx : l.toFinset ⊆ x) :
        heightWeight (heightSelect q t) l ≤ F := by
      induction l using List.reverseRecOn with
      | nil => simp [heightWeight, heightFrom]
      | append_singleton l j ih =>
        have hj : j ∉ l.toFinset := fun hm => hl.disjoint (List.mem_toFinset.mp hm) (by simp)
        by_cases hp : 0 < heightSelect q t l.toFinset j
        · have hy : (l ++ [j]).toFinset ∈ heightEndpoints q := by
            rw [heightSnocFinset]
            exact heightMemEndpoints hj (heightSelectPositive hp)
          exact (heightWeightLeBest (heightSelect q t) hl rfl).trans
            (Finset.le_sup (Finset.mem_filter.mpr ⟨hy, hx⟩))
        · rw [heightWeightSnoc, Nat.eq_zero_of_not_pos hp, Nat.add_zero]
          apply ih hl.of_append_left
          rw [heightSnocFinset] at hx
          exact (Finset.subset_insert _ _).trans hx
    apply Finset.sup_le
    intro l hl
    obtain ⟨hn, he⟩ := heightMemPaths.mp hl
    exact aux l hn (by rw [he])
  · apply Finset.sup_le
    intro y hy
    exact heightBestMono _ (Finset.mem_filter.mp hy).2

lemma sparseHeight {n T b : Nat} (q : Finset (Fin n) → Fin n → Nat)
    (hlocal : ∀ x j, j ∉ x → q x j ≤ T)
    (hpath : ∀ π : Equiv.Perm (Fin n), Finset.univ.sum (fun k => q (pre π k) (π k)) ≤ T*(2^b-1)) :
    ∃ (S : Finset (Finset (Fin n))) (H : Fin T → Finset (Fin n) → Nat),
      S.card ≤ support q ∧ (∀ t x, H t x ≤ min n (2^b-1)) ∧
      (∀ t x, H t x = (S.filter (fun y => y ⊆ x)).sup (H t)) ∧
      ∀ x j, j ∉ x → q x j ≤ ((Finset.univ : Finset (Fin T)).filter
        (fun t => H t x < H t (insert j x))).card := by
  classical
  let H : Fin T → Finset (Fin n) → Nat := fun t => heightBest (heightSelect q t)
  refine ⟨heightEndpoints q, H, heightEndpointsCard q, ?_, heightCompress q, ?_⟩
  · intro t x
    obtain ⟨l, hl, he, hh⟩ := heightBestWitness (heightSelect q t) x
    obtain ⟨hn, hr⟩ := heightSelectPath q t l hl
    rw [he] at hr
    exact hh.trans_le (le_min (hn.trans (heightLength hl))
      (hr.trans (heightRankBound t (heightBestBound q hpath x))))
  · intro x j hj
    have hq := hlocal x j hj
    let f : Fin (q x j) → Fin T := fun i =>
      ⟨(heightBest q x + i.val) % T, Nat.mod_lt _ ((Nat.zero_lt_of_lt i.isLt).trans_le hq)⟩
    have hf : Function.Injective f := by
      intro i k hik
      have hmod : Nat.ModEq T (heightBest q x + i.val) (heightBest q x + k.val) :=
        congrArg Fin.val hik
      have he : i.val % T = k.val % T := Nat.ModEq.add_left_cancel' (heightBest q x) hmod
      rw [Nat.mod_eq_of_lt (i.isLt.trans_le hq), Nat.mod_eq_of_lt (k.isLt.trans_le hq)] at he
      exact Fin.ext he
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin (q x j))))
        (t := (Finset.univ : Finset (Fin T)).filter (fun t => H t x < H t (insert j x))) f
        (by
          intro i _
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have hsel : heightSelect q (f i) x j = 1 := by
            unfold heightSelect
            exact if_pos ⟨heightBest q x + i.val, Nat.le_add_right _ _,
              Nat.add_lt_add_left i.isLt _, rfl⟩
          have hstep := heightBestStep (heightSelect q (f i)) hj
          rw [hsel] at hstep
          exact Nat.lt_of_succ_le hstep)
        hf.injOn)
/- Markov drop-count helpers and input lookup ported from
   232d467ea394f7d4d61352a1740c7df677fb40fc, lean/PEqualNP/Outside/L_lib_1262.lean.
   The permutation chain and sum over quotas adapt the bound to coordinate taps. -/
namespace NecessaryDrops

lemma gateOp_eval_mono {op : GateOp} (hop : op = GateOp.and ∨ op = GateOp.or)
    {l₁ l₂ : List Bool} (hlen : l₁.length = l₂.length)
    (hle : ∀ i (hi : i < l₁.length), l₁[i] = true → l₂[i]'(hlen ▸ hi) = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h1 b hb
    rcases List.mem_iff_getElem.mp hb with ⟨i, hi, rfl⟩
    have hi1 : i < l₁.length := hlen ▸ hi
    exact hle i hi1 (h1 l₁[i] (List.getElem_mem hi1))
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    rcases List.mem_iff_getElem.mp hb with ⟨i, hi, heq⟩
    exact ⟨l₂[i]'(hlen ▸ hi), List.getElem_mem _, hle i hi heq⟩

lemma exists_rise_between {L : ℕ} (v : Fin (L + 1) → Bool)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ L)
    (ha0 : v ⟨a, by omega⟩ = false) (hb1 : v ⟨b, by omega⟩ = true) :
    ∃ s : Fin L, a ≤ s.val ∧ s.val < b ∧ v s.castSucc = false ∧ v s.succ = true := by
  induction b with
  | zero =>
    have ha' : a = 0 := by omega
    subst ha'
    rw [ha0] at hb1
    exact Bool.noConfusion hb1
  | succ b' ih =>
    by_cases heq : a = b' + 1
    · subst heq
      rw [ha0] at hb1
      exact Bool.noConfusion hb1
    · have hab' : a ≤ b' := by omega
      cases hvb' : v ⟨b', by omega⟩
      · refine ⟨⟨b', by omega⟩, hab', by dsimp; omega, hvb', hb1⟩
      · rcases ih hab' (by omega) ha0 hvb' with ⟨s, hs1, hs2, hs3, hs4⟩
        exact ⟨s, hs1, by omega, hs3, hs4⟩

lemma card_le_of_between {L : ℕ} (A D : Finset (Fin L))
    (hbet : ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁.val < a₂.val → ∃ d ∈ D, a₁.val < d.val ∧ d.val < a₂.val) :
    A.card ≤ D.card + 1 := by
  by_cases hA : A.Nonempty
  · set m := A.max' hA
    have hm : m ∈ A := Finset.max'_mem A hA
    set A' := A.erase m
    have hcardA : A'.card + 1 = A.card := Finset.card_erase_add_one hm
    have hex : ∀ a ∈ A', ∃ d ∈ D, a.val < d.val ∧ d.val < m.val := by
      intro a ha
      have hne : a ≠ m := (Finset.mem_erase.mp ha).1
      have haA : a ∈ A := Finset.mem_of_mem_erase ha
      have hle : a ≤ m := Finset.le_max' A a haA
      have hlt : a.val < m.val := lt_of_le_of_ne hle (fun h => hne (Fin.ext h))
      exact hbet a haA m hm hlt
    let f : Fin L → Fin L := fun a =>
      if h : (D.filter (fun d => a.val < d.val)).Nonempty then
        (D.filter (fun d => a.val < d.val)).min' h
      else a
    have hf_mem : ∀ a ∈ A', f a ∈ D := by
      intro a ha
      rcases hex a ha with ⟨d, hd, hlt, _⟩
      have hne : (D.filter (fun d => a.val < d.val)).Nonempty :=
        ⟨d, Finset.mem_filter.mpr ⟨hd, hlt⟩⟩
      simp only [f, hne, ↓reduceDIte]
      exact (Finset.mem_filter.mp (Finset.min'_mem _ hne)).1
    have hf_lt : ∀ a₁ ∈ A', ∀ a₂ ∈ A', a₁.val < a₂.val → (f a₁).val < (f a₂).val := by
      intro a₁ ha₁ a₂ ha₂ hlt
      rcases hbet a₁ (Finset.mem_of_mem_erase ha₁) a₂ (Finset.mem_of_mem_erase ha₂) hlt with
        ⟨d, hd, hd1, hd2⟩
      have hne1 : (D.filter (fun x => a₁.val < x.val)).Nonempty :=
        ⟨d, Finset.mem_filter.mpr ⟨hd, hd1⟩⟩
      rcases hex a₂ ha₂ with ⟨d₂, hd₂, hd₂1, _⟩
      have hne2 : (D.filter (fun x => a₂.val < x.val)).Nonempty :=
        ⟨d₂, Finset.mem_filter.mpr ⟨hd₂, hd₂1⟩⟩
      have h1 : (f a₁).val ≤ d.val := by
        simp only [f, hne1, ↓reduceDIte]
        exact Finset.min'_le _ d (Finset.mem_filter.mpr ⟨hd, hd1⟩)
      have h2 : a₂.val < (f a₂).val := by
        simp only [f, hne2, ↓reduceDIte]
        exact (Finset.mem_filter.mp (Finset.min'_mem _ hne2)).2
      omega
    have hf_inj : Set.InjOn f (A' : Set (Fin L)) := by
      intro a₁ ha₁ a₂ ha₂ hfeq
      by_contra hne
      have ha₁' : a₁ ∈ A' := Finset.mem_coe.mp ha₁
      have ha₂' : a₂ ∈ A' := Finset.mem_coe.mp ha₂
      have hne_val : a₁.val ≠ a₂.val := fun h => hne (Fin.ext h)
      rcases lt_or_gt_of_ne hne_val with hlt | hlt
      · have := hf_lt a₁ ha₁' a₂ ha₂' hlt; rw [hfeq] at this; omega
      · have := hf_lt a₂ ha₂' a₁ ha₁' hlt; rw [hfeq] at this; omega
    have hle : A'.card ≤ D.card := by
      calc A'.card = (A'.image f).card := (Finset.card_image_of_injOn hf_inj).symm
        _ ≤ D.card := Finset.card_le_card (Finset.image_subset_iff.mpr hf_mem)
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hA]
    simp

def drops {I L : ℕ} (xs : Fin (L + 1) → List Bool) (gs : List Gate) : Finset (Fin L) :=
  Finset.univ.filter (fun t : Fin L =>
    ∃ w < I + gs.length,
      (evalWires gs (xs t.castSucc)).getD w false = true ∧
      (evalWires gs (xs t.succ)).getD w false = false)

lemma markov_drops_bound {I L : ℕ} (xs : Fin (L + 1) → List Bool)
    (hlen : ∀ t : Fin (L + 1), (xs t).length = I)
    (hmono : ∀ t : Fin L, ∀ w < I,
      (xs t.castSucc).getD w false = true → (xs t.succ).getD w false = true) :
    ∀ gs : List Gate,
      (∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) →
      (drops (I := I) xs gs).card + 1 ≤ 2 ^ notCount ⟨gs, 0⟩ := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _
    have hemp : drops (I := I) xs [] = ∅ := by
      ext t
      simp only [drops, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false, not_exists, List.length_nil, Nat.add_zero]
      rintro w ⟨hw, h1, h2⟩
      exact Bool.noConfusion ((hmono t w hw h1).symm.trans h2)
    rw [hemp]
    simp [notCount]
  | append_singleton gs g ih =>
    intro hfan
    have hfan_pre : ∀ g' ∈ gs, (g'.op = .and ∨ g'.op = .or ∨ g'.op = .not) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hfan g' (List.mem_append_left _ hg')
    have hg_fan := hfan g (List.mem_append_right _ (List.mem_singleton_self g))
    have hih := ih hfan_pre
    set D := drops (I := I) xs gs
    set v : Fin (L + 1) → Bool := fun t => (evalWires (gs ++ [g]) (xs t)).getD (I + gs.length) false
    set newD : Finset (Fin L) := Finset.univ.filter (fun t : Fin L => v t.castSucc = true ∧ v t.succ = false)
    have hsplit : drops (I := I) xs (gs ++ [g]) = D ∪ newD := by
      ext t
      simp only [drops, D, newD, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        List.length_append, List.length_singleton]
      constructor
      · rintro ⟨w, hw, h1, h2⟩
        by_cases hlt : w < I + gs.length
        · left
          refine ⟨w, hlt, ?_, ?_⟩
          · rwa [evalWires_snoc_old gs g (xs t.castSucc) (by rw [hlen]; exact hlt)] at h1
          · rwa [evalWires_snoc_old gs g (xs t.succ) (by rw [hlen]; exact hlt)] at h2
        · have heq : w = I + gs.length := by omega
          subst heq
          exact Or.inr ⟨h1, h2⟩
      · rintro (⟨w, hw, h1, h2⟩ | ⟨h1, h2⟩)
        · refine ⟨w, by omega, ?_, ?_⟩
          · rw [evalWires_snoc_old gs g (xs t.castSucc) (by rw [hlen]; exact hw)]; exact h1
          · rw [evalWires_snoc_old gs g (xs t.succ) (by rw [hlen]; exact hw)]; exact h2
        · exact ⟨I + gs.length, by omega, h1, h2⟩
    have hv_eq : ∀ t : Fin (L + 1),
        v t = g.op.eval (g.inputs.map fun i => (evalWires gs (xs t)).getD i false) := by
      intro t
      dsimp only [v]
      rw [← hlen t]
      exact evalWires_snoc_last gs g (xs t)
    rcases hg_fan.1 with hop | hop | hop
    · have hnc : notCount ⟨gs ++ [g], 0⟩ = notCount ⟨gs, 0⟩ := by
        unfold notCount
        simp [List.filter_append, hop]
      have hsub : newD ⊆ D := by
        intro t ht
        simp only [newD, Finset.mem_filter, Finset.mem_univ, true_and] at ht
        by_contra hnd
        have hnondec : ∀ i : ℕ, (evalWires gs (xs t.castSucc)).getD i false = true →
            (evalWires gs (xs t.succ)).getD i false = true := by
          intro i hi
          by_cases hilt : i < I + gs.length
          · cases h2 : (evalWires gs (xs t.succ)).getD i false
            · exfalso
              apply hnd
              simp only [D, drops, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨i, hilt, hi, h2⟩
            · rfl
          · rw [getD_of_le _ _ (by rw [evalWires_length, hlen]; omega)] at hi
            exact Bool.noConfusion hi
        have htrue : v t.succ = true := by
          have h1 := ht.1
          rw [hv_eq] at h1 ⊢
          refine gateOp_eval_mono (Or.inl hop) (by simp) (fun idx hidx hval => ?_) h1
          simp only [List.length_map] at hidx
          simp only [List.getElem_map] at hval ⊢
          exact hnondec g.inputs[idx] hval
        rw [ht.2] at htrue
        exact Bool.noConfusion htrue
      rw [hsplit, Finset.union_eq_left.mpr hsub, hnc]
      exact hih
    · have hnc : notCount ⟨gs ++ [g], 0⟩ = notCount ⟨gs, 0⟩ := by
        unfold notCount
        simp [List.filter_append, hop]
      have hsub : newD ⊆ D := by
        intro t ht
        simp only [newD, Finset.mem_filter, Finset.mem_univ, true_and] at ht
        by_contra hnd
        have hnondec : ∀ i : ℕ, (evalWires gs (xs t.castSucc)).getD i false = true →
            (evalWires gs (xs t.succ)).getD i false = true := by
          intro i hi
          by_cases hilt : i < I + gs.length
          · cases h2 : (evalWires gs (xs t.succ)).getD i false
            · exfalso
              apply hnd
              simp only [D, drops, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨i, hilt, hi, h2⟩
            · rfl
          · rw [getD_of_le _ _ (by rw [evalWires_length, hlen]; omega)] at hi
            exact Bool.noConfusion hi
        have htrue : v t.succ = true := by
          have h1 := ht.1
          rw [hv_eq] at h1 ⊢
          refine gateOp_eval_mono (Or.inr hop) (by simp) (fun idx hidx hval => ?_) h1
          simp only [List.length_map] at hidx
          simp only [List.getElem_map] at hval ⊢
          exact hnondec g.inputs[idx] hval
        rw [ht.2] at htrue
        exact Bool.noConfusion htrue
      rw [hsplit, Finset.union_eq_left.mpr hsub, hnc]
      exact hih
    · have hnc : notCount ⟨gs ++ [g], 0⟩ = notCount ⟨gs, 0⟩ + 1 := by
        unfold notCount
        simp [List.filter_append, hop]
      set A := newD \ D
      have hbet : ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁.val < a₂.val → ∃ d ∈ D, a₁.val < d.val ∧ d.val < a₂.val := by
        intro a₁ ha₁ a₂ ha₂ hlt
        have ha₁' := Finset.mem_filter.mp (Finset.mem_sdiff.mp ha₁).1
        have ha₂' := Finset.mem_filter.mp (Finset.mem_sdiff.mp ha₂).1
        rcases exists_rise_between v (a := a₁.val + 1) (b := a₂.val) (by omega) (by omega)
            ha₁'.2.2 ha₂'.2.1 with ⟨s, hs1, hs2, hsf, hst⟩
        refine ⟨s, ?_, by omega, hs2⟩
        rw [hv_eq, hop] at hsf hst
        cases hin : g.inputs with
        | nil =>
          simp [hin, GateOp.eval] at hsf
        | cons w0 _ =>
          simp only [hin, List.map_cons, GateOp.eval, List.headD_cons, Bool.not_eq_false',
            Bool.not_eq_true'] at hsf hst
          have hw0_lt : w0 < I + gs.length := by
            by_contra hge
            rw [getD_of_le _ _ (by rw [evalWires_length, hlen]; omega)] at hsf
            exact Bool.noConfusion hsf
          simp only [D, drops, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨w0, hw0_lt, hsf, hst⟩
      have hA_le : A.card ≤ D.card + 1 := card_le_of_between A D hbet
      have hunion : D ∪ newD = D ∪ A := by
        ext x; simp only [A, Finset.mem_union, Finset.mem_sdiff]; tauto
      have hcard_u : (D ∪ newD).card ≤ D.card + A.card := by
        rw [hunion]; exact Finset.card_union_le D A
      rw [hsplit, hnc, Nat.pow_succ]
      omega
lemma inp_getD (n : ℕ) (P : Fin n → Bool) (w : ℕ) :
    (List.ofFn P ++ [false, true]).getD w false =
      if h : w < n then P ⟨w, h⟩ else decide (w = n + 1) := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_append_left (by simpa using h)]
    simp [h]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn]
    rcases Nat.lt_or_ge w (n + 2) with h2 | h2
    · by_cases h3 : w = n + 1
      · subst h3; simp
      · have : w = n := by omega
        subst this; simp
    · rw [List.getElem?_eq_none (by simp; omega)]
      simp; omega

end NecessaryDrops

private def necessaryPrefix {n : Nat} (π : Equiv.Perm (Fin n)) (r : Nat) :
    Finset (Fin n) :=
  (Finset.univ.filter (fun i : Fin n => i.val < r)).image (fun i => π i)

private lemma mem_necessaryPrefix {n : Nat} (π : Equiv.Perm (Fin n))
    (r : Nat) (j : Fin n) : j ∈ necessaryPrefix π r ↔ (π.symm j).val < r := by
  classical
  simp only [necessaryPrefix, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    simpa using hi
  · intro h
    exact ⟨π.symm j, h, π.apply_symm_apply j⟩

private lemma pre_eq_necessaryPrefix {n : Nat} (π : Equiv.Perm (Fin n)) (k : Fin n) :
    pre π k = necessaryPrefix π k.val := by
  classical
  ext j
  simp only [pre, necessaryPrefix, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]

private lemma necessaryPrefix_succ {n : Nat} (π : Equiv.Perm (Fin n)) (k : Fin n) :
    necessaryPrefix π (k.val + 1) = insert (π k) (pre π k) := by
  classical
  rw [pre_eq_necessaryPrefix]
  ext j
  simp only [Finset.mem_insert, mem_necessaryPrefix]
  have he : j = π k ↔ (π.symm j).val = k.val := by
    constructor
    · rintro rfl
      simp
    · intro h
      have h' : π.symm j = k := Fin.ext h
      simpa using congrArg (fun i => π i) h'
  rw [he]
  omega

private lemma necessaryInp_mono {n : Nat} {x y : Finset (Fin n)} (hxy : x ⊆ y)
    (w : Nat) (h : (inp x).getD w false = true) : (inp y).getD w false = true := by
  classical
  simp only [inp, NecessaryDrops.inp_getD] at h ⊢
  split_ifs at h ⊢
  · simp only [decide_eq_true_eq] at h ⊢
    exact hxy h
  · exact h

lemma necessary {n T b : Nat} {q : Finset (Fin n) → Fin n → Nat}
    (cs : Fin T → Circuit) (a : ∀ t, Fin n → Fin (n+2+(cs t).size))
    (hv : ∀ t, valid n b (cs t))
    (hm : letI : ∀ p : Prop, Decidable p := Classical.propDecidable
      ∀ x j, j ∉ x → q x j ≤ ((Finset.univ : Finset (Fin T)).filter
        (fun t => val (cs t) (a t) x j = true ∧
          val (cs t) (a t) (insert j x) j = false)).card) :
    (∀ x j, j ∉ x → q x j ≤ T) ∧
    ∀ π : Equiv.Perm (Fin n), Finset.univ.sum (fun k => q (pre π k) (π k)) ≤ T*(2^b-1) := by
  classical
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  constructor
  · intro x j hj
    refine (hm x j hj).trans ?_
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_filter_le (Finset.univ : Finset (Fin T)) (fun t =>
        val (cs t) (a t) x j = true ∧ val (cs t) (a t) (insert j x) j = false))
  · intro π
    have hnot : ∀ k, π k ∉ pre π k := by
      intro k
      rw [pre_eq_necessaryPrefix, mem_necessaryPrefix, π.symm_apply_apply]
      exact Nat.lt_irrefl _
    let xs : Fin (n+1) → List Bool := fun r => inp (necessaryPrefix π r.val)
    let hit (k : Fin n) (t : Fin T) : Prop :=
      val (cs t) (a t) (pre π k) (π k) = true ∧
      val (cs t) (a t) (insert (π k) (pre π k)) (π k) = false
    have hcol : ∀ t : Fin T, ((Finset.univ : Finset (Fin n)).filter
        (fun k => hit k t)).card ≤ 2^b-1 := by
      intro t
      have hf := (hv t).1
      have hb := (hv t).2.2.2
      have hf' : ∀ g ∈ (cs t).gates,
          (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
        intro g hg
        obtain ⟨h1, h2⟩ := hf g hg
        exact ⟨by simpa using h1, h2⟩
      have hchain (r : Fin n) : necessaryPrefix π r.val ⊆ necessaryPrefix π (r.val+1) := by
        intro j hj
        rw [mem_necessaryPrefix] at hj ⊢
        exact Nat.lt_succ_of_lt hj
      have hm' := NecessaryDrops.markov_drops_bound (I := n+2) xs
        (fun r => inp_length _) (fun r w _ hw => necessaryInp_mono (hchain r) w hw)
        (cs t).gates hf'
      have hs : ((Finset.univ : Finset (Fin n)).filter (fun k => hit k t)) ⊆
          NecessaryDrops.drops (I := n+2) xs (cs t).gates := by
        intro k hk
        rcases (Finset.mem_filter.mp hk).2 with ⟨h1, h2⟩
        simp only [NecessaryDrops.drops, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨(a t (π k)).val, (a t (π k)).isLt, ?_, ?_⟩
        · change val (cs t) (a t) (necessaryPrefix π k.val) (π k) = true
          rwa [← pre_eq_necessaryPrefix]
        · change val (cs t) (a t) (necessaryPrefix π (k.val+1)) (π k) = false
          rw [necessaryPrefix_succ]
          simpa only [classical_insert] using h2
      change (NecessaryDrops.drops (I := n+2) xs (cs t).gates).card + 1 ≤
        2 ^ notCount (cs t) at hm'
      have hp : 2 ^ notCount (cs t) ≤ 2^b := Nat.pow_le_pow_right (Nat.zero_lt_succ 1) hb
      have hc := Finset.card_le_card hs
      exact Nat.le_sub_of_add_le ((Nat.add_le_add_right hc 1).trans (hm'.trans hp))
    calc
      (∑ k : Fin n, q (pre π k) (π k)) ≤ ∑ k : Fin n, ∑ t : Fin T,
          if hit k t then 1 else 0 := by
        apply Finset.sum_le_sum
        intro k _
        rw [← Finset.sum_filter]
        simpa [hit] using hm (pre π k) (π k) (hnot k)
      _ = ∑ t : Fin T, ∑ k : Fin n, if hit k t then 1 else 0 := Finset.sum_comm
      _ ≤ ∑ _t : Fin T, (2^b-1) := by
        apply Finset.sum_le_sum
        intro t _
        rw [← Finset.sum_filter]
        simpa using hcol t
      _ = T*(2^b-1) := by simp
def Meets {n T : Nat} (q : Finset (Fin n) → Fin n → Nat)
    (cs : Fin T → Circuit) (a : ∀ t, Fin n → Fin (n+2+(cs t).size)) : Prop :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  ∀ x j, j ∉ x → q x j ≤ ((Finset.univ : Finset (Fin T)).filter
    (fun t => val (cs t) (a t) x j = true ∧ val (cs t) (a t) (insert j x) j = false)).card

def Feasible {n : Nat} (T b : Nat) (q : Finset (Fin n) → Fin n → Nat) : Prop :=
  (∀ x j, j ∉ x → q x j ≤ T) ∧
  ∀ π : Equiv.Perm (Fin n), Finset.univ.sum (fun k => q (pre π k) (π k)) ≤ T*(2^b-1)

def Tight {n b : Nat} (s : Nat) (C : Circuit) (a : Fin n → Fin (n+2+C.size)) : Prop :=
  valid n b C ∧ C.size ≤ 64*(n+1)^2*(s+1) ∧ ∀ x j, j ∈ x → val C a x j = false

lemma sufficient {n T b : Nat} {q : Finset (Fin n) → Fin n → Nat} (h : Feasible T b q) :
    ∃ (cs : Fin T → Circuit) (a : ∀ t, Fin n → Fin (n+2+(cs t).size)),
      (∀ t, Tight (b := b) (support q) (cs t) (a t)) ∧ Meets q cs a := by
  classical
  obtain ⟨S, H, hS, hb, hH, hquota⟩ := sparseHeight q h.1 h.2
  have hpow : 0 < (2:Nat)^b := by positivity
  let m := min n (2^b-1)
  have hm : m ≤ n := min_le_left ..
  have hmb : m < 2^b := (min_le_right ..).trans_lt (by omega)
  have build (t : Fin T) : ∃ (C : Circuit) (a : Fin n → Fin (n+2+C.size)),
      valid n b C ∧ C.size ≤ 64*(n+1)^2*(support q+1) ∧
      ∀ x j, val C a x j = decide (H t x < H t (insert j x)) :=
    sparseCompile S (H t) hS hm hmb (hH t) (hb t)
  choose cs a hv hsize heval using build
  have one (t : Fin T) (x : Finset (Fin n)) (j : Fin n) (hj : j ∈ x) :
      val (cs t) (a t) x j = false := by
    rw [heval, Finset.insert_eq_of_mem hj]
    simp
  refine ⟨cs, a, fun t => ⟨hv t, hsize t, one t⟩, ?_⟩
  intro x j hj
  refine (hquota x j hj).trans (Finset.card_le_card ?_)
  intro t ht
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
  rw [classical_insert]
  exact ⟨(heval t x j).trans (decide_eq_true ht), one t (insert j x) j (Finset.mem_insert_self ..)⟩

lemma result (n T b : Nat) (q : Finset (Fin n) → Fin n → Nat) :
    ((∃ (cs : Fin T → Circuit) (a : ∀ t, Fin n → Fin (n+2+(cs t).size)),
      (∀ t, valid n b (cs t)) ∧ Meets q cs a) ↔ Feasible T b q) ∧
    (Feasible T b q → ∃ (cs : Fin T → Circuit) (a : ∀ t, Fin n → Fin (n+2+(cs t).size)),
      (∀ t, Tight (b := b) (support q) (cs t) (a t)) ∧ Meets q cs a) := by
  refine ⟨⟨?_, ?_⟩, sufficient⟩
  · rintro ⟨cs, a, hv, hq⟩
    exact necessary cs a hv hq
  · intro h
    obtain ⟨cs, a, hv, hq⟩ := sufficient h
    exact ⟨cs, a, fun t => (hv t).1, hq⟩

end PEqualNP.Outside.L_meta_51424_aux

theorem PEqualNP.Outside.L_meta_51424 :
letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (n T b : Nat) (q : Finset (Fin n) → Fin n → Nat),
  let X := Finset (Fin n)
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let taps := fun (C : Circ) => Fin n → Fin (n+2+C.size)
  let input := fun (x : X) => List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false,true]
  let val := fun (C : Circ) (a : taps C) (x : X) (j : Fin n) =>
    (C.wires (input x)).getD (a j).val false
  let valid := fun (C : Circ) => PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧ C.output < n+2+C.size ∧
    PEqualNP.NotBracket.notCount C ≤ b
  let oneSide := fun (C : Circ) (a : taps C) => ∀ (x : X) (j : Fin n), j ∈ x → val C a x j = false
  let pre := fun (π : Equiv.Perm (Fin n)) (k : Fin n) =>
    ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < k.val)).image (fun i => π i)
  let supp := (Finset.univ : Finset X).sum (fun x =>
    ((Finset.univ : Finset (Fin n)).filter (fun j => j ∉ x ∧ 0 < q x j)).card)
  let meets := fun (cs : Fin T → Circ) (a : ∀ t, taps (cs t)) =>
    ∀ (x : X) (j : Fin n), j ∉ x → q x j ≤ ((Finset.univ : Finset (Fin T)).filter
      (fun t => val (cs t) (a t) x j = true ∧ val (cs t) (a t) (insert j x) j = false)).card
  let feasible := (∀ (x : X) (j : Fin n), j ∉ x → q x j ≤ T) ∧
    ∀ π : Equiv.Perm (Fin n), Finset.univ.sum (fun k => q (pre π k) (π k)) ≤ T*(2^b-1)
  ((∃ (cs : Fin T → Circ) (a : ∀ t, taps (cs t)), (∀ t, valid (cs t)) ∧ meets cs a) ↔ feasible) ∧
  (feasible → ∃ (cs : Fin T → Circ) (a : ∀ t, taps (cs t)),
    (∀ t, valid (cs t) ∧ (cs t).size ≤ 64*(n+1)^2*(supp+1) ∧ oneSide (cs t) (a t)) ∧ meets cs a) := by
  intro n T b q
  exact PEqualNP.Outside.L_meta_51424_aux.result n T b q
