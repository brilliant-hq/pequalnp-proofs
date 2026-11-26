import PEqualNP.Defs.Represents

namespace PEqualNP.Outside.Power19382

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C (n : ℕ) : Circuit := ⟨[
  ⟨.or,[n+1,n+2]⟩,
  ⟨.or,[0,n+n]⟩,
  ⟨.or,[1,n]⟩,
  ⟨.or,[n+n,n+n+2]⟩,
  ⟨.and,[n+n+1,n+n+2]⟩,
  ⟨.not,[n+n+4]⟩,
  ⟨.and,[n+n+3,n+n+5]⟩], n+n+6⟩

theorem early (l : List Bool) (b : Bool) (i : ℕ) (h : i < l.length) :
    (l ++ [b]).getD i false = l.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem lastBit (l : List Bool) (b : Bool) (i : ℕ) (h : i = l.length) :
    (l ++ [b]).getD i false = b := by
  subst i
  simp [List.getD_eq_getElem?_getD]

theorem leftBit {n : ℕ} (u v : Fin n) (i : ℕ) (hi : i < n) :
    (oneEach u v).getD i false = decide (i = u.val) := by
  unfold oneEach
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa), List.getElem?_eq_getElem (by simpa)]
  simp [Fin.ext_iff]

theorem rightBit {n : ℕ} (u v : Fin n) (i : ℕ) (hi : i < n) :
    (oneEach u v).getD (n+i) false = decide (i = v.val) := by
  unfold oneEach
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left]
  rw [List.getElem?_eq_getElem (by simpa)]
  simp [Fin.ext_iff]

theorem lookup (l : List Bool) (b : Bool) (i : ℕ) :
    (l ++ [b]).getD i false = if i = l.length then b else l.getD i false := by
  by_cases h : i < l.length
  · rw [early _ _ _ h, if_neg (Nat.ne_of_lt h)]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    by_cases e : i = l.length
    · simp [e]
    · have hs : 1 ≤ i-l.length := by omega
      rw [List.getElem?_eq_none (by simpa using hs), if_neg e, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]

theorem truth (a b : ℕ) :
    ((decide (1 = b) || decide (2 = b) || (decide (1 = a) || decide (0 = b))) &&
      !((decide (0 = a) || (decide (1 = b) || decide (2 = b))) && (decide (1 = a) || decide (0 = b)))) =
    decide (a = 0 ∧ (b = 1 ∨ b = 2) ∨ a = 1 ∧ ¬(b = 1 ∨ b = 2) ∨ 2 ≤ a ∧ b ≤ 2) := by
  rcases a with _ | _ | a <;> rcases b with _ | _ | _ | b <;> simp +arith

end PEqualNP.Outside.Power19382

open PEqualNP.Outside.Power19382 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_19382 : ∀ n : ℕ, 3 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ (v.val = 1 ∨ v.val = 2)) ∨ (u.val = 1 ∧ ¬ (v.val = 1 ∨ v.val = 2)) ∨ (2 ≤ u.val ∧ v.val ≤ 2))) C := by
  intro n hn
  refine ⟨C n, ?_, ?_, ?_⟩
  · simp [FanInTwo, C]
  · exact Nat.le_refl 7
  · intro u v
    have hl : (oneEach u v).length = n+n := by simp [oneEach]
    have rz : (oneEach u v).getD n false = decide (0 = v.val) := by simpa using rightBit u v 0 (by omega)
    simp only [C, Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil,
      List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
      List.all_cons, List.all_nil, List.headD_cons, id_eq, Bool.or_false, Bool.and_true]
    have hh0 : (0 : ℕ) ≠ (n+n) := by omega
    have hh7 : (1 : ℕ) ≠ (n+n) := by omega
    have hh8 : (1 : ℕ) ≠ (n+n+1) := by omega
    have hh14 : (n : ℕ) ≠ (n+n) := by omega
    have hh15 : (n : ℕ) ≠ (n+n+1) := by omega
    have hh36 : (n+n : ℕ) ≠ (n+n+1) := by omega
    have hh37 : (n+n : ℕ) ≠ (n+n+1+1) := by omega
    have hh42 : (n+n+1 : ℕ) ≠ (n+n) := by omega
    have hh44 : (n+n+1 : ℕ) ≠ (n+n+1+1) := by omega
    have hh45 : (n+n+1 : ℕ) ≠ (n+n+1+1+1) := by omega
    have hh49 : (n+n+2 : ℕ) ≠ (n+n) := by omega
    have hh50 : (n+n+2 : ℕ) ≠ (n+n+1) := by omega
    have hh51 : (n+n+2 : ℕ) = (n+n+1+1) := by omega
    have hh52 : (n+n+2 : ℕ) ≠ (n+n+1+1+1) := by omega
    have hh56 : (n+n+3 : ℕ) ≠ (n+n) := by omega
    have hh57 : (n+n+3 : ℕ) ≠ (n+n+1) := by omega
    have hh58 : (n+n+3 : ℕ) ≠ (n+n+1+1) := by omega
    have hh59 : (n+n+3 : ℕ) = (n+n+1+1+1) := by omega
    have hh60 : (n+n+3 : ℕ) ≠ (n+n+1+1+1+1) := by omega
    have hh61 : (n+n+3 : ℕ) ≠ (n+n+1+1+1+1+1) := by omega
    have hh63 : (n+n+4 : ℕ) ≠ (n+n) := by omega
    have hh64 : (n+n+4 : ℕ) ≠ (n+n+1) := by omega
    have hh65 : (n+n+4 : ℕ) ≠ (n+n+1+1) := by omega
    have hh66 : (n+n+4 : ℕ) ≠ (n+n+1+1+1) := by omega
    have hh67 : (n+n+4 : ℕ) = (n+n+1+1+1+1) := by omega
    have hh70 : (n+n+5 : ℕ) ≠ (n+n) := by omega
    have hh71 : (n+n+5 : ℕ) ≠ (n+n+1) := by omega
    have hh72 : (n+n+5 : ℕ) ≠ (n+n+1+1) := by omega
    have hh73 : (n+n+5 : ℕ) ≠ (n+n+1+1+1) := by omega
    have hh74 : (n+n+5 : ℕ) ≠ (n+n+1+1+1+1) := by omega
    have hh75 : (n+n+5 : ℕ) = (n+n+1+1+1+1+1) := by omega
    have hh77 : (n+n+6 : ℕ) ≠ (n+n) := by omega
    have hh78 : (n+n+6 : ℕ) ≠ (n+n+1) := by omega
    have hh79 : (n+n+6 : ℕ) ≠ (n+n+1+1) := by omega
    have hh80 : (n+n+6 : ℕ) ≠ (n+n+1+1+1) := by omega
    have hh81 : (n+n+6 : ℕ) ≠ (n+n+1+1+1+1) := by omega
    have hh82 : (n+n+6 : ℕ) ≠ (n+n+1+1+1+1+1) := by omega
    have hh83 : (n+n+6 : ℕ) = (n+n+1+1+1+1+1+1) := by omega
    simp only [lookup, List.length_append, List.length_cons, List.length_nil, hl, Nat.reduceAdd]
    simp only [hh0,hh7,hh8,hh14,hh15,hh36,hh37,hh42,hh44,hh45,hh49,hh50,hh51,hh52,hh56,hh57,hh58,hh59,hh60,hh61,hh63,hh64,hh65,hh66,hh67,hh70,hh71,hh72,hh73,hh74,hh75,hh77,hh78,hh79,hh80,hh81,hh82,hh83, if_true, if_false, rz, leftBit u v 0 (by omega), leftBit u v 1 (by omega), rightBit u v 1 (by omega), rightBit u v 2 (by omega)]
    exact truth u.val v.val

