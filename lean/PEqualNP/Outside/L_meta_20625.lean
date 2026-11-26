import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20625

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def advance (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def ordered (T : Finset Nat) (x y : List Bool) :=
  ∀ i ∈ T, x.getD i false = true → y.getD i false = true

theorem away (w : List Bool) (b : Bool) (i : Nat) (hi : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  by_cases h : i < w.length
  · exact List.getD_append _ _ _ _ h
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem atNew (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
  rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]; rfl

theorem gate_mono (g : Gate) (x y : List Bool)
    (op : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp))
    (h : ordered g.inputs.toFinset x y) :
    g.op.eval (g.inputs.map fun i => x.getD i false) = true →
      g.op.eval (g.inputs.map fun i => y.getD i false) = true := by
  rcases (show g.op = .and ∨ g.op = .or from op) with eq | eq
  · simp [eq,GateOp.eval]
    exact fun hx i hi => h i (List.mem_toFinset.mpr hi) (hx i hi)
  · simp [eq,GateOp.eval]
    rintro i hi hv
    exact ⟨i,hi,h i (List.mem_toFinset.mpr hi) hv⟩

theorem support (gs : List Gate) (n : Nat) (S : Finset Nat)
    (ok : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∃ T : Finset Nat, T.card ≤ S.card + gs.length ∧
      ∀ x y : List Bool, x.length = n → y.length = n → ordered T x y →
        ordered S (gs.foldl advance x) (gs.foldl advance y) := by
  induction gs generalizing n S with
  | nil => exact ⟨S,by simp,fun _ _ _ _ h => h⟩
  | cons g gs ih =>
    obtain ⟨U,hu,dep⟩ := ih (n+1) S (fun a ha => ok a (List.mem_cons_of_mem _ ha))
    obtain ⟨hop,arity⟩ := ok g List.mem_cons_self
    by_cases used : n ∈ U
    · let T := U.erase n ∪ g.inputs.toFinset
      have cost := Finset.card_union_le (U.erase n) g.inputs.toFinset
      have erased := Finset.card_erase_of_mem used
      have pos := Finset.card_pos.mpr ⟨n,used⟩
      have fan := List.toFinset_card_le g.inputs
      refine ⟨T,by change (U.erase n ∪ g.inputs.toFinset).card ≤ S.card + (gs.length + 1); omega,?_⟩
      intro x y hx hy h
      apply dep (advance x g) (advance y g) (by simp [advance,hx]) (by simp [advance,hy])
      intro i hi
      by_cases eq : i=n
      · subst i
        unfold advance
        rw [← hx,atNew,hx,← hy,atNew]
        apply gate_mono _ _ _ hop
        exact fun j hj => h j (Finset.mem_union_right _ hj)
      · unfold advance
        rw [away _ _ _ (hx ▸ eq),away _ _ _ (hy ▸ eq)]
        exact h i (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hi⟩))
    · refine ⟨U,by simp only [List.length_cons]; omega,?_⟩
      intro x y hx hy h
      apply dep (advance x g) (advance y g) (by simp [advance,hx]) (by simp [advance,hy])
      intro i hi
      have eq : i ≠ n := fun e => used (e ▸ hi)
      unfold advance
      rw [away _ _ _ (hx ▸ eq),away _ _ _ (hy ▸ eq)]
      exact h i hi

def matrix (u v : Fin 5) := (33489920 : Nat).testBit (5*u.val+v.val)
def circuit : Circuit := ⟨[
  ⟨.and,[2,5]⟩, ⟨.or,[6,7]⟩, ⟨.or,[11,8]⟩, ⟨.or,[12,9]⟩,
  ⟨.and,[3,13]⟩, ⟨.or,[4,10]⟩, ⟨.or,[15,14]⟩],16⟩

theorem upper : RepSizeAtMost matrix 7 := by
  refine ⟨circuit,?_,by decide,by decide +kernel⟩
  intro g hg
  simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem witnesses : ∀ k : Fin 10, 2 ≤ k.val → ∃ u v a b : Fin 5,
    matrix u v = true ∧ matrix a b = false ∧ ∀ i : Fin 10, i ≠ k →
      (oneEach u v).getD i.val false = true → (oneEach a b).getD i.val false = true := by
  decide +kernel

theorem lower : ¬ RepSizeAtMost matrix 6 := by
  rintro ⟨C,ok,budget,rep⟩
  obtain ⟨T,size,dep⟩ := support C.gates 10 {C.output} ok
  have needed : Finset.Ico 2 10 ⊆ T := by
    intro k hk
    obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp hk
    obtain ⟨u,v,a,b,yes,no,ord⟩ := witnesses ⟨k,hi⟩ lo
    by_contra missing
    have h : ordered T (oneEach u v) (oneEach a b) := by
      intro i hmem
      by_cases bit : i < 10
      · apply ord ⟨i,bit⟩
        intro eq
        have same : i = k := congrArg Fin.val eq
        exact missing (same ▸ hmem)
      · rw [List.getD_eq_default _ _ (by simp [oneEach]; omega)]
        simp
    have final := dep _ _ (by simp [oneEach]) (by simp [oneEach]) h C.output (by simp)
    change C.eval (oneEach u v) = true → C.eval (oneEach a b) = true at final
    rw [rep u v,rep a b,yes,no] at final
    simp at final
  have count := Finset.card_le_card needed
  have eight : (Finset.Ico 2 10).card = 8 := by decide
  change C.gates.length ≤ 6 at budget
  simp only [Finset.card_singleton] at size
  omega

end PEqualNP.Outside.L_meta_20625

theorem PEqualNP.Outside.L_meta_20625 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (33489920 : ℕ).testBit (5 * u.val + v.val)) 7 ∧ ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (33489920 : ℕ).testBit (5 * u.val + v.val)) 6) := by
  exact ⟨PEqualNP.Outside.L_meta_20625.upper,PEqualNP.Outside.L_meta_20625.lower⟩
