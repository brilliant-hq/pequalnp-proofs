import Mathlib.SetTheory.Cardinal.Finite
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_372_aux

def forcedBit (free forced : ℕ)
    (rule : (i : Fin forced) → (Fin free → Bool) → (Fin i.val → Bool) → Bool)
    (seed : Fin free → Bool) : (k : ℕ) → k < forced → Bool
  | k, hk => rule ⟨k, hk⟩ seed (fun j => forcedBit free forced rule seed j.val (Nat.lt_trans j.isLt hk))
termination_by k => k

def buildWord (free forced : ℕ)
    (rule : (i : Fin forced) → (Fin free → Bool) → (Fin i.val → Bool) → Bool)
    (seed : Fin free → Bool) (x : Fin (free + forced)) : Bool :=
  if h : x.val < free then seed ⟨x.val, h⟩
  else forcedBit free forced rule seed (x.val - free) (by omega)

lemma buildWord_castAdd (free forced : ℕ)
    (rule : (i : Fin forced) → (Fin free → Bool) → (Fin i.val → Bool) → Bool)
    (seed : Fin free → Bool) (a : Fin free) :
    buildWord free forced rule seed (Fin.castAdd forced a) = seed a := by
  simp [buildWord]

lemma buildWord_natAdd (free forced : ℕ)
    (rule : (i : Fin forced) → (Fin free → Bool) → (Fin i.val → Bool) → Bool)
    (seed : Fin free → Bool) (i : Fin forced) :
    buildWord free forced rule seed (Fin.natAdd free i) = forcedBit free forced rule seed i.val i.isLt := by
  unfold buildWord
  have hnot : ¬ (Fin.natAdd free i).val < free := by simp
  rw [dite_eq_right hnot]
  congr 1
  simp

lemma buildWord_passes (free forced : ℕ)
    (rule : (i : Fin forced) → (Fin free → Bool) → (Fin i.val → Bool) → Bool)
    (seed : Fin free → Bool) :
    ∀ i : Fin forced, buildWord free forced rule seed (Fin.natAdd free i) =
      rule i (fun a => buildWord free forced rule seed (Fin.castAdd forced a))
        (fun j => buildWord free forced rule seed (Fin.natAdd free (Fin.castLE (Nat.le_of_lt i.isLt) j))) := by
  intro i
  rw [buildWord_natAdd]
  conv_lhs => unfold forcedBit
  have hfree : (fun a => buildWord free forced rule seed (Fin.castAdd forced a)) = seed := by
    funext a
    exact buildWord_castAdd free forced rule seed a
  rw [hfree]
  congr 1
  funext j
  rw [buildWord_natAdd]
  rfl

lemma word_natAdd_eq_forcedBit (free forced : ℕ)
    (rule : (i : Fin forced) → (Fin free → Bool) → (Fin i.val → Bool) → Bool)
    (seed : Fin free → Bool) (word : Fin (free + forced) → Bool)
    (hfree : (fun a => word (Fin.castAdd forced a)) = seed)
    (hpass : ∀ i : Fin forced, word (Fin.natAdd free i) =
      rule i (fun a => word (Fin.castAdd forced a))
        (fun j => word (Fin.natAdd free (Fin.castLE (Nat.le_of_lt i.isLt) j)))) :
    ∀ (k : ℕ) (hk : k < forced), word (Fin.natAdd free ⟨k, hk⟩) = forcedBit free forced rule seed k hk := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk
    rw [hpass ⟨k, hk⟩, hfree]
    conv_rhs => unfold forcedBit
    congr 1
    funext j
    exact ih j.val j.isLt (Nat.lt_trans j.isLt hk)

lemma eq_buildWord_of_passes (free forced : ℕ)
    (rule : (i : Fin forced) → (Fin free → Bool) → (Fin i.val → Bool) → Bool)
    (seed : Fin free → Bool) (word : Fin (free + forced) → Bool)
    (hfree : (fun a => word (Fin.castAdd forced a)) = seed)
    (hpass : ∀ i : Fin forced, word (Fin.natAdd free i) =
      rule i (fun a => word (Fin.castAdd forced a))
        (fun j => word (Fin.natAdd free (Fin.castLE (Nat.le_of_lt i.isLt) j)))) :
    word = buildWord free forced rule seed := by
  funext x
  by_cases h : x.val < free
  · have hx : x = Fin.castAdd forced ⟨x.val, h⟩ := by ext; simp
    rw [hx, buildWord_castAdd]
    exact congrFun hfree ⟨x.val, h⟩
  · have hk : x.val - free < forced := by omega
    have hx : x = Fin.natAdd free ⟨x.val - free, hk⟩ := by ext; simp; omega
    rw [hx, buildWord_natAdd]
    exact word_natAdd_eq_forcedBit free forced rule seed word hfree hpass (x.val - free) hk

end PEqualNP.Outside.L_lib_372_aux

open PEqualNP.Outside.L_lib_372_aux in
theorem PEqualNP.Outside.L_lib_372 : (∀ (free forced : ℕ)
  (rule : (i : Fin forced) → (Fin free → Bool) → (Fin i.val → Bool) → Bool),
  let freeBits := fun (word : Fin (free + forced) → Bool) (a : Fin free) =>
    word (Fin.castAdd forced a)
  let passes := fun (word : Fin (free + forced) → Bool) =>
    ∀ i : Fin forced, word (Fin.natAdd free i) =
      rule i (freeBits word)
        (fun j => word (Fin.natAdd free (Fin.castLE (Nat.le_of_lt i.isLt) j)))
  ∃ complete : (Fin free → Bool) ≃ { word // passes word },
    (∀ seed word, freeBits word.val = seed ↔ word = complete seed) ∧
    Nat.card { word // passes word } = 2 ^ free) := by
  intro free forced rule freeBits passes
  let complete : (Fin free → Bool) ≃ { word // passes word } :=
    { toFun := fun seed => ⟨buildWord free forced rule seed, buildWord_passes free forced rule seed⟩
      invFun := fun w => freeBits w.val
      left_inv := fun seed => by
        funext a
        exact buildWord_castAdd free forced rule seed a
      right_inv := fun w => by
        apply Subtype.ext
        exact (eq_buildWord_of_passes free forced rule (freeBits w.val) w.val rfl w.property).symm }
  refine ⟨complete, ?_, ?_⟩
  · intro seed word
    constructor
    · intro h
      apply Subtype.ext
      exact eq_buildWord_of_passes free forced rule seed word.val h word.property
    · intro h
      subst h
      funext a
      exact buildWord_castAdd free forced rule seed a
  · rw [← Nat.card_congr complete, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
