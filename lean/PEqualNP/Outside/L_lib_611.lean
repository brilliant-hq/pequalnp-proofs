import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_611

variable {V : Type} [Fintype V] [DecidableEq V]

def mono (term : Finset V) (word : V → Bool) : ZMod 2 :=
  if ∀ v ∈ term, word v = true then 1 else 0

def evalPoly (coeff : Finset V → ZMod 2) (word : V → Bool) : ZMod 2 :=
  ∑ term, coeff term * mono term word

def HasBound (bound : Nat) (func : (V → Bool) → ZMod 2) : Prop :=
  ∃ coeff : Finset V → ZMod 2, (∀ term, coeff term ≠ 0 → term.card ≤ bound) ∧
    ∀ word, evalPoly coeff word = func word

def push {ι : Type} [Fintype ι] (dest : ι → Finset V) (weight : ι → ZMod 2)
    (target : Finset V) : ZMod 2 := ∑ idx, if dest idx = target then weight idx else 0

lemma evalPush {ι : Type} [Fintype ι] (dest : ι → Finset V) (weight : ι → ZMod 2)
    (word : V → Bool) : evalPoly (push dest weight) word = ∑ idx, weight idx * mono (dest idx) word := by
  classical
  unfold evalPoly push
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro idx _
  simp [ite_mul]

lemma monUnion (left right : Finset V) (word : V → Bool) :
    mono (left ∪ right) word = mono left word * mono right word := by
  simp only [mono, Finset.forall_mem_union]
  split_ifs <;> simp_all

lemma constantBound (bound : Nat) (value : ZMod 2) :
    HasBound (V := V) bound (fun _ => value) := by
  classical
  refine ⟨fun term => if term = ∅ then value else 0, ?_, ?_⟩
  · intro term h
    dsimp only at h
    split_ifs at h with heq <;> simp_all
  · intro word
    unfold evalPoly
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp [mono]

lemma plusConst {bound : Nat} {func : (V → Bool) → ZMod 2} (hf : HasBound bound func)
    (value : ZMod 2) : HasBound bound (fun w => func w + value) := by
  obtain ⟨cf, df, ef⟩ := hf
  obtain ⟨cc, dc, ec⟩ := constantBound (V := V) bound value
  refine ⟨fun term => cf term + cc term, ?_, ?_⟩
  · intro term hn
    by_cases hh : cf term = 0
    · exact dc term (by simpa [hh] using hn)
    · exact df term hh
  · intro word
    simpa [evalPoly, add_mul, Finset.sum_add_distrib] using congrArg₂ (· + ·) (ef word) (ec word)

lemma mulBound {bf bg : Nat} {ff fg : (V → Bool) → ZMod 2}
    (hf : HasBound bf ff) (hg : HasBound bg fg) :
    HasBound (bf + bg) (fun word => ff word * fg word) := by
  classical
  obtain ⟨cf, df, ef⟩ := hf
  obtain ⟨cg, dg, eg⟩ := hg
  let dest := fun p : Finset V × Finset V => p.1 ∪ p.2
  let weight := fun p : Finset V × Finset V => cf p.1 * cg p.2
  refine ⟨push dest weight, ?_, ?_⟩
  · intro term hn
    by_contra! hgt
    apply hn
    apply Finset.sum_eq_zero
    intro p _
    split_ifs with heq
    · rcases p with ⟨left, right⟩
      change left ∪ right = term at heq
      change cf left * cg right = 0
      by_cases hh : cf left = 0
      · simp [hh]
      by_cases hi : cg right = 0
      · simp [hi]
      have := Finset.card_union_le left right
      have := df left hh
      have := dg right hi
      subst term
      omega
    · rfl
  · intro word
    change evalPoly _ word = ff word * fg word
    rw [evalPush, ← ef, ← eg, Fintype.sum_prod_type]
    simp only [dest, weight, monUnion, evalPoly, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro left _
    apply Finset.sum_congr rfl
    intro right _
    ring

lemma evalInjZero (coeff : Finset V → ZMod 2) (hz : ∀ word, evalPoly coeff word = 0) :
    ∀ term, coeff term = 0 := by
  classical
  intro term
  induction term using Finset.strongInductionOn with
  | _ term ih =>
    have hh := hz (fun v => decide (v ∈ term))
    rw [evalPoly, Finset.sum_eq_single term] at hh
    · simpa [mono] using hh
    · intro other _ hne
      by_cases hsub : other ⊆ term
      · rw [ih other (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩), zero_mul]
      · simp [mono, show ¬ (∀ v ∈ other, v ∈ term) from hsub]
    · simp

lemma hasFace {bound : Nat} {func : (V → Bool) → ZMod 2} (hf : HasBound bound func)
    (anchor : V → Bool) (ha : func anchor ≠ 0) :
    ∃ free : Finset V, free.card ≤ bound ∧ ∀ word : V → Bool,
      ∃ hit : V → Bool, func hit ≠ 0 ∧ ∀ v ∉ free, hit v = word v := by
  classical
  obtain ⟨coeff, hc, he⟩ := hf
  let supp := Finset.univ.filter (fun term => coeff term ≠ 0)
  have hs : supp.Nonempty := by
    by_contra h
    have hall : ∀ term, coeff term = 0 := by simpa [supp, Finset.nonempty_iff_ne_empty] using h
    exact ha (by simp [← he, evalPoly, hall])
  obtain ⟨free, hm, hmax⟩ := supp.exists_max_image Finset.card hs
  have hn : coeff free ≠ 0 := (Finset.mem_filter.mp hm).2
  refine ⟨free, hc free hn, ?_⟩
  intro word
  by_contra! nohit
  let dest := fun term : Finset V => term ∩ free
  let weight := fun term : Finset V => coeff term * mono (term \ free) word
  have hz : ∀ inside, evalPoly (push dest weight) inside = 0 := by
    intro inside
    let hit := fun v => if v ∈ free then inside v else word v
    have heq : evalPoly (push dest weight) inside = evalPoly coeff hit := by
      rw [evalPush, evalPoly]
      apply Finset.sum_congr rfl
      intro term _
      change coeff term * mono (term \ free) word * mono (term ∩ free) inside = _
      rw [mul_assoc]
      congr 1
      simp only [mono]
      split_ifs <;> simp_all [hit] <;> grind
    rw [heq, he]
    by_contra h
    obtain ⟨v, hv, hne⟩ := nohit hit h
    exact hne (by simp [hit, hv])
  apply hn
  have hzero := evalInjZero _ hz free
  rw [push, Finset.sum_eq_single free] at hzero
  · simp [dest, weight, mono] at hzero
    exact hzero (by grind)
  · intro term _ hne
    split_ifs with hh
    · have hsub : free ⊆ term := by simpa [dest] using hh ▸ (Finset.inter_subset_left (s₁ := term) (s₂ := free))
      have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, Ne.symm hne⟩)
      have hc0 : coeff term = 0 := by
        by_contra hnterm
        exact (not_le_of_gt hlt) (hmax term (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnterm⟩))
      simp [weight, hc0]
    · rfl
  · simp

def bit (answer : Bool) : ZMod 2 := answer.toNat

lemma inputBound {bound : Nat} {query : (V → Bool) → Bool} (terms : Finset (Finset V))
    (ht : ∀ term ∈ terms, term.card ≤ bound) (he : ∀ word, query word =
      (((terms.filter (fun term => ∀ v ∈ term, word v = true)).card % 2) == 1)) :
    HasBound bound (fun word => bit (query word)) := by
  classical
  refine ⟨fun term => if term ∈ terms then 1 else 0, ?_, ?_⟩
  · intro term h
    exact ht term (by by_contra hh; simp [hh] at h)
  · intro word
    let count := (terms.filter (fun term => ∀ v ∈ term, word v = true)).card
    have hc : evalPoly (fun term => if term ∈ terms then 1 else 0) word = (count : ZMod 2) := by
      unfold evalPoly
      simp only [ite_mul, one_mul, zero_mul, ← Finset.sum_filter]
      simp [mono, count]
    change evalPoly _ word = bit (query word)
    rw [hc, he]
    change (count : ZMod 2) = bit ((count % 2) == 1)
    rw [← ZMod.natCast_mod count 2]
    rcases Nat.mod_two_eq_zero_or_one count with h | h <;> simp [h, bit]

def runCode {W : Type} (ask : Nat → Nat → W → Bool) (len : Nat) (word : W) : Nat :=
  (List.range len).foldl (fun h step => h + ((ask step h word).toNat <<< step)) 0

lemma runSucc {W : Type} (ask : Nat → Nat → W → Bool) (len : Nat) (word : W) :
    runCode ask (len + 1) word = runCode ask len word +
      (ask len (runCode ask len word) word).toNat * 2 ^ len := by
  simp [runCode, List.range_succ, List.foldl_append, Nat.shiftLeft_eq]

lemma runLt {W : Type} (ask : Nat → Nat → W → Bool) (len : Nat) (word : W) :
    runCode ask len word < 2 ^ len := by
  induction len with
  | zero => simp [runCode]
  | succ len ih =>
    rw [runSucc, pow_succ]
    cases ask len (runCode ask len word) word <;> simp_all <;> omega

lemma runEq {W : Type} (ask : Nat → Nat → W → Bool) (len : Nat) (word anchor : W) :
    runCode ask (len + 1) word = runCode ask (len + 1) anchor ↔
      runCode ask len word = runCode ask len anchor ∧
      ask len (runCode ask len anchor) word = ask len (runCode ask len anchor) anchor := by
  rw [runSucc, runSucc]
  have hl := runLt ask len word
  have hr := runLt ask len anchor
  by_cases hh : runCode ask len word = runCode ask len anchor
  · rw [hh]
    cases ask len (runCode ask len anchor) word <;> cases ask len (runCode ask len anchor) anchor <;> simp_all
  · cases ask len (runCode ask len word) word <;> cases ask len (runCode ask len anchor) anchor <;> simp_all <;> omega

lemma pathBound (ask : Nat → Nat → (V → Bool) → Bool) (anchor : V → Bool)
    (len : Nat) (bounds : Fin len → Nat) (hb : ∀ idx, HasBound (bounds idx)
      (fun word => bit (ask idx.val (runCode ask idx.val anchor) word))) :
    HasBound (∑ idx, bounds idx) (fun word => if runCode ask len word = runCode ask len anchor then 1 else 0) := by
  induction len with
  | zero => simpa [runCode] using constantBound (V := V) 0 1
  | succ len ih =>
    rw [Fin.sum_univ_castSucc]
    have hp := ih (fun idx => bounds idx.castSucc) (fun idx => hb idx.castSucc)
    let query := ask len (runCode ask len anchor)
    have hq : HasBound (bounds (Fin.last len)) (fun word => bit (query word)) := hb (Fin.last len)
    have hlit : HasBound (bounds (Fin.last len)) (fun word => if query word = query anchor then 1 else 0) := by
      cases hh : query anchor with
      | false =>
        convert plusConst hq 1 using 2 with word
        cases query word <;> decide
      | true =>
        convert hq using 2 with word
        cases query word <;> decide
    convert mulBound hp hlit using 2 with word
    simp only [runEq]
    change (if _ ∧ query word = query anchor then _ else _) = _
    split_ifs <;> simp_all

end PEqualNP.Outside.L_lib_611

open PEqualNP.Outside.L_lib_611

theorem PEqualNP.Outside.L_lib_611 : (∀ (m r d : Nat),
  let V := Fin m × Fin r
  let W := V → Bool
  let Symbol := Fin r → Bool
  let deg := fun (b : Nat) (f : W → Bool) =>
    ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ b) ∧ ∀ word,
      f word = (((terms.filter (fun mon => ∀ v ∈ mon, word v = true)).card % 2) == 1)
  let run := fun (ask : Nat → Nat → W → Bool) (len : Nat) (x : W) =>
    (List.range len).foldl (fun h step => h + ((ask step h x).toNat <<< step)) 0
  ∀ (ask : Nat → Nat → W → Bool) (anchor : W) (j : Nat), j ≤ d →
    let pathCode := run ask j anchor
    let cell := (Finset.univ : Finset W).filter (fun sample => run ask j sample = pathCode)
    let leaves := cell.image (run ask d)
    ∀ B : Fin j → Nat, (∀ t, deg (B t) (ask t.val (run ask t.val anchor))) →
      ∃ U : Finset V, U.card ≤ ∑ t : Fin j, B t ∧
        ∀ (L : Nat) (bad : Nat → Fin L → Fin m → Symbol),
          let gone := U.image Prod.fst
          let outside := (Finset.univ : Finset W).filter (fun w =>
            ∀ h ∈ leaves, ∀ a, ∃ i, i ∉ gone ∧ (fun v => w (i,v)) = bad h a i)
          let errors := cell.filter (fun input => ∀ a, ∃ i,
            (fun v => input (i,v)) = bad (run ask d input) a i)
          outside.card ≤ 2^U.card * errors.card) := by
  classical
  intro m r d V W Symbol deg run ask anchor j _ pathCode cell leaves bounds hdeg
  have hp := pathBound ask anchor j bounds (by
    intro idx
    obtain ⟨terms, hcard, hval⟩ := hdeg idx
    exact inputBound terms hcard hval)
  obtain ⟨free, hsize, hface⟩ := hasFace hp anchor (by simp)
  refine ⟨free, hsize, ?_⟩
  intro len bad gone outside errors
  choose repair hhit hsame using hface
  have hcell (word : W) : repair word ∈ cell := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hh := hhit word
    by_contra h
    exact hh (if_neg h)
  have herr (word : W) (hw : word ∈ outside) : repair word ∈ errors := by
    apply Finset.mem_filter.mpr
    refine ⟨hcell word, ?_⟩
    intro item
    have hleaf : run ask d (repair word) ∈ leaves := Finset.mem_image_of_mem _ (hcell word)
    obtain ⟨idx, hidx, hblock⟩ := (Finset.mem_filter.mp hw).2 _ hleaf item
    refine ⟨idx, ?_⟩
    rw [← hblock]
    funext col
    exact hsame word (idx, col) (fun hm => hidx (Finset.mem_image_of_mem Prod.fst hm))
  let encode := fun word : W => ((fun v : free => word v.val), repair word)
  have hmap : Set.MapsTo encode (outside : Set W)
      ((Finset.univ (α := free → Bool) ×ˢ errors : Finset _) : Set _) := by
    intro word hw
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, herr word hw⟩
  have hinj : (outside : Set W).InjOn encode := by
    intro left _ right _ hpair
    funext v
    by_cases hv : v ∈ free
    · exact congrFun (congrArg Prod.fst hpair) ⟨v, hv⟩
    · exact (hsame left v hv).symm.trans ((congrFun (congrArg Prod.snd hpair) v).trans (hsame right v hv))
  simpa using Finset.card_le_card_of_injOn encode hmap hinj
