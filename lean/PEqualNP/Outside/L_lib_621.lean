import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_621

namespace L621Scratch
noncomputable section

local instance instClassicalDecidable (p : Prop) : Decidable p := Classical.propDecidable p

lemma even_card_involutive_no_fixed {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → α) (hf : Function.Involutive f)
    (hclosed : ∀ x ∈ s, f x ∈ s) (hfree : ∀ x ∈ s, f x ≠ x) : Even s.card := by
  classical
  let P : ℕ → Prop := fun n => ∀ s : Finset α, s.card = n →
    (∀ x ∈ s, f x ∈ s) → (∀ x ∈ s, f x ≠ x) → Even s.card
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro t ht htc htf
      by_cases hempty : t = ∅
      · simp [hempty]
      · have hne : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
        obtain ⟨a, ha⟩ := hne
        let b := f a
        have hb : b ∈ t := htc a ha
        have hba : b ≠ a := htf a ha
        let u := (t.erase a).erase b
        have hua : a ∉ u := by simp [u]
        have hub : b ∉ u := by simp [u]
        have huc : ∀ x ∈ u, f x ∈ u := by
          intro x hx
          have hxt : x ∈ t := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2
          have hfx : f x ∈ t := htc x hxt
          have hfx_ne_a : f x ≠ a := by
            intro heq
            have : x = b := by calc
              x = f (f x) := (hf x).symm
              _ = f a := by rw [heq]
              _ = b := rfl
            exact (Finset.mem_erase.mp hx).1 this
          have hfx_ne_b : f x ≠ b := by
            intro heq
            have : x = a := by calc
              x = f (f x) := (hf x).symm
              _ = f b := by rw [heq]
              _ = a := hf a
            exact (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1 this
          exact Finset.mem_erase.mpr ⟨hfx_ne_b, Finset.mem_erase.mpr ⟨hfx_ne_a, hfx⟩⟩
        have huf : ∀ x ∈ u, f x ≠ x := by
          intro x hx
          exact htf x ((Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2)
        have hb' : b ∈ t.erase a := Finset.mem_erase.mpr ⟨hba, hb⟩
        have hucard : u.card + 2 = n := by
          have hu1 : ((t.erase a).erase b).card + 1 = (t.erase a).card :=
            Finset.card_erase_add_one hb'
          have ha1 : (t.erase a).card + 1 = t.card := Finset.card_erase_add_one ha
          rw [← ht]
          dsimp [u]
          omega
        have htlt : u.card < n := by omega
        have heu : Even u.card := ih u.card htlt u rfl huc huf
        have htcard : t.card = u.card + 2 := by omega
        rw [htcard]
        rcases heu with ⟨m, hm⟩
        refine ⟨m+1, ?_⟩
        omega
  simpa [P] using hP s.card s rfl hclosed hfree


lemma filter_card_mod_two_eq_fixed {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → α) (hf : Function.Involutive f)
    (hclosed : ∀ x ∈ s, f x ∈ s)
    (P : α → Prop) [DecidablePred P]
    (hP : ∀ x, P (f x) ↔ P x) :
    (s.filter P).card % 2 = (s.filter (fun x => P x ∧ f x = x)).card % 2 := by
  classical
  let q := s.filter P
  let fixed := q.filter (fun x => f x = x)
  let moving := q.filter (fun x => f x ≠ x)
  have hqclosed : ∀ x ∈ q, f x ∈ q := by
    intro x hx
    have hxs : x ∈ s := (Finset.mem_filter.mp hx).1
    have hpx : P x := (Finset.mem_filter.mp hx).2
    exact Finset.mem_filter.mpr ⟨hclosed x hxs, hP x |>.mpr hpx⟩
  have hmoveclosed : ∀ x ∈ moving, f x ∈ moving := by
    intro x hx
    have hq : x ∈ q := (Finset.mem_filter.mp hx).1
    have hfx : f x ∈ q := hqclosed x hq
    have hneq : f (f x) ≠ f x := by
      intro h
      have : f x = x := ((hf x).symm.trans h).symm
      exact (Finset.mem_filter.mp hx).2 this
    exact Finset.mem_filter.mpr ⟨hfx, hneq⟩
  have hmovefree : ∀ x ∈ moving, f x ≠ x := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have heven : Even moving.card := even_card_involutive_no_fixed moving f hf hmoveclosed hmovefree
  have hsplit : fixed ∪ moving = q := by
    ext x
    simp [fixed, moving, Finset.mem_filter, q]
    tauto
  have hdis : Disjoint fixed moving := by
    rw [Finset.disjoint_left]
    intro x hx hfmem
    exact (Finset.mem_filter.mp hfmem).2 ((Finset.mem_filter.mp hx).2)
  have hcard : q.card = fixed.card + moving.card := by
    rw [← hsplit, Finset.card_union_of_disjoint hdis]
  have hmove_mod : moving.card % 2 = 0 := Nat.mod_eq_zero_of_dvd (Even.two_dvd heven)
  have hmod : q.card % 2 = fixed.card % 2 := by rw [hcard]; omega
  have hfixed : fixed = s.filter (fun x => P x ∧ f x = x) := by
    ext x
    simp [fixed, q, and_assoc, and_left_comm, and_comm]
  rw [hfixed] at hmod
  simpa [q] using hmod


def fixedBy {α : Type*} (fs : List (α → α)) (x : α) : Prop := ∀ f ∈ fs, f x = x

lemma filter_card_mod_two_eq_fixedBy {α : Type*} [DecidableEq α] (s : Finset α)
    (P : α → Prop) [DecidablePred P] (fs : List (α → α))
    (hinv : ∀ f ∈ fs, Function.Involutive f)
    (hclosed : ∀ f ∈ fs, ∀ x ∈ s, f x ∈ s)
    (hPinv : ∀ f ∈ fs, ∀ x, P (f x) ↔ P x)
    (hcomm : ∀ f ∈ fs, ∀ g ∈ fs, ∀ x, f (g x) = g (f x)) :
    (s.filter P).card % 2 = (s.filter (fun x => P x ∧ fixedBy fs x)).card % 2 := by
  classical
  induction fs with
  | nil => simp [fixedBy]
  | cons f fs ih =>
    have htailInv : ∀ g ∈ fs, Function.Involutive g := by
      intro g hg
      exact hinv g (by simp [hg])
    have htailClosed : ∀ g ∈ fs, ∀ x ∈ s, g x ∈ s := by
      intro g hg x hx
      exact hclosed g (by simp [hg]) x hx
    have htailP : ∀ g ∈ fs, ∀ x, P (g x) ↔ P x := by
      intro g hg x
      exact hPinv g (by simp [hg]) x
    have htailComm : ∀ g ∈ fs, ∀ h ∈ fs, ∀ x, g (h x) = h (g x) := by
      intro g hg h hh x
      exact hcomm g (by simp [hg]) h (by simp [hh]) x
    have htailParity := ih htailInv htailClosed htailP htailComm
    have hPredInv : ∀ x, (P (f x) ∧ fixedBy fs (f x)) ↔ (P x ∧ fixedBy fs x) := by
      intro x
      constructor
      · rintro ⟨hpx, hfix⟩
        refine ⟨(hPinv f (by simp) x).mp hpx, ?_⟩
        intro g hg
        have hfx := hfix g hg
        have hcommx := hcomm f (by simp) g (by simp [hg]) x
        have hfg : f (g x) = f x := by rw [hcommx, hfx]
        have hcancel := congrArg f hfg
        rw [hinv f (by simp) (g x)] at hcancel
        rw [hinv f (by simp) x] at hcancel
        exact hcancel
      · rintro ⟨hpx, hfix⟩
        refine ⟨(hPinv f (by simp) x).mpr hpx, ?_⟩
        intro g hg
        have hcommx := hcomm f (by simp) g (by simp [hg]) x
        calc
          g (f x) = f (g x) := hcommx.symm
          _ = f x := by rw [hfix g hg]
    have hstep := filter_card_mod_two_eq_fixed s f (hinv f (by simp))
      (hclosed f (by simp)) (fun x => P x ∧ fixedBy fs x) hPredInv
    calc
      (s.filter P).card % 2 = (s.filter (fun x => P x ∧ fixedBy fs x)).card % 2 := htailParity
      _ = (s.filter (fun x => P x ∧ fixedBy fs x ∧ f x = x)).card % 2 := by
        simpa [and_assoc] using hstep
      _ = (s.filter (fun x => P x ∧ fixedBy (f :: fs) x)).card % 2 := by
        apply congrArg (fun q : Finset α => q.card % 2)
        ext x
        simp [fixedBy, and_assoc, and_left_comm, and_comm]

end
end L621Scratch


namespace L621Action
open L621Scratch

abbrev Site (n : ℕ) := Fin n
abbrev Slot (n r : ℕ) := Fin r × Finset (Fin n)

def flipSet {n : ℕ} (j : Fin n) (X : Finset (Fin n)) : Finset (Fin n) :=
  if j ∈ X then X.erase j else insert j X

lemma flipSet_involutive {n : ℕ} (j : Fin n) : Function.Involutive (flipSet j) := by
  intro X
  ext x
  by_cases hxj : x = j <;> by_cases hj : j ∈ X <;> simp [flipSet, hxj, hj]

lemma flipSet_mem {n : ℕ} (j x : Fin n) (X : Finset (Fin n)) :
    x ∈ flipSet j X ↔ (x ∈ X ∧ x ≠ j) ∨ (x = j ∧ j ∉ X) := by
  by_cases hj : j ∈ X
  · by_cases hxj : x = j
    · subst x
      simp [flipSet, hj]
    · simp [flipSet, hj, hxj]
  · by_cases hxj : x = j
    · subst x
      simp [flipSet, hj]
    · simp [flipSet, hj, hxj]

lemma flipSet_inter_of_not_mem {n : ℕ} (j : Fin n) (X U : Finset (Fin n))
    (hju : j ∉ U) : flipSet j X ∩ U = X ∩ U := by
  ext x
  by_cases hxj : x = j
  · subst x
    simp [flipSet_mem, hju]
  · simp [flipSet_mem, hxj]

lemma flipSet_subset {n : ℕ} (j : Fin n) (X S : Finset (Fin n))
    (hXS : X ⊆ S) (hjS : j ∈ S) : flipSet j X ⊆ S := by
  intro x hx
  rcases (flipSet_mem j x X).mp hx with ⟨hxX, _⟩ | ⟨rfl, _⟩
  · exact hXS hxX
  · exact hjS

def flipSlot {n r : ℕ} (scope : Fin r → Finset (Fin n)) (j : Fin n) (s : Slot n r) : Slot n r :=
  (s.1, if j ∈ scope s.1 then flipSet j s.2 else s.2)

lemma flipSlot_involutive {n r : ℕ} (scope : Fin r → Finset (Fin n)) (j : Fin n) :
    Function.Involutive (flipSlot scope j) := by
  intro s
  by_cases h : j ∈ scope s.1
  · simp only [flipSlot, if_pos h]
    rw [flipSet_involutive j s.2]
  · simp [flipSlot, h]

lemma flipSlot_inter {n r : ℕ} (scope : Fin r → Finset (Fin n)) (j : Fin n)
    (U : Finset (Fin n)) (hju : j ∉ U) (s : Slot n r) :
    (flipSlot scope j s).1 = s.1 ∧ (flipSlot scope j s).2 ∩ U = s.2 ∩ U := by
  simp only [flipSlot]
  split
  · constructor
    · trivial
    · exact flipSet_inter_of_not_mem j s.2 U hju
  · constructor
    · trivial
    · rfl

lemma flipSlot_preserves_scope {n r : ℕ} (scope : Fin r → Finset (Fin n)) (j : Fin n)
    (s : Slot n r) (hs : s.2 ⊆ scope s.1) : (flipSlot scope j s).2 ⊆ scope s.1 := by
  simp only [flipSlot]
  split
  · exact flipSet_subset j s.2 (scope s.1) hs ‹j ∈ scope s.1›
  · exact hs


def project {n r : ℕ} (U : Finset (Fin n)) (s : Slot n r) : Slot n r :=
  (s.1, s.2 ∩ U)

def slots {n r : ℕ} (scope : Fin r → Finset (Fin n)) (U : Finset (Fin n)) : Finset (Slot n r) :=
  Finset.univ.filter (fun s => s.2 ⊆ scope s.1 ∩ U)

def liftTable {n r : ℕ} (scope : Fin r → Finset (Fin n)) (U : Finset (Fin n))
    (A : Finset (Slot n r)) : Finset (Slot n r) :=
  (slots scope (Finset.univ : Finset (Fin n))).filter (fun s => project U s ∈ A)

lemma mem_liftTable_iff {n r : ℕ} (scope : Fin r → Finset (Fin n)) (U : Finset (Fin n))
    (A : Finset (Slot n r)) (s : Slot n r) :
    s ∈ liftTable scope U A ↔ s.2 ⊆ scope s.1 ∧ project U s ∈ A := by
  simp [liftTable, slots, project, Finset.subset_inter_iff]

lemma flipSlot_mem_liftTable {n r : ℕ} (scope : Fin r → Finset (Fin n))
    (U : Finset (Fin n)) (A : Finset (Slot n r)) (j : Fin n) (hju : j ∉ U)
    (s : Slot n r) (hs : s ∈ liftTable scope U A) :
    flipSlot scope j s ∈ liftTable scope U A := by
  rw [mem_liftTable_iff] at hs ⊢
  rcases hs with ⟨hscope, hproj⟩
  exact ⟨flipSlot_preserves_scope scope j s hscope, by
    have h := flipSlot_inter scope j U hju s
    rcases h with ⟨hrow, hpat⟩
    simpa [project, hrow, hpat] using hproj⟩

def flipTable {n r : ℕ} (scope : Fin r → Finset (Fin n)) (j : Fin n)
    (T : Finset (Slot n r)) : Finset (Slot n r) := T.image (flipSlot scope j)

lemma flipTable_involutive {n r : ℕ} (scope : Fin r → Finset (Fin n)) (j : Fin n) :
    Function.Involutive (flipTable scope j) := by
  classical
  intro T
  rw [flipTable, flipTable, Finset.image_image]
  change Finset.image (flipSlot scope j ∘ flipSlot scope j) T = T
  ext s
  simp [flipSlot_involutive]

lemma flipTable_preserves_subset_lift {n r : ℕ} (scope : Fin r → Finset (Fin n))
    (U : Finset (Fin n)) (A T : Finset (Slot n r)) (j : Fin n) (hju : j ∉ U)
    (hT : T ⊆ liftTable scope U A) : flipTable scope j T ⊆ liftTable scope U A := by
  intro s hs
  rcases Finset.mem_image.mp hs with ⟨t, ht, rfl⟩
  exact flipSlot_mem_liftTable scope U A j hju t (hT ht)


lemma mem_flipTable_iff {n r : ℕ} (scope : Fin r → Finset (Fin n)) (j : Fin n)
    (T : Finset (Slot n r)) (s : Slot n r) :
    s ∈ flipTable scope j T ↔ flipSlot scope j s ∈ T := by
  constructor
  · intro hs
    rcases Finset.mem_image.mp hs with ⟨t, ht, hts⟩
    have heq : t = flipSlot scope j s := by
      calc
        t = flipSlot scope j (flipSlot scope j t) := (flipSlot_involutive scope j t).symm
        _ = flipSlot scope j s := by rw [hts]
    simpa [heq] using ht
  · intro hs
    refine Finset.mem_image.mpr ⟨flipSlot scope j s, hs, ?_⟩
    exact flipSlot_involutive scope j s

lemma flipTable_eq_iff {n r : ℕ} (scope : Fin r → Finset (Fin n)) (j : Fin n)
    (T : Finset (Slot n r)) :
    flipTable scope j T = T ↔ ∀ s, s ∈ T ↔ flipSlot scope j s ∈ T := by
  constructor
  · intro h s
    constructor
    · intro hs
      have hs' : s ∈ flipTable scope j T := by simpa [h] using hs
      exact (mem_flipTable_iff scope j T s).mp hs'
    · intro hs
      have hs' : flipSlot scope j s ∈ flipTable scope j T := by simpa [h] using hs
      have hh := (mem_flipTable_iff scope j T (flipSlot scope j s)).mp hs'
      rw [flipSlot_involutive scope j s] at hh
      exact hh
  · intro h
    ext s
    rw [mem_flipTable_iff, h s]


lemma symmDiff_flipSet_erase {n : ℕ} (j : Fin n) (X Y : Finset (Fin n))
    (hj : j ∈ symmDiff X Y) :
    symmDiff (flipSet j X) Y = (symmDiff X Y).erase j := by
  ext x
  by_cases hx : x = j
  · subst x
    have hxy : (j ∈ X ∧ j ∉ Y) ∨ (j ∈ Y ∧ j ∉ X) := Finset.mem_symmDiff.mp hj
    rcases hxy with ⟨hxX, hxY⟩ | ⟨hxY, hxX⟩ <;> simp [Finset.mem_symmDiff, flipSet, hxX, hxY]
  · simp [Finset.mem_symmDiff, flipSet_mem, hx]


lemma fiber_closure_of_flip_closed {n r : ℕ} (scope : Fin r → Finset (Fin n))
    (U : Finset (Fin n)) (T : Finset (Slot n r))
    (hstable : ∀ t ∈ T, ∀ j, j ∉ U → j ∈ scope t.1 → flipSlot scope j t ∈ T)
    (s t : Slot n r) (hscope : s.2 ⊆ scope s.1) (htscope : t.2 ⊆ scope t.1)
    (hrow : s.1 = t.1) (hproj : s.2 ∩ U = t.2 ∩ U) (ht : t ∈ T) : s ∈ T := by
  classical
  let P : ℕ → Prop := fun m => ∀ s t : Slot n r,
    (symmDiff s.2 t.2).card = m → s.2 ⊆ scope s.1 → t.2 ⊆ scope t.1 →
    s.1 = t.1 → s.2 ∩ U = t.2 ∩ U → t ∈ T → s ∈ T
  have hP : ∀ m, P m := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro x y hcard hxscope hyscope hxy hprojxy hyT
      let D := symmDiff x.2 y.2
      by_cases hD : D = ∅
      · have hpatterns : x.2 = y.2 := (Finset.symmDiff_eq_empty).mp hD
        have hxy' : x = y := by cases x; cases y; simp_all
        simpa [hxy'] using hyT
      · have hDne : D.Nonempty := Finset.nonempty_iff_ne_empty.mpr hD
        obtain ⟨j, hjD⟩ := hDne
        have hjcases := Finset.mem_symmDiff.mp (show j ∈ symmDiff x.2 y.2 from by simpa [D] using hjD)
        have hju : j ∉ U := by
          intro hjU
          rcases hjcases with ⟨hjx, hjny⟩ | ⟨hjy, hjnx⟩
          · have hmem : j ∈ y.2 ∩ U := by rw [← hprojxy]; exact Finset.mem_inter.mpr ⟨hjx, hjU⟩
            exact hjny (Finset.mem_inter.mp hmem).1
          · have hmem : j ∈ x.2 ∩ U := by rw [hprojxy]; exact Finset.mem_inter.mpr ⟨hjy, hjU⟩
            exact hjnx (Finset.mem_inter.mp hmem).1
        have hjScope : j ∈ scope y.1 := by
          rcases hjcases with ⟨hjx, hjny⟩ | ⟨hjy, hjnx⟩
          · have : j ∈ scope x.1 := hxscope hjx
            simpa [hxy] using this
          · exact hyscope hjy
        let y' := flipSlot scope j y
        have hy'T : y' ∈ T := hstable y hyT j hju hjScope
        have hrow' : x.1 = y'.1 := by simpa [y', flipSlot] using hxy
        have hproj' : x.2 ∩ U = y'.2 ∩ U := by
          have hi := flipSlot_inter scope j U hju y
          simpa [y'] using hprojxy.trans hi.2.symm
        have hyscope' : y'.2 ⊆ scope y'.1 := by
          simpa [y', flipSlot] using flipSlot_preserves_scope scope j y hyscope
        have hj' : j ∈ symmDiff y.2 x.2 := by
          simpa [Finset.mem_symmDiff, or_comm, and_comm] using hjcases
        have hD' : (symmDiff x.2 y'.2).card < m := by
          have hEq : symmDiff y'.2 x.2 = (symmDiff y.2 x.2).erase j := by
            simpa [y', flipSlot, hjScope] using symmDiff_flipSet_erase j y.2 x.2 hj'
          have hcard' : (symmDiff y'.2 x.2).card = (symmDiff y.2 x.2).card - 1 := by
            rw [hEq, Finset.card_erase_of_mem hj']
          have hcomm : (symmDiff y.2 x.2).card = m := by
            rw [symmDiff_comm, hcard]
          rw [hcomm] at hcard'
          rw [symmDiff_comm]
          rw [hcard']
          have hmpos : 0 < m := by
            have hp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hD)
            rw [hcard] at hp
            exact hp
          omega
        exact ih (symmDiff x.2 y'.2).card hD' x y' rfl hxscope hyscope' hrow' hproj' hy'T
  exact hP (symmDiff s.2 t.2).card s t rfl hscope htscope hrow hproj ht


def baseTable {n r : ℕ} (U : Finset (Fin n)) (T : Finset (Slot n r)) : Finset (Slot n r) :=
  T.image (project U)

lemma baseTable_subset {n r : ℕ} (scope : Fin r → Finset (Fin n)) (U : Finset (Fin n))
    (A T : Finset (Slot n r)) (hT : T ⊆ liftTable scope U A) : baseTable U T ⊆ A := by
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨s, hs, rfl⟩
  exact (mem_liftTable_iff scope U A s).mp (hT hs) |>.2

lemma fixed_subtable_is_lift {n r : ℕ} (scope : Fin r → Finset (Fin n))
    (U : Finset (Fin n)) (A T : Finset (Slot n r))
    (hT : T ⊆ liftTable scope U A)
    (hstable : ∀ t ∈ T, ∀ j, j ∉ U → j ∈ scope t.1 → flipSlot scope j t ∈ T) :
    T = liftTable scope U (baseTable U T) := by
  apply Finset.Subset.antisymm
  · intro s hs
    apply mem_liftTable_iff scope U (baseTable U T) s |>.2
    rcases (mem_liftTable_iff scope U A s).mp (hT hs) with ⟨hscope, _⟩
    exact ⟨hscope, Finset.mem_image.mpr ⟨s, hs, rfl⟩⟩
  · intro s hs
    rcases (mem_liftTable_iff scope U (baseTable U T) s).mp hs with ⟨hscope, hproj⟩
    rcases Finset.mem_image.mp hproj with ⟨t, ht, hEq⟩
    rcases (mem_liftTable_iff scope U A t).mp (hT ht) with ⟨htscope, _⟩
    have hrow : s.1 = t.1 := (congrArg Prod.fst hEq).symm
    have hpat : s.2 ∩ U = t.2 ∩ U := (congrArg Prod.snd hEq).symm
    exact fiber_closure_of_flip_closed scope U T hstable s t hscope htscope hrow hpat ht

lemma fixed_lift_subtable {n r : ℕ} (scope : Fin r → Finset (Fin n))
    (U : Finset (Fin n)) (A : Finset (Slot n r)) (j : Fin n) (hju : j ∉ U) :
    ∀ t ∈ liftTable scope U A, flipSlot scope j t ∈ liftTable scope U A := by
  intro t ht
  exact flipSlot_mem_liftTable scope U A j hju t ht


lemma flipSet_commute {n : ℕ} (j k : Fin n) (hjk : j ≠ k) (X : Finset (Fin n)) :
    flipSet j (flipSet k X) = flipSet k (flipSet j X) := by
  by_cases hj : j ∈ X <;> by_cases hk : k ∈ X <;> ext x <;>
    by_cases hxj : x = j <;> by_cases hxk : x = k <;>
    simp [flipSet, hj, hk, hxj, hxk, hjk, Ne.symm hjk]

lemma flipSlot_commute {n r : ℕ} (scope : Fin r → Finset (Fin n))
    (j k : Fin n) (hjk : j ≠ k) (s : Slot n r) :
    flipSlot scope j (flipSlot scope k s) = flipSlot scope k (flipSlot scope j s) := by
  by_cases hj : j ∈ scope s.1 <;> by_cases hk : k ∈ scope s.1
  · simp [flipSlot, hj, hk, flipSet_commute j k hjk]
  · simp [flipSlot, hj, hk]
  · simp [flipSlot, hj, hk]
  · simp [flipSlot, hj, hk]

lemma flipTable_commute {n r : ℕ} (scope : Fin r → Finset (Fin n))
    (j k : Fin n) (hjk : j ≠ k) (T : Finset (Slot n r)) :
    flipTable scope j (flipTable scope k T) = flipTable scope k (flipTable scope j T) := by
  classical
  rw [flipTable, flipTable, Finset.image_image, flipTable, flipTable, Finset.image_image]
  congr 1
  funext s
  exact flipSlot_commute scope j k hjk s


def passes {n r : ℕ} (scope : Fin r → Finset (Fin n)) (T : Finset (Slot n r))
    (x : Finset (Fin n)) : Prop := ∀ i, (i, x ∩ scope i) ∈ T

noncomputable def totalWords {n r : ℕ} (V : Finset (Fin n)) (scope : Fin r → Finset (Fin n))
    (T : Finset (Slot n r)) : ℕ := by
  classical
  exact (V.powerset.filter (passes scope T)).card

lemma flipSet_inter_of_mem {n : ℕ} (j : Fin n) (X W : Finset (Fin n))
    (hjW : j ∈ W) : flipSet j X ∩ W = flipSet j (X ∩ W) := by
  ext x
  by_cases hxj : x = j
  · subst x
    simp [flipSet_mem, hjW]
  · simp [flipSet_mem, hxj]

lemma flipSlot_wordPattern {n r : ℕ} (scope : Fin r → Finset (Fin n))
    (j : Fin n) (x : Finset (Fin n)) (i : Fin r) :
    flipSlot scope j (i, x ∩ scope i) = (i, flipSet j x ∩ scope i) := by
  by_cases hj : j ∈ scope i
  · simp [flipSlot, hj, flipSet_inter_of_mem j x (scope i) hj]
  · simp [flipSlot, hj, flipSet_inter_of_not_mem j x (scope i) hj]

lemma passes_flipTable_iff {n r : ℕ} (scope : Fin r → Finset (Fin n)) (j : Fin n)
    (T : Finset (Slot n r)) (x : Finset (Fin n)) :
    passes scope (flipTable scope j T) x ↔ passes scope T (flipSet j x) := by
  constructor
  · intro hx i
    have h := hx i
    rw [mem_flipTable_iff] at h
    rw [flipSlot_wordPattern] at h
    exact h
  · intro hx i
    have h : (i, flipSet j x ∩ scope i) ∈ T := hx i
    rw [← flipSlot_wordPattern scope j x i] at h
    exact (mem_flipTable_iff scope j T (i, x ∩ scope i)).mpr h

lemma totalWords_flipTable {n r : ℕ} (scope : Fin r → Finset (Fin n))
    (j : Fin n) (T : Finset (Slot n r)) :
    totalWords Finset.univ scope (flipTable scope j T) = totalWords Finset.univ scope T := by
  classical
  unfold totalWords
  apply Finset.card_bij (fun x _ => flipSet j x)
  · intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxsub, hpass⟩
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_powerset.mpr (Finset.subset_univ _)
    · exact (passes_flipTable_iff scope j T x).mp hpass
  · intro x hx y hy hxy
    have h := congrArg (flipSet j) hxy
    rw [flipSet_involutive j x, flipSet_involutive j y] at h
    exact h
  · intro y hy
    rcases Finset.mem_filter.mp hy with ⟨hysub, hpass⟩
    refine ⟨flipSet j y, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_powerset.mpr (Finset.subset_univ _)
      · have hback := (passes_flipTable_iff scope j T (flipSet j y)).mpr ?_
        · exact hback
        · rw [flipSet_involutive j y]
          exact hpass
    · exact flipSet_involutive j y


lemma inter_scope_U_eq (n : ℕ) (U S x : Finset (Fin n)) :
    (x ∩ S) ∩ U = (x ∩ U) ∩ S := by
  ext j
  simp [and_assoc, and_left_comm, and_comm]

lemma passes_liftTable_iff {n r : ℕ} (scope : Fin r → Finset (Fin n))
    (U : Finset (Fin n)) (B : Finset (Slot n r)) (x : Finset (Fin n)) :
    passes scope (liftTable scope U B) x ↔ passes scope B (x ∩ U) := by
  constructor
  · intro h i
    have hi := (mem_liftTable_iff scope U B (i, x ∩ scope i)).mp (h i)
    rcases hi with ⟨_, hp⟩
    have heq : project U (i, x ∩ scope i) = (i, (x ∩ U) ∩ scope i) := by
      apply Prod.ext
      · rfl
      · exact inter_scope_U_eq n U (scope i) x
    simpa [heq] using hp
  · intro h i
    apply (mem_liftTable_iff scope U B (i, x ∩ scope i)).mpr
    refine ⟨Finset.inter_subset_right, ?_⟩
    have hi := h i
    have heq : project U (i, x ∩ scope i) = (i, (x ∩ U) ∩ scope i) := by
      apply Prod.ext
      · rfl
      · exact inter_scope_U_eq n U (scope i) x
    rw [heq]
    exact hi

lemma totalWords_liftTable {n r : ℕ} (scope : Fin r → Finset (Fin n))
    (U : Finset (Fin n)) (B : Finset (Slot n r)) :
    totalWords Finset.univ scope (liftTable scope U B) =
      2^(n-U.card) * totalWords U scope B := by
  classical
  let all : Finset (Fin n) := Finset.univ
  let free := all \ U
  let source := all.powerset.filter (passes scope (liftTable scope U B))
  let target := (U.powerset.filter (passes scope B)) ×ˢ free.powerset
  have hbij : source.card = target.card := by
    apply Finset.card_bij (fun x _ => (x ∩ U, x \ U))
    · intro x hx
      rcases Finset.mem_filter.mp hx with ⟨hsub, hpass⟩
      apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_powerset.mpr Finset.inter_subset_right
        · simpa using (passes_liftTable_iff scope U B x).mp hpass
      · apply Finset.mem_powerset.mpr
        intro z hz
        have hzx : z ∈ x := (Finset.mem_sdiff.mp hz).1
        have hzU : z ∉ U := (Finset.mem_sdiff.mp hz).2
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hzU⟩
    · intro x hx y hy hxy
      have hfst := congrArg Prod.fst hxy
      have hsnd := congrArg Prod.snd hxy
      change x ∩ U = y ∩ U at hfst
      change x \ U = y \ U at hsnd
      have hxsplit : (x ∩ U) ∪ (x \ U) = x := by
        ext z
        simp [Finset.mem_sdiff, or_and_right, and_assoc, and_left_comm, and_comm]
      have hysplit : (y ∩ U) ∪ (y \ U) = y := by
        ext z
        simp [Finset.mem_sdiff, or_and_right, and_assoc, and_left_comm, and_comm]
      calc
        x = (x ∩ U) ∪ (x \ U) := hxsplit.symm
        _ = (y ∩ U) ∪ (y \ U) := by rw [hfst, hsnd]
        _ = y := hysplit
    · intro y hy
      rcases Finset.mem_product.mp hy with ⟨ha, hb⟩
      rcases Finset.mem_filter.mp ha with ⟨haU, hpass⟩
      have haSub : y.1 ⊆ U := Finset.mem_powerset.mp haU
      have hbFree : y.2 ⊆ free := Finset.mem_powerset.mp hb
      let x := y.1 ∪ y.2
      have hxsub : x ⊆ all := by
        intro z hz
        rcases Finset.mem_union.mp hz with hza | hzb
        · exact Finset.mem_univ z
        · exact Finset.mem_univ z
      have hxU : x ∩ U = y.1 := by
        ext z
        constructor
        · intro hz
          rcases Finset.mem_inter.mp hz with ⟨hzx, hzU⟩
          rcases Finset.mem_union.mp (by simpa [x] using hzx) with hza | hzb
          · exact hza
          · have hzfree : z ∈ free := hbFree hzb
            exact False.elim ((Finset.mem_sdiff.mp hzfree).2 hzU)
        · intro hza
          exact Finset.mem_inter.mpr ⟨by simp [x, hza], haSub hza⟩
      have hxFree : x \ U = y.2 := by
        ext z
        constructor
        · intro hz
          rcases Finset.mem_sdiff.mp hz with ⟨hzx, hzU⟩
          rcases Finset.mem_union.mp (by simpa [x] using hzx) with hza | hzb
          · exact False.elim (hzU (haSub hza))
          · exact hzb
        · intro hzb
          have hzfree : z ∈ free := hbFree hzb
          exact Finset.mem_sdiff.mpr ⟨by simp [x, hzb], (Finset.mem_sdiff.mp hzfree).2⟩
      have hpassx : passes scope (liftTable scope U B) x := by
        rw [passes_liftTable_iff]
        simpa [hxU] using hpass
      refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (by simpa [all] using hxsub), hpassx⟩, ?_⟩
      simp [x, hxU, hxFree]
  have hcard : source.card = (U.powerset.filter (passes scope B)).card * free.powerset.card := by
    simpa [target, Finset.card_product] using hbij
  have hfree : free.card = n-U.card := by
    dsimp [free, all]
    rw [Finset.card_sdiff]
    simp
  rw [totalWords, totalWords]
  rw [hcard]
  rw [Finset.card_powerset, hfree]
  simp [Nat.mul_comm]


noncomputable def freeSites {n : ℕ} (U : Finset (Fin n)) : List (Fin n) :=
  (Finset.univ.filter (fun j => j ∉ U)).toList

noncomputable def freeActions {n r : ℕ} (scope : Fin r → Finset (Fin n)) (U : Finset (Fin n)) :
    List (Finset (Slot n r) → Finset (Slot n r)) :=
  (freeSites U).map (fun j => flipTable scope j)

lemma mem_freeSites {n : ℕ} (U : Finset (Fin n)) (j : Fin n) :
    j ∈ freeSites U ↔ j ∉ U := by
  simp [freeSites]

lemma freeActions_involutive {n r : ℕ} (scope : Fin r → Finset (Fin n)) (U : Finset (Fin n)) :
    ∀ f ∈ freeActions scope U, Function.Involutive f := by
  intro f hf T
  rcases List.mem_map.mp hf with ⟨j, hj, rfl⟩
  exact flipTable_involutive scope j T

lemma freeActions_commute {n r : ℕ} (scope : Fin r → Finset (Fin n)) (U : Finset (Fin n)) :
    ∀ f ∈ freeActions scope U, ∀ g ∈ freeActions scope U, ∀ T,
      f (g T) = g (f T) := by
  intro f hf g hg T
  rcases List.mem_map.mp hf with ⟨j, hj, rfl⟩
  rcases List.mem_map.mp hg with ⟨k, hk, rfl⟩
  by_cases hjk : j = k
  · subst k
    rfl
  · exact flipTable_commute scope j k hjk T

lemma freeActions_closed_powerset {n r : ℕ} (scope : Fin r → Finset (Fin n))
    (U : Finset (Fin n)) (A : Finset (Slot n r)) :
    ∀ f ∈ freeActions scope U, ∀ T ∈ (liftTable scope U A).powerset,
      f T ∈ (liftTable scope U A).powerset := by
  intro f hf T hT
  rcases List.mem_map.mp hf with ⟨j, hj, rfl⟩
  have hju : j ∉ U := (mem_freeSites U j).mp hj
  exact Finset.mem_powerset.mpr
    (flipTable_preserves_subset_lift scope U A T j hju (Finset.mem_powerset.mp hT))

lemma freeActions_pred_invariant {n r : ℕ} (scope : Fin r → Finset (Fin n))
    (U : Finset (Fin n)) (A : Finset (Slot n r)) (g : ℕ → Bool) :
    ∀ f ∈ freeActions scope U, ∀ T,
      g (totalWords Finset.univ scope (f T)) = g (totalWords Finset.univ scope T) := by
  intro f hf T
  rcases List.mem_map.mp hf with ⟨j, hj, rfl⟩
  rw [totalWords_flipTable]

lemma fixedBy_freeActions_iff {n r : ℕ} (scope : Fin r → Finset (Fin n))
    (U : Finset (Fin n)) (T : Finset (Slot n r)) :
    fixedBy (freeActions scope U) T ↔ ∀ j, j ∉ U → flipTable scope j T = T := by
  constructor
  · intro h j hju
    apply h
    apply List.mem_map.mpr
    refine ⟨j, ?_, rfl⟩
    exact (mem_freeSites U j).mpr hju
  · intro h f hf
    rcases List.mem_map.mp hf with ⟨j, hj, rfl⟩
    exact h j ((mem_freeSites U j).mp hj)


lemma liftTable_mono {n r : ℕ} (scope : Fin r → Finset (Fin n)) (U : Finset (Fin n))
    {A B : Finset (Slot n r)} (hBA : B ⊆ A) : liftTable scope U B ⊆ liftTable scope U A := by
  intro s hs
  rcases (mem_liftTable_iff scope U B s).mp hs with ⟨hscope, hp⟩
  exact (mem_liftTable_iff scope U A s).mpr ⟨hscope, hBA hp⟩

lemma baseTable_liftTable {n r : ℕ} (scope : Fin r → Finset (Fin n))
    (U : Finset (Fin n)) (B : Finset (Slot n r))
    (hB : B ⊆ slots scope U) : baseTable U (liftTable scope U B) = B := by
  apply Finset.Subset.antisymm
  · intro p hp
    rcases Finset.mem_image.mp hp with ⟨s, hs, rfl⟩
    exact (mem_liftTable_iff scope U B s).mp hs |>.2
  · intro p hp
    rcases p with ⟨i, pat⟩
    have hpat : pat ⊆ scope i ∩ U := (Finset.mem_filter.mp (hB hp)).2
    have hpatU : pat ⊆ U := Finset.Subset.trans hpat Finset.inter_subset_right
    have hpatInt : pat ∩ U = pat := by
      ext z
      simp [hpatU]
    have hs : (i, pat) ∈ liftTable scope U B := by
      apply (mem_liftTable_iff scope U B (i, pat)).mpr
      constructor
      · exact Finset.Subset.trans hpat Finset.inter_subset_left
      · have hproj : project U (i, pat) = (i, pat) := by
          apply Prod.ext
          · rfl
          · exact hpatInt
        rw [hproj]
        exact hp
    apply Finset.mem_image.mpr
    have hproj : project U (i, pat) = (i, pat) := by
      apply Prod.ext
      · rfl
      · exact hpatInt
    exact ⟨(i, pat), hs, hproj⟩

lemma coeff_parity_scratch {n r : ℕ} (scope : Fin r → Finset (Fin n))
    (U : Finset (Fin n)) (A : Finset (Slot n r)) (hA : A ⊆ slots scope U)
    (g : ℕ → Bool) :
    ((liftTable scope U A).powerset.filter (fun T => g (totalWords Finset.univ scope T))).card.testBit 0 =
      (A.powerset.filter (fun B => g (2^(n-U.card) * totalWords U scope B))).card.testBit 0 := by
  classical
  let L := liftTable scope U A
  let actions := freeActions scope U
  let P : Finset (Slot n r) → Prop := fun T => g (totalWords Finset.univ scope T)
  let fixed : Finset (Finset (Slot n r)) := L.powerset.filter (fun T => P T ∧ fixedBy actions T)
  let good : Finset (Finset (Slot n r)) := A.powerset.filter (fun B => g (2^(n-U.card) * totalWords U scope B))
  have hPinv : ∀ f ∈ actions, ∀ T, P (f T) ↔ P T := by
    intro f hf T
    change g (totalWords Finset.univ scope (f T)) = true ↔
      g (totalWords Finset.univ scope T) = true
    rw [freeActions_pred_invariant scope U A g f hf T]
  have hpar := filter_card_mod_two_eq_fixedBy L.powerset P actions
    (freeActions_involutive scope U)
    (freeActions_closed_powerset scope U A)
    hPinv
    (freeActions_commute scope U)
  have hbit : (L.powerset.filter P).card.testBit 0 = fixed.card.testBit 0 := by
    rw [Nat.testBit_zero, Nat.testBit_zero, hpar]
  have hbase : fixed.card = good.card := by
    apply Finset.card_bij (fun T _ => baseTable U T)
    · intro T hT
      rcases Finset.mem_filter.mp hT with ⟨hpow, hpred⟩
      have hsub : T ⊆ L := Finset.mem_powerset.mp hpow
      have hallfix := (fixedBy_freeActions_iff scope U T).mp hpred.2
      have hstable : ∀ t ∈ T, ∀ j, j ∉ U → j ∈ scope t.1 → flipSlot scope j t ∈ T := by
        intro t ht j hju hjscope
        have hjfix := hallfix j hju
        exact ((flipTable_eq_iff scope j T).mp hjfix t).mp ht
      have hTL : T = liftTable scope U (baseTable U T) :=
        fixed_subtable_is_lift scope U A T hsub hstable
      have hBA : baseTable U T ⊆ A := baseTable_subset scope U A T hsub
      have htotal : totalWords Finset.univ scope T =
          2^(n-U.card) * totalWords U scope (baseTable U T) := by
        calc
          totalWords Finset.univ scope T =
              totalWords Finset.univ scope (liftTable scope U (baseTable U T)) := congrArg (fun X => totalWords Finset.univ scope X) hTL
          _ = 2^(n-U.card) * totalWords U scope (baseTable U T) :=
              totalWords_liftTable scope U (baseTable U T)
      have hbaseval : P T = (g (2^(n-U.card) * totalWords U scope (baseTable U T)) = true) := by
        dsimp [P]
        rw [htotal]
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr hBA, ?_⟩
      rw [← hbaseval]
      exact hpred.1
    · intro T hT S hS hEq
      rcases Finset.mem_filter.mp hT with ⟨hpowT, hpredT⟩
      rcases Finset.mem_filter.mp hS with ⟨hpowS, hpredS⟩
      have hsubT : T ⊆ L := Finset.mem_powerset.mp hpowT
      have hsubS : S ⊆ L := Finset.mem_powerset.mp hpowS
      have getLift (X : Finset (Slot n r)) (hsub : X ⊆ L)
          (hpred : fixedBy actions X) : X = liftTable scope U (baseTable U X) := by
        have hallfix := (fixedBy_freeActions_iff scope U X).mp hpred
        have hstable : ∀ t ∈ X, ∀ j, j ∉ U → j ∈ scope t.1 → flipSlot scope j t ∈ X := by
          intro t ht j hju hjscope
          exact ((flipTable_eq_iff scope j X).mp (hallfix j hju) t).mp ht
        exact fixed_subtable_is_lift scope U A X hsub hstable
      rw [getLift T hsubT hpredT.2, getLift S hsubS hpredS.2, hEq]
    · intro B hB
      rcases Finset.mem_filter.mp hB with ⟨hpow, hpred⟩
      have hBA : B ⊆ A := Finset.mem_powerset.mp hpow
      have hBU : B ⊆ slots scope U := Finset.Subset.trans hBA hA
      let T := liftTable scope U B
      have hTL : T ⊆ L := liftTable_mono scope U hBA
      have hTpow : T ∈ L.powerset := Finset.mem_powerset.mpr hTL
      have hfixed : fixedBy actions T := by
        apply (fixedBy_freeActions_iff scope U T).mpr
        intro j hju
        apply (flipTable_eq_iff scope j T).mpr
        intro s
        constructor
        · exact flipSlot_mem_liftTable scope U B j hju s
        · intro hs
          have h := flipSlot_mem_liftTable scope U B j hju (flipSlot scope j s) hs
          rw [flipSlot_involutive scope j s] at h
          exact h
      have hpredT : P T := by
        dsimp [P, T]
        rw [totalWords_liftTable]
        exact hpred
      have hbaseT : baseTable U T = B := baseTable_liftTable scope U B hBU
      have hTmem : T ∈ fixed := Finset.mem_filter.mpr ⟨hTpow, ⟨hpredT, hfixed⟩⟩
      refine ⟨T, hTmem, ?_⟩
      exact hbaseT
  rw [hbase] at hbit
  exact hbit


def rawTotal {n r : ℕ} (V : Finset (Fin n))
    (scope : Fin r → Finset (Fin n)) (T : Finset (Slot n r)) : ℕ :=
  (V.powerset.filter (fun x => ∀ i : Fin r, (i, x ∩ scope i) ∈ T)).card

def rawSlots {n r : ℕ} (scope : Fin r → Finset (Fin n)) (U : Finset (Fin n)) :=
  (Finset.univ : Finset (Slot n r)).filter (fun candidate => candidate.2 ⊆ scope candidate.1 ∩ U)

def rawLift {n r : ℕ} (scope : Fin r → Finset (Fin n)) (U : Finset (Fin n))
    (A : Finset (Slot n r)) :=
  (rawSlots scope Finset.univ).filter (fun s => (s.1, s.2 ∩ U) ∈ A)

lemma rawTotal_eq_totalWords {n r : ℕ} (V : Finset (Fin n))
    (scope : Fin r → Finset (Fin n)) (T : Finset (Slot n r)) :
    rawTotal V scope T = totalWords V scope T := by
  classical
  unfold rawTotal totalWords passes
  congr 1
  ext x
  simp

lemma rawLift_eq_liftTable {n r : ℕ} (scope : Fin r → Finset (Fin n))
    (U : Finset (Fin n)) (A : Finset (Slot n r)) : rawLift scope U A = liftTable scope U A := by
  rfl

theorem exact_statement_scratch : (∀ (n r : Nat) (scope : Fin r → Finset (Fin n)),
  let Site := Fin n
  let Slot := Fin r × Finset Site
  let all := (Finset.univ : Finset Site)
  let slots := fun U : Finset Site => (Finset.univ : Finset Slot).filter
    (fun candidate => candidate.2 ⊆ scope candidate.1 ∩ U)
  let total := fun (U : Finset Site) (table : Finset Slot) =>
    (U.powerset.filter (fun x => ∀ i : Fin r, (i, x ∩ scope i) ∈ table)).card
  let coeff := fun (U : Finset Site) (M : Finset Slot) (g : Nat → Bool) =>
    ((M.powerset.filter (fun T => g (total U T))).card).testBit 0
  ∀ (U : Finset Site) (A : Finset Slot), A ⊆ slots U →
    let lift := (slots all).filter (fun s => (s.1, s.2 ∩ U) ∈ A)
    ∀ g : Nat → Bool, coeff all lift g =
      coeff U A (fun c => g (2^(n-U.card)*c)))  := by
  intro n r scope
  dsimp
  intro U A hA g
  let targetLift := ((Finset.univ : Finset (Fin r × Finset (Fin n))).filter
    (fun s => s.2 ⊆ scope s.1 ∩ (Finset.univ : Finset (Fin n)))).filter
    (fun s => (s.1, s.2 ∩ U) ∈ A)
  have hLift : targetLift = liftTable scope U A := by
    ext s
    simp [targetLift, liftTable, slots, project, Finset.subset_inter_iff]
  have hTotal (V : Finset (Fin n)) (T : Finset (Slot n r)) :
      (V.powerset.filter (fun x => ∀ i : Fin r, (i, x ∩ scope i) ∈ T)).card =
        totalWords V scope T := rawTotal_eq_totalWords V scope T
  have hcore := coeff_parity_scratch scope U A hA g
  have hLeftOrig :
      (((((Finset.univ : Finset (Fin r × Finset (Fin n))).filter
          (fun s => s.2 ⊆ scope s.1 ∩ (Finset.univ : Finset (Fin n)))).filter
          (fun s => (s.1, s.2 ∩ U) ∈ A)).powerset.filter
          (fun T => g ((Finset.univ.powerset.filter
            (fun x => ∀ i : Fin r, (i, x ∩ scope i) ∈ T)).card))).card).testBit 0 =
        ((liftTable scope U A).powerset.filter
          (fun T => g (totalWords Finset.univ scope T))).card.testBit 0 := by
    apply congrArg (fun k : ℕ => k.testBit 0)
    apply congrArg Finset.card
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨hsub, hval⟩
      refine ⟨?_, ?_⟩
      · intro s hs
        have hmem := hsub hs
        rcases Finset.mem_filter.mp hmem with ⟨hslots, hproj⟩
        rcases Finset.mem_filter.mp hslots with ⟨_, hpat⟩
        have hscope : s.2 ⊆ scope s.1 := by
          intro x hx
          exact (Finset.mem_inter.mp (hpat hx)).1
        exact (mem_liftTable_iff scope U A s).mpr ⟨hscope, hproj⟩
      · have hEq := congrArg g (hTotal Finset.univ T)
        simpa only [hEq] using hval
    · rintro ⟨hsub, hval⟩
      refine ⟨?_, ?_⟩
      · intro s hs
        rcases (mem_liftTable_iff scope U A s).mp (hsub hs) with ⟨hscope, hproj⟩
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_filter.mpr
          constructor
          · exact Finset.mem_univ s
          · intro x hx
            exact Finset.mem_inter.mpr ⟨hscope hx, Finset.mem_univ x⟩
        · exact hproj
      · have hEq := congrArg g (hTotal Finset.univ T)
        simpa only [← hEq] using hval
  have hRightOrig :
      ((A.powerset.filter (fun B => g (2^(n-U.card) *
        (U.powerset.filter (fun x => ∀ i : Fin r, (i, x ∩ scope i) ∈ B)).card))).card).testBit 0 =
      (A.powerset.filter (fun B => g (2^(n-U.card) * totalWords U scope B))).card.testBit 0 := by
    apply congrArg (fun k : ℕ => k.testBit 0)
    apply congrArg Finset.card
    ext B
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor <;> intro h
    · rcases h with ⟨hsub, hval⟩
      have hEq := congrArg (fun c => g (2^(n-U.card) * c)) (hTotal U B)
      exact ⟨hsub, by simpa only [hEq] using hval⟩
    · rcases h with ⟨hsub, hval⟩
      have hEq := congrArg (fun c => g (2^(n-U.card) * c)) (hTotal U B)
      exact ⟨hsub, by simpa only [← hEq] using hval⟩
  rw [hLeftOrig, hRightOrig]
  exact hcore

end L621Action

end PEqualNP.Outside.L_lib_621

theorem PEqualNP.Outside.L_lib_621 : (∀ (n r : Nat) (scope : Fin r → Finset (Fin n)),
  let Site := Fin n
  let Slot := Fin r × Finset Site
  let all := (Finset.univ : Finset Site)
  let slots := fun U : Finset Site => (Finset.univ : Finset Slot).filter
    (fun candidate => candidate.2 ⊆ scope candidate.1 ∩ U)
  let total := fun (U : Finset Site) (table : Finset Slot) =>
    (U.powerset.filter (fun x => ∀ i : Fin r, (i, x ∩ scope i) ∈ table)).card
  let coeff := fun (U : Finset Site) (M : Finset Slot) (g : Nat → Bool) =>
    ((M.powerset.filter (fun T => g (total U T))).card).testBit 0
  ∀ (U : Finset Site) (A : Finset Slot), A ⊆ slots U →
    let lift := (slots all).filter (fun s => (s.1, s.2 ∩ U) ∈ A)
    ∀ g : Nat → Bool, coeff all lift g =
      coeff U A (fun c => g (2^(n-U.card)*c))) := by
  exact PEqualNP.Outside.L_lib_621.L621Action.exact_statement_scratch
