import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21436

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

private def appendGate (g : Gate) (w : List Bool) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun v g => appendGate g v) w

private theorem preserves (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (appendGate g w)).getD i false = w.getD i false
    rw [ih _ (by simp [appendGate]; omega)]
    exact List.getD_append _ _ _ _ hi

private theorem foldAgrees (gs : List Gate) (safe : ℕ → Prop) (t : ℕ) (w v : List Bool)
    (hlen : w.length = v.length)
    (hstart : ∀ i, safe i → w.getD i false = v.getD i false)
    (hinputs : ∀ j (hj : j < gs.length), safe (w.length + j) → w.length + j ≠ t →
      ∀ i ∈ gs[j].inputs, safe i)
    (hcut : (run gs w).getD t false = (run gs v).getD t false) :
    ∀ i, safe i → (run gs w).getD i false = (run gs v).getD i false := by
  induction gs generalizing w v with
  | nil => exact hstart
  | cons g gs ih =>
    have hw : (appendGate g w).length = w.length + 1 := by simp [appendGate]
    have hv : (appendGate g v).length = v.length + 1 := by simp [appendGate]
    have hlen' : (appendGate g w).length = (appendGate g v).length := by omega
    change ∀ i, safe i →
      (run gs (appendGate g w)).getD i false = (run gs (appendGate g v)).getD i false
    apply ih _ _ hlen' _ _ hcut
    · intro i hi
      rcases lt_trichotomy i w.length with hlt | heq | hgt
      · unfold appendGate
        rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega)]
        exact hstart i hi
      · by_cases ht : i = t
        · subst t
          change (run gs (appendGate g w)).getD i false =
            (run gs (appendGate g v)).getD i false at hcut
          simpa only [preserves gs _ i (by omega : i < (appendGate g w).length),
            preserves gs _ i (by omega : i < (appendGate g v).length)] using hcut
        · have hin : ∀ a ∈ g.inputs, safe a := by
            have hzero := hinputs 0 (by simp) (by simpa [heq] using hi) (by simpa [heq] using ht)
            change ∀ a ∈ g.inputs, safe a at hzero
            exact hzero
          have hm : (g.inputs.map fun a => w.getD a false) =
              (g.inputs.map fun a => v.getD a false) :=
            List.map_congr_left fun a ha => hstart a (hin a ha)
          have hev : (g.op.eval (g.inputs.map fun a => w.getD a false)) =
              (g.op.eval (g.inputs.map fun a => v.getD a false)) := congrArg g.op.eval hm
          conv_lhs => rw [heq]
          conv_rhs => rw [heq, hlen]
          simpa [appendGate, List.getD_eq_getElem?_getD] using hev
      · have hwb : (appendGate g w).length ≤ i := by omega
        have hvb : (appendGate g v).length ≤ i := by omega
        exact (List.getD_eq_default _ _ hwb).trans (List.getD_eq_default _ _ hvb).symm
    · intro j hj hs ht i hi
      have hidx : w.length + (j + 1) = (appendGate g w).length + j := by omega
      exact hinputs (j + 1) (by simp; omega) (hidx ▸ hs) (hidx ▸ ht) i
        (by simpa only [List.getElem_cons_succ] using hi)

end PEqualNP.Outside.L_meta_21436

open PEqualNP.Outside.L_meta_21436

theorem PEqualNP.Outside.L_meta_21436 :
    ∀ (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (S Rg : Finset ℕ) (tj : ℕ),
      PEqualNP.MetaComplexity.NestedCover.ReadsBack m C → tj ∈ Rg → (∀ j ∈ Rg, j < C.size) →
      (∀ j < C.size, ∀ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
        (w ∈ S ∨ (m ≤ w ∧ w - m ∈ Rg ∧ w ≠ m + tj)) → j ∈ Rg) →
      C.output ∉ S → (∀ j ∈ Rg, j ≠ tj → C.output ≠ m + j) →
      ∃ G : Bool → (Fin m → Bool) → Bool,
        (∀ (c : Bool) (x y : Fin m → Bool), (∀ i : Fin m, (i : ℕ) ∉ S → x i = y i) → G c x = G c y) ∧
        ∀ x : Fin m → Bool,
          C.eval (List.ofFn x) = G ((C.wires (List.ofFn x)).getD (m + tj) false) x := by
  classical
  intro m C S Rg tj _ _ _ hclosed houtS houtRg
  let safe (i : ℕ) := i ∉ S ∧ ¬ (m ≤ i ∧ i - m ∈ Rg ∧ i ≠ m + tj)
  let masked (x : Fin m → Bool) (i : Fin m) := if (i : ℕ) ∈ S then false else x i
  let cut (x : Fin m → Bool) := (C.wires (List.ofFn x)).getD (m + tj) false
  let out (x : Fin m → Bool) := C.eval (List.ofFn x)
  have agrees (x y : Fin m → Bool) (hm : masked x = masked y) (hc : cut x = cut y) :
      out x = out y := by
    refine foldAgrees C.gates safe (m + tj) (List.ofFn x) (List.ofFn y) (by simp)
      ?_ ?_ hc C.output ?_
    · intro i hi
      by_cases him : i < m
      · simpa [masked, hi.1, List.getD_eq_getElem?_getD, him] using congrFun hm ⟨i, him⟩
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt him),
            List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt him)]
    · simp only [List.length_ofFn]
      intro j hj hs ht i hi
      have hn : j ∉ Rg := by
        intro hjr
        exact hs.2 ⟨by omega, by simpa using hjr, ht⟩
      have hig : i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs := by
        simpa [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hj] using hi
      exact ⟨fun h => hn (hclosed j hj i hig (.inl h)),
        fun h => hn (hclosed j hj i hig (.inr h))⟩
    · refine ⟨houtS, ?_⟩
      rintro ⟨hle, hjr, hne⟩
      have he : C.output = m + (C.output - m) := by omega
      exact houtRg _ hjr (by intro e; apply hne; omega) he
  let G (c : Bool) (x : Fin m → Bool) :=
    if ∃ y, cut y = c ∧ masked y = masked x ∧ out y = true then true else false
  refine ⟨G, ?_, ?_⟩
  · intro c x y hxy
    have hm : masked x = masked y := by
      funext i
      by_cases hi : (i : ℕ) ∈ S
      · simp [masked, hi]
      · simp [masked, hi, hxy i hi]
    simp only [G, hm]
  · intro x
    change out x = G (cut x) x
    by_cases hx : out x = true
    · have he : ∃ y, cut y = cut x ∧ masked y = masked x ∧ out y = true := ⟨x, rfl, rfl, hx⟩
      simpa [G, he] using hx
    · have hn : ¬ ∃ y, cut y = cut x ∧ masked y = masked x ∧ out y = true := by
        rintro ⟨y, hc, hm, hy⟩
        exact hx ((agrees y x hm hc).symm.trans hy)
      have hx' : out x = false := by
        cases he : out x
        · rfl
        · exact (hx he).elim
      simpa [G, hn] using hx'
