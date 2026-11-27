import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29908_aux
open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem len_foldl (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl, ih, step, List.length_append, List.length_cons,
      List.length_nil]; omega

theorem getD_append_lt (w l : List Bool) (j : ℕ) (h : j < w.length) :
    (w ++ l).getD j false = w.getD j false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem prefix_foldl (gs : List Gate) (w : List Bool) (j : ℕ) (h : j < w.length) :
    (gs.foldl step w).getD j false = w.getD j false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl]
    rw [ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ h

theorem getD_snoc (w : List Bool) (b : Bool) (j : ℕ) : (w ++ [b]).getD j false =
    if j < w.length then w.getD j false else if j = w.length then b else false := by
  split_ifs with h1 h2
  · exact getD_append_lt _ _ _ h1
  · subst h2; simp
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; rfl

theorem agree_foldl (gs : List Gate) (hg : ∀ g ∈ gs, 0 ∉ g.inputs) (w w' : List Bool)
    (hl : w.length = w'.length) (ha : ∀ j, j ≠ 0 → w.getD j false = w'.getD j false) :
    (gs.foldl step w).length = (gs.foldl step w').length ∧
      ∀ j, j ≠ 0 → (gs.foldl step w).getD j false = (gs.foldl step w').getD j false := by
  induction gs generalizing w w' with
  | nil => exact ⟨hl, ha⟩
  | cons g gs ih =>
    simp only [List.foldl]
    apply ih (fun g hg' => hg g (List.mem_cons_of_mem _ hg'))
    · simp [step, hl]
    · intro j hj
      have hmap : g.inputs.map (fun i => w.getD i false) =
          g.inputs.map (fun i => w'.getD i false) := by
        apply List.map_congr_left
        intro i hi
        exact ha i (fun h => hg g (by simp) (h ▸ hi))
      simp only [step, getD_snoc, hl, hmap, ha j hj]

theorem sub04 (l : List ℕ) (h0 : 0 ∈ l) (h4 : 4 ∈ l) (hl : l.length ≤ 2) :
    ∀ a ∈ l, a = 0 ∨ a = 4 := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> simp at h0 h4 hl ⊢ <;> omega

end PEqualNP.Outside.L_meta_29908_aux

open PEqualNP.Outside.L_meta_29908_aux in
theorem PEqualNP.Outside.L_meta_29908 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 8 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 4 ∈ (C.gates.get i).inputs ∧ 4 ≠ 0 ∧ 4 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 4 false = true)) := by
  rintro ⟨⟨gs, o⟩, i, k, hi8, hfan, hsize, hf, hi0, hu, hop8, hop9, hik, h15, h4, -, -, -⟩
  have hlen : gs.length = 10 := hsize
  rcases gs with _|⟨g0,_|⟨g1,_|⟨g2,_|⟨g3,_|⟨g4,_|⟨g5,_|⟨g6,_|⟨g7,_|⟨g8,_|⟨g9,_|⟨g10,gs⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (simp at hlen; done)
  obtain ⟨iv, hiv⟩ := i
  obtain ⟨kv, hkv⟩ := k
  simp only at hi8 hik
  subst hi8
  have hk9 : kv = 9 := by simp at hkv; omega
  subst hk9
  change g8.op = _ at hop8
  change g9.op = _ at hop9
  change 0 ∈ g8.inputs at hi0
  change 4 ∈ g8.inputs at h4
  change 15 ∈ g9.inputs at h15
  have h8len : g8.inputs.length ≤ 2 := (hfan g8 (by simp)).2
  have hsub := sub04 _ hi0 h4 h8len
  have hpre : ∀ g ∈ [g0, g1, g2, g3, g4, g5, g6, g7], 0 ∉ g.inputs := by
    intro g hg h0
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact absurd (hu ⟨0, by simp⟩ h0) (by simp)
    · exact absurd (hu ⟨1, by simp⟩ h0) (by simp)
    · exact absurd (hu ⟨2, by simp⟩ h0) (by simp)
    · exact absurd (hu ⟨3, by simp⟩ h0) (by simp)
    · exact absurd (hu ⟨4, by simp⟩ h0) (by simp)
    · exact absurd (hu ⟨5, by simp⟩ h0) (by simp)
    · exact absurd (hu ⟨6, by simp⟩ h0) (by simp)
    · exact absurd (hu ⟨7, by simp⟩ h0) (by simp)
  set pre := [g0, g1, g2, g3, g4, g5, g6, g7] with hpre_def
  have hev : ∀ L, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨[g0, g1, g2, g3, g4, g5, g6, g7, g8, g9], o⟩ L
      = (step (step (pre.foldl step L) g8) g9).getD o false := fun L => rfl
  have hWlen : ∀ L : List Bool, L.length = 7 → (pre.foldl step L).length = 15 := by
    intro L hL; rw [len_foldl, hL]; rfl

  have hc := hf ![false, true, true, false, false, false, false]
  have hc' : (List.ofFn ![false, true, true, false, false, false, false]) =
      [false, true, true, false, false, false, false] := rfl
  rw [hc', hev] at hc
  by_cases ho : o < 15
  · have hlow : ∀ L : List Bool, L.length = 7 →
        (step (step (pre.foldl step L) g8) g9).getD o false = (pre.foldl step L).getD o false := by
      intro L hL
      simp only [step, getD_snoc, List.length_append, List.length_singleton, hWlen L hL]
      split_ifs <;> first | rfl | omega
    by_cases ho0 : o = 0
    · subst ho0
      have h1 := hf ![true, false, false, false, false, false, false]
      have h1' : (List.ofFn ![true, false, false, false, false, false, false]) =
          [true, false, false, false, false, false, false] := rfl
      rw [h1', hev, hlow _ rfl, prefix_foldl _ _ _ (by simp)] at h1
      exact absurd h1 (by decide)
    · have ha := hf ![false, true, false, false, false, false, false]
      have ha' : (List.ofFn ![false, true, false, false, false, false, false]) =
          [false, true, false, false, false, false, false] := rfl
      have hb := hf ![true, true, false, false, false, false, false]
      have hb' : (List.ofFn ![true, true, false, false, false, false, false]) =
          [true, true, false, false, false, false, false] := rfl
      rw [ha', hev, hlow _ rfl] at ha
      rw [hb', hev, hlow _ rfl] at hb
      have hag := (agree_foldl pre hpre [false, true, false, false, false, false, false]
        [true, true, false, false, false, false, false] rfl (by
          intro j hj
          rcases j with _ | j
          · exact absurd rfl hj
          · rfl)).2 o ho0
      rw [hag, hb] at ha
      exact absurd ha (by decide)
  · exfalso
    set W := pre.foldl step [false, true, true, false, false, false, false] with hW
    have hWl : W.length = 15 := hWlen _ rfl
    have hW0 : W.getD 0 false = false := prefix_foldl _ _ _ (by simp)
    have hW4 : W.getD 4 false = false := prefix_foldl _ _ _ (by simp)
    have hv8 : g8.op.eval (g8.inputs.map fun i => W.getD i false) = false := by
      rw [hop8]
      show List.any _ id = false
      rw [List.any_eq_false]
      intro a ha
      simp only [List.mem_map] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      rcases hsub b hb with rfl | rfl
      · exact Bool.eq_false_iff.mp hW0
      · exact Bool.eq_false_iff.mp hW4
    have h15v : (step W g8).getD 15 false = false := by
      simp only [step, getD_snoc, hWl]
      simpa using hv8
    have hv9 : g9.op.eval (g9.inputs.map fun i => (step W g8).getD i false) = false := by
      rw [hop9]
      show List.all _ id = false
      rw [List.all_eq_false]
      exact ⟨_, List.mem_map_of_mem h15, Bool.eq_false_iff.mp h15v⟩
    have hsl : (step W g8).length = 16 := by simp [step, hWl]
    have : (step (step W g8) g9).getD o false = false := by
      rw [step, getD_snoc, hsl, hv9]
      rw [step, getD_snoc, hWl, hv8]
      split_ifs <;> rfl
    rw [this] at hc
    exact absurd hc (by decide)
