import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25551

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

lemma foldl_wires_append_step (l : List Gate) (acc : List Bool) :
    ∃ ext : List Bool,
      l.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc =
        acc ++ ext ∧ ext.length = l.length := by
  induction l generalizing acc with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    simp only [List.foldl_cons]
    obtain ⟨ext, heq, hlen⟩ := ih (acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)])
    refine ⟨[g.op.eval (g.inputs.map fun i => acc.getD i false)] ++ ext, ?_, ?_⟩
    · rw [heq, List.append_assoc]
    · simp [hlen]

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.size := by
  unfold Circuit.wires Circuit.size
  obtain ⟨ext, heq, hlen⟩ := foldl_wires_append_step C.gates x
  rw [heq, List.length_append, hlen]

lemma wires_getD_lt_input (C : Circuit) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (C.wires x).getD w false = x.getD w false := by
  unfold Circuit.wires
  obtain ⟨ext, heq, _⟩ := foldl_wires_append_step C.gates x
  rw [heq]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hw]

lemma wires_getD_gate (C : Circuit) (x : List Bool) (k : ℕ) (hk : k < C.size)
    (hRB : ReadsBack x.length C) :
    (C.wires x).getD (x.length + k) false =
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun i => (C.wires x).getD i false) := by
  have hk' : k < C.gates.length := hk
  have hsplit : C.gates = C.gates.take k ++ C.gates[k] :: C.gates.drop (k + 1) := by
    have h1 := List.take_append_drop k C.gates
    have h2 : C.gates.drop k = C.gates[k] :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons hk'
    rw [← h2, h1]
  set step : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  set pref := (C.gates.take k).foldl step x
  set gval := C.gates[k].op.eval (C.gates[k].inputs.map fun i => pref.getD i false)
  have hpref_len : pref.length = x.length + k := by
    obtain ⟨ext, heq, hlen⟩ := foldl_wires_append_step (C.gates.take k) x
    rw [show pref = x ++ ext from heq, List.length_append, hlen, List.length_take_of_le (Nat.le_of_lt hk')]
  have hgate : gateAt C k = C.gates[k] := by
    unfold gateAt
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']
  have hfull : ∃ ext : List Bool, C.wires x = (pref ++ [gval]) ++ ext := by
    obtain ⟨ext, heq, _⟩ := foldl_wires_append_step (C.gates.drop (k + 1)) (pref ++ [gval])
    refine ⟨ext, ?_⟩
    unfold Circuit.wires
    rw [hsplit, List.foldl_append, List.foldl_cons]
    exact heq
  obtain ⟨ext, heq⟩ := hfull
  have hpref_eq : ∀ i < x.length + k, (C.wires x).getD i false = pref.getD i false := by
    intro i hi
    rw [heq, List.append_assoc]
    have hi' : i < pref.length := hpref_len ▸ hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi']
  have hmap : (C.gates[k].inputs.map fun i => (C.wires x).getD i false) =
      (C.gates[k].inputs.map fun i => pref.getD i false) := by
    apply List.map_congr_left
    intro i hi
    exact hpref_eq i (hRB k hk' i (hgate.symm ▸ hi))
  rw [hgate, hmap, heq]
  have hlt : x.length + k < (pref ++ [gval]).length := by
    rw [List.length_append, hpref_len]; simp
  have hge : pref.length ≤ x.length + k := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
      List.getElem?_append_right hge, hpref_len, Nat.sub_self]
  rfl

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i (h₁ : i < l₁.length) (h₂ : i < l₂.length), l₁[i] = true → l₂[i] = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have hi₁ : i < l₁.length := hlen ▸ hi
    exact hle i hi₁ hi (h l₁[i] (List.getElem_mem hi₁))
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have hi₂ : i < l₂.length := hlen ▸ hi
    exact ⟨l₂[i], List.getElem_mem hi₂, hle i hi hi₂ hbi⟩

def evalSim (raw : ℕ) (C : Circuit) (region entry : Finset ℕ) (active : ℕ) (b : Bool) : ℕ → Bool :=
  WellFounded.fix Nat.lt_wfRel.wf fun w ih =>
    if w ∈ entry then
      b
    else if w < raw then
      decide (w = active)
    else if w - raw ∈ region then
      (gateAt C (w - raw)).op.eval
        ((gateAt C (w - raw)).inputs.map fun i =>
          if h : i < w then ih i h else false)
    else
      false

lemma evalSim_unfold (raw : ℕ) (C : Circuit) (region entry : Finset ℕ) (active : ℕ) (b : Bool) (w : ℕ) :
    evalSim raw C region entry active b w =
      if w ∈ entry then
        b
      else if w < raw then
        decide (w = active)
      else if w - raw ∈ region then
        (gateAt C (w - raw)).op.eval
          ((gateAt C (w - raw)).inputs.map fun i =>
            if i < w then evalSim raw C region entry active b i else false)
      else
        false := by
  unfold evalSim
  rw [WellFounded.fix_eq]
  rfl

lemma evalSim_mono (raw : ℕ) (C : Circuit) (region entry : Finset ℕ) (active : ℕ)
    (hInsideOp : ∀ k ∈ region, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) :
    ∀ w, evalSim raw C region entry active false w = true →
         evalSim raw C region entry active true w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rw [evalSim_unfold, evalSim_unfold]
    split_ifs with h1 h2 h3
    · intro h; cases h
    · exact id
    · apply gateOp_eval_mono _ (hInsideOp _ h3)
      · simp
      · intro i hi₁ hi₂
        simp only [List.getElem_map]
        split_ifs with hlt
        · exact ih _ hlt
        · exact id
    · exact id

lemma evalSim_agree (raw : ℕ) (C : Circuit) (sources region entry : Finset ℕ) (active : ℕ)
    (x : List Bool) (b : Bool)
    (hxlen : x.length = raw)
    (hRB : ReadsBack raw C)
    (hRegSub : region ⊆ Finset.range C.size)
    (hSrcLt : ∀ w ∈ sources, w < raw)
    (hEntry : ∀ w ∈ entry, w ∉ sources ∧ ¬ (raw ≤ w ∧ w - raw ∈ region))
    (hInside : ∀ k ∈ region, ∀ w ∈ (gateAt C k).inputs,
      w ∈ sources ∨ (raw ≤ w ∧ w - raw ∈ region) ∨ w ∈ entry)
    (hSrcVal : ∀ w ∈ sources, (C.wires x).getD w false = decide (w = active))
    (hEntryVal : ∀ w ∈ entry, (C.wires x).getD w false = b) :
    ∀ w, (w ∈ sources ∨ (raw ≤ w ∧ w - raw ∈ region) ∨ w ∈ entry) →
      (C.wires x).getD w false = evalSim raw C region entry active b w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    rcases hw with hsrc | ⟨hge, hreg⟩ | hent
    · have hnotent : w ∉ entry := fun h => (hEntry w h).1 hsrc
      rw [hSrcVal w hsrc, evalSim_unfold, if_neg hnotent, if_pos (hSrcLt w hsrc)]
    · have hnotlt : ¬ w < raw := Nat.not_lt.mpr hge
      have hnotent : w ∉ entry := fun h => (hEntry w h).2 ⟨hge, hreg⟩
      rw [evalSim_unfold, if_neg hnotent, if_neg hnotlt, if_pos hreg]
      set k := w - raw
      have hw_eq : w = raw + k := by omega
      have hk_lt : k < C.size := Finset.mem_range.mp (hRegSub hreg)
      have hwg : (C.wires x).getD w false =
          (gateAt C k).op.eval ((gateAt C k).inputs.map fun i => (C.wires x).getD i false) := by
        conv_lhs => rw [hw_eq, ← hxlen]
        exact wires_getD_gate C x k hk_lt (hxlen.symm ▸ hRB)
      rw [hwg]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hilt : i < w := by
        have := hRB k hk_lt i hi
        omega
      rw [if_pos hilt]
      exact ih i hilt (hInside k hreg i hi)
    · rw [hEntryVal w hent, evalSim_unfold, if_pos hent]

lemma outside_before_top_eq (raw : ℕ) (C : Circuit) (sources region : Finset ℕ) (top : ℕ)
    (x₁ x₂ : List Bool)
    (hx₁ : x₁.length = raw) (hx₂ : x₂.length = raw)
    (hRB : ReadsBack raw C)
    (hRegSub : region ⊆ Finset.range C.size)
    (hTop : top ∈ region)
    (hOutside : ∀ k < C.size, k ∉ region → ∀ w ∈ (gateAt C k).inputs,
      w ∉ sources ∧ ((raw ≤ w ∧ w - raw ∈ region) → w = raw + top))
    (hAgree : ∀ w < raw, w ∉ sources → x₁.getD w false = x₂.getD w false) :
    ∀ w < raw + top, w ∉ sources → ¬ (raw ≤ w ∧ w - raw ∈ region) →
      (C.wires x₁).getD w false = (C.wires x₂).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwlt hns hni
    by_cases hlt : w < raw
    · rw [wires_getD_lt_input C x₁ w (hx₁.symm ▸ hlt),
          wires_getD_lt_input C x₂ w (hx₂.symm ▸ hlt)]
      exact hAgree w hlt hns
    · have hge : raw ≤ w := Nat.le_of_not_lt hlt
      set k := w - raw
      have hw_eq : w = raw + k := by omega
      have htop_lt : top < C.size := Finset.mem_range.mp (hRegSub hTop)
      have hk_lt : k < C.size := by omega
      have hk_not_reg : k ∉ region := fun hr => hni ⟨hge, hr⟩
      have hg₁ : (C.wires x₁).getD w false =
          (gateAt C k).op.eval ((gateAt C k).inputs.map fun i => (C.wires x₁).getD i false) := by
        conv_lhs => rw [hw_eq, ← hx₁]
        exact wires_getD_gate C x₁ k hk_lt (hx₁.symm ▸ hRB)
      have hg₂ : (C.wires x₂).getD w false =
          (gateAt C k).op.eval ((gateAt C k).inputs.map fun i => (C.wires x₂).getD i false) := by
        conv_lhs => rw [hw_eq, ← hx₂]
        exact wires_getD_gate C x₂ k hk_lt (hx₂.symm ▸ hRB)
      rw [hg₁, hg₂]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hilt : i < w := by
        have := hRB k hk_lt i hi
        omega
      have ⟨hins, hiin⟩ := hOutside k hk_lt hk_not_reg i hi
      have hinot : ¬ (raw ≤ i ∧ i - raw ∈ region) := fun h => by
        have := hiin h
        omega
      exact ih i hilt (by omega) hins hinot

lemma outside_all_eq (raw : ℕ) (C : Circuit) (sources region : Finset ℕ) (top : ℕ)
    (x₁ x₂ : List Bool)
    (hx₁ : x₁.length = raw) (hx₂ : x₂.length = raw)
    (hRB : ReadsBack raw C)
    (hOutside : ∀ k < C.size, k ∉ region → ∀ w ∈ (gateAt C k).inputs,
      w ∉ sources ∧ ((raw ≤ w ∧ w - raw ∈ region) → w = raw + top))
    (hAgree : ∀ w < raw, w ∉ sources → x₁.getD w false = x₂.getD w false)
    (hTopEq : (C.wires x₁).getD (raw + top) false = (C.wires x₂).getD (raw + top) false) :
    ∀ w, w ∉ sources → ((raw ≤ w ∧ w - raw ∈ region) → w = raw + top) →
      (C.wires x₁).getD w false = (C.wires x₂).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hns hin
    by_cases hlt : w < raw
    · rw [wires_getD_lt_input C x₁ w (hx₁.symm ▸ hlt),
          wires_getD_lt_input C x₂ w (hx₂.symm ▸ hlt)]
      exact hAgree w hlt hns
    · have hge : raw ≤ w := Nat.le_of_not_lt hlt
      set k := w - raw
      have hw_eq : w = raw + k := by omega
      by_cases hk_lt : k < C.size
      · by_cases hk_reg : k ∈ region
        · have heq : w = raw + top := hin ⟨hge, hk_reg⟩
          rw [heq]
          exact hTopEq
        · have hg₁ : (C.wires x₁).getD w false =
              (gateAt C k).op.eval ((gateAt C k).inputs.map fun i => (C.wires x₁).getD i false) := by
            conv_lhs => rw [hw_eq, ← hx₁]
            exact wires_getD_gate C x₁ k hk_lt (hx₁.symm ▸ hRB)
          have hg₂ : (C.wires x₂).getD w false =
              (gateAt C k).op.eval ((gateAt C k).inputs.map fun i => (C.wires x₂).getD i false) := by
            conv_lhs => rw [hw_eq, ← hx₂]
            exact wires_getD_gate C x₂ k hk_lt (hx₂.symm ▸ hRB)
          rw [hg₁, hg₂]
          congr 1
          apply List.map_congr_left
          intro i hi
          have hilt : i < w := by
            have := hRB k hk_lt i hi
            omega
          have ⟨hins, hiin⟩ := hOutside k hk_lt hk_reg i hi
          exact ih i hilt hins hiin
      · have hlen₁ : (C.wires x₁).length ≤ w := by rw [wires_length, hx₁]; omega
        have hlen₂ : (C.wires x₂).length ≤ w := by rw [wires_length, hx₂]; omega
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen₁, List.getElem?_eq_none hlen₂]

lemma card_le_two_add_entry {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (raw d : ℕ) (C : Circuit) (sources region entry : Finset ℕ) (top : ℕ)
    (A : Finset α) (B_opp : Finset β)
    (M : α → β → Bool) (inp : α → β → List Bool) (active : α → ℕ)
    (hDist : ∀ a₁ a₂ : α, a₁ ≠ a₂ → d ≤ (Finset.univ.filter (fun b => M a₁ b ≠ M a₂ b)).card)
    (hLen : ∀ a b, (inp a b).length = raw)
    (hRep : ∀ a b, C.eval (inp a b) = M a b)
    (hAgreeNonSrc : ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ b, ∀ w < raw, w ∉ sources →
      (inp a₁ b).getD w false = (inp a₂ b).getD w false)
    (hSrcVal : ∀ a ∈ A, ∀ b, b ∉ B_opp → ∀ w ∈ sources,
      (inp a b).getD w false = decide (w = active a))
    (hSrcLt : ∀ w ∈ sources, w < raw)
    (hRB : ReadsBack raw C)
    (hRegSub : region ⊆ Finset.range C.size)
    (hTop : top ∈ region)
    (hEntryCard : entry.card ≤ 1)
    (hEntry : ∀ w ∈ entry, w < raw + top ∧ w ∉ sources ∧ ¬ (raw ≤ w ∧ w - raw ∈ region))
    (hInsideGate : ∀ k ∈ region,
      ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
      ∀ w ∈ (gateAt C k).inputs, w ∈ sources ∨ (raw ≤ w ∧ w - raw ∈ region) ∨ w ∈ entry)
    (hOutsideGate : ∀ k < C.size, k ∉ region → ∀ w ∈ (gateAt C k).inputs,
      w ∉ sources ∧ ((raw ≤ w ∧ w - raw ∈ region) → w = raw + top))
    (hOutNotSrc : C.output ∉ sources)
    (hOutInside : (raw ≤ C.output ∧ C.output - raw ∈ region) → C.output = raw + top)
    (hB : B_opp.card < d) :
    A.card ≤ 2 + entry.card := by
  have hInsideOp : ∀ k ∈ region, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or :=
    fun k hk => (hInsideGate k hk).1
  have hInsideIn : ∀ k ∈ region, ∀ w ∈ (gateAt C k).inputs,
      w ∈ sources ∨ (raw ≤ w ∧ w - raw ∈ region) ∨ w ∈ entry :=
    fun k hk => (hInsideGate k hk).2
  have hTopIn : raw ≤ raw + top ∧ (raw + top) - raw ∈ region := by
    refine ⟨Nat.le_add_right raw top, ?_⟩
    simpa using hTop
  have hEntry2 : ∀ w ∈ entry, w ∉ sources ∧ ¬ (raw ≤ w ∧ w - raw ∈ region) :=
    fun w hw => ⟨(hEntry w hw).2.1, (hEntry w hw).2.2⟩
  by_cases hempty : entry = ∅
  · rw [hempty, Finset.card_empty, Nat.add_zero]
    let prof : α → Bool := fun a => evalSim raw C region entry (active a) false (raw + top)
    have hinj : Set.InjOn prof A := by
      intro a₁ ha₁ a₂ ha₂ hpeq
      by_contra hne
      have hsub : Finset.univ.filter (fun b => M a₁ b ≠ M a₂ b) ⊆ B_opp := by
        intro b hb
        by_contra hbnot
        have hdiff : M a₁ b ≠ M a₂ b := (Finset.mem_filter.mp hb).2
        have hsim₁ : (C.wires (inp a₁ b)).getD (raw + top) false = prof a₁ := by
          apply evalSim_agree raw C sources region entry (active a₁) (inp a₁ b) false
            (hLen a₁ b) hRB hRegSub hSrcLt hEntry2 hInsideIn
          · intro w hw
            rw [wires_getD_lt_input C (inp a₁ b) w ((hLen a₁ b).symm ▸ hSrcLt w hw)]
            exact hSrcVal a₁ ha₁ b hbnot w hw
          · intro w hw; rw [hempty] at hw; exact False.elim (Finset.notMem_empty w hw)
          · exact Or.inr (Or.inl hTopIn)
        have hsim₂ : (C.wires (inp a₂ b)).getD (raw + top) false = prof a₂ := by
          apply evalSim_agree raw C sources region entry (active a₂) (inp a₂ b) false
            (hLen a₂ b) hRB hRegSub hSrcLt hEntry2 hInsideIn
          · intro w hw
            rw [wires_getD_lt_input C (inp a₂ b) w ((hLen a₂ b).symm ▸ hSrcLt w hw)]
            exact hSrcVal a₂ ha₂ b hbnot w hw
          · intro w hw; rw [hempty] at hw; exact False.elim (Finset.notMem_empty w hw)
          · exact Or.inr (Or.inl hTopIn)
        have htop_eq : (C.wires (inp a₁ b)).getD (raw + top) false =
            (C.wires (inp a₂ b)).getD (raw + top) false := by
          rw [hsim₁, hsim₂, hpeq]
        have hout_eq : C.eval (inp a₁ b) = C.eval (inp a₂ b) := by
          unfold Circuit.eval
          exact outside_all_eq raw C sources region top (inp a₁ b) (inp a₂ b)
            (hLen a₁ b) (hLen a₂ b) hRB hOutsideGate (hAgreeNonSrc a₁ ha₁ a₂ ha₂ b) htop_eq
            C.output hOutNotSrc hOutInside
        rw [hRep a₁ b, hRep a₂ b] at hout_eq
        exact hdiff hout_eq
      have hcard := Finset.card_le_card hsub
      have hdist := hDist a₁ a₂ hne
      omega
    calc A.card = (A.image prof).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.univ : Finset Bool).card := Finset.card_le_card (Finset.subset_univ _)
      _ = 2 := by decide
  · have hcard1 : entry.card = 1 := by
      have hpos : 0 < entry.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
      omega
    obtain ⟨e₀, he₀⟩ := Finset.card_eq_one.mp hcard1
    rw [hcard1]
    let prof : α → Bool × Bool := fun a =>
      (evalSim raw C region entry (active a) false (raw + top),
       evalSim raw C region entry (active a) true (raw + top))
    have hinj : Set.InjOn prof A := by
      intro a₁ ha₁ a₂ ha₂ hpeq
      by_contra hne
      have hsub : Finset.univ.filter (fun b => M a₁ b ≠ M a₂ b) ⊆ B_opp := by
        intro b hb
        by_contra hbnot
        have hdiff : M a₁ b ≠ M a₂ b := (Finset.mem_filter.mp hb).2
        have he₀_mem : e₀ ∈ entry := he₀ ▸ Finset.mem_singleton_self e₀
        have he₀_info := hEntry e₀ he₀_mem
        have he₀_eq : (C.wires (inp a₁ b)).getD e₀ false = (C.wires (inp a₂ b)).getD e₀ false :=
          outside_before_top_eq raw C sources region top (inp a₁ b) (inp a₂ b)
            (hLen a₁ b) (hLen a₂ b) hRB hRegSub hTop hOutsideGate
            (hAgreeNonSrc a₁ ha₁ a₂ ha₂ b) e₀ he₀_info.1 he₀_info.2.1 he₀_info.2.2
        set v := (C.wires (inp a₁ b)).getD e₀ false
        have hsim₁ : (C.wires (inp a₁ b)).getD (raw + top) false =
            evalSim raw C region entry (active a₁) v (raw + top) := by
          apply evalSim_agree raw C sources region entry (active a₁) (inp a₁ b) v
            (hLen a₁ b) hRB hRegSub hSrcLt hEntry2 hInsideIn
          · intro w hw
            rw [wires_getD_lt_input C (inp a₁ b) w ((hLen a₁ b).symm ▸ hSrcLt w hw)]
            exact hSrcVal a₁ ha₁ b hbnot w hw
          · intro w hw
            have hweq : w = e₀ := Finset.mem_singleton.mp (he₀ ▸ hw)
            rw [hweq]
          · exact Or.inr (Or.inl hTopIn)
        have hsim₂ : (C.wires (inp a₂ b)).getD (raw + top) false =
            evalSim raw C region entry (active a₂) v (raw + top) := by
          apply evalSim_agree raw C sources region entry (active a₂) (inp a₂ b) v
            (hLen a₂ b) hRB hRegSub hSrcLt hEntry2 hInsideIn
          · intro w hw
            rw [wires_getD_lt_input C (inp a₂ b) w ((hLen a₂ b).symm ▸ hSrcLt w hw)]
            exact hSrcVal a₂ ha₂ b hbnot w hw
          · intro w hw
            have hweq : w = e₀ := Finset.mem_singleton.mp (he₀ ▸ hw)
            rw [hweq, ← he₀_eq]
          · exact Or.inr (Or.inl hTopIn)
        have htop_eq : (C.wires (inp a₁ b)).getD (raw + top) false =
            (C.wires (inp a₂ b)).getD (raw + top) false := by
          rw [hsim₁, hsim₂]
          cases v
          · exact congrArg Prod.fst hpeq
          · exact congrArg Prod.snd hpeq
        have hout_eq : C.eval (inp a₁ b) = C.eval (inp a₂ b) := by
          unfold Circuit.eval
          exact outside_all_eq raw C sources region top (inp a₁ b) (inp a₂ b)
            (hLen a₁ b) (hLen a₂ b) hRB hOutsideGate (hAgreeNonSrc a₁ ha₁ a₂ ha₂ b) htop_eq
            C.output hOutNotSrc hOutInside
        rw [hRep a₁ b, hRep a₂ b] at hout_eq
        exact hdiff hout_eq
      have hcard := Finset.card_le_card hsub
      have hdist := hDist a₁ a₂ hne
      omega
    let allowed : Finset (Bool × Bool) := {(false, false), (false, true), (true, true)}
    have himg : A.image prof ⊆ allowed := by
      intro p hp
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
      have hmono := evalSim_mono raw C region entry (active a) hInsideOp (raw + top)
      cases h1 : evalSim raw C region entry (active a) false (raw + top) <;>
        cases h2 : evalSim raw C region entry (active a) true (raw + top)
      · simp [prof, allowed, h1, h2]
      · simp [prof, allowed, h1, h2]
      · have hcontra := hmono h1
        rw [h2] at hcontra
        cases hcontra
      · simp [prof, allowed, h1, h2]
    calc A.card = (A.image prof).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ allowed.card := Finset.card_le_card himg
      _ = 2 + 1 := by decide

lemma oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) :
    (oneEach u v).length = n + m := by
  unfold oneEach
  simp

lemma oneEach_getD_lt {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) (hw : w < n) :
    (oneEach u v).getD w false = decide (w = u.val) := by
  unfold oneEach
  have hlen : (List.ofFn (fun i : Fin n => decide (i = u))).length = n := by simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (hlen.symm ▸ hw), List.getElem?_ofFn]
  simp [hw, Fin.ext_iff]

lemma oneEach_getD_ge {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) (hge : n ≤ w) (hlt : w < n + m) :
    (oneEach u v).getD w false = decide (w = n + v.val) := by
  unfold oneEach
  have hlen : (List.ofFn (fun i : Fin n => decide (i = u))).length = n := by simp
  have hlt2 : w - n < m := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (hlen.symm ▸ hge), hlen, List.getElem?_ofFn]
  simp only [hlt2, ↓reduceDIte, Option.getD_some, Fin.ext_iff, decide_eq_decide]
  omega

end PEqualNP.Outside.L_meta_25551

theorem PEqualNP.Outside.L_meta_25551 : (∀ (n m d : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (region entry : Finset ℕ) (top : ℕ),
  let raw := n + m
  let sources := R.image (fun sourceRow => sourceRow.val) ∪ B.image (fun sourceCol => n + sourceCol.val)
  let inside := fun (w : ℕ) => raw ≤ w ∧ w - raw ∈ region
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  (∀ firstRow secondRow : Fin n, firstRow ≠ secondRow → d ≤ (Finset.univ.filter (fun col => G firstRow col ≠ G secondRow col)).card) →
  (∀ firstCol secondCol : Fin m, firstCol ≠ secondCol → d ≤ (Finset.univ.filter (fun row => G row firstCol ≠ G row secondCol)).card) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack raw C →
  PEqualNP.Represents.Represents G C → region ⊆ Finset.range C.size → top ∈ region →
  entry.card ≤ 1 → (∀ w ∈ entry, w < raw + top ∧ w ∉ sources ∧ ¬ inside w) →
  (∀ k ∈ region,
    ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
     (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
    ∀ w ∈ (gate k).inputs, w ∈ sources ∨ inside w ∨ w ∈ entry) →
  (∀ k < C.size, k ∉ region → ∀ w ∈ (gate k).inputs,
    w ∉ sources ∧ (inside w → w = raw + top)) →
  C.output ∉ sources → (inside C.output → C.output = raw + top) →
  (B.card < d → R.card ≤ 2 + entry.card) ∧ (R.card < d → B.card ≤ 2 + entry.card)) := by
  intro n m d G C R B region entry top
  dsimp only
  intro hRowDist hColDist hRB hRep hRegSub hTop hEntryCard hEntry hInsideGate hOutsideGate
    hOutNotSrc hOutInside
  set raw := n + m
  set sources := R.image (fun sourceRow => sourceRow.val) ∪ B.image (fun sourceCol => n + sourceCol.val)
  have hSrcLt : ∀ w ∈ sources, w < raw := by
    intro w hw
    rcases Finset.mem_union.mp hw with hR | hB
    · obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hR
      omega
    · obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hB
      omega
  constructor
  · intro hB
    apply PEqualNP.Outside.L_meta_25551.card_le_two_add_entry
      raw d C sources region entry top R B G PEqualNP.Represents.oneEach (fun r => r.val)
      hRowDist
      (fun r c => PEqualNP.Outside.L_meta_25551.oneEach_length r c)
      hRep
      ?hAgreeR ?hSrcR hSrcLt hRB hRegSub hTop hEntryCard hEntry hInsideGate hOutsideGate
      hOutNotSrc hOutInside hB
    · intro r₁ hr₁ r₂ hr₂ c w hwlt hns
      by_cases hw : w < n
      · rw [PEqualNP.Outside.L_meta_25551.oneEach_getD_lt r₁ c w hw,
            PEqualNP.Outside.L_meta_25551.oneEach_getD_lt r₂ c w hw]
        have hne₁ : w ≠ r₁.val := fun heq =>
          hns (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r₁, hr₁, heq.symm⟩))
        have hne₂ : w ≠ r₂.val := fun heq =>
          hns (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r₂, hr₂, heq.symm⟩))
        simp [hne₁, hne₂]
      · have hge : n ≤ w := Nat.le_of_not_lt hw
        rw [PEqualNP.Outside.L_meta_25551.oneEach_getD_ge r₁ c w hge hwlt,
            PEqualNP.Outside.L_meta_25551.oneEach_getD_ge r₂ c w hge hwlt]
    · intro r _ c hcnot w hw
      rcases Finset.mem_union.mp hw with hR | hB'
      · obtain ⟨r₀, _, rfl⟩ := Finset.mem_image.mp hR
        exact PEqualNP.Outside.L_meta_25551.oneEach_getD_lt r c r₀.val r₀.isLt
      · obtain ⟨c₀, hc₀, rfl⟩ := Finset.mem_image.mp hB'
        rw [PEqualNP.Outside.L_meta_25551.oneEach_getD_ge r c (n + c₀.val) (Nat.le_add_right _ _) (by omega)]
        have hne₁ : c₀.val ≠ c.val := fun heq => hcnot (Fin.ext heq ▸ hc₀)
        have hne₂ : n + c₀.val ≠ r.val := by omega
        simp [hne₁, hne₂]
  · intro hR
    apply PEqualNP.Outside.L_meta_25551.card_le_two_add_entry
      raw d C sources region entry top B R (fun c r => G r c)
      (fun c r => PEqualNP.Represents.oneEach r c) (fun c => n + c.val)
      hColDist
      (fun c r => PEqualNP.Outside.L_meta_25551.oneEach_length r c)
      (fun c r => hRep r c)
      ?hAgreeB ?hSrcB hSrcLt hRB hRegSub hTop hEntryCard hEntry hInsideGate hOutsideGate
      hOutNotSrc hOutInside hR
    · intro c₁ hc₁ c₂ hc₂ r w hwlt hns
      by_cases hw : w < n
      · rw [PEqualNP.Outside.L_meta_25551.oneEach_getD_lt r c₁ w hw,
            PEqualNP.Outside.L_meta_25551.oneEach_getD_lt r c₂ w hw]
      · have hge : n ≤ w := Nat.le_of_not_lt hw
        rw [PEqualNP.Outside.L_meta_25551.oneEach_getD_ge r c₁ w hge hwlt,
            PEqualNP.Outside.L_meta_25551.oneEach_getD_ge r c₂ w hge hwlt]
        have hne₁ : w ≠ n + c₁.val := fun heq =>
          hns (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨c₁, hc₁, heq.symm⟩))
        have hne₂ : w ≠ n + c₂.val := fun heq =>
          hns (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨c₂, hc₂, heq.symm⟩))
        simp [hne₁, hne₂]
    · intro c _ r hrnot w hw
      rcases Finset.mem_union.mp hw with hR' | hB'
      · obtain ⟨r₀, hr₀, rfl⟩ := Finset.mem_image.mp hR'
        rw [PEqualNP.Outside.L_meta_25551.oneEach_getD_lt r c r₀.val r₀.isLt]
        have hne₁ : r₀.val ≠ r.val := fun heq =>
          hrnot (Fin.ext heq ▸ hr₀)
        have hne₂ : r₀.val ≠ n + c.val := by omega
        simp [hne₁, hne₂]
      · obtain ⟨c₀, _, rfl⟩ := Finset.mem_image.mp hB'
        exact PEqualNP.Outside.L_meta_25551.oneEach_getD_ge r c (n + c₀.val) (Nat.le_add_right _ _) (by omega)
