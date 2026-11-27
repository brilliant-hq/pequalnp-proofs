import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29920

private def cyclePairRows : List (Nat × Nat) :=
  [(0, 0), (0, 0), (6, 5), (3, 1), (12, 9), (12, 9), (12, 5), (12, 5),
   (24, 9), (24, 9), (3, 34), (3, 34), (6, 5), (3, 1), (0, 0), (0, 0),
   (3, 1), (3, 5), (3, 1), (3, 9), (3, 1), (3, 17), (3, 1), (3, 33),
   (12, 9), (12, 9), (3, 1), (3, 5), (0, 0), (0, 0), (25, 17), (13, 5),
   (13, 9), (48, 36), (6, 34), (6, 34), (12, 5), (12, 5), (3, 1), (3, 9),
   (25, 17), (13, 5), (0, 0), (0, 0), (13, 5), (13, 21), (12, 36), (12, 36),
   (24, 9), (24, 9), (3, 1), (3, 17), (13, 9), (48, 36), (13, 5), (13, 21),
   (0, 0), (0, 0), (24, 40), (24, 40), (3, 34), (3, 34), (3, 1), (3, 33),
   (6, 34), (6, 34), (12, 36), (12, 36), (24, 40), (24, 40), (0, 0), (0, 0)]

private def cyclePairGate (useOr : Bool) (r : Nat) (i j : Fin 6) : Bool :=
  if useOr then r.testBit i || r.testBit j else r.testBit i && r.testBit j

private def cyclePairValid (i j : Fin 6) (useOr : Bool) : Prop :=
  let p := cyclePairRows[(i.val * 6 + j.val) * 2 + useOr.toNat]?.getD (0, 0)
  p.1 < 64 ∧ p.2 < 64 ∧ (p.1 &&& (p.1 >>> 1)) ≠ 0 ∧
  (p.2 &&& (p.2 >>> 1)) = 0 ∧ (p.2 &&& 33) ≠ 0 ∧
  cyclePairGate useOr p.1 i j = cyclePairGate useOr p.2 i j ∧
  ∀ k : Fin 6, k ≠ i → k ≠ j → p.1.testBit k = p.2.testBit k

private theorem cyclePairTable :
    ∀ (i j : Fin 6) (useOr : Bool), i ≠ j → cyclePairValid i j useOr := by
  unfold cyclePairValid
  decide

private def cycleStep (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

private theorem cycleReadStep (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate)
    (j : Nat) : (cycleStep w g).getD j false =
      if j = w.length then g.op.eval (g.inputs.map fun i => w.getD i false)
      else w.getD j false := by
  split_ifs with h
  · subst j
    simp [cycleStep, List.getD]
  · by_cases hlt : j < w.length
    · simp [cycleStep, List.getD, List.getElem?_append_left hlt]
    · have h₁ : w.length ≤ j := by omega
      have h₂ : (cycleStep w g).length ≤ j := by simp [cycleStep] <;> omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h₁, List.getElem?_eq_none h₂]

private theorem cycleFrontier (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hf : ∀ g ∈ gs, g.inputs.length ≤ 2) (n : Nat) (s : Finset Nat) :
    ∃ t : Finset Nat, t.card ≤ s.card + gs.length ∧
      ∀ (u v : List Bool), u.length = n → v.length = n →
        (∀ j ∈ t, u.getD j false = v.getD j false) →
        ∀ j ∈ s, (gs.foldl cycleStep u).getD j false =
          (gs.foldl cycleStep v).getD j false := by
  induction gs generalizing n s with
  | nil => exact ⟨s, by simp, by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht, he⟩ := ih (fun z hz => hf z (by simp [hz])) (n+1) s
    by_cases hn : n ∈ t
    · refine ⟨t.erase n ∪ g.inputs.toFinset, ?_, ?_⟩
      · have h₁ := Finset.card_union_le (t.erase n) g.inputs.toFinset
        have h₂ := Finset.card_erase_of_mem hn
        have h₃ := List.toFinset_card_le g.inputs
        have hpos : 0 < t.card := Finset.card_pos.mpr ⟨n, hn⟩
        have h₄ := hf g (by simp)
        simp only [List.length_cons]
        omega
      · intro u v hu hv h
        apply he (cycleStep u g) (cycleStep v g) (by simp [cycleStep, hu]) (by simp [cycleStep, hv])
        intro j hj
        rw [cycleReadStep, cycleReadStep, hu, hv]
        split_ifs with e
        · apply congrArg g.op.eval
          apply List.map_congr_left
          intro z hz
          exact h z (by simp [hz])
        · exact h j (by simp [e, hj])
    · refine ⟨t, by simp only [List.length_cons] <;> omega, ?_⟩
      intro u v hu hv h
      apply he (cycleStep u g) (cycleStep v g) (by simp [cycleStep, hu]) (by simp [cycleStep, hv])
      intro j hj
      have hne : j ≠ n := by rintro rfl; exact hn hj
      rw [cycleReadStep, cycleReadStep, hu, hv, if_neg hne, if_neg hne]
      exact h j hj

private def cycleInput (b : Bool) (r : Nat) : List Bool :=
  List.ofFn (fun i : Fin 7 => if i = 0 then b else r.testBit (i.val - 1))

private theorem cycleInputLen (b : Bool) (r : Nat) : (cycleInput b r).length = 7 := by
  simp [cycleInput]

private theorem cycleInputRead (b : Bool) (r j : Nat) : (cycleInput b r).getD j false =
    if j = 0 then b else if j < 7 then r.testBit (j-1) else false := by
  by_cases hj : j < 7
  · have hlen : j < (cycleInput b r).length := by rwa [cycleInputLen]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
    simp only [cycleInput, List.getElem_ofFn, Option.getD_some, if_pos hj]
    by_cases hz : j = 0
    · subst j
      rfl
    · have hn : (⟨j, hj⟩ : Fin 7) ≠ 0 := fun h => hz (congrArg Fin.val h)
      simp [hn, hz]
  · have hn : j ≠ 0 := by omega
    simp [cycleInput, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, hn]

private def cycleRowsDiffer (a b : Nat) : Prop :=
  a < 64 ∧ b < 64 ∧ (a &&& (a >>> 1)) ≠ 0 ∧ (b &&& (b >>> 1)) = 0 ∧ (b &&& 33) ≠ 0

private def cycleSingleRows : List (Nat × Nat) := [(35, 34), (3, 1), (13, 9), (13, 5), (25, 9), (49, 17)]

private theorem cycleSingle (i : Fin 6) :
    ∃ a b, cycleRowsDiffer a b ∧
      ∀ j : Nat, j ≠ i.val + 1 →
        (cycleInput false a).getD j false = (cycleInput false b).getD j false := by
  let p := cycleSingleRows[i.val]?.getD (0,0)
  have cert : ∀ k : Fin 6, let q := cycleSingleRows[k.val]?.getD (0,0)
      cycleRowsDiffer q.1 q.2 ∧ ∀ l : Fin 6, l ≠ k → q.1.testBit l = q.2.testBit l := by
    unfold cycleRowsDiffer
    decide
  obtain ⟨hh, he⟩ := cert i
  refine ⟨p.1, p.2, hh, ?_⟩
  intro j hj
  rw [cycleInputRead, cycleInputRead]
  split_ifs with h₀ h₇
  · rfl
  · exact he ⟨j-1, by omega⟩ (fun h => hj (by have := congrArg Fin.val h; dsimp at this; omega))
  · rfl

private theorem cycleDouble (i j : Fin 6) (hne : i ≠ j) (o : Bool) :
    ∃ a b, cycleRowsDiffer a b ∧ cyclePairGate o a i j = cyclePairGate o b i j ∧
      ∀ k : Nat, k ≠ i.val + 1 → k ≠ j.val + 1 →
        (cycleInput false a).getD k false = (cycleInput false b).getD k false := by
  let p := cyclePairRows[(i.val * 6 + j.val) * 2 + o.toNat]?.getD (0,0)
  obtain ⟨ha,hb,hc,hd,he,hf,hg⟩ := cyclePairTable i j o hne
  refine ⟨p.1,p.2,⟨ha,hb,hc,hd,he⟩,hf,?_⟩
  intro k hi hj
  rw [cycleInputRead, cycleInputRead]
  split_ifs with h₀ h₇
  · rfl
  · apply hg ⟨k-1, by omega⟩
    · intro h
      have := congrArg Fin.val h
      dsimp at this
      omega
    · intro h
      have := congrArg Fin.val h
      dsimp at this
      omega
  · rfl

private theorem cycleFirstImpossible (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hlen : g.inputs.length ≤ 2)
    (t : Finset Nat) (ht : t.card ≤ 5)
    (hsep : ∀ a b, cycleRowsDiffer a b → ∃ j ∈ t,
      (cycleStep (cycleInput false a) g).getD j false ≠
      (cycleStep (cycleInput false b) g).getD j false) : False := by
  let u : Finset Nat := {1,2,3,4,5,6}
  have hu : u.card = 6 := by decide
  have hmem : ∀ n ∈ u, 1 ≤ n ∧ n ≤ 6 := by decide
  have hsingle (n : Nat) (hn : n ∈ u) (hout : n ∉ t) :
      7 ∈ t ∧ n ∈ g.inputs ∧ (g.op = .not → g.inputs.head? = some n) := by
    have hr := hmem n hn
    let i : Fin 6 := ⟨n-1, by omega⟩
    have hi : i.val + 1 = n := by dsimp [i]; omega
    obtain ⟨a,b,hab,he⟩ := cycleSingle i
    rw [hi] at he
    obtain ⟨j,hj,hne⟩ := hsep a b hab
    rw [cycleReadStep, cycleReadStep, cycleInputLen, cycleInputLen] at hne
    by_cases h7 : j = 7
    · subst j
      simp only [if_true] at hne
      refine ⟨hj, ?_, ?_⟩
      · by_contra hm
        apply hne
        apply congrArg g.op.eval
        apply List.map_congr_left
        intro k hk
        exact he k (by rintro rfl; exact hm hk)
      · intro hop'
        cases hg : g.inputs with
        | nil => simp [hg, hop', PEqualNP.CircuitLowerBounds.GateOp.eval] at hne
        | cons k ks =>
          have hk : k = n := by
            by_contra hkn
            exact hne (by simpa [hg, hop', PEqualNP.CircuitLowerBounds.GateOp.eval] using he k hkn)
          simp [hk]
    · exact False.elim (hne (by simpa [h7] using he j (fun h => hout (h ▸ hj))))
  have hd := Finset.le_card_sdiff t u
  obtain ⟨z,hz⟩ := Finset.card_pos.mp (show 0 < (u \ t).card by omega)
  obtain ⟨hz₁,hz₂⟩ := Finset.mem_sdiff.mp hz
  have h7 := (hsingle z hz₁ hz₂).1
  have hcard := Finset.card_erase_of_mem h7
  have hd₂ := Finset.le_card_sdiff (t.erase 7) u
  obtain ⟨n,hn,m,hm,hnm⟩ := Finset.one_lt_card.mp (show 1 < (u \ t.erase 7).card by omega)
  obtain ⟨hn₁,hn₂⟩ := Finset.mem_sdiff.mp hn
  obtain ⟨hm₁,hm₂⟩ := Finset.mem_sdiff.mp hm
  have hrn := hmem n hn₁
  have hrm := hmem m hm₁
  have hnt : n ∉ t := fun h => hn₂ (Finset.mem_erase.mpr ⟨by omega,h⟩)
  have hmt : m ∉ t := fun h => hm₂ (Finset.mem_erase.mpr ⟨by omega,h⟩)
  obtain ⟨_,hng,hnotn⟩ := hsingle n hn₁ hnt
  obtain ⟨_,hmg,hnotm⟩ := hsingle m hm₁ hmt
  have hnot : g.op ≠ .not := fun h => hnm (Option.some.inj ((hnotn h).symm.trans (hnotm h)))
  have hlist : g.inputs = [n,m] ∨ g.inputs = [m,n] := by
    rcases hg : g.inputs with _ | ⟨x, _ | ⟨y, _ | ⟨z,zs⟩⟩⟩ <;>
      simp_all [List.mem_cons]
    all_goals grind
  let i : Fin 6 := ⟨n-1, by omega⟩
  let k : Fin 6 := ⟨m-1, by omega⟩
  have hiv : i.val + 1 = n := by dsimp [i]; omega
  have hkv : k.val + 1 = m := by dsimp [k]; omega
  have hik : i ≠ k := fun h => hnm (hiv.symm.trans ((congrArg (fun f : Fin 6 => f.val + 1) h).trans hkv))
  let o := match g.op with | .or => true | _ => false
  obtain ⟨a,b,hab,hgate,he⟩ := cycleDouble i k hik o
  rw [hiv,hkv] at he
  obtain ⟨j,hj,hne⟩ := hsep a b hab
  rw [cycleReadStep, cycleReadStep, cycleInputLen, cycleInputLen] at hne
  by_cases hj7 : j = 7
  · simp only [hj7, if_true] at hne
    have read (r : Nat) (l : Fin 6) : (cycleInput false r)[l.val+1]?.getD false = r.testBit l := by
      rw [← List.getD_eq_getElem?_getD, cycleInputRead]
      simp [show l.val+1 < 7 by omega]
    rw [← hiv, ← hkv] at hlist
    rcases hop with h | h | h
    · rcases hlist with hl | hl <;> apply hne <;>
        simpa [o, h, hl, PEqualNP.CircuitLowerBounds.GateOp.eval, cyclePairGate, read,
          Bool.and_comm] using hgate
    · rcases hlist with hl | hl <;> apply hne <;>
        simpa [o, h, hl, PEqualNP.CircuitLowerBounds.GateOp.eval, cyclePairGate, read,
          Bool.or_comm] using hgate
    · exact hnot h
  · exact hne (by simpa [hj7] using he j (fun h => hnt (h ▸ hj)) (fun h => hmt (h ▸ hj)))

private theorem cycleFoldLen (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
    (gs.foldl cycleStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih, cycleStep, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private theorem cycleFoldOld (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool)
    (j : Nat) (hj : j < w.length) : (gs.foldl cycleStep w).getD j false = w.getD j false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [cycleStep]; omega), cycleReadStep, if_neg (by omega)]

private theorem cycleFoldSkip (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hg : ∀ g ∈ gs, 0 ∉ g.inputs) (u v : List Bool) (hl : u.length = v.length)
    (he : ∀ j, j ≠ 0 → u.getD j false = v.getD j false) :
    ∀ j, j ≠ 0 → (gs.foldl cycleStep u).getD j false = (gs.foldl cycleStep v).getD j false := by
  induction gs generalizing u v with
  | nil => exact he
  | cons g gs ih =>
    apply ih (fun a ha => hg a (by simp [ha])) _ _ (by simp [cycleStep, hl])
    intro j hj
    rw [cycleReadStep,cycleReadStep,hl]
    split_ifs
    · apply congrArg g.op.eval
      apply List.map_congr_left
      intro n hn
      exact he n (by rintro rfl; exact hg g (by simp) hn)
    · exact he j hj

private def cycleTarget (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0)

private def cyclePattern (b : Bool) (r : Nat) (i : Fin 7) : Bool :=
  if i = 0 then b else r.testBit (i.val - 1)

private theorem cycleTargetRow (b : Bool) (r : Nat) (hr : r < 64) :
    cycleTarget (cyclePattern b r) =
    (decide ((r &&& (r >>> 1)) ≠ 0) || (b && decide ((r &&& 33) ≠ 0))) := by
  have h : ∀ (c : Bool) (v : Fin 64), cycleTarget (cyclePattern c v.val) =
      (decide ((v.val &&& (v.val >>> 1)) ≠ 0) || (c && decide ((v.val &&& 33) ≠ 0))) := by decide
  exact h b ⟨r,hr⟩

private theorem cycleTail (p : Bool → Nat → List Bool)
    (O D : PEqualNP.CircuitLowerBounds.Gate) (out : Nat)
    (plen : ∀ c r, (p c r).length = 15)
    (pz : ∀ c r, (p c r).getD 0 false = c)
    (peq : ∀ r j, j ≠ 0 → (p false r).getD j false = (p true r).getD j false)
    (ho : ∀ c r, O.op.eval (O.inputs.map fun j => (p c r).getD j false) =
      (c || (p c r).getD 11 false))
    (hd : D.op = .and) (h15 : 15 ∈ D.inputs) (h0 : 0 ∉ D.inputs)
    (heval : ∀ c r, r < 64 → (cycleStep (cycleStep (p c r) O) D).getD out false =
      cycleTarget (cyclePattern c r)) :
    ∀ a b, cycleRowsDiffer a b →
      (p false a).getD 11 false ≠ (p false b).getD 11 false := by
  let w c r := cycleStep (p c r) O
  have hw c r : (w c r).length = 16 := by simp [w,cycleStep,plen]
  have read c r j : (w c r).getD j false =
      if j = 15 then c || (p c r).getD 11 false else (p c r).getD j false := by
    dsimp only [w]
    rw [cycleReadStep,plen,ho]
  have ev c r (hr : r < 64) :
      (if out = 16 then D.op.eval (D.inputs.map fun j => (w c r).getD j false)
       else (w c r).getD out false) = cycleTarget (cyclePattern c r) := by
    have h := heval c r hr
    change (cycleStep (w c r) D).getD out false = _ at h
    rwa [cycleReadStep,hw] at h
  have singleton := ev true 0 (by decide)
  have s0 : cycleTarget (cyclePattern true 0) = false := by decide
  rw [s0] at singleton
  have hn0 : out ≠ 0 := by
    rintro rfl
    rw [if_neg (by decide), read, if_neg (by decide), pz] at singleton
    contradiction
  have hn15 : out ≠ 15 := by
    rintro rfl
    rw [if_neg (by decide), read, if_pos rfl] at singleton
    contradiction
  have hout : out = 16 := by
    by_contra h
    have hf := ev false 1 (by decide)
    have ht := ev true 1 (by decide)
    simp only [if_neg h,read,if_neg hn15] at hf ht
    have e := peq 1 out hn0
    rw [hf,ht] at e
    exact (by decide : cycleTarget (cyclePattern false 1) ≠ cycleTarget (cyclePattern true 1)) e
  intro a b hab
  obtain ⟨ha,hb,hea,heb,hend⟩ := hab
  have ea := ev false a ha
  simp only [hout, if_true, hd, PEqualNP.CircuitLowerBounds.GateOp.eval] at ea
  rw [cycleTargetRow _ _ ha] at ea
  simp [hea] at ea
  have ha15 := ea 15 h15
  have ha11 : (p false a).getD 11 false = true := by
    change (w false a).getD 15 false = true at ha15
    rw [read,if_pos rfl,Bool.false_or] at ha15
    exact ha15
  intro same
  have hb11 : (p false b).getD 11 false = true := same ▸ ha11
  have hh : ∀ j, j ≠ 0 → (w false b).getD j false = (w true b).getD j false := by
    intro j hj
    rw [read,read]
    split_ifs
    · rw [hb11, Bool.true_or, Bool.false_or]
    · exact peq b j hj
  have e := congrArg D.op.eval (List.map_congr_left (l := D.inputs)
      (fun j hj => hh j (fun h => h0 (h ▸ hj))))
  have hf := ev false b hb
  have ht := ev true b hb
  simp only [hout,if_true] at hf ht
  rw [hf,ht,cycleTargetRow _ _ hb,cycleTargetRow _ _ hb] at e
  simp [heb,hend] at e

private theorem cycleTen {α : Type} (gs : List α) (h : gs.length = 10) :
    ∃ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : α, gs = [x0,x1,x2,x3,x4,x5,x6,x7,x8,x9] := by
  obtain _ | ⟨x0,gs⟩ := gs
  · simp at h
  obtain _ | ⟨x1,gs⟩ := gs
  · simp at h
  obtain _ | ⟨x2,gs⟩ := gs
  · simp at h
  obtain _ | ⟨x3,gs⟩ := gs
  · simp at h
  obtain _ | ⟨x4,gs⟩ := gs
  · simp at h
  obtain _ | ⟨x5,gs⟩ := gs
  · simp at h
  obtain _ | ⟨x6,gs⟩ := gs
  · simp at h
  obtain _ | ⟨x7,gs⟩ := gs
  · simp at h
  obtain _ | ⟨x8,gs⟩ := gs
  · simp at h
  obtain _ | ⟨x9,gs⟩ := gs
  · simp at h
  cases gs with
  | nil => exact ⟨x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,rfl⟩
  | cons a gs => simp at h

end PEqualNP.Outside.L_meta_29920

open PEqualNP.Outside.L_meta_29920

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.L_meta_29920 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 8 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 11 ∈ (C.gates.get i).inputs ∧ 11 ≠ 0 ∧ 11 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 11 false = true)) := by
  rintro ⟨⟨gs,out⟩, i,k,hi,hfan,hsize,hev,hzero,hunique,hop,hand,hik,hlink,hw11,_⟩
  change gs.length = 10 at hsize
  obtain ⟨g0,g1,g2,g3,g4,g5,g6,g7,O,D,rfl⟩ := cycleTen gs hsize
  have hir : i = ⟨8,by change 8 < 10; decide⟩ := Fin.ext hi
  have hkr : k = ⟨9,by change 9 < 10; decide⟩ := Fin.ext (by change k.val = 9; have hk : k.val < 10 := k.isLt; omega)
  subst i
  subst k
  change 0 ∈ O.inputs at hzero
  change 11 ∈ O.inputs at hw11
  change O.op = .or at hop
  change D.op = .and at hand
  change 15 ∈ D.inputs at hlink
  let first := [g0,g1,g2,g3,g4,g5,g6,g7]
  let mid := [g1,g2,g3,g4]
  let tail3 := [g5,g6,g7]
  let p c r := first.foldl cycleStep (cycleInput c r)
  have hno : ∀ g ∈ first, 0 ∉ g.inputs := by
    intro g hg hz
    simp only [first,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact (by decide : (0 : Fin 10) ≠ 8) (hunique 0 hz)
      | exact (by decide : (1 : Fin 10) ≠ 8) (hunique 1 hz)
      | exact (by decide : (2 : Fin 10) ≠ 8) (hunique 2 hz)
      | exact (by decide : (3 : Fin 10) ≠ 8) (hunique 3 hz)
      | exact (by decide : (4 : Fin 10) ≠ 8) (hunique 4 hz)
      | exact (by decide : (5 : Fin 10) ≠ 8) (hunique 5 hz)
      | exact (by decide : (6 : Fin 10) ≠ 8) (hunique 6 hz)
      | exact (by decide : (7 : Fin 10) ≠ 8) (hunique 7 hz)
  have hd0 : 0 ∉ D.inputs := fun h => (by decide : (9 : Fin 10) ≠ 8) (hunique 9 h)
  have plen c r : (p c r).length = 15 := by rw [show p c r = _ from rfl,cycleFoldLen,cycleInputLen]; rfl
  have pzero c r : (p c r).getD 0 false = c := by
    change (first.foldl cycleStep _).getD 0 false = c
    rw [cycleFoldOld _ _ _ (by rw [cycleInputLen]; decide),cycleInputRead]
    rfl
  have peq r j (hj : j ≠ 0) : (p false r).getD j false = (p true r).getD j false := by
    apply cycleFoldSkip first hno _ _ (by simp only [cycleInputLen]) _ j hj
    intro k hk
    simp only [cycleInputRead,if_neg hk]
  have hoLen := (hfan O (by simp)).2
  have olist : O.inputs = [0,11] ∨ O.inputs = [11,0] := by
    rcases hg : O.inputs with _ | ⟨x, _ | ⟨y, _ | ⟨z,zs⟩⟩⟩ <;>
      simp_all only [List.mem_cons,List.not_mem_nil,or_false,List.length_cons,List.length_nil]
    all_goals grind
  have orEval c r : O.op.eval (O.inputs.map fun j => (p c r).getD j false) =
      (c || (p c r).getD 11 false) := by
    rcases olist with h | h <;> simp only [hop,h,List.map_cons,List.map_nil,
      PEqualNP.CircuitLowerBounds.GateOp.eval,List.any_cons,List.any_nil,id_eq,pzero,Bool.or_false]
    exact Bool.or_comm _ _
  have result := cycleTail p O D out plen pzero peq orEval hand hlink hd0
    (fun c r _ => hev (cyclePattern c r))
  have g0fan := hfan g0 (by simp)
  have glen : ∀ g ∈ mid, g.inputs.length ≤ 2 := by
    intro g hg
    apply (hfan g _).2
    simp only [mid,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp
  obtain ⟨t,ht,hagree⟩ := cycleFrontier mid glen 8 {11}
  apply cycleFirstImpossible g0 (by simpa using g0fan.1) g0fan.2 t (by simpa [mid] using ht)
  intro a b hab
  by_contra! hn
  have e := hagree (cycleStep (cycleInput false a) g0) (cycleStep (cycleInput false b) g0)
    (by simp [cycleStep,cycleInputLen]) (by simp [cycleStep,cycleInputLen]) hn 11 (by simp)
  have old (r : Nat) : (p false r).getD 11 false =
      (mid.foldl cycleStep (cycleStep (cycleInput false r) g0)).getD 11 false := by
    change (tail3.foldl cycleStep (mid.foldl cycleStep (cycleStep (cycleInput false r) g0))).getD 11 false = _
    apply cycleFoldOld
    rw [cycleFoldLen]
    simp [mid,cycleStep,cycleInputLen]
  exact result a b hab ((old a).trans (e.trans (old b).symm))

