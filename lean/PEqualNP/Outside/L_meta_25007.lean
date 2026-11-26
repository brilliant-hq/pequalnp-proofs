import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25007_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

abbrev Mask := BitVec 9

def row (p : Fin 9) : Fin 3 := ⟨p.val / 3, by omega⟩

def col (p : Fin 9) : Fin 3 := ⟨p.val % 3, by omega⟩

def rowMask (i : Fin 3) : Mask := ![7, 56, 448] i

def colMask (i : Fin 3) : Mask := ![73, 146, 292] i

def seed : List Mask := [0, 7, 56, 448, 73, 146, 292]

theorem rowBit (i : Fin 3) (p : Fin 9) :
    (rowMask i).getLsbD p.val = decide (row p = i) := by
  fin_cases i <;> fin_cases p <;> decide

theorem colBit (i : Fin 3) (p : Fin 9) :
    (colMask i).getLsbD p.val = decide (col p = i) := by
  fin_cases i <;> fin_cases p <;> decide

theorem three {n : ℕ} (S : Finset (Fin n)) (hn : 3 ≤ n)
    (hS : S.Nonempty) (hc : Sᶜ.Nonempty) :
    ∃ (u : Fin 3 → Fin n) (b : Bool), Function.Injective u ∧
      ∀ i, decide (u i ∈ S) = if i = 0 then b else !b := by
  have select (x y z : Fin n) (b : Bool) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
      (hx : decide (x ∈ S) = b) (hy : decide (y ∈ S) = !b)
      (hz : decide (z ∈ S) = !b) :
      ∃ (u : Fin 3 → Fin n) (b : Bool), Function.Injective u ∧
        ∀ i, decide (u i ∈ S) = if i = 0 then b else !b := by
    refine ⟨![x, y, z], b, ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    · intro i
      fin_cases i <;> simpa [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  by_cases hlarge : 1 < S.card
  · rcases Finset.one_lt_card.mp hlarge with ⟨y, hy, z, hz, hyz⟩
    rcases hc with ⟨x, hx⟩
    have hx' := Finset.mem_compl.mp hx
    exact select x y z false (fun h => hx' (h ▸ hy)) (fun h => hx' (h ▸ hz))
      hyz (by simp [hx']) (by simp [hy]) (by simp [hz])
  · have hcard : Sᶜ.card = n - S.card := by simp [Finset.card_compl]
    have hlarge' : 1 < Sᶜ.card := by omega
    rcases Finset.one_lt_card.mp hlarge' with ⟨y, hy, z, hz, hyz⟩
    rcases hS with ⟨x, hx⟩
    have hy' := Finset.mem_compl.mp hy
    have hz' := Finset.mem_compl.mp hz
    exact select x y z true (fun h => hy' (h ▸ hx)) (fun h => hz' (h ▸ hx))
      hyz (by simp [hx]) (by simp [hy']) (by simp [hz'])

theorem each_value {n m : ℕ} (w : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach w v).getD i false = decide (i = w.val ∨ i = n + v.val) := by
  have hw := w.isLt
  have hv := v.isLt
  apply Bool.eq_iff_iff.2
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs <;> simp [Fin.ext_iff] <;> omega

def covered (xs : Fin 9 → List Bool) (pool : List Mask) : Prop :=
  ∀ i : ℕ, ∃ a ∈ pool, ∀ p, (xs p).getD i false = a.getLsbD p.val

theorem inputCovered {n : ℕ} (u v : Fin 3 → Fin n)
    (hu : Function.Injective u) (hv : Function.Injective v) :
    covered (fun p => oneEach (u (row p)) (v (col p))) seed := by
  intro i
  by_cases hr : ∃ a, i = (u a).val
  · obtain ⟨a, rfl⟩ := hr
    refine ⟨rowMask a, ?_, ?_⟩
    · fin_cases a <;> decide
    · intro p
      rw [rowBit, each_value]
      congr 1
      apply propext
      have hb := (u a).isLt
      constructor
      · rintro (h | h)
        · exact hu (Fin.ext h.symm)
        · omega
      · intro h
        exact Or.inl (by rw [h])
  · by_cases hc : ∃ b, i = n + (v b).val
    · obtain ⟨b, h⟩ := hc
      refine ⟨colMask b, ?_, ?_⟩
      · fin_cases b <;> decide
      · intro p
        rw [colBit, each_value]
        congr 1
        apply propext
        constructor
        · rintro (e | e)
          · exact (hr ⟨row p, e⟩).elim
          · exact hv (Fin.ext (by omega))
        · intro e
          exact Or.inr (by rw [e, h])
    · refine ⟨0, by decide, fun p => ?_⟩
      rw [each_value]
      simp [show i ≠ (u (row p)).val from fun h => hr ⟨row p, h⟩,
        show i ≠ n + (v (col p)).val from fun h => hc ⟨col p, h⟩]

def target (b c : Bool) : Mask := if b = c then 433 else 78

theorem targetBit {n : ℕ} {S T : Finset (Fin n)} {u v : Fin 3 → Fin n}
    {b c : Bool} (hu : ∀ i, decide (u i ∈ S) = if i = 0 then b else !b)
    (hv : ∀ i, decide (v i ∈ T) = if i = 0 then c else !c) (p : Fin 9) :
    decide ((u (row p) ∈ S ∧ v (col p) ∈ T) ∨ (u (row p) ∉ S ∧ v (col p) ∉ T)) =
      (target b c).getLsbD p.val := by
  have same (P Q : Prop) [Decidable P] [Decidable Q] :
      decide ((P ∧ Q) ∨ (¬ P ∧ ¬ Q)) = (decide P == decide Q) := by
    by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]
  rw [same, hu, hv]
  fin_cases p <;> cases b <;> cases c <;> decide

def choices (pool : List Mask) : List Mask :=
  ([0, 511] ++ pool ++ pool.map (fun a => ~~~a) ++
    pool.flatMap (fun a => pool.flatMap (fun b => [a &&& b, a ||| b]))).eraseDups

theorem memChoices {pool : List Mask} {x : Mask} :
    x ∈ choices pool ↔ x = 0 ∨ x = 511 ∨ x ∈ pool ∨
      (∃ a ∈ pool, x = ~~~a) ∨
      ∃ a ∈ pool, ∃ b ∈ pool, x = a &&& b ∨ x = a ||| b := by
  simp only [choices, List.mem_eraseDups, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_flatMap]
  simp only [eq_comm (a := x), or_assoc]

theorem gateMask {xs : Fin 9 → List Bool} {pool : List Mask} (hxs : covered xs pool)
    (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) :
    ∃ a ∈ choices pool, ∀ p, g.op.eval (g.inputs.map fun i => (xs p).getD i false) =
      a.getLsbD p.val := by
  have ha (x : Mask) (hx : x ∈ pool) : x ∈ choices pool :=
    memChoices.mpr (Or.inr (Or.inr (Or.inl hx)))
  have hn (x : Mask) (hx : x ∈ pool) : ~~~x ∈ choices pool :=
    memChoices.mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨x, hx, rfl⟩))))
  have hb (x y : Mask) (hx : x ∈ pool) (hy : y ∈ pool) :
      x &&& y ∈ choices pool ∧ x ||| y ∈ choices pool :=
    ⟨memChoices.mpr (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, hx, y, hy, Or.inl rfl⟩)))),
      memChoices.mpr (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, hx, y, hy, Or.inr rfl⟩))))⟩
  rcases g with ⟨op, l⟩
  change op ∈ _ at hop
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases l with _ | ⟨i, _ | ⟨j, _ | ⟨k, ks⟩⟩⟩
  · rcases hop with rfl | rfl | rfl
    · refine ⟨511, memChoices.mpr (Or.inr (Or.inl rfl)), fun p => ?_⟩
      change true = (511 : Mask).getLsbD p.val
      fin_cases p <;> decide
    · exact ⟨0, memChoices.mpr (Or.inl rfl), by simp [GateOp.eval]⟩
    · refine ⟨511, memChoices.mpr (Or.inr (Or.inl rfl)), fun p => ?_⟩
      change true = (511 : Mask).getLsbD p.val
      fin_cases p <;> decide
  · obtain ⟨x, hx, ex⟩ := hxs i
    rcases hop with rfl | rfl | rfl
    · refine ⟨x, ha x hx, fun p => ?_⟩
      simpa [GateOp.eval, List.getD_eq_getElem?_getD] using ex p
    · refine ⟨x, ha x hx, fun p => ?_⟩
      simpa [GateOp.eval, List.getD_eq_getElem?_getD] using ex p
    · refine ⟨~~~x, hn x hx, fun p => ?_⟩
      have hp := p.isLt
      simp [GateOp.eval, hp, List.getD_eq_getElem?_getD] at ex ⊢
      exact ex p
  · obtain ⟨x, hx, ex⟩ := hxs i
    obtain ⟨y, hy, ey⟩ := hxs j
    rcases hop with rfl | rfl | rfl
    · refine ⟨x &&& y, (hb x y hx hy).1, fun p => ?_⟩
      rw [BitVec.getLsbD_and]
      simpa [GateOp.eval, List.getD_eq_getElem?_getD] using congrArg₂ (· && ·) (ex p) (ey p)
    · refine ⟨x ||| y, (hb x y hx hy).2, fun p => ?_⟩
      rw [BitVec.getLsbD_or]
      simpa [GateOp.eval, List.getD_eq_getElem?_getD] using congrArg₂ (· || ·) (ex p) (ey p)
    · refine ⟨~~~x, hn x hx, fun p => ?_⟩
      have hp := p.isLt
      simp [GateOp.eval, hp, List.getD_eq_getElem?_getD] at ex ⊢
      exact ex p
  · simp at hlen

def step (xs : Fin 9 → List Bool) (g : Gate) (p : Fin 9) : List Bool :=
  xs p ++ [g.op.eval (g.inputs.map fun i => (xs p).getD i false)]

theorem advance {xs : Fin 9 → List Bool} {pool : List Mask} {l : ℕ}
    (hx : covered xs pool) (h0 : 0 ∈ pool) (hL : ∀ p, (xs p).length = l)
    (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) :
    ∃ a ∈ choices pool, covered (step xs g) (a :: pool) ∧
      ∀ p, (step xs g p).length = l + 1 := by
  obtain ⟨a, ha, ea⟩ := gateMask hx g hop.1 hop.2
  refine ⟨a, ha, ?_, fun p => by simp [step, hL]⟩
  intro i
  by_cases hi : i < l
  · obtain ⟨x, hm, ex⟩ := hx i
    refine ⟨x, List.mem_cons_of_mem _ hm, fun p => ?_⟩
    have hlt : i < (xs p).length := (hL p).symm ▸ hi
    rw [step, List.getD_append _ _ _ _ hlt]
    exact ex p
  · have hle : l ≤ i := by omega
    by_cases e : i = l
    · subst i
      refine ⟨a, List.mem_cons_self, fun p => ?_⟩
      have hre : (xs p).length ≤ l := (hL p).le
      simpa [step, List.getD_eq_getElem?_getD, List.getElem?_append_right hre, hL p] using ea p
    · refine ⟨0, List.mem_cons_of_mem _ h0, fun p => ?_⟩
      have hout : (step xs g p).length ≤ i := by simp [step, hL]; omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hout]

def firstMasks : List Mask :=
  [0, 1, 2, 4, 7, 8, 16, 32, 56, 63, 64, 73, 79, 121, 128, 146,
    151, 186, 219, 256, 292, 295, 316, 365, 438, 448, 455, 457, 466, 484, 504, 511]

def pairOK (a b : Mask) : Bool :=
  [a, b, ~~~a, ~~~b, a &&& b, a ||| b].all fun z => z != 433 && z != 78

theorem pairCertificate {a b : Mask} (ha : a ∈ choices seed)
    (hb : b ∈ choices (a :: seed)) : pairOK a b = true := by
  have hfirst : (choices seed).toFinset ⊆ firstMasks.toFinset := by decide
  have hm : a ∈ firstMasks := List.mem_toFinset.mp (hfirst (List.mem_toFinset.mpr ha))
  have hall : (choices (a :: seed)).all (pairOK a) = true := by
    simp only [firstMasks, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact List.all_eq_true.mp hall b hb

theorem pairNe {a b : Mask} (ha : a ∈ choices seed) (hb : b ∈ choices (a :: seed))
    (x : Mask) (hx : x ∈ [a, b, ~~~a, ~~~b, a &&& b, a ||| b]) :
    x ≠ 433 ∧ x ≠ 78 := by
  have h := List.all_eq_true.mp (pairCertificate ha hb) x hx
  simpa using h

def isTarget (t : Mask) : Prop := t = 433 ∨ t = 78

theorem seedFree {t : Mask} (ht : isTarget t) {x : Mask} (hx : x ∈ seed) :
    x ≠ t ∧ ~~~x ≠ t ∧ x &&& t ≠ t ∧ (x ||| t = t → x = 0) := by
  simp only [seed, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases ht with rfl | rfl <;>
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem finalFree {a b : Mask} (ha : a ∈ choices seed) (hb : b ∈ choices (a :: seed))
    {t : Mask} (ht : isTarget t) : t ∉ choices (b :: a :: seed) := by
  have pairs (x : Mask) (hx : x ∈ [a, b, ~~~a, ~~~b, a &&& b, a ||| b]) : x ≠ t := by
    rcases ht with rfl | rfl
    · exact (pairNe ha hb x hx).1
    · exact (pairNe ha hb x hx).2
  have free (x : Mask) (hx : x ∈ b :: a :: seed) : x ≠ t ∧ ~~~x ≠ t := by
    simp only [List.mem_cons] at hx
    rcases hx with hxb | hxa | hm
    · subst x
      exact ⟨pairs b (by simp), pairs (~~~b) (by simp)⟩
    · subst x
      exact ⟨pairs a (by simp), pairs (~~~a) (by simp)⟩
    · exact ⟨(seedFree ht hm).1, (seedFree ht hm).2.1⟩
  have mix (x y : Mask) (hx : x ∈ seed) (hy : y ∈ b :: a :: seed) :
      x &&& y ≠ t ∧ x ||| y ≠ t := by
    have hs := seedFree ht hx
    constructor
    · intro e
      apply hs.2.2.1
      calc
        x &&& t = x &&& (x &&& y) := by rw [e]
        _ = x &&& y := by rw [← BitVec.and_assoc, BitVec.and_self]
        _ = t := e
    · intro e
      have hsub : x ||| t = t := by
        calc
          x ||| t = x ||| (x ||| y) := by rw [e]
          _ = x ||| y := by rw [← BitVec.or_assoc, BitVec.or_self]
          _ = t := e
      have hzero := hs.2.2.2 hsub
      apply (free y hy).1
      simpa [hzero] using e
  intro h
  rcases memChoices.mp h with he | he | hm | ⟨x, hx, he⟩ | ⟨x, hx, y, hy, he⟩
  · exact (seedFree ht (show (0 : Mask) ∈ seed by decide)).1 he.symm
  · rcases ht with rfl | rfl <;> contradiction
  · exact (free t hm).1 rfl
  · exact (free x hx).2 he.symm
  · have both : x &&& y ≠ t ∧ x ||| y ≠ t := by
      rcases List.mem_cons.mp hx with hxb | hx
      · subst x
        rcases List.mem_cons.mp hy with hyb | hy
        · subst y
          simpa using And.intro (free b (by simp)).1 (free b (by simp)).1
        · rcases List.mem_cons.mp hy with hya | hy
          · subst y
            rw [BitVec.and_comm b a, BitVec.or_comm b a]
            exact ⟨pairs _ (by simp), pairs _ (by simp)⟩
          · rw [BitVec.and_comm b y, BitVec.or_comm b y]
            exact mix y b hy (by simp)
      · rcases List.mem_cons.mp hx with hxa | hx
        · subst x
          rcases List.mem_cons.mp hy with hyb | hy
          · subst y
            exact ⟨pairs _ (by simp), pairs _ (by simp)⟩
          · rcases List.mem_cons.mp hy with hya | hy
            · subst y
              simpa using And.intro (free a (by simp)).1 (free a (by simp)).1
            · rw [BitVec.and_comm a y, BitVec.or_comm a y]
              exact mix y a hy (by simp)
        · exact mix x y hx hy
    exact he.elim (fun e => both.1 e.symm) (fun e => both.2 e.symm)

theorem targetExclusion (C : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo C)
    (hN : C.size ≤ 3) {xs : Fin 9 → List Bool} {l : ℕ} (hx : covered xs seed)
    (hL : ∀ p, (xs p).length = l) {t : Mask} (ht : isTarget t) :
    ¬ ∀ p, C.eval (xs p) = t.getLsbD p.val := by
  intro hOutput
  have extract {a b : Mask} (ha : a ∈ choices seed) (hb : b ∈ choices (a :: seed))
      {ws : Fin 9 → List Bool} {pool : List Mask} (hw : covered ws pool)
      (hpool : ∀ z ∈ pool, z ∈ choices (b :: a :: seed))
      (hout : ∀ p, (ws p).getD C.output false = t.getLsbD p.val) : False := by
    obtain ⟨z, hz, he⟩ := hw C.output
    have e : z = t := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      exact (he ⟨i, hi⟩).symm.trans (hout ⟨i, hi⟩)
    exact finalFree ha hb ht (e ▸ hpool z hz)
  have retain {pool : List Mask} {z : Mask} (hz : z ∈ pool) : z ∈ choices pool :=
    memChoices.mpr (Or.inr (Or.inr (Or.inl hz)))
  have addZero (pool : List Mask) : 0 ∈ choices pool := memChoices.mpr (Or.inl rfl)
  have h0 : (0 : Mask) ∈ seed := by decide
  have hgates : C.gates.length ≤ 3 := hN
  rcases e : C.gates with _ | ⟨g, _ | ⟨h, _ | ⟨k, _ | ⟨j, js⟩⟩⟩⟩
  · exact extract (addZero seed) (addZero (0 :: seed)) hx
      (fun _ hz => retain (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz)))
      (by simpa [Circuit.eval, Circuit.wires, e] using hOutput)
  · obtain ⟨a, ha, h1, hl1⟩ := advance hx h0 hL g (hC g (by simp [e]))
    exact extract ha (addZero (a :: seed)) h1
      (fun _ hz => retain (List.mem_cons_of_mem _ hz))
      (by simpa [Circuit.eval, Circuit.wires, e, step] using hOutput)
  · obtain ⟨a, ha, h1, hl1⟩ := advance hx h0 hL g (hC g (by simp [e]))
    obtain ⟨b, hb, h2, hl2⟩ := advance h1 (List.mem_cons_of_mem _ h0) hl1 h (hC h (by simp [e]))
    exact extract ha hb h2 (fun _ hz => retain hz)
      (by simpa [Circuit.eval, Circuit.wires, e, step] using hOutput)
  · obtain ⟨a, ha, h1, hl1⟩ := advance hx h0 hL g (hC g (by simp [e]))
    obtain ⟨b, hb, h2, hl2⟩ := advance h1 (List.mem_cons_of_mem _ h0) hl1 h (hC h (by simp [e]))
    obtain ⟨c, hc, h3, _⟩ := advance h2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h0))
      hl2 k (hC k (by simp [e]))
    exact extract ha hb h3
      (fun z hz => (List.mem_cons.mp hz).elim (fun eq => eq.symm ▸ hc) retain)
      (by simpa [Circuit.eval, Circuit.wires, e, step] using hOutput)
  · simp [e] at hgates
    omega

end PEqualNP.Outside.L_meta_25007_aux

open PEqualNP.Outside.L_meta_25007_aux in

theorem PEqualNP.Outside.L_meta_25007 : ∀ (n : ℕ) (S T : Finset (Fin n)), 3 ≤ n → S.Nonempty → Sᶜ.Nonempty → T.Nonempty → Tᶜ.Nonempty → ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 3 ∧ PEqualNP.Represents.Represents (fun u v : Fin n => decide ((u ∈ S ∧ v ∈ T) ∨ (u ∉ S ∧ v ∉ T))) C := by
  intro n S T hn hS hSc hT hTc h
  obtain ⟨C, hC, hN, hR⟩ := h
  obtain ⟨u, b, hu, hbu⟩ := three S hn hS hSc
  obtain ⟨v, c, hv, hcv⟩ := three T hn hT hTc
  have ht : isTarget (target b c) := by
    cases b <;> cases c <;> simp [isTarget, target]
  apply targetExclusion C hC hN (inputCovered u v hu hv)
    (l := n+n) (fun p => by simp [PEqualNP.Represents.oneEach]) ht
  intro p
  exact (hR (u (row p)) (v (col p))).trans (targetBit hbu hcv p)
