import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1337

open PEqualNP.CircuitLowerBounds

def isNot (op : GateOp) : Bool :=
  match op with
  | GateOp.not => true
  | _ => false

lemma decide_eq_not (op : GateOp) (inst : Decidable (op = GateOp.not)) :
    @decide (op = GateOp.not) inst = isNot op := by
  cases op <;> simp [isNot]

lemma isNot_eq_true_iff (op : GateOp) : isNot op = true ↔ op = GateOp.not := by
  cases op <;> simp [isNot]

def evalStep (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def evalGates (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [evalStep w g]) x

lemma evalGates_nil (x : List Bool) : evalGates [] x = x := rfl

lemma evalGates_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    evalGates (g :: gs) x = evalGates gs (x ++ [evalStep x g]) := rfl

lemma evalGates_append (gs₁ gs₂ : List Gate) (x : List Bool) :
    evalGates (gs₁ ++ gs₂) x = evalGates gs₂ (evalGates gs₁ x) := by
  simp [evalGates, List.foldl_append]

lemma evalGates_concat (gs : List Gate) (g : Gate) (x : List Bool) :
    evalGates (gs ++ [g]) x = evalGates gs x ++ [evalStep (evalGates gs x) g] := by
  simp [evalGates, List.foldl_append]

lemma evalGates_length (gs : List Gate) (x : List Bool) :
    (evalGates gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [evalGates]
  | cons g gs ih =>
    rw [evalGates_cons, ih]
    simp
    omega

lemma list_getD_append_left {α : Type*} (l₁ l₂ : List α) (i : Nat) (d : α)
    (hi : i < l₁.length) : (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

lemma list_getD_append_right {α : Type*} (l₁ l₂ : List α) (i : Nat) (d : α)
    (hi : l₁.length ≤ i) : (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
  simp [List.getD, List.getElem?_append_right hi]

lemma list_getD_concat_last {α : Type*} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  rw [list_getD_append_right l [a] l.length d (Nat.le_refl _)]
  simp

lemma evalGates_getD_lt (gs : List Gate) (x : List Bool) (i : Nat) (hi : i < x.length) :
    (evalGates gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [evalGates_cons]
    have hi' : i < (x ++ [evalStep x g]).length := by
      simp
      omega
    rw [ih (x ++ [evalStep x g]) hi']
    exact list_getD_append_left x [evalStep x g] i false hi

lemma evalGates_append_getD_lt (gs₁ gs₂ : List Gate) (x : List Bool) (i : Nat)
    (hi : i < x.length + gs₁.length) :
    (evalGates (gs₁ ++ gs₂) x).getD i false = (evalGates gs₁ x).getD i false := by
  rw [evalGates_append]
  apply evalGates_getD_lt
  rw [evalGates_length]
  exact hi

def FanInTwoList (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def Monotone2List (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def ReadsBackList (n : Nat) (gs : List Gate) : Prop :=
  ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + j

lemma monotone2List_to_fanInTwoList {gs : List Gate} (h : Monotone2List gs) :
    FanInTwoList gs := by
  intro g hg
  rcases h g hg with ⟨hop, hlen⟩
  refine ⟨?_, hlen⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
  rcases hop with h1 | h2
  · left; exact h1
  · right; left; exact h2

lemma monotone2List_append {gs₁ gs₂ : List Gate}
    (h1 : Monotone2List gs₁) (h2 : Monotone2List gs₂) :
    Monotone2List (gs₁ ++ gs₂) := by
  intro g hg
  rcases List.mem_append.mp hg with hg₁ | hg₂
  · exact h1 g hg₁
  · exact h2 g hg₂

lemma readsBackList_append {n : Nat} {gs₁ gs₂ : List Gate}
    (h1 : ReadsBackList n gs₁) (h2 : ReadsBackList (n + gs₁.length) gs₂) :
    ReadsBackList n (gs₁ ++ gs₂) := by
  intro j hj i hi
  by_cases hlt : j < gs₁.length
  · rw [list_getD_append_left gs₁ gs₂ j _ hlt] at hi
    exact h1 j hlt i hi
  · have hge : gs₁.length ≤ j := Nat.le_of_not_lt hlt
    rw [list_getD_append_right gs₁ gs₂ j _ hge] at hi
    have hj2 : j - gs₁.length < gs₂.length := by
      simp only [List.length_append] at hj
      omega
    have hlt2 := h2 (j - gs₁.length) hj2 i hi
    omega

lemma readsBackList_prefix {n : Nat} {gs : List Gate} {g : Gate}
    (h : ReadsBackList n (gs ++ [g])) : ReadsBackList n gs := by
  intro j hj i hi
  have hj' : j < (gs ++ [g]).length := by simp; omega
  have hi' : i ∈ ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).inputs := by
    rw [list_getD_append_left gs [g] j _ hj]
    exact hi
  exact h j hj' i hi'

lemma readsBackList_last {n : Nat} {gs : List Gate} {g : Gate}
    (h : ReadsBackList n (gs ++ [g])) : ∀ i ∈ g.inputs, i < n + gs.length := by
  intro i hi
  have hj' : gs.length < (gs ++ [g]).length := by simp
  have hi' : i ∈ ((gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩).inputs := by
    rw [list_getD_concat_last]
    exact hi
  exact h gs.length hj' i hi'

def notCountList (gs : List Gate) : Nat :=
  (gs.filter fun g => isNot g.op).length

lemma notCountList_nil : notCountList [] = 0 := rfl

lemma notCountList_concat (gs : List Gate) (g : Gate) :
    notCountList (gs ++ [g]) = notCountList gs + if isNot g.op then 1 else 0 := by
  unfold notCountList
  rw [List.filter_append, List.length_append]
  cases h : isNot g.op <;> simp [h]

lemma notCount_eq (C : Circuit) :
    PEqualNP.NotBracket.notCount C = notCountList C.gates := by
  unfold PEqualNP.NotBracket.notCount notCountList
  congr 1
  apply List.filter_congr
  intro g _
  exact decide_eq_not g.op _

def fromBitsAux (acc : Nat) (bs : List Bool) : Nat :=
  bs.foldl (fun a b => 2 * a + if b then 1 else 0) acc

def fromBits (bs : List Bool) : Nat :=
  fromBitsAux 0 bs

lemma fromBitsAux_eq (acc : Nat) (bs : List Bool) :
    fromBitsAux acc bs = acc * 2 ^ bs.length + fromBits bs := by
  induction bs generalizing acc with
  | nil => simp [fromBits, fromBitsAux]
  | cons b bs ih =>
    simp only [fromBits, fromBitsAux, List.foldl_cons, List.length_cons] at ih ⊢
    rw [ih (2 * acc + if b then 1 else 0)]
    rw [ih (2 * 0 + if b then 1 else 0)]
    have hpow : 2 ^ (bs.length + 1) = 2 * 2 ^ bs.length := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow]
    cases b <;> ring

lemma fromBits_nil : fromBits [] = 0 := rfl

lemma fromBits_cons (b : Bool) (bs : List Bool) :
    fromBits (b :: bs) = (if b then 2 ^ bs.length else 0) + fromBits bs := by
  change fromBitsAux (2 * 0 + if b then 1 else 0) bs =
    (if b then 2 ^ bs.length else 0) + fromBits bs
  rw [fromBitsAux_eq]
  cases b <;> simp

lemma fromBits_concat (bs : List Bool) (b : Bool) :
    fromBits (bs ++ [b]) = 2 * fromBits bs + if b then 1 else 0 := by
  simp [fromBits, fromBitsAux, List.foldl_append]

lemma fromBits_lt (bs : List Bool) : fromBits bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [fromBits_nil]
  | cons b bs ih =>
    rw [fromBits_cons, List.length_cons, Nat.pow_succ]
    cases b <;> simp <;> omega

lemma fromBits_inj {bs₁ bs₂ : List Bool} (hlen : bs₁.length = bs₂.length)
    (heq : fromBits bs₁ = fromBits bs₂) : bs₁ = bs₂ := by
  induction bs₁ generalizing bs₂ with
  | nil =>
    cases bs₂ with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons b₁ t₁ ih =>
    cases bs₂ with
    | nil => simp at hlen
    | cons b₂ t₂ =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [fromBits_cons, fromBits_cons, hlen] at heq
      have h1 := fromBits_lt t₁
      have h2 := fromBits_lt t₂
      rw [hlen] at h1
      have hb : b₁ = b₂ := by
        cases b₁ <;> cases b₂ <;> simp at heq ⊢ <;> omega
      subst hb
      have ht : fromBits t₁ = fromBits t₂ := by
        cases b₁ <;> simp at heq <;> omega
      rw [ih hlen ht]

def refBits (b v : Nat) : List Bool :=
  (List.range b).map (fun r => v.testBit (b - 1 - r))

lemma refBits_length (b v : Nat) : (refBits b v).length = b := by
  simp [refBits]

lemma refBits_getD (b v r : Nat) (hr : r < b) :
    (refBits b v).getD r false = v.testBit (b - 1 - r) := by
  simp [refBits, List.getD, hr]

lemma refBits_succ (b v : Nat) :
    refBits (b + 1) v = refBits b (v / 2) ++ [v.testBit 0] := by
  unfold refBits
  rw [List.range_succ, List.map_append]
  simp only [List.map_singleton, Nat.add_sub_cancel, Nat.sub_self]
  congr 1
  apply List.map_congr_left
  intro r hr
  rw [List.mem_range] at hr
  have hsub : b - r = (b - 1 - r) + 1 := by omega
  rw [hsub, Nat.testBit_succ]

lemma fromBits_refBits (b v : Nat) (hv : v < 2 ^ b) :
    fromBits (refBits b v) = v := by
  induction b generalizing v with
  | zero =>
    simp only [Nat.pow_zero] at hv
    have : v = 0 := by omega
    subst this
    rfl
  | succ b ih =>
    rw [refBits_succ, fromBits_concat]
    have hv' : v / 2 < 2 ^ b := by
      rw [Nat.pow_succ] at hv
      omega
    rw [ih (v / 2) hv']
    rw [Nat.testBit_zero]
    have hmod : v % 2 = 0 ∨ v % 2 = 1 := Nat.mod_two_eq_zero_or_one v
    rcases hmod with h0 | h1
    · simp [h0]
      omega
    · simp [h1]
      omega

def foldBool (s0 : Bool) : List (Bool × Bool) → Bool
  | [] => s0
  | (rb, db) :: rest =>
    if rb then db && foldBool s0 rest else db || foldBool s0 rest

lemma foldBool_spec_ge (ref u simB : List Bool)
    (h1 : ref.length = u.length) (h2 : simB.length = u.length)
    (hagree : ∀ r < ref.length, (∀ t < r, u.getD t false = ref.getD t false) →
      simB.getD r false = u.getD r false) :
    foldBool true (ref.zip simB) = true ↔ fromBits ref ≤ fromBits u := by
  induction ref generalizing u simB with
  | nil =>
    cases u with
    | nil =>
      cases simB with
      | nil => simp [foldBool, fromBits_nil]
      | cons _ _ => simp at h2
    | cons _ _ => simp at h1
  | cons rb rrest ih =>
    cases u with
    | nil => simp at h1
    | cons ub urest =>
      cases simB with
      | nil => simp at h2
      | cons sb srest =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
        have hhead : sb = ub := by
          have h0 := hagree 0 (by simp) (by intro t ht; omega)
          simpa [List.getD] using h0
        simp only [List.zip_cons_cons, foldBool, hhead]
        rw [fromBits_cons, fromBits_cons, h1]
        have hlt_r := fromBits_lt rrest
        have hlt_u := fromBits_lt urest
        rw [h1] at hlt_r
        by_cases heq : rb = ub
        · subst heq
          have hagree' : ∀ r < rrest.length,
              (∀ t < r, urest.getD t false = rrest.getD t false) →
              srest.getD r false = urest.getD r false := by
            intro r hr hpre
            have h := hagree (r + 1) (by simp; omega) (by
              intro t ht
              cases t with
              | zero => simp [List.getD]
              | succ t' =>
                simpa [List.getD] using hpre t' (by omega))
            simpa [List.getD] using h
          have ih' := ih urest srest h1 h2 hagree'
          cases rb <;> simp [ih']
        · cases rb <;> cases ub
          · exact absurd rfl heq
          · simp
            omega
          · simp
            omega
          · exact absurd rfl heq

lemma foldBool_spec_gt (ref u simB : List Bool)
    (h1 : ref.length = u.length) (h2 : simB.length = u.length)
    (hagree : ∀ r < ref.length, (∀ t < r, u.getD t false = ref.getD t false) →
      simB.getD r false = u.getD r false) :
    foldBool false (ref.zip simB) = true ↔ fromBits ref < fromBits u := by
  induction ref generalizing u simB with
  | nil =>
    cases u with
    | nil =>
      cases simB with
      | nil => simp [foldBool, fromBits_nil]
      | cons _ _ => simp at h2
    | cons _ _ => simp at h1
  | cons rb rrest ih =>
    cases u with
    | nil => simp at h1
    | cons ub urest =>
      cases simB with
      | nil => simp at h2
      | cons sb srest =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
        have hhead : sb = ub := by
          have h0 := hagree 0 (by simp) (by intro t ht; omega)
          simpa [List.getD] using h0
        simp only [List.zip_cons_cons, foldBool, hhead]
        rw [fromBits_cons, fromBits_cons, h1]
        have hlt_r := fromBits_lt rrest
        have hlt_u := fromBits_lt urest
        rw [h1] at hlt_r
        by_cases heq : rb = ub
        · subst heq
          have hagree' : ∀ r < rrest.length,
              (∀ t < r, urest.getD t false = rrest.getD t false) →
              srest.getD r false = urest.getD r false := by
            intro r hr hpre
            have h := hagree (r + 1) (by simp; omega) (by
              intro t ht
              cases t with
              | zero => simp [List.getD]
              | succ t' =>
                simpa [List.getD] using hpre t' (by omega))
            simpa [List.getD] using h
          have ih' := ih urest srest h1 h2 hagree'
          cases rb <;> simp [ih']
        · cases rb <;> cases ub
          · exact absurd rfl heq
          · simp
            omega
          · simp
            omega
          · exact absurd rfl heq

def actualDrv (w : List Bool) (g : Gate) : Bool :=
  match g.inputs with
  | [] => false
  | i :: _ => w.getD i false

lemma evalStep_not (w : List Bool) (g : Gate) (hg : g.op = GateOp.not) :
    evalStep w g = !(actualDrv w g) := by
  unfold evalStep actualDrv
  rw [hg]
  cases g.inputs with
  | nil => rfl
  | cons i rest => rfl

def actualRun (gs : List Gate) (inp : List Bool) : List Bool × List Bool :=
  gs.foldl (fun st g =>
    (st.1 ++ [evalStep st.1 g], if isNot g.op then st.2 ++ [actualDrv st.1 g] else st.2)) (inp, [])

lemma actualRun_fst (gs : List Gate) (inp : List Bool) :
    (actualRun gs inp).1 = evalGates gs inp := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    simp only [actualRun, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
    rw [ih, evalGates_concat]

lemma actualRun_concat (gs : List Gate) (g : Gate) (inp : List Bool) :
    actualRun (gs ++ [g]) inp =
      (evalGates gs inp ++ [evalStep (evalGates gs inp) g],
       if isNot g.op then (actualRun gs inp).2 ++ [actualDrv (evalGates gs inp) g]
       else (actualRun gs inp).2) := by
  have h1 := actualRun_fst gs inp
  unfold actualRun
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  unfold actualRun at h1
  rw [h1]

lemma actualRun_snd_length (gs : List Gate) (inp : List Bool) :
    (actualRun gs inp).2.length = notCountList gs := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [actualRun_concat, notCountList_concat]
    cases isNot g.op <;> simp [ih]

def rankList (n : Nat) (gs : List Gate) (w : List Bool) : Nat :=
  let idxs := (List.range gs.length).filter (fun j => isNot (gs.getD j ⟨GateOp.or, []⟩).op)
  idxs.foldl (fun acc j => 2 * acc + if w.getD (n + j) false then 0 else 1) 0

lemma rankList_eq_fromBits (gs : List Gate) (inp : List Bool) :
    rankList inp.length gs (evalGates gs inp) = fromBits (actualRun gs inp).2 := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [actualRun_concat]
    unfold rankList
    rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append]
    have hfilt_pre :
        (List.range gs.length).filter
          (fun j => isNot ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).op) =
        (List.range gs.length).filter
          (fun j => isNot (gs.getD j ⟨GateOp.or, []⟩).op) := by
      apply List.filter_congr
      intro j hj
      rw [List.mem_range] at hj
      rw [list_getD_append_left gs [g] j _ hj]
    rw [hfilt_pre]
    have hlast_get : ((gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩) = g :=
      list_getD_concat_last gs g ⟨GateOp.or, []⟩
    rw [List.foldl_append]
    have hfold_pre :
        ((List.range gs.length).filter (fun j => isNot (gs.getD j ⟨GateOp.or, []⟩).op)).foldl
          (fun acc j => 2 * acc + if (evalGates (gs ++ [g]) inp).getD (inp.length + j) false then 0 else 1) 0 =
        rankList inp.length gs (evalGates gs inp) := by
      unfold rankList
      have hcongr : ∀ (l : List Nat) (acc : Nat), (∀ j ∈ l, j < gs.length) →
          l.foldl (fun a j => 2 * a + if (evalGates (gs ++ [g]) inp).getD (inp.length + j) false then 0 else 1) acc =
          l.foldl (fun a j => 2 * a + if (evalGates gs inp).getD (inp.length + j) false then 0 else 1) acc := by
        intro l
        induction l with
        | nil => intro _ _; rfl
        | cons j l ih_l =>
          intro acc hall
          simp only [List.foldl_cons]
          have hj : j < gs.length := hall j (by simp)
          have hget : (evalGates (gs ++ [g]) inp).getD (inp.length + j) false =
              (evalGates gs inp).getD (inp.length + j) false :=
            evalGates_append_getD_lt gs [g] inp (inp.length + j) (by omega)
          rw [hget]
          exact ih_l _ (fun k hk => hall k (by simp [hk]))
      apply hcongr
      intro j hj
      exact List.mem_range.mp (List.mem_filter.mp hj).1
    rw [hfold_pre, ih]
    simp only [List.filter_cons, hlast_get, List.filter_nil]
    cases hnot : isNot g.op
    · simp
    · simp only [ite_true, List.foldl_cons, List.foldl_nil, fromBits_concat]
      have hgop : g.op = GateOp.not := (isNot_eq_true_iff g.op).mp hnot
      rw [evalGates_concat]
      have hlen : (evalGates gs inp).length = inp.length + gs.length := evalGates_length gs inp
      rw [← hlen, list_getD_concat_last, evalStep_not (evalGates gs inp) g hgop]
      cases actualDrv (evalGates gs inp) g <;> rfl

def scanStep (d b v : Nat) (st : List Gate × List Nat × List Nat) (g : Gate) :
    List Gate × List Nat × List Nat :=
  let sim := st.1
  let cmap := st.2.1
  let drvs := st.2.2
  if isNot g.op then
    let r := drvs.length
    let drv := match g.inputs with | [] => d | i :: _ => cmap.getD i 0
    let outW := if v.testBit (b - 1 - r) then d else d + 1
    (sim, cmap ++ [outW], drvs ++ [drv])
  else
    let newGate : Gate := ⟨g.op, g.inputs.map (fun i => cmap.getD i 0)⟩
    (sim ++ [newGate], cmap ++ [d + 2 + sim.length], drvs)

def scanRun (d b v : Nat) (gs : List Gate) : List Gate × List Nat × List Nat :=
  gs.foldl (scanStep d b v) ([], List.range (d + 2), [])

lemma scanRun_concat (d b v : Nat) (gs : List Gate) (g : Gate) :
    scanRun d b v (gs ++ [g]) = scanStep d b v (scanRun d b v gs) g := by
  simp [scanRun, List.foldl_append]

lemma scanRun_struct (d b v : Nat) (gs : List Gate)
    (hfan : FanInTwoList gs) (hrb : ReadsBackList (d + 2) gs) :
    let st := scanRun d b v gs
    st.1.length + notCountList gs = gs.length ∧
    st.2.1.length = d + 2 + gs.length ∧
    st.2.2.length = notCountList gs ∧
    Monotone2List st.1 ∧
    ReadsBackList (d + 2) st.1 ∧
    (∀ w ∈ st.2.1, w < d + 2 + st.1.length) ∧
    (∀ w ∈ st.2.2, w < d + 2 + st.1.length) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨rfl, ?_, rfl, ?_, ?_, ?_, ?_⟩
    · simp [scanRun]
    · intro g hg; cases hg
    · intro j hj; simp [scanRun] at hj
    · intro w hw
      simp only [scanRun, List.foldl_nil, List.mem_range] at hw
      omega
    · intro w hw; cases hw
  | append_singleton gs g ih =>
    have hfan_pre : FanInTwoList gs := fun x hx => hfan x (List.mem_append_left _ hx)
    have hfan_g := hfan g (by simp)
    have hrb_pre : ReadsBackList (d + 2) gs := readsBackList_prefix hrb
    have hrb_g : ∀ i ∈ g.inputs, i < d + 2 + gs.length := readsBackList_last hrb
    rcases ih hfan_pre hrb_pre with
      ⟨hlen_sum, hcmap_len, hdrvs_len, hmono, hrb_sim, hcmap_lt, hdrvs_lt⟩
    rw [scanRun_concat]
    simp only [scanStep]
    have hget_lt : ∀ i < d + 2 + gs.length,
        (scanRun d b v gs).2.1.getD i 0 < d + 2 + (scanRun d b v gs).1.length := by
      intro i hi
      have hi' : i < (scanRun d b v gs).2.1.length := by omega
      have hmem : (scanRun d b v gs).2.1.getD i 0 ∈ (scanRun d b v gs).2.1 := by
        simp [List.getD, hi']
      exact hcmap_lt _ hmem
    cases hnot : isNot g.op
    · simp only [Bool.false_eq_true, ↓reduceIte, notCountList_concat, hnot,
        List.length_append, List.length_singleton]
      have hgop_mono : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := by
        rcases hfan_g.1 with h1 | h2 | h3
        · left; exact h1
        · right; exact h2
        · exfalso
          have : isNot g.op = true := (isNot_eq_true_iff g.op).mpr h3
          rw [hnot] at this
          cases this
      refine ⟨by omega, by omega, hdrvs_len, ?_, ?_, ?_, ?_⟩
      · apply monotone2List_append hmono
        intro x hx
        simp only [List.mem_singleton] at hx
        subst hx
        exact ⟨hgop_mono, by simpa using hfan_g.2⟩
      · apply readsBackList_append hrb_sim
        intro j hj i hi
        simp only [List.length_singleton] at hj
        have hj0 : j = 0 := by omega
        subst hj0
        simp only [List.getD_cons_zero, List.mem_map] at hi
        rcases hi with ⟨k, hk, rfl⟩
        have hklt := hrb_g k hk
        have := hget_lt k hklt
        omega
      · intro w hw
        rcases List.mem_append.mp hw with hw₁ | hw₂
        · have := hcmap_lt w hw₁; omega
        · simp only [List.mem_singleton] at hw₂; omega
      · intro w hw
        have := hdrvs_lt w hw; omega
    · simp only [↓reduceIte, notCountList_concat, hnot, List.length_append, List.length_singleton]
      refine ⟨by omega, by omega, by omega, hmono, hrb_sim, ?_, ?_⟩
      · intro w hw
        rcases List.mem_append.mp hw with hw₁ | hw₂
        · exact hcmap_lt w hw₁
        · simp only [List.mem_singleton] at hw₂
          subst hw₂
          split <;> omega
      · intro w hw
        rcases List.mem_append.mp hw with hw₁ | hw₂
        · exact hdrvs_lt w hw₁
        · simp only [List.mem_singleton] at hw₂
          subst hw₂
          cases hgin : g.inputs with
          | nil => simp; omega
          | cons i rest =>
            simp only
            have hi : i < d + 2 + gs.length := hrb_g i (by simp [hgin])
            exact hget_lt i hi

lemma scanRun_sem (d b v : Nat) (gs : List Gate) (inp : List Bool)
    (hinp_len : inp.length = d + 2)
    (hinp_f : inp.getD d false = false)
    (hinp_t : inp.getD (d + 1) false = true)
    (hfan : FanInTwoList gs)
    (hrb : ReadsBackList (d + 2) gs)
    (hb : notCountList gs ≤ b) :
    let st := scanRun d b v gs
    let wA := evalGates gs inp
    let wD := evalGates st.1 inp
    let u := (actualRun gs inp).2
    ((∀ t < notCountList gs, u.getD t false = (refBits b v).getD t false) →
      ∀ j < d + 2 + gs.length, wD.getD (st.2.1.getD j 0) false = wA.getD j false) ∧
    (∀ r < notCountList gs,
      (∀ t < r, u.getD t false = (refBits b v).getD t false) →
      wD.getD (st.2.2.getD r 0) false = u.getD r false) := by
  induction gs using List.reverseRecOn with
  | nil =>
    constructor
    · intro _ j hj
      simp only [scanRun, evalGates_nil, List.foldl_nil, List.length_nil, Nat.add_zero] at hj ⊢
      have hget : (List.range (d + 2)).getD j 0 = j := by
        simp [List.getD, hj]
      rw [hget]
    · intro r hr
      simp [notCountList_nil] at hr
  | append_singleton gs g ih =>
    have hfan_pre : FanInTwoList gs := fun x hx => hfan x (List.mem_append_left _ hx)
    have hrb_pre : ReadsBackList (d + 2) gs := readsBackList_prefix hrb
    have hrb_g : ∀ i ∈ g.inputs, i < d + 2 + gs.length := readsBackList_last hrb
    have hb_pre : notCountList gs ≤ b := by
      rw [notCountList_concat] at hb
      omega
    rcases scanRun_struct d b v gs hfan_pre hrb_pre with
      ⟨hlen_sum, hcmap_len, hdrvs_len, hmono, hrb_sim, hcmap_lt, hdrvs_lt⟩
    rcases ih hfan_pre hrb_pre hb_pre with ⟨ih_eq, ih_drv⟩
    set st := scanRun d b v gs
    set wA := evalGates gs inp
    set wD := evalGates st.1 inp
    set u := (actualRun gs inp).2
    have hget_cmap_lt : ∀ i < d + 2 + gs.length, st.2.1.getD i 0 < d + 2 + st.1.length := by
      intro i hi
      have hi' : i < st.2.1.length := by omega
      have hmem : st.2.1.getD i 0 ∈ st.2.1 := by simp [List.getD, hi']
      exact hcmap_lt _ hmem
    have hget_drv_lt : ∀ r < notCountList gs, st.2.2.getD r 0 < d + 2 + st.1.length := by
      intro r hr
      have hr' : r < st.2.2.length := by omega
      have hmem : st.2.2.getD r 0 ∈ st.2.2 := by simp [List.getD, hr']
      exact hdrvs_lt _ hmem
    rw [scanRun_concat]
    simp only [scanStep]
    cases hnot : isNot g.op
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hnc : notCountList (gs ++ [g]) = notCountList gs := by
        rw [notCountList_concat, hnot]; simp
      have hu' : (actualRun (gs ++ [g]) inp).2 = u := by
        rw [actualRun_concat]; simp [hnot, u]
      set newG : Gate := ⟨g.op, g.inputs.map (fun i => st.2.1.getD i 0)⟩
      constructor
      · intro hmatch j hj
        rw [hnc, hu'] at hmatch
        have hj' : j < d + 2 + gs.length + 1 := by
          simp only [List.length_append, List.length_singleton] at hj
          omega
        by_cases hlt : j < d + 2 + gs.length
        · have hjc : j < st.2.1.length := by omega
          rw [list_getD_append_left st.2.1 [d + 2 + st.1.length] j 0 hjc]
          have hwD_eq : (evalGates (st.1 ++ [newG]) inp).getD (st.2.1.getD j 0) false =
              wD.getD (st.2.1.getD j 0) false := by
            apply evalGates_append_getD_lt
            rw [hinp_len]
            exact hget_cmap_lt j hlt
          have hwA_eq : (evalGates (gs ++ [g]) inp).getD j false = wA.getD j false := by
            apply evalGates_append_getD_lt
            rw [hinp_len]
            exact hlt
          rw [hwD_eq, hwA_eq]
          exact ih_eq hmatch j hlt
        · have hjeq : j = d + 2 + gs.length := by omega
          subst hjeq
          have hget_last : (st.2.1 ++ [d + 2 + st.1.length]).getD (d + 2 + gs.length) 0 =
              d + 2 + st.1.length := by
            rw [← hcmap_len]
            exact list_getD_concat_last st.2.1 (d + 2 + st.1.length) 0
          rw [hget_last, evalGates_concat, evalGates_concat]
          have hlenD : wD.length = d + 2 + st.1.length := by
            rw [evalGates_length, hinp_len]
          have hlenA : wA.length = d + 2 + gs.length := by
            rw [evalGates_length, hinp_len]
          rw [← hlenD, list_getD_concat_last, ← hlenA, list_getD_concat_last]
          unfold evalStep
          simp only [newG, List.map_map]
          congr 1
          apply List.map_congr_left
          intro i hi
          exact ih_eq hmatch i (hrb_g i hi)
      · intro r hr hpre
        rw [hnc] at hr
        rw [hu'] at hpre ⊢
        have hwD_eq : (evalGates (st.1 ++ [newG]) inp).getD (st.2.2.getD r 0) false =
            wD.getD (st.2.2.getD r 0) false := by
          apply evalGates_append_getD_lt
          rw [hinp_len]
          exact hget_drv_lt r hr
        rw [hwD_eq]
        exact ih_drv r hr hpre
    · simp only [↓reduceIte]
      have hnc : notCountList (gs ++ [g]) = notCountList gs + 1 := by
        rw [notCountList_concat, hnot]; simp
      have hu' : (actualRun (gs ++ [g]) inp).2 = u ++ [actualDrv wA g] := by
        rw [actualRun_concat]; simp [hnot, u, wA]
      have hulen : u.length = notCountList gs := actualRun_snd_length gs inp
      set m := notCountList gs
      have hmb : m < b := by omega
      have hgop : g.op = GateOp.not := (isNot_eq_true_iff g.op).mp hnot
      constructor
      · intro hmatch j hj
        rw [hnc] at hmatch
        rw [hu'] at hmatch
        have hmatch_pre : ∀ t < m, u.getD t false = (refBits b v).getD t false := by
          intro t ht
          have hm := hmatch t (by omega)
          rwa [list_getD_append_left u [actualDrv wA g] t false (by omega)] at hm
        have hmatch_last : actualDrv wA g = v.testBit (b - 1 - m) := by
          have hm := hmatch m (by omega)
          have hL : (u ++ [actualDrv wA g]).getD m false = actualDrv wA g := by
            rw [← hulen, list_getD_concat_last]
          rw [hL, refBits_getD b v m hmb] at hm
          exact hm
        have hj' : j < d + 2 + gs.length + 1 := by
          simp only [List.length_append, List.length_singleton] at hj
          omega
        by_cases hlt : j < d + 2 + gs.length
        · have hjc : j < st.2.1.length := by omega
          rw [list_getD_append_left st.2.1 _ j 0 hjc]
          have hwA_eq : (evalGates (gs ++ [g]) inp).getD j false = wA.getD j false := by
            apply evalGates_append_getD_lt
            rw [hinp_len]
            exact hlt
          rw [hwA_eq]
          exact ih_eq hmatch_pre j hlt
        · have hjeq : j = d + 2 + gs.length := by omega
          subst hjeq
          have hget_last :
              (st.2.1 ++ [if v.testBit (b - 1 - st.2.2.length) then d else d + 1]).getD
                (d + 2 + gs.length) 0 =
              if v.testBit (b - 1 - m) then d else d + 1 := by
            rw [← hcmap_len, list_getD_concat_last, hdrvs_len]
          rw [hget_last, evalGates_concat]
          have hlenA : wA.length = d + 2 + gs.length := by
            rw [evalGates_length, hinp_len]
          rw [← hlenA, list_getD_concat_last, evalStep_not wA g hgop, hmatch_last]
          cases v.testBit (b - 1 - m)
          · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
            rw [evalGates_getD_lt st.1 inp (d + 1) (by omega), hinp_t]
          · simp only [↓reduceIte, Bool.not_true]
            rw [evalGates_getD_lt st.1 inp d (by omega), hinp_f]
      · intro r hr hpre
        rw [hnc] at hr
        rw [hu'] at hpre ⊢
        by_cases hlt : r < m
        · have hr' : r < st.2.2.length := by omega
          rw [list_getD_append_left st.2.2 _ r 0 hr']
          rw [list_getD_append_left u [actualDrv wA g] r false (by omega)]
          apply ih_drv r hlt
          intro t ht
          have hp := hpre t ht
          rwa [list_getD_append_left u [actualDrv wA g] t false (by omega)] at hp
        · have hreq : r = m := by omega
          subst hreq
          have hL : (st.2.2 ++ [match g.inputs with | [] => d | i :: _ => st.2.1.getD i 0]).getD m 0 =
              match g.inputs with | [] => d | i :: _ => st.2.1.getD i 0 := by
            rw [← hdrvs_len, list_getD_concat_last]
          have hR : (u ++ [actualDrv wA g]).getD m false = actualDrv wA g := by
            rw [← hulen, list_getD_concat_last]
          rw [hL, hR]
          have hmatch_pre : ∀ t < m, u.getD t false = (refBits b v).getD t false := by
            intro t ht
            have hp := hpre t ht
            rwa [list_getD_append_left u [actualDrv wA g] t false (by omega)] at hp
          cases hgin : g.inputs with
          | nil =>
            simp only [actualDrv, hgin]
            rw [evalGates_getD_lt st.1 inp d (by omega), hinp_f]
          | cons i rest =>
            simp only [actualDrv, hgin]
            exact ih_eq hmatch_pre i (hrb_g i (by simp [hgin]))

def foldGates (base seed : Nat) : List (Bool × Nat) → List Gate × Nat
  | [] => ([], seed)
  | (rb, dw) :: rest =>
    let res := foldGates base seed rest
    let op := if rb then GateOp.and else GateOp.or
    (res.1 ++ [⟨op, [dw, res.2]⟩], base + res.1.length)

lemma foldGates_struct (base seed : Nat) (ps : List (Bool × Nat))
    (hseed : seed < base) (hp : ∀ p ∈ ps, p.2 < base) :
    let res := foldGates base seed ps
    res.1.length = ps.length ∧
    res.2 < base + ps.length ∧
    Monotone2List res.1 ∧
    ReadsBackList base res.1 := by
  induction ps with
  | nil =>
    refine ⟨rfl, by simpa [foldGates], ?_, ?_⟩
    · intro g hg; cases hg
    · intro j hj; simp [foldGates] at hj
  | cons p rest ih =>
    rcases p with ⟨rb, dw⟩
    have hdw : dw < base := hp (rb, dw) (by simp)
    have hrest : ∀ q ∈ rest, q.2 < base := fun q hq => hp q (by simp [hq])
    rcases ih hrest with ⟨hlen, hout, hmono, hrb⟩
    simp only [foldGates, List.length_append, List.length_cons, List.length_nil]
    refine ⟨by omega, by omega, ?_, ?_⟩
    · apply monotone2List_append hmono
      intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      refine ⟨?_, by simp⟩
      cases rb <;> simp
    · apply readsBackList_append hrb
      intro j hj i hi
      simp only [List.length_singleton] at hj
      have hj0 : j = 0 := by omega
      subst hj0
      simp only [List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · omega
      · omega

lemma foldGates_eval (base seed : Nat) (ps : List (Bool × Nat)) (w0 : List Bool)
    (hw0 : w0.length = base) (hp : ∀ p ∈ ps, p.2 < base) :
    let res := foldGates base seed ps
    (evalGates res.1 w0).getD res.2 false =
      foldBool (w0.getD seed false) (ps.map fun p => (p.1, w0.getD p.2 false)) := by
  induction ps with
  | nil =>
    simp [foldGates, evalGates_nil, foldBool]
  | cons p rest ih =>
    rcases p with ⟨rb, dw⟩
    have hdw : dw < base := hp (rb, dw) (by simp)
    have hrest : ∀ q ∈ rest, q.2 < base := fun q hq => hp q (by simp [hq])
    have ih' := ih hrest
    simp only [foldGates, List.map_cons, foldBool]
    set res := foldGates base seed rest
    rw [evalGates_concat]
    have hlen : (evalGates res.1 w0).length = base + res.1.length := by
      rw [evalGates_length, hw0]
    rw [← hlen, list_getD_concat_last]
    unfold evalStep
    simp only [List.map_cons, List.map_nil]
    have hdw_val : (evalGates res.1 w0).getD dw false = w0.getD dw false :=
      evalGates_getD_lt res.1 w0 dw (by omega)
    rw [hdw_val, ih']
    cases rb <;> simp [GateOp.eval]

lemma zip_map_snd_eq {α β γ : Type*} (l₁ : List α) (l₂ : List β) (f : β → γ) :
    (l₁.zip l₂).map (fun p => (p.1, f p.2)) = l₁.zip (l₂.map f) := by
  induction l₁ generalizing l₂ with
  | nil => rfl
  | cons a t₁ ih =>
    cases l₂ with
    | nil => rfl
    | cons b t₂ =>
      simp [ih]

lemma bits_props (d : Nat) (x : Finset (Fin d)) [DecidablePred (fun a : Fin d => a ∈ x)] :
    let inp := List.ofFn (fun a : Fin d => decide (a ∈ x)) ++ [false, true]
    inp.length = d + 2 ∧ inp.getD d false = false ∧ inp.getD (d + 1) false = true := by
  refine ⟨by simp, ?_, ?_⟩
  · have hlen : (List.ofFn (fun a : Fin d => decide (a ∈ x))).length = d := by simp
    rw [list_getD_append_right _ [false, true] d false (by omega)]
    simp [hlen]
  · have hlen : (List.ofFn (fun a : Fin d => decide (a ∈ x))).length = d := by simp
    rw [list_getD_append_right _ [false, true] (d + 1) false (by omega)]
    simp [hlen]

end PEqualNP.Outside.L_lib_1337

theorem PEqualNP.Outside.L_lib_1337 : letI : ∀ P : Prop, Decidable P := Classical.propDecidable
let valid := fun (d : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (d+2) C ∧
  C.output < d+2+C.size
let bits := fun (d : Nat) (x : Finset (Fin d)) =>
  List.ofFn (fun a : Fin d => decide (a ∈ x)) ++ [false,true]
let rank := fun (d : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) (x : Finset (Fin d)) =>
  let w := C.wires (bits d x)
  let gates := (List.range C.size).filter (fun j => decide
    ((C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op = .not))
  gates.foldl (fun v j => 2*v+(if w.getD (d+2+j) false then 0 else 1)) 0
∀ (d : Nat) (A : PEqualNP.CircuitLowerBounds.Circuit) (v : Nat),
  valid d A → v < 2^(PEqualNP.NotBracket.notCount A) →
  ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (ge gt : Nat) (copy : Nat → Nat),
    valid d D ∧ PEqualNP.MetaComplexity.Monotone2 D ∧
    D.size ≤ A.size + PEqualNP.NotBracket.notCount A ∧
    ge < d+2+D.size ∧ ge < d+2+A.size ∧ gt < d+2+D.size ∧
    (∀ j, j < d+2+A.size → copy j < d+2+D.size) ∧
    ∀ x : Finset (Fin d),
      let w := D.wires (bits d x)
      w.getD ge false = decide (v ≤ rank d A x) ∧ w.getD gt false = decide (v < rank d A x) ∧
      (rank d A x = v → ∀ j, j < d+2+A.size →
        w.getD (copy j) false = (A.wires (bits d x)).getD j false) := by
  intro valid bits rank d A v hvalid hv
  rcases hvalid with ⟨hfanA, hrbA, _⟩
  let b := PEqualNP.NotBracket.notCount A
  have hb_eq : b = PEqualNP.Outside.L_lib_1337.notCountList A.gates :=
    PEqualNP.Outside.L_lib_1337.notCount_eq A
  have hstruct := PEqualNP.Outside.L_lib_1337.scanRun_struct d b v A.gates hfanA hrbA
  rcases hst : PEqualNP.Outside.L_lib_1337.scanRun d b v A.gates with ⟨sim, cmap, drvs⟩
  dsimp only at hstruct
  rw [hst] at hstruct
  dsimp only at hstruct
  rcases hstruct with ⟨hlen_sum, hcmap_len, hdrvs_len, hmono_sim, hrb_sim, hcmap_lt, hdrvs_lt⟩
  let pairs := (PEqualNP.Outside.L_lib_1337.refBits b v).zip drvs
  have hpairs_len : pairs.length = b := by
    simp [pairs, PEqualNP.Outside.L_lib_1337.refBits_length, hdrvs_len, hb_eq]
  have hpairs_lt : ∀ p ∈ pairs, p.2 < d + 2 + sim.length := by
    intro p hp
    exact hdrvs_lt p.2 (List.of_mem_zip hp).2
  have hge_struct :=
    PEqualNP.Outside.L_lib_1337.foldGates_struct (d + 2 + sim.length) (d + 1) pairs (by omega) hpairs_lt
  rcases hge : PEqualNP.Outside.L_lib_1337.foldGates (d + 2 + sim.length) (d + 1) pairs with ⟨geGates, ge⟩
  dsimp only at hge_struct
  rw [hge] at hge_struct
  dsimp only at hge_struct
  rcases hge_struct with ⟨hge_len, hge_out, hge_mono, hge_rb⟩
  have hpairs_lt_gt : ∀ p ∈ pairs, p.2 < d + 2 + (sim ++ geGates).length := by
    intro p hp
    have := hpairs_lt p hp
    simp only [List.length_append]
    omega
  have hgt_struct :=
    PEqualNP.Outside.L_lib_1337.foldGates_struct (d + 2 + (sim ++ geGates).length) d pairs (by omega) hpairs_lt_gt
  rcases hgt : PEqualNP.Outside.L_lib_1337.foldGates (d + 2 + (sim ++ geGates).length) d pairs with ⟨gtGates, gt⟩
  dsimp only at hgt_struct
  rw [hgt] at hgt_struct
  dsimp only at hgt_struct
  rcases hgt_struct with ⟨hgt_len, hgt_out, hgt_mono, hgt_rb⟩
  let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨sim ++ geGates ++ gtGates, 0⟩
  have hA_size : A.size = A.gates.length := rfl
  have hD_size : D.size = A.size + b := by
    change (sim ++ geGates ++ gtGates).length = A.gates.length + b
    simp only [List.length_append]
    omega
  have hD_mono : PEqualNP.MetaComplexity.Monotone2 D := by
    apply PEqualNP.Outside.L_lib_1337.monotone2List_append
    · exact PEqualNP.Outside.L_lib_1337.monotone2List_append hmono_sim hge_mono
    · exact hgt_mono
  have hD_fan : PEqualNP.MetaComplexity.FanInTwo D :=
    PEqualNP.Outside.L_lib_1337.monotone2List_to_fanInTwoList hD_mono
  have hD_rb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + 2) D := by
    apply PEqualNP.Outside.L_lib_1337.readsBackList_append
    · exact PEqualNP.Outside.L_lib_1337.readsBackList_append hrb_sim hge_rb
    · exact hgt_rb
  refine ⟨D, ge, gt, (fun j => cmap.getD j 0),
    ⟨hD_fan, hD_rb, by change 0 < d + 2 + D.size; omega⟩,
    hD_mono, by omega, by omega, by omega, ?_, ?_, ?_⟩
  · simp only [List.length_append] at hgt_out
    omega
  · intro j hj
    have hj' : j < cmap.length := by omega
    have hmem : cmap.getD j 0 ∈ cmap := by simp [List.getD, hj']
    have hlt := hcmap_lt _ hmem
    change cmap.getD j 0 < d + 2 + D.size
    omega
  · intro x
    let inp := bits d x
    have hbits : inp.length = d + 2 ∧ inp.getD d false = false ∧ inp.getD (d + 1) false = true :=
      @PEqualNP.Outside.L_lib_1337.bits_props d x (fun a => Classical.propDecidable (a ∈ x))
    rcases hbits with ⟨hinp_len, hinp_f, hinp_t⟩
    have hsem := PEqualNP.Outside.L_lib_1337.scanRun_sem d b v A.gates inp
      hinp_len hinp_f hinp_t hfanA hrbA (by omega)
    dsimp only at hsem
    rw [hst] at hsem
    dsimp only at hsem
    rcases hsem with ⟨hsem_eq, hsem_drv⟩
    let wSim := PEqualNP.Outside.L_lib_1337.evalGates sim inp
    let wGe := PEqualNP.Outside.L_lib_1337.evalGates (sim ++ geGates) inp
    let wD := PEqualNP.Outside.L_lib_1337.evalGates D.gates inp
    let u := (PEqualNP.Outside.L_lib_1337.actualRun A.gates inp).2
    have hu_len : u.length = b := by
      change (PEqualNP.Outside.L_lib_1337.actualRun A.gates inp).2.length = b
      rw [PEqualNP.Outside.L_lib_1337.actualRun_snd_length, ← hb_eq]
    have hrank_eq : rank d A x = PEqualNP.Outside.L_lib_1337.fromBits u := by
      dsimp only [rank]
      have hfilt :
          (List.range A.size).filter (fun j => @decide
            ((A.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op = .not)
            (Classical.propDecidable _)) =
          (List.range A.gates.length).filter (fun j =>
            PEqualNP.Outside.L_lib_1337.isNot
              (A.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op) := by
        apply List.filter_congr
        intro j _
        exact PEqualNP.Outside.L_lib_1337.decide_eq_not _ _
      rw [hfilt]
      have hr := PEqualNP.Outside.L_lib_1337.rankList_eq_fromBits A.gates inp
      rw [hinp_len] at hr
      simpa [PEqualNP.Outside.L_lib_1337.rankList, inp,
        PEqualNP.CircuitLowerBounds.Circuit.wires,
        PEqualNP.Outside.L_lib_1337.evalGates,
        PEqualNP.Outside.L_lib_1337.evalStep, u] using hr
    have hv_eq : PEqualNP.Outside.L_lib_1337.fromBits (PEqualNP.Outside.L_lib_1337.refBits b v) = v :=
      PEqualNP.Outside.L_lib_1337.fromBits_refBits b v hv
    let simB := drvs.map (fun wire => wSim.getD wire false)
    have hsimB_len : simB.length = u.length := by
      simp [simB, hdrvs_len, hu_len, hb_eq]
    have href_len : (PEqualNP.Outside.L_lib_1337.refBits b v).length = u.length := by
      rw [PEqualNP.Outside.L_lib_1337.refBits_length, hu_len]
    have hagree : ∀ r < (PEqualNP.Outside.L_lib_1337.refBits b v).length,
        (∀ t < r, u.getD t false = (PEqualNP.Outside.L_lib_1337.refBits b v).getD t false) →
        simB.getD r false = u.getD r false := by
      intro r hr hpre
      rw [PEqualNP.Outside.L_lib_1337.refBits_length] at hr
      have hr' : r < drvs.length := by omega
      have hget_simB : simB.getD r false = wSim.getD (drvs.getD r 0) false := by
        simp [simB, List.getD, hr']
      rw [hget_simB]
      exact hsem_drv r (by omega) hpre
    have hge_val : wD.getD ge false =
        PEqualNP.Outside.L_lib_1337.foldBool true
          ((PEqualNP.Outside.L_lib_1337.refBits b v).zip simB) := by
      have h1 : wD.getD ge false = wGe.getD ge false := by
        change (PEqualNP.Outside.L_lib_1337.evalGates ((sim ++ geGates) ++ gtGates) inp).getD ge false = _
        apply PEqualNP.Outside.L_lib_1337.evalGates_append_getD_lt
        rw [hinp_len, List.length_append]
        omega
      rw [h1]
      have h2 : wGe = PEqualNP.Outside.L_lib_1337.evalGates geGates wSim :=
        PEqualNP.Outside.L_lib_1337.evalGates_append sim geGates inp
      rw [h2]
      have hwSim_len : wSim.length = d + 2 + sim.length := by
        change (PEqualNP.Outside.L_lib_1337.evalGates sim inp).length = d + 2 + sim.length
        rw [PEqualNP.Outside.L_lib_1337.evalGates_length, hinp_len]
      have hev := PEqualNP.Outside.L_lib_1337.foldGates_eval (d + 2 + sim.length) (d + 1) pairs wSim
        hwSim_len hpairs_lt
      dsimp only at hev
      rw [hge] at hev
      dsimp only at hev
      rw [hev]
      have ht_val : wSim.getD (d + 1) false = true := by
        change (PEqualNP.Outside.L_lib_1337.evalGates sim inp).getD (d + 1) false = true
        rw [PEqualNP.Outside.L_lib_1337.evalGates_getD_lt sim inp (d + 1) (by omega), hinp_t]
      rw [ht_val]
      dsimp only [pairs, simB]
      rw [PEqualNP.Outside.L_lib_1337.zip_map_snd_eq (PEqualNP.Outside.L_lib_1337.refBits b v) drvs
        (fun wire => wSim.getD wire false)]
    have hgt_val : wD.getD gt false =
        PEqualNP.Outside.L_lib_1337.foldBool false
          ((PEqualNP.Outside.L_lib_1337.refBits b v).zip simB) := by
      have h2 : wD = PEqualNP.Outside.L_lib_1337.evalGates gtGates wGe :=
        PEqualNP.Outside.L_lib_1337.evalGates_append (sim ++ geGates) gtGates inp
      rw [h2]
      have hwGe_len : wGe.length = d + 2 + (sim ++ geGates).length := by
        change (PEqualNP.Outside.L_lib_1337.evalGates (sim ++ geGates) inp).length = _
        rw [PEqualNP.Outside.L_lib_1337.evalGates_length, hinp_len]
      have hev := PEqualNP.Outside.L_lib_1337.foldGates_eval (d + 2 + (sim ++ geGates).length) d pairs wGe
        hwGe_len hpairs_lt_gt
      dsimp only at hev
      rw [hgt] at hev
      dsimp only at hev
      rw [hev]
      have hf_val : wGe.getD d false = false := by
        change (PEqualNP.Outside.L_lib_1337.evalGates (sim ++ geGates) inp).getD d false = false
        rw [PEqualNP.Outside.L_lib_1337.evalGates_getD_lt (sim ++ geGates) inp d (by omega), hinp_f]
      rw [hf_val]
      dsimp only [pairs, simB]
      rw [PEqualNP.Outside.L_lib_1337.zip_map_snd_eq (PEqualNP.Outside.L_lib_1337.refBits b v) drvs
        (fun wire => wGe.getD wire false)]
      congr 2
      apply List.map_congr_left
      intro wire hwire
      apply PEqualNP.Outside.L_lib_1337.evalGates_append_getD_lt
      rw [hinp_len]
      exact hdrvs_lt wire hwire
    refine ⟨?_, ?_, ?_⟩
    · show wD.getD ge false = @decide (v ≤ rank d A x) (Classical.propDecidable _)
      rw [hge_val, Bool.eq_iff_iff, @decide_eq_true_iff _ (Classical.propDecidable _)]
      have hge_iff := PEqualNP.Outside.L_lib_1337.foldBool_spec_ge _ u simB href_len hsimB_len hagree
      rwa [hv_eq, ← hrank_eq] at hge_iff
    · show wD.getD gt false = @decide (v < rank d A x) (Classical.propDecidable _)
      rw [hgt_val, Bool.eq_iff_iff, @decide_eq_true_iff _ (Classical.propDecidable _)]
      have hgt_iff := PEqualNP.Outside.L_lib_1337.foldBool_spec_gt _ u simB href_len hsimB_len hagree
      rwa [hv_eq, ← hrank_eq] at hgt_iff
    · intro hreq j hj
      rw [hrank_eq, ← hv_eq] at hreq
      have hu_eq_ref : u = PEqualNP.Outside.L_lib_1337.refBits b v :=
        PEqualNP.Outside.L_lib_1337.fromBits_inj href_len.symm hreq
      have hmatch : ∀ t < PEqualNP.Outside.L_lib_1337.notCountList A.gates,
          u.getD t false = (PEqualNP.Outside.L_lib_1337.refBits b v).getD t false := by
        intro t _
        rw [hu_eq_ref]
      have hcopy_lt : cmap.getD j 0 < d + 2 + sim.length := by
        have hj' : j < cmap.length := by omega
        exact hcmap_lt _ (by simp [List.getD, hj'])
      have hwD_eq : wD.getD (cmap.getD j 0) false = wSim.getD (cmap.getD j 0) false := by
        have hassoc : D.gates = sim ++ (geGates ++ gtGates) := by
          simp [D, List.append_assoc]
        change (PEqualNP.Outside.L_lib_1337.evalGates D.gates inp).getD (cmap.getD j 0) false = _
        rw [hassoc]
        apply PEqualNP.Outside.L_lib_1337.evalGates_append_getD_lt
        rw [hinp_len]
        exact hcopy_lt
      show wD.getD (cmap.getD j 0) false = (A.wires inp).getD j false
      rw [hwD_eq]
      exact hsem_eq hmatch j hj
