import Mathlib.Tactic.Tauto
import Mathlib.Data.BitVec
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20839

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

abbrev Mask := BitVec 25
def target : Mask := 32471073
def sources : List Mask := [31, 992, 31744, 1015808, 32505856, 1082401, 2164802, 4329604, 8659208, 17318416]
def allBits : Mask := BitVec.allOnes 25

def isAnd : GateOp → Bool
  | .and => true
  | _ => false

def act (isOr : Bool) (x y : Mask) : Mask :=
  if isOr then x ||| y else x &&& y

theorem act_bits (o : Bool) (a b : Mask) (i : Fin 25) :
    (act o a b)[i.val] = if o then a[i.val] || b[i.val] else a[i.val] && b[i.val] := by
  cases o <;> simp [act]

def gateMask (g : Gate) (w : List Mask) : Mask :=
  match g.inputs with
  | [] => if isAnd g.op then allBits else 0
  | [a] => w.getD a 0
  | a :: b :: _ => act (!(isAnd g.op)) (w.getD a 0) (w.getD b 0)

theorem gateMask_bits (g : Gate) (w : List Mask) (i : Fin 25)
    (op : g.op = .and ∨ g.op = .or) (arity : g.inputs.length ≤ 2) :
    (gateMask g w)[i.val] =
      g.op.eval (g.inputs.map fun a => (w.map (fun v : Mask => v[i.val])).getD a false) := by
  have bitGet (a : ℕ) : (w.getD a 0)[i.val] = (w.map (fun v : Mask => v[i.val])).getD a false := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    change (w[a]?.getD (0 : Mask)).getLsbD i.val = _
    generalize w[a]? = q
    cases q <;> simp
  rcases g with ⟨o,l⟩
  simp only at op arity
  rcases op with rfl | rfl <;>
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil, gateMask, isAnd, ite_true, ite_false,
       Bool.not_true, Bool.not_false, act, GateOp.eval, List.map_cons, List.map_nil,
       List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true,
       Bool.or_false, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_zero, bitGet] at arity ⊢
  all_goals first
    | omega
    | exact BitVec.getElem_allOnes _ i.isLt
    | simp
  have fromSome (q : Option Mask) :
      (q.getD (0#25)).getLsbD i.val = (q.map (fun v : Mask => v.getLsbD i.val)).getD false := by
    cases q <;> simp
  simp only [← BitVec.getLsbD_eq_getElem i.isLt, fromSome]

def stage (w : List Mask) (g : Gate) := w ++ [gateMask g w]

theorem wireProjection (gs : List Gate)
    (mono : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (w : List Mask) (i : Fin 25) :
    ((gs.foldl stage w).map (fun v : Mask => v[i.val])) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun a => w.getD a false)])
        (w.map (fun v : Mask => v[i.val])) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (fun h hm => mono h (List.mem_cons_of_mem _ hm))]
    simp only [stage, List.map_append, List.map_cons, List.map_nil]
    rw [gateMask_bits g w i (mono g (by simp)).1 (mono g (by simp)).2]

def row (i : Fin 25) : List Bool :=
  oneEach (⟨i.val / 5, by omega⟩ : Fin 5) (⟨i.val % 5, by omega⟩ : Fin 5)

theorem source_projection : ∀ i : Fin 25, sources.map (fun v : Mask => v[i.val]) = row i := by
  decide

theorem evalMask (C : Circuit) (mono : Monotone2 C) (i : Fin 25) :
    ((C.gates.foldl stage sources).getD C.output 0)[i.val] = C.eval (row i) := by
  rw [Circuit.eval, Circuit.wires, ← source_projection i, ← wireProjection]
  · cases h : (C.gates.foldl stage sources)[C.output]? <;>
      simp [List.getD_eq_getElem?_getD, h]
  · intro g hg
    simpa using mono g hg

theorem evalTarget (C : Circuit) (mono : Monotone2 C)
    (computes : Represents (fun (u : Fin 5) (v : Fin 5) => (32471073 : ℕ).testBit (5*u.val+v.val)) C) :
    (C.gates.foldl stage sources).getD C.output 0 = target := by
  apply BitVec.eq_of_getElem_eq
  intro i ilt
  rw [evalMask C mono ⟨i,ilt⟩]
  change C.eval (oneEach (⟨i / 5, by omega⟩ : Fin 5) (⟨i % 5, by omega⟩ : Fin 5)) = _
  rw [computes]
  have eq : 5*(i/5)+i % 5 = i := by omega
  change (32471073 : ℕ).testBit (5 * (i / 5) + i % 5) = _
  rw [eq]
  rfl

inductive Build : Finset Mask → ℕ → Prop
  | done {W} : target ∈ W → Build W 0
  | advance {W a b o k} : a ∈ W → b ∈ W → act o a b ∉ W →
      act o a b ≠ 0 → act o a b ≠ allBits →
      Build (insert (act o a b) W) k → Build W (k+1)

theorem basicGate (g : Gate) (w : List Mask)
    (op : g.op = .and ∨ g.op = .or) (arity : g.inputs.length ≤ 2) :
    gateMask g w = 0 ∨ gateMask g w = allBits ∨ gateMask g w ∈ w ∨
      ∃ a ∈ w, ∃ b ∈ w, ∃ o : Bool, gateMask g w = act o a b := by
  have getMem (j : ℕ) : w.getD j 0 = 0 ∨ w.getD j 0 ∈ w := by
    simp only [List.getD_eq_getElem?_getD]
    cases h : w[j]? with
    | none => simp
    | some v => exact Or.inr (List.mem_of_getElem? h)
  rcases g with ⟨op', l⟩
  change op' = .and ∨ op' = .or at op
  change l.length ≤ 2 at arity
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩
  · rcases op with rfl | rfl <;> simp [gateMask, isAnd]
  · rcases getMem a with z | m
    · exact Or.inl z
    · exact Or.inr (Or.inr (Or.inl m))
  · simp only [gateMask]
    rcases getMem a with ha | ha <;> rcases getMem b with hb | hb
    · rw [ha,hb]
      rcases op with rfl | rfl <;> simp [act, isAnd]
    · rw [ha]
      rcases op with rfl | rfl
      · simp [act, isAnd]
      · exact Or.inr (Or.inr (Or.inl (by
        change ((0 : Mask) ||| w.getD b 0) ∈ w
        rw [show (0 : Mask) ||| w.getD b 0 = w.getD b 0 from BitVec.zero_or]
        exact hb)))
    · rw [hb]
      rcases op with rfl | rfl
      · simp [act, isAnd]
      · exact Or.inr (Or.inr (Or.inl (by
        change (w.getD a 0 ||| (0 : Mask)) ∈ w
        rw [show w.getD a 0 ||| (0 : Mask) = w.getD a 0 from BitVec.or_zero]
        exact ha)))
    · exact Or.inr (Or.inr (Or.inr ⟨_,ha,_,hb,_,rfl⟩))
  · simp at arity

theorem buildFrom (gs : List Gate)
    (mono : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (w : List Mask) (W : Finset Mask)
    (inv : ∀ v ∈ w, v = 0 ∨ v = allBits ∨ v ∈ W)
    (endMem : target ∈ gs.foldl stage w) :
    ∃ k ≤ gs.length, Build W k := by
  induction gs generalizing w W with
  | nil =>
    have h : target ∈ w := endMem
    rcases inv target h with z | t | mem
    · contradiction
    · contradiction
    · exact ⟨0, by simp, .done mem⟩
  | cons g gs ih =>
    have mono' : ∀ h ∈ gs, (h.op = .and ∨ h.op = .or) ∧ h.inputs.length ≤ 2 :=
      fun h hh => mono h (List.mem_cons_of_mem _ hh)
    by_cases already : gateMask g w = 0 ∨ gateMask g w = allBits ∨ gateMask g w ∈ W
    · have extend : ∀ v ∈ stage w g, v = 0 ∨ v = allBits ∨ v ∈ W := by
        intro v hv
        simp only [stage, List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | rfl
        · exact inv _ hv
        · exact already
      obtain ⟨k,hk,b⟩ := ih mono' _ W extend endMem
      exact ⟨k, by simp; omega, b⟩
    · obtain ⟨a,ha,b,hb,o,eq⟩ : ∃ a ∈ w, ∃ b ∈ w, ∃ o : Bool,
          gateMask g w = act o a b := by
        have gate := mono g (by simp)
        rcases basicGate g w gate.1 gate.2 with z | t | mem | ex
        · exact (already (Or.inl z)).elim
        · exact (already (Or.inr (Or.inl t))).elim
        · exact (already (inv _ mem)).elim
        · exact ex
      have hz : act o a b ≠ 0 := fun h => already (Or.inl (eq.trans h))
      have ht : act o a b ≠ allBits := fun h => already (Or.inr (Or.inl (eq.trans h)))
      have hm : act o a b ∉ W := fun h => already (Or.inr (Or.inr (eq ▸ h)))
      have aw : a ∈ W := by
        rcases inv a ha with h | h | h
        · subst a
          cases o
          · exact (hz (by simp [act])).elim
          · have e : gateMask g w = b := eq.trans (by simp [act])
            exact (already (e ▸ inv _ hb)).elim
        · subst a
          cases o
          · have e : gateMask g w = b := eq.trans (by exact BitVec.allOnes_and)
            exact (already (e ▸ inv _ hb)).elim
          · exact (ht (by exact BitVec.allOnes_or)).elim
        · exact h
      have bw : b ∈ W := by
        rcases inv b hb with h | h | h
        · subst b
          cases o
          · exact (hz (by simp [act])).elim
          · have e : gateMask g w = a := eq.trans (by simp [act])
            exact (already (e ▸ inv _ ha)).elim
        · subst b
          cases o
          · have e : gateMask g w = a := eq.trans (by exact BitVec.and_allOnes)
            exact (already (e ▸ inv _ ha)).elim
          · exact (ht (by exact BitVec.or_allOnes)).elim
        · exact h
      have extend : ∀ v ∈ stage w g, v = 0 ∨ v = allBits ∨ v ∈ insert (act o a b) W := by
        intro v hv
        simp only [stage, List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | rfl
        · exact (inv _ hv).imp_right (Or.imp_right (fun h => Finset.mem_insert_of_mem h))
        · simp [eq]
      obtain ⟨k,hk,d⟩ := ih mono' _ _ extend endMem
      exact ⟨k+1, by simpa using hk, .advance aw bw hm hz ht d⟩

theorem representsBuild (C : Circuit) (mono : Monotone2 C)
    (computes : Represents (fun (u : Fin 5) (v : Fin 5) => (32471073 : ℕ).testBit (5*u.val+v.val)) C) :
    ∃ k ≤ C.size, Build sources.toFinset k := by
  have targetOutput := evalTarget C mono computes
  have targetMem : target ∈ C.gates.foldl stage sources := by
    simp only [List.getD_eq_getElem?_getD] at targetOutput
    cases h : (C.gates.foldl stage sources)[C.output]? with
    | none => simp [h, target] at targetOutput
    | some x =>
      simp only [h, Option.getD_some] at targetOutput
      exact targetOutput ▸ List.mem_of_getElem? h
  exact buildFrom C.gates (by intro g hg; simpa using mono g hg) _ _
    (by intro v hv; exact Or.inr (Or.inr (List.mem_toFinset.mpr hv))) targetMem

inductive Reach : Finset Mask → ℕ → Prop
  | done : Reach {target} 0
  | advance {W R a b o k} : a ∈ W → b ∈ W → act o a b ∉ W →
      act o a b ≠ 0 → act o a b ≠ allBits →
      R ⊆ W → W ⊆ insert a (insert b R) →
      Reach (insert (act o a b) R) k → Reach W (k+1)

theorem buildReach {W : Finset Mask} {k : ℕ} (b : Build W k) :
    ∃ U ⊆ W, ∃ j ≤ k, Reach U j := by
  induction b with
  | done h => exact ⟨{target}, by simpa, 0, le_rfl, .done⟩
  | @advance W a b o k aw bw fresh nz nt _ ih =>
    obtain ⟨D, sub, j, jle, reach⟩ := ih
    let v := act o a b
    by_cases hv : v ∈ D
    · let R := D.erase v
      let U := insert a (insert b R)
      have rsub : R ⊆ W := by
        intro x hx
        have xx := Finset.mem_erase.mp hx
        exact (Finset.mem_insert.mp (sub xx.2)).resolve_left xx.1
      have usub : U ⊆ W := Finset.insert_subset_iff.mpr ⟨aw,
        Finset.insert_subset_iff.mpr ⟨bw,rsub⟩⟩
      have dEq : insert v R = D := Finset.insert_erase hv
      refine ⟨U,usub,j+1,Nat.succ_le_succ jle,.advance (R := R) (a := a) (b := b) (o := o) (by simp [U]) (by simp [U])
        (fun h => fresh (usub h)) nz nt (fun x hx => by simp [U,hx]) (by rfl) ?_⟩
      exact dEq ▸ reach
    · refine ⟨D, ?_, j, by omega, reach⟩
      intro x hx
      exact (Finset.mem_insert.mp (sub hx)).resolve_left (fun e => hv (e ▸ hx : act o a b ∈ D))

theorem reachCard {W : Finset Mask} {k : ℕ} (h : Reach W k) : W.card ≤ k+1 := by
  induction h with
  | done => simp
  | @advance W R a b o k _ _ fresh _ _ sub small _ ih =>
    rw [Finset.card_insert_of_notMem (fun h => fresh (sub h))] at ih
    have ub := (Finset.card_le_card small).trans
      ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ (Finset.card_insert_le _ _)))
    omega

def Separates (W : Finset Mask) : Prop :=
  ∀ p n : Fin 25, target[p.val] = true → target[n.val] = false →
    ∃ w ∈ W, w[p.val] = true ∧ w[n.val] = false

theorem splitSeparation {o : Bool} {a b : Mask} {p n : Fin 25}
    (yes : (act o a b)[p.val] = true) (no : (act o a b)[n.val] = false) :
    (a[p.val] = true ∧ a[n.val] = false) ∨ (b[p.val] = true ∧ b[n.val] = false) := by
  rw [act_bits] at yes no
  cases o <;> simp_all only [ite_true, ite_false, Bool.false_eq_true,
    Bool.and_eq_true, Bool.and_eq_false_iff, Bool.or_eq_true, Bool.or_eq_false_iff] <;> tauto

theorem reachSeparates {W : Finset Mask} {k : ℕ} (h : Reach W k) : Separates W := by
  intro p n hp hn
  induction h with
  | done => exact ⟨target, by simp, hp, hn⟩
  | @advance W R a b o k am bm _ _ _ sub _ _ ih =>
    obtain ⟨w, hw, yes, no⟩ := ih
    rcases Finset.mem_insert.mp hw with rfl | old
    · rcases splitSeparation yes no with h | h
      · exact ⟨a,am,h⟩
      · exact ⟨b,bm,h⟩
    · exact ⟨w,sub old,yes,no⟩

def criticalPairs : List (Fin 25 × Fin 25) :=
  [(0,10), (5,10), (11,1), (16,1), (21,1), (0,1), (11,10), (12,10), (13,10), (14,10)]

theorem essentialData : ∀ i : Fin 10,
    let (p,n) := criticalPairs[i.val]'(by exact i.isLt)
    target[p.val] = true ∧ target[n.val] = false ∧
    ∀ j : Fin 10, (sources[j.val]'(by exact j.isLt))[p.val] = true →
      (sources[j.val]'(by exact j.isLt))[n.val] = false → j = i := by
  decide +kernel

theorem allSources (W : Finset Mask) (hW : W ⊆ sources.toFinset)
    (sep : Separates W) : W = sources.toFinset := by
  apply Finset.Subset.antisymm hW
  intro w hw
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp hw)
  let j : Fin 10 := ⟨i, by simpa [sources] using hi⟩
  have key := essentialData j
  obtain ⟨v, hv, yes, no⟩ := sep _ _ key.1 key.2.1
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp (hW hv))
  let q : Fin 10 := ⟨t, by simpa [sources] using ht⟩
  have equal := key.2.2 q yes no
  have hv' : sources[q.val]'q.isLt ∈ W := hv
  change sources[j.val]'j.isLt ∈ W
  exact (congrArg (fun i : Fin 10 => sources[i.val]'i.isLt) equal) ▸ hv'

theorem lower (C : Circuit) (mono : Monotone2 C)
    (computes : Represents (fun (u : Fin 5) (v : Fin 5) => (32471073 : ℕ).testBit (5*u.val+v.val)) C) :
    9 ≤ C.size := by
  obtain ⟨k,hk,hb⟩ := representsBuild C mono computes
  obtain ⟨U,hu,j,hj,hr⟩ := buildReach hb
  have eq := allSources U hu (reachSeparates hr)
  have hc := reachCard hr
  rw [eq] at hc
  have : sources.toFinset.card = 10 := by decide
  omega

def witness : Circuit :=
  ⟨[⟨.or,[0,1]⟩, ⟨.and,[10,5]⟩, ⟨.or,[2,3]⟩, ⟨.or,[12,4]⟩,
    ⟨.or,[6,7]⟩, ⟨.or,[14,8]⟩, ⟨.or,[15,9]⟩, ⟨.and,[13,16]⟩,
    ⟨.or,[11,17]⟩],18⟩

theorem upper : RepSizeAtMost
    (fun (u : Fin 5) (v : Fin 5) => (32471073 : ℕ).testBit (5*u.val+v.val)) 9 := by
  refine ⟨witness, ?_, ?_, ?_⟩
  · intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [List.length_cons, List.length_nil]
  · decide
  · decide +kernel

end PEqualNP.Outside.L_meta_20839

theorem PEqualNP.Outside.L_meta_20839 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (32471073 : ℕ).testBit (5 * u.val + v.val)) 9 ∧ ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (32471073 : ℕ).testBit (5 * u.val + v.val)) 8) := by
  refine ⟨PEqualNP.Outside.L_meta_20839.upper, ?_⟩
  rintro ⟨C, hm, hs, hr⟩
  have := PEqualNP.Outside.L_meta_20839.lower C hm hr
  omega
