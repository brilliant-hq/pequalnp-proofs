import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_45356_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev X := Fin 6 → Bool
abbrev F := X → Bool

def Cst (f : F) : Prop := ∃ b, f = fun _ => b

def Av (s : Set F) (f : F) : Prop := Cst f ∨ ∃ u ∈ s, f = u ∨ f = fun x => !u x

def comb (t : Bool) (a b : F) : F := fun x => if t then a x && b x else a x || b x

def rs (i : Fin 6) (c : Bool) (f : F) : F := fun x => f (Function.update x i c)

def Ind (i : Fin 6) (f : F) : Prop := ∀ x b, f (Function.update x i b) = f x

def Smp (i : Fin 6) (c : Bool) (f : F) : Prop := Ind i f ∨ Cst (rs i c f)

def LI (i : Fin 6) (f : F) : Prop := Ind i f ∨ ∃ e, f = fun x => xor (x i) e

inductive Prog : Set F → F → ℕ → Prop where
  | done {s f} (h : Av s f) : Prog s f 0
  | gate {s f a b k} (t : Bool) (ha : Av s a) (hb : Av s b)
      (tail : Prog (insert (comb t a b) s) f k) : Prog s f (k + 1)

theorem av_mem {s : Set F} {f} (h : f ∈ s) : Av s f := Or.inr ⟨f, h, Or.inl rfl⟩

theorem av_ins {s : Set F} {f} (g) (h : Av s f) : Av (insert g s) f := by
  rcases h with h | ⟨u, hu, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨u, Set.mem_insert_of_mem _ hu, h⟩

theorem av_not {s : Set F} {f} (h : Av s f) : Av s (fun x => !f x) := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl ⟨!b, rfl⟩
  · exact Or.inr ⟨_, hu, Or.inr rfl⟩
  · exact Or.inr ⟨u, hu, Or.inl (by funext x; simp)⟩

theorem av_rs {s t : Set F} {i c} (hs : ∀ u ∈ s, Av t (rs i c u)) {f} (h : Av s f) :
    Av t (rs i c f) := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl ⟨b, rfl⟩
  · exact hs _ hu
  · exact av_not (hs _ hu)

theorem av_cheap {s : Set F} (t) {a b : F} (ha : Av s a) (hb : Av s b) (h : Cst a ∨ Cst b) :
    Av s (comb t a b) := by
  rcases h with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · by_cases h : e = t
    · subst h
      rw [show comb e (fun _ => e) b = b by funext x; cases e <;> simp [comb]]
      exact hb
    · exact Or.inl ⟨e, by funext x; cases t <;> cases e <;> simp_all [comb]⟩
  · by_cases h : e = t
    · subst h
      rw [show comb e a (fun _ => e) = a by funext x; cases e <;> simp [comb]]
      exact ha
    · exact Or.inl ⟨e, by funext x; cases t <;> cases e <;> simp_all [comb]⟩

theorem smp_av {s : Set F} {i c} (hs : ∀ u ∈ s, Smp i c u) {f} (h : Av s f) : Smp i c f := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl fun _ _ => rfl
  · exact hs _ hu
  · rcases hs _ hu with h | ⟨b, h⟩
    · exact Or.inl fun x b => congrArg not (h x b)
    · exact Or.inr ⟨!b, by funext x; exact congrArg not (congrFun h x)⟩

theorem li_av {s : Set F} {i} (hs : ∀ u ∈ s, LI i u) {f} (h : Av s f) : LI i f := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl fun _ _ => rfl
  · exact hs _ hu
  · rcases hs _ hu with h | ⟨e, rfl⟩
    · exact Or.inl fun x b => congrArg not (h x b)
    · exact Or.inr ⟨!e, by funext x; cases e <;> simp⟩

theorem restrict {i : Fin 6} {c : Bool} {s : Set F} {f k} (p : Prog s f k) :
    ∀ t : Set F, (∀ u ∈ s, Av t (rs i c u)) →
    ∃ j ≤ k, Prog t (rs i c f) j ∧ (j = k → (∀ u ∈ s, Smp i c u) → Smp i c f) := by
  induction p with
  | done h => exact fun t hs => ⟨0, le_rfl, .done (av_rs hs h), fun _ h' => smp_av h' h⟩
  | @gate s f a b k tag ha hb tail ih =>
    intro t hs
    have pa := av_rs hs ha
    have pb := av_rs hs hb
    by_cases hc : Cst (rs i c a) ∨ Cst (rs i c b)
    · obtain ⟨j, hj, q, _⟩ := ih t (by
        intro v hv
        rcases Set.mem_insert_iff.mp hv with rfl | hu
        · exact av_cheap tag pa pb hc
        · exact hs _ hu)
      exact ⟨j, by omega, q, fun he => by omega⟩
    · obtain ⟨j, hj, q, act⟩ := ih (insert (comb tag (rs i c a) (rs i c b)) t) (by
        intro v hv
        rcases Set.mem_insert_iff.mp hv with rfl | hu
        · exact av_mem (Set.mem_insert _ _)
        · exact av_ins _ (hs _ hu))
      refine ⟨j + 1, by omega, .gate tag pa pb q, fun he ss => act (by omega) ?_⟩
      intro u hu
      rcases Set.mem_insert_iff.mp hu with rfl | hu
      · have sa := (smp_av ss ha).resolve_right (fun h => hc (.inl h))
        have sb := (smp_av ss hb).resolve_right (fun h => hc (.inr h))
        exact Or.inl fun x e => by simp only [comb, sa x e, sb x e]
      · exact ss _ hu

theorem strict {i : Fin 6} {c : Bool} {s : Set F} {f k} (p : Prog s f k) (t : Set F)
    (hs : ∀ u ∈ s, Av t (rs i c u)) (hi : ∀ u ∈ s, Smp i c u) (hf : ¬ Smp i c f) :
    ∃ j, j + 1 ≤ k ∧ Prog t (rs i c f) j := by
  obtain ⟨j, hj, q, h⟩ := restrict p t hs
  exact ⟨j, lt_of_le_of_ne hj (fun he => hf (h he hi)), q⟩

theorem li_smp {i c f} (h : LI i f) : Smp i c f := by
  rcases h with h | ⟨e, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨xor c e, by funext x; simp [rs]⟩

theorem kill {i : Fin 6} {t : Bool} {a b : F} (h : (∃ e, a = fun x => xor (x i) e) ∨
    ∃ e, b = fun x => xor (x i) e) : ∃ c, Cst (rs i c (comb t a b)) := by
  rcases h with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · refine ⟨xor e (!t), !t, ?_⟩
    funext x
    cases t <;> cases e <;> simp [rs, comb]
  · refine ⟨xor e (!t), !t, ?_⟩
    funext x
    cases t <;> cases e <;> simp [rs, comb]

theorem double {i : Fin 6} {s : Set F} {f k} (p : Prog s f k) (hs : ∀ u ∈ s, LI i u)
    (hf : ∀ c, ¬ Smp i c f) :
    ∃ c, ∀ t : Set F, (∀ u ∈ s, Av t (rs i c u)) → ∃ j, j + 2 ≤ k ∧ Prog t (rs i c f) j := by
  induction p with
  | done h => exact absurd (li_smp (li_av hs h)) (hf true)
  | @gate s f a b k tag ha hb tail ih =>
    by_cases hl : (∃ e, a = fun x => xor (x i) e) ∨ ∃ e, b = fun x => xor (x i) e
    · obtain ⟨c, hc⟩ := kill (t := tag) hl
      refine ⟨c, fun t ht => ?_⟩
      obtain ⟨j, hj, q⟩ := strict tail t (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact Or.inl hc
        · exact ht _ hu) (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact Or.inr hc
        · exact li_smp (hs _ hu)) (hf c)
      exact ⟨j, by omega, q⟩
    · have ia := (li_av hs ha).resolve_right (fun h => hl (.inl h))
      have ib := (li_av hs hb).resolve_right (fun h => hl (.inr h))
      obtain ⟨c, hc⟩ := ih (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact Or.inl fun x e => by simp only [comb, ia x e, ib x e]
        · exact hs _ hu) hf
      refine ⟨c, fun t ht => ?_⟩
      obtain ⟨j, hj, q⟩ := hc (insert (comb tag (rs i c a) (rs i c b)) t) (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact av_mem (Set.mem_insert _ _)
        · exact av_ins _ (ht _ hu))
      exact ⟨j + 1, by omega, .gate tag (av_rs ht ha) (av_rs ht hb) q⟩

def stock : Set F := Set.range fun (i : Fin 6) (x : X) => x i

theorem stock_li (i) : ∀ u ∈ stock, LI i u := by
  rintro _ ⟨j, rfl⟩
  by_cases h : j = i
  · subst h
    exact Or.inr ⟨false, by simp⟩
  · exact Or.inl fun x b => by simp [Function.update_of_ne h]

theorem stock_rs (i c) : ∀ u ∈ stock, Av stock (rs i c u) := by
  rintro _ ⟨j, rfl⟩
  by_cases h : j = i
  · subst h
    exact Or.inl ⟨c, by funext x; simp [rs]⟩
  · exact Or.inr ⟨_, ⟨j, rfl⟩, Or.inl (by funext x; simp [rs, Function.update_of_ne h])⟩

def pt (n : ℕ) : X := fun i => n.testBit i

theorem good_at {i c f} (a b d : ℕ)
    (h : (f (Function.update (pt a) i true) != f (pt a)) &&
        (rs i c f (pt b) != rs i c f (pt d)) = true) : ¬ Smp i c f := by
  simp only [Bool.and_eq_true, bne_iff_ne] at h
  obtain ⟨ha, hb⟩ := h
  rintro (hi | ⟨v, e⟩)
  · exact ha (hi _ _)
  · rw [e] at hb
    simp at hb

def Low (n : ℕ) (f : F) : Prop := ∀ k, Prog stock f k → n ≤ k

theorem zero (f : F) : Low 0 f := fun _ _ => Nat.zero_le _

theorem one {n f} (i c) (h : ¬ Smp i c f) (t : Low n (rs i c f)) : Low (n + 1) f := by
  intro k p
  obtain ⟨j, hj, q⟩ := strict p stock (stock_rs i c) (fun u hu => li_smp (stock_li i u hu))
    h
  have := t j q
  omega

theorem two {n f} (i) (h0 : ¬ Smp i false f) (h1 : ¬ Smp i true f)
    (t0 : Low n (rs i false f)) (t1 : Low n (rs i true f)) : Low (n + 2) f := by
  intro k p
  obtain ⟨c, hc⟩ := double p (stock_li i) (by
    intro c
    cases c
    · exact h0
    · exact h1)
  obtain ⟨j, hj, q⟩ := hc stock (stock_rs i c)
  cases c
  · have := t0 j q
    omega
  · have := t1 j q
    omega

def rd (w : List F) (i : ℕ) : F := fun x => (w.map fun f => f x).getD i false

def gv (w : List F) (g : Gate) : F := fun x => g.op.eval (g.inputs.map fun i => rd w i x)

theorem rd_av {s : Set F} {w : List F} (hw : ∀ u ∈ w, Av s u) (i : ℕ) : Av s (rd w i) := by
  by_cases h : i < w.length
  · have e : rd w i = w[i] := by funext x; simp [rd, h]
    rw [e]
    exact hw _ (List.getElem_mem h)
  · exact Or.inl ⟨false, by funext x; simp [rd, Nat.le_of_not_lt h]⟩

theorem gv_av {s : Set F} {w : List F} (hw : ∀ u ∈ w, Av s u) (g : Gate)
    (hop : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hl : g.inputs.length ≤ 2) :
    Av s (gv w g) ∨ (g.op ≠ .not ∧ ∃ t a b, Av s a ∧ Av s b ∧ gv w g = comb t a b) := by
  obtain ⟨op, args⟩ := g
  simp only at hop hl
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨k, r⟩⟩⟩
  · left
    exact Or.inl ⟨op.eval [], by funext x; simp [gv]⟩
  · left
    rcases hop with rfl | rfl | rfl
    · rw [show gv w ⟨.and, [i]⟩ = rd w i by funext x; simp [gv, GateOp.eval]]
      exact rd_av hw i
    · rw [show gv w ⟨.or, [i]⟩ = rd w i by funext x; simp [gv, GateOp.eval]]
      exact rd_av hw i
    · rw [show gv w ⟨.not, [i]⟩ = fun x => !rd w i x by funext x; simp [gv, GateOp.eval]]
      exact av_not (rd_av hw i)
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr ⟨by simp, true, _, _, rd_av hw i, rd_av hw j,
        by funext x; simp [gv, GateOp.eval, comb]⟩
    · exact Or.inr ⟨by simp, false, _, _, rd_av hw i, rd_av hw j,
        by funext x; simp [gv, GateOp.eval, comb]⟩
    · left
      rw [show gv w ⟨.not, [i, j]⟩ = fun x => !rd w i x by funext x; simp [gv, GateOp.eval]]
      exact av_not (rd_av hw i)
  · simp at hl

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false

theorem toProg (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) (o : ℕ) :
    ∀ (w : List F) (s : Set F), (∀ u ∈ w, Av s u) →
    ∃ k ≤ (gs.filter fun g => !isNot g).length,
      Prog s (rd (gs.foldl (fun w g => w ++ [gv w g]) w) o) k := by
  induction gs with
  | nil => exact fun w s hw => ⟨0, le_rfl, .done (rd_av hw o)⟩
  | cons g gs ih =>
    intro w s hw
    have hg' := hg g (by simp)
    have ih := ih fun v hv => hg v (by simp [hv])
    have hlen : (gs.filter fun g => !isNot g).length ≤
        ((g :: gs).filter fun g => !isNot g).length := by
      rw [List.filter_cons]
      split <;> simp
    rcases gv_av hw g hg'.1 hg'.2 with h | ⟨hn, t, a, b, ha, hb, e⟩
    · obtain ⟨k, hk, p⟩ := ih (w ++ [gv w g]) s (by
        intro u hu
        rcases List.mem_append.mp hu with h' | h'
        · exact hw _ h'
        · rw [List.mem_singleton.mp h']
          exact h)
      exact ⟨k, hk.trans hlen, p⟩
    · obtain ⟨k, hk, p⟩ := ih (w ++ [gv w g]) (insert (comb t a b) s) (by
        intro u hu
        rcases List.mem_append.mp hu with h' | h'
        · exact av_ins _ (hw _ h')
        · rw [List.mem_singleton.mp h', e]
          exact av_mem (Set.mem_insert _ _))
      refine ⟨k + 1, ?_, .gate t ha hb p⟩
      have : isNot g = false := by
        rcases hg'.1 with h | h | h
        · simp [isNot, h]
        · simp [isNot, h]
        · exact absurd h hn
      simp [this]
      simpa using hk

theorem fold_eval (gs : List Gate) (x : X) : ∀ w : List F,
    (gs.foldl (fun w g => w ++ [gv w g]) w).map (fun f => f x) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (w.map fun f => f x) := by
  induction gs with
  | nil => exact fun _ => rfl
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons, ih, List.map_append, List.map_cons, List.map_nil]
    rfl

theorem all_not_not {n : ℕ} {f : F} (hl : Low n f) (gs : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : gs.length ≤ n)
    (he : ∀ x : X, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = f x) :
    ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  obtain ⟨k, hk, p⟩ := toProg gs hg o
    (List.ofFn fun (i : Fin 6) (x : X) => x i) stock (by
      intro u hu
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
      exact av_mem ⟨i, rfl⟩)
  have e : rd (gs.foldl (fun w g => w ++ [gv w g])
      (List.ofFn fun (i : Fin 6) (x : X) => x i)) o = f := by
    funext x
    rw [← he x, rd, fold_eval, List.map_ofFn]
    rfl
  rw [e] at p
  have h := hl k p
  have hle := List.length_filter_le (fun g => !isNot g) gs
  have hall : ∀ g ∈ gs, (!isNot g) = true := by
    rw [← List.length_filter_eq_length_iff]
    omega
  intro g hm
  have h2 := hall g hm
  refine ⟨?_, (hg g hm).2⟩
  rcases (hg g hm).1 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · simp [isNot, h] at h2

def sixTarget : F := fun x : Fin 6 → Bool => Nat.testBit (4276677320 * 2 ^ 32 + 4276125824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def sixWitness : Circuit := ⟨[⟨.or, [2, 3]⟩, ⟨.and, [6, 4]⟩, ⟨.or, [4, 1]⟩, ⟨.and, [8, 2]⟩, ⟨.or, [9, 0]⟩, ⟨.and, [5, 10]⟩, ⟨.or, [11, 7]⟩, ⟨.and, [10, 3]⟩, ⟨.or, [13, 1]⟩, ⟨.and, [12, 14]⟩, ⟨.and, [9, 0]⟩, ⟨.or, [15, 16]⟩], 17⟩

theorem basis : Monotone2 sixWitness := by simp [Monotone2, sixWitness]
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
theorem correct : ∀ x : X, sixWitness.eval (List.ofFn x) = sixTarget x := by decide +kernel

namespace Evidence

def packCertificateWords (ws : List Nat) : Nat := ws.foldl (fun n w => (n <<< 64) + w) 0

def largeWord0 : Nat := packCertificateWords [0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa]

def largeWord1 : Nat := packCertificateWords [0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc]

def largeWord2 : Nat := packCertificateWords [0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0]

def largeWord3 : Nat := packCertificateWords [0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00]

def largeWord4 : Nat := packCertificateWords [0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000]

def largeWord5 : Nat := packCertificateWords [0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000]

def largeWord6 : Nat := packCertificateWords [0xffffffffffffffff, 0x0, 0xffffffffffffffff, 0x0]

def largeWord7 : Nat := packCertificateWords [0xffffffffffffffff, 0xffffffffffffffff, 0x0, 0x0]

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
def mask256:Nat:=2 ^ 256 - 1
def negD (d w:Nat):Nat:=(w^^^mask256)&&&d
def andD (d a b:Nat):Nat:=(a&&&b)&&&d
def orD (d a b:Nat):Nat:=(a|||b)&&&d
def opD (d:Nat) (op:Nat) (a b:Nat):Nat :=
  if op==0 then andD d a b
  else if op==1 then orD d a b
  else if op==2 then andD d a (negD d b)
  else andD d (negD d a) b
def allowedB (u:Bool) (op:Nat):Bool :=
  decide (op < 2)||(u&&decide (op < 4))
def flipOp (op:Nat):Nat :=
  if op==2 then 3 else if op==3 then 2 else op
def nrmD (u:Bool) (d w:Nat):Nat :=
  if u&&w.testBit 0 then negD d w else w&&&d
def kept {α : Type} (b:Bool) (x : α) (xs:List α):List α :=
  if b then x :: xs else xs
def RunD (u:Bool) (d y:Nat) (t : ℕ) (ws:List Nat) : Prop :=
  ∀ P : ℕ → List Nat → Prop,P 0 [y] →
    (∀ {s xs zs},List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a b r} (op:Nat) (ka kb:Bool),
      allowedB u op = true →
      opD d op a b ≠ 0 →
      opD d op a b ≠ d →
      opD d op a b ∉ (a :: b :: r) →
      P s (opD d op a b :: kept ka a (kept kb b r)) →
      P (s + 1) (a :: b :: r)) → P t ws
section
variable {u:Bool} {d y:Nat}
theorem Run.done : RunD u d y 0 [y]:=fun _ dn _ _=>dn
theorem Run.perm {s xs zs} (p : List.Perm xs zs) (h : RunD u d y s xs) :
    RunD u d y s zs:=fun P dn q b=>q p (h P dn q b)
theorem Run.two {s a b r} (op:Nat) (ka kb:Bool)
    (hop : allowedB u op = true)
    (h0 : opD d op a b ≠ 0) (hd : opD d op a b ≠ d) (hm : opD d op a b ∉ (a :: b :: r))
    (h : RunD u d y s (opD d op a b :: kept ka a (kept kb b r))) :
    RunD u d y (s + 1) (a :: b :: r):=fun P dn q v=>v op ka kb hop h0 hd hm (h P dn q v)
theorem Run.fold {P : ∀ t ws,RunD u d y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : RunD u d y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (two : ∀ {s a b r} (op:Nat) (ka kb:Bool)
      (hop : allowedB u op = true)
      (h0 : opD d op a b ≠ 0) (hd : opD d op a b ≠ d) (hm : opD d op a b ∉ (a :: b :: r))
      (h : RunD u d y s (opD d op a b :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two op ka kb hop h0 hd hm h))
    {t ws} (h : RunD u d y t ws) : P t ws h:=by
  have hex:=h (fun s xs=>∃ h' : RunD u d y s xs,P s xs h')
    ⟨Run.done,done⟩
    (fun hp ⟨h',ih⟩=>⟨Run.perm hp h',perm hp h' ih⟩)
    (fun op ka kb hop h0 hd hm ⟨h',ih⟩=>⟨Run.two op ka kb hop h0 hd hm h',two op ka kb hop h0 hd hm h' ih⟩)
  exact hex.elim fun _ hp=>hp
end
theorem allowed_cases {u:Bool} {op:Nat} (h : allowedB u op = true) :
    op = 0 ∨ op = 1 ∨ (u = true ∧ op = 2) ∨ (u = true ∧ op = 3):=by
  simp only [allowedB,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with h | ⟨hu,h⟩
  · omega
  · have : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3:=by omega
    rcases this with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl ⟨hu,rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hu,rfl⟩))
theorem opD_comm {u:Bool} (d:Nat) {op:Nat} (hop : allowedB u op = true) (a b:Nat) :
    opD d op a b = opD d (flipOp op) b a:=by
  rcases allowed_cases hop with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;>
    simp [opD,flipOp,andD,orD,Nat.and_comm,Nat.or_comm]
theorem flipOp_allowed {u:Bool} {op:Nat} (hop : allowedB u op = true) :
    allowedB u (flipOp op) = true:=by
  rcases allowed_cases hop with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [allowedB,flipOp]
theorem kept_map {α β : Type} (e : α → β) (b:Bool) (x : α) (xs:List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e):=by cases b <;> simp [kept]
theorem mem_kept {α : Type} (b:Bool) (x a : α) (xs:List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs:=by cases b <;> simp [kept]
theorem nodup_kept {α : Type} (b:Bool) (x : α) (xs:List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup:=by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h
theorem keep_perm {α : Type} {xs ys:List α} (p : xs.Perm ys) (b:Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys):=by cases b <;> simpa [kept] using p
theorem run_len {u d y s xs} (h : RunD u d y s xs) :
    xs.length ≤ s + 1:=by
  induction h using Run.fold with
  | done=>simp
  | perm hp _ ih=>rwa [← hp.length_eq]
  | two _ ka kb _ _ _ _ _ ih=>cases ka <;> cases kb <;> simp_all [kept] <;> omega
theorem zero_done {u d y t ws} (h : RunD u d y t ws) :
    t = 0 → ws = [y]:=by
  induction h using Run.fold with
  | done=>simp
  | perm p _ ih=>intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | two=>simp
def IsConst (d w:Nat) : Prop:=(w&&&d) = 0 ∨ (w&&&d) = d
def isConstB (d w:Nat):Bool:=(w&&&d==0)||(w&&&d==d)
theorem isConstB_iff (d w:Nat) : isConstB d w = true ↔ IsConst d w:=by
  simp [isConstB,IsConst]
def Avail (u:Bool) (d:Nat) (bank:List Nat) (w:Nat) : Prop :=
  IsConst d w ∨ (∃ v ∈ bank,(v&&&d) = (w&&&d)) ∨ (u = true ∧ ∃ v ∈ bank,(v&&&d) = negD d w)
def availB (u:Bool) (d:Nat) (bank:List Nat) (w:Nat):Bool :=
  let m:=w&&&d
  m==0||m==d||bank.any (fun v=>(v&&&d)==m) ||
    (u&&bank.any (fun v=>(v&&&d)==negD d w))
theorem availB_iff (u:Bool) (d:Nat) (bank:List Nat) (w:Nat) :
    availB u d bank w = true ↔ Avail u d bank w:=by
  simp [availB,Avail,IsConst,or_assoc]
def NatReach (u:Bool) (d:Nat) (roots:List Nat):Nat → List Nat → Prop
  | 0,bank=>bank = roots
  | p + 1,bank =>
    ∃ b a c op,allowedB u op = true ∧ bank = opD d op a c :: b ∧
      NatReach u d roots p b ∧ Avail u d b a ∧ Avail u d b c
def Lower (u:Bool) (d:Nat) (roots:List Nat) (T:Nat) (L:Nat) : Prop :=
  ∀ p bank,NatReach u d roots p bank → Avail u d bank T → L ≤ p
theorem opD_and_sub {d d1:Nat} (hd : d&&&mask256 = d) (hsub : d&&&d1 = d) (op a b:Nat) :
    opD d1 op a b&&&d = opD d op a b:=by
  apply Nat.eq_of_testBit_eq; intro i
  have h1:=congrArg (fun v=>v.testBit i) hd
  have h2:=congrArg (fun v=>v.testBit i) hsub
  unfold opD
  split_ifs <;> simp only [andD,orD,negD,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor] at * <;>
    cases hi : d.testBit i <;> simp_all
theorem negD_invol {d:Nat} (hd : d&&&mask256 = d) (a:Nat) :
    negD d (negD d a) = a&&&d:=by
  apply Nat.eq_of_testBit_eq; intro i
  have h1:=congrArg (fun v=>v.testBit i) hd
  simp only [negD,Nat.testBit_and,Nat.testBit_xor] at *
  cases hi : d.testBit i <;> cases ha : a.testBit i <;> simp_all
theorem negD_mask (d a:Nat) : negD d (a&&&d) = negD d a:=by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [negD,Nat.testBit_and,Nat.testBit_xor]
  cases d.testBit i <;> simp
theorem opD_mask_self (d op a b:Nat) : opD d op a b&&&d = opD d op a b:=by
  apply Nat.eq_of_testBit_eq; intro i
  unfold opD; split_ifs <;> simp only [andD,orD,negD,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor] <;>
    cases d.testBit i <;> simp
theorem negD_const {d:Nat} (hd : d&&&mask256 = d) {a:Nat} (hc : IsConst d a) :
    IsConst d (negD d a):=by
  rcases hc with h0 | h1
  · right; apply Nat.eq_of_testBit_eq; intro i
    have h0i:=congrArg (fun v=>v.testBit i) h0
    have hdi:=congrArg (fun v=>v.testBit i) hd
    simp only [negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
  · left; apply Nat.eq_of_testBit_eq; intro i
    have h1i:=congrArg (fun v=>v.testBit i) h1
    have hdi:=congrArg (fun v=>v.testBit i) hd
    simp only [negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
theorem avail_cons {u:Bool} {d:Nat} {bank:List Nat} (z w:Nat) (h : Avail u d bank w) :
    Avail u d (z :: bank) w:=by
  rcases h with hc | ⟨v,hv,he⟩ | ⟨hu,v,hv,he⟩
  · exact Or.inl hc
  · exact Or.inr (Or.inl ⟨v,List.mem_cons_of_mem _ hv,he⟩)
  · exact Or.inr (Or.inr ⟨hu,v,List.mem_cons_of_mem _ hv,he⟩)
theorem avail_of_eq {u:Bool} {d:Nat} {bank:List Nat} {v w:Nat}
    (he : v&&&d = w&&&d) (h : Avail u d bank v) : Avail u d bank w:=by
  rcases h with (h0 | h1) | ⟨x,hx,hxe⟩ | ⟨hu,x,hx,hxe⟩
  · exact Or.inl (Or.inl (he.symm.trans h0))
  · exact Or.inl (Or.inr (he.symm.trans h1))
  · exact Or.inr (Or.inl ⟨x,hx,hxe.trans he⟩)
  · exact Or.inr (Or.inr ⟨hu,x,hx,hxe.trans (by rw [← negD_mask,he,negD_mask])⟩)
theorem avail_neg {d:Nat} (hd : d&&&mask256 = d) {bank:List Nat} {w:Nat}
    (h : Avail true d bank w) : Avail true d bank (negD d w):=by
  rcases h with hc | ⟨v,hv,he⟩ | ⟨_,v,hv,he⟩
  · exact Or.inl (negD_const hd hc)
  · refine Or.inr (Or.inr ⟨rfl,v,hv,?_⟩)
    rw [negD_invol hd,he]
  · refine Or.inr (Or.inl ⟨v,hv,?_⟩)
    rw [he]; simp [negD,Nat.and_assoc,Nat.and_self]
theorem opD_const_left {u:Bool} {d:Nat} (hd : d&&&mask256 = d) {op:Nat}
    (hop : allowedB u op = true) {a b:Nat} (hc : IsConst d a) :
    (opD d op a b&&&d = 0) ∨ (opD d op a b&&&d = d) ∨
      (opD d op a b&&&d = b&&&d) ∨ (u = true ∧ opD d op a b&&&d = negD d b):=by
  rcases allowed_cases hop with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · rcases hc with h0 | h1
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h0i:=congrArg (fun v=>v.testBit i) h0
      simp only [opD,andD,Nat.testBit_and,Nat.zero_testBit,beq_self_eq_true,ite_true] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · right; right; left; apply Nat.eq_of_testBit_eq; intro i
      have h1i:=congrArg (fun v=>v.testBit i) h1
      simp only [opD,andD,Nat.testBit_and,beq_self_eq_true,ite_true] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rcases hc with h0 | h1
    · right; right; left; apply Nat.eq_of_testBit_eq; intro i
      have h0i:=congrArg (fun v=>v.testBit i) h0
      simp only [opD,orD,Nat.testBit_and,Nat.testBit_or,Nat.zero_testBit,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · right; left; apply Nat.eq_of_testBit_eq; intro i
      have h1i:=congrArg (fun v=>v.testBit i) h1
      simp only [opD,orD,Nat.testBit_and,Nat.testBit_or,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rcases hc with h0 | h1
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h0i:=congrArg (fun v=>v.testBit i) h0
      simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · right; right; right; refine ⟨hu,?_⟩
      apply Nat.eq_of_testBit_eq; intro i
      have h1i:=congrArg (fun v=>v.testBit i) h1
      have hdi:=congrArg (fun v=>v.testBit i) hd
      simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rcases hc with h0 | h1
    · right; right; left; apply Nat.eq_of_testBit_eq; intro i
      have h0i:=congrArg (fun v=>v.testBit i) h0
      have hdi:=congrArg (fun v=>v.testBit i) hd
      simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h1i:=congrArg (fun v=>v.testBit i) h1
      have hdi:=congrArg (fun v=>v.testBit i) hd
      simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
theorem countP_kept_ge {α : Type} (p : α → Bool) (b:Bool) (a : α) (xs:List α) :
    xs.countP p ≤ (kept b a xs).countP p:=by
  cases b <;> simp [kept,List.countP_cons] <;> split <;> omega
theorem contraction {u:Bool} {d d1 T:Nat} (hd : d&&&mask256 = d) (hsub : d&&&d1 = d)
    (hnc : ¬ IsConst d T) {s ws} (h : RunD u d1 T s ws) {roots p bank}
    (hp:NatReach u d roots p bank) (hs : ∀ w ∈ ws,Avail u d bank w) :
    ∃ q next,NatReach u d roots q next ∧ Avail u d next T ∧
      q + ws.countP (isConstB d) ≤ p + s:=by
  induction h using Run.fold generalizing p bank with
  | done =>
    have hfalse : isConstB d T = false:=by
      cases hc : isConstB d T with
      | false=>rfl
      | true=>exact absurd ((isConstB_iff d T).1 hc) hnc
    exact ⟨p,bank,hp,hs T (by simp),by simp [hfalse]⟩
  | perm eq _ ih =>
    obtain ⟨q,next,hq,ht,hle⟩:=ih hp (fun w hw=>hs w (eq.mem_iff.1 hw))
    rw [eq.countP_eq] at hle
    exact ⟨q,next,hq,ht,hle⟩
  | @two s a b r op ka kb hop _ _ _ _ ih =>
    have ha:=hs a List.mem_cons_self
    have hb:=hs b (List.mem_cons_of_mem _ List.mem_cons_self)
    set z1:=opD d1 op a b
    set z0:=opD d op a b
    have hz_eq : z1&&&d = z0&&&d:=by
      rw [opD_and_sub hd hsub,opD_mask_self]
    by_cases hcab : IsConst d a ∨ IsConst d b
    · have hz_av : Avail u d bank z1:=by
        apply avail_of_eq hz_eq.symm
        rcases hcab with hca | hcb
        · rcases opD_const_left hd hop hca with h0 | h1 | he | ⟨rfl,hn⟩
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm hb
          · exact avail_of_eq (by rw [hn]; simp [negD,Nat.and_assoc,Nat.and_self]) (avail_neg hd hb)
        · dsimp only [z0]; rw [opD_comm d hop a b]
          rcases opD_const_left hd (flipOp_allowed hop) hcb with h0 | h1 | he | ⟨rfl,hn⟩
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm ha
          · exact avail_of_eq (by rw [hn]; simp [negD,Nat.and_assoc,Nat.and_self]) (avail_neg hd ha)
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r),Avail u d bank w:=by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hz_av
        · rw [mem_kept,mem_kept] at hw
          rcases hw with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hw
          · exact ha
          · exact hb
          · exact hs w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))
      obtain ⟨q,next,hq,ht,hle⟩:=ih hp hs'
      have hkr : r.countP (isConstB d) ≤ (kept ka a (kept kb b r)).countP (isConstB d) :=
        le_trans (countP_kept_ge _ kb b r) (countP_kept_ge _ ka a _)
      have hcost : (if isConstB d a = true then 1 else 0) + (if isConstB d b = true then 1 else 0)
          ≤ 1 + (if isConstB d z1 = true then 1 else 0):=by
        rcases hcab with hca | hcb
        · have ha1 : isConstB d a = true:=(isConstB_iff _ _).2 hca
          rcases opD_const_left hd hop hca with h0 | h1 | he | ⟨_,hn⟩
          · have hz1 : isConstB d z1 = true:=(isConstB_iff _ _).2 (Or.inl (hz_eq.trans h0))
            simp [ha1,hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true:=(isConstB_iff _ _).2 (Or.inr (hz_eq.trans h1))
            simp [ha1,hz1]; split <;> omega
          · have hzb : isConstB d z1 = isConstB d b:=by simp only [isConstB,hz_eq.trans he]
            simp [ha1,hzb]
          · have hzb : isConstB d z1 = isConstB d b:=by
              apply Bool.eq_iff_iff.2; rw [isConstB_iff,isConstB_iff]
              have hnm : negD d b&&&d = negD d b:=by simp [negD,Nat.and_assoc,Nat.and_self]
              constructor
              · intro hz; have hnb : IsConst d (negD d b):=by
                  rcases hz with h0 | h1
                  · exact Or.inl (hnm.trans (hn.symm.trans (hz_eq.symm.trans h0)))
                  · exact Or.inr (hnm.trans (hn.symm.trans (hz_eq.symm.trans h1)))
                have h2:=negD_const hd hnb
                rw [negD_invol hd] at h2
                rcases h2 with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc,Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc,Nat.and_self] using e)]
              · intro hb'; have hnb:=negD_const hd hb'
                rcases hnb with h0 | h1
                · exact Or.inl (hz_eq.trans (hn.trans (hnm.symm.trans h0)))
                · exact Or.inr (hz_eq.trans (hn.trans (hnm.symm.trans h1)))
            simp [ha1,hzb]
        · have hb1 : isConstB d b = true:=(isConstB_iff _ _).2 hcb
          have hz_eq' : z1&&&d = opD d (flipOp op) b a&&&d:=by rw [hz_eq]; dsimp only [z0]; rw [opD_comm d hop a b]
          rcases opD_const_left hd (flipOp_allowed hop) hcb with h0 | h1 | he | ⟨_,hn⟩
          · have hz1 : isConstB d z1 = true:=(isConstB_iff _ _).2 (Or.inl (hz_eq'.trans h0))
            simp [hb1,hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true:=(isConstB_iff _ _).2 (Or.inr (hz_eq'.trans h1))
            simp [hb1,hz1]; split <;> omega
          · have hza : isConstB d z1 = isConstB d a:=by simp only [isConstB,hz_eq'.trans he]
            simp [hb1,hza]
          · have hza : isConstB d z1 = isConstB d a:=by
              apply Bool.eq_iff_iff.2; rw [isConstB_iff,isConstB_iff]
              have hnm : negD d a&&&d = negD d a:=by simp [negD,Nat.and_assoc,Nat.and_self]
              constructor
              · intro hz; have hna : IsConst d (negD d a):=by
                  rcases hz with h0 | h1
                  · exact Or.inl (hnm.trans (hn.symm.trans (hz_eq'.symm.trans h0)))
                  · exact Or.inr (hnm.trans (hn.symm.trans (hz_eq'.symm.trans h1)))
                have h2:=negD_const hd hna
                rw [negD_invol hd] at h2
                rcases h2 with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc,Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc,Nat.and_self] using e)]
              · intro ha'; have hna:=negD_const hd ha'
                rcases hna with h0 | h1
                · exact Or.inl (hz_eq'.trans (hn.trans (hnm.symm.trans h0)))
                · exact Or.inr (hz_eq'.trans (hn.trans (hnm.symm.trans h1)))
            simp [hb1,hza]
      simp only [List.countP_cons] at hle ⊢
      exact ⟨q,next,hq,ht,by omega⟩
    · have hna : isConstB d a = false:=by
        cases h : isConstB d a with | false=>rfl | true=>exact absurd (Or.inl ((isConstB_iff _ _).1 h)) hcab
      have hnb : isConstB d b = false:=by
        cases h : isConstB d b with | false=>rfl | true=>exact absurd (Or.inr ((isConstB_iff _ _).1 h)) hcab
      have hreach':NatReach u d roots (p + 1) (z0 :: bank):=⟨bank,a,b,op,hop,rfl,hp,ha,hb⟩
      have hz_av : Avail u d (z0 :: bank) z1:=Or.inr (Or.inl ⟨z0,List.mem_cons_self,hz_eq.symm⟩)
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r),Avail u d (z0 :: bank) w:=by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hz_av
        · rw [mem_kept,mem_kept] at hw
          rcases hw with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hw
          · exact avail_cons _ _ ha
          · exact avail_cons _ _ hb
          · exact avail_cons _ _ (hs w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)))
      obtain ⟨q,next,hq,ht,hle⟩:=ih hreach' hs'
      have hkr : r.countP (isConstB d) ≤ (kept ka a (kept kb b r)).countP (isConstB d) :=
        le_trans (countP_kept_ge _ kb b r) (countP_kept_ge _ ka a _)
      simp only [List.countP_cons,hna,hnb,Bool.false_eq_true,ite_false] at hle ⊢
      exact ⟨q,next,hq,ht,by omega⟩
theorem nrmD_mask (u:Bool) (d w:Nat) : nrmD u d w&&&d = nrmD u d w:=by
  unfold nrmD; split <;> simp [negD,Nat.and_assoc,Nat.and_self]
theorem nrmD_of_bit0_false (u:Bool) (d w:Nat) (hw : w.testBit 0 = false) :
    nrmD u d w = w&&&d:=by
  simp [nrmD,hw]
theorem nrmD_and_d {d:Nat} (hd0 : d.testBit 0 = true) (u:Bool) (w:Nat) :
    nrmD u d (w&&&d) = nrmD u d w:=by
  unfold nrmD
  rw [Nat.testBit_and,hd0,Bool.and_true,negD_mask,Nat.and_assoc,Nat.and_self]
theorem nrmD_neg {d:Nat} (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true) (w:Nat) :
    nrmD true d (negD d w) = nrmD true d w:=by
  have hm0 : mask256.testBit 0 = true:=by decide
  unfold nrmD
  have hnb : (negD d w).testBit 0 = !w.testBit 0:=by
    simp only [negD,Nat.testBit_and,Nat.testBit_xor,hd0,hm0,Bool.and_true,Bool.xor_true]
  rw [hnb]
  cases hw : w.testBit 0
  · simp [negD_invol hd]
  · simp [negD,Nat.and_assoc,Nat.and_self]
theorem nrmD_const_iff {d:Nat} (hd : d&&&mask256 = d) (u:Bool) (w:Nat) :
    (nrmD u d w ≠ 0 ∧ nrmD u d w ≠ d) ↔ ¬ IsConst d w:=by
  unfold nrmD
  have hnm : negD d w&&&d = negD d w:=by simp [negD,Nat.and_assoc,Nat.and_self]
  split
  · constructor
    · rintro ⟨h0,h1⟩ hc
      rcases negD_const hd hc with hn0 | hn1
      · exact h0 (hnm.symm.trans hn0)
      · exact h1 (hnm.symm.trans hn1)
    · intro hnc; refine ⟨fun h0=>?_,fun h1=>?_⟩
      · have:=negD_const hd (a:=negD d w) (Or.inl (hnm.trans h0))
        rw [negD_invol hd] at this
        exact hnc (by rcases this with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc,Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc,Nat.and_self] using e)])
      · have:=negD_const hd (a:=negD d w) (Or.inr (hnm.trans h1))
        rw [negD_invol hd] at this
        exact hnc (by rcases this with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc,Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc,Nat.and_self] using e)])
  · simp [IsConst,not_or]
theorem opD_bit {d:Nat} (hd : d&&&mask256 = d) (op a b i:Nat) (hdi : d.testBit i = true) :
    (opD d op a b).testBit i =
      if op==0 then a.testBit i&&b.testBit i
      else if op==1 then a.testBit i||b.testBit i
      else if op==2 then a.testBit i&&!(b.testBit i)
      else !(a.testBit i)&&b.testBit i:=by
  have hmi : mask256.testBit i = true:=by
    have:=congrArg (fun v=>v.testBit i) hd; simp [Nat.testBit_and,hdi] at this; exact this
  unfold opD; split_ifs <;>
    simp only [andD,orD,negD,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,hdi,hmi,Bool.and_true,Bool.xor_true]
theorem nrmD_bit {d:Nat} (hd : d&&&mask256 = d) (w i:Nat) (hdi : d.testBit i = true) :
    (nrmD true d w).testBit i = if w.testBit 0 then !(w.testBit i) else w.testBit i:=by
  have hmi : mask256.testBit i = true:=by
    have:=congrArg (fun v=>v.testBit i) hd; simp [Nat.testBit_and,hdi] at this; exact this
  unfold nrmD
  cases hw0 : w.testBit 0 <;>
    simp only [hw0,Bool.true_and,Bool.and_false,Bool.false_eq_true,ite_true,ite_false,
      negD,Nat.testBit_and,Nat.testBit_xor,hdi,hmi,Bool.and_true,Bool.xor_true]
theorem nrmD_opD {d:Nat} (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (u:Bool) (op:Nat) (hop : allowedB u op = true) (a b:Nat) :
    ∃ op',allowedB u op' = true ∧
      nrmD u d (opD d op a b) = opD d op' (nrmD u d a) (nrmD u d b):=by
  cases u with
  | false =>
    rcases allowed_cases hop with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
    · exact ⟨0,rfl,by
        apply Nat.eq_of_testBit_eq; intro i
        simp only [nrmD,opD,andD,Bool.false_and,Bool.false_eq_true,ite_false,beq_self_eq_true,ite_true,Nat.testBit_and]
        cases d.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,rfl,by
        apply Nat.eq_of_testBit_eq; intro i
        simp only [nrmD,opD,orD,Bool.false_and,Bool.false_eq_true,ite_false]
        simp only [show (1==0) = false from rfl,show (1==1) = true from rfl,Bool.false_eq_true,ite_false,ite_true,Nat.testBit_and,Nat.testBit_or]
        cases d.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · contradiction
    · contradiction
  | true =>
    have h4 : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3:=by
      rcases allowed_cases hop with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp
    have hbit : ∀ (e:Nat),
        (∀ i,d.testBit i = true →
          (nrmD true d (opD d op a b)).testBit i =
          (opD d e (nrmD true d a) (nrmD true d b)).testBit i) →
        nrmD true d (opD d op a b) = opD d e (nrmD true d a) (nrmD true d b):=by
      intro e h; apply Nat.eq_of_testBit_eq; intro i
      by_cases hdi : d.testBit i = true
      · exact h i hdi
      · have hf : d.testBit i = false:=Bool.eq_false_iff.2 hdi
        have h1:=congrArg (fun v=>v.testBit i) (nrmD_mask true d (opD d op a b))
        have h2:=congrArg (fun v=>v.testBit i) (opD_mask_self d e (nrmD true d a) (nrmD true d b))
        simp only [Nat.testBit_and,hf,Bool.and_false] at h1 h2; exact h1.symm.trans h2
    rcases h4 with rfl | rfl | rfl | rfl <;>
      cases ha0 : a.testBit 0 <;> cases hb0 : b.testBit 0
    · exact ⟨0,by decide,hbit 0 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2,by decide,hbit 2 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3,by decide,hbit 3 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,by decide,hbit 1 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,by decide,hbit 1 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3,by decide,hbit 3 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2,by decide,hbit 2 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨0,by decide,hbit 0 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2,by decide,hbit 2 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨0,by decide,hbit 0 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,by decide,hbit 1 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3,by decide,hbit 3 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3,by decide,hbit 3 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,by decide,hbit 1 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨0,by decide,hbit 0 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2,by decide,hbit 2 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
theorem avail_nrm_mem {u:Bool} {d:Nat} (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    {b:List Nat} {w:Nat} (h : Avail u d b w) (hnc : ¬ IsConst d w) :
    nrmD u d w ∈ b.map (nrmD u d):=by
  rcases h with hc | ⟨v,hv,he⟩ | ⟨rfl,v,hv,he⟩
  · exact absurd hc hnc
  · refine List.mem_map.2 ⟨v,hv,?_⟩
    rw [← nrmD_and_d hd0,he,nrmD_and_d hd0]
  · refine List.mem_map.2 ⟨v,hv,?_⟩
    rw [← nrmD_and_d hd0,he,nrmD_neg hd hd0]
theorem pull_two {u:Bool} {d Y k ws} (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hnd : ws.Nodup) (hprop : ∀ w ∈ ws,w ≠ 0 ∧ w ≠ d) (h : RunD u d Y k ws)
    {b:List Nat} {a c:Nat} (op:Nat) (hop : allowedB u op = true)
    (ha : Avail u d b a) (hc : Avail u d b c)
    (hsub : ∀ w ∈ ws,w ∈ nrmD u d (opD d op a c) :: b.map (nrmD u d)) :
    ∃ k' ws',k' ≤ k + 1 ∧ ws'.Nodup ∧ (∀ w ∈ ws',w ≠ 0 ∧ w ≠ d) ∧
      (∀ w ∈ ws',w ∈ b.map (nrmD u d)) ∧ RunD u d Y k' ws':=by
  set z:=nrmD u d (opD d op a c)
  by_cases hzm : z ∈ ws
  · by_cases hzb : z ∈ b.map (nrmD u d)
    · exact ⟨k,ws,by omega,hnd,hprop,fun w hw=>by
        rcases List.mem_cons.1 (hsub w hw) with rfl | hm
        · exact hzb
        · exact hm,h⟩
    · have hzp:=hprop z hzm
      obtain ⟨op',hop',hez⟩:=nrmD_opD hd hd0 u op hop a c
      have ha_nc : ¬ IsConst d a:=by
        intro hca
        have hznc : ¬ IsConst d (opD d op a c):=(nrmD_const_iff hd u _).1 hzp
        rcases opD_const_left hd hop hca with e0 | e1 | ec | ⟨rfl,en⟩
        · exact hznc (Or.inl e0)
        · exact hznc (Or.inr e1)
        · have hcn : ¬ IsConst d c:=fun hcc=>hznc (by rcases hcc with e | e <;> [exact Or.inl (ec.trans e); exact Or.inr (ec.trans e)])
          have hz_eq : z = nrmD u d c:=by dsimp only [z]; rw [← nrmD_and_d hd0 u (opD d op a c),ec,nrmD_and_d hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 hc hcn)
        · have hcn : ¬ IsConst d c:=fun hcc=>hznc (by
            rcases negD_const hd hcc with e | e
            · exact Or.inl (en.trans (by simpa [negD,Nat.and_assoc,Nat.and_self] using e))
            · exact Or.inr (en.trans (by simpa [negD,Nat.and_assoc,Nat.and_self] using e)))
          have hz_eq : z = nrmD true d c:=by dsimp only [z]; rw [← nrmD_and_d hd0 true (opD d op a c),en,nrmD_neg hd hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 hc hcn)
      have hc_nc : ¬ IsConst d c:=by
        intro hcc
        have hznc : ¬ IsConst d (opD d op a c):=(nrmD_const_iff hd u _).1 hzp
        have hcm : opD d op a c = opD d (flipOp op) c a:=opD_comm d hop a c
        rcases opD_const_left hd (flipOp_allowed hop) hcc with e0 | e1 | ea | ⟨rfl,en⟩
        · exact hznc (Or.inl (hcm.symm ▸ e0))
        · exact hznc (Or.inr (hcm.symm ▸ e1))
        · have hz_eq : z = nrmD u d a:=by
            dsimp only [z]; rw [← nrmD_and_d hd0 u (opD d op a c),hcm,ea,nrmD_and_d hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 ha ha_nc)
        · have hz_eq : z = nrmD true d a:=by
            dsimp only [z]; rw [← nrmD_and_d hd0 true (opD d op a c),hcm,en,nrmD_neg hd hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 ha ha_nc)
      set a':=nrmD u d a
      set c':=nrmD u d c
      have ha'_mem : a' ∈ b.map (nrmD u d):=avail_nrm_mem hd hd0 ha ha_nc
      have hc'_mem : c' ∈ b.map (nrmD u d):=avail_nrm_mem hd hd0 hc hc_nc
      have ha'_prop : a' ≠ 0 ∧ a' ≠ d:=(nrmD_const_iff hd u a).2 ha_nc
      have hc'_prop : c' ≠ 0 ∧ c' ≠ d:=(nrmD_const_iff hd u c).2 hc_nc
      have hne_ac : a' ≠ c':=by
        intro heq
        have hz_eq : opD d op' a' a' = a' ∨ opD d op' a' a' = 0:=by
          rcases allowed_cases hop' with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
          · left; apply Nat.eq_of_testBit_eq; intro i
            have hm:=congrArg (fun v=>v.testBit i) (nrmD_mask u d a)
            change (a'&&&d).testBit i = a'.testBit i at hm
            simp only [opD,andD,Nat.testBit_and] at hm ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
          · left; apply Nat.eq_of_testBit_eq; intro i
            have hm:=congrArg (fun v=>v.testBit i) (nrmD_mask u d a)
            change (a'&&&d).testBit i = a'.testBit i at hm
            simp only [opD,orD,Nat.testBit_and,Nat.testBit_or] at hm ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
          · right; apply Nat.eq_of_testBit_eq; intro i
            have hdi:=congrArg (fun v=>v.testBit i) hd
            simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at hdi ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
          · right; apply Nat.eq_of_testBit_eq; intro i
            have hdi:=congrArg (fun v=>v.testBit i) hd
            simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at hdi ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
        have hez' : z = opD d op' a' a':=by
          have : z = opD d op' a' c':=hez
          rw [← heq] at this; exact this
        rcases hz_eq with e | e
        · exact hzb ((hez'.trans e).symm ▸ ha'_mem)
        · exact hzp.1 (hez'.trans e)
      set rest:=ws.erase z
      have hrest_nd : rest.Nodup:=hnd.erase z
      have hrest_sub : ∀ w ∈ rest,w ∈ b.map (nrmD u d):=by
        intro w hw
        have ⟨hne,hm⟩:=hnd.mem_erase_iff.1 hw
        rcases List.mem_cons.1 (hsub w hm) with rfl | hmb
        · exact absurd rfl hne
        · exact hmb
      have hrest_prop : ∀ w ∈ rest,w ≠ 0 ∧ w ≠ d:=fun w hw=>hprop w (List.mem_of_mem_erase hw)
      have hp1 : ws.Perm (z :: rest):=List.perm_cons_erase hzm
      have h1 : RunD u d Y k (opD d op' a' c' :: rest):=by
        rw [← hez]; exact Run.perm hp1 h
      set ka:=decide (a' ∈ rest)
      set kb:=decide (c' ∈ rest)
      set tail:=(rest.erase a').erase c'
      have htail_nd : tail.Nodup:=(hrest_nd.erase a').erase c'
      have hna_tail : a' ∉ tail:=by
        intro hm; exact hrest_nd.not_mem_erase (List.mem_of_mem_erase hm)
      have hnc_tail : c' ∉ tail:=(hrest_nd.erase a').not_mem_erase
      have hna_mid : a' ∉ kept kb c' tail:=by
        rw [mem_kept]; rintro (⟨_,h⟩ | h)
        · exact hne_ac h
        · exact hna_tail h
      have hrest_perm : rest.Perm (kept ka a' (kept kb c' tail)):=by
        refine (List.perm_ext_iff_of_nodup hrest_nd (nodup_kept ka a' _ (nodup_kept kb c' _ htail_nd hnc_tail) hna_mid)).2 ?_
        intro x
        rw [mem_kept,mem_kept,(hrest_nd.erase a').mem_erase_iff,hrest_nd.mem_erase_iff]
        by_cases hxa : x = a' <;> by_cases hxc : x = c' <;> by_cases hxr : x ∈ rest <;>
          simp_all [ka,kb]
      have h2:=Run.perm (hrest_perm.cons _) h1
      have hne0 : opD d op' a' c' ≠ 0:=fun h0=>hzp.1 (hez.trans h0)
      have hned : opD d op' a' c' ≠ d:=fun h1=>hzp.2 (hez.trans h1)
      have hnm : opD d op' a' c' ∉ (a' :: c' :: tail):=by
        rw [← hez,List.mem_cons,List.mem_cons]; rintro (e | e | hm)
        · exact hzb (by simpa [z,e] using ha'_mem)
        · exact hzb (by simpa [z,e] using hc'_mem)
        · exact hnd.not_mem_erase (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
      have h3 : RunD u d Y (k + 1) (a' :: c' :: tail):=Run.two op' ka kb hop' hne0 hned hnm h2
      have hnd3 : (a' :: c' :: tail).Nodup :=
        List.nodup_cons.2 ⟨by simp [hne_ac,hna_tail],List.nodup_cons.2 ⟨hnc_tail,htail_nd⟩⟩
      refine ⟨k + 1,a' :: c' :: tail,le_rfl,hnd3,?_,?_,h3⟩
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact ha'_prop
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact hc'_prop
          · exact hrest_prop w (List.mem_of_mem_erase (List.mem_of_mem_erase hw))
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact ha'_mem
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact hc'_mem
          · exact hrest_sub w (List.mem_of_mem_erase (List.mem_of_mem_erase hw))
  · exact ⟨k,ws,by omega,hnd,hprop,fun w hw=>by
      rcases List.mem_cons.1 (hsub w hw) with rfl | hm
      · exact absurd hw hzm
      · exact hm,h⟩
theorem reach_to_run_aux {u:Bool} {d:Nat} {roots:List Nat} {p bank}
    (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hr:NatReach u d roots p bank) :
    ∀ {Y k ws},ws.Nodup → (∀ w ∈ ws,w ≠ 0 ∧ w ≠ d) →
      (∀ w ∈ ws,w ∈ bank.map (nrmD u d)) → RunD u d Y k ws →
      ∃ k' ws',k' ≤ p + k ∧ ws'.Nodup ∧ (∀ w ∈ ws',w ≠ 0 ∧ w ≠ d) ∧
        (∀ w ∈ ws',w ∈ roots.map (nrmD u d)) ∧ RunD u d Y k' ws':=by
  induction p generalizing bank with
  | zero =>
    intro Y k ws hnd hprop hsub hrun
    subst hr
    exact ⟨k,ws,by omega,hnd,hprop,hsub,hrun⟩
  | succ p ih =>
    intro Y k ws hnd hprop hsub hrun
    obtain ⟨b,a,c,op,hop,rfl,hrb,ha,hc⟩:=hr
    have hsub' : ∀ w ∈ ws,w ∈ nrmD u d (opD d op a c) :: b.map (nrmD u d):=by
      intro w hw; simpa [List.map_cons] using hsub w hw
    obtain ⟨k1,ws1,hk1,hnd1,hprop1,hsub1,hrun1⟩:=pull_two hd hd0 hnd hprop hrun op hop ha hc hsub'
    obtain ⟨k2,ws2,hk2,hnd2,hprop2,hsub2,hrun2⟩:=ih hrb hnd1 hprop1 hsub1 hrun1
    exact ⟨k2,ws2,by omega,hnd2,hprop2,hsub2,hrun2⟩
theorem reach_to_run {u:Bool} {d:Nat} {roots:List Nat} {T:Nat} {p bank}
    (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hT0 : T.testBit 0 = false) (hR0 : roots.all (fun r=>!r.testBit 0) = true)
    (hnc : ¬ IsConst d T) (hr:NatReach u d roots p bank) (ha : Avail u d bank T) :
    ∃ s ws,s ≤ p ∧ ws.Nodup ∧ (∀ w ∈ ws,w ∈ roots.map (·&&&d)) ∧ RunD u d (T&&&d) s ws:=by
  have hTmem : T&&&d ∈ bank.map (nrmD u d):=by
    have:=avail_nrm_mem hd hd0 ha hnc
    rwa [nrmD_of_bit0_false u d T hT0] at this
  have hprop : ∀ w ∈ [T&&&d],w ≠ 0 ∧ w ≠ d:=by
    intro w hw; rw [List.mem_singleton.1 hw]
    exact ⟨fun e=>hnc (Or.inl e),fun e=>hnc (Or.inr e)⟩
  have hsub : ∀ w ∈ [T&&&d],w ∈ bank.map (nrmD u d):=by
    intro w hw; rw [List.mem_singleton.1 hw]; exact hTmem
  obtain ⟨s,ws,hs,hnd,_,hsub',hrun⟩:=reach_to_run_aux hd hd0 hr (List.nodup_singleton _) hprop hsub Run.done
  have hrmap : roots.map (nrmD u d) = roots.map (·&&&d):=by
    apply List.map_congr_left
    intro r hr_m
    have h0:=List.all_eq_true.1 hR0 r hr_m
    simp only [Bool.not_eq_true'] at h0
    exact nrmD_of_bit0_false u d r h0
  rw [hrmap] at hsub'
  exact ⟨s,ws,by omega,hnd,hsub',hrun⟩
theorem runD_bits {u d y s ws} (hd : d&&&mask256 = d) (h : RunD u d y s ws) (i j:Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws,w.testBit i = w.testBit j) : y.testBit i = y.testBit j:=by
  have hmi : mask256.testBit i = true:=by
    have:=congrArg (fun v=>v.testBit i) hd; simp [Nat.testBit_and,hi] at this; exact this
  have hmj : mask256.testBit j = true:=by
    have:=congrArg (fun v=>v.testBit j) hd; simp [Nat.testBit_and,hj] at this; exact this
  induction h using Run.fold with
  | done=>exact hw _ (by simp)
  | perm hp _ ih=>exact ih (fun w h=>hw w (hp.mem_iff.1 h))
  | two op ka kb hop _ _ _ _ ih =>
    apply ih; have ha:=hw _ List.mem_cons_self; have hb:=hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm
    rcases List.mem_cons.1 hm with rfl | hr
    · rcases allowed_cases hop with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;>
        simp [opD,andD,orD,negD,ha,hb,hi,hj,hmi,hmj]
    · rw [mem_kept,mem_kept] at hr
      rcases hr with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hr
      · exact ha
      · exact hb
      · exact hw _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
theorem runD_bits_le_mono {d y s ws} (h : RunD false d y s ws) (i j:Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws,w.testBit i ≤ w.testBit j) : y.testBit i ≤ y.testBit j:=by
  induction h using Run.fold with
  | done=>exact hw _ (by simp)
  | perm hp _ ih=>exact ih (fun w h=>hw w (hp.mem_iff.1 h))
  | two op ka kb hop _ _ _ _ ih =>
    apply ih; have ha:=hw _ List.mem_cons_self; have hb:=hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm
    rcases List.mem_cons.1 hm with rfl | hr
    · rcases allowed_cases hop with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · simp only [opD,andD,beq_self_eq_true,ite_true,Nat.testBit_and,hi,hj,Bool.and_true]; grind
      · simp only [opD,orD,beq_self_eq_true,ite_true,ite_false,Nat.testBit_and,Nat.testBit_or,hi,hj,Bool.and_true]; grind
      · contradiction
      · contradiction
    · rw [mem_kept,mem_kept] at hr
      rcases hr with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hr
      · exact ha
      · exact hb
      · exact hw _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
def moveBits (tag d w:Nat):Nat :=
  ((w&&&tag) <<< d)|||((w >>> d)&&&tag) |||
    (w^^^((w&&&tag)|||(w&&&(tag <<< d))))
theorem moved (tag d i w:Nat) (h : (tag&&&(tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d + i)
       else if (tag <<< d).testBit i then w.testBit (i - d) else w.testBit i):=by
  have ht:=congrArg (fun v:Nat=>v.testBit i) h
  simp only [Nat.testBit_and,Nat.zero_testBit] at ht
  simp only [moveBits,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_and,
    Nat.testBit_shiftRight,Nat.testBit_xor] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind
theorem move_hom (tag d:Nat) (h : (tag&&&(tag <<< d)) = 0) (a b:Nat) :
    moveBits tag d (a&&&b) = (moveBits tag d a&&&moveBits tag d b) ∧
    moveBits tag d (a|||b) = (moveBits tag d a|||moveBits tag d b) ∧
    moveBits tag d (a^^^b) = (moveBits tag d a^^^moveBits tag d b):=by
  refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,moved tag d i _ h] <;>
    split_ifs <;> simp
theorem move_zero (tag d:Nat) (h : (tag&&&(tag <<< d)) = 0) : moveBits tag d 0 = 0:=by
  apply Nat.eq_of_testBit_eq; intro i; rw [moved tag d i 0 h]; split_ifs <;> simp
def applyMoves (ms:List (Nat × Nat)) (w:Nat):Nat :=
  ms.foldl (fun acc p=>moveBits p.1 p.2 acc) w
def moveOK256 (p:Nat × Nat):Bool :=
  (p.1&&&(p.1 <<< p.2)==0)&&(moveBits p.1 p.2 mask256==mask256)
theorem applyMoves_hom (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true) :
    (∀ a b,applyMoves ms (a&&&b) = applyMoves ms a&&&applyMoves ms b) ∧
    (∀ a b,applyMoves ms (a|||b) = applyMoves ms a|||applyMoves ms b) ∧
    (∀ a b,applyMoves ms (a^^^b) = applyMoves ms a^^^applyMoves ms b) ∧
    applyMoves ms 0 = 0 ∧ applyMoves ms mask256 = mask256:=by
  induction ms with
  | nil=>exact ⟨fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,rfl,rfl⟩
  | cons p ps ih =>
    simp only [List.all_cons,Bool.and_eq_true,moveOK256,beq_iff_eq] at hok
    obtain ⟨⟨hz,hm⟩,hps⟩:=hok
    obtain ⟨hand,hor,hxor,h0,h256⟩:=ih hps
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro a b; simp only [applyMoves,List.foldl_cons,(move_hom p.1 p.2 hz a b).1]; exact hand _ _
    · intro a b; simp only [applyMoves,List.foldl_cons,(move_hom p.1 p.2 hz a b).2.1]; exact hor _ _
    · intro a b; simp only [applyMoves,List.foldl_cons,(move_hom p.1 p.2 hz a b).2.2]; exact hxor _ _
    · simp only [applyMoves,List.foldl_cons,move_zero p.1 p.2 hz]; exact h0
    · simp only [applyMoves,List.foldl_cons,hm]; exact h256
theorem move_invol (tag d w:Nat) (h : (tag&&&(tag <<< d)) = 0) :
    moveBits tag d (moveBits tag d w) = w:=by
  apply Nat.eq_of_testBit_eq; intro i
  have ht:=congrArg (fun v:Nat=>v.testBit i) h
  simp only [Nat.testBit_and,Nat.zero_testBit] at ht
  rw [moved tag d i _ h]
  by_cases h1 : tag.testBit i = true
  · simp only [h1,ite_true,moved tag d (d + i) w h]
    have h2 : tag.testBit (d + i) = false:=by
      have htd:=congrArg (fun v:Nat=>v.testBit (d + i)) h
      simp only [Nat.testBit_and,Nat.testBit_shiftLeft,Nat.zero_testBit] at htd
      have hge : d ≤ d + i:=Nat.le_add_right d i
      have hsub : d + i - d = i:=Nat.add_sub_cancel_left d i
      simp [hge,hsub,h1] at htd; exact htd
    have h3 : (tag <<< d).testBit (d + i) = true:=by
      simp [Nat.testBit_shiftLeft,Nat.le_add_right,Nat.add_sub_cancel_left,h1]
    simp [h2,h3,Nat.add_sub_cancel_left]
  · simp only [h1,ite_false]
    by_cases h2 : (tag <<< d).testBit i = true
    · simp only [h2,ite_true,moved tag d (i - d) w h]
      rw [Nat.testBit_shiftLeft] at h2
      simp only [Bool.and_eq_true,decide_eq_true_eq] at h2
      simp [h2.2,Nat.add_sub_of_le h2.1]
    · simp [h1,h2,moved tag d i w h]
theorem applyMoves_inj (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true) :
    Function.Injective (applyMoves ms):=by
  induction ms with
  | nil=>intro a b h; exact h
  | cons p ps ih =>
    simp only [List.all_cons,Bool.and_eq_true,moveOK256,beq_iff_eq] at hok
    intro a b h
    simp only [applyMoves,List.foldl_cons] at h
    have h1:=ih hok.2 h
    have:=congrArg (moveBits p.1 p.2) h1
    rwa [move_invol p.1 p.2 a hok.1.1,move_invol p.1 p.2 b hok.1.1] at this
theorem applyMoves_opD (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    {d1 d2:Nat} (hd : applyMoves ms d2 = d1) (op a b:Nat) :
    applyMoves ms (opD d2 op a b) = opD d1 op (applyMoves ms a) (applyMoves ms b):=by
  obtain ⟨hand,hor,hxor,_,h256⟩:=applyMoves_hom ms hok
  unfold opD; split_ifs <;> simp only [andD,orD,negD,hand,hor,hxor,h256,hd]
theorem applyMoves_runD {u d Y s} (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd : applyMoves ms d = d) (hY : applyMoves ms Y = Y) {ws} (h : RunD u d Y s ws) :
    RunD u d Y s (ws.map (applyMoves ms)):=by
  obtain ⟨_,_,_,h0,_⟩:=applyMoves_hom ms hok
  have hinj:=applyMoves_inj ms hok
  rw [← hY]
  induction h using Run.fold with
  | done=>exact Run.done
  | perm hp _ ih=>exact Run.perm (hp.map _) ih
  | @two s a b r op ka kb hop hne0 hned hnm _ ih =>
    have eop:=applyMoves_opD ms hok hd op a b
    have e1 : (opD d op a b :: kept ka a (kept kb b r)).map (applyMoves ms) =
        opD d op (applyMoves ms a) (applyMoves ms b) ::
          kept ka (applyMoves ms a) (kept kb (applyMoves ms b) (r.map (applyMoves ms))):=by
      simp [kept_map,eop]
    rw [e1] at ih
    refine Run.two op ka kb hop ?_ ?_ ?_ ih
    · intro e; rw [← eop] at e; exact hne0 (hinj (e.trans h0.symm))
    · intro e; rw [← eop] at e; exact hned (hinj (e.trans hd.symm))
    · rw [← eop,← List.map_cons,← List.map_cons,List.mem_map]; rintro ⟨x,hx,he⟩; exact hnm (hinj he ▸ hx)
theorem reach_map_moves {u:Bool} (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    {d1 d2:Nat} (hd1 : d1&&&mask256 = d1) (hd : applyMoves ms d2 = d1)
    {roots1 roots2:List Nat} (hroots : ∀ r ∈ roots2,Avail u d1 roots1 (applyMoves ms r)) :
    ∀ {p bank},NatReach u d2 roots2 p bank →
      ∃ bank',NatReach u d1 roots1 p bank' ∧ ∀ v ∈ bank,Avail u d1 bank' (applyMoves ms v):=by
  obtain ⟨hand,_,hxor,h0,h256⟩:=applyMoves_hom ms hok
  have hav : ∀ {b b' w},(∀ v ∈ b,Avail u d1 b' (applyMoves ms v)) →
      Avail u d2 b w → Avail u d1 b' (applyMoves ms w):=by
    intro b b' w hbb hw
    rcases hw with (hz | h1) | ⟨v,hv,he⟩ | ⟨rfl,v,hv,he⟩
    · exact Or.inl (Or.inl (by rw [← hd,← hand,hz,h0]))
    · exact Or.inl (Or.inr (by rw [← hd,← hand,h1]))
    · have hve : applyMoves ms v&&&d1 = applyMoves ms w&&&d1:=by rw [← hd,← hand,← hand,he]
      exact avail_of_eq hve (hbb v hv)
    · have hve : applyMoves ms v&&&d1 = negD d1 (applyMoves ms w)&&&d1:=by
        rw [← hd,← hand,he]; simp only [negD,hand,hxor,h256,hd,Nat.and_assoc,Nat.and_self]
      have hneg:=avail_neg hd1 (avail_of_eq hve (hbb v hv))
      exact avail_of_eq (by rw [negD_invol hd1,Nat.and_assoc,Nat.and_self]) hneg
  intro p
  induction p with
  | zero =>
    intro bank hr; subst hr
    exact ⟨roots1,rfl,hroots⟩
  | succ p ih =>
    intro bank hr
    obtain ⟨b,a,c,op,hop,rfl,hrb,ha,hc⟩:=hr
    obtain ⟨b',hrb',hbb⟩:=ih hrb
    have ha':=hav hbb ha; have hc':=hav hbb hc
    refine ⟨opD d1 op (applyMoves ms a) (applyMoves ms c) :: b',
      ⟨b',applyMoves ms a,applyMoves ms c,op,hop,rfl,hrb',ha',hc'⟩,?_⟩
    intro v hv; rcases List.mem_cons.1 hv with rfl | hv
    · exact Or.inr (Or.inl ⟨opD d1 op (applyMoves ms a) (applyMoves ms c),List.mem_cons_self,by
        rw [applyMoves_opD ms hok hd]⟩)
    · exact avail_cons _ _ (hbb v hv)
theorem lower_iso {u:Bool} {d1 d2 T1 T2 L:Nat} {roots1 roots2:List Nat}
    (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd1 : d1&&&mask256 = d1) (hd : applyMoves ms d2 = d1) (hT : applyMoves ms T2 = T1)
    (hroots : roots2.all (fun r=>availB u d1 roots1 (applyMoves ms r)) = true)
    (h1 : Lower u d1 roots1 T1 L) : Lower u d2 roots2 T2 L:=by
  obtain ⟨hand,_,hxor,h0,h256⟩:=applyMoves_hom ms hok
  have hr : ∀ r ∈ roots2,Avail u d1 roots1 (applyMoves ms r):=fun r hr =>
    (availB_iff u _ _ _).1 (List.all_eq_true.1 hroots r hr)
  intro p bank hreach ha
  obtain ⟨bank',hrb',hbb⟩:=reach_map_moves ms hok hd1 hd hr hreach
  apply h1 p bank' hrb'
  rcases ha with (hz | ho) | ⟨v,hv,he⟩ | ⟨rfl,v,hv,he⟩
  · exact Or.inl (Or.inl (by rw [← hT,← hd,← hand,hz,h0]))
  · exact Or.inl (Or.inr (by rw [← hT,← hd,← hand,ho]))
  · have hve : applyMoves ms v&&&d1 = T1&&&d1:=by rw [← hT,← hd,← hand,← hand,he]
    exact avail_of_eq hve (hbb v hv)
  · have hve : applyMoves ms v&&&d1 = negD d1 T1&&&d1:=by
      rw [← hT,← hd,← hand,he]; simp only [negD,hand,hxor,h256,hd,Nat.and_assoc,Nat.and_self]
    have hneg:=avail_neg hd1 (avail_of_eq hve (hbb v hv))
    exact avail_of_eq (by rw [negD_invol hd1,Nat.and_assoc,Nat.and_self]) hneg
def pairOK (d T:Nat) (p:Nat × Nat):Bool :=
  d.testBit p.1&&d.testBit p.2&&(T.testBit p.1 != T.testBit p.2)
def essOK (d T:Nat) (roots:List Nat) (a:Nat) (p:Nat × Nat):Bool :=
  pairOK d T p&&roots.all (fun v=>(v==a)||(v.testBit p.1==v.testBit p.2))
theorem countP_ge_sublist (p:Nat → Bool) {xs ys:List Nat}
    (hnd : xs.Nodup) (hsub : ∀ a ∈ xs,a ∈ ys) (hall : ∀ a ∈ xs,p a = true) :
    xs.length ≤ ys.countP p:=by
  induction xs generalizing ys with
  | nil=>simp
  | cons a xs ih =>
    have ⟨hna,hnd'⟩:=List.nodup_cons.1 hnd
    have ham : a ∈ ys:=hsub a List.mem_cons_self
    have hperm : ys.Perm (a :: ys.erase a):=List.perm_cons_erase ham
    rw [hperm.countP_eq,List.countP_cons,hall a List.mem_cons_self]
    have ih':=ih hnd' (fun x hx=>by
      have hne : x ≠ a:=fun e=>hna (e ▸ hx)
      exact (List.mem_erase_of_ne hne).2 (hsub x (List.mem_cons_of_mem _ hx)))
      (fun x hx=>hall x (List.mem_cons_of_mem _ hx))
    simp only [ite_true,List.length_cons]
    omega
theorem lower_slice {u:Bool} {d dSub T TSub L:Nat} {roots rootsSub:List Nat}
    (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hT0 : T.testBit 0 = false) (hR0 : roots.all (fun r=>!r.testBit 0) = true)
    (hdSub : dSub&&&mask256 = dSub) (hsub : dSub&&&d = dSub)
    (hT : T&&&dSub = TSub&&&dSub)
    (hnc : isConstB d T = false) (hncSub : isConstB dSub TSub = false)
    (hcov : roots.all (availB u dSub rootsSub) = true)
    (singles:List (Nat × Nat × Nat))
    (hs_nd : (singles.map Prod.fst).Nodup)
    (hs_ok : singles.all (fun e=>isConstB dSub e.1&&essOK d (T&&&d) (roots.map (·&&&d)) e.1 e.2) = true)
    (hprior : Lower u dSub rootsSub TSub L) :
    Lower u d roots T (L + singles.length):=by
  have hnc' : ¬ IsConst d T:=fun h=>by rw [(isConstB_iff _ _).2 h] at hnc; contradiction
  have hncSub' : ¬ IsConst dSub (T&&&d):=by
    intro h
    have e : (T&&&d)&&&dSub = TSub&&&dSub:=by
      rw [Nat.and_assoc,Nat.and_comm d dSub,hsub,hT]
    rcases h with h0 | h1
    · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
    · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
  intro p bank hr ha
  obtain ⟨s,ws,hs_le,hnd,hws_sub,hrun⟩:=reach_to_run hd hd0 hT0 hR0 hnc' hr ha
  have hws_av : ∀ w ∈ ws,Avail u dSub rootsSub w:=by
    intro w hw
    obtain ⟨r,hr_m,rfl⟩:=List.mem_map.1 (hws_sub w hw)
    have hav:=(availB_iff u _ _ _).1 (List.all_eq_true.1 hcov r hr_m)
    exact avail_of_eq (by rw [Nat.and_assoc,Nat.and_comm d dSub,hsub]) hav
  obtain ⟨q,next,hq,ht,hle⟩:=contraction hdSub hsub hncSub' hrun (p:=0) (bank:=rootsSub) rfl hws_av
  have hTSub_av : Avail u dSub next TSub:=avail_of_eq (by
    rw [Nat.and_assoc,Nat.and_comm d dSub,hsub,hT]) ht
  have hL : L ≤ q:=hprior q next hq hTSub_av
  have hsin_mem : ∀ a ∈ singles.map Prod.fst,a ∈ ws:=by
    intro a ha
    obtain ⟨⟨a',r1,r2⟩,hm,rfl⟩:=List.mem_map.1 ha
    have hok:=List.all_eq_true.1 hs_ok (a',r1,r2) hm
    simp only [Bool.and_eq_true,essOK,pairOK,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at hok
    obtain ⟨_,⟨⟨hr1,hr2⟩,hdiff⟩,hiso⟩:=hok
    by_contra hnot
    apply hdiff
    apply runD_bits hd hrun r1 r2 hr1 hr2
    intro w hw
    rcases hiso w (hws_sub w hw) with rfl | heq
    · exact absurd hw hnot
    · exact heq
  have hsin_const : ∀ a ∈ singles.map Prod.fst,isConstB dSub a = true:=by
    intro a ha
    obtain ⟨⟨a',r1,r2⟩,hm,rfl⟩:=List.mem_map.1 ha
    have hok:=List.all_eq_true.1 hs_ok _ hm
    simp only [Bool.and_eq_true] at hok
    exact hok.1
  have hcnt:=countP_ge_sublist (isConstB dSub) hs_nd hsin_mem hsin_const
  simp only [List.length_map] at hcnt
  omega
def stepOp (u:Bool) (d:Nat) (st:Nat × List Nat) (g:Nat × Nat × Nat):Nat × List Nat :=
  if allowedB u g.1 then
    let om:=opD d g.1 g.2.1 g.2.2
    if availB u d st.2 om then st
    else if availB u d st.2 g.2.1&&availB u d st.2 g.2.2 then (st.1 + 1,om :: st.2)
    else st
  else st
def runOps (u:Bool) (d:Nat) (st:Nat × List Nat) (ops:List (Nat × Nat × Nat)):Nat × List Nat :=
  ops.foldl (stepOp u d) st
theorem avail_of_availB_pool {u:Bool} {d:Nat} (hd : d&&&mask256 = d)
    {bank pool:List Nat} (hsup : ∀ v ∈ pool,Avail u d bank v) {w:Nat}
    (hb : availB u d pool w = true) : Avail u d bank w:=by
  rcases (availB_iff u d pool w).1 hb with hc | ⟨v,hv,he⟩ | ⟨rfl,v,hv,he⟩
  · exact Or.inl hc
  · exact avail_of_eq he (hsup v hv)
  · have hneg:=avail_neg hd (hsup v hv)
    have he' : negD d v&&&d = w&&&d:=by
      rw [← negD_mask,he,negD_invol hd,Nat.and_assoc,Nat.and_self]
    exact avail_of_eq he' hneg
theorem stepOp_sound {u:Bool} {d:Nat} (hd : d&&&mask256 = d) {roots bank:List Nat}
    (st:Nat × List Nat) (g:Nat × Nat × Nat)
    (hr:NatReach u d roots st.1 bank) (hsup : ∀ v ∈ st.2,Avail u d bank v) :
    ∃ bank',NatReach u d roots (stepOp u d st g).1 bank' ∧ ∀ v ∈ (stepOp u d st g).2,Avail u d bank' v:=by
  unfold stepOp; dsimp only
  split
  · rename_i hop
    split
    · exact ⟨bank,hr,hsup⟩
    · split
      · rename_i hab
        simp only [Bool.and_eq_true] at hab
        have ha:=avail_of_availB_pool hd hsup hab.1
        have hb:=avail_of_availB_pool hd hsup hab.2
        refine ⟨opD d g.1 g.2.1 g.2.2 :: bank,⟨bank,g.2.1,g.2.2,g.1,hop,rfl,hr,ha,hb⟩,?_⟩
        intro v hv
        rcases List.mem_cons.1 hv with rfl | hv
        · exact Or.inr (Or.inl ⟨_,List.mem_cons_self,rfl⟩)
        · exact avail_cons _ _ (hsup v hv)
      · exact ⟨bank,hr,hsup⟩
  · exact ⟨bank,hr,hsup⟩
theorem runOps_sound {u:Bool} {d:Nat} (hd : d&&&mask256 = d) {roots:List Nat}
    (ops:List (Nat × Nat × Nat)) :
    ∀ (st:Nat × List Nat) (bank:List Nat),
      NatReach u d roots st.1 bank → (∀ v ∈ st.2,Avail u d bank v) →
      ∃ bank',NatReach u d roots (runOps u d st ops).1 bank' ∧ ∀ v ∈ (runOps u d st ops).2,Avail u d bank' v:=by
  induction ops with
  | nil=>intro st bank hr hsup; exact ⟨bank,hr,hsup⟩
  | cons g ops ih =>
    intro st bank hr hsup
    obtain ⟨bank1,hr1,hsup1⟩:=stepOp_sound hd st g hr hsup
    exact ih (stepOp u d st g) bank1 hr1 hsup1
def checkPool (u:Bool) (dSub LSub s:Nat) (st:Nat × List Nat) (ws:List Nat):Bool :=
  decide (s + st.1 < LSub + ws.countP (isConstB dSub))&&ws.all (availB u dSub st.2)
theorem checkPool_sound {u:Bool} {d dSub T TSub LSub s:Nat} {rootsSub ws:List Nat}
    (hdSub : dSub&&&mask256 = dSub) (hsub : dSub&&&d = dSub)
    (hT : T&&&dSub = TSub&&&dSub) (hncSub : isConstB dSub TSub = false)
    (hprior : Lower u dSub rootsSub TSub LSub)
    (st:Nat × List Nat) (bank:List Nat)
    (hrb:NatReach u dSub rootsSub st.1 bank) (hsb : ∀ v ∈ st.2,Avail u dSub bank v)
    (hchk : checkPool u dSub LSub s st ws = true) :
    ¬ RunD u d (T&&&d) s ws:=by
  intro hrun
  simp only [checkPool,Bool.and_eq_true,decide_eq_true_eq] at hchk
  obtain ⟨hineq,hall⟩:=hchk
  have hws_av : ∀ w ∈ ws,Avail u dSub bank w:=fun w hw =>
    avail_of_availB_pool hdSub hsb (List.all_eq_true.1 hall w hw)
  have hnc' : ¬ IsConst dSub (T&&&d):=by
    intro h; have e : (T&&&d)&&&dSub = TSub&&&dSub:=by rw [Nat.and_assoc,Nat.and_comm d dSub,hsub,hT]
    rcases h with h0 | h1
    · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
    · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
  obtain ⟨q,next,hq,ht,hle⟩:=contraction hdSub hsub hnc' hrun hrb hws_av
  have hL:=hprior q next hq (avail_of_eq (by rw [Nat.and_assoc,Nat.and_comm d dSub,hsub,hT]) ht)
  omega
def subValidB (d dSub T TSub:Nat):Bool :=
  (dSub&&&mask256==dSub)&&(dSub&&&d==dSub)&&(T&&&dSub==TSub&&&dSub)&&!(isConstB dSub TSub)
theorem cpcs {u:Bool} {d dSub T TSub LSub s:Nat} {rootsSub ws:List Nat}
    (hv : subValidB d dSub T TSub = true)
    (hprior : Lower u dSub rootsSub TSub LSub)
    (ops:List (Nat × Nat × Nat)) (g:Nat × Nat × Nat)
    (hchk : checkPool u dSub LSub s (stepOp u dSub (runOps u dSub (0,rootsSub) ops) g) ws = true) :
    ¬ RunD u d (T&&&d) s ws:=by
  simp only [subValidB,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at hv
  have hsup0 : ∀ v ∈ rootsSub,Avail u dSub rootsSub v:=fun v hv=>Or.inr (Or.inl ⟨v,hv,rfl⟩)
  obtain ⟨bank1,hr1,hsup1⟩:=runOps_sound hv.1.1.1 ops (0,rootsSub) rootsSub rfl hsup0
  obtain ⟨bank2,hr2,hsup2⟩:=stepOp_sound hv.1.1.1 _ g hr1 hsup1
  exact checkPool_sound hv.1.1.1 hv.1.1.2 hv.1.2 hv.2 hprior _ bank2 hr2 hsup2 hchk
theorem checkRootSub_sound {u:Bool} {d dSub T TSub LSub s:Nat} {rootsSub ws:List Nat}
    (hv : subValidB d dSub T TSub = true)
    (hprior : Lower u dSub rootsSub TSub LSub)
    (hchk : checkPool u dSub LSub s (0,rootsSub) ws = true) :
    ¬ RunD u d (T&&&d) s ws:=by
  simp only [subValidB,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at hv
  exact checkPool_sound hv.1.1.1 hv.1.1.2 hv.1.2 hv.2 hprior (0,rootsSub) rootsSub rfl (fun v hv=>Or.inr (Or.inl ⟨v,hv,rfl⟩)) hchk
def coversP (u:Bool) (pairs:List (Nat × Nat)) (ws:List Nat):Bool :=
  if !u then
    pairs.all (fun p=>ws.any (fun w=>!w.testBit p.1&&w.testBit p.2))
  else
    pairs.all (fun p=>ws.any (fun w=>w.testBit p.1 != w.testBit p.2))
theorem coversP_ok {u:Bool} {d T s:Nat} (hd : d&&&mask256 = d)
    (pairs:List (Nat × Nat))
    (hpairs : pairs.all (fun p=>d.testBit p.1&&d.testBit p.2&&!(T&&&d).testBit p.1&&(T&&&d).testBit p.2) = true)
    {ws:List Nat} (h : RunD u d (T&&&d) s ws) : coversP u pairs ws = true:=by
  cases u with
  | false =>
    simp only [coversP,Bool.not_false,ite_true,List.all_eq_true,List.any_eq_true]
    intro ⟨u1,v1⟩ hm
    have hp:=List.all_eq_true.1 hpairs (u1,v1) hm
    simp only [Bool.and_eq_true,Bool.not_eq_true'] at hp
    by_contra! hall
    have hle:=runD_bits_le_mono h v1 u1 hp.1.1.2 hp.1.1.1 (fun w hw=>by
      have hbad:=hall w hw
      cases hu : w.testBit u1 <;> cases hv : w.testBit v1 <;> simp_all)
    rw [hp.1.2,hp.2] at hle; contradiction
  | true =>
    simp only [coversP,Bool.not_true,Bool.false_eq_true,ite_false,List.all_eq_true,List.any_eq_true,bne_iff_ne]
    intro ⟨u1,v1⟩ hm
    have hp:=List.all_eq_true.1 hpairs (u1,v1) hm
    simp only [Bool.and_eq_true,Bool.not_eq_true'] at hp
    by_contra! hall
    have heq:=runD_bits hd h u1 v1 hp.1.1.1 hp.1.1.2 hall
    rw [hp.1.2,hp.2] at heq; contradiction
def unorientedCov (pairs:List (Nat × Nat)) (ws:List Nat):Bool :=
  pairs.all (fun p=>ws.any (fun w=>w.testBit p.1 != w.testBit p.2))
theorem unorientedCov_ok {u:Bool} {d T s:Nat} (hd : d&&&mask256 = d)
    (pairs:List (Nat × Nat))
    (hpairs : pairs.all (fun p=>d.testBit p.1&&d.testBit p.2&&!(T&&&d).testBit p.1&&(T&&&d).testBit p.2) = true)
    {ws:List Nat} (h : RunD u d (T&&&d) s ws) : unorientedCov pairs ws = true:=by
  simp only [unorientedCov,List.all_eq_true,List.any_eq_true,bne_iff_ne]
  intro ⟨u1,v1⟩ hm
  have hp:=List.all_eq_true.1 hpairs (u1,v1) hm
  simp only [Bool.and_eq_true,Bool.not_eq_true'] at hp
  by_contra! hall
  have heq:=runD_bits hd h u1 v1 hp.1.1.1 hp.1.1.2 hall
  rw [hp.1.2,hp.2] at heq; contradiction
def maskP (m:Nat):Nat:=2 ^ m - 1
def projBit (rs:List Nat) (w:Nat):Nat :=
  rs.foldr (fun r acc=>(acc <<< 1)|||(if w.testBit r then 1 else 0)) 0
theorem projBit_testBit (rs:List Nat) (w:Nat) (i:Nat) :
    (projBit rs w).testBit i = if h : i < rs.length then w.testBit rs[i] else false:=by
  induction rs generalizing i with
  | nil=>simp [projBit]
  | cons r rs ih =>
    cases i with
    | zero =>
      simp only [projBit,List.foldr_cons,Nat.testBit_or,Nat.testBit_shiftLeft,
        Nat.not_le.2 Nat.zero_lt_one,decide_false,Bool.false_and,Bool.false_or,
        List.length_cons,Nat.zero_lt_succ,dite_true,List.getElem_cons_zero]
      cases w.testBit r <;> simp
    | succ i =>
      simp only [projBit,List.foldr_cons,Nat.testBit_or,Nat.testBit_shiftLeft,
        Nat.succ_le_succ (Nat.zero_le i),decide_true,Bool.true_and,Nat.add_sub_cancel,
        List.length_cons,Nat.succ_lt_succ_iff,List.getElem_cons_succ]
      have h1 : (if w.testBit r = true then 1 else 0).testBit (i + 1) = false:=by
        cases w.testBit r <;> simp [Nat.testBit_succ]
      rw [h1,Bool.or_false]; exact ih i
def opP (mp op:Nat) (pa pb:Nat):Nat :=
  if op==0 then pa&&&pb
  else if op==1 then pa|||pb
  else if op==2 then pa&&&(pb^^^mp)
  else (pa^^^mp)&&&pb
theorem projBit_opD {dm:Nat} (hd : dm&&&mask256 = dm) {rs:List Nat}
    (hrs : ∀ r ∈ rs,dm.testBit r = true) (op a b:Nat) :
    projBit rs (opD dm op a b) = opP (maskP rs.length) op (projBit rs a) (projBit rs b):=by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases hi : i < rs.length
  · have hdr:=hrs rs[i] (List.getElem_mem hi)
    have hmr : mask256.testBit rs[i] = true:=by
      have:=congrArg (fun v=>v.testBit rs[i]) hd; simp [Nat.testBit_and,hdr] at this; exact this
    unfold opD opP
    split_ifs <;>
      simp only [projBit_testBit,hi,dite_true,andD,orD,negD,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,
        maskP,Nat.testBit_two_pow_sub_one,decide_true,hdr,hmr,Bool.and_true,Bool.xor_true] <;>
      (cases a.testBit rs[i] <;> cases b.testBit rs[i] <;> rfl)
  · unfold opD opP
    split_ifs <;>
      simp only [projBit_testBit,hi,dite_false,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,
        maskP,Nat.testBit_two_pow_sub_one,decide_false,Bool.false_and,Bool.and_false,Bool.false_or,Bool.xor_false]
theorem foldl_or_testBit {α : Type} (g : α → Nat) (xs:List α) (acc i:Nat) :
    (xs.foldl (fun a x=>a|||g x) acc).testBit i = (acc.testBit i||xs.any (fun x=>(g x).testBit i)):=by
  induction xs generalizing acc with
  | nil=>simp
  | cons x xs ih =>
    simp only [List.foldl_cons,ih,Nat.testBit_or,List.any_cons,Bool.or_assoc]
def colB (mp:Nat) (oriented:Bool) (p:Nat × Nat):Nat :=
  if oriented then (p.1^^^mp)&&&p.2 else p.1^^^p.2
def coversD (u:Bool) (mp:Nat) (dws:List (Nat × Nat × Nat)):Bool :=
  dws.foldl (fun acc d=>acc|||colB mp (!u) d.2) 0==mp
theorem coversD_eq (u:Bool) (pairs:List (Nat × Nat)) (ws:List Nat) :
    coversD u (maskP pairs.length) (ws.map (fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w))) =
      coversP u pairs ws:=by
  set r1s:=pairs.map Prod.fst
  set r2s:=pairs.map Prod.snd
  set mp:=maskP pairs.length
  have hr1 : r1s.length = pairs.length:=List.length_map _
  have hr2 : r2s.length = pairs.length:=List.length_map _
  unfold coversD coversP
  cases u with
  | false =>
    simp only [Bool.not_false,colB,ite_true]
    apply Bool.eq_iff_iff.2; rw [beq_iff_eq,List.all_eq_true]
    constructor
    · intro heq pr hpr
      obtain ⟨i,hi,rfl⟩:=List.mem_iff_getElem.1 hpr
      have hb:=congrArg (fun v=>v.testBit i) heq
      rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,List.any_map] at hb
      simp only [mp,maskP,Nat.testBit_two_pow_sub_one,hi,decide_true] at hb
      obtain ⟨w,hw,hwt⟩:=List.any_eq_true.1 hb
      simp only [Function.comp_def,Nat.testBit_and,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_true,
        Nat.testBit_two_pow_sub_one,decide_true,Bool.xor_true] at hwt
      exact List.any_eq_true.2 ⟨w,hw,by simpa [r1s,r2s] using hwt⟩
    · intro hall
      apply Nat.eq_of_testBit_eq; intro i
      rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,List.any_map]
      simp only [mp,maskP,Nat.testBit_two_pow_sub_one]
      by_cases hi : i < pairs.length
      · simp only [hi,decide_true]
        obtain ⟨w,hw,hwt⟩:=List.any_eq_true.1 (hall pairs[i] (List.getElem_mem hi))
        exact List.any_eq_true.2 ⟨w,hw,by
          simp only [Function.comp_def,Nat.testBit_and,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_true,
            Nat.testBit_two_pow_sub_one,decide_true,Bool.xor_true,r1s,r2s,List.getElem_map]
          exact hwt⟩
      · simp only [hi,decide_false,List.any_eq_false]
        intro w _
        simp only [Function.comp_def,Nat.testBit_and,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_false,
          Nat.testBit_two_pow_sub_one,decide_false,Bool.xor_false,Bool.and_false,not_false_eq_true,Bool.false_eq_true]
  | true =>
    simp only [Bool.not_true,colB,Bool.false_eq_true,ite_false]
    apply Bool.eq_iff_iff.2; rw [beq_iff_eq,List.all_eq_true]
    constructor
    · intro heq pr hpr
      obtain ⟨i,hi,rfl⟩:=List.mem_iff_getElem.1 hpr
      have hb:=congrArg (fun v=>v.testBit i) heq
      rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,List.any_map] at hb
      simp only [mp,maskP,Nat.testBit_two_pow_sub_one,hi,decide_true] at hb
      obtain ⟨w,hw,hwt⟩:=List.any_eq_true.1 hb
      simp only [Function.comp_def,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_true] at hwt
      exact List.any_eq_true.2 ⟨w,hw,by simpa [r1s,r2s,bne] using hwt⟩
    · intro hall
      apply Nat.eq_of_testBit_eq; intro i
      rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,List.any_map]
      simp only [mp,maskP,Nat.testBit_two_pow_sub_one]
      by_cases hi : i < pairs.length
      · simp only [hi,decide_true]
        obtain ⟨w,hw,hwt⟩:=List.any_eq_true.1 (hall pairs[i] (List.getElem_mem hi))
        exact List.any_eq_true.2 ⟨w,hw,by
          simp only [Function.comp_def,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_true,r1s,r2s,List.getElem_map]
          simpa [bne] using hwt⟩
      · simp only [hi,decide_false,List.any_eq_false]
        intro w _
        simp only [Function.comp_def,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_false,
          Bool.xor_false,Bool.false_eq_true,not_false_eq_true]
theorem erase_map_inj {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hinj : Function.Injective f) (xs:List α) (a : α) :
    (xs.map f).erase (f a) = (xs.erase a).map f:=by
  induction xs with
  | nil=>rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.erase_cons]
    by_cases h : x = a
    · subst h; simp
    · have hf : (f x==f a) = false:=beq_false_of_ne (fun e=>h (hinj e))
      have hx : (x==a) = false:=beq_false_of_ne h
      simp [hf,hx,ih]
def value6 (a b c d e f:Bool):Nat :=
  let x:=b.toNat + c.toNat
  let y:=(!e).toNat + (!f).toNat
  if a then (if d then y else max x (max y (x + y - 1))) else (if d then 0 else x)
theorem value6_and : ∀ a b c d e f g h i j l m:Bool,
    value6 (a&&g) (b&&h) (c&&i) (d&&j) (e&&l) (f&&m)
      ≤ value6 a b c d e f + value6 g h i j l m:=by decide +kernel
theorem value6_or : ∀ a b c d e f g h i j l m:Bool,
    value6 (a||g) (b||h) (c||i) (d||j) (e||l) (f||m)
      ≤ value6 a b c d e f + value6 g h i j l m:=by decide +kernel
theorem score_bound {d y s ws} (h : RunD false d y s ws) (hl : ws.length = s + 1)
    (v:Nat → Nat) (hand : ∀ a b,v (andD d a b) ≤ v a + v b)
    (hor : ∀ a b,v (orD d a b) ≤ v a + v b) : v y ≤ (ws.map v).sum:=by
  induction h using Run.fold with
  | done=>simp
  | perm p _ ih=>rw [← (p.map v).sum_eq]; exact ih (p.length_eq.trans hl)
  | two op ka kb hop _ _ _ h ih =>
    have hh:=run_len h; cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih':=ih (by simp [kept]; omega)
    rcases allowed_cases hop with rfl | rfl | ⟨hc,_⟩ | ⟨hc,_⟩
    · simp only [opD,beq_self_eq_true,ite_true,kept,Bool.false_eq_true,ite_false,List.map_cons,List.sum_cons] at ih' ⊢
      grw [← Nat.add_assoc,← hand]; exact ih'
    · simp only [opD,beq_self_eq_true,ite_true,ite_false,kept,Bool.false_eq_true,List.map_cons,List.sum_cons] at ih' ⊢
      grw [← Nat.add_assoc,← hor]; exact ih'
    · contradiction
    · contradiction
def eval6 (a b c d e f v:Nat):=value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)
theorem eval6_bound {dm y s ws} (h : RunD false dm y s ws) (hl : ws.length = s + 1)
    (a b c d e f:Nat)
    (ha : dm.testBit a = true) (hb : dm.testBit b = true) (hc : dm.testBit c = true)
    (hd : dm.testBit d = true) (he : dm.testBit e = true) (hf : dm.testBit f = true) :
    eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum:=by
  apply score_bound h hl
  · intro v w
    simpa only [eval6,andD,Nat.testBit_and,ha,hb,hc,hd,he,hf,Bool.and_true] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6,orD,Nat.testBit_and,Nat.testBit_or,ha,hb,hc,hd,he,hf,Bool.and_true] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
def sumBelow (v:Nat → Nat):List Nat → Nat → Bool
  | [],n=>n != 0
  | w :: ws,n=>decide (v w < n)&&sumBelow v ws (n - v w)
theorem sumBelow_iff (v:Nat → Nat) (ws:List Nat) (n:Nat) :
    sumBelow v ws n = true ↔ (ws.map v).sum < n:=by
  induction ws generalizing n with
  | nil=>simp [sumBelow]
  | cons w ws ih=>rw [sumBelow,Bool.and_eq_true,decide_eq_true_eq,ih,List.map_cons,List.sum_cons]; omega
def scoreCheck (dm y s:Nat) (ws:List Nat) (code:Nat):Bool :=
  let a:=code&&&255
  let b:=(code >>> 8)&&&255
  let c:=(code >>> 16)&&&255
  let d:=(code >>> 24)&&&255
  let e:=(code >>> 32)&&&255
  let f:=(code >>> 40)&&&255
  dm.testBit a&&dm.testBit b&&dm.testBit c&&dm.testBit d&&dm.testBit e&&dm.testBit f &&
    ws.length==s + 1&&sumBelow (eval6 a b c d e f) ws (eval6 a b c d e f y)
theorem scoreCheck_no {dm y s ws} (h : RunD false dm y s ws) (code:Nat) :
    scoreCheck dm y s ws code = false:=by
  unfold scoreCheck
  by_cases hok : dm.testBit (code&&&255) = true ∧ dm.testBit ((code >>> 8)&&&255) = true ∧
      dm.testBit ((code >>> 16)&&&255) = true ∧ dm.testBit ((code >>> 24)&&&255) = true ∧
      dm.testBit ((code >>> 32)&&&255) = true ∧ dm.testBit ((code >>> 40)&&&255) = true ∧
      ws.length = s + 1
  · obtain ⟨ha,hb,hc,hd,he,hf,hl⟩:=hok
    simp only [ha,hb,hc,hd,he,hf,hl,beq_self_eq_true,Bool.true_and]
    by_contra hbad
    have hsum:=(sumBelow_iff _ _ _).1 (Bool.eq_true_of_not_eq_false hbad)
    exact (Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _ ha hb hc hd he hf)) hsum
  · by_contra hbad
    have ht:=Bool.eq_true_of_not_eq_false hbad
    simp only [Bool.and_eq_true,beq_iff_eq] at ht
    exact hok ⟨ht.1.1.1.1.1.1.1,ht.1.1.1.1.1.1.2,ht.1.1.1.1.1.2,ht.1.1.1.1.2,ht.1.1.1.2,ht.1.1.2,ht.1.2⟩
def scr (u:Bool) (dm y s:Nat) (pool:List Nat) (zs:List Nat):Bool :=
  !u&&zs.length==s + 1&&pool.any (scoreCheck dm y s zs)
theorem scr_no {u:Bool} {dm y s:Nat} (pool:List Nat) {zs:List Nat}
    (h : RunD u dm y s zs) : scr u dm y s pool zs = false:=by
  cases u with
  | true=>simp [scr]
  | false =>
    unfold scr; simp only [Bool.not_false,Bool.true_and]
    rw [Bool.and_eq_false_iff]; right; rw [List.any_eq_false]
    intro x _; rw [scoreCheck_no h x]; simp
def opsOf (u:Bool):List Nat:=if u then [0,1,2,3] else [0,1]
theorem mem_opsOf {u:Bool} {op:Nat} (hop : allowedB u op = true) : op ∈ opsOf u:=by
  rcases allowed_cases hop with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> decide
  · cases u <;> decide
  · decide
  · decide
def nextD (u:Bool) (dm:Nat) (slack:Nat) (ws:List Nat) (f : (Nat × Nat × Nat) → List Nat → Bool):Bool :=
  ws.any fun a =>
    let ra:=ws.erase a
    ra.any fun b =>
      a ≤ b&&(let r:=ra.erase b
        (opsOf u).any fun op =>
          let w:=opD dm op a b
          let g:=(op,a,b)
          w != 0&&w != dm&&!(ws.contains w) &&
            (f g (w :: r)||(slack ≥ 1&&(f g (w :: a :: r)||f g (w :: b :: r))) ||
              (slack ≥ 2&&f g (w :: a :: b :: r))))
theorem nextD_two_sorted {u:Bool} {dm y a b rest} {op:Nat} {ka kb:Bool} {s ws}
    (hop : allowedB u op = true) (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h0 : opD dm op a b ≠ 0) (hd : opD dm op a b ≠ dm) (hnm : opD dm op a b ∉ (a :: b :: rest))
    (h : RunD u dm y s (opD dm op a b :: kept ka a (kept kb b rest)))
    (f : (Nat × Nat × Nat) → List Nat → Bool) (hf : ∀ g ys,RunD u dm y s ys → f g ys = true) :
    nextD u dm (s + 2 - ws.length) ws f = true:=by
  have ha:=p.mem_iff.1 List.mem_cons_self
  have pp:=(p.trans (List.perm_cons_erase ha)).cons_inv
  have hb:=pp.mem_iff.1 List.mem_cons_self
  have pr:=(pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh:=run_len h; have hl:=p.length_eq; simp only [List.length_cons] at hl hh
  have hnc : ws.contains (opD dm op a b) = false:=by
    cases h : ws.contains (opD dm op a b) with
    | false=>rfl
    | true=>exact absurd (p.mem_iff.2 (by simpa using h)) hnm
  have h0b : (opD dm op a b != 0) = true:=bne_iff_ne.2 h0
  have hdb : (opD dm op a b != dm) = true:=bne_iff_ne.2 hd
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  apply List.any_eq_true.2 ⟨b,hb,?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨op,mem_opsOf hop,?_⟩
  simp only [h0b,hdb,hnc,Bool.not_false,Bool.true_and]
  have ht:=hf (op,a,b) _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht,Bool.true_or,Bool.or_true,Bool.and_true] <;>
    first | (simp [show 2 ≤ s + 2 - ws.length by omega]) | (simp [show 1 ≤ s + 2 - ws.length by omega])
theorem nextD_two {u:Bool} {dm y a b rest} {op:Nat} {ka kb:Bool} {s ws}
    (hop : allowedB u op = true) (p : (a :: b :: rest).Perm ws)
    (h0 : opD dm op a b ≠ 0) (hd : opD dm op a b ≠ dm) (hnm : opD dm op a b ∉ (a :: b :: rest))
    (h : RunD u dm y s (opD dm op a b :: kept ka a (kept kb b rest)))
    (f : (Nat × Nat × Nat) → List Nat → Bool) (hf : ∀ g ys,RunD u dm y s ys → f g ys = true) :
    nextD u dm (s + 2 - ws.length) ws f = true:=by
  rcases le_total a b with hab | hba
  · exact nextD_two_sorted hop hab p h0 hd hnm h f hf
  · have he : opD dm op a b = opD dm (flipOp op) b a:=opD_comm dm hop a b
    have hnm' : opD dm (flipOp op) b a ∉ (b :: a :: rest):=by
      rw [← he]; intro hm; exact hnm ((List.Perm.swap _ _ _).mem_iff.1 hm)
    apply nextD_two_sorted (op:=flipOp op) (ka:=kb) (kb:=ka) (flipOp_allowed hop) hba
      ((List.Perm.swap _ _ _).trans p) (he ▸ h0) (he ▸ hd) hnm' _ f hf
    rw [he] at h; apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]; exact List.Perm.swap _ _ _
theorem nextD_complete {u:Bool} {dm y t ws} (h : RunD u dm y t ws) :
    ∀ s,t = s + 1 → ∀ zs,ws.Perm zs → ∀ f : (Nat × Nat × Nat) → List Nat → Bool,
      (∀ g ys,RunD u dm y s ys → f g ys = true) →
      nextD u dm (s + 2 - zs.length) zs f = true:=by
  induction h using Run.fold with
  | done=>simp
  | perm p _ ih=>intro s he zs q; exact ih s he zs (p.trans q)
  | two op ka kb hop h0 hd hnm h _=>intro s he zs p f hf; cases he; exact nextD_two hop p h0 hd hnm h f hf
def span (f:Nat → Bool):Nat → Nat → Bool
  | 0,_=>true
  | n + 1,i=>f i&&span f n (i + 1)
theorem span_ok {f n o} (h : span f n o = true) : ∀ i,o ≤ i → i < o + n → f i = true:=by
  induction n generalizing o with
  | zero=>omega
  | succ n ih =>
    simp only [span,Bool.and_eq_true] at h; intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)
theorem range_split {P:Nat → Prop} {lo mid hi:Nat}
    (h1 : ∀ i,lo ≤ i → i < mid → P i) (h2 : ∀ i,mid ≤ i → i < hi → P i) :
    ∀ i,lo ≤ i → i < hi → P i:=fun i hlo hhi =>
  if h : i < mid then h1 i hlo h else h2 i (Nat.le_of_not_lt h) hhi
def fld (T w i:Nat):Nat :=
  (T >>> (w * i))&&&(if w==32 then 4294967295 else if w==52 then 4503599627370495 else if w==256 then mask256 else 2 ^ w - 1)
def bsr (read:Nat → Nat) (h:Nat):Nat → Nat → Nat → Nat
  | 0,lo,_=>lo
  | f + 1,lo,hi =>
    if lo + 1 < hi then
      (if read ((lo + hi) / 2) ≤ h then bsr read h f ((lo + hi) / 2) hi
       else bsr read h f lo ((lo + hi) / 2))
    else lo
def hw256 (seed w:Nat):Nat :=
  let x:=(((w&&&4294967295)^^^seed) * 2654435761 +
            (((w >>> 32)&&&4294967295)^^^seed) * 2246822519 +
            (((w >>> 64)&&&4294967295)^^^seed) * 3266489917 +
            (((w >>> 96)&&&4294967295)^^^seed) * 668265263 +
            (((w >>> 128)&&&4294967295)^^^seed) * 374761393 +
            (((w >>> 160)&&&4294967295)^^^seed) * 1274126177 +
            (((w >>> 192)&&&4294967295)^^^seed) * 2869860233 +
            (((w >>> 224)&&&4294967295)^^^seed) * 1640531527)&&&4294967295
  let y:=((x^^^(x >>> 16)) * 2246822519)&&&4294967295
  ((y^^^(y >>> 13)) * 3266489917)&&&4294967295
def hz (seed:Nat):List Nat → Nat
  | []=>0
  | w :: t=>hw256 seed w + hz seed t
def hk (seed:Nat) (zs:List Nat):Nat:=hz seed zs&&&4294967295
def found (S:Nat → Nat → List Nat) (N:Nat → Nat) (idx:Nat → List Nat → Nat)
    (s:Nat) (zs:List Nat):Bool :=
  decide (idx s zs < N s)&&zs.isPerm (S s (idx s zs))
def foundH (S:Nat → Nat → List Nat) (N:Nat → Nat) (htAt:Nat → Nat → Nat)
    (idxH:Nat → Nat → Nat) (s h:Nat) (zs:List Nat):Bool :=
  let i:=idxH s h
  decide (i < N s)&&(htAt s i==h)&&zs.isPerm (S s i)
def nextD_decor (u:Bool) (dm mp:Nat) (slack:Nat) (dws:List (Nat × Nat × Nat))
    (f : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool):Bool :=
  dws.any fun da =>
    let a:=da.1
    let ra:=dws.erase da
    ra.any fun db =>
      let b:=db.1
      a ≤ b&&(let r:=ra.erase db
        (opsOf u).any fun op =>
          let w:=opD dm op a b
          let g:=(op,a,b)
          w != 0&&w != dm&&!(dws.any (fun x=>x.1==w)) &&
            let dw:=(w,opP mp op da.2.1 db.2.1,opP mp op da.2.2 db.2.2)
            (f g (dw :: r)||(slack ≥ 1&&(f g (dw :: da :: r)||f g (dw :: db :: r))) ||
              (slack ≥ 2&&f g (dw :: da :: db :: r))))
theorem nextD_decor_gen (u:Bool) (dm mp:Nat) (dec:Nat → Nat × Nat × Nat)
    (hfst : ∀ w,(dec w).1 = w)
    (hop : ∀ op a b,(opD dm op a b,opP mp op (dec a).2.1 (dec b).2.1,opP mp op (dec a).2.2 (dec b).2.2) = dec (opD dm op a b))
    (slack:Nat) (ws:List Nat) (g : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool) :
    nextD_decor u dm mp slack (ws.map dec) g = nextD u dm slack ws (fun opab zs=>g opab (zs.map dec)):=by
  have hinj : Function.Injective dec:=fun x y h=>by rw [← hfst x,← hfst y,h]
  have herase : ∀ (l:List Nat) x,(l.map dec).erase (dec x) = (l.erase x).map dec :=
    fun l x=>erase_map_inj dec hinj l x
  have hcont : ∀ (l:List Nat) w,(l.map dec).any (fun x=>x.1==w) = l.contains w:=by
    intro l w; apply Bool.eq_iff_iff.2; simp [hfst]
  unfold nextD_decor nextD
  simp only [List.any_map,Function.comp_def,hfst,herase,hcont,hop,List.map_cons]
theorem nextD_decor_eq (u:Bool) {dm:Nat} (hd : dm&&&mask256 = dm)
    (pairs:List (Nat × Nat))
    (hr1 : ∀ r ∈ pairs.map Prod.fst,dm.testBit r = true)
    (hr2 : ∀ r ∈ pairs.map Prod.snd,dm.testBit r = true)
    (slack:Nat) (ws:List Nat) (g : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool) :
    let dec:=fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w)
    nextD_decor u dm (maskP pairs.length) slack (ws.map dec) g =
      nextD u dm slack ws (fun opab zs=>g opab (zs.map dec)):=by
  intro dec
  apply nextD_decor_gen
  · intro w; rfl
  · intro op a b
    simp only [dec,projBit_opD hd hr1,projBit_opD hd hr2,List.length_map]
def addC (x:Nat) (c:Nat × Nat × Nat):Nat × Nat × Nat :=
  (c.1|||x,c.2.1|||(c.1&&&x),c.2.2|||(c.2.1&&&x))
def cov3 (mp:Nat) (d:Bool) (dws:List (Nat × Nat × Nat)):Nat × Nat × Nat :=
  dws.foldl (fun c dw=>addC (colB mp d dw.2) c) (0,0,0)
def takeOne (c:Nat × Nat × Nat) (x:Nat):Nat:=(c.1^^^x)|||c.2.1
def takeTwo (c:Nat × Nat × Nat) (x y:Nat):Nat :=
  (c.1^^^(x|||y))|||(c.2.1&&&(x^^^y))|||c.2.2
theorem cov3_bit (mp:Nat) (d:Bool) (dws:List (Nat × Nat × Nat)) (i:Nat) :
    let k:=dws.countP (fun dw=>(colB mp d dw.2).testBit i)
    (cov3 mp d dws).1.testBit i = decide (1 ≤ k) ∧
    (cov3 mp d dws).2.1.testBit i = decide (2 ≤ k) ∧
    (cov3 mp d dws).2.2.testBit i = decide (3 ≤ k):=by
  have hgen : ∀ (xs:List (Nat × Nat × Nat)) (c:Nat × Nat × Nat) (k0:Nat),
      (c.1.testBit i = decide (1 ≤ k0) ∧ c.2.1.testBit i = decide (2 ≤ k0) ∧ c.2.2.testBit i = decide (3 ≤ k0)) →
      let k:=k0 + xs.countP (fun dw=>(colB mp d dw.2).testBit i)
      (xs.foldl (fun acc dw=>addC (colB mp d dw.2) acc) c).1.testBit i = decide (1 ≤ k) ∧
      (xs.foldl (fun acc dw=>addC (colB mp d dw.2) acc) c).2.1.testBit i = decide (2 ≤ k) ∧
      (xs.foldl (fun acc dw=>addC (colB mp d dw.2) acc) c).2.2.testBit i = decide (3 ≤ k):=by
    intro xs
    induction xs with
    | nil=>intro c k0 ⟨h1,h2,h3⟩; simp [h1,h2,h3]
    | cons dw xs ih =>
      intro c k0 ⟨h1,h2,h3⟩
      simp only [List.foldl_cons,List.countP_cons]
      have hc : (addC (colB mp d dw.2) c).1.testBit i =
            decide (1 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) ∧
          (addC (colB mp d dw.2) c).2.1.testBit i =
            decide (2 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) ∧
          (addC (colB mp d dw.2) c).2.2.testBit i =
            decide (3 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)):=by
        simp only [addC,Nat.testBit_or,Nat.testBit_and,h1,h2,h3]
        cases hb : (colB mp d dw.2).testBit i <;>
          rcases k0 with _ | _ | _ | k0 <;>
          simp [hb,Nat.le_add_left]
      have ih':=ih (addC (colB mp d dw.2) c) (k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) hc
      cases hb : (colB mp d dw.2).testBit i <;> simp only [hb,↓reduceIte,Bool.false_eq_true,Nat.add_zero] at ih' ⊢
      · exact ih'
      · simpa only [Nat.add_assoc,Nat.add_comm 1] using ih'
  simpa only [cov3,Nat.zero_testBit,Nat.zero_add] using hgen dws (0,0,0) 0 (by simp)
theorem cov3_perm (mp:Nat) (d:Bool) {xs ys:List (Nat × Nat × Nat)} (p : xs.Perm ys) :
    cov3 mp d xs = cov3 mp d ys:=by
  have heq : ∀ i,(cov3 mp d xs).1.testBit i = (cov3 mp d ys).1.testBit i ∧
      (cov3 mp d xs).2.1.testBit i = (cov3 mp d ys).2.1.testBit i ∧
      (cov3 mp d xs).2.2.testBit i = (cov3 mp d ys).2.2.testBit i:=by
    intro i
    obtain ⟨a1,a2,a3⟩:=cov3_bit mp d xs i
    obtain ⟨b1,b2,b3⟩:=cov3_bit mp d ys i
    rw [p.countP_eq] at a1 a2 a3
    exact ⟨a1.trans b1.symm,a2.trans b2.symm,a3.trans b3.symm⟩
  apply Prod.ext
  · exact Nat.eq_of_testBit_eq (fun i=>(heq i).1)
  · apply Prod.ext
    · exact Nat.eq_of_testBit_eq (fun i=>(heq i).2.1)
    · exact Nat.eq_of_testBit_eq (fun i=>(heq i).2.2)
theorem takeOne_eq (mp:Nat) (d:Bool) (a:Nat × Nat × Nat) (rest:List (Nat × Nat × Nat)) :
    takeOne (cov3 mp d (a :: rest)) (colB mp d a.2) = (cov3 mp d rest).1:=by
  apply Nat.eq_of_testBit_eq; intro i
  obtain ⟨h1,h2,_⟩:=cov3_bit mp d (a :: rest) i
  obtain ⟨r1,_,_⟩:=cov3_bit mp d rest i
  simp only [takeOne,Nat.testBit_or,Nat.testBit_xor,h1,h2,r1,List.countP_cons]
  set k:=rest.countP (fun dw=>(colB mp d dw.2).testBit i)
  cases ha : (colB mp d a.2).testBit i <;> simp only [ha,Bool.false_eq_true,↓reduceIte] <;>
    rcases k with _ | _ | _ | k
  · decide
  · decide
  · decide
  · simp only [show 1 ≤ k + 3 by omega,show 2 ≤ k + 3 by omega,decide_true,Bool.xor_false,Bool.or_true]
  · decide
  · decide
  · decide
  · simp only [show 1 ≤ k + 3 + 1 by omega,show 2 ≤ k + 3 + 1 by omega,show 1 ≤ k + 3 by omega,
      decide_true,Bool.xor_true,Bool.or_true,Bool.or_false]
theorem takeTwo_eq (mp:Nat) (d:Bool) (a b:Nat × Nat × Nat) (rest:List (Nat × Nat × Nat)) :
    takeTwo (cov3 mp d (a :: b :: rest)) (colB mp d a.2) (colB mp d b.2) = (cov3 mp d rest).1:=by
  apply Nat.eq_of_testBit_eq; intro i
  obtain ⟨h1,h2,h3⟩:=cov3_bit mp d (a :: b :: rest) i
  obtain ⟨r1,_,_⟩:=cov3_bit mp d rest i
  simp only [takeTwo,Nat.testBit_or,Nat.testBit_and,Nat.testBit_xor,h1,h2,h3,r1,List.countP_cons]
  set k:=rest.countP (fun dw=>(colB mp d dw.2).testBit i)
  cases ha : (colB mp d a.2).testBit i <;> cases hb : (colB mp d b.2).testBit i <;>
    simp only [ha,hb,Bool.false_eq_true,↓reduceIte] <;>
    rcases k with _ | _ | _ | k <;>
    (first | decide | simp only [
      show 1 ≤ k + 3 by omega,show 2 ≤ k + 3 by omega,show 3 ≤ k + 3 by omega,
      show 1 ≤ k + 3 + 1 by omega,show 2 ≤ k + 3 + 1 by omega,show 3 ≤ k + 3 + 1 by omega,
      show 1 ≤ k + 3 + 1 + 1 by omega,show 2 ≤ k + 3 + 1 + 1 by omega,show 3 ≤ k + 3 + 1 + 1 by omega,
      decide_true,Bool.xor_true,Bool.xor_false,Bool.or_true,Bool.or_false,Bool.and_true,Bool.and_false])
theorem cov3_coversD (u:Bool) (mp:Nat) (dw:Nat × Nat × Nat) (rest:List (Nat × Nat × Nat)) :
    ((cov3 mp (!u) rest).1|||colB mp (!u) dw.2==mp) = coversD u mp (dw :: rest):=by
  have e : ((cov3 mp (!u) rest).1|||colB mp (!u) dw.2) =
      (dw :: rest).foldl (fun acc x=>acc|||colB mp (!u) x.2) 0:=by
    apply Nat.eq_of_testBit_eq; intro i
    obtain ⟨h1,_,_⟩:=cov3_bit mp (!u) rest i
    rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,Nat.testBit_or,h1,List.any_cons]
    have hp : decide (1 ≤ rest.countP (fun dw=>(colB mp (!u) dw.2).testBit i)) =
        rest.any (fun x=>(colB mp (!u) x.2).testBit i):=by
      rw [Bool.eq_iff_iff,decide_eq_true_eq,Nat.succ_le_iff,List.countP_pos_iff,List.any_eq_true]
    rw [hp,Bool.or_comm]
  unfold coversD; exact congrArg (·==mp) e
def nextD_cov (u:Bool) (dm mp slack:Nat) (dws:List (Nat × Nat × Nat))
    (f : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool):Bool :=
  let ori:=!u
  let cov:=cov3 mp ori dws
  dws.any fun da =>
    let a:=da.1
    let ca:=colB mp ori da.2
    let ra:=dws.erase da
    ra.any fun db =>
      let b:=db.1
      a ≤ b &&
        (let cb:=colB mp ori db.2
         let base0:=takeTwo cov ca cb
         let base1a:=takeOne cov cb
         let base1b:=takeOne cov ca
         let r:=ra.erase db
         (opsOf u).any fun op =>
           let pz:=(opP mp op da.2.1 db.2.1,opP mp op da.2.2 db.2.2)
           let cz:=colB mp ori pz
           let ok0:=(base0|||cz)==mp
           let ok1a:=slack ≥ 1&&((base1a|||cz)==mp)
           let ok1b:=slack ≥ 1&&((base1b|||cz)==mp)
           let ok2:=slack ≥ 2&&((cov.1|||cz)==mp)
           (ok0||ok1a||ok1b||ok2) &&
           (let w:=opD dm op a b
            let g:=(op,a,b)
            w != 0&&w != dm&&!(dws.any (fun x=>x.1==w)) &&
              let dw:=(w,pz)
              ((ok0&&f g (dw :: r))||(ok1a&&f g (dw :: da :: r)) ||
               (ok1b&&f g (dw :: db :: r))||(ok2&&f g (dw :: da :: db :: r)))))
theorem nextD_cov_eq (u:Bool) (dm mp slack:Nat) (dws:List (Nat × Nat × Nat))
    (g : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool) :
    nextD_cov u dm mp slack dws g =
      nextD_decor u dm mp slack dws (fun opab dzs=>coversD u mp dzs&&g opab dzs):=by
  unfold nextD_cov nextD_decor
  dsimp only
  apply Bool.eq_iff_iff.2; simp only [List.any_eq_true,Bool.or_eq_true,Bool.and_eq_true]
  constructor
  · rintro ⟨da,hda,db,hdb,hab,op,hop,_,⟨⟨hw0,hwdm⟩,hnw⟩,hfx⟩
    refine ⟨da,hda,db,hdb,hab,op,hop,⟨⟨hw0,hwdm⟩,hnw⟩,?_⟩
    set pz:=(opP mp op da.2.1 db.2.1,opP mp op da.2.2 db.2.2)
    set dw:=(opD dm op da.1 db.1,pz)
    set ra:=dws.erase da
    set r:=ra.erase db
    have hp : dws.Perm (da :: db :: r):=(List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
    have hc2:=cov3_perm mp (!u) hp
    have hca:=cov3_perm mp (!u) (hp.trans (List.Perm.swap _ _ _))
    have hcov0 : (takeTwo (cov3 mp (!u) dws) (colB mp (!u) da.2) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: r):=by rw [hc2,takeTwo_eq]; exact cov3_coversD u mp dw r
    have hcov1a : (takeOne (cov3 mp (!u) dws) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: da :: r):=by rw [hca,takeOne_eq]; exact cov3_coversD u mp dw (da :: r)
    have hcov1b : (takeOne (cov3 mp (!u) dws) (colB mp (!u) da.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: db :: r):=by rw [hc2,takeOne_eq]; exact cov3_coversD u mp dw (db :: r)
    have hcov2 : ((cov3 mp (!u) dws).1|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: da :: db :: r):=by rw [hc2]; exact cov3_coversD u mp dw (da :: db :: r)
    rcases hfx with ((⟨hu0,hf0⟩ | ⟨⟨hsl1,hu1a⟩,hf1a⟩) | ⟨⟨hsl1,hu1b⟩,hf1b⟩) | ⟨⟨hsl2,hu2⟩,hf2⟩
    · left; left; exact ⟨hcov0 ▸ hu0,hf0⟩
    · left; right; exact ⟨hsl1,Or.inl ⟨hcov1a ▸ hu1a,hf1a⟩⟩
    · left; right; exact ⟨hsl1,Or.inr ⟨hcov1b ▸ hu1b,hf1b⟩⟩
    · right; exact ⟨hsl2,hcov2 ▸ hu2,hf2⟩
  · rintro ⟨da,hda,db,hdb,hab,op,hop,⟨⟨hw0,hwdm⟩,hnw⟩,hfx⟩
    refine ⟨da,hda,db,hdb,hab,op,hop,?_⟩
    set pz:=(opP mp op da.2.1 db.2.1,opP mp op da.2.2 db.2.2)
    set dw:=(opD dm op da.1 db.1,pz)
    set ra:=dws.erase da
    set r:=ra.erase db
    have hp : dws.Perm (da :: db :: r):=(List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
    have hc2:=cov3_perm mp (!u) hp
    have hca:=cov3_perm mp (!u) (hp.trans (List.Perm.swap _ _ _))
    have hcov0 : (takeTwo (cov3 mp (!u) dws) (colB mp (!u) da.2) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: r):=by rw [hc2,takeTwo_eq]; exact cov3_coversD u mp dw r
    have hcov1a : (takeOne (cov3 mp (!u) dws) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: da :: r):=by rw [hca,takeOne_eq]; exact cov3_coversD u mp dw (da :: r)
    have hcov1b : (takeOne (cov3 mp (!u) dws) (colB mp (!u) da.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: db :: r):=by rw [hc2,takeOne_eq]; exact cov3_coversD u mp dw (db :: r)
    have hcov2 : ((cov3 mp (!u) dws).1|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: da :: db :: r):=by rw [hc2]; exact cov3_coversD u mp dw (da :: db :: r)
    rcases hfx with (⟨hc0,hg0⟩ | ⟨hsl1,⟨hc1a,hg1a⟩ | ⟨hc1b,hg1b⟩⟩) | ⟨hsl2,hc2',hg2⟩
    · have u0 : (takeTwo (cov3 mp (!u) dws) (colB mp (!u) da.2) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) = true:=hcov0.symm ▸ hc0
      exact ⟨Or.inl (Or.inl (Or.inl u0)),⟨⟨hw0,hwdm⟩,hnw⟩,Or.inl (Or.inl (Or.inl ⟨u0,hg0⟩))⟩
    · have u1a : (takeOne (cov3 mp (!u) dws) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) = true:=hcov1a.symm ▸ hc1a
      exact ⟨Or.inl (Or.inl (Or.inr ⟨hsl1,u1a⟩)),⟨⟨hw0,hwdm⟩,hnw⟩,Or.inl (Or.inl (Or.inr ⟨⟨hsl1,u1a⟩,hg1a⟩))⟩
    · have u1b : (takeOne (cov3 mp (!u) dws) (colB mp (!u) da.2)|||colB mp (!u) pz==mp) = true:=hcov1b.symm ▸ hc1b
      exact ⟨Or.inl (Or.inr ⟨hsl1,u1b⟩),⟨⟨hw0,hwdm⟩,hnw⟩,Or.inl (Or.inr ⟨⟨hsl1,u1b⟩,hg1b⟩)⟩
    · have u2 : ((cov3 mp (!u) dws).1|||colB mp (!u) pz==mp) = true:=hcov2.symm ▸ hc2'
      exact ⟨Or.inr ⟨hsl2,u2⟩,⟨⟨hw0,hwdm⟩,hnw⟩,Or.inr ⟨⟨hsl2,u2⟩,hg2⟩⟩
def bar (u:Bool) (dm Y:Nat) (mp:Nat)
    (SD:Nat → Nat → List (Nat × Nat × Nat)) (S:Nat → Nat → List Nat)
    (N:Nat → Nat) (htAt idxH:Nat → Nat → Nat)
    (ori:List Nat → List Nat) (seed:Nat) (pool:List Nat)
    (mkCut:Nat → Nat → (Nat × Nat × Nat) → List Nat → Bool):Nat → Nat → Bool
  | 0,i=>!(S 0 i==[Y])
  | s + 1,i =>
    let dws:=SD (s + 1) i
    !(nextD_cov u dm mp (s + 2 - dws.length) dws fun g dzs =>
        let zs:=dzs.map Prod.fst
        !(scr u dm Y s pool zs)&&!(mkCut (s + 1) i g zs) &&
        (let cz:=ori zs
         let h:=hk seed cz
         !(foundH S N htAt idxH s h cz)))
def barP (u:Bool) (dm Y:Nat) (mp:Nat)
    (SD:Nat → Nat → List (Nat × Nat × Nat)) (S:Nat → Nat → List Nat)
    (N:Nat → Nat) (htAt idxH:Nat → Nat → Nat)
    (ori:List Nat → List Nat) (seed:Nat) (pool:List Nat)
    (mkPools:Nat → Nat → List (Nat × Nat × (Nat × List Nat))):Nat → Nat → Bool
  | 0,i=>!(S 0 i==[Y])
  | s + 1,i =>
    let dws:=SD (s + 1) i
    match mkPools (s + 1) i with
    | [] =>
      !(nextD_cov u dm mp (s + 2 - dws.length) dws fun _ dzs =>
          let zs:=dzs.map Prod.fst
          !(scr u dm Y s pool zs) &&
          (let cz:=ori zs; let h:=hk seed cz; !(foundH S N htAt idxH s h cz)))
    | p :: ps =>
      !(nextD_cov u dm mp (s + 2 - dws.length) dws fun g dzs =>
          let zs:=dzs.map Prod.fst
          !(scr u dm Y s pool zs) &&
          !((p :: ps).any fun e=>checkPool u e.1 e.2.1 s (stepOp u e.1 e.2.2 g) zs) &&
          (let cz:=ori zs; let h:=hk seed cz; !(foundH S N htAt idxH s h cz)))
theorem lower_of_search {u:Bool} {d T L:Nat} {roots:List Nat} {pairs:List (Nat × Nat)}
    (hinit : (d&&&mask256==d)&&d.testBit 0&&!(T.testBit 0)&&roots.all (fun r=>!r.testBit 0) &&
             !(isConstB d T)&&(roots.map (·&&&d)).Nodup &&
             pairs.all (fun p=>d.testBit p.1&&d.testBit p.2&&!(T&&&d).testBit p.1&&(T&&&d).testBit p.2) = true)
    (hpf : ∀ zs ∈ (roots.map (·&&&d)).sublists,zs ≠ roots.map (·&&&d) → unorientedCov pairs zs = false)
    (hno : ∀ s ≤ L - 1,RunD u d (T&&&d) s (roots.map (·&&&d)) → False) :
    Lower u d roots T L:=by
  simp only [Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at hinit
  obtain ⟨⟨⟨⟨⟨⟨hd,hd0⟩,hT0⟩,hR0⟩,hncb⟩,hnd_xs⟩,hpairs⟩:=hinit
  have hnd_xs' : (roots.map (·&&&d)).Nodup:=by simpa using hnd_xs
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst d T:=fun h=>by rw [(isConstB_iff _ _).2 h] at hncb; contradiction
  obtain ⟨s,ws,hs_le,hnd,hws_sub,hrun⟩:=reach_to_run hd hd0 hT0 hR0 hnc hr ha
  have hperm_sub : ∃ zs,zs.Sublist (roots.map (·&&&d)) ∧ ws.Perm zs:=by
    refine ⟨(roots.map (·&&&d)).filter (fun x=>decide (x ∈ ws)),List.filter_sublist,?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ hnd_xs')).2 ?_
    intro x; simp only [List.mem_filter,decide_eq_true_eq]
    exact ⟨fun hx=>⟨hws_sub x hx,hx⟩,fun h=>h.2⟩
  obtain ⟨zs,hsub,hpz⟩:=hperm_sub
  have hrun':=Run.perm hpz hrun
  by_cases heq : zs = roots.map (·&&&d)
  · subst heq; exact hno s (by omega) hrun'
  · have hcov:=unorientedCov_ok hd pairs hpairs hrun'
    rw [hpf zs (List.mem_sublists.2 hsub) heq] at hcov; contradiction
theorem barP_eq (u:Bool) (dm Y mp:Nat) (SD S N htAt idxH ori seed pool mkPools s i) :
    barP u dm Y mp SD S N htAt idxH ori seed pool mkPools s i =
      bar u dm Y mp SD S N htAt idxH ori seed pool
        (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool u e.1 e.2.1 (s' - 1) (stepOp u e.1 e.2.2 g) zs) s i:=by
  cases s with
  | zero=>rfl
  | succ s =>
    unfold barP bar; dsimp only
    cases mkPools (s + 1) i with
    | nil=>simp
    | cons p ps=>rfl
theorem bar_all {u:Bool} {dm T:Nat} {pairs:List (Nat × Nat)} {r1s r2s mp SD S N htAt idxH ori seed pool mkCut cap}
    (hd : dm&&&mask256 = dm)
    (hr1_eq : r1s = pairs.map Prod.fst) (hr2_eq : r2s = pairs.map Prod.snd) (hmp_eq : mp = maskP pairs.length)
    (hSD : ∀ s j,SD s j = (S s j).map (fun w=>(w,projBit r1s w,projBit r2s w)))
    (hpairs : pairs.all (fun p=>dm.testBit p.1&&dm.testBit p.2&&!(T&&&dm).testBit p.1&&(T&&&dm).testBit p.2) = true)
    (hr : ∀ {v ys},RunD u dm (T&&&dm) v ys → RunD u dm (T&&&dm) v (ori ys))
    (hcut : ∀ {s i g ys},mkCut (s + 1) i g ys = true → ¬ RunD u dm (T&&&dm) s ys)
    (hc : ∀ s ≤ cap,∀ i < N s,bar u dm (T&&&dm) mp SD S N htAt idxH ori seed pool mkCut s i = true) :
    ∀ s ≤ cap,∀ i < N s,¬ RunD u dm (T&&&dm) s (S s i):=by
  subst hr1_eq hr2_eq hmp_eq
  have hr1 : ∀ r ∈ pairs.map Prod.fst,dm.testBit r = true:=by
    intro r hr'; obtain ⟨p,hp,rfl⟩:=List.mem_map.1 hr'
    have h:=List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.1
  have hr2 : ∀ r ∈ pairs.map Prod.snd,dm.testBit r = true:=by
    intro r hr'; obtain ⟨p,hp,rfl⟩:=List.mem_map.1 hr'
    have h:=List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.2
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    have hb:=hc s hs i hi
    cases s with
    | zero=>simp [bar,zero_done hh rfl] at hb
    | succ s =>
      by_contra! hn
      let F (g:Nat × Nat × Nat) (zs:List Nat) :=
        coversP u pairs zs&&!(scr u dm (T&&&dm) s pool zs)&&!(mkCut (s + 1) i g zs) &&
        (let cz:=ori zs
         let h:=hk seed cz
         !(foundH S N htAt idxH s h cz))
      have hF (g zs) (hz : RunD u dm (T&&&dm) s zs) : F g zs = true:=by
        have hcz:=hr hz
        have hcutf : mkCut (s + 1) i g zs = false:=by
          cases h : mkCut (s + 1) i g zs with
          | false=>rfl
          | true=>exact absurd hz (hcut h)
        simp only [F,coversP_ok hd pairs hpairs hz,scr_no pool hz,hcutf,Bool.not_false,Bool.true_and,foundH]
        simp only [Bool.not_eq_true',Bool.and_eq_false_imp,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
        rintro ⟨hj,_⟩
        by_contra! hp
        have p:=List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact ih s (by omega) (by omega) _ hj (Run.perm p hcz)
      have hN:=nextD_complete hh s rfl _ (List.Perm.refl _) F hF
      dsimp only [bar] at hb
      rw [hSD,List.length_map,nextD_cov_eq,nextD_decor_eq u hd pairs hr1 hr2] at hb
      have hFeq : (fun g zs=>coversD u (maskP pairs.length) (zs.map (fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w))) &&
          (let zs':=(zs.map (fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w))).map Prod.fst
           !(scr u dm (T&&&dm) s pool zs')&&!(mkCut (s + 1) i g zs') &&
           (let cz:=ori zs'
            let h:=hk seed cz
            !(foundH S N htAt idxH s h cz)))) = F:=by
        funext g zs
        have hfst : (zs.map (fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w))).map Prod.fst = zs:=by
          simp [List.map_map,Function.comp_def]
        rw [coversD_eq,hfst]
        simp only [F,Bool.and_assoc]
      rw [hFeq,hN] at hb
      contradiction
def pickMin (seed:Nat) (orig:List Nat):List (List (Nat × Nat)) → List Nat → Nat → List Nat
  | [],best,_=>best
  | ms :: rest,best,bestH =>
    let img:=orig.map (applyMoves ms)
    let h:=hk seed img
    if h < bestH then pickMin seed orig rest img h else pickMin seed orig rest best bestH
theorem pickMin_runD {u:Bool} {dm Y v} (seed:Nat) (orig:List Nat) (h0 : RunD u dm Y v orig) :
    ∀ (syms:List (List (Nat × Nat))) (best:List Nat) (bestH:Nat),
      syms.all (fun ms=>ms.all moveOK256&&(applyMoves ms dm==dm)&&(applyMoves ms Y==Y)) = true →
      RunD u dm Y v best →
      RunD u dm Y v (pickMin seed orig syms best bestH)
  | [],_,_,_,hb=>hb
  | ms :: rest,best,bestH,hok,hb=>by
    simp only [List.all_cons,Bool.and_eq_true,beq_iff_eq] at hok
    unfold pickMin; dsimp only; split
    · exact pickMin_runD seed orig h0 rest _ _ hok.2 (applyMoves_runD ms hok.1.1.1 hok.1.1.2 hok.1.2 h0)
    · exact pickMin_runD seed orig h0 rest best bestH hok.2 hb
def xs256:List Nat :=
  [(OfNat.ofNat largeWord0),
   (OfNat.ofNat largeWord1),
   (OfNat.ofNat largeWord2),
   (OfNat.ofNat largeWord3),
   (OfNat.ofNat largeWord4),
   (OfNat.ofNat largeWord5),
   (OfNat.ofNat largeWord6),
   (OfNat.ofNat largeWord7)]
def sampled (points : Nat → X) (d : Nat) (f : F) (w : Nat) : Prop :=
  ∀ i, d.testBit i = true → w.testBit i = f (points i)

theorem sample_congr {points d f v w} (a : sampled points d f v) (b : sampled points d f w) :
    v &&& d = w &&& d := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases h : d.testBit i
  · simp [Nat.testBit_and, h]
  · simp [Nat.testBit_and, h, a i h, b i h]

theorem sample_neg {points d f w} (hd : d &&& mask256 = d) (a : sampled points d f w) :
    sampled points d (fun x => !f x) (negD d w) := by
  intro i hi
  have e := congrArg (fun v : Nat => v.testBit i) hd
  have hm : mask256.testBit i = true := by simpa [Nat.testBit_and, hi] using e
  simp [negD, Nat.testBit_and, Nat.testBit_xor, hi, hm, a i hi]

theorem sample_gate {points d a b wa wb} (tag : Bool)
    (ha : sampled points d a wa) (hb : sampled points d b wb) :
    sampled points d (PEqualNP.Outside.L_meta_45356_aux.comb tag a b) (opD d (if tag then 0 else 1) wa wb) := by
  intro i hi
  cases tag <;> simp [PEqualNP.Outside.L_meta_45356_aux.comb, opD, andD, orD, Nat.testBit_and, Nat.testBit_or, hi, ha i hi, hb i hi]

theorem sample_available {points d bank s f}
    (hd : d &&& mask256 = d)
    (hs : ∀ u ∈ s, ∃ w, Avail true d bank w ∧ sampled points d u w)
    (h : PEqualNP.Outside.L_meta_45356_aux.Av s f) :
    ∃ w, Avail true d bank w ∧ sampled points d f w := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · cases b
    · exact ⟨0, Or.inl (Or.inl (by simp)), fun i _ => by simp⟩
    · exact ⟨d, Or.inl (Or.inr (by simp)), fun _ hi => hi⟩
  · exact hs _ hu
  · obtain ⟨w, hw, hrep⟩ := hs _ hu
    exact ⟨negD d w, avail_neg hd hw, sample_neg hd hrep⟩

theorem sample_program (points : Nat → X) (d : Nat) (hd : d &&& mask256 = d)
    (roots : List Nat) {s : Set F} {f : F} {k : Nat} (prog : PEqualNP.Outside.L_meta_45356_aux.Prog s f k) :
    ∀ {spent bank}, NatReach true d roots spent bank →
    (∀ u ∈ s, ∃ w, Avail true d bank w ∧ sampled points d u w) →
    ∃ result w, NatReach true d roots (spent + k) result ∧ Avail true d result w ∧ sampled points d f w := by
  induction prog with
  | done h =>
    intro spent bank run hs
    obtain ⟨w, hw, hr⟩ := sample_available hd hs h
    exact ⟨bank, w, run, hw, hr⟩
  | @gate s f a b k tag ha hb tail ih =>
    intro spent bank run hs
    obtain ⟨wa, haa, har⟩ := sample_available hd hs ha
    obtain ⟨wb, hba, hbr⟩ := sample_available hd hs hb
    let op : Nat := if tag then 0 else 1
    let z := opD d op wa wb
    have ok : allowedB true op = true := by cases tag <;> decide
    have next : NatReach true d roots (spent + 1) (z :: bank) :=
      ⟨bank, wa, wb, op, ok, rfl, run, haa, hba⟩
    obtain ⟨result, w, reach, hit, rep⟩ := ih next (by
      intro u hu
      rcases Set.mem_insert_iff.mp hu with rfl | hu
      · exact ⟨z, Or.inr (Or.inl ⟨z, List.mem_cons_self, rfl⟩), sample_gate tag har hbr⟩
      · obtain ⟨v, hv, hl⟩ := hs _ hu
        exact ⟨v, avail_cons _ _ hv, hl⟩)
    exact ⟨result, w, by simpa only [Nat.add_assoc, Nat.add_comm 1 k] using reach, hit, rep⟩

namespace Certificate0

def packCertificateWords (ws : List Nat) : Nat := ws.foldl (fun n w => (n <<< 64) + w) 0

def largeWord0 : Nat := packCertificateWords [0xa35f290e, 0x9908a63a7316d6a0, 0x587818bd564b80b0, 0x4536224829c5ac2a, 0x29a4607124088376, 0x216373de0100fcd0]

def largeWord1 : Nat := packCertificateWords [0x54fde8fc4b5405dd, 0x2e5ade2929c5ac2a, 0x26366b081f979d7b, 0x18e398641767c918]

def largeWord2 : Nat := packCertificateWords [0xf0000c0000000c00, 0xf000c000f000ca, 0xa00000000f000, 0xf000a00003000300, 0xc0, 0xce000e000e000e, 0x8000800080008f00, 0xf000f0000f00000, 0xe0000000e, 0xc000f000c000, 0xcc0000000f000040, 0x40004000420002, 0x20002c000c000, 0xc000c00000000e00, 0xe40004000c000cf, 0xf000000006000, 0x600060006f000000, 0xf0000a000a000a0, 0xa30003000c000c]

def largeWord3 : Nat := packCertificateWords [0x411c, 0x2411c37208f60905, 0x384823849511c24, 0x11c29208e1a10470, 0xa262384419448283, 0xdcd3848c38482584, 0x8238487504824a04, 0x7098820948218820]

def largeWord4 : Nat := packCertificateWords [0xb9152264448790, 0xd216424839052064]

def largeWord5 : Nat := packCertificateWords [0xa8b3d6, 0x52c6482af15bab25]

def largeWord6 : Nat := packCertificateWords [0xffff0000, 0xffff0000, 0xffff0000, 0xffff0000]

def largeWord7 : Nat := packCertificateWords [0xcccc0000cccc, 0xcccc0000cccc, 0xcccc0000cccc, 0xcccc0000cccc]

def largeWord8 : Nat := packCertificateWords [0xcccccccc, 0xcccccccc, 0xcccccccc, 0xcccccccc]

def largeWord9 : Nat := packCertificateWords [0x1, 0x4140000000280000, 0x28040400000404]

def largeWord10 : Nat := packCertificateWords [0xff00ff00, 0xff00ff00, 0xff00ff00, 0xff00ff00]

def largeWord11 : Nat := packCertificateWords [0xcc00cc00cc00cc, 0xcc00cc00cc00cc, 0xcc00cc00cc00cc, 0xcc00cc00cc00cc]

def largeWord12 : Nat := packCertificateWords [0x2222222222222222, 0x2222222222222222, 0x2222222222222222, 0x2222222222222222]

def largeWord13 : Nat := packCertificateWords [0xf0f00000f0f0, 0xf0f00000f0f0, 0xf0f00000f0f0, 0xf0f00000f0f0]

def largeWord14 : Nat := packCertificateWords [0xaa00aa00aa00aa, 0xaa00aa00aa00aa, 0xaa00aa00aa00aa, 0xaa00aa00aa00aa]

def largeWord15 : Nat := packCertificateWords [0xf000f000f000f0, 0xf000f000f000f0, 0xf000f000f000f0, 0xf000f000f000f0]

def largeWord16 : Nat := packCertificateWords [0xff000000ff00, 0xff000000ff00, 0xff000000ff00, 0xff000000ff00]

def largeWord17 : Nat := packCertificateWords [0xf0f0f0f0, 0xf0f0f0f0, 0xf0f0f0f0, 0xf0f0f0f0]

def largeWord18 : Nat := packCertificateWords [0xa0a0a0a0a0a0a0a, 0xa0a0a0a0a0a0a0a, 0xa0a0a0a0a0a0a0a, 0xa0a0a0a0a0a0a0a]

def largeWord19 : Nat := packCertificateWords [0xc0c0c0c0c0c0c0c, 0xc0c0c0c0c0c0c0c, 0xc0c0c0c0c0c0c0c, 0xc0c0c0c0c0c0c0c]

def largeWord20 : Nat := packCertificateWords [0xf88bcab5, 0xf1d796ba739645eb, 0x65370def1f724d16]

def largeWord21 : Nat := packCertificateWords [0xecd3ba2ceca0bfa4, 0xdddd59cccb927da3, 0xc1d6afedbaa8a906, 0xb404f765b317cb6c, 0xaacaf859a6122054, 0xa3ca27209a7a6a89, 0x99819ab0936eb8fb, 0x92afa6188a6f7d02, 0x7cb926ba7a89da3b, 0x73b05f9c6bedb233, 0x6b0a02b169311663, 0x67363b7765a3f7e2, 0x59d2fcbf459c07cf, 0x4546c3fa44c5b18d, 0x40a8ee9440125717, 0x3efd9b1e3783b819, 0x2de2010e2d81f8cc, 0x2d4f7a062cfd287d, 0x1f7d988f1ef18b50, 0x1c1fc6611661f45f, 0x135a1e9013085cd7, 0x124b987d1167c1ff, 0x114d3acc112b7718, 0x959af8503419f62, 0x25f20b90227a138]

def largeWord22 : Nat := packCertificateWords [0x716ee0677155158a, 0x7096b87d6e798886, 0x6dc5501869b3c8f1, 0x67e347646768fa6d, 0x671b41186668d9ed, 0x661c077f65441249, 0x64665047644c01d3, 0x63afa33f623c5ba4, 0x61db797a5f288d8d, 0x5d24b87a5d0bdb86, 0x5c842bde5c6343d7, 0x5b9dea1f5a17e938, 0x57946fe255307145, 0x5453de0e536d2afe, 0x5326aae25242b2d0, 0x52370bb751df884f, 0x4f7ff5cc4d376ce9, 0x4d25e0dd4ccbff88, 0x4c86e70e4c03fcd6, 0x4b0b7bf14af6fe64, 0x4a308ab4497c32c3, 0x47a4ad8a44768316, 0x43ff525643ce0185, 0x42c29cc3424f6b88, 0x4202c728416528e6, 0x412eb1603fc97be9, 0x3cd804cc3c26c8d6, 0x3bd43d603a626511, 0x38e7f2e238bcfe3d, 0x3872e0b636cf7fd0, 0x34d2a9ed33d18282, 0x32c96c623243572e, 0x3210f99c2f2577ae, 0x2eb472a22cb8b852, 0x2c0092932bc9d21d, 0x2b23eeec2a722300, 0x27b3fb732795edac, 0x25c46cb125c09a4e, 0x256f93ee25264393, 0x24f3212e24c201da, 0x238a57762340a6b3, 0x20f4685420a70f1e, 0x207bef03207bde1c, 0x1ea7c97e1dfdbcdc, 0x1dc0e0b01cd2e113, 0x1b1331711af21fc6, 0x1aa682401a4f1e32, 0x19b1e3ce1951fa5a, 0x192848ce1788b8f9, 0x162cda8b15494a2b, 0x153acf1714863b6a, 0x13f31e3d13d06be4, 0x13af4cab13a40f83, 0x13720c0212ce17cb, 0x1139f5361133a3cc, 0x1100129910262ea0, 0xee49f660d6a83cc, 0xcdf2f2e0c7d5456, 0xb17f9e80a930f44, 0x9fde6980853c553, 0x71e52fb05f36344, 0x548f31e01766cb4, 0x1745acf01528bc9, 0x11ed795000fbc49]

def largeWord23 : Nat := packCertificateWords [0xfcb34b42f94e4bbf, 0xf8844fc8f8057f4c, 0xf7d0412bf1af9878, 0xf13280daf103f879, 0xf0cdc2a0ee7b703c, 0xecd3ba2cebec9947, 0xeb26da25e95cf97c, 0xe74f14dae698529d, 0xe196ca21df65625a, 0xdbabc5a1d896650f, 0xd631a64ad21be976, 0xd0602502cf6d76b3, 0xcedb659bce230cf2, 0xcae86773c991470d, 0xc97898b5c833077b, 0xc7d8277ec48fc107, 0xc3e4598fc1eb1ff9, 0xbf5732d5bb7fea6e, 0xb993e758b9531318, 0xb7fc6408b733f83d, 0xb6960700b68e03c2, 0xb5b1a835b09b6ee3, 0xaf078363abc3ee75, 0xaba68d29aa0c28c8, 0xa8734b95a43e7c5a, 0xa26b8d199f7f1e1e, 0x9ebd2eeb9d2df7a2, 0x9b81245298061833, 0x952e5fac944f7586, 0x930071ea92c77812, 0x924cdeb79245d4b7, 0x916a2e698febd864, 0x8f2b93488d30b93e, 0x8c4efa538a3473a1, 0x88d46013889f7fd6, 0x85be787685108395, 0x8478e042830cc445, 0x81e5c3ea8061855d, 0x7f10ad477efce6d7, 0x7e4c69b17e0e1c90, 0x7cae83ef79d9ff34, 0x788c2e7476bdb548]

def largeWord24 : Nat := packCertificateWords [0x346456b83420cbf6, 0x33d56105334c5dcd, 0x32e3cd7832915817, 0x3253456c32507548, 0x318fd84e3048cfa2, 0x2da7c1af2d6dc12e, 0x2d19d73a2cdc473c, 0x2c3f0cd82afb782e, 0x2af926a1298579be, 0x2952666e28b8eb48, 0x273e51d0271b4896, 0x26ddb89826c0978c, 0x26a89d02266d6b0f, 0x25919a8025911e77, 0x257b6f2a25038861, 0x24d09179248c042c, 0x2475d9f723fa8917, 0x23aed07e22e9210c, 0x22afdb28229c95fc, 0x2271dc8622691b63, 0x22172930219cf3ae, 0x219bf63e21713cf2, 0x20d976f920b10be2, 0x2095f7cd20956898, 0x1fc81ea61f1b3c56, 0x1ea2845f1e7cf6c3, 0x1e7b2b601e463aae, 0x1c937f9e1c289a1c, 0x1c240a571b5ed537, 0x1b34b1c01a316961, 0x19ddf34919a5e647, 0x192327d018ba295f, 0x18460d05175df24d, 0x16a3a4ae15d7d72f, 0x1589cdba1512a956, 0x14daaf6d1498f53b, 0x14302c0013ee1b6c, 0x13cabe6513c66112, 0x1358686112fe5c9f, 0x12f972ef12e6df4a, 0x125836041251c2ff, 0x11ee96fc11d48a66, 0x119c1cdc1139f536, 0x1127d1d2104735d3, 0x1022b21e0fb1fe78, 0xfa3ff2a0efa52cf, 0xee30fa10ebbc847, 0xd261f890cd96ed2, 0xc8545670c21dbf3, 0xbe1c94d0b70bf66, 0xb43b9f30aad28f5, 0xa9e75d50a53ab1a, 0xa02db080964b6d7, 0x963a25b09530b86, 0x94859a6090ac9a8, 0x8f01f90085cf66e, 0x7ee3e9307b681be, 0x79ae9f0076d4567, 0x763b48b0721632f, 0x68f0e0c06184877, 0x533099e0518e009, 0x4e3c95f014cd4d7, 0x12492b400f50720, 0x8e16b0004bd32f]

def largeWord25 : Nat := packCertificateWords [0x743ab308742b5d22, 0x7295703a72391913, 0x71fcb6ee704b57ba, 0x70187c1c6dfc4d30, 0x6deec9496d9b601c, 0x6d5d4a9d6d25dd9b, 0x6ce102b26c86863f, 0x6c388c356b4e2e59, 0x6ac225ec6a4dea6d, 0x699c178468b32052, 0x677d624e6698ef28, 0x65d2954065758648, 0x655f307664356fdf, 0x64030bcb63d1d804, 0x637d858d6350121c, 0x62f9aef761b2a37f, 0x60e5306960b0bfb9, 0x608f4c406076a95b, 0x601bc7b65fab894d, 0x5f15af545ee0d3b9, 0x5e7367355e5add38, 0x5e4140d95d91986e, 0x5c43e99d5acb3334, 0x5a6a7453587a071b, 0x56ea332556e1a3af, 0x56599c9d55e33072, 0x55cbe2b4553b0f00, 0x5529af8e54a5b2c6, 0x54439a93542e23a1, 0x531052e152e72ce3, 0x52abf21d51739032, 0x5132b3be512e441a, 0x512da257511544f2, 0x50f3509f50d43d77, 0x50c18218503af769, 0x4fffc6dd4fa8a1d7, 0x4f7ff5cc4f17765d, 0x4e7fd8434dd315c5, 0x4d80a9bb4d6c9e20, 0x4ca19c624c8f461e, 0x4c17d9284c0c16b4, 0x4b4ef5cf4b0862a7, 0x4a1494c54a097fe5, 0x4a0275e549f111df, 0x48078cf347f6ceff, 0x47cc50c346d37d7d, 0x46b727ec464205ba, 0x4605c573451aa2c1, 0x43989aa143879ebe, 0x4325707a42c03b42, 0x4201c361405fd1c2, 0x40359fa23f9a1721, 0x3f3dc53c3f35156d, 0x3f220d953ed37e61, 0x3e9cac873cdc8865, 0x3cb982853c9ff65a, 0x3c789c573c618acb, 0x3b7b395d3ab0557a, 0x3a06439239fff9a1, 0x38be8a43378a706b, 0x3773fc14374f2ae4, 0x36a611a0366f7fb9, 0x360b018935ffb1fc, 0x35eedc71348d3ddf]

def largeWord26 : Nat := packCertificateWords [0xffbd6cda, 0xfe9154bbfbb2c816, 0xf20c7b2bf0cdc2a0, 0xea003b16e82da1c3, 0xe816cfbae469504a, 0xe015b690df43e71a, 0xde83b2f0dc649f3d, 0xdc444255d7952373, 0xd75d6e16d5d31b7b, 0xd35ddeeed153b31b, 0xce808172ce73fb80, 0xcd865458cc095396, 0xcb7cb389c9af7278, 0xc8ec4700c84e57c9, 0xc55be272c36aa6c4, 0xc2436907bfd350d4, 0xbf862093bf413fcc, 0xbde8d04fbb55384c, 0xb993e758b92f8601, 0xb67046f2b4ce5c24, 0xb456c7dcb34d92ff, 0xb2ea1914b1c30d46, 0xb0f6501aafbb20ac, 0xae5009a5ae336223, 0xadffad69ad4b7bd1, 0xac4647dbab88336b, 0xaa8edb56aa75bd38, 0xa9a3edb4a865a70b, 0xa5b66b45a488ea04, 0xa47e61c9a420e469, 0xa40305d5a3e77a52, 0xa3176e09a170586e, 0xa060b677a05678de, 0xa022b60aa004e9df, 0x9e001ea99d2df7a2, 0x9c0020a79b8768c7, 0x9b43879d9ab2e189, 0x99e844ba9976a97a, 0x98d4a79b973ca9d7, 0x96e0f4a1968f64de, 0x964cc94d96026e0f, 0x9586e7439296e0c9, 0x9137b8fd90a8ace1, 0x8fdcac138ca4a9c9, 0x8b0b9d198b07f87c, 0x89f74d3089921da8, 0x885d643b87855b3b, 0x86c5d34b86a71034, 0x861a382a851e58bd, 0x83ad3f8381234491, 0x80dbe8e57f8b47dd, 0x7dd2e1557d049057, 0x7cb261947c166f0c, 0x7b05602a7a4e56d2, 0x7a42b52a7a1e3eb7, 0x79ea78f9793d88c3, 0x777722507633e8d2, 0x75c1120174bfe284]

def largeWord27 : Nat := packCertificateWords [0xaae96690aa817e3a, 0xa4ff8acfa3f876e6, 0xa3626338a33974df, 0xa01f03909cf02c9d, 0x9afeeeaf9aea8d45, 0x968f64de93bb1ec8, 0x91e00a568f7554fa, 0x8df5cbbe8a42b5d3, 0x8868d1ff863cd907, 0x844f9f5d8202ddc9, 0x81af6859802b286e, 0x7f8b47dd7d7e93c7, 0x7d4fb6c17cb26194, 0x7c5c4f4c79630cd4, 0x75c11201742b5d22, 0x727860797240ed1d, 0x713455817082d366, 0x704b57ba6eef8717, 0x6e60e7b56dfc4d30, 0x6c86863f6a707d4d, 0x6a6279476933765e, 0x68bfa94c68791c16, 0x67e3cb706560625b, 0x63f25c0d61e530cc, 0x5fd736de5f214d13, 0x5e4c573e5a4275b2, 0x59e2356d59ddc5c9, 0x58676d6256438df5, 0x51466125511544f2, 0x508ece464ba99e66, 0x4339b9da42c499aa, 0x41e921ab40c7ba3f, 0x3de6f6463dad40b4, 0x3d457f193cbf984d, 0x3c6dcde03b10d3b7, 0x3b0003853abf3775, 0x39fc54ee3968c4c0, 0x38be8a43378cbae2, 0x36284ab635c85379, 0x346456b833ca35c5, 0x3135faf83091e62c, 0x2f5ee2712e91394b, 0x2c7c9cd62c05a2a6, 0x2b43d1ba28bf54f0, 0x285f93d2267dc72e, 0x260cdc3224bc29b9, 0x23419d7923415b6d, 0x23040d7b22afdb28, 0x225567f622172930, 0x21572d742125cf48, 0x1ea2845f1db7ccad, 0x1d83bc4a1cdd3626, 0x1bdf6c631bda94ab, 0x1af3d06e19ddf349, 0x176dd385174ef202, 0x162e383715c3810b, 0x1311a6fa13019fb0, 0x10773ac51065ccb2, 0xebbc8470e8112ae, 0xd9247a00cd87b2c, 0x94859a60763b48b, 0x728131f064e77b9, 0x5c2aad8059b9297, 0x46f0bf60469dff1]

def largeWord28 : Nat := packCertificateWords [0xfe24254af40b9d29, 0xf2afbcc5e9d907e1, 0xe9809f6be618545a, 0xde650322dc1578ee, 0xd9a2c40ed70844bd, 0xd25ef427d0dfb02f, 0xc7011277c2436907, 0xc1bf7c36bf413fcc, 0xbe7595d4be74fb79, 0xbe576b4cbbced012, 0xba2e0454ba154586, 0xb93c8a41b843944f, 0xb43689f7b2ea1914, 0xafbb20acadd0b0a7]

def largeWord29 : Nat := packCertificateWords [0xe96d8581d1cd36f1, 0xbf98b147ba2e0454, 0xa96ded2ca5e2e6eb, 0xa3f876e6963660d1, 0x928aab73869f6fdc, 0x704b57ba6f149ea9, 0x6e21827567d0cec2, 0x64ee17b544608fe2, 0x3cfb43bc32620738, 0x2485f87923419d79, 0x10710c500ed4e76f, 0x322b61c003c1023]

def largeWord30 : Nat := packCertificateWords [0xee00ee00ee00ee30, 0x30003000300c00, 0xc000c000ccc00ff, 0xff00cc0000cc00, 0xcc00cc0300ff00ff, 0x33003300cc00, 0xcc3000f000c000f0, 0xf000c000c000cff, 0xff00aa00aaea00, 0xea00c000c0700050, 0x7000503300cc00, 0x3300ccff00ea00c0, 0xc0ff00aa000000, 0xff00cc00ee00cc, 0xfc00f000f800f0fc, 0xfc00fc00fcc000, 0xc000c000c05500aa, 0x5500aaff00ff00, 0x140014003c, 0x3cf000f000f000, 0xf0cc0033003300cc, 0xaa00aa00aa00aaff, 0xff00005500, 0x5500aa00aa3c003c, 0x3c003cfa00ea00, 0xea00eafa00ea00ea, 0xfacc00cc00cc00, 0xcc0000ff00ff0000]

def largeWord31 : Nat := packCertificateWords [0xee00ee00000000cc, 0xcf00cf00ccff00, 0xff00ff0000fe00aa, 0xaa00aafa00fa00, 0xfa00fa11001100ee, 0xee3f003f000000, 0xf000c000c000f0, 0xff0000000000, 0xff0000f000, 0xf300f300f0ff0033, 0xff00cc33000000, 0xcc0000f000c000c0, 0xc0cc000000ff00, 0x3300cc00cc, 0xc000ff00ff00c0fa, 0xea00fa00eafa00, 0xc800c800c8550000, 0x5500000000aa00, 0xaa3300cc0066, 0xcc0000ff000000, 0xaaaa00aa00000000, 0xff00aa00ff0000fe, 0xfe00aa00aaee00, 0xee00000000cc, 0xcc0000ee00aa00, 0xaa00aa15002a0015, 0x2aff0000000000, 0xfa00c800fa00c8]

def largeWord32 : Nat := packCertificateWords [0x3300000022000000, 0xcc004400ccff00, 0xab00ff0000330000, 0x33000000003300, 0xaa000000aa, 0x100030001000, 0x300e000c000e000c, 0xfe00cc00cc00ccf0, 0xf000c000c0cc00, 0xcc000000000000ff, 0xcc11001100, 0xfe000000aa, 0x330033000000, 0xff00cc00cc, 0x3300cc0000000000, 0xaa00aa0f00, 0xe000c000cf000c0, 0xf000f0ea00ea00, 0xea00ea00003f003f, 0xff000000ee00, 0xcc003300ff0000, 0xcc00cccc, 0xcc0000, 0x3300330000cc00c0, 0xc000ccff00aa00, 0xaa00aacc00000033, 0x33000000, 0xccff000000aa0000]

def largeWord33 : Nat := packCertificateWords [0xff00aaee, 0xaa000000005000, 0x5000500050cc0000, 0xcc0000fc00f800, 0xf800f8fa000000fa, 0xf000e000e000, 0xe0ff00ee00cc00cc, 0xff00aa00ff00aaf0, 0xff00000000fc00, 0xf800f000f0ff00cc, 0xff00ccee00aa00, 0xee00aaff00cc0000, 0xcc00ff00cc00, 0xcc66006600660066, 0xbb00aa00aa00aafa, 0xfa00ea00fafc00, 0xfc0000ee00cc, 0xee00ccee00ee00, 0xcc00cc1f001f0000, 0xff00ff00cc00, 0xcc0d000c000c000c, 0xf003f000c000cff, 0x3000000000000, 0x4400cc00ccff00cc, 0xcc00cc03000000, 0xff00005500550000, 0xcc00ff000000, 0x88008800aa00aa]

def largeWord34 : Nat := packCertificateWords [0xff00f000f000f088, 0xcc00cc00ccf000, 0xc000f000c0bb00aa, 0xbb00aa30007000, 0xf000f0ea00c000ea, 0xc0d000c000c000, 0xc050004000400040, 0x33003300330000fc, 0xfc00a800a8fc00, 0xfc00fcf000ff, 0xff00f00000fc00, 0xfc00fc1100110044, 0x44330022003300, 0x223f002a003f002a, 0xf000e000e000ecc, 0x8800000000ff00, 0xaa00aa990099, 0x88008800000000, 0xfc00fc3300000000, 0xff00c000ff00, 0xc0f000f000e000e0, 0xfc00000000000000, 0xcc000000cc0000, 0x330000fa00fa, 0xcc003300, 0xc000ff00c0, 0xc0100050005000, 0x50cc00aa00cc00aa]

def largeWord35 : Nat := packCertificateWords [0xf000f0000fe, 0xfc00fe00fce000, 0xc000e000c0cc0088, 0x880088ff00fa00, 0xf000f0f000a00000, 0x1100cc001100, 0xcc0200aa00aa00aa, 0xcc00c800c800c833, 0x2200220022bb00, 0xbb00ee00eeaf00ae, 0xae00ae05000400, 0x40004ff00330000, 0xaa00fe00aa00, 0xfeff00aa00330000, 0xf300f30000000033, 0xff000000003300, 0xff00cc00cc220000, 0x220000ff003300, 0xff0000f000c000e0, 0xc0fe00f000f000, 0xf0ff00ff00ee00ee, 0x54005400fc00fcff, 0xff00aa00000000, 0xfc000000fc540000, 0xff0000bb00bb00, 0xcc00ccff00f300ff, 0xfe000000fe00, 0xaf008c00af008c]

def largeWord36 : Nat := packCertificateWords [0xf000ff00f0ff, 0xc00ff000c0c00, 0xff0000000000, 0xff00ccbb00bb00, 0xaa00aafe00fe00fc, 0xfc0f0000000f00, 0xfa00aa00ff00aa, 0x55000000440000ee, 0xaa00ff00aa0f00, 0xf000c000c440000, 0x440000ff00ff00, 0xc000cf000400040, 0x40ff00ee00ee00, 0xee33003200320032, 0xdc005000500050ff, 0x3300330000cc00, 0xcc00ff00cc3f0000, 0x3f00000000ee00, 0xee00eef300f300f3, 0x500050005100, 0x5054005000500050, 0xae00ae000c000cff, 0xee00aa00aa3000, 0x7000700070000000, 0xee00ee1f003f00, 0x1000f000f0, 0xf0fa00aa00aa00, 0xaaaf008c008c008c]

def largeWord37 : Nat := packCertificateWords [0x3300ff00330000fc, 0xf000f000f00c00, 0xc00ff000c5500ff, 0xf000, 0xf05100000051, 0x880088008800, 0x884400ff00000000, 0xfb00fb00aa00aacc, 0xee00aafc00, 0xfc00000000cc0000, 0x88000033000000, 0xff00005400540000, 0xaf00aa00af00, 0xaa88008800cc00cc, 0xff000000330000f0, 0xff00000000, 0xfa00fa00faf30000, 0xf3000044004400, 0x4400444400550000, 0x300ff000000, 0xbb00bb00000000, 0xff0000000c00000f, 0xa000000003300, 0x3300220022f00000, 0xf50000ff00ff00, 0x330000f000f00000, 0xf300f300a200, 0xa2ee00ee00aa00aa]

def largeWord38 : Nat := packCertificateWords [0xee00ff0000000011, 0xff00000000af00, 0xaa0000050005, 0xaa00ff00, 0xff00ff00fc, 0x540054005400, 0x54ab000000ab0000, 0x220022002200220f, 0xf000000000000, 0x5500000000770000, 0x770000ae00ae00, 0xae00aeae000000ae, 0xf000a000ff00, 0xaa33000000770000, 0x33002200ff00aacc, 0x8800ff00aabb00, 0xff00aa00aaf000f0, 0x5000500c00ae00, 0xc00aef0000000f0, 0x3000f000f000, 0xf0bb000000bb0000, 0xfc00000000ff, 0xcc00000500, 0xff00000000f30000, 0x10001000, 0x30003000000000f3, 0xcc00cc00ff00, 0x11000000110000]

def largeWord39 : Nat := packCertificateWords [0x55005000500050ff, 0x4400440044dd00, 0xcc00cc00cccc0000, 0xf500f000, 0xf000f0cc00cc00aa, 0xaaee0000000000, 0x50005500000000, 0xff000f00ff0000ff, 0xae00ff00ae0000, 0x4400440044aa00ee, 0xee00ee00000000, 0xf000f03300220000, 0xe000e000c000, 0xc011000000000000, 0x5500000000000022, 0xaa00aa00aaff00, 0xf000fa00f0fc0054, 0xfc005455004400, 0x440044ff000000f0, 0xff00fa00aa00, 0xaa0e000e000c000c, 0xfa000000000000aa, 0xaa00fe00fef000, 0xf300f000f0000054, 0x540f000000, 0xaf00aa00aa, 0xaa550004005500, 0x4ff00ee00ff00ee]

def largeWord40 : Nat := packCertificateWords [0xa800a800a800a80f, 0xf000f0000f200, 0xf200f200f2cc0088, 0xcc0088cc00cc00, 0xcc0000fa00fa00f0, 0xf0700070007000, 0x705000f0005000f0, 0xcc00cc00ee00ee55, 0xff0000ff00, 0x8800ff00880f000a, 0xf000aa200a200, 0xa200a2f000ff00f0, 0xf0cc000000cc00, 0xcc44004400000000, 0xf000c000f000cff, 0xff00cc5500, 0x5000550050440044, 0xcc00cccc00cc00, 0x440044ff00ff00f0, 0xf0f000f000fa00, 0xfaff00f000ff00f0, 0xfa00f000fa00f0fc, 0xfc00fc0000bb00, 0xff000c, 0xc000c0f000a00, 0xa000acc000000dd, 0xf0005000f000, 0x50ff00fa00fa00fa]

def largeWord41 : Nat := packCertificateWords [0xa000a000a, 0xaf800f800f800, 0xf8d000d000d000d0]

def largeWord42 : Nat := packCertificateWords [0x2462071802402, 0x2f0381c3c1d0002c, 0x5c250082c0c2d0f8, 0x2c58041582c12071, 0x50381a070002c0e0, 0x4148580c280209c4, 0xc090082c401f1282, 0x438071202c200911, 0x82c12011102c4220, 0xf82c181e0e82438, 0x70d82402070d018, 0xe190c0040e17000, 0x580c0e0a82c0e140, 0x98480c0e038440c0, 0x70202c200f0382c1, 0xc0d0602c0c070502, 0x4100703810000602, 0x8100601000080200]

def largeWord43 : Nat := packCertificateWords [0xc82c12070993c16, 0x6038109c0b03004, 0xe4d059300231038, 0x2402070011416270, 0x70340e0b03084060, 0x10487002070002c0, 0xc030082496010002, 0x4020725124763f00, 0x8249007238248c07, 0x2282488070002c4e, 0x70202c8620008f4, 0x4203008248407209, 0x763f008247c070, 0xf4780900818760, 0x11d024020c1c8440, 0xc03008e002070001, 0xc08371b0d4020700, 0xd01207198c80207]

def largeWord44 : Nat := packCertificateWords [0x21818121f0581802, 0x73402c0c010399c, 0x7a66048040e11048, 0x1cb86532018123f0, 0x38240207318dc0c6, 0x20f0749c0b048049, 0x720024c2010381, 0x81207300640c0900, 0x81c740b0481cbe5e, 0x597412010384412, 0x10397012310396c, 0x8e0b0301cb258058, 0x18ae3b03818ac550, 0x39500c0903864a60, 0xb290240207058381, 0x2010601812072894, 0xc09008143a4303, 0x247e01030240e2c]

def largeWord45 : Nat := packCertificateWords [0x9f018060481c32, 0x3705818f6010382c, 0x867a0480416063c8, 0x40e78088240e5c0, 0x58181e01039dc120, 0x12d0e48076048040, 0xe11031d402070b02, 0xce809399a40c211d, 0x87c16720481c260b, 0x302496710581812, 0x7029818ac070c82c, 0xc3b009bc0c09008, 0x340a16058240e130, 0x498402310382c0c6, 0xe0081c166d049b00, 0xe0b1381c3c1d0302, 0x4d60735018ac0103, 0x940d2061d87c7e69]

def largeWord46 : Nat := packCertificateWords [0x4902c0c3b0fa4416, 0x900969200b03004, 0xe8f3c018128e03a, 0x3412010397016060, 0x487d1806049ac0e8, 0xb058240e134502d1, 0x2093881c0c881f80, 0x40e0b04804181e1e, 0xa1c12010382c1207, 0x9a142c0642004fa, 0xb03024d64b05825, 0x6070982c4220008, 0x1c12014101c6c0b0, 0x308c028105824028, 0x160181c0d039fc2, 0x27a048040e160302, 0x4fc010581cfa132e, 0x1e00c092a81c1609]

def largeWord47 : Nat := packCertificateWords [0x4e8940207058185a, 0x10382c0c0936270, 0x1606048fce011030, 0x40e9b03158c2010, 0x382c800939804220, 0x6070340e0b3b8253, 0x4012181876840081, 0x84209038647a2100, 0x81c2e060481ca25e, 0xb018763f0082c0c, 0x990081c16060488c, 0x20b030040e98320, 0x8412074b82c0c960, 0x681c92091f8040e0, 0x6038783a7f058192, 0xa0d03a5012010380, 0x1c090081c003d04, 0x8040e93030240e19]

def largeWord48 : Nat := packCertificateWords [0x48040e450582402, 0x5506084121c0081c, 0xc095181c16094e0, 0x1c26a8030ec7e010, 0x48040e1e00100760, 0x10394416060681d4, 0xea6048040ea50881, 0x80e1e0e82c120103, 0xa90124b008dc6c06, 0x481c325404804f8, 0x70001812a303945, 0x4421048040e43030, 0xec0251030240e513, 0x282c0c07020dc420, 0x903a5c360b50824d, 0x8070581cfa130588, 0x402a003a7c120103, 0x8000c0903a78a20b]

def largeWord49 : Nat := packCertificateWords [0x2886c160900ac456, 0x16030a03c1d04804, 0x1a07001a40c091f8, 0x1d6011048040e0b3, 0x2018060108818020, 0x7269015e090081c1, 0x60e068b0560b0315, 0xc120720024020757, 0x10002073e9440c09, 0x3ab4a20b0481c26, 0xac531b4120103818, 0x4c09008a01609128, 0x5380b030040e810, 0x48040e1d002ac0c0, 0x9038642c06070345, 0x34030240e190480, 0x48c070002c80aa00, 0x81c1606548040e21]

def largeWord50 : Nat := packCertificateWords [0x581802076281876, 0x129b102c0b0301c, 0x806049b00ec3320, 0x2402070002c0c010, 0x3b0816061db04020, 0xb030058007048040, 0xe005f8381a071b8d, 0x816065f2f40e0b03, 0x243ebc108240207, 0x4baec0cba0081c16, 0x91281d720b03024, 0x2b8059900c3b0f8, 0x2c0c095b81c16061, 0xd8056c6921818760, 0x1030256a070c82c0, 0xc015a01c16060081, 0xd663d108c8020759, 0x1001201038180e7d]

def largeWord51 : Nat := packCertificateWords [0x38a0b80b030040e, 0x7d0d82c0cd20081c, 0x16d1030ec0209008, 0x1c00240581812076, 0x804412014001c160, 0x6678040ece108240, 0x207058259a076602, 0xc0c320081c16061e, 0x24020b0300c020b, 0x30ec02cb0581806, 0x10388594090081c, 0x16060081d920b030, 0x8c027d048040e000, 0xd8440c09118040e1, 0xe0e8dc6c0b030040, 0xec8058198e070f02, 0xd8c061d8040c0903, 0x864820b049840e13]

def largeWord52 : Nat := packCertificateWords [0x30240207459380c, 0x3b0081ca23632018, 0x4209039441606048, 0x5b60705818121f0, 0xb6c16066d024d60, 0x705819b0090081c1, 0x643048040e5c0581, 0x8120103b5c166d04, 0x8040e2b0581812d6, 0x81c16060081cfa, 0x5c34818420103b54, 0xc09038b0a247058, 0x18126c0387816060, 0x48058e0705818423, 0x20081c0c0e04804c, 0x44e349c80c090081, 0xc16740481da8d303, 0x2402071b0841201]

def largeWord53 : Nat := packCertificateWords [0xb02c0c093980416, 0x6048040e5f08824, 0x2072e02c0c09668, 0x1c3c0b0338412010, 0x39a40c097001c160, 0x900954582b058181, 0x20103b7c16776f02, 0x40207030855e0900, 0x81d6406048040e06, 0x481ca21b0308402, 0x73e944160604804, 0xedd03024020728b, 0x7016090081d98360, 0x589c1c090081c160, 0x60081cfa53048040, 0xe1d1b8d80c090098, 0xc4511e990420900, 0x81c1640048040e5c]

def largeWord54 : Nat := packCertificateWords [0x1881ca216058181c, 0xd0382ce821049f0, 0xe0b030240207750, 0x2c0c090081dd20b0, 0x3005d0073e818120, 0x1038a1160b0339c1, 0x2010382c0c093601, 0xc3a0b03274020728, 0x82c0c090081dcc0b, 0x480462072e02c0c, 0x3b0081dca0b03210, 0x2073e82c0c09700, 0x4566903158aa070, 0x5884760103970160, 0x9008c40e2c048040, 0xe622e0dc160604b9, 0x2077182c12072e, 0x218220604b880207]

def largeWord55 : Nat := packCertificateWords [0x7b01c1606048040e, 0xf303210120103988, 0x160604805382c030, 0x8412072886c7a067, 0xa824020705900120, 0x17a01c12010681c6, 0xe36058184c090081, 0xc16090081de63705, 0x818120103bc81606, 0x4805e2070590c0c, 0x3b04804d20604954, 0xe37048040e00030, 0x240ef02882dde090, 0x81cb80b04bb8020, 0x71602c0c3b0081dd, 0xa0b7602402071b82, 0xcc8060481dd60b03, 0x240207450841201]

def largeWord56 : Nat := packCertificateWords [0x58181273009680c, 0x903864a20b03024, 0x2820382c0c3b008, 0x1e000b030ec3e018, 0x2c120103bfcb80, 0xb033f80207058181, 0x20103bf40c0e0480, 0x40efc05824023103, 0xbec16061d9840207, 0x58240207528d816, 0x6048040efa05818, 0x121f7c94c0c0900b, 0xa00e620581812010, 0x3be0161020024020, 0x7058181207488781, 0x60604b8002070581, 0x9ee090081c7a2104, 0x8040e1b058181201]

def largeWord57 : Nat := packCertificateWords [0x668340e0b5d81812, 0x10382c0c090081e, 0xa0604804c41e270, 0x18120103988a20b3, 0xb8244a010382c423, 0xb3d0040e0b034101, 0x2010385816060387, 0x83a21048040e0005, 0x8240280039701606, 0x49ac0f033490c0c, 0x90081c2c061d804, 0xe510581802073eb, 0x941606048040f020, 0x5818763f0081c160, 0x61d87c7e010590c0, 0xc090f8041606049b, 0x1a0705824c2072e, 0x218160604c040207]

def largeWord58 : Nat := packCertificateWords [0x8681c1609770040e, 0x3705844120103970, 0x1606308040e7d030, 0x240e191e81812010, 0x3a2c12012a81c6e3, 0x60581a18012a81c1, 0x606048040f0b3481, 0x8423b0081c160985, 0x940207030381201, 0x39fc16060081e12, 0xb6f01802073e82c, 0xee0900c200e0b030, 0x2402078382c0c090, 0x8c40e0b32018121, 0xf0382c0d061d8040, 0xe0b03084761f0082, 0xc0c090081d6c0b04, 0x80462071b82c0c09]

def largeWord59 : Nat := packCertificateWords [0x5782402070581812, 0x103bfdc60604804, 0xe510589c1201038, 0x742c06048040eae0, 0xb01802073e944160, 0x6048062407059001, 0x20103978160604c4, 0x4020705818120d03, 0xa4416061f8040e7d, 0x5818120103c40ee, 0x90081cb87f3481a, 0xc092a81c1664030, 0x40e170581812010, 0x3c3c0c09009883a4, 0xe05900120103b641, 0x66d048040e360581, 0x802073ea2c160604, 0x8061c07058181201]

def largeWord60 : Nat := packCertificateWords [0x81cfb1c0581812, 0x7005824031b03970, 0x42090081ca25c718, 0x8412010397016068, 0x30040e7d059900c0, 0x90081e340b030240, 0x20705818ec01039f, 0x416060487ce00b03, 0x24031803818123f, 0x81ca60b030243e, 0x70d82c0c0911804, 0xc090081ca6c4058, 0x1812016dc5c16060, 0x488c020703024020, 0x78b1fc0c21048040, 0xe500b10012010394, 0x416090081cb91505, 0x82402078a1702c06]

def largeWord61 : Nat := packCertificateWords [0x7282c0c090081e42, 0xb900244a010382c, 0xc098f8040e69058, 0x193a010382c0c090, 0x81e3c0b03130020, 0x70581812014e4001, 0x609008b0a22b0581, 0x812014701c160604, 0x8063a07058192c09, 0x81c16060480500, 0x7348184201039f4, 0x2c0b3a024f807058, 0x18e601039f40c090, 0x81df81e058192a0, 0x90081c0c091f8040, 0xe621082402072e0d, 0xc1606070340e4e05, 0xb180c090081c1606]

def largeWord62 : Nat := packCertificateWords [0x960240207059d042, 0x9d0081c160604804, 0xf2b05ca40c09008, 0x1c2c060480450d90, 0x5818126b03ca00c2, 0x104805d007058187, 0x7270081c16640303, 0x812070302402077e, 0x741606048064c07, 0x581a4a010382ce8, 0x9008c40e0b04804, 0x62072d8184284048, 0x40e110303812010, 0x382c0c09258046e0, 0xb0302402079202c0, 0xc0900c880e690302, 0x4aa072a02c0c090f, 0x8fdf20b030240eeb]

def largeWord63 : Nat := packCertificateWords [0x3cbca2064202402, 0x71b01812012a988, 0x9c21048040e51158, 0x1842090081ca2160, 0x58040ed97d82c0c0, 0x9358fc0e0b030240, 0x2072982ccc060480, 0x40e69030240e1905, 0x81812019702c0c09, 0x81cb80b5101812, 0x10382c120103970, 0x6e0b0301c3c1d273, 0x4c1606710040e0b9, 0x690012010382c0c0, 0x9038641606048040, 0xecb0581812710081, 0xcd206048040e5003, 0x247e01039441606]

def largeWord64 : Nat := packCertificateWords [0x590012013e01c16, 0x1003024020705818, 0x1273008b0d206108, 0x240eeb0b01812013, 0x1145c621048040e0, 0xb030ec02db0382c0, 0xc0935cc40e0b0300, 0x40e7d6a02c0c0900, 0x81e600b368240207, 0x2d02c0c090081d4e, 0xb0302402e80382d, 0xbc090081c580b030, 0x243e077282c0c840, 0x48040e0604805d00, 0x71b018120103874f, 0xe06048040e391b02, 0xda206048040e0604, 0x8041a077e0181201]

def largeWord65 : Nat := packCertificateWords [0x381812010282c0c, 0x90081dda6903024, 0x7e07059900c32008, 0x1c16743e01cfa690, 0x30243e3f039a4420, 0x90081cb80b030040, 0xe170302402db3114, 0x41606048040f3505, 0x818760103a281606, 0x4382402070581812, 0x103b94160607024, 0xd60703084123f008, 0x1c1706048040e5c0, 0x581812019a01cd20, 0x6108240e51030247, 0xe0103ccc2c060702, 0x4022808818120103, 0xcc87a21070240207]

def largeWord66 : Nat := packCertificateWords [0x48fc02070581812, 0x103978160610804, 0xe17058181339008, 0x1c167704bb802070, 0x30247e01038d8164, 0x3030ec023d108240, 0x27c0382c0c090081, 0xe700b9b884120103, 0x82e6c06048040e69, 0x3084121f0382c0c, 0x90081d261103024, 0x2077302cee09008, 0xc40e0b3201812070, 0xe82c0c0900b6c503, 0xd4f88412010382c0, 0xc09009bc0e0b0300, 0x5b6073e8440c0900, 0x81c3a16032101201]

def largeWord67 : Nat := packCertificateWords [0x1b0180207311f4a2, 0x3d1082402070e82d, 0xbc21048040e0b030, 0x678073e82c0d3b0, 0x48040e6903024020, 0x79782c0c090081d2, 0xe0b21818423b0085, 0x80c09008a03c6903, 0x8412010382c0c09, 0x81d3c0b4482402, 0x71b084120103a5c, 0x16060081cfaf30b0, 0x1812019d01cd2060, 0x48fc0207058181c0, 0xd038dc16061d8040, 0xf050b01812010394, 0x40c3b0081cc45105, 0x81802073ea281606]

def largeWord68 : Nat := packCertificateWords [0x48068a07048040e, 0x1e1b8d8160665024, 0x207058186401039, 0xa4e821048040e0b3, 0x201802073e82c0d2, 0x7048040e16030240, 0x20d1402e88060480, 0x40e0b030240207a1, 0x82c0c0900d080e0b, 0x350402550382e80, 0x6048040e0b03024, 0x2079f82ce8093e0, 0x1cc40b9f01812010, 0x382c0c0900af00e0, 0xb030267a01038580, 0xc09008a03a0b3201, 0x87601038195e0900, 0x81cc40e048040e37]

def largeWord69 : Nat := packCertificateWords [0x81c160604804aa, 0x73102c0d4904804, 0xe0b03024020d038, 0xac1606048040e850, 0x581812010681c6e0, 0x6048040e7f0b02e9, 0x6048040eb20302, 0x4020705818767a00, 0x81c160604804aa07, 0x1602c0c3b0081ca2, 0xb0302402db0382c, 0xc01039f4b80b031, 0xb41201038f416060, 0x4804aa070581a8e0, 0x90081c1606108240, 0x27c0382ce8093e01, 0xda60b03024020705, 0x81a8c090081c1606]

def largeWord70 : Nat := packCertificateWords [0x2e218174e0302402, 0x705818120103d34, 0x16060481e980b030, 0x8412010387416061, 0xd8040e16058181c0, 0x90081c16061d87c0, 0x20b03025c0010382, 0xc0c09008c40e5105, 0x818120103bcc1606, 0x1d87c02070581812, 0x14e01cb80b03024, 0x2f10382c0c01039, 0xf5d60b033b012010, 0x3a980c090081c160, 0x604804f8071b02c0, 0xd2a048040e0b0302, 0x4034b0382c0c0900, 0x81d154a058184209]

def largeWord71 : Nat := packCertificateWords [0x302402078b02d64, 0x6048040e0b03024, 0x207a982c0c1f008, 0x1cfa0b0302402070, 0xe8d8160607024020, 0x72d02c0d52048040, 0xe0ba702402070581, 0x812011881c160610, 0x8ec0207058181201, 0xa881c2206048040e, 0x6048040e622882c, 0xc09009540e2b058, 0x1812019e01c16060, 0x48040f5005818020, 0x7a782c0c40048040, 0xe0b2181812010382, 0xc0c090081c3c3605, 0x8193a010382c1207]

def largeWord72 : Nat := packCertificateWords [0x38580c09008a02c, 0xb0302402070e9a4, 0x1606049540e3d108, 0x240207058181c090, 0x81c9c0b03024027, 0xc039681606048040, 0xe512e38c16060480, 0x40e5c05818120103, 0xd5016060487df20b, 0x308402073e82cc8, 0x6048040e0b03024, 0x2076e02cee06048, 0x4f8070581812010, 0x3988b81605818120, 0x13e01c160604bb80, 0x2070590c0c210480, 0x40e0b03504020705, 0x818120103d301677]

def largeWord73 : Nat := packCertificateWords [0x356802070581908, 0x90081c160604804, 0xe626c82c0c09008, 0x1cb41d0308412010, 0x39441606048040e5, 0x3058180207ac82c0, 0xc090f8040e530582, 0x4022c1582c0c0103, 0xd601606048040e5c, 0x581812012a81c6c, 0xb030243e0103970, 0x16090081cb837058, 0x1812710081c16060, 0x4d5c020705818126, 0xb0382c0c090081c3, 0x60b048040f560581, 0x876018b82eaa0900, 0x81c1664030841201]

def largeWord74 : Nat := packCertificateWords [0x39a41606048040e, 0x5c0581a920103824, 0x2071b8d81606048, 0x40e1d2702c0c0e0, 0x48040e2c05818420, 0x90081dd60b030240, 0x207728f416060702, 0x4020705d200c0900, 0x81cc4e3058181201, 0x382c0c090081c3c, 0x4e0581812013e01c, 0x500b03004f8073e8, 0x2c0c0900d700e0b9, 0xb81812010382c0c0, 0x9358040e0b048040, 0xf14058181201ad81, 0xc160604805d00705, 0x81842090081c360b]

def largeWord75 : Nat := packCertificateWords [0x302402550393816, 0x6048040f5e05818, 0x120103a5c2c0b030, 0x2402072e1a40c210, 0x48040e0b03024020, 0x78c82c0c0e048040, 0xe3705818120103cb, 0xc1606048040f1c05, 0x81842090081c1606, 0x8302402070581812, 0x18981c160610824, 0x3e010382c0c0975c, 0x5c2c06048040e510, 0x5818123f0081c160, 0x60487c7e010382c0, 0xc090081d160b0308, 0x476090081c1606ae, 0x8040e0b030243e01]

def largeWord76 : Nat := packCertificateWords [0x302402074302c0c, 0x9009540e0b03004, 0xe7d058181201039, 0x381606048040f620, 0x581876010382c0c0, 0x90081c3a0b030240, 0x2072d52816060480, 0x40e0b3b818120103, 0x82d3e06108240207, 0x5818120103c8cd2, 0xb3a01812010382d, 0x3e06048040e0ba40, 0x181201038d816061, 0x83812010382c0d6, 0x10081c1606b00040, 0xe0b0302402071607, 0x41606048040f5f1e, 0x82c0c090081c3a0b]

def largeWord77 : Nat := packCertificateWords [0xb030240, 0x20705818120103c5, 0xc160607024020705, 0x9d00c090081c1606, 0x1082402070581812, 0x103b64160604804, 0xe0b030243e01038, 0x2c0c3b048040e0b0, 0x302402071b82c0c0, 0x90081dd60b030240, 0x2072e02c0c090081, 0xc580b0302402077c, 0x8f41606048040e0b]

def largeWord78 : Nat := packCertificateWords [0x1a68, 0xcf4065a031d0186, 0x80bf405da02dd016, 0x680af4055a029d01, 0x46809f404da025d0, 0x126808f4045a021d, 0x106807f403da01d, 0xd00e6806f4035a01, 0x9d00c6805f402da0, 0x15d00a6804f4025a, 0x11d0086803f401d, 0xa00dd0066802f401, 0x5a009d0046801f40, 0xda005d0026800f4]

def largeWord79 : Nat := packCertificateWords [0x108a8831440ea202, 0x50fea87e143e6a1e, 0xe50f4a879143bea1, 0xda50eaa87414396a, 0x1c650e0a86f1436e, 0xa1b340d7286a5434, 0x8a19f50cd2865543, 0x20a18b50c3286054, 0x2f8a17750b9285b5, 0x42d0a16350af2856, 0x542a8a14f50a5285, 0x154280a13b509b28, 0x4c54258a12750912, 0x84754230a1135087, 0x284254208a0ff507, 0xd283d541e0a0eb50, 0x732838541b8a0d75]

def largeWord80 : Nat := packCertificateWords [0x1a828d2d468ca341, 0x519e28cdd4664a32, 0xd519428c8d463ca3, 0x19518a28c410616a, 0x3065180a8bf145ee, 0xa2f25176a8ba145c, 0x6a2de516ca8b5145, 0x9ea2ca5162a8b014, 0x576a2b65158a8ab1, 0x454ea2a2514ea8a6, 0x14526a28e5144a8a, 0x1144fea27a513aa8, 0x9c144d6a2665130a, 0x897144aea2525126, 0xa89214486a23e511, 0xca88d1445ea22a51, 0x12a88814436a2165]

def largeWord81 : Nat := packCertificateWords [0x247a9229490aa480, 0x523da91d948e2a46, 0xc5233a918948baa4, 0x585229a91394892a, 0x444521fa90e9486a, 0xa4305215a9099484, 0x2a41c520ba904948, 0x1aa4085201a8ff94, 0x7f2a3f451f7a8fa9, 0x47caa3e051eda8f5, 0x947a2a3cc51e3a8f, 0x9477aa3b851d9a8, 0xeb94752a3a451cfa, 0x8e69472aa39051c5, 0xa8e194702a37c51b, 0xba8dc946dc836951, 0xb228d7d46b4a3555]

def largeWord82 : Nat := packCertificateWords [0x27929, 0x3b549d0a4e3526f2, 0x936549a8a4cf5265, 0x29315498284bc525, 0xba92c9495aa4a852, 0x51a92794932a4945]

def largeWord83 : Nat := packCertificateWords [0x335b19958cbec659, 0x6329b19358c8ec64, 0x1631db18d58c5ec6, 0x296312298798c30c, 0x6126306318198c00, 0xc5fa62fa317bd4bd, 0x2c5e362ef297618b, 0xa4c5cc62e3317054, 0xb78a5b662d8316a9, 0x8b48c59e62cc3164, 0x98b18c58662c0315, 0xe98ae8c56e62b431, 0x5898ab8c55662a83, 0x15298a88c53e629c, 0x314c98a58c526629, 0x314698a28c50e62, 0x84a940d89fac4f76]

def largeWord84 : Nat := packCertificateWords [0x3f2b1f7d8fb2c7d3, 0x63e6b1f214f84c7b, 0xc63db31ec18f54c7, 0xa463cf31e618f24c, 0x78c63c331e018ef4, 0xc77553b7b1da58ec, 0x6c75d63ac29d498e, 0x98c74663a031ce98, 0xe68c72e639431c89, 0x8e38c716638831c2, 0x98e08c6fe637c31b, 0xc98dd8c6e6637031, 0xb698da8c6ce63643, 0x1b098d78c6b66358, 0x31ab10d4ea6a1634, 0xdb1a558d1ec68963, 0x41b19f58ceec6716]

def largeWord85 : Nat := packCertificateWords [0x4b03256992a8c94e, 0x64a4aa50d927ac93, 0x764992a4b1924cc9, 0x20648d32451921cc, 0x9086481323f191ec, 0xc8f064753239191b, 0xcc8d864693233191, 0x8cc8c0645d322d19, 0x15cc8a8645132271, 0x912cc89064453221, 0x190fcc8786439321, 0xb190d08862642e32, 0x15990a0c84a64223, 0x20f99072a8336416, 0xb209d9042c81b640, 0xab203d9012c80363, 0xfeb1fdd8fe2c7eb6]

def largeWord86 : Nat := packCertificateWords [0x56cb2b4d959acac8, 0x5561aaaf5956ecab, 0x16555b2a95953eca, 0x9a554a32a399510c, 0xa82653e329d994e0, 0xca6a65323297994b, 0xca5265263291994, 0x80ca3b551ab28bd9, 0x452ca23650eb285d, 0x9422ca0b6502b27f, 0xd93f2c9f364f6b27, 0x9d93c2c9dc54eb32, 0x7419394c9c464df3, 0x26e19364c9ac64d3, 0x326819334c99464c, 0x7326219304c97c64, 0xbc225c992d8c9666]

def largeWord87 : Nat := packCertificateWords [0x629b3135988ecc41, 0x661db30d5985ecc2, 0x96611b3075982ecc, 0x116605b301597fec, 0xbfb45fab2fc157d4, 0xcbe555efb2f6597a, 0x8abce65e432f0997, 0x78cbb665d832ea99, 0x748cb9e65cc32e49, 0x9718cb8665c032de, 0x996e8cb6e65b432d, 0x8996baab5765a8b2, 0xd2d968acb3f659cb, 0x2ccd965acb276590, 0xb2c6d962acb0f658, 0x4b2c0d95facaf765, 0x78b2bad95cacadf6]

def largeWord88 : Nat := packCertificateWords [0x36099af8c, 0xd7666b8335ad5aca, 0xcd5f66acb354d9a9, 0xacd4766a0b34ed9a, 0x6acd2f6694b348d9, 0xa3acd176688b342d, 0x9a0accff667cb33c, 0xd99dacce76670b33, 0x6d99aacccf6664b3, 0x30d997accb766592, 0xb2b1994ccca0664d, 0x33251991ccc88664, 0x1331f198eccc7066, 0x353319198bccc595]

def largeWord89 : Nat := packCertificateWords [0x7842bc099df6eef5, 0x6777b3ba59dc4eed, 0xb776ab3b415d94ce, 0xc4675f33ae55d66c, 0xeac775333a819d36, 0xae956747b3a21dd0, 0x6ae7e573c339c99c, 0xdaae667730ab969d, 0xcaaae4f67243b909, 0x9c78ce357717b38a, 0x59c46ce1e570bbb8, 0x459c16ce0566ff3b, 0x7dddbe2cdea76f23, 0x3775dbb0add176e6, 0x2b7199b7eedb966d, 0x9b36b59b4ecda076, 0xcd3364ddb1cad886]

def largeWord90 : Nat := packCertificateWords [0x848b4229e10ab07f, 0x683c3c1cd60dcb06, 0x778303c165e0a6d0, 0x4c7822bc0fda070f, 0x317815b4095a03e, 0xd019680a2c039a01, 0xd00177fe2bfd99f, 0xdeefe877f133f719, 0xfaeafd077e5abf19, 0x5f80cfb977d93beb, 0x19f4ccfa067cdabe, 0x559f20af8b57c32b, 0xdfddef4af7377b6b, 0x3da15ec2ef5a77a9, 0xbbd31de8ccf41579, 0xdb3cd59e5ecf2877, 0x90bbc69de28cf0d7]

def largeWord91 : Nat := packCertificateWords [0x8a03c4e, 0x9a266f12d68933c4, 0x7de234b11558873c, 0x421a202f0fa787a3, 0x43b9a1cef0e1686d, 0xb4351e19cd0c8686, 0x1342f1a16cd0af78, 0x552c291a13cd0977]

def largeWord92 : Nat := packCertificateWords [0x8e7347, 0x21a384d1bc68db34, 0x6c56356d1a568cfb, 0x4665a326d18d68c3, 0xb4605a2f6d17568b, 0x82c5a9a2c8d15f58, 0xacb454da29ad1476]

def largeWord93 : Nat := packCertificateWords [0x301c1e887058180, 0x5819009690301c05, 0x9dc0301d1081d048, 0x1d03004048042e21, 0x903006030071e887, 0x581805819030040, 0x801008b00301f0b, 0x18030070481d108, 0x1d0301d0301c1081, 0xd0481d0307c1e887, 0x5818058191e8870, 0x5818058190300403, 0x1d0301c0307f2e2, 0x1903006030070306, 0x70301d0301c0081d, 0x481d03004048040, 0x58050081d1081d03, 0x9470307f00969030, 0x1c160ad0301e0301, 0xf030060b0180307c]

def largeWord94 : Nat := packCertificateWords [0x5818059730301d0, 0x59b70481f0581c00, 0x9690301c05807059, 0x733b807030ec0301, 0xe030040300403007, 0x581805807059dc0, 0x301d0301d030070b, 0x18030070581a030, 0x4030040581d0480, 0x6058180480605971, 0x58180481f3481b0, 0x581a048050581b05, 0x81a1080503007058, 0x1e0581803971049a, 0xd05b67030070301e, 0x597303007030050, 0x3006009690301c2d, 0x75048060301c059, 0xd0058050301f0581, 0xa048061080610806]

def largeWord95 : Nat := packCertificateWords [0x481d0307c0081d1, 0x804058180307503, 0x3af1080505818059, 0x730581a059dc0301, 0xd0301d030070307c, 0x30ec05818108770, 0x58181e8870581805, 0x8191081d03005030, 0x76981a0307c0307, 0xc009690301c0581c, 0x30040581a058180, 0x596b0301c0307f05, 0x81f033af088053b8, 0x70301d0307c1080, 0x60581f030ec03007, 0x8804048043681d0, 0x48050301f1081d05, 0x8181e88705818058, 0x19030070301f0581, 0x805b670581f108ee]

def largeWord96 : Nat := packCertificateWords [0x307c0301d6981f0, 0x587d3a0240580503, 0x50597203007030, 0x7f0081d059dc0301, 0xd05bc403b650581e, 0x481f058050596b0, 0x301c0307c75c5d00, 0x81e0081f05818059, 0x700fbe70081c0081, 0xd034670701f0307f, 0x81d05818058180, 0x307f039710581803, 0x50301f05971030, 0x40344c038750480, 0x6088060581d3b807, 0x301d0307c030041, 0x805058180581d03, 0x270581a0300705b, 0x670301d030070300, 0x405819030040301e]

def largeWord97 : Nat := packCertificateWords [0x581903004200050, 0x59dc0301d0581f03, 0x40081f05971030, 0x7049ac0301c0716, 0xb048050301c03971, 0x581f3b8070301d0, 0x48b20301f059de03, 0x1d0581a1087d059, 0x6b0301c058070301, 0xf058180300705818, 0x581d0307c0322f0, 0x4805030041080405, 0x8180301d05bb1030, 0x4030050307c0301, 0xe9501d058180081f, 0x108ec05818108050, 0x58180596b0301c03, 0xa2d0597205973058, 0x180481d0581a0480, 0x503c8d0581803004]

def largeWord98 : Nat := packCertificateWords [0x480603007048060, 0x5818058190480610, 0x804058181081f108, 0x1d058180481d1080, 0x500cbf0581a0307c, 0x581a0581f030070, 0x307f200061087c10, 0x81d058180481d058, 0x1805b656981d0480, 0x60081d08827059dc, 0x301d10805058180, 0x3007058190581804, 0x8060581d030ec058, 0x180307c058180481, 0xf058050581805807, 0x581803007218060, 0x5970059b40303804, 0x805009690301c008, 0x1d34818058070300, 0x5058180880705818]

def largeWord99 : Nat := packCertificateWords [0x481f03077048060, 0x59690301c0581b03, 0x4a501803025030, 0x1e05970030070581, 0x8030250581f03004, 0x301e0301e059720, 0x3007048040581a05, 0x9de0301d0301d05a, 0x1b03006030ec0481, 0xd0301f030070481d, 0x397103007030070, 0x481f030380480503, 0x40301c05818058, 0x50307504806033a, 0x108050581805818, 0x1080505818108ec0, 0x5818048040581803, 0x4218254f81f058, 0x1805805058182180, 0x410805058180301f]

def largeWord100 : Nat := packCertificateWords [0x58180301e0096b0, 0x301c0581d05a1b03, 0x60387704806008, 0x1d0481f0581a0480, 0x6048050301c0581a, 0x300605973030070, 0x58180481d008df05, 0x81a059dc0301d030, 0x70301f0301e0300, 0x41080405818008b0, 0x301f3a027030050, 0x59dc0301d1081d05, 0x8180581a3a024030, 0x5030060300705a1, 0x903006a501f03025, 0x301c058180301d0, 0x48050481d0081d03, 0x40597303004048, 0x1d0081d039710300, 0x703b65030270081f]

def largeWord101 : Nat := packCertificateWords [0x33af0081f058180, 0x301c030ec0481d05, 0x81f0302704806030, 0x1c058180307f0081, 0xd0081c0307f0301e, 0x301f0496b0301c0, 0x3007030040300700, 0x81d030070581a008, 0xdd0581a0301e1080, 0x6058180081e0481d, 0x33e50081c108050, 0x58180301d0480603, 0x40581805819030, 0x1e048050581c0300, 0x4058070300703007, 0x3b8270301d0081c0, 0x81d058180481f10, 0x80505818059d2030, 0x50581d0301d0300, 0x405b67030271081d]

def largeWord102 : Nat := packCertificateWords [0x3004058191e8070, 0x5819030070581803, 0x50701f04805048, 0x50581a058b00301, 0xf048b20301f05818, 0x59d003005038750, 0x48060081e0081f03, 0x1d030070307c008, 0x1d0307c0303a0480, 0x50581804c5d0081e, 0x81d05807030050, 0x301e0301e0480604, 0x8050301f058183b8, 0x70301d048050581, 0x90301f0597103007, 0x48070301e0301c0, 0x3004030040481f3b, 0x8040301d05b65030, 0x27009690301c033e, 0x70081c1e80405819]

def largeWord103 : Nat := packCertificateWords [0x81e03005, 0x58180081d0581a0, 0x81f030070301f00, 0x81c0581903006030, 0x40301e0301c0302, 0x50301d0581810827, 0x581805805030051, 0x825058180581800, 0x81c04c5f0081e030, 0x1f048060701c0480, 0x504806058190581e]

def largeWord104 : Nat := packCertificateWords [0x200000, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]

def largeWord105 : Nat := packCertificateWords [0x112000000, 0xf200000000, 0xe100000d1030, 0x4000000000000000, 0x288000, 0x0, 0x244, 0x810000000000000, 0x18800000000000, 0x330000000000, 0x21000000000000, 0x0]

def largeWord106 : Nat := packCertificateWords [0x988, 0x0, 0x0, 0x0, 0x24208880, 0x844000, 0x0, 0x1e306cc, 0x684000060800, 0x5c40000, 0x0, 0x143000000004c40, 0x0]

def largeWord107 : Nat := packCertificateWords [0xfc4000000000000, 0x0, 0xf0c00, 0xe8800000003820, 0x0, 0x3620d4400000000, 0x0, 0xd04000000000000, 0x0, 0x313000000, 0xb8c0000, 0x0, 0xb442c10a880, 0xa08000]

def largeWord108 : Nat := packCertificateWords [0x7c11ec47a100, 0x7821dc40001d84, 0x7511d047221c446f, 0x21b8400000000001, 0xb086b11a8468219c, 0x4000198465100006, 0x32184860117c45e1, 0x5d117045b100, 0x592000058115c4, 0x5610000551000054, 0x114c452114440001, 0x4044f113844d1130, 0x44a211cc00000004, 0x6111084220000411]

def largeWord109 : Nat := packCertificateWords [0x2c48b012b88ac200, 0xa93000000029c8, 0xa610000a512904a3, 0x10000a1200000002, 0x7c80002784000000, 0x274400026c80, 0x9a1, 0x260800025c495225, 0x400024c40000000, 0x912240400000008f, 0x123848c200000002, 0x2c48920000863210, 0x883120487f200000, 0x7e11f44000]

def largeWord110 : Nat := packCertificateWords [0xe61000000038, 0xcce1237c8de13744, 0xdc136c4da10000d9, 0x1000000036040000, 0xd710000d61000, 0xd333484d1133c8c, 0xe100000003344cb2, 0x3248c8100, 0xc710000c613108, 0x30c4c210000c1, 0x13004bf12f480002, 0xec8ba12e44000000, 0xb810000b710000b, 0x612d44b320000000]

def largeWord111 : Nat := packCertificateWords [0x478400047091b146, 0x4918145c40000000, 0x1161000000, 0x454514144c40000, 0x11210000000440, 0x90e243090a242450, 0x8141c40004148000, 0x410503140490013f, 0xc4fe13f44fc10000, 0xf930000f723d4800, 0x3cc8f120000f013, 0xbc4ee10000ec2000, 0xeb1000000000000, 0x3a0c00039c4000]

def largeWord112 : Nat := packCertificateWords [0x594963258, 0x8400057cc0005749, 0x5c15688000000159, 0x155c800055855515, 0x505522000150253c, 0x54e153454c152880, 0x51cd46150cd421, 0x14114f, 0xc93e14ecd3924e04, 0x4d880004d4400, 0x13414c4d3014, 0xbc52d24ac80004a4, 0x928149c525248c80, 0x121248051f1]

def largeWord113 : Nat := packCertificateWords [0x64c400000019126, 0x4058e263098b1628, 0x4000000189162058, 0x62614584160c4000, 0x18125fc80005f, 0x857b35e857820001, 0x7710001743000173, 0x15c8571100000000, 0x17015bc4000000, 0x16d200016c15ac40, 0x5a840000001673]

def largeWord114 : Nat := packCertificateWords [0x7f85fc27ec5f927d, 0xc9f527cc9f127c05, 0xef17b49eb27a49e7, 0x27949e327849df27, 0x749db27649d81758, 0x9d427489d0273c5c, 0xe10001cc27289c91, 0x7205c717149c3270, 0x49bf26f49bb26e49, 0xb726d85b426c89b0, 0x26bc5ae16b09aa26, 0xa09a716949a32688, 0x5a0267899c266899, 0x9166059716585942]

def largeWord115 : Nat := packCertificateWords [0x98ca621980a5f197, 0x4a5c100025a2960a, 0x571954a532948650, 0x2938a4c2928a4829, 0x18a442908a4028f8, 0xa3d18f063a28e0a3, 0x628d463328c86311, 0x8bca2d28b062b18a, 0x4a272894a2410002, 0x2220002202878a1c, 0x200021a286461728, 0x54a132844a101838, 0xa0c2828a082818a0, 0x5100020328049ff2]

def largeWord116 : Nat := packCertificateWords [0xa4, 0x468f2a34a8b20002, 0x8a1a246872a14a83, 0x2a04a7f29f867c29, 0xec67929dca7529cc, 0xa7129c066e29b080, 0x9a8a682998a651]

def largeWord117 : Nat := packCertificateWords [0xa844, 0xa8069f1000000, 0xa784000a7469c1a, 0x6c69a1a646981a5c, 0x6961000295100000, 0x2941a4c6921]

def largeWord118 : Nat := packCertificateWords [0x7c0f41e, 0x3b0740e01883005, 0xa0ac140250480881, 0x820030050098120, 0x220400600a012020, 0x280400600800800]

def largeWord119 : Nat := packCertificateWords [0x10420440, 0x7f0f61e83c8770e, 0x41c0358680c016c2, 0xc8580aa1482804f0, 0x9c1302584a09011c, 0x220430841042003f]

def largeWord120 : Nat := packCertificateWords [0x2464848d, 0x9192224308490820, 0x840c811012003fc7, 0xa8ec19e32c650c81, 0x8e2f85e8b915c2b0, 0x540a413223444084]

def largeWord121 : Nat := packCertificateWords [0x40880500, 0x1ff3a874cdb99d31, 0x5ecbc9762d65a4b, 0x95f2b655ca99492, 0x865009e93b2744e4, 0x9892d2524a092924]

def largeWord122 : Nat := packCertificateWords [0x6bad6d9f, 0xb2163ac157ead959, 0xeb315fabd578a914, 0x27f4fa9f13826f4, 0xa093d1ea3c468891, 0x10a1041c83506208]

def largeWord123 : Nat := packCertificateWords [0x39, 0xff2fd9fb375eeafd, 0x49a3b06d99a7f2e6, 0x503ff7eefbdceb5f]

def largeWord124 : Nat := packCertificateWords [0x2000000000000, 0x0, 0x0, 0x0, 0x0]

def largeWord125 : Nat := packCertificateWords [0x4000000000a0000, 0x0, 0x1040000000200, 0x1, 0x100210001000000, 0x330000000000003e, 0xa0600000000, 0x0, 0x100000004, 0x2100270600, 0x900, 0x0, 0xa21000000000100, 0x100000621, 0x0]

def largeWord126 : Nat := packCertificateWords [0x4000000, 0xa00000000000000, 0x1000100, 0x1000000000004, 0x2100000000000000, 0x600000000000000, 0x3e00000000, 0x100000000000000, 0x21042d0000000200]

def largeWord127 : Nat := packCertificateWords [0x12086a0100420400, 0x2a0200532e0f2701, 0x1b1801000604, 0x1800010000000021, 0x120027012d004006, 0x56080000218158, 0x400540700073610, 0x5807000000045300, 0x53105300010e04, 0x1002242d8b2d0200, 0x3d01457d2b5300, 0x36210062131a1804, 0x10012100010040, 0x7d53001000102104, 0x4c005304017d2101, 0x30000101a600927]

def largeWord128 : Nat := packCertificateWords [0x2100578d0f101000, 0x53008d00007d10, 0x10400770600130f, 0x101530a10005700, 0x1904547d21105306, 0x11000107210507, 0x904060f010023, 0x400090031001300, 0xa0000390b2218, 0x1821100a007f0000, 0x10000410003f0007, 0x2104012300047d01, 0x4007e53007d0404, 0x33002d53007d0104, 0x1000b0108000006, 0x630000453010000]

def largeWord129 : Nat := packCertificateWords [0x1000, 0x113015b285300, 0x212754060a0600, 0xf150023050407, 0x4008300044101, 0x90000105300000c, 0x2325000600068a, 0x400015709000500, 0x123010000045527, 0x53330a1a00130a23, 0x270654002209850a, 0x401272216, 0x400960028060053, 0x310533355000101, 0x2701150000021301]

def largeWord130 : Nat := packCertificateWords [0x696c6890879e815f, 0x59343c9a58990d4a, 0x3c3c9b521c8938a5, 0x6f6e6c5f1d2f1621, 0x4e4b957d1f93b0a2, 0x28ad4d6720ab2871, 0x8d426b1b86916e39, 0x8aad89092150a1aa, 0x2652571e733b9c5d, 0xa78894a0b12c3a37, 0xa651698aaf011748, 0x149d3a5e5d6a767c, 0x447976477a356397, 0x92a3a2437e34a401, 0x981e8a5a1e704674, 0x523c667d6d441d64]

def largeWord131 : Nat := packCertificateWords [0x54a8875c, 0x45b683563766184, 0x5c89808e7557977b, 0xac8f72271c3a3c27]

def largeWord132 : Nat := packCertificateWords [0x3b651eae788c3b6f, 0xa93b494f3b821e1e, 0x298a326f5e4f9f2c]

def largeWord133 : Nat := packCertificateWords [0x33333333000000, 0xcccc0000cccc00, 0x330033003300330, 0xc0c0c0c0c0c0c0c, 0x2222222222222222]

def largeWord134 : Nat := packCertificateWords [0x4ebae2c83f4b9445, 0x37b2141b1f596e8a]

def largeWord135 : Nat := packCertificateWords [0xe6d7b8d7d66b03b9, 0xacc8b14c85c9d431, 0x7eb9f287552add5f, 0x30d9886e2928435f, 0x24b172a10fed498e, 0x6c5ef24044cb8d6]

def largeWord136 : Nat := packCertificateWords [0xf0f08080f, 0xf080820202020a0, 0xa0a0a0000f000000, 0xf00700070007000, 0x7008080808000000, 0x70707070000000, 0xa000a0000000000, 0x3030303000000003, 0x30003000300f0, 0xf0000000000c0c, 0xc0c00000000a0a0, 0xa0a0000000070007, 0xf000f0040c040, 0xc0c0c0c0cf000f00, 0xf000f00a0a0f0a0, 0xf00c0c0c0c0c, 0xc0c0ca0a0a0a0a0, 0xa0a0af0f0f0f0000, 0xf0f00000f0f0, 0xc000c000c000c, 0xa000a000a000a0, 0x808080808080808]

def largeWord137 : Nat := packCertificateWords [0x41a0c520, 0xd062ac8341985259, 0x628083418b5220c, 0x55d083418b320d06, 0x2c883418b120d062, 0xc0834140f20d0503, 0x868698ab1a0cc2ac, 0x834182020cc55106, 0x82a48831ca418820]

def largeWord138 : Nat := packCertificateWords [0xa, 0xcd41a534467cce19, 0x932c64cc818d3146]

def largeWord139 : Nat := packCertificateWords [0x3142183141a23, 0x1431461421831431, 0x4220314218314314]

def largeWord140 : Nat := packCertificateWords [0xc100a291, 0x7200610051322111]

def largeWord141 : Nat := packCertificateWords [0xffbb70, 0x452a201811060100]

def largeWord142 : Nat := packCertificateWords [0x443fc56f3770bdeb, 0x2f2504b62e12f427, 0x2b8d2b7e262ad8c1, 0x18ab9c7114e1c470]

def largeWord143 : Nat := packCertificateWords [0x57e3d3b0, 0x129291b907006be5]

def largeWord144 : Nat := packCertificateWords [0xffaafefe00fc, 0xf000fa4444ff00, 0xfafaf0f000fecccc, 0xfff0ffccfcfcaaaa]

def largeWord145 : Nat := packCertificateWords [0x86, 0x408640e864081640, 0x387408d6408640c8, 0x140b8640a3814028, 0x6098174064053210]

def largeWord146 : Nat := packCertificateWords [0x56a995, 0xa9c52ea4946a885]

def largeWord147 : Nat := packCertificateWords [0xf56a1f9c, 0xd4b6d4718ec34ef7, 0x8c5fec1e84cb36aa, 0x5e483e8534479cc6]

def largeWord148 : Nat := packCertificateWords [0xca410ae5c5510f74, 0xc4f1028dbb05676f, 0xb68b2110b34bde55, 0xb0c90f16b02600ac, 0xacb08d0bacaf0b77, 0xaa4a833ba98bd46a, 0xa1c581329d354eda, 0x9c1996d09a4922e0, 0x99fdf6f89596f062, 0x939e38a391a32906, 0x9161d1649126ee9e, 0x9122537e8fa5ae84, 0x8cd93f208bd5b2f2, 0x89f7fdcd89c3c463, 0x86bf0a3f82b5db70, 0x7f62a33b7d616691, 0x6dec5a0a6d98ab27, 0x6bc4904469ef5dbe, 0x68a7fc9d681b91a0, 0x64fcbe5763b3cc1d, 0x62d9b6dd61c330f5, 0x60120a2f6007a545, 0x5d1238125cf465f2, 0x5ad289835a375d15, 0x5924bc4d58b575a7, 0x587e57c756e89399, 0x552ab1c4509a7f6c, 0x501b78f74fa8a7b0, 0x4e05812e4b3c7a80, 0x4a97c9ac49754ed6, 0x47c6fa82470a5cc6, 0x45a36502459b0020, 0x4535264144c701f6, 0x40c0e7c6409e5e51, 0x3f9fcc513f5dcc41, 0x3da1d1603d9645c7, 0x3d4d68483b36d699, 0x3a2501ca3888b023, 0x364ac10934b24baa, 0x3426ec7c341cd23d, 0x327a6fe6318acd91, 0x30f9833230b82b90, 0x307d48ca2e224023, 0x2d6317072c6d059e, 0x2c37be842c273104, 0x2a69ac7e28ff4e1c, 0x27dcd34626b7fa10, 0x24812a8522624656, 0x202b40fc1e109a03, 0x1c430be91c0955d0, 0x1b8d6a361a275a13, 0x19dcd7c61861eee9, 0x16e05e5515ed589f, 0x136de1a21346ad64, 0x1184cb1e113cbe53, 0x106281700ea95a0e, 0xea2f8410deba9d5, 0xd0a76280bcfa876, 0xae8822e0aa7b6b0, 0x9cc5dd4098a08c6, 0x8bf775506a9f90f, 0x4e9f8c704d89e9d, 0x427963002cbca3d, 0x264d830014ddb2e]

def largeWord149 : Nat := packCertificateWords [0xe4680b7e, 0xe19c44e3dacf3814]

def largeWord150 : Nat := packCertificateWords [0x3f5dcc413e9a767d, 0x3e92c9913e54fa97, 0x3da1d1603d893b2c, 0x3d86ab1e3c1a1023, 0x3c109fc33a2f451f, 0x38f076f337c31de5, 0x379f53e63786d9bf, 0x366e3bbf3662cb6a, 0x36374edd362ce41d, 0x35f20157359a4ad2, 0x34d2bbf333e8e3c7, 0x33954b5a331f1062, 0x327a6fe63201a3d1, 0x31c07e7731a3e952, 0x3170e96430b82b90, 0x2fe3cb7c2f9385a6, 0x2e5608a12e4499be, 0x2bda19dd2bcb972c, 0x2b2553822a4bb8ce, 0x2a2a4ff12a1dc82e, 0x286e5510273b64d4, 0x272f99e92654e857, 0x252e722e24f97721, 0x24a6669623863d57, 0x22b1f1752298ee68, 0x216bd392216a342f, 0x2016343e1f7e35a3, 0x1ef9d35d1ef6f865, 0x1eba38e61e46f382, 0x1de0f1b11ddb8fcc, 0x1d953a641d51fb05, 0x1d4595111d1e44c1, 0x1d1cf1cd1d172947, 0x1ce965801c0955d0, 0x1bd0fa9f1b92ecfe, 0x1a6f6b6f1a3f8812, 0x1a33fbe319b6c12a, 0x18b9ff74189b0920, 0x185caaf5181cb762, 0x17d88cd6177d0234, 0x1742191d16d9650a, 0x16621c6c163ecc28, 0x15feb1a915d5aaba, 0x1519cabf151720b4, 0x14f9da3314c83fdd, 0x149ee5ce13936ff7, 0x132d6ea811a6453e, 0x11982b5b1192a17f, 0xe616dc10deba9d5, 0xde343b40c71fe63, 0xc39d32b0af493e3, 0xa91a3ed0a673ee1, 0x9d66ab609951314, 0x9701b2d095a304e, 0x93d1a6708c6b48c, 0x82bb2f907d288fa, 0x795c01807711ece, 0x7044c8606d5d980, 0x6bff29b0653e7fd, 0x61ff50f04526d98, 0x44d1ef6030fac4c, 0x30deb0602ff50a2, 0x2b55aa10220e3de, 0x1f6885100ac2075]

def largeWord151 : Nat := packCertificateWords [0x999430e898b81843, 0x97db5c1497d7e165, 0x967af1b49596f062, 0x94aa391a91a32906, 0x9126ee9e903a00d8, 0x8fb4e2818faad6bf, 0x8f89dd9f8f5c7889, 0x8ea7cf768dc32e79, 0x8c1bd8ee8be654fe, 0x8bbcacfc89f7fdcd, 0x8769f47e86bf0a3f, 0x859221d8856ca5c9, 0x835bd69682ac1a80, 0x826199ba81d2980c, 0x814c2fc7812ed8c1, 0x80f8a0fd7fff301f, 0x7fa595617fa4738b, 0x7f620e257d0379b2, 0x7bf112d87bec798b, 0x7baa0aa17ae562da, 0x796e0e3778e8a7a8, 0x78c00d1e780b9354, 0x766690ac757539bf, 0x753bb4ad751fdd97, 0x74944693739e532a, 0x7358b0df73496e18, 0x70ea08487090d91e, 0x6f64164b6edf4c7f, 0x6e5009296e216296, 0x6e1db5af6df55a3c, 0x6dd24e0f6d0ca7d5, 0x6c37d5ca6b6a4128, 0x6b220e5a6a0ce040, 0x69eea2bf681d274b, 0x66c7162865d2413a, 0x6539b33964464566, 0x63ce8b446378063a, 0x6373dbe2632c3f68, 0x631dab3262420584, 0x610a451360a6b92c, 0x5f02e12e5ecc106a, 0x5ea28f925e9974da, 0x5e4ac6625dc393f9, 0x5d5fefa75ce5d596, 0x5b9591b15a619578, 0x58b575a75867a616, 0x5797230855d202a4, 0x55058d5a54f85fc3, 0x543bd6f1533c64e2, 0x52e3179452b9fb64, 0x52824ed4527f189e, 0x50adef194f3a5f03, 0x4e0658254aff15cf, 0x4abb9ddd4a447f02, 0x48233c2547d6c292, 0x4779ad824751c4f5, 0x466bb67545d6b026, 0x455f5d1544c701f6, 0x447230f543378873, 0x42cc454242994b4a, 0x42269b13417856d0, 0x40bacd3b407e6999, 0x4056b4ba40022f31, 0x3fc3a61e3f66498d]

def largeWord152 : Nat := packCertificateWords [0xfadb57f2f94c1570, 0xeaa42c48e37626bc, 0xe1de62c4e10c1333, 0xda93bc79d4e5d36c, 0xce838bb9cc40ac2e, 0xc89f9dddc8360337, 0xc7b89038c6df32ae, 0xc6526190c645282b, 0xc3e010efc17965a9, 0xbe44c5e7bd4c59b8, 0xbc2b9dc9bb63907f, 0xb76d4208b4bb271b, 0xb3a5ec8baf1a4984, 0xae03d8e4ad9665ef, 0xad881b03abf5347a, 0xabc7dc7aaa48da52, 0xa8537a75a70c652d, 0xa6d5b928a4c5ce06, 0xa3b57be7a1a6335d, 0xa0b7a2c2a09ebea0, 0x9fed8d6d9eca1beb, 0x9c89c2f89b5d5b15, 0x9a9d9a389a6aca22]

def largeWord153 : Nat := packCertificateWords [0x43dfabe24358f550, 0x431deb014319edeb, 0x427b26d8425b66cf, 0x4244a0e240f8329b, 0x40dd29da40d49df0, 0x40c8b4c140bd4fd5, 0x408f88274073ea4b, 0x3f8718b73ebe0cb3, 0x3de06abd3d67fb90, 0x3a5d89983a3cbe7d, 0x39bdffda39398c84, 0x38e89bda383e6c71, 0x37cda7f237b1fffe, 0x3775142c366b3531, 0x362ce41d35b5e6c5, 0x35a080f035674793, 0x34ff69903475e8c9, 0x3349baee32512a94, 0x31bea6153123a890, 0x310354fe30e877f6, 0x30c2fcda306e337b, 0x2f12aa542eece433, 0x2c0031742bfa7ecb, 0x2b373e1f2a377883, 0x28cfa3f6274dc3c3, 0x26439a1a25bfc918, 0x2551654824084368, 0x2301ae1321faf870, 0x21f54f5721d08c11, 0x2194ce9b2115b8de, 0x20e5646a1ebffd38, 0x1e6b8a021e489d4d, 0x1de044ca1d853eac, 0x1d2275031c6866fd, 0x1c0850591ba03678, 0x1b67e75e1b13165d, 0x1a80579d1a466b8b, 0x197366b7192a467a, 0x186ed88f179d9693, 0x15e918d415cb7182, 0x153b5be514c83fdd, 0x145cce64145953b5, 0x1442b6c81400b75b, 0x134c3aee12ef47ae, 0x12b1852b11a6453e, 0x10d02a870e290ae8, 0xe00f47e0d574f4c, 0xd1f19440c3b303a, 0xbf274900bc415b8, 0xbc1162909e08ade, 0x9a7d8f709951314, 0x97b662508d28bee, 0x86b9afb0867c74e, 0x84bb8820811cecc, 0x72cd911070adda6, 0x6c005bf063fd312, 0x60752a905001300, 0x4f9784904f6ee09, 0x3fd00cd0362d51d, 0x3486bd803026ea4, 0x2174f7101df929b, 0x1d6939901c638ea, 0x1a2813b015a5931, 0xec9e360067d350]

def largeWord154 : Nat := packCertificateWords [0xec927571e47a6982, 0xe3d4fe57d704caf4, 0xd28b70f2d0fe898e, 0xd080abebc76d0723, 0xbea8a026bceebcd0, 0xbaf049d3b744f36c, 0xaf930799aed8f1e2, 0xae6025cdab5a7594, 0xa7fc7918a684b1da, 0xa5dd5bf1a4ce50bc, 0xa3368cc4a2643d33, 0xa236c81aa1c44cfd, 0xa129948a9fbe3e35, 0x9ec076b19d69ed2d, 0x9c55d9d49c233cba, 0x9c051afd9ad15029, 0x9a19852c99cfb3d0, 0x999e641d99989b97, 0x997cc6bd97b096a9, 0x964edcee949e29b2, 0x94580ad79392a047, 0x9337e7069252a89a, 0x9161d1648f89dd9f, 0x8e366e858e127b08, 0x8d2d5fe58d0267a7, 0x8ca00cef8c4e3876, 0x8c3a8743897949ca, 0x8946e502891e5fbc, 0x8860caa984aaed58, 0x84a647a883ff3e6e, 0x829619e27f36ccf1, 0x7f30454d7ea82caf, 0x7defba927db5bc98, 0x78180520780e9d69, 0x7780d6c176a33ec7, 0x75a848c075746e58, 0x751696de74656a02, 0x73dc95fb73cdae27, 0x7372e193712a1940, 0x710c45666de7fdbd, 0x6dd977086c37d5ca, 0x69896e1d680000fa, 0x66159e9f65fb51eb, 0x656c93bf647d74b3, 0x636fcea262a2f7be, 0x5ee7f2835ec37a3c, 0x5e342b405d8d8583, 0x5d716bf35d5fefa7, 0x5d4222545d2650f0, 0x5d0e99285ce5e66c, 0x5ce5d5965c5c9892, 0x5c3db75c5adf9439, 0x5ac3cbe45a64fcf8, 0x59c8630959967f3a, 0x5966f1845762308c, 0x5761180d56994abe, 0x5653f03252fb5306, 0x527f189e5270c805, 0x51c7b8e5506d53ad, 0x4ff701f34ec2c2d8, 0x4ead54614d553f16, 0x4c7b51494aebb286, 0x49df6f9248398ccd, 0x47c0752346912e38]

def largeWord155 : Nat := packCertificateWords [0xf2d7842ae2f6cc52, 0xdc943f54d97bde48, 0xc6adaa0ac649b516, 0xb70b8c48ace40d3f, 0xabe6e128a8c42078, 0xa7848147a74692fb, 0xa2e1b633a0acd41c, 0x9ffc183a9be1e518, 0x906efd648f9570a7, 0x8215fd6d7f482aa1, 0x7c00ecf67b3a363b, 0x79238a6e723bc333, 0x70098edb6f02c272, 0x6efe5e576dd427ae, 0x680ad10c6501036f, 0x64dcc446642830f2, 0x5f9423af5f84236f, 0x5f4048c95e12612d, 0x5c56672d5aa3dacd, 0x5a4a0be5584d6a3b, 0x572d3d6a565fc1da, 0x52b9fb6450606b13, 0x4c7b51494b36dbf4, 0x45e0152944e04f8d, 0x431deb014268d4dc, 0x3e67f4813abf1546, 0x34b0cb8f32ccbb28, 0x3161aefe2eb642ba, 0x2b039043241cb7b2, 0x23c89a0a22c5a1b5, 0x21b4f2fa205f4d0c, 0x1edb55471be11d8c, 0x18907b5416e0a505, 0x16032cd515e918d4, 0x14e19db8138b8c95, 0x13195c2512b3d679, 0x118433b6117fcf9b, 0x10de97a00ea31109, 0xe61fd760e5dbbed, 0xde343b40d59fc0a, 0xca6363d0a93ed58, 0x9e2bbbd090f6918]

def largeWord156 : Nat := packCertificateWords [0xab95585a579c512c, 0x569c8b903e49a493, 0x34b0cb8f2e079448, 0x258c480e21a8620b, 0x205f4d0c202fbf56, 0x129dfe450d59fc0a, 0x9e2bbbd090d6eb4]

def largeWord157 : Nat := packCertificateWords [0x1414141444cc44cc, 0xffff2200ffaaffaa, 0xfaf0faf0ffaa0000, 0x44444444cc88cc88, 0x55ee55ee50f050f0, 0x55aac4c8c4c8, 0xff000000fcfccccc, 0xeaeaeaeaffffaa00, 0xeecceecc15ea15ea, 0xfca8fca8eac0eac0, 0xaa5555aaaaaaaaaa, 0xffff00cccccccc, 0xa55aa55aff00ff00, 0x96969696f0f0f0f0, 0x3333ccccffff0000, 0x55aa55aa3c3c3c3c]

def largeWord158 : Nat := packCertificateWords [0x152a152a56565656, 0x3cfc3cfc0000ffaa, 0xfcfc0000faf0f0f0, 0xc0c0fcfc3c3cfcfc, 0xffff8800f3f30000, 0x30303c3c55550000, 0xaaaafcfcc0c0, 0x3cff0000ffffc0c0, 0xffc0ffc0aa00aa88, 0x55ffaa00fcfcfcfc, 0x55aa0000ffeecccc, 0xfcf8f0f0ff3cff3c, 0x3c003c00f0e0f0e0, 0xc0c0c0c003fc03fc, 0xf0a0f0a0ccc8ccc8, 0xaa00aa0082828282]

def largeWord159 : Nat := packCertificateWords [0xffaa55aa0000ffee, 0xffffa00077bb0000, 0x70f070f03c3c3f3c, 0xffffaaaaaaaa0000, 0xc300c300003c003c, 0xf0f0c0c0eecccccc, 0xff00aaf8f0f8f0, 0xffff3c3c3c3c0000, 0xffffff00ff3c0000, 0xddeeddee44884488, 0x5656aaaafcfc3c3c, 0xfe00feffeac0c0, 0x33cc33ccddaaddaa, 0xfcfc3f3f0000, 0x3f003f00d5aad5aa, 0xf5fa55ff0000]

def largeWord160 : Nat := packCertificateWords [0x30303030babababa, 0x2c2c2c2c55145514, 0xecccecccff00ff0c, 0xffee0000cfcf0000, 0xc0c3c3c9a9a9a9a, 0xc0c0c0caaff5500, 0xaa00aaaa44aa44, 0x33223322aaaaeaea, 0xc3c3000000003c3c, 0xf5af0f00000fffa, 0x2a2aaaaa15150000, 0x1c3c1c3cffc0c0c0, 0xfffcff00feaaaaaa, 0xffaaaa0055fa55fa, 0x7f7f00005af05af0, 0x555455543e3c3e3c]

def largeWord161 : Nat := packCertificateWords [0xa2a2a2a255aa5500, 0xcc00cc00fefefefe, 0xa8a8a8a8f8f8f8f8, 0xaeaeaeaeffeaffea, 0xea00ea00ffff5500, 0x5500000000440044, 0xaaf0c0f0c0, 0xaa000033003300, 0xcc00ccee00ee00, 0xbbaabbaaaa000000, 0x8080808055005500, 0xf5f0fffa0000, 0xf0f0f050d5ead5ea, 0xc2c2c2c2ffccffcc, 0xffff8844ff300000, 0xaaa8aaa8ffffc300]

def largeWord162 : Nat := packCertificateWords [0xf0f00a000a00, 0xfefe0a0afcfc8888, 0xaa88aa880000c0c0, 0xfffffcfcf5f0f5f0, 0xc000c00033330000, 0xcccce0c0e0c0, 0xfff0ff0050a050a0, 0xff003300c0c00000, 0xff0cff0c3070f0f0, 0xffff55aa2a002a00, 0xbb00bb003f2a0000, 0x3030ffaaaaaa, 0xee00eeeeeeeeee, 0x3e3e3e3e20202020, 0x550000fffff0f0, 0xf0f000000f0c0f0c]

def largeWord163 : Nat := packCertificateWords [0xff44ff44ff50ff50, 0x332200000044cccc, 0x888888880f0a0000, 0x50f0f00000fffc, 0xf0a0f0a3f2a3f2a, 0xaa55aa0070707070, 0xc000c00ffff0c0c, 0xc080ffaafc000000, 0x5000500302ffaa, 0xa000a00054545454, 0x2222222244004400, 0xfceccccc50005000, 0xf4f40000fcfc00fc, 0xfff0fff0f000f000, 0x2aaaaaa04040404, 0xaa000f0f0000]

def largeWord164 : Nat := packCertificateWords [0xffc0ff00153f0000, 0x323232321f3f0000, 0xa00aa00fefeaaaa, 0xa8a800001e1e1e1e, 0x28282828f300f300, 0xfe00aaffbb0000, 0xf2f2fafa000a000a, 0x4444cccc22002200, 0xfffcfffcff00f300, 0xffff00aaa0f0a0f0, 0x5000500feaa0000, 0xaa55aa11221122, 0xeeaaaaaa40404040, 0xfe00aa00ffea0000, 0x50505050ffff0044, 0xf050f050ae0cae0c]

def largeWord165 : Nat := packCertificateWords [0xfefcdcfc0000, 0xfca80000fcfcfffc, 0x88008850f0f0f0, 0xf0e0f0e00fc00fc, 0xfe00fe00fc00fc00, 0xfffc000074740000, 0xdcdcdcdcf0faf0fa, 0xa000a0f8f8f0f0, 0xbfaa0000aa00ffaa, 0x55f00000fefcaa00, 0xaf00af00cf00cf00, 0xfaaafaaa5050f0f0, 0xff55000054ff0000, 0x1133000077007700, 0xe0e0e0e010301030, 0xe0c0e0cffaaff00]

def largeWord166 : Nat := packCertificateWords [0xa0a0a0a00220022, 0xfcccfcccfeeefeee, 0xfffaf0f054445444, 0xc0cccfc0000, 0x88cc88ccbfaabfaa, 0x202020254fc54fc, 0xff00ff0fafafafa, 0xa0a0a0a05a5a5a5a, 0x3030000011001100, 0xffff3030acacacac, 0xeeaaeeaaeeaa0000, 0x6666666654540000, 0xf000f00ddcccccc, 0xff00003f0000, 0x10101010eaea0000, 0xf000f0feee0000]

def largeWord167 : Nat := packCertificateWords [0xff30ff30aaff0000, 0xfc54fc5403030000, 0xf0a000000eee0eee, 0x3020302030103010, 0xb0a0b0a0ddccddcc, 0xab00ab00ffffffaa, 0xcceeccee44cc0000, 0x73507350cc44cc44, 0x202aaaaff303030, 0x405040500300ff00, 0xcccc00003f000000, 0x131300001f001f00, 0xc0c0000ccaaccaa, 0xfcecfceca8fca8fc, 0x8c0c8c0cffcc0000, 0x88008800ffffcccc]

def largeWord168 : Nat := packCertificateWords [0xfafa0000fff00000, 0x77770000c0f0c0f0, 0xafaaafaaff330000, 0x2a2a2a2aff88ff88, 0xcae0caec0e0c0e0, 0x50550000fcdcfcdc]

def largeWord169 : Nat := packCertificateWords [0x160c814021302002, 0x1a020043c06050c4, 0x3017828001a020, 0x205c1c020205a020, 0xe0b0181a0203c020, 0x4040ac2a2a030a41, 0x402140284e040400, 0x42a0213060420212, 0x82848020e0840002, 0x118884202030803e, 0x10020043c1d0e06c, 0x101a0203c3202020, 0x602e08008582a020, 0x2050020609848221, 0x203c0202020201, 0xc020683008080582, 0x80009010200e0203, 0x140801018080200]

def largeWord170 : Nat := packCertificateWords [0x400456020203c02, 0x202134980602020, 0x9602179281402050, 0x9248030b014080, 0x8ac2c3b020288e0, 0x20d9181006090ec2, 0x230178b014020208, 0x8020a218008a0205, 0x10c000a2210c0002, 0x210810040400482, 0x1b04100020202020, 0x7e02030947c02178, 0x287a1c0d8202a1b0, 0x4004782f1d828000, 0x21d02002061c8280, 0x300302870370202, 0x2061b0286a020d, 0x82002061a000662f]

def largeWord171 : Nat := packCertificateWords [0x2020021a0302800, 0x1a02020c8060518c, 0x20e020c402031, 0x84000203028c05f0, 0x2020800404004bc5, 0xd0e06c102f160448, 0xa300510c00020e06, 0xc1e0404170020204, 0x16c0204200043c04, 0x878782c1282812, 0x203028b40407900, 0x25903160001c020, 0x3c2a040780478022, 0xb828ac022a820021, 0xe010a80205000a, 0x6022902002020200, 0x43c5103028a04f09, 0x828004e030280004]

def largeWord172 : Nat := packCertificateWords [0x30280002009fcea, 0x2068944202031f8, 0xfa02031f000100e0, 0xe810020e06cf6060, 0x5100000605000780, 0x23d0280079020200, 0x2063c028ee1a0202, 0x202031d8ea0605, 0x8a02030280006, 0x51100004041d0e6, 0x2021c8e202178b0, 0xe00637828dc1a020, 0x3c140604028da100, 0x2020020404004d80, 0x203000d60211820c, 0x80609044d4020302, 0x8d24f340b0143b05, 0x10c0067330101065]

def largeWord173 : Nat := packCertificateWords [0x101010014a00838, 0x411084040404005, 0x26020315c1400030, 0xed24080504038040, 0x4100041c0d820020, 0x20202002911d8101, 0x490478080c04089c, 0x40404470211a0242, 0x18581101010108c, 0x87036081090004, 0x60522c000203028, 0x6800010181458001, 0x3c262c1282808084, 0x51cd128802020020, 0x2438200202022181, 0x61da141484030e, 0xc228302020028203, 0x2800061d8950280]

def largeWord174 : Nat := packCertificateWords [0x30b014a50e01010, 0x21158080c7e521d4, 0x4060526c0002030, 0x2886000202042a31, 0xe21034040402944a, 0x104228e6061d8201, 0x4a001018149f0000, 0x8080800a28040605, 0xac1a030a4100a, 0x1010109e3981010, 0x10a8080c0a3f9d5, 0x83b022741402032, 0x704a9b0d01934080, 0x501876084c828049, 0x80225c1006160280, 0x4501018580a0025, 0x808084a9cc0c2c05, 0x1100002030b10a0a]

def largeWord175 : Nat := packCertificateWords [0x201fcea020302800, 0x7301070080f0c808, 0x80800ac80404040, 0x5461a58810100a1, 0x801858b0050095e0, 0x6050009e02030280, 0x20302800900106, 0xc10010d018100a57, 0x2b4040404004041c, 0x2021581a0202156, 0xa42018762505018, 0x147f3a8f0041b020, 0x2002023d028fe750, 0x3010100a550080c0, 0xa002a5501a020204, 0x210030b04a0a0d01, 0x100a538c05e0616, 0x29081a022981402]

def largeWord176 : Nat := packCertificateWords [0xf008080800b0410, 0x8a601cd7e5901018, 0x14000e01042400f0, 0x8080800af804040, 0x7820021c02020022, 0xb032f40808050083, 0x8040780438041087, 0x878065e010100a0d, 0x185825050680c04, 0x42ec042f1602974, 0x1c0203c424002020, 0x42010aae40406050, 0x4b80202002020, 0x30344a0a01018582, 0x530870080f108f00, 0x42f162dc1404452d, 0x8e6b50101858b405, 0x2cc0808052540c0a]

def largeWord177 : Nat := packCertificateWords [0x4081826a10882034, 0x404084780202021, 0x9a01010b00808008, 0x80c0a6600034060, 0x206596020202002c, 0xa41018147f3a8184, 0xa0a0011434066481, 0x14025c021907301, 0x184a0a000184a0a, 0x2200020020202002, 0x663810100a01019, 0x8c25050700808109, 0x798a1a6202014301, 0x78b01430030b0140, 0x30ec0808618083, 0x6081080404040400, 0x43c020510c000203, 0x2800c2010700801]

def largeWord178 : Nat := packCertificateWords [0xb5c04060982800, 0x20202042d601070, 0x8086aa103404050, 0x64040605001961a0, 0x302014d401070360, 0xf0400808010f0083, 0x40404004380410ad, 0x96a06160ec14000d, 0x180811040080c0a, 0x34da4020302800, 0x2030b04a6b01018, 0x1400228080c99050, 0x4060511000060, 0x2021a20a33b40080, 0x8050101001158080, 0x80800b3c0c040402, 0x99c0217818581101, 0x101e0101018080f]

def largeWord179 : Nat := packCertificateWords [0x40085e2c0539860, 0x61282800e51d810, 0x100a720180811040, 0x403804040840c3b0, 0x4029c6e20e010102, 0x10101042010f0083, 0x81b0781876e10402, 0x8040670028fe1a6f, 0x810100a0d3780808, 0x50101021008ac0c, 0x405375b8020203c, 0x42010d01808a66d8, 0x80c2c1282838081, 0xb017e0616094144, 0x408008381b040187, 0x608050580c3b0882, 0x140604029b4d903, 0xb04a0a6c0080808]

def largeWord180 : Nat := packCertificateWords [0xe06c1e210101814, 0x7b818f00a3aaa4, 0x4067b028003b020, 0x2014f57a07008081, 0x8703404040840c3, 0xb798201402020200, 0x2f2030ec080a7880, 0x8080800bc0040404, 0x58002020204a01, 0x77818762505009dc, 0xa3f9d40406050d4, 0xeaed020211491010, 0x21d8eb39819d4040, 0x4028048a3f9d4e60, 0x6160941440010101, 0x8a7480950130203, 0xc042803028000202, 0x2002e80d01808e7]

def largeWord181 : Nat := packCertificateWords [0x541434040402a08, 0x2032981400030ee, 0x608050180811041, 0x4060540a02020, 0x31bc14008004c080, 0x80501814503f9d40, 0x41c02020c806051f, 0xcea6e0306c100a22, 0x9fe2c128280498, 0x202042060202014, 0xfe0107036210f018, 0x7604053f40c2c050, 0xdc060203c14fc0, 0x107008087d819f40, 0x4043e40468030b01, 0x4790e0101021030e, 0xd340805018762505, 0x40604029f002]

def largeWord182 : Nat := packCertificateWords [0x107008541086808, 0x800810110f0510c, 0xc0a001140c0a220, 0x38040443842960, 0x1010100103010100, 0xa868083808108580, 0xd0c0202014025401, 0x8080f010bc580a21, 0x8680808858280406, 0x85028000202084e2, 0x940d0101e0a01070, 0x427f3a8400808008, 0x80d090203c0c3b0, 0x402a100202134100, 0x101070080c040080, 0xc0a811d60e040422, 0x926020202002bf03, 0x10100a8304c080f]

def largeWord183 : Nat := packCertificateWords [0xd0101490178b04a, 0xa228080c0a00140, 0x760404228e6028b8, 0xb04a0a0101046080, 0x8080c0a001b804a, 0x80203c04ef8b0941, 0x515030b04a0a4206, 0x8089d05018080805, 0x450041c040042c02, 0x301023130d01014, 0x9047868080810864, 0x3808109002c06050, 0xa075010184a0a1, 0xc07010210b0f0051, 0x20422a220404004e, 0x6150101814200001, 0x877100402804061b, 0x280002420181400]

def largeWord184 : Nat := packCertificateWords [0x40840c3b0409414, 0x20202002b503480, 0x808050080c04078, 0x4404ef0302800020, 0x3270140001018148, 0xa00018080f0547d5, 0x602020b0020408, 0x4021601070582510, 0x818580a222e83404, 0x408528060247810, 0xa010184c110401a, 0x3a0404028381a0d8, 0x204202034704a0a0, 0x101010018d818582, 0x5051b8041c040863, 0x4020e02043190101, 0x1e0a8c040381b04, 0x840406051fcfa84]

def largeWord185 : Nat := packCertificateWords [0x50080d0a051fcea, 0x1a03010100a10808, 0x3804040843c02030, 0x1254080500908040, 0x40292a0203248100, 0xa3f8080c04948080, 0x80f052280c3b0202, 0x15280d018080805, 0x49c041c0202042c1, 0x101809260402804, 0x6051fceb2503010, 0x100a224900406020, 0x44112301071ec040, 0x4028040602488100, 0xa010185825051140, 0x41c0202042be0d01, 0x8080805484040616, 0x94144401070080f]

def largeWord186 : Nat := packCertificateWords [0x12100c0a3f9d404, 0x1c0203c420202021, 0x1475398080c04533, 0x6e4602030b0080f0, 0x50083804040859a0, 0x202020028a010705, 0x8040408404044702, 0x152e968080c0a3f, 0x9d40c3b0202014cb, 0x30114c080511020, 0x20e010102101018, 0x112c0538c0406020, 0x3d680a0101876080, 0x538c040604264147, 0xf0e0180808051100, 0x4061602800020304, 0xc5825053140c0404, 0x2888020301010e0]

def largeWord187 : Nat := packCertificateWords [0x202042d70101808, 0xc040280406044c1, 0xc6020402a6602030, 0x28fea43a80808084, 0x51cde40203022600, 0x20e0101021388680, 0xc0404029b4061d81, 0x1420805008380410, 0x878041c0d0101021, 0x1010108a601cc38, 0x602020144001018, 0x80f4e8280404040, 0x9514730101822086, 0x187604040297e0, 0x202020148a480187, 0x6040402a5e020e01, 0x102167a10340404, 0x2804061b028fe75]

def largeWord188 : Nat := packCertificateWords [0x101808a6042340c, 0x40402880e301011, 0x1c08052280406024, 0xe0100a0101011374, 0x51ce001a03010100, 0xa034c80808051103, 0x40602020147f0d01, 0x808c404028040404, 0x4d81443014580808, 0x51cc04060203c14, 0x9001018260408821, 0x806020201444010, 0x1808110432c0c040, 0x4028808f01018582, 0x5054d40404042299, 0x73010180808054d, 0x4040402920a351, 0x8380404084041c]

def largeWord189 : Nat := packCertificateWords [0xe0101025108080c, 0x407828ea0202021, 0x1495398080c04040, 0x8598024c01808110, 0x4500040404228e60, 0x20e01010213a8680, 0xc040402a7e020228, 0x4108a398680c0404, 0x292202020211473, 0x9f0080c250500004, 0x69e010100a01019, 0x4211044ec3406020, 0x201402030101e0a8, 0x818080805084880, 0x203010100a9d0080, 0xc045084410020302, 0x8fe759c818080805, 0x1124e02030280075]

def largeWord190 : Nat := packCertificateWords [0x3980838040451814, 0x2030b04a0a92808, 0xc040782a04061d8, 0x114c08050080d450, 0x2020140602020149, 0x55b0080c04818201, 0x41c030ec08080500, 0x80c040402a881a03, 0x10100a453140c3b, 0x202014020301010, 0xa350080c0407829, 0x80020302015430b0, 0x80c0407a3814060, 0x2020144435008380, 0x404085e142030101, 0xa5b0080c040789, 0x414020e010102160, 0x83804040868202]

def largeWord191 : Nat := packCertificateWords [0x34f408a60501876, 0x40402a62061d810, 0x100aa63b40404042, 0x28e602098101e080, 0x5018760404029c60, 0x61d810100a6d8096, 0x6040402914061d81, 0x114b05018080805, 0x112948409810100a, 0x5b0185825051140c, 0x2c12828880203010, 0x100aa48080c0408c, 0x88100203010100aa, 0x40080c040426d140, 0x203028fe75a38180, 0x8080510032020304, 0x4100a3f8080c0404, 0x2a5c02020201443]

def largeWord192 : Nat := packCertificateWords [0x2022a08a3987034, 0x404084040605000, 0xfe7503010100a201, 0xfc0c3b02020154f0, 0x10181a04040280c3, 0xb99010100a010101, 0xa008180808051f, 0xc780202298108a39, 0x8a83406020201484, 0x30ec08080500838, 0x404229200203029, 0x147f3a8080c04078, 0x2a0a100e01010210, 0x101808a608822800, 0x20e0101021015380, 0xc040402834060202, 0x1433030ec100a71, 0x8080c040402a9a02]

def largeWord193 : Nat := packCertificateWords [0x48008095604228e6, 0x20e010460810808, 0xc0a1a1fcea1a030, 0x10100a398080c040, 0x4554140203010220, 0x890d50041c020204, 0x20203028fe751980, 0x8095304228e6061d, 0x810100a0c8180808, 0x5102a4020202114, 0xe339809080602044, 0x100203010100aa88, 0x18760404029f2020, 0x202114738d8080c0, 0x4042299802020229, 0x68a3980808e10422, 0x8e60202020152e53, 0x8187604040284202]

def largeWord194 : Nat := packCertificateWords [0x500838040452c42, 0x202021560a45008, 0xc0a3f9d55202030, 0x4808080500808084, 0x5064e60217818582, 0x5050680c0404028e, 0xa020302800020e02, 0x421601018580805, 0x580406020280002, 0x34f4080a0c8080c, 0x2c0882014020e010, 0x1018108080c04040, 0x2ab2020e01010210, 0xb0080c04044d8140, 0x203010100aac2a03, 0x4060202014020301, 0x115705008080845, 0x3ace61c0d010100a]

def largeWord195 : Nat := packCertificateWords [0x20201444398080c, 0x4078296c0203011, 0x8811040083804040, 0x856c027781858250, 0x50080c9c16094140, 0x2030b04a0a450080, 0x808451ce22020202, 0x1152e39808380407, 0x8280406ae810100a, 0x10185825055700c, 0x3b02020153f0d018, 0x95b040280c2c040, 0x29c64501018080f0, 0x538c340404028e60, 0x203010100aad0080, 0xc0407d2c14025781, 0x8147f3a93c040605, 0x1fcea02030b04ab0]

def largeWord196 : Nat := packCertificateWords [0x402804060202014, 0x7f658080c04051fc, 0xea020e0180808050, 0x80c041182014020, 0x30114d2901018080, 0x80558c042c020211, 0x4730304c0808054b, 0xc0c3b02020149003, 0xec08084e8280406, 0x2022c40a0101808, 0x8055840c2c1d810, 0x100a0101ac004040, 0x28040602044108a0, 0x10185825050cc040, 0x60882014c00157c0, 0xc0a3f9d404040457, 0x91473010bc582505, 0x80c2c128280006]

def largeWord197 : Nat := packCertificateWords [0x51cc04060254c10, 0xa0101a64040402a, 0x4a0203010100a718, 0x1808080511004060, 0x2384100a01018080, 0x8a80280404040291, 0x47301018100a0b00, 0x8080805229200203, 0x10100a453000406, 0x20204a0a450080c, 0x404060140203010, 0x100a0b0080c04040, 0x2aca020301022080, 0x500ac80404028040, 0x602298100a718080, 0xc040402914750101, 0x8260404028fe0203, 0x28fe750101808a6]

def largeWord198 : Nat := packCertificateWords [0x457814061d81010, 0xa010180808b3828, 0x56603010100a010, 0x185825050080c040, 0x4094147301018080, 0x8054b80406020201, 0x475398080c045302, 0x147f0101808c453, 0x201402030120608, 0x500838060202014, 0x7f01018091304028, 0x40602298100a970, 0x80c040402842024, 0x20180808052d8040, 0x60229a0608050080, 0xc04ab02014020301, 0x10ab050080c0404, 0x2a3002030b00808]

def largeWord199 : Nat := packCertificateWords [0x20201402034c811, 0x31010700c2c02020, 0x1402030114cdb010, 0x180808052296c060, 0x2020156901018360, 0x8050080c08053500, 0x40602020148a7180, 0x80c0404594040602, 0x44100203010114b, 0x522804069902014, 0x7f010180808b4028, 0x4060202014b63f8, 0x80c040cb2c042f0, 0x3010100a01315880, 0x805008100a93c840, 0x48403010100a3f80, 0x80c0495820140203, 0x4f40808050080c04]

def largeWord200 : Nat := packCertificateWords [0x536c04060202014, 0x8f0101808a604028, 0x41c03010100a013, 0x140c040402804069, 0x9284100a01018273, 0x2020201402030101, 0xa978080c040409, 0x414212c8080d3202, 0x20140203021c73f, 0x10700c040422804, 0x616010100a10808, 0xc0404029c690010, 0x1ad6040402acc060, 0x2020140203010100, 0xa451fc0406020201, 0x4710101a24040402, 0x8040404028428a01, 0x1858080538ed406]

def largeWord201 : Nat := packCertificateWords [0x80c040402804, 0x602020147301018, 0x808051fc0406023, 0x10100a0101808080, 0x5064040602020142, 0x1010180808054840, 0x48403010100a0101, 0x80808054c4040602, 0x2014e3010180808]

def largeWord202 : Nat := packCertificateWords [0x48c01e600c30, 0x498018c00660003]

def largeWord203 : Nat := packCertificateWords [0x88a043502128105, 0x4080a03f501f280f, 0x54078a03b501d280, 0xe54070a037501b28, 0xd54068a03350192, 0x80c54060a02f5017, 0x280b54058a02b501, 0x5280a54050a02750, 0x13280954048a0235, 0x11280854040a01f, 0x500f280754038a01, 0xb500d280654030a0, 0x17500b280554028a, 0x135009280454020, 0xa00f500728035401, 0x8a00b50052802540, 0x10a0075003280154]

def largeWord204 : Nat := packCertificateWords [0x108a083504128205, 0x4100a07f503f281f, 0x540f8a07b503d281, 0xe540f0a077503b28, 0x1d540e8a07350392, 0x81c540e0a06f5037, 0x281b540d8a06b503, 0x5281a540d0a06750, 0x332819540c8a0635, 0x312818540c0a05f, 0x502f2817540b8a05, 0xb502d2816540b0a0, 0x57502b2815540a8a, 0x5350292814540a0, 0xa04f502728135409, 0x8a04b50252812540, 0x90a0475023281154]

def largeWord205 : Nat := packCertificateWords [0x1ad28d5546a0a34c, 0x41a3a8d09467aa33, 0x85199a8cb94652a3, 0x24518fa8c69462aa, 0x3105185a8c194602, 0xa2fc517ba8bc945d, 0xaa2e85171a8b7945, 0xb2a2d45167a8b294, 0x58aa2c0515da8add, 0x564a2ad515428a8, 0xd453ca299514a28a, 0x3d4514a285514028, 0x9ed44eca27151362, 0x899d44c4a25d512c, 0x2894d449ca249512, 0x2288fd4474a23551, 0x18288ad444ca2215]

def largeWord206 : Nat := packCertificateWords [0x24ba1249491aa488, 0x5242211fd48f4a47, 0x55238291ad48cca4, 0x61522e2915d48a4a, 0x44d52242910d487c, 0xa439521a290bd485, 0x4a4255210a107148, 0x2ea4125206a90250, 0x808a3ff51fd28fd5, 0x47e0a3eb51f328f8, 0x547b8a3d751e928f, 0x354790a3c351df28, 0xee54768a3af51d52, 0x8e954740a39b51cb, 0x28e454718a38751c, 0x128df546f0a37351, 0xb728da546c8a35f5]

def largeWord207 : Nat := packCertificateWords [0x2ea2973d4b94a5c5, 0x52e0296ed4b6ca5b, 0x152d62969d4b44a5, 0x9d52cc2964d4b1ca, 0x58952c2295fd4af4, 0xa57552b8295ad4ac, 0xca56152ae2955d4a, 0xa6854e52a4a95114, 0xa7ea53a529aa94c1, 0x4a56a5265290a947, 0x14a2ea5125286a94, 0x214a06a4fe527ca9, 0x3d149dea4ea5272a, 0x938149b6a4d74269, 0x293354990a4c3525, 0xf292e54968a4af52, 0x55292954940a49b5]

def largeWord208 : Nat := packCertificateWords [0x387a9c294e0aa700, 0x537da9bdd0de4a6e, 0xe437521b954dc0a6, 0xdb536b29b454d98a, 0x6c7536129af54d70, 0xa6b44357a9aad0d4, 0xca6a1534e29a5d4d, 0x24a68d534429a0d4, 0xcfca679533a299bd, 0x4cd4a66553302996, 0xd4caca6515326299, 0x1d4c84a63d531c29, 0x8cd4c5ca62953122, 0x987d4c34a6155308, 0x2982d4c0ca60152f, 0xe297dd4be4a5ed52, 0xf42978d4bbca5d95]

def largeWord209 : Nat := packCertificateWords [0xfe8, 0xa7ef53f529f954fc, 0xa7db53eb29f454f, 0x98a7c753e129ef54, 0xf70a7b353d729ea5, 0x4f48a79f53cd29e5, 0x54f20a78b53c329e, 0x54ef8a77753b929, 0xdb54ed0a76353af2, 0x9d690eaaa75053a5, 0xa9d194e82a73c539, 0xba9cc94e5aa72853, 0x91a9c794e32a7145]

def largeWord210 : Nat := packCertificateWords [0x4b3b258592ba8957, 0x64a8b252d928ca94, 0x649d324d1925cc9, 0x286491aa475922ec, 0x9116485b24195200, 0xc8fa647aaa3bd91d, 0x2c8e3646eb236151, 0xa4c8cc6463323019, 0x174c8b46457322a1, 0x9144c89c644b3224, 0x55116c885643fb21, 0xe590e6c86d6433b2, 0x18590b6c85744292, 0xa131908cc840641d, 0x320d1905cc828641, 0x132071902cc81064, 0x5320118ffcc7f95]

def largeWord211 : Nat := packCertificateWords [0x570b2b6d95aacacf, 0x6564b2b0d957acab, 0x76558b2aad954aca, 0x9f654cb2a4d951ac, 0xa876540b29ed94ea, 0xca6f6534b298d94b, 0xaca576528b292d94, 0x8aca3f651d2a8d19, 0x45eaa296511b2875, 0x942eca116505b281, 0x59400a9fa64fa327, 0xb993d0c9e264ee32, 0x75993a0c9ca64e23, 0x26f99370c9b264d6, 0x326999340c99a64c, 0xa326399310c98264, 0xbe325d992e2a96d4]

def largeWord212 : Nat := packCertificateWords [0x62db3155989ecc49, 0x6621b30f5986ecc3, 0x16615b3095983ecc, 0x196609b3035980ec, 0xc0165fdb2fd957e0, 0xcbea65f232f7997b, 0xcbd355e6b2f1d97, 0x82cbbb65dab2ebd9, 0x752cba455cf32e61, 0x9724cb8c65c3aae0, 0x596f6cb7565b7b2d, 0xa596c6cb5d65abb2, 0xd459696cb45659fb, 0x2ce9566aab2f6594, 0xb2c8d963acb17658, 0x8b2c2d960acaff65, 0x7cb2bcd95dacae76]

def largeWord213 : Nat := packCertificateWords [0x6ea337399b90cdc2, 0x66de336d99b60cda, 0xa66d2336799b30cd, 0x9266c63361d5b02c, 0xd7b66bab35bd9ad2, 0xcd6366aeb355d9aa, 0x2cd4b66a32b5019a, 0x74cd346697334a19, 0xa44cd1d568bb3445, 0x9a16cd05667fb33e, 0x599e6cced6673b33, 0x8599b6ccd56668a3, 0x331598cccc1565db, 0x32d5995ecca96651, 0xb3275992ecc91664, 0x5b321598fecc7966, 0x39b31b598cecc616]

def largeWord214 : Nat := packCertificateWords [0x7b2bbd815eb6af56, 0x57a7bbd295e8aaf3, 0xe779c33cc99e56ef, 0x26579033c6d5e2ca, 0xf0f7784b3c0d9dfa, 0xcef8577933bb19dc, 0xeaee0776d33b4ddd, 0x98eec5775fb3ae1d, 0xd64ceab7752b3a79, 0xdd2eee916745b3a1, 0x59cfcee786738bb9, 0xad9cccae60672d33, 0x9519c9eae4967213, 0xb8eddc6ace2f6714, 0xb388d9c3cae17770, 0x83b825dc08adfe66, 0xfbbb7c59bd6cde56]

def largeWord215 : Nat := packCertificateWords [0x7f033, 0xf65dfa6cfcc77e2b, 0xbf015f74cfb377d6, 0x3be999f42af9a77c, 0xa33e399f10cf8267, 0xbeabde15ee2ef6c5]

def largeWord216 : Nat := packCertificateWords [0x2068d02e6814, 0x34089a038d016680, 0x834029a008cffe67, 0xfc33fc99fd8cfe66]

def largeWord217 : Nat := packCertificateWords [0x302801070030295, 0x821030290302850, 0x8210107002021030, 0x2b0302a040850302, 0x8030290329a451cd, 0x30280302b0302a0, 0x302b0302a0302b03, 0x2a5082103029030, 0x2803029030280107, 0x30290302803029, 0x107003029030284, 0x51cd030290302b03, 0x2a0107003029030, 0x28010700302b0302, 0xa030290302b0302a, 0x202002021030280, 0x1070030290302803, 0x290302801070030, 0x2b0302a010700302, 0xb0302a0302b0302a]

def largeWord218 : Nat := packCertificateWords [0x3013030120302b0, 0x302a994c70202902, 0x280302903028030, 0x2b0302a020210302, 0x802028030280302b, 0x302a03028030290, 0x3029030280202901, 0x700302904085030, 0x2803029030280302, 0xb0302a0302902021, 0x3028032980229b0, 0x4029030280302903, 0x280302904085030, 0x280302b030280202, 0x302a0202001070, 0x3029014ac020284, 0x2010030210302b53, 0x36f0402804029020, 0x2301070030290302, 0x8030280302803029]

def largeWord219 : Nat := packCertificateWords [0x302803029030280, 0x1023020290408503, 0x280302903028030, 0x29030280302b0302, 0xa02020030290302b, 0x302a03022010700, 0x30290302b0302a01, 0x709e82962029030, 0x1001010030280302, 0x803028030280438d, 0x202b04029030230, 0x2298040290302b03, 0x2b0302a03029030, 0x2801070040590302, 0x80202b0408503028, 0x3028030280202a0, 0x3028160870202103, 0x280302303029030, 0x2903028128850202, 0x30280302393c85]

def largeWord220 : Nat := packCertificateWords [0x208703028030290, 0x202201070021c70e, 0x230302903028030, 0x2903028030290302, 0x80302b0302a02023, 0x302b0302a0229b0, 0x302803029030280e, 0xb00202103029020, 0x2204085030280302, 0x9030280302803029, 0x302803029010b00, 0x30290344f0438d02, 0x2b0402903010030, 0x2b0302a040850302, 0x803029098110302b, 0x302801018020290, 0x302802022118210e, 0x10030290302b030, 0x2802023010700302, 0x8040850302803028]

def largeWord221 : Nat := packCertificateWords [0x202202087030280, 0x202b0302b0302b03, 0x280302b0e020030, 0x2902087030280408, 0x7030280408503028, 0x4029020230302a0, 0x302b0402a0302b03, 0x2b0302b0e010030, 0x295336f040280402, 0x9030290302b0302a, 0x302a02021030290, 0x40850302b0302a04, 0x850302803028030, 0x2903028020210107, 0x30230202201070, 0x408503028030290, 0x30280232f0402a03, 0x2b0302b02022010, 0x7002021020870302, 0x80302b0302804059]

def largeWord222 : Nat := packCertificateWords [0x302904028040290, 0x302b040280208503, 0x280236f04028030, 0x28030280302b0202, 0x90302b0338f0202b, 0x302b02085030280, 0x3011030100301303, 0x120302b044c5020, 0x2862029030100302, 0xb04485030120202a, 0x20200302a0302b0, 0x20220302a0302b04, 0x290229804029043, 0x8d0202b0229b0302, 0xb010230202904029, 0x302b030670402a0, 0xe013030290202103, 0x2a041cd0302a020, 0x290202903028021c, 0xf0302a041cf0302a]

def largeWord223 : Nat := packCertificateWords [0x302a0302b030, 0x100402a030280301, 0x202029020280202b, 0x40280202a040290, 0x3029030110202902, 0x290302b02020030, 0x2802029030230302, 0xb020210302803023, 0x202b020290202a0, 0x302b0e0230302902, 0x1cd0302a0302b030, 0x2303029013140301, 0x1020290202802021]

def largeWord224 : Nat := packCertificateWords [0xd3000000018200, 0x51000000000004, 0x101c40a400000000, 0x0, 0x1040000, 0x440000, 0x0, 0x0, 0x0, 0x2]

def largeWord225 : Nat := packCertificateWords [0x65, 0x181000000000, 0x0, 0x2c415100, 0x0, 0x4c80, 0x0, 0x2420000, 0x0, 0x0, 0x2040000000000000, 0x0]

def largeWord226 : Nat := packCertificateWords [0x16a, 0x159000, 0xa4850, 0x2000000000000000, 0x4c400012, 0x1000000000000000, 0x4, 0x6200010900000000, 0x10080000000000, 0x1f10000, 0x748, 0x0, 0x0]

def largeWord227 : Nat := packCertificateWords [0xe8, 0x8000000000000072, 0x2000000000000037, 0x2000000000000000, 0x35200000, 0x66400000000000, 0x0, 0x0, 0x0, 0xc84, 0x3110000000000, 0x0]

def largeWord228 : Nat := packCertificateWords [0xf040000000000000, 0x0, 0x0]

def largeWord229 : Nat := packCertificateWords [0x1f08f26000000, 0x7723a91cc, 0x8e426f3370800000, 0x6d13591a4800000, 0x66332, 0x11888be65c300000, 0xb625922c095880, 0x55100000000005, 0x4129100009e60002, 0x6900009464732308, 0x8a24320000000, 0x8420000001044000, 0x3f21f080000003d1]

def largeWord230 : Nat := packCertificateWords [0x641b1c58c2000000, 0x3108000c31609300, 0x4000bf15e92ec972, 0x4b725a90000000b3, 0x258900015e400056, 0x1aa8952200000029, 0x8d48400000028c40, 0xa2100028440009, 0xe34e8a68c0009824, 0xb8a5840009514990, 0x12068f14708001, 0x184000000224d0e4, 0x852000208d0227e3]

def largeWord231 : Nat := packCertificateWords [0x7b8bd480000007a0, 0x8000000f31000000, 0x1e24f017710001da, 0x2ec10003a8800000, 0x39cc000e6100, 0x0, 0x1c84e22708b7c80, 0xde16e1364dae40, 0x3549a640006, 0x90b408000cf16690, 0x6608000, 0x0, 0xcb10000000000000]

def largeWord232 : Nat := packCertificateWords [0x90180000000008f8, 0x80023a40008e0800, 0x8d1000000, 0x8c145c62a400, 0x8a, 0x800000000089880, 0x224310200043880, 0x430a1260, 0x840c1c40010610, 0x20670210004, 0x440000000003f8c, 0xfd10000000000, 0x1f64f83]

def largeWord233 : Nat := packCertificateWords [0xbe0dec6f25772000, 0x5d86ea3741b915c0, 0xade2000b695acad2, 0x5681b31590ac6200, 0xb0958040015e2ae, 0x8d6cab43591ab900, 0x2aa5541a98d44aa, 0x34f1a6952ca9254, 0x72a30d146883422a, 0x14fc67a53b29d0c, 0xe0a6c53429914c08, 0x12f19694b04001, 0x2b1950ca46503262]

def largeWord234 : Nat := packCertificateWords [0xc, 0xd0e647303962ca8e, 0x507263912c796387, 0x1a38c1c51620b0e3, 0x852c19604afe57d2]

def largeWord235 : Nat := packCertificateWords [0x3503a71d30e947, 0x483a31d10e847403, 0x9f1cf0e7473839b1]

def largeWord236 : Nat := packCertificateWords [0x4582241, 0x1008304082000800, 0x21010007c03a01b0, 0xd006002c0140088, 0x4001e00e0068030, 0x16009004001c00a, 0x40018008002000]

def largeWord237 : Nat := packCertificateWords [0x24592289, 0x40820310004bc2, 0x4e0cf867431a18b0, 0xc3861830a1840c08, 0x46421a10c0840414, 0x202100071828013e, 0x9d04a024412008e]

def largeWord238 : Nat := packCertificateWords [0x8cbc62e3, 0x111818c044762010, 0x8f846c2020330114, 0xde267531490d450a, 0x8100a8044001aa8, 0xb1e58b2c4940097a, 0x4ab250127c93a492]

def largeWord239 : Nat := packCertificateWords [0x56fe, 0xb5f5abacdd65eb01, 0x51d8cfc676337198]

def largeWord240 : Nat := packCertificateWords [0x200, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]

def largeWord241 : Nat := packCertificateWords [0x438000080000008, 0x400700000000800, 0x84000000, 0x4000000408040040, 0x8001000808b80000, 0x202001000004000, 0x8000000000438000, 0x4000800000, 0x10000, 0x3800200000021c08, 0x14080000, 0x1c0000000080003, 0x8707000000400000, 0x102000000001]

def largeWord242 : Nat := packCertificateWords [0x83800000, 0x40000800c800000, 0x7070010200040000, 0x1320008000000000, 0x100000000001, 0x100001c5c0, 0x1a08000000038000, 0xe00219060000002, 0x100000004c800400, 0x80021020, 0x200103800, 0x2000002e00000000, 0x807000000400040, 0x0]

def largeWord243 : Nat := packCertificateWords [0xc800000000000020, 0x3800000080070, 0x107000800000000, 0x6400004002, 0x4002000008380]

def largeWord244 : Nat := packCertificateWords [0x5204d000048c9702, 0xa02170a0d2010a00, 0x14200080120438, 0x700aa180013801a0, 0x12c0080e24005032, 0xc00498002972e003, 0x8140811caa89c, 0x20e0e000020102, 0x1820d4c002171e4c, 0x800d150a1478, 0x30000b8134540460, 0x4b5600a044c0, 0x111c18002010000b, 0x80005c0052000217]

def largeWord245 : Nat := packCertificateWords [0x2380003400c001c, 0x2000000268, 0x800000384700000, 0x140038700040000, 0x4f005e1c010001, 0x14e500e870008a80, 0x100107041c0091c, 0x34040072e6403a00, 0x40e021c1560e3c, 0x4039000000, 0x80008174047017, 0xaa560000040802e0, 0x401736000002e000, 0xe000042000000]

def largeWord246 : Nat := packCertificateWords [0x20, 0x69c903442d864060, 0x304b882bebf72a1f, 0x2febc7232a181c0, 0xa67bec7718a3d140, 0x80cd9c02e54f0eb, 0x2903af02549edb7d, 0x36aaa402a673682e, 0x56a0025a1351715f, 0x5d773406a3b67237]

def largeWord247 : Nat := packCertificateWords [0xad267105, 0xdfc2d2f3fcefcb5f]

def dom_7:=0xff
def roots_7:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0]
def dom_11:=0xf0f
def roots_11:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 3 0]
def dom_13:=0x3333
def roots_13:List Nat:=[xs256.getD 0 0,xs256.getD 2 0,xs256.getD 3 0]
def dom_14:=0x5555
def roots_14:List Nat:=[xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0]
def dom_15:=0xffff
def roots_15:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0]
def dom_22:=0x550055
def roots_22:List Nat:=[xs256.getD 1 0,xs256.getD 2 0,xs256.getD 4 0]
def dom_23:=0xff00ff
def roots_23:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 4 0]
def dom_25:=0x3030303
def roots_25:List Nat:=[xs256.getD 0 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_27:=0xf0f0f0f
def roots_27:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_29:=0x33333333
def roots_29:List Nat:=[xs256.getD 0 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_30:=0x55555555
def roots_30:List Nat:=[xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_31:=0xffffffff
def roots_31:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_38:=0x5500000055
def roots_38:List Nat:=[xs256.getD 1 0,xs256.getD 2 0,xs256.getD 5 0]
def dom_39:=0xff000000ff
def roots_39:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 5 0]
def roots_41:List Nat:=[xs256.getD 0 0,xs256.getD 3 0,xs256.getD 5 0]
def dom_42:=0x50500000505
def roots_42:List Nat:=[xs256.getD 1 0,xs256.getD 3 0,xs256.getD 5 0]
def dom_43:=0xf0f00000f0f
def roots_43:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 3 0,xs256.getD 5 0]
def roots_45:List Nat:=[xs256.getD 0 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 5 0]
def dom_49:=0x3000300030003
def roots_49:List Nat:=[xs256.getD 0 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_51:=0xf000f000f000f
def roots_51:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_53:=0x33003300330033
def roots_53:List Nat:=[xs256.getD 0 0,xs256.getD 2 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_54:=0x55005500550055
def roots_54:List Nat:=[xs256.getD 1 0,xs256.getD 2 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_55:=0xff00ff00ff00ff
def roots_55:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 4 0,xs256.getD 5 0]
def roots_57:List Nat:=[xs256.getD 0 0,xs256.getD 3 0,xs256.getD 4 0,xs256.getD 5 0]
def roots_58:List Nat:=[xs256.getD 1 0,xs256.getD 3 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_59:=0xf0f0f0f0f0f0f0f
def dom_61:=0x3333333333333333
def dom_62:=0x5555555555555555
def goal_7_48:=0xe8
def goal_11_48:=0xe08
def goal_13_48:=0x3220
def goal_14_48:=0x5440
def goal_15_16:=0xeae0
def goal_15_48:=0xfee8
def goal_22_40:=0x540040
def goal_23_8:=0xea00c8
def goal_23_32:=0xe800c8
def goal_23_40:=0xfe00ea
def goal_25_36:=0x3020200
def goal_27_32:=0xe080a08
def goal_27_36:=0xf0e0e0c
def goal_29_32:=0x32202200
def goal_30_32:=0x54404040
def goal_31_32:=0xfee8eac8
def goal_38_24:=0x5400000040
def goal_39_8:=0xea000000c8
def goal_39_24:=0xfe000000ea
def goal_42_1:=0x50400000400
def goal_43_0:=0xa0800000800
def goal_49_12:=0x3000200020000
def goal_51_8:=0xe000a000a0008
def goal_51_12:=0xf000e000e000c
def goal_53_8:=0x32002200220000
def goal_54_8:=0x54004000400040
def goal_55_8:=0xfe00ea00ea00c8
def goal_59_0:=0xe080a080a000800
def goal_61_0:=0x3220220022200000
def goal_62_0:=0x5440404040404040
namespace S_51_8
def pairsG:List (Nat × Nat):=[(1,3),(1,17),(1,33),(2,3),(16,17),(18,19),(18,50),(32,33),(34,35),(34,50),(48,49),(48,50)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_51.map (· &&& dom_51)
def goalM:Nat:=goal_51_8 &&& dom_51
def NN:Nat → Nat
|2=>2
|3=>11
|4=>8
|5=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>0x4bea8e87009cbb69
|3,0=>(OfNat.ofNat largeWord0)
|4,0=>(OfNat.ofNat largeWord1)
|5,0=>0x29c5ac2a
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>(OfNat.ofNat largeWord2)
|_,_=>0
def stPool:Nat → Nat
|0=>(OfNat.ofNat largeWord3)
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>0x19803
|3,0=>(OfNat.ofNat largeWord4)
|4,0=>(OfNat.ofNat largeWord5)
|5,0=>0x594
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 24 then fld (dictB (i / 512) (i / 32 % 16)) 52 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 5 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 11 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 12 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 31),wireSAt ((code >>> 7) &&& 31))::readOps n (p+1)
def mkPools (_ _:Nat):List (Nat × Nat × (Nat × List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat × Nat × Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_51 goalM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_51 goalM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat × Nat)):=[[((OfNat.ofNat largeWord6),16)],[((OfNat.ofNat largeWord7),14)],[((OfNat.ofNat largeWord8),30)],[((OfNat.ofNat largeWord6),16),((OfNat.ofNat largeWord8),30)],[((OfNat.ofNat largeWord6),16),((OfNat.ofNat largeWord7),14)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_51==dom_51) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_51 goalM v ys):RunD true dom_51 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_51 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 2 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 2 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 11 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 11 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4:∀ i,0 ≤ i → i < 8 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 8 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5:∀ i,0 ≤ i → i < 1 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 5):∀ i < NN s,bar true dom_51 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_51 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 3 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 5) (h:RunD true dom_51 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_51 roots_51 goal_51_8 6:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_51_8
theorem lowS_51_8:Lower true dom_51 roots_51 goal_51_8 6:=S_51_8.noCircuit
namespace S_42_1
def pairsG:List (Nat × Nat):=[(2,10),(2,34),(8,10),(8,40),(32,34),(32,40)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x3f
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_42.map (· &&& dom_42)
def goalM:Nat:=goal_42_1 &&& dom_42
def NN:Nat → Nat
|2=>1
|3=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>0x47202343
|3,0=>0x47202343
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>(OfNat.ofNat largeWord9)
|_,_=>0
def stPool:Nat → Nat
|0=>0x924
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>3
|3,0=>0x33
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 3 then fld (dictB (i / 512) (i / 32 % 16)) 43 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 2 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 7 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 6 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 3),wireSAt ((code >>> 4) &&& 3))::readOps n (p+1)
def mkPools (_ _:Nat):List (Nat × Nat × (Nat × List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat × Nat × Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_42 goalM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_42 goalM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat × Nat)):=[[((OfNat.ofNat largeWord10),24)],[((OfNat.ofNat largeWord11),6)],[((OfNat.ofNat largeWord8),30)],[((OfNat.ofNat largeWord10),24),((OfNat.ofNat largeWord8),30)],[((OfNat.ofNat largeWord10),24),((OfNat.ofNat largeWord11),6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_42==dom_42) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_42 goalM v ys):RunD true dom_42 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_42 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 1 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 1 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 1 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 3):∀ i < NN s,bar true dom_42 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_42 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 2=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 3) (h:RunD true dom_42 goalM s xsM):False:=by
  have hmin:2 ≤ s:=by have hl:=run_len h;change 3 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_42 roots_42 goal_42_1 4:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_42_1
theorem lowS_42_1:Lower true dom_42 roots_42 goal_42_1 4:=S_42_1.noCircuit
def isoMv_25_36:List (Nat × Nat):=[((OfNat.ofNat largeWord6),16),((OfNat.ofNat largeWord12),1)]
theorem lowS_25_36:Lower true dom_25 roots_25 goal_25_36 4:=lower_iso isoMv_25_36 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_42_1
def dzo_25_4:=0x30303030
def gzo_25_36_4:=0x30202000
theorem lowSh_25_36_4:Lower true dzo_25_4 roots_25 gzo_25_36_4 4:=lower_iso (d1:=dom_25) (roots1:=roots_25) (T1:=goal_25_36) [(dom_25,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_25_36
namespace S_29_32
def pairsG:List (Nat × Nat):=[(1,9),(5,13),(5,21),(8,9),(12,13),(12,28),(17,21),(17,25),(20,21),(20,28),(24,25),(24,28)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_29.map (· &&& dom_29)
def goalM:Nat:=goal_29_32 &&& dom_29
def NN:Nat → Nat
|_=>0
def HT:Nat → Nat → Nat
|_,_=>0
def dictB:Nat → Nat → Nat
|_,_=>0
def stPool:Nat → Nat
|_=>0
def stOffB:Nat → Nat → Nat
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 0 then fld (dictB (i / 512) (i / 32 % 16)) 1 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 1 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 5 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 1 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|_=>0
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 4 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 1),wireSAt ((code >>> 3) &&& 1))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0
|_=>0
def pmB:Nat → Nat → Nat
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dzo_25_4,4,runOps true dzo_25_4 (0,roots_25) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_29 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    obtain ⟨_,rfl⟩:=he;exact cpcs (by decide +kernel) lowSh_25_36_4 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_25_4 4 s (0,roots_25) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_29 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_25_36_4 h
def symsG:List (List (Nat × Nat)):=[[((OfNat.ofNat largeWord13),12)],[((OfNat.ofNat largeWord14),7)],[((OfNat.ofNat largeWord13),12),((OfNat.ofNat largeWord14),7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_29==dom_29) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_29 goalM v ys):RunD true dom_29 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_29 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
private theorem z3:∀ i,0 ≤ i → i < 0 → Z 3 i=true:=by omega
private theorem z4:∀ i,0 ≤ i → i < 0 → Z 4 i=true:=by omega
theorem checked (s:Nat) (hs:s ≤ 4):∀ i < NN s,bar true dom_29 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_29 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 4) (h:RunD true dom_29 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_29 roots_29 goal_29_32 5:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_29_32
theorem lowS_29_32:Lower true dom_29 roots_29 goal_29_32 5:=S_29_32.noCircuit
def isoMv_54_8:List (Nat × Nat):=[((OfNat.ofNat largeWord6),16),((OfNat.ofNat largeWord10),24),((OfNat.ofNat largeWord15),4),((OfNat.ofNat largeWord12),1)]
theorem lowS_54_8:Lower true dom_54 roots_54 goal_54_8 5:=lower_iso isoMv_54_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_29_32
def isoMv_22_40:List (Nat × Nat):=[((OfNat.ofNat largeWord6),16),((OfNat.ofNat largeWord15),4)]
theorem lowS_22_40:Lower true dom_22 roots_22 goal_22_40 4:=lower_iso isoMv_22_40 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_42_1
theorem lowS_23_40:Lower true dom_23 roots_23 goal_23_40 5:=lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xaa00aa,0,1)] (by decide +kernel) (by decide +kernel) lowS_22_40
def isoMv_39_24:List (Nat × Nat):=[((OfNat.ofNat largeWord6),16)]
theorem lowS_39_24:Lower true dom_39 roots_39 goal_39_24 5:=lower_iso isoMv_39_24 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_23_40
def isoMv_38_24:List (Nat × Nat):=[((OfNat.ofNat largeWord15),4)]
theorem lowS_38_24:Lower true dom_38 roots_38 goal_38_24 4:=lower_iso isoMv_38_24 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_42_1
def isoMv_49_12:List (Nat × Nat):=[((OfNat.ofNat largeWord16),8),((OfNat.ofNat largeWord12),1)]
theorem lowS_49_12:Lower true dom_49 roots_49 goal_49_12 4:=lower_iso isoMv_49_12 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_42_1
def isoMv_7_48:List (Nat × Nat):=[((OfNat.ofNat largeWord6),16),((OfNat.ofNat largeWord17),28),((OfNat.ofNat largeWord11),6),((OfNat.ofNat largeWord12),1)]
theorem lowS_7_48:Lower true dom_7 roots_7 goal_7_48 4:=lower_iso isoMv_7_48 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_42_1
def dzo_7_16:=0xff0000
def gzo_7_48_16:=0xe80000
theorem lowSh_7_48_16:Lower true dzo_7_16 roots_7 gzo_7_48_16 4:=lower_iso (d1:=dom_7) (roots1:=roots_7) (T1:=goal_7_48) [(dom_7,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_7_48
namespace S_23_32
def pairsG:List (Nat × Nat):=[(1,3),(2,3),(2,6),(4,6),(5,7),(5,21),(17,19),(17,21),(18,19),(18,22),(20,21),(20,22)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_23.map (· &&& dom_23)
def goalM:Nat:=goal_23_32 &&& dom_23
def NN:Nat → Nat
|_=>0
def HT:Nat → Nat → Nat
|_,_=>0
def dictB:Nat → Nat → Nat
|_,_=>0
def stPool:Nat → Nat
|_=>0
def stOffB:Nat → Nat → Nat
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 0 then fld (dictB (i / 512) (i / 32 % 16)) 1 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 1 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 5 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 1 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|_=>0
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 4 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 1),wireSAt ((code >>> 3) &&& 1))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0
|_=>0
def pmB:Nat → Nat → Nat
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dzo_7_16,4,runOps true dzo_7_16 (0,roots_7) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_23 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    obtain ⟨_,rfl⟩:=he;exact cpcs (by decide +kernel) lowSh_7_48_16 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_7_16 4 s (0,roots_7) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_23 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_7_48_16 h
def symsG:List (List (Nat × Nat)):=[[((OfNat.ofNat largeWord18),3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_23==dom_23) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_23 goalM v ys):RunD true dom_23 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_23 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
private theorem z3:∀ i,0 ≤ i → i < 0 → Z 3 i=true:=by omega
private theorem z4:∀ i,0 ≤ i → i < 0 → Z 4 i=true:=by omega
theorem checked (s:Nat) (hs:s ≤ 4):∀ i < NN s,bar true dom_23 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_23 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 4) (h:RunD true dom_23 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_23 roots_23 goal_23_32 5:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_23_32
theorem lowS_23_32:Lower true dom_23 roots_23 goal_23_32 5:=S_23_32.noCircuit
def isoMv_53_8:List (Nat × Nat):=[((OfNat.ofNat largeWord6),16),((OfNat.ofNat largeWord10),24),((OfNat.ofNat largeWord13),12),((OfNat.ofNat largeWord11),6),((OfNat.ofNat largeWord12),1)]
theorem lowS_53_8:Lower true dom_53 roots_53 goal_53_8 5:=lower_iso isoMv_53_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_23_32
namespace S_15_16
def pairsG:List (Nat × Nat):=[(1,5),(1,9),(2,6),(3,7),(3,11),(4,5),(4,6),(8,9),(10,11),(10,14),(12,13),(12,14)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_15.map (· &&& dom_15)
def goalM:Nat:=goal_15_16 &&& dom_15
def NN:Nat → Nat
|3=>1
|_=>0
def HT:Nat → Nat → Nat
|3,0=>0x57e3d3b0
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0xff00f0f0ccccaaaa
|_,_=>0
def stPool:Nat → Nat
|0=>0xe4
|_=>0
def stOffB:Nat → Nat → Nat
|3,0=>4
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 4 then fld (dictB (i / 512) (i / 32 % 16)) 16 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 2 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 7 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 6 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 3),wireSAt ((code >>> 4) &&& 3))::readOps n (p+1)
def mkPools (_ _:Nat):List (Nat × Nat × (Nat × List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat × Nat × Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_15 goalM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_15 goalM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat × Nat)):=[[((OfNat.ofNat largeWord11),6),((OfNat.ofNat largeWord18),3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_15==dom_15) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_15 goalM v ys):RunD true dom_15 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_15 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 1 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 3):∀ i < NN s,bar true dom_15 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_15 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 1 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 3) (h:RunD true dom_15 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_15 roots_15 goal_15_16 4:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_15_16
theorem lowS_15_16:Lower true dom_15 roots_15 goal_15_16 4:=S_15_16.noCircuit
def isoMv_39_8:List (Nat × Nat):=[((OfNat.ofNat largeWord6),16),((OfNat.ofNat largeWord16),8),((OfNat.ofNat largeWord19),2)]
theorem lowS_39_8:Lower true dom_39 roots_39 goal_39_8 4:=lower_iso isoMv_39_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_16
def isoMv_51_12:List (Nat × Nat):=[((OfNat.ofNat largeWord6),16),((OfNat.ofNat largeWord10),24),((OfNat.ofNat largeWord15),4),((OfNat.ofNat largeWord12),1)]
theorem lowS_51_12:Lower true dom_51 roots_51 goal_51_12 5:=lower_iso isoMv_51_12 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_23_40
def isoMv_23_8:List (Nat × Nat):=[((OfNat.ofNat largeWord16),8),((OfNat.ofNat largeWord19),2)]
theorem lowS_23_8:Lower true dom_23 roots_23 goal_23_8 4:=lower_iso isoMv_23_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_16
def dzo_39_16:=0xff000000ff0000
def gzo_39_24_16:=0xfe000000ea0000
theorem lowSh_39_24_16:Lower true dzo_39_16 roots_39 gzo_39_24_16 5:=lower_iso (d1:=dom_39) (roots1:=roots_39) (T1:=goal_39_24) [(dom_39,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_39_24
def dzo_38_16:=0x55000000550000
def gzo_38_24_16:=0x54000000400000
theorem lowSh_38_24_16:Lower true dzo_38_16 roots_38 gzo_38_24_16 4:=lower_iso (d1:=dom_38) (roots1:=roots_38) (T1:=goal_38_24) [(dom_38,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_38_24
def dzo_49_4:=0x30003000300030
def gzo_49_12_4:=0x30002000200000
theorem lowSh_49_12_4:Lower true dzo_49_4 roots_49 gzo_49_12_4 4:=lower_iso (d1:=dom_49) (roots1:=roots_49) (T1:=goal_49_12) [(dom_49,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_49_12
def dzo_22_32:=0x55005500000000
def gzo_22_40_32:=0x54004000000000
theorem lowSh_22_40_32:Lower true dzo_22_32 roots_22 gzo_22_40_32 4:=lower_iso (d1:=dom_22) (roots1:=roots_22) (T1:=goal_22_40) [(dom_22,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_22_40
def dzo_51_4:=0xf000f000f000f0
def gzo_51_12_4:=0xf000e000e000c0
theorem lowSh_51_12_4:Lower true dzo_51_4 roots_51 gzo_51_12_4 5:=lower_iso (d1:=dom_51) (roots1:=roots_51) (T1:=goal_51_12) [(dom_51,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51_12
def dzo_23_32:=0xff00ff00000000
def gzo_23_40_32:=0xfe00ea00000000
theorem lowSh_23_40_32:Lower true dzo_23_32 roots_23 gzo_23_40_32 5:=lower_iso (d1:=dom_23) (roots1:=roots_23) (T1:=goal_23_40) [(dom_23,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_23_40
namespace S_55_8
def pairsG:List (Nat × Nat):=[(1,3),(1,17),(1,33),(2,3),(2,6),(4,6),(5,7),(5,21),(5,37),(16,17),(18,19),(18,22),(18,50),(20,21),(20,22),(20,52),(32,33),(34,35),(34,38),(34,50),(36,37),(36,38),(36,52),(48,49),(48,50),(48,52)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x3ffffff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_55.map (· &&& dom_55)
def goalM:Nat:=goal_55_8 &&& dom_55
def NN:Nat → Nat
|2=>5
|3=>50
|4=>212
|5=>371
|6=>156
|7=>24
|8=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>(OfNat.ofNat largeWord20)
|3,0=>(OfNat.ofNat largeWord21)
|4,0=>(OfNat.ofNat largeWord22)
|4,1=>(OfNat.ofNat largeWord23)
|5,0=>(OfNat.ofNat largeWord24)
|5,1=>(OfNat.ofNat largeWord25)
|5,2=>(OfNat.ofNat largeWord26)
|6,0=>(OfNat.ofNat largeWord27)
|6,1=>(OfNat.ofNat largeWord28)
|7,0=>(OfNat.ofNat largeWord29)
|8,0=>0xa5e2e6eb
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>(OfNat.ofNat largeWord30)
|0,1=>(OfNat.ofNat largeWord31)
|0,2=>(OfNat.ofNat largeWord32)
|0,3=>(OfNat.ofNat largeWord33)
|0,4=>(OfNat.ofNat largeWord34)
|0,5=>(OfNat.ofNat largeWord35)
|0,6=>(OfNat.ofNat largeWord36)
|0,7=>(OfNat.ofNat largeWord37)
|0,8=>(OfNat.ofNat largeWord38)
|0,9=>(OfNat.ofNat largeWord39)
|0,10=>(OfNat.ofNat largeWord40)
|0,11=>(OfNat.ofNat largeWord41)
|_,_=>0
def stPool:Nat → Nat
|0=>(OfNat.ofNat largeWord42)
|1=>(OfNat.ofNat largeWord43)
|2=>(OfNat.ofNat largeWord44)
|3=>(OfNat.ofNat largeWord45)
|4=>(OfNat.ofNat largeWord46)
|5=>(OfNat.ofNat largeWord47)
|6=>(OfNat.ofNat largeWord48)
|7=>(OfNat.ofNat largeWord49)
|8=>(OfNat.ofNat largeWord50)
|9=>(OfNat.ofNat largeWord51)
|10=>(OfNat.ofNat largeWord52)
|11=>(OfNat.ofNat largeWord53)
|12=>(OfNat.ofNat largeWord54)
|13=>(OfNat.ofNat largeWord55)
|14=>(OfNat.ofNat largeWord56)
|15=>(OfNat.ofNat largeWord57)
|16=>(OfNat.ofNat largeWord58)
|17=>(OfNat.ofNat largeWord59)
|18=>(OfNat.ofNat largeWord60)
|19=>(OfNat.ofNat largeWord61)
|20=>(OfNat.ofNat largeWord62)
|21=>(OfNat.ofNat largeWord63)
|22=>(OfNat.ofNat largeWord64)
|23=>(OfNat.ofNat largeWord65)
|24=>(OfNat.ofNat largeWord66)
|25=>(OfNat.ofNat largeWord67)
|26=>(OfNat.ofNat largeWord68)
|27=>(OfNat.ofNat largeWord69)
|28=>(OfNat.ofNat largeWord70)
|29=>(OfNat.ofNat largeWord71)
|30=>(OfNat.ofNat largeWord72)
|31=>(OfNat.ofNat largeWord73)
|32=>(OfNat.ofNat largeWord74)
|33=>(OfNat.ofNat largeWord75)
|34=>(OfNat.ofNat largeWord76)
|35=>(OfNat.ofNat largeWord77)
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>0xc300498018c00660003
|3,0=>(OfNat.ofNat largeWord78)
|4,0=>(OfNat.ofNat largeWord79)
|4,1=>(OfNat.ofNat largeWord80)
|4,2=>(OfNat.ofNat largeWord81)
|4,3=>(OfNat.ofNat largeWord82)
|5,0=>(OfNat.ofNat largeWord83)
|5,1=>(OfNat.ofNat largeWord84)
|5,2=>(OfNat.ofNat largeWord85)
|5,3=>(OfNat.ofNat largeWord86)
|5,4=>(OfNat.ofNat largeWord87)
|5,5=>(OfNat.ofNat largeWord88)
|6,0=>(OfNat.ofNat largeWord89)
|6,1=>(OfNat.ofNat largeWord90)
|6,2=>(OfNat.ofNat largeWord91)
|7,0=>(OfNat.ofNat largeWord92)
|8,0=>0x11d45
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 355 then fld (dictB (i / 512) (i / 32 % 16)) 56 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 9 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 17 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|0=>(OfNat.ofNat largeWord93)
|1=>(OfNat.ofNat largeWord94)
|2=>(OfNat.ofNat largeWord95)
|3=>(OfNat.ofNat largeWord96)
|4=>(OfNat.ofNat largeWord97)
|5=>(OfNat.ofNat largeWord98)
|6=>(OfNat.ofNat largeWord99)
|7=>(OfNat.ofNat largeWord100)
|8=>(OfNat.ofNat largeWord101)
|9=>(OfNat.ofNat largeWord102)
|10=>(OfNat.ofNat largeWord103)
|_=>0
def opOffB:Nat → Nat → Nat
|3,0=>(OfNat.ofNat largeWord104)
|4,0=>(OfNat.ofNat largeWord105)
|4,1=>(OfNat.ofNat largeWord106)
|4,2=>(OfNat.ofNat largeWord107)
|4,3=>0x10040000000000
|5,0=>(OfNat.ofNat largeWord108)
|5,1=>(OfNat.ofNat largeWord109)
|5,2=>(OfNat.ofNat largeWord110)
|5,3=>(OfNat.ofNat largeWord111)
|5,4=>(OfNat.ofNat largeWord112)
|5,5=>(OfNat.ofNat largeWord113)
|6,0=>(OfNat.ofNat largeWord114)
|6,1=>(OfNat.ofNat largeWord115)
|6,2=>(OfNat.ofNat largeWord116)
|7,0=>(OfNat.ofNat largeWord117)
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 20 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 511),wireSAt ((code >>> 11) &&& 511))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 14 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>(OfNat.ofNat largeWord118)
|1=>(OfNat.ofNat largeWord119)
|2=>(OfNat.ofNat largeWord120)
|3=>(OfNat.ofNat largeWord121)
|4=>(OfNat.ofNat largeWord122)
|5=>(OfNat.ofNat largeWord123)
|_=>0
def pmB:Nat → Nat → Nat
|3,0=>(OfNat.ofNat largeWord124)
|4,0=>(OfNat.ofNat largeWord125)
|4,1=>(OfNat.ofNat largeWord126)
|5,0=>(OfNat.ofNat largeWord127)
|5,1=>(OfNat.ofNat largeWord128)
|5,2=>(OfNat.ofNat largeWord129)
|6,0=>(OfNat.ofNat largeWord130)
|6,1=>(OfNat.ofNat largeWord131)
|7,0=>(OfNat.ofNat largeWord132)
|8,0=>1
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 8 (j % 128);fld (pmPalB (k / 32)) 11 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dom_51,6,runOps true dom_51 (0,roots_51) ops)] else [])++(if pm.testBit 1 then [(dom_54,5,runOps true dom_54 (0,roots_54) ops)] else [])++(if pm.testBit 2 then [(dzo_39_16,5,runOps true dzo_39_16 (0,roots_39) ops)] else [])++(if pm.testBit 3 then [(dzo_38_16,4,runOps true dzo_38_16 (0,roots_38) ops)] else [])++(if pm.testBit 4 then [(dzo_49_4,4,runOps true dzo_49_4 (0,roots_49) ops)] else [])++(if pm.testBit 5 then [(dom_53,5,runOps true dom_53 (0,roots_53) ops)] else [])++(if pm.testBit 6 then [(dzo_22_32,4,runOps true dzo_22_32 (0,roots_22) ops)] else [])++(if pm.testBit 7 then [(dom_39,4,runOps true dom_39 (0,roots_39) ops)] else [])++(if pm.testBit 8 then [(dzo_51_4,5,runOps true dzo_51_4 (0,roots_51) ops)] else [])++(if pm.testBit 9 then [(dzo_23_32,5,runOps true dzo_23_32 (0,roots_23) ops)] else [])++(if pm.testBit 10 then [(dom_23,4,runOps true dom_23 (0,roots_23) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_55 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_51_8 _ g hchk
    · exact cpcs (by decide +kernel) lowS_54_8 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_39_24_16 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_38_24_16 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_49_12_4 _ g hchk
    · exact cpcs (by decide +kernel) lowS_53_8 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_22_40_32 _ g hchk
    · exact cpcs (by decide +kernel) lowS_39_8 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_51_12_4 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_23_40_32 _ g hchk
    · exact cpcs (by decide +kernel) lowS_23_8 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dom_51 6 s (0,roots_51) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_55 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_51_8 h
def symsG:List (List (Nat × Nat)):=[[((OfNat.ofNat largeWord6),16)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_55==dom_55) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_55 goalM v ys):RunD true dom_55 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_55 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 5 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 5 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 50 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 50 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_0:∀ i,0 ≤ i → i < 64 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_64:∀ i,64 ≤ i → i < 128 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 64 64=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_128:∀ i,128 ≤ i → i < 192 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 64 128=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_192:∀ i,192 ≤ i → i < 212 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 20 192=true)
private theorem z4:∀ i,0 ≤ i → i < 212 → Z 4 i=true:=(range_split (range_split z4_0 z4_64) (range_split z4_128 z4_192))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_0:∀ i,0 ≤ i → i < 64 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_64:∀ i,64 ≤ i → i < 128 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 64=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_128:∀ i,128 ≤ i → i < 192 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 128=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_192:∀ i,192 ≤ i → i < 256 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 192=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_256:∀ i,256 ≤ i → i < 320 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 256=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_320:∀ i,320 ≤ i → i < 371 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 51 320=true)
private theorem z5:∀ i,0 ≤ i → i < 371 → Z 5 i=true:=(range_split (range_split z5_0 (range_split z5_64 z5_128)) (range_split z5_192 (range_split z5_256 z5_320)))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0:∀ i,0 ≤ i → i < 64 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_64:∀ i,64 ≤ i → i < 128 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 64 64=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128:∀ i,128 ≤ i → i < 156 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 28 128=true)
private theorem z6:∀ i,0 ≤ i → i < 156 → Z 6 i=true:=(range_split z6_0 (range_split z6_64 z6_128))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7:∀ i,0 ≤ i → i < 24 → Z 7 i=true:=span_ok (by decide +kernel:span (Z 7) 24 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8:∀ i,0 ≤ i → i < 1 → Z 8 i=true:=span_ok (by decide +kernel:span (Z 8) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 8):∀ i < NN s,bar true dom_55 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_55 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 4=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 8) (h:RunD true dom_55 goalM s xsM):False:=by
  have hmin:4 ≤ s:=by have hl:=run_len h;change 5 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_55 roots_55 goal_55_8 9:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull

namespace BranchZero

def sourceIndex : Fin 6 → Nat := ![4, 5, 1, 2, 0, 0]

def column (j : Fin 6) : Nat := xs256.getD (sourceIndex j) 0

def points (r : Nat) (j : Fin 6) : Bool := !(column j).testBit r

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem finiteRows : ∀ r : Fin 256, dom_55.testBit r.val = true →
   goal_55_8.testBit r.val = (!(rs 5 false sixTarget) (points r.val)) := by decide +kernel

theorem observed : sampled points dom_55 (fun x => !(rs 5 false sixTarget) x) goal_55_8 := by
 intro i hi
 have hi256 : i < 256 := by
   by_contra! h
   have e : dom_55 < 2 ^ i :=
     lt_of_lt_of_le (by decide +kernel : dom_55 < 2 ^ 256) (Nat.pow_le_pow_right (by decide) h)
   rw [Nat.testBit_lt_two_pow e] at hi
   contradiction
 exact finiteRows ⟨i, hi256⟩ hi

theorem lower : Low 9 (rs 5 false sixTarget) := by
 have hd : dom_55 &&& mask256 = dom_55 := by decide +kernel
 have cols : ∀ j : Fin 6, column j ∈ roots_55 := by decide +kernel
 intro n program
 obtain ⟨bank, w, reached, hit, obs⟩ := sample_program points dom_55 hd roots_55 program
   (spent := 0) (bank := roots_55) rfl (by
     rintro u ⟨j, rfl⟩
     have hv : Avail true dom_55 roots_55 (column j) :=
       Or.inr (Or.inl ⟨column j, cols j, rfl⟩)
     refine ⟨(negD dom_55 (column j)), avail_neg hd hv, ?_⟩
     intro i h
     have rowMask := congrArg (fun w : Nat => w.testBit i) hd
     have hm : mask256.testBit i = true := by simpa [Nat.testBit_and, h] using rowMask
     simp [negD, Nat.testBit_xor, Nat.testBit_and, h, hm, points])
 have hv := avail_of_eq (sample_congr (sample_neg hd obs) observed) (avail_neg hd hit)
 have lowerBound := noCircuit n bank (by simpa using reached) hv
 omega

end BranchZero


end S_55_8
def dzo_54_8:=0x5500550055005500
namespace S_62_0
def pairsG:List (Nat × Nat):=[(2,6),(4,6),(10,14),(12,14),(18,22),(20,22),(26,30),(26,58),(28,30),(28,60),(34,38),(36,38),(42,46),(42,58),(44,46),(44,60),(50,54),(50,58),(52,54),(52,60),(56,58),(56,60)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x3fffff
def pool6G:List Nat:=[]
def goalM:Nat:=goal_62_0 &&& dom_62
def NN:Nat → Nat
|_=>0
def HT:Nat → Nat → Nat
|_,_=>0
def dictB:Nat → Nat → Nat
|_,_=>0
def stPool:Nat → Nat
|_=>0
def stOffB:Nat → Nat → Nat
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 0 then fld (dictB (i / 512) (i / 32 % 16)) 1 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 1 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 5 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 1 0 (NN s)
def opPool:Nat → Nat
|_=>0
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 4 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 1),wireSAt ((code >>> 3) &&& 1))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0
|_=>0
def pmB:Nat → Nat → Nat
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dzo_54_8,5,runOps true dzo_54_8 (0,roots_54) ops)] else [])
def symsG:List (List (Nat × Nat)):=[[((OfNat.ofNat largeWord6),16)],[((OfNat.ofNat largeWord16),8)],[((OfNat.ofNat largeWord10),24)],[((OfNat.ofNat largeWord19),2)],[((OfNat.ofNat largeWord6),16),((OfNat.ofNat largeWord10),24)],[((OfNat.ofNat largeWord6),16),((OfNat.ofNat largeWord16),8)],[((OfNat.ofNat largeWord6),16),((OfNat.ofNat largeWord19),2)]]
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
def Z (s:Nat):=barP true dom_62 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
private theorem z3:∀ i,0 ≤ i → i < 0 → Z 3 i=true:=by omega
private theorem z4:∀ i,0 ≤ i → i < 0 → Z 4 i=true:=by omega
private theorem z5:∀ i,0 ≤ i → i < 0 → Z 5 i=true:=by omega
end S_62_0
def dzo_57_4:=0x3030303030303030
def dzo_53_8:=0x3300330033003300
def dzo_45_16:=0x3333000033330000
def dzo_29_32:=0x3333333300000000
namespace S_61_0
def pairsG:List (Nat × Nat):=[(5,21),(9,25),(9,41),(13,29),(13,45),(17,21),(17,25),(20,21),(24,25),(28,29),(28,60),(33,41),(37,45),(37,53),(40,41),(44,45),(44,60),(49,53),(49,57),(52,53),(52,60),(56,57),(56,60)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x7fffff
def pool6G:List Nat:=[]
def goalM:Nat:=goal_61_0 &&& dom_61
def NN:Nat → Nat
|6=>1
|_=>0
def HT:Nat → Nat → Nat
|6,0=>0x653667d8
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>(OfNat.ofNat largeWord133)
|_,_=>0
def stPool:Nat → Nat
|0=>0x4688
|_=>0
def stOffB:Nat → Nat → Nat
|6,0=>5
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 5 then fld (dictB (i / 512) (i / 32 % 16)) 62 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 3 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 7 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 2 0 (NN s)
def opPool:Nat → Nat
|_=>0
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 8 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 7),wireSAt ((code >>> 5) &&& 7))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0xf0
|_=>0
def pmB:Nat → Nat → Nat
|6,0=>1
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 4 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dzo_57_4,5,runOps true dzo_57_4 (0,roots_57) ops)] else [])++(if pm.testBit 1 then [(dzo_53_8,5,runOps true dzo_53_8 (0,roots_53) ops)] else [])++(if pm.testBit 2 then [(dzo_45_16,5,runOps true dzo_45_16 (0,roots_45) ops)] else [])++(if pm.testBit 3 then [(dzo_29_32,5,runOps true dzo_29_32 (0,roots_29) ops)] else [])
def symsG:List (List (Nat × Nat)):=[[((OfNat.ofNat largeWord16),8),((OfNat.ofNat largeWord17),28)]]
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
def Z (s:Nat):=barP true dom_61 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
private theorem z3:∀ i,0 ≤ i → i < 0 → Z 3 i=true:=by omega
private theorem z4:∀ i,0 ≤ i → i < 0 → Z 4 i=true:=by omega
private theorem z5:∀ i,0 ≤ i → i < 0 → Z 5 i=true:=by omega
end S_61_0
def dzo_42_1:=0xa0a00000a0a
namespace S_43_0
def pairsG:List (Nat × Nat):=[(3,11),(3,35),(9,11),(9,41),(10,11),(33,35),(33,41),(34,35),(40,41),(42,43)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x3ff
def pool6G:List Nat:=[]
def goalM:Nat:=goal_43_0 &&& dom_43
def NN:Nat → Nat
|_=>0
def HT:Nat → Nat → Nat
|_,_=>0
def dictB:Nat → Nat → Nat
|_,_=>0
def stPool:Nat → Nat
|_=>0
def stOffB:Nat → Nat → Nat
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 0 then fld (dictB (i / 512) (i / 32 % 16)) 1 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 1 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 5 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 1 0 (NN s)
def opPool:Nat → Nat
|_=>0
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 4 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 1),wireSAt ((code >>> 3) &&& 1))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0
|_=>0
def pmB:Nat → Nat → Nat
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dzo_42_1,4,runOps true dzo_42_1 (0,roots_42) ops)] else [])
def symsG:List (List (Nat × Nat)):=[[((OfNat.ofNat largeWord10),24)],[((OfNat.ofNat largeWord11),6)],[((OfNat.ofNat largeWord8),30)],[((OfNat.ofNat largeWord10),24),((OfNat.ofNat largeWord8),30)],[((OfNat.ofNat largeWord10),24),((OfNat.ofNat largeWord11),6)]]
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
def Z (s:Nat):=barP true dom_43 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
private theorem z3:∀ i,0 ≤ i → i < 0 → Z 3 i=true:=by omega
private theorem z4:∀ i,0 ≤ i → i < 0 → Z 4 i=true:=by omega
end S_43_0
def isoMv_27_32:List (Nat × Nat):=[((OfNat.ofNat largeWord15),4),((OfNat.ofNat largeWord12),1)]
theorem lowS_27_32:Lower true dom_27 roots_27 goal_27_32 5:=lower_iso isoMv_27_32 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_23_32
def dzo_51_8:=0xf000f000f000f00
def dzo_43_16:=0xf0f00000f0f0000
def dzo_58_1:=0xa0a0a0a0a0a0a0a
def dzo_57_2:=0xc0c0c0c0c0c0c0c
def dzo_41_18:=0xc0c00000c0c0000
def dzo_27_32:=0xf0f0f0f00000000
namespace S_59_0
def pairsG:List (Nat × Nat):=[(3,11),(3,35),(9,11),(9,25),(9,41),(10,11),(17,25),(19,27),(19,51),(24,25),(26,27),(26,58),(33,35),(33,41),(34,35),(40,41),(42,43),(42,58),(49,51),(49,57),(50,51),(50,58),(56,57),(56,58)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xffffff
def pool6G:List Nat:=[]
def goalM:Nat:=goal_59_0 &&& dom_59
def NN:Nat → Nat
|4=>4
|5=>12
|6=>2
|7=>1
|_=>0
def HT:Nat → Nat → Nat
|4,0=>(OfNat.ofNat largeWord134)
|5,0=>(OfNat.ofNat largeWord135)
|6,0=>0x89a9dbc0638b81de
|7,0=>0xf0260ba
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>(OfNat.ofNat largeWord136)
|_,_=>0
def stPool:Nat → Nat
|0=>(OfNat.ofNat largeWord137)
|_=>0
def stOffB:Nat → Nat → Nat
|4,0=>0x1ea2942a805
|5,0=>(OfNat.ofNat largeWord138)
|6,0=>0x3135c6
|7,0=>0x685
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 23 then fld (dictB (i / 512) (i / 32 % 16)) 60 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 5 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 11 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 5 0 (NN s)
def opPool:Nat → Nat
|0=>(OfNat.ofNat largeWord139)
|_=>0
def opOffB:Nat → Nat → Nat
|4,0=>1
|5,0=>(OfNat.ofNat largeWord140)
|6,0=>0xe1d1
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 12 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 31),wireSAt ((code >>> 7) &&& 31))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 8 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>(OfNat.ofNat largeWord141)
|_=>0
def pmB:Nat → Nat → Nat
|4,0=>1
|5,0=>0x204170651381
|6,0=>0xa9
|7,0=>9
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 4 (j % 128);fld (pmPalB (k / 32)) 8 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dzo_51_8,6,runOps true dzo_51_8 (0,roots_51) ops)] else [])++(if pm.testBit 1 then [(dom_43,5,runOps true dom_43 (0,roots_43) ops)] else [])++(if pm.testBit 2 then [(dzo_42_1,4,runOps true dzo_42_1 (0,roots_42) ops)] else [])++(if pm.testBit 3 then [(dzo_43_16,5,runOps true dzo_43_16 (0,roots_43) ops)] else [])++(if pm.testBit 4 then [(dzo_58_1,5,runOps true dzo_58_1 (0,roots_58) ops)] else [])++(if pm.testBit 5 then [(dzo_57_2,5,runOps true dzo_57_2 (0,roots_57) ops)] else [])++(if pm.testBit 6 then [(dzo_41_18,4,runOps true dzo_41_18 (0,roots_41) ops)] else [])++(if pm.testBit 7 then [(dzo_27_32,5,runOps true dzo_27_32 (0,roots_27) ops)] else [])
def symsG:List (List (Nat × Nat)):=[[((OfNat.ofNat largeWord8),30)]]
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
def Z (s:Nat):=barP true dom_59 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
private theorem z3:∀ i,0 ≤ i → i < 0 → Z 3 i=true:=by omega
end S_59_0
def isoMv_13_48:List (Nat × Nat):=[((OfNat.ofNat largeWord6),16),((OfNat.ofNat largeWord10),24),((OfNat.ofNat largeWord15),4),((OfNat.ofNat largeWord12),1)]
theorem lowS_13_48:Lower true dom_13 roots_13 goal_13_48 4:=lower_iso isoMv_13_48 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_42_1
def isoMv_14_48:List (Nat × Nat):=[((OfNat.ofNat largeWord6),16),((OfNat.ofNat largeWord10),24),((OfNat.ofNat largeWord15),4)]
theorem lowS_14_48:Lower true dom_14 roots_14 goal_14_48 4:=lower_iso isoMv_14_48 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_42_1
def isoMv_11_48:List (Nat × Nat):=[((OfNat.ofNat largeWord6),16),((OfNat.ofNat largeWord10),24),((OfNat.ofNat largeWord15),4),((OfNat.ofNat largeWord11),6),((OfNat.ofNat largeWord12),1)]
theorem lowS_11_48:Lower true dom_11 roots_11 goal_11_48 4:=lower_iso isoMv_11_48 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_42_1
namespace S_15_48
def pairsG:List (Nat × Nat):=[(1,3),(1,5),(1,9),(2,3),(2,6),(2,10),(4,5),(4,6),(4,12),(8,9),(8,10),(8,12)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_15.map (· &&& dom_15)
def goalM:Nat:=goal_15_48 &&& dom_15
def NN:Nat → Nat
|3=>2
|4=>8
|5=>3
|6=>1
|_=>0
def HT:Nat → Nat → Nat
|3,0=>0x804d157017d4d0b
|4,0=>(OfNat.ofNat largeWord142)
|5,0=>(OfNat.ofNat largeWord143)
|6,0=>0x57e3d3b0
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>(OfNat.ofNat largeWord144)
|_,_=>0
def stPool:Nat → Nat
|0=>(OfNat.ofNat largeWord145)
|_=>0
def stOffB:Nat → Nat → Nat
|3,0=>0x22004
|4,0=>(OfNat.ofNat largeWord146)
|5,0=>0xe91aab05
|6,0=>0x3e4
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 15 then fld (dictB (i / 512) (i / 32 % 16)) 16 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 4 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 11 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|0=>0x80501605018690160d01
|_=>0
def opOffB:Nat → Nat → Nat
|3,0=>1
|4,0=>0x5141003100211100
|5,0=>0x7161
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 10 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 15),wireSAt ((code >>> 6) &&& 15))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 8 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0xf7653210
|_=>0
def pmB:Nat → Nat → Nat
|3,0=>3
|4,0=>0x8420d5
|5,0=>0x1bf
|6,0=>7
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 3 (j % 128);fld (pmPalB (k / 32)) 4 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dom_7,4,runOps true dom_7 (0,roots_7) ops)] else [])++(if pm.testBit 1 then [(dom_13,4,runOps true dom_13 (0,roots_13) ops)] else [])++(if pm.testBit 2 then [(dom_14,4,runOps true dom_14 (0,roots_14) ops)] else [])++(if pm.testBit 3 then [(dom_11,4,runOps true dom_11 (0,roots_11) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_15 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_7_48 _ g hchk
    · exact cpcs (by decide +kernel) lowS_13_48 _ g hchk
    · exact cpcs (by decide +kernel) lowS_14_48 _ g hchk
    · exact cpcs (by decide +kernel) lowS_11_48 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dom_7 4 s (0,roots_7) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_15 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_7_48 h
def symsG:List (List (Nat × Nat)):=[[((OfNat.ofNat largeWord15),4)],[((OfNat.ofNat largeWord19),2)],[((OfNat.ofNat largeWord11),6)],[((OfNat.ofNat largeWord12),1)],[((OfNat.ofNat largeWord18),3)],[((OfNat.ofNat largeWord14),7)],[((OfNat.ofNat largeWord15),4),((OfNat.ofNat largeWord11),6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_15==dom_15) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_15 goalM v ys):RunD true dom_15 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_15 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 2 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 2 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4:∀ i,0 ≤ i → i < 8 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 8 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5:∀ i,0 ≤ i → i < 3 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 3 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6:∀ i,0 ≤ i → i < 1 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 6):∀ i < NN s,bar true dom_15 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_15 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 4 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 6) (h:RunD true dom_15 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_15 roots_15 goal_15_48 7:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_15_48
theorem lowS_15_48:Lower true dom_15 roots_15 goal_15_48 7:=S_15_48.noCircuit
def isoMv_30_32:List (Nat × Nat):=[((OfNat.ofNat largeWord15),4),((OfNat.ofNat largeWord12),1)]
theorem lowS_30_32:Lower true dom_30 roots_30 goal_30_32 5:=lower_iso isoMv_30_32 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_29_32
def isoMv_27_36:List (Nat × Nat):=[((OfNat.ofNat largeWord15),4),((OfNat.ofNat largeWord12),1)]
theorem lowS_27_36:Lower true dom_27 roots_27 goal_27_36 5:=lower_iso isoMv_27_36 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_23_40
def dzo_15_16:=0xffff0000
def gzo_15_48_16:=0xfee80000
theorem lowSh_15_48_16:Lower true dzo_15_16 roots_15 gzo_15_48_16 7:=lower_iso (d1:=dom_15) (roots1:=roots_15) (T1:=goal_15_48) [(dom_15,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_48
def dzo_22_8:=0x55005500
def gzo_22_40_8:=0x54004000
theorem lowSh_22_40_8:Lower true dzo_22_8 roots_22 gzo_22_40_8 4:=lower_iso (d1:=dom_22) (roots1:=roots_22) (T1:=goal_22_40) [(dom_22,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_22_40
def dzo_23_8:=0xff00ff00
def gzo_23_40_8:=0xfe00ea00
theorem lowSh_23_40_8:Lower true dzo_23_8 roots_23 gzo_23_40_8 5:=lower_iso (d1:=dom_23) (roots1:=roots_23) (T1:=goal_23_40) [(dom_23,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_23_40
def dzo_13_16:=0x33330000
def gzo_13_48_16:=0x32200000
theorem lowSh_13_48_16:Lower true dzo_13_16 roots_13 gzo_13_48_16 4:=lower_iso (d1:=dom_13) (roots1:=roots_13) (T1:=goal_13_48) [(dom_13,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_13_48
def dzo_14_16:=0x55550000
def gzo_14_48_16:=0x54400000
theorem lowSh_14_48_16:Lower true dzo_14_16 roots_14 gzo_14_48_16 4:=lower_iso (d1:=dom_14) (roots1:=roots_14) (T1:=goal_14_48) [(dom_14,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_14_48
def dzo_11_16:=0xf0f0000
def gzo_11_48_16:=0xe080000
theorem lowSh_11_48_16:Lower true dzo_11_16 roots_11 gzo_11_48_16 4:=lower_iso (d1:=dom_11) (roots1:=roots_11) (T1:=goal_11_48) [(dom_11,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_11_48
def dzo_27_4:=0xf0f0f0f0
def gzo_27_36_4:=0xf0e0e0c0
theorem lowSh_27_36_4:Lower true dzo_27_4 roots_27 gzo_27_36_4 5:=lower_iso (d1:=dom_27) (roots1:=roots_27) (T1:=goal_27_36) [(dom_27,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_27_36
namespace S_31_32
def pairsG:List (Nat × Nat):=[(1,3),(1,9),(2,3),(2,6),(4,6),(5,7),(5,13),(5,21),(8,9),(10,11),(10,14),(10,26),(12,13),(12,14),(12,28),(17,19),(17,21),(17,25),(18,19),(18,22),(18,26),(20,21),(20,22),(20,28),(24,25),(24,26),(24,28)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x7ffffff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_31.map (· &&& dom_31)
def goalM:Nat:=goal_31_32 &&& dom_31
def NN:Nat → Nat
|2=>7
|3=>131
|4=>302
|5=>258
|6=>84
|7=>14
|8=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>(OfNat.ofNat largeWord147)
|3,0=>(OfNat.ofNat largeWord148)
|3,1=>(OfNat.ofNat largeWord149)
|4,0=>(OfNat.ofNat largeWord150)
|4,1=>(OfNat.ofNat largeWord151)
|4,2=>(OfNat.ofNat largeWord152)
|5,0=>(OfNat.ofNat largeWord153)
|5,1=>(OfNat.ofNat largeWord154)
|5,2=>0xf483970feeee01a8
|6,0=>(OfNat.ofNat largeWord155)
|7,0=>(OfNat.ofNat largeWord156)
|8,0=>0x1f16380d
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>(OfNat.ofNat largeWord157)
|0,1=>(OfNat.ofNat largeWord158)
|0,2=>(OfNat.ofNat largeWord159)
|0,3=>(OfNat.ofNat largeWord160)
|0,4=>(OfNat.ofNat largeWord161)
|0,5=>(OfNat.ofNat largeWord162)
|0,6=>(OfNat.ofNat largeWord163)
|0,7=>(OfNat.ofNat largeWord164)
|0,8=>(OfNat.ofNat largeWord165)
|0,9=>(OfNat.ofNat largeWord166)
|0,10=>(OfNat.ofNat largeWord167)
|0,11=>(OfNat.ofNat largeWord168)
|_,_=>0
def stPool:Nat → Nat
|0=>(OfNat.ofNat largeWord169)
|1=>(OfNat.ofNat largeWord170)
|2=>(OfNat.ofNat largeWord171)
|3=>(OfNat.ofNat largeWord172)
|4=>(OfNat.ofNat largeWord173)
|5=>(OfNat.ofNat largeWord174)
|6=>(OfNat.ofNat largeWord175)
|7=>(OfNat.ofNat largeWord176)
|8=>(OfNat.ofNat largeWord177)
|9=>(OfNat.ofNat largeWord178)
|10=>(OfNat.ofNat largeWord179)
|11=>(OfNat.ofNat largeWord180)
|12=>(OfNat.ofNat largeWord181)
|13=>(OfNat.ofNat largeWord182)
|14=>(OfNat.ofNat largeWord183)
|15=>(OfNat.ofNat largeWord184)
|16=>(OfNat.ofNat largeWord185)
|17=>(OfNat.ofNat largeWord186)
|18=>(OfNat.ofNat largeWord187)
|19=>(OfNat.ofNat largeWord188)
|20=>(OfNat.ofNat largeWord189)
|21=>(OfNat.ofNat largeWord190)
|22=>(OfNat.ofNat largeWord191)
|23=>(OfNat.ofNat largeWord192)
|24=>(OfNat.ofNat largeWord193)
|25=>(OfNat.ofNat largeWord194)
|26=>(OfNat.ofNat largeWord195)
|27=>(OfNat.ofNat largeWord196)
|28=>(OfNat.ofNat largeWord197)
|29=>(OfNat.ofNat largeWord198)
|30=>(OfNat.ofNat largeWord199)
|31=>(OfNat.ofNat largeWord200)
|32=>(OfNat.ofNat largeWord201)
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>(OfNat.ofNat largeWord202)
|3,0=>(OfNat.ofNat largeWord203)
|3,1=>(OfNat.ofNat largeWord204)
|3,2=>0x875043282154
|4,0=>(OfNat.ofNat largeWord205)
|4,1=>(OfNat.ofNat largeWord206)
|4,2=>(OfNat.ofNat largeWord207)
|4,3=>(OfNat.ofNat largeWord208)
|4,4=>(OfNat.ofNat largeWord209)
|5,0=>(OfNat.ofNat largeWord210)
|5,1=>(OfNat.ofNat largeWord211)
|5,2=>(OfNat.ofNat largeWord212)
|5,3=>(OfNat.ofNat largeWord213)
|5,4=>0x1bc0adda6
|6,0=>(OfNat.ofNat largeWord214)
|6,1=>(OfNat.ofNat largeWord215)
|7,0=>(OfNat.ofNat largeWord216)
|8,0=>0x103a5
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 364 then fld (dictB (i / 512) (i / 32 % 16)) 32 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 9 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 17 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|0=>(OfNat.ofNat largeWord217)
|1=>(OfNat.ofNat largeWord218)
|2=>(OfNat.ofNat largeWord219)
|3=>(OfNat.ofNat largeWord220)
|4=>(OfNat.ofNat largeWord221)
|5=>(OfNat.ofNat largeWord222)
|6=>(OfNat.ofNat largeWord223)
|_=>0
def opOffB:Nat → Nat → Nat
|4,0=>(OfNat.ofNat largeWord224)
|4,1=>(OfNat.ofNat largeWord225)
|4,2=>(OfNat.ofNat largeWord226)
|4,3=>(OfNat.ofNat largeWord227)
|4,4=>(OfNat.ofNat largeWord228)
|5,0=>(OfNat.ofNat largeWord229)
|5,1=>(OfNat.ofNat largeWord230)
|5,2=>(OfNat.ofNat largeWord231)
|5,3=>(OfNat.ofNat largeWord232)
|5,4=>0x2466000
|6,0=>(OfNat.ofNat largeWord233)
|6,1=>(OfNat.ofNat largeWord234)
|7,0=>(OfNat.ofNat largeWord235)
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 20 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 511),wireSAt ((code >>> 11) &&& 511))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 13 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>(OfNat.ofNat largeWord236)
|1=>(OfNat.ofNat largeWord237)
|2=>(OfNat.ofNat largeWord238)
|3=>(OfNat.ofNat largeWord239)
|_=>0
def pmB:Nat → Nat → Nat
|3,0=>(OfNat.ofNat largeWord240)
|3,1=>0
|4,0=>(OfNat.ofNat largeWord241)
|4,1=>(OfNat.ofNat largeWord242)
|4,2=>(OfNat.ofNat largeWord243)
|5,0=>(OfNat.ofNat largeWord244)
|5,1=>(OfNat.ofNat largeWord245)
|5,2=>0xe00
|6,0=>(OfNat.ofNat largeWord246)
|7,0=>(OfNat.ofNat largeWord247)
|8,0=>1
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 7 (j % 128);fld (pmPalB (k / 32)) 13 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dzo_15_16,7,runOps true dzo_15_16 (0,roots_15) ops)] else [])++(if pm.testBit 1 then [(dzo_22_8,4,runOps true dzo_22_8 (0,roots_22) ops)] else [])++(if pm.testBit 2 then [(dom_23,5,runOps true dom_23 (0,roots_23) ops)] else [])++(if pm.testBit 3 then [(dom_30,5,runOps true dom_30 (0,roots_30) ops)] else [])++(if pm.testBit 4 then [(dzo_23_8,5,runOps true dzo_23_8 (0,roots_23) ops)] else [])++(if pm.testBit 5 then [(dzo_13_16,4,runOps true dzo_13_16 (0,roots_13) ops)] else [])++(if pm.testBit 6 then [(dzo_7_16,4,runOps true dzo_7_16 (0,roots_7) ops)] else [])++(if pm.testBit 7 then [(dzo_25_4,4,runOps true dzo_25_4 (0,roots_25) ops)] else [])++(if pm.testBit 8 then [(dom_27,5,runOps true dom_27 (0,roots_27) ops)] else [])++(if pm.testBit 9 then [(dzo_14_16,4,runOps true dzo_14_16 (0,roots_14) ops)] else [])++(if pm.testBit 10 then [(dom_29,5,runOps true dom_29 (0,roots_29) ops)] else [])++(if pm.testBit 11 then [(dzo_11_16,4,runOps true dzo_11_16 (0,roots_11) ops)] else [])++(if pm.testBit 12 then [(dzo_27_4,5,runOps true dzo_27_4 (0,roots_27) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_31 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowSh_15_48_16 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_22_40_8 _ g hchk
    · exact cpcs (by decide +kernel) lowS_23_32 _ g hchk
    · exact cpcs (by decide +kernel) lowS_30_32 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_23_40_8 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_13_48_16 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_7_48_16 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_25_36_4 _ g hchk
    · exact cpcs (by decide +kernel) lowS_27_32 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_14_48_16 _ g hchk
    · exact cpcs (by decide +kernel) lowS_29_32 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_11_48_16 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_27_36_4 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_15_16 7 s (0,roots_15) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_31 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_15_48_16 h
def symsG:List (List (Nat × Nat)):=[[((OfNat.ofNat largeWord15),4),((OfNat.ofNat largeWord12),1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_31==dom_31) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_31 goalM v ys):RunD true dom_31 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_31 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 7 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 7 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3_0:∀ i,0 ≤ i → i < 64 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3_64:∀ i,64 ≤ i → i < 128 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 64 64=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3_128:∀ i,128 ≤ i → i < 131 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 3 128=true)
private theorem z3:∀ i,0 ≤ i → i < 131 → Z 3 i=true:=(range_split z3_0 (range_split z3_64 z3_128))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_0:∀ i,0 ≤ i → i < 64 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_64:∀ i,64 ≤ i → i < 128 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 64 64=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_128:∀ i,128 ≤ i → i < 192 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 64 128=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_192:∀ i,192 ≤ i → i < 256 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 64 192=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_256:∀ i,256 ≤ i → i < 302 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 46 256=true)
private theorem z4:∀ i,0 ≤ i → i < 302 → Z 4 i=true:=(range_split (range_split z4_0 z4_64) (range_split z4_128 (range_split z4_192 z4_256)))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_0:∀ i,0 ≤ i → i < 64 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_64:∀ i,64 ≤ i → i < 128 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 64=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_128:∀ i,128 ≤ i → i < 192 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 128=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_192:∀ i,192 ≤ i → i < 256 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 192=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_256:∀ i,256 ≤ i → i < 258 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 2 256=true)
private theorem z5:∀ i,0 ≤ i → i < 258 → Z 5 i=true:=(range_split (range_split z5_0 z5_64) (range_split z5_128 (range_split z5_192 z5_256)))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0:∀ i,0 ≤ i → i < 64 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_64:∀ i,64 ≤ i → i < 84 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 20 64=true)
private theorem z6:∀ i,0 ≤ i → i < 84 → Z 6 i=true:=(range_split z6_0 z6_64)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7:∀ i,0 ≤ i → i < 14 → Z 7 i=true:=span_ok (by decide +kernel:span (Z 7) 14 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8:∀ i,0 ≤ i → i < 1 → Z 8 i=true:=span_ok (by decide +kernel:span (Z 8) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 8):∀ i < NN s,bar true dom_31 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_31 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 4=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 8) (h:RunD true dom_31 goalM s xsM):False:=by
  have hmin:4 ≤ s:=by have hl:=run_len h;change 5 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_31 roots_31 goal_31_32 9:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull

namespace BranchOne

def sourceIndex : Fin 6 → Nat := ![0, 1, 2, 3, 4, 0]

def column (j : Fin 6) : Nat := xs256.getD (sourceIndex j) 0

def points (r : Nat) (j : Fin 6) : Bool := (column j).testBit r

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem finiteRows : ∀ r : Fin 256, dom_31.testBit r.val = true →
   goal_31_32.testBit r.val = ((rs 5 true sixTarget) (points r.val)) := by decide +kernel

theorem observed : sampled points dom_31 (rs 5 true sixTarget) goal_31_32 := by
 intro i hi
 have hi256 : i < 256 := by
   by_contra! h
   have e : dom_31 < 2 ^ i :=
     lt_of_lt_of_le (by decide +kernel : dom_31 < 2 ^ 256) (Nat.pow_le_pow_right (by decide) h)
   rw [Nat.testBit_lt_two_pow e] at hi
   contradiction
 exact finiteRows ⟨i, hi256⟩ hi

theorem lower : Low 9 (rs 5 true sixTarget) := by
 have hd : dom_31 &&& mask256 = dom_31 := by decide +kernel
 have cols : ∀ j : Fin 6, column j ∈ roots_31 := by decide +kernel
 intro n program
 obtain ⟨bank, w, reached, hit, obs⟩ := sample_program points dom_31 hd roots_31 program
   (spent := 0) (bank := roots_31) rfl (by
     rintro u ⟨j, rfl⟩
     have hv : Avail true dom_31 roots_31 (column j) :=
       Or.inr (Or.inl ⟨column j, cols j, rfl⟩)
     refine ⟨(column j), hv, ?_⟩
     intro i h
     rfl)
 have hv := avail_of_eq (sample_congr obs observed) hit
 have lowerBound := noCircuit n bank (by simpa using reached) hv
 omega

end BranchOne

end S_31_32



end Certificate0

end Evidence

theorem sixLower : Low 11 sixTarget :=
  two 5 (good_at 3 7 0 (by decide +kernel)) (good_at 3 3 0 (by decide +kernel)) Evidence.Certificate0.S_55_8.BranchZero.lower Evidence.Certificate0.S_31_32.BranchOne.lower

end PEqualNP.Outside.L_meta_45356_aux

open PEqualNP.Outside.L_meta_45356_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_45356 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677320 * 2 ^ 32 + 4276125824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677320 * 2 ^ 32 + 4276125824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s h
  by_cases enough : 12 ≤ s
  · exact ⟨sixWitness, basis, enough, correct⟩
  obtain ⟨⟨gs,o⟩, fit, size, computes⟩ := h
  have hf : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    exact ⟨by simpa using (fit g hg).1, (fit g hg).2⟩
  change gs.length ≤ s at size
  exact ⟨⟨gs,o⟩, all_not_not sixLower gs o hf (by omega) computes, size, computes⟩
